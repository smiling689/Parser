#include "cfg.hpp"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

/* inputs: */
int number_of_symb; /* number of symbols */
int number_of_prod; /* number of productions */
struct prod grammar[MAX_NUMBER_OF_PROD];

/* outputs: */
struct state state_info[MAX_NUMBER_OF_STATE];
struct trans_result trans[MAX_NUMBER_OF_STATE][MAX_NUMBER_OF_SYMB];

bool operator<(const handler &a, const handler &b) {
    if (a.prod_id != b.prod_id) {
        return a.prod_id < b.prod_id;
    }
    return a.dot_pos < b.dot_pos;
}

namespace {

struct ItemCompare {
    bool operator()(const handler &a, const handler &b) const {
        if (a.prod_id != b.prod_id) {
            return a.prod_id < b.prod_id;
        }
        return a.dot_pos < b.dot_pos;
    }
};

constexpr int ACTION_SHIFT = 0;
constexpr int ACTION_REDUCE = 1;
constexpr int ACTION_NONE = -1;

std::vector<std::string> symbol_names;
std::vector<int> is_terminal;
std::vector<std::vector<int>> prods_by_left;
std::vector<std::set<int>> first_set;
std::vector<std::set<int>> follow_set;
std::vector<std::vector<handler>> canonical_states;
std::vector<std::vector<int>> goto_table;

int eof_symbol = -1;
int augmented_start_symbol = -1;
int augmented_prod_id = -1;

std::string production_to_string(int prod_id, int dot_pos = -1) {
    if (prod_id < 0 || prod_id >= number_of_prod) {
        return "<invalid production>";
    }
    const prod &p = grammar[prod_id];
    std::string result = symbol_names[p.l] + " ->";
    for (int i = 0; i < p.len; ++i) {
        if (dot_pos == i) {
            result += " .";
        }
        result += " " + symbol_names[p.r[i]];
    }
    if (dot_pos == p.len) {
        result += " .";
    }
    return result;
}

void initialize_transitions(int state_count) {
    for (int i = 0; i < state_count; ++i) {
        for (int j = 0; j < number_of_symb; ++j) {
            trans[i][j].t = ACTION_NONE;
            trans[i][j].id = -1;
        }
    }
}

std::vector<handler> closure(const std::vector<handler> &items) {
    std::vector<handler> result;
    std::queue<handler> q;
    std::set<std::pair<int, int>> seen;

    for (const handler &it : items) {
        q.push(it);
    }

    while (!q.empty()) {
        handler cur = q.front();
        q.pop();
        auto key = std::make_pair(cur.prod_id, cur.dot_pos);
        if (!seen.insert(key).second) {
            continue;
        }
        result.push_back(cur);
        const prod &p = grammar[cur.prod_id];
        if (cur.dot_pos >= p.len) {
            continue;
        }
        int sym = p.r[cur.dot_pos];
        if (is_terminal[sym]) {
            continue;
        }
        for (int prod_id : prods_by_left[sym]) {
            handler nxt{prod_id, 0};
            if (seen.find(std::make_pair(nxt.prod_id, nxt.dot_pos)) ==
                seen.end()) {
                q.push(nxt);
            }
        }
    }
    std::sort(result.begin(), result.end(), ItemCompare());
    return result;
}

std::vector<handler> goto_set(const std::vector<handler> &state, int symbol) {
    std::vector<handler> moved;
    for (const handler &it : state) {
        const prod &p = grammar[it.prod_id];
        if (it.dot_pos < p.len && p.r[it.dot_pos] == symbol) {
            moved.push_back(handler{it.prod_id, it.dot_pos + 1});
        }
    }
    if (moved.empty()) {
        return {};
    }
    return closure(moved);
}

void compute_first_sets() {
    first_set.assign(number_of_symb, {});
    for (int i = 0; i < number_of_symb; ++i) {
        if (is_terminal[i]) {
            first_set[i].insert(i);
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < number_of_prod; ++i) {
            const prod &p = grammar[i];
            if (p.len == 0) {
                continue;
            }
            int sym = p.r[0];
            for (int token : first_set[sym]) {
                if (!first_set[p.l].count(token)) {
                    first_set[p.l].insert(token);
                    changed = true;
                }
            }
        }
    }
}

void compute_follow_sets() {
    follow_set.assign(number_of_symb, {});
    if (augmented_start_symbol >= 0 && eof_symbol >= 0) {
        follow_set[augmented_start_symbol].insert(eof_symbol);
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < number_of_prod; ++i) {
            const prod &p = grammar[i];
            for (int j = 0; j < p.len - 1; ++j) {
                int cur_sym = p.r[j];
                int next_sym = p.r[j + 1];
                if (is_terminal[cur_sym]) {
                    continue;
                }
                for (int token : first_set[next_sym]) {
                    if (!follow_set[cur_sym].count(token)) {
                        follow_set[cur_sym].insert(token);
                        changed = true;
                    }
                }
            }
            if (p.len == 0) {
                continue;
            }
            int last_sym = p.r[p.len - 1];
            if (is_terminal[last_sym]) {
                continue;
            }
            for (int token : follow_set[p.l]) {
                if (!follow_set[last_sym].count(token)) {
                    follow_set[last_sym].insert(token);
                    changed = true;
                }
            }
        }
    }
}

int ensure_state(const std::vector<handler> &items,
                 std::map<std::vector<handler>, int> &state_id) {
    auto it = state_id.find(items);
    if (it != state_id.end()) {
        return it->second;
    }
    int id = static_cast<int>(canonical_states.size());
    canonical_states.push_back(items);
    state_id[items] = id;
    return id;
}

void build_canonical_collection() {
    canonical_states.clear();
    goto_table.clear();
    std::map<std::vector<handler>, int> state_id;

    std::vector<handler> start_items = closure({handler{augmented_prod_id, 0}});
    int start_state = ensure_state(start_items, state_id);

    std::queue<int> q;
    q.push(start_state);
    goto_table.resize(1);
    goto_table[0].assign(number_of_symb, -1);

    while (!q.empty()) {
        int cur_state = q.front();
        q.pop();
        if (static_cast<int>(goto_table.size()) <= cur_state) {
            goto_table.resize(cur_state + 1,
                              std::vector<int>(number_of_symb, -1));
        }

        std::set<int> seen_symbols;
        for (const handler &item : canonical_states[cur_state]) {
            const prod &p = grammar[item.prod_id];
            if (item.dot_pos >= p.len) {
                continue;
            }
            seen_symbols.insert(p.r[item.dot_pos]);
        }
        for (int sym : seen_symbols) {
            std::vector<handler> dest_items =
                goto_set(canonical_states[cur_state], sym);
            if (dest_items.empty()) {
                continue;
            }
            int dest_id = ensure_state(dest_items, state_id);
            if (static_cast<int>(goto_table.size()) <= dest_id) {
                goto_table.resize(dest_id + 1,
                                  std::vector<int>(number_of_symb, -1));
            }
            if (static_cast<int>(goto_table[cur_state].size()) <
                number_of_symb) {
                goto_table[cur_state].resize(number_of_symb, -1);
            }
            goto_table[cur_state][sym] = dest_id;
            if (dest_id >= static_cast<int>(canonical_states.size()) - 1) {
                q.push(dest_id);
            }
        }
    }

    goto_table.resize(canonical_states.size(),
                      std::vector<int>(number_of_symb, -1));
}

void dump_states() {
    std::cout << "States (" << canonical_states.size() << "):\n";
    for (size_t i = 0; i < canonical_states.size(); ++i) {
        std::cout << "State " << i << ":\n";
        for (const handler &item : canonical_states[i]) {
            std::cout << "  "
                      << production_to_string(item.prod_id, item.dot_pos)
                      << "\n";
        }
    }
}

void populate_state_info() {
    for (size_t i = 0; i < canonical_states.size(); ++i) {
        state_info[i].size = static_cast<int>(canonical_states[i].size());
        handler *arr = new handler[state_info[i].size];
        for (int j = 0; j < state_info[i].size; ++j) {
            arr[j] = canonical_states[i][j];
        }
        state_info[i].s = arr;
    }
}

bool set_action(int state, int symbol, int type, int id) {
    trans_result &entry = trans[state][symbol];
    if (entry.t == ACTION_NONE) {
        entry.t = type;
        entry.id = id;
        return true;
    }
    if (entry.t == type && entry.id == id) {
        return true;
    }
    std::cerr << "Conflict detected in state " << state << " on symbol "
              << symbol_names[symbol] << ".\n";
    return false;
}

void build_parse_table() {
    int state_count = static_cast<int>(canonical_states.size());
    initialize_transitions(state_count);

    for (int state = 0; state < state_count; ++state) {
        for (const handler &item : canonical_states[state]) {
            const prod &p = grammar[item.prod_id];
            if (item.dot_pos < p.len) {
                int sym = p.r[item.dot_pos];
                if (!is_terminal[sym]) {
                    continue;
                }
                int dest = goto_table[state][sym];
                if (dest != -1) {
                    set_action(state, sym, ACTION_SHIFT, dest);
                }
            } else {
                int lhs = p.l;
                const std::set<int> &lookahead = follow_set[lhs];
                for (int la : lookahead) {
                    set_action(state, la, ACTION_REDUCE, item.prod_id);
                }
            }
        }
    }
}

void dump_first_follow() {
    std::cout << "First sets:\n";
    for (size_t i = 0; i < symbol_names.size(); ++i) {
        if (is_terminal[i]) {
            continue;
        }
        std::cout << "  " << symbol_names[i] << ": {";
        bool first_entry = true;
        for (int token : first_set[i]) {
            if (!first_entry) {
                std::cout << ", ";
            }
            std::cout << symbol_names[token];
            first_entry = false;
        }
        std::cout << "}\n";
    }

    std::cout << "Follow sets:\n";
    for (size_t i = 0; i < symbol_names.size(); ++i) {
        if (is_terminal[i]) {
            continue;
        }
        std::cout << "  " << symbol_names[i] << ": {";
        bool first_entry = true;
        for (int token : follow_set[i]) {
            if (!first_entry) {
                std::cout << ", ";
            }
            std::cout << symbol_names[token];
            first_entry = false;
        }
        std::cout << "}\n";
    }
}

void dump_transitions() {
    std::cout << "Parse table (shift/reduce entries shown for terminals):\n";
    for (size_t state = 0; state < canonical_states.size(); ++state) {
        std::cout << "State " << state << ":\n";
        for (size_t sym = 0; sym < symbol_names.size(); ++sym) {
            if (!is_terminal[sym]) {
                continue;
            }
            const trans_result &entry = trans[state][sym];
            if (entry.t == ACTION_NONE) {
                continue;
            }
            std::cout << "  on " << symbol_names[sym] << " -> ";
            if (entry.t == ACTION_SHIFT) {
                std::cout << "shift " << entry.id;
            } else {
                std::cout << "reduce " << production_to_string(entry.id);
            }
            std::cout << "\n";
        }
    }
}

void simulate_parse(const std::vector<int> &input_tokens) {
    if (input_tokens.empty()) {
        std::cout << "No input sequence provided for simulation.\n";
        return;
    }
    std::cout << "Parse simulation:\n";
    std::vector<int> stack;
    stack.push_back(0);
    size_t position = 0;
    int step = 0;
    while (true) {
        if (position >= input_tokens.size()) {
            std::cout << "  [error] Ran out of input symbols.\n";
            return;
        }
        int state = stack.back();
        int lookahead = input_tokens[position];
        const trans_result &entry = trans[state][lookahead];
        if (entry.t == ACTION_SHIFT) {
            std::cout << "  Step " << step++ << ": shift "
                      << symbol_names[lookahead] << ", goto state " << entry.id
                      << "\n";
            stack.push_back(entry.id);
            ++position;
        } else if (entry.t == ACTION_REDUCE) {
            if (entry.id == augmented_prod_id && lookahead == eof_symbol) {
                std::cout << "  Step " << step++ << ": accept\n";
                break;
            }
            const prod &p = grammar[entry.id];
            std::cout << "  Step " << step++ << ": reduce "
                      << production_to_string(entry.id) << "\n";
            for (int i = 0; i < p.len; ++i) {
                if (!stack.empty()) {
                    stack.pop_back();
                }
            }
            if (stack.empty()) {
                std::cout
                    << "  [error] State stack is empty during reduction.\n";
                return;
            }
            int goto_state = goto_table[stack.back()][p.l];
            if (goto_state == -1) {
                std::cout << "  [error] Missing goto from state "
                          << stack.back() << " on " << symbol_names[p.l]
                          << "\n";
                return;
            }
            stack.push_back(goto_state);
        } else {
            std::cout << "  [error] No valid action at state " << state
                      << " on symbol " << symbol_names[lookahead] << "\n";
            return;
        }
    }
}

} // namespace

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    const bool debug_mode = std::getenv("PARSER_DEBUG") != nullptr;

    int terminal_count = 0;
    int non_terminal_count = 0;
    int prod_count = 0;
    if (!(std::cin >> terminal_count >> non_terminal_count >> prod_count)) {
        std::cerr << "Failed to read grammar sizes.\n";
        return 1;
    }

    symbol_names.clear();
    is_terminal.clear();
    symbol_names.reserve(terminal_count + non_terminal_count + 2);
    is_terminal.reserve(terminal_count + non_terminal_count + 2);

    std::unordered_map<std::string, int> symbol_id;
    symbol_id.reserve(terminal_count + non_terminal_count + 2);

    for (int i = 0; i < terminal_count; ++i) {
        std::string name;
        std::cin >> name;
        symbol_id[name] = static_cast<int>(symbol_names.size());
        symbol_names.push_back(name);
        is_terminal.push_back(1);
    }
    for (int i = 0; i < non_terminal_count; ++i) {
        std::string name;
        std::cin >> name;
        symbol_id[name] = static_cast<int>(symbol_names.size());
        symbol_names.push_back(name);
        is_terminal.push_back(0);
    }

    std::string start_symbol_name;
    std::cin >> start_symbol_name;
    if (!symbol_id.count(start_symbol_name)) {
        std::cerr << "Start symbol " << start_symbol_name << " is undefined.\n";
        return 1;
    }
    int original_start_symbol = symbol_id[start_symbol_name];

    for (int i = 0; i < prod_count; ++i) {
        std::string lhs;
        int len = 0;
        if (!(std::cin >> lhs >> len)) {
            std::cerr << "Failed to read production " << i << ".\n";
            return 1;
        }
        if (!symbol_id.count(lhs)) {
            std::cerr << "Unknown symbol: " << lhs << "\n";
            return 1;
        }
        if (debug_mode) {
            std::cerr << "[debug] production " << i << ": " << lhs << " length "
                      << len << "\n";
        }
        grammar[i].l = symbol_id[lhs];
        grammar[i].len = len;
        grammar[i].r = new int[len];
        for (int j = 0; j < len; ++j) {
            std::string sym;
            if (!(std::cin >> sym)) {
                std::cerr << "Failed to read RHS symbol " << j
                          << " of production " << i << ".\n";
                return 1;
            }
            if (!symbol_id.count(sym)) {
                std::cerr << "Unknown symbol: " << sym << "\n";
                return 1;
            }
            grammar[i].r[j] = symbol_id[sym];
            if (debug_mode) {
                std::cerr << "    [debug] rhs " << j << ": " << sym << "\n";
            }
        }
    }

    int input_len = 0;
    if (!(std::cin >> input_len)) {
        std::cerr << "Failed to read input sequence length.\n";
        return 1;
    }
    std::vector<int> input_sequence;
    for (int i = 0; i < input_len; ++i) {
        std::string sym;
        if (!(std::cin >> sym)) {
            std::cerr << "Failed to read symbol " << i
                      << " of input sequence.\n";
            return 1;
        }
        if (!symbol_id.count(sym)) {
            std::cerr << "Unknown input symbol: " << sym << "\n";
            return 1;
        }
        int id = symbol_id[sym];
        if (!is_terminal[id]) {
            std::cerr << "Input symbol " << sym << " is not a terminal.\n";
            return 1;
        }
        input_sequence.push_back(id);
    }

    int original_symbol_count = terminal_count + non_terminal_count;
    eof_symbol = original_symbol_count;
    symbol_names.push_back("$");
    is_terminal.push_back(1);

    augmented_start_symbol = original_symbol_count + 1;
    symbol_names.push_back(start_symbol_name + "_aug");
    is_terminal.push_back(0);

    symbol_id["$"] = eof_symbol;
    symbol_id[start_symbol_name + "_aug"] = augmented_start_symbol;

    number_of_symb = original_symbol_count + 2;

    augmented_prod_id = prod_count;
    grammar[augmented_prod_id].l = augmented_start_symbol;
    grammar[augmented_prod_id].len = 1;
    grammar[augmented_prod_id].r = new int[1];
    grammar[augmented_prod_id].r[0] = original_start_symbol;

    number_of_prod = prod_count + 1;

    prods_by_left.assign(number_of_symb, {});
    for (int i = 0; i < number_of_prod; ++i) {
        prods_by_left[grammar[i].l].push_back(i);
    }

    compute_first_sets();
    compute_follow_sets();

    build_canonical_collection();
    populate_state_info();
    build_parse_table();

    dump_first_follow();
    dump_states();
    dump_transitions();

    input_sequence.push_back(eof_symbol);
    simulate_parse(input_sequence);

    return 0;
}
