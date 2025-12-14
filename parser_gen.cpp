#include "cfg.hpp"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <iostream>
#include <sstream> // 新增: 用于解析行输入
#include <map>
#include <queue>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

/* 输入: */
int number_of_symb; /* 符号总数 (终结符 + 非终结符 + 增广符号) */
int number_of_prod; /* 产生式总数 (包括增广产生式) */
struct prod grammar[MAX_NUMBER_OF_PROD]; /* 存储所有产生式的数组 */

/* 输出: */
struct state state_info[MAX_NUMBER_OF_STATE]; /* 存储所有状态的信息 (项集) */
struct trans_result trans[MAX_NUMBER_OF_STATE][MAX_NUMBER_OF_SYMB]; /* 状态转移表 (分析表) */

bool show_details = false; // 全局变量：控制是否打印调试表

/**
 * @brief 重载 handler (项) 的小于操作符, 用于std::set 或 std::map。
 */
bool operator<(const handler &a, const handler &b) {
    if (a.prod_id != b.prod_id) {
        return a.prod_id < b.prod_id;
    }
    return a.dot_pos < b.dot_pos;
}

namespace {

/**
 * @brief 用于 std::sort 和 std::map 的项比较结构体。
 */
struct ItemCompare {
    bool operator()(const handler &a, const handler &b) const {
        if (a.prod_id != b.prod_id) {
            return a.prod_id < b.prod_id;
        }
        return a.dot_pos < b.dot_pos;
    }
};

// 定义分析表中的动作类型
constexpr int ACTION_SHIFT = 0;  // 移入
constexpr int ACTION_REDUCE = 1; // 规约
constexpr int ACTION_NONE = -1;  // 无动作 (错误)

/* 内部使用的数据结构 */
std::vector<std::string> symbol_names; // 存储所有符号的名称
std::vector<int> is_terminal; // 标记每个符号是否为终结符 (1: 是, 0: 否)
std::vector<std::vector<int>> prods_by_left; // 按产生式左侧非终结符索引, 存储产生式 ID
std::vector<std::set<int>> first_set;  // 存储每个符号的 FIRST 集
std::vector<std::set<int>> follow_set; // 存储每个非终结符的 FOLLOW 集
std::vector<std::vector<handler>> canonical_states; // 存储所有规范 LR(0) 项集 (状态)
std::vector<std::vector<int>> goto_table; // GOTO 表, goto_table[state_id][symbol_id] = next_state_id

int eof_symbol = -1; // 结束符号 $ 的 ID
int augmented_start_symbol = -1; // 增广开始符号 S' 的 ID
int augmented_prod_id = -1; // 增广产生式 S' -> S 的 ID

/**
 * @brief 将产生式转换为字符串, 用于调试输出。
 */
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

/**
 * @brief 初始化状态转移表 (分析表), 将所有动作设为 ACTION_NONE。
 */
void initialize_transitions(int state_count) {
    for (int i = 0; i < state_count; ++i) {
        for (int j = 0; j < number_of_symb; ++j) {
            trans[i][j].t = ACTION_NONE;
            trans[i][j].id = -1;
        }
    }
}

/**
 * @brief 计算一个 LR(0) 项集的闭包 (closure)。
 */
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

/**
 * @brief 计算状态 state 经过符号 symbol 的 GOTO 集。
 */
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

/**
 * @brief 计算所有符号的 FIRST 集。
 */
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

/**
 * @brief 计算所有非终结符的 FOLLOW 集。
 */
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

/**
 * @brief 确保一个项集 (状态) 存在于 canonical_states 中, 并返回其 ID。
 */
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

/**
 * @brief 构建 LR(0) 规范项集族 (DFA)。
 */
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

/**
 * @brief (调试) 打印所有状态及其项集。
 */
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

/**
 * @brief 将内部的 canonical_states 转换为 cfg.hpp 定义的 state_info 数组。
 */
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

/**
 * @brief 尝试在分析表 (trans) 中设置一个动作。
 */
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

/**
 * @brief 构建 SLR(1) 分析表 (trans)。
 */
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

/**
 * @brief (调试) 打印 FIRST 和 FOLLOW 集。
 */
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

/**
 * @brief (调试) 打印分析表 (trans)。
 */
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

/**
 * @brief 模拟 SLR(1) 分析器处理输入序列。
 * @param input_tokens 输入的终结符序列 (必须以 $ 结尾)。
 */
void simulate_parse(const std::vector<int> &input_tokens) {
    if (input_tokens.empty()) {
        std::cout << "No input sequence provided for simulation.\n";
        return;
    }
    std::cout << "\n=== 移入规约过程 (Shift/Reduce Process) ===\n";
    
    // 栈存储 {state_id, symbol_id}
    // symbol_id 为进入该状态所代表的符号，初始状态无符号用 -1
    std::vector<std::pair<int, int>> stack;
    stack.push_back({0, -1});
    
    size_t position = 0;

    // 辅助lambda：打印当前行
    auto print_current_step = [&]() {
        // 打印栈内容（即左侧已解析部分）
        for (size_t i = 1; i < stack.size(); ++i) { // 跳过初始状态
            std::cout << symbol_names[stack[i].second] << " ";
        }
        // 打印分隔符
        std::cout << "| ";
        // 打印剩余输入（即右侧未解析部分）
        for (size_t i = position; i < input_tokens.size(); ++i) {
            if (input_tokens[i] == eof_symbol) continue; // 不打印末尾的 $
            std::cout << symbol_names[input_tokens[i]] << " ";
        }
        std::cout << "\n";
    };

    while (true) {
        print_current_step();

        if (position >= input_tokens.size()) {
            std::cout << "  [error] Ran out of input symbols (missing $?).\n";
            return;
        }
        int state = stack.back().first;
        int lookahead = input_tokens[position];
        
        const trans_result &entry = trans[state][lookahead];

        if (entry.t == ACTION_SHIFT) {
            // 移入: 压栈 {新状态, 当前输入符号}
            stack.push_back({entry.id, lookahead});
            ++position;
        } else if (entry.t == ACTION_REDUCE) {
            if (entry.id == augmented_prod_id && lookahead == eof_symbol) {
                std::cout << "=== ACCEPT ===\n";
                break;
            }

            const prod &p = grammar[entry.id];
            
            // 规约: 弹出 RHS 长度个状态
            for (int i = 0; i < p.len; ++i) {
                if (!stack.empty()) {
                    stack.pop_back();
                }
            }
            
            if (stack.empty()) {
                std::cout << "  [error] State stack is empty during reduction.\n";
                return;
            }

            // GOTO: 根据栈顶状态和 LHS 符号查找下一个状态
            int top_state = stack.back().first;
            int goto_state = goto_table[top_state][p.l];
            
            if (goto_state == -1) {
                std::cout << "  [error] Missing goto from state "
                          << top_state << " on " << symbol_names[p.l]
                          << "\n";
                return;
            }
            
            // 压入 {GOTO状态, LHS符号}
            stack.push_back({goto_state, p.l});

        } else {
            std::cout << "=== ERROR ===\n";
            return;
        }
    }
}

} // namespace

int main() {
    // std::ios::sync_with_stdio(false);
    // std::cin.tie(nullptr);

    // 交互询问是否显示调试信息
    std::cout << "是否显示调试信息 (FIRST/FOLLOW/表)? (y/n): ";
    char show_choice;
    std::cin >> show_choice;
    if (show_choice == 'y' || show_choice == 'Y') {
        show_details = true;
    }

    std::cout << "请输入上下文无关语法 (CFG) 和待分析序列。\n";
    std::cout << "输入格式:\n";
    std::cout << "1. <终结符数量T> <非终结符数量N> <产生式数量P>\n";
    std::cout << "2. T行: 每行一个终结符名称 (例如: ID, PLUS, ...)\n";
    std::cout << "3. N行: 每行一个非终结符名称 (例如: E, T, F, ...)\n";
    std::cout << "4. 1行: 原始开始符号名称\n";
    std::cout << "5. P行: 每行描述一个产生式 (格式: LHS -> RHS1 RHS2 ...):\n";
    std::cout << "   例如: E -> E PLUS T\n";
    std::cout << "   例如: F -> ID\n";
    std::cout << "6. <待分析序列长度K>\n";
    std::cout << "7. 待分析的终结符序列，终结符请用换行或空格隔开\n";
    std::cout << "---------------------------------\n";

    int terminal_count = 0;
    int non_terminal_count = 0;
    int prod_count = 0;
    if (!(std::cin >> terminal_count >> non_terminal_count >> prod_count)) {
        std::cerr << "错误: 无法读取语法规模 (T N P)。\n";
        return 1;
    }

    symbol_names.clear();
    is_terminal.clear();
    symbol_names.reserve(terminal_count + non_terminal_count + 2);
    is_terminal.reserve(terminal_count + non_terminal_count + 2);

    std::unordered_map<std::string, int> symbol_id;

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
        std::cerr << "错误: 开始符号 " << start_symbol_name
                  << " 未在非终结符中定义。\n";
        return 1;
    }
    int original_start_symbol = symbol_id[start_symbol_name];

    // 消耗换行符，以便后续 getline 正常工作
    std::string dummy_line;
    std::getline(std::cin, dummy_line);

    for (int i = 0; i < prod_count; ++i) {
        std::string line;
        if (!std::getline(std::cin, line)) {
            std::cerr << "错误: 无法读取产生式 " << i << "。\n";
            return 1;
        }

        std::stringstream ss(line);
        std::string lhs, arrow, rhs_sym;
        
        // 读取 LHS 和 "->"
        if (!(ss >> lhs >> arrow)) {
             std::cerr << "错误: 产生式 " << i << " 格式错误 (期望: LHS -> ...)。\n";
             return 1;
        }

        if (!symbol_id.count(lhs)) {
            std::cerr << "错误: 未知符号: " << lhs << "\n";
            return 1;
        }
        
        grammar[i].l = symbol_id[lhs];
        
        // 解析右侧符号
        std::vector<int> rhs_indices;
        while (ss >> rhs_sym) {
            if (!symbol_id.count(rhs_sym)) {
                std::cerr << "错误: 未知符号: " << rhs_sym << "\n";
                return 1;
            }
            rhs_indices.push_back(symbol_id[rhs_sym]);
        }
        
        grammar[i].len = static_cast<int>(rhs_indices.size());
        grammar[i].r = new int[grammar[i].len];
        for (int k = 0; k < grammar[i].len; ++k) {
            grammar[i].r[k] = rhs_indices[k];
        }
    }

    int input_len = 0;
    if (!(std::cin >> input_len)) {
        std::cerr << "错误: 无法读取输入序列长度。\n";
        return 1;
    }
    std::vector<int> input_sequence;
    for (int i = 0; i < input_len; ++i) {
        std::string sym;
        if (!(std::cin >> sym)) {
            std::cerr << "错误: 无法读取输入序列的第 " << i << " 个符号。\n";
            return 1;
        }
        if (!symbol_id.count(sym)) {
            std::cerr << "错误: 未知的输入符号: " << sym << "\n";
            return 1;
        }
        int id = symbol_id[sym];
        if (!is_terminal[id]) {
            std::cerr << "错误: 输入符号 " << sym << " 不是终结符。\n";
            return 1;
        }
        input_sequence.push_back(id);
    }

    // 后续构建逻辑保持不变
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

    if (show_details) {
        dump_first_follow();
        dump_states();
        dump_transitions();
    }

    input_sequence.push_back(eof_symbol);
    simulate_parse(input_sequence);

    return 0;
}