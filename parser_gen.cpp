#include "cfg.hpp" // 引入上下文无关语法相关的数据结构定义

#include <algorithm> // 包含
#include <cctype>    // 包含
#include <cstdlib>   // 包含
#include <iostream>  // 包含输入输出流
#include <map>       // 包含 map 容器
#include <queue>     // 包含队列容器
#include <set>       // 包含集合容器
#include <string>    // 包含字符串处理
#include <unordered_map> // 包含哈希表
#include <utility>   // 包含
#include <vector>    // 包含动态数组

/*
 * 以下是 cfg.hpp 中定义的, 用于外部交互的全局变量
 */

/* 输入: */
int number_of_symb; /* 符号总数 (终结符 + 非终结符 + 增广符号) */
int number_of_prod; /* 产生式总数 (包括增广产生式) */
struct prod grammar[MAX_NUMBER_OF_PROD]; /* 存储所有产生式的数组 */

/* 输出: */
struct state state_info[MAX_NUMBER_OF_STATE]; /* 存储所有状态的信息 (项集) */
struct trans_result trans[MAX_NUMBER_OF_STATE][MAX_NUMBER_OF_SYMB]; /* 状态转移表 (分析表) */

/**
 * @brief 重载 handler (项) 的小于操作符, 用于
 * std::set 或 std::map。
 */
bool operator<(const handler &a, const handler &b) {
    if (a.prod_id != b.prod_id) {
        return a.prod_id < b.prod_id;
    }
    return a.dot_pos < b.dot_pos;
}

namespace { // 使用匿名命名空间封装内部实现细节

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

/*
 * 以下是生成器内部使用的数据结构
 */

std::vector<std::string> symbol_names; // 存储所有符号的名称 (用于调试输出)
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
 * @param prod_id 产生式 ID。
 * @param dot_pos "点" 的位置 (-1 表示不显示点)。
 * @return 格式化后的字符串。
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
 * @param state_count 状态总数。
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
 * @param items 初始项集 (核)。
 * @return 包含所有闭包项的完整项集。
 */
std::vector<handler> closure(const std::vector<handler> &items) {
    std::vector<handler> result; // 存储最终的闭包项集
    std::queue<handler> q; // 工作队列
    std::set<std::pair<int, int>> seen; // 记录已处理过的项, 避免重复

    // 将所有核项加入队列
    for (const handler &it : items) {
        q.push(it);
    }

    while (!q.empty()) {
        handler cur = q.front();
        q.pop();

        // 检查是否已处理过
        auto key = std::make_pair(cur.prod_id, cur.dot_pos);
        if (!seen.insert(key).second) {
            continue; // 如果已处理, 跳过
        }

        // 将当前项加入结果集
        result.push_back(cur);
        const prod &p = grammar[cur.prod_id];

        // 如果点已在末尾, 无法扩展
        if (cur.dot_pos >= p.len) {
            continue;
        }

        // 获取点之后的符号
        int sym = p.r[cur.dot_pos];

        // 如果点后面是终结符, 无法扩展
        if (is_terminal[sym]) {
            continue;
        }

        // 如果点后面是非终结符 B, 将 B 的所有产生式 B -> .γ 加入队列
        for (int prod_id : prods_by_left[sym]) {
            handler nxt{prod_id, 0}; // B -> .γ
            if (seen.find(std::make_pair(nxt.prod_id, nxt.dot_pos)) ==
                seen.end()) {
                q.push(nxt); // 加入队列等待处理
            }
        }
    }
    // 对结果进行排序, 确保项集比较的一致性
    std::sort(result.begin(), result.end(), ItemCompare());
    return result;
}

/**
 * @brief 计算状态 state 经过符号 symbol 的 GOTO 集。
 * @param state 
 * @param symbol 
 * @return GOTO(state, symbol) 对应的项集 (已计算闭包)。
 */
std::vector<handler> goto_set(const std::vector<handler> &state, int symbol) {
    std::vector<handler> moved; // 存储所有 A -> αX.β 形式的项
    for (const handler &it : state) {
        const prod &p = grammar[it.prod_id];
        // 检查项是否为 A -> α.Xβ 且 X == symbol
        if (it.dot_pos < p.len && p.r[it.dot_pos] == symbol) {
            // 将点右移, 得到 A -> αX.β
            moved.push_back(handler{it.prod_id, it.dot_pos + 1});
        }
    }
    if (moved.empty()) {
        return {}; // 如果没有可转移的项, 返回空集
    }
    // 对 GOTO 后的项集求闭包
    return closure(moved);
}

/**
 * @brief 计算所有符号的 FIRST 集。
 * * 算法:
 * 1. 对所有终结符 X, FIRST(X) = {X}。
 * 2. 对所有非终结符, FIRST(A) = {}。
 * 3. 循环直到 FIRST 集不再变化:
 * - 对每个产生式 A -> Y...:
 * - 将 FIRST(Y) 中的所有终结符加入 FIRST(A)。
 * - (本实现简化了, 没处理 epsilon 和 Y1Y2... 的情况,
 * 仅处理了 A -> Y... 的情况, 假设 Y 是终结符或 FIRST(Y)
 * 不含 epsilon)
 */
void compute_first_sets() {
    first_set.assign(number_of_symb, {});
    // 1. 终结符的 FIRST 集是其自身
    for (int i = 0; i < number_of_symb; ++i) {
        if (is_terminal[i]) {
            first_set[i].insert(i);
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        // 遍历所有产生式 A -> Y...
        for (int i = 0; i < number_of_prod; ++i) {
            const prod &p = grammar[i];
            if (p.len == 0) { // 忽略 A -> ε (虽然题目假设非空)
                continue;
            }
            int sym = p.r[0]; // Y
            // 3. 将 FIRST(Y) 加入 FIRST(A)
            for (int token : first_set[sym]) {
                if (!first_set[p.l].count(token)) {
                    first_set[p.l].insert(token);
                    changed = true; // 标记 FIRST 集发生变化
                }
            }
        }
    }
}

/**
 * @brief 计算所有非终结符的 FOLLOW 集。
 *
 * 算法:
 * 1. 将 $ (EOF) 加入 FOLLOW(S') (S'
 * 是增广开始符号)。
 * 2. 循环直到 FOLLOW 集不再变化:
 * - 对每个产生式 A -> αBβ:
 * - 将 FIRST(β) (不含
 * ε) 加入 FOLLOW(B)。
 * - 对每个产生式 A -> αB, 或 A -> αBβ
 * 且 FIRST(β) 含 ε:
 * - 将 FOLLOW(A) 加入 FOLLOW(B)。
 *
 * (本实现简化了对 ε 的处理, 仅实现了以下规则)
 */
void compute_follow_sets() {
    follow_set.assign(number_of_symb, {});
    // 1. 将 $ 加入 FOLLOW(S')
    if (augmented_start_symbol >= 0 && eof_symbol >= 0) {
        follow_set[augmented_start_symbol].insert(eof_symbol);
    }

    bool changed = true;
    while (changed) {
        changed = false;
        // 遍历所有产生式
        for (int i = 0; i < number_of_prod; ++i) {
            const prod &p = grammar[i];
            // 2a. 规则 A -> αBβ
            // (简化: 仅考虑 A -> ...BY... , Y 是 β 的第一个符号)
            for (int j = 0; j < p.len - 1; ++j) {
                int cur_sym = p.r[j];   // B
                int next_sym = p.r[j + 1]; // Y
                if (is_terminal[cur_sym]) {
                    continue; // B 必须是非终结符
                }
                // 将 FIRST(Y) 加入 FOLLOW(B)
                for (int token : first_set[next_sym]) {
                    if (!follow_set[cur_sym].count(token)) {
                        follow_set[cur_sym].insert(token);
                        changed = true;
                    }
                }
            }

            // 2b. 规则 A -> αB
            if (p.len == 0) {
                continue;
            }
            int last_sym = p.r[p.len - 1]; // B
            if (is_terminal[last_sym]) {
                continue; // B 必须是非终结符
            }
            // 将 FOLLOW(A) 加入 FOLLOW(B)
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
 * @brief 辅助函数: 确保一个项集 (状态) 存在于
 * canonical_states 中, 并返回其 ID。
 * @param items 项集。
 * @param state_id 
 * @return 状态 ID。
 */
int ensure_state(const std::vector<handler> &items,
                 std::map<std::vector<handler>, int> &state_id) {
    // 查找该项集是否已存在
    auto it = state_id.find(items);
    if (it != state_id.end()) {
        return it->second; // 已存在, 返回 ID
    }
    // 不存在, 创建新状态
    int id = static_cast<int>(canonical_states.size());
    canonical_states.push_back(items); // 加入状态列表
    state_id[items] = id; // 记录映射
    return id;
}

/**
 * @brief 构建 LR(0) 规范项集族 (DFA)。
 */
void build_canonical_collection() {
    canonical_states.clear();
    goto_table.clear();
    // 存储项集到状态 ID 的映射
    std::map<std::vector<handler>, int> state_id;

    // 1. 计算初始状态 I0 = closure({S' -> .S})
    std::vector<handler> start_items = closure({handler{augmented_prod_id, 0}});
    int start_state = ensure_state(start_items, state_id);

    // 2. 使用广度优先搜索 (BFS) 构建 DFA
    std::queue<int> q;
    q.push(start_state);
    goto_table.resize(1); // 初始化 GOTO 表
    goto_table[0].assign(number_of_symb, -1);

    while (!q.empty()) {
        int cur_state = q.front();
        q.pop();

        // 确保 GOTO 表足够大
        if (static_cast<int>(goto_table.size()) <= cur_state) {
            goto_table.resize(cur_state + 1,
                              std::vector<int>(number_of_symb, -1));
        }

        // 查找当前状态所有可能的 GOTO 符号
        std::set<int> seen_symbols;
        for (const handler &item : canonical_states[cur_state]) {
            const prod &p = grammar[item.prod_id];
            if (item.dot_pos >= p.len) {
                continue; // 点在末尾, 无法转移
            }
            seen_symbols.insert(p.r[item.dot_pos]); // 记录点后的符号
        }

        // 3. 对每个符号 X, 计算 GOTO(I, X)
        for (int sym : seen_symbols) {
            // 计算 GOTO 集
            std::vector<handler> dest_items =
                goto_set(canonical_states[cur_state], sym);
            if (dest_items.empty()) {
                continue;
            }
            // 确保 GOTO 目标状态存在, 并获取其 ID
            int dest_id = ensure_state(dest_items, state_id);

            // 确保 GOTO 表大小
            if (static_cast<int>(goto_table.size()) <= dest_id) {
                goto_table.resize(dest_id + 1,
                                  std::vector<int>(number_of_symb, -1));
            }
            if (static_cast<int>(goto_table[cur_state].size()) <
                number_of_symb) {
                goto_table[cur_state].resize(number_of_symb, -1);
            }

            // 4. 记录转移: GOTO[cur_state][sym] = dest_id
            goto_table[cur_state][sym] = dest_id;

            // 5. 如果是新状态, 加入 BFS 队列
            // (这里的判断条件 dest_id >= ... - 1
            // 似乎是为了确保只添加刚创建的状态)
            if (dest_id >= static_cast<int>(canonical_states.size()) - 1) {
                q.push(dest_id);
            }
        }
    }

    // 调整 GOTO 表大小, 确保所有状态都有条目
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
 * @brief 将内部的 canonical_states 转换为 cfg.hpp
 * 定义的 state_info 数组。
 */
void populate_state_info() {
    for (size_t i = 0; i < canonical_states.size(); ++i) {
        state_info[i].size = static_cast<int>(canonical_states[i].size());
        // 动态分配内存, 匹配 cfg.hpp 中的 struct state
        // (注意: 这里 new
        // 出来的内存没有在程序中 delete, 存在内存泄漏)
        handler *arr = new handler[state_info[i].size];
        for (int j = 0; j < state_info[i].size; ++j) {
            arr[j] = canonical_states[i][j];
        }
        state_info[i].s = arr;
    }
}

/**
 * @brief 尝试在分析表 (trans) 中设置一个动作。
 * @return true 如果设置成功, false 如果发生冲突。
 */
bool set_action(int state, int symbol, int type, int id) {
    trans_result &entry = trans[state][symbol];
    if (entry.t == ACTION_NONE) {
        // 动作为空, 直接设置
        entry.t = type;
        entry.id = id;
        return true;
    }
    // 如果已存在相同动作, 忽略
    if (entry.t == type && entry.id == id) {
        return true;
    }
    // 发生冲突 (移入/规约 或 规约/规约)
    std::cerr << "Conflict detected in state " << state << " on symbol "
              << symbol_names[symbol] << ".\n";
    // (可以进一步打印冲突详情)
    return false;
}

/**
 * @brief 构建 SLR(1) 分析表 (trans)。
 */
void build_parse_table() {
    int state_count = static_cast<int>(canonical_states.size());
    initialize_transitions(state_count); // 初始化分析表

    // 遍历所有状态
    for (int state = 0; state < state_count; ++state) {
        // 遍历状态中的所有项
        for (const handler &item : canonical_states[state]) {
            const prod &p = grammar[item.prod_id];
            
            // 规则 1: 移入 (Shift)
            // 如果项是 [A -> α.aβ] (a 是终结符), 且 GOTO(I, a) = J
            if (item.dot_pos < p.len) {
                int sym = p.r[item.dot_pos]; // a
                if (!is_terminal[sym]) {
                    continue; // 必须是终结符
                }
                int dest = goto_table[state][sym]; // J
                if (dest != -1) {
                    // ACTION[state][a] = SHIFT J
                    set_action(state, sym, ACTION_SHIFT, dest);
                }
            } 
            // 规则 2: 规约 (Reduce)
            // 如果项是 [A -> α.] (A != S')
            else {
                int lhs = p.l; // A
                // 获取 A 的 FOLLOW 集
                const std::set<int> &lookahead = follow_set[lhs];
                // 对 FOLLOW(A) 中的每个终结符 a
                for (int la : lookahead) {
                    // ACTION[state][a] = REDUCE A -> α
                    set_action(state, la, ACTION_REDUCE, item.prod_id);
                }
            }
            // 规则 3: 接受 (Accept)
            // 在 SLR(1) 中, 接受动作 [S' -> S.]
            // 隐含在规则 2 中 (当 item.prod_id ==
            // augmented_prod_id 且 lookahead == eof_symbol 时)
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
            continue; // 只显示非终结符的 FIRST 集
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
            continue; // 只显示非终结符的 FOLLOW 集
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
                continue; // 只显示终结符的动作
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
    std::cout << "Parse simulation:\n";
    std::vector<int> stack; // 状态栈
    stack.push_back(0); // 初始状态 0
    size_t position = 0; // 输入指针
    int step = 0;

    while (true) {
        if (position >= input_tokens.size()) {
            std::cout << "  [error] Ran out of input symbols (missing $?).\n";
            return;
        }
        int state = stack.back(); // 栈顶状态
        int lookahead = input_tokens[position]; // 当前输入符号
        
        // 查询分析表
        const trans_result &entry = trans[state][lookahead];

        // 动作: 移入
        if (entry.t == ACTION_SHIFT) {
            std::cout << "  Step " << step++ << ": shift "
                      << symbol_names[lookahead] << ", goto state " << entry.id
                      << "\n";
            stack.push_back(entry.id); // 新状态入栈
            ++position; // 消耗输入
        } 
        // 动作: 规约
        else if (entry.t == ACTION_REDUCE) {
            
            // 接受: 当规约 S' -> S 且 展望符为 $
            if (entry.id == augmented_prod_id && lookahead == eof_symbol) {
                std::cout << "  Step " << step++ << ": accept\n";
                break; // 分析成功
            }

            const prod &p = grammar[entry.id]; // 获取规约用的产生式 A -> β
            std::cout << "  Step " << step++ << ": reduce "
                      << production_to_string(entry.id) << "\n";
            
            // 弹出 |β| 个状态
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

            // 规约后, 栈顶状态为 S, 查询 GOTO(S, A)
            int goto_state = goto_table[stack.back()][p.l];
            if (goto_state == -1) {
                std::cout << "  [error] Missing goto from state "
                          << stack.back() << " on " << symbol_names[p.l]
                          << "\n";
                return;
            }
            // GOTO 状态入栈
            stack.push_back(goto_state);
        } 
        // 动作: 错误
        else {
            std::cout << "  [error] No valid action at state " << state
                      << " on symbol " << symbol_names[lookahead] << "\n";
            return; // 分析失败
        }
    }
}

} // namespace

int main() {
    // 优化 C++ iostream 性能
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    // 检查是否设置了调试模式环境变量 (例如: export PARSER_DEBUG=1)
    const bool debug_mode = std::getenv("PARSER_DEBUG") != nullptr;

    // --- 输入格式提示 (新增) ---
    std::cout << "--- SLR(1) Parser Generator ---\n";
    std::cout << "请输入上下文无关语法 (CFG) 和待分析序列。\n";
    std::cout << "输入格式:\n";
    std::cout << "1. <终结符数量T> <非终结符数量N> <产生式数量P>\n";
    std::cout << "2. T行: 每行一个终结符名称 (例如: ID, PLUS, ...)\n";
    std::cout << "3. N行: 每行一个非终结符名称 (例如: E, T, F, ...)\n";
    std::cout
        << "4. 1行: 原始开始符号名称 (必须在 N 中定义过, 例如: E)\n";
    std::cout << "5. P行: 每行描述一个产生式:\n";
    std::cout
        << "   <左侧符号LHS> <右侧符号数量K> [K个右侧符号RHS ...]\n";
    std::cout << "   例如: E 3 E PLUS T\n";
    std::cout << "   例如: F 1 ID\n";
    std::cout << "6. <待分析序列长度K>\n";
    std::cout << "7. K行: 每行一个待分析的终结符 (来自 T)\n";
    std::cout << "---------------------------------\n";
    std::cout << "请输入:\n";
    // --- 提示结束 ---

    int terminal_count = 0;
    int non_terminal_count = 0;
    int prod_count = 0; // 原始产生式数量
    if (!(std::cin >> terminal_count >> non_terminal_count >> prod_count)) {
        std::cerr << "错误: 无法读取语法规模 (T N P)。\n";
        return 1;
    }

    symbol_names.clear();
    is_terminal.clear();
    symbol_names.reserve(terminal_count + non_terminal_count + 2);
    is_terminal.reserve(terminal_count + non_terminal_count + 2);

    // 符号到 ID 的映射
    std::unordered_map<std::string, int> symbol_id;
    symbol_id.reserve(terminal_count + non_terminal_count + 2);

    // 1. 读取终结符
    for (int i = 0; i < terminal_count; ++i) {
        std::string name;
        std::cin >> name;
        symbol_id[name] = static_cast<int>(symbol_names.size());
        symbol_names.push_back(name);
        is_terminal.push_back(1);
    }
    // 2. 读取非终结符
    for (int i = 0; i < non_terminal_count; ++i) {
        std::string name;
        std::cin >> name;
        symbol_id[name] = static_cast<int>(symbol_names.size());
        symbol_names.push_back(name);
        is_terminal.push_back(0);
    }

    // 3. 读取原始开始符号
    std::string start_symbol_name;
    std::cin >> start_symbol_name;
    if (!symbol_id.count(start_symbol_name)) {
        std::cerr << "错误: 开始符号 " << start_symbol_name
                  << " 未在非终结符中定义。\n";
        return 1;
    }
    int original_start_symbol = symbol_id[start_symbol_name];

    // 4. 读取 P 个产生式
    for (int i = 0; i < prod_count; ++i) {
        std::string lhs;
        int len = 0;
        if (!(std::cin >> lhs >> len)) {
            std::cerr << "错误: 无法读取产生式 " << i << " (LHS len)。\n";
            return 1;
        }
        if (!symbol_id.count(lhs)) {
            std::cerr << "错误: 未知符号: " << lhs << "\n";
            return 1;
        }
        if (debug_mode) {
            std::cerr << "[debug] production " << i << ": " << lhs << " length "
                      << len << "\n";
        }
        grammar[i].l = symbol_id[lhs];
        grammar[i].len = len;
        // (注意: 假设 cfg.hpp 保证 MAX_NUMBER_OF_PROD 足够大)
        grammar[i].r = new int[len]; // (存在内存泄漏风险)
        for (int j = 0; j < len; ++j) {
            std::string sym;
            if (!(std::cin >> sym)) {
                std::cerr << "错误: 无法读取产生式 " << i << " 的第 " << j
                          << " 个 RHS 符号。\n";
                return 1;
            }
            if (!symbol_id.count(sym)) {
                std::cerr << "错误: 未知符号: " << sym << "\n";
                return 1;
            }
            grammar[i].r[j] = symbol_id[sym];
            if (debug_mode) {
                std::cerr << "    [debug] rhs " << j << ": " << sym << "\n";
            }
        }
    }

    // 5. 读取待分析序列
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

    // --- 语法增广 ---
    // 原始符号数量
    int original_symbol_count = terminal_count + non_terminal_count;

    // 添加 EOF 符号 $
    eof_symbol = original_symbol_count;
    symbol_names.push_back("$");
    is_terminal.push_back(1);

    // 添加 增广开始符号 S'
    augmented_start_symbol = original_symbol_count + 1;
    symbol_names.push_back(start_symbol_name + "_aug");
    is_terminal.push_back(0);

    symbol_id["$"] = eof_symbol;
    symbol_id[start_symbol_name + "_aug"] = augmented_start_symbol;

    // 更新符号总数
    number_of_symb = original_symbol_count + 2;

    // 添加 增广产生式 S' -> S
    augmented_prod_id = prod_count; // ID 为 P
    grammar[augmented_prod_id].l = augmented_start_symbol;
    grammar[augmented_prod_id].len = 1;
    grammar[augmented_prod_id].r = new int[1]; // (内存泄漏)
    grammar[augmented_prod_id].r[0] = original_start_symbol;

    // 更新产生式总数
    number_of_prod = prod_count + 1;
    // --- 增广结束 ---

    // 预处理: 构建按 LHS 索引产生式的列表
    prods_by_left.assign(number_of_symb, {});
    for (int i = 0; i < number_of_prod; ++i) {
        prods_by_left[grammar[i].l].push_back(i);
    }

    // --- 执行分析器生成 ---
    compute_first_sets();
    compute_follow_sets();
    build_canonical_collection();
    populate_state_info(); // 填充要输出的 state_info
    build_parse_table();   // 填充要输出的 trans

    // --- 输出结果 ---
    dump_first_follow();
    dump_states();
    dump_transitions();

    // --- 执行分析模拟 ---
    input_sequence.push_back(eof_symbol); // 在输入末尾添加 $
    simulate_parse(input_sequence);

    // (注意: 程序未释放 new
    // 出来的内存, 在实际应用中应添加清理逻辑)
    return 0;
}