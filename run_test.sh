#!/bin/bash

# 定义目录和文件名
TEST_DIR="test"
OUTPUT_DIR="output" # 新增：定义输出目录
EXECUTABLE="parser_gen"
EXECUTABLE_PATH="${OUTPUT_DIR}/${EXECUTABLE}" # 新增：定义可执行文件的完整路径

echo "--- 准备测试环境 ---"

# 创建测试目录
if [ ! -d "$TEST_DIR" ]; then
    mkdir -p "$TEST_DIR"
    echo "创建目录: ${TEST_DIR}"
fi

# 创建输出目录
if [ ! -d "$OUTPUT_DIR" ]; then
    mkdir -p "$OUTPUT_DIR"
    echo "创建输出目录: ${OUTPUT_DIR}"
fi

# 将测试数据移动或复制到测试目录
# 假设 test_grammar.txt 在当前目录下，并移动到 test/
if [ -f "test_grammar.txt" ]; then
    # 注意：这里确保文件被命名为 test_grammar.txt
    mv test_grammar.txt "${TEST_DIR}/test_grammar.txt"
    echo "将 test_grammar.txt 移动到 ${TEST_DIR}/"
fi

# --- 编译 C++ 程序 ---
# 假设你已安装 g++ 编译器
echo "正在编译 parser_gen.cpp..."
# 将可执行文件输出到 output/ 目录
g++ -std=c++17 -o "$EXECUTABLE_PATH" parser_gen.cpp

# 检查编译是否成功
if [ $? -ne 0 ]; then
    echo "编译失败！请检查 g++ 是否已安装以及代码是否存在错误。"
    exit 1
fi

echo "编译成功。可执行文件为: ${EXECUTABLE_PATH}"
echo ""

# --- 运行所有测试 ---
echo "--- 正在运行 ${TEST_DIR} 目录下的所有测试文件 (*.txt) ---"
TEST_COUNT=0
SUCCESS_COUNT=0

# 遍历 test/ 目录下所有以 .txt 结尾的文件
for GRAMMAR_FILE in ${TEST_DIR}/*.txt; do
    # 检查是否有匹配的文件（如果 test/ 目录为空，可能会匹配到字面量 "*.txt"）
    if [ ! -f "$GRAMMAR_FILE" ]; then
        echo "未找到任何测试文件 (期待 *.txt 文件)。请确保 test/ 目录下有测试数据。"
        break
    fi

    TEST_COUNT=$((TEST_COUNT + 1))
    
    # 提取文件名（不带路径和扩展名），例如 test/case1.txt -> case1
    BASE_NAME=$(basename "$GRAMMAR_FILE" .txt)
    # 定义输出文件名，现在位于 output/ 目录下
    OUTPUT_FILE="${OUTPUT_DIR}/${BASE_NAME}_output.txt"
    
    echo ""
    echo "=================================================="
    echo "运行测试: ${GRAMMAR_FILE}"
    
    # 执行程序，使用 output/parser_gen 运行，输出到 output/case1_output.txt
    "$EXECUTABLE_PATH" < "$GRAMMAR_FILE" > "$OUTPUT_FILE"

    # 检查运行是否成功
    if [ $? -ne 0 ]; then
        echo "程序运行失败！(返回非零退出码)"
        echo "--------------------------------------------------"
        continue
    fi
    
    SUCCESS_COUNT=$((SUCCESS_COUNT + 1))

    echo "程序运行完毕。输出保存到 ${OUTPUT_FILE}。"

    # --- 显示部分关键输出 ---
    echo ""
    echo "--- [${OUTPUT_FILE}] 移入规约过程模拟 ---"
    # 显示 "Parse simulation:" 及其后的所有行
    grep -A 100 "Parse simulation:" "$OUTPUT_FILE"
    echo "=================================================="

done

echo ""
echo "--- 测试总结 ---"
echo "总测试文件数量: ${TEST_COUNT}"
echo "成功运行数量: ${SUCCESS_COUNT}"
echo "所有输出文件和可执行文件都已生成到 /${OUTPUT_DIR} 目录中。"