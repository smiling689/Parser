cmake_minimum_required(VERSION 3.10)

# 项目名称
project(ParserGenerator)

# 设置 C++ 标准 (推荐使用 C++17 或更高)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ==========================================
# 关键配置：设置输出目录
# ==========================================
# 将可执行文件的输出路径设置为项目根目录下的 output 文件夹
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/output)

# ==========================================
# 添加源文件
# ==========================================
set(SOURCE_FILES
    parser_gen.cpp
    cfg.hpp
)

# 生成可执行文件
# 可执行文件名为 parser_gen (在该配置下会自动生成到 output/parser_gen)
add_executable(parser_gen ${SOURCE_FILES})

# (可选) 添加编译器警告，有助于发现潜在 bug
if(MSVC)
    target_compile_options(parser_gen PRIVATE /W4)
else()
    target_compile_options(parser_gen PRIVATE -Wall -Wextra)
endif()