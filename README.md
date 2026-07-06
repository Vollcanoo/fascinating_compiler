# fascinating_compiler

ToyC 语言编译器，使用 OCaml 5.3 + Dune 3.19 实现，将 ToyC 源程序编译为 RISC-V32 汇编。

## 项目结构

```
fascinating_compiler/
├── bin/                 # 编译器入口（stdin → stdout）
├── lib/
│   ├── ast/             # 抽象语法树定义
│   ├── frontend/        # 词法分析 + 语法分析
│   ├── analysis/        # 语义分析
│   └── backend/         # IR、优化、RISC-V32 代码生成
├── examples/            # ToyC 示例程序 (*.tc)
└── test/                # 单元测试
```

## 构建

```bash
dune build
```

## 使用

```bash
# 基本编译
dune exec fascinating_compiler < examples/hello.tc > output.s

# 开启优化
dune exec fascinating_compiler -- -opt < examples/hello.tc > output.s
```

## 编译流水线

```
stdin → Lexer → Parser → AST → Semantic → IR → Optimize → Codegen → stdout
```
