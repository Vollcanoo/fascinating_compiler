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
│   └── backend/
│       ├── ir.ml        # 三地址码 IR + AST 下降
│       ├── cfg.ml       # 指令级控制流图、支配关系、自然循环
│       ├── liveness.ml  # 活跃变量分析
│       ├── optimize.ml  # 优化流水线
│       ├── target.ml    # RISC-V 立即数编码规则（优化器与后端共用）
│       ├── regalloc.ml  # 图着色寄存器分配
│       └── codegen.ml   # RISC-V32 指令选择与发射
├── examples/            # ToyC 示例程序 (*.tc)
└── test/
    ├── cases/           # 端到端回归程序
    ├── bench/           # 性能基准程序
    └── regress/         # 回归驱动 + RV32IM 模拟器 + 参考解释器
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
stdin → Lexer → Parser → AST → Semantic → IR → Optimize → Regalloc → Codegen → stdout
```

## 测试

```bash
dune test
```

包含三部分：

- 词法/语法/语义单元测试；
- 后端不变式检查（跨回边的活跃值不共用寄存器、参数入口拷贝互不覆盖、
  叶子函数不建栈帧、比较被折进分支、`-opt` 不删除全局副作用）；
- `test/cases/` 下的端到端回归：每个程序分别以 `-O0` 和 `-opt` 编译，在
  `test/regress/rv32.ml` 的 RV32IM 模拟器上执行，结果与 `test/regress/interp.ml`
  这个独立的 AST 参考解释器比对。同时报告**实际退休指令数**。

基准程序不在 `dune test` 里（跑得比较久），单独运行：

```bash
dune exec test/regress/regress.exe -- test/bench
```

模拟器和参考解释器仅供测试使用，`lib/` 与 `bin/` 都不依赖它们。

## 优化

见 [docs/optimization-policy.md](docs/optimization-policy.md)。
