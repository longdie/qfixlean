# QFixLean：固定点量子搜索的 Lean 形式化

[English](README.md)

QFixLean 是 **上海交通大学量子科学计算课程（2026 年秋季学期）** 的课程项目。

固定点量子搜索旨在解决普通 Grover 搜索中的过冲问题。我们希望通过这一主题加深对量子算法的理解，并探索如何使用 Lean 明确算法的假设与正确性保证，使其接受机器检查。

项目计划使用 **Lean 4 和 Mathlib**。基础目标是先形式化课程中的量子基础知识（量子态、酉变换、投影测量与相位操作），再完成对 [Grover 于 2005 年提出的 π/3 固定点搜索算法](https://arxiv.org/abs/quant-ph/0503205)的形式化。拓展目标是尝试形式化 [Yoder、Low 和 Chuang 于 2014 年提出的固定点振幅放大算法](https://arxiv.org/abs/1409.3305)，其完成情况将取决于项目进度。

我们希望为量子科学计算与 Lean 形式化社区贡献可复用的定义和证明，逐步积累服务于量子算法学习与验证的基础设施。

项目固定使用 **Lean 4.35.0** 和 **Mathlib v4.35.0**。安装 [elan](https://github.com/leanprover/elan) 后，在仓库目录运行：

```sh
lake exe cache get
lake build
```

当前代码提供工程骨架与数学依赖导入，量子定义及算法证明仍待开展。
