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

`lean-toolchain` 指定 Lean 版本，已提交的 `lake-manifest.json` 固定依赖 revision。复现构建时保留这两个文件；只有主动升级依赖时才运行 `lake update`。

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) 在推送或提交拉取请求到 `main` 时运行 `lake build --wfail`，也支持手动触发。工作流下载 Mathlib 编译缓存、从源码构建 QFixLean，在出现构建警告（包括 `sorry` 警告）时失败，并检查公开导入列表完整、依赖版本文件未被改动。所用 Actions 固定到 commit。这些检查用于补充定理与公理审查，不能代替审查。

使用 `import QFixLean` 导入公开库。新增模块后运行 `lake exe mk_all --lib QFixLean` 更新自动生成的库入口。本地复现 CI 检查时，依次运行 `lake build --wfail`、`lake exe mk_all --check --lib QFixLean` 和 `git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json`。

主表示采用复内积空间上的连续线性算符，有限维例子使用 `EuclideanSpace`。当前已提供[归一化纯态](QFixLean/Basic/State.lean)与[酉作用](QFixLean/Basic/Unitary.lean)接口，包含内积保持、复合及伴随或逆操作恢复原态的证明。[精确量子比特例子](QFixLean/Examples/Qubit.lean)覆盖计算基态、叠加态 `(3/5, 4/5)` 和 Pauli X。

[投影接口](QFixLean/Basic/Projection.lean)支持一般目标子空间、正交补投影和归一化源态的秩一投影。对正交投影，[测量权重](QFixLean/Basic/Probability.lean)之和等于输入的平方范数；归一化时，它们是 `[0,1]` 内的概率。复内积桥接与全局相位不变性将这些权重连接到向量运算。[精确测量例子](QFixLean/Examples/Measurement.lean)包含成功率、失败率为 `9/25`、`16/25` 的量子比特，以及三维中保留两个坐标的目标。

库中还已证明[选择性相位的代数性质与酉性](QFixLean/Basic/Phase.lean)，以及[符号化单步展开](QFixLean/PiOverThree/Step.lean)和 π/3 所需的标量消去恒等式。完整相位重叠与失败概率的连接、指数相位的具体代入及完整搜索算法证明仍待完成。测量接口目前覆盖二结果投影测量的概率；混态、POVM 和测后态更新不在该接口范围内。
