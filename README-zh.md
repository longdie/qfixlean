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

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) 在推送或提交拉取请求到 `main` 时运行 `lake build --wfail`，也支持手动触发。工作流下载 Mathlib 编译缓存、从源码构建 QFixLean，在出现构建警告（包括 `sorry` 警告）时失败，并检查公开导入列表完整、依赖版本文件未被改动。[公理审查程序](scripts/CheckAxioms.lean)检查项目模块中声明的传递依赖，只允许 `propext`、`Classical.choice` 和 `Quot.sound`；出现其他公理则检查失败。所用 Actions 固定到 commit。这些检查用于补充对定理陈述、假设及其算法对应关系的审查。

使用 `import QFixLean` 导入公开库。新增模块后运行 `lake exe mk_all --lib QFixLean` 更新自动生成的库入口。本地复现 CI 检查时，依次运行 `lake build --wfail`、`lake exe mk_all --check --lib QFixLean`、`lake env lean -DwarningAsError=true scripts/CheckAxioms.lean` 和 `git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json`。

主表示采用复内积空间上的连续线性算符，有限维例子使用 `EuclideanSpace`。当前已提供[归一化纯态](QFixLean/Basic/State.lean)与[酉作用](QFixLean/Basic/Unitary.lean)接口，包含内积保持、复合及伴随或逆操作恢复原态的证明。[精确量子比特例子](QFixLean/Examples/Qubit.lean)覆盖计算基态、叠加态 `(3/5, 4/5)` 和 Pauli X。

[投影接口](QFixLean/Basic/Projection.lean)支持一般目标子空间、正交补投影和归一化源态的秩一投影。对正交投影，[测量权重](QFixLean/Basic/Probability.lean)之和等于输入的平方范数；归一化时，它们是 `[0,1]` 内的概率。复内积桥接与全局相位不变性将这些权重连接到向量运算。[精确测量例子](QFixLean/Examples/Measurement.lean)包含成功率、失败率为 `9/25`、`16/25` 的量子比特，以及三维中保留两个坐标的目标。

[选择性相位接口](QFixLean/Basic/Phase.lean)已包含目标与补分量作用、同一目标的测量权重不变性，以及用成功/失败权重表达的内积重叠公式。[实角度相位](QFixLean/Basic/PhaseRotation.lean)采用 `exp (I * φ)`，包含伴随、逆、酉性和源态作用证明。[标量相位因子](QFixLean/Basic/PhaseFactor.lean)已精确证明 π、π/3 的值和 `(ζ - 1)² = -ζ`。[相位例子](QFixLean/Examples/Phase.lean)验证了精确量子比特输出、概率保持，以及包含两个坐标的目标。

[π/3 搜索单步](QFixLean/PiOverThree/Step.lean)构造了实际酉算符 `U R_s U† R_P U`，两处相位均为正 π/3。对任意归一化源态、酉算符 U 和正交目标投影，已证明实际输出的失败向量为输入失败向量的 `ζ ε` 倍，失败概率为 `ε³`，成功概率为 `1 - ε³`。其中 `ζ = exp (I * π/3)`，ε 是 `U s` 的失败概率。证明包含 `ε = 0, 1` 的边界，不限制目标投影的秩。

[精确搜索单步例子](QFixLean/Examples/PiOverThree.lean)对 `(3/5, 4/5)` 独立展开实际算符积，验证失败概率从 `16/25` 变为 `4096/15625 = (16/25)³`。

[递归构造](QFixLean/PiOverThree/Recursion.lean)固定源态与目标，从 `U₀ = U` 开始，将当前酉算符替换为其搜索单步。已证明每层实际输出 `Uₖ s` 归一化，失败概率为 `ε₀^(3^k)`，成功概率为 `1 - ε₀^(3^k)`。[精确递归例子](QFixLean/Examples/PiOverThreeRecursion.lean)检查了第 0、1、2 层，对照两次单步推导与闭式公式，并包含保留两个坐标的目标。

[边界结果](QFixLean/PiOverThree/Boundary.lean)证明初始失败概率为 0 时始终为 0，为 1 时始终为 1；相应的补空间或目标向量分量在每层均为零。[单调性与收敛](QFixLean/PiOverThree/Convergence.lean)证明失败概率不增、成功概率不减。当 `ε₀ < 1`（等价于初始成功概率为正）时，失败概率与补分量范数趋于零，成功概率趋于一。结论包含 `ε₀ = 0`，不声称保留全局相位的完整态向量收敛。[精确收敛例子](QFixLean/Examples/PiOverThreeConvergence.lean)覆盖两个计算基态边界、有理量子比特态，以及三维中保留两个坐标的目标。

[可计数构造](QFixLean/PiOverThree/Construction.lean)记录基础变换、源态相位、目标相位及其逆原语；结构伴随反转乘积顺序，并逐个取逆。[资源证明](QFixLean/PiOverThree/Resources.lean)将其解释为与现有递归完全相同的酉算符。第 k 层目标相位查询数为 `qₖ = (3^k - 1)/2`，基础 U/U† 调用数为 `3^k`，源态相位调用数为 `qₖ`。同一个构造的实际失败概率为 `ε₀^(2*qₖ + 1)`，成功概率为一减去该值。[完整精确示例](QFixLean/Examples/PiOverThreeResources.lean)连接计数、概率、归一化、单调性与极限，包含第 0、1、2 层及三维目标。

上述计数针对未经优化的递归构造：每个目标相位及其逆计一次查询，基础调用不含目标查询成本，输入源态视为已提供，源态相位单独计数。这些结果不表示物理门数、位翻转预言机查询数或最优实现成本。至此完成项目约定的 π/3 核心验证范围，不表示覆盖了 2005 年论文的全部应用或物理实现。2014 年算法仍是后续工作。测量接口目前覆盖二结果投影测量的概率；混态、POVM 和测后态更新不在该接口范围内。

Copyright © 2026 QFixLean contributors。QFixLean 采用 [Apache License 2.0](LICENSE)；依赖保留各自的许可证及声明。
