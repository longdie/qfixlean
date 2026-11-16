# QFixLean：固定点量子搜索的 Lean 形式化

[English](README.md)

QFixLean 是 **上海交通大学量子科学计算课程（2026 年秋季学期）** 的课程项目，使用 **Lean 4.35.0 和 Mathlib v4.35.0**，形式化验证 Grover 2005 年 π/3 搜索和 Yoder–Low–Chuang 2014 年固定点振幅放大的核心正确性与构造成本。

量子层在本项目内编写，通用数学复用 Mathlib；其他量子形式化库作为参考，不作为依赖。[SOURCES.md](SOURCES.md)记录三篇论文、参考库固定版本及许可。

下列主要结果已有完整 Lean 证明，将实际酉构造连接到测量概率及同一构造的资源计数。范围覆盖纯态和正交目标子空间，不表示已形式化论文中的全部结果。

主表示是在复内积完备空间上的连续线性算符 `E →L[ℂ] E`，使用归一化 `PureState E`、原生 `unitary` 和 `IsStarProjection P`。有限维例子采用 `EuclideanSpace`。内积对第一变元共轭线性，算符从右向左作用。对归一化 ψ，成功和失败概率分别为 `‖P ψ‖²`、`‖(1−P) ψ‖²`，统一相位操作为 `R_P(φ) = I + (exp(iφ)−1)P`。

**主要结果索引。** 表中名称省略 `QFixLean` 命名空间，链接指向对应源码。量子结果采用上述共同假设，附加条件在表中注明。

| 结果 | Lean 入口 | 条件与结论 |
| --- | --- | --- |
| 投影测量概率 | [PureState.successWeight_add_failureWeight](QFixLean/Basic/Probability.lean) | 归一化态、正交 P：两概率之和为一；同模块证明均在 `[0,1]` |
| 通用相位 | [phaseRotation_mem_unitary](QFixLean/Basic/PhaseRotation.lean) | 正交 P、任意实角：相位为酉，伴随等于负角相位 |
| π/3 单步 | [PiOverThree.searchStep_failureWeight](QFixLean/PiOverThree/Step.lean) | 任意酉 U、归一 s、正交 P：实际失败概率变为 ε³ |
| π/3 递归 | [PiOverThree.searchRecursion_failureWeight](QFixLean/PiOverThree/Recursion.lean) | 固定同一 s、P：第 k 层实际失败为 ε₀^(3^k)，包含 ε₀=0、1 |
| π/3 收敛 | [PiOverThree.searchRecursion_failureWeight_tendsto_zero](QFixLean/PiOverThree/Convergence.lean) | ε₀<1：失败概率、补分量范数趋零，成功概率趋一；单调性包含两端点 |
| π/3 资源 | [PiOverThree.searchConstruction_spec](QFixLean/PiOverThree/Resources.lean) | 同一构造的精确递归语义、归一化、概率与结构计数 |
| 准 Chebyshev 恒等式 | [QuasiChebyshev.terminal_value_chebyshev](QFixLean/Polynomial/QuasiChebyshevIdentity.lean) | L=2ℓ+1、0<γ≤1：实际标量递推对任意复输入等于 Chebyshev 比值 |
| 显式相位概率 | [FixedPoint.ExplicitPhases.p14Search_probabilities](QFixLean/FixedPoint/Correctness.lean) | L=2ℓ+1、0<γ≤1：实际 P14 输出满足下述概率公式，包含初始成功率 0、1 |
| 选参算法与查询保证 | [FixedPoint.QueryAlgorithm.selected_spec](QFixLean/FixedPoint/Resources.lean) | 酉制备 A、归一参考态、正交 P、0<λ₀≤1、0<δ<1、制备后成功率≥λ₀：联合给出实际输出、辅助位恢复、误差和资源保证 |

**π/3 搜索**采用 `U₀=U`、`Uₖ₊₁=Uₖ R_s Uₖ† R_P Uₖ`，两处相位均为正 π/3，输出为 `Uₖ s`；R_s 使用源态 s 的投影，`ε₀=‖(I−P)Us‖²`。每层构造新的算符，源态和目标保持固定。失败概率为 ε₀^(3^k)；未经优化的构造使用 `(3^k−1)/2` 次目标相位查询、合计 `3^k` 次 U/U† 调用，以及 `(3^k−1)/2` 次源态相位。每个目标相位或其逆计一次查询，基础 U/U† 不含目标查询成本，源态视为已提供。收敛结论针对概率和补分量范数，不声称带全局相位的完整态向量收敛。

**显式固定点振幅放大**中，λ 表示初始成功概率，δ 是失败振幅容限。已证明成功概率公式

$$
p_L(\lambda)=1-\left[\frac{T_L(\sqrt{1-\lambda}/\gamma)}{T_L(1/\gamma)}\right]^2.
$$

取 `B=log(2/δ)/sqrt(λ₀)`、`ℓ=ceil(B/2)`、`L=2ℓ+1`、`γ=1/cosh(arcosh(1/δ)/L)`，证明中推出 `1−γ²≤λ₀`，因此制备后成功率至少为 λ₀ 时，输出成功率至少为 `1−δ²`。完整编译构造从参考态与干净辅助位开始，恢复辅助位为零，使用 `Q=L−1<B+2` 次位翻转查询、`ℓ+1` 次 A、`ℓ` 次 A†，以及各 `ℓ` 次参考态相位和辅助位相位。若已提供制备态，则省去初始额外的一次 A。与 P14 向量的精确对应保留全局因子 `(-1)^ℓ`。

证明先连接[实际演化与振幅递推](QFixLean/FixedPoint/AmplitudeRecurrence.lean)，建立[循环正切求和](QFixLean/Polynomial/CyclicTangentSum.lean)及准 Chebyshev 恒等式，再将[显式相位](QFixLean/FixedPoint/ExplicitPhases.lean)与同一递推相连。通用[条件性误差定理](QFixLean/FixedPoint/Conditional.lean)继续保留公式前提；显式算法已经证明该公式，选参算法还证明了参数匹配。调用 `selected_spec` 时无需提供这两个额外前提。

**建议查看的精确例子：**

- [有理量子比特测量](QFixLean/Examples/Measurement.lean)：`(3/5,4/5)` 对第一坐标目标的成功率为 `9/25`、失败率为 `16/25`；另有三维中保留两个坐标的目标。
- [π/3 递归](QFixLean/Examples/PiOverThreeRecursion.lean)：第 0、1、2 层失败率为 `16/25`、`4096/15625`、`(16/25)^9`；二层分别用两次单步和闭式公式核对。
- [完整选参算法](QFixLean/Examples/FixedPointResources.lean)：非恒等制备，`λ₀=1/4`、`δ=1/2`、`ℓ=2`、`L=5`；成功率至少 `3/4`，四次查询、三次 A、两次 A†，辅助位恢复。
- [周期圆周铺砖](QFixLean/Examples/CyclicTilings.lean)：长度九时，三种不同旋转各出现三次；一般证明保留全部旋转及稳定子的重数。

**构建与检查。** 安装 [elan](https://github.com/leanprover/elan)，保留受控的 `lean-toolchain` 与 `lake-manifest.json`，在仓库目录运行：

```sh
lake exe cache get
lake build
lake build --wfail
lake exe mk_all --check --lib QFixLean
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckResults.lean
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

使用 `import QFixLean` 导入公开库；新增模块后用 `lake exe mk_all --lib QFixLean` 更新入口。仅在主动升级依赖时运行 `lake update`。

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) 在推送或拉取请求到 `main` 时执行严格构建、公开入口、公理、主要结果和依赖锁检查，也支持手动触发；Actions 固定到 commit。[公理审查](scripts/CheckAxioms.lean)按声明所属项目模块检查传递依赖，仅允许 `propext`、`Classical.choice`、`Quot.sound`；[结果检查](scripts/CheckResults.lean)固定预期结论及允许的假设。这些检查补充对数学语义的审查。

独立复现应从指定提交的新检出或 archive 开始。允许下载依赖缓存；QFixLean 从受控源码构建，不复制已有项目编译产物或本地笔记。无 Git 元数据的 archive 副本用提交中的源码和版本文件哈希替代最后一条 Git 命令。详细审查记录和课程材料位于被忽略的本地 `docs/`。

**范围与局限。** 两种资源模型均假定基础制备内部不含目标查询成本。π/3 分支统计目标相位，2014 编译分支统计位翻转查询，比较前需要明确实现换算。2014 方案是在承诺输入区间上的统一误差保证，不要求每个单步都使成功概率提高。查询最优性下界、最小门数、运行时间和有限精度相位综合尚不在证明范围内。量子层覆盖纯态和二结果投影概率，未包含混态、一般信道、测后态更新及一般 QSP/QSVT 完备性。项目贡献是形式化实现与可复用接口，不宣称首次形式化固定点搜索。

Copyright © 2026 QFixLean contributors。采用 [Apache-2.0](LICENSE)；依赖保留各自许可和声明。
