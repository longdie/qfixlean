# QFixLean：固定点量子搜索的 Lean 形式化

[English](README.md)

QFixLean 是 **上海交通大学量子科学计算课程（2026 年秋季学期）** 的课程项目。

固定点量子搜索旨在解决普通 Grover 搜索中的过冲问题。我们希望通过这一主题加深对量子算法的理解，并探索如何使用 Lean 明确算法的假设与正确性保证，使其接受机器检查。

项目使用 **Lean 4 和 Mathlib**，目前代码已覆盖所需量子基础、[Grover 于 2005 年提出的 π/3 固定点搜索算法](https://arxiv.org/abs/quant-ph/0503205)的核心概率与资源保证，以及 [Yoder、Low 和 Chuang 于 2014 年提出的固定点振幅放大算法](https://arxiv.org/abs/1409.3305)的显式相位正确性和位翻转预言机查询上界。各项结果的范围与假设见下文。

我们希望为量子科学计算与 Lean 形式化社区贡献可复用的定义和证明，逐步积累服务于量子算法学习与验证的基础设施。

项目固定使用 **Lean 4.35.0** 和 **Mathlib v4.35.0**。安装 [elan](https://github.com/leanprover/elan) 后，在仓库目录运行：

```sh
lake exe cache get
lake build
```

`lean-toolchain` 指定 Lean 版本，已提交的 `lake-manifest.json` 固定依赖 revision。复现构建时保留这两个文件；只有主动升级依赖时才运行 `lake update`。

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) 在推送或提交拉取请求到 `main` 时运行 `lake build --wfail`，也支持手动触发。工作流下载 Mathlib 编译缓存、从源码构建 QFixLean，在出现构建警告（包括 `sorry` 警告）时失败，并检查公开导入列表完整、依赖版本文件未被改动。[公理审查程序](scripts/CheckAxioms.lean)检查项目模块中声明的传递依赖，只允许 `propext`、`Classical.choice` 和 `Quot.sound`；出现其他公理则检查失败。[主要结果检查](scripts/CheckResults.lean)明确写出预期算法输出、概率、极限及构造成本和允许的假设，再通过公共库完成证明。所用 Actions 固定到 commit。这些检查用于补充对定理陈述、假设及其算法对应关系的审查。

使用 `import QFixLean` 导入公开库。新增模块后运行 `lake exe mk_all --lib QFixLean` 更新自动生成的库入口。本地复现 CI 检查时，依次运行：

```sh
lake build --wfail
lake exe mk_all --check --lib QFixLean
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckResults.lean
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

独立复现时，从所需提交的全新检出开始，保留固定工具链与依赖锁，通过 `lake exe cache get` 下载依赖缓存，不复制已有 QFixLean 构建目录。缓存提供已编译依赖，QFixLean 根据受控源码构建。无 Git 元数据的 archive 副本应将版本文件和源码哈希与对应提交比较，替代 Git 差异命令。[来源与许可](SOURCES.md)记录论文版本、依赖及参考库快照。

主表示采用复内积空间上的连续线性算符，有限维例子使用 `EuclideanSpace`。当前已提供[归一化纯态](QFixLean/Basic/State.lean)与[酉作用](QFixLean/Basic/Unitary.lean)接口，包含内积保持、复合及伴随或逆操作恢复原态的证明。[精确量子比特例子](QFixLean/Examples/Qubit.lean)覆盖计算基态、叠加态 `(3/5, 4/5)` 和 Pauli X。

[投影接口](QFixLean/Basic/Projection.lean)支持一般目标子空间、正交补投影和归一化源态的秩一投影。对正交投影，[测量权重](QFixLean/Basic/Probability.lean)之和等于输入的平方范数；归一化时，它们是 `[0,1]` 内的概率。复内积桥接与全局相位不变性将这些权重连接到向量运算。[精确测量例子](QFixLean/Examples/Measurement.lean)包含成功率、失败率为 `9/25`、`16/25` 的量子比特，以及三维中保留两个坐标的目标。

[选择性相位接口](QFixLean/Basic/Phase.lean)已包含目标与补分量作用、同一目标的测量权重不变性，以及用成功/失败权重表达的内积重叠公式。[实角度相位](QFixLean/Basic/PhaseRotation.lean)采用 `exp (I * φ)`，包含伴随、逆、酉性和源态作用证明。[标量相位因子](QFixLean/Basic/PhaseFactor.lean)已精确证明 π、π/3 的值和 `(ζ - 1)² = -ζ`。[相位例子](QFixLean/Examples/Phase.lean)验证了精确量子比特输出、概率保持，以及包含两个坐标的目标。

[π/3 搜索单步](QFixLean/PiOverThree/Step.lean)构造了实际酉算符 `U R_s U† R_P U`，两处相位均为正 π/3。对任意归一化源态、酉算符 U 和正交目标投影，已证明实际输出的失败向量为输入失败向量的 `ζ ε` 倍，失败概率为 `ε³`，成功概率为 `1 - ε³`。其中 `ζ = exp (I * π/3)`，ε 是 `U s` 的失败概率。证明包含 `ε = 0, 1` 的边界，不限制目标投影的秩。

[精确搜索单步例子](QFixLean/Examples/PiOverThree.lean)对 `(3/5, 4/5)` 独立展开实际算符积，验证失败概率从 `16/25` 变为 `4096/15625 = (16/25)³`。

[递归构造](QFixLean/PiOverThree/Recursion.lean)固定源态与目标，从 `U₀ = U` 开始，将当前酉算符替换为其搜索单步。已证明每层实际输出 `Uₖ s` 归一化，失败概率为 `ε₀^(3^k)`，成功概率为 `1 - ε₀^(3^k)`。[精确递归例子](QFixLean/Examples/PiOverThreeRecursion.lean)检查了第 0、1、2 层，对照两次单步推导与闭式公式，并包含保留两个坐标的目标。

[边界结果](QFixLean/PiOverThree/Boundary.lean)证明初始失败概率为 0 时始终为 0，为 1 时始终为 1；相应的补空间或目标向量分量在每层均为零。[单调性与收敛](QFixLean/PiOverThree/Convergence.lean)证明失败概率不增、成功概率不减。当 `ε₀ < 1`（等价于初始成功概率为正）时，失败概率与补分量范数趋于零，成功概率趋于一。结论包含 `ε₀ = 0`，不声称保留全局相位的完整态向量收敛。[精确收敛例子](QFixLean/Examples/PiOverThreeConvergence.lean)覆盖两个计算基态边界、有理量子比特态，以及三维中保留两个坐标的目标。

[可计数构造](QFixLean/PiOverThree/Construction.lean)记录基础变换、源态相位、目标相位及其逆原语；结构伴随反转乘积顺序，并逐个取逆。[资源证明](QFixLean/PiOverThree/Resources.lean)将其解释为与现有递归完全相同的酉算符。第 k 层目标相位查询数为 `qₖ = (3^k - 1)/2`，基础 U/U† 调用数为 `3^k`，源态相位调用数为 `qₖ`。同一个构造的实际失败概率为 `ε₀^(2*qₖ + 1)`，成功概率为一减去该值。[完整精确示例](QFixLean/Examples/PiOverThreeResources.lean)连接计数、概率、归一化、单调性与极限，包含第 0、1、2 层及三维目标。

上述计数针对未经优化的递归构造：每个目标相位及其逆计一次查询，基础调用不含目标查询成本，输入源态视为已提供，源态相位单独计数。这些结果不表示物理门数、位翻转预言机查询数或最优实现成本。至此完成项目约定的 π/3 核心验证范围，不表示覆盖了 2005 年论文的全部应用或物理实现。测量接口目前覆盖二结果投影测量的概率；混态、POVM 和测后态更新不在该接口范围内。

对于 2014 年方案，[Chebyshev 比值界](QFixLean/Polynomial/ChebyshevBounds.lean)与[标准参数分析](QFixLean/Polynomial/ChebyshevParameters.lean)已证明标量误差保证。对正次数 L 和 `0 < δ < 1`，参数为 `γ = 1 / cosh(arcosh(1/δ)/L)`，归一化分母精确满足 `T_L(1/γ) = 1/δ`。当成功率参数 `λ ∈ [0,1]` 且 `λ ≥ 1 - γ²` 时，带符号比值 `T_L(sqrt(1-λ)/γ) / T_L(1/γ)` 的绝对值不超过 δ，其平方不超过 `δ²`，互补标量模型至少为 `1 - δ²`。对满足参数匹配条件的下界 `λ₀`，保证在整个承诺区间统一成立；这些标量界不要求次数为奇数。

[条件性量子保证](QFixLean/FixedPoint/Conditional.lean)明确假设实际归一化输出的失败概率等于上述比值平方，其中 λ 取实际初始态的成功概率。在这个公式前提及承诺区间条件下，证明同一输出的失败概率不超过 `δ²`、成功概率至少为 `1 - δ²`。[精确例子](QFixLean/Examples/Chebyshev.lean)包含负的三次比值 `-1/26`，以及直接证明公式前提的次数一量子比特实例。这个通用条件性接口继续保留。下文的显式相位算法正确性证明已提供其公式前提；位翻转预言机查询代价和最优性是另外的问题。

[广义相位序列](QFixLean/FixedPoint/PhaseSequence.lean)已按明确的时间顺序执行任意目标/源态相位，始终固定参考态。原始好坏分量张成的子空间在整个执行中保持不变，包含退化输入。当初始成功率严格位于零和一之间时，[规范二维约化](QFixLean/FixedPoint/Reduction.lean)将欧氏坏/好坐标等距嵌入该子空间，证明每个实际单步及序列与[显式酉矩阵](QFixLean/FixedPoint/TwoDimensional.lean)精确对应；同一输出的失败、成功概率等于两个坐标的模平方。[约定转换](QFixLean/FixedPoint/PhaseConventions.lean)证明 P14/P24 的参数对应及精确全局因子 `(-1)^length`。[边界证明](QFixLean/FixedPoint/PhaseBoundary.lean)保留累积相位，说明任意序列下初始成功率零、一分别保持为零、一。[精确例子](QFixLean/Examples/FixedPointReduction.lean)独立核对算符与矩阵计算、执行顺序、复相位和一般秩目标。这些一般演化结果用于下文的显式相位正确性证明。

[振幅递推桥接](QFixLean/FixedPoint/AmplitudeRecurrence.lean)进一步证明，同一实际输出的失败概率等于[复系数多项式](QFixLean/Polynomial/PhaseRecurrence.lean)在初始失败振幅大小处求值的模平方。长度为 ℓ 的广义迭代列表使用 `2*ℓ` 个递推角，终止于振幅下标 `2*ℓ+1`；初值为 `1, x`，更新为 `a_next = x*(1+exp(-iφ))*a_current - exp(-iφ)*a_previous`。[交错矩阵证明](QFixLean/FixedPoint/Interleaved.lean)以不含除法的恒等式消去辅助坐标；精确向量等式保留累积相位，统一概率定理包含初始成功率零和一。P14 执行沿用已有参数转换并保留额外的 `(-1)^ℓ`。[精确递推例子](QFixLean/Examples/FixedPointRecurrence.lean)对照直接执行与递推计算，包含真正为非实数的终值。指定标量相位递推的恒等式及其与显式算法的对应已在下文证明。

[准 Chebyshev 代数准备](QFixLean/Polynomial/QuasiChebyshev.lean)已将该递推实例化为 `φₙ = 2*arctan(sqrt(1−γ²)*tan(nπ/L))`。正奇数长度下正切避开极点，每个复数分母因子均非零。分子多项式满足保留相邻下标 n、n−1 的精确清分母递推；完整 L−1 个角的终值对任意复数输入等于 `N_L(x)/D_L`，归一化关系 `N_n(1)=D_n` 独立于 Chebyshev 公式成立。[精确检查](QFixLean/Examples/QuasiChebyshev.lean)覆盖相位符号、短前缀、L=1、γ=1，以及 L=3 的两条独立三次式计算。终值恒等式和显式相位对应已在下文证明。通用条件性误差定理保留公式前提，新增算法定理则证明该前提。位翻转预言机实现与资源证明见下文。

[循环正切求和](QFixLean/Polynomial/CyclicTangentSum.lean)已证明：对正奇数循环上的任意下标集合 S，`∑_j ∏_{m∈S} i*tan((m+j)π/L)` 在 S.card 为偶数时等于 L，为奇数时等于零。下标按模 L 解释，包含空集和 L=1。[独立根多项式证明](QFixLean/Polynomial/CyclicTangentProduct.lean)提供向下归纳所需的非零正切乘积。单射枚举、固定系数及 `sqrt(1−γ²)` 缩放接口将结果连接到已有相位正切，包含 γ=1。[精确例子](QFixLean/Examples/CyclicTangent.lean)对照三项直接计算与一般定理，给出重复下标反例，并检查只有三个不同平移集合、但仍计全部九个平移的合数长度实例。带权比较、标量恒等式及显式相位整合已在下文证明；位翻转预言机代价已在下文证明。

[准 Chebyshev 恒等式](QFixLean/Polynomial/QuasiChebyshevIdentity.lean)已证明：对全部正奇数 L 和 `0 < γ ≤ 1`，原分子为 `γ^L T_L(X/γ)`，分母为 `γ^L T_L(1/γ)`，同一 L−1 个角的递推终值对任意复数 x 等于 `T_L(x/γ)/T_L(1/γ)`。实数输入时，它恰为 M11 的带符号振幅，其平方等于终值模平方。证明将[实际有限线段铺砖](QFixLean/Polynomial/LineTilings.lean)连接到[圆周权重](QFixLean/Polynomial/TilingWeights.lean)，用 M15 展开互异端点子集，再以置换双重求和保留全部旋转重数。[精确检查](QFixLean/Examples/QuasiChebyshevIdentity.lean)覆盖 L=1、γ=1、独立三次式计算及数值 `−1/26`；[实际长度九周期铺砖](QFixLean/Examples/CyclicTilings.lean)有三种不同旋转，每种计三次。该标量恒等式用于下文的实际算法正确性证明；预言机资源已在下文证明。

[显式相位](QFixLean/FixedPoint/ExplicitPhases.lean)已将 P14 的反余切相位序列连接到 P24 执行：转换后的每个目标角相差一整圈，精确算符关系保留全局因子 `(-1)^ℓ`。[正确性证明](QFixLean/FixedPoint/Correctness.lean)对 `L=2ℓ+1` 和 `0<γ≤1` 证明实际输出的失败概率为 `[T_L(sqrt(1−λ)/γ)/T_L(1/γ)]²`，成功概率为一减去该值。概率定理包含初始成功率零、一、空序列和任意秩目标。采用标准参数且 `λ≥1−γ²` 时，同一实际 P14 输出的失败概率不超过 `δ²`、成功概率至少为 `1−δ²`，无需公式假设。满足参数匹配条件的下界给出统一保证，相位不依赖未知的实际 λ。[精确算法检查](QFixLean/Examples/FixedPointCorrectness.lean)对照直接算符计算与一般公式，保留复相位和带符号振幅。下文的实现提供位翻转预言机语义、辅助位恢复、有限次数选择和查询界。

[Hilbert 辅助位空间](QFixLean/Basic/Ancilla.lean)对两个数据分量使用平方和范数。[目标控制位翻转预言机](QFixLean/FixedPoint/Oracle.lean)在整个扩展空间上为酉变换；两次调用之间插入辅助位 `diag(1, exp(iφ))`，对任意数据向量精确实现目标相位并恢复辅助位为零。[态制备共轭](QFixLean/FixedPoint/Preparation.lean)用 `A†`、参考态相位、`A` 实现固定源态相位。[可计数表达式](QFixLean/FixedPoint/Construction.lean)及其[酉语义](QFixLean/FixedPoint/Compilation.lean)编译 M17 的同一个相位列表，保留执行顺序和 P14 的精确全局因子 `(-1)^ℓ`。[预言机例子](QFixLean/Examples/Oracle.lean)覆盖计算基 XOR、直接叠加分量计算、连续辅助位复用及秩二目标。

[有限选参](QFixLean/FixedPoint/Parameters.lean)明确规定 `B = log(2/δ)/sqrt(λ₀)`、`ℓ = ceil(B/2)`、`L = 2ℓ+1`，证明标准参数满足 `1−γ²≤λ₀`，并得到 `Q < B+2` 和 `L < B+3`。[联合算法定理](QFixLean/FixedPoint/Resources.lean)的前提为归一参考态、酉态制备、正交目标、`0<δ<1`，以及实际制备态成功率至少为 `λ₀∈(0,1]`。实际编译输出归一化、辅助位恢复，与已证明的显式算法对应，失败概率不超过 `δ²`、成功概率至少为 `1−δ²`。同一个未经优化的构造使用 `Q=2ℓ=L−1` 次位翻转查询、`ℓ+1` 次 A、`ℓ` 次 A†，以及各 `ℓ` 次参考态相位和辅助位相位；若已提供制备态，则去掉初始额外的一次 A。[完整精确例子](QFixLean/Examples/FixedPointResources.lean)使用非恒等有理旋转、`λ₀=1/4`、`δ=1/2`：次数五、成功率至少 `3/4`、四次位翻转查询、三次 A 和两次 A†。

这些是精确相位模型下的构造成本：所述查询界假定 A/A† 不含目标查询成本，参考态与辅助位相位作为另计的已提供操作。M10 统计目标相位查询，M18 统计位翻转查询，比较前需要明确实现换算。有限上界不包含查询最优性的下界证明，也不表示最小门数或运行时间；精确实数相位不等于已完成有限精度相位综合。上述检查提供全项目证明与复现的验收入口；M20 课程报告和汇报材料仍待推进。

Copyright © 2026 QFixLean contributors。QFixLean 采用 [Apache License 2.0](LICENSE)；依赖保留各自的许可证及声明。
