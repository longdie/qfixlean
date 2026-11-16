# QFixLean: Formalizing Fixed-Point Quantum Search in Lean

[中文](README-zh.md)

QFixLean is a **Quantum Scientific Computing course project at Shanghai Jiao Tong University (Fall 2026)**. It formalizes the core correctness and construction costs of Grover's 2005 π/3 search and Yoder–Low–Chuang's 2014 fixed-point amplitude amplification in **Lean 4.35.0 and Mathlib v4.35.0**.

The quantum layer is developed within this repository using Mathlib's general mathematics. Other quantum formalization libraries are references, not dependencies. [SOURCES.md](SOURCES.md) records the three papers, fixed reference snapshots and licenses.

The main results below have complete Lean proofs. They connect actual unitary constructions to measured probabilities and to counts derived from the same constructions. The scope covers pure states and orthogonal target subspaces; it does not claim to formalize every result in the papers.

The representation uses continuous linear operators `E →L[ℂ] E` on complete complex inner-product spaces, normalized `PureState E`, native `unitary`, and `IsStarProjection P`. Finite-dimensional examples use `EuclideanSpace`. The inner product is conjugate-linear in its first argument; products act from right to left. For normalized ψ, success and failure are `‖P ψ‖²` and `‖(1−P) ψ‖²`. The shared phase operation is `R_P(φ) = I + (exp(iφ)−1)P`.

**Main result index.** Names in the table are relative to namespace `QFixLean`; links open their source files. The common quantum assumptions above apply, with additional conditions shown explicitly.

| Result | Lean entry point | Conditions and conclusion |
| --- | --- | --- |
| Projection probabilities | [PureState.successWeight_add_failureWeight](QFixLean/Basic/Probability.lean) | Normalized state and orthogonal P: probabilities sum to one; the same module proves both lie in `[0,1]` |
| General selective phases | [phaseRotation_mem_unitary](QFixLean/Basic/PhaseRotation.lean) | Orthogonal P and any real angle: unitary, with adjoint equal to the negative-angle phase |
| π/3 single step | [PiOverThree.searchStep_failureWeight](QFixLean/PiOverThree/Step.lean) | Any unitary U, normalized s and orthogonal P: actual failure becomes ε³ |
| π/3 recursion | [PiOverThree.searchRecursion_failureWeight](QFixLean/PiOverThree/Recursion.lean) | Same fixed s and P: actual failure at level k is ε₀^(3^k), including ε₀=0,1 |
| π/3 convergence | [PiOverThree.searchRecursion_failureWeight_tendsto_zero](QFixLean/PiOverThree/Convergence.lean) | ε₀<1: failure and complementary norm tend to zero; success tends to one. Monotonicity includes both endpoints |
| π/3 resources | [PiOverThree.searchConstruction_spec](QFixLean/PiOverThree/Resources.lean) | Exact recursive semantics, normalization, probabilities and structural counts in one theorem |
| Quasi-Chebyshev identity | [QuasiChebyshev.terminal_value_chebyshev](QFixLean/Polynomial/QuasiChebyshevIdentity.lean) | L=2ℓ+1 and 0<γ≤1: the actual scalar recurrence equals the Chebyshev ratio for every complex input |
| Explicit-phase probabilities | [FixedPoint.ExplicitPhases.p14Search_probabilities](QFixLean/FixedPoint/Correctness.lean) | L=2ℓ+1 and 0<γ≤1: the actual P14 output satisfies the probability formula below, including initial success 0 and 1 |
| Selected algorithm and queries | [FixedPoint.QueryAlgorithm.selected_spec](QFixLean/FixedPoint/Resources.lean) | Unitary preparation A, normalized reference, orthogonal P, 0<λ₀≤1, 0<δ<1, and prepared success ≥λ₀: actual output, ancilla reset, error and resource guarantees together |

For **π/3 search**, the recursion is `U₀=U`, `Uₖ₊₁=Uₖ R_s Uₖ† R_P Uₖ`, with both angles positive π/3 and output `Uₖ s`. Here R_s uses the projection onto s, and `ε₀=‖(I−P)Us‖²`. Each level constructs a new operator using the fixed source and target. Failure is ε₀^(3^k); the unoptimized construction uses `(3^k−1)/2` target-phase queries, `3^k` total U/U† calls, and `(3^k−1)/2` source-phase calls. Each target phase or inverse costs one query, base U/U† contain no target-query cost, and the source is supplied. The convergence statements concern probabilities and the complementary norm, not the full vector with its global phase.

For **explicit fixed-point amplitude amplification**, λ denotes initial success probability and δ bounds failure amplitude. The proved success formula is

$$
p_L(\lambda)=1-\left[\frac{T_L(\sqrt{1-\lambda}/\gamma)}{T_L(1/\gamma)}\right]^2.
$$

Choose `B=log(2/δ)/sqrt(λ₀)`, `ℓ=ceil(B/2)`, `L=2ℓ+1`, and `γ=1/cosh(arcosh(1/δ)/L)`. The proof derives `1−γ²≤λ₀`, so prepared success at least λ₀ yields output success at least `1−δ²`. The full compiled construction starts from the reference state with a clean ancilla, restores that ancilla, and uses `Q=L−1<B+2` bit-flip queries, `ℓ+1` calls to A, `ℓ` to A†, and `ℓ` each to reference-state and ancilla phases. Supplying the prepared state removes the initial extra A. The exact relation to the P14 vector retains the global factor `(-1)^ℓ`.

The proof connects [actual evolution to the amplitude recurrence](QFixLean/FixedPoint/AmplitudeRecurrence.lean), establishes the [cyclic tangent sum](QFixLean/Polynomial/CyclicTangentSum.lean) and quasi-Chebyshev identity, then links the [explicit phases](QFixLean/FixedPoint/ExplicitPhases.lean) to that recurrence. The reusable [conditional error theorem](QFixLean/FixedPoint/Conditional.lean) still takes a formula premise; the explicit algorithm proves it, and the selected algorithm also proves parameter matching. Neither premise is required from callers of `selected_spec`.

**Exact examples to explore:**

- [Rational qubit measurement](QFixLean/Examples/Measurement.lean): `(3/5,4/5)` has success `9/25` and failure `16/25` for the first-coordinate target; a three-dimensional target retains two coordinates.
- [π/3 recursion](QFixLean/Examples/PiOverThreeRecursion.lean): failures `16/25`, `4096/15625`, `(16/25)^9` at levels 0, 1, 2; the last is checked through two single steps and through the closed form.
- [Complete selected algorithm](QFixLean/Examples/FixedPointResources.lean): nonidentity preparation, `λ₀=1/4`, `δ=1/2`, `ℓ=2`, `L=5`; success at least `3/4`, four queries, three A calls and two A† calls, with a restored ancilla.
- [Periodic cyclic tiling](QFixLean/Examples/CyclicTilings.lean): at length nine, three distinct rotations each occur three times. The general proof counts all rotations, including stabilizers.

**Build and verification.** Install [elan](https://github.com/leanprover/elan), keep the committed `lean-toolchain` and `lake-manifest.json`, and run from the repository directory:

```sh
lake exe cache get
lake build
lake build --wfail
lake exe mk_all --check --lib QFixLean
lake env lean -DwarningAsError=true scripts/CheckAxioms.lean
lake env lean -DwarningAsError=true scripts/CheckResults.lean
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Use `import QFixLean` to access the library. After adding modules, regenerate its entry point with `lake exe mk_all --lib QFixLean`. Use `lake update` only for intentional dependency upgrades.

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) runs the strict build, public-import check, axiom audit, result specifications and dependency-pin check on pushes and pull requests to `main`, with manual runs available. Actions are pinned to commits. The [axiom audit](scripts/CheckAxioms.lean) inspects transitive dependencies of declarations by defining project module, allowing only `propext`, `Classical.choice` and `Quot.sound`. The [result specifications](scripts/CheckResults.lean) fix expected conclusions and allowed assumptions. These checks supplement review of mathematical meaning.

Independent reproduction starts from a fresh checkout or archive of the intended commit. Dependency caches may be downloaded; QFixLean must be built from committed source without copying its existing build artifacts or local notes. For an archive without Git metadata, compare source and pin hashes against the commit instead of running the final Git command. Detailed audit records and course materials remain local under ignored `docs/`.

**Scope and limits.** Both resource models assume preparation primitives contain no target-query cost. The π/3 branch counts target phases; the compiled 2014 branch counts bit-flip queries. Comparing them requires an explicit implementation conversion. The 2014 guarantee is uniform over the promised input interval; it does not assert improvement after every individual iterate. Query-optimality lower bounds, minimal gate counts, running time and finite-precision phase synthesis remain outside the proved scope. The quantum layer covers pure states and two-outcome projection probabilities; mixed states, general channels, postmeasurement state updates and general QSP/QSVT completeness are not included. This work provides formalization and reusable interfaces, without claiming the first formalization of fixed-point search.

Copyright © 2026 QFixLean contributors. Licensed under [Apache-2.0](LICENSE); dependencies retain their own licenses and notices.
