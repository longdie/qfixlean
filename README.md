# QFixLean: Formalizing Fixed-Point Quantum Search in Lean

[中文](README-zh.md)

QFixLean is a project for the **Quantum Scientific Computing course at Shanghai Jiao Tong University (Fall 2026)**.

Fixed-point quantum search addresses the overshooting problem in ordinary Grover search. We chose this topic to deepen our understanding of quantum algorithms while exploring how Lean can make their assumptions and correctness guarantees explicit and machine-checkable.

Using **Lean 4 and Mathlib**, our core goal is to first formalize quantum fundamentals covered in the course—quantum states, unitary transformations, projective measurements, and phase operations—and then formalize [Grover’s 2005 π/3 fixed-point search algorithm](https://arxiv.org/abs/quant-ph/0503205). As an extension, we aim to explore the formalization of [Yoder, Low, and Chuang’s 2014 fixed-point amplitude amplification algorithm](https://arxiv.org/abs/1409.3305); completion of this extension will depend on progress.

We hope to contribute reusable definitions and proofs for quantum scientific computing and the Lean formalization community, gradually developing a foundation for learning about and verifying quantum algorithms.

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**. With [elan](https://github.com/leanprover/elan) installed, run these commands from the repository directory:

```sh
lake exe cache get
lake build
```

`lean-toolchain` selects Lean, and the committed `lake-manifest.json` pins dependency revisions. Keep both files when reproducing a build; `lake update` is for intentional dependency upgrades.

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) runs `lake build --wfail` on pushes and pull requests to `main`, and supports manual runs. It downloads Mathlib's compiled cache, builds QFixLean from source, fails on build warnings (including `sorry` warnings), and checks the public import list and unchanged dependency pins. An [axiom audit](scripts/CheckAxioms.lean) checks declarations from project modules and their transitive dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`; any other axiom makes the check fail. The workflow actions are pinned to commit hashes. These checks supplement review of theorem statements, assumptions, and their connection to the algorithms.

Import the public library with `import QFixLean`. After adding modules, update its generated entry point with `lake exe mk_all --lib QFixLean`. To reproduce the CI checks locally, run `lake build --wfail`, `lake exe mk_all --check --lib QFixLean`, `lake env lean -DwarningAsError=true scripts/CheckAxioms.lean`, and `git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json`.

The representation uses continuous linear operators on complex inner-product spaces, with `EuclideanSpace` for finite-dimensional examples. The code provides [normalized pure states](QFixLean/Basic/State.lean) and [unitary evolution](QFixLean/Basic/Unitary.lean), including inner-product preservation, composition, and recovery by the adjoint or inverse. [Exact qubit examples](QFixLean/Examples/Qubit.lean) cover computational basis states, the superposition `(3/5, 4/5)`, and Pauli X.

The [projection interface](QFixLean/Basic/Projection.lean) covers arbitrary target subspaces, orthogonal complements, and normalized source-state projections. For orthogonal projections, [measurement weights](QFixLean/Basic/Probability.lean) sum to the input's squared norm; for normalized inputs they are probabilities in `[0,1]`. Complex inner-product bridges and global-phase invariance connect these weights to vector calculations. [Exact measurement examples](QFixLean/Examples/Measurement.lean) include a qubit with probabilities `9/25` and `16/25`, and a three-dimensional target retaining two coordinates.

The [selective phase interface](QFixLean/Basic/Phase.lean) describes target and complementary components, same-target measurement invariance, and the overlap in terms of success and failure weights. [Real-angle rotations](QFixLean/Basic/PhaseRotation.lean) use `exp (I * φ)`, with adjoint, inverse, unitarity and source-state action proofs. The [scalar phase factors](QFixLean/Basic/PhaseFactor.lean) include exact π and π/3 values and the identity `(ζ - 1)² = -ζ`. [Phase examples](QFixLean/Examples/Phase.lean) verify exact qubit outputs, probability preservation and a target with two coordinates.

The [π/3 search step](QFixLean/PiOverThree/Step.lean) constructs the unitary `U R_s U† R_P U` with both phases equal to positive π/3. For any normalized source, unitary `U`, and orthogonal target projection, its actual output has failure vector `ζ ε` times the input failure vector, failure probability `ε³`, and success probability `1 - ε³`. Here `ζ = exp (I * π/3)` and `ε` is the failure probability of `U s`. The proof includes the endpoints `ε = 0, 1` and imposes no target-rank restriction.

[Exact search-step examples](QFixLean/Examples/PiOverThree.lean) independently expand the operator product for `(3/5, 4/5)` and verify that failure probability `16/25` becomes `4096/15625 = (16/25)³`.

The [recursive construction](QFixLean/PiOverThree/Recursion.lean) keeps the source and target fixed, starting at `U₀ = U` and replacing each current unitary by its search step. Every level's actual output `Uₖ s` is normalized, with failure probability `ε₀^(3^k)` and success probability `1 - ε₀^(3^k)`. [Exact recursion examples](QFixLean/Examples/PiOverThreeRecursion.lean) check levels 0, 1 and 2, compare two single-step applications with the closed form, and include a target retaining two coordinates.

The [endpoint results](QFixLean/PiOverThree/Boundary.lean) show that initial failure zero stays zero, while initial failure one stays one; the corresponding complementary or target vector component vanishes at every level. [Monotonicity and convergence](QFixLean/PiOverThree/Convergence.lean) show that failure probabilities are nonincreasing and success probabilities are nondecreasing. If `ε₀ < 1`, equivalently if initial success is positive, failure probability and the complementary component's norm tend to zero, while success probability tends to one. This includes `ε₀ = 0` and does not assert convergence of the full state vector with its global phase. [Exact convergence examples](QFixLean/Examples/PiOverThreeConvergence.lean) cover both basis endpoints, the rational qubit state, and a three-dimensional target retaining two coordinates.

The [countable construction](QFixLean/PiOverThree/Construction.lean) records base, source-phase and target-phase primitives and their inverses. Its structural adjoint reverses products and inverts each primitive. [Resource proofs](QFixLean/PiOverThree/Resources.lean) show that its interpretation is exactly the existing recursive unitary. At level `k`, target-phase queries number `qₖ = (3^k - 1)/2`, base `U`/`U†` calls number `3^k`, and source-phase calls number `qₖ`. The same construction's failure probability is `ε₀^(2*qₖ + 1)`, and success is one minus that value. [Complete exact examples](QFixLean/Examples/PiOverThreeResources.lean) connect these costs, probabilities, normalization, monotonicity and limits, including levels 0, 1 and 2 and a three-dimensional target.

These counts describe the unoptimized recursive construction: each target phase or its inverse costs one query, base calls have no target-query cost, and the input source is supplied. Source phases are counted separately. They are not physical gate counts or bit-flip oracle query counts, and do not establish optimal implementation costs. This completes the project's π/3 core verification scope, rather than every application or physical implementation in the 2005 paper. Measurement currently covers two-outcome projection probabilities; mixed states, POVMs, and postmeasurement state updates are outside this interface.

For the 2014 scheme, the [Chebyshev ratio bounds](QFixLean/Polynomial/ChebyshevBounds.lean) and [standard parameter analysis](QFixLean/Polynomial/ChebyshevParameters.lean) prove scalar error guarantees. With positive degree `L` and `0 < δ < 1`, the parameter is `γ = 1 / cosh(arcosh(1/δ)/L)`, and the normalization denominator is exactly `T_L(1/γ) = 1/δ`. For success parameter `λ ∈ [0,1]` satisfying `λ ≥ 1 - γ²`, the signed ratio `T_L(sqrt(1-λ)/γ) / T_L(1/γ)` has absolute value at most `δ`, its square is at most `δ²`, and the complementary scalar model is at least `1 - δ²`. The guarantee holds uniformly above any matched lower bound `λ₀`; these scalar bounds do not require odd degree.

The [conditional quantum guarantee](QFixLean/FixedPoint/Conditional.lean) explicitly assumes that an actual normalized output's failure probability equals this squared ratio, with `λ` taken from the actual initial state's success probability. Under that formula premise and the promise interval, it proves failure at most `δ²` and success at least `1 - δ²` for the same output. [Exact examples](QFixLean/Examples/Chebyshev.lean) include the negative cubic ratio `-1/26` and a degree-one qubit instance whose formula premise is proved directly. The scalar analysis is complete; proving the formula for the explicit P14 positive odd phase sequence, its evolution and recurrence, and its bit-oracle query cost remains future work. These conditional results do not establish that algorithm's correctness or optimality.

Copyright © 2026 QFixLean contributors. QFixLean is licensed under the [Apache License 2.0](LICENSE). Dependencies retain their own licenses and notices.
