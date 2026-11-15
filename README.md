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

[GitHub Actions](https://github.com/longdie/qfixlean/actions/workflows/lean.yml) runs `lake build --wfail` on pushes and pull requests to `main`, and supports manual runs. It downloads Mathlib's compiled cache, builds QFixLean from source, fails on build warnings (including `sorry` warnings), and checks the public import list and unchanged dependency pins. The workflow actions are pinned to commit hashes. These checks supplement the theorem and axiom review; they do not replace it.

Import the public library with `import QFixLean`. After adding modules, update its generated entry point with `lake exe mk_all --lib QFixLean`. To reproduce the CI checks locally, run `lake build --wfail`, `lake exe mk_all --check --lib QFixLean`, and `git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json`.

The representation uses continuous linear operators on complex inner-product spaces, with `EuclideanSpace` for finite-dimensional examples. The code provides [normalized pure states](QFixLean/Basic/State.lean) and [unitary evolution](QFixLean/Basic/Unitary.lean), including inner-product preservation, composition, and recovery by the adjoint or inverse. [Exact qubit examples](QFixLean/Examples/Qubit.lean) cover computational basis states, the superposition `(3/5, 4/5)`, and Pauli X.

The [projection interface](QFixLean/Basic/Projection.lean) covers arbitrary target subspaces, orthogonal complements, and normalized source-state projections. For orthogonal projections, [measurement weights](QFixLean/Basic/Probability.lean) sum to the input's squared norm; for normalized inputs they are probabilities in `[0,1]`. Complex inner-product bridges and global-phase invariance connect these weights to vector calculations. [Exact measurement examples](QFixLean/Examples/Measurement.lean) include a qubit with probabilities `9/25` and `16/25`, and a three-dimensional target retaining two coordinates.

The [selective phase interface](QFixLean/Basic/Phase.lean) describes target and complementary components, same-target measurement invariance, and the overlap in terms of success and failure weights. [Real-angle rotations](QFixLean/Basic/PhaseRotation.lean) use `exp (I * φ)`, with adjoint, inverse, unitarity and source-state action proofs. The [scalar phase factors](QFixLean/Basic/PhaseFactor.lean) include exact π and π/3 values and the identity `(ζ - 1)² = -ζ`. [Phase examples](QFixLean/Examples/Phase.lean) verify exact qubit outputs, probability preservation and a target with two coordinates.

The [π/3 search step](QFixLean/PiOverThree/Step.lean) constructs the unitary `U R_s U† R_P U` with both phases equal to positive π/3. For any normalized source, unitary `U`, and orthogonal target projection, its actual output has failure vector `ζ ε` times the input failure vector, failure probability `ε³`, and success probability `1 - ε³`. Here `ζ = exp (I * π/3)` and `ε` is the failure probability of `U s`. The proof includes the endpoints `ε = 0, 1` and imposes no target-rank restriction.

[Exact search-step examples](QFixLean/Examples/PiOverThree.lean) independently expand the operator product for `(3/5, 4/5)` and verify that failure probability `16/25` becomes `4096/15625 = (16/25)³`.

The [recursive construction](QFixLean/PiOverThree/Recursion.lean) keeps the source and target fixed, starting at `U₀ = U` and replacing each current unitary by its search step. Every level's actual output `Uₖ s` is normalized, with failure probability `ε₀^(3^k)` and success probability `1 - ε₀^(3^k)`. [Exact recursion examples](QFixLean/Examples/PiOverThreeRecursion.lean) check levels 0, 1 and 2, compare two single-step applications with the closed form, and include a target retaining two coordinates.

Monotonicity, convergence, query counts, and the 2014 algorithm remain planned. Measurement currently covers two-outcome projection probabilities; mixed states, POVMs, and postmeasurement state updates are outside this interface.
