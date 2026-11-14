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

The representation uses continuous linear operators on complex inner-product spaces, with `EuclideanSpace` for finite-dimensional examples. The current code proves [selective phase identities and unitarity](QFixLean/Basic/Phase.lean), together with a [symbolic single-step expansion](QFixLean/PiOverThree/Step.lean) and the scalar cancellation needed at π/3. Connecting the overlap to failure probability, specializing the exponential phase, and proving the complete search algorithms remain planned.
