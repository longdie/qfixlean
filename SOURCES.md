# Mathematical and software sources

QFixLean uses Mathlib for general mathematics and Lean's kernel for proof
checking. The quantum definitions and algorithm proofs are maintained in this
repository; other quantum formalization libraries are not dependencies.

## Papers

| Reference | Fixed version | Use in QFixLean |
| --- | --- | --- |
| Lov K. Grover, *A different kind of quantum search* | [quant-ph/0503205v1](https://arxiv.org/html/quant-ph/0503205v1) | Positive π/3 search step, recursive construction and probability/resource formulas; Sections 2–4 |
| Theodore J. Yoder, Guang Hao Low, Isaac L. Chuang, *Fixed-point quantum search with an optimal number of queries* | [1409.3305v2](https://arxiv.org/html/1409.3305v2) | Explicit phases, Chebyshev success formula and bit-oracle query model |
| Guanzhong Li, Shiguang Feng, Lvzhou Li, *Revisiting fixed-point quantum search: proof of the quasi-Chebyshev lemma* | [2403.02057v3](https://arxiv.org/html/2403.02057v3) | Recurrence and detailed quasi-Chebyshev proof, including cyclic tangent sums and weighted tilings; Sections 3–4 |

Module comments identify the relevant formulas and any changed conventions.
In particular, P14's λ is a success probability, while P24's λ and w denote
amplitude magnitudes. Exact vector identities retain global phases.

## Mathematical dependency

[Mathlib](https://github.com/leanprover-community/mathlib4), v4.35.0,
commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, is the sole direct library
dependency, under Apache-2.0. It supplies general inner-product, operator,
complex-number, polynomial, analytic and proof-tool interfaces.
`lake-manifest.json` records all transitive dependency revisions. Dependencies
retain their own licenses and notices: their root licenses are Apache-2.0
except for Lean's `Cli` package (MIT); bundled resources can carry additional
notices, including importGraph's frontend assets.

## Quantum-library survey

These fixed snapshots were consulted for representations and proof organization:

| Project | Survey commit | License at that snapshot |
| --- | --- | --- |
| [Physlib](https://github.com/leanprover-community/physlib) | `ca577bfd34ef356be2595528da1ef13a4a405816` | Apache-2.0, with applicable per-file notices |
| [Lean-QuantumAlg](https://github.com/QudeLeap/Lean-QuantumAlg) | `971dc8be8a153a116b6d7cd748f984d545861b00` | Apache-2.0, with applicable per-file notices |
| [quantum-computing-lean](https://github.com/duckki/quantum-computing-lean) | `127ace2fa4a00bfb1f2e40fa7ede1a1de7d86ca2` | No clear license identified in the inspected snapshot; interface study provides no permission to copy its code |

The survey did not compile or certify these libraries. They are not linked into
QFixLean. Development records describe the quantum layer as written within
QFixLean, and no copied or adapted blocks from these snapshots were identified
in the source and history review. This assessment is based on the available
records, not an exhaustive certification of provenance. Any future code reuse
must preserve its source and applicable license notices.

QFixLean itself is distributed under [Apache-2.0](LICENSE). Paper citations and
software dependencies do not make the corresponding external material part of
that license grant.
