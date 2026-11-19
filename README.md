# Sharp Eliashberg pairing bounds: replay supplement

Davis Rens, SuperMatics Inc. ([ORCID](https://orcid.org/0000-0001-5839-5197)).

This repository accompanies the preprint [Sharp Eliashberg pairing bounds for an energy-dependent density of states](https://doi.org/10.5281/zenodo.24364879). The archived software release is [10.5281/zenodo.24364881](https://doi.org/10.5281/zenodo.24364881). The DOI links resolve after the records are published.

The paper concerns linearized scalar Migdal–Eliashberg onset under its stated positive-branch and self-consistency hypotheses. It does not establish a general bound beyond those hypotheses, or identify the linear onset with a thermodynamic transition in every model.

## Replay

From `replay/`, run Python 3 on `g3x_replay.py`, `g3x_independent.py`, `asym_guard.py`, `transfer_cutoff.py`, `screening_replay.py`, `window.py`, and `closure.py`. These use exact rational arithmetic and include the specified mutant checks. `qmc_conversions.py` is a separate floating-point convention cross-check requiring SciPy; its tolerance comparison is not a rigorous error bound.

With the toolchain in `replay/lean-toolchain`, `lake exe cache get` followed by `lake build` checks `Core.lean` and `Finite.lean` using the pinned manifest. These files formalize finite algebraic components, not the full paper theorem. See the paper for definitions, hypotheses, and the proof.

The replay code and Lean sources are licensed under Apache-2.0. The paper is distributed separately. The source snapshot is from manuscript commit `b12338aad5`.

AI agents contributed proofs, certificates, code, Lean sources and manuscript drafts and edits under the author's direction and review.
