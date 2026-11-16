# GraphEK — Shifted Eneström–Kakeya disks for set systems, formalised in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24271250.svg)](https://doi.org/10.5281/zenodo.24271250)
[![Lean Action CI](https://github.com/sajadcosmos/GraphEK/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/sajadcosmos/GraphEK/actions/workflows/lean_action_ci.yml)

This repository contains the complete Lean 4 formalisation, together with the numerical
experiments and figures, accompanying the paper

> **S. A. Sheikh**, *Shifted Eneström–Kakeya disks for set systems: extension bounds, matroid
> closures, domination and random graphs, with a complete Lean 4 formalisation* (submitted).

Author: Sajad A. Sheikh, Department of Mathematics, University of Kashmir, South Campus,
Anantnag 192101, Jammu and Kashmir, India.

---

## Overview

The paper locates the complex zeros of generating polynomials of **down-closed** set systems
(simplicial complexes, e.g. independent sets of a graph or of a matroid) and **up-closed** set
systems (filters, e.g. dominating sets or spanning sets of a matroid). The common mechanism is
that coefficient ratios are governed by *one-element extensions*: a uniform lower bound
`g_k` on the number of extensions of every `k`-face bounds all ratios `f_k / f_{k+1}`, and a
shifted-disk refinement of the Eneström–Kakeya theorem (due to Aziz and Zargar) turns the
resulting gap into an explicit disk `|z + R − ρ| ≤ R`.

Main results (all formalised):

| Result | Statement (informal) |
|---|---|
| Extension-bounded complexes | If every `k`-face of a rank-`d` complex has at least `g_k` extensions, all zeros lie in an explicit disk built from `(g_k)`. |
| Pure complexes / well-covered graphs | All zeros satisfy `|z + (d+1)/2| ≤ d`; for well-covered graphs, also a degree-sharpened radius `α/μ`, `μ = n − (α−1)(Δ+1)`, attained by every complete graph. |
| Apollonius disks | Every complex on `n` points has `|1 + ((n+1)/2) z| ≤ n|z|` at every zero; every graph satisfies an analogous zero-free disk governed by its **average degree**. |
| Random graphs `G(n,p)` | Deterministic edge-count / minimum-degree form of the zero-free region (combined in the paper with Hoeffding's inequality). |
| Filters and domination | Every filter containing its ground set has all zeros in `|z + (n+1)/2| ≤ n`; pure filters have a zero-free disk about the origin — applied to well-dominated and well-totally-dominated graphs. |
| Matroids with bounded closures | If closures of independent `k`-sets have at most `φ(k)` elements, explicit shifted disks for the independence polynomial (built on Mathlib's `Matroid`). |

---

## Repository layout

```
GraphEK.lean            -- the complete formalisation (single file, 1749 lines)
lakefile.toml           -- Lake project file (depends on Mathlib)
lean-toolchain          -- leanprover/lean4:v4.36.0-rc2
lake-manifest.json      -- pinned dependency versions
numerics/               -- Python scripts for the numerical experiments and figures
  verify.py             --   independence / domination polynomials, well-covered graphs
  verify_new.py         --   well-dominated graphs, average-degree disks, matroid checks
  verify_matroid.py     --   representable matroids, PG/AG geometries, forests, random graphs
  matroid_tools.py      --   closed forms for PG(r−1,q), AG(r−1,q), forests of K_p
  figures.py, figure_wd.py, figure_matroid.py  -- figure generation
  summary*.json         --   recorded outputs of the verification runs
  requirements.txt
figures/                -- figures of the paper (PDF and PNG)
.github/workflows/      -- continuous integration (builds the Lean file on every push)
```

---

## Building and checking the formalisation

Requirements: [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager).

```bash
git clone https://github.com/sajadcosmos/GraphEK.git
cd GraphEK
lake exe cache get      # download prebuilt Mathlib (a few minutes)
lake build              # check GraphEK.lean
```

The build finishes with `Build completed successfully`. The file contains **no `sorry`**, and

```lean
#print axioms GraphEK.matroid_closure_shifted
```

(and likewise for every main theorem) reports only the three standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

Toolchain: Lean `v4.36.0-rc2`, Mathlib tag `v4.36.0-rc2`.

---

## Structure of `GraphEK.lean`

| Part | Content | Key declarations |
|---|---|---|
| I | Shifted Eneström–Kakeya disk (rescaled Aziz–Zargar) and its reciprocal form | `P`, `mul_identity`, `tail_bound`, `shifted_disk`, `ek_outer`, `P_reflect`, `shifted_inner`, `ek_inner` |
| II | Extension counting for independent sets; well-covered graphs | `ext_identity`, `ic_zero`, `ic_one`, `ext_upper`, `ext_lower_degree`, `exists_maxIndep_superset`, `wc_ext_lower`, `wc_ratio`, `ratio_upper` |
| III | Zero regions for independence polynomials | `wc_shifted`, `wc_disk`, `wc_shifted_half`, `wc_degree`, `indep_inner` |
| IV | Up-closed families, domination, total domination | `up_ratio`, `up_shifted`, `up_disks`, `domination_disks`, `total_domination_disks` |
| V | Half-plane, sector and Apollonius consequences | `shifted_re`, `apollonius_re`, `wc_sector`, `indep_apollonius`, `domination_sector` |
| VI | Pure complexes, essential elements, pure filters, well-dominated graphs, average degree | `down_identity`, `pure_shifted`, `down_apollonius`, `essential_subset_minimal`, `up_reverse`, `pure_filter_inner`, `well_dominated_inner`, `well_totally_dominated_inner`, `two_ic_two`, `indep_avg`, `indep_avg_simple` |
| VII | Extension-bounded complexes; parametric and edge-count regions | `down_ratio_lower`, `down_ratio_exact`, `down_ext_shifted`, `down_ext_disk`, `indep_avg_param`, `indep_edges`, `indep_edges_mindeg` |
| VIII | Matroids with bounded closures (Mathlib `Matroid`) | `clCard`, `matroid_ext_closure`, `matroid_pure`, `matroid_closure_shifted` |

### Correspondence with the paper

| Paper | Lean |
|---|---|
| Thm 2.2–2.3, Cor 2.4 (Eneström–Kakeya, Aziz–Zargar, reciprocal form) | `ek_outer`, `ek_inner`, `shifted_disk`, `shifted_inner` |
| Thm 2.5 (extension identity), Thm 2.6 (local LYM), Thm 2.7 (Burcroff–O'Brien) | `down_identity`, `ext_identity`, `up_ratio`, `up_reverse` |
| Lemma 2.8, Thm 2.9 (Brown–Dilcher–Nowakowski) | `dext_upper`, `pure_dext_lower`, `ext_upper`, `ext_lower_degree`, `wc_disk` |
| Thm 3.1, Prop 3.2 (extension-bounded / extension-regular complexes) | `down_ext_shifted`, `down_ext_disk`, `down_ratio_lower`, `down_ratio_exact` |
| Cor 3.3, Thm 3.4 (pure complexes, Apollonius disk) | `pure_shifted`, `wc_sector`, `down_apollonius` |
| Prop 3.5, Thm 3.6 (ratio profile, well-covered graphs) | `ratio_upper`, `two_ic_two`, `wc_ratio`, `wc_shifted_half`, `wc_degree` |
| Thm 3.7 (average-degree Apollonius disk) | `indep_avg`, `indep_avg_param`, `indep_avg_simple`, `indep_inner` |
| Thm 3.8 (random graphs, deterministic part) | `indep_edges_mindeg`, `indep_edges` |
| Thm 3.9–3.11 (filters, pure filters, domination) | `up_shifted`, `up_disks`, `pure_filter_inner`, `domination_disks`, `well_dominated_inner`, `well_totally_dominated_inner` |
| Thm 3.12 and Cor 3.13–3.18 (matroids) | `matroid_closure_shifted`, `down_apollonius`, `pure_filter_inner` |

### What is (and is not) formalised

Every theorem of the paper is formalised, including the known results it builds on. Three
standard inputs are **not** formalised; each enters a formal theorem only as an explicit
hypothesis:

* closure counts in simple representable matroids and in affine geometries, and the bound on
  closures of forests in graphic matroids — these enter through the closure-bound hypothesis
  `φ` of `matroid_closure_shifted`;
* Hoeffding's inequality — the random-graph theorem is formalised in its deterministic form
  (`indep_edges_mindeg`), whose hypotheses `|E| ≥ m₀` and `δ ≥ δ₀` are the events controlled by
  Hoeffding's inequality in the paper.

### Conventions

* Polynomials are finite sums `P a d z = ∑_{j ≤ d} a_j z^j` with `a : ℕ → ℝ`, `z : ℂ`.
* Set systems are predicates on `Finset V` for a `Fintype V`; graphs are Mathlib's
  `SimpleGraph V` with decidable adjacency; matroids are Mathlib's `Matroid V` with ground set
  `Set.univ`.
* Independence and domination polynomials are always the full sums up to `n = Fintype.card V`;
  facts such as `f_d > 0` or `f_k = 0` beyond the rank are derived, not assumed.

---

## Numerical experiments

```bash
cd numerics
pip install -r requirements.txt
python verify.py          # writes summary.json
python verify_new.py      # writes summary_new.json
python verify_matroid.py  # writes summary_matroid.json
python figures.py; python figure_wd.py; python figure_matroid.py   # regenerate ../figures
```

The checks cover all graphs of order at most 7 (networkx graph atlas), random graphs `G(n,p)`
with `n ≤ 14`, coronas and unions of cliques, random simple binary matroids, projective and affine
geometries, graphic matroids and uniform matroids. No violation of any theorem occurs.

---

## Citation

If you use this code, please cite the paper (reference to be updated on publication) and the
archived release:

> S. A. Sheikh, *GraphEK: Lean 4 formalisation of shifted Eneström–Kakeya disks for set systems*,
> version 1.0.0, Zenodo, 2026. https://doi.org/10.5281/zenodo.24271250

See also [`CITATION.cff`](CITATION.cff).

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
