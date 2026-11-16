/-
Copyright (c) 2026 Sajad A. Sheikh. All rights reserved.
Released under Apache 2.0 license.
Author: Sajad A. Sheikh, Department of Mathematics, University of Kashmir,
        South Campus, Anantnag, 192101, Jammu and Kashmir, India

# Eneström–Kakeya disks for independence and domination polynomials

Complete formalisation (single file, no `sorry`, standard axioms only) of the paper
"Eneström–Kakeya disks for independence and domination polynomials: extension counts,
degree sharpening, and a complete Lean 4 formalisation".

* Part I   – shifted Eneström–Kakeya disk (rescaled Aziz–Zargar) and its reciprocal form.
* Part II  – extension identity `(k+1) i_{k+1} = ∑_S |V \ N[S]|`, extension bounds via
             `δ`, `Δ` and well-coveredness, up-closed ratio inequality.
* Part III – zero regions for independence polynomials (well-covered and all graphs).
* Part IV  – zero regions for filters, domination and total domination polynomials.
* Part V   – half-plane, sector and Apollonius consequences.
* Part VI  – pure complexes, the essential-element inequality for filters (counting argument
             of Burcroff–O'Brien), pure filters, well-dominated and well-totally-dominated
             graphs, average-degree Apollonius disk.
* Part VII – extension-bounded complexes; parametric, edge-count and minimum-degree regions
             (deterministic input of the random-graph theorem).
* Part VIII – matroids with bounded closures (via Mathlib's `Matroid`).

Parts I–IV also formalise the known results the paper quotes in its preliminaries
(Eneström–Kakeya, Aziz–Zargar, the extension identity, the local LYM inequality,
the Brown–Dilcher–Nowakowski disk), because the new theorems are built on them.

Toolchain: Lean `v4.36.0-rc2`, Mathlib tag `v4.36.0-rc2`.
-/
import Mathlib

open Finset

set_option linter.unusedSectionVars false

namespace GraphEK

/-! ## Part I. Shifted Eneström–Kakeya disks -/

/-- The polynomial `∑_{j=0}^{d} a_j z^j` with real coefficients, evaluated at `z : ℂ`. -/
noncomputable def P (a : ℕ → ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (d + 1), (a j : ℂ) * z ^ j

/-- Telescoping identity for `(ρ - z) p(z)`. -/
lemma mul_identity (a : ℕ → ℝ) (ρ : ℝ) (z : ℂ) (d : ℕ) :
    ((ρ : ℂ) - z) * P a d z =
      ((ρ * a 0 : ℝ) : ℂ) + (∑ j ∈ range d, ((ρ * a (j + 1) - a j : ℝ) : ℂ) * z ^ (j + 1))
        - (a d : ℂ) * z ^ (d + 1) := by
  induction d with
  | zero => simp [P]; ring
  | succ d ih =>
    have h : P a (d + 1) z = P a d z + (a (d + 1) : ℂ) * z ^ (d + 1) := by
      simp [P, sum_range_succ]
    rw [h, mul_add, ih, sum_range_succ]
    push_cast
    ring

/-- The basic real estimate behind the Eneström–Kakeya argument. -/
lemma tail_bound (a : ℕ → ℝ) (ρ t : ℝ) (hρ : 0 ≤ ρ) (ht : ρ ≤ t) (ha : ∀ j, 0 ≤ a j) :
    ∀ m : ℕ, (∀ j, j < m → a j ≤ ρ * a (j + 1)) →
      ρ * a 0 + ∑ j ∈ range m, (ρ * a (j + 1) - a j) * t ^ (j + 1) ≤ ρ * a m * t ^ m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ih' := ih (fun j hj => hm j (by omega))
    rw [sum_range_succ]
    have ht0 : 0 ≤ t := le_trans hρ ht
    have h1 : 0 ≤ a m * t ^ m * (t - ρ) := by
      have := ha m; positivity
    have : ρ * a m * t ^ m + (ρ * a (m + 1) - a m) * t ^ (m + 1)
        = ρ * a (m + 1) * t ^ (m + 1) - a m * t ^ m * (t - ρ) := by ring
    linarith

/-- **Theorem A (shifted Eneström–Kakeya disk).**
Let `a_0,…,a_d ≥ 0`, `a_d > 0`, `d ≥ 1`, `0 ≤ ρ ≤ R`, with `a_j ≤ ρ a_{j+1}` for `j ≤ d-2`
and `a_{d-1} ≤ R a_d`. Then every zero `z` of `∑ a_j z^j` satisfies `|z + (R - ρ)| ≤ R`. -/
theorem shifted_disk (a : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (ha : ∀ j, 0 ≤ a j) (had : 0 < a d)
    (hmono : ∀ j, j + 2 ≤ d → a j ≤ ρ * a (j + 1))
    (hlast : a (d - 1) ≤ R * a d)
    (z : ℂ) (hz : P a d z = 0) : ‖z + ((R - ρ : ℝ) : ℂ)‖ ≤ R := by
  by_cases hsmall : ‖z‖ ≤ ρ
  · calc ‖z + ((R - ρ : ℝ) : ℂ)‖ ≤ ‖z‖ + ‖((R - ρ : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + (R - ρ) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ R := by linarith
  replace hsmall := not_le.mp hsmall
  set t := ‖z‖ with ht_def
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have he : e + 1 - 1 = e := by omega
  rw [he] at hlast
  have ht0 : 0 < t := lt_of_le_of_lt hρ hsmall
  -- the identity, with the top two terms regrouped
  have hid := mul_identity a ρ z (e + 1)
  rw [hz, mul_zero, sum_range_succ] at hid
  set A : ℂ := ((ρ * a 0 : ℝ) : ℂ) + (∑ j ∈ range e, ((ρ * a (j + 1) - a j : ℝ) : ℂ) * z ^ (j + 1))
      + ((R * a (e + 1) - a e : ℝ) : ℂ) * z ^ (e + 1) with hA
  have key : (a (e + 1) : ℂ) * z ^ (e + 1) * (z + ((R - ρ : ℝ) : ℂ)) = A := by
    rw [hA]
    have := hid
    push_cast at this ⊢
    linear_combination this
  -- bound the norm of A
  have hcoef : ∀ j ∈ range e, 0 ≤ ρ * a (j + 1) - a j := by
    intro j hj
    have := hmono j (by simp at hj; omega)
    linarith
  have hsum : ‖∑ j ∈ range e, ((ρ * a (j + 1) - a j : ℝ) : ℂ) * z ^ (j + 1)‖
      ≤ ∑ j ∈ range e, (ρ * a (j + 1) - a j) * t ^ (j + 1) := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine sum_congr rfl (fun j hj => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hcoef j hj)]
  have hlastc : 0 ≤ R * a (e + 1) - a e := by linarith
  have hA_le : ‖A‖ ≤ ρ * a 0 + (∑ j ∈ range e, (ρ * a (j + 1) - a j) * t ^ (j + 1))
      + (R * a (e + 1) - a e) * t ^ (e + 1) := by
    rw [hA]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ hsum)) ?_
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ (ha 0))]
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlastc]
  have htail := tail_bound a ρ t hρ hsmall.le ha e (fun j hj => hmono j (by omega))
  have hstep : ρ * a e * t ^ e ≤ a e * t ^ (e + 1) := by
    have : 0 ≤ a e * t ^ e := mul_nonneg (ha e) (pow_nonneg ht0.le _)
    rw [pow_succ]; nlinarith
  have hA_le2 : ‖A‖ ≤ R * a (e + 1) * t ^ (e + 1) := by nlinarith
  have hnorm : ‖A‖ = a (e + 1) * t ^ (e + 1) * ‖z + ((R - ρ : ℝ) : ℂ)‖ := by
    rw [← key, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos had]
  have hpos : 0 < a (e + 1) * t ^ (e + 1) := mul_pos had (pow_pos ht0 _)
  rw [hnorm] at hA_le2
  have : a (e + 1) * t ^ (e + 1) * ‖z + ((R - ρ : ℝ) : ℂ)‖ ≤ a (e + 1) * t ^ (e + 1) * R := by
    linarith
  exact le_of_mul_le_mul_left this hpos

/-- **Corollary A1 (Eneström–Kakeya, outer radius).** -/
theorem ek_outer (a : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ha : ∀ j, 0 ≤ a j) (had : 0 < a d)
    (hmono : ∀ j, j + 1 ≤ d → a j ≤ ρ * a (j + 1))
    (z : ℂ) (hz : P a d z = 0) : ‖z‖ ≤ ρ := by
  have h := shifted_disk a d hd ρ ρ hρ le_rfl ha had (fun j hj => hmono j (by omega))
    (hmono (d - 1) (by omega) |>.trans_eq (by congr 2; omega)) z hz
  simpa using h

/-- Reflection: `P a d z = z^d · P (a ∘ (d - ·)) d z⁻¹` for `z ≠ 0`. -/
lemma P_reflect (a : ℕ → ℝ) (d : ℕ) (z : ℂ) (hz : z ≠ 0) :
    P a d z = z ^ d * P (fun j => a (d - j)) d z⁻¹ := by
  unfold P
  rw [mul_sum]
  have : ∀ j ∈ range (d + 1), z ^ d * ((a (d - j) : ℂ) * z⁻¹ ^ j)
      = (a (d - j) : ℂ) * z ^ (d - j) := by
    intro j hj
    have hj' : j ≤ d := by simp at hj; omega
    have : z ^ d = z ^ (d - j) * z ^ j := by rw [← pow_add]; congr 1; omega
    rw [this, inv_pow]
    field_simp
  rw [sum_congr rfl this]
  have := sum_range_reflect (fun j => (a j : ℂ) * z ^ j) (d + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this]

/-- **Theorem A' (reciprocal shifted disk).** If `a_0 > 0`, `a_{j+1} ≤ σ a_j` for `1 ≤ j ≤ d-1`,
`a_1 ≤ T a_0` and `0 ≤ σ ≤ T`, then every zero satisfies `|1 + (T - σ) z| ≤ T |z|`. -/
theorem shifted_inner (a : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) (σ T : ℝ) (hσ : 0 ≤ σ) (hσT : σ ≤ T)
    (ha : ∀ j, 0 ≤ a j) (ha0 : 0 < a 0)
    (hmono : ∀ j, 1 ≤ j → j + 1 ≤ d → a (j + 1) ≤ σ * a j)
    (hfirst : a 1 ≤ T * a 0)
    (z : ℂ) (hz : P a d z = 0) : ‖1 + ((T - σ : ℝ) : ℂ) * z‖ ≤ T * ‖z‖ := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    have : P a d 0 = (a 0 : ℂ) := by
      unfold P; rw [sum_range_succ']; simp
    rw [this] at hz
    exact absurd (by exact_mod_cast hz : a 0 = 0) (ne_of_gt ha0)
  set b : ℕ → ℝ := fun j => a (d - j) with hb
  have hPb : P b d z⁻¹ = 0 := by
    have := P_reflect a d z hz0
    rw [hz] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd (pow_eq_zero_iff (by omega) |>.mp h) hz0
    · exact h
  have hw := shifted_disk b d hd σ T hσ hσT (fun j => ha _) (by simp [hb, ha0])
    (by
      intro j hj
      have := hmono (d - j - 1) (by omega) (by omega)
      simp only [hb]
      have e1 : d - j = d - j - 1 + 1 := by omega
      have e2 : d - (j + 1) = d - j - 1 := by omega
      rw [e2, e1]; exact this)
    (by
      simp only [hb]
      have e1 : d - (d - 1) = 1 := by omega
      rw [e1, Nat.sub_self]; exact hfirst) z⁻¹ hPb
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  calc ‖1 + ((T - σ : ℝ) : ℂ) * z‖ = ‖z‖ * ‖z⁻¹ + ((T - σ : ℝ) : ℂ)‖ := by
        rw [← norm_mul, mul_add, mul_inv_cancel₀ hz0, mul_comm]
    _ ≤ ‖z‖ * T := mul_le_mul_of_nonneg_left hw hzn.le
    _ = T * ‖z‖ := mul_comm _ _

/-- **Corollary A2 (Eneström–Kakeya, inner radius).** -/
theorem ek_inner (a : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ)
    (ha : ∀ j, 0 ≤ a j) (ha0 : 0 < a 0)
    (hmono : ∀ j, j + 1 ≤ d → a (j + 1) ≤ σ * a j)
    (z : ℂ) (hz : P a d z = 0) : 1 ≤ σ * ‖z‖ := by
  have h := shifted_inner a d hd σ σ hσ le_rfl ha ha0 (fun j _ hj => hmono j hj)
    (hmono 0 hd) z hz
  simpa using h

/-! ## Part II. Extension counting for independent sets -/

section Indep

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `s` is an independent set of `G`. -/
def IsIndep (s : Finset V) : Prop := ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

instance (s : Finset V) : Decidable (IsIndep G s) := by unfold IsIndep; infer_instance

/-- The independent `k`-sets of `G`. -/
def indepSets (k : ℕ) : Finset (Finset V) := (univ.powersetCard k).filter (IsIndep G)

/-- `i_k(G)`, the number of independent `k`-sets. -/
def ic (k : ℕ) : ℕ := #(indepSets G k)

/-- The extension set `V \ N[s]` of `s`: vertices that can be added to `s`. -/
def extSet (s : Finset V) : Finset V := univ.filter (fun v => v ∉ s ∧ ∀ u ∈ s, ¬ G.Adj u v)

variable {G}

lemma mem_indepSets {k : ℕ} {s : Finset V} : s ∈ indepSets G k ↔ #s = k ∧ IsIndep G s := by
  simp [indepSets, mem_powersetCard]

lemma IsIndep.mono {s t : Finset V} (h : IsIndep G t) (hst : s ⊆ t) : IsIndep G s :=
  fun u hu v hv => h u (hst hu) v (hst hv)

lemma mem_extSet {s : Finset V} {v : V} : v ∈ extSet G s ↔ v ∉ s ∧ ∀ u ∈ s, ¬ G.Adj u v := by
  simp [extSet]

lemma isIndep_insert {s : Finset V} {v : V} (hs : IsIndep G s) (hv : v ∈ extSet G s) :
    IsIndep G (insert v s) := by
  rw [mem_extSet] at hv
  intro u hu w hw
  rw [mem_insert] at hu hw
  rcases hu with rfl | hu <;> rcases hw with rfl | hw
  · exact G.irrefl
  · exact fun h => hv.2 w hw h.symm
  · exact hv.2 u hu
  · exact hs u hu w hw

lemma card_above {k : ℕ} {s : Finset V} (hs : s ∈ indepSets G k) :
    #((indepSets G (k + 1)).filter (fun t => s ⊆ t)) = #(extSet G s) := by
  rw [mem_indepSets] at hs
  have himg : (indepSets G (k + 1)).filter (fun t => s ⊆ t)
      = (extSet G s).image (fun v => insert v s) := by
    ext t
    simp only [mem_filter, mem_image, mem_indepSets]
    constructor
    · rintro ⟨⟨htc, hti⟩, hst⟩
      have hc : #(t \ s) = 1 := by rw [card_sdiff_of_subset hst]; omega
      obtain ⟨v, hv⟩ := card_eq_one.mp hc
      have hvt : v ∈ t \ s := by rw [hv]; exact mem_singleton_self v
      rw [mem_sdiff] at hvt
      refine ⟨v, mem_extSet.mpr ⟨hvt.2, fun u hu => hti u (hst hu) v hvt.1⟩, ?_⟩
      rw [← union_sdiff_of_subset hst, hv, insert_eq, union_comm]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨?_, isIndep_insert hs.2 hv⟩, subset_insert v s⟩
      rw [card_insert_of_notMem (mem_extSet.mp hv).1, hs.1]
  rw [himg, card_image_of_injOn]
  intro v hv w hw hvw
  simp only at hvw
  have hv' := (mem_extSet.mp (mem_coe.mp hv)).1
  have : v ∈ insert w s := by rw [← hvw]; exact mem_insert_self v s
  rcases mem_insert.mp this with h | h
  · exact h
  · exact absurd h hv'

lemma card_below {k : ℕ} {t : Finset V} (ht : t ∈ indepSets G (k + 1)) :
    #((indepSets G k).filter (fun s => s ⊆ t)) = k + 1 := by
  rw [mem_indepSets] at ht
  have : (indepSets G k).filter (fun s => s ⊆ t) = t.powersetCard k := by
    ext s
    simp only [mem_filter, mem_indepSets, mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2, ht.2.mono h1⟩, h1⟩
  rw [this, card_powersetCard, ht.1, Nat.choose_succ_self_right]

/-- **Theorem B(i) (extension identity).** `(k+1) i_{k+1} = ∑_{S ∈ 𝓘_k} |V \ N[S]|`. -/
theorem ext_identity (k : ℕ) :
    (k + 1) * ic G (k + 1) = ∑ s ∈ indepSets G k, #(extSet G s) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun s t : Finset V => s ⊆ t)
    (s := indepSets G k) (t := indepSets G (k + 1))
  simp only [bipartiteAbove, bipartiteBelow] at h
  rw [sum_congr rfl (fun s hs => card_above hs), sum_congr rfl (fun t ht => card_below ht)] at h
  rw [h, sum_const, smul_eq_mul, ic, mul_comm]

lemma ic_zero : ic G 0 = 1 := by
  have : indepSets G 0 = {∅} := by
    ext s
    simp only [mem_indepSets, mem_singleton, card_eq_zero]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, by simp [IsIndep]⟩
  simp [ic, this]

lemma extSet_empty : extSet G ∅ = univ := by ext v; simp [mem_extSet]

lemma ic_one : ic G 1 = Fintype.card V := by
  have h := ext_identity (G := G) 0
  have : indepSets G 0 = {∅} := by
    ext s
    simp only [mem_indepSets, mem_singleton, card_eq_zero]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, by simp [IsIndep]⟩
  rw [this, sum_singleton, extSet_empty, card_univ] at h
  simpa using h

/-- Upper bound on extensions: `|V \ N[S]| + k + δ ≤ n` for an independent `k`-set, `k ≥ 1`. -/
lemma ext_upper {k : ℕ} (hk : 1 ≤ k) {s : Finset V} (hs : s ∈ indepSets G k) :
    #(extSet G s) + k + G.minDegree ≤ Fintype.card V := by
  rw [mem_indepSets] at hs
  obtain ⟨u, hu⟩ : s.Nonempty := card_pos.mp (by omega)
  have hsub : extSet G s ⊆ univ \ (s ∪ G.neighborFinset u) := by
    intro v hv
    rw [mem_extSet] at hv
    simp only [mem_sdiff, mem_univ, mem_union, SimpleGraph.mem_neighborFinset, true_and, not_or]
    exact ⟨hv.1, hv.2 u hu⟩
  have hdisj : Disjoint s (G.neighborFinset u) := by
    rw [disjoint_left]
    intro x hx hxn
    rw [SimpleGraph.mem_neighborFinset] at hxn
    exact hs.2 u hu x hx hxn
  have h1 := card_le_card hsub
  rw [card_univ_sdiff, card_union_of_disjoint hdisj, G.card_neighborFinset_eq_degree, hs.1] at h1
  have h2 : #(s ∪ G.neighborFinset u) ≤ Fintype.card V := card_le_univ _
  rw [card_union_of_disjoint hdisj, G.card_neighborFinset_eq_degree, hs.1] at h2
  have h3 := G.minDegree_le_degree u
  omega

/-- Lower bound on extensions: `n ≤ |V \ N[S]| + k (Δ + 1)` for any `k`-set. -/
lemma ext_lower_degree {k : ℕ} {s : Finset V} (hs : #s = k) :
    Fintype.card V ≤ #(extSet G s) + k * (G.maxDegree + 1) := by
  have hcov : (univ : Finset V) ⊆ extSet G s ∪ s.biUnion (fun u => insert u (G.neighborFinset u)) := by
    intro v _
    by_cases h : v ∈ extSet G s
    · exact mem_union_left _ h
    · apply mem_union_right
      rw [mem_extSet] at h
      push Not at h
      rw [mem_biUnion]
      by_cases hv : v ∈ s
      · exact ⟨v, hv, mem_insert_self _ _⟩
      · obtain ⟨u, hu, hadj⟩ := h hv
        exact ⟨u, hu, mem_insert_of_mem ((G.mem_neighborFinset u v).mpr hadj)⟩
  have h1 := card_le_card hcov
  rw [card_univ] at h1
  have h2 := card_union_le (extSet G s) (s.biUnion (fun u => insert u (G.neighborFinset u)))
  have h3 := card_biUnion_le (s := s) (t := fun u => insert u (G.neighborFinset u))
  have h4 : ∑ u ∈ s, #(insert u (G.neighborFinset u)) ≤ ∑ _u ∈ s, (G.maxDegree + 1) := by
    apply sum_le_sum
    intro u _
    refine (card_insert_le _ _).trans ?_
    rw [G.card_neighborFinset_eq_degree]
    exact Nat.add_le_add_right (G.degree_le_maxDegree u) 1
  rw [sum_const, smul_eq_mul, hs] at h4
  omega

/-- A maximal independent set. -/
def IsMaxIndep (s : Finset V) : Prop := IsIndep G s ∧ ∀ v, v ∉ s → ¬ IsIndep G (insert v s)

variable (G) in
/-- `G` is well covered with independence number `α`: all maximal independent sets have size `α`. -/
def WellCovered (α : ℕ) : Prop := ∀ s : Finset V, IsMaxIndep (G := G) s → #s = α

lemma exists_maxIndep_superset {s : Finset V} (hs : IsIndep G s) :
    ∃ M, s ⊆ M ∧ IsMaxIndep (G := G) M := by
  let F := (univ : Finset (Finset V)).filter (fun t => IsIndep G t ∧ s ⊆ t)
  have hF : F.Nonempty := ⟨s, by simp [F, hs]⟩
  obtain ⟨M, hM, hmax⟩ := exists_max_image F card hF
  simp only [F, mem_filter, mem_univ, true_and] at hM
  refine ⟨M, hM.2, hM.1, fun v hv hind => ?_⟩
  have := hmax (insert v M) (by simp [F, hind, hM.2.trans (subset_insert v M)])
  rw [card_insert_of_notMem hv] at this
  omega

lemma wc_ext_lower {α k : ℕ} (hwc : WellCovered G α) {s : Finset V} (hs : s ∈ indepSets G k) :
    α ≤ #(extSet G s) + k := by
  rw [mem_indepSets] at hs
  obtain ⟨M, hsM, hM⟩ := exists_maxIndep_superset hs.2
  have hMc := hwc M hM
  have hsub : M \ s ⊆ extSet G s := by
    intro v hv
    rw [mem_sdiff] at hv
    exact mem_extSet.mpr ⟨hv.2, fun u hu => hM.1 u (hsM hu) v hv.1⟩
  have h1 := card_le_card hsub
  have h2 := card_sdiff_add_card_eq_card hsM
  omega

lemma wc_ic_pos {α : ℕ} (hwc : WellCovered G α) : 0 < ic G α := by
  obtain ⟨M, -, hM⟩ := exists_maxIndep_superset (G := G) (s := ∅) (by simp [IsIndep])
  exact card_pos.mpr ⟨M, mem_indepSets.mpr ⟨hwc M hM, hM.1⟩⟩

lemma wc_ic_eq_zero {α k : ℕ} (hwc : WellCovered G α) (hk : α < k) : ic G k = 0 := by
  rw [ic, card_eq_zero, eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_indepSets] at hs
  obtain ⟨M, hsM, hM⟩ := exists_maxIndep_superset hs.2
  have := card_le_card hsM
  rw [hwc M hM] at this
  omega

lemma wc_alpha_le {α : ℕ} (hwc : WellCovered G α) : α ≤ Fintype.card V := by
  obtain ⟨s, hs⟩ := card_pos.mp (wc_ic_pos hwc)
  rw [mem_indepSets] at hs
  rw [← hs.1]; exact card_le_univ s

/-- For a well-covered graph the full independence polynomial equals its truncation at `α`. -/
lemma wc_poly_eq {α : ℕ} (hwc : WellCovered G α) (z : ℂ) :
    P (fun k => (ic G k : ℝ)) (Fintype.card V) z = P (fun k => (ic G k : ℝ)) α z := by
  unfold P
  rw [← sum_range_add_sum_Ico _ (Nat.add_le_add_right (wc_alpha_le hwc) 1)]
  rw [add_eq_left]
  apply sum_eq_zero
  intro k hk
  rw [mem_Ico] at hk
  show ((ic G k : ℝ) : ℂ) * z ^ k = 0
  rw [wc_ic_eq_zero hwc (by omega)]
  simp

/-- **Theorem C (ratio bounds, well-covered).**
`max(α - k, n - k(Δ+1)) · i_k ≤ (k+1) i_{k+1}`. -/
theorem wc_ratio {α : ℕ} (hwc : WellCovered G α) (k : ℕ) :
    max (α - k) (Fintype.card V - k * (G.maxDegree + 1)) * ic G k ≤ (k + 1) * ic G (k + 1) := by
  rw [ext_identity, ic, mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro s hs
  apply max_le
  · have := wc_ext_lower hwc hs; omega
  · have := ext_lower_degree (G := G) (mem_indepSets.mp hs).1; omega

/-- **Theorem C' (ratio bounds, all graphs).** `(k+1) i_{k+1} + (k + δ) i_k ≤ n i_k` for `k ≥ 1`. -/
theorem ratio_upper {k : ℕ} (hk : 1 ≤ k) :
    (k + 1) * ic G (k + 1) + (k + G.minDegree) * ic G k ≤ Fintype.card V * ic G k := by
  have h : ∑ s ∈ indepSets G k, (#(extSet G s) + (k + G.minDegree))
      ≤ ∑ _s ∈ indepSets G k, Fintype.card V :=
    sum_le_sum (fun s hs => by have := ext_upper hk hs; omega)
  rw [sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at h
  rw [ext_identity, ic]
  linarith [mul_comm (#(indepSets G k)) (k + G.minDegree), mul_comm (#(indepSets G k)) (Fintype.card V)]

end Indep

/-! ## Part III. Zero regions for independence polynomials -/

section IndepRoots

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Theorem D (well-covered graphs, parametric shifted disk).** -/
theorem wc_shifted {α : ℕ} (hα : 1 ≤ α) (hwc : WellCovered G α) (ρ R : ℝ) (hρ : 0 ≤ ρ)
    (hρR : ρ ≤ R)
    (hrat : ∀ k, k + 2 ≤ α →
      ((k : ℝ) + 1) ≤ ρ * ((max (α - k) (Fintype.card V - k * (G.maxDegree + 1)) : ℕ) : ℝ))
    (hlast : (α : ℝ) ≤ R * ((max 1 (Fintype.card V - (α - 1) * (G.maxDegree + 1)) : ℕ) : ℝ))
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖z + ((R - ρ : ℝ) : ℂ)‖ ≤ R := by
  rw [wc_poly_eq hwc] at hz
  refine shifted_disk _ α hα ρ R hρ hρR (fun j => Nat.cast_nonneg _)
    (by exact_mod_cast wc_ic_pos hwc) ?_ ?_ z hz
  · intro j hj
    have h1 := wc_ratio hwc j
    have h1' : ((max (α - j) (Fintype.card V - j * (G.maxDegree + 1)) : ℕ) : ℝ) * (ic G j : ℝ)
        ≤ ((j : ℝ) + 1) * (ic G (j + 1) : ℝ) := by exact_mod_cast h1
    have h2 := hrat j hj
    have hic : (0 : ℝ) ≤ ic G j := Nat.cast_nonneg _
    have hic1 : (0 : ℝ) ≤ ic G (j + 1) := Nat.cast_nonneg _
    have : ((j : ℝ) + 1) * ic G j ≤ ((j : ℝ) + 1) * (ρ * ic G (j + 1)) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · have h1 := wc_ratio hwc (α - 1)
    have e1 : α - (α - 1) = 1 := by omega
    have e2 : α - 1 + 1 = α := by omega
    rw [e1, e2] at h1
    have h1' : ((max 1 (Fintype.card V - (α - 1) * (G.maxDegree + 1)) : ℕ) : ℝ) * (ic G (α - 1) : ℝ)
        ≤ (α : ℝ) * (ic G α : ℝ) := by exact_mod_cast h1
    have hic : (0 : ℝ) ≤ ic G (α - 1) := Nat.cast_nonneg _
    have hic1 : (0 : ℝ) ≤ ic G α := Nat.cast_nonneg _
    have hα' : (0 : ℝ) < α := by exact_mod_cast hα
    have : (α : ℝ) * ic G (α - 1) ≤ (α : ℝ) * (R * ic G α) := by nlinarith
    simpa using le_of_mul_le_mul_left this hα'

/-- **Corollary D1 (Brown–Dilcher–Nowakowski bound, recovered).** `|z| ≤ α`. -/
theorem wc_disk {α : ℕ} (hα : 1 ≤ α) (hwc : WellCovered G α)
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) : ‖z‖ ≤ α := by
  have h := wc_shifted G hα hwc α α (by positivity) le_rfl ?_ ?_ z hz
  · simpa using h
  · intro k hk
    have : ((α - k : ℕ) : ℝ) ≤ ((max (α - k) (Fintype.card V - k * (G.maxDegree + 1)) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have e : ((α - k : ℕ) : ℝ) = (α : ℝ) - k := by rw [Nat.cast_sub (by omega)]
    have hk' : (k : ℝ) + 2 ≤ α := by exact_mod_cast hk
    nlinarith
  · have : (1 : ℝ) ≤ ((max 1 (Fintype.card V - (α - 1) * (G.maxDegree + 1)) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have : (0 : ℝ) ≤ α := by positivity
    nlinarith

/-- **Corollary D2 (shifted disk for well-covered graphs).** For `α ≥ 2`,
every independence root satisfies `|z + (α+1)/2| ≤ α`; in particular `Re z ≤ (α-1)/2`. -/
theorem wc_shifted_half {α : ℕ} (hα : 2 ≤ α) (hwc : WellCovered G α)
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖z + ((((α : ℝ) + 1) / 2 : ℝ) : ℂ)‖ ≤ α := by
  have hα2 : (2 : ℝ) ≤ α := by exact_mod_cast hα
  have h := wc_shifted G (by omega) hwc (((α : ℝ) - 1) / 2) α (by linarith) (by linarith)
    ?_ ?_ z hz
  · have e : (α : ℝ) - ((α : ℝ) - 1) / 2 = ((α : ℝ) + 1) / 2 := by ring
    rwa [e] at h
  · intro k hk
    have : ((α - k : ℕ) : ℝ) ≤ ((max (α - k) (Fintype.card V - k * (G.maxDegree + 1)) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have e : ((α - k : ℕ) : ℝ) = (α : ℝ) - k := by rw [Nat.cast_sub (by omega)]
    have hk' : (k : ℝ) + 2 ≤ α := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  · have : (1 : ℝ) ≤ ((max 1 (Fintype.card V - (α - 1) * (G.maxDegree + 1)) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    nlinarith

/-- **Corollary D3 (degree-sharpened bounds).** Let `μ = n - (α-1)(Δ+1) ≥ 1`. Then every
independence root of a well-covered graph satisfies `|z| ≤ α/μ` and
`|z + (α/μ - (α-1)/(μ+Δ+1))| ≤ α/μ`. -/
theorem wc_degree {α : ℕ} (hα : 1 ≤ α) (hwc : WellCovered G α)
    (hμ : 1 ≤ Fintype.card V - (α - 1) * (G.maxDegree + 1))
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ≤ (α : ℝ) / (Fintype.card V - (α - 1) * (G.maxDegree + 1) : ℕ) ∧
    ‖z + ((((α : ℝ) / (Fintype.card V - (α - 1) * (G.maxDegree + 1) : ℕ))
        - ((α : ℝ) - 1) / ((Fintype.card V - (α - 1) * (G.maxDegree + 1) : ℕ) + G.maxDegree + 1)
        : ℝ) : ℂ)‖
      ≤ (α : ℝ) / (Fintype.card V - (α - 1) * (G.maxDegree + 1) : ℕ) := by
  set n := Fintype.card V
  set Δ := G.maxDegree
  set μ := n - (α - 1) * (Δ + 1) with hμdef
  have hμr : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hα1 : (1 : ℝ) ≤ α := by exact_mod_cast hα
  -- for k ≤ α - 2 the second term of the max is at least μ + Δ + 1
  have hbig : ∀ k, k + 2 ≤ α → μ + Δ + 1 ≤ n - k * (Δ + 1) := by
    intro k hk
    have : (k + 1) * (Δ + 1) ≤ (α - 1) * (Δ + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : (k + 1) * (Δ + 1) = k * (Δ + 1) + (Δ + 1) := by ring
    omega
  have hmaxk : ∀ k, k + 2 ≤ α →
      (μ : ℝ) + Δ + 1 ≤ ((max (α - k) (n - k * (Δ + 1)) : ℕ) : ℝ) := by
    intro k hk
    have := (hbig k hk).trans (le_max_right (α - k) _)
    exact_mod_cast this
  have hlastμ : (μ : ℝ) ≤ ((max 1 (n - (α - 1) * (Δ + 1)) : ℕ) : ℝ) := by
    exact_mod_cast le_max_right _ _
  have hμpos : (0 : ℝ) < μ := by linarith
  have hD : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  have hR : (α : ℝ) ≤ (α : ℝ) / μ * ((max 1 (n - (α - 1) * (Δ + 1)) : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hμpos]
    exact mul_le_mul_of_nonneg_left hlastμ (by linarith)
  constructor
  · have h := wc_shifted G hα hwc ((α : ℝ) / μ) ((α : ℝ) / μ) (by positivity) le_rfl ?_ hR z hz
    · simpa using h
    · intro k hk
      have hk' : (k : ℝ) + 2 ≤ α := by exact_mod_cast hk
      have h1 := hmaxk k hk
      have : (α : ℝ) / μ * ((μ : ℝ) + Δ + 1) ≤
          (α : ℝ) / μ * ((max (α - k) (n - k * (Δ + 1)) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have : (α : ℝ) ≤ (α : ℝ) / μ * ((μ : ℝ) + Δ + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hμpos]; nlinarith
      linarith
  · have hρ0 : (0 : ℝ) ≤ ((α : ℝ) - 1) / ((μ : ℝ) + Δ + 1) := by
      apply div_nonneg <;> linarith
    have hρR : ((α : ℝ) - 1) / ((μ : ℝ) + Δ + 1) ≤ (α : ℝ) / μ := by
      rw [div_le_div_iff₀ (by linarith) hμpos]; nlinarith
    exact wc_shifted G hα hwc _ _ hρ0 hρR (by
      intro k hk
      have hk' : (k : ℝ) + 2 ≤ α := by exact_mod_cast hk
      have h1 := hmaxk k hk
      have : ((α : ℝ) - 1) / ((μ : ℝ) + Δ + 1) * ((μ : ℝ) + Δ + 1) = (α : ℝ) - 1 := by
        field_simp
      have : ((α : ℝ) - 1) / ((μ : ℝ) + Δ + 1) * ((μ : ℝ) + Δ + 1) ≤
          ((α : ℝ) - 1) / ((μ : ℝ) + Δ + 1) * ((max (α - k) (n - k * (Δ + 1)) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hρ0
      linarith) hR z hz

/-- **Theorem E (all graphs: zero-free regions near the origin).** For every graph of order
`n ≥ 1` with minimum degree `δ`, every independence root satisfies `|z| ≥ 1/n` and
`|1 + ((n+1+δ)/2) z| ≤ n |z|`. -/
theorem indep_inner (hn : 1 ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    1 ≤ (Fintype.card V : ℝ) * ‖z‖ ∧
    ‖1 + ((((Fintype.card V : ℝ) + 1 + G.minDegree) / 2 : ℝ) : ℂ) * z‖
      ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  set n := Fintype.card V
  set δ := G.minDegree
  have hδ : (δ : ℝ) ≤ n - 1 := by
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp hn
    have h1 := G.minDegree_le_degree v
    have h2 := G.degree_lt_card_verts v
    have : δ + 1 ≤ n := by omega
    have : ((δ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  have hic0 : (ic G 0 : ℝ) = 1 := by rw [ic_zero]; simp
  have hic1 : (ic G 1 : ℝ) = n := by rw [ic_one]
  -- the basic real ratio inequality for j ≥ 1
  have hrat : ∀ j : ℕ, 1 ≤ j →
      ((j : ℝ) + 1) * ic G (j + 1) ≤ ((n : ℝ) - j - δ) * ic G j := by
    intro j hj
    have := ratio_upper (G := G) hj
    have h' : ((j : ℝ) + 1) * ic G (j + 1) + ((j : ℝ) + δ) * ic G j ≤ (n : ℝ) * ic G j := by
      exact_mod_cast this
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · refine ek_inner _ n hn n (by linarith) (fun j => Nat.cast_nonneg _) (by rw [hic0]; norm_num)
      ?_ z hz
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hic0, hic1]
    · have h := hrat j hj0
      have hic : (0 : ℝ) ≤ ic G j := Nat.cast_nonneg _
      have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
      have k1 : ((n : ℝ) - j - δ) ≤ ((j : ℝ) + 1) * n := by nlinarith
      have k2 := mul_le_mul_of_nonneg_right k1 hic
      have : ((j : ℝ) + 1) * ic G (j + 1) ≤ ((j : ℝ) + 1) * ((n : ℝ) * ic G j) := by
        linarith [mul_assoc ((j : ℝ) + 1) (n : ℝ) (ic G j : ℝ)]
      exact le_of_mul_le_mul_left this (by positivity)
  · have hσ : (0 : ℝ) ≤ ((n : ℝ) - 1 - δ) / 2 := by linarith
    have h := shifted_inner _ n hn (((n : ℝ) - 1 - δ) / 2) n hσ (by linarith)
      (fun j => Nat.cast_nonneg _) (by rw [hic0]; norm_num) ?_ (by rw [hic0, hic1]; simp) z hz
    · have e : (n : ℝ) - ((n : ℝ) - 1 - δ) / 2 = ((n : ℝ) + 1 + δ) / 2 := by ring
      rwa [e] at h
    · intro j hj _
      have h := hrat j hj
      have hic : (0 : ℝ) ≤ ic G j := Nat.cast_nonneg _
      have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have key : ((n : ℝ) - j - δ) ≤ ((j : ℝ) + 1) * (((n : ℝ) - 1 - δ) / 2) := by nlinarith
      have : ((j : ℝ) + 1) * ic G (j + 1) ≤ ((j : ℝ) + 1) * ((((n : ℝ) - 1 - δ) / 2) * ic G j) := by
        nlinarith
      exact le_of_mul_le_mul_left this (by positivity)

end IndepRoots

/-! ## Part IV. Up-closed families: domination and total domination -/

section UpClosed

variable {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → Prop) [DecidablePred p]

/-- The `k`-sets in an up-closed family. -/
def upSets (k : ℕ) : Finset (Finset V) := (univ.powersetCard k).filter p

/-- `f_k`, the number of `k`-sets in the family. -/
def uc (k : ℕ) : ℕ := #(upSets p k)

variable {p}

/-- **Theorem B(ii).** For an up-closed family, `(n-k) f_k ≤ (k+1) f_{k+1}`. -/
theorem up_ratio (hup : ∀ s t : Finset V, s ⊆ t → p s → p t) (k : ℕ) :
    (Fintype.card V - k) * uc p k ≤ (k + 1) * uc p (k + 1) := by
  have h := card_mul_le_card_mul (fun s t : Finset V => s ⊆ t) (s := upSets p k)
    (t := upSets p (k + 1)) (m := Fintype.card V - k) (n := k + 1) ?_ ?_
  · rw [uc, uc]; linarith [mul_comm (#(upSets p k)) (Fintype.card V - k),
      mul_comm (#(upSets p (k + 1))) (k + 1)]
  · intro s hs
    simp only [upSets, mem_filter, mem_powersetCard] at hs
    have hsub : (univ \ s).image (fun v => insert v s) ⊆
        bipartiteAbove (fun s t : Finset V => s ⊆ t) (upSets p (k + 1)) s := by
      intro t ht
      simp only [mem_image, mem_sdiff, mem_univ, true_and] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      simp only [bipartiteAbove, mem_filter, upSets, mem_powersetCard]
      refine ⟨⟨⟨subset_univ _, ?_⟩, hup _ _ (subset_insert v s) hs.2⟩, subset_insert v s⟩
      rw [card_insert_of_notMem hv, hs.1.2]
    refine le_trans ?_ (card_le_card hsub)
    rw [card_image_of_injOn, card_univ_sdiff, hs.1.2]
    intro v hv w hw hvw
    simp only at hvw
    have hv' : v ∉ s := by simpa using hv
    have : v ∈ insert w s := by rw [← hvw]; exact mem_insert_self v s
    rcases mem_insert.mp this with h | h
    · exact h
    · exact absurd h hv'
  · intro t ht
    simp only [upSets, mem_filter, mem_powersetCard] at ht
    have hsub : bipartiteBelow (fun s t : Finset V => s ⊆ t) (upSets p k) t ⊆ t.powersetCard k := by
      intro s hs
      simp only [bipartiteBelow, mem_filter, upSets, mem_powersetCard] at hs
      exact mem_powersetCard.mpr ⟨hs.2, hs.1.1.2⟩
    refine (card_le_card hsub).trans ?_
    rw [card_powersetCard, ht.1.2, Nat.choose_succ_self_right]

lemma uc_top (huniv : p univ) : uc p (Fintype.card V) = 1 := by
  have : upSets p (Fintype.card V) = {univ} := by
    rw [upSets, ← card_univ, powersetCard_self]
    simp [huniv]
  rw [uc, this, card_singleton]

lemma uc_le_choose (k : ℕ) : uc p k ≤ (Fintype.card V).choose k := by
  rw [uc, upSets, ← card_univ, ← card_powersetCard]
  exact card_filter_le _ _

/-- **Theorem F (filters: shifted disk).** Let `𝓕` be an up-closed family of subsets of an
`n`-set (`n ≥ 2`) containing the whole set, with generating polynomial `f(z) = ∑ f_k z^k`.
For any `R ≥ max(f_{n-1}, (n-1)/2)`, every zero satisfies `|z + R - (n-1)/2| ≤ R`. -/
theorem up_shifted (hup : ∀ s t : Finset V, s ⊆ t → p s → p t) (huniv : p univ)
    (hn : 2 ≤ Fintype.card V) (R : ℝ) (hR1 : ((Fintype.card V : ℝ) - 1) / 2 ≤ R)
    (hR2 : (uc p (Fintype.card V - 1) : ℝ) ≤ R)
    (z : ℂ) (hz : P (fun k => (uc p k : ℝ)) (Fintype.card V) z = 0) :
    ‖z + ((R - ((Fintype.card V : ℝ) - 1) / 2 : ℝ) : ℂ)‖ ≤ R := by
  set n := Fintype.card V
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine shifted_disk _ n (by omega) _ R (by linarith) hR1 (fun j => Nat.cast_nonneg _)
    (by rw [uc_top huniv]; norm_num) ?_ (by rw [uc_top huniv]; simpa using hR2) z hz
  intro j hj
  have h := up_ratio hup j
  have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by rw [Nat.cast_sub (by omega)]
  have h' : ((n : ℝ) - j) * uc p j ≤ ((j : ℝ) + 1) * uc p (j + 1) := by
    have : (((n - j : ℕ) : ℝ)) * uc p j ≤ ((j + 1 : ℕ) : ℝ) * uc p (j + 1) := by exact_mod_cast h
    rw [hcast] at this; push_cast at this; exact this
  have hj' : (j : ℝ) + 2 ≤ n := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hu : (0 : ℝ) ≤ uc p (j + 1) := Nat.cast_nonneg _
  have key : (j : ℝ) + 1 ≤ ((n : ℝ) - 1) / 2 * ((n : ℝ) - j) := by nlinarith
  have : ((n : ℝ) - j) * uc p j ≤ ((n : ℝ) - j) * (((n : ℝ) - 1) / 2 * uc p (j + 1)) := by
    nlinarith
  exact le_of_mul_le_mul_left this (by linarith)

/-- **Corollary F1.** For an up-closed family containing the whole `n`-set (`n ≥ 2`),
every zero of its generating polynomial satisfies `|z| ≤ n` and `|z + (n+1)/2| ≤ n`. -/
theorem up_disks (hup : ∀ s t : Finset V, s ⊆ t → p s → p t) (huniv : p univ)
    (hn : 2 ≤ Fintype.card V)
    (z : ℂ) (hz : P (fun k => (uc p k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ≤ Fintype.card V ∧ ‖z + ((((Fintype.card V : ℝ) + 1) / 2 : ℝ) : ℂ)‖ ≤ Fintype.card V := by
  set n := Fintype.card V
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlast : (uc p (n - 1) : ℝ) ≤ n := by
    have h1 := uc_le_choose (p := p) (n - 1)
    have h2 : n.choose (n - 1) = n := by
      rw [Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
    rw [h2] at h1; exact_mod_cast h1
  constructor
  · refine ek_outer _ n (by omega) n (by linarith) (fun j => Nat.cast_nonneg _)
      (by rw [uc_top huniv]; norm_num) ?_ z hz
    intro j hj
    have h := up_ratio hup j
    have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by rw [Nat.cast_sub (by omega)]
    have h' : ((n : ℝ) - j) * uc p j ≤ ((j : ℝ) + 1) * uc p (j + 1) := by
      have : (((n - j : ℕ) : ℝ)) * uc p j ≤ ((j + 1 : ℕ) : ℝ) * uc p (j + 1) := by
        exact_mod_cast h
      rw [hcast] at this; push_cast at this; exact this
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hu : (0 : ℝ) ≤ uc p (j + 1) := Nat.cast_nonneg _
    have key : (j : ℝ) + 1 ≤ (n : ℝ) * ((n : ℝ) - j) := by nlinarith
    have : ((n : ℝ) - j) * uc p j ≤ ((n : ℝ) - j) * ((n : ℝ) * uc p (j + 1)) := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  · have h := up_shifted hup huniv hn n (by linarith) hlast z hz
    have e : (n : ℝ) - ((n : ℝ) - 1) / 2 = ((n : ℝ) + 1) / 2 := by ring
    rwa [e] at h

end UpClosed

section Domination

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `s` is a dominating set: every vertex is in `s` or adjacent to a vertex of `s`. -/
def IsDom (s : Finset V) : Prop := ∀ v, ∃ u ∈ s, u = v ∨ G.Adj u v

instance (s : Finset V) : Decidable (IsDom G s) := by unfold IsDom; infer_instance

/-- `s` is a total dominating set: every vertex is adjacent to a vertex of `s`. -/
def IsTotDom (s : Finset V) : Prop := ∀ v, ∃ u ∈ s, G.Adj u v

instance (s : Finset V) : Decidable (IsTotDom G s) := by unfold IsTotDom; infer_instance

lemma isDom_up : ∀ s t : Finset V, s ⊆ t → IsDom G s → IsDom G t :=
  fun _ _ hst hs v => let ⟨u, hu, h⟩ := hs v; ⟨u, hst hu, h⟩

lemma isTotDom_up : ∀ s t : Finset V, s ⊆ t → IsTotDom G s → IsTotDom G t :=
  fun _ _ hst hs v => let ⟨u, hu, h⟩ := hs v; ⟨u, hst hu, h⟩

/-- **Theorem G (domination roots).** For every graph of order `n ≥ 2`, every root of the
domination polynomial `D(G;z) = ∑ d_k z^k` satisfies `|z| ≤ n` and `|z + (n+1)/2| ≤ n`;
in particular `Re z ≤ (n-1)/2`. -/
theorem domination_disks (hn : 2 ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (uc (IsDom G) k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ≤ Fintype.card V ∧ ‖z + ((((Fintype.card V : ℝ) + 1) / 2 : ℝ) : ℂ)‖ ≤ Fintype.card V :=
  up_disks (isDom_up G) (fun v => ⟨v, mem_univ v, Or.inl rfl⟩) hn z hz

/-- **Theorem G' (total domination roots).** For every graph of order `n ≥ 2` without
isolated vertices, every root of the total domination polynomial satisfies the same bounds. -/
theorem total_domination_disks (hn : 2 ≤ Fintype.card V) (hiso : ∀ v : V, ∃ u, G.Adj u v)
    (z : ℂ) (hz : P (fun k => (uc (IsTotDom G) k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ≤ Fintype.card V ∧ ‖z + ((((Fintype.card V : ℝ) + 1) / 2 : ℝ) : ℂ)‖ ≤ Fintype.card V :=
  up_disks (isTotDom_up G) (fun v => let ⟨u, h⟩ := hiso v; ⟨u, mem_univ u, h⟩) hn z hz

end Domination

/-! ## Part V. Geometric consequences (half-planes, sectors, Apollonius discs) -/

section Geometry

/-- Expanding a shifted disk: `|z + c| ≤ R` gives `|z|² + 2c Re z + c² ≤ R²`. -/
lemma shifted_re (c R : ℝ) (z : ℂ) (h : ‖z + (c : ℂ)‖ ≤ R) :
    ‖z‖ ^ 2 + 2 * c * z.re + c ^ 2 ≤ R ^ 2 := by
  have h2 : ‖z + (c : ℂ)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero] at h2
  nlinarith

/-- Expanding an Apollonius inequality: `|1 + c z| ≤ T |z|` gives
`1 + 2c Re z + c² |z|² ≤ T² |z|²`. -/
lemma apollonius_re (c T : ℝ) (z : ℂ) (h : ‖1 + (c : ℂ) * z‖ ≤ T * ‖z‖) :
    1 + 2 * c * z.re + c ^ 2 * ‖z‖ ^ 2 ≤ T ^ 2 * ‖z‖ ^ 2 := by
  have h2 : ‖1 + (c : ℂ) * z‖ ^ 2 ≤ (T * ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Complex.sq_norm, Complex.normSq_apply] at h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add] at h2
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Corollary (half-plane and sector, well-covered).** For `α ≥ 2`, every independence root
satisfies `|z|² + (α+1) Re z ≤ (α-1)(3α+1)/4`. -/
theorem wc_sector {α : ℕ} (hα : 2 ≤ α) (hwc : WellCovered G α)
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ^ 2 + ((α : ℝ) + 1) * z.re ≤ ((α : ℝ) - 1) * (3 * α + 1) / 4 := by
  have h := shifted_re (((α : ℝ) + 1) / 2) α z (wc_shifted_half G hα hwc z hz)
  nlinarith

/-- **Corollary (Apollonius form, all graphs).** -/
theorem indep_apollonius (hn : 1 ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    1 + ((Fintype.card V : ℝ) + 1 + G.minDegree) * z.re
      + (((Fintype.card V : ℝ) + 1 + G.minDegree) / 2) ^ 2 * ‖z‖ ^ 2
      ≤ (Fintype.card V : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  have h := apollonius_re _ (Fintype.card V : ℝ) z
    (indep_inner G hn z hz).2
  nlinarith

/-- **Corollary (half-plane and sector, domination).** -/
theorem domination_sector (hn : 2 ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (uc (IsDom G) k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ^ 2 + ((Fintype.card V : ℝ) + 1) * z.re
      ≤ ((Fintype.card V : ℝ) - 1) * (3 * Fintype.card V + 1) / 4 := by
  have h := shifted_re (((Fintype.card V : ℝ) + 1) / 2) (Fintype.card V) z
    (domination_disks G hn z hz).2
  nlinarith

end Geometry

/-! ## Part VI. Pure complexes, pure filters, and a reverse local LYM inequality -/

section PureComplex

variable {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → Prop) [DecidablePred p]

/-- The `k`-faces of a down-closed family. -/
def downSets (k : ℕ) : Finset (Finset V) := (univ.powersetCard k).filter p

/-- `f_k` for a down-closed family. -/
def dc (k : ℕ) : ℕ := #(downSets p k)

/-- One-element extensions of a face. -/
def dext (s : Finset V) : Finset V := univ.filter (fun v => v ∉ s ∧ p (insert v s))

/-- A maximal face (facet). -/
def IsMaxFace (s : Finset V) : Prop := p s ∧ ∀ v, v ∉ s → ¬ p (insert v s)

/-- Purity: every facet has exactly `d` elements. -/
def PureOf (d : ℕ) : Prop := ∀ s, IsMaxFace p s → #s = d

variable {p}

lemma mem_downSets {k : ℕ} {s : Finset V} : s ∈ downSets p k ↔ #s = k ∧ p s := by
  simp [downSets, mem_powersetCard]

lemma mem_dext {s : Finset V} {v : V} : v ∈ dext p s ↔ v ∉ s ∧ p (insert v s) := by
  simp [dext]

/-- Extension identity for down-closed families: `(k+1) f_{k+1} = ∑_{S} |ext(S)|`. -/
theorem down_identity (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) (k : ℕ) :
    (k + 1) * dc p (k + 1) = ∑ s ∈ downSets p k, #(dext p s) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun s t : Finset V => s ⊆ t)
    (s := downSets p k) (t := downSets p (k + 1))
  simp only [bipartiteAbove, bipartiteBelow] at h
  have habove : ∀ s ∈ downSets p k,
      #((downSets p (k + 1)).filter (fun t => s ⊆ t)) = #(dext p s) := by
    intro s hs
    rw [mem_downSets] at hs
    have himg : (downSets p (k + 1)).filter (fun t => s ⊆ t)
        = (dext p s).image (fun v => insert v s) := by
      ext t
      simp only [mem_filter, mem_image, mem_downSets, mem_dext]
      constructor
      · rintro ⟨⟨htc, hpt⟩, hst⟩
        have hc : #(t \ s) = 1 := by rw [card_sdiff_of_subset hst]; omega
        obtain ⟨v, hv⟩ := card_eq_one.mp hc
        have hvt : v ∈ t \ s := by rw [hv]; exact mem_singleton_self v
        rw [mem_sdiff] at hvt
        have hins : insert v s = t := by
          rw [← union_sdiff_of_subset hst, hv, insert_eq, union_comm]
        exact ⟨v, ⟨hvt.2, hins ▸ hpt⟩, hins⟩
      · rintro ⟨v, ⟨hv, hpv⟩, rfl⟩
        exact ⟨⟨by rw [card_insert_of_notMem hv, hs.1], hpv⟩, subset_insert v s⟩
    rw [himg, card_image_of_injOn]
    intro v hv w _ hvw
    simp only at hvw
    have hv' : v ∉ s := (mem_dext.mp (mem_coe.mp hv)).1
    have : v ∈ insert w s := by rw [← hvw]; exact mem_insert_self v s
    rcases mem_insert.mp this with h | h
    · exact h
    · exact absurd h hv'
  have hbelow : ∀ t ∈ downSets p (k + 1),
      #((downSets p k).filter (fun s => s ⊆ t)) = k + 1 := by
    intro t ht
    rw [mem_downSets] at ht
    have : (downSets p k).filter (fun s => s ⊆ t) = t.powersetCard k := by
      ext s
      simp only [mem_filter, mem_downSets, mem_powersetCard]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, hdown _ _ h1 ht.2⟩, h1⟩
    rw [this, card_powersetCard, ht.1, Nat.choose_succ_self_right]
  rw [sum_congr rfl habove, sum_congr rfl hbelow] at h
  rw [h, sum_const, smul_eq_mul, dc, mul_comm]

lemma exists_maxFace {s : Finset V} (hs : p s) : ∃ M, s ⊆ M ∧ IsMaxFace p M := by
  let F := (univ : Finset (Finset V)).filter (fun t => p t ∧ s ⊆ t)
  have hF : F.Nonempty := ⟨s, by simp [F, hs]⟩
  obtain ⟨M, hM, hmax⟩ := exists_max_image F card hF
  simp only [F, mem_filter, mem_univ, true_and] at hM
  refine ⟨M, hM.2, hM.1, fun v hv hind => ?_⟩
  have := hmax (insert v M) (by simp [F, hind, hM.2.trans (subset_insert v M)])
  rw [card_insert_of_notMem hv] at this
  omega

lemma dext_upper {k : ℕ} {s : Finset V} (hs : s ∈ downSets p k) :
    #(dext p s) + k ≤ Fintype.card V := by
  rw [mem_downSets] at hs
  have hsub : dext p s ⊆ univ \ s := by
    intro v hv; rw [mem_dext] at hv; simp [hv.1]
  have h1 := card_le_card hsub
  rw [card_univ_sdiff, hs.1] at h1
  have h2 : #s ≤ Fintype.card V := card_le_univ s
  omega

lemma pure_dext_lower (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) {d k : ℕ}
    (hpure : PureOf p d) {s : Finset V} (hs : s ∈ downSets p k) :
    d ≤ #(dext p s) + k := by
  rw [mem_downSets] at hs
  obtain ⟨M, hsM, hM⟩ := exists_maxFace hs.2
  have hMc := hpure M hM
  have hsub : M \ s ⊆ dext p s := by
    intro v hv
    rw [mem_sdiff] at hv
    refine mem_dext.mpr ⟨hv.2, hdown _ _ ?_ hM.1⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hv.1
    · exact hsM hx
  have h1 := card_le_card hsub
  have h2 := card_sdiff_add_card_eq_card hsM
  omega

/-- Ratio bounds for a down-closed family: `(k+1) f_{k+1} ≤ (n-k) f_k`, and, if pure of rank `d`,
`(d-k) f_k ≤ (k+1) f_{k+1}`. -/
theorem down_ratio_upper (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) (k : ℕ) :
    (k + 1) * dc p (k + 1) + k * dc p k ≤ Fintype.card V * dc p k := by
  have h : ∑ s ∈ downSets p k, (#(dext p s) + k) ≤ ∑ _s ∈ downSets p k, Fintype.card V :=
    sum_le_sum (fun s hs => dext_upper hs)
  rw [sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at h
  rw [down_identity hdown, dc]
  linarith [mul_comm (#(downSets p k)) k, mul_comm (#(downSets p k)) (Fintype.card V)]

theorem pure_ratio (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) {d : ℕ} (hpure : PureOf p d)
    (k : ℕ) : (d - k) * dc p k ≤ (k + 1) * dc p (k + 1) := by
  rw [down_identity hdown, dc, mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro s hs
  have := pure_dext_lower hdown hpure hs
  omega

lemma pure_dc_pos (hne : p ∅) {d : ℕ} (hpure : PureOf p d) : 0 < dc p d := by
  obtain ⟨M, -, hM⟩ := exists_maxFace hne
  exact card_pos.mpr ⟨M, mem_downSets.mpr ⟨hpure M hM, hM.1⟩⟩

lemma pure_dc_eq_zero {d k : ℕ} (hpure : PureOf p d) (hk : d < k) : dc p k = 0 := by
  rw [dc, card_eq_zero, eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_downSets] at hs
  obtain ⟨M, hsM, hM⟩ := exists_maxFace hs.2
  have := card_le_card hsM
  rw [hpure M hM] at this
  omega

lemma pure_poly_eq (hne : p ∅) {d : ℕ} (hpure : PureOf p d) (z : ℂ) :
    P (fun k => (dc p k : ℝ)) (Fintype.card V) z = P (fun k => (dc p k : ℝ)) d z := by
  have hdn : d ≤ Fintype.card V := by
    obtain ⟨s, hs⟩ := card_pos.mp (pure_dc_pos hne hpure)
    rw [mem_downSets] at hs
    rw [← hs.1]; exact card_le_univ s
  unfold P
  rw [← sum_range_add_sum_Ico _ (Nat.add_le_add_right hdn 1), add_eq_left]
  apply sum_eq_zero
  intro k hk
  rw [mem_Ico] at hk
  show ((dc p k : ℝ) : ℂ) * z ^ k = 0
  rw [pure_dc_eq_zero hpure (by omega)]
  simp

lemma dc_zero (hne : p ∅) : dc p 0 = 1 := by
  have : downSets p 0 = {∅} := by
    ext s
    simp only [mem_downSets, mem_singleton, card_eq_zero]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, hne⟩
  simp [dc, this]

lemma dc_one_le : dc p 1 ≤ Fintype.card V := by
  rw [dc, downSets]
  refine (card_filter_le _ _).trans ?_
  rw [card_powersetCard, card_univ, Nat.choose_one_right]

/-- **Theorem (pure complexes).** If `𝓚` is a down-closed family on an `n`-set whose facets all
have `d ≥ 2` elements, every zero of its face polynomial satisfies `|z| ≤ d` and
`|z + (d+1)/2| ≤ d`. -/
theorem pure_shifted (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) (hne : p ∅) {d : ℕ}
    (hd : 2 ≤ d) (hpure : PureOf p d)
    (z : ℂ) (hz : P (fun k => (dc p k : ℝ)) (Fintype.card V) z = 0) :
    ‖z‖ ≤ d ∧ ‖z + ((((d : ℝ) + 1) / 2 : ℝ) : ℂ)‖ ≤ d := by
  rw [pure_poly_eq hne hpure] at hz
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < dc p d := by exact_mod_cast pure_dc_pos hne hpure
  have hratio : ∀ k : ℕ, k + 1 ≤ d →
      ((d : ℝ) - k) * dc p k ≤ ((k : ℝ) + 1) * dc p (k + 1) := by
    intro k hk
    have h := pure_ratio hdown hpure k
    have hc : ((d - k : ℕ) : ℝ) = (d : ℝ) - k := by rw [Nat.cast_sub (by omega)]
    have : ((d - k : ℕ) : ℝ) * dc p k ≤ ((k + 1 : ℕ) : ℝ) * dc p (k + 1) := by exact_mod_cast h
    rw [hc] at this; push_cast at this; exact this
  have hlast : (dc p (d - 1) : ℝ) ≤ d * dc p d := by
    have h := hratio (d - 1) (by omega)
    have e1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have e2 : d - 1 + 1 = d := by omega
    rw [e1, e2] at h
    linarith
  constructor
  · refine ek_outer _ d (by omega) d (by linarith) (fun j => Nat.cast_nonneg _) hpos ?_ z hz
    intro j hj
    have h := hratio j hj
    have hj' : (j : ℝ) + 1 ≤ d := by exact_mod_cast hj
    have hu : (0 : ℝ) ≤ dc p (j + 1) := Nat.cast_nonneg _
    have hdj : (1 : ℝ) ≤ (d : ℝ) - j := by linarith
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have k1 : (j : ℝ) + 1 ≤ ((d : ℝ) - j) * d := by nlinarith
    have k2 := mul_le_mul_of_nonneg_right k1 hu
    have : ((d : ℝ) - j) * dc p j ≤ ((d : ℝ) - j) * ((d : ℝ) * dc p (j + 1)) := by
      linarith [mul_assoc ((d : ℝ) - j) (d : ℝ) (dc p (j + 1) : ℝ)]
    exact le_of_mul_le_mul_left this (by linarith)
  · have h := shifted_disk _ d (by omega) (((d : ℝ) - 1) / 2) d (by linarith) (by linarith)
      (fun j => Nat.cast_nonneg _) hpos ?_ hlast z hz
    · have e : (d : ℝ) - ((d : ℝ) - 1) / 2 = ((d : ℝ) + 1) / 2 := by ring
      rwa [e] at h
    · intro j hj
      have h := hratio j (by omega)
      have hj' : (j : ℝ) + 2 ≤ d := by exact_mod_cast hj
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hu : (0 : ℝ) ≤ dc p (j + 1) := Nat.cast_nonneg _
      have key : (j : ℝ) + 1 ≤ ((d : ℝ) - 1) / 2 * ((d : ℝ) - j) := by nlinarith
      have : ((d : ℝ) - j) * dc p j ≤ ((d : ℝ) - j) * ((((d : ℝ) - 1) / 2) * dc p (j + 1)) := by
        nlinarith
      exact le_of_mul_le_mul_left this (by linarith)

/-- **Theorem (down-closed families: zero-free Apollonius disk).** For every down-closed family
on an `n`-set containing `∅`, every zero satisfies `|z| ≥ 1/n` and `|1 + ((n+1)/2) z| ≤ n |z|`. -/
theorem down_apollonius (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) (hne : p ∅)
    (hn : 1 ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (dc p k : ℝ)) (Fintype.card V) z = 0) :
    1 ≤ (Fintype.card V : ℝ) * ‖z‖ ∧
    ‖1 + ((((Fintype.card V : ℝ) + 1) / 2 : ℝ) : ℂ) * z‖ ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  set n := Fintype.card V
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (dc p 0 : ℝ) = 1 := by rw [dc_zero hne]; simp
  have h1 : (dc p 1 : ℝ) ≤ n := by exact_mod_cast dc_one_le
  have hrat : ∀ j : ℕ, ((j : ℝ) + 1) * dc p (j + 1) ≤ ((n : ℝ) - j) * dc p j := by
    intro j
    have := down_ratio_upper hdown (p := p) j
    have h' : ((j : ℝ) + 1) * dc p (j + 1) + (j : ℝ) * dc p j ≤ (n : ℝ) * dc p j := by
      exact_mod_cast this
    linarith
  constructor
  · refine ek_inner _ n hn n (by linarith) (fun j => Nat.cast_nonneg _) (by rw [h0]; norm_num)
      ?_ z hz
    intro j _
    have h := hrat j
    have hic : (0 : ℝ) ≤ dc p j := Nat.cast_nonneg _
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have k1 : ((n : ℝ) - j) ≤ ((j : ℝ) + 1) * n := by nlinarith
    have k2 := mul_le_mul_of_nonneg_right k1 hic
    have : ((j : ℝ) + 1) * dc p (j + 1) ≤ ((j : ℝ) + 1) * ((n : ℝ) * dc p j) := by
      linarith [mul_assoc ((j : ℝ) + 1) (n : ℝ) (dc p j : ℝ)]
    exact le_of_mul_le_mul_left this (by positivity)
  · have h := shifted_inner _ n hn (((n : ℝ) - 1) / 2) n (by linarith) (by linarith)
      (fun j => Nat.cast_nonneg _) (by rw [h0]; norm_num) ?_ (by rw [h0]; simpa using h1) z hz
    · have e : (n : ℝ) - ((n : ℝ) - 1) / 2 = ((n : ℝ) + 1) / 2 := by ring
      rwa [e] at h
    · intro j hj _
      have h := hrat j
      have hic : (0 : ℝ) ≤ dc p j := Nat.cast_nonneg _
      have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have key : ((n : ℝ) - j) ≤ ((j : ℝ) + 1) * (((n : ℝ) - 1) / 2) := by nlinarith
      have : ((j : ℝ) + 1) * dc p (j + 1) ≤ ((j : ℝ) + 1) * ((((n : ℝ) - 1) / 2) * dc p j) := by
        nlinarith
      exact le_of_mul_le_mul_left this (by positivity)

end PureComplex

section PureFilter

variable {V : Type*} [Fintype V] [DecidableEq V] {p : Finset V → Prop} [DecidablePred p]

/-- A minimal member of a family. -/
def IsMinMem (p : Finset V → Prop) (s : Finset V) : Prop := p s ∧ ∀ v ∈ s, ¬ p (s.erase v)

lemma exists_minMem_subset {t : Finset V} (ht : p t) : ∃ M, M ⊆ t ∧ IsMinMem p M := by
  let F := t.powerset.filter p
  have hF : F.Nonempty := ⟨t, by simp [F, ht]⟩
  obtain ⟨M, hM, hmin⟩ := exists_min_image F card hF
  simp only [F, mem_filter, mem_powerset] at hM
  refine ⟨M, hM.1, hM.2, fun v hv hpv => ?_⟩
  have := hmin (M.erase v) (by
    simp only [F, mem_filter, mem_powerset]
    exact ⟨(erase_subset v M).trans hM.1, hpv⟩)
  rw [card_erase_of_mem hv] at this
  have : 0 < #M := card_pos.mpr ⟨v, hv⟩
  omega

/-- **Lemma (essential elements).** In an up-closed family, every essential element of a member
`T` (one whose removal leaves the family) lies in every minimal member contained in `T`. -/
lemma essential_subset_minimal (hup : ∀ s t : Finset V, s ⊆ t → p s → p t) {T M : Finset V}
    (hMT : M ⊆ T) (hM : IsMinMem p M) : T.filter (fun v => ¬ p (T.erase v)) ⊆ M := by
  intro v hv
  rw [mem_filter] at hv
  by_contra hvM
  apply hv.2
  refine hup M _ ?_ hM.1
  intro x hx
  rw [mem_erase]
  exact ⟨fun h => hvM (h ▸ hx), hMT hx⟩

/-- **Theorem (reverse local LYM inequality).** If every minimal member of an up-closed family
has at most `Γ` elements, then `(k+1-Γ) f_{k+1} ≤ (n-k) f_k`. -/
theorem up_reverse (hup : ∀ s t : Finset V, s ⊆ t → p s → p t) (Γ : ℕ)
    (hmin : ∀ M, IsMinMem p M → #M ≤ Γ) (k : ℕ) :
    (k + 1 - Γ) * uc p (k + 1) ≤ (Fintype.card V - k) * uc p k := by
  have h := card_mul_le_card_mul' (fun s t : Finset V => s ⊆ t) (s := upSets p k)
    (t := upSets p (k + 1)) (n := k + 1 - Γ) (m := Fintype.card V - k) ?_ ?_
  · rw [uc, uc]; linarith [mul_comm (#(upSets p (k + 1))) (k + 1 - Γ),
      mul_comm (#(upSets p k)) (Fintype.card V - k)]
  · intro T hT
    simp only [upSets, mem_filter, mem_powersetCard] at hT
    obtain ⟨M, hMT, hM⟩ := exists_minMem_subset hT.2
    have hMc := hmin M hM
    have hess := essential_subset_minimal hup hMT hM
    have hcover : T ⊆ T.filter (fun v => p (T.erase v)) ∪ M := by
      intro v hv
      by_cases h : p (T.erase v)
      · exact mem_union_left _ (mem_filter.mpr ⟨hv, h⟩)
      · exact mem_union_right _ (hess (mem_filter.mpr ⟨hv, h⟩))
    have hc1 := (card_le_card hcover).trans (card_union_le _ _)
    have hsub : (T.filter (fun v => p (T.erase v))).image (fun v => T.erase v) ⊆
        bipartiteBelow (fun s t : Finset V => s ⊆ t) (upSets p k) T := by
      intro s hs
      simp only [mem_image, mem_filter] at hs
      obtain ⟨v, ⟨hvT, hpv⟩, rfl⟩ := hs
      simp only [bipartiteBelow, mem_filter, upSets, mem_powersetCard]
      refine ⟨⟨⟨subset_univ _, ?_⟩, hpv⟩, erase_subset v T⟩
      rw [card_erase_of_mem hvT, hT.1.2]; rfl
    have hinj : Set.InjOn (fun v => T.erase v) (T.filter (fun v => p (T.erase v)) : Set V) := by
      intro v hv w hw hvw
      simp only at hvw
      have hvT : v ∈ T := (mem_filter.mp (mem_coe.mp hv)).1
      by_contra hne
      have : v ∈ T.erase w := mem_erase.mpr ⟨hne, hvT⟩
      rw [← hvw] at this
      exact (notMem_erase v T) this
    have hc2 := card_le_card hsub
    rw [card_image_of_injOn hinj] at hc2
    rw [hT.1.2] at hc1
    omega
  · intro S hS
    simp only [upSets, mem_filter, mem_powersetCard] at hS
    have hsub : bipartiteAbove (fun s t : Finset V => s ⊆ t) (upSets p (k + 1)) S ⊆
        (univ \ S).image (fun v => insert v S) := by
      intro T hT
      simp only [bipartiteAbove, mem_filter, upSets, mem_powersetCard] at hT
      simp only [mem_image, mem_sdiff, mem_univ, true_and]
      have hc : #(T \ S) = 1 := by rw [card_sdiff_of_subset hT.2]; omega
      obtain ⟨v, hv⟩ := card_eq_one.mp hc
      have hvt : v ∈ T \ S := by rw [hv]; exact mem_singleton_self v
      rw [mem_sdiff] at hvt
      exact ⟨v, hvt.2, by rw [← union_sdiff_of_subset hT.2, hv, insert_eq, union_comm]⟩
    refine (card_le_card hsub).trans ?_
    refine card_image_le.trans ?_
    rw [card_univ_sdiff, hS.1.2]

/-- Purity of a filter: all minimal members have exactly `γ` elements. -/
def PureFilter (p : Finset V → Prop) (γ : ℕ) : Prop := ∀ M, IsMinMem p M → #M = γ

lemma pf_uc_eq_zero {γ k : ℕ} (hpure : PureFilter p γ) (hk : k < γ) : uc p k = 0 := by
  rw [uc, card_eq_zero, eq_empty_iff_forall_notMem]
  intro s hs
  simp only [upSets, mem_filter, mem_powersetCard] at hs
  obtain ⟨M, hMs, hM⟩ := exists_minMem_subset hs.2
  have := card_le_card hMs
  rw [hpure M hM, hs.1.2] at this
  omega

lemma pf_uc_pos (huniv : p univ) {γ : ℕ} (hpure : PureFilter p γ) : 0 < uc p γ := by
  obtain ⟨M, -, hM⟩ := exists_minMem_subset huniv
  refine card_pos.mpr ⟨M, ?_⟩
  simp only [upSets, mem_filter, mem_powersetCard]
  exact ⟨⟨subset_univ _, hpure M hM⟩, hM.1⟩

/-- Factoring out `z^γ` when the first `γ` coefficients vanish. -/
lemma P_shift (a : ℕ → ℝ) (n γ : ℕ) (hγ : γ ≤ n) (ha : ∀ k, k < γ → a k = 0) (z : ℂ) :
    P a n z = z ^ γ * P (fun j => a (γ + j)) (n - γ) z := by
  unfold P
  have e : n + 1 = γ + (n - γ + 1) := by omega
  rw [e, sum_range_add, mul_sum]
  have h0 : ∑ x ∈ range γ, (a x : ℂ) * z ^ x = 0 :=
    sum_eq_zero (fun k hk => by rw [ha k (mem_range.mp hk)]; simp)
  rw [h0, zero_add]
  refine sum_congr rfl (fun j _ => ?_)
  rw [pow_add]; ring

/-- **Theorem (pure filters: zero-free region around the origin).** Let `𝓕` be an up-closed family
on an `n`-set containing the whole set, all of whose minimal members have `γ < n` elements.
Every nonzero zero of its generating polynomial satisfies `|z| ≥ 1/(n-γ)` and
`|1 + ((n-γ+1)/2) z| ≤ (n-γ) |z|`. -/
theorem pure_filter_inner (hup : ∀ s t : Finset V, s ⊆ t → p s → p t) (huniv : p univ)
    {γ : ℕ} (hpure : PureFilter p γ) (hγ : γ < Fintype.card V)
    (z : ℂ) (hz : P (fun k => (uc p k : ℝ)) (Fintype.card V) z = 0) (hz0 : z ≠ 0) :
    1 ≤ ((Fintype.card V : ℝ) - γ) * ‖z‖ ∧
    ‖1 + ((((Fintype.card V : ℝ) - γ + 1) / 2 : ℝ) : ℂ) * z‖
      ≤ ((Fintype.card V : ℝ) - γ) * ‖z‖ := by
  set n := Fintype.card V
  set N := n - γ with hN
  have hNr : ((N : ℕ) : ℝ) = (n : ℝ) - γ := by rw [hN, Nat.cast_sub hγ.le]
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hshift := P_shift (fun k => (uc p k : ℝ)) n γ hγ.le
    (fun k hk => by simp [pf_uc_eq_zero hpure hk]) z
  rw [hz] at hshift
  have hb : P (fun j => (uc p (γ + j) : ℝ)) N z = 0 := by
    rcases mul_eq_zero.mp hshift.symm with h | h
    · exact absurd h (pow_ne_zero γ hz0)
    · exact h
  have hb0 : (0 : ℝ) < uc p (γ + 0) := by simpa using (show (0:ℝ) < uc p γ by exact_mod_cast pf_uc_pos huniv hpure)
  -- ratio: (j+1) b_{j+1} ≤ (N - j) b_j
  have hrat : ∀ j : ℕ, j + 1 ≤ N →
      ((j : ℝ) + 1) * uc p (γ + (j + 1)) ≤ ((N : ℝ) - j) * uc p (γ + j) := by
    intro j hj
    have h := up_reverse hup γ (fun M hM => (hpure M hM).le) (γ + j)
    have e1 : γ + j + 1 - γ = j + 1 := by omega
    have e2 : n - (γ + j) = N - j := by omega
    rw [e1, e2] at h
    have hc : ((N - j : ℕ) : ℝ) = (N : ℝ) - j := by rw [Nat.cast_sub (by omega)]
    have : ((j + 1 : ℕ) : ℝ) * uc p (γ + j + 1) ≤ ((N - j : ℕ) : ℝ) * uc p (γ + j) := by
      exact_mod_cast h
    rw [hc] at this; push_cast at this
    simpa [add_assoc] using this
  constructor
  · have h := ek_inner (fun j => (uc p (γ + j) : ℝ)) N hN1 N (by linarith)
      (fun j => Nat.cast_nonneg _) hb0 ?_ z hb
    · rwa [hNr] at h
    · intro j hj
      have h := hrat j hj
      have hic : (0 : ℝ) ≤ uc p (γ + j) := Nat.cast_nonneg _
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have k1 : ((N : ℝ) - j) ≤ ((j : ℝ) + 1) * N := by nlinarith
      have k2 := mul_le_mul_of_nonneg_right k1 hic
      have : ((j : ℝ) + 1) * uc p (γ + (j + 1)) ≤ ((j : ℝ) + 1) * ((N : ℝ) * uc p (γ + j)) := by
        linarith [mul_assoc ((j : ℝ) + 1) (N : ℝ) (uc p (γ + j) : ℝ)]
      exact le_of_mul_le_mul_left this (by positivity)
  · have h := shifted_inner (fun j => (uc p (γ + j) : ℝ)) N hN1 (((N : ℝ) - 1) / 2) N
      (by linarith) (by linarith) (fun j => Nat.cast_nonneg _) hb0 ?_ ?_ z hb
    · have e : (N : ℝ) - ((N : ℝ) - 1) / 2 = ((N : ℝ) + 1) / 2 := by ring
      rw [e, hNr] at h
      exact h
    · intro j hj hjN
      have h := hrat j hjN
      have hic : (0 : ℝ) ≤ uc p (γ + j) := Nat.cast_nonneg _
      have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have key : ((N : ℝ) - j) ≤ ((j : ℝ) + 1) * (((N : ℝ) - 1) / 2) := by nlinarith
      have : ((j : ℝ) + 1) * uc p (γ + (j + 1)) ≤
          ((j : ℝ) + 1) * ((((N : ℝ) - 1) / 2) * uc p (γ + j)) := by nlinarith
      exact le_of_mul_le_mul_left this (by positivity)
    · have h := hrat 0 hN1
      simpa using h

end PureFilter

section WellDominated

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Theorem (well-dominated graphs).** If every minimal dominating set of `G` has `γ < n`
elements, every nonzero domination root satisfies `|z| ≥ 1/(n-γ)` and
`|1 + ((n-γ+1)/2) z| ≤ (n-γ)|z|`. -/
theorem well_dominated_inner {γ : ℕ} (hwd : PureFilter (IsDom G) γ) (hγ : γ < Fintype.card V)
    (z : ℂ) (hz : P (fun k => (uc (IsDom G) k : ℝ)) (Fintype.card V) z = 0) (hz0 : z ≠ 0) :
    1 ≤ ((Fintype.card V : ℝ) - γ) * ‖z‖ ∧
    ‖1 + ((((Fintype.card V : ℝ) - γ + 1) / 2 : ℝ) : ℂ) * z‖
      ≤ ((Fintype.card V : ℝ) - γ) * ‖z‖ :=
  pure_filter_inner (isDom_up G) (fun v => ⟨v, mem_univ v, Or.inl rfl⟩) hwd hγ z hz hz0

/-- **Theorem (well-totally-dominated graphs).** -/
theorem well_totally_dominated_inner (hiso : ∀ v : V, ∃ u, G.Adj u v) {γ : ℕ}
    (hwd : PureFilter (IsTotDom G) γ) (hγ : γ < Fintype.card V)
    (z : ℂ) (hz : P (fun k => (uc (IsTotDom G) k : ℝ)) (Fintype.card V) z = 0) (hz0 : z ≠ 0) :
    1 ≤ ((Fintype.card V : ℝ) - γ) * ‖z‖ ∧
    ‖1 + ((((Fintype.card V : ℝ) - γ + 1) / 2 : ℝ) : ℂ) * z‖
      ≤ ((Fintype.card V : ℝ) - γ) * ‖z‖ :=
  pure_filter_inner (isTotDom_up G) (fun v => let ⟨u, h⟩ := hiso v; ⟨u, mem_univ u, h⟩)
    hwd hγ z hz hz0

/-! ### Average degree -/

/-- `2 i_2 + ∑_v (deg v + 1) = n²`, i.e. `i_2 = (n(n-1) - ∑ deg)/2`. -/
lemma two_ic_two : 2 * ic G 2 + ∑ v, (G.degree v + 1) = Fintype.card V * Fintype.card V := by
  have h := ext_identity (G := G) 1
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  have hI1 : indepSets G 1 = univ.image (fun v : V => ({v} : Finset V)) := by
    ext s
    simp only [mem_indepSets, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hc, -⟩
      obtain ⟨a, rfl⟩ := card_eq_one.mp hc
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨card_singleton a, ?_⟩
      intro u hu w hw
      rw [mem_singleton] at hu hw
      subst hu; subst hw; exact G.irrefl
  rw [hI1, sum_image (fun a _ b _ h => singleton_injective h)] at h
  have hext : ∀ v : V, #(extSet G {v}) + (G.degree v + 1) = Fintype.card V := by
    intro v
    have hset : extSet G {v} = univ \ insert v (G.neighborFinset v) := by
      ext w
      simp only [mem_extSet, mem_singleton, forall_eq, mem_sdiff, mem_univ, true_and, mem_insert,
        SimpleGraph.mem_neighborFinset, not_or]
    have hnot : v ∉ G.neighborFinset v := by simp
    have hc := card_le_univ (insert v (G.neighborFinset v))
    rw [hset, card_univ_sdiff, card_insert_of_notMem hnot, G.card_neighborFinset_eq_degree]
    rw [card_insert_of_notMem hnot, G.card_neighborFinset_eq_degree] at hc
    omega
  have hsum : ∑ v, (#(extSet G {v}) + (G.degree v + 1)) = ∑ _v : V, Fintype.card V :=
    sum_congr rfl (fun v _ => hext v)
  rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul] at hsum
  omega

/-- **Theorem (average-degree Apollonius disk).** Let `d̄` be the average degree and
`σ = max((n-1-d̄)/2, (n-2-δ)/3)`. Every independence root satisfies `|1 + (n-σ) z| ≤ n|z|`. -/
theorem indep_avg (hn : 1 ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖1 + (((Fintype.card V : ℝ) -
        max (((Fintype.card V : ℝ) - 1 - (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2)
            (((Fintype.card V : ℝ) - 2 - G.minDegree) / 3) : ℝ) : ℂ) * z‖
      ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  set n := Fintype.card V
  set δ := G.minDegree
  set S : ℝ := ∑ v, (G.degree v : ℝ) with hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hδ : (δ : ℝ) ≤ n - 1 := by
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp hn
    have h1 := G.minDegree_le_degree v
    have h2 := G.degree_lt_card_verts v
    have : δ + 1 ≤ n := by omega
    have : ((δ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  have h2 : 2 * (ic G 2 : ℝ) + S + n = (n : ℝ) * n := by
    have := two_ic_two G
    have h' : ((2 * ic G 2 + ∑ v, (G.degree v + 1) : ℕ) : ℝ) = ((n * n : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [sum_add_distrib] at h'
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h'
    rw [hS]; linarith
  have hS0 : 0 ≤ S := sum_nonneg (fun v _ => Nat.cast_nonneg _)
  have hic2 : (0 : ℝ) ≤ ic G 2 := Nat.cast_nonneg _
  set σ := max ((((n : ℝ) - 1 - S / n)) / 2) (((n : ℝ) - 2 - δ) / 3) with hσdef
  have hσ1 : ((n : ℝ) - 1 - S / n) / 2 ≤ σ := le_max_left _ _
  have hσ2 : ((n : ℝ) - 2 - δ) / 3 ≤ σ := le_max_right _ _
  have hSn : S / n ≤ n - 1 := by
    rw [div_le_iff₀ hnpos]; nlinarith
  have hσ0 : 0 ≤ σ := le_trans (by linarith) hσ1
  have hσn : σ ≤ n := by
    apply max_le
    · have : 0 ≤ S / n := div_nonneg hS0 hnpos.le
      linarith
    · have : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
      linarith
  have hic0 : (ic G 0 : ℝ) = 1 := by rw [ic_zero]; simp
  have hic1 : (ic G 1 : ℝ) = n := by rw [ic_one]
  have hrat : ∀ j : ℕ, 1 ≤ j →
      ((j : ℝ) + 1) * ic G (j + 1) ≤ ((n : ℝ) - j - δ) * ic G j := by
    intro j hj
    have := ratio_upper (G := G) hj
    have h' : ((j : ℝ) + 1) * ic G (j + 1) + ((j : ℝ) + δ) * ic G j ≤ (n : ℝ) * ic G j := by
      exact_mod_cast this
    linarith
  refine shifted_inner _ n hn σ n hσ0 hσn (fun j => Nat.cast_nonneg _)
    (by rw [hic0]; norm_num) ?_ (by rw [hic0, hic1]; simp) z hz
  intro j hj _
  rcases Nat.eq_or_lt_of_le hj with rfl | hj2
  · -- j = 1: exact second coefficient
    rw [hic1]
    show (ic G 2 : ℝ) ≤ σ * n
    have : (ic G 2 : ℝ) = n * (((n : ℝ) - 1 - S / n) / 2) := by
      field_simp
      linarith
    rw [this]
    nlinarith
  · have h := hrat j hj
    have hic : (0 : ℝ) ≤ ic G j := Nat.cast_nonneg _
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    have key : ((n : ℝ) - j - δ) ≤ ((j : ℝ) + 1) * σ := by nlinarith
    have : ((j : ℝ) + 1) * ic G (j + 1) ≤ ((j : ℝ) + 1) * (σ * ic G j) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)

/-- **Corollary (average-degree form).** If `3 d̄ ≤ n + 1 + 2δ`, every independence root satisfies
`|1 + ((n+1+d̄)/2) z| ≤ n |z|`. -/
theorem indep_avg_simple (hn : 1 ≤ Fintype.card V)
    (hcond : 3 * ((∑ v, (G.degree v : ℝ)) / Fintype.card V) ≤
      (Fintype.card V : ℝ) + 1 + 2 * G.minDegree)
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖1 + ((((Fintype.card V : ℝ) + 1 + (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2 : ℝ) : ℂ)
        * z‖ ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  have h := indep_avg G hn z hz
  have hmax : max (((Fintype.card V : ℝ) - 1 - (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2)
      (((Fintype.card V : ℝ) - 2 - G.minDegree) / 3)
      = ((Fintype.card V : ℝ) - 1 - (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2 := by
    apply max_eq_left; linarith
  rw [hmax] at h
  have e : (Fintype.card V : ℝ) - ((Fintype.card V : ℝ) - 1 -
      (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2
      = ((Fintype.card V : ℝ) + 1 + (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2 := by ring
  rwa [e] at h

end WellDominated

/-! ## Part VII. Extension-bounded complexes and parametric average-degree regions -/

section ExtBounded

variable {V : Type*} [Fintype V] [DecidableEq V] {p : Finset V → Prop} [DecidablePred p]

/-- Lower extension function ⇒ lower ratio bound: `g_k f_k ≤ (k+1) f_{k+1}`. -/
theorem down_ratio_lower (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) (g : ℕ → ℕ) (k : ℕ)
    (hg : ∀ s ∈ downSets p k, g k ≤ #(dext p s)) :
    g k * dc p k ≤ (k + 1) * dc p (k + 1) := by
  rw [down_identity hdown, dc, mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum hg

/-- Extension-regular complexes: if every `k`-face has exactly `g_k` extensions then
`(k+1) f_{k+1} = g_k f_k`. -/
theorem down_ratio_exact (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) (g : ℕ → ℕ) (k : ℕ)
    (hg : ∀ s ∈ downSets p k, #(dext p s) = g k) :
    (k + 1) * dc p (k + 1) = g k * dc p k := by
  rw [down_identity hdown, sum_congr rfl hg, sum_const, smul_eq_mul, dc, mul_comm]

/-- **Theorem (extension-bounded complexes).** Let `𝓚` be down-closed of rank `d ≥ 1`
(`f_d > 0`, `f_k = 0` for `k > d`) and suppose every `k`-face, `k ≤ d-1`, has at least `g_k`
extensions. If `0 ≤ ρ ≤ R`, `k+1 ≤ ρ g_k` for `k ≤ d-2` and `d ≤ R g_{d-1}`, then every zero of
the face polynomial satisfies `|z + R - ρ| ≤ R`. -/
theorem down_ext_shifted (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) {d : ℕ} (hd : 1 ≤ d)
    (hpos : 0 < dc p d) (habove : ∀ k, d < k → dc p k = 0) (g : ℕ → ℕ)
    (hg : ∀ k, k < d → ∀ s ∈ downSets p k, g k ≤ #(dext p s))
    (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hrat : ∀ k, k + 2 ≤ d → ((k : ℝ) + 1) ≤ ρ * g k)
    (hlast : (d : ℝ) ≤ R * g (d - 1))
    (z : ℂ) (hz : P (fun k => (dc p k : ℝ)) (Fintype.card V) z = 0) :
    ‖z + ((R - ρ : ℝ) : ℂ)‖ ≤ R := by
  have hdn : d ≤ Fintype.card V := by
    obtain ⟨s, hs⟩ := card_pos.mp hpos
    rw [mem_downSets] at hs
    rw [← hs.1]; exact card_le_univ s
  have heq : P (fun k => (dc p k : ℝ)) (Fintype.card V) z = P (fun k => (dc p k : ℝ)) d z := by
    unfold P
    rw [← sum_range_add_sum_Ico _ (Nat.add_le_add_right hdn 1), add_eq_left]
    apply sum_eq_zero
    intro k hk
    rw [mem_Ico] at hk
    show ((dc p k : ℝ) : ℂ) * z ^ k = 0
    rw [habove k (by omega)]
    simp
  rw [heq] at hz
  have hcast : ∀ k, k < d → (g k : ℝ) * dc p k ≤ ((k : ℝ) + 1) * dc p (k + 1) := by
    intro k hk
    have := down_ratio_lower hdown g k (hg k hk)
    exact_mod_cast this
  refine shifted_disk _ d hd ρ R hρ hρR (fun j => Nat.cast_nonneg _) (by exact_mod_cast hpos)
    ?_ ?_ z hz
  · intro j hj
    have h1 := hcast j (by omega)
    have h2 := hrat j hj
    have hic : (0 : ℝ) ≤ dc p j := Nat.cast_nonneg _
    have hic1 : (0 : ℝ) ≤ dc p (j + 1) := Nat.cast_nonneg _
    have : ((j : ℝ) + 1) * dc p j ≤ ((j : ℝ) + 1) * (ρ * dc p (j + 1)) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · have h1 := hcast (d - 1) (by omega)
    have e : d - 1 + 1 = d := by omega
    rw [e] at h1
    have e2 : ((d - 1 : ℕ) : ℝ) + 1 = d := by
      rw [Nat.cast_sub hd]; push_cast; ring
    rw [e2] at h1
    have hic : (0 : ℝ) ≤ dc p (d - 1) := Nat.cast_nonneg _
    have hic1 : (0 : ℝ) ≤ dc p d := Nat.cast_nonneg _
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have : (d : ℝ) * dc p (d - 1) ≤ (d : ℝ) * (R * dc p d) := by nlinarith
    exact le_of_mul_le_mul_left this hd'

/-- **Corollary (extension-bounded complexes, disk).** With `ρ = R` as above, `|z| ≤ R`. -/
theorem down_ext_disk (hdown : ∀ s t : Finset V, s ⊆ t → p t → p s) {d : ℕ} (hd : 1 ≤ d)
    (hpos : 0 < dc p d) (habove : ∀ k, d < k → dc p k = 0) (g : ℕ → ℕ)
    (hg : ∀ k, k < d → ∀ s ∈ downSets p k, g k ≤ #(dext p s))
    (R : ℝ) (hR : 0 ≤ R) (hrat : ∀ k, k + 1 ≤ d → ((k : ℝ) + 1) ≤ R * g k)
    (z : ℂ) (hz : P (fun k => (dc p k : ℝ)) (Fintype.card V) z = 0) : ‖z‖ ≤ R := by
  have h := down_ext_shifted hdown hd hpos habove g hg R R hR le_rfl
    (fun k hk => hrat k (by omega))
    (by have := hrat (d - 1) (by omega); rwa [Nat.cast_sub hd, Nat.cast_one, sub_add_cancel] at this)
    z hz
  simpa using h

end ExtBounded

section AvgParam

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Theorem (parametric average-degree region).** For any `σ` with
`(n-1-d̄)/2 ≤ σ`, `(n-2-δ)/3 ≤ σ` and `σ ≤ n`, every independence root satisfies
`|1 + (n-σ) z| ≤ n |z|`. (Used for the random-graph corollary, where `d̄` is only bounded below.) -/
theorem indep_avg_param (hn : 1 ≤ Fintype.card V) (σ : ℝ)
    (hσ1 : ((Fintype.card V : ℝ) - 1 - (∑ v, (G.degree v : ℝ)) / Fintype.card V) / 2 ≤ σ)
    (hσ2 : ((Fintype.card V : ℝ) - 2 - G.minDegree) / 3 ≤ σ)
    (hσn : σ ≤ Fintype.card V) (z : ℂ)
    (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖1 + (((Fintype.card V : ℝ) - σ : ℝ) : ℂ) * z‖ ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  set n := Fintype.card V
  set δ := G.minDegree
  set S : ℝ := ∑ v, (G.degree v : ℝ) with hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h2 : 2 * (ic G 2 : ℝ) + S + n = (n : ℝ) * n := by
    have := two_ic_two G
    have h' : ((2 * ic G 2 + ∑ v, (G.degree v + 1) : ℕ) : ℝ) = ((n * n : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [sum_add_distrib] at h'
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h'
    rw [hS]; linarith
  have hS0 : 0 ≤ S := sum_nonneg (fun v _ => Nat.cast_nonneg _)
  have hic2 : (0 : ℝ) ≤ ic G 2 := Nat.cast_nonneg _
  have hSn : S / n ≤ n - 1 := by rw [div_le_iff₀ hnpos]; nlinarith
  have hσ0 : 0 ≤ σ := le_trans (by linarith) hσ1
  have hic0 : (ic G 0 : ℝ) = 1 := by rw [ic_zero]; simp
  have hic1 : (ic G 1 : ℝ) = n := by rw [ic_one]
  have hrat : ∀ j : ℕ, 1 ≤ j →
      ((j : ℝ) + 1) * ic G (j + 1) ≤ ((n : ℝ) - j - δ) * ic G j := by
    intro j hj
    have := ratio_upper (G := G) hj
    have h' : ((j : ℝ) + 1) * ic G (j + 1) + ((j : ℝ) + δ) * ic G j ≤ (n : ℝ) * ic G j := by
      exact_mod_cast this
    linarith
  refine shifted_inner _ n hn σ n hσ0 hσn (fun j => Nat.cast_nonneg _)
    (by rw [hic0]; norm_num) ?_ (by rw [hic0, hic1]; simp) z hz
  intro j hj _
  rcases Nat.eq_or_lt_of_le hj with rfl | hj2
  · rw [hic1]
    show (ic G 2 : ℝ) ≤ σ * n
    have : (ic G 2 : ℝ) = n * (((n : ℝ) - 1 - S / n) / 2) := by
      field_simp
      linarith
    rw [this]
    nlinarith
  · have h := hrat j hj
    have hic : (0 : ℝ) ≤ ic G j := Nat.cast_nonneg _
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    have key : ((n : ℝ) - j - δ) ≤ ((j : ℝ) + 1) * σ := by nlinarith
    have : ((j : ℝ) + 1) * ic G (j + 1) ≤ ((j : ℝ) + 1) * (σ * ic G j) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)

/-- **Corollary (edge-count form).** If the graph has at least `m₀` edges, i.e.
`∑ deg ≥ 2 m₀`, then with `σ₀ = max((n-1-2m₀/n)/2, (n-2)/3)` every independence root satisfies
`|1 + (n-σ₀) z| ≤ n |z|`. This is the deterministic input of the random-graph corollary. -/
theorem indep_edges (hn : 1 ≤ Fintype.card V) (m₀ : ℝ) (hm0 : 0 ≤ m₀)
    (hm : 2 * m₀ ≤ ∑ v, (G.degree v : ℝ)) (z : ℂ)
    (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖1 + (((Fintype.card V : ℝ) -
        max (((Fintype.card V : ℝ) - 1 - 2 * m₀ / Fintype.card V) / 2)
            (((Fintype.card V : ℝ) - 2) / 3) : ℝ) : ℂ) * z‖ ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hq : 0 ≤ 2 * m₀ / Fintype.card V := div_nonneg (by linarith) hnpos.le
  refine indep_avg_param G hn _ ?_ ?_ ?_ z hz
  · refine le_trans ?_ (le_max_left _ _)
    have : 2 * m₀ / Fintype.card V ≤ (∑ v, (G.degree v : ℝ)) / Fintype.card V :=
      div_le_div_of_nonneg_right hm hnpos.le
    linarith
  · refine le_trans ?_ (le_max_right _ _)
    have : (0 : ℝ) ≤ G.minDegree := Nat.cast_nonneg _
    linarith
  · apply max_le <;> linarith

/-- **Theorem (edge-count and minimum-degree form).** If `G` has at least `m₀ ≥ 0` edges
(`∑ deg ≥ 2 m₀`) and minimum degree at least `δ₀`, then with
`σ₀ = max((n-1-2m₀/n)/2, (n-2-δ₀)/3)` (assumed `≤ n`), every independence root satisfies
`|1 + (n-σ₀) z| ≤ n |z|`. This is the deterministic input of the random-graph theorem. -/
theorem indep_edges_mindeg (hn : 1 ≤ Fintype.card V) (m₀ δ₀ : ℝ)
    (hm : 2 * m₀ ≤ ∑ v, (G.degree v : ℝ)) (hδ : δ₀ ≤ G.minDegree)
    (hσn : max (((Fintype.card V : ℝ) - 1 - 2 * m₀ / Fintype.card V) / 2)
            (((Fintype.card V : ℝ) - 2 - δ₀) / 3) ≤ Fintype.card V)
    (z : ℂ) (hz : P (fun k => (ic G k : ℝ)) (Fintype.card V) z = 0) :
    ‖1 + (((Fintype.card V : ℝ) -
        max (((Fintype.card V : ℝ) - 1 - 2 * m₀ / Fintype.card V) / 2)
            (((Fintype.card V : ℝ) - 2 - δ₀) / 3) : ℝ) : ℂ) * z‖ ≤ (Fintype.card V : ℝ) * ‖z‖ := by
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  refine indep_avg_param G hn _ ?_ ?_ hσn z hz
  · refine le_trans ?_ (le_max_left _ _)
    have : 2 * m₀ / Fintype.card V ≤ (∑ v, (G.degree v : ℝ)) / Fintype.card V :=
      div_le_div_of_nonneg_right hm hnpos.le
    linarith
  · refine le_trans ?_ (le_max_right _ _)
    linarith

end AvgParam

/-! ## Part VIII. Matroids with bounded closures -/

section MatroidSec

variable {V : Type*} [Fintype V] [DecidableEq V] (M : Matroid V)
  [DecidablePred (fun s : Finset V => M.Indep (s : Set V))]

open Classical in
/-- Size of the closure of `s`, as a `Finset` count. -/
noncomputable def clCard (s : Finset V) : ℕ :=
  #((univ : Finset V).filter (fun v => v ∈ M.closure (s : Set V)))

lemma matroid_down : ∀ s t : Finset V, s ⊆ t →
    M.Indep (t : Set V) → M.Indep (s : Set V) :=
  fun _ _ hst ht => ht.subset (by exact_mod_cast hst)

/-- In a matroid with full ground set, `|ext(S)| + |cl(S)| ≥ n` for every independent `S`. -/
lemma matroid_ext_closure (hE : M.E = Set.univ) {s : Finset V} (hs : M.Indep (s : Set V)) :
    Fintype.card V ≤ #(dext (fun s : Finset V => M.Indep (s : Set V)) s) + clCard M s := by
  classical
  have hcov : (univ : Finset V) ⊆ dext (fun s : Finset V => M.Indep (s : Set V)) s ∪
      (univ : Finset V).filter (fun v => v ∈ M.closure (s : Set V)) := by
    intro v _
    by_cases hv : v ∈ M.closure (s : Set V)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ v, hv⟩)
    · apply mem_union_left
      have hvs : v ∉ s := by
        intro hvs
        apply hv
        exact M.subset_closure (s : Set V) (by rw [hE]; exact Set.subset_univ _) (by simpa using hvs)
      rw [mem_dext]
      refine ⟨hvs, ?_⟩
      rw [coe_insert, hs.insert_indep_iff_of_notMem (by simpa using hvs), hE]
      exact ⟨Set.mem_univ v, hv⟩
  have h1 := (card_le_card hcov).trans (card_union_le _ _)
  rw [card_univ] at h1
  exact h1

/-- Maximal independent `Finset`s are bases; hence the independence complex is pure. -/
lemma matroid_pure {r : ℕ} {B₀ : Finset V}
    (hB₀ : M.IsBase (B₀ : Set V)) (hr : #B₀ = r) :
    PureOf (fun s : Finset V => M.Indep (s : Set V)) r := by
  classical
  intro s hs
  have hbase : M.IsBase (s : Set V) := by
    refine hs.1.isBase_of_maximal (fun J hJ hsJ => ?_)
    by_contra hne
    obtain ⟨e, heJ, hes⟩ : ∃ e ∈ J, e ∉ (s : Set V) := by
      by_contra hcon
      push Not at hcon
      exact hne (Set.Subset.antisymm hsJ hcon)
    apply hs.2 e (by simpa using hes)
    have : ((insert e s : Finset V) : Set V) ⊆ J := by
      rw [coe_insert]; exact Set.insert_subset heJ hsJ
    exact hJ.subset this
  have := hbase.ncard_eq_ncard_of_isBase hB₀
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset] at this
  rw [this, hr]

/-- **Theorem (matroids with bounded closures).** Let `M` be a matroid on `V` (ground set all of
`V`, `n = |V|`) of rank `r ≥ 1`, and suppose every independent `k`-set has closure of size at
most `φ k`. With `g_k = max(r-k, n-φ_k)`, if `0 ≤ ρ ≤ R`, `k+1 ≤ ρ g_k` for `k ≤ r-2` and
`r ≤ R g_{r-1}`, every zero of the independence polynomial satisfies `|z + R - ρ| ≤ R`. -/
theorem matroid_closure_shifted (hE : M.E = Set.univ) {r : ℕ} (hr1 : 1 ≤ r) {B₀ : Finset V}
    (hB₀ : M.IsBase (B₀ : Set V)) (hr : #B₀ = r) (φ : ℕ → ℕ)
    (hφ : ∀ s : Finset V, M.Indep (s : Set V) → clCard M s ≤ φ #s)
    (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hrat : ∀ k, k + 2 ≤ r →
      ((k : ℝ) + 1) ≤ ρ * ((max (r - k) (Fintype.card V - φ k) : ℕ) : ℝ))
    (hlast : (r : ℝ) ≤ R * ((max 1 (Fintype.card V - φ (r - 1)) : ℕ) : ℝ))
    (z : ℂ) (hz : P (fun k => (dc (fun s : Finset V => M.Indep (s : Set V)) k : ℝ))
      (Fintype.card V) z = 0) :
    ‖z + ((R - ρ : ℝ) : ℂ)‖ ≤ R := by
  have hpure := matroid_pure M hB₀ hr
  have hne : M.Indep ((∅ : Finset V) : Set V) := by simp
  have e1 : r - (r - 1) = 1 := by omega
  refine down_ext_shifted (matroid_down M) hr1 (pure_dc_pos hne hpure)
    (fun k hk => pure_dc_eq_zero hpure hk) (fun k => max (r - k) (Fintype.card V - φ k)) ?_
    ρ R hρ hρR hrat (by simpa [e1] using hlast) z hz
  intro k _ s hs
  apply max_le
  · have := pure_dext_lower (matroid_down M) hpure hs; omega
  · rw [mem_downSets] at hs
    have h1 := matroid_ext_closure M hE hs.2
    have h2 := hφ s hs.2
    rw [hs.1] at h2
    omega

end MatroidSec

end GraphEK
