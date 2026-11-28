import OMAReductions.R_Erdos694_erdos_694_variants_inf_unique_R1_H1_R1
import Mathlib

-- Step H2 of reduction Erdos694.erdos_694.variants.inf_unique.R1.H1.R1.
-- Proof: Brun-Titchmarsh in progressions plus Mertens II give an m-th falling-factorial moment bound
-- for the number of small prime factors of p - 1; a square-part sieve handles repeated factors.
-- Pasted (pruned to the dependency closure): HilbertDB.BrunTitchmarsh (own Selberg sieve, sieve core
-- adapted from the abstract Selberg sieve of Steven Enamakel), HilbertDB.MertensSecond (own).

-- tags: Brun–Titchmarsh, Selberg sieve, primes in short intervals, primes in arithmetic progressions, upper bound sieve, π(x+y)-π(x) ≪ y/log y, Chebyshev upper bound, Selberg G ≥ (φ(q)/q) log z
-- use-when: explicit upper bound for the number of primes in (x, x+y] (≤ 165 y/log y, y ≥ 2), in a progression p ≡ a mod q up to x (≤ 170 x/(φ(q) log(x/q)), q < x), in (X, 2X] (≤ 165 X/log X) or in (x, x+x^θ] (≤ 330 x^θ/(θ log x)); sieve forms with free level z
-- source: own (Selberg sieve + G lower bound); sieve core copied from lemmas/NumberTheory/CoprimeSelbergSieve.lean (abstract Selberg/Rankin from @senamakel's Erdos16 romanoff R1.H1)
section

open scoped Classical
open Finset

namespace HilbertDB.BrunTitchmarsh

variable {ι : Type*} [DecidableEq ι]
/-- The Selberg function `h(p) = g(p)/(1 - g(p))` attached to a local density `g`. -/
noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

/-- Selberg's normaliser `G = Σ_{S ∈ D} Π_{p ∈ S} h(p)` for a support family `D`. -/
noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

/-- The optimal Selberg weights
`λ_S = (-1)^{|S|} (Π_{p∈S} g(p)⁻¹) G⁻¹ Σ_{T ∈ D, S ⊆ T} Π_{p∈T} h(p)`. -/
noncomputable def selbergWeight (g : ι → ℝ) (D : Finset (Finset ι)) (S : Finset ι) : ℝ :=
  (-1) ^ S.card * (∏ p ∈ S, (g p)⁻¹) / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p

/-- Inclusion-exclusion over an interval `[U, T]` of the subset lattice. -/
theorem sum_interval_neg_one_pow {U T : Finset ι} (hUT : U ⊆ T) :
    ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card = if T = U then (-1) ^ U.card else 0 := by
  have h1 : ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card
      = ∑ V ∈ (T \ U).powerset, (-1 : ℝ) ^ U.card * (-1) ^ V.card := by
    refine Finset.sum_nbij' (fun S => S \ U) (fun V => U ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS ⊢
      exact sdiff_subset_sdiff hS.1 le_rfl
    · intro V hV
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hV ⊢
      refine ⟨union_subset hUT (hV.trans sdiff_subset), subset_union_left⟩
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      exact union_sdiff_of_subset hS.2
    · intro V hV
      simp only [mem_powerset, mem_coe] at hV
      have : Disjoint U V := by
        rw [disjoint_iff_ne]; intro a ha b hb hab; subst hab
        have := hV hb; simp at this; exact this.2 ha
      exact union_sdiff_cancel_left this
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      rw [← pow_add, add_comm, card_sdiff_add_card_eq_card hS.2]
  have h2 : ∑ V ∈ (T \ U).powerset, ((-1 : ℝ)) ^ V.card = if T \ U = ∅ then 1 else 0 := by
    have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := T \ U))
    push_cast at this
    rw [this]
  rw [h1, ← mul_sum, h2]
  have : T \ U = ∅ ↔ T = U := by
    constructor
    · intro h; exact Subset.antisymm (sdiff_eq_empty_iff_subset.mp h) hUT
    · intro h; subst h; simp
  by_cases hT : T = U
  · simp [hT]
  · rw [if_neg (by rwa [this]), if_neg hT, mul_zero]

section Abstract

variable {Q : Finset ι} {g : ι → ℝ} {D : Finset (Finset ι)}

theorem hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {p : ι} (hp : p ∈ Q) :
    0 < hFun g p := div_pos (hg0 p hp) (by linarith [hg1 p hp])

theorem prod_hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S : Finset ι}
    (hS : S ⊆ Q) : 0 < ∏ p ∈ S, hFun g p :=
  prod_pos fun p hp => hFun_pos hg0 hg1 (hS hp)

/-- `G ≥ 1`, since the empty set contributes `1`. -/
theorem one_le_selbergG (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : 1 ≤ selbergG g D := by
  unfold selbergG
  have := single_le_sum (f := fun S => ∏ p ∈ S, hFun g p)
    (fun S hS => (prod_hFun_pos hg0 hg1 (hDQ S hS)).le) hemp
  simpa using this

theorem selbergWeight_mul_prod (hg0 : ∀ p ∈ Q, 0 < g p) {S : Finset ι} (hS : S ⊆ Q) :
    selbergWeight g D S * ∏ p ∈ S, g p
      = (-1) ^ S.card / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p := by
  unfold selbergWeight
  have h : (∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun p hp => inv_mul_cancel₀ (hg0 p (hS hp)).ne'
  calc _ = (-1) ^ S.card / selbergG g D * (∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p) *
        ((∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p) := by ring
    _ = _ := by rw [h, mul_one]

/-- The diagonalising variables `y_U = Σ_{S ∈ D, U ⊆ S} λ_S g(S)` of the Selberg weights. -/
theorem selbergY (hg0 : ∀ p ∈ Q, 0 < g p) (hDQ : ∀ S ∈ D, S ⊆ Q)
    (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (U : Finset ι) :
    ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / selbergG g D else 0 := by
  set G := selbergG g D
  set hS : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have e1 : ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = ∑ S ∈ D, ∑ T ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0 := by
    rw [sum_filter]
    refine sum_congr rfl fun S hSD => ?_
    by_cases hU : U ⊆ S
    · rw [if_pos hU, selbergWeight_mul_prod hg0 (hDQ S hSD), mul_sum, sum_filter]
      refine sum_congr rfl fun T _ => ?_
      by_cases hST : S ⊆ T <;> simp [hU, hST, hS, G]
    · rw [if_neg hU]; symm
      exact sum_eq_zero fun T _ => by simp [hU]
  rw [e1, sum_comm]
  have e2 : ∀ T ∈ D, (∑ S ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0)
      = if T = U then (-1) ^ U.card / G * hS U else 0 := by
    intro T hT
    rw [← sum_filter]
    by_cases hUT : U ⊆ T
    · have hf : D.filter (fun S => U ⊆ S ∧ S ⊆ T) = T.powerset.filter (fun S => U ⊆ S) := by
        ext S; simp only [mem_filter, mem_powerset]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩; exact ⟨hdown T hT S h2, h1, h2⟩
      rw [hf, ← sum_mul, ← sum_div, sum_interval_neg_one_pow hUT]
      by_cases hTU : T = U
      · subst hTU; simp
      · simp [hTU]
    · have hTU : T ≠ U := by rintro rfl; exact hUT le_rfl
      rw [if_neg hTU]
      refine sum_eq_zero fun S hS' => ?_
      simp only [mem_filter] at hS'
      exact absurd (hS'.2.1.trans hS'.2.2) hUT
  rw [sum_congr rfl e2, sum_ite_eq']
  split_ifs <;> ring

theorem prod_union_eq (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S₁ S₂ : Finset ι}
    (h₁ : S₁ ⊆ Q) (h₂ : S₂ ⊆ Q) :
    ∏ p ∈ S₁ ∪ S₂, g p = (∏ p ∈ S₁, g p) * (∏ p ∈ S₂, g p) *
      ∑ U ∈ Q.powerset, if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0 := by
  have hinv : (∏ p ∈ S₁ ∩ S₂, g p)⁻¹ = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← prod_inv_distrib]
    have : ∀ p ∈ S₁ ∩ S₂, (g p)⁻¹ = 1 + (hFun g p)⁻¹ := by
      intro p hp
      have hp' : p ∈ Q := h₁ (mem_inter.mp hp).1
      have a := hg0 p hp'; have b := hg1 p hp'
      unfold hFun; rw [inv_div]; field_simp; ring
    rw [prod_congr rfl this, prod_one_add]
    exact sum_congr rfl fun U _ => by rw [prod_inv_distrib]
  have hsum : ∑ U ∈ Q.powerset, (if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0)
      = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext U; simp only [mem_filter, mem_powerset, subset_inter_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1.trans h₁, h⟩
  have hne : (∏ p ∈ S₁ ∩ S₂, g p) ≠ 0 :=
    (prod_pos fun p hp => hg0 p (h₁ (mem_inter.mp hp).1)).ne'
  rw [hsum, ← hinv, ← prod_union_inter (s₁ := S₁) (s₂ := S₂)]
  field_simp

/-- The Selberg quadratic form evaluated at the optimal weights equals `1 / G`. -/
theorem selberg_mainTerm (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D) :
    ∑ S₁ ∈ D, ∑ S₂ ∈ D, selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
      = 1 / selbergG g D := by
  set G := selbergG g D with hG
  set a : Finset ι → ℝ := fun S => selbergWeight g D S * ∏ p ∈ S, g p
  set w : Finset ι → ℝ := fun U => (∏ p ∈ U, hFun g p)⁻¹
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have e1 : ∀ S₁ ∈ D, ∀ S₂ ∈ D,
      selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
        = ∑ U ∈ Q.powerset, w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0)) := by
    intro S₁ h₁ S₂ h₂
    rw [prod_union_eq hg0 hg1 (hDQ _ h₁) (hDQ _ h₂), mul_sum, mul_sum]
    refine sum_congr rfl fun U _ => ?_
    by_cases u1 : U ⊆ S₁ <;> by_cases u2 : U ⊆ S₂ <;> simp [u1, u2, a, w] <;> ring
  rw [sum_congr rfl fun S₁ h₁ => sum_congr rfl fun S₂ h₂ => e1 S₁ h₁ S₂ h₂]
  have eswap : ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∑ U ∈ Q.powerset,
      w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0))
      = ∑ U ∈ Q.powerset, w U * ((∑ S ∈ D with U ⊆ S, a S) * (∑ S ∈ D with U ⊆ S, a S)) := by
    simp_rw [sum_filter, sum_mul_sum, mul_sum]
    conv_lhs => arg 2; ext S₁; rw [sum_comm]
    rw [sum_comm]
  rw [eswap]
  have hy : ∀ U, ∑ S ∈ D with U ⊆ S, a S
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0 :=
    selbergY hg0 hDQ hdown
  simp_rw [hy]
  have e3 : ∀ U ∈ Q.powerset, w U * ((if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0) *
      (if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0))
      = if U ∈ D then (∏ p ∈ U, hFun g p) / G ^ 2 else 0 := by
    intro U hU
    split_ifs with hUD
    · have hpos := prod_hFun_pos hg0 hg1 (hDQ U hUD)
      simp only [w]
      field_simp
      rw [← pow_mul, mul_comm (U.card) 2, pow_mul]; simp
    · simp
  rw [sum_congr rfl e3, ← sum_filter]
  have : Q.powerset.filter (fun U => U ∈ D) = D := by
    ext U; simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨hDQ U h, h⟩⟩
  rw [this, ← sum_div]
  change G / G ^ 2 = 1 / G
  field_simp

/-- The optimal Selberg weights satisfy `|λ_S| ≤ 1`. -/
theorem abs_selbergWeight_le (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    {S : Finset ι} (hS : S ∈ D) : |selbergWeight g D S| ≤ 1 := by
  set G := selbergG g D with hG
  set hp : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have hSQ := hDQ S hS
  have hnn : ∀ T ⊆ Q, 0 ≤ hp T := fun T hT => (prod_hFun_pos hg0 hg1 hT).le
  have hginv : 0 < ∏ p ∈ S, (g p)⁻¹ := prod_pos fun p h => inv_pos.mpr (hg0 p (hSQ h))
  have habs : |selbergWeight g D S|
      = (∏ p ∈ S, (g p)⁻¹) * (∑ T ∈ D with S ⊆ T, hp T) / G := by
    unfold selbergWeight
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hginv, abs_of_pos (by linarith : (0:ℝ) < G),
      abs_of_nonneg (sum_nonneg fun T hT => hnn T (hDQ T (mem_filter.mp hT).1))]
    ring
  rw [habs, div_le_one (by linarith)]
  have key : ∀ T ∈ D.filter (fun T => S ⊆ T),
      (∏ p ∈ S, (g p)⁻¹) * hp T = ∑ W ∈ S.powerset, hp (W ∪ (T \ S)) := by
    intro T hT
    have hST := (mem_filter.mp hT).2
    have h1 : hp T = hp S * hp (T \ S) := by
      simp only [hp]; rw [mul_comm, prod_sdiff hST]
    have h2 : (∏ p ∈ S, (g p)⁻¹) * hp S = ∏ p ∈ S, (1 + hFun g p) := by
      simp only [hp]; rw [← prod_mul_distrib]
      refine prod_congr rfl fun p h => ?_
      have a := hg0 p (hSQ h); have b := hg1 p (hSQ h)
      have c : 1 - g p ≠ 0 := by linarith
      unfold hFun; field_simp; ring
    rw [h1, ← mul_assoc, h2, prod_one_add, sum_mul]
    refine sum_congr rfl fun W hW => ?_
    simp only [hp]
    rw [prod_union]
    exact disjoint_of_subset_left (mem_powerset.mp hW) disjoint_sdiff
  rw [mul_sum, sum_congr rfl key, sum_comm, ← sum_product']
  rw [← sum_image (s := S.powerset ×ˢ D.filter (fun T => S ⊆ T)) (g := fun x => x.1 ∪ (x.2 \ S))
    (f := hp)]
  · apply sum_le_sum_of_subset_of_nonneg
    · intro U hU
      simp only [mem_image, mem_product, mem_powerset, mem_filter] at hU
      obtain ⟨⟨W, T⟩, ⟨hW, hT, _⟩, rfl⟩ := hU
      exact hdown T hT _ (union_subset (hW.trans (by assumption)) sdiff_subset)
    · intro U hU _
      exact hnn U (hDQ U hU)
  · intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powerset, mem_filter] at hx hy
    simp only at hxy
    have e1 : x.1 = (x.1 ∪ (x.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hx.1]
    have e2 : y.1 = (y.1 ∪ (y.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hy.1]
    have f1 : x.2 = S ∪ (x.1 ∪ (x.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hx.1, union_sdiff_of_subset hx.2.2]
    have f2 : y.2 = S ∪ (y.1 ∪ (y.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hy.1, union_sdiff_of_subset hy.2.2]
    exact Prod.ext (by rw [e1, e2, hxy]) (by rw [f1, f2, hxy])

theorem selbergWeight_empty (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : selbergWeight g D ∅ = 1 := by
  have hG1 : 1 ≤ selbergG g D := one_le_selbergG hg0 hg1 hDQ hemp
  unfold selbergWeight
  simp only [card_empty, pow_zero, prod_empty, one_mul, empty_subset, filter_true_of_mem,
    implies_true]
  change 1 / selbergG g D * selbergG g D = 1
  field_simp

/-- **Selberg's upper-bound sieve, abstract form.**

`A` is a finite family of objects, `E a` is the set of primes dividing `a`, `Q` is the finite
set of sieving primes, and `D` is any down-closed family of subsets of `Q` containing `∅` (the
support of the Selberg weights; for the classical sieve, the sets of primes with product `< z`).
If for every `S ⊆ Q` the number of `a` divisible by all of `S` is `X * Π_{p∈S} g p + r S`, with
`0 < g p < 1`, then the number of `a` free of all primes of `Q` is at most
`X / G + Σ_{S₁, S₂ ∈ D} |r (S₁ ∪ S₂)|`, where `G = selbergG g D`. -/
theorem selberg_sieve_abstract {α : Type*} (A : Finset α) (E : α → Finset ι)
    (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    (X : ℝ) (r : Finset ι → ℝ)
    (hr : ∀ S ⊆ Q, ((A.filter (fun a => S ⊆ E a)).card : ℝ) = X * ∏ p ∈ S, g p + r S) :
    ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
  set lam := selbergWeight g D
  have step1 : ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2 := by
    rw [card_filter]; push_cast
    refine sum_le_sum fun a _ => ?_
    split_ifs with hd
    · have : (∑ S ∈ D, if S ⊆ E a then lam S else 0) = lam ∅ := by
        have e := sum_ite_eq' D ∅ lam
        rw [if_pos hemp] at e
        rw [← e]
        refine sum_congr rfl fun S hS => ?_
        by_cases hS0 : S = ∅
        · subst hS0; simp
        · have : ¬ S ⊆ E a := by
            intro h
            apply hS0
            exact subset_empty.mp fun x hx =>
              (disjoint_left.mp hd (hDQ S hS hx) (h hx)).elim
          simp [this, hS0, Ne.symm hS0]
      have e1 : lam ∅ = 1 := selbergWeight_empty hg0 hg1 hDQ hemp
      rw [this, e1]; norm_num
    · positivity
  have step2 : ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2
      = ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ) := by
    simp_rw [sq, sum_mul_sum, card_filter]
    push_cast
    rw [sum_comm]
    refine sum_congr rfl fun S₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun S₂ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : S₁ ⊆ E a <;> by_cases h2 : S₂ ⊆ E a <;> simp [h1, h2, union_subset_iff]
  have step3 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ)
      = X * (∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * ∏ p ∈ S₁ ∪ S₂, g p)
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₁ h₁ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₂ h₂ => ?_
    rw [hr _ (union_subset (hDQ _ h₁) (hDQ _ h₂))]; ring
  have step4 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂)
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have a1 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₁
    have a2 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₂
    calc lam S₁ * lam S₂ * r (S₁ ∪ S₂) ≤ |lam S₁ * lam S₂ * r (S₁ ∪ S₂)| := le_abs_self _
      _ = |lam S₁| * |lam S₂| * |r (S₁ ∪ S₂)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * |r (S₁ ∪ S₂)| := by gcongr
      _ = _ := by ring
  rw [selberg_mainTerm hg0 hg1 hDQ hdown hemp] at step3
  calc _ ≤ _ := step1
    _ = _ := step2
    _ = _ := step3
    _ ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
      rw [mul_one_div]; linarith

end Abstract
/-! ## Counting residue conditions -/


theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hper : ∀ n, P n ↔ P (n % m)) (q : ℕ) :
    Nat.count P (m * q) = q * Nat.count P m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hfun : (fun k => P (m * q + k)) = P := by
      funext k; apply propext
      rw [hper (m * q + k), hper k, Nat.mul_add_mod]
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : Nat.count (fun k => P (m * q + k)) m = Nat.count P m := by
      simp_rw [hfun]
    rw [this]; ring

/-- Counting a periodic set in an initial segment: if `P` is `m`-periodic with `K` solutions
in `[0, m)`, then the number of solutions in `[0, N)` is `N K / m` up to an error of at most `K`. -/
theorem card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : 0 < m)
    (hper : ∀ n, P n ↔ P (n % m)) (N : ℕ) :
    |(((range N).filter P).card : ℝ) - N * ((range m).filter P).card / m|
      ≤ ((range m).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  set K := Nat.count P m
  have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hc : Nat.count P N = (N / m) * K + Nat.count P (N % m) := by
    conv_lhs => rw [hN]
    rw [Nat.count_add, count_periodic_mul P hper]
    congr 1
    congr 1
    funext k; apply propext
    rw [hper (m * (N / m) + k), hper k, Nat.mul_add_mod]
  have hle : Nat.count P (N % m) ≤ K := Nat.count_monotone P (Nat.mod_lt N hm).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  have hNR : (N : ℝ) = m * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [hc, abs_le]
  push_cast
  have hleR : ((Nat.count P (N % m) : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (N : ℝ) * K / m = ((N / m : ℕ) : ℝ) * K + ((N % m : ℕ) : ℝ) * K / m := by
    rw [hNR]; field_simp
  have h2 : ((N % m : ℕ) : ℝ) * K / m ≤ K := by
    rw [div_le_iff₀ hmR]; nlinarith
  have h3 : 0 ≤ ((N % m : ℕ) : ℝ) * K / m := by positivity
  rw [e]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (N % m))]


theorem card_filter_range_mul (F : ℕ → Prop) [DecidablePred F] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ((range (p * m)).filter F).card
      = ∑ j ∈ range p, ((range m).filter (fun t => F (j + p * t))).card := by
  have : ((range (p * m)).filter F).card
      = ((range p ×ˢ range m).filter (fun x => F (x.1 + p * x.2))).card := by
    refine Finset.card_nbij' (fun r => (r % p, r / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hx
      simp only
      refine Prod.ext ?_ ?_
      · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1.1]
      · simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1.1, zero_add]
  rw [this, card_filter, sum_product]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem card_filter_range_shift (P : ℕ → Prop) [DecidablePred P] {m p : ℕ} (hm : 0 < m) (hpm : Nat.Coprime p m)
    (hper : ∀ n, P n ↔ P (n % m)) (j : ℕ) :
    ((range m).filter (fun t => P (j + p * t))).card = ((range m).filter P).card := by
  set f : ℕ → ℕ := fun t => (j + p * t) % m
  have hinj : Set.InjOn f (range m) := by
    intro t ht t' ht' h
    simp only [coe_range, Set.mem_Iio] at ht ht'
    have h1 : j + p * t ≡ j + p * t' [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' j h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hpm) h2
    have := Nat.mod_eq_of_lt ht; have := Nat.mod_eq_of_lt ht'
    unfold Nat.ModEq at h3; omega
  have himg : (range m).image f = range m := by
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_image, mem_range] at hu ⊢
      obtain ⟨t, _, rfl⟩ := hu
      exact Nat.mod_lt _ hm
    · rw [card_image_of_injOn hinj]
  have hfilt : (range m).filter (fun t => P (j + p * t)) = (range m).filter (fun t => P (f t)) := by
    refine filter_congr fun t _ => ?_
    simp only [f]; exact hper _
  have himg2 : (range m).filter P = ((range m).filter (fun t => P (f t))).image f := by
    ext u
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hu, hP⟩
      rw [← himg] at hu
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
      exact ⟨t, ⟨ht, hP⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
      exact ⟨mem_range.mpr (Nat.mod_lt _ hm), hP⟩
  rw [hfilt, himg2, card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Chinese remainder count: if each condition `C p` is `p`-periodic, the number of residues
modulo `Π_{p∈S} p` satisfying all of them is `Π_{p∈S} ω(p)`. -/
theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (hSc : (S : Set ℕ).Pairwise Nat.Coprime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, 0 < q := fun q hq => hS q (mem_insert_of_mem hq)
    have hSc' : (S : Set ℕ).Pairwise Nat.Coprime := hSc.mono (by simp)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => hS' q hq
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      hSc (by simp) (by simp [hq]) (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp, ← ih hS' hSc']
    have hperS : ∀ n, (∀ q ∈ S, C q n) ↔ (∀ q ∈ S, C q (n % ∏ q ∈ S, q)) := by
      intro n
      refine forall₂_congr fun q hq => ?_
      have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
      rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
    have step : ∀ j ∈ range p,
        ((range (∏ q ∈ S, q)).filter (fun t => ∀ q ∈ insert p S, C q (j + p * t))).card
          = if C p j then ((range (∏ q ∈ S, q)).filter (fun r => ∀ q ∈ S, C q r)).card else 0 := by
      intro j hj
      have hj' : ∀ t, C p (j + p * t) ↔ C p j := by
        intro t
        rw [hper p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hj)]
      simp_rw [forall_mem_insert, hj']
      split_ifs with hc
      · simp only [hc, true_and]
        convert card_filter_range_shift (fun n => ∀ q ∈ S, C q n) hm hcop hperS j using 2 <;> (ext; simp)
      · simp [hc]
    rw [sum_congr rfl step, ← sum_filter, sum_const, smul_eq_mul]

/-- The number `ω(p)` of residues `r ∈ [0, p)` that are removed by the local condition `C p`. -/
noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

/-- The classical Selberg support: sets of primes from `Q` whose product is `< z`. -/
noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

/-- The number of `n < N` meeting every condition `C p`, `p ∈ S`, is `N Π_{p∈S} ω(p)/p` up to an
error of at most `Π_{p∈S} ω(p)`. -/
theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (hSc : (S : Set ℕ).Pairwise Nat.Coprime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => hS p hp
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS hSc
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

/-- **Selberg's sieve for residue conditions.** For each prime `p ∈ Q` let `C p` be a
`p`-periodic condition on `ℕ` holding for `ω(p)` residues, with `0 < ω(p) < p`. Then the number
of `n < N` satisfying no condition `C p`, `p ∈ Q`, is at most
`N / G + Σ_{S₁,S₂ ∈ D} Π_{p ∈ S₁ ∪ S₂} ω(p)`, with `G = selbergG (ω/p) D`, for any down-closed
support family `D ∋ ∅` of subsets of `Q`. -/
theorem selberg_residue (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p)
    (hQc : (Q : Set ℕ).Pairwise Nat.Coprime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p)
    (D : Finset (Finset ℕ)) (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D)
    (hemp : ∅ ∈ D) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) D
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
  set g : ℕ → ℝ := fun p => (omega C p : ℝ) / p
  have hg0 : ∀ p ∈ Q, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast hω0 p hp) (by exact_mod_cast hQ p hp)
  have hg1 : ∀ p ∈ Q, g p < 1 := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast hQ p hp
    simp only [g]; rw [div_lt_one this]; exact_mod_cast hω1 p hp
  set E : ℕ → Finset ℕ := fun n => Q.filter (fun p => C p n)
  set r : Finset ℕ → ℝ := fun S =>
    (((range N).filter (fun n => S ⊆ E n)).card : ℝ) - N * ∏ p ∈ S, g p
  have key := selberg_sieve_abstract (range N) E hg0 hg1 hDQ hdown hemp (N : ℝ) r
    (fun S _ => by simp only [r]; rw [add_sub_cancel])
  have hrem : ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)|
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset (hDQ _ h₁) (hDQ _ h₂)
    have hc : ((range N).filter (fun n => S₁ ∪ S₂ ⊆ E n)).card
        = ((range N).filter (fun n => ∀ p ∈ S₁ ∪ S₂, C p n)).card := by
      congr 1; ext n
      simp only [E, mem_filter, subset_iff]
      exact ⟨fun h => ⟨h.1, fun p hp => (h.2 hp).2⟩, fun h => ⟨h.1, fun p hp => ⟨hSQ hp, h.2 p hp⟩⟩⟩
    have := card_residue_error C hper (S₁ ∪ S₂) (fun p hp => hQ p (hSQ hp))
      (hQc.mono (by exact_mod_cast hSQ)) N
    simp only [r]; rw [hc]
    exact this
  have k2 := key.trans (add_le_add le_rfl hrem)
  have hc : ((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card
      = ((range N).filter (fun n => Disjoint Q (E n))).card := by
    congr 1; ext n
    simp only [E, disjoint_left, mem_filter, not_and]
    exact ⟨fun h => ⟨h.1, fun p hp _ => h.2 p hp⟩, fun h => ⟨h.1, fun p hp => h.2 hp hp⟩⟩
  have hc' : (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      = (((range N).filter (fun n => Disjoint Q (E n))).card : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  exact k2

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun S hS => mem_powerset.mp (mem_filter.mp hS).1

theorem levelFamily_down {Q : Finset ℕ} (hQ : ∀ p ∈ Q, 0 < p) {z : ℕ} :
    ∀ S ∈ levelFamily Q z, ∀ T ⊆ S, T ∈ levelFamily Q z := by
  intro S hS T hT
  simp only [levelFamily, mem_filter, mem_powerset] at hS ⊢
  refine ⟨hT.trans hS.1, lt_of_le_of_lt ?_ hS.2⟩
  exact prod_le_prod_of_subset_of_one_le' hT fun p hp _ => hQ p (hS.1 hp)

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

/-- Distinct subsets of a pairwise coprime family of numbers `≥ 2` have distinct products. -/
theorem prod_injOn {Q : Finset ℕ} (hQ2 : ∀ p ∈ Q, 2 ≤ p) (hQc : (Q : Set ℕ).Pairwise Nat.Coprime)
    {S T : Finset ℕ} (hS : S ⊆ Q) (hT : T ⊆ Q) (h : ∏ p ∈ S, p = ∏ p ∈ T, p) : S = T := by
  have key : ∀ {S T : Finset ℕ}, S ⊆ Q → T ⊆ Q → ∏ p ∈ S, p = ∏ p ∈ T, p → S ⊆ T := by
    intro S T hS hT h p hp
    by_contra hpT
    have hdvd : p ∣ ∏ q ∈ T, q := h ▸ dvd_prod_of_mem (fun i : ℕ => i) hp
    have hcop : Nat.Coprime p (∏ q ∈ T, q) := Nat.Coprime.prod_right fun q hq =>
      hQc (hS hp) (hT hq) (fun e => hpT (e ▸ hq))
    have := Nat.Coprime.eq_one_of_dvd hcop hdvd
    have := hQ2 p (hS hp)
    omega
  exact Subset.antisymm (key hS hT h) (key hT hS h.symm)

theorem card_levelFamily_le {Q : Finset ℕ} (hQ2 : ∀ p ∈ Q, 2 ≤ p)
    (hQc : (Q : Set ℕ).Pairwise Nat.Coprime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_ofPred_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_ofPred_eq] at hS hT
      exact prod_injOn hQ2 hQc hS.1 hT.1 h)
  simpa using this

/-- **Selberg's sieve at level `z`, with a crude explicit remainder.** With the classical support
`levelFamily Q z` (products of primes `< z`), the number of `n < N` meeting no condition `C p`,
`p ∈ Q`, is at most `N / G + z ^ 4`. -/
theorem selberg_residue_level (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hQ2 : ∀ p ∈ Q, 2 ≤ p)
    (hQc : (Q : Set ℕ).Pairwise Nat.Coprime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z) + (z : ℝ) ^ 4 := by
  have hQ : ∀ p ∈ Q, 0 < p := fun p hp => by have := hQ2 p hp; omega
  have key := selberg_residue N Q hQ hQc C hper hω0 hω1 (levelFamily Q z) levelFamily_subset
    (levelFamily_down hQ) (empty_mem_levelFamily hz)
  refine key.trans (add_le_add le_rfl ?_)
  have hterm : ∀ S₁ ∈ levelFamily Q z, ∀ S₂ ∈ levelFamily Q z,
      ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ (z : ℝ) ^ 2 := by
    intro S₁ h₁ S₂ h₂
    have h₁' := h₁; have h₂' := h₂
    simp only [levelFamily, mem_filter, mem_powerset] at h₁' h₂'
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset h₁'.1 h₂'.1
    have a : ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ ∏ p ∈ S₁ ∪ S₂, (p : ℝ) :=
      prod_le_prod (fun p _ => by positivity)
        (fun p hp => by exact_mod_cast (hω1 p (hSQ hp)).le)
    have b : ∏ p ∈ S₁ ∪ S₂, p ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
      rw [← prod_union_inter]
      exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => hQ p (h₁'.1 (mem_inter.mp hp).1))
    have c : (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ≤ z * z :=
      Nat.mul_le_mul h₁'.2.le h₂'.2.le
    have : ((∏ p ∈ S₁ ∪ S₂, p : ℕ) : ℝ) ≤ (z : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast b.trans c
    push_cast at this
    linarith
  calc ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ)
      ≤ ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, (z : ℝ) ^ 2 :=
        sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => hterm S₁ h₁ S₂ h₂
    _ = ((levelFamily Q z).card : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        have h1 : ((levelFamily Q z).card : ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ2 hQc z
        have h0 : (0 : ℝ) ≤ ((levelFamily Q z).card : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = (z : ℝ) ^ 4 := by ring

/-- `selbergG` only depends on `g` on the primes of `Q`. -/
theorem selbergG_congr {Q : Finset ℕ} {D : Finset (Finset ℕ)} (hDQ : ∀ S ∈ D, S ⊆ Q)
    {g g' : ℕ → ℝ} (h : ∀ p ∈ Q, g p = g' p) : selbergG g D = selbergG g' D := by
  unfold selbergG hFun
  exact sum_congr rfl fun S hS => prod_congr rfl fun p hp => by rw [h p (hDQ S hS hp)]

/-! ## Selberg's G ≥ log z for the one-dimensional prime sieve -/

theorem hFun_inv_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ hFun (fun p : ℕ => 1 / (p : ℝ)) p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold hFun
  apply div_nonneg (by positivity)
  rw [sub_nonneg, div_le_one (by linarith)]; linarith

/-- Truncated geometric series: `Σ_{1 ≤ k < K} p^{-k} ≤ 1/(p-1) = h(p)`. -/
theorem geom_le_hFun {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    ∑ k ∈ Ico 1 K, (1 / (p : ℝ)) ^ k ≤ hFun (fun p : ℕ => 1 / (p : ℝ)) p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have := geom_sum_Ico_le_of_lt_one (m := 1) (n := K) (x := 1 / (p : ℝ)) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith)
  simpa [hFun] using this

/-- For a set `S` of primes, the `m < z` with prime support exactly `S` contribute at most
`Π_{p∈S} 1/(p-1)` to the harmonic sum. -/
theorem sum_fiber_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (z : ℕ) :
    ∑ m ∈ (Ico 1 z).filter (fun m => m.primeFactors = S), 1 / (m : ℝ)
      ≤ ∏ p ∈ S, hFun (fun p : ℕ => 1 / (p : ℝ)) p := by
  set F := (Ico 1 z).filter (fun m => m.primeFactors = S)
  set φ : ℕ → ((a : ℕ) → a ∈ S → ℕ) := fun m => fun p _ => m.factorization p
  have hF : ∀ m ∈ F, m ≠ 0 ∧ m < z ∧ m.primeFactors = S := by
    intro m hm
    simp only [F, mem_filter, mem_Ico] at hm
    exact ⟨by omega, hm.1.2, hm.2⟩
  have hinj : Set.InjOn φ F := by
    intro m hm m' hm' h
    obtain ⟨h0, -, hpf⟩ := hF m hm
    obtain ⟨h0', -, hpf'⟩ := hF m' hm'
    refine Nat.eq_of_factorization_eq h0 h0' fun p => ?_
    by_cases hp : p ∈ S
    · exact congrFun (congrFun h p) hp
    · have a : p ∉ m.factorization.support := by rw [Nat.support_factorization, hpf]; exact hp
      have b : p ∉ m'.factorization.support := by rw [Nat.support_factorization, hpf']; exact hp
      rw [Finsupp.notMem_support_iff.mp a, Finsupp.notMem_support_iff.mp b]
  have himg : F.image φ ⊆ S.pi (fun _ => Ico 1 z) := by
    intro f hf
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hf
    obtain ⟨h0, hz, hpf⟩ := hF m hm
    rw [mem_pi]
    intro p hp
    simp only [φ, mem_Ico]
    have hp' : p ∈ m.factorization.support := by rw [Nat.support_factorization, hpf]; exact hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp'),
      (Nat.factorization_lt p h0).trans hz⟩
  have hterm : ∀ m ∈ F, ∏ x ∈ S.attach, (1 / (x.1 : ℝ)) ^ (φ m x.1 x.2) = 1 / (m : ℝ) := by
    intro m hm
    obtain ⟨h0, -, hpf⟩ := hF m hm
    simp only [φ]
    rw [prod_attach S (fun p => (1 / (p : ℝ)) ^ m.factorization p)]
    have e : (m : ℝ) = ∏ p ∈ S, (p : ℝ) ^ m.factorization p := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization h0]
      rw [hpf]; push_cast; rfl
    rw [e]; simp only [div_pow, one_pow]; rw [prod_div_distrib, prod_const_one]
  have hnn : ∀ f ∈ S.pi (fun _ => Ico 1 z),
      0 ≤ ∏ x ∈ S.attach, (1 / (x.1 : ℝ)) ^ (f x.1 x.2) := fun f _ =>
    prod_nonneg fun x _ => by positivity
  calc ∑ m ∈ F, 1 / (m : ℝ)
      = ∑ m ∈ F, ∏ x ∈ S.attach, (1 / (x.1 : ℝ)) ^ (φ m x.1 x.2) :=
        (sum_congr rfl hterm).symm
    _ = ∑ f ∈ F.image φ, ∏ x ∈ S.attach, (1 / (x.1 : ℝ)) ^ (f x.1 x.2) :=
        (sum_image (f := fun f => ∏ x ∈ S.attach, (1 / (x.1 : ℝ)) ^ (f x.1 x.2)) hinj).symm
    _ ≤ ∑ f ∈ S.pi (fun _ => Ico 1 z), ∏ x ∈ S.attach, (1 / (x.1 : ℝ)) ^ (f x.1 x.2) :=
        sum_le_sum_of_subset_of_nonneg himg fun f hf _ => hnn f hf
    _ = ∏ p ∈ S, ∑ k ∈ Ico 1 z, (1 / (p : ℝ)) ^ k :=
        (prod_sum S (fun _ => Ico 1 z) (fun p k => (1 / (p : ℝ)) ^ k)).symm
    _ ≤ ∏ p ∈ S, hFun (fun p : ℕ => 1 / (p : ℝ)) p :=
        prod_le_prod (fun p _ => sum_nonneg fun k _ => by positivity)
          (fun p hp => geom_le_hFun (hS p hp).two_le z)

/-- **Selberg's `G` dominates the harmonic sum** (one-dimensional prime case). If `Q` is a set
of primes containing every prime `< z`, then with `g(p) = 1/p`,
`Σ_{1 ≤ m < z} 1/m ≤ G = Σ_{S ⊆ Q, Π S < z} Π_{p∈S} 1/(p-1)`. -/
theorem harmonic_le_selbergG (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (z : ℕ) (hQz : ∀ p, p.Prime → p < z → p ∈ Q) :
    ∑ m ∈ Ico 1 z, 1 / (m : ℝ) ≤ selbergG (fun p : ℕ => 1 / (p : ℝ)) (levelFamily Q z) := by
  have hmaps : ∀ m ∈ Ico 1 z, m.primeFactors ∈ levelFamily Q z := by
    intro m hm
    rw [mem_Ico] at hm
    have h0 : m ≠ 0 := by omega
    simp only [levelFamily, mem_filter, mem_powerset]
    refine ⟨fun p hp => ?_, ?_⟩
    · have hpp := Nat.prime_of_mem_primeFactors hp
      exact hQz p hpp (lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
        hm.2)
    · exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)) hm.2
  rw [← sum_fiberwise_of_maps_to hmaps]
  unfold selbergG
  refine sum_le_sum fun S hS => ?_
  have hSQ : S ⊆ Q := mem_powerset.mp (mem_filter.mp hS).1
  exact sum_fiber_le_prod S (fun p hp => hQ p (hSQ hp)) z

/-- `log z ≤ Σ_{1 ≤ m < z} 1/m` for `z ≥ 1`. -/
theorem log_le_sum_Ico_inv (z : ℕ) (hz : 1 ≤ z) :
    Real.log z ≤ ∑ m ∈ Ico 1 z, 1 / (m : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, z = n + 1 := ⟨z - 1, by omega⟩
  have h := log_add_one_le_harmonic n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have e : Ico 1 (n + 1) = Icc 1 n := by ext; simp [mem_Ico, mem_Icc]
  rw [e]; simpa using h

/-- **`G ≥ log z`** for the one-dimensional prime sieve: `Q` a set of primes containing all
primes `< z`, `g(p) = 1/p`, support `levelFamily Q z`. -/
theorem log_le_selbergG (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (z : ℕ) (hz : 1 ≤ z) (hQz : ∀ p, p.Prime → p < z → p ∈ Q) :
    Real.log z ≤ selbergG (fun p : ℕ => 1 / (p : ℝ)) (levelFamily Q z) :=
  (log_le_sum_Ico_inv z hz).trans (harmonic_le_selbergG Q hQ z hQz)

/-! ## Removing the primes dividing `q` from `G` -/

theorem selbergG_le_prod_mul (z q : ℕ) (hq : q ≠ 0) :
    selbergG (fun p : ℕ => 1 / (p : ℝ)) (levelFamily ((range z).filter Nat.Prime) z)
      ≤ (∏ p ∈ q.primeFactors, (1 + hFun (fun p : ℕ => 1 / (p : ℝ)) p)) *
        selbergG (fun p : ℕ => 1 / (p : ℝ))
          (levelFamily ((range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)) z) := by
  set g : ℕ → ℝ := fun p : ℕ => 1 / (p : ℝ)
  set P := q.primeFactors
  set LF := levelFamily ((range z).filter Nat.Prime) z
  set LFq := levelFamily ((range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)) z
  set H : Finset ℕ → ℝ := fun S => ∏ p ∈ S, hFun g p
  have hH : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 0 ≤ H S := fun S hS =>
    prod_nonneg fun p hp => hFun_inv_nonneg (hS p hp).two_le
  set ψ : Finset ℕ → Finset ℕ × Finset ℕ := fun S => (S ∩ P, S \ P)
  have hinj : Set.InjOn ψ LF := by
    intro S _ T _ h
    simp only [ψ, Prod.mk.injEq] at h
    rw [← sdiff_union_inter S P, ← sdiff_union_inter T P, h.1, h.2]
  have himg : LF.image ψ ⊆ P.powerset ×ˢ LFq := by
    intro x hx
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hx
    simp only [LF, levelFamily, mem_filter, mem_powerset] at hS
    simp only [ψ, mem_product, mem_powerset, LFq, levelFamily, mem_filter]
    refine ⟨inter_subset_right, ?_, ?_⟩
    · intro p hp
      rw [mem_sdiff] at hp
      have h1 := hS.1 hp.1
      rw [mem_filter] at h1 ⊢
      exact ⟨h1.1, h1.2, fun hd => hp.2 (Nat.mem_primeFactors.mpr ⟨h1.2, hd, hq⟩)⟩
    · refine lt_of_le_of_lt ?_ hS.2
      exact prod_le_prod_of_subset_of_one_le' sdiff_subset
        fun p hp _ => (mem_filter.mp (hS.1 hp)).2.one_lt.le
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hLFq : ∀ S ∈ LFq, ∀ p ∈ S, p.Prime := fun S hS p hp => by
    simp only [LFq, levelFamily, mem_filter, mem_powerset] at hS
    exact (mem_filter.mp (hS.1 hp)).2.1
  calc selbergG g LF = ∑ S ∈ LF, H (ψ S).1 * H (ψ S).2 := by
        unfold selbergG; refine sum_congr rfl fun S _ => ?_
        simp only [H, ψ]; rw [prod_inter_mul_prod_sdiff]
    _ = ∑ x ∈ LF.image ψ, H x.1 * H x.2 :=
        (sum_image (f := fun x => H x.1 * H x.2) hinj).symm
    _ ≤ ∑ x ∈ P.powerset ×ˢ LFq, H x.1 * H x.2 :=
        sum_le_sum_of_subset_of_nonneg himg fun x hx _ =>
          mul_nonneg (hH _ fun p hp => hPp p (mem_powerset.mp (mem_product.mp hx).1 hp))
            (hH _ (hLFq _ (mem_product.mp hx).2))
    _ = (∑ A ∈ P.powerset, H A) * ∑ B ∈ LFq, H B := by rw [sum_product, sum_mul_sum]
    _ = _ := by rw [prod_one_add]; rfl

/-- `φ(q)/q = Π_{p ∣ q} (1 - 1/p)` and `Π_{p∣q} (1 + h(p)) · φ(q)/q = 1` for `h(p) = 1/(p-1)`. -/
theorem prod_one_add_hFun_mul_totient (q : ℕ) (hq : q ≠ 0) :
    (∏ p ∈ q.primeFactors, (1 + hFun (fun p : ℕ => 1 / (p : ℝ)) p)) * ((Nat.totient q : ℝ) / q) = 1 := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors q)
  push_cast at h
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [h, mul_div_cancel_left₀ _ hq0, ← prod_mul_distrib]
  refine prod_eq_one fun p hp => ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  unfold hFun
  field_simp
  ring

/-- **Selberg's `G` for primes not dividing `q`:** `(φ(q)/q) log z ≤ G_q`, where
`G_q = Σ_{S ⊆ {p < z prime, p ∤ q}, Π S < z} Π_{p∈S} 1/(p-1)`. -/
theorem totient_mul_log_le_selbergG (z q : ℕ) (hz : 1 ≤ z) (hq : q ≠ 0) :
    (Nat.totient q : ℝ) / q * Real.log z
      ≤ selbergG (fun p : ℕ => 1 / (p : ℝ))
          (levelFamily ((range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)) z) := by
  have hG := log_le_selbergG ((range z).filter Nat.Prime) (fun p hp => (mem_filter.mp hp).2) z hz
    (fun p hp hpz => mem_filter.mpr ⟨mem_range.mpr hpz, hp⟩)
  have hsplit := selbergG_le_prod_mul z q hq
  have hone := prod_one_add_hFun_mul_totient q hq
  have hr : 0 ≤ (Nat.totient q : ℝ) / q := by positivity
  calc (Nat.totient q : ℝ) / q * Real.log z
      ≤ (Nat.totient q : ℝ) / q * selbergG (fun p : ℕ => 1 / (p : ℝ))
          (levelFamily ((range z).filter Nat.Prime) z) := mul_le_mul_of_nonneg_left hG hr
    _ ≤ (Nat.totient q : ℝ) / q * ((∏ p ∈ q.primeFactors, (1 + hFun (fun p : ℕ => 1 / (p : ℝ)) p)) *
        selbergG (fun p : ℕ => 1 / (p : ℝ))
          (levelFamily ((range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)) z)) :=
        mul_le_mul_of_nonneg_left hsplit hr
    _ = _ := by rw [← mul_assoc, mul_comm ((Nat.totient q : ℝ) / q), hone, one_mul]

/-- **Selberg sieve on `r + q j`.** The number of `j < N` with `r + q j` a prime `≥ z` is at most
`N / G_q + z^4` (no coprimality assumption on `r, q` needed). -/
theorem sifted_count (r q N z : ℕ) (hq : 1 ≤ q) (hz : 2 ≤ z) :
    (((range N).filter (fun j => (r + q * j).Prime ∧ z ≤ r + q * j)).card : ℝ)
      ≤ N / selbergG (fun p : ℕ => 1 / (p : ℝ))
          (levelFamily ((range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)) z) + (z : ℝ) ^ 4 := by
  set Q := (range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)
  have hQ2 : ∀ p ∈ Q, 2 ≤ p := fun p hp => (mem_filter.mp hp).2.1.two_le
  have hQc : (Q : Set ℕ).Pairwise Nat.Coprime := fun p hp p' hp' hne =>
    (Nat.coprime_primes (mem_filter.mp hp).2.1 (mem_filter.mp hp').2.1).mpr hne
  set C : ℕ → ℕ → Prop := fun ℓ j => ℓ ∣ r + q * j
  have hper : ∀ ℓ n, C ℓ n ↔ C ℓ (n % ℓ) := by
    intro ℓ n
    simp only [C]
    have e : r + q * n = (r + q * (n % ℓ)) + ℓ * (q * (n / ℓ)) := by
      conv_lhs => rw [← Nat.mod_add_div n ℓ]
      ring
    rw [e]
    exact Nat.dvd_add_left (dvd_mul_right _ _)
  have hω : ∀ ℓ ∈ Q, omega C ℓ = 1 := by
    intro ℓ hℓ
    have hℓp := (mem_filter.mp hℓ).2.1
    have hcop : Nat.Coprime q ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓp).mpr (mem_filter.mp hℓ).2.2).symm
    have hP : ∀ n, ℓ ∣ n ↔ ℓ ∣ n % ℓ := fun n => (Nat.dvd_mod_iff (dvd_refl ℓ)).symm
    have := card_filter_range_shift (fun t => ℓ ∣ t) hℓp.pos hcop hP r
    unfold omega
    simp only [C]
    rw [this]
    have e : (range ℓ).filter (fun t => ℓ ∣ t) = {0} := by
      ext t
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; exact Nat.eq_zero_of_dvd_of_lt h2 h1
      · rintro rfl; exact ⟨hℓp.pos, dvd_zero ℓ⟩
    rw [e, card_singleton]
  have hω0 : ∀ p ∈ Q, 0 < omega C p := fun p hp => by rw [hω p hp]; omega
  have hω1 : ∀ p ∈ Q, omega C p < p := fun p hp => by rw [hω p hp]; have := hQ2 p hp; omega
  have key := selberg_residue_level N z hz Q hQ2 hQc C hper hω0 hω1
  have hG : selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z)
      = selbergG (fun p : ℕ => 1 / (p : ℝ)) (levelFamily Q z) :=
    selbergG_congr levelFamily_subset fun p hp => by rw [hω p hp]; simp
  rw [hG] at key
  refine le_trans ?_ key
  have hsub : (range N).filter (fun j => (r + q * j).Prime ∧ z ≤ r + q * j)
      ⊆ (range N).filter (fun n => ∀ p ∈ Q, ¬ C p n) := by
    intro j hj
    rw [mem_filter] at hj ⊢
    refine ⟨hj.1, fun ℓ hℓ hd => ?_⟩
    have hℓp := (mem_filter.mp hℓ).2.1
    have hℓz := mem_range.mp (mem_filter.mp hℓ).1
    rcases hj.2.1.eq_one_or_self_of_dvd ℓ hd with h | h
    · exact hℓp.one_lt.ne' h
    · omega
  have hcR : (((range N).filter (fun j => (r + q * j).Prime ∧ z ≤ r + q * j)).card : ℝ)
      ≤ (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  refine le_of_le_of_eq hcR ?_
  congr 2
  ext n; simp only [mem_filter]

/-- **Sieve form of Brun–Titchmarsh in progressions.** For `q ≥ 1`, `z ≥ 2` and any `a`,
`#{p ≤ x prime : p ≡ a (mod q)} ≤ z + (⌊x/q⌋ + 1) / ((φ(q)/q) log z) + z^4`. -/
theorem primes_AP_le_sieve (x q a z : ℕ) (hq : 1 ≤ q) (hz : 2 ≤ z) :
    (((range (x + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ)
      ≤ z + ((x / q : ℕ) + 1 : ℝ) / ((Nat.totient q : ℝ) / q * Real.log z) + (z : ℝ) ^ 4 := by
  set A := (range (x + 1)).filter (fun p => p.Prime ∧ p % q = a % q)
  set B := (range (x / q + 1)).filter
    (fun j => (a % q + q * j).Prime ∧ z ≤ a % q + q * j)
  have hsub : A ⊆ (range z).filter Nat.Prime ∪ B.image (fun j => a % q + q * j) := by
    intro p hp
    simp only [A, mem_filter, mem_range] at hp
    rw [mem_union]
    by_cases hpz : p < z
    · left; exact mem_filter.mpr ⟨mem_range.mpr hpz, hp.2.1⟩
    · right
      refine mem_image.mpr ⟨p / q, ?_, ?_⟩
      · have e : a % q + q * (p / q) = p := by rw [← hp.2.2]; exact Nat.mod_add_div p q
        simp only [B, mem_filter, mem_range, e]
        refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)), hp.2.1, by omega⟩
      · rw [← hp.2.2]; exact Nat.mod_add_div p q
  have hcard : (A.card : ℝ) ≤ z + B.card := by
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 : ((range z).filter Nat.Prime).card ≤ z := (card_filter_le _ _).trans (card_range z).le
    have h3 := card_image_le (s := B) (f := fun j => a % q + q * j)
    have : A.card ≤ z + B.card := by omega
    exact_mod_cast this
  have hB := sifted_count (a % q) q (x / q + 1) z hq hz
  have hGq := totient_mul_log_le_selbergG z q (by omega) (by omega)
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hpos : 0 < (Nat.totient q : ℝ) / q * Real.log z := by
    have : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  have hdiv : ((x / q + 1 : ℕ) : ℝ) / selbergG (fun p : ℕ => 1 / (p : ℝ))
        (levelFamily ((range z).filter (fun p => p.Prime ∧ ¬ p ∣ q)) z)
      ≤ ((x / q : ℕ) + 1 : ℝ) / ((Nat.totient q : ℝ) / q * Real.log z) := by
    push_cast
    exact div_le_div_of_nonneg_left (by positivity) hpos hGq
  linarith

/-! ## Choosing the level `z = ⌈t^{1/5}⌉` -/

theorem level_choice (t : ℝ) (ht : 1 < t) :
    2 ≤ ⌈t ^ (1 / 5 : ℝ)⌉₊ ∧ Real.log t / 5 ≤ Real.log ⌈t ^ (1 / 5 : ℝ)⌉₊ ∧
      (⌈t ^ (1 / 5 : ℝ)⌉₊ : ℝ) + (⌈t ^ (1 / 5 : ℝ)⌉₊ : ℝ) ^ 4 ≤ 160 * t / Real.log t := by
  set u := t ^ (1 / 5 : ℝ) with hu
  have hu1 : 1 < u := Real.one_lt_rpow ht (by norm_num)
  have hu5 : u ^ 5 = t := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hlogt : Real.log t = 5 * Real.log u := by
    rw [← hu5, Real.log_pow]; norm_num
  have hz2 : 1 < ⌈u⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hu1)
  have hzle : (⌈u⌉₊ : ℝ) ≤ 2 * u := by
    have := Nat.ceil_lt_add_one (show 0 ≤ u by linarith); linarith
  have hzge : u ≤ ⌈u⌉₊ := Nat.le_ceil u
  refine ⟨hz2, ?_, ?_⟩
  · rw [hlogt]
    have := Real.log_le_log (by linarith) hzge
    linarith
  · have hlpos : 0 < Real.log t := Real.log_pos ht
    have hlu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hz4 : (⌈u⌉₊ : ℝ) ^ 4 ≤ (2 * u) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hzle 4
    rw [le_div_iff₀ hlpos]
    have hu4 : 1 ≤ u ^ 3 := one_le_pow₀ hu1.le
    have h1 : (⌈u⌉₊ : ℝ) + (⌈u⌉₊ : ℝ) ^ 4 ≤ 32 * u ^ 4 := by nlinarith
    have h2 : Real.log t ≤ 5 * u := by linarith
    have h3 : 0 ≤ (⌈u⌉₊ : ℝ) + (⌈u⌉₊ : ℝ) ^ 4 := by positivity
    calc ((⌈u⌉₊ : ℝ) + (⌈u⌉₊ : ℝ) ^ 4) * Real.log t ≤ (32 * u ^ 4) * (5 * u) :=
          mul_le_mul h1 h2 hlpos.le (by positivity)
      _ = 160 * u ^ 5 := by ring
      _ = 160 * t := by rw [hu5]

/-- **Brun–Titchmarsh in arithmetic progressions.** For `1 ≤ q < x` and any `a`,
`#{p ≤ x prime : p ≡ a (mod q)} ≤ 170 x / (φ(q) log(x/q))`. -/
theorem brun_titchmarsh_AP (x q a : ℕ) (hq : 1 ≤ q) (hqx : q < x) :
    (((range (x + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ)
      ≤ 170 * x / (Nat.totient q * Real.log ((x : ℝ) / q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqxR : (q : ℝ) < x := by exact_mod_cast hqx
  set t : ℝ := (x : ℝ) / q with ht
  have ht1 : 1 < t := by rw [ht, lt_div_iff₀ hq0]; linarith
  obtain ⟨hz2, hlz, herr⟩ := level_choice t ht1
  set z := ⌈t ^ (1 / 5 : ℝ)⌉₊
  have h := primes_AP_le_sieve x q a z hq hz2
  have hL : 0 < Real.log t := Real.log_pos ht1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hnum : ((x / q : ℕ) + 1 : ℝ) ≤ 2 * t := by
    have : ((x / q : ℕ) : ℝ) ≤ t := Nat.cast_div_le
    linarith
  have hden : (Nat.totient q : ℝ) / q * (Real.log t / 5)
      ≤ (Nat.totient q : ℝ) / q * Real.log z :=
    mul_le_mul_of_nonneg_left hlz (by positivity)
  have hmain : ((x / q : ℕ) + 1 : ℝ) / ((Nat.totient q : ℝ) / q * Real.log z)
      ≤ 10 * x / (Nat.totient q * Real.log t) := by
    calc ((x / q : ℕ) + 1 : ℝ) / ((Nat.totient q : ℝ) / q * Real.log z)
        ≤ (2 * t) / ((Nat.totient q : ℝ) / q * (Real.log t / 5)) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 10 * x / (Nat.totient q * Real.log t) := by rw [ht]; field_simp; ring
  have herr' : 160 * t / Real.log t ≤ 160 * x / (Nat.totient q * Real.log t) := by
    have e : 160 * t / Real.log t = 160 * x / (q * Real.log t) := by rw [ht]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hφq hL.le)
  have e : 170 * (x : ℝ) / (Nat.totient q * Real.log t)
      = 10 * x / (Nat.totient q * Real.log t) + 160 * x / (Nat.totient q * Real.log t) := by ring
  linarith

end HilbertDB.BrunTitchmarsh

end

section MertensCopy
-- tags: Mertens second theorem, sum of prime reciprocals, Σ 1/p ≤ log log n + C, Abel summation, summation by parts over primes, log log, explicit constants
-- summary: Σ_{p≤n} 1/p ≤ log log n + 3 − log log 2 ≤ log log n + 4 (n ≥ 2), via the discrete Abel invariant Σ_{p≤n} 1/p − T(n)/log n ≤ log log n − log log 2 + log 4 (1/log 2 − 1/log n), T(n) = Σ_{p≤n} log p/p ≤ log n + log 4 (self-contained copy of the Mertens-first upper half); Σ over primesLE (n+1) = Σ over primesLE n + [n+1 prime] f(n+1)
-- use-when: upper bounds on Σ_{p≤x} 1/p or ∏_{p≤x}(1+1/p), counting integers with many prime factors (Hardy–Ramanujan / Turán-type), Erdős-style estimates needing Σ 1/p = log log x + O(1); pair with PrimeReciprocalLower (log log(n+1) − 1 ≤ Σ_{p≤n} 1/p) for a two-sided bound
-- pattern: induction on n with F(n) = Σ 1/p − T(n)/log n, F(n+1) = F(n) + T(n)(1/log n − 1/log(n+1)); log n·(1/log n − 1/log(n+1)) ≤ log log(n+1) − log log n from log y ≥ 1 − 1/y
-- source: own (textbook Mertens 1874 via summation by parts), 2026-11-27

open Finset Real Nat

namespace HilbertDB.MertensSecond
/-- `log m = Σ_{p ∈ S} v_p(m) log p` for any finite set `S` containing the prime factors of `m`. -/
theorem log_eq_sum_factorization {m : ℕ} (hm : m ≠ 0) {S : Finset ℕ} (hS : m.primeFactors ⊆ S) :
    Real.log m = ∑ p ∈ S, (m.factorization p : ℝ) * Real.log p := by
  have key : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ (m.factorization p) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.prod_primeFactors_pow_factorization hm)
  rw [key, Real.log_prod (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity)]
  simp_rw [Real.log_pow]
  apply Finset.sum_subset hS
  intro p _ hp
  have : m.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
  simp [this]

lemma primeFactors_factorial_subset (n : ℕ) : (n !).primeFactors ⊆ primesLE n := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [mem_primesLE]
  exact ⟨(hpp.dvd_factorial).1 (Nat.dvd_of_mem_primeFactors hp), hpp⟩

/-- `log n! = Σ_{p ≤ n} v_p(n!) log p`. -/
theorem log_factorial_eq_sum (n : ℕ) :
    Real.log (n ! : ℕ) = ∑ p ∈ primesLE n, ((n !).factorization p : ℝ) * Real.log p :=
  log_eq_sum_factorization (Nat.factorial_ne_zero n) (primeFactors_factorial_subset n)

/-- `⌊n/p⌋ ≤ v_p(n!)` (the first Legendre term). -/
lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n !).factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p n + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Ico 1 (Nat.log p n + 2) := by simp
  have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

lemma real_div_sub_one_le {n p : ℕ} (hp : 0 < p) : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n p
  have h2 := Nat.mod_lt n hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h3 : (n : ℝ) < p * ((n / p : ℕ) : ℝ) + p := by
    have : n < p * (n / p) + p := by omega
    exact_mod_cast this
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

/-- `log n! ≤ n log n`. -/
lemma log_factorial_le (n : ℕ) : Real.log (n ! : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
  exact_mod_cast Nat.factorial_le_pow n

/-- **Mertens' first theorem, upper half** (explicit): `Σ_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem sum_log_div_le (n : ℕ) :
    ∑ p ∈ primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primesLE_zero]; exact Real.log_nonneg (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- n Σ log p/p - θ(n) ≤ Σ ⌊n/p⌋ log p ≤ log n!
  have h1 : ∑ p ∈ primesLE n, ((n : ℝ) / p - 1) * Real.log p ≤ Real.log (n ! : ℕ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (mem_primesLE.1 hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hl
    calc (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := real_div_sub_one_le hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp n
  have htheta : ∑ p ∈ primesLE n, Real.log p ≤ Real.log 4 * n := by
    have := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) hn'.le
    rwa [Chebyshev.theta_eq_sum_primesLE_log] at this
  have hsplit : ∑ p ∈ primesLE n, ((n : ℝ) / p - 1) * Real.log p =
      n * ∑ p ∈ primesLE n, Real.log p / p - ∑ p ∈ primesLE n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  have h2 := log_factorial_le n
  have : (n : ℝ) * ∑ p ∈ primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hn'

/-- Adding the next integer to `primesLE`: the sum gains `f (n+1)` exactly when `n+1` is prime. -/
lemma sum_primesLE_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ primesLE (n + 1), f p =
      ∑ p ∈ primesLE n, f p + (if (n + 1).Prime then f (n + 1) else 0) := by
  rw [primesLE_eq_filter_range, primesLE_eq_filter_range, Finset.range_add_one, filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp), add_comm]
  · simp

lemma primesLE_two : primesLE 2 = {2} := by
  ext p; rw [mem_primesLE, mem_singleton]; constructor
  · rintro ⟨h, hp⟩
    have := hp.two_le
    omega
  · rintro rfl; exact ⟨le_rfl, Nat.prime_two⟩

/-- `1 - a/b ≤ log b - log a` for `0 < a, b` (from `log y ≥ 1 - 1/y`). -/
lemma one_sub_div_le_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - a / b ≤ Real.log b - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (show 0 < a / b by positivity)
  rw [Real.log_div ha.ne' hb.ne'] at h
  linarith

/-- The Abel-summation invariant: for `n ≥ 2`,
`Σ_{p≤n} 1/p - T(n)/log n ≤ log log n - log log 2 + log 4 (1/log 2 - 1/log n)`,
where `T(n) = Σ_{p≤n} log p / p`. -/
theorem abel_invariant (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ primesLE n, (1 : ℝ) / p - (∑ p ∈ primesLE n, Real.log p / p) / Real.log n ≤
      Real.log (Real.log n) - Real.log (Real.log 2) +
        Real.log 4 * (1 / Real.log 2 - 1 / Real.log n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [primesLE_two]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    simp only [sum_singleton, Nat.cast_ofNat]
    field_simp
    ring_nf
    rfl
  | succ n hn ih =>
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    have hl1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hmono : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    set T := ∑ p ∈ primesLE n, Real.log p / p with hT
    set R := ∑ p ∈ primesLE n, (1 : ℝ) / p with hR
    have hT1 := sum_primesLE_succ (fun p => Real.log p / p) n
    have hR1 := sum_primesLE_succ (fun p => (1 : ℝ) / p) n
    -- the new invariant equals the old one plus `T (1/log n - 1/log(n+1))`
    have key : ∑ p ∈ primesLE (n + 1), (1 : ℝ) / p -
        (∑ p ∈ primesLE (n + 1), Real.log p / p) / Real.log ((n + 1 : ℕ) : ℝ) =
        (R - T / Real.log n) + T * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
      rw [hT1, hR1]
      push_cast
      split_ifs
      · field_simp
        ring
      · field_simp
        ring
    rw [key]
    have hTle : T ≤ Real.log n + Real.log 4 := sum_log_div_le n
    have hd : 0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hl hmono
    have h1 : T * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
        (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hTle hd
    have h2 : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
        Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
      have := one_sub_div_le_log_sub hl hl1
      have e : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
          1 - Real.log n / Real.log ((n : ℝ) + 1) := by field_simp
      linarith
    push_cast
    nlinarith

/-- **Mertens' second theorem, explicit upper bound**:
`Σ_{p ≤ n} 1/p ≤ log log n + 3 - log log 2` for `n ≥ 2`. -/
theorem sum_inv_primes_le' (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ primesLE n, (1 : ℝ) / p ≤ Real.log (Real.log n) + 3 - Real.log (Real.log 2) := by
  have h := abel_invariant n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT := sum_log_div_le n
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hTdiv : (∑ p ∈ primesLE n, Real.log p / p) / Real.log n ≤ 1 + Real.log 4 / Real.log n := by
    rw [div_le_iff₀ hl]
    have : (1 + Real.log 4 / Real.log n) * Real.log n = Real.log n + Real.log 4 := by
      field_simp
    linarith
  have e : Real.log 4 * (1 / Real.log 2 - 1 / Real.log n) = 2 - Real.log 4 / Real.log n := by
    rw [h4]; field_simp
  linarith

/-- **Mertens' second theorem, explicit upper bound** (rounded): `Σ_{p ≤ n} 1/p ≤ log log n + 4`
for `n ≥ 2`. -/
theorem sum_inv_primes_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ primesLE n, (1 : ℝ) / p ≤ Real.log (Real.log n) + 4 := by
  have h := sum_inv_primes_le' n hn
  -- `-log log 2 = log (1/log 2) ≤ 1/log 2 - 1 < 1`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / Real.log 2 by positivity)
  rw [Real.log_div (by norm_num) hl2.ne', Real.log_one] at h1
  have h2 : 1 / Real.log 2 < 2 := by
    rw [div_lt_iff₀ hl2]; have := Real.log_two_gt_d9; linarith
  linarith

end HilbertDB.MertensSecond

end MertensCopy
section E694Main

open Finset
open scoped Classical

namespace E694

/-- Primes in `(k, X]` with `d ∣ p - 1`. -/
noncomputable def N (k X d : ℕ) : ℕ := ((Ioc k X).filter fun p => p.Prime ∧ d ∣ p - 1).card

/-- Brun–Titchmarsh at level `d ≤ √X`. -/
theorem N_le (k X d : ℕ) (hd : 1 ≤ d) (hX : 2 ≤ X) (hdX : d ^ 2 ≤ X) :
    (N k X d : ℝ) ≤ 340 * X / (Nat.totient d * Real.log X) := by
  have hdlt : d < X := by
    by_contra h
    push Not at h
    have : X ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left h 2
    nlinarith
  have bt := HilbertDB.BrunTitchmarsh.brun_titchmarsh_AP X d 1 hd hdlt
  have sub : (Ioc k X).filter (fun p => p.Prime ∧ d ∣ p - 1) ⊆
      (range (X + 1)).filter (fun p => p.Prime ∧ p % d = 1 % d) := by
    intro p hp
    simp only [mem_filter, mem_Ioc, mem_range] at hp ⊢
    obtain ⟨⟨_, hpX⟩, pp, dv⟩ := hp
    exact ⟨by omega, pp, Nat.ModEq.symm ((Nat.modEq_iff_dvd' pp.one_le).mpr dv)⟩
  have c1 : (N k X d : ℝ) ≤ (((range (X + 1)).filter (fun p => p.Prime ∧ p % d = 1 % d)).card : ℝ) := by
    exact_mod_cast card_le_card sub
  have hXr : (0 : ℝ) < X := by positivity
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log X / 2 ≤ Real.log ((X : ℝ) / d) := by
    have h1 : (X : ℝ) ≤ ((X : ℝ) / d) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have : ((d ^ 2 : ℕ) : ℝ) ≤ X := by exact_mod_cast hdX
      push_cast at this
      nlinarith
    have := Real.log_le_log hXr h1
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  calc (N k X d : ℝ) ≤ 170 * X / (Nat.totient d * Real.log ((X : ℝ) / d)) := c1.trans bt
    _ ≤ 170 * X / (Nat.totient d * (Real.log X / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hlog hφ.le
    _ = 340 * X / (Nat.totient d * Real.log X) := by field_simp; ring

/-- Fewer than `j` prime factors `q` of `n < X` have `q ^ j > X`. -/
theorem large_primes (n X j : ℕ) (hn : 1 ≤ n) (hnX : n < X) (hj : 1 ≤ j) :
    (n.primeFactors.filter fun q => X < q ^ j).card < j := by
  set F := n.primeFactors.filter fun q => X < q ^ j
  have dvd : ∏ q ∈ F, q ∣ n := Finset.prod_primes_dvd n
    (fun q hq => (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1).prime)
    (fun q hq => Nat.dvd_of_mem_primeFactors (mem_filter.mp hq).1)
  have le : ∏ q ∈ F, q ≤ n := Nat.le_of_dvd hn dvd
  have low : (X + 1) ^ F.card ≤ (∏ q ∈ F, q) ^ j := by
    rw [← Finset.prod_pow, ← Finset.prod_const]
    exact Finset.prod_le_prod' (fun q hq => Nat.succ_le_of_lt (mem_filter.mp hq).2)
  have up : (∏ q ∈ F, q) ^ j < (X + 1) ^ j := Nat.pow_lt_pow_left (by omega) (by omega)
  exact (Nat.pow_lt_pow_iff_right (by omega)).mp (lt_of_le_of_lt low up)

/-- Divisor bound off the square set. -/
theorem divisors_le (n X R E : ℕ) (hn : 1 ≤ n) (hnX : n < X) (hE : 4 ≤ E)
    (small : ∀ q, q.Prime → q ≤ R → ¬ q ^ E ∣ n)
    (mid : ∀ q, q.Prime → R < q → q ^ 4 ≤ X → ¬ q ^ 2 ∣ n) :
    n.divisors.card ≤ 2 ^ n.primeFactors.card * (E ^ (R + 1) * 8) := by
  rw [Nat.card_divisors (by omega)]
  have each : ∀ q ∈ n.primeFactors, n.factorization q + 1 ≤
      2 * ((if q ≤ R then E else 1) * (if X < q ^ 4 then 2 else 1)) := by
    intro q hq
    have qp := Nat.prime_of_mem_primeFactors hq
    have q1 : 1 < q := qp.one_lt
    have pdv : q ^ n.factorization q ∣ n := Nat.ordProj_dvd n q
    by_cases hR : q ≤ R
    · have : n.factorization q < E := by
        by_contra h
        push Not at h
        exact small q qp hR ((Nat.pow_dvd_pow q h).trans pdv)
      rw [if_pos hR]
      split_ifs <;> omega
    · rw [if_neg hR]
      by_cases hX : X < q ^ 4
      · rw [if_pos hX]
        have : q ^ n.factorization q < q ^ 4 := lt_of_le_of_lt (Nat.le_of_dvd hn pdv) (by omega)
        have := (Nat.pow_lt_pow_iff_right q1).mp this
        omega
      · rw [if_neg hX]
        have : n.factorization q < 2 := by
          by_contra h
          push Not at h
          exact mid q qp (by omega) (by omega) ((Nat.pow_dvd_pow q h).trans pdv)
        omega
  calc ∏ q ∈ n.primeFactors, (n.factorization q + 1)
      ≤ ∏ q ∈ n.primeFactors, 2 * ((if q ≤ R then E else 1) * (if X < q ^ 4 then 2 else 1)) :=
        Finset.prod_le_prod' each
    _ = 2 ^ n.primeFactors.card * ((∏ q ∈ n.primeFactors, (if q ≤ R then E else 1)) *
          ∏ q ∈ n.primeFactors, (if X < q ^ 4 then 2 else 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ 2 ^ n.primeFactors.card * (E ^ (R + 1) * 8) := by
        apply Nat.mul_le_mul_left
        rw [Finset.prod_ite, Finset.prod_ite]
        simp only [Finset.prod_const, one_pow, mul_one]
        apply Nat.mul_le_mul
        · apply Nat.pow_le_pow_right (by omega)
          have : n.primeFactors.filter (fun q => q ≤ R) ⊆ range (R + 1) := by
            intro q hq
            simp only [mem_filter, mem_range] at hq ⊢
            omega
          simpa using card_le_card this
        · have := large_primes n X 4 hn hnX (by norm_num)
          calc 2 ^ (n.primeFactors.filter fun q => X < q ^ 4).card ≤ 2 ^ 3 :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 8 := by norm_num

/-- `x^(n+1) + (n+1) y x^n ≤ (x+y)^(n+1)`. -/
theorem binom_low (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∀ n : ℕ, x ^ (n + 1) + (n + 1) * y * x ^ n ≤ (x + y) ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 ≤ x ^ n := pow_nonneg hx n
    have e1 : (x + y) ^ (n + 1 + 1) = (x + y) * (x + y) ^ (n + 1) := by ring
    rw [e1]
    have h2 : (x + y) * (x ^ (n + 1) + (n + 1) * y * x ^ n) ≤ (x + y) * (x + y) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have h3 : x ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * y * x ^ (n + 1)
        ≤ (x + y) * (x ^ (n + 1) + (n + 1) * y * x ^ n) := by
      have : 0 ≤ (n + 1 : ℝ) * y * y * x ^ n := by positivity
      have id : (x + y) * (x ^ (n + 1) + (n + 1) * y * x ^ n) = x ^ (n + 1 + 1)
          + (n + 1 + 1) * y * x ^ (n + 1) + (n + 1) * y * y * x ^ n := by ring
      push_cast
      linarith [this, id]
    push_cast at h3 ⊢
    linarith

/-- `m! e_m(w) ≤ (Σ w)^m`. -/
theorem esymm_le (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q) (P : Finset ℕ) : ∀ m : ℕ,
    (m.factorial : ℝ) * ∑ S ∈ P.powersetCard m, ∏ q ∈ S, w q ≤ (∑ q ∈ P, w q) ^ m := by
  induction P using Finset.induction_on with
  | empty =>
    intro m
    cases m with
    | zero => simp
    | succ m => rw [Finset.powersetCard_eq_empty.mpr (by simp)]; simp
  | insert a s ha ih =>
    intro m
    cases m with
    | zero => simp
    | succ m =>
      have inj : Set.InjOn (insert a) (s.powersetCard m : Set (Finset ℕ)) := by
        intro S1 h1 S2 h2 h
        have n1 : a ∉ S1 := fun h' => ha ((mem_powersetCard.mp (Finset.mem_coe.mp h1)).1 h')
        have n2 : a ∉ S2 := fun h' => ha ((mem_powersetCard.mp (Finset.mem_coe.mp h2)).1 h')
        rw [← Finset.erase_insert n1, ← Finset.erase_insert n2, h]
      have disj : Disjoint (s.powersetCard (m + 1)) ((s.powersetCard m).image (insert a)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        obtain ⟨S, _, rfl⟩ := mem_image.mp hT'
        exact ha ((mem_powersetCard.mp hT).1 (mem_insert_self a S))
      rw [Finset.powersetCard_succ_insert ha, Finset.sum_union disj, Finset.sum_image inj,
        Finset.sum_insert ha]
      · have hsum : ∑ S ∈ s.powersetCard m, ∏ q ∈ insert a S, w q
            = w a * ∑ S ∈ s.powersetCard m, ∏ q ∈ S, w q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          have : a ∉ S := fun h => ha ((mem_powersetCard.mp hS).1 h)
          rw [Finset.prod_insert this]
        rw [hsum]
        have i1 := ih (m + 1)
        have i2 := ih m
        set x := ∑ q ∈ s, w q
        have hx : 0 ≤ x := Finset.sum_nonneg fun q _ => hw q
        have bl := binom_low x (w a) hx (hw a) m
        have fe : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
          push_cast [Nat.factorial_succ]; ring
        have hwa := hw a
        have step : ((m + 1).factorial : ℝ) * (w a * ∑ S ∈ s.powersetCard m, ∏ q ∈ S, w q)
            ≤ (m + 1) * w a * x ^ m := by
          rw [fe]
          have := mul_le_mul_of_nonneg_left i2 (show 0 ≤ (m + 1 : ℝ) * w a by positivity)
          nlinarith [this]
        rw [add_comm (w a) x]
        nlinarith [i1, step, bl]

theorem totient_prod_primes (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    Nat.totient (∏ q ∈ S, q) = ∏ q ∈ S, (q - 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have pa := hS a (mem_insert_self a s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    rw [prod_insert ha, prod_insert ha, Nat.totient_mul, Nat.totient_prime pa, ih hs]
    exact Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes pa (hs q hq)).mpr (fun e => ha (e ▸ hq))

theorem tele_eq (a : ℕ) (ha : 1 ≤ a) : ∀ b, a ≤ b →
    ∑ n ∈ Ioc a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / a - 1 / b := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih]
    have : (1 : ℝ) ≤ b := by exact_mod_cast (le_trans ha hab)
    push_cast
    rw [show ((b : ℝ) + 1 - 1) = b by ring]
    field_simp
    ring

theorem tele_le (a b : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / a := by
  rcases le_or_gt a b with h | h
  · rw [tele_eq a ha b h]
    have : (0 : ℝ) ≤ 1 / b := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty_of_le (by omega)]
    simp

/-- The weight `1/(q-1)`. -/
noncomputable def w (q : ℕ) : ℝ := 1 / ((q - 1 : ℕ) : ℝ)

theorem w_nonneg (q : ℕ) : 0 ≤ w q := by unfold w; positivity

/-- Mertens for the weight `1/(q-1)`. -/
theorem sum_w_le (X : ℕ) (hX : 2 ≤ X) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE X) :
    ∑ q ∈ P, w q ≤ Real.log (Real.log X) + 5 := by
  have m2 := HilbertDB.MertensSecond.sum_inv_primes_le X hX
  have split : ∀ q ∈ Nat.primesLE X, w q = 1 / (q : ℝ) + 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
    intro q hq
    have q2 : 2 ≤ q := (Nat.mem_primesLE.mp hq).2.two_le
    have : (2 : ℝ) ≤ q := by exact_mod_cast q2
    unfold w
    rw [Nat.cast_sub (by omega)]
    push_cast
    have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have tail : ∑ q ∈ Nat.primesLE X, 1 / ((q : ℝ) * ((q : ℝ) - 1)) ≤ 1 := by
    have sub : Nat.primesLE X ⊆ Ioc 1 X := by
      intro q hq
      have := Nat.mem_primesLE.mp hq
      exact mem_Ioc.mpr ⟨this.2.one_lt, this.1⟩
    calc ∑ q ∈ Nat.primesLE X, 1 / ((q : ℝ) * ((q : ℝ) - 1))
        ≤ ∑ q ∈ Ioc 1 X, 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
          apply sum_le_sum_of_subset_of_nonneg sub
          intro n hn _
          have : (1 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
          have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          positivity
      _ ≤ 1 / (1 : ℕ) := tele_le 1 X le_rfl
      _ = 1 := by simp
  calc ∑ q ∈ P, w q ≤ ∑ q ∈ Nat.primesLE X, w q :=
        sum_le_sum_of_subset_of_nonneg hP (fun q _ _ => w_nonneg q)
    _ = ∑ q ∈ Nat.primesLE X, 1 / (q : ℝ) + ∑ q ∈ Nat.primesLE X, 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
        rw [← sum_add_distrib]; exact sum_congr rfl split
    _ ≤ Real.log (Real.log X) + 5 := by linarith

/-- Double counting with `m`-subsets. -/
theorem moment_count (k X m T : ℕ) (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) :
    T.choose m * ((Ioc k X).filter fun p => p.Prime ∧ T ≤ (P.filter (· ∣ p - 1)).card).card
      ≤ ∑ S ∈ P.powersetCard m, N k X (∏ q ∈ S, q) := by
  set A := (Ioc k X).filter fun p => p.Prime
  set B := (Ioc k X).filter fun p => p.Prime ∧ T ≤ (P.filter (· ∣ p - 1)).card
  let g : ℕ → Finset ℕ → Prop := fun p S => ∀ q ∈ S, q ∣ p - 1
  have each : ∀ p ∈ B, T.choose m ≤ ((P.powersetCard m).filter (g p)).card := by
    intro p hp
    have hT := (mem_filter.mp hp).2.2
    calc T.choose m ≤ (P.filter (· ∣ p - 1)).card.choose m := Nat.choose_le_choose m hT
      _ = ((P.filter (· ∣ p - 1)).powersetCard m).card := (card_powersetCard _ _).symm
      _ ≤ ((P.powersetCard m).filter (g p)).card := by
          apply card_le_card
          intro S hS
          obtain ⟨hsub, hc⟩ := mem_powersetCard.mp hS
          refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub.trans (filter_subset _ _), hc⟩, ?_⟩
          intro q hq
          exact (mem_filter.mp (hsub hq)).2
  have BA : B ⊆ A := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨h1, h2⟩
  calc T.choose m * B.card = ∑ p ∈ B, T.choose m := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ B, ((P.powersetCard m).filter (g p)).card := sum_le_sum each
    _ ≤ ∑ p ∈ A, ((P.powersetCard m).filter (g p)).card :=
        sum_le_sum_of_subset_of_nonneg BA (fun _ _ _ => Nat.zero_le _)
    _ = ∑ S ∈ P.powersetCard m, (A.filter (fun p => g p S)).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ S ∈ P.powersetCard m, N k X (∏ q ∈ S, q) := by
        apply sum_le_sum
        intro S hS
        apply card_le_card
        intro p hp
        obtain ⟨hpA, hg⟩ := mem_filter.mp hp
        obtain ⟨hI, pp⟩ := mem_filter.mp hpA
        refine mem_filter.mpr ⟨hI, pp, ?_⟩
        exact Finset.prod_primes_dvd (p - 1)
          (fun q hq => (hP q ((mem_powersetCard.mp hS).1 hq)).prime) hg

/-- Count of the square set. -/
theorem squares_bound (k X R E : ℕ) (hX : 2 ≤ X) (hR : 1 ≤ R) (hE : 4 ≤ E)
    (hRE : R ^ (2 * E) ≤ X) :
    (∑ q ∈ (range (R + 1)).filter Nat.Prime, (N k X (q ^ E) : ℝ))
      + ∑ q ∈ (Ioc R X).filter (fun q => q.Prime ∧ q ^ 4 ≤ X), (N k X (q ^ 2) : ℝ)
      ≤ 340 * X / Real.log X * ((R + 1) / 2 ^ (E - 1) + 1 / R) := by
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  set K := 340 * (X : ℝ) / Real.log X with hK
  have hK0 : 0 ≤ K := by positivity
  have s1 : ∀ q ∈ (range (R + 1)).filter Nat.Prime, (N k X (q ^ E) : ℝ) ≤ K / 2 ^ (E - 1) := by
    intro q hq
    obtain ⟨hqr, qp⟩ := mem_filter.mp hq
    have qR : q ≤ R := by have := mem_range.mp hqr; omega
    have hsq : (q ^ E) ^ 2 ≤ X := by
      calc (q ^ E) ^ 2 = q ^ (2 * E) := by ring
        _ ≤ R ^ (2 * E) := Nat.pow_le_pow_left qR _
        _ ≤ X := hRE
    have b := N_le k X (q ^ E) (Nat.one_le_pow _ _ qp.pos) hX hsq
    have tot : (2 : ℝ) ^ (E - 1) ≤ Nat.totient (q ^ E) := by
      rw [Nat.totient_prime_pow qp (by omega)]
      have : 2 ^ (E - 1) ≤ q ^ (E - 1) * (q - 1) := by
        have := qp.two_le
        calc 2 ^ (E - 1) ≤ q ^ (E - 1) := Nat.pow_le_pow_left this _
          _ ≤ q ^ (E - 1) * (q - 1) := Nat.le_mul_of_pos_right _ (by omega)
      exact_mod_cast this
    calc (N k X (q ^ E) : ℝ) ≤ 340 * X / (Nat.totient (q ^ E) * Real.log X) := b
      _ ≤ 340 * X / (2 ^ (E - 1) * Real.log X) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right tot hL.le
      _ = K / 2 ^ (E - 1) := by rw [hK]; field_simp
  have s2 : ∀ q ∈ (Ioc R X).filter (fun q => q.Prime ∧ q ^ 4 ≤ X),
      (N k X (q ^ 2) : ℝ) ≤ K * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
    intro q hq
    obtain ⟨_, qp, q4⟩ := mem_filter.mp hq
    have hsq : (q ^ 2) ^ 2 ≤ X := by rw [← pow_mul]; exact q4
    have b := N_le k X (q ^ 2) (Nat.one_le_pow _ _ qp.pos) hX hsq
    have tot : (Nat.totient (q ^ 2) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
      rw [Nat.totient_prime_pow qp (by norm_num)]
      have := qp.one_le
      push_cast [Nat.cast_sub this]
      ring
    rw [tot] at b
    have q2 : (2 : ℝ) ≤ q := by exact_mod_cast qp.two_le
    have : 0 < (q : ℝ) * ((q : ℝ) - 1) := by nlinarith
    calc (N k X (q ^ 2) : ℝ) ≤ 340 * X / ((q : ℝ) * ((q : ℝ) - 1) * Real.log X) := b
      _ = K * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by rw [hK]; field_simp
  have c1 : ∑ q ∈ (range (R + 1)).filter Nat.Prime, (N k X (q ^ E) : ℝ)
      ≤ (R + 1) * (K / 2 ^ (E - 1)) := by
    calc _ ≤ ∑ q ∈ (range (R + 1)).filter Nat.Prime, K / 2 ^ (E - 1) := sum_le_sum s1
      _ = ((range (R + 1)).filter Nat.Prime).card * (K / 2 ^ (E - 1)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (R + 1) * (K / 2 ^ (E - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := card_le_card (filter_subset Nat.Prime (range (R + 1)))
          rw [card_range] at this
          exact_mod_cast this
  have c2 : ∑ q ∈ (Ioc R X).filter (fun q => q.Prime ∧ q ^ 4 ≤ X), (N k X (q ^ 2) : ℝ)
      ≤ K * (1 / R) := by
    calc _ ≤ ∑ q ∈ (Ioc R X).filter (fun q => q.Prime ∧ q ^ 4 ≤ X),
          K * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := sum_le_sum s2
      _ ≤ ∑ q ∈ Ioc R X, K * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro n hn _
          have : (1 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt hR (mem_Ioc.mp hn).1)
          have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          positivity
      _ = K * ∑ q ∈ Ioc R X, 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by rw [mul_sum]
      _ ≤ K * (1 / R) := mul_le_mul_of_nonneg_left (tele_le R X hR) hK0
  have e : K * ((R + 1) / 2 ^ (E - 1) + 1 / R) = (R + 1) * (K / 2 ^ (E - 1)) + K * (1 / R) := by
    ring
  linarith

/-- The `m`-moment bound on the number of `p` with many small prime factors of `p - 1`. -/
theorem moment_bound (k X m T : ℕ) (hX : 2 ≤ X) (hm : 1 ≤ m) (P : Finset ℕ)
    (hP : P ⊆ (Nat.primesLE X).filter (fun q => q ^ (2 * m) ≤ X)) :
    ((T.choose m * ((Ioc k X).filter fun p => p.Prime ∧ T ≤ (P.filter (· ∣ p - 1)).card).card : ℕ) : ℝ)
        * m.factorial
      ≤ 340 * X / Real.log X * (∑ q ∈ P, w q) ^ m := by
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hPp : ∀ q ∈ P, q.Prime := fun q hq => (Nat.mem_primesLE.mp (mem_filter.mp (hP hq)).1).2
  have mc := moment_count k X m T P hPp
  have each : ∀ S ∈ P.powersetCard m, (N k X (∏ q ∈ S, q) : ℝ)
      ≤ 340 * X / Real.log X * ∏ q ∈ S, w q := by
    intro S hS
    obtain ⟨hsub, hc⟩ := mem_powersetCard.mp hS
    have hSp : ∀ q ∈ S, q.Prime := fun q hq => hPp q (hsub hq)
    have pos : 1 ≤ ∏ q ∈ S, q := Finset.prod_pos (fun q hq => (hSp q hq).pos)
    have sq : (∏ q ∈ S, q) ^ 2 ≤ X := by
      have big : ((∏ q ∈ S, q) ^ 2) ^ m ≤ X ^ m := by
        calc ((∏ q ∈ S, q) ^ 2) ^ m = ∏ q ∈ S, q ^ (2 * m) := by
              rw [← pow_mul, Finset.prod_pow]
          _ ≤ ∏ q ∈ S, X := Finset.prod_le_prod' (fun q hq => (mem_filter.mp (hP (hsub hq))).2)
          _ = X ^ m := by rw [Finset.prod_const, hc]
      exact (Nat.pow_le_pow_iff_left (by omega)).mp big
    have b := N_le k X _ pos hX sq
    rw [totient_prod_primes S hSp, Nat.cast_prod] at b
    have hpw : ∏ q ∈ S, w q = 1 / ∏ q ∈ S, ((q - 1 : ℕ) : ℝ) := by
      unfold w
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    have hpos : 0 < ∏ q ∈ S, ((q - 1 : ℕ) : ℝ) := Finset.prod_pos (fun q hq => by
      have := (hSp q hq).two_le
      have : 1 ≤ q - 1 := by omega
      exact_mod_cast this)
    rw [hpw]
    calc (N k X (∏ q ∈ S, q) : ℝ) ≤ _ := b
      _ = 340 * X / Real.log X * (1 / ∏ q ∈ S, ((q - 1 : ℕ) : ℝ)) := by field_simp
  have es := esymm_le w w_nonneg P m
  have sumb : (∑ S ∈ P.powersetCard m, N k X (∏ q ∈ S, q) : ℝ)
      ≤ 340 * X / Real.log X * ∑ S ∈ P.powersetCard m, ∏ q ∈ S, w q := by
    rw [mul_sum]; exact sum_le_sum each
  have mcR : ((T.choose m * ((Ioc k X).filter fun p => p.Prime ∧
      T ≤ (P.filter (· ∣ p - 1)).card).card : ℕ) : ℝ)
      ≤ (∑ S ∈ P.powersetCard m, N k X (∏ q ∈ S, q) : ℝ) := by exact_mod_cast mc
  have hKpos : 0 ≤ 340 * (X : ℝ) / Real.log X := by positivity
  have hf : (0 : ℝ) ≤ m.factorial := by positivity
  calc _ ≤ (340 * X / Real.log X * ∑ S ∈ P.powersetCard m, ∏ q ∈ S, w q) * m.factorial :=
        mul_le_mul_of_nonneg_right (mcR.trans sumb) hf
    _ = 340 * X / Real.log X * ((m.factorial : ℝ) * ∑ S ∈ P.powersetCard m, ∏ q ∈ S, w q) := by ring
    _ ≤ 340 * X / Real.log X * (∑ q ∈ P, w q) ^ m := mul_le_mul_of_nonneg_left es hKpos

/-- Pointwise: off the square set, many divisors force many small prime factors. -/
theorem cover_point (X R E m C0 T n : ℕ) (hn : 1 ≤ n) (hnX : n < X) (hE : 4 ≤ E) (hm : 1 ≤ m)
    (hC0 : C0 = 8 * E ^ (R + 1) * 4 ^ m) (hT : C0 * 2 ^ T ≤ D)
    (small : ∀ q, q.Prime → q ≤ R → ¬ q ^ E ∣ n)
    (mid : ∀ q, q.Prime → R < q → q ^ 4 ≤ X → ¬ q ^ 2 ∣ n)
    (many : D < n.divisors.card) :
    T ≤ (((Nat.primesLE X).filter (fun q => q ^ (2 * m) ≤ X)).filter (· ∣ n)).card := by
  set P := (Nat.primesLE X).filter (fun q => q ^ (2 * m) ≤ X)
  have dl := divisors_le n X R E hn hnX hE small mid
  have lp := large_primes n X (2 * m) hn hnX (by omega)
  have split : n.primeFactors ⊆ (n.primeFactors.filter fun q => ¬ X < q ^ (2 * m)) ∪
      (n.primeFactors.filter fun q => X < q ^ (2 * m)) := by
    intro q hq
    by_cases h : X < q ^ (2 * m)
    · exact mem_union_right _ (mem_filter.mpr ⟨hq, h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, h⟩)
  have sub : (n.primeFactors.filter fun q => ¬ X < q ^ (2 * m)) ⊆ P.filter (· ∣ n) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    have qp := Nat.prime_of_mem_primeFactors hq1
    have qd := Nat.dvd_of_mem_primeFactors hq1
    have qn : q ≤ n := Nat.le_of_dvd hn qd
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, qp⟩, by omega⟩, qd⟩
  have om : n.primeFactors.card ≤ (P.filter (· ∣ n)).card + 2 * m := by
    have := (card_le_card split).trans (card_union_le _ _)
    have := card_le_card sub
    omega
  by_contra hlt
  push Not at hlt
  have : n.divisors.card ≤ C0 * 2 ^ T := by
    calc n.divisors.card ≤ 2 ^ n.primeFactors.card * (E ^ (R + 1) * 8) := dl
      _ ≤ 2 ^ ((P.filter (· ∣ n)).card + 2 * m) * (E ^ (R + 1) * 8) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) om)
      _ ≤ 2 ^ (T + 2 * m) * (E ^ (R + 1) * 8) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = C0 * 2 ^ T := by rw [hC0, pow_add, pow_mul]; ring
  omega

set_option maxHeartbeats 1000000 in
theorem h2 (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in Filter.atTop,
    let X : ℕ := 2 ^ (k ^ 10)
    (((Ioc k X).filter fun p => p.Prime ∧ k ^ 8 < (p - 1).divisors.card).card : ℝ) * (k : ℝ) ^ 10
      ≤ ε * X := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l2u : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  set δ := ε * Real.log 2 / 1020 with hδ
  have δpos : 0 < δ := by positivity
  set R := ⌈1 / δ⌉₊ + 1 with hRdef
  have hR1 : 1 ≤ R := by omega
  have hRδ : 1 / (R : ℝ) ≤ δ := by
    have c : 1 / δ ≤ (R : ℝ) := by
      have := Nat.le_ceil (1 / δ)
      rw [hRdef]; push_cast; linarith
    have Rpos : (0 : ℝ) < R := by exact_mod_cast hR1
    rw [div_le_iff₀ Rpos]
    rw [div_le_iff₀ δpos] at c
    linarith
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (R + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set E := n0 + 4 with hEdef
  have hE4 : 4 ≤ E := by omega
  have hEδ : ((R : ℝ) + 1) / 2 ^ (E - 1) ≤ δ := by
    have e1 : E - 1 = n0 + 3 := by omega
    rw [e1]
    have h2n : (2 : ℝ) ^ n0 ≤ 2 ^ (n0 + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hp : (0 : ℝ) < 2 ^ n0 := by positivity
    have : (1 / 2 : ℝ) ^ n0 = 1 / 2 ^ n0 := by rw [one_div_pow]
    rw [this, lt_div_iff₀ (by positivity)] at hn0
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 : ℝ) ^ n0 * (R + 1) < δ := hn0
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hp] at this
    nlinarith
  obtain ⟨m0, hm0⟩ := exists_pow_lt_of_lt_one δpos (show (0.9 : ℝ) < 1 by norm_num)
  set m := m0 + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmδ : (0.9 : ℝ) ^ m ≤ δ :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans hm0.le
  set C0 := 8 * E ^ (R + 1) * 4 ^ m with hC0
  have hC0pos : 0 < C0 := by positivity
  set K0 := 5 * ((5 + 0.9 * (m : ℝ)) + 0.9 * Real.log C0) with hK0
  have C0r : (1 : ℝ) ≤ C0 := by exact_mod_cast hC0pos
  have logC0 : 0 ≤ Real.log C0 := Real.log_nonneg C0r
  filter_upwards [Filter.eventually_ge_atTop (max (max 2 (R ^ (2 * E))) (max C0 ⌈Real.exp K0⌉₊))]
    with k hk
  intro X
  have hXdef : X = 2 ^ (k ^ 10) := rfl
  clear_value X
  have k2 : 2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have kRE : R ^ (2 * E) ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have kC0 : C0 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have kexp : ⌈Real.exp K0⌉₊ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have kk10 : k ≤ k ^ 10 := Nat.le_self_pow (by norm_num) k
  have kX : k < X := by rw [hXdef]; exact lt_of_le_of_lt kk10 Nat.lt_two_pow_self
  have hX2 : 2 ≤ X := by omega
  have hRE : R ^ (2 * E) ≤ X := by omega
  have kr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  -- logarithms
  set L := Real.log k with hL
  have hLK : K0 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le kr]
    exact (Nat.le_ceil _).trans (by exact_mod_cast kexp)
  have K0nn : 0 ≤ K0 := by rw [hK0]; positivity
  have logX : Real.log X = (k : ℝ) ^ 10 * Real.log 2 := by
    rw [hXdef]; push_cast; rw [Real.log_pow]; push_cast; ring
  have k10pos : (0 : ℝ) < (k : ℝ) ^ 10 := by positivity
  have hLX : 0 < Real.log X := by rw [logX]; positivity
  have llX : Real.log (Real.log X) ≤ 10 * L := by
    rw [logX, Real.log_mul (by positivity) l2.ne', Real.log_pow]
    have : Real.log (Real.log 2) < 0 := Real.log_neg l2 (by linarith)
    push_cast
    linarith
  -- the sets
  set P := (Nat.primesLE X).filter (fun q => q ^ (2 * m) ≤ X) with hPdef
  set T := Nat.log 2 (k ^ 8 / C0) with hTdef
  have k8C0 : k ^ 8 / C0 ≠ 0 := by
    have : C0 ≤ k ^ 8 := kC0.trans (Nat.le_self_pow (by norm_num) k)
    exact (Nat.div_pos this hC0pos).ne'
  have hT : C0 * 2 ^ T ≤ k ^ 8 := by
    have := Nat.pow_log_le_self 2 k8C0
    calc C0 * 2 ^ T ≤ C0 * (k ^ 8 / C0) := Nat.mul_le_mul_left _ this
      _ ≤ k ^ 8 := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have hT1 : k ^ 8 < C0 * 2 ^ (T + 1) := by
    have a := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (k ^ 8 / C0)
    have b := Nat.lt_mul_div_succ (k ^ 8) hC0pos
    calc k ^ 8 < C0 * (k ^ 8 / C0 + 1) := b
      _ ≤ C0 * 2 ^ (T + 1) := Nat.mul_le_mul_left _ a
  have Tlog : 8 * L < Real.log C0 + ((T : ℝ) + 1) * Real.log 2 := by
    have h := Real.log_lt_log (by positivity) (show ((k ^ 8 : ℕ) : ℝ) < ((C0 * 2 ^ (T + 1) : ℕ) : ℝ)
      by exact_mod_cast hT1)
    push_cast at h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    rw [hL]; push_cast at h; linarith
  set W := ∑ q ∈ P, w q with hW
  have W0 : 0 ≤ W := sum_nonneg fun q _ => w_nonneg q
  have Wle : W ≤ 10 * L + 5 :=
    (sum_w_le X hX2 P (filter_subset _ _)).trans (by linarith)
  have L0 : 0 ≤ L := K0nn.trans hLK
  have ratio : 10 * L + 5 + 0.9 * m < 0.9 * ((T : ℝ) + 1) := by
    have a1 : L * Real.log 2 ≤ L * 0.7 := mul_le_mul_of_nonneg_left l2u.le L0
    have a2 : (5 + 0.9 * (m : ℝ)) * Real.log 2 ≤ (5 + 0.9 * (m : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have key : (10 * L + 5 + 0.9 * m) * Real.log 2 < (0.9 * ((T : ℝ) + 1)) * Real.log 2 := by
      rw [hK0] at hLK
      have e1 : (10 * L + 5 + 0.9 * m) * Real.log 2
          = 10 * (L * Real.log 2) + (5 + 0.9 * (m : ℝ)) * Real.log 2 := by ring
      have e2 : (0.9 * ((T : ℝ) + 1)) * Real.log 2 = 0.9 * (((T : ℝ) + 1) * Real.log 2) := by ring
      rw [e1, e2]
      linarith
    exact lt_of_mul_lt_mul_right key l2.le
  have mT : m ≤ T := by
    have : (m : ℝ) < (T : ℝ) + 1 := by linarith
    have : m < T + 1 := by exact_mod_cast this
    omega
  have Wr : W ≤ 0.9 * ((T + 1 - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  -- count B
  set B := (Ioc k X).filter fun p => p.Prime ∧ T ≤ (P.filter (· ∣ p - 1)).card with hB
  have mb := moment_bound k X m T hX2 hm1 P le_rfl
  set K := 340 * (X : ℝ) / Real.log X with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  set Dm : ℝ := (m.factorial : ℝ) * (T.choose m : ℝ) with hDm
  have Dlow : (((T + 1 - m : ℕ) : ℝ)) ^ m ≤ Dm := by
    have := Nat.pow_sub_le_descFactorial T m
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    rw [hDm]; exact_mod_cast this
  have Dpos : 0 < Dm := by
    rw [hDm]
    have : 0 < T.choose m := Nat.choose_pos mT
    positivity
  have Bb : (B.card : ℝ) ≤ K * δ := by
    have mb' : Dm * B.card ≤ K * W ^ m := by
      have : ((T.choose m * B.card : ℕ) : ℝ) * m.factorial = Dm * B.card := by
        rw [hDm]; push_cast; ring
      rw [← this]; exact mb
    have Wm : W ^ m ≤ 0.9 ^ m * Dm := by
      calc W ^ m ≤ (0.9 * ((T + 1 - m : ℕ) : ℝ)) ^ m := pow_le_pow_left₀ W0 Wr m
        _ = 0.9 ^ m * (((T + 1 - m : ℕ) : ℝ)) ^ m := by rw [mul_pow]
        _ ≤ 0.9 ^ m * Dm := mul_le_mul_of_nonneg_left Dlow (by positivity)
    have : Dm * B.card ≤ Dm * (K * δ) := by
      calc Dm * B.card ≤ K * W ^ m := mb'
        _ ≤ K * (0.9 ^ m * Dm) := mul_le_mul_of_nonneg_left Wm hKpos.le
        _ = Dm * (K * 0.9 ^ m) := by ring
        _ ≤ Dm * (K * δ) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmδ hKpos.le) Dpos.le
    exact le_of_mul_le_mul_left this Dpos
  -- count S1
  set Q1 := (range (R + 1)).filter Nat.Prime with hQ1
  set Q2 := (Ioc R X).filter (fun q => q.Prime ∧ q ^ 4 ≤ X) with hQ2
  set U1 := Q1.biUnion (fun q => (Ioc k X).filter fun p => p.Prime ∧ q ^ E ∣ p - 1) with hU1
  set U2 := Q2.biUnion (fun q => (Ioc k X).filter fun p => p.Prime ∧ q ^ 2 ∣ p - 1) with hU2
  have sqb := squares_bound k X R E hX2 hR1 hE4 hRE
  have U1c : (U1.card : ℝ) ≤ ∑ q ∈ Q1, (N k X (q ^ E) : ℝ) := by
    have := card_biUnion_le (s := Q1) (t := fun q => (Ioc k X).filter fun p => p.Prime ∧ q ^ E ∣ p - 1)
    exact_mod_cast this
  have U2c : (U2.card : ℝ) ≤ ∑ q ∈ Q2, (N k X (q ^ 2) : ℝ) := by
    have := card_biUnion_le (s := Q2) (t := fun q => (Ioc k X).filter fun p => p.Prime ∧ q ^ 2 ∣ p - 1)
    exact_mod_cast this
  -- covering
  set Ebad := (Ioc k X).filter fun p => p.Prime ∧ k ^ 8 < (p - 1).divisors.card with hEbad
  have cov : Ebad ⊆ (U1 ∪ U2) ∪ B := by
    intro p hp
    obtain ⟨hpI, pp, many⟩ := mem_filter.mp hp
    obtain ⟨_, hpX⟩ := mem_Ioc.mp hpI
    by_cases h1 : ∃ q ∈ Q1, q ^ E ∣ p - 1
    · obtain ⟨q, hq, hd⟩ := h1
      exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨q, hq, mem_filter.mpr ⟨hpI, pp, hd⟩⟩))
    by_cases h2 : ∃ q ∈ Q2, q ^ 2 ∣ p - 1
    · obtain ⟨q, hq, hd⟩ := h2
      exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨q, hq, mem_filter.mpr ⟨hpI, pp, hd⟩⟩))
    apply mem_union_right
    refine mem_filter.mpr ⟨hpI, pp, ?_⟩
    have p2 := pp.two_le
    apply cover_point X R E m C0 T (p - 1) (by omega) (by omega) hE4 hm1 hC0 hT _ _ many
    · intro q qp qR hd
      exact h1 ⟨q, mem_filter.mpr ⟨mem_range.mpr (by omega), qp⟩, hd⟩
    · intro q qp Rq q4 hd
      have : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
      exact h2 ⟨q, mem_filter.mpr ⟨mem_Ioc.mpr ⟨Rq, by omega⟩, qp, q4⟩, hd⟩
  have Ec : (Ebad.card : ℝ) ≤ U1.card + U2.card + B.card := by
    have := (card_le_card cov).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    exact_mod_cast this
  have total : (Ebad.card : ℝ) ≤ K * (3 * δ) := by
    have h1 : K * (((R : ℝ) + 1) / 2 ^ (E - 1) + 1 / R) ≤ K * (2 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hKpos.le
    have sqb' : (∑ q ∈ Q1, (N k X (q ^ E) : ℝ)) + ∑ q ∈ Q2, (N k X (q ^ 2) : ℝ)
        ≤ K * (((R : ℝ) + 1) / 2 ^ (E - 1) + 1 / R) := sqb
    have e : K * (3 * δ) = K * (2 * δ) + K * δ := by ring
    linarith
  calc (Ebad.card : ℝ) * (k : ℝ) ^ 10 ≤ K * (3 * δ) * (k : ℝ) ^ 10 :=
        mul_le_mul_of_nonneg_right total k10pos.le
    _ = ε * X := by
        rw [hK, hδ, logX]
        field_simp
        ring

end E694

end E694Main

theorem OMA.solution : OMA.R_Erdos694_erdos_694_variants_inf_unique_R1_H1_R1.H2 :=
  E694.h2

