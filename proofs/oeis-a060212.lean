import OMAStatements.S_oeis_a060212
import Mathlib

/- The finite Selberg sieve and elementary Mertens estimate are extracted from
Steven Enamakel (@senamakel), open-math-agents PR 2394, as reused in
Erdos16.erdos_16.variant.romanoff.R1.H2.R1.H1 at commit
2c51b93c40315f0d44015065a3363a1ce9b3503f. -/

section

open scoped Classical
open Finset

namespace OMALib.Sieve

variable {ι : Type*} [DecidableEq ι]

noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

noncomputable def selbergWeight (g : ι → ℝ) (D : Finset (Finset ι)) (S : Finset ι) : ℝ :=
  (-1) ^ S.card * (∏ p ∈ S, (g p)⁻¹) / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p

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
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx
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

theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS' q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp.pos, ← ih hS']
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

noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).pos
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

theorem selberg_residue (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p)
    (D : Finset (Finset ℕ)) (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D)
    (hemp : ∅ ∈ D) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) D
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
  set g : ℕ → ℝ := fun p => (omega C p : ℝ) / p
  have hg0 : ∀ p ∈ Q, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast hω0 p hp) (by exact_mod_cast (hQ p hp).pos)
  have hg1 : ∀ p ∈ Q, g p < 1 := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
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
    have := card_residue_error C hper (S₁ ∪ S₂) (fun p hp => hQ p (hSQ hp)) N
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

theorem levelFamily_down {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {z : ℕ} :
    ∀ S ∈ levelFamily Q z, ∀ T ⊆ S, T ∈ levelFamily Q z := by
  intro S hS T hT
  simp only [levelFamily, mem_filter, mem_powerset] at hS ⊢
  refine ⟨hT.trans hS.1, lt_of_le_of_lt ?_ hS.2⟩
  exact prod_le_prod_of_subset_of_one_le' hT fun p hp _ => (hQ p (hS.1 hp)).one_lt.le

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS hT
      have h1 := Nat.primeFactors_prod (s := S) fun p hp => hQ p (hS.1 hp)
      have h2 := Nat.primeFactors_prod (s := T) fun p hp => hQ p (hT.1 hp)
      simp only at h
      rw [← h1, ← h2, h])
  simpa using this

theorem selberg_residue_level (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z) + (z : ℝ) ^ 4 := by
  have key := selberg_residue N Q hQ C hper hω0 hω1 (levelFamily Q z) levelFamily_subset
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
      exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => (hQ p (h₁'.1 (mem_inter.mp hp).1)).pos)
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
        have h1 : ((levelFamily Q z).card : ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ z
        have h0 : (0 : ℝ) ≤ ((levelFamily Q z).card : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = (z : ℝ) ^ 4 := by ring

theorem selbergG_congr {Q : Finset ℕ} {D : Finset (Finset ℕ)} (hDQ : ∀ S ∈ D, S ⊆ Q)
    {g g' : ℕ → ℝ} (h : ∀ p ∈ Q, g p = g' p) : selbergG g D = selbergG g' D := by
  unfold selbergG hFun
  exact sum_congr rfl fun S hS => prod_congr rfl fun p hp => by rw [h p (hDQ S hS hp)]

end OMALib.Sieve
end
section

open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

end OMALib.Mertens
end
open scoped Classical
open Finset Real Filter Asymptotics
namespace A060212
open OMA.S_oeis_a060212
def Q (Y : ℕ) := Y.primesLE.filter (5 ≤ ·)
lemma memQ {Y p} : p ∈ Q Y ↔ p ≤ Y ∧ p.Prime ∧ 5 ≤ p := by
  simp [Q, and_assoc, Nat.mem_primesLE]
noncomputable def roots (p : ℕ) : Finset ℕ :=
  {0, ((6 : ZMod p)⁻¹).val, (-(6 : ZMod p)⁻¹).val}
def C (p n : ℕ) : Prop := n % p ∈ roots p

lemma six_ne {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : (6 : ZMod p) ≠ 0 := by
  change ((6 : ℕ) : ZMod p) ≠ 0
  simp only [ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by decide : 0 < 6) h
  interval_cases p <;> norm_num at *

lemma roots_card {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ((range p).filter (C p)).card = 3 := by
  let : Fact p.Prime := ⟨hp⟩
  have h6 := six_ne hp h5
  let a := (6 : ZMod p)⁻¹
  have ha : a ≠ 0 := inv_ne_zero h6
  have ht : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    simp only [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have han : a ≠ -a := by
    intro h
    have h' : (2 : ZMod p) * a = 0 := by linear_combination h
    exact (mul_ne_zero ht ha) h'
  have hs : (range p).filter (C p) = roots p := by
    ext x
    simp only [mem_filter, mem_range, C]
    constructor
    · rintro ⟨h, hx⟩
      simpa [Nat.mod_eq_of_lt h] using hx
    · intro hx
      have h : x < p := by
        change x ∈ ({0, a.val, (-a).val} : Finset ℕ) at hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · omega
        · exact ZMod.val_lt _
        · exact ZMod.val_lt _
      exact ⟨h, by simpa [Nat.mod_eq_of_lt h] using hx⟩
  rw [hs]
  change ({0, a.val, (-a).val} : Finset ℕ).card = 3
  have h1 : a.val ≠ 0 := by simpa using ha
  have h2 : (-a).val ≠ 0 := by simpa using ha
  have h3 : a.val ≠ (-a).val := fun h => han (ZMod.val_injective _ h)
  simp [h1.symm, h2.symm, h3]

lemma avoids {Y p q : ℕ} (hp : p ∈ Q Y) (hq : P q) (hlt : Y < q) : ¬ C p q := by
  obtain ⟨hpy, hpp, h5⟩ := memQ.mp hp
  let : Fact p.Prime := ⟨hpp⟩
  have h6 := six_ne hpp h5
  have nz (a : ℕ) (ha : a.Prime) (hpa : p < a) : (a : ZMod p) ≠ 0 := by
    simp only [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.prime_dvd_prime_iff_eq hpp ha).mp h |> ne_of_lt hpa
  have hq0 := nz q hq.1 (by omega)
  have hm := nz (6*q-1) hq.2.1 (by omega)
  have hp' := nz (6*q+1) hq.2.2 (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ 6*q)] at hm
  push_cast at hm hp'
  intro h
  change q % p ∈ ({0, ((6 : ZMod p)⁻¹).val, (-(6 : ZMod p)⁻¹).val} : Finset ℕ) at h
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h
  all_goals have e := congrArg (fun n : ℕ => (n : ZMod p)) h
  all_goals simp only [ZMod.natCast_mod, Nat.cast_zero, ZMod.natCast_zmod_val] at e
  · exact hq0 e
  · apply hm
    simp [e, h6]
  · apply hp'
    simp [e, h6]

noncomputable def H (p : ℕ) : ℝ := 3 / ((p : ℝ) - 3)
noncomputable def W (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 + H p)
noncomputable def mass (s : Finset ℕ) : ℝ := ∏ p ∈ s, H p
lemma W_sum (s : Finset ℕ) : W s = ∑ t ∈ s.powerset, mass t := prod_one_add s
lemma Hpos {p : ℕ} (h : 5 ≤ p) : 0 < H p := by
  have : (5:ℝ) ≤ p := by exact_mod_cast h
  exact div_pos (by norm_num) (by linarith)

/-- The first logarithmic moment of the subset weights, expanded one prime at a time. -/
lemma moment (s : Finset ℕ) (hs : ∀ p ∈ s, 5 ≤ p) :
    ∑ t ∈ s.powerset, mass t * (∑ p ∈ t, log p) =
    W s * (∑ p ∈ s, 3 * log p / p) := by
  induction s using Finset.induction_on with
  | empty => simp [W, mass]
  | @insert p s hps ih =>
    have hp := hs p (mem_insert_self _ _)
    have hp' : (5:ℝ) ≤ p := by exact_mod_cast hp
    have hid : (1 + H p) * (3 * log p / p) = H p * log p := by
      unfold H
      field_simp [show (p:ℝ) - 3 ≠ 0 by linarith, show (p:ℝ) ≠ 0 by linarith]
      ring
    have hW : W (insert p s) = (1 + H p) * W s := prod_insert hps
    have hm : ∑ t ∈ s.powerset, mass (insert p t) * (∑ i ∈ insert p t, log i) =
        H p * log p * W s + H p * (∑ t ∈ s.powerset, mass t * ∑ i ∈ t, log i) := by
      rw [W_sum, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun t ht => ?_
      have hpt : p ∉ t := fun h => hps (mem_powerset.mp ht h)
      simp only [mass, prod_insert hpt, sum_insert hpt]
      ring
    rw [sum_powerset_insert hps, hm, ih (fun q hq => hs q (mem_insert_of_mem hq)),
      hW, sum_insert hps]
    linear_combination -(W s) * hid

lemma euler (Y : ℕ) (hY : 5 ≤ Y) :
    log Y ≤ 3 * ∏ p ∈ Q Y, (1 - (p : ℝ)⁻¹)⁻¹ := by
  let f : ℕ →* ℝ := { toFun := fun n => (n : ℝ)⁻¹, map_one' := by simp, map_mul' := by intros; push_cast; simp [mul_comm] }
  have hf : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf (Y+1)).2
  let e : ↥(Icc 1 Y) ↪ (Y+1).smoothNumbers :=
    ⟨fun n => ⟨n.val, Nat.mem_smoothNumbers_of_lt (mem_Icc.mp n.prop).1
      (Nat.lt_succ_of_le (mem_Icc.mp n.prop).2)⟩, fun _ _ h => Subtype.ext (congrArg (fun m : (Y+1).smoothNumbers => m.val) h)⟩
  have hl := hsum.summable.sum_le_tsum ((Icc 1 Y).attach.map e)
    (fun n _ => (inv_nonneg.mpr (Nat.cast_nonneg n.val) : 0 ≤ f n.val))
  replace hl := hl.trans_eq hsum.tsum_eq
  rw [sum_map] at hl
  change (∑ n ∈ (Icc 1 Y).attach, (n.val : ℝ)⁻¹) ≤
    ∏ p ∈ Y.primesLE, (1 - (p : ℝ)⁻¹)⁻¹ at hl
  rw [sum_attach _ (fun n : ℕ => (n : ℝ)⁻¹)] at hl
  have he : Y.primesLE = insert 2 (insert 3 (Q Y)) := by
    ext p
    simp only [Nat.mem_primesLE, mem_insert, memQ]
    constructor
    · rintro ⟨hle,hp⟩
      by_cases h : 5 ≤ p
      · exact Or.inr (Or.inr ⟨hle,hp,h⟩)
      · have := hp.two_le
        interval_cases p <;> norm_num at *
    · rintro (rfl | rfl | ⟨hl,hp,_⟩)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, Nat.prime_three⟩
      · exact ⟨hl,hp⟩
  rw [he, prod_insert (by simp [memQ]), prod_insert (by simp [memQ])] at hl
  norm_num at hl
  have hh := log_add_one_le_harmonic Y
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  have ht := Real.log_le_log (by positivity : (0:ℝ) < Y) (by exact_mod_cast Nat.le_succ Y : (Y:ℝ) ≤ (Y+1:ℕ))
  rw [prod_inv_distrib]
  linarith

noncomputable def G (Y : ℕ) : ℝ :=
  ∑ s ∈ (Q Y).powerset with ∏ p ∈ s, p < Y^12, mass s

/-- Subsets with product at least the level carry at most half the total weight. -/
lemma truncate (Y : ℕ) (hY : 5 ≤ Y)
    (hmert : ∑ p ∈ Y.primesLE, log p / p ≤ log Y + log 4) :
    W (Q Y) ≤ 2 * G Y := by
  have hYr : (5:ℝ) ≤ Y := by exact_mod_cast hY
  have hlog : 0 < log Y := log_pos (by linarith)
  have hm := moment (Q Y) (fun _ h => (memQ.mp h).2.2)
  have hsum : (∑ p ∈ Q Y, 3 * log p / p) ≤ 6 * log Y := by
    have hs : (∑ p ∈ Q Y, log p / p) ≤ ∑ p ∈ Y.primesLE, log p / p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ =>
        div_nonneg (log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)) (by positivity)
    simp_rw [mul_div_assoc, ← mul_sum]
    linarith [log_le_log (by norm_num : (0:ℝ) < 4) (by linarith : (4:ℝ) ≤ Y)]
  have hw : 0 ≤ W (Q Y) := prod_nonneg fun p hp => by
    have := Hpos (memQ.mp hp).2.2
    linarith
  have hb : 12 * log Y * W (Q Y) ≤ 12 * log Y * G Y +
      ∑ s ∈ (Q Y).powerset, mass s * (∑ p ∈ s, log p) := by
    rw [W_sum, G, sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun s hs => ?_
    have hsub := mem_powerset.mp hs
    have hn : 0 ≤ mass s := prod_nonneg fun p hp => (Hpos (memQ.mp (hsub hp)).2.2).le
    have hpl (p) (hp : p ∈ s) : 1 ≤ p := (memQ.mp (hsub hp)).2.1.one_le
    split_ifs with h
    · have hl := sum_nonneg (s := s) (f := fun p : ℕ => log p)
          fun p hp => log_nonneg (by exact_mod_cast hpl p hp)
      linarith [mul_nonneg hn hl]
    · have hle : ((Y:ℝ)^12) ≤ (∏ p ∈ s, (p:ℝ)) := by rw [← Nat.cast_prod]; exact_mod_cast le_of_not_gt h
      have hl := log_le_log (by positivity) hle
      rw [log_pow, log_prod (fun p hp => by exact_mod_cast (Nat.ne_of_gt (hpl p hp)))] at hl
      push_cast at hl
      nlinarith [mul_le_mul_of_nonneg_left hl hn]
  rw [hm] at hb
  have ha := mul_le_mul_of_nonneg_left hsum hw
  by_contra! h
  nlinarith [mul_pos hlog (sub_pos.mpr h)]

lemma lower (Y : ℕ) (hY : 5 ≤ Y)
    (hmert : ∑ p ∈ Y.primesLE, log p / p ≤ log Y + log 4) :
    (log Y)^3 ≤ 54 * G Y := by
  have hpow : (∏ p ∈ Q Y, (1 - (p:ℝ)⁻¹)⁻¹)^3 ≤ W (Q Y) := by
    rw [← prod_pow]
    apply Finset.prod_le_prod
    · intro p hp
      have h : (1:ℝ) < p := by exact_mod_cast (memQ.mp hp).2.1.one_lt
      have := inv_lt_one_of_one_lt₀ h
      positivity
    · intro p hp
      have hh : (5:ℝ) ≤ p := by exact_mod_cast (memQ.mp hp).2.2
      have hp0 : (0:ℝ) < p := by linarith
      have h1 : (0:ℝ) < p-1 := by linarith
      have h3 : (0:ℝ) < p-3 := by linarith
      have he : (1 - (p:ℝ)⁻¹)⁻¹ = p / (p-1:ℝ) := by
        rw [show 1 - (p:ℝ)⁻¹ = (p-1:ℝ)/p by field_simp, inv_div]
      rw [he, div_pow, div_le_iff₀ (pow_pos h1 _)]
      unfold H
      field_simp [h3.ne']
      nlinarith [sq_nonneg ((p:ℝ)-3)]
  have hh := pow_le_pow_left₀ (log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))) (euler Y hY) 3
  rw [mul_pow] at hh
  linarith [truncate Y hY hmert]

open OMALib.Sieve
lemma count_bound (X Y : ℕ) (hY : 5 ≤ Y) :
    (Nat.count P X : ℝ) ≤ Y + (Y : ℝ)^48 + 54 * X / (log Y)^3 := by
  have hω (p) (hp : p ∈ Q Y) : omega C p = 3 :=
    roots_card (memQ.mp hp).2.1 (memQ.mp hp).2.2
  have hz : 2 ≤ Y^12 := le_trans (by decide : 2 ≤ 5^12) (Nat.pow_le_pow_left hY _)
  have hk := selberg_residue_level X (Y^12) hz (Q Y) (fun _ h => (memQ.mp h).2.1)
    C (fun p n => by simp [C]) (fun p hp => by rw [hω p hp]; decide)
    (fun p hp => by rw [hω p hp]; have := (memQ.mp hp).2.2; omega)
  have hg : selbergG (fun p => (omega C p : ℝ)/p) (levelFamily (Q Y) (Y^12)) = G Y := by
    apply sum_congr rfl
    intro s hs
    refine prod_congr rfl fun p hp => ?_
    have hm := levelFamily_subset s hs hp
    have hp5 : (5:ℝ) ≤ p := by exact_mod_cast (memQ.mp hm).2.2
    simp only [hFun, hω p hm, Nat.cast_ofNat, H]
    field_simp [show (p:ℝ) ≠ 0 by linarith, show (p:ℝ)-3 ≠ 0 by linarith]
  rw [hg, Nat.cast_pow, ← pow_mul] at hk
  have hcount : Nat.count P X ≤ Y + ((range X).filter (fun n => ∀ p ∈ Q Y, ¬ C p n)).card := by
    rw [Nat.count_eq_card_filter_range]
    let t := (range X).filter (fun n => ∀ p ∈ Q Y, ¬ C p n)
    have hsub : (range X).filter P ⊆ Icc 1 Y ∪ t := by
      intro q hq
      obtain ⟨hx,hpq⟩ := mem_filter.mp hq
      by_cases h : q ≤ Y
      · exact mem_union_left _ (mem_Icc.mpr ⟨hpq.1.one_le,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hx,fun p hp => avoids hp hpq (by omega)⟩)
    simpa [t] using (card_le_card hsub).trans (card_union_le _ _)
  have hl := lower Y hY (OMALib.Mertens.sum_log_div_le_nat Y)
  have hp : 0 < log Y := log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hpos := pow_pos hp 3
  have hgpos : 0 < G Y := by linarith
  have hdiv : (X:ℝ) / G Y ≤ 54 * X / (log Y)^3 := by
    rw [div_le_div_iff₀ hgpos hpos]
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg X)]
  have hreal : (Nat.count P X : ℝ) ≤ (Y:ℝ) + ((range X).filter (fun n => ∀ p ∈ Q Y, ¬ C p n)).card := by exact_mod_cast hcount
  linarith

namespace Growth
variable {P : ℕ → Prop} [DecidablePred P]
noncomputable def F (n : ℕ) : ℝ := n * log n * log (n * log n) * log (log n)

lemma log_gt_one {n : ℕ} (hn : 3 ≤ n) : 1 < log n := by
  apply (lt_log_iff_exp_lt (by positivity)).2
  exact exp_one_lt_three.trans_le (by exact_mod_cast hn)

lemma F_pos {n : ℕ} (hn : 3 ≤ n) : 0 < F n := by
  have hl := log_gt_one hn
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hl' := log_pos hl
  have hl'' : 0 < log (n * log n) := log_pos (by nlinarith)
  unfold F
  positivity

def index (j : ℕ) := j^91 * 2^(96*j^2)
def level (j : ℕ) := j * 2^(j^2)
lemma scale (j : ℕ) : level j ^ 96 = j^5 * index j := by
  simp only [level, index, mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
  rw [Nat.mul_comm (j^2) 96]

lemma le_index (j : ℕ) : j ≤ index j := (Nat.le_pow (by decide : 0 < 91)).trans
  (Nat.le_mul_of_pos_right _ (by positivity))

lemma analytic_bound (k : ℕ) (hk : 3 ≤ k) :
    F (index (k^2)) ≤ index (k^2) * (200 : ℝ)^2 * 2 * (k^2:ℕ)^4 * (204*k) := by
  let j := k^2
  let n := index j
  change F n ≤ (n:ℝ) * _ * _ * (j:ℝ)^4 * _
  have hkj : k ≤ j := Nat.le_pow (by decide : 0 < 2)
  have hkn : k ≤ n := hkj.trans (le_index j)
  have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hjr : (3:ℝ) ≤ j := by exact_mod_cast hk.trans hkj
  have hl := log_gt_one (hk.trans hkn)
  have hn : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hj : (0:ℝ) < j := by linarith
  have hlj : log j ≤ (j:ℝ)^2 := (log_le_self hj.le).trans (by nlinarith)
  have hln : log n ≤ 200 * (j:ℝ)^2 := by
    change log ((j^91 * 2^(96*j^2) : ℕ) : ℝ) ≤ _
    push_cast
    rw [log_mul (by positivity) (by positivity), log_pow, log_pow]
    push_cast
    nlinarith [mul_nonneg (sq_nonneg (j:ℝ)) (le_of_lt log_two_lt_d9 |> sub_nonneg.mpr)]
  have hll : log (log n) ≤ 204 * k := by
    have ht := log_le_log (by linarith : 0 < log n) hln
    rw [log_mul (by norm_num) (by positivity), log_pow] at ht
    have hjlog : log j = 2 * log k := by simp [j, log_pow]
    rw [hjlog] at ht
    norm_num at ht
    nlinarith [log_le_self (by norm_num : (0:ℝ) ≤ 200), log_le_self (Nat.cast_nonneg k)]
  have hnl : log (n * log n) ≤ 2 * (200 * (j:ℝ)^2) := by
    rw [log_mul hn.ne' (by linarith)]
    linarith [log_le_self (by linarith : 0 ≤ log n)]
  have hm : 0 ≤ log (n * log n) := log_nonneg (by
    have : (3:ℝ) ≤ n := by exact_mod_cast hk.trans hkn
    nlinarith)
  calc F n ≤ n * (200 * (j:ℝ)^2) * (2 * (200 * (j:ℝ)^2)) * (204*k) := by
         unfold F
         gcongr
         all_goals exact log_nonneg hl.le
       _ = _ := by ring

lemma count_small (j : ℕ) (hj : 2000 ≤ j)
    (bound : (Nat.count P (level j ^ 96) : ℝ) ≤ level j + (level j : ℝ)^48 +
      54 * (level j : ℝ)^96 / (log (level j))^3) :
    Nat.count P (level j^96) < index j := by
  let Y := level j
  let n := index j
  have hjr : (2000:ℝ) ≤ j := by exact_mod_cast hj
  have hjY : j ≤ Y := Nat.le_mul_of_pos_right _ (by positivity)
  have hYr : (j:ℝ) ≤ Y := by exact_mod_cast hjY
  have hYone : (1:ℝ) ≤ Y := by linarith
  have hn : (0:ℝ) < n := by have := le_index j; change 0 < (index j:ℝ); exact_mod_cast (by omega : 0 < index j)
  have hid : (Y:ℝ)^96 = (j:ℝ)^5 * n := by exact_mod_cast scale j
  have hlog : (j:ℝ)^2 / 2 ≤ log Y := by
    change _ ≤ log ((j * 2^(j^2) : ℕ) : ℝ)
    push_cast
    rw [log_mul (by positivity) (by positivity), log_pow]
    push_cast
    nlinarith [mul_nonneg (sq_nonneg (j:ℝ)) (sub_nonneg.mpr log_two_gt_d9.le),
      log_nonneg (by linarith : (1:ℝ) ≤ j)]
  have hmain : 54 * (Y:ℝ)^96 / (log Y)^3 < n / 2 := by
    have hp := pow_le_pow_left₀ (by positivity) hlog 3
    have hl : 0 < log Y := by nlinarith
    rw [div_lt_iff₀ (pow_pos hl 3), hid]
    have hc : 108 * (j:ℝ)^5 < ((j:ℝ)^2/2)^3 := by
      nlinarith [mul_pos (by linarith : 0 < (j:ℝ)-864) (by positivity : 0 < (j:ℝ)^5)]
    nlinarith only [mul_lt_mul_of_pos_right (hc.trans_le hp) hn]
  have herr : 4 * (Y:ℝ)^48 ≤ n := by
    have h4 : 4*(j:ℝ)^5 ≤ (Y:ℝ)^48 := calc
      _ ≤ (j:ℝ)*(j:ℝ)^5 := by gcongr; linarith
      _ = (j:ℝ)^6 := by ring
      _ ≤ (Y:ℝ)^6 := by gcongr
      _ ≤ (Y:ℝ)^48 := pow_le_pow_right₀ hYone (by decide)
    have ht := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ (Y:ℝ)^48)
    have hsq : (Y:ℝ)^48 * (Y:ℝ)^48 = (Y:ℝ)^96 := by ring
    rw [hsq, hid] at ht
    apply le_of_mul_le_mul_left (a := (j:ℝ)^5) _ (by positivity)
    linarith only [ht]
  have hy := le_self_pow₀ hYone (by decide : (48:ℕ) ≠ 0)
  change (Nat.count P (Y^96) : ℝ) ≤ _ at bound
  change (Nat.count P (Y^96) : ℝ) ≤ Y + (Y:ℝ)^48 + 54 * (Y:ℝ)^96 / (log Y)^3 at bound
  exact_mod_cast (show (Nat.count P (Y^96) : ℝ) < n by linarith only [bound, herr, hy, hmain])

lemma refute (hcount : ∀ X Y : ℕ, 5 ≤ Y →
    (Nat.count P X : ℝ) ≤ Y + (Y:ℝ)^48 + 54 * X / (log Y)^3) :
    ¬ IsEquivalent atTop (fun n : ℕ => (Nat.nth P (n-1) : ℝ)) F := by
  intro h
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < F n := (eventually_ge_atTop 3).mono fun _ => F_pos
  by_cases hf : (Set.ofPred P).Finite
  · obtain ⟨N,hN⟩ := eventually_atTop.mp (h.eventually_pos hpos)
    let n := N + hf.toFinset.card + 1
    have hn := hN n (by dsimp [n]; omega)
    have hz := Nat.nth_of_card_le hf (show hf.toFinset.card ≤ n-1 by dsimp [n]; omega)
    simp [hz] at hn
  obtain ⟨B,hB,hO⟩ := h.isBigO.exists_pos
  obtain ⟨N,hN⟩ := eventually_atTop.mp hO.bound
  obtain ⟨b,hb⟩ := exists_nat_gt (B * 200^2 * 2 * 204)
  let k := b + N + 2000
  let j := k^2
  let n := index j
  let Y := level j
  have hk : 2000 ≤ k := by dsimp [k]; omega
  have hkj : k ≤ j := Nat.le_pow (by decide : 0 < 2)
  have hj : 2000 ≤ j := hk.trans hkj
  have hn := hkj.trans (le_index j)
  have hn3 : 3 ≤ n := by change 3 ≤ index j; omega
  have hNk : N ≤ k := by dsimp [k]; omega
  have hnn := hN n (hNk.trans hn)
  change ‖(Nat.nth P (n-1) : ℝ)‖ ≤ B * ‖F n‖ at hnn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (F_pos hn3).le] at hnn
  have hscale : (Y:ℝ)^96 = (j:ℝ)^5 * n := by exact_mod_cast scale j
  have hjr : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hnr : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkr : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hBk : B * 200^2 * 2 * 204 < k :=
    hb.trans_le (by exact_mod_cast (show b ≤ k by dsimp [k]; omega))
  have hsmall : B * F n < (Y:ℝ)^96 := by
    have hu := mul_le_mul_of_nonneg_left (analytic_bound k (by omega)) hB.le
    rw [hscale]
    have hc := mul_lt_mul_of_pos_right hBk hkr
    have hkjr : (k:ℝ)^2 = (j:ℝ) := by simp [j]
    have haux : B * 200^2 * 2 * (204*k) < (j:ℝ) := by nlinarith only [hc, hkjr]
    have hm := mul_lt_mul_of_pos_left haux (mul_pos hnr (pow_pos hjr 4))
    refine hu.trans_lt ?_
    change B * ((n:ℝ) * 200^2 * 2 * (j:ℝ)^4 * (204*k)) < _
    linarith only [hm]
  have hlt : Nat.nth P (n-1) < Y^96 := by exact_mod_cast hnn.trans_lt hsmall
  have hlow := (Nat.count_monotone P) (show Nat.nth P (n-1)+1 ≤ Y^96 by omega)
  rw [Nat.count_nth_succ_of_infinite hf, Nat.sub_add_cancel (by omega : 1 ≤ n)] at hlow
  have hYj : j ≤ Y := Nat.le_mul_of_pos_right _ (by positivity)
  have hu := hcount (Y^96) Y (by omega)
  rw [Nat.cast_pow] at hu
  exact (count_small j hj hu).not_ge hlow
end Growth
end A060212

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a060212.main) := by
  exact A060212.Growth.refute A060212.count_bound
