import FormalConjectures.Wikipedia.LonelyRunnerConjecture
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
Module 1a: Green-Walker concentration lemma (Lemma 2.1) and GCD extremal bound (Theorem 1.1 / 6.2).
Zero MeasureTheory, pure finite algebra and p-adic valuations.
-/

namespace LRMod1

open Finset BigOperators

section Helpers

lemma rpow_two_mul_half {a p : ℝ} (ha : 0 ≤ a) : (a ^ (p / 2)) ^ 2 = a ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  norm_num

lemma sum_rpow_half_cs {S' S'' : Finset ℤ} {x y : ℤ → ℝ} {q' : ℝ}
    (hx : ∀ i ∈ S', 0 ≤ x i) (hy : ∀ j ∈ S'', 0 ≤ y j)
    (m : ℤ) (hm : ∀ i ∈ S', i + m ∈ S'') :
    ∑ i ∈ S', (x i * y (i + m)) ^ (q' / 2) ≤
      Real.sqrt (∑ i ∈ S', x i ^ q') * Real.sqrt (∑ j ∈ S'', y j ^ q') := by
  have h1 : ∑ i ∈ S', (x i * y (i + m)) ^ (q' / 2) =
      ∑ i ∈ S', (x i ^ (q' / 2)) * (y (i + m) ^ (q' / 2)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact Real.mul_rpow (hx i hi) (hy (i + m) (hm i hi))
  rw [h1]
  refine (Real.sum_mul_le_sqrt_mul_sqrt S' (fun i => x i ^ (q' / 2))
    (fun i => y (i + m) ^ (q' / 2))).trans ?_
  have hsq1 : ∑ i ∈ S', (x i ^ (q' / 2)) ^ 2 = ∑ i ∈ S', x i ^ q' :=
    Finset.sum_congr rfl fun i hi => rpow_two_mul_half (hx i hi)
  have hsq2 : ∑ i ∈ S', (y (i + m) ^ (q' / 2)) ^ 2 ≤ ∑ j ∈ S'', y j ^ q' := by
    have heq : ∑ i ∈ S', (y (i + m) ^ (q' / 2)) ^ 2 = ∑ i ∈ S', y (i + m) ^ q' :=
      Finset.sum_congr rfl fun i hi => rpow_two_mul_half (hy (i + m) (hm i hi))
    rw [heq]
    have hinj : Set.InjOn (fun i : ℤ => i + m) (S' : Set ℤ) := fun a _ b _ h => add_right_cancel h
    rw [← Finset.sum_image (f := fun j => y j ^ q') (g := fun i => i + m) (by
      intro a ha b hb h; exact hinj ha hb h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hm i hi
    · intro j hj _
      exact Real.rpow_nonneg (hy j hj) _
  rw [hsq1]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq2) (Real.sqrt_nonneg _)

lemma geom_sum_nat_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ d ∈ Finset.range N, r ^ d ≤ 1 / (1 - r) := by
  rw [geom_sum_eq hr1.ne]
  have h1 : 0 < 1 - r := sub_pos.mpr hr1
  have h2 : 0 ≤ r ^ N := pow_nonneg hr0 N
  have heq : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
    rw [show r ^ N - 1 = -(1 - r ^ N) by ring, show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
  rw [heq, div_le_div_iff_of_pos_right h1]
  linarith

lemma sum_natAbs_pow_le {M : Finset ℤ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ m ∈ M, r ^ m.natAbs ≤ 1 + 2 * r / (1 - r) := by
  by_cases hM : M.Nonempty
  · obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ m ∈ M, m.natAbs < D := by
      refine ⟨(M.image Int.natAbs).sup id + 1, fun m hm => ?_⟩
      have hle : m.natAbs ≤ (M.image Int.natAbs).sup id :=
        Finset.le_sup (f := id) (Finset.mem_image_of_mem Int.natAbs hm)
      omega
    let T : Finset ℤ := Finset.Ioo (-(D : ℤ)) (D : ℤ)
    have hMT : M ⊆ T := by
      intro m hm
      have h := hD m hm
      rw [Finset.mem_Ioo]
      omega
    have hsub : ∑ m ∈ M, r ^ m.natAbs ≤ ∑ m ∈ T, r ^ m.natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hMT (fun _ _ _ => pow_nonneg hr0 _)
    refine hsub.trans ?_
    have hsplit : ∑ m ∈ T, r ^ m.natAbs =
        r ^ (0 : ℕ) + ∑ d ∈ Finset.Ico 1 D, (r ^ d + r ^ d) := by
      have h0 : (0 : ℤ) ∈ T := by
        rw [Finset.mem_Ioo]
        have : 0 < D := by
          obtain ⟨m0, hm0⟩ := hM
          have := hD m0 hm0
          omega
        omega
      have hT_eq : T = insert 0 ((Finset.Ico 1 D).biUnion fun d => ({(d : ℤ), -(d : ℤ)} : Finset ℤ)) := by
        ext z
        simp only [T, Finset.mem_Ioo, Finset.mem_Ico, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_singleton]
        constructor
        · intro hz
          by_cases h0z : z = 0
          · exact Or.inl h0z
          · right
            have hpos : 1 ≤ z.natAbs := Int.natAbs_pos.mpr h0z
            have hlt : z.natAbs < D := by
              rcases Int.natAbs_eq z with h | h <;> omega
            refine ⟨z.natAbs, ⟨hpos, hlt⟩, ?_⟩
            rcases Int.natAbs_eq z with h | h
            · left; exact h
            · right; omega
        · rintro (rfl | ⟨d, ⟨hd1, hd2⟩, rfl | rfl⟩)
          · have : 0 < D := by
              obtain ⟨m0, hm0⟩ := hM
              have := hD m0 hm0
              omega
            omega
          · omega
          · omega
      rw [hT_eq, Finset.sum_insert]
      · simp only [Int.natAbs_zero]
        congr 1
        rw [Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.mem_Ico] at hd
          rw [Finset.sum_pair (by omega : (d : ℤ) ≠ -(d : ℤ))]
          simp
        · intro d1 hd1 d2 hd2 hne
          simp only [Finset.mem_coe, Finset.mem_Ico] at hd1 hd2
          rw [Function.onFun, Finset.disjoint_left]
          intro z hz1 hz2
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
          omega
      · simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
        rintro ⟨d, ⟨hd1, _⟩, h | h⟩ <;> omega
    rw [hsplit, pow_zero]
    have hsum2 : ∑ d ∈ Finset.Ico 1 D, (r ^ d + r ^ d) =
        2 * r * ∑ k ∈ Finset.range (D - 1), r ^ k := by
      have h1 : ∑ d ∈ Finset.Ico 1 D, (r ^ d + r ^ d) = 2 * ∑ d ∈ Finset.Ico 1 D, r ^ d := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by ring
      rw [h1, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      have hDpos : 1 ≤ D := by
        obtain ⟨m0, hm0⟩ := hM
        have := hD m0 hm0
        omega
      have hbij : ∑ d ∈ Finset.Ico 1 D, r ^ d = ∑ k ∈ Finset.range (D - 1), r ^ (k + 1) := by
        refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
        · intro d hd; rw [Finset.mem_Ico] at hd; rw [Finset.mem_range]; omega
        · intro d1 hd1 d2 hd2 h; rw [Finset.mem_Ico] at hd1 hd2; omega
        · intro k hk; rw [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro d hd; rw [Finset.mem_Ico] at hd; congr 1; omega
      rw [hbij]
      refine Finset.sum_congr rfl fun k _ => by rw [pow_succ']
    rw [hsum2]
    have hgeom := geom_sum_nat_le hr0 hr1 (D - 1)
    have hmul : 2 * r * ∑ k ∈ Finset.range (D - 1), r ^ k ≤ 2 * r * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    linarith [show 2 * r * (1 / (1 - r)) = 2 * r / (1 - r) by ring]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hM, Finset.sum_empty]
    have : 0 < 1 - r := sub_pos.mpr hr1
    positivity

lemma sum_natAbs_pow_ne_zero_le {M : Finset ℤ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h0 : (0 : ℤ) ∉ M) :
    ∑ m ∈ M, r ^ m.natAbs ≤ 2 * r / (1 - r) := by
  have h := sum_natAbs_pow_le (M := insert 0 M) hr0 hr1
  rw [Finset.sum_insert h0, Int.natAbs_zero, pow_zero] at h
  linarith

lemma sum_natAbs_ge_two_le {M : Finset ℤ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h2 : ∀ m ∈ M, 2 ≤ m.natAbs) :
    ∑ m ∈ M, r ^ (m.natAbs - 2) ≤ 2 / (1 - r) := by
  have h1 : ∑ m ∈ M, r ^ (m.natAbs - 2) * r ^ 2 = ∑ m ∈ M, r ^ m.natAbs := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← pow_add, Nat.sub_add_cancel (h2 m hm)]
  by_cases hr : r = 0
  · subst hr
    have hsub : M ⊆ ({(2 : ℤ), -(2 : ℤ)} : Finset ℤ) ∪ M.filter (fun m => 3 ≤ m.natAbs) := by
      intro m hm
      have := h2 m hm
      by_cases h3 : 3 ≤ m.natAbs
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, h3⟩)
      · refine Finset.mem_union_left _ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    have h0' : ∑ m ∈ M, (0 : ℝ) ^ (m.natAbs - 2) ≤
        ∑ m ∈ M.filter (fun m => m.natAbs = 2), (1 : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not M (fun m => m.natAbs = 2)]
      have hzero : ∑ m ∈ M.filter (fun m => ¬ m.natAbs = 2), (0 : ℝ) ^ (m.natAbs - 2) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [Finset.mem_filter] at hm
        have := h2 m hm.1
        rw [zero_pow (by omega)]
      rw [hzero, add_zero]
      refine le_of_eq (Finset.sum_congr rfl fun m hm => ?_)
      rw [Finset.mem_filter] at hm
      simp [hm.2]
    have hcard : (M.filter (fun m => m.natAbs = 2)).card ≤ 2 := by
      have hsub2 : M.filter (fun m => m.natAbs = 2) ⊆ ({(2 : ℤ), -(2 : ℤ)} : Finset ℤ) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub2).trans (by decide)
    calc ∑ m ∈ M, (0 : ℝ) ^ (m.natAbs - 2)
        ≤ (M.filter (fun m => m.natAbs = 2)).card := by simpa using h0'
      _ ≤ 2 := by exact_mod_cast hcard
      _ = 2 / (1 - 0) := by norm_num
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hnot0 : (0 : ℤ) ∉ M := fun h => by have := h2 0 h; simp at this
    have hnot1 : (1 : ℤ) ∉ M := fun h => by have := h2 1 h; simp at this
    have hnotm1 : (-1 : ℤ) ∉ M := fun h => by have := h2 (-1) h; simp at this
    have hall := sum_natAbs_pow_le (M := insert 0 (insert 1 (insert (-1) M))) hr0 hr1
    rw [Finset.sum_insert (by simp [hnot0]),
        Finset.sum_insert (by simp [hnot1]),
        Finset.sum_insert (by simp [hnotm1])] at hall
    simp only [Int.natAbs_zero, pow_zero, Int.natAbs_one, pow_one,
      show (-1 : ℤ).natAbs = 1 by decide] at hall
    have hMsum : ∑ m ∈ M, r ^ m.natAbs ≤ 2 * r ^ 2 / (1 - r) := by
      have hpos1 : 0 < 1 - r := sub_pos.mpr hr1
      have hid : 2 * r / (1 - r) - 2 * r = 2 * r ^ 2 / (1 - r) := by
        field_simp; ring
      linarith
    rw [← h1, ← Finset.sum_mul] at hMsum
    have hr2pos : 0 < r ^ 2 := pow_pos hrpos 2
    have hmul : (∑ m ∈ M, r ^ (m.natAbs - 2)) * r ^ 2 ≤ (2 / (1 - r)) * r ^ 2 := by
      linarith [show (2 / (1 - r)) * r ^ 2 = 2 * r ^ 2 / (1 - r) by ring]
    exact le_of_mul_le_mul_right hmul hr2pos

end Helpers

section Concentration

/-- Explicit constant C_Q for Green-Walker Lemma 2.1 (Hu-Jing Lemma 6.1). -/
noncomputable def gwConst (Q : ℝ) : ℝ :=
  let q' := Q / (Q - 1)
  let B := 60 / (1 - q' / 2)
  11 * (2 : ℝ) ^ (2 / q') * B ^ (2 * Q - 2) + 6 * (2 : ℝ) ^ (1 / q') * B ^ (Q - 1)

lemma gwConst_pos {Q : ℝ} (hQ2 : 2 < Q) : 0 < gwConst Q := by
  unfold gwConst
  dsimp only
  have hQ1 : 0 < Q - 1 := by linarith
  have hq'2 : Q / (Q - 1) / 2 < 1 := by
    rw [div_lt_one (by norm_num), div_lt_iff₀ hQ1]
    linarith
  have hden : 0 < 1 - Q / (Q - 1) / 2 := sub_pos.mpr hq'2
  have hB : 0 < 60 / (1 - Q / (Q - 1) / 2) := div_pos (by norm_num) hden
  positivity

set_option maxHeartbeats 800000 in
/-- Green-Walker Lemma 2.1 / Hu-Jing Lemma 6.1 on a finite support S ⊆ ℤ. -/
theorem gw_concentration {Q : ℝ} (hQ2 : 2 < Q) (hQ3 : Q < 3)
    (S : Finset ℤ) (α β : ℤ → ℝ) (μ : ℤ × ℤ → ℝ)
    (hα0 : ∀ i ∈ S, 0 ≤ α i) (hβ0 : ∀ j ∈ S, 0 ≤ β j)
    (hα1 : ∑ i ∈ S, α i = 1) (hβ1 : ∑ j ∈ S, β j = 1)
    (hμ0 : ∀ p ∈ S ×ˢ S, 0 ≤ μ p) (hμ1 : ∑ p ∈ S ×ˢ S, μ p = 1)
    {c lam : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hlam0 : 0 < lam) (hlam1 : lam ≤ 4 / 5)
    (hμ : ∀ i ∈ S, ∀ j ∈ S, μ (i, j) ≤ c * lam ^ (i - j).natAbs * (α i * β j) ^ (1 - 1 / Q)) :
    (1 / 9 : ℝ) ≤ c ∧
      ∃ k ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun p => 2 ≤ (p.1 - k).natAbs + (p.2 - k).natAbs), μ p ≤
        gwConst Q * lam ^ (2 * Q - 2) := by
  have hQpos : 0 < Q := by linarith
  have hQ1 : 0 < Q - 1 := by linarith
  set q' : ℝ := Q / (Q - 1) with hq'_def
  have hq'pos : 0 < q' := div_pos hQpos hQ1
  have hq'gt1 : 1 < q' := by
    rw [hq'_def, one_lt_div hQ1]; linarith
  have hq'lt2 : q' < 2 := by
    rw [hq'_def, div_lt_iff₀ hQ1]; linarith
  have h1q' : 1 / q' = 1 - 1 / Q := by
    rw [hq'_def]; field_simp
  have hq'half_lt1 : q' / 2 < 1 := by linarith
  have hq'half_pos : 0 < q' / 2 := by linarith
  have hlam_lt1 : lam < 1 := by linarith
  have hS_ne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hα1
    norm_num at hα1
  let x : ℤ → ℝ := fun i => (α i) ^ (1 / q')
  let y : ℤ → ℝ := fun j => (β j) ^ (1 / q')
  have hx0 : ∀ i ∈ S, 0 ≤ x i := fun i hi => Real.rpow_nonneg (hα0 i hi) _
  have hy0 : ∀ j ∈ S, 0 ≤ y j := fun j hj => Real.rpow_nonneg (hβ0 j hj) _
  have hxq' : ∀ i ∈ S, x i ^ q' = α i := fun i hi => by
    dsimp only [x]
    rw [← Real.rpow_mul (hα0 i hi), one_div_mul_cancel hq'pos.ne', Real.rpow_one]
  have hyq' : ∀ j ∈ S, y j ^ q' = β j := fun j hj => by
    dsimp only [y]
    rw [← Real.rpow_mul (hβ0 j hj), one_div_mul_cancel hq'pos.ne', Real.rpow_one]
  have hxsum : ∑ i ∈ S, x i ^ q' = 1 := by
    rw [Finset.sum_congr rfl hxq', hα1]
  have hysum : ∑ j ∈ S, y j ^ q' = 1 := by
    rw [Finset.sum_congr rfl hyq', hβ1]
  have hxle1 : ∀ i ∈ S, x i ≤ 1 := fun i hi => by
    have hαle1 : α i ≤ 1 := by
      rw [← hα1]
      exact Finset.single_le_sum hα0 hi
    exact Real.rpow_le_one (hα0 i hi) hαle1 (by positivity)
  have hyle1 : ∀ j ∈ S, y j ≤ 1 := fun j hj => by
    have hβle1 : β j ≤ 1 := by
      rw [← hβ1]
      exact Finset.single_le_sum hβ0 hj
    exact Real.rpow_le_one (hβ0 j hj) hβle1 (by positivity)
  have hμxy : ∀ i ∈ S, ∀ j ∈ S, μ (i, j) ≤ c * lam ^ (i - j).natAbs * (x i * y j) := by
    intro i hi j hj
    have h := hμ i hi j hj
    rw [← h1q', Real.mul_rpow (hα0 i hi) (hβ0 j hj)] at h
    exact h
  -- Part 1: 1/9 ≤ c
  have hc_lb : (1 / 9 : ℝ) ≤ c := by
    let M : Finset ℤ := (S ×ˢ S).image (fun p => p.2 - p.1)
    have hpart : ∑ p ∈ S ×ˢ S, μ p =
        ∑ m ∈ M, ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 - p.1 = m), μ p := by
      exact (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp) μ).symm
    have hfiber : ∀ m ∈ M,
        ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 - p.1 = m), μ p ≤ c * lam ^ m.natAbs := by
      intro m _
      let S_m : Finset ℤ := S.filter (fun i => i + m ∈ S)
      have hbij : ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 - p.1 = m), μ p =
          ∑ i ∈ S_m, μ (i, i + m) := by
        refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_product, S_m] at hp ⊢
          exact ⟨hp.1.1, by rw [show p.1 + m = p.2 by omega]; exact hp.1.2⟩
        · intro p1 hp1 p2 hp2 h
          simp only [Finset.mem_filter] at hp1 hp2
          ext
          · exact h
          · omega
        · intro i hi
          simp only [Finset.mem_filter, S_m] at hi
          refine ⟨(i, i + m), ?_, rfl⟩
          simp [hi.1, hi.2]
        · intro p hp
          simp only [Finset.mem_filter] at hp
          congr 1; ext <;> [rfl; omega]
      rw [hbij]
      calc ∑ i ∈ S_m, μ (i, i + m)
          ≤ ∑ i ∈ S_m, c * lam ^ m.natAbs * (x i * y (i + m)) ^ (q' / 2) := by
            refine Finset.sum_le_sum fun i hi => ?_
            simp only [Finset.mem_filter, S_m] at hi
            have h1 := hμxy i hi.1 (i + m) hi.2
            have habs : (i - (i + m)).natAbs = m.natAbs := by
              rw [show i - (i + m) = -m by ring, Int.natAbs_neg]
            rw [habs] at h1
            have hxy0 : 0 ≤ x i * y (i + m) := mul_nonneg (hx0 i hi.1) (hy0 _ hi.2)
            have hxy1 : x i * y (i + m) ≤ 1 := mul_le_one₀ (hxle1 i hi.1) (hy0 _ hi.2) (hyle1 _ hi.2)
            have hrpow : x i * y (i + m) ≤ (x i * y (i + m)) ^ (q' / 2) := by
              by_cases hz : x i * y (i + m) = 0
              · rw [hz, Real.zero_rpow hq'half_pos.ne']
              · have hpos : 0 < x i * y (i + m) := lt_of_le_of_ne hxy0 (Ne.symm hz)
                simpa using Real.rpow_le_rpow_of_exponent_ge hpos hxy1 hq'half_lt1.le
            exact h1.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))
        _ = c * lam ^ m.natAbs * ∑ i ∈ S_m, (x i * y (i + m)) ^ (q' / 2) := by
            rw [Finset.mul_sum]
        _ ≤ c * lam ^ m.natAbs * (Real.sqrt (∑ i ∈ S_m, x i ^ q') * Real.sqrt (∑ j ∈ S, y j ^ q')) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_rpow_half_cs (fun i hi => hx0 i (Finset.mem_filter.mp hi).1) hy0 m
              (fun i hi => (Finset.mem_filter.mp hi).2)
        _ ≤ c * lam ^ m.natAbs * (Real.sqrt 1 * Real.sqrt 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hxsub : ∑ i ∈ S_m, x i ^ q' ≤ 1 := by
              rw [← hxsum]
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun i hi _ => Real.rpow_nonneg (hx0 i hi) _)
            rw [hysum]
            exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxsub) (Real.sqrt_nonneg _)
        _ = c * lam ^ m.natAbs := by simp
    have htotal : (1 : ℝ) ≤ c * 9 := by
      calc (1 : ℝ) = ∑ p ∈ S ×ˢ S, μ p := hμ1.symm
        _ = ∑ m ∈ M, ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 - p.1 = m), μ p := hpart
        _ ≤ ∑ m ∈ M, c * lam ^ m.natAbs := Finset.sum_le_sum hfiber
        _ = c * ∑ m ∈ M, lam ^ m.natAbs := by rw [Finset.mul_sum]
        _ ≤ c * (1 + 2 * lam / (1 - lam)) :=
            mul_le_mul_of_nonneg_left (sum_natAbs_pow_le hlam0.le hlam_lt1) hc0.le
        _ ≤ c * 9 := by
            refine mul_le_mul_of_nonneg_left ?_ hc0.le
            have h1mlam : 0 < 1 - lam := by linarith
            rw [show (9 : ℝ) = 1 + 8 by norm_num]
            have : 2 * lam / (1 - lam) ≤ 8 := by
              rw [div_le_iff₀ h1mlam]; linarith
            linarith
    linarith
  refine ⟨hc_lb, ?_⟩
  -- Part 2: Concentration around maximizer k ∈ S of x i * y i
  obtain ⟨k, hkS, hkmax⟩ := Finset.exists_max_image S (fun i => x i * y i) hS_ne
  refine ⟨k, hkS, ?_⟩
  set γ : ℝ := 1 - x k * y k with hγ_def
  have hγ0 : 0 ≤ γ := by
    have : x k * y k ≤ 1 := mul_le_one₀ (hxle1 k hkS) (hy0 k hkS) (hyle1 k hkS)
    linarith
  have hγ1 : γ ≤ 1 := by
    have : 0 ≤ x k * y k := mul_nonneg (hx0 k hkS) (hy0 k hkS)
    linarith
  have hxk_ge : 1 - γ ≤ x k := by
    have : x k * y k ≤ x k * 1 := mul_le_mul_of_nonneg_left (hyle1 k hkS) (hx0 k hkS)
    linarith
  have hyk_ge : 1 - γ ≤ y k := by
    have : x k * y k ≤ 1 * y k := mul_le_mul_of_nonneg_right (hxle1 k hkS) (hy0 k hkS)
    linarith
  have h1mγ_ge : 1 - 2 * γ ≤ (1 - γ) ^ q' := by
    have h1mγ0 : 0 ≤ 1 - γ := by linarith
    have h1mγ1 : 1 - γ ≤ 1 := by linarith
    have hpow : (1 - γ) ^ (2 : ℝ) ≤ (1 - γ) ^ q' := by
      by_cases hz : 1 - γ = 0
      · rw [hz, Real.zero_rpow (by norm_num), Real.zero_rpow hq'pos.ne']
      · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne h1mγ0 (Ne.symm hz)) h1mγ1 hq'lt2.le
    have hsq : (1 - γ) ^ (2 : ℝ) = (1 - γ) ^ (2 : ℕ) := Real.rpow_two (1 - γ)
    rw [hsq] at hpow
    nlinarith
  have hx_tail : ∑ i ∈ S.erase k, x i ^ q' ≤ 2 * γ := by
    have h1 : x k ^ q' + ∑ i ∈ S.erase k, x i ^ q' = 1 := by
      rw [Finset.add_sum_erase S (fun i => x i ^ q') hkS, hxsum]
    have h2 : (1 - γ) ^ q' ≤ x k ^ q' := Real.rpow_le_rpow (by linarith) hxk_ge hq'pos.le
    linarith
  have hy_tail : ∑ j ∈ S.erase k, y j ^ q' ≤ 2 * γ := by
    have h1 : y k ^ q' + ∑ j ∈ S.erase k, y j ^ q' = 1 := by
      rw [Finset.add_sum_erase S (fun j => y j ^ q') hkS, hysum]
    have h2 : (1 - γ) ^ q' ≤ y k ^ q' := Real.rpow_le_rpow (by linarith) hyk_ge hq'pos.le
    linarith
  have hx_pt : ∀ i ∈ S.erase k, x i ≤ (2 * γ) ^ (1 / q') := by
    intro i hi
    have hiS : i ∈ S := Finset.mem_of_mem_erase hi
    have hle : x i ^ q' ≤ 2 * γ :=
      (Finset.single_le_sum (fun u hu => Real.rpow_nonneg (hx0 u (Finset.mem_of_mem_erase hu)) _) hi).trans hx_tail
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (hx0 i hiS) _) hle (by positivity : (0 : ℝ) ≤ 1 / q')
    rwa [← Real.rpow_mul (hx0 i hiS), mul_one_div_cancel hq'pos.ne', Real.rpow_one] at hpow
  have hy_pt : ∀ j ∈ S.erase k, y j ≤ (2 * γ) ^ (1 / q') := by
    intro j hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hle : y j ^ q' ≤ 2 * γ :=
      (Finset.single_le_sum (fun u hu => Real.rpow_nonneg (hy0 u (Finset.mem_of_mem_erase hu)) _) hj).trans hy_tail
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (hy0 j hjS) _) hle (by positivity : (0 : ℝ) ≤ 1 / q')
    rwa [← Real.rpow_mul (hy0 j hjS), mul_one_div_cancel hq'pos.ne', Real.rpow_one] at hpow
  -- Trivial case γ = 0
  by_cases hγz : γ = 0
  · have hzero : ∑ p ∈ (S ×ˢ S).filter (fun p => 2 ≤ (p.1 - k).natAbs + (p.2 - k).natAbs), μ p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      have hne : p.1 ≠ k ∨ p.2 ≠ k := by
        by_contra h
        push Not at h
        rw [h.1, h.2, sub_self, Int.natAbs_zero] at hp
        omega
      have hprod0 : x p.1 * y p.2 = 0 := by
        rcases hne with h1 | h2
        · have hxle := hx_pt p.1 (Finset.mem_erase.mpr ⟨h1, hp.1.1⟩)
          rw [hγz, mul_zero, Real.zero_rpow (by positivity)] at hxle
          have : x p.1 = 0 := le_antisymm hxle (hx0 p.1 hp.1.1)
          rw [this, zero_mul]
        · have hyle := hy_pt p.2 (Finset.mem_erase.mpr ⟨h2, hp.1.2⟩)
          rw [hγz, mul_zero, Real.zero_rpow (by positivity)] at hyle
          have : y p.2 = 0 := le_antisymm hyle (hy0 p.2 hp.1.2)
          rw [this, mul_zero]
      have hle := hμxy p.1 hp.1.1 p.2 hp.1.2
      rw [hprod0, mul_zero] at hle
      exact le_antisymm hle (hμ0 p (Finset.mem_product.mpr hp.1))
    rw [hzero]
    exact mul_nonneg (gwConst_pos hQ2).le (Real.rpow_nonneg hlam0.le _)
  have hγpos : 0 < γ := lt_of_le_of_ne hγ0 (Ne.symm hγz)
  have h2γpos : 0 < 2 * γ := by positivity
  have hμ1' : ∀ i ∈ S, ∀ j ∈ S, μ (i, j) ≤ lam ^ (i - j).natAbs * (x i * y j) := by
    intro i hi j hj
    have h := hμxy i hi j hj
    calc μ (i, j) ≤ c * lam ^ (i - j).natAbs * (x i * y j) := h
      _ ≤ 1 * lam ^ (i - j).natAbs * (x i * y j) := by
          gcongr
          exact mul_nonneg (hx0 i hi) (hy0 j hj)
      _ = lam ^ (i - j).natAbs * (x i * y j) := by ring
  -- Define the 6 sets partitioning S ×ˢ S
  let S1 := (S ×ˢ S).filter (fun p => p.1 ≠ k ∧ p.2 ≠ k ∧ p.1 ≠ p.2)
  let S2 := (S ×ˢ S).filter (fun p => p.1 = k ∧ 2 ≤ (p.2 - k).natAbs)
  let S3 := (S ×ˢ S).filter (fun p => p.2 = k ∧ 2 ≤ (p.1 - k).natAbs)
  let S4 := (S ×ˢ S).filter (fun p =>
    (p.1 = k ∧ (p.2 - k).natAbs = 1) ∨ (p.2 = k ∧ (p.1 - k).natAbs = 1))
  let S5 := (S ×ˢ S).filter (fun p => p.1 = p.2 ∧ p.1 ≠ k)
  let S56 := (S ×ˢ S).filter (fun p => p.1 = p.2)
  -- Bound B1
  have hB1 : ∑ p ∈ S1, μ p ≤ 10 * lam * (2 * γ) ^ (2 / q') := by
    let M1 : Finset ℤ := S1.image (fun p => p.2 - p.1)
    have h0M1 : (0 : ℤ) ∉ M1 := by
      simp only [M1, Finset.mem_image, S1, Finset.mem_filter]
      rintro ⟨p, ⟨_, _, _, hne⟩, heq⟩
      omega
    have hpart : ∑ p ∈ S1, μ p = ∑ m ∈ M1, ∑ p ∈ S1.filter (fun p => p.2 - p.1 = m), μ p :=
      (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp) μ).symm
    have hfib : ∀ m ∈ M1,
        ∑ p ∈ S1.filter (fun p => p.2 - p.1 = m), μ p ≤ lam ^ m.natAbs * (2 * γ) ^ (2 / q') := by
      intro m _
      let T : Finset ℤ := (S.erase k).filter (fun i => i + m ∈ S.erase k ∧ i ≠ i + m)
      have hbij : ∑ p ∈ S1.filter (fun p => p.2 - p.1 = m), μ p = ∑ i ∈ T, μ (i, i + m) := by
        refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, S1, Finset.mem_product, T, Finset.mem_erase] at hp ⊢
          refine ⟨⟨hp.1.2.1, hp.1.1.1⟩, ⟨?_, ?_⟩, ?_⟩
          · have : p.1 + m = p.2 := by omega
            rw [this]; exact hp.1.2.2.1
          · have : p.1 + m = p.2 := by omega
            rw [this]; exact hp.1.1.2
          · omega
        · intro p1 hp1 p2 hp2 h
          simp only [Finset.mem_filter] at hp1 hp2
          ext <;> [exact h; omega]
        · intro i hi
          simp only [Finset.mem_filter, T, Finset.mem_erase] at hi
          refine ⟨(i, i + m), ?_, rfl⟩
          simp [S1, hi.1.1, hi.1.2, hi.2.1.1, hi.2.1.2, hi.2.2]
        · intro p hp
          simp only [Finset.mem_filter] at hp
          congr 1; ext <;> [rfl; omega]
      rw [hbij]
      have hpt : ∀ i ∈ T, μ (i, i + m) ≤
          lam ^ m.natAbs * (2 * γ) ^ (2 / q' - 1) * (x i * y (i + m)) ^ (q' / 2) := by
        intro i hi
        simp only [Finset.mem_filter, T, Finset.mem_erase] at hi
        have h1 := hμ1' i hi.1.2 (i + m) hi.2.1.2
        rw [show (i - (i + m)).natAbs = m.natAbs by
          rw [show i - (i + m) = -m by ring, Int.natAbs_neg]] at h1
        have hxy_le : x i * y (i + m) ≤ (2 * γ) ^ (2 / q') := by
          have h1' := hx_pt i (Finset.mem_erase.mpr hi.1)
          have h2' := hy_pt (i + m) (Finset.mem_erase.mpr hi.2.1)
          calc x i * y (i + m)
              ≤ (2 * γ) ^ (1 / q') * (2 * γ) ^ (1 / q') :=
                mul_le_mul h1' h2' (hy0 _ hi.2.1.2) (Real.rpow_nonneg h2γpos.le _)
            _ = (2 * γ) ^ (2 / q') := by
                rw [← Real.rpow_add h2γpos]; congr 1; ring
        have hxy0 : 0 ≤ x i * y (i + m) := mul_nonneg (hx0 i hi.1.2) (hy0 _ hi.2.1.2)
        have hdecomp : x i * y (i + m) ≤ (2 * γ) ^ (2 / q' - 1) * (x i * y (i + m)) ^ (q' / 2) := by
          have hpow1 : (x i * y (i + m)) ^ (1 - q' / 2) ≤ ((2 * γ) ^ (2 / q')) ^ (1 - q' / 2) :=
            Real.rpow_le_rpow hxy0 hxy_le (by linarith)
          rw [← Real.rpow_mul h2γpos.le,
              show 2 / q' * (1 - q' / 2) = 2 / q' - 1 by field_simp] at hpow1
          calc x i * y (i + m)
              = (x i * y (i + m)) ^ (1 - q' / 2) * (x i * y (i + m)) ^ (q' / 2) := by
                by_cases hz : x i * y (i + m) = 0
                · rw [hz, Real.zero_rpow (by linarith), zero_mul]
                · rw [← Real.rpow_add (lt_of_le_of_ne hxy0 (Ne.symm hz)),
                      sub_add_cancel, Real.rpow_one]
            _ ≤ (2 * γ) ^ (2 / q' - 1) * (x i * y (i + m)) ^ (q' / 2) :=
                mul_le_mul_of_nonneg_right hpow1 (Real.rpow_nonneg hxy0 _)
        calc μ (i, i + m)
            ≤ lam ^ m.natAbs * (x i * y (i + m)) := h1
          _ ≤ lam ^ m.natAbs * ((2 * γ) ^ (2 / q' - 1) * (x i * y (i + m)) ^ (q' / 2)) :=
              mul_le_mul_of_nonneg_left hdecomp (pow_nonneg hlam0.le _)
          _ = lam ^ m.natAbs * (2 * γ) ^ (2 / q' - 1) * (x i * y (i + m)) ^ (q' / 2) := by ring
      calc ∑ i ∈ T, μ (i, i + m)
          ≤ ∑ i ∈ T, lam ^ m.natAbs * (2 * γ) ^ (2 / q' - 1) * (x i * y (i + m)) ^ (q' / 2) :=
            Finset.sum_le_sum hpt
        _ = lam ^ m.natAbs * (2 * γ) ^ (2 / q' - 1) * ∑ i ∈ T, (x i * y (i + m)) ^ (q' / 2) := by
            rw [Finset.mul_sum]
        _ ≤ lam ^ m.natAbs * (2 * γ) ^ (2 / q' - 1) *
              (Real.sqrt (∑ i ∈ T, x i ^ q') * Real.sqrt (∑ j ∈ S.erase k, y j ^ q')) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_rpow_half_cs
              (fun i hi => hx0 i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1))
              (fun j hj => hy0 j (Finset.mem_of_mem_erase hj))
              m (fun i hi => (Finset.mem_filter.mp hi).2.1)
        _ ≤ lam ^ m.natAbs * (2 * γ) ^ (2 / q' - 1) * (Real.sqrt (2 * γ) * Real.sqrt (2 * γ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hxT : ∑ i ∈ T, x i ^ q' ≤ 2 * γ :=
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun i hi _ => Real.rpow_nonneg (hx0 i (Finset.mem_of_mem_erase hi)) _)).trans hx_tail
            exact mul_le_mul (Real.sqrt_le_sqrt hxT) (Real.sqrt_le_sqrt hy_tail)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = lam ^ m.natAbs * (2 * γ) ^ (2 / q') := by
            rw [Real.mul_self_sqrt h2γpos.le, mul_assoc]
            congr 1
            rw [show (2 * γ) ^ (2 / q') = (2 * γ) ^ (2 / q' - 1) * (2 * γ) by
              rw [← Real.rpow_add_one h2γpos.ne', sub_add_cancel]]
    calc ∑ p ∈ S1, μ p
        = ∑ m ∈ M1, ∑ p ∈ S1.filter (fun p => p.2 - p.1 = m), μ p := hpart
      _ ≤ ∑ m ∈ M1, lam ^ m.natAbs * (2 * γ) ^ (2 / q') := Finset.sum_le_sum hfib
      _ = (∑ m ∈ M1, lam ^ m.natAbs) * (2 * γ) ^ (2 / q') := by rw [Finset.sum_mul]
      _ ≤ (2 * lam / (1 - lam)) * (2 * γ) ^ (2 / q') :=
          mul_le_mul_of_nonneg_right (sum_natAbs_pow_ne_zero_le hlam0.le hlam_lt1 h0M1)
            (Real.rpow_nonneg h2γpos.le _)
      _ ≤ 10 * lam * (2 * γ) ^ (2 / q') := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg h2γpos.le _)
          have h1mlam : 0 < 1 - lam := by linarith
          rw [div_le_iff₀ h1mlam]; nlinarith [hlam0, hlam1]
  -- Helper for B2 and B3
  have hB23_aux : ∀ (w : ℤ → ℝ), (∀ j ∈ S, 0 ≤ w j) →
      (∑ j ∈ S.erase k, w j ^ q' ≤ 2 * γ) →
      (∀ j ∈ S.erase k, w j ≤ (2 * γ) ^ (1 / q')) →
      ∑ j ∈ S.filter (fun j => 2 ≤ (j - k).natAbs), lam ^ (j - k).natAbs * w j ≤
        3 * lam ^ 2 * (2 * γ) ^ (1 / q') := by
    intro w hw0 hw_tail hw_pt
    let J := S.filter (fun j => 2 ≤ (j - k).natAbs)
    have hJsub : J ⊆ S.erase k := by
      intro j hj
      simp only [J, Finset.mem_filter, Finset.mem_erase] at hj ⊢
      exact ⟨by intro heq; rw [heq, sub_self, Int.natAbs_zero] at hj; omega, hj.1⟩
    have hpt : ∀ j ∈ J, lam ^ (j - k).natAbs * w j ≤
        lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) * ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2) * w j ^ (q' / 2)) := by
      intro j hj
      have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
      have hge2 : 2 ≤ (j - k).natAbs := (Finset.mem_filter.mp hj).2
      have hlam_bd : lam ^ (j - k).natAbs ≤ lam ^ 2 * (4 / 5 : ℝ) ^ ((j - k).natAbs - 2) := by
        calc lam ^ (j - k).natAbs
            = lam ^ (2 + ((j - k).natAbs - 2)) := by congr 1; omega
          _ = lam ^ 2 * lam ^ ((j - k).natAbs - 2) := pow_add _ _ _
          _ ≤ lam ^ 2 * (4 / 5 : ℝ) ^ ((j - k).natAbs - 2) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlam0.le hlam1 _) (pow_nonneg hlam0.le 2)
      have hw_decomp : w j ≤ (2 * γ) ^ (1 / q' - 1 / 2) * w j ^ (q' / 2) := by
        have h1 : w j ^ (1 - q' / 2) ≤ ((2 * γ) ^ (1 / q')) ^ (1 - q' / 2) :=
          Real.rpow_le_rpow (hw0 j hjS) (hw_pt j (hJsub hj)) (by linarith)
        rw [← Real.rpow_mul h2γpos.le,
            show 1 / q' * (1 - q' / 2) = 1 / q' - 1 / 2 by field_simp] at h1
        calc w j
            = w j ^ (1 - q' / 2) * w j ^ (q' / 2) := by
              by_cases hz : w j = 0
              · rw [hz, Real.zero_rpow (by linarith), zero_mul]
              · rw [← Real.rpow_add (lt_of_le_of_ne (hw0 j hjS) (Ne.symm hz)),
                    sub_add_cancel, Real.rpow_one]
          _ ≤ (2 * γ) ^ (1 / q' - 1 / 2) * w j ^ (q' / 2) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hw0 j hjS) _)
      calc lam ^ (j - k).natAbs * w j
          ≤ (lam ^ 2 * (4 / 5 : ℝ) ^ ((j - k).natAbs - 2)) *
              ((2 * γ) ^ (1 / q' - 1 / 2) * w j ^ (q' / 2)) :=
            mul_le_mul hlam_bd hw_decomp (hw0 j hjS) (by positivity)
        _ = lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) *
              ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2) * w j ^ (q' / 2)) := by ring
    calc ∑ j ∈ J, lam ^ (j - k).natAbs * w j
        ≤ ∑ j ∈ J, lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) *
            ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2) * w j ^ (q' / 2)) := Finset.sum_le_sum hpt
      _ = lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) *
            ∑ j ∈ J, (4 / 5 : ℝ) ^ ((j - k).natAbs - 2) * w j ^ (q' / 2) := by rw [Finset.mul_sum]
      _ ≤ lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) *
            (Real.sqrt (∑ j ∈ J, ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2)) ^ 2) *
             Real.sqrt (∑ j ∈ J, (w j ^ (q' / 2)) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.sum_mul_le_sqrt_mul_sqrt J _ _
      _ ≤ lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) * (3 * Real.sqrt (2 * γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hgeom : ∑ j ∈ J, ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2)) ^ 2 ≤ 9 := by
            let MJ := J.image (fun j => j - k)
            have hinj : Set.InjOn (fun j : ℤ => j - k) (J : Set ℤ) := fun a _ b _ h => sub_left_inj.mp h
            have heq : ∑ j ∈ J, ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2)) ^ 2 =
                ∑ m ∈ MJ, (16 / 25 : ℝ) ^ (m.natAbs - 2) := by
              rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← pow_mul, mul_comm, pow_mul]; norm_num
            rw [heq]
            have hge2 : ∀ m ∈ MJ, 2 ≤ m.natAbs := by
              intro m hm
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
              exact (Finset.mem_filter.mp hj).2
            have hbd := sum_natAbs_ge_two_le (M := MJ) (r := (16 / 25 : ℝ)) (by norm_num) (by norm_num) hge2
            linarith
          have hwJ : ∑ j ∈ J, (w j ^ (q' / 2)) ^ 2 ≤ 2 * γ := by
            have heq : ∑ j ∈ J, (w j ^ (q' / 2)) ^ 2 = ∑ j ∈ J, w j ^ q' :=
              Finset.sum_congr rfl fun j hj => rpow_two_mul_half (hw0 j (Finset.mem_filter.mp hj).1)
            rw [heq]
            exact (Finset.sum_le_sum_of_subset_of_nonneg hJsub
              (fun j hj _ => Real.rpow_nonneg (hw0 j (Finset.mem_of_mem_erase hj)) _)).trans hw_tail
          have hsq3 : Real.sqrt (∑ j ∈ J, ((4 / 5 : ℝ) ^ ((j - k).natAbs - 2)) ^ 2) ≤ 3 := by
            calc Real.sqrt _ ≤ Real.sqrt 9 := Real.sqrt_le_sqrt hgeom
              _ = 3 := by norm_num
          exact mul_le_mul hsq3 (Real.sqrt_le_sqrt hwJ) (Real.sqrt_nonneg _) (by norm_num)
      _ = 3 * lam ^ 2 * (2 * γ) ^ (1 / q') := by
          rw [Real.sqrt_eq_rpow]
          have hadd : (2 * γ) ^ (1 / q' - 1 / 2) * (2 * γ) ^ (1 / 2 : ℝ) = (2 * γ) ^ (1 / q') := by
            rw [← Real.rpow_add h2γpos]; congr 1; ring
          calc lam ^ 2 * (2 * γ) ^ (1 / q' - 1 / 2) * (3 * (2 * γ) ^ (1 / 2 : ℝ))
              = 3 * lam ^ 2 * ((2 * γ) ^ (1 / q' - 1 / 2) * (2 * γ) ^ (1 / 2 : ℝ)) := by ring
            _ = 3 * lam ^ 2 * (2 * γ) ^ (1 / q') := by rw [hadd]
  -- Bound B2
  have hB2 : ∑ p ∈ S2, μ p ≤ 3 * lam ^ 2 * (2 * γ) ^ (1 / q') := by
    have hbij : ∑ p ∈ S2, μ p = ∑ j ∈ S.filter (fun j => 2 ≤ (j - k).natAbs), μ (k, j) := by
      refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
      · intro p hp; simp only [S2, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨hp.1.2, hp.2.2⟩
      · intro p1 hp1 p2 hp2 h; simp only [S2, Finset.mem_filter] at hp1 hp2
        exact Prod.ext (hp1.2.1.trans hp2.2.1.symm) h
      · intro j hj; simp only [Finset.mem_filter] at hj
        exact ⟨(k, j), by simp [S2, hkS, hj.1, hj.2], rfl⟩
      · intro p hp; simp only [S2, Finset.mem_filter] at hp
        exact congrArg μ (Prod.ext hp.2.1 rfl)
    rw [hbij]
    refine (Finset.sum_le_sum fun j hj => ?_).trans (hB23_aux y hy0 hy_tail hy_pt)
    have hjS := (Finset.mem_filter.mp hj).1
    have h1 := hμ1' k hkS j hjS
    rw [show (k - j).natAbs = (j - k).natAbs by rw [← Int.natAbs_neg, neg_sub]] at h1
    calc μ (k, j) ≤ lam ^ (j - k).natAbs * (x k * y j) := h1
      _ ≤ lam ^ (j - k).natAbs * (1 * y j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hxle1 k hkS) (hy0 j hjS)) (pow_nonneg hlam0.le _)
      _ = lam ^ (j - k).natAbs * y j := by ring
  -- Bound B3
  have hB3 : ∑ p ∈ S3, μ p ≤ 3 * lam ^ 2 * (2 * γ) ^ (1 / q') := by
    have hbij : ∑ p ∈ S3, μ p = ∑ i ∈ S.filter (fun i => 2 ≤ (i - k).natAbs), μ (i, k) := by
      refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
      · intro p hp; simp only [S3, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨hp.1.1, hp.2.2⟩
      · intro p1 hp1 p2 hp2 h; simp only [S3, Finset.mem_filter] at hp1 hp2
        exact Prod.ext h (hp1.2.1.trans hp2.2.1.symm)
      · intro i hi; simp only [Finset.mem_filter] at hi
        exact ⟨(i, k), by simp [S3, hkS, hi.1, hi.2], rfl⟩
      · intro p hp; simp only [S3, Finset.mem_filter] at hp
        exact congrArg μ (Prod.ext rfl hp.2.1)
    rw [hbij]
    refine (Finset.sum_le_sum fun i hi => ?_).trans (hB23_aux x hx0 hx_tail hx_pt)
    have hiS := (Finset.mem_filter.mp hi).1
    have h1 := hμ1' i hiS k hkS
    calc μ (i, k) ≤ lam ^ (i - k).natAbs * (x i * y k) := h1
      _ ≤ lam ^ (i - k).natAbs * (x i * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hyle1 k hkS) (hx0 i hiS)) (pow_nonneg hlam0.le _)
      _ = lam ^ (i - k).natAbs * x i := by ring
  -- Bound B4
  have hB4 : ∑ p ∈ S4, μ p ≤ 4 * lam * (2 * γ) ^ (1 / q') := by
    have hcard : S4.card ≤ 4 := by
      let F : Finset (ℤ × ℤ) := {(k, k + 1), (k, k - 1), (k + 1, k), (k - 1, k)}
      have hsub : S4 ⊆ F := by
        intro p hp
        simp only [S4, Finset.mem_filter] at hp
        simp only [F, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        rcases hp.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have : p.2 = k + 1 ∨ p.2 = k - 1 := by omega
          rcases this with h | h <;> [left; (right; left)] <;> exact ⟨h1, h⟩
        · have : p.1 = k + 1 ∨ p.1 = k - 1 := by omega
          rcases this with h | h <;> [(right; right; left); (right; right; right)] <;> exact ⟨h, h1⟩
      have hF : F.card ≤ 4 := by
        have h1 := Finset.card_insert_le (k, k + 1) ({(k, k - 1), (k + 1, k), (k - 1, k)} : Finset (ℤ × ℤ))
        have h2 := Finset.card_insert_le (k, k - 1) ({(k + 1, k), (k - 1, k)} : Finset (ℤ × ℤ))
        have h3 := Finset.card_insert_le (k + 1, k) ({(k - 1, k)} : Finset (ℤ × ℤ))
        have h4 : ({(k - 1, k)} : Finset (ℤ × ℤ)).card = 1 := Finset.card_singleton _
        dsimp only [F]
        omega
      exact (Finset.card_le_card hsub).trans hF
    have hpt : ∀ p ∈ S4, μ p ≤ lam * (2 * γ) ^ (1 / q') := by
      intro p hp
      simp only [S4, Finset.mem_filter, Finset.mem_product] at hp
      have h1 := hμ1' p.1 hp.1.1 p.2 hp.1.2
      rcases hp.2 with ⟨hpk, hdist⟩ | ⟨hpk, hdist⟩
      · have habs : (p.1 - p.2).natAbs = 1 := by
          rw [hpk, ← Int.natAbs_neg, neg_sub, hdist]
        rw [habs, pow_one] at h1
        have hne : p.2 ≠ k := by intro h; rw [h, sub_self, Int.natAbs_zero] at hdist; omega
        calc μ p ≤ lam * (x p.1 * y p.2) := h1
          _ ≤ lam * (1 * (2 * γ) ^ (1 / q')) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hxle1 p.1 hp.1.1) (hy_pt p.2 (Finset.mem_erase.mpr ⟨hne, hp.1.2⟩))
                (hy0 p.2 hp.1.2) zero_le_one) hlam0.le
          _ = lam * (2 * γ) ^ (1 / q') := by ring
      · have habs : (p.1 - p.2).natAbs = 1 := by rw [hpk, hdist]
        rw [habs, pow_one] at h1
        have hne : p.1 ≠ k := by intro h; rw [h, sub_self, Int.natAbs_zero] at hdist; omega
        calc μ p ≤ lam * (x p.1 * y p.2) := h1
          _ ≤ lam * ((2 * γ) ^ (1 / q') * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hx_pt p.1 (Finset.mem_erase.mpr ⟨hne, hp.1.1⟩))
                (hyle1 p.2 hp.1.2) (hy0 p.2 hp.1.2) (Real.rpow_nonneg h2γpos.le _)) hlam0.le
          _ = lam * (2 * γ) ^ (1 / q') := by ring
    calc ∑ p ∈ S4, μ p ≤ ∑ _p ∈ S4, lam * (2 * γ) ^ (1 / q') := Finset.sum_le_sum hpt
      _ = (S4.card : ℝ) * (lam * (2 * γ) ^ (1 / q')) := by simp
      _ ≤ 4 * (lam * (2 * γ) ^ (1 / q')) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 4 * lam * (2 * γ) ^ (1 / q') := by ring
  -- Bound B5
  have hB5 : ∑ p ∈ S5, μ p ≤ (2 * γ) ^ (2 / q') := by
    have hbij : ∑ p ∈ S5, μ p = ∑ i ∈ S.erase k, μ (i, i) := by
      refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
      · intro p hp; simp only [S5, Finset.mem_filter, Finset.mem_product, Finset.mem_erase] at hp ⊢
        exact ⟨hp.2.2, hp.1.1⟩
      · intro p1 hp1 p2 hp2 h; simp only [S5, Finset.mem_filter] at hp1 hp2
        ext <;> [exact h; exact hp1.2.1.symm.trans (h.trans hp2.2.1)]
      · intro i hi; simp only [Finset.mem_erase] at hi
        exact ⟨(i, i), by simp [S5, hi.1, hi.2], rfl⟩
      · intro p hp; simp only [S5, Finset.mem_filter] at hp
        exact congrArg μ (Prod.ext rfl hp.2.1.symm)
    rw [hbij]
    have hpt : ∀ i ∈ S.erase k, μ (i, i) ≤ (2 * γ) ^ (2 / q' - 1) * (x i * y i) ^ (q' / 2) := by
      intro i hi
      have hiS := Finset.mem_of_mem_erase hi
      have h1 := hμ1' i hiS i hiS
      simp only [sub_self, Int.natAbs_zero, pow_zero, one_mul] at h1
      have hxy0 : 0 ≤ x i * y i := mul_nonneg (hx0 i hiS) (hy0 i hiS)
      have hxy_le : x i * y i ≤ (2 * γ) ^ (2 / q') := by
        calc x i * y i ≤ (2 * γ) ^ (1 / q') * (2 * γ) ^ (1 / q') :=
              mul_le_mul (hx_pt i hi) (hy_pt i hi) (hy0 i hiS) (Real.rpow_nonneg h2γpos.le _)
          _ = (2 * γ) ^ (2 / q') := by rw [← Real.rpow_add h2γpos]; congr 1; ring
      have hpow1 : (x i * y i) ^ (1 - q' / 2) ≤ ((2 * γ) ^ (2 / q')) ^ (1 - q' / 2) :=
        Real.rpow_le_rpow hxy0 hxy_le (by linarith)
      rw [← Real.rpow_mul h2γpos.le,
          show 2 / q' * (1 - q' / 2) = 2 / q' - 1 by field_simp] at hpow1
      refine h1.trans ?_
      calc x i * y i
          = (x i * y i) ^ (1 - q' / 2) * (x i * y i) ^ (q' / 2) := by
            by_cases hz : x i * y i = 0
            · rw [hz, Real.zero_rpow (by linarith), zero_mul]
            · rw [← Real.rpow_add (lt_of_le_of_ne hxy0 (Ne.symm hz)),
                  sub_add_cancel, Real.rpow_one]
        _ ≤ (2 * γ) ^ (2 / q' - 1) * (x i * y i) ^ (q' / 2) :=
            mul_le_mul_of_nonneg_right hpow1 (Real.rpow_nonneg hxy0 _)
    calc ∑ i ∈ S.erase k, μ (i, i)
        ≤ ∑ i ∈ S.erase k, (2 * γ) ^ (2 / q' - 1) * (x i * y i) ^ (q' / 2) := Finset.sum_le_sum hpt
      _ = (2 * γ) ^ (2 / q' - 1) * ∑ i ∈ S.erase k, (x i * y i) ^ (q' / 2) := by rw [Finset.mul_sum]
      _ ≤ (2 * γ) ^ (2 / q' - 1) *
            (Real.sqrt (∑ i ∈ S.erase k, x i ^ q') * Real.sqrt (∑ j ∈ S.erase k, y j ^ q')) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using sum_rpow_half_cs
            (fun i hi => hx0 i (Finset.mem_of_mem_erase hi))
            (fun j hj => hy0 j (Finset.mem_of_mem_erase hj))
            0 (fun i hi => by simpa using hi)
      _ ≤ (2 * γ) ^ (2 / q' - 1) * (Real.sqrt (2 * γ) * Real.sqrt (2 * γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (Real.sqrt_le_sqrt hx_tail) (Real.sqrt_le_sqrt hy_tail)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (2 * γ) ^ (2 / q') := by
          rw [Real.mul_self_sqrt h2γpos.le, ← Real.rpow_add_one h2γpos.ne', sub_add_cancel]
  -- Bound B5 + B6
  have hB56 : ∑ p ∈ S56, μ p ≤ 1 - (1 - q' / 2) * γ := by
    have hbij : ∑ p ∈ S56, μ p = ∑ i ∈ S, μ (i, i) := by
      refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
      · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · intro p1 hp1 p2 hp2 h; simp only [S56, Finset.mem_filter] at hp1 hp2
        ext <;> [exact h; exact hp1.2.symm.trans (h.trans hp2.2)]
      · intro i hi; exact ⟨(i, i), by simp [S56, hi], rfl⟩
      · intro p hp; simp only [S56, Finset.mem_filter] at hp
        exact congrArg μ (Prod.ext rfl hp.2.symm)
    rw [hbij]
    have hpt : ∀ i ∈ S, μ (i, i) ≤ (1 - γ) ^ (1 - q' / 2) * (x i * y i) ^ (q' / 2) := by
      intro i hi
      have h1 := hμ1' i hi i hi
      simp only [sub_self, Int.natAbs_zero, pow_zero, one_mul] at h1
      have hxy0 : 0 ≤ x i * y i := mul_nonneg (hx0 i hi) (hy0 i hi)
      have hxy_le : x i * y i ≤ 1 - γ := by
        have := hkmax i hi
        linarith
      have hpow1 : (x i * y i) ^ (1 - q' / 2) ≤ (1 - γ) ^ (1 - q' / 2) :=
        Real.rpow_le_rpow hxy0 hxy_le (by linarith)
      refine h1.trans ?_
      calc x i * y i
          = (x i * y i) ^ (1 - q' / 2) * (x i * y i) ^ (q' / 2) := by
            by_cases hz : x i * y i = 0
            · rw [hz, Real.zero_rpow (by linarith), zero_mul]
            · rw [← Real.rpow_add (lt_of_le_of_ne hxy0 (Ne.symm hz)),
                  sub_add_cancel, Real.rpow_one]
        _ ≤ (1 - γ) ^ (1 - q' / 2) * (x i * y i) ^ (q' / 2) :=
            mul_le_mul_of_nonneg_right hpow1 (Real.rpow_nonneg hxy0 _)
    have hAMGM : (1 - γ) ^ (1 - q' / 2) ≤ 1 - (1 - q' / 2) * γ := by
      have h := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - q' / 2)
        (by linarith : (0 : ℝ) ≤ q' / 2) (by linarith : (0 : ℝ) ≤ 1 - γ) zero_le_one (by ring)
      rw [Real.one_rpow, mul_one] at h
      linarith
    calc ∑ i ∈ S, μ (i, i)
        ≤ ∑ i ∈ S, (1 - γ) ^ (1 - q' / 2) * (x i * y i) ^ (q' / 2) := Finset.sum_le_sum hpt
      _ = (1 - γ) ^ (1 - q' / 2) * ∑ i ∈ S, (x i * y i) ^ (q' / 2) := by rw [Finset.mul_sum]
      _ ≤ (1 - γ) ^ (1 - q' / 2) * (Real.sqrt (∑ i ∈ S, x i ^ q') * Real.sqrt (∑ j ∈ S, y j ^ q')) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
          simpa using sum_rpow_half_cs hx0 hy0 0 (fun i hi => by simpa using hi)
      _ = (1 - γ) ^ (1 - q' / 2) := by rw [hxsum, hysum]; simp
      _ ≤ 1 - (1 - q' / 2) * γ := hAMGM
  -- Cover S ×ˢ S by S1 ∪ S2 ∪ S3 ∪ S4 ∪ S56 to upper bound γ
  have hcover_all : S ×ˢ S ⊆ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S56 := by
    intro p hp
    simp only [Finset.mem_union, S1, S2, S3, S4, S56, Finset.mem_filter]
    by_cases heq : p.1 = p.2
    · exact Or.inr ⟨hp, heq⟩
    · by_cases h1 : p.1 = k
      · have hne2 : p.2 ≠ k := by omega
        by_cases hd : 2 ≤ (p.2 - k).natAbs
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hp, h1, hd⟩)))
        · exact Or.inl (Or.inr ⟨hp, Or.inl ⟨h1, by omega⟩⟩)
      · by_cases h2 : p.2 = k
        · by_cases hd : 2 ≤ (p.1 - k).natAbs
          · exact Or.inl (Or.inl (Or.inr ⟨hp, h2, hd⟩))
          · exact Or.inl (Or.inr ⟨hp, Or.inr ⟨h2, by omega⟩⟩)
        · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hp, h1, h2, heq⟩)))
  have h1le : (1 : ℝ) ≤ ∑ p ∈ S1, μ p + ∑ p ∈ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S4, μ p + ∑ p ∈ S56, μ p := by
    rw [← hμ1]
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcover_all (fun p hp _ => by
      have hp' : p ∈ S ×ˢ S := by
        simp only [Finset.mem_union, S1, S2, S3, S4, S56, Finset.mem_filter] at hp
        rcases hp with (((h | h) | h) | h) | h <;> exact h.1
      exact hμ0 p hp')
    have hnonneg : ∀ p ∈ S ×ˢ S, 0 ≤ μ p := hμ0
    have hu : ∀ A B : Finset (ℤ × ℤ), A ⊆ S ×ˢ S → B ⊆ S ×ˢ S →
        ∑ p ∈ A ∪ B, μ p ≤ ∑ p ∈ A, μ p + ∑ p ∈ B, μ p := by
      intro A B hA _
      have heq := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := μ)
      have hnn : 0 ≤ ∑ p ∈ A ∩ B, μ p :=
        Finset.sum_nonneg fun p hp => hμ0 p (hA (Finset.mem_inter.mp hp).1)
      linarith
    have hsub1 : S1 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub2 : S2 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub3 : S3 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub4 : S4 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub56 : S56 ⊆ S ×ˢ S := Finset.filter_subset _ _
    calc ∑ p ∈ S ×ˢ S, μ p
        ≤ ∑ p ∈ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S56, μ p := hsub
      _ ≤ ∑ p ∈ S1 ∪ S2 ∪ S3 ∪ S4, μ p + ∑ p ∈ S56, μ p :=
          hu _ _ (Finset.union_subset (Finset.union_subset (Finset.union_subset hsub1 hsub2) hsub3) hsub4) hsub56
      _ ≤ ∑ p ∈ S1 ∪ S2 ∪ S3, μ p + ∑ p ∈ S4, μ p + ∑ p ∈ S56, μ p := by
          gcongr; exact hu _ _ (Finset.union_subset (Finset.union_subset hsub1 hsub2) hsub3) hsub4
      _ ≤ ∑ p ∈ S1 ∪ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S4, μ p + ∑ p ∈ S56, μ p := by
          gcongr; exact hu _ _ (Finset.union_subset hsub1 hsub2) hsub3
      _ ≤ ∑ p ∈ S1, μ p + ∑ p ∈ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S4, μ p + ∑ p ∈ S56, μ p := by
          gcongr; exact hu _ _ hsub1 hsub2
  have h2γ_2q' : (2 * γ) ^ (2 / q') ≤ 2 * (2 * γ) ^ (1 / q') := by
    rw [show 2 / q' = 1 / q' + 1 / q' by ring, Real.rpow_add h2γpos]
    have hle2 : (2 * γ) ^ (1 / q') ≤ 2 := by
      have h1 : (2 * γ) ^ (1 / q') ≤ (2 : ℝ) ^ (1 / q') :=
        Real.rpow_le_rpow h2γpos.le (by linarith) (by positivity)
      have h2 : (2 : ℝ) ^ (1 / q') ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one hq'pos]; exact hq'gt1.le)
      linarith [Real.rpow_one (2 : ℝ)]
    have hnn := Real.rpow_nonneg h2γpos.le (1 / q')
    exact mul_le_mul_of_nonneg_right hle2 hnn
  have hlam2 : lam ^ 2 ≤ lam := by
    calc lam ^ 2 = lam * lam := sq lam
      _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hlam_lt1.le hlam0.le
      _ = lam := mul_one lam
  have hγ_step : (1 - q' / 2) * γ ≤ 60 * lam * γ ^ (1 / q') := by
    have h2pow : (2 : ℝ) ^ (1 / q') ≤ 2 := by
      have hle1 : (1 : ℝ) / q' ≤ 1 := by rw [div_le_one hq'pos]; exact hq'gt1.le
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle1
      simpa only [Real.rpow_one] using h
    have h30 : (1 - q' / 2) * γ ≤ 30 * lam * (2 * γ) ^ (1 / q') := by
      have ha : 3 * lam ^ 2 * (2 * γ) ^ (1 / q') ≤ 3 * lam * (2 * γ) ^ (1 / q') := by
        have hnn := Real.rpow_nonneg h2γpos.le (1 / q')
        have hmul := mul_le_mul_of_nonneg_right hlam2 hnn
        linarith
      have hb : 10 * lam * (2 * γ) ^ (2 / q') ≤ 20 * lam * (2 * γ) ^ (1 / q') := by
        have hmul := mul_le_mul_of_nonneg_left h2γ_2q' hlam0.le
        linarith
      linarith [h1le, hB1, hB2, hB3, hB4, hB56, ha, hb]
    rw [Real.mul_rpow (by norm_num) hγpos.le] at h30
    have hmul2 : 30 * lam * ((2 : ℝ) ^ (1 / q') * γ ^ (1 / q')) ≤ 30 * lam * (2 * γ ^ (1 / q')) := by
      gcongr
    linarith [h30, hmul2]
  set B : ℝ := 60 / (1 - q' / 2) with hB_def
  have hBpos : 0 < B := div_pos (by norm_num) (by linarith)
  have hγ_ub : γ ≤ (B * lam) ^ Q := by
    have h1 : γ ^ (1 / Q) ≤ B * lam := by
      have hdiv : γ / γ ^ (1 / q') ≤ B * lam := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hγpos _), hB_def]
        have hden : 0 < 1 - q' / 2 := by linarith
        have := (le_div_iff₀' hden).mpr hγ_step
        linarith [show 60 / (1 - q' / 2) * lam * γ ^ (1 / q') =
          (60 * lam * γ ^ (1 / q')) / (1 - q' / 2) by ring]
      have hpow : γ / γ ^ (1 / q') = γ ^ (1 / Q) := by
        calc γ / γ ^ (1 / q')
            = γ ^ (1 : ℝ) / γ ^ (1 / q') := by rw [Real.rpow_one]
          _ = γ ^ ((1 : ℝ) - 1 / q') := (Real.rpow_sub hγpos _ _).symm
          _ = γ ^ (1 / Q) := by congr 1; rw [h1q']; ring
      rwa [hpow] at hdiv
    have hpowQ := Real.rpow_le_rpow (Real.rpow_nonneg hγpos.le _) h1 hQpos.le
    rwa [← Real.rpow_mul hγpos.le, one_div_mul_cancel hQpos.ne', Real.rpow_one] at hpowQ
  -- Cover tail {|i - k| + |j - k| ≥ 2} by S1 ∪ S2 ∪ S3 ∪ S5
  let Stail := (S ×ˢ S).filter (fun p => 2 ≤ (p.1 - k).natAbs + (p.2 - k).natAbs)
  have htail_sub : Stail ⊆ S1 ∪ S2 ∪ S3 ∪ S5 := by
    intro p hp
    simp only [Stail, Finset.mem_filter, Finset.mem_union, S1, S2, S3, S5] at hp ⊢
    by_cases h1 : p.1 = k
    · have h2 : 2 ≤ (p.2 - k).natAbs := by
        rw [h1, sub_self, Int.natAbs_zero, zero_add] at hp; exact hp.2
      exact Or.inl (Or.inl (Or.inr ⟨hp.1, h1, h2⟩))
    · by_cases h2 : p.2 = k
      · have h1' : 2 ≤ (p.1 - k).natAbs := by
          rw [h2, sub_self, Int.natAbs_zero, add_zero] at hp; exact hp.2
        exact Or.inl (Or.inr ⟨hp.1, h2, h1'⟩)
      · by_cases heq : p.1 = p.2
        · exact Or.inr ⟨hp.1, heq, h1⟩
        · exact Or.inl (Or.inl (Or.inl ⟨hp.1, h1, h2, heq⟩))
  have htail_sum : ∑ p ∈ Stail, μ p ≤
      ∑ p ∈ S1, μ p + ∑ p ∈ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S5, μ p := by
    have hsub1 : S1 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub2 : S2 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub3 : S3 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hsub5 : S5 ⊆ S ×ˢ S := Finset.filter_subset _ _
    have hu : ∀ A B : Finset (ℤ × ℤ), A ⊆ S ×ˢ S → B ⊆ S ×ˢ S →
        ∑ p ∈ A ∪ B, μ p ≤ ∑ p ∈ A, μ p + ∑ p ∈ B, μ p := by
      intro A B hA _
      have heq := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := μ)
      have hnn : 0 ≤ ∑ p ∈ A ∩ B, μ p :=
        Finset.sum_nonneg fun p hp => hμ0 p (hA (Finset.mem_inter.mp hp).1)
      linarith
    calc ∑ p ∈ Stail, μ p
        ≤ ∑ p ∈ S1 ∪ S2 ∪ S3 ∪ S5, μ p :=
          Finset.sum_le_sum_of_subset_of_nonneg htail_sub (fun p hp _ => by
            simp only [Finset.mem_union, S1, S2, S3, S5, Finset.mem_filter] at hp
            rcases hp with ((h | h) | h) | h <;> exact hμ0 p h.1)
      _ ≤ ∑ p ∈ S1 ∪ S2 ∪ S3, μ p + ∑ p ∈ S5, μ p :=
          hu _ _ (Finset.union_subset (Finset.union_subset hsub1 hsub2) hsub3) hsub5
      _ ≤ ∑ p ∈ S1 ∪ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S5, μ p := by
          gcongr; exact hu _ _ (Finset.union_subset hsub1 hsub2) hsub3
      _ ≤ ∑ p ∈ S1, μ p + ∑ p ∈ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S5, μ p := by
          gcongr; exact hu _ _ hsub1 hsub2
  have hterm1 : (2 * γ) ^ (2 / q') ≤ (2 : ℝ) ^ (2 / q') * B ^ (2 * Q - 2) * lam ^ (2 * Q - 2) := by
    have h1 : (2 * γ) ^ (2 / q') ≤ (2 * (B * lam) ^ Q) ^ (2 / q') :=
      Real.rpow_le_rpow h2γpos.le (by linarith) (by positivity)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (by positivity),
        show Q * (2 / q') = 2 * Q - 2 by rw [hq'_def]; field_simp,
        Real.mul_rpow hBpos.le hlam0.le, ← mul_assoc] at h1
    exact h1
  have hterm2 : lam ^ 2 * (2 * γ) ^ (1 / q') ≤
      (2 : ℝ) ^ (1 / q') * B ^ (Q - 1) * lam ^ (2 * Q - 2) := by
    have h1 : (2 * γ) ^ (1 / q') ≤ (2 * (B * lam) ^ Q) ^ (1 / q') :=
      Real.rpow_le_rpow h2γpos.le (by linarith) (by positivity)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (by positivity),
        show Q * (1 / q') = Q - 1 by rw [hq'_def]; field_simp,
        Real.mul_rpow hBpos.le hlam0.le] at h1
    have hlam_exp : lam ^ 2 * lam ^ (Q - 1) ≤ lam ^ (2 * Q - 2) := by
      rw [← Real.rpow_natCast lam 2, ← Real.rpow_add hlam0]
      exact Real.rpow_le_rpow_of_exponent_ge hlam0 hlam_lt1.le (by norm_num; linarith)
    calc lam ^ 2 * (2 * γ) ^ (1 / q')
        ≤ lam ^ 2 * ((2 : ℝ) ^ (1 / q') * (B ^ (Q - 1) * lam ^ (Q - 1))) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hlam0.le 2)
      _ = (2 : ℝ) ^ (1 / q') * B ^ (Q - 1) * (lam ^ 2 * lam ^ (Q - 1)) := by ring
      _ ≤ (2 : ℝ) ^ (1 / q') * B ^ (Q - 1) * lam ^ (2 * Q - 2) :=
          mul_le_mul_of_nonneg_left hlam_exp (by positivity)
  have h10lam : 10 * lam * (2 * γ) ^ (2 / q') + (2 * γ) ^ (2 / q') ≤ 11 * (2 * γ) ^ (2 / q') := by
    have hmul := mul_le_mul_of_nonneg_right hlam_lt1.le (Real.rpow_nonneg h2γpos.le (2 / q'))
    linarith
  unfold gwConst
  dsimp only
  rw [← hq'_def, ← hB_def]
  calc ∑ p ∈ Stail, μ p
      ≤ ∑ p ∈ S1, μ p + ∑ p ∈ S2, μ p + ∑ p ∈ S3, μ p + ∑ p ∈ S5, μ p := htail_sum
    _ ≤ 10 * lam * (2 * γ) ^ (2 / q') + 3 * lam ^ 2 * (2 * γ) ^ (1 / q') +
          3 * lam ^ 2 * (2 * γ) ^ (1 / q') + (2 * γ) ^ (2 / q') := by linarith
    _ ≤ 11 * (2 * γ) ^ (2 / q') + 6 * (lam ^ 2 * (2 * γ) ^ (1 / q')) := by linarith
    _ ≤ 11 * ((2 : ℝ) ^ (2 / q') * B ^ (2 * Q - 2) * lam ^ (2 * Q - 2)) +
          6 * ((2 : ℝ) ^ (1 / q') * B ^ (Q - 1) * lam ^ (2 * Q - 2)) := by
        gcongr
    _ = (11 * (2 : ℝ) ^ (2 / q') * B ^ (2 * Q - 2) +
          6 * (2 : ℝ) ^ (1 / q') * B ^ (Q - 1)) * lam ^ (2 * Q - 2) := by ring

end Concentration

end LRMod1

/-!
Module 1b: Algebraic Type I loss and Hu-Jing Section 5 (Dense rational box -> Type I loss).
-/

namespace LRMod1Box

open Finset BigOperators

noncomputable def typeILoss (V : Finset ℕ) (δ : ℝ) : ℝ := by
  classical
  exact 2 * δ * ∑ q ∈ V.biUnion Nat.divisors, (Nat.totient q : ℝ) *
    ((∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
      if h : (V.filter (q ∣ ·)).Nonempty then (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ) else 0)

lemma typeILoss_linear (V : Finset ℕ) (δ₁ δ₂ : ℝ) (hδ₂ : δ₂ ≠ 0) :
    typeILoss V δ₁ = (δ₁ / δ₂) * typeILoss V δ₂ := by
  unfold typeILoss
  field_simp

lemma typeILoss_mono {U V : Finset ℕ} (hUV : U ⊆ V) (_hV : ∀ v ∈ V, 0 < v) {δ : ℝ} (hδ : 0 ≤ δ) :
    typeILoss U δ ≤ typeILoss V δ := by
  classical
  unfold typeILoss
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hdiv : U.biUnion Nat.divisors ⊆ V.biUnion Nat.divisors :=
    Finset.biUnion_subset_biUnion_of_subset_left Nat.divisors hUV
  have hterm_nonneg : ∀ q ∈ V.biUnion Nat.divisors,
      0 ≤ (Nat.totient q : ℝ) * ((∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
        if h : (V.filter (q ∣ ·)).Nonempty then (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ) else 0) := by
    intro q _
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    split_ifs with h
    · have hmin : (V.filter (q ∣ ·)).min' h ∈ V.filter (q ∣ ·) := Finset.min'_mem _ h
      have hle : (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ) ≤ ∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ) :=
        Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / (v : ℝ)) (fun _ _ => by positivity) hmin
      linarith
    · rw [sub_zero]
      exact Finset.sum_nonneg (fun v _ => by positivity)
  calc ∑ q ∈ U.biUnion Nat.divisors, (Nat.totient q : ℝ) *
        ((∑ v ∈ U.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
          if h : (U.filter (q ∣ ·)).Nonempty then (1 : ℝ) / ((U.filter (q ∣ ·)).min' h : ℝ) else 0)
      ≤ ∑ q ∈ U.biUnion Nat.divisors, (Nat.totient q : ℝ) *
        ((∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
          if h : (V.filter (q ∣ ·)).Nonempty then (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ) else 0) := by
        refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hfsub : U.filter (q ∣ ·) ⊆ V.filter (q ∣ ·) := Finset.filter_subset_filter _ hUV
        by_cases hU : (U.filter (q ∣ ·)).Nonempty
        · have hVne : (V.filter (q ∣ ·)).Nonempty := hU.mono hfsub
          rw [dif_pos hU, dif_pos hVne]
          set u0 := (U.filter (q ∣ ·)).min' hU
          set v0 := (V.filter (q ∣ ·)).min' hVne
          have hu0_mem : u0 ∈ U.filter (q ∣ ·) := Finset.min'_mem _ hU
          have hv0_mem : v0 ∈ V.filter (q ∣ ·) := Finset.min'_mem _ hVne
          have hv0_le_u0 : v0 ≤ u0 := Finset.min'_le _ u0 (hfsub hu0_mem)
          have hsub_erase : (U.filter (q ∣ ·)).erase u0 ⊆ (V.filter (q ∣ ·)).erase v0 := by
            intro x hx
            rw [Finset.mem_erase] at hx ⊢
            have hlt : u0 < x := lt_of_le_of_ne (Finset.min'_le _ x hx.2) (Ne.symm hx.1)
            exact ⟨by omega, hfsub hx.2⟩
          have hsumU : (∑ v ∈ U.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) - (1 : ℝ) / (u0 : ℝ) =
              ∑ v ∈ (U.filter (q ∣ ·)).erase u0, (1 : ℝ) / (v : ℝ) := by
            rw [← Finset.add_sum_erase _ _ hu0_mem]; ring
          have hsumV : (∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) - (1 : ℝ) / (v0 : ℝ) =
              ∑ v ∈ (V.filter (q ∣ ·)).erase v0, (1 : ℝ) / (v : ℝ) := by
            rw [← Finset.add_sum_erase _ _ hv0_mem]; ring
          rw [hsumU, hsumV]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub_erase (fun v _ _ => by positivity)
        · rw [dif_neg hU, Finset.not_nonempty_iff_eq_empty.mp hU, Finset.sum_empty, sub_zero]
          split_ifs with hVne
          · have hmin := Finset.min'_mem _ hVne
            have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / (v : ℝ))
              (fun v _ => by positivity) hmin
            linarith
          · rw [sub_zero]; exact Finset.sum_nonneg (fun _ _ => by positivity)
    _ ≤ ∑ q ∈ V.biUnion Nat.divisors, (Nat.totient q : ℝ) *
        ((∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
          if h : (V.filter (q ∣ ·)).Nonempty then (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hdiv (fun q hq _ => hterm_nonneg q hq)

lemma typeILoss_ge_of_matching {U : Finset ℕ} (hU : ∀ u ∈ U, 0 < u) {δ : ℝ} (hδ : 0 ≤ δ)
    (M : Finset (ℕ × ℕ))
    (hM_mem : ∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 < p.2)
    (hM_snd_inj : Set.InjOn Prod.snd (M : Set (ℕ × ℕ))) :
    2 * δ * ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) ≤ typeILoss U δ := by
  classical
  unfold typeILoss
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  let Q := U.biUnion Nat.divisors
  have hswap : ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) =
      ∑ q ∈ Q, (Nat.totient q : ℝ) * ∑ p ∈ M.filter (fun p => q ∣ p.1 ∧ q ∣ p.2), (1 : ℝ) / (p.2 : ℝ) := by
    have h1 : ∀ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) =
        ∑ q ∈ Q, if q ∣ p.1 ∧ q ∣ p.2 then (Nat.totient q : ℝ) * ((1 : ℝ) / (p.2 : ℝ)) else 0 := by
      intro p hp
      have hp1 : p.1 ∈ U := (hM_mem p hp).1
      have hp2 : p.2 ∈ U := (hM_mem p hp).2.1
      have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 (hU p.1 hp1)
      have hsub : (Nat.gcd p.1 p.2).divisors ⊆ Q := by
        intro q hq
        rw [Nat.mem_divisors] at hq
        exact Finset.mem_biUnion.mpr ⟨p.1, hp1, Nat.mem_divisors.mpr ⟨hq.1.trans (Nat.gcd_dvd_left _ _), (hU p.1 hp1).ne'⟩⟩
      have hfilt : Q.filter (fun q => q ∣ p.1 ∧ q ∣ p.2) = (Nat.gcd p.1 p.2).divisors := by
        ext q
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · intro h; exact ⟨Nat.dvd_gcd h.2.1 h.2.2, hgpos.ne'⟩
        · intro h; exact ⟨hsub (Nat.mem_divisors.mpr h),
            h.1.trans (Nat.gcd_dvd_left _ _), h.1.trans (Nat.gcd_dvd_right _ _)⟩
      rw [← Finset.sum_filter, hfilt, ← Finset.sum_mul]
      have htot : (∑ q ∈ (Nat.gcd p.1 p.2).divisors, (Nat.totient q : ℝ)) = (Nat.gcd p.1 p.2 : ℝ) := by
        exact_mod_cast Nat.sum_totient (Nat.gcd p.1 p.2)
      rw [htot]
      ring
    calc ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)
        = ∑ p ∈ M, ∑ q ∈ Q, if q ∣ p.1 ∧ q ∣ p.2 then (Nat.totient q : ℝ) * ((1 : ℝ) / (p.2 : ℝ)) else 0 :=
          Finset.sum_congr rfl h1
      _ = ∑ q ∈ Q, ∑ p ∈ M, if q ∣ p.1 ∧ q ∣ p.2 then (Nat.totient q : ℝ) * ((1 : ℝ) / (p.2 : ℝ)) else 0 :=
          Finset.sum_comm
      _ = ∑ q ∈ Q, (Nat.totient q : ℝ) * ∑ p ∈ M.filter (fun p => q ∣ p.1 ∧ q ∣ p.2), (1 : ℝ) / (p.2 : ℝ) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  let Mq := M.filter (fun p => q ∣ p.1 ∧ q ∣ p.2)
  by_cases hMq : Mq.Nonempty
  · obtain ⟨p0, hp0⟩ := hMq
    have hp0' := Finset.mem_filter.mp hp0
    have hUq : (U.filter (q ∣ ·)).Nonempty :=
      ⟨p0.1, Finset.mem_filter.mpr ⟨(hM_mem p0 hp0'.1).1, hp0'.2.1⟩⟩
    rw [dif_pos hUq]
    set v0 := (U.filter (q ∣ ·)).min' hUq
    have hv0_mem : v0 ∈ U.filter (q ∣ ·) := Finset.min'_mem _ hUq
    have hsumU : (∑ v ∈ U.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) - (1 : ℝ) / (v0 : ℝ) =
        ∑ v ∈ (U.filter (q ∣ ·)).erase v0, (1 : ℝ) / (v : ℝ) := by
      rw [← Finset.add_sum_erase _ _ hv0_mem]; ring
    rw [hsumU]
    have hinj : Set.InjOn Prod.snd (Mq : Set (ℕ × ℕ)) :=
      hM_snd_inj.mono (by exact_mod_cast Finset.filter_subset _ M)
    rw [← Finset.sum_image (f := fun v : ℕ => (1 : ℝ) / (v : ℝ)) (g := Prod.snd)
      (fun a ha b hb h => hinj ha hb h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    have hp' := Finset.mem_filter.mp hp
    have hmem1 : p.1 ∈ U.filter (q ∣ ·) := Finset.mem_filter.mpr ⟨(hM_mem p hp'.1).1, hp'.2.1⟩
    have hmem2 : p.2 ∈ U.filter (q ∣ ·) := Finset.mem_filter.mpr ⟨(hM_mem p hp'.1).2.1, hp'.2.2⟩
    have hv0_le : v0 ≤ p.1 := Finset.min'_le _ p.1 hmem1
    have hlt : p.1 < p.2 := (hM_mem p hp'.1).2.2
    exact Finset.mem_erase.mpr ⟨by omega, hmem2⟩
  · change ∑ p ∈ Mq, (1 : ℝ) / (p.2 : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hMq, Finset.sum_empty]
    split_ifs with hUq
    · have hmin := Finset.min'_mem _ hUq
      have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / (v : ℝ))
        (fun _ _ => by positivity) hmin
      linarith
    · rw [sub_zero]; exact Finset.sum_nonneg (fun _ _ => by positivity)

section SmoothRough

lemma geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ k ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq hr1.ne, inv_eq_one_div]
  have h1 : 0 < 1 - r := sub_pos.mpr hr1
  have h2 : 0 ≤ r ^ N := pow_nonneg hr0 N
  have heq : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
    rw [show r ^ N - 1 = -(1 - r ^ N) by ring, show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
  rw [heq, div_le_div_iff_of_pos_right h1]
  linarith

lemma prod_geometric_ge_smooth_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {α : ℝ} (hα : 0 < α) (A : ℕ) :
    ∑ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P), ((s : ℝ) ^ α)⁻¹ ≤
      ∏ p ∈ P, (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ := by
  classical
  let E := A + 1
  have h1 : ∑ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P), ((s : ℝ) ^ α)⁻¹ ≤
      ∏ p ∈ P, ∑ k ∈ Finset.range E, (((p : ℝ) ^ α)⁻¹) ^ k := by
    rw [Finset.prod_sum]
    let φ : ℕ → (∀ p ∈ P, ℕ) := fun s p _ => s.factorization p
    have hmaps : ∀ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P),
        φ s ∈ P.pi (fun _ => Finset.range E) := by
      intro s hs
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_range]
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs
      have hp2 : 2 ≤ p := (hP p hp).two_le
      have hpow : p ^ s.factorization p ≤ s := by
        by_cases hdiv : p ∣ s
        · exact Nat.le_of_dvd (by omega) (Nat.ordProj_dvd s p)
        · rw [Nat.factorization_eq_zero_of_not_dvd hdiv, pow_zero]; omega
      have hlt : s.factorization p < 2 ^ s.factorization p := Nat.lt_two_pow_self
      have h2le : 2 ^ s.factorization p ≤ p ^ s.factorization p := Nat.pow_le_pow_left hp2 _
      dsimp only [φ, E]
      omega
    have hval : ∀ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P),
        ((s : ℝ) ^ α)⁻¹ = ∏ p ∈ P.attach, (((p.1 : ℝ) ^ α)⁻¹) ^ (φ s p.1 p.2) := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs
      have hs0 : s ≠ 0 := by omega
      have hprod : ∏ p ∈ P, p ^ s.factorization p = s := by
        have hsupp : s.factorization.support ⊆ P := by
          rw [Nat.support_factorization]; exact hs.2
        calc ∏ p ∈ P, p ^ s.factorization p
            = ∏ p ∈ s.factorization.support, p ^ s.factorization p :=
              (Finset.prod_subset hsupp fun p _ hpnot => by
                rw [Finsupp.notMem_support_iff.mp hpnot, pow_zero]).symm
          _ = s := Nat.prod_factorization_pow_eq_self hs0
      have hprodR : (s : ℝ) = ∏ p ∈ P, (p : ℝ) ^ s.factorization p := by
        exact_mod_cast hprod.symm
      rw [hprodR]
      have hrpow : (∏ p ∈ P, (p : ℝ) ^ s.factorization p) ^ α =
          ∏ p ∈ P, ((p : ℝ) ^ α) ^ s.factorization p := by
        rw [← Real.finsetProd_rpow P _ (fun p _ => by positivity)]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm,
            Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
      rw [hrpow, ← Finset.prod_inv_distrib]
      rw [← Finset.prod_attach (s := P) (f := fun p => (((p : ℝ) ^ α) ^ s.factorization p)⁻¹)]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [inv_pow]
    have hinj : Set.InjOn φ ((Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P) : Set ℕ) := by
      intro s1 hs1 s2 hs2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hs1 hs2
      have hs10 : s1 ≠ 0 := by omega
      have hs20 : s2 ≠ 0 := by omega
      have hsupp1 : s1.factorization.support ⊆ P := by rw [Nat.support_factorization]; exact hs1.2
      have hsupp2 : s2.factorization.support ⊆ P := by rw [Nat.support_factorization]; exact hs2.2
      have hprod1 : ∏ p ∈ P, p ^ s1.factorization p = s1 := by
        calc ∏ p ∈ P, p ^ s1.factorization p
            = ∏ p ∈ s1.factorization.support, p ^ s1.factorization p :=
              (Finset.prod_subset hsupp1 fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp, pow_zero]).symm
          _ = s1 := Nat.prod_factorization_pow_eq_self hs10
      have hprod2 : ∏ p ∈ P, p ^ s2.factorization p = s2 := by
        calc ∏ p ∈ P, p ^ s2.factorization p
            = ∏ p ∈ s2.factorization.support, p ^ s2.factorization p :=
              (Finset.prod_subset hsupp2 fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp, pow_zero]).symm
          _ = s2 := Nat.prod_factorization_pow_eq_self hs20
      rw [← hprod1, ← hprod2]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpeq : φ s1 p hp = φ s2 p hp := congrFun (congrFun heq p) hp
      exact congrArg (p ^ ·) hpeq
    calc ∑ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P), ((s : ℝ) ^ α)⁻¹
        = ∑ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P),
            ∏ p ∈ P.attach, (((p.1 : ℝ) ^ α)⁻¹) ^ (φ s p.1 p.2) := Finset.sum_congr rfl hval
      _ = ∑ f ∈ ((Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P)).image φ,
            ∏ p ∈ P.attach, (((p.1 : ℝ) ^ α)⁻¹) ^ (f p.1 p.2) := by
          rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
      _ ≤ ∑ f ∈ P.pi (fun _ => Finset.range E),
            ∏ p ∈ P.attach, (((p.1 : ℝ) ^ α)⁻¹) ^ (f p.1 p.2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
          intro f hf
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hf
          exact hmaps s hs
  refine h1.trans ?_
  refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun _ _ => by positivity)) fun p hp => ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
  have hr1 : ((p : ℝ) ^ α)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr (Real.one_lt_rpow hp1 hα)
  exact geom_sum_le_inv (by positivity) hr1 E

lemma exists_prime_finset_prod_le {C : ℝ} (hC : 0 < C) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 / (8 * C) := by
  have htend := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨X, hX⟩ := htend (8 * C)
  let P := (Finset.Icc 1 X).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  refine ⟨P, hP, ?_⟩
  have hXbound : 8 * C ≤ ∑ i ∈ Finset.range X, (1 : ℝ) / ((i : ℝ) + 1) := hX X le_rfl
  have hsum_eq : ∑ i ∈ Finset.range X, (1 : ℝ) / ((i : ℝ) + 1) =
      ∑ s ∈ (Finset.Icc 1 X).filter (fun s => s.primeFactors ⊆ P), ((s : ℝ) ^ (1 : ℝ))⁻¹ := by
    have hall : (Finset.Icc 1 X).filter (fun s => s.primeFactors ⊆ P) = Finset.Icc 1 X := by
      rw [Finset.filter_eq_self]
      intro s hs p hp
      rw [Nat.mem_primeFactors] at hp
      rw [Finset.mem_Icc] at hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.1.pos, Nat.le_of_dvd (by omega) hp.2.1 |>.trans hs.2⟩, hp.1⟩
    rw [hall]
    refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
    · intro a _ b _ h; omega
    · intro s hs; rw [Finset.mem_Icc] at hs
      exact ⟨s - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i _
      simp [Real.rpow_one]
  have hprod := prod_geometric_ge_smooth_sum P hP zero_lt_one X
  rw [← hsum_eq] at hprod
  have hprod_eq : ∏ p ∈ P, (1 - ((p : ℝ) ^ (1 : ℝ))⁻¹)⁻¹ = (∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Real.rpow_one, one_div]
  rw [hprod_eq] at hprod
  have hpos_prod : 0 < ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have h8C : 8 * C ≤ (∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := hXbound.trans hprod
  rw [le_inv_comm₀ (by positivity) hpos_prod] at h8C
  simpa [one_div] using h8C

def smoothPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

def roughPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  a / smoothPart P a

lemma smoothPart_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) :
    0 < smoothPart P a :=
  Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _

lemma smoothPart_dvd (P : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    smoothPart P a ∣ a := by
  unfold smoothPart
  have h1 : ∏ p ∈ P ∩ a.primeFactors, p ^ a.factorization p = ∏ p ∈ P, p ^ a.factorization p := by
    refine Finset.prod_subset Finset.inter_subset_left fun p hp hpnot => ?_
    have hnotpf : p ∉ a.primeFactors := fun h => hpnot (Finset.mem_inter.mpr ⟨hp, h⟩)
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hnotpf
    rw [hnotpf, pow_zero]
  rw [← h1]
  have h2 := Nat.prod_factorization_pow_eq_self ha.ne'
  rw [Finsupp.prod, Nat.support_factorization] at h2
  have h3 : ∏ p ∈ P ∩ a.primeFactors, p ^ a.factorization p ∣ ∏ p ∈ a.primeFactors, p ^ a.factorization p :=
    Finset.prod_dvd_prod_of_subset (P ∩ a.primeFactors) a.primeFactors
      (fun p => p ^ a.factorization p) Finset.inter_subset_right
  rwa [h2] at h3

lemma smoothPart_mul_roughPart (P : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    smoothPart P a * roughPart P a = a :=
  Nat.mul_div_cancel' (smoothPart_dvd P ha)

lemma smoothPart_primeFactors_subset (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) :
    (smoothPart P a).primeFactors ⊆ P := by
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  have hdvd := hq.2.1
  unfold smoothPart at hdvd
  obtain ⟨p, hpP, hp⟩ := (hq.1.prime.dvd_finsetProd_iff _).mp hdvd
  have hqp : q ∣ p := hq.1.prime.dvd_of_dvd_pow hp
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq.1 (hP p hpP)).mp hqp
  rwa [heq]

lemma roughPart_not_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ℕ} (ha : 0 < a)
    {p : ℕ} (hp : p ∈ P) : ¬ p ∣ roughPart P a := by
  intro hdvd
  have hmul := smoothPart_mul_roughPart P ha
  have hpow_dvd : p ^ a.factorization p ∣ smoothPart P a :=
    Finset.dvd_prod_of_mem _ hp
  have hsucc : p ^ (a.factorization p + 1) ∣ smoothPart P a * roughPart P a := by
    rw [pow_succ]
    exact mul_dvd_mul hpow_dvd hdvd
  rw [hmul] at hsucc
  have hle := ((hP p hp).pow_dvd_iff_le_factorization ha.ne').mp hsucc
  omega

lemma count_smooth_gt_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A S : ℕ) (hS : 1 ≤ S) :
    (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ) ≤
      (A : ℝ) * (∏ p ∈ P, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹) / Real.sqrt (S : ℝ) := by
  classical
  let BadS := (Finset.Icc 1 A).filter (fun s => S < s ∧ s.primeFactors ⊆ P)
  have hcover : (Finset.Icc 1 A).filter (fun a => S < smoothPart P a) ⊆
      BadS.biUnion (fun s => (Finset.Icc 1 A).filter (fun a => s ∣ a)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    refine Finset.mem_biUnion.mpr ⟨smoothPart P a, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨smoothPart_pos P hP a,
        (Nat.le_of_dvd (by omega) (smoothPart_dvd P (by omega))).trans ha.1.2⟩,
        ha.2, smoothPart_primeFactors_subset P hP a⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ha.1, smoothPart_dvd P (by omega)⟩
  have hmult_card : ∀ s : ℕ, 0 < s → (((Finset.Icc 1 A).filter (fun a => s ∣ a)).card : ℝ) ≤ (A : ℝ) / (s : ℝ) := by
    intro s hs
    have hcard : ((Finset.Icc 1 A).filter (fun a => s ∣ a)).card ≤ A / s := by
      have hinj : ((Finset.Icc 1 A).filter (fun a => s ∣ a)).image (· / s) ⊆ Finset.Icc 1 (A / s) := by
        intro q hq
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
        exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) ha.2) hs, Nat.div_le_div_right ha.1.2⟩
      have hbij : Set.InjOn (· / s) ((Finset.Icc 1 A).filter (fun a => s ∣ a) : Set ℕ) := by
        intro a ha b hb h
        dsimp only at h
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        calc a = s * (a / s) := (Nat.mul_div_cancel' ha.2).symm
          _ = s * (b / s) := by rw [h]
          _ = b := Nat.mul_div_cancel' hb.2
      calc ((Finset.Icc 1 A).filter (fun a => s ∣ a)).card
          = (((Finset.Icc 1 A).filter (fun a => s ∣ a)).image (· / s)).card :=
            (Finset.card_image_of_injOn hbij).symm
        _ ≤ (Finset.Icc 1 (A / s)).card := Finset.card_le_card hinj
        _ = A / s := by simp
    exact (Nat.cast_le.mpr hcard).trans (Nat.cast_div_le)
  have h1 : (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ) ≤
      (A : ℝ) * ∑ s ∈ BadS, (1 : ℝ) / (s : ℝ) := by
    have hc := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hcR : (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ) ≤
        ∑ s ∈ BadS, (((Finset.Icc 1 A).filter (fun a => s ∣ a)).card : ℝ) := by
      exact_mod_cast hc
    refine hcR.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    have hm := hmult_card s (by omega)
    rwa [mul_one_div]
  have h2 : ∑ s ∈ BadS, (1 : ℝ) / (s : ℝ) ≤
      (1 / Real.sqrt (S : ℝ)) * ∑ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P),
        ((s : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    have hsub : BadS ⊆ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P) := by
      intro s hs
      simp only [BadS, Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.2⟩
    refine (Finset.sum_le_sum fun s hs => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
    have hs_gt : S < s := (Finset.mem_filter.mp hs).2.1
    have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
    have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hsqrt_le : Real.sqrt (S : ℝ) ≤ Real.sqrt (s : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hs_gt.le)
    rw [← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) := Real.mul_self_sqrt hspos.le
    have hle_prod : Real.sqrt (S : ℝ) * Real.sqrt (s : ℝ) ≤ (s : ℝ) := by
      calc Real.sqrt (S : ℝ) * Real.sqrt (s : ℝ) ≤ Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) :=
            mul_le_mul_of_nonneg_right hsqrt_le (Real.sqrt_nonneg _)
        _ = (s : ℝ) := hsq
    have h1div : 1 / (s : ℝ) ≤ 1 / (Real.sqrt (S : ℝ) * Real.sqrt (s : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr hSpos) (Real.sqrt_pos.mpr hspos)) hle_prod
    have hrhs : 1 / (Real.sqrt (S : ℝ) * Real.sqrt (s : ℝ)) = 1 / Real.sqrt (S : ℝ) * (Real.sqrt (s : ℝ))⁻¹ := by
      field_simp
    linarith
  have h3 := prod_geometric_ge_smooth_sum P hP (by norm_num : (0 : ℝ) < 1 / 2) A
  calc (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ)
      ≤ (A : ℝ) * ∑ s ∈ BadS, (1 : ℝ) / (s : ℝ) := h1
    _ ≤ (A : ℝ) * ((1 / Real.sqrt (S : ℝ)) *
          ∑ s ∈ (Finset.Icc 1 A).filter (fun s => s.primeFactors ⊆ P), ((s : ℝ) ^ (1 / 2 : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg A)
    _ ≤ (A : ℝ) * ((1 / Real.sqrt (S : ℝ)) * ∏ p ∈ P, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹) := by
        gcongr
    _ = (A : ℝ) * (∏ p ∈ P, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹) / Real.sqrt (S : ℝ) := by ring

lemma prime_finset_prod_dvd_iff {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (a : ℕ) :
    (∏ p ∈ D, p) ∣ a ↔ ∀ p ∈ D, p ∣ a := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hD p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hD q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := fun h => hps (h ▸ hq)
      exact (Nat.coprime_primes hp (hs q hq)).mpr hne
    constructor
    · intro h
      have h1 : p ∣ a := (dvd_mul_right p (∏ q ∈ s, q)).trans h
      have h2 : (∏ q ∈ s, q) ∣ a := (dvd_mul_left (∏ q ∈ s, q) p).trans h
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact h1
      · exact (ih hs).mp h2 q hq
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (h p (Finset.mem_insert_self _ _))
        ((ih hs).mpr fun q hq => h q (Finset.mem_insert_of_mem hq))

lemma count_rough_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A : ℕ) :
    (((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card : ℝ) ≤
      (A : ℝ) * ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) + (2 : ℝ) ^ P.card := by
  classical
  have hind : ∀ a ∈ Finset.Icc 1 A,
      (if ∀ p ∈ P, ¬ p ∣ a then (1 : ℝ) else 0) =
        ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * (if (∏ p ∈ D, p) ∣ a then (1 : ℝ) else 0) := by
    intro a _
    have hprod_ind : (if ∀ p ∈ P, ¬ p ∣ a then (1 : ℝ) else 0) =
        ∏ p ∈ P, ((if p ∣ a then (-1 : ℝ) else 0) + 1) := by
      by_cases h : ∀ p ∈ P, ¬ p ∣ a
      · rw [if_pos h]
        exact (Finset.prod_eq_one fun p hp => by simp [h p hp]).symm
      · rw [if_neg h]
        push Not at h
        obtain ⟨p, hpP, hpa⟩ := h
        exact (Finset.prod_eq_zero hpP (by simp [hpa])).symm
    rw [hprod_ind, Finset.prod_add]
    refine Finset.sum_congr rfl fun D hD => ?_
    have hDP : D ⊆ P := Finset.mem_powerset.mp hD
    rw [Finset.prod_const_one, mul_one]
    by_cases hdvd : (∏ p ∈ D, p) ∣ a
    · rw [if_pos hdvd, mul_one]
      have hall := (prime_finset_prod_dvd_iff (fun p hp => hP p (hDP hp)) a).mp hdvd
      rw [Finset.prod_congr rfl (fun p hp => by rw [if_pos (hall p hp)]), Finset.prod_const]
    · rw [if_neg hdvd, mul_zero]
      have hnotall : ¬ ∀ p ∈ D, p ∣ a := fun h => hdvd ((prime_finset_prod_dvd_iff (fun p hp => hP p (hDP hp)) a).mpr h)
      push Not at hnotall
      obtain ⟨p, hpD, hpa⟩ := hnotall
      exact Finset.prod_eq_zero hpD (by rw [if_neg hpa])
  have hsum_card : (((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card : ℝ) =
      ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * ((A / ∏ p ∈ D, p : ℕ) : ℝ) := by
    calc (((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card : ℝ)
        = ∑ a ∈ Finset.Icc 1 A, if ∀ p ∈ P, ¬ p ∣ a then (1 : ℝ) else 0 := by
          rw [Finset.sum_boole]
      _ = ∑ a ∈ Finset.Icc 1 A,
            ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * (if (∏ p ∈ D, p) ∣ a then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl hind
      _ = ∑ D ∈ P.powerset,
            (-1 : ℝ) ^ D.card * ∑ a ∈ Finset.Icc 1 A, (if (∏ p ∈ D, p) ∣ a then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun D _ => by rw [Finset.mul_sum]
      _ = ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * ((A / ∏ p ∈ D, p : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun D hD => ?_
          congr 1
          rw [Finset.sum_boole]
          congr 1
          have hdpos : 0 < ∏ p ∈ D, p := Finset.prod_pos fun p hp => (hP p (Finset.mem_powerset.mp hD hp)).pos
          have hbij : ((Finset.Icc 1 A).filter (fun a => (∏ p ∈ D, p) ∣ a)).card = (Finset.Icc 1 (A / ∏ p ∈ D, p)).card := by
            refine Finset.card_bij (fun a _ => a / ∏ p ∈ D, p) ?_ ?_ ?_
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
              exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) ha.2) hdpos, Nat.div_le_div_right ha.1.2⟩
            · intro a ha b hb h
              simp only [Finset.mem_filter] at ha hb
              calc a = (∏ p ∈ D, p) * (a / ∏ p ∈ D, p) := (Nat.mul_div_cancel' ha.2).symm
                _ = (∏ p ∈ D, p) * (b / ∏ p ∈ D, p) := by rw [h]
                _ = b := Nat.mul_div_cancel' hb.2
            · intro q hq
              simp only [Finset.mem_Icc] at hq
              refine ⟨(∏ p ∈ D, p) * q, ?_, Nat.mul_div_cancel_left q hdpos⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right _ _⟩
              · exact Nat.mul_pos hdpos (by omega)
              · exact (Nat.mul_le_mul_left _ hq.2).trans (Nat.mul_div_le A _)
          simpa using hbij
  have hmain : (A : ℝ) * ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) =
      ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * ((A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) := by
    have hprod : ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) =
        ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * (1 / ((∏ p ∈ D, p : ℕ) : ℝ)) := by
      have : ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) = ∏ p ∈ P, ((-((1 : ℝ) / (p : ℝ))) + 1) := by
        refine Finset.prod_congr rfl fun p _ => by ring
      rw [this, Finset.prod_add]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [Finset.prod_const_one, mul_one, Finset.prod_neg]
      simp_rw [one_div]
      rw [Finset.prod_inv_distrib]
      push_cast
      ring
    rw [hprod, Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => by ring
  rw [hsum_card]
  have hdiff : ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * ((A / ∏ p ∈ D, p : ℕ) : ℝ) -
      ∑ D ∈ P.powerset, (-1 : ℝ) ^ D.card * ((A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) ≤ (2 : ℝ) ^ P.card := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ D ∈ P.powerset, ((-1 : ℝ) ^ D.card * ((A / ∏ p ∈ D, p : ℕ) : ℝ) -
            (-1 : ℝ) ^ D.card * ((A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)))
        ≤ ∑ _D ∈ P.powerset, (1 : ℝ) := by
          refine Finset.sum_le_sum fun D hD => ?_
          have hdpos : 0 < ∏ p ∈ D, p := Finset.prod_pos fun p hp => (hP p (Finset.mem_powerset.mp hD hp)).pos
          have hdposR : (0 : ℝ) < ((∏ p ∈ D, p : ℕ) : ℝ) := by exact_mod_cast hdpos
          have hfloor_le : ((A / ∏ p ∈ D, p : ℕ) : ℝ) ≤ (A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ) := Nat.cast_div_le
          have hfloor_ge : (A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ) - 1 ≤ ((A / ∏ p ∈ D, p : ℕ) : ℝ) := by
            rw [sub_le_iff_le_add, div_le_iff₀ hdposR]
            have hlt : A < (A / ∏ p ∈ D, p + 1) * (∏ p ∈ D, p) := by
              have := Nat.div_add_mod A (∏ p ∈ D, p)
              have hmod := Nat.mod_lt A hdpos
              nlinarith
            have hltR : (A : ℝ) < (((A / ∏ p ∈ D, p : ℕ) : ℝ) + 1) * ((∏ p ∈ D, p : ℕ) : ℝ) := by
              exact_mod_cast hlt
            linarith
          have habs : |((A / ∏ p ∈ D, p : ℕ) : ℝ) - (A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          calc (-1 : ℝ) ^ D.card * ((A / ∏ p ∈ D, p : ℕ) : ℝ) -
                (-1 : ℝ) ^ D.card * ((A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ))
              = (-1 : ℝ) ^ D.card * (((A / ∏ p ∈ D, p : ℕ) : ℝ) - (A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) := by ring
            _ ≤ |(-1 : ℝ) ^ D.card * (((A / ∏ p ∈ D, p : ℕ) : ℝ) - (A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ))| := le_abs_self _
            _ = |((A / ∏ p ∈ D, p : ℕ) : ℝ) - (A : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)| := by
                rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            _ ≤ 1 := habs
      _ = (2 : ℝ) ^ P.card := by simp
  linarith

end SmoothRough

section MaximalMatching

lemma exists_maximal_matching (U : Finset ℕ) (E : ℕ → ℕ → Prop) [DecidableRel E]
    (hEsym : ∀ u v, E u v → E v u) :
    ∃ M : Finset (ℕ × ℕ),
      (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 < p.2 ∧ E p.1 p.2) ∧
      (∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint ({p.1, p.2} : Finset ℕ) {q.1, q.2}) ∧
      (∀ u ∈ U \ M.biUnion (fun p => ({p.1, p.2} : Finset ℕ)),
        ∀ v ∈ U \ M.biUnion (fun p => ({p.1, p.2} : Finset ℕ)), u ≠ v → ¬ E u v) := by
  classical
  let AllEdges := (U ×ˢ U).filter (fun p => p.1 < p.2 ∧ E p.1 p.2)
  let Valid := AllEdges.powerset.filter (fun M =>
    ∀ p ∈ M, ∀ q ∈ M, p ≠ q → Disjoint ({p.1, p.2} : Finset ℕ) {q.1, q.2})
  have hVne : Valid.Nonempty := ⟨∅, by simp [Valid]⟩
  obtain ⟨M, hM, hMmax⟩ := Finset.exists_max_image Valid Finset.card hVne
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  refine ⟨M, ?_, hM.2, ?_⟩
  · intro p hp
    have := Finset.mem_filter.mp (hM.1 hp)
    exact ⟨(Finset.mem_product.mp this.1).1, (Finset.mem_product.mp this.1).2, this.2.1, this.2.2⟩
  · intro u hu v hv huv hEuv
    rw [Finset.mem_sdiff] at hu hv
    -- Orient the pair so first < second
    let e : ℕ × ℕ := if u < v then (u, v) else (v, u)
    have he_all : e ∈ AllEdges := by
      simp only [AllEdges, Finset.mem_filter, Finset.mem_product, e]
      split_ifs with hlt
      · exact ⟨⟨hu.1, hv.1⟩, hlt, hEuv⟩
      · exact ⟨⟨hv.1, hu.1⟩, lt_of_le_of_ne (not_lt.mp hlt) huv.symm, hEsym u v hEuv⟩
    have he_notM : e ∉ M := by
      intro hmem
      have huin : u ∈ M.biUnion (fun p => ({p.1, p.2} : Finset ℕ)) := by
        refine Finset.mem_biUnion.mpr ⟨e, hmem, ?_⟩
        simp only [e]; split_ifs <;> simp
      exact hu.2 huin
    have he_disj : ∀ p ∈ M, Disjoint ({e.1, e.2} : Finset ℕ) {p.1, p.2} := by
      intro p hp
      rw [Finset.disjoint_left]
      intro x hxe hxp
      have hxin : x ∈ M.biUnion (fun q => ({q.1, q.2} : Finset ℕ)) :=
        Finset.mem_biUnion.mpr ⟨p, hp, hxp⟩
      have hxe' : x = u ∨ x = v := by
        simp only [e, Finset.mem_insert, Finset.mem_singleton] at hxe
        split_ifs at hxe <;> tauto
      rcases hxe' with rfl | rfl
      · exact hu.2 hxin
      · exact hv.2 hxin
    have hM' : insert e M ∈ Valid := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset he_all hM.1, ?_⟩
      intro p hp q hq hpq
      rw [Finset.mem_insert] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · exact absurd rfl hpq
      · exact he_disj q hq
      · exact (he_disj p hp).symm
      · exact hM.2 p hp q hq hpq
    have hle := hMmax (insert e M) hM'
    rw [Finset.card_insert_of_notMem he_notM] at hle
    omega

end MaximalMatching

set_option maxHeartbeats 800000 in
/-- Hu-Jing Lemma 5.1: A dense rational box forces a uniform positive Type I loss. -/
theorem dense_rational_box {C : ℝ} (hC : 1 ≤ C) :
    ∃ κ > 0, ∀ (U : Finset ℕ), 2 ≤ U.card → (∀ u ∈ U, 0 < u) →
      ∀ (ξ : ℚ), 0 < ξ → ∀ (A B : ℕ), 1 ≤ A → 1 ≤ B → ((A : ℝ) * (B : ℝ) ≤ C * (U.card : ℝ)) →
      (∀ u ∈ U, ∃ a b : ℕ, 1 ≤ a ∧ a ≤ A ∧ 1 ≤ b ∧ b ≤ B ∧ (u : ℚ) = ξ * (a : ℚ) / (b : ℚ)) →
      κ ≤ typeILoss U (1 / (2 * (U.card : ℝ))) := by
  classical
  obtain ⟨P, hPprime, hdP⟩ := exists_prime_finset_prod_le (show (0 : ℝ) < C by linarith)
  set A_P : ℝ := ∏ p ∈ P, (1 - ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹)⁻¹ with hAP_def
  have hAP_pos : 0 < A_P := by
    refine Finset.prod_pos fun p hp => inv_pos.mpr ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hPprime p hp).one_lt
    have : ((p : ℝ) ^ (1 / 2 : ℝ))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; exact Or.inr (Real.one_lt_rpow hp1 (by norm_num))
    linarith
  let S : ℕ := max 1 (Nat.ceil ((8 * C * A_P) ^ 2))
  have hS1 : 1 ≤ S := le_max_left _ _
  have hS_bd : A_P / Real.sqrt (S : ℝ) ≤ 1 / (8 * C) := by
    have hSge : (8 * C * A_P) ^ 2 ≤ (S : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
    have hsqrt : 8 * C * A_P ≤ Real.sqrt (S : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 8 * C * A_P)]
      exact Real.sqrt_le_sqrt hSge
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hS1)) (by positivity)]
    linarith
  let N0 : ℕ := max 2 (Nat.ceil ((8 * C * (2 : ℝ) ^ P.card) ^ 2))
  have hN0_pos : 0 < N0 := by omega
  let κ : ℝ := min (1 / (4 * ((S : ℝ) ^ 2))) (1 / (C * ((N0 : ℝ) ^ 2)))
  have hκ_pos : 0 < κ := by
    have hSpos : (0 : ℝ) < S := by exact_mod_cast hS1
    have hN0R : (0 : ℝ) < N0 := by exact_mod_cast hN0_pos
    exact lt_min (by positivity) (by positivity)
  refine ⟨κ, hκ_pos, ?_⟩
  intro U hUcard hUpos ξ hξ A B hA1 hB1 hAB hrep
  set m := U.card with hm_def
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  -- Pick a representation (a_u, b_u) for each u ∈ U
  let repA : ℕ → ℕ := fun u => if h : u ∈ U then (hrep u h).choose else 1
  let repB : ℕ → ℕ := fun u => if h : u ∈ U then (hrep u h).choose_spec.choose else 1
  have hrep_spec : ∀ u ∈ U, 1 ≤ repA u ∧ repA u ≤ A ∧ 1 ≤ repB u ∧ repB u ≤ B ∧
      (u : ℚ) = ξ * (repA u : ℚ) / (repB u : ℚ) := by
    intro u hu
    simp only [repA, repB, dif_pos hu]
    exact (hrep u hu).choose_spec.choose_spec
  have hrep_inj : Set.InjOn (fun u => (repA u, repB u)) (U : Set ℕ) := by
    intro u hu v hv heq
    have hu' := hrep_spec u hu
    have hv' := hrep_spec v hv
    have ha : repA u = repA v := congrArg Prod.fst heq
    have hb : repB u = repB v := congrArg Prod.snd heq
    have hq : (u : ℚ) = (v : ℚ) := by rw [hu'.2.2.2.2, hv'.2.2.2.2, ha, hb]
    exact_mod_cast hq
  -- Small case: m < N0 -> one pair suffices
  by_cases hm_small : m < N0
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
    let p : ℕ × ℕ := if u < v then (u, v) else (v, u)
    have hp1 : p.1 ∈ U := by simp only [p]; split_ifs <;> assumption
    have hp2 : p.2 ∈ U := by simp only [p]; split_ifs <;> assumption
    have hplt : p.1 < p.2 := by simp only [p]; split_ifs with h <;> omega
    have hmatch := typeILoss_ge_of_matching hUpos (by positivity : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)))
      ({p} : Finset (ℕ × ℕ)) (by simp [hp1, hp2, hplt]) (by simp)
    rw [Finset.sum_singleton] at hmatch
    -- Bound p.2 / gcd(p.1, p.2) ≤ A * B ≤ C * m
    have hr1 := hrep_spec p.1 hp1
    have hr2 := hrep_spec p.2 hp2
    have hcross : p.1 * (repB p.1 * repA p.2) = p.2 * (repA p.1 * repB p.2) := by
      have h1Q : (p.1 : ℚ) * (repB p.1 : ℚ) = ξ * (repA p.1 : ℚ) := by
        rw [hr1.2.2.2.2]; field_simp [show (repB p.1 : ℚ) ≠ 0 by exact_mod_cast (by omega : repB p.1 ≠ 0)]
      have h2Q : (p.2 : ℚ) * (repB p.2 : ℚ) = ξ * (repA p.2 : ℚ) := by
        rw [hr2.2.2.2.2]; field_simp [show (repB p.2 : ℚ) ≠ 0 by exact_mod_cast (by omega : repB p.2 ≠ 0)]
      have hQ : (p.1 : ℚ) * ((repB p.1 : ℚ) * (repA p.2 : ℚ)) =
          (p.2 : ℚ) * ((repA p.1 : ℚ) * (repB p.2 : ℚ)) := by
        calc (p.1 : ℚ) * ((repB p.1 : ℚ) * (repA p.2 : ℚ))
            = ((p.1 : ℚ) * (repB p.1 : ℚ)) * (repA p.2 : ℚ) := by ring
          _ = (ξ * (repA p.1 : ℚ)) * (repA p.2 : ℚ) := by rw [h1Q]
          _ = (ξ * (repA p.2 : ℚ)) * (repA p.1 : ℚ) := by ring
          _ = ((p.2 : ℚ) * (repB p.2 : ℚ)) * (repA p.1 : ℚ) := by rw [h2Q]
          _ = (p.2 : ℚ) * ((repA p.1 : ℚ) * (repB p.2 : ℚ)) := by ring
      exact_mod_cast hQ
    have hratio : p.2 / Nat.gcd p.1 p.2 ≤ repB p.1 * repA p.2 := by
      set g := Nat.gcd p.1 p.2
      have hgpos : 0 < g := Nat.gcd_pos_of_pos_left p.2 (hUpos p.1 hp1)
      have hcop : Nat.Coprime (p.1 / g) (p.2 / g) := Nat.coprime_div_gcd_div_gcd hgpos
      have hdvd : (p.2 / g) ∣ (p.1 / g) * (repB p.1 * repA p.2) := by
        use repA p.1 * repB p.2
        have h1 : g * ((p.1 / g) * (repB p.1 * repA p.2)) = g * ((p.2 / g) * (repA p.1 * repB p.2)) := by
          calc g * ((p.1 / g) * (repB p.1 * repA p.2))
              = (g * (p.1 / g)) * (repB p.1 * repA p.2) := by ring
            _ = p.1 * (repB p.1 * repA p.2) := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
            _ = p.2 * (repA p.1 * repB p.2) := hcross
            _ = (g * (p.2 / g)) * (repA p.1 * repB p.2) := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
            _ = g * ((p.2 / g) * (repA p.1 * repB p.2)) := by ring
        exact Nat.eq_of_mul_eq_mul_left hgpos h1
      have hdvd' : (p.2 / g) ∣ repB p.1 * repA p.2 := hcop.symm.dvd_of_dvd_mul_left hdvd
      exact Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd'
    have hp2_le : (p.2 : ℝ) ≤ (C * (m : ℝ)) * (Nat.gcd p.1 p.2 : ℝ) := by
      have hmul_le : repB p.1 * repA p.2 ≤ B * A := Nat.mul_le_mul hr1.2.2.2.1 hr2.2.1
      have h1 : p.2 ≤ (B * A) * Nat.gcd p.1 p.2 := by
        calc p.2 = (p.2 / Nat.gcd p.1 p.2) * Nat.gcd p.1 p.2 :=
              (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
          _ ≤ (repB p.1 * repA p.2) * Nat.gcd p.1 p.2 := Nat.mul_le_mul_right _ hratio
          _ ≤ (B * A) * Nat.gcd p.1 p.2 := Nat.mul_le_mul_right _ hmul_le
      have h1R : (p.2 : ℝ) ≤ ((A : ℝ) * (B : ℝ)) * (Nat.gcd p.1 p.2 : ℝ) := by
        have : (p.2 : ℝ) ≤ ((B : ℝ) * (A : ℝ)) * (Nat.gcd p.1 p.2 : ℝ) := by exact_mod_cast h1
        linarith
      exact h1R.trans (mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg _))
    have hlow : 1 / (C * (N0 : ℝ) ^ 2) ≤ 2 * (1 / (2 * (m : ℝ))) * ((Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)) := by
      have hp2pos : (0 : ℝ) < p.2 := by exact_mod_cast hUpos p.2 hp2
      have hCm_pos : 0 < C * (m : ℝ) := mul_pos (by linarith) hm_pos
      have hfrac : 1 / (C * (m : ℝ)) ≤ (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) := by
        rw [div_le_div_iff₀ hCm_pos hp2pos]
        linarith
      have hN0ge : (m : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hm_small.le
      have hCm2_pos : 0 < C * (m : ℝ) ^ 2 := mul_pos (by linarith) (pow_pos hm_pos 2)
      calc 1 / (C * (N0 : ℝ) ^ 2)
          ≤ 1 / (C * (m : ℝ) ^ 2) := by
            refine one_div_le_one_div_of_le hCm2_pos ?_
            have : (m : ℝ) ^ 2 ≤ (N0 : ℝ) ^ 2 := by nlinarith
            nlinarith
        _ = (1 / (m : ℝ)) * (1 / (C * (m : ℝ))) := by field_simp [hm_pos.ne', (show C ≠ 0 by linarith)]
        _ ≤ (1 / (m : ℝ)) * ((Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hfrac (one_div_nonneg.mpr hm_pos.le)
        _ = 2 * (1 / (2 * (m : ℝ))) * ((Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)) := by
            have hmne : (m : ℝ) ≠ 0 := hm_pos.ne'
            have h2m : (2 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hmne
            rw [show 2 * (1 / (2 * (m : ℝ))) = 1 / (m : ℝ) by field_simp [hmne]]
    exact (min_le_right _ _).trans (hlow.trans hmatch)
  -- Large case: N0 ≤ m
  push Not at hm_small
  -- Independent set bound: any U0 ⊆ U with pairwise reduced ratio height > S^2 has card ≤ m / 2
  have hindep_bound : ∀ U0 ⊆ U,
      (∀ u ∈ U0, ∀ v ∈ U0, u ≠ v → S ^ 2 * Nat.gcd u v < max u v) →
      (U0.card : ℝ) ≤ (m : ℝ) / 2 := by
    intro U0 hU0U hU0_sep
    let BadA := U0.filter (fun u => S < smoothPart P (repA u))
    let BadB := U0.filter (fun u => S < smoothPart P (repB u))
    let Good := U0.filter (fun u => smoothPart P (repA u) ≤ S ∧ smoothPart P (repB u) ≤ S)
    have hBadA : (BadA.card : ℝ) ≤ (m : ℝ) / 8 := by
      have himg : BadA.image (fun u => (repA u, repB u)) ⊆
          ((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)) ×ˢ Finset.Icc 1 B := by
        intro p hp
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
        have hu' := Finset.mem_filter.mp hu
        have hr := hrep_spec u (hU0U hu'.1)
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr.1, hr.2.1⟩, hu'.2⟩,
          Finset.mem_Icc.mpr ⟨hr.2.2.1, hr.2.2.2.1⟩⟩
      have hcard : BadA.card ≤ ((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card * B := by
        calc BadA.card
            = (BadA.image (fun u => (repA u, repB u))).card :=
              (Finset.card_image_of_injOn (hrep_inj.mono (by exact_mod_cast (Finset.filter_subset _ U0).trans hU0U))).symm
          _ ≤ (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)) ×ˢ Finset.Icc 1 B).card :=
              Finset.card_le_card himg
          _ = ((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card * B := by simp
      have hcardR : (BadA.card : ℝ) ≤ (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ) * (B : ℝ) := by
        exact_mod_cast hcard
      calc (BadA.card : ℝ)
          ≤ (((Finset.Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ) * (B : ℝ) := hcardR
        _ ≤ ((A : ℝ) * A_P / Real.sqrt (S : ℝ)) * (B : ℝ) :=
            mul_le_mul_of_nonneg_right (count_smooth_gt_le P hPprime A S hS1) (Nat.cast_nonneg B)
        _ = ((A : ℝ) * (B : ℝ)) * (A_P / Real.sqrt (S : ℝ)) := by ring
        _ ≤ (C * (m : ℝ)) * (1 / (8 * C)) :=
            mul_le_mul hAB hS_bd (by positivity) (by positivity)
        _ = (m : ℝ) / 8 := by field_simp
    have hBadB : (BadB.card : ℝ) ≤ (m : ℝ) / 8 := by
      have himg : BadB.image (fun u => (repA u, repB u)) ⊆
          Finset.Icc 1 A ×ˢ ((Finset.Icc 1 B).filter (fun b => S < smoothPart P b)) := by
        intro p hp
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
        have hu' := Finset.mem_filter.mp hu
        have hr := hrep_spec u (hU0U hu'.1)
        exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hr.1, hr.2.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr.2.2.1, hr.2.2.2.1⟩, hu'.2⟩⟩
      have hcard : BadB.card ≤ A * ((Finset.Icc 1 B).filter (fun b => S < smoothPart P b)).card := by
        calc BadB.card
            = (BadB.image (fun u => (repA u, repB u))).card :=
              (Finset.card_image_of_injOn (hrep_inj.mono (by exact_mod_cast (Finset.filter_subset _ U0).trans hU0U))).symm
          _ ≤ (Finset.Icc 1 A ×ˢ ((Finset.Icc 1 B).filter (fun b => S < smoothPart P b))).card :=
              Finset.card_le_card himg
          _ = A * ((Finset.Icc 1 B).filter (fun b => S < smoothPart P b)).card := by simp
      have hcardR : (BadB.card : ℝ) ≤ (A : ℝ) * (((Finset.Icc 1 B).filter (fun b => S < smoothPart P b)).card : ℝ) := by
        exact_mod_cast hcard
      calc (BadB.card : ℝ)
          ≤ (A : ℝ) * (((Finset.Icc 1 B).filter (fun b => S < smoothPart P b)).card : ℝ) := hcardR
        _ ≤ (A : ℝ) * ((B : ℝ) * A_P / Real.sqrt (S : ℝ)) :=
            mul_le_mul_of_nonneg_left (count_smooth_gt_le P hPprime B S hS1) (Nat.cast_nonneg A)
        _ = ((A : ℝ) * (B : ℝ)) * (A_P / Real.sqrt (S : ℝ)) := by ring
        _ ≤ (C * (m : ℝ)) * (1 / (8 * C)) :=
            mul_le_mul hAB hS_bd (by positivity) (by positivity)
        _ = (m : ℝ) / 8 := by field_simp
    -- On Good, (roughPart P (repA u), roughPart P (repB u)) is injective!
    have hrough_inj : Set.InjOn (fun u => (roughPart P (repA u), roughPart P (repB u))) (Good : Set ℕ) := by
      intro u hu v hv heq
      by_contra huv
      simp only [Finset.mem_coe, Good, Finset.mem_filter] at hu hv
      have hru := hrep_spec u (hU0U hu.1)
      have hrv := hrep_spec v (hU0U hv.1)
      have hreqA : roughPart P (repA u) = roughPart P (repA v) := congrArg Prod.fst heq
      have hreqB : roughPart P (repB u) = roughPart P (repB v) := congrArg Prod.snd heq
      have hsm_uA := smoothPart_mul_roughPart P (by omega : 0 < repA u)
      have hsm_uB := smoothPart_mul_roughPart P (by omega : 0 < repB u)
      have hsm_vA := smoothPart_mul_roughPart P (by omega : 0 < repA v)
      have hsm_vB := smoothPart_mul_roughPart P (by omega : 0 < repB v)
      have hroughA_pos : 0 < roughPart P (repA u) := by
        by_contra h0; push Not at h0; have : roughPart P (repA u) = 0 := by omega
        rw [this, mul_zero] at hsm_uA; omega
      have hroughB_pos : 0 < roughPart P (repB u) := by
        by_contra h0; push Not at h0; have : roughPart P (repB u) = 0 := by omega
        rw [this, mul_zero] at hsm_uB; omega
      -- Cross-multiply u/v = (sA(u)*sB(v)) / (sA(v)*sB(u))
      have hcross : u * (smoothPart P (repA v) * smoothPart P (repB u)) =
          v * (smoothPart P (repA u) * smoothPart P (repB v)) := by
        have h1Q : (u : ℚ) * (repB u : ℚ) = ξ * (repA u : ℚ) := by
          rw [hru.2.2.2.2]; field_simp [show (repB u : ℚ) ≠ 0 by exact_mod_cast (by omega : repB u ≠ 0)]
        have h2Q : (v : ℚ) * (repB v : ℚ) = ξ * (repA v : ℚ) := by
          rw [hrv.2.2.2.2]; field_simp [show (repB v : ℚ) ≠ 0 by exact_mod_cast (by omega : repB v ≠ 0)]
        have hfull : u * (repB u * repA v) = v * (repA u * repB v) := by
          have hQ : (u : ℚ) * ((repB u : ℚ) * (repA v : ℚ)) = (v : ℚ) * ((repA u : ℚ) * (repB v : ℚ)) := by
            calc (u : ℚ) * ((repB u : ℚ) * (repA v : ℚ))
                = ((u : ℚ) * (repB u : ℚ)) * (repA v : ℚ) := by ring
              _ = (ξ * (repA u : ℚ)) * (repA v : ℚ) := by rw [h1Q]
              _ = (ξ * (repA v : ℚ)) * (repA u : ℚ) := by ring
              _ = ((v : ℚ) * (repB v : ℚ)) * (repA u : ℚ) := by rw [h2Q]
              _ = (v : ℚ) * ((repA u : ℚ) * (repB v : ℚ)) := by ring
          exact_mod_cast hQ
        have hmul_cancel : (roughPart P (repA u) * roughPart P (repB u)) *
            (u * (smoothPart P (repA v) * smoothPart P (repB u))) =
            (roughPart P (repA u) * roughPart P (repB u)) *
            (v * (smoothPart P (repA u) * smoothPart P (repB v))) := by
          calc (roughPart P (repA u) * roughPart P (repB u)) *
                (u * (smoothPart P (repA v) * smoothPart P (repB u)))
              = u * ((smoothPart P (repB u) * roughPart P (repB u)) *
                  (smoothPart P (repA v) * roughPart P (repA v))) := by rw [← hreqA]; ring
            _ = u * (repB u * repA v) := by rw [hsm_uB, hsm_vA]
            _ = v * (repA u * repB v) := hfull
            _ = v * ((smoothPart P (repA u) * roughPart P (repA u)) *
                  (smoothPart P (repB v) * roughPart P (repB v))) := by rw [hsm_uA, hsm_vB]
            _ = (roughPart P (repA u) * roughPart P (repB u)) *
                (v * (smoothPart P (repA u) * smoothPart P (repB v))) := by rw [← hreqB]; ring
        exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hroughA_pos hroughB_pos) hmul_cancel
      set g := Nat.gcd u v
      have hgpos : 0 < g := Nat.gcd_pos_of_pos_left v (hUpos u (hU0U hu.1))
      have hcop : Nat.Coprime (u / g) (v / g) := Nat.coprime_div_gcd_div_gcd hgpos
      have hdiv_eq : (u / g) * (smoothPart P (repA v) * smoothPart P (repB u)) =
          (v / g) * (smoothPart P (repA u) * smoothPart P (repB v)) := by
        apply Nat.eq_of_mul_eq_mul_left hgpos
        calc g * ((u / g) * (smoothPart P (repA v) * smoothPart P (repB u)))
            = (g * (u / g)) * (smoothPart P (repA v) * smoothPart P (repB u)) := by ring
          _ = u * (smoothPart P (repA v) * smoothPart P (repB u)) := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
          _ = v * (smoothPart P (repA u) * smoothPart P (repB v)) := hcross
          _ = (g * (v / g)) * (smoothPart P (repA u) * smoothPart P (repB v)) := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
          _ = g * ((v / g) * (smoothPart P (repA u) * smoothPart P (repB v))) := by ring
      have hu_le : u / g ≤ S ^ 2 := by
        have hdvd : (u / g) ∣ smoothPart P (repA u) * smoothPart P (repB v) :=
          hcop.dvd_of_dvd_mul_left ⟨smoothPart P (repA v) * smoothPart P (repB u), hdiv_eq.symm⟩
        have hpos : 0 < smoothPart P (repA u) * smoothPart P (repB v) :=
          Nat.mul_pos (smoothPart_pos P hPprime _) (smoothPart_pos P hPprime _)
        exact (Nat.le_of_dvd hpos hdvd).trans (by rw [sq]; exact Nat.mul_le_mul hu.2.1 hv.2.2)
      have hv_le : v / g ≤ S ^ 2 := by
        have hdvd : (v / g) ∣ smoothPart P (repA v) * smoothPart P (repB u) :=
          hcop.symm.dvd_of_dvd_mul_left ⟨smoothPart P (repA u) * smoothPart P (repB v), hdiv_eq⟩
        have hpos : 0 < smoothPart P (repA v) * smoothPart P (repB u) :=
          Nat.mul_pos (smoothPart_pos P hPprime _) (smoothPart_pos P hPprime _)
        exact (Nat.le_of_dvd hpos hdvd).trans (by rw [sq]; exact Nat.mul_le_mul hv.2.1 hu.2.2)
      have hmax_le : max u v ≤ S ^ 2 * g := by
        rw [max_le_iff]
        constructor
        · calc u = (u / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
            _ ≤ S ^ 2 * g := Nat.mul_le_mul_right g hu_le
        · calc v = (v / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
            _ ≤ S ^ 2 * g := Nat.mul_le_mul_right g hv_le
      have hsep := hU0_sep u hu.1 v hv.1 huv
      dsimp only [g] at hmax_le
      omega
    -- Bound Good.card ≤ m / 4 by counting rough parts along the larger of A, B
    have hABge : m ≤ A * B := by
      have himg : U.image (fun u => (repA u, repB u)) ⊆ Finset.Icc 1 A ×ˢ Finset.Icc 1 B := by
        intro p hp
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
        have hr := hrep_spec u hu
        exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hr.1, hr.2.1⟩, Finset.mem_Icc.mpr ⟨hr.2.2.1, hr.2.2.2.1⟩⟩
      calc m = (U.image (fun u => (repA u, repB u))).card := (Finset.card_image_of_injOn hrep_inj).symm
        _ ≤ (Finset.Icc 1 A ×ˢ Finset.Icc 1 B).card := Finset.card_le_card himg
        _ = A * B := by simp
    have hGood : (Good.card : ℝ) ≤ (m : ℝ) / 4 := by
      have hbound_side : ∀ (X Y : ℕ), 1 ≤ X → 1 ≤ Y → Y ≤ X → ((X : ℝ) * (Y : ℝ) ≤ C * (m : ℝ)) →
          m ≤ X * Y →
          (((Finset.Icc 1 X).filter (fun x => ∀ p ∈ P, ¬ p ∣ x)).card : ℝ) * (Y : ℝ) ≤ (m : ℝ) / 4 := by
        intro X Y hX1 hY1 hYX hXY_ub hXY_lb
        have hXsq : (m : ℝ) ≤ (X : ℝ) ^ 2 := by
          have : m ≤ X * X := hXY_lb.trans (Nat.mul_le_mul_left X hYX)
          have hR : (m : ℝ) ≤ (X : ℝ) * (X : ℝ) := by exact_mod_cast this
          linarith [sq (X : ℝ)]
        have hXge_sqrt : Real.sqrt (m : ℝ) ≤ (X : ℝ) := by
          rw [← Real.sqrt_sq (Nat.cast_nonneg X)]
          exact Real.sqrt_le_sqrt hXsq
        have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
        have hY_ub : (Y : ℝ) ≤ C * (m : ℝ) / (X : ℝ) := by
          rw [le_div_iff₀ hXpos]; linarith
        have hterm2 : (2 : ℝ) ^ P.card * (Y : ℝ) ≤ (m : ℝ) / 8 := by
          have hN0_bd : 8 * C * (2 : ℝ) ^ P.card ≤ Real.sqrt (m : ℝ) := by
            have h1 : (8 * C * (2 : ℝ) ^ P.card) ^ 2 ≤ (N0 : ℝ) :=
              (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 2 _))
            have h2 : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_small
            rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 8 * C * (2 : ℝ) ^ P.card)]
            exact Real.sqrt_le_sqrt (h1.trans h2)
          calc (2 : ℝ) ^ P.card * (Y : ℝ)
              ≤ (2 : ℝ) ^ P.card * (C * (m : ℝ) / (X : ℝ)) :=
                mul_le_mul_of_nonneg_left hY_ub (by positivity)
            _ ≤ (2 : ℝ) ^ P.card * (C * (m : ℝ) / Real.sqrt (m : ℝ)) := by
                gcongr
            _ = (C * (2 : ℝ) ^ P.card) * Real.sqrt (m : ℝ) := by
                have hsq : (m : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := (Real.mul_self_sqrt hm_pos.le).symm
                have hsqpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
                field_simp
                rw [Real.sq_sqrt hm_pos.le]
            _ ≤ (Real.sqrt (m : ℝ) / 8) * Real.sqrt (m : ℝ) := by
                have : C * (2 : ℝ) ^ P.card ≤ Real.sqrt (m : ℝ) / 8 := by linarith
                exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
            _ = (m : ℝ) / 8 := by
                have := Real.mul_self_sqrt hm_pos.le
                linarith
        calc (((Finset.Icc 1 X).filter (fun x => ∀ p ∈ P, ¬ p ∣ x)).card : ℝ) * (Y : ℝ)
            ≤ ((X : ℝ) * ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) + (2 : ℝ) ^ P.card) * (Y : ℝ) :=
              mul_le_mul_of_nonneg_right (count_rough_le P hPprime X) (Nat.cast_nonneg Y)
          _ = ((X : ℝ) * (Y : ℝ)) * (∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))) + (2 : ℝ) ^ P.card * (Y : ℝ) := by ring
          _ ≤ (C * (m : ℝ)) * (1 / (8 * C)) + (m : ℝ) / 8 := by
              refine add_le_add ?_ hterm2
              refine mul_le_mul hXY_ub hdP ?_ (by positivity)
              refine Finset.prod_nonneg fun p hp => ?_
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPprime p hp).two_le
              have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by positivity)]; linarith
              linarith
          _ = (m : ℝ) / 4 := by field_simp; ring
      rcases le_total B A with hBA | hAB_le
      · have himg : Good.image (fun u => (roughPart P (repA u), roughPart P (repB u))) ⊆
            ((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)) ×ˢ Finset.Icc 1 B := by
          intro p hp
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
          have hr := hrep_spec u (hU0U (Finset.mem_filter.mp hu).1)
          have hrA_pos : 0 < roughPart P (repA u) := by
            have hmul := smoothPart_mul_roughPart P (by omega : 0 < repA u)
            by_contra h0; push Not at h0; have hz : roughPart P (repA u) = 0 := by omega
            rw [hz, mul_zero] at hmul; omega
          have hrB_pos : 0 < roughPart P (repB u) := by
            have hmul := smoothPart_mul_roughPart P (by omega : 0 < repB u)
            by_contra h0; push Not at h0; have hz : roughPart P (repB u) = 0 := by omega
            rw [hz, mul_zero] at hmul; omega
          exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
            ⟨hrA_pos, (Nat.div_le_self _ _).trans hr.2.1⟩,
            fun q hq => roughPart_not_dvd P hPprime (by omega) hq⟩,
            Finset.mem_Icc.mpr ⟨hrB_pos, (Nat.div_le_self _ _).trans hr.2.2.2.1⟩⟩
        have hcard : Good.card ≤ ((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card * B := by
          calc Good.card
              = (Good.image (fun u => (roughPart P (repA u), roughPart P (repB u)))).card :=
                (Finset.card_image_of_injOn hrough_inj).symm
            _ ≤ (((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)) ×ˢ Finset.Icc 1 B).card :=
                Finset.card_le_card himg
            _ = ((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card * B := by simp
        have hcardR : (Good.card : ℝ) ≤
            (((Finset.Icc 1 A).filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card : ℝ) * (B : ℝ) := by
          exact_mod_cast hcard
        exact hcardR.trans (hbound_side A B hA1 hB1 hBA hAB hABge)
      · have himg : Good.image (fun u => (roughPart P (repA u), roughPart P (repB u))) ⊆
            Finset.Icc 1 A ×ˢ ((Finset.Icc 1 B).filter (fun b => ∀ p ∈ P, ¬ p ∣ b)) := by
          intro p hp
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
          have hr := hrep_spec u (hU0U (Finset.mem_filter.mp hu).1)
          have hrA_pos : 0 < roughPart P (repA u) := by
            have hmul := smoothPart_mul_roughPart P (by omega : 0 < repA u)
            by_contra h0; push Not at h0; have hz : roughPart P (repA u) = 0 := by omega
            rw [hz, mul_zero] at hmul; omega
          have hrB_pos : 0 < roughPart P (repB u) := by
            have hmul := smoothPart_mul_roughPart P (by omega : 0 < repB u)
            by_contra h0; push Not at h0; have hz : roughPart P (repB u) = 0 := by omega
            rw [hz, mul_zero] at hmul; omega
          exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hrA_pos, (Nat.div_le_self _ _).trans hr.2.1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrB_pos, (Nat.div_le_self _ _).trans hr.2.2.2.1⟩,
            fun q hq => roughPart_not_dvd P hPprime (by omega) hq⟩⟩
        have hcard : Good.card ≤ A * ((Finset.Icc 1 B).filter (fun b => ∀ p ∈ P, ¬ p ∣ b)).card := by
          calc Good.card
              = (Good.image (fun u => (roughPart P (repA u), roughPart P (repB u)))).card :=
                (Finset.card_image_of_injOn hrough_inj).symm
            _ ≤ (Finset.Icc 1 A ×ˢ ((Finset.Icc 1 B).filter (fun b => ∀ p ∈ P, ¬ p ∣ b))).card :=
                Finset.card_le_card himg
            _ = A * ((Finset.Icc 1 B).filter (fun b => ∀ p ∈ P, ¬ p ∣ b)).card := by simp
        have hcardR : (Good.card : ℝ) ≤
            (((Finset.Icc 1 B).filter (fun b => ∀ p ∈ P, ¬ p ∣ b)).card : ℝ) * (A : ℝ) := by
          have : (Good.card : ℝ) ≤ (A : ℝ) * (((Finset.Icc 1 B).filter (fun b => ∀ p ∈ P, ¬ p ∣ b)).card : ℝ) := by
            exact_mod_cast hcard
          linarith
        exact hcardR.trans (hbound_side B A hB1 hA1 hAB_le (by linarith) (by linarith))
    have hcover : U0 ⊆ BadA ∪ BadB ∪ Good := by
      intro u hu
      simp only [Finset.mem_union, BadA, BadB, Good, Finset.mem_filter]
      by_cases h1 : S < smoothPart P (repA u)
      · exact Or.inl (Or.inl ⟨hu, h1⟩)
      · by_cases h2 : S < smoothPart P (repB u)
        · exact Or.inl (Or.inr ⟨hu, h2⟩)
        · exact Or.inr ⟨hu, not_lt.mp h1, not_lt.mp h2⟩
    have hc := (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hcR : (U0.card : ℝ) ≤ (BadA.card : ℝ) + (BadB.card : ℝ) + (Good.card : ℝ) := by
      exact_mod_cast hc
    linarith
  -- Construct a maximal matching in U with edge predicate max u v ≤ S^2 * gcd u v
  let E : ℕ → ℕ → Prop := fun u v => max u v ≤ S ^ 2 * Nat.gcd u v
  have hEsym : ∀ u v, E u v → E v u := by
    intro u v h; simp only [E, max_comm, Nat.gcd_comm] at h ⊢; exact h
  obtain ⟨M, hMmem, hMdisj, hMindep⟩ := exists_maximal_matching U E hEsym
  let VM := M.biUnion (fun p => ({p.1, p.2} : Finset ℕ))
  have hU'_bound : ((U \ VM).card : ℝ) ≤ (m : ℝ) / 2 := by
    refine hindep_bound (U \ VM) Finset.sdiff_subset fun u hu v hv huv => ?_
    exact not_le.mp (hMindep u hu v hv huv)
  have hVM_card : VM.card ≤ 2 * M.card := by
    calc VM.card ≤ ∑ p ∈ M, ({p.1, p.2} : Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ M, 2 := Finset.sum_le_sum fun p _ => by
          calc ({p.1, p.2} : Finset ℕ).card ≤ 1 + ({p.2} : Finset ℕ).card := Finset.card_insert_le _ _
            _ = 2 := by simp
      _ = 2 * M.card := by simp [mul_comm]
  have hMcard : (m : ℝ) / 4 ≤ (M.card : ℝ) := by
    have h1 : m ≤ (U \ VM).card + VM.card := by
      have := Finset.card_le_card (show U ⊆ (U \ VM) ∪ VM from fun x hx => by
        by_cases h : x ∈ VM
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
      exact this.trans (Finset.card_union_le _ _)
    have h1R : (m : ℝ) ≤ ((U \ VM).card : ℝ) + (VM.card : ℝ) := by exact_mod_cast h1
    have hVMR : (VM.card : ℝ) ≤ 2 * (M.card : ℝ) := by exact_mod_cast hVM_card
    linarith
  have hMsnd_inj : Set.InjOn Prod.snd (M : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    by_contra hpq
    have hd := hMdisj p hp q hq hpq
    rw [Finset.disjoint_left] at hd
    exact hd (Finset.mem_insert_of_mem (Finset.mem_singleton_self p.2))
      (by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q.2))
  have hmatch := typeILoss_ge_of_matching hUpos (by positivity : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)))
    M (fun p hp => ⟨(hMmem p hp).1, (hMmem p hp).2.1, (hMmem p hp).2.2.1⟩) hMsnd_inj
  have hsum_lb : (M.card : ℝ) * (1 / ((S : ℝ) ^ 2)) ≤ ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) := by
    calc (M.card : ℝ) * (1 / ((S : ℝ) ^ 2))
        = ∑ _p ∈ M, (1 / ((S : ℝ) ^ 2)) := by simp
      _ ≤ ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := hMmem p hp
          have hp2pos : (0 : ℝ) < p.2 := by exact_mod_cast hUpos p.2 hp'.2.1
          have hE : p.2 ≤ S ^ 2 * Nat.gcd p.1 p.2 := by
            have := hp'.2.2.2
            simp only [E] at this
            rwa [max_eq_right hp'.2.2.1.le] at this
          have hER : (p.2 : ℝ) ≤ (S : ℝ) ^ 2 * (Nat.gcd p.1 p.2 : ℝ) := by exact_mod_cast hE
          have hS2pos : (0 : ℝ) < (S : ℝ) ^ 2 := pow_pos (by exact_mod_cast hS1) 2
          rw [div_le_div_iff₀ hS2pos hp2pos]
          linarith
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS1
  have hlow : 1 / (4 * (S : ℝ) ^ 2) ≤ 2 * (1 / (2 * (m : ℝ))) * ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) := by
    calc 1 / (4 * (S : ℝ) ^ 2)
        = (1 / (m : ℝ)) * (((m : ℝ) / 4) * (1 / (S : ℝ) ^ 2)) := by field_simp [hm_pos.ne', hSpos.ne']
      _ ≤ (1 / (m : ℝ)) * ((M.card : ℝ) * (1 / (S : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMcard (by positivity)) (by positivity)
      _ ≤ (1 / (m : ℝ)) * ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_lb (by positivity)
      _ = 2 * (1 / (2 * (m : ℝ))) * ∑ p ∈ M, (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) := by
          field_simp [hm_pos.ne']
  exact (min_le_left _ _).trans (hlow.trans hmatch)

end LRMod1Box

/-!
Module 1c:
1. Elementary telescoping tail bound for ∑ n^{-(1+α)}
2. Shared p-adic defect counting (Green-Walker Prop 1.3 + Hu-Jing Prop 7.1)
3. Green-Walker GCD extremal bound (Theorem 1.1 / Hu-Jing Theorem 6.2) at q₀ = 9/4
4. Hu-Jing rational box extraction (Prop 7.1) and linear Type I loss (Theorem 7.2)
-/

namespace LRMod1GCD

open Finset BigOperators

section TailBound

lemma rpow_step_le_diff {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (-(1 + α)) ≤ (1 / α) * (((n - 1 : ℕ) : ℝ) ^ (-α) - (n : ℝ) ^ (-α)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hnm1_eq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  set t : ℝ := ((n - 1 : ℕ) : ℝ) / (n : ℝ) with ht_def
  have ht_pos : 0 < t := div_pos hnm1_pos hn_pos
  have hlog : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht_pos
  have hexp : 1 + α * (1 - t) ≤ t ^ (-α) := by
    rw [Real.rpow_def_of_pos ht_pos]
    have h1 : α * (1 - t) ≤ Real.log t * (-α) := by nlinarith
    have h2 := Real.add_one_le_exp (Real.log t * (-α))
    linarith
  have h1mt : 1 - t = 1 / (n : ℝ) := by
    rw [ht_def, hnm1_eq]; field_simp; ring
  have htrpow : t ^ (-α) = ((n - 1 : ℕ) : ℝ) ^ (-α) / (n : ℝ) ^ (-α) :=
    Real.div_rpow hnm1_pos.le hn_pos.le (-α)
  rw [h1mt, htrpow] at hexp
  have hnα_pos : 0 < (n : ℝ) ^ (-α) := Real.rpow_pos_of_pos hn_pos (-α)
  have hmul : α * (1 / (n : ℝ)) * (n : ℝ) ^ (-α) ≤
      (((n - 1 : ℕ) : ℝ) ^ (-α) / (n : ℝ) ^ (-α) - 1) * (n : ℝ) ^ (-α) := by
    refine mul_le_mul_of_nonneg_right ?_ hnα_pos.le
    linarith
  have hrhs : (((n - 1 : ℕ) : ℝ) ^ (-α) / (n : ℝ) ^ (-α) - 1) * (n : ℝ) ^ (-α) =
      ((n - 1 : ℕ) : ℝ) ^ (-α) - (n : ℝ) ^ (-α) := by
    field_simp
  have hlhs : (1 / (n : ℝ)) * (n : ℝ) ^ (-α) = (n : ℝ) ^ (-(1 + α)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hn_pos]
    congr 1; ring
  rw [hrhs, mul_assoc, hlhs] at hmul
  rw [one_div, inv_mul_eq_div, le_div_iff₀' hα]
  exact hmul

lemma sum_Ico_rpow_diff_le {α : ℝ} {M K : ℕ} (hMK : M ≤ K) :
    ∑ n ∈ Finset.Ico M K, (((n - 1 : ℕ) : ℝ) ^ (-α) - (n : ℝ) ^ (-α)) ≤
      ((M - 1 : ℕ) : ℝ) ^ (-α) := by
  induction K, hMK using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.sum_empty]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  | succ k hMk ih =>
    have htele : ∑ n ∈ Finset.Ico M (k + 1), (((n - 1 : ℕ) : ℝ) ^ (-α) - (n : ℝ) ^ (-α)) =
        ((M - 1 : ℕ) : ℝ) ^ (-α) - (k : ℝ) ^ (-α) := by
      clear ih
      induction k, hMk using Nat.le_induction with
      | base =>
        rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
      | succ j hMj ihj =>
        rw [Finset.sum_Ico_succ_top (by omega : M ≤ j + 1), ihj]
        simp only [Nat.add_sub_cancel]
        ring
    rw [htele]
    have hnn : 0 ≤ (k : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg k) _
    linarith

lemma rpow_tail_sum_le {α : ℝ} (hα : 0 < α) {M : ℕ} (hM : 2 ≤ M) (F : Finset ℕ)
    (hF : ∀ n ∈ F, M ≤ n) :
    ∑ n ∈ F, (n : ℝ) ^ (-(1 + α)) ≤ (1 / α) * ((M - 1 : ℕ) : ℝ) ^ (-α) := by
  let K : ℕ := max M (F.sup id + 1)
  have hsub : F ⊆ Finset.Ico M K := by
    intro n hn
    rw [Finset.mem_Ico]
    have hle : n ≤ F.sup id := Finset.le_sup (f := id) hn
    exact ⟨hF n hn, lt_of_lt_of_le (Nat.lt_succ_of_le hle) (le_max_right _ _)⟩
  calc ∑ n ∈ F, (n : ℝ) ^ (-(1 + α))
      ≤ ∑ n ∈ Finset.Ico M K, (n : ℝ) ^ (-(1 + α)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ∑ n ∈ Finset.Ico M K, (1 / α) * (((n - 1 : ℕ) : ℝ) ^ (-α) - (n : ℝ) ^ (-α)) :=
        Finset.sum_le_sum fun n hn => rpow_step_le_diff hα (by rw [Finset.mem_Ico] at hn; omega)
    _ = (1 / α) * ∑ n ∈ Finset.Ico M K, (((n - 1 : ℕ) : ℝ) ^ (-α) - (n : ℝ) ^ (-α)) := by
        rw [← Finset.mul_sum]
    _ ≤ (1 / α) * ((M - 1 : ℕ) : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_left (sum_Ico_rpow_diff_le (le_max_left _ _)) (by positivity)

lemma exists_tail_threshold {C α : ℝ} (hC : 0 < C) (hα : 0 < α) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ F : Finset ℕ, (∀ n ∈ F, p0 < n) →
      C * ∑ n ∈ F, (n : ℝ) ^ (-(1 + α)) ≤ 1 / 2 := by
  let p0 : ℕ := max 2 (Nat.ceil ((2 * C / α) ^ (1 / α)))
  refine ⟨p0, le_max_left _ _, fun F hF => ?_⟩
  have hM : 2 ≤ p0 + 1 := by omega
  have hsub : ∀ n ∈ F, p0 + 1 ≤ n := fun n hn => hF n hn
  have htail := rpow_tail_sum_le hα hM F hsub
  simp only [Nat.add_sub_cancel] at htail
  have hp0_ge : (2 * C / α) ^ (1 / α) ≤ (p0 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 _)
  have hp0_pos : (0 : ℝ) < p0 := by exact_mod_cast (by omega : 0 < p0)
  have hp0_rpow : 2 * C / α ≤ (p0 : ℝ) ^ α := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hp0_ge hα.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at h
  have hinv : (p0 : ℝ) ^ (-α) ≤ α / (2 * C) := by
    rw [Real.rpow_neg hp0_pos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hp0_pos α) (by positivity)]
    simpa [inv_div] using hp0_rpow
  calc C * ∑ n ∈ F, (n : ℝ) ^ (-(1 + α))
      ≤ C * ((1 / α) * (p0 : ℝ) ^ (-α)) := mul_le_mul_of_nonneg_left htail hC.le
    _ ≤ C * ((1 / α) * (α / (2 * C))) := by gcongr
    _ = 1 / 2 := by field_simp

end TailBound

section DefectCounting

def defPlus (N a : ℕ) : ℕ :=
  ∏ p ∈ a.primeFactors, if N.factorization p + 1 = a.factorization p then p else 1

def defMinus (N a : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, if a.factorization p + 1 = N.factorization p then p else 1

def defect (N a : ℕ) : ℕ := defPlus N a * defMinus N a

lemma defPlus_pos (N a : ℕ) : 0 < defPlus N a := by
  refine Finset.prod_pos fun p hp => ?_
  split_ifs
  · exact (Nat.prime_of_mem_primeFactors hp).pos
  · exact one_pos

lemma defMinus_pos (N a : ℕ) : 0 < defMinus N a := by
  refine Finset.prod_pos fun p hp => ?_
  split_ifs
  · exact (Nat.prime_of_mem_primeFactors hp).pos
  · exact one_pos

lemma defect_pos (N a : ℕ) : 0 < defect N a :=
  Nat.mul_pos (defPlus_pos N a) (defMinus_pos N a)

lemma factorization_defPlus {N a p : ℕ} (hp : p.Prime) :
    (defPlus N a).factorization p = if N.factorization p + 1 = a.factorization p then 1 else 0 := by
  unfold defPlus
  have hne : ∀ q ∈ a.primeFactors, (if N.factorization q + 1 = a.factorization q then q else 1) ≠ 0 := by
    intro q hq
    split_ifs
    · exact (Nat.prime_of_mem_primeFactors hq).ne_zero
    · exact one_ne_zero
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  have hterm : ∀ q ∈ a.primeFactors,
      (if N.factorization q + 1 = a.factorization q then q else 1).factorization p =
        if q = p ∧ N.factorization q + 1 = a.factorization q then 1 else 0 := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    by_cases hcond : N.factorization q + 1 = a.factorization q
    · rw [if_pos hcond, hqprime.factorization]
      by_cases hqp : q = p
      · subst hqp; simp [hcond]
      · simp [hqp, hcond, Finsupp.single_eq_of_ne (Ne.symm hqp)]
    · rw [if_neg hcond, Nat.factorization_one, Finsupp.zero_apply, if_neg (fun h => hcond h.2)]
  rw [Finset.sum_congr rfl hterm]
  by_cases hcond : N.factorization p + 1 = a.factorization p
  · have hp_mem : p ∈ a.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    rw [if_pos hcond, Finset.sum_eq_single p]
    · simp [hcond]
    · intro q _ hqp; simp [hqp]
    · intro h; exact absurd hp_mem h
  · rw [if_neg hcond]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hqp : q = p
    · subst hqp; simp [hcond]
    · simp [hqp]

lemma factorization_defMinus {N a p : ℕ} (hp : p.Prime) :
    (defMinus N a).factorization p = if a.factorization p + 1 = N.factorization p then 1 else 0 :=
  factorization_defPlus hp

lemma mul_defMinus_eq_mul_defPlus {N a : ℕ} (hN : 0 < N) (ha : 0 < a)
    (hval : ∀ p, p.Prime → ((a.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1) :
    a * defMinus N a = N * defPlus N a := by
  have hlhs_ne : a * defMinus N a ≠ 0 := (Nat.mul_pos ha (defMinus_pos N a)).ne'
  have hrhs_ne : N * defPlus N a ≠ 0 := (Nat.mul_pos hN (defPlus_pos N a)).ne'
  rw [← Nat.factorization_inj hlhs_ne hrhs_ne]
  ext p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul ha.ne' (defMinus_pos N a).ne',
        Nat.factorization_mul hN.ne' (defPlus_pos N a).ne',
        Finsupp.add_apply, Finsupp.add_apply,
        factorization_defMinus hp, factorization_defPlus hp]
    have hv := hval p hp
    split_ifs <;> omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

lemma defect_mul_defect_mul_gcd_sq {N a b : ℕ} (_hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (hval : ∀ p, p.Prime →
      ((a.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs +
      ((b.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1) :
    defect N a * defect N b * (Nat.gcd a b) ^ 2 = a * b := by
  have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hlhs_ne : defect N a * defect N b * (Nat.gcd a b) ^ 2 ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (defect_pos N a) (defect_pos N b)) (pow_pos hgpos 2)).ne'
  have hrhs_ne : a * b ≠ 0 := (Nat.mul_pos ha hb).ne'
  rw [← Nat.factorization_inj hlhs_ne hrhs_ne]
  ext p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (Nat.mul_pos (defect_pos N a) (defect_pos N b)).ne' (pow_pos hgpos 2).ne',
        Nat.factorization_mul (defect_pos N a).ne' (defect_pos N b).ne']
    unfold defect
    rw [Nat.factorization_mul (defPlus_pos N a).ne' (defMinus_pos N a).ne',
        Nat.factorization_mul (defPlus_pos N b).ne' (defMinus_pos N b).ne',
        Nat.factorization_pow, Nat.factorization_gcd ha.ne' hb.ne',
        Nat.factorization_mul ha.ne' hb.ne']
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.inf_apply]
    rw [factorization_defPlus hp, factorization_defMinus hp,
        factorization_defPlus hp, factorization_defMinus hp]
    have hv := hval p hp
    split_ifs <;> omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

lemma count_defect_le {N : ℕ} (hN : 0 < N) {A T : ℝ} (hA : 0 < A) (hT : 0 ≤ T)
    (S : Finset ℕ)
    (hS : ∀ a ∈ S, 0 < a ∧ A ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * A ∧
      ∀ p, p.Prime → ((a.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1) :
    ((S.filter (fun a => (defect N a : ℝ) ≤ T)).card : ℝ) ≤ 2 * T := by
  classical
  let Sf := S.filter (fun a => (defect N a : ℝ) ≤ T)
  let B1 : ℕ := Nat.floor (Real.sqrt (2 * A * T / (N : ℝ)))
  let B2 : ℕ := Nat.floor (Real.sqrt ((N : ℝ) * T / A))
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinj : Set.InjOn (fun a => (defPlus N a, defMinus N a)) (Sf : Set ℕ) := by
    intro a ha b hb heq
    have haS := hS a (Finset.mem_filter.mp ha).1
    have hbS := hS b (Finset.mem_filter.mp hb).1
    have h1 := mul_defMinus_eq_mul_defPlus hN haS.1 haS.2.2.2
    have h2 := mul_defMinus_eq_mul_defPlus hN hbS.1 hbS.2.2.2
    have hp : defPlus N a = defPlus N b := congrArg Prod.fst heq
    have hm : defMinus N a = defMinus N b := congrArg Prod.snd heq
    have hmul : a * defMinus N a = b * defMinus N a := by rw [h1, hp, ← h2, hm]
    exact Nat.eq_of_mul_eq_mul_right (defMinus_pos N a) hmul
  have himg : Sf.image (fun a => (defPlus N a, defMinus N a)) ⊆ Finset.Icc 1 B1 ×ˢ Finset.Icc 1 B2 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have ha_f := Finset.mem_filter.mp ha
    have haS := hS a ha_f.1
    have hrel := mul_defMinus_eq_mul_defPlus hN haS.1 haS.2.2.2
    have hrelR : (a : ℝ) * (defMinus N a : ℝ) = (N : ℝ) * (defPlus N a : ℝ) := by exact_mod_cast hrel
    have hdefR : (defPlus N a : ℝ) * (defMinus N a : ℝ) = (defect N a : ℝ) := by
      unfold defect; push_cast; rfl
    have hplus_sq : (defPlus N a : ℝ) ^ 2 ≤ 2 * A * T / (N : ℝ) := by
      have h1 : (N : ℝ) * (defPlus N a : ℝ) ^ 2 = (a : ℝ) * (defect N a : ℝ) := by
        calc (N : ℝ) * (defPlus N a : ℝ) ^ 2
            = ((N : ℝ) * (defPlus N a : ℝ)) * (defPlus N a : ℝ) := by ring
          _ = ((a : ℝ) * (defMinus N a : ℝ)) * (defPlus N a : ℝ) := by rw [hrelR]
          _ = (a : ℝ) * ((defPlus N a : ℝ) * (defMinus N a : ℝ)) := by ring
          _ = (a : ℝ) * (defect N a : ℝ) := by rw [hdefR]
      rw [le_div_iff₀' hNposR, h1]
      exact mul_le_mul haS.2.2.1 ha_f.2 (Nat.cast_nonneg _) (by positivity)
    have hminus_sq : (defMinus N a : ℝ) ^ 2 ≤ (N : ℝ) * T / A := by
      have h1 : (a : ℝ) * (defMinus N a : ℝ) ^ 2 = (N : ℝ) * (defect N a : ℝ) := by
        calc (a : ℝ) * (defMinus N a : ℝ) ^ 2
            = ((a : ℝ) * (defMinus N a : ℝ)) * (defMinus N a : ℝ) := by ring
          _ = ((N : ℝ) * (defPlus N a : ℝ)) * (defMinus N a : ℝ) := by rw [hrelR]
          _ = (N : ℝ) * ((defPlus N a : ℝ) * (defMinus N a : ℝ)) := by ring
          _ = (N : ℝ) * (defect N a : ℝ) := by rw [hdefR]
      rw [le_div_iff₀' hA]
      have h2 : A * (defMinus N a : ℝ) ^ 2 ≤ (a : ℝ) * (defMinus N a : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right haS.2.1 (sq_nonneg _)
      have h3 : (N : ℝ) * (defect N a : ℝ) ≤ (N : ℝ) * T :=
        mul_le_mul_of_nonneg_left ha_f.2 hNposR.le
      linarith
    have hplus_le : defPlus N a ≤ B1 := by
      refine Nat.le_floor ?_
      rw [← Real.sqrt_sq (Nat.cast_nonneg (defPlus N a))]
      exact Real.sqrt_le_sqrt hplus_sq
    have hminus_le : defMinus N a ≤ B2 := by
      refine Nat.le_floor ?_
      rw [← Real.sqrt_sq (Nat.cast_nonneg (defMinus N a))]
      exact Real.sqrt_le_sqrt hminus_sq
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨defPlus_pos N a, hplus_le⟩,
      Finset.mem_Icc.mpr ⟨defMinus_pos N a, hminus_le⟩⟩
  have hcard : Sf.card ≤ B1 * B2 := by
    calc Sf.card = (Sf.image (fun a => (defPlus N a, defMinus N a))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 B1 ×ˢ Finset.Icc 1 B2).card := Finset.card_le_card himg
      _ = B1 * B2 := by simp
  have hcardR : (Sf.card : ℝ) ≤ (B1 : ℝ) * (B2 : ℝ) := by exact_mod_cast hcard
  have hB1 : (B1 : ℝ) ≤ Real.sqrt (2 * A * T / (N : ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)
  have hB2 : (B2 : ℝ) ≤ Real.sqrt ((N : ℝ) * T / A) := Nat.floor_le (Real.sqrt_nonneg _)
  have hprod : Real.sqrt (2 * A * T / (N : ℝ)) * Real.sqrt ((N : ℝ) * T / A) ≤ 2 * T := by
    rw [← Real.sqrt_mul (by positivity)]
    have heq : (2 * A * T / (N : ℝ)) * ((N : ℝ) * T / A) = 2 * T ^ 2 := by field_simp
    rw [heq]
    have h2le4 : 2 * T ^ 2 ≤ (2 * T) ^ 2 := by nlinarith
    calc Real.sqrt (2 * T ^ 2) ≤ Real.sqrt ((2 * T) ^ 2) := Real.sqrt_le_sqrt h2le4
      _ = 2 * T := Real.sqrt_sq (by positivity)
  exact hcardR.trans ((mul_le_mul hB1 hB2 (Nat.cast_nonneg B2) (Real.sqrt_nonneg _)).trans hprod)

lemma exists_high_degree_subset {X Y : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hYne : Y.Nonempty) (hEsub : E ⊆ X ×ˢ Y) {ρ : ℝ} (hρ : 0 < ρ)
    (hEdens : (ρ / 2) * (X.card : ℝ) * (Y.card : ℝ) ≤ (E.card : ℝ)) :
    let Xhigh := X.filter (fun u => (ρ / 4) * (Y.card : ℝ) ≤ ((E.filter (fun e => e.1 = u)).card : ℝ))
    (ρ / 4) * (X.card : ℝ) ≤ (Xhigh.card : ℝ) := by
  classical
  intro Xhigh
  have hsum : (E.card : ℝ) = ∑ u ∈ X, ((E.filter (fun e => e.1 = u)).card : ℝ) := by
    have hN : E.card = ∑ u ∈ X, (E.filter (fun e => e.1 = u)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := E) (t := X)
        (fun e he => (Finset.mem_product.mp (hEsub he)).1)
    exact_mod_cast hN
  have hdeg_le : ∀ u ∈ X, ((E.filter (fun e => e.1 = u)).card : ℝ) ≤ (Y.card : ℝ) := by
    intro u _
    have h1 : (E.filter (fun e => e.1 = u)).card ≤ Y.card := by
      have himg : (E.filter (fun e => e.1 = u)).image Prod.snd ⊆ Y := by
        intro y hy
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_product.mp (hEsub (Finset.mem_filter.mp he).1)).2
      have hinj : Set.InjOn Prod.snd (E.filter (fun e => e.1 = u) : Set (ℕ × ℕ)) := by
        intro e1 he1 e2 he2 h
        have h1' := (Finset.mem_filter.mp he1).2
        have h2' := (Finset.mem_filter.mp he2).2
        ext <;> [exact h1'.trans h2'.symm; exact h]
      calc (E.filter (fun e => e.1 = u)).card
          = ((E.filter (fun e => e.1 = u)).image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ Y.card := Finset.card_le_card himg
    exact_mod_cast h1
  let Xlow := X.filter (fun u => ¬ ((ρ / 4) * (Y.card : ℝ) ≤ ((E.filter (fun e => e.1 = u)).card : ℝ)))
  have hsplit : ∑ u ∈ X, ((E.filter (fun e => e.1 = u)).card : ℝ) =
      ∑ u ∈ Xhigh, ((E.filter (fun e => e.1 = u)).card : ℝ) +
      ∑ u ∈ Xlow, ((E.filter (fun e => e.1 = u)).card : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not X _ _).symm
  have hpart1 : ∑ u ∈ Xhigh, ((E.filter (fun e => e.1 = u)).card : ℝ) ≤ (Xhigh.card : ℝ) * (Y.card : ℝ) := by
    calc ∑ u ∈ Xhigh, ((E.filter (fun e => e.1 = u)).card : ℝ)
        ≤ ∑ _u ∈ Xhigh, (Y.card : ℝ) := Finset.sum_le_sum fun u hu => hdeg_le u (Finset.mem_filter.mp hu).1
      _ = (Xhigh.card : ℝ) * (Y.card : ℝ) := by simp
  have hpart2 : ∑ u ∈ Xlow, ((E.filter (fun e => e.1 = u)).card : ℝ) ≤
      (X.card : ℝ) * ((ρ / 4) * (Y.card : ℝ)) := by
    calc ∑ u ∈ Xlow, ((E.filter (fun e => e.1 = u)).card : ℝ)
        ≤ ∑ _u ∈ Xlow, ((ρ / 4) * (Y.card : ℝ)) :=
          Finset.sum_le_sum fun u hu => le_of_lt (not_le.mp (Finset.mem_filter.mp hu).2)
      _ = (Xlow.card : ℝ) * ((ρ / 4) * (Y.card : ℝ)) := by simp
      _ ≤ (X.card : ℝ) * ((ρ / 4) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ X)) (by positivity)
  have hYpos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hYne.card_pos
  have hineq : (ρ / 4) * (X.card : ℝ) * (Y.card : ℝ) ≤ (Xhigh.card : ℝ) * (Y.card : ℝ) := by linarith
  exact le_of_mul_le_mul_right hineq hYpos

end DefectCounting

section GreenWalkerGCD

def allPrimes (X Y : Finset ℕ) : Finset ℕ :=
  (X ∪ Y).biUnion Nat.primeFactors

def smlPrimes (p0 : ℕ) (X Y : Finset ℕ) : Finset ℕ :=
  (allPrimes X Y).filter (· ≤ p0)

lemma padic_slice_props {p : ℕ} (hp_prime : p.Prime)
    {A B D : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    {X Y : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (_hEsub : E ⊆ X ×ˢ Y)
    (hX : ∀ x ∈ X, 0 < x ∧ A ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A)
    (hY : ∀ y ∈ Y, 0 < y ∧ B ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * B)
    (hE : ∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ))
    (in_ jn_ : ℕ)
    (hEij : (E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
      e.2 ∈ Y.filter (fun y => y.factorization p = jn_))).Nonempty) :
    let Xi := X.filter (fun x => x.factorization p = in_)
    let Yj := Y.filter (fun y => y.factorization p = jn_)
    let Eij := E.filter (fun e => e.1 ∈ Xi ∧ e.2 ∈ Yj)
    let Xbar := Xi.image (· / p ^ in_)
    let Ybar := Yj.image (· / p ^ jn_)
    let Ebar := Eij.image (fun e => (e.1 / p ^ in_, e.2 / p ^ jn_))
    Xbar.card = Xi.card ∧ Ybar.card = Yj.card ∧ Ebar.card = Eij.card ∧
    Xbar.Nonempty ∧ Ybar.Nonempty ∧ Ebar.Nonempty ∧ Ebar ⊆ Xbar ×ˢ Ybar ∧
    p ∉ allPrimes Xbar Ybar ∧ allPrimes Xbar Ybar ⊆ (allPrimes X Y).erase p ∧
    (∀ u ∈ Xbar, 0 < u ∧ A / (p : ℝ) ^ in_ ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * (A / (p : ℝ) ^ in_)) ∧
    (∀ v ∈ Ybar, 0 < v ∧ B / (p : ℝ) ^ jn_ ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * (B / (p : ℝ) ^ jn_)) ∧
    (∀ e ∈ Ebar, D / (p : ℝ) ^ min in_ jn_ ≤ (Nat.gcd e.1 e.2 : ℝ)) ∧
    ((D / (p : ℝ) ^ min in_ jn_) ^ 2 / ((A / (p : ℝ) ^ in_) * (B / (p : ℝ) ^ jn_)) =
      (D ^ 2 / (A * B)) * (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs) := by
  classical
  intro Xi Yj Eij Xbar Ybar Ebar
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
  have hpi_pos : 0 < p ^ in_ := pow_pos hp_prime.pos in_
  have hpj_pos : 0 < p ^ jn_ := pow_pos hp_prime.pos jn_
  have hpi_dvd : ∀ x ∈ Xi, p ^ in_ ∣ x := fun x hx => by
    rw [← (Finset.mem_filter.mp hx).2]; exact Nat.ordProj_dvd x p
  have hpj_dvd : ∀ y ∈ Yj, p ^ jn_ ∣ y := fun y hy => by
    rw [← (Finset.mem_filter.mp hy).2]; exact Nat.ordProj_dvd y p
  have hXbar_card : Xbar.card = Xi.card := by
    refine Finset.card_image_of_injOn fun x1 hx1 x2 hx2 h => ?_
    calc x1 = p ^ in_ * (x1 / p ^ in_) := (Nat.mul_div_cancel' (hpi_dvd x1 hx1)).symm
      _ = p ^ in_ * (x2 / p ^ in_) := by rw [h]
      _ = x2 := Nat.mul_div_cancel' (hpi_dvd x2 hx2)
  have hYbar_card : Ybar.card = Yj.card := by
    refine Finset.card_image_of_injOn fun y1 hy1 y2 hy2 h => ?_
    calc y1 = p ^ jn_ * (y1 / p ^ jn_) := (Nat.mul_div_cancel' (hpj_dvd y1 hy1)).symm
      _ = p ^ jn_ * (y2 / p ^ jn_) := by rw [h]
      _ = y2 := Nat.mul_div_cancel' (hpj_dvd y2 hy2)
  have hEbar_card : Ebar.card = Eij.card := by
    refine Finset.card_image_of_injOn fun e1 he1 e2 he2 h => ?_
    have he1' := Finset.mem_filter.mp he1
    have he2' := Finset.mem_filter.mp he2
    have h1 : e1.1 / p ^ in_ = e2.1 / p ^ in_ := congrArg Prod.fst h
    have h2 : e1.2 / p ^ jn_ = e2.2 / p ^ jn_ := congrArg Prod.snd h
    ext
    · calc e1.1 = p ^ in_ * (e1.1 / p ^ in_) := (Nat.mul_div_cancel' (hpi_dvd _ he1'.2.1)).symm
        _ = p ^ in_ * (e2.1 / p ^ in_) := by rw [h1]
        _ = e2.1 := Nat.mul_div_cancel' (hpi_dvd _ he2'.2.1)
    · calc e1.2 = p ^ jn_ * (e1.2 / p ^ jn_) := (Nat.mul_div_cancel' (hpj_dvd _ he1'.2.2)).symm
        _ = p ^ jn_ * (e2.2 / p ^ jn_) := by rw [h2]
        _ = e2.2 := Nat.mul_div_cancel' (hpj_dvd _ he2'.2.2)
  have hp_not_all : p ∉ allPrimes Xbar Ybar := by
    intro hmem
    obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hmem
    have hpdvd : p ∣ u := (Nat.mem_primeFactors.mp hpu).2.1
    rcases Finset.mem_union.mp hu with huX | huY
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp huX
      have hx' := Finset.mem_filter.mp hx
      have hxpos := (hX x hx'.1).1
      have hsucc : p ^ (in_ + 1) ∣ x := by
        rw [pow_succ, ← Nat.mul_div_cancel' (hpi_dvd x hx)]
        exact mul_dvd_mul_left (p ^ in_) hpdvd
      have := (hp_prime.pow_dvd_iff_le_factorization hxpos.ne').mp hsucc
      omega
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp huY
      have hy' := Finset.mem_filter.mp hy
      have hypos := (hY y hy'.1).1
      have hsucc : p ^ (jn_ + 1) ∣ y := by
        rw [pow_succ, ← Nat.mul_div_cancel' (hpj_dvd y hy)]
        exact mul_dvd_mul_left (p ^ jn_) hpdvd
      have := (hp_prime.pow_dvd_iff_le_factorization hypos.ne').mp hsucc
      omega
  have hall_sub : allPrimes Xbar Ybar ⊆ (allPrimes X Y).erase p := by
    intro q hq
    have hqne : q ≠ p := fun heq => hp_not_all (heq ▸ hq)
    refine Finset.mem_erase.mpr ⟨hqne, ?_⟩
    obtain ⟨u, hu, hqu⟩ := Finset.mem_biUnion.mp hq
    have hq' := Nat.mem_primeFactors.mp hqu
    rcases Finset.mem_union.mp hu with huX | huY
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp huX
      have hxX := (Finset.mem_filter.mp hx).1
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left Y hxX,
        Nat.mem_primeFactors.mpr ⟨hq'.1, hq'.2.1.trans (Nat.div_dvd_of_dvd (hpi_dvd x hx)), (hX x hxX).1.ne'⟩⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp huY
      have hyY := (Finset.mem_filter.mp hy).1
      exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_union_right X hyY,
        Nat.mem_primeFactors.mpr ⟨hq'.1, hq'.2.1.trans (Nat.div_dvd_of_dvd (hpj_dvd y hy)), (hY y hyY).1.ne'⟩⟩
  have hEbar_ne : Ebar.Nonempty := hEij.image _
  have hXbar_ne : Xbar.Nonempty := by
    obtain ⟨e, he⟩ := hEij
    exact ⟨e.1 / p ^ in_, Finset.mem_image_of_mem _ (Finset.mem_filter.mp he).2.1⟩
  have hYbar_ne : Ybar.Nonempty := by
    obtain ⟨e, he⟩ := hEij
    exact ⟨e.2 / p ^ jn_, Finset.mem_image_of_mem _ (Finset.mem_filter.mp he).2.2⟩
  have hEbar_sub : Ebar ⊆ Xbar ×ˢ Ybar := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    have he0' := Finset.mem_filter.mp he0
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he0'.2.1, Finset.mem_image_of_mem _ he0'.2.2⟩
  have hXbar_bd : ∀ u ∈ Xbar, 0 < u ∧ A / (p : ℝ) ^ in_ ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * (A / (p : ℝ) ^ in_) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    have hxX := hX x (Finset.mem_filter.mp hx).1
    have hdvd := hpi_dvd x hx
    have hcast : ((x / p ^ in_ : ℕ) : ℝ) = (x : ℝ) / (p : ℝ) ^ in_ := by
      rw [Nat.cast_div hdvd (by positivity)]; push_cast; rfl
    refine ⟨Nat.div_pos (Nat.le_of_dvd hxX.1 hdvd) hpi_pos, ?_, ?_⟩
    · rw [hcast]; exact div_le_div_of_nonneg_right hxX.2.1 (by positivity)
    · rw [hcast, ← mul_div_assoc]; exact div_le_div_of_nonneg_right hxX.2.2 (by positivity)
  have hYbar_bd : ∀ v ∈ Ybar, 0 < v ∧ B / (p : ℝ) ^ jn_ ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * (B / (p : ℝ) ^ jn_) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hyY := hY y (Finset.mem_filter.mp hy).1
    have hdvd := hpj_dvd y hy
    have hcast : ((y / p ^ jn_ : ℕ) : ℝ) = (y : ℝ) / (p : ℝ) ^ jn_ := by
      rw [Nat.cast_div hdvd (by positivity)]; push_cast; rfl
    refine ⟨Nat.div_pos (Nat.le_of_dvd hyY.1 hdvd) hpj_pos, ?_, ?_⟩
    · rw [hcast]; exact div_le_div_of_nonneg_right hyY.2.1 (by positivity)
    · rw [hcast, ← mul_div_assoc]; exact div_le_div_of_nonneg_right hyY.2.2 (by positivity)
  have hEbar_gcd : ∀ e ∈ Ebar, D / (p : ℝ) ^ min in_ jn_ ≤ (Nat.gcd e.1 e.2 : ℝ) := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    have he0' := Finset.mem_filter.mp he0
    have hxpos := (hX e0.1 (Finset.mem_filter.mp he0'.2.1).1).1
    have hypos := (hY e0.2 (Finset.mem_filter.mp he0'.2.2).1).1
    have hgcd_eq : Nat.gcd (e0.1 / p ^ in_) (e0.2 / p ^ jn_) * p ^ min in_ jn_ = Nat.gcd e0.1 e0.2 := by
      have h1ne : (e0.1 / p ^ in_) ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hxpos (hpi_dvd _ he0'.2.1)) hpi_pos).ne'
      have h2ne : (e0.2 / p ^ jn_) ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hypos (hpj_dvd _ he0'.2.2)) hpj_pos).ne'
      have hlhs : Nat.gcd (e0.1 / p ^ in_) (e0.2 / p ^ jn_) * p ^ min in_ jn_ ≠ 0 :=
        (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h1ne)) (pow_pos hp_prime.pos _)).ne'
      have hrhs : Nat.gcd e0.1 e0.2 ≠ 0 := (Nat.gcd_pos_of_pos_left _ hxpos).ne'
      rw [← Nat.factorization_inj hlhs hrhs]
      ext q
      by_cases hq : q.Prime
      · rw [Nat.factorization_mul (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h1ne)).ne'
            (pow_pos hp_prime.pos _).ne',
            Nat.factorization_gcd h1ne h2ne, Nat.factorization_gcd hxpos.ne' hypos.ne',
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.inf_apply, Finsupp.inf_apply,
            Finsupp.smul_apply, smul_eq_mul,
            Nat.factorization_div (hpi_dvd _ he0'.2.1), Nat.factorization_div (hpj_dvd _ he0'.2.2),
            Finsupp.tsub_apply, Finsupp.tsub_apply, Nat.factorization_pow, Nat.factorization_pow,
            Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
        by_cases hqp : q = p
        · subst hqp
          have hfx := (Finset.mem_filter.mp he0'.2.1).2
          have hfy := (Finset.mem_filter.mp he0'.2.2).2
          rw [hq.factorization_self, hfx, hfy]; simp
        · rw [hp_prime.factorization, Finsupp.single_eq_of_ne hqp]; simp
      · rw [Nat.factorization_eq_zero_of_not_prime _ hq, Nat.factorization_eq_zero_of_not_prime _ hq]
    have hgcdR : (Nat.gcd (e0.1 / p ^ in_) (e0.2 / p ^ jn_) : ℝ) * (p : ℝ) ^ min in_ jn_ =
        (Nat.gcd e0.1 e0.2 : ℝ) := by exact_mod_cast hgcd_eq
    rw [div_le_iff₀ (pow_pos hp_pos _), hgcdR]
    exact hE e0 he0'.1
  have hratio : (D / (p : ℝ) ^ min in_ jn_) ^ 2 / ((A / (p : ℝ) ^ in_) * (B / (p : ℝ) ^ jn_)) =
      (D ^ 2 / (A * B)) * (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs := by
    have hexp : in_ + jn_ = 2 * min in_ jn_ + ((in_ : ℤ) - (jn_ : ℤ)).natAbs := by omega
    have hpow : (p : ℝ) ^ in_ * (p : ℝ) ^ jn_ =
        ((p : ℝ) ^ min in_ jn_) ^ 2 * (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs := by
      rw [← pow_add, ← pow_mul, mul_comm (min in_ jn_) 2, ← pow_add, hexp]
    have hDne := hD.ne'
    have hAne := hA.ne'
    have hBne := hB.ne'
    have hpne := hp_pos.ne'
    field_simp
    exact hpow
  exact ⟨hXbar_card, hYbar_card, hEbar_card, hXbar_ne, hYbar_ne, hEbar_ne, hEbar_sub,
    hp_not_all, hall_sub, hXbar_bd, hYbar_bd, hEbar_gcd, hratio⟩

private lemma gw_slice_algebra {ρ α β μ p_real Kbase Knew Kstep : ℝ} {d : ℕ}
    (hρ : 0 < ρ) (hα : 0 < α) (hβ : 0 < β) (hμ : 0 < μ) (hp : 0 < p_real)
    (hKbase : 0 < Kbase) (hKstep : 0 < Kstep)
    (hpow : Knew * Kstep ≤ Kbase)
    {M : ℝ} (hMbad : Kbase < ρ ^ (9 / 4 : ℝ) * M)
    (hih : (ρ * (μ / (α * β))) ^ (9 / 4 : ℝ) * (M * (α * β)) * p_real ^ d ≤ Knew) :
    μ ≤ Kstep ^ (-(4 / 9 : ℝ)) * (p_real ^ (-(4 / 9 : ℝ))) ^ d * (α * β) ^ (1 - 1 / (9 / 4 : ℝ)) := by
  have hlhs_eq : (ρ * (μ / (α * β))) ^ (9 / 4 : ℝ) * (M * (α * β)) * p_real ^ d =
      (ρ ^ (9 / 4 : ℝ) * M) * (μ ^ (9 / 4 : ℝ) * (α * β) ^ (-(5 / 4 : ℝ)) * p_real ^ d) := by
    rw [Real.mul_rpow hρ.le (by positivity), Real.div_rpow hμ.le (by positivity)]
    have hcomb : (α * β) / (α * β) ^ (9 / 4 : ℝ) = (α * β) ^ (-(5 / 4 : ℝ)) := by
      calc (α * β) / (α * β) ^ (9 / 4 : ℝ)
          = (α * β) ^ (1 : ℝ) / (α * β) ^ (9 / 4 : ℝ) := by rw [Real.rpow_one]
        _ = (α * β) ^ ((1 : ℝ) - 9 / 4) := (Real.rpow_sub (mul_pos hα hβ) _ _).symm
        _ = (α * β) ^ (-(5 / 4 : ℝ)) := by norm_num
    have hstep : (μ ^ (9 / 4 : ℝ) / (α * β) ^ (9 / 4 : ℝ)) * (α * β) =
        μ ^ (9 / 4 : ℝ) * (α * β) ^ (-(5 / 4 : ℝ)) := by rw [← hcomb]; ring
    calc ρ ^ (9 / 4 : ℝ) * (μ ^ (9 / 4 : ℝ) / (α * β) ^ (9 / 4 : ℝ)) * (M * (α * β)) * p_real ^ d
        = (ρ ^ (9 / 4 : ℝ) * M) * (((μ ^ (9 / 4 : ℝ) / (α * β) ^ (9 / 4 : ℝ)) * (α * β)) * p_real ^ d) := by ring
      _ = _ := by rw [hstep]
  rw [hlhs_eq] at hih
  have hprod_le1 : μ ^ (9 / 4 : ℝ) * (α * β) ^ (-(5 / 4 : ℝ)) * p_real ^ d * Kstep ≤ 1 := by
    have h1 : Kbase * (μ ^ (9 / 4 : ℝ) * (α * β) ^ (-(5 / 4 : ℝ)) * p_real ^ d) ≤ Knew :=
      (mul_le_mul_of_nonneg_right hMbad.le (by positivity)).trans hih
    have h2 : Kbase * (μ ^ (9 / 4 : ℝ) * (α * β) ^ (-(5 / 4 : ℝ)) * p_real ^ d * Kstep) ≤ Kbase * 1 := by
      calc _ = (Kbase * (μ ^ (9 / 4 : ℝ) * (α * β) ^ (-(5 / 4 : ℝ)) * p_real ^ d)) * Kstep := by ring
        _ ≤ Knew * Kstep := mul_le_mul_of_nonneg_right h1 hKstep.le
        _ ≤ Kbase := hpow
        _ = Kbase * 1 := by ring
    exact le_of_mul_le_mul_left h2 hKbase
  have hμpow : μ ^ (9 / 4 : ℝ) ≤ Kstep⁻¹ * (p_real ^ d)⁻¹ * (α * β) ^ (5 / 4 : ℝ) := by
    have hneg : (α * β) ^ (-(5 / 4 : ℝ)) = ((α * β) ^ (5 / 4 : ℝ))⁻¹ :=
      Real.rpow_neg (mul_pos hα hβ).le _
    rw [hneg] at hprod_le1
    have hαβ_pos : 0 < (α * β) ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos (mul_pos hα hβ) _
    have hfac_pos : 0 < p_real ^ d * Kstep := mul_pos (pow_pos hp d) hKstep
    have hmul : μ ^ (9 / 4 : ℝ) * (p_real ^ d * Kstep) ≤ (α * β) ^ (5 / 4 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hprod_le1 hαβ_pos.le
      have heq : μ ^ (9 / 4 : ℝ) * ((α * β) ^ (5 / 4 : ℝ))⁻¹ * p_real ^ d * Kstep * (α * β) ^ (5 / 4 : ℝ) =
          μ ^ (9 / 4 : ℝ) * (p_real ^ d * Kstep) := by field_simp
      linarith
    calc μ ^ (9 / 4 : ℝ)
        ≤ (α * β) ^ (5 / 4 : ℝ) / (p_real ^ d * Kstep) := (le_div_iff₀ hfac_pos).mpr hmul
      _ = Kstep⁻¹ * (p_real ^ d)⁻¹ * (α * β) ^ (5 / 4 : ℝ) := by rw [div_eq_mul_inv, mul_inv]; ring
  have h49 := Real.rpow_le_rpow (Real.rpow_nonneg hμ.le _) hμpow (by norm_num : (0 : ℝ) ≤ 4 / 9)
  rw [← Real.rpow_mul hμ.le, show (9 / 4 : ℝ) * (4 / 9) = 1 by norm_num, Real.rpow_one] at h49
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)] at h49
  have h1 : (Kstep⁻¹) ^ (4 / 9 : ℝ) = Kstep ^ (-(4 / 9 : ℝ)) := by
    rw [Real.inv_rpow hKstep.le, Real.rpow_neg hKstep.le]
  have h2 : ((p_real ^ d)⁻¹) ^ (4 / 9 : ℝ) = (p_real ^ (-(4 / 9 : ℝ))) ^ d := by
    rw [Real.inv_rpow (pow_nonneg hp.le d), ← Real.rpow_neg (pow_nonneg hp.le d),
        ← Real.rpow_natCast p_real, ← Real.rpow_mul hp.le, ← Real.rpow_natCast (p_real ^ _),
        ← Real.rpow_mul hp.le]
    congr 1; ring
  have h3 : ((α * β) ^ (5 / 4 : ℝ)) ^ (4 / 9 : ℝ) = (α * β) ^ (1 - 1 / (9 / 4 : ℝ)) := by
    rw [← Real.rpow_mul (mul_pos hα hβ).le]
    congr 1; norm_num
  rwa [h1, h2, h3] at h49

set_option maxHeartbeats 800000 in
/-- Green-Walker Theorem 1.1 / Hu-Jing Theorem 6.2 at q₀ = 9/4 (taking concentration as input). -/
theorem gw_gcd_9_4
    (hConc : ∀ {Q : ℝ}, 2 < Q → Q < 3 → ∃ C_Q > 0,
      ∀ (S : Finset ℤ) (α β : ℤ → ℝ) (μ : ℤ × ℤ → ℝ),
        (∀ i ∈ S, 0 ≤ α i) → (∀ j ∈ S, 0 ≤ β j) →
        (∑ i ∈ S, α i = 1) → (∑ j ∈ S, β j = 1) →
        (∀ p ∈ S ×ˢ S, 0 ≤ μ p) → (∑ p ∈ S ×ˢ S, μ p = 1) →
        ∀ {c lam : ℝ}, 0 < c → c ≤ 1 → 0 < lam → lam ≤ 4 / 5 →
        (∀ i ∈ S, ∀ j ∈ S, μ (i, j) ≤ c * lam ^ (i - j).natAbs * (α i * β j) ^ (1 - 1 / Q)) →
        (1 / 9 : ℝ) ≤ c ∧
        ∃ k ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun p => 2 ≤ (p.1 - k).natAbs + (p.2 - k).natAbs), μ p ≤
          C_Q * lam ^ (2 * Q - 2)) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧
      ∀ (A B D : ℝ), 0 < A → 0 < B → 0 < D →
      ∀ (X Y : Finset ℕ) (E : Finset (ℕ × ℕ)),
        X.Nonempty → Y.Nonempty → E.Nonempty → E ⊆ X ×ˢ Y →
        (∀ x ∈ X, 0 < x ∧ A ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A) →
        (∀ y ∈ Y, 0 < y ∧ B ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * B) →
        (∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ)) →
        let ρ : ℝ := (E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))
        ρ ^ (9 / 4 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤ K0 := by
  classical
  obtain ⟨C0, hC0_pos, hC0⟩ := hConc (Q := (9 / 4 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨p0, hp0_ge2, hp0_tail⟩ := exists_tail_threshold hC0_pos (α := (1 / 9 : ℝ)) (by norm_num)
  -- Core inductive claim with factor 2000 ^ (1 + #smlPrimes p0 X Y)
  have hcore : ∀ n : ℕ, ∀ (A B D : ℝ), 0 < A → 0 < B → 0 < D →
      ∀ (X Y : Finset ℕ) (E : Finset (ℕ × ℕ)),
        (allPrimes X Y).card = n →
        X.Nonempty → Y.Nonempty → E.Nonempty → E ⊆ X ×ˢ Y →
        (∀ x ∈ X, 0 < x ∧ A ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A) →
        (∀ y ∈ Y, 0 < y ∧ B ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * B) →
        (∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ)) →
        ((E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))) ^ (9 / 4 : ℝ) *
          (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤
          (2000 : ℝ) ^ (1 + (smlPrimes p0 X Y).card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B D hA hB hD X Y E hcard hXne hYne hEne hEsub hX hY hE
      set ρ : ℝ := (E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ)) with hρ_def
      have hXpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hXne.card_pos
      have hYpos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hYne.card_pos
      have hEpos : (0 : ℝ) < (E.card : ℝ) := by exact_mod_cast hEne.card_pos
      have hρpos : 0 < ρ := div_pos hEpos (mul_pos hXpos hYpos)
      have hρle1 : ρ ≤ 1 := by
        rw [hρ_def, div_le_one (mul_pos hXpos hYpos)]
        have : E.card ≤ X.card * Y.card := by
          simpa using Finset.card_le_card hEsub
        exact_mod_cast this
      by_contra hbad
      push Not at hbad
      -- Step 1: For every prime p ∈ allPrimes X Y, apply IH on slices to get concentration
      have hlocal : ∀ p ∈ allPrimes X Y,
          p0 < p ∧ ∃ kp : ℕ,
            (((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
              ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))).card : ℝ) ≤
              C0 * (p : ℝ) ^ (-(1 + 1 / 9 : ℝ)) * (E.card : ℝ)) := by
        intro p hp_all
        have hp_prime : p.Prime := by
          obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hp_all
          exact Nat.prime_of_mem_primeFactors hu
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        let maxE : ℕ := (X ∪ Y).sup (fun u => u.factorization p)
        let S : Finset ℤ := (Finset.range (maxE + 1)).image (fun i : ℕ => (i : ℤ))
        let Xi : ℤ → Finset ℕ := fun i => X.filter (fun x => (x.factorization p : ℤ) = i)
        let Yj : ℤ → Finset ℕ := fun j => Y.filter (fun y => (y.factorization p : ℤ) = j)
        let Eij : ℤ → ℤ → Finset (ℕ × ℕ) := fun i j => E.filter (fun e => e.1 ∈ Xi i ∧ e.2 ∈ Yj j)
        let α : ℤ → ℝ := fun i => ((Xi i).card : ℝ) / (X.card : ℝ)
        let β : ℤ → ℝ := fun j => ((Yj j).card : ℝ) / (Y.card : ℝ)
        let μ : ℤ × ℤ → ℝ := fun q => ((Eij q.1 q.2).card : ℝ) / (E.card : ℝ)
        have hα0 : ∀ i ∈ S, 0 ≤ α i := fun i _ => by positivity
        have hβ0 : ∀ j ∈ S, 0 ≤ β j := fun j _ => by positivity
        have hμ0 : ∀ q ∈ S ×ˢ S, 0 ≤ μ q := fun q _ => by positivity
        have hX_maps : ∀ x ∈ X, (x.factorization p : ℤ) ∈ S := fun x hx => by
          refine Finset.mem_image.mpr ⟨x.factorization p, Finset.mem_range.mpr ?_, rfl⟩
          have hle : x.factorization p ≤ maxE :=
            Finset.le_sup (f := fun u => u.factorization p) (Finset.mem_union_left Y hx)
          omega
        have hY_maps : ∀ y ∈ Y, (y.factorization p : ℤ) ∈ S := fun y hy => by
          refine Finset.mem_image.mpr ⟨y.factorization p, Finset.mem_range.mpr ?_, rfl⟩
          have hle : y.factorization p ≤ maxE :=
            Finset.le_sup (f := fun u => u.factorization p) (Finset.mem_union_right X hy)
          omega
        have hα1 : ∑ i ∈ S, α i = 1 := by
          simp only [α, ← Finset.sum_div]
          rw [div_eq_one_iff_eq hXpos.ne']
          have hN : ∑ i ∈ S, (Xi i).card = X.card :=
            (Finset.card_eq_sum_card_fiberwise
              (f := fun x : ℕ => (x.factorization p : ℤ)) (s := X) (t := S)
              (fun x hx => hX_maps x hx)).symm
          exact_mod_cast hN
        have hβ1 : ∑ j ∈ S, β j = 1 := by
          simp only [β, ← Finset.sum_div]
          rw [div_eq_one_iff_eq hYpos.ne']
          have hN : ∑ j ∈ S, (Yj j).card = Y.card :=
            (Finset.card_eq_sum_card_fiberwise
              (f := fun y : ℕ => (y.factorization p : ℤ)) (s := Y) (t := S)
              (fun y hy => hY_maps y hy)).symm
          exact_mod_cast hN
        have hμ1 : ∑ q ∈ S ×ˢ S, μ q = 1 := by
          simp only [μ, ← Finset.sum_div]
          rw [div_eq_one_iff_eq hEpos.ne']
          have hE_maps : ∀ e ∈ E, ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)) ∈ S ×ˢ S := fun e he =>
            Finset.mem_product.mpr ⟨hX_maps e.1 (Finset.mem_product.mp (hEsub he)).1,
              hY_maps e.2 (Finset.mem_product.mp (hEsub he)).2⟩
          have hN : ∑ q ∈ S ×ˢ S, (Eij q.1 q.2).card = E.card := by
            have h1 := (Finset.card_eq_sum_card_fiberwise
              (f := fun e : ℕ × ℕ => ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)))
              (s := E) (t := S ×ˢ S) (fun e he => hE_maps e he)).symm
            rw [← h1]
            refine Finset.sum_congr rfl fun q _ => ?_
            congr 1; ext e
            simp only [Eij, Xi, Yj, Finset.mem_filter, Prod.ext_iff]
            constructor
            · rintro ⟨he, ⟨_, h1'⟩, ⟨_, h2'⟩⟩; exact ⟨he, h1', h2'⟩
            · rintro ⟨he, h1', h2'⟩
              have hmem := Finset.mem_product.mp (hEsub he)
              exact ⟨he, ⟨hmem.1, h1'⟩, ⟨hmem.2, h2'⟩⟩
          exact_mod_cast hN
        set c_p : ℝ := if p ≤ p0 then (2000 : ℝ) ^ (-(4 / 9 : ℝ)) else 1 with hcp_def
        have hcp0 : 0 < c_p := by dsimp [c_p]; split_ifs <;> positivity
        have hcp1 : c_p ≤ 1 := by
          dsimp [c_p]; split_ifs
          · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
          · exact le_rfl
        set lam : ℝ := (p : ℝ) ^ (-(4 / 9 : ℝ)) with hlam_def
        have hlam0 : 0 < lam := Real.rpow_pos_of_pos hp_pos _
        have hlam1 : lam ≤ 4 / 5 := by
          have h1 : lam ≤ (2 : ℝ) ^ (-(4 / 9 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
          have h2 : (2 : ℝ) ^ (-(4 / 9 : ℝ)) ≤ 4 / 5 := by
            rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
            have hpow : ((5 / 4 : ℝ) ^ (9 : ℕ)) ≤ (2 : ℝ) ^ (4 : ℕ) := by norm_num
            have h9 : ((5 / 4 : ℝ) ^ (9 : ℝ)) ≤ ((2 : ℝ) ^ (4 / 9 : ℝ)) ^ (9 : ℝ) := by
              rw [← Real.rpow_mul (by norm_num), show (4 / 9 : ℝ) * 9 = 4 by norm_num]
              exact_mod_cast hpow
            have hroot := Real.rpow_le_rpow (by positivity) h9 (by norm_num : (0 : ℝ) ≤ 1 / 9)
            rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by positivity),
              show (9 : ℝ) * (1 / 9) = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hroot
            calc ((4 / 5 : ℝ))⁻¹ = 5 / 4 := by norm_num
              _ ≤ (2 : ℝ) ^ (4 / 9 : ℝ) := hroot
          exact h1.trans h2
        -- Key slice inequality μ(i, j) ≤ c_p * lam^|i-j| * (α_i β_j)^(5/9)
        have hμ_bd : ∀ i ∈ S, ∀ j ∈ S,
            μ (i, j) ≤ c_p * lam ^ (i - j).natAbs * (α i * β j) ^ (1 - 1 / (9 / 4 : ℝ)) := by
          intro i hiS j hjS
          by_cases hEij : (Eij i j).Nonempty
          · obtain ⟨in_, _, rfl⟩ := Finset.mem_image.mp hiS
            obtain ⟨jn_, _, rfl⟩ := Finset.mem_image.mp hjS
            have hXi_eq : Xi (in_ : ℤ) = X.filter (fun x => x.factorization p = in_) := by
              ext x; simp [Xi]
            have hYj_eq : Yj (jn_ : ℤ) = Y.filter (fun y => y.factorization p = jn_) := by
              ext y; simp [Yj]
            have hEij_eq : Eij (in_ : ℤ) (jn_ : ℤ) =
                E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
                  e.2 ∈ Y.filter (fun y => y.factorization p = jn_)) := by
              simp [Eij, hXi_eq, hYj_eq]
            have hEij' : (E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
                e.2 ∈ Y.filter (fun y => y.factorization p = jn_))).Nonempty := hEij_eq ▸ hEij
            obtain ⟨hXbar_card, hYbar_card, hEbar_card, hXbar_ne, hYbar_ne, hEbar_ne, hEbar_sub,
              _, hall_sub, hXbar_bd, hYbar_bd, hEbar_gcd, hratio⟩ :=
              padic_slice_props hp_prime hA hB hD hEsub hX hY hE in_ jn_ hEij'
            let Xbar := (X.filter (fun x => x.factorization p = in_)).image (· / p ^ in_)
            let Ybar := (Y.filter (fun y => y.factorization p = jn_)).image (· / p ^ jn_)
            let Ebar := (E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
              e.2 ∈ Y.filter (fun y => y.factorization p = jn_))).image (fun e => (e.1 / p ^ in_, e.2 / p ^ jn_))
            have hcard_lt : (allPrimes Xbar Ybar).card < n := by
              rw [← hcard]
              exact (Finset.card_le_card hall_sub).trans_lt (Finset.card_erase_lt_of_mem hp_all)
            have hsml_le : (smlPrimes p0 Xbar Ybar).card + (if p ≤ p0 then 1 else 0) ≤ (smlPrimes p0 X Y).card := by
              by_cases hple : p ≤ p0
              · rw [if_pos hple]
                have hsub : smlPrimes p0 Xbar Ybar ⊆ (smlPrimes p0 X Y).erase p := by
                  intro q hq
                  have hq' := Finset.mem_filter.mp hq
                  have hq2 := Finset.mem_erase.mp (hall_sub hq'.1)
                  exact Finset.mem_erase.mpr ⟨hq2.1, Finset.mem_filter.mpr ⟨hq2.2, hq'.2⟩⟩
                have hp_sml : p ∈ smlPrimes p0 X Y := Finset.mem_filter.mpr ⟨hp_all, hple⟩
                have hle := Finset.card_le_card hsub
                have hlt := Finset.card_erase_add_one hp_sml
                omega
              · rw [if_neg hple, add_zero]
                refine Finset.card_le_card fun q hq => ?_
                have hq' := Finset.mem_filter.mp hq
                exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hall_sub hq'.1)).2, hq'.2⟩
            have hih := ih (allPrimes Xbar Ybar).card hcard_lt
              (A / (p : ℝ) ^ in_) (B / (p : ℝ) ^ jn_) (D / (p : ℝ) ^ min in_ jn_)
              (div_pos hA (pow_pos hp_pos in_)) (div_pos hB (pow_pos hp_pos jn_))
              (div_pos hD (pow_pos hp_pos (min in_ jn_)))
              Xbar Ybar Ebar rfl hXbar_ne hYbar_ne hEbar_ne hEbar_sub hXbar_bd hYbar_bd hEbar_gcd
            have hXbar_card' : Xbar.card = (Xi (in_ : ℤ)).card := by rw [hXi_eq]; exact hXbar_card
            have hYbar_card' : Ybar.card = (Yj (jn_ : ℤ)).card := by rw [hYj_eq]; exact hYbar_card
            have hEbar_card' : Ebar.card = (Eij (in_ : ℤ) (jn_ : ℤ)).card := by rw [hEij_eq]; exact hEbar_card
            have hαpos : 0 < α in_ := div_pos (by exact_mod_cast hXbar_card' ▸ hXbar_ne.card_pos) hXpos
            have hβpos : 0 < β jn_ := div_pos (by exact_mod_cast hYbar_card' ▸ hYbar_ne.card_pos) hYpos
            have hμpos : 0 < μ (in_, jn_) := div_pos (by exact_mod_cast hEbar_card' ▸ hEbar_ne.card_pos) hEpos
            have hXicard_eq : ((Xi (in_ : ℤ)).card : ℝ) = (X.card : ℝ) * α in_ := by
              dsimp only [α]; exact (mul_div_cancel₀ _ hXpos.ne').symm
            have hYjcard_eq : ((Yj (jn_ : ℤ)).card : ℝ) = (Y.card : ℝ) * β jn_ := by
              dsimp only [β]; exact (mul_div_cancel₀ _ hYpos.ne').symm
            have hEijcard_eq : ((Eij (in_ : ℤ) (jn_ : ℤ)).card : ℝ) = (E.card : ℝ) * μ (in_, jn_) := by
              dsimp only [μ]; exact (mul_div_cancel₀ _ hEpos.ne').symm
            have hXY_eq : (Xbar.card : ℝ) * (Ybar.card : ℝ) = (X.card : ℝ) * (Y.card : ℝ) * (α in_ * β jn_) := by
              rw [hXbar_card', hYbar_card', hXicard_eq, hYjcard_eq]; ring
            have hρ'_eq : (Ebar.card : ℝ) / ((Xbar.card : ℝ) * (Ybar.card : ℝ)) =
                ρ * (μ (in_, jn_) / (α in_ * β jn_)) := by
              rw [hEbar_card', hEijcard_eq, hXY_eq, hρ_def]
              exact mul_div_mul_comm _ _ _ _
            have hih' : (ρ * (μ (in_, jn_) / (α in_ * β jn_))) ^ (9 / 4 : ℝ) *
                (((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) * (α in_ * β jn_)) *
                (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs ≤
                (2000 : ℝ) ^ (1 + (smlPrimes p0 Xbar Ybar).card) := by
              have hrew : ((Ebar.card : ℝ) / ((Xbar.card : ℝ) * (Ybar.card : ℝ))) ^ (9 / 4 : ℝ) *
                  (Xbar.card : ℝ) * (Ybar.card : ℝ) *
                  ((D / (p : ℝ) ^ min in_ jn_) ^ 2 / ((A / (p : ℝ) ^ in_) * (B / (p : ℝ) ^ jn_))) =
                  (ρ * (μ (in_, jn_) / (α in_ * β jn_))) ^ (9 / 4 : ℝ) *
                  (((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) * (α in_ * β jn_)) *
                  (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs := by
                rw [hρ'_eq, mul_assoc ((ρ * _) ^ _), hXY_eq, hratio]; ring
              rwa [hrew] at hih
            have hpow_cmp : (2000 : ℝ) ^ (1 + (smlPrimes p0 Xbar Ybar).card) *
                (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0) ≤ (2000 : ℝ) ^ (1 + (smlPrimes p0 X Y).card) := by
              rw [← pow_add]
              exact pow_le_pow_right₀ (by norm_num) (by omega)
            have hMbad : (2000 : ℝ) ^ (1 + (smlPrimes p0 X Y).card) <
                ρ ^ (9 / 4 : ℝ) * ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) := by
              linarith
            have halg := gw_slice_algebra hρpos hαpos hβpos hμpos hp_pos
              (by positivity : (0 : ℝ) < (2000 : ℝ) ^ (1 + (smlPrimes p0 X Y).card))
              (by positivity : (0 : ℝ) < (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0))
              hpow_cmp hMbad hih'
            have hcp_eq : ((2000 : ℝ) ^ (if p ≤ p0 then 1 else 0)) ^ (-(4 / 9 : ℝ)) = c_p := by
              dsimp only [c_p]; split_ifs <;> simp only [pow_one, pow_zero, Real.one_rpow]
            rw [hcp_eq, ← hlam_def] at halg
            exact halg
          · have hzero : μ (i, j) = 0 := by
              dsimp [μ]
              rw [Finset.not_nonempty_iff_eq_empty.mp hEij, Finset.card_empty, Nat.cast_zero, zero_div]
            rw [hzero]
            exact mul_nonneg (mul_nonneg hcp0.le (pow_nonneg hlam0.le _))
              (Real.rpow_nonneg (mul_nonneg (hα0 i hiS) (hβ0 j hjS)) _)
        -- Apply concentration lemma!
        obtain ⟨hcp_ge, k, hkS, hconc_bd⟩ := hC0 S α β μ hα0 hβ0 hα1 hβ1 hμ0 hμ1 hcp0 hcp1 hlam0 hlam1 hμ_bd
        -- First deduce p0 < p from 1/9 ≤ c_p!
        have hp_gt : p0 < p := by
          by_contra hle
          push Not at hle
          rw [hcp_def, if_pos hle] at hcp_ge
          have h2000 : (2000 : ℝ) ^ (-(4 / 9 : ℝ)) < 1 / 9 := by
            rw [Real.rpow_neg (by norm_num), one_div, inv_lt_inv₀ (by positivity) (by norm_num)]
            have hpow : (9 : ℝ) ^ (9 : ℕ) < (2000 : ℝ) ^ (4 : ℕ) := by norm_num
            have h9 : (9 : ℝ) ^ (9 : ℝ) < ((2000 : ℝ) ^ (4 / 9 : ℝ)) ^ (9 : ℝ) := by
              rw [← Real.rpow_mul (by norm_num), show (4 / 9 : ℝ) * 9 = 4 by norm_num]
              exact_mod_cast hpow
            have := Real.rpow_lt_rpow (by positivity) h9 (by norm_num : (0 : ℝ) < 1 / 9)
            rwa [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by positivity),
              show (9 : ℝ) * (1 / 9) = 1 by norm_num, Real.rpow_one, Real.rpow_one] at this
          linarith
        -- Extract kp : ℕ from k ∈ S
        obtain ⟨kp, _, rfl⟩ := Finset.mem_image.mp hkS
        refine ⟨hp_gt, kp, ?_⟩
        -- Match filtered edge set to tail sum of μ
        have hlam_exp : lam ^ (2 * (9 / 4 : ℝ) - 2) = (p : ℝ) ^ (-(1 + 1 / 9 : ℝ)) := by
          rw [hlam_def, ← Real.rpow_mul hp_pos.le]
          congr 1; norm_num
        rw [hlam_exp] at hconc_bd
        have hfilt_eq : (((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
            ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))).card : ℝ) / (E.card : ℝ)) =
            ∑ q ∈ (S ×ˢ S).filter (fun q => 2 ≤ (q.1 - (kp : ℤ)).natAbs + (q.2 - (kp : ℤ)).natAbs), μ q := by
          simp only [μ, ← Finset.sum_div]
          congr 1
          have hN : (E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
              ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))).card =
              ∑ q ∈ (S ×ˢ S).filter (fun q => 2 ≤ (q.1 - (kp : ℤ)).natAbs + (q.2 - (kp : ℤ)).natAbs),
                (Eij q.1 q.2).card := by
            let Ebad := E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
              ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))
            let Stail := (S ×ˢ S).filter (fun q => 2 ≤ (q.1 - (kp : ℤ)).natAbs + (q.2 - (kp : ℤ)).natAbs)
            have hmaps : ∀ e ∈ Ebad, ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)) ∈ Stail := by
              intro e he
              have he' := Finset.mem_filter.mp he
              have hmem := Finset.mem_product.mp (hEsub he'.1)
              exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hX_maps _ hmem.1, hY_maps _ hmem.2⟩,
                by omega⟩
            rw [Finset.card_eq_sum_card_fiberwise
              (f := fun e : ℕ × ℕ => ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)))
              (s := Ebad) (t := Stail) (fun e he => hmaps e he)]
            refine Finset.sum_congr rfl fun q hq => ?_
            have hq' := Finset.mem_filter.mp hq
            congr 1; ext e
            simp only [Ebad, Eij, Xi, Yj, Finset.mem_filter, Prod.ext_iff]
            constructor
            · rintro ⟨⟨he, _⟩, h1', h2'⟩
              have hmem := Finset.mem_product.mp (hEsub he)
              exact ⟨he, ⟨hmem.1, h1'⟩, ⟨hmem.2, h2'⟩⟩
            · rintro ⟨he, ⟨_, h1'⟩, ⟨_, h2'⟩⟩
              refine ⟨⟨he, ?_⟩, h1', h2'⟩
              rw [h1', h2']; omega
          exact_mod_cast hN
        rw [← hfilt_eq, div_le_iff₀ hEpos] at hconc_bd
        exact hconc_bd
      -- Step 2: Intersect over all primes p ∈ allPrimes X Y to get E' of size ≥ |E|/2 and N
      let kp_fn : ℕ → ℕ := fun p => if h : p ∈ allPrimes X Y then (hlocal p h).2.choose else 0
      let N : ℕ := ∏ p ∈ allPrimes X Y, p ^ kp_fn p
      have hNpos : 0 < N := Finset.prod_pos fun p hp => by
        obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hp
        exact pow_pos (Nat.prime_of_mem_primeFactors hu).pos _
      have hNfac : ∀ p, p.Prime → N.factorization p = if p ∈ allPrimes X Y then kp_fn p else 0 := by
        intro p hp
        unfold N
        have hne : ∀ q ∈ allPrimes X Y, q ^ kp_fn q ≠ 0 := fun q hq => by
          obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hq
          exact (pow_pos (Nat.prime_of_mem_primeFactors hu).pos _).ne'
        rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
        have hterm : ∀ q ∈ allPrimes X Y, (q ^ kp_fn q).factorization p = if q = p then kp_fn q else 0 := by
          intro q hq
          obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hq
          have hqp : q.Prime := Nat.prime_of_mem_primeFactors hu
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
          by_cases heq : q = p
          · subst heq; simp [hqp.factorization_self]
          · rw [hqp.factorization, Finsupp.single_eq_of_ne (Ne.symm heq)]; simp [heq]
        rw [Finset.sum_congr rfl hterm]
        by_cases hmem : p ∈ allPrimes X Y
        · rw [if_pos hmem, Finset.sum_eq_single p]
          · simp
          · intro q _ hqp; simp [hqp]
          · intro h; exact absurd hmem h
        · rw [if_neg hmem]
          refine Finset.sum_eq_zero fun q hq => ?_
          have hne' : q ≠ p := fun heq => hmem (heq ▸ hq)
          simp [hne']
      let E' := E.filter (fun e => ∀ p, p.Prime →
        ((e.1.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs +
        ((e.2.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1)
      have hE'_card : (E.card : ℝ) / 2 ≤ (E'.card : ℝ) := by
        have hbad_sub : E \ E' ⊆ (allPrimes X Y).biUnion (fun p =>
            E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs +
              ((e.2.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs ≤ 1))) := by
          intro e he
          rw [Finset.mem_sdiff] at he
          have hnot : ¬ ∀ p, p.Prime →
              ((e.1.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs +
              ((e.2.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1 := by
            intro h; exact he.2 (Finset.mem_filter.mpr ⟨he.1, h⟩)
          push Not at hnot
          obtain ⟨p, hp, hgt⟩ := hnot
          have hp_all : p ∈ allPrimes X Y := by
            by_contra hnotmem
            have hN0 : N.factorization p = 0 := by rw [hNfac p hp, if_neg hnotmem]
            have hmemXY := Finset.mem_product.mp (hEsub he.1)
            have he1_0 : e.1.factorization p = 0 := by
              by_contra hnz
              have hpf : p ∈ e.1.primeFactors := by
                rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact hnz
              exact hnotmem (Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_union_left Y hmemXY.1, hpf⟩)
            have he2_0 : e.2.factorization p = 0 := by
              by_contra hnz
              have hpf : p ∈ e.2.primeFactors := by
                rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact hnz
              exact hnotmem (Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_union_right X hmemXY.2, hpf⟩)
            rw [hN0, he1_0, he2_0] at hgt; simp at hgt
          refine Finset.mem_biUnion.mpr ⟨p, hp_all, Finset.mem_filter.mpr ⟨he.1, ?_⟩⟩
          rw [hNfac p hp, if_pos hp_all] at hgt
          omega
        have hbad_card : ((E \ E').card : ℝ) ≤ (E.card : ℝ) / 2 := by
          have hc1 := (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
          have hc1R : ((E \ E').card : ℝ) ≤ ∑ p ∈ allPrimes X Y,
              ((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs +
                ((e.2.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs ≤ 1))).card : ℝ) := by
            exact_mod_cast hc1
          refine hc1R.trans ?_
          have hsum_le : ∑ p ∈ allPrimes X Y,
              ((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs +
                ((e.2.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs ≤ 1))).card : ℝ) ≤
              (C0 * ∑ p ∈ allPrimes X Y, (p : ℝ) ^ (-(1 + 1 / 9 : ℝ))) * (E.card : ℝ) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_le_sum fun p hp => ?_
            have hspec := (hlocal p hp).2.choose_spec
            simpa only [kp_fn, dif_pos hp] using hspec
          have htail := hp0_tail (allPrimes X Y) (fun p hp => (hlocal p hp).1)
          exact hsum_le.trans (by nlinarith)
        have hadd : E'.card + (E \ E').card = E.card := by
          have hsub : E' ⊆ E := Finset.filter_subset _ E
          have h := Finset.card_sdiff_add_card_eq_card hsub
          omega
        have haddR : (E'.card : ℝ) + ((E \ E').card : ℝ) = (E.card : ℝ) := by exact_mod_cast hadd
        linarith
      -- Step 3: Defect counting (Green-Walker Prop 1.3) gives |X||Y| ≤ 1024 ρ^(-2) AB/D^2, contradiction!
      have hE'sub : E' ⊆ X ×ˢ Y := (Finset.filter_subset _ E).trans hEsub
      have hE'dens : (ρ / 2) * (X.card : ℝ) * (Y.card : ℝ) ≤ (E'.card : ℝ) := by
        have : (E.card : ℝ) = ρ * (X.card : ℝ) * (Y.card : ℝ) := by
          dsimp [ρ]; field_simp
        linarith
      let Xhigh := X.filter (fun u => (ρ / 4) * (Y.card : ℝ) ≤ ((E'.filter (fun e => e.1 = u)).card : ℝ))
      have hXhigh_card : (ρ / 4) * (X.card : ℝ) ≤ (Xhigh.card : ℝ) :=
        exists_high_degree_subset hYne hE'sub hρpos hE'dens
      have hXhigh_spec : ∀ u ∈ Xhigh, 0 < u ∧ A ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * A ∧
          ∀ p, p.Prime → ((u.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1 := by
        intro u hu
        have hu' := Finset.mem_filter.mp hu
        have huX := hX u hu'.1
        refine ⟨huX.1, huX.2.1, huX.2.2, ?_⟩
        have hne : (E'.filter (fun e => e.1 = u)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          have : (0 : ℝ) < (ρ / 4) * (Y.card : ℝ) := by positivity
          rw [hemp, Finset.card_empty, Nat.cast_zero] at hu'
          linarith
        obtain ⟨e, he⟩ := hne
        have he' := Finset.mem_filter.mp he
        have heE' := (Finset.mem_filter.mp he'.1).2
        intro p hp
        have := heE' p hp
        rw [he'.2] at this
        omega
      -- Some u ∈ Xhigh has defect N u > ρ * |X| / 16
      have hu_ex : ∃ u ∈ Xhigh, (ρ / 16) * (X.card : ℝ) < (defect N u : ℝ) := by
        by_contra hall
        push Not at hall
        have hfilt : Xhigh.filter (fun u => (defect N u : ℝ) ≤ (ρ / 16) * (X.card : ℝ)) = Xhigh :=
          Finset.filter_eq_self.mpr hall
        have hbd := count_defect_le hNpos hA (by positivity : (0 : ℝ) ≤ (ρ / 16) * (X.card : ℝ)) Xhigh hXhigh_spec
        rw [hfilt] at hbd
        have hpos : 0 < ρ * (X.card : ℝ) := mul_pos hρpos hXpos
        linarith
      obtain ⟨u, huHigh, hu_def⟩ := hu_ex
      let Yu := (E'.filter (fun e => e.1 = u)).image Prod.snd
      have hYu_card : (ρ / 4) * (Y.card : ℝ) ≤ (Yu.card : ℝ) := by
        have hinj : Set.InjOn Prod.snd (E'.filter (fun e => e.1 = u) : Set (ℕ × ℕ)) := by
          intro e1 he1 e2 he2 h
          ext <;> [exact (Finset.mem_filter.mp he1).2.trans (Finset.mem_filter.mp he2).2.symm; exact h]
        rw [Finset.card_image_of_injOn hinj]
        exact (Finset.mem_filter.mp huHigh).2
      have hYu_spec : ∀ v ∈ Yu, 0 < v ∧ B ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * B ∧
          ∀ p, p.Prime → ((v.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1 := by
        intro v hv
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
        have he' := Finset.mem_filter.mp he
        have hvY := hY e.2 (Finset.mem_product.mp (hE'sub he'.1)).2
        have heE' := (Finset.mem_filter.mp he'.1).2
        refine ⟨hvY.1, hvY.2.1, hvY.2.2, fun p hp => ?_⟩
        have := heE' p hp
        omega
      have hv_ex : ∃ v ∈ Yu, (ρ / 16) * (Y.card : ℝ) < (defect N v : ℝ) := by
        by_contra hall
        push Not at hall
        have hfilt : Yu.filter (fun v => (defect N v : ℝ) ≤ (ρ / 16) * (Y.card : ℝ)) = Yu :=
          Finset.filter_eq_self.mpr hall
        have hbd := count_defect_le hNpos hB (by positivity : (0 : ℝ) ≤ (ρ / 16) * (Y.card : ℝ)) Yu hYu_spec
        rw [hfilt] at hbd
        have hpos : 0 < ρ * (Y.card : ℝ) := mul_pos hρpos hYpos
        linarith
      obtain ⟨v, hvYu, hv_def⟩ := hv_ex
      obtain ⟨e, he, hv_eq⟩ := Finset.mem_image.mp hvYu
      have he' := Finset.mem_filter.mp he
      have huv_E' : (u, v) ∈ E' := by
        have : (u, v) = e := by ext <;> [exact he'.2.symm; exact hv_eq.symm]
        rw [this]; exact he'.1
      have huv_E : (u, v) ∈ E := (Finset.mem_filter.mp huv_E').1
      have huv_val := (Finset.mem_filter.mp huv_E').2
      have huX := hX u (Finset.mem_filter.mp huHigh).1
      have hvY := hY v (Finset.mem_product.mp (hEsub huv_E)).2
      have hprod_eq := defect_mul_defect_mul_gcd_sq hNpos huX.1 hvY.1 huv_val
      have hprodR : (defect N u : ℝ) * (defect N v : ℝ) * (Nat.gcd u v : ℝ) ^ 2 = (u : ℝ) * (v : ℝ) := by
        exact_mod_cast hprod_eq
      have hgcd_ge : D ≤ (Nat.gcd u v : ℝ) := hE (u, v) huv_E
      have hdef_ub : (defect N u : ℝ) * (defect N v : ℝ) * D ^ 2 ≤ 4 * A * B := by
        calc (defect N u : ℝ) * (defect N v : ℝ) * D ^ 2
            ≤ (defect N u : ℝ) * (defect N v : ℝ) * (Nat.gcd u v : ℝ) ^ 2 := by
              gcongr
          _ = (u : ℝ) * (v : ℝ) := hprodR
          _ ≤ (2 * A) * (2 * B) := mul_le_mul huX.2.2 hvY.2.2 (Nat.cast_nonneg v) (by positivity)
          _ = 4 * A * B := by ring
      have hdef_lb : ((ρ / 16) * (X.card : ℝ)) * ((ρ / 16) * (Y.card : ℝ)) * D ^ 2 <
          (defect N u : ℝ) * (defect N v : ℝ) * D ^ 2 := by
        have h1 : ((ρ / 16) * (X.card : ℝ)) * ((ρ / 16) * (Y.card : ℝ)) <
            (defect N u : ℝ) * (defect N v : ℝ) :=
          mul_lt_mul hu_def hv_def.le (by positivity) (Nat.cast_nonneg _)
        exact mul_lt_mul_of_pos_right h1 (pow_pos hD 2)
      have h1024 : ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤ 1024 := by
        have h1 : ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * D ^ 2 ≤ 1024 * (A * B) := by linarith
        rw [mul_div_assoc', div_le_iff₀ (mul_pos hA hB)]
        linarith
      have hρpow : ρ ^ (9 / 4 : ℝ) ≤ ρ ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hρpos hρle1 (by norm_num)
      rw [Real.rpow_two] at hρpow
      have hlhs_le : ρ ^ (9 / 4 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤ 1024 := by
        calc ρ ^ (9 / 4 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))
            ≤ ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) := by gcongr
          _ ≤ 1024 := h1024
      have h2000_ge : (2000 : ℝ) ≤ (2000 : ℝ) ^ (1 + (smlPrimes p0 X Y).card) := by
        calc (2000 : ℝ) = (2000 : ℝ) ^ (1 : ℕ) := by ring
          _ ≤ (2000 : ℝ) ^ (1 + (smlPrimes p0 X Y).card) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  -- Conclude with K0 = 2000 ^ (1 + (p0 + 1))
  refine ⟨(2000 : ℝ) ^ (1 + (p0 + 1)), by
    calc (1 : ℝ) ≤ (2000 : ℝ) ^ (0 : ℕ) := by norm_num
      _ ≤ (2000 : ℝ) ^ (1 + (p0 + 1)) := pow_le_pow_right₀ (by norm_num) (by omega), ?_⟩
  intro A B D hA hB hD X Y E hXne hYne hEne hEsub hX hY hE
  have h1 := hcore (allPrimes X Y).card A B D hA hB hD X Y E rfl hXne hYne hEne hEsub hX hY hE
  have hsml_card : (smlPrimes p0 X Y).card ≤ p0 + 1 := by
    have hsub : smlPrimes p0 X Y ⊆ Finset.range (p0 + 1) := by
      intro q hq
      rw [Finset.mem_range]
      have := (Finset.mem_filter.mp hq).2
      omega
    exact (Finset.card_le_card hsub).trans (by simp)
  exact h1.trans (pow_le_pow_right₀ (by norm_num) (by omega))

end GreenWalkerGCD

end LRMod1GCD

namespace LRMod1Extract

open Finset BigOperators
open LRMod1 LRMod1Box LRMod1GCD

section MPExtraction

private lemma mp_slice_algebra {ρ z α β μ p_real Kstep : ℝ} {d : ℕ}
    (hρ : 0 < ρ) (hz : 0 < z) (hα : 0 < α) (hβ : 0 < β) (hμ : 0 < μ)
    (hp : 0 < p_real) (hKstep : 0 < Kstep)
    (hmax : (ρ * (μ / (α * β))) ^ (5 / 2 : ℝ) * (α * β) * p_real ^ d *
        (z * (α * β)) ^ (1 / 20 : ℝ) * Kstep ≤
      ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) :
    μ ≤ Kstep ^ (-(2 / 5 : ℝ)) * (p_real ^ (-(2 / 5 : ℝ))) ^ d *
      (α * β) ^ (1 - 1 / (50 / 21 : ℝ)) := by
  have hαβ : 0 < α * β := mul_pos hα hβ
  have hlhs : (ρ * (μ / (α * β))) ^ (5 / 2 : ℝ) * (α * β) * p_real ^ d *
      (z * (α * β)) ^ (1 / 20 : ℝ) * Kstep =
      (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) *
      (μ ^ (5 / 2 : ℝ) * (α * β) ^ (-(29 / 20 : ℝ)) * p_real ^ d * Kstep) := by
    rw [Real.mul_rpow hρ.le (by positivity), Real.div_rpow hμ.le hαβ.le,
        Real.mul_rpow hz.le hαβ.le]
    have hcomb : (α * β) * (α * β) ^ (1 / 20 : ℝ) / (α * β) ^ (5 / 2 : ℝ) =
        (α * β) ^ (-(29 / 20 : ℝ)) := by
      calc (α * β) * (α * β) ^ (1 / 20 : ℝ) / (α * β) ^ (5 / 2 : ℝ)
          = (α * β) ^ (1 : ℝ) * (α * β) ^ (1 / 20 : ℝ) / (α * β) ^ (5 / 2 : ℝ) := by
            rw [Real.rpow_one]
        _ = (α * β) ^ ((1 : ℝ) + 1 / 20) / (α * β) ^ (5 / 2 : ℝ) := by
            rw [← Real.rpow_add hαβ]
        _ = (α * β) ^ ((1 : ℝ) + 1 / 20 - 5 / 2) := (Real.rpow_sub hαβ _ _).symm
        _ = (α * β) ^ (-(29 / 20 : ℝ)) := by norm_num
    have hstep : (μ ^ (5 / 2 : ℝ) / (α * β) ^ (5 / 2 : ℝ)) * (α * β) * (α * β) ^ (1 / 20 : ℝ) =
        μ ^ (5 / 2 : ℝ) * (α * β) ^ (-(29 / 20 : ℝ)) := by
      rw [← hcomb]; ring
    calc ρ ^ (5 / 2 : ℝ) * (μ ^ (5 / 2 : ℝ) / (α * β) ^ (5 / 2 : ℝ)) * (α * β) * p_real ^ d *
          (z ^ (1 / 20 : ℝ) * (α * β) ^ (1 / 20 : ℝ)) * Kstep
        = (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) *
          (((μ ^ (5 / 2 : ℝ) / (α * β) ^ (5 / 2 : ℝ)) * (α * β) * (α * β) ^ (1 / 20 : ℝ)) *
            p_real ^ d * Kstep) := by ring
      _ = _ := by rw [hstep]
  rw [hlhs] at hmax
  have hbase_pos : 0 < ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ) := by positivity
  have hprod_le1 : μ ^ (5 / 2 : ℝ) * (α * β) ^ (-(29 / 20 : ℝ)) * p_real ^ d * Kstep ≤ 1 := by
    have h2 : (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) *
        (μ ^ (5 / 2 : ℝ) * (α * β) ^ (-(29 / 20 : ℝ)) * p_real ^ d * Kstep) ≤
        (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) * 1 := by linarith
    exact le_of_mul_le_mul_left h2 hbase_pos
  have hμpow : μ ^ (5 / 2 : ℝ) ≤ Kstep⁻¹ * (p_real ^ d)⁻¹ * (α * β) ^ (29 / 20 : ℝ) := by
    have hneg : (α * β) ^ (-(29 / 20 : ℝ)) = ((α * β) ^ (29 / 20 : ℝ))⁻¹ :=
      Real.rpow_neg hαβ.le _
    rw [hneg] at hprod_le1
    have hαβ_pos : 0 < (α * β) ^ (29 / 20 : ℝ) := Real.rpow_pos_of_pos hαβ _
    have hfac_pos : 0 < p_real ^ d * Kstep := mul_pos (pow_pos hp d) hKstep
    have hmul : μ ^ (5 / 2 : ℝ) * (p_real ^ d * Kstep) ≤ (α * β) ^ (29 / 20 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hprod_le1 hαβ_pos.le
      have heq : μ ^ (5 / 2 : ℝ) * ((α * β) ^ (29 / 20 : ℝ))⁻¹ * p_real ^ d * Kstep *
          (α * β) ^ (29 / 20 : ℝ) = μ ^ (5 / 2 : ℝ) * (p_real ^ d * Kstep) := by field_simp
      linarith
    calc μ ^ (5 / 2 : ℝ)
        ≤ (α * β) ^ (29 / 20 : ℝ) / (p_real ^ d * Kstep) := (le_div_iff₀ hfac_pos).mpr hmul
      _ = Kstep⁻¹ * (p_real ^ d)⁻¹ * (α * β) ^ (29 / 20 : ℝ) := by rw [div_eq_mul_inv, mul_inv]; ring
  have h25 := Real.rpow_le_rpow (Real.rpow_nonneg hμ.le _) hμpow (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_mul hμ.le, show (5 / 2 : ℝ) * (2 / 5) = 1 by norm_num, Real.rpow_one] at h25
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)] at h25
  have h1 : (Kstep⁻¹) ^ (2 / 5 : ℝ) = Kstep ^ (-(2 / 5 : ℝ)) := by
    rw [Real.inv_rpow hKstep.le, Real.rpow_neg hKstep.le]
  have h2 : ((p_real ^ d)⁻¹) ^ (2 / 5 : ℝ) = (p_real ^ (-(2 / 5 : ℝ))) ^ d := by
    rw [Real.inv_rpow (pow_nonneg hp.le d), ← Real.rpow_neg (pow_nonneg hp.le d),
        ← Real.rpow_natCast p_real, ← Real.rpow_mul hp.le, ← Real.rpow_natCast (p_real ^ _),
        ← Real.rpow_mul hp.le]
    congr 1; ring
  have h3 : ((α * β) ^ (29 / 20 : ℝ)) ^ (2 / 5 : ℝ) = (α * β) ^ (1 - 1 / (50 / 21 : ℝ)) := by
    rw [← Real.rpow_mul hαβ.le]
    congr 1; norm_num
  rwa [h1, h2, h3] at h25

private lemma gcd_div_mul_gcd_eq {x y dX dY : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hdX : dX ∣ x) (hdY : dY ∣ y)
    (hdisj : ∀ p : ℕ, p.Prime → p ∣ dX * dY → ¬ p ∣ x / dX ∧ ¬ p ∣ y / dY) :
    Nat.gcd (x / dX) (y / dY) * Nat.gcd dX dY = Nat.gcd x y := by
  have hdX_pos : 0 < dX := Nat.pos_of_dvd_of_pos hdX hx
  have hdY_pos : 0 < dY := Nat.pos_of_dvd_of_pos hdY hy
  have hxd_pos : 0 < x / dX := Nat.div_pos (Nat.le_of_dvd hx hdX) hdX_pos
  have hyd_pos : 0 < y / dY := Nat.div_pos (Nat.le_of_dvd hy hdY) hdY_pos
  have hlhs_ne : Nat.gcd (x / dX) (y / dY) * Nat.gcd dX dY ≠ 0 :=
    (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hxd_pos) (Nat.gcd_pos_of_pos_left _ hdX_pos)).ne'
  have hrhs_ne : Nat.gcd x y ≠ 0 := (Nat.gcd_pos_of_pos_left _ hx).ne'
  rw [← Nat.factorization_inj hlhs_ne hrhs_ne]
  ext p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (Nat.gcd_pos_of_pos_left _ hxd_pos).ne'
          (Nat.gcd_pos_of_pos_left _ hdX_pos).ne',
        Nat.factorization_gcd hxd_pos.ne' hyd_pos.ne',
        Nat.factorization_gcd hdX_pos.ne' hdY_pos.ne',
        Nat.factorization_gcd hx.ne' hy.ne',
        Finsupp.add_apply, Finsupp.inf_apply, Finsupp.inf_apply, Finsupp.inf_apply,
        Nat.factorization_div hdX, Nat.factorization_div hdY,
        Finsupp.tsub_apply, Finsupp.tsub_apply]
    by_cases hpdvd : p ∣ dX * dY
    · have ⟨h1, h2⟩ := hdisj p hp hpdvd
      have hx0 : (x / dX).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd h1
      have hy0 : (y / dY).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd h2
      rw [Nat.factorization_div hdX, Finsupp.tsub_apply] at hx0
      rw [Nat.factorization_div hdY, Finsupp.tsub_apply] at hy0
      have hleX : dX.factorization p ≤ x.factorization p :=
        (Nat.factorization_le_iff_dvd hdX_pos.ne' hx.ne').mpr hdX p
      have hleY : dY.factorization p ≤ y.factorization p :=
        (Nat.factorization_le_iff_dvd hdY_pos.ne' hy.ne').mpr hdY p
      omega
    · have hndX : ¬ p ∣ dX := fun h => hpdvd (dvd_mul_of_dvd_left h dY)
      have hndY : ¬ p ∣ dY := fun h => hpdvd (dvd_mul_of_dvd_right h dX)
      rw [Nat.factorization_eq_zero_of_not_dvd hndX, Nat.factorization_eq_zero_of_not_dvd hndY]
      simp
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma gcd_mul_pow_eq {dX dY p i j : ℕ}
    (hdX : 0 < dX) (hdY : 0 < dY) (hp : p.Prime) (hndX : ¬ p ∣ dX) (hndY : ¬ p ∣ dY) :
    Nat.gcd (dX * p ^ i) (dY * p ^ j) = Nat.gcd dX dY * p ^ min i j := by
  have hlhs_ne : Nat.gcd (dX * p ^ i) (dY * p ^ j) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hdX (pow_pos hp.pos i))).ne'
  have hrhs_ne : Nat.gcd dX dY * p ^ min i j ≠ 0 :=
    (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hdX) (pow_pos hp.pos _)).ne'
  rw [← Nat.factorization_inj hlhs_ne hrhs_ne]
  ext q
  by_cases hq : q.Prime
  · rw [Nat.factorization_gcd (Nat.mul_pos hdX (pow_pos hp.pos i)).ne'
          (Nat.mul_pos hdY (pow_pos hp.pos j)).ne',
        Nat.factorization_mul (Nat.gcd_pos_of_pos_left _ hdX).ne' (pow_pos hp.pos _).ne',
        Nat.factorization_gcd hdX.ne' hdY.ne',
        Nat.factorization_mul hdX.ne' (pow_pos hp.pos i).ne',
        Nat.factorization_mul hdY.ne' (pow_pos hp.pos j).ne',
        Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
        Finsupp.add_apply, Finsupp.inf_apply, Finsupp.inf_apply,
        Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
        smul_eq_mul, smul_eq_mul, smul_eq_mul]
    by_cases hqp : q = p
    · subst hqp
      rw [Nat.factorization_eq_zero_of_not_dvd hndX, Nat.factorization_eq_zero_of_not_dvd hndY,
          hq.factorization_self]
      simp
    · rw [hp.factorization, Finsupp.single_eq_of_ne hqp]; simp
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq, Nat.factorization_eq_zero_of_not_prime _ hq]

set_option maxHeartbeats 600000 in
private lemma mp_extract_box_of_local
    {A B D F0 K0 CQ : ℝ} (hApos : 0 < A) (hBpos : 0 < B) (hDpos : 0 < D)
    (hF0pos : 0 < F0) (hK0pos : 0 < K0) (hCQ_pos : 0 < CQ)
    {p0 : ℕ}
    (hp0_tail : ∀ F : Finset ℕ, (∀ n ∈ F, p0 < n) → CQ * ∑ n ∈ F, (n : ℝ) ^ (-(1 + 11 / 105 : ℝ)) ≤ 1 / 2)
    {X Y Y0 Ys : Finset ℕ} {E : Finset (ℕ × ℕ)} {dY : ℕ}
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hEne : E.Nonempty) (hEsub : E ⊆ X ×ˢ Y)
    (hXbd : ∀ u ∈ X, 0 < u ∧ A ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * A)
    (hYbd : ∀ v ∈ Y, 0 < v ∧ B ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * B)
    (hEbd : ∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ))
    (hdY_pos : 0 < dY) (hYs_sub : Ys ⊆ Y0) (hdY_dvd : ∀ y ∈ Ys, dY ∣ y)
    (hY_eq_img : Y = Ys.image (· / dY))
    {ρ z : ℝ} (hρ_def : ρ = (E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ)))
    (hρpos : 0 < ρ) (hz_Y : z * (Y0.card : ℝ) ≤ (Y.card : ℝ))
    (hρ_lb : (F0 / K0) ^ (4 : ℕ) ≤ ρ) (hz_lb : (F0 / K0) ^ (20 : ℕ) ≤ z)
    (hF0_le_Q : F0 ≤ ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)))
    (hlocal : ∀ p ∈ allPrimes X Y,
      p0 < p ∧ ∃ kp : ℕ,
        (((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
          ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))).card : ℝ) ≤
          CQ * (p : ℝ) ^ (-(1 + 11 / 105 : ℝ)) * (E.card : ℝ))) :
    ∃ (U : Finset ℕ) (ξ : ℚ) (AU BU : ℕ),
      U ⊆ Y0 ∧
      (1 / 4 : ℝ) * (F0 / K0) ^ (24 : ℕ) * (Y0.card : ℝ) ≤ (U.card : ℝ) ∧
      0 < ξ ∧ 0 < AU ∧ 0 < BU ∧
      ((AU : ℝ) * (BU : ℝ) ≤ (512 / F0) * (U.card : ℝ)) ∧
      ∀ u ∈ U, ∃ a b : ℕ, 1 ≤ a ∧ a ≤ AU ∧ 1 ≤ b ∧ b ≤ BU ∧
        (u : ℚ) = ξ * (a : ℚ) / (b : ℚ) := by
  classical
  have hXpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hXne.card_pos
  have hYpos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hYne.card_pos
  have hEpos : (0 : ℝ) < (E.card : ℝ) := by exact_mod_cast hEne.card_pos
  let kp_fn : ℕ → ℕ := fun p => if h : p ∈ allPrimes X Y then (hlocal p h).2.choose else 0
  let N : ℕ := ∏ p ∈ allPrimes X Y, p ^ kp_fn p
  have hNpos : 0 < N := Finset.prod_pos fun p hp => by
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hu).pos _
  have hNfac : ∀ p, p.Prime → N.factorization p = if p ∈ allPrimes X Y then kp_fn p else 0 := by
    intro p hp
    unfold N
    have hne : ∀ q ∈ allPrimes X Y, q ^ kp_fn q ≠ 0 := fun q hq => by
      obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hq
      exact (pow_pos (Nat.prime_of_mem_primeFactors hu).pos _).ne'
    rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
    have hterm : ∀ q ∈ allPrimes X Y, (q ^ kp_fn q).factorization p = if q = p then kp_fn q else 0 := by
      intro q hq
      obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hu
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      by_cases heq : q = p
      · subst heq; simp [hqp.factorization_self]
      · rw [hqp.factorization, Finsupp.single_eq_of_ne (Ne.symm heq)]; simp [heq]
    rw [Finset.sum_congr rfl hterm]
    by_cases hmem : p ∈ allPrimes X Y
    · rw [if_pos hmem, Finset.sum_eq_single p]
      · simp
      · intro q _ hqp; simp [hqp]
      · intro h; exact absurd hmem h
    · rw [if_neg hmem]
      refine Finset.sum_eq_zero fun q hq => ?_
      have hne' : q ≠ p := fun heq => hmem (heq ▸ hq)
      simp [hne']
  let E' := E.filter (fun e => ∀ p, p.Prime →
    ((e.1.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs +
    ((e.2.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1)
  have hE'_card : (E.card : ℝ) / 2 ≤ (E'.card : ℝ) := by
    have hbad_sub : E \ E' ⊆ (allPrimes X Y).biUnion (fun p =>
        E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs +
          ((e.2.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs ≤ 1))) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      have hnot : ¬ ∀ p, p.Prime →
          ((e.1.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs +
          ((e.2.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1 := fun h =>
        he.2 (Finset.mem_filter.mpr ⟨he.1, h⟩)
      push Not at hnot
      obtain ⟨p, hp, hgt⟩ := hnot
      have hp_all : p ∈ allPrimes X Y := by
        by_contra hnotmem
        have hN0 : N.factorization p = 0 := by rw [hNfac p hp, if_neg hnotmem]
        have hmemXY := Finset.mem_product.mp (hEsub he.1)
        have he1_0 : e.1.factorization p = 0 := by
          by_contra hnz
          have hpf : p ∈ e.1.primeFactors := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact hnz
          exact hnotmem (Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_union_left Y hmemXY.1, hpf⟩)
        have he2_0 : e.2.factorization p = 0 := by
          by_contra hnz
          have hpf : p ∈ e.2.primeFactors := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact hnz
          exact hnotmem (Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_union_right X hmemXY.2, hpf⟩)
        rw [hN0, he1_0, he2_0] at hgt; simp at hgt
      refine Finset.mem_biUnion.mpr ⟨p, hp_all, Finset.mem_filter.mpr ⟨he.1, ?_⟩⟩
      rw [hNfac p hp, if_pos hp_all] at hgt
      omega
    have hbad_card : ((E \ E').card : ℝ) ≤ (E.card : ℝ) / 2 := by
      have hc1 := (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
      have hc1R : ((E \ E').card : ℝ) ≤ ∑ p ∈ allPrimes X Y,
          ((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs +
            ((e.2.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs ≤ 1))).card : ℝ) := by
        exact_mod_cast hc1
      refine hc1R.trans ?_
      have hsum_le : ∑ p ∈ allPrimes X Y,
          ((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs +
            ((e.2.factorization p : ℤ) - (kp_fn p : ℤ)).natAbs ≤ 1))).card : ℝ) ≤
          (CQ * ∑ p ∈ allPrimes X Y, (p : ℝ) ^ (-(1 + 11 / 105 : ℝ))) * (E.card : ℝ) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun p hp => ?_
        have hspec := (hlocal p hp).2.choose_spec
        simpa only [kp_fn, dif_pos hp] using hspec
      have htail := hp0_tail (allPrimes X Y) (fun p hp => (hlocal p hp).1)
      have hCQ_nn : 0 ≤ CQ := hCQ_pos.le
      exact hsum_le.trans (by nlinarith)
    have hadd : E'.card + (E \ E').card = E.card := by
      have hsub : E' ⊆ E := Finset.filter_subset _ E
      have h := Finset.card_sdiff_add_card_eq_card hsub; omega
    have haddR : (E'.card : ℝ) + ((E \ E').card : ℝ) = (E.card : ℝ) := by exact_mod_cast hadd
    linarith
  have hE'sub : E' ⊆ X ×ˢ Y := (Finset.filter_subset _ E).trans hEsub
  have hE'dens : (ρ / 2) * (X.card : ℝ) * (Y.card : ℝ) ≤ (E'.card : ℝ) := by
    have hEeq : (E.card : ℝ) = ρ * (X.card : ℝ) * (Y.card : ℝ) := by
      rw [hρ_def, mul_assoc, div_mul_cancel₀ _ (mul_pos hXpos hYpos).ne']
    linarith
  let Xhigh := X.filter (fun u => (ρ / 4) * (Y.card : ℝ) ≤ ((E'.filter (fun e => e.1 = u)).card : ℝ))
  have hXhigh_card : (ρ / 4) * (X.card : ℝ) ≤ (Xhigh.card : ℝ) :=
    exists_high_degree_subset hYne hE'sub hρpos hE'dens
  have hXhigh_spec : ∀ u ∈ Xhigh, 0 < u ∧ A ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * A ∧
      ∀ p, p.Prime → ((u.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1 := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have huX := hXbd u hu'.1
    refine ⟨huX.1, huX.2.1, huX.2.2, ?_⟩
    have hne : (E'.filter (fun e => e.1 = u)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have : (0 : ℝ) < (ρ / 4) * (Y.card : ℝ) := by positivity
      rw [hemp, Finset.card_empty, Nat.cast_zero] at hu'; linarith
    obtain ⟨e, he⟩ := hne
    have he' := Finset.mem_filter.mp he
    have heE' := (Finset.mem_filter.mp he'.1).2
    intro p hp; have := heE' p hp; rw [he'.2] at this; omega
  have hu_ex : ∃ u ∈ Xhigh, (ρ / 16) * (X.card : ℝ) < (defect N u : ℝ) := by
    by_contra hall
    push Not at hall
    have hfilt : Xhigh.filter (fun u => (defect N u : ℝ) ≤ (ρ / 16) * (X.card : ℝ)) = Xhigh :=
      Finset.filter_eq_self.mpr hall
    have hbd := count_defect_le hNpos hApos (by positivity : (0 : ℝ) ≤ (ρ / 16) * (X.card : ℝ)) Xhigh hXhigh_spec
    rw [hfilt] at hbd
    have hpos : 0 < ρ * (X.card : ℝ) := mul_pos hρpos hXpos
    linarith
  obtain ⟨u, huHigh, hu_def⟩ := hu_ex
  let U' := (E'.filter (fun e => e.1 = u)).image Prod.snd
  have hU'_sub : U' ⊆ Y := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_product.mp (hE'sub (Finset.mem_filter.mp he).1)).2
  have hU'_card : (ρ / 4) * (Y.card : ℝ) ≤ (U'.card : ℝ) := by
    have hinj : Set.InjOn Prod.snd (E'.filter (fun e => e.1 = u) : Set (ℕ × ℕ)) := by
      intro e1 he1 e2 he2 h
      ext <;> [exact (Finset.mem_filter.mp he1).2.trans (Finset.mem_filter.mp he2).2.symm; exact h]
    rw [Finset.card_image_of_injOn hinj]
    exact (Finset.mem_filter.mp huHigh).2
  have hU'_ne : U'.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < (U'.card : ℝ) := lt_of_lt_of_le (by positivity) hU'_card
    exact_mod_cast this
  let Q0 : ℝ := A * B / D ^ 2
  have hQ0_pos : 0 < Q0 := by dsimp only [Q0]; positivity
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  let AU : ℕ := Nat.floor (Real.sqrt (128 * Q0 * B / ((N : ℝ) * ρ * (X.card : ℝ))))
  let BU : ℕ := Nat.floor (Real.sqrt (64 * (N : ℝ) * Q0 / (B * ρ * (X.card : ℝ))))
  have hU'_rep : ∀ v ∈ U',
      1 ≤ defPlus N v ∧ defPlus N v ≤ AU ∧ 1 ≤ defMinus N v ∧ defMinus N v ≤ BU ∧
      v * defMinus N v = N * defPlus N v := by
    intro v hv
    obtain ⟨e, he, hv_eq⟩ := Finset.mem_image.mp hv
    have he' := Finset.mem_filter.mp he
    have huv_E' : (u, v) ∈ E' := by
      have : (u, v) = e := by ext <;> [exact he'.2.symm; exact hv_eq.symm]
      rw [this]; exact he'.1
    have huv_E : (u, v) ∈ E := (Finset.mem_filter.mp huv_E').1
    have huv_val := (Finset.mem_filter.mp huv_E').2
    have huX := hXbd u (Finset.mem_filter.mp huHigh).1
    have hvY := hYbd v (hU'_sub hv)
    have hv_val : ∀ p, p.Prime → ((v.factorization p : ℤ) - (N.factorization p : ℤ)).natAbs ≤ 1 :=
      fun p hp => by have h := huv_val p hp; dsimp only at h; omega
    have hrel := mul_defMinus_eq_mul_defPlus hNpos hvY.1 hv_val
    have hprodR : (defect N u : ℝ) * (defect N v : ℝ) * (Nat.gcd u v : ℝ) ^ 2 = (u : ℝ) * (v : ℝ) := by
      exact_mod_cast defect_mul_defect_mul_gcd_sq hNpos huX.1 hvY.1 huv_val
    have hgcd_ge : D ≤ (Nat.gcd u v : ℝ) := hEbd (u, v) huv_E
    have hdef_ub : (defect N u : ℝ) * (defect N v : ℝ) ≤ 4 * Q0 := by
      have hsq : D ^ 2 ≤ (Nat.gcd u v : ℝ) ^ 2 := pow_le_pow_left₀ hDpos.le hgcd_ge 2
      have h1 : (defect N u : ℝ) * (defect N v : ℝ) * D ^ 2 ≤ 4 * A * B := by
        calc (defect N u : ℝ) * (defect N v : ℝ) * D ^ 2
            ≤ (defect N u : ℝ) * (defect N v : ℝ) * (Nat.gcd u v : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (u : ℝ) * (v : ℝ) := hprodR
          _ ≤ (2 * A) * (2 * B) := mul_le_mul huX.2.2 hvY.2.2 (Nat.cast_nonneg v) (by positivity)
          _ = 4 * A * B := by ring
      dsimp only [Q0]
      rw [show 4 * (A * B / D ^ 2) = 4 * A * B / D ^ 2 by ring, le_div_iff₀ (pow_pos hDpos 2)]
      exact h1
    have hv_def : (defect N v : ℝ) ≤ 64 * Q0 / (ρ * (X.card : ℝ)) := by
      rw [le_div_iff₀ (mul_pos hρpos hXpos)]
      have h1 : ((ρ / 16) * (X.card : ℝ)) * (defect N v : ℝ) ≤ 4 * Q0 := by
        calc ((ρ / 16) * (X.card : ℝ)) * (defect N v : ℝ)
            ≤ (defect N u : ℝ) * (defect N v : ℝ) := mul_le_mul_of_nonneg_right hu_def.le (Nat.cast_nonneg _)
          _ ≤ 4 * Q0 := hdef_ub
      linarith
    have hrelR : (v : ℝ) * (defMinus N v : ℝ) = (N : ℝ) * (defPlus N v : ℝ) := by exact_mod_cast hrel
    have hdefR : (defPlus N v : ℝ) * (defMinus N v : ℝ) = (defect N v : ℝ) := by
      unfold defect; push_cast; rfl
    have hplus_sq : (defPlus N v : ℝ) ^ 2 ≤ 128 * Q0 * B / ((N : ℝ) * ρ * (X.card : ℝ)) := by
      have h1 : (N : ℝ) * (defPlus N v : ℝ) ^ 2 = (v : ℝ) * (defect N v : ℝ) := by
        calc (N : ℝ) * (defPlus N v : ℝ) ^ 2
            = ((N : ℝ) * (defPlus N v : ℝ)) * (defPlus N v : ℝ) := by ring
          _ = ((v : ℝ) * (defMinus N v : ℝ)) * (defPlus N v : ℝ) := by rw [hrelR]
          _ = (v : ℝ) * ((defPlus N v : ℝ) * (defMinus N v : ℝ)) := by ring
          _ = (v : ℝ) * (defect N v : ℝ) := by rw [hdefR]
      rw [show 128 * Q0 * B / ((N : ℝ) * ρ * (X.card : ℝ)) =
          (2 * B * (64 * Q0 / (ρ * (X.card : ℝ)))) / (N : ℝ) by ring, le_div_iff₀' hNposR, h1]
      exact mul_le_mul hvY.2.2 hv_def (Nat.cast_nonneg _) (by positivity)
    have hminus_sq : (defMinus N v : ℝ) ^ 2 ≤ 64 * (N : ℝ) * Q0 / (B * ρ * (X.card : ℝ)) := by
      have h1 : (v : ℝ) * (defMinus N v : ℝ) ^ 2 = (N : ℝ) * (defect N v : ℝ) := by
        calc (v : ℝ) * (defMinus N v : ℝ) ^ 2
            = ((v : ℝ) * (defMinus N v : ℝ)) * (defMinus N v : ℝ) := by ring
          _ = ((N : ℝ) * (defPlus N v : ℝ)) * (defMinus N v : ℝ) := by rw [hrelR]
          _ = (N : ℝ) * ((defPlus N v : ℝ) * (defMinus N v : ℝ)) := by ring
          _ = (N : ℝ) * (defect N v : ℝ) := by rw [hdefR]
      rw [show 64 * (N : ℝ) * Q0 / (B * ρ * (X.card : ℝ)) =
          ((N : ℝ) * (64 * Q0 / (ρ * (X.card : ℝ)))) / B by ring, le_div_iff₀' hBpos]
      have h2 : B * (defMinus N v : ℝ) ^ 2 ≤ (v : ℝ) * (defMinus N v : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hvY.2.1 (sq_nonneg _)
      have h3 : (N : ℝ) * (defect N v : ℝ) ≤ (N : ℝ) * (64 * Q0 / (ρ * (X.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hv_def hNposR.le
      linarith
    refine ⟨defPlus_pos N v, Nat.le_floor ?_, defMinus_pos N v, Nat.le_floor ?_, hrel⟩
    · rw [← Real.sqrt_sq (Nat.cast_nonneg (defPlus N v))]; exact Real.sqrt_le_sqrt hplus_sq
    · rw [← Real.sqrt_sq (Nat.cast_nonneg (defMinus N v))]; exact Real.sqrt_le_sqrt hminus_sq
  have hAU_pos : 0 < AU := by obtain ⟨v0, hv0⟩ := hU'_ne; have h := hU'_rep v0 hv0; omega
  have hBU_pos : 0 < BU := by obtain ⟨v0, hv0⟩ := hU'_ne; have h := hU'_rep v0 hv0; omega
  let U : Finset ℕ := U'.image (· * dY)
  have hU_sub : U ⊆ Y0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    have hvY : v ∈ Y := hU'_sub hv
    rw [hY_eq_img] at hvY
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hvY
    rw [Nat.div_mul_cancel (hdY_dvd y hy)]
    exact hYs_sub hy
  have hU_card : U.card = U'.card :=
    Finset.card_image_of_injOn fun v1 _ v2 _ h => Nat.eq_of_mul_eq_mul_right hdY_pos h
  have hU_lb : (1 / 4 : ℝ) * (F0 / K0) ^ (24 : ℕ) * (Y0.card : ℝ) ≤ (U.card : ℝ) := by
    rw [hU_card]
    have hstep1 : (F0 / K0) ^ (20 : ℕ) * (Y0.card : ℝ) ≤ z * (Y0.card : ℝ) :=
      mul_le_mul_of_nonneg_right hz_lb (Nat.cast_nonneg _)
    have hstep2 : (F0 / K0) ^ (4 : ℕ) * ((F0 / K0) ^ (20 : ℕ) * (Y0.card : ℝ)) ≤ ρ * (Y.card : ℝ) :=
      mul_le_mul hρ_lb (hstep1.trans hz_Y) (by positivity) hρpos.le
    calc (1 / 4 : ℝ) * (F0 / K0) ^ (24 : ℕ) * (Y0.card : ℝ)
        = (1 / 4 : ℝ) * ((F0 / K0) ^ (4 : ℕ) * ((F0 / K0) ^ (20 : ℕ) * (Y0.card : ℝ))) := by ring
      _ ≤ (1 / 4 : ℝ) * (ρ * (Y.card : ℝ)) := mul_le_mul_of_nonneg_left hstep2 (by norm_num)
      _ = (ρ / 4) * (Y.card : ℝ) := by ring
      _ ≤ (U'.card : ℝ) := hU'_card
  have harea : (AU : ℝ) * (BU : ℝ) ≤ (512 / F0) * (U.card : ℝ) := by
    rw [hU_card]
    have hAU_le : (AU : ℝ) ≤ Real.sqrt (128 * Q0 * B / ((N : ℝ) * ρ * (X.card : ℝ))) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have hBU_le : (BU : ℝ) ≤ Real.sqrt (64 * (N : ℝ) * Q0 / (B * ρ * (X.card : ℝ))) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have hprod_le : (AU : ℝ) * (BU : ℝ) ≤ 128 * Q0 / (ρ * (X.card : ℝ)) := by
      calc (AU : ℝ) * (BU : ℝ)
          ≤ Real.sqrt (128 * Q0 * B / ((N : ℝ) * ρ * (X.card : ℝ))) *
            Real.sqrt (64 * (N : ℝ) * Q0 / (B * ρ * (X.card : ℝ))) :=
            mul_le_mul hAU_le hBU_le (Nat.cast_nonneg BU) (Real.sqrt_nonneg _)
        _ = Real.sqrt ((128 * Q0 * B / ((N : ℝ) * ρ * (X.card : ℝ))) *
              (64 * (N : ℝ) * Q0 / (B * ρ * (X.card : ℝ)))) :=
            (Real.sqrt_mul (by positivity) _).symm
        _ = Real.sqrt (8192 * (Q0 / (ρ * (X.card : ℝ))) ^ 2) := by
            congr 1; field_simp [hBpos.ne', hNposR.ne', hρpos.ne', hXpos.ne']; ring
        _ ≤ Real.sqrt ((128 * (Q0 / (ρ * (X.card : ℝ)))) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            have : (0 : ℝ) ≤ (Q0 / (ρ * (X.card : ℝ))) ^ 2 := sq_nonneg _
            nlinarith
        _ = 128 * Q0 / (ρ * (X.card : ℝ)) := by
            rw [Real.sqrt_sq (mul_nonneg (by norm_num) (div_nonneg hQ0_pos.le (mul_nonneg hρpos.le hXpos.le)))]; ring
    have hQ0_F0 : Q0 / (ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ)) ≤ 1 / F0 := by
      have hQ0_inv : D ^ 2 / (A * B) = 1 / Q0 := by dsimp only [Q0]; rw [one_div_div]
      have hF0_le : F0 ≤ ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) / Q0 := by
        rw [hQ0_inv] at hF0_le_Q; linarith [show ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (1 / Q0) =
          ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) / Q0 by ring]
      rw [div_le_div_iff₀ (by positivity) hF0pos, one_mul]
      rwa [le_div_iff₀ hQ0_pos, mul_comm] at hF0_le
    calc (AU : ℝ) * (BU : ℝ)
        ≤ 128 * Q0 / (ρ * (X.card : ℝ)) := hprod_le
      _ = (512 * (Q0 / (ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ)))) * ((ρ / 4) * (Y.card : ℝ)) := by
          field_simp [hρpos.ne', hXpos.ne', hYpos.ne']; ring
      _ ≤ (512 * (1 / F0)) * (U'.card : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQ0_F0 (by norm_num)) hU'_card (by positivity) (by positivity)
      _ = (512 / F0) * (U'.card : ℝ) := by ring
  let ξ : ℚ := ((N * dY : ℕ) : ℚ)
  have hξ_pos : 0 < ξ := by dsimp only [ξ]; exact_mod_cast Nat.mul_pos hNpos hdY_pos
  refine ⟨U, ξ, AU, BU, hU_sub, hU_lb, hξ_pos, hAU_pos, hBU_pos, harea, ?_⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨ha1, ha2, hb1, hb2, hrel⟩ := hU'_rep v hv
  refine ⟨defPlus N v, defMinus N v, ha1, ha2, hb1, hb2, ?_⟩
  have hrelQ : (v : ℚ) * (defMinus N v : ℚ) = (N : ℚ) * (defPlus N v : ℚ) := by exact_mod_cast hrel
  have hb_ne : (defMinus N v : ℚ) ≠ 0 := by exact_mod_cast (by omega : 0 < defMinus N v).ne'
  dsimp only [ξ]
  rw [eq_div_iff hb_ne]
  push_cast
  calc (v : ℚ) * (dY : ℚ) * (defMinus N v : ℚ)
      = ((v : ℚ) * (defMinus N v : ℚ)) * (dY : ℚ) := by ring
    _ = ((N : ℚ) * (defPlus N v : ℚ)) * (dY : ℚ) := by rw [hrelQ]
    _ = (N : ℚ) * (dY : ℚ) * (defPlus N v : ℚ) := by ring

set_option maxHeartbeats 1200000 in
/-- Hu-Jing Proposition 7.1: Extraction of a dense rational box with cardinality penalty. -/
theorem mp_extraction
    (hConc : ∀ {Q : ℝ}, 2 < Q → Q < 3 → ∃ C_Q > 0,
      ∀ (S : Finset ℤ) (α β : ℤ → ℝ) (μ : ℤ × ℤ → ℝ),
        (∀ i ∈ S, 0 ≤ α i) → (∀ j ∈ S, 0 ≤ β j) →
        (∑ i ∈ S, α i = 1) → (∑ j ∈ S, β j = 1) →
        (∀ p ∈ S ×ˢ S, 0 ≤ μ p) → (∑ p ∈ S ×ˢ S, μ p = 1) →
        ∀ {c lam : ℝ}, 0 < c → c ≤ 1 → 0 < lam → lam ≤ 4 / 5 →
        (∀ i ∈ S, ∀ j ∈ S, μ (i, j) ≤ c * lam ^ (i - j).natAbs * (α i * β j) ^ (1 - 1 / Q)) →
        (1 / 9 : ℝ) ≤ c ∧
        ∃ k ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun p => 2 ≤ (p.1 - k).natAbs + (p.2 - k).natAbs), μ p ≤
          C_Q * lam ^ (2 * Q - 2))
    {K0 : ℝ} (hK0_ge : 1 ≤ K0)
    (hGCD : ∀ (A B D : ℝ), 0 < A → 0 < B → 0 < D →
      ∀ (X Y : Finset ℕ) (E : Finset (ℕ × ℕ)),
        X.Nonempty → Y.Nonempty → E.Nonempty → E ⊆ X ×ˢ Y →
        (∀ x ∈ X, 0 < x ∧ A ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A) →
        (∀ y ∈ Y, 0 < y ∧ B ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * B) →
        (∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ)) →
        ((E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))) ^ (9 / 4 : ℝ) *
          (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤ K0) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ (A0 B0 D0 : ℝ), 0 < A0 → 0 < B0 → 0 < D0 →
      ∀ (X0 Y0 : Finset ℕ) (E0 : Finset (ℕ × ℕ)),
        X0.Nonempty → Y0.Nonempty → E0.Nonempty → E0 ⊆ X0 ×ˢ Y0 →
        (∀ x ∈ X0, 0 < x ∧ A0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A0) →
        (∀ y ∈ Y0, 0 < y ∧ B0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * B0) →
        (∀ e ∈ E0, D0 ≤ (Nat.gcd e.1 e.2 : ℝ)) →
        let ρ0 : ℝ := (E0.card : ℝ) / ((X0.card : ℝ) * (Y0.card : ℝ))
        let F0 : ℝ := ρ0 ^ (5 / 2 : ℝ) * (X0.card : ℝ) * (Y0.card : ℝ) *
          (D0 ^ 2 / (A0 * B0)) / (2000 : ℝ) ^ (p0 + 1)
        ∃ (U : Finset ℕ) (ξ : ℚ) (AU BU : ℕ),
          U ⊆ Y0 ∧
          (1 / 4 : ℝ) * (F0 / K0) ^ (24 : ℕ) * (Y0.card : ℝ) ≤ (U.card : ℝ) ∧
          0 < ξ ∧ 0 < AU ∧ 0 < BU ∧
          ((AU : ℝ) * (BU : ℝ) ≤ (512 / F0) * (U.card : ℝ)) ∧
          ∀ u ∈ U, ∃ a b : ℕ, 1 ≤ a ∧ a ≤ AU ∧ 1 ≤ b ∧ b ≤ BU ∧
            (u : ℚ) = ξ * (a : ℚ) / (b : ℚ) := by
  classical
  obtain ⟨CQ, hCQ_pos, hCQ⟩ := hConc (Q := (50 / 21 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨p0, hp0_ge2, hp0_tail⟩ := exists_tail_threshold hCQ_pos (α := (11 / 105 : ℝ)) (by norm_num)
  refine ⟨p0, hp0_ge2, ?_⟩
  intro A0 B0 D0 hA0 hB0 hD0 X0 Y0 E0 hX0ne hY0ne hE0ne hE0sub hX0 hY0 hE0
  intro ρ0 F0
  have hX0pos : (0 : ℝ) < (X0.card : ℝ) := by exact_mod_cast hX0ne.card_pos
  have hY0pos : (0 : ℝ) < (Y0.card : ℝ) := by exact_mod_cast hY0ne.card_pos
  have hE0pos : (0 : ℝ) < (E0.card : ℝ) := by exact_mod_cast hE0ne.card_pos
  have hρ0pos : 0 < ρ0 := div_pos hE0pos (mul_pos hX0pos hY0pos)
  have hF0pos : 0 < F0 := by
    dsimp only [F0]; positivity
  have hK0pos : 0 < K0 := lt_of_lt_of_le zero_lt_one hK0_ge
  let MX : ℕ := X0.sup id
  let MY : ℕ := Y0.sup id
  have hMX_pos : 1 ≤ MX := by
    obtain ⟨x, hx⟩ := hX0ne
    have hle : x ≤ MX := Finset.le_sup (f := id) hx
    have := (hX0 x hx).1; omega
  have hMY_pos : 1 ≤ MY := by
    obtain ⟨y, hy⟩ := hY0ne
    have hle : y ≤ MY := Finset.le_sup (f := id) hy
    have := (hY0 y hy).1; omega
  -- State space: (Xs, Ys, Es, dX, dY)
  let Univ := X0.powerset ×ˢ Y0.powerset ×ˢ E0.powerset ×ˢ Finset.Icc 1 MX ×ˢ Finset.Icc 1 MY
  let IsValid : Finset ℕ × Finset ℕ × Finset (ℕ × ℕ) × ℕ × ℕ → Prop := fun s =>
    s.1.Nonempty ∧ s.2.1.Nonempty ∧ s.2.2.1.Nonempty ∧ s.2.2.1 ⊆ s.1 ×ˢ s.2.1 ∧
    1 ≤ s.2.2.2.1 ∧ 1 ≤ s.2.2.2.2 ∧
    (∀ x ∈ s.1, s.2.2.2.1 ∣ x) ∧ (∀ y ∈ s.2.1, s.2.2.2.2 ∣ y) ∧
    (∀ p ∈ allPrimes X0 Y0, p ∣ s.2.2.2.1 * s.2.2.2.2 →
      (∀ x ∈ s.1, ¬ p ∣ x / s.2.2.2.1) ∧ (∀ y ∈ s.2.1, ¬ p ∣ y / s.2.2.2.2))
  let ValidStates := Univ.filter IsValid
  let scX : Finset ℕ × Finset ℕ × Finset (ℕ × ℕ) × ℕ × ℕ → Finset ℕ :=
    fun s => s.1.image (· / s.2.2.2.1)
  let scY : Finset ℕ × Finset ℕ × Finset (ℕ × ℕ) × ℕ × ℕ → Finset ℕ :=
    fun s => s.2.1.image (· / s.2.2.2.2)
  let scE : Finset ℕ × Finset ℕ × Finset (ℕ × ℕ) × ℕ × ℕ → Finset (ℕ × ℕ) :=
    fun s => s.2.2.1.image (fun e => (e.1 / s.2.2.2.1, e.2 / s.2.2.2.2))
  let score : Finset ℕ × Finset ℕ × Finset (ℕ × ℕ) × ℕ × ℕ → ℝ := fun s =>
    let ρs := (s.2.2.1.card : ℝ) / ((s.1.card : ℝ) * (s.2.1.card : ℝ))
    let zs := ((s.1.card : ℝ) * (s.2.1.card : ℝ)) / ((X0.card : ℝ) * (Y0.card : ℝ))
    let As := A0 / (s.2.2.2.1 : ℝ)
    let Bs := B0 / (s.2.2.2.2 : ℝ)
    let Ds := D0 / (Nat.gcd s.2.2.2.1 s.2.2.2.2 : ℝ)
    let rs := (smlPrimes p0 (scX s) (scY s)).card
    ρs ^ (5 / 2 : ℝ) * (s.1.card : ℝ) * (s.2.1.card : ℝ) *
      (Ds ^ 2 / (As * Bs)) * zs ^ (1 / 20 : ℝ) / (2000 : ℝ) ^ rs
  let s0 : Finset ℕ × Finset ℕ × Finset (ℕ × ℕ) × ℕ × ℕ := (X0, Y0, E0, 1, 1)
  have hs0_mem : s0 ∈ ValidStates := by
    refine Finset.mem_filter.mpr ⟨?_, hX0ne, hY0ne, hE0ne, hE0sub, le_rfl, le_rfl,
      fun _ _ => one_dvd _, fun _ _ => one_dvd _, fun p hp hpdvd => ?_⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Subset.rfl,
        Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Subset.rfl,
        Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Subset.rfl,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hMX_pos⟩,
        Finset.mem_Icc.mpr ⟨le_rfl, hMY_pos⟩⟩⟩⟩⟩
    · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hp
      exact absurd hpdvd (Nat.prime_of_mem_primeFactors hu).not_dvd_one
  have hs0_ge : F0 ≤ score s0 := by
    have hscX0 : scX s0 = X0 := by simp [scX, s0]
    have hscY0 : scY s0 = Y0 := by simp [scY, s0]
    have hz0 : ((X0.card : ℝ) * (Y0.card : ℝ)) / ((X0.card : ℝ) * (Y0.card : ℝ)) = 1 :=
      div_self (mul_pos hX0pos hY0pos).ne'
    have hr0 : (smlPrimes p0 X0 Y0).card ≤ p0 + 1 := by
      have hsub : smlPrimes p0 X0 Y0 ⊆ Finset.range (p0 + 1) := fun q hq => by
        rw [Finset.mem_range]; have := (Finset.mem_filter.mp hq).2; omega
      exact (Finset.card_le_card hsub).trans (by simp)
    have hsc0_eq : score s0 = ρ0 ^ (5 / 2 : ℝ) * (X0.card : ℝ) * (Y0.card : ℝ) *
        (D0 ^ 2 / (A0 * B0)) / (2000 : ℝ) ^ (smlPrimes p0 X0 Y0).card := by
      dsimp only [score, s0, ρ0]
      rw [hscX0, hscY0, hz0, Real.one_rpow, mul_one]
      simp
    rw [hsc0_eq]
    dsimp only [F0]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_right₀ (by norm_num) hr0
  obtain ⟨smax, hsmax_mem, hsmax_max⟩ := Finset.exists_max_image ValidStates score ⟨s0, hs0_mem⟩
  have hF0_le_max : F0 ≤ score smax := hs0_ge.trans (hsmax_max s0 hs0_mem)
  -- Unpack smax
  rcases smax with ⟨Xs, Ys, Es, dX, dY⟩
  have hsmax_univ := (Finset.mem_filter.mp hsmax_mem).1
  have hsmax_val := (Finset.mem_filter.mp hsmax_mem).2
  dsimp only [IsValid] at hsmax_val
  have hXs_sub : Xs ⊆ X0 := Finset.mem_powerset.mp (Finset.mem_product.mp hsmax_univ).1
  have hYs_sub : Ys ⊆ Y0 := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_product.mp hsmax_univ).2).1
  have hEs_sub0 : Es ⊆ E0 := Finset.mem_powerset.mp (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hsmax_univ).2).2).1
  obtain ⟨hXs_ne, hYs_ne, hEs_ne, hEs_sub, hdX1, hdY1, hdX_dvd, hdY_dvd, hdisj⟩ := hsmax_val
  let X := scX (Xs, Ys, Es, dX, dY)
  let Y := scY (Xs, Ys, Es, dX, dY)
  let E := scE (Xs, Ys, Es, dX, dY)
  let A : ℝ := A0 / (dX : ℝ)
  let B : ℝ := B0 / (dY : ℝ)
  let D : ℝ := D0 / (Nat.gcd dX dY : ℝ)
  have hdX_pos : (0 : ℝ) < (dX : ℝ) := by exact_mod_cast (by omega : 0 < dX)
  have hdY_pos : (0 : ℝ) < (dY : ℝ) := by exact_mod_cast (by omega : 0 < dY)
  have hgcd_d_pos : (0 : ℝ) < (Nat.gcd dX dY : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left dY (by omega : 0 < dX)
  have hApos : 0 < A := div_pos hA0 hdX_pos
  have hBpos : 0 < B := div_pos hB0 hdY_pos
  have hDpos : 0 < D := div_pos hD0 hgcd_d_pos
  have hX_card : X.card = Xs.card := by
    refine Finset.card_image_of_injOn fun x1 hx1 x2 hx2 h => ?_
    calc x1 = dX * (x1 / dX) := (Nat.mul_div_cancel' (hdX_dvd x1 hx1)).symm
      _ = dX * (x2 / dX) := by rw [h]
      _ = x2 := Nat.mul_div_cancel' (hdX_dvd x2 hx2)
  have hY_card : Y.card = Ys.card := by
    refine Finset.card_image_of_injOn fun y1 hy1 y2 hy2 h => ?_
    calc y1 = dY * (y1 / dY) := (Nat.mul_div_cancel' (hdY_dvd y1 hy1)).symm
      _ = dY * (y2 / dY) := by rw [h]
      _ = y2 := Nat.mul_div_cancel' (hdY_dvd y2 hy2)
  have hE_card : E.card = Es.card := by
    refine Finset.card_image_of_injOn fun e1 he1 e2 he2 h => ?_
    have he1' := Finset.mem_product.mp (hEs_sub he1)
    have he2' := Finset.mem_product.mp (hEs_sub he2)
    have h1 : e1.1 / dX = e2.1 / dX := congrArg Prod.fst h
    have h2 : e1.2 / dY = e2.2 / dY := congrArg Prod.snd h
    ext
    · calc e1.1 = dX * (e1.1 / dX) := (Nat.mul_div_cancel' (hdX_dvd _ he1'.1)).symm
        _ = dX * (e2.1 / dX) := by rw [h1]
        _ = e2.1 := Nat.mul_div_cancel' (hdX_dvd _ he2'.1)
    · calc e1.2 = dY * (e1.2 / dY) := (Nat.mul_div_cancel' (hdY_dvd _ he1'.2)).symm
        _ = dY * (e2.2 / dY) := by rw [h2]
        _ = e2.2 := Nat.mul_div_cancel' (hdY_dvd _ he2'.2)
  have hXne : X.Nonempty := hXs_ne.image _
  have hYne : Y.Nonempty := hYs_ne.image _
  have hEne : E.Nonempty := hEs_ne.image _
  have hEsub : E ⊆ X ×ˢ Y := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    have he0' := Finset.mem_product.mp (hEs_sub he0)
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he0'.1, Finset.mem_image_of_mem _ he0'.2⟩
  have hXbd : ∀ u ∈ X, 0 < u ∧ A ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * A := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    have hx0 := hX0 x (hXs_sub hx)
    have hdvd := hdX_dvd x hx
    have hcast : ((x / dX : ℕ) : ℝ) = (x : ℝ) / (dX : ℝ) := Nat.cast_div hdvd hdX_pos.ne'
    refine ⟨Nat.div_pos (Nat.le_of_dvd hx0.1 hdvd) (Nat.lt_of_lt_of_le zero_lt_one hdX1), ?_, ?_⟩
    · rw [hcast]; exact div_le_div_of_nonneg_right hx0.2.1 hdX_pos.le
    · rw [hcast]; dsimp only [A]; rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hx0.2.2 hdX_pos.le
  have hYbd : ∀ v ∈ Y, 0 < v ∧ B ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * B := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hy0 := hY0 y (hYs_sub hy)
    have hdvd := hdY_dvd y hy
    have hcast : ((y / dY : ℕ) : ℝ) = (y : ℝ) / (dY : ℝ) := Nat.cast_div hdvd hdY_pos.ne'
    refine ⟨Nat.div_pos (Nat.le_of_dvd hy0.1 hdvd) (Nat.lt_of_lt_of_le zero_lt_one hdY1), ?_, ?_⟩
    · rw [hcast]; exact div_le_div_of_nonneg_right hy0.2.1 hdY_pos.le
    · rw [hcast]; dsimp only [B]; rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hy0.2.2 hdY_pos.le
  have hEbd : ∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ) := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    have he0' := Finset.mem_product.mp (hEs_sub he0)
    have hx0 := (hX0 e0.1 (hXs_sub he0'.1)).1
    have hy0 := (hY0 e0.2 (hYs_sub he0'.2)).1
    have hgeq : Nat.gcd (e0.1 / dX) (e0.2 / dY) * Nat.gcd dX dY = Nat.gcd e0.1 e0.2 := by
      refine gcd_div_mul_gcd_eq hx0 hy0 (hdX_dvd _ he0'.1) (hdY_dvd _ he0'.2) fun p hp hpdvd => ?_
      have hp_all0 : p ∈ allPrimes X0 Y0 := by
        rcases hp.dvd_mul.mp hpdvd with h1 | h2
        · exact Finset.mem_biUnion.mpr ⟨e0.1, Finset.mem_union_left Y0 (hXs_sub he0'.1),
            Nat.mem_primeFactors.mpr ⟨hp, h1.trans (hdX_dvd _ he0'.1), hx0.ne'⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨e0.2, Finset.mem_union_right X0 (hYs_sub he0'.2),
            Nat.mem_primeFactors.mpr ⟨hp, h2.trans (hdY_dvd _ he0'.2), hy0.ne'⟩⟩
      have ⟨h1, h2⟩ := hdisj p hp_all0 hpdvd
      exact ⟨h1 e0.1 he0'.1, h2 e0.2 he0'.2⟩
    have hgeqR : (Nat.gcd (e0.1 / dX) (e0.2 / dY) : ℝ) * (Nat.gcd dX dY : ℝ) = (Nat.gcd e0.1 e0.2 : ℝ) := by
      exact_mod_cast hgeq
    dsimp only [D]
    rw [div_le_iff₀ hgcd_d_pos, hgeqR]
    exact hE0 e0 (hEs_sub0 he0)
  -- Density ρ and proportion z of maximizer
  set ρ : ℝ := (E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ)) with hρ_def
  set z : ℝ := ((X.card : ℝ) * (Y.card : ℝ)) / ((X0.card : ℝ) * (Y0.card : ℝ)) with hz_def
  set r : ℕ := (smlPrimes p0 X Y).card with hr_def
  have hXpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hXne.card_pos
  have hYpos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hYne.card_pos
  have hEpos : (0 : ℝ) < (E.card : ℝ) := by exact_mod_cast hEne.card_pos
  have hρpos : 0 < ρ := div_pos hEpos (mul_pos hXpos hYpos)
  have hρle1 : ρ ≤ 1 := by
    rw [hρ_def, div_le_one (mul_pos hXpos hYpos)]
    have : E.card ≤ X.card * Y.card := by simpa using Finset.card_le_card hEsub
    exact_mod_cast this
  have hzpos : 0 < z := div_pos (mul_pos hXpos hYpos) (mul_pos hX0pos hY0pos)
  have hzle1 : z ≤ 1 := by
    rw [hz_def, div_le_one (mul_pos hX0pos hY0pos)]
    have h1 : X.card ≤ X0.card := hX_card ▸ Finset.card_le_card hXs_sub
    have h2 : Y.card ≤ Y0.card := hY_card ▸ Finset.card_le_card hYs_sub
    exact_mod_cast Nat.mul_le_mul h1 h2
  have hscore_eq : score (Xs, Ys, Es, dX, dY) =
      ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) *
        z ^ (1 / 20 : ℝ) / (2000 : ℝ) ^ r := by
    dsimp only [score]
    rw [← hX_card, ← hY_card, ← hE_card]
  -- Step 1: Lower bounds on ρ and z using hGCD
  have hgcd_max := hGCD A B D hApos hBpos hDpos X Y E hXne hYne hEne hEsub hXbd hYbd hEbd
  have hmax_le : score (Xs, Ys, Es, dX, dY) ≤ K0 * ρ ^ (1 / 4 : ℝ) * z ^ (1 / 20 : ℝ) := by
    rw [hscore_eq]
    have h2000_ge1 : (1 : ℝ) ≤ (2000 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have hρ_split : ρ ^ (5 / 2 : ℝ) = ρ ^ (9 / 4 : ℝ) * ρ ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hρpos]; congr 1; norm_num
    have hnum : ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) * z ^ (1 / 20 : ℝ) ≤
        K0 * ρ ^ (1 / 4 : ℝ) * z ^ (1 / 20 : ℝ) := by
      rw [hρ_split]
      have h1 : (ρ ^ (9 / 4 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) *
          (ρ ^ (1 / 4 : ℝ) * z ^ (1 / 20 : ℝ)) ≤ K0 * (ρ ^ (1 / 4 : ℝ) * z ^ (1 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_right hgcd_max (mul_nonneg (Real.rpow_nonneg hρpos.le _) (Real.rpow_nonneg hzpos.le _))
      linarith
    exact (div_le_self (by positivity) h2000_ge1).trans hnum
  have hρ_lb : (F0 / K0) ^ (4 : ℕ) ≤ ρ := by
    have h1 : F0 / K0 ≤ ρ ^ (1 / 4 : ℝ) := by
      have hzpow : z ^ (1 / 20 : ℝ) ≤ 1 := Real.rpow_le_one hzpos.le hzle1 (by norm_num)
      rw [div_le_iff₀ hK0pos]
      calc F0 ≤ K0 * ρ ^ (1 / 4 : ℝ) * z ^ (1 / 20 : ℝ) := hF0_le_max.trans hmax_le
        _ ≤ K0 * ρ ^ (1 / 4 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hzpow (mul_nonneg hK0pos.le (Real.rpow_nonneg hρpos.le _))
        _ = ρ ^ (1 / 4 : ℝ) * K0 := by ring
    have h4 := pow_le_pow_left₀ (div_pos hF0pos hK0pos).le h1 4
    have hpow4 : (ρ ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = ρ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρpos.le]; norm_num
    rwa [hpow4] at h4
  have hz_lb : (F0 / K0) ^ (20 : ℕ) ≤ z := by
    have h1 : F0 / K0 ≤ z ^ (1 / 20 : ℝ) := by
      have hρpow : ρ ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hρpos.le hρle1 (by norm_num)
      rw [div_le_iff₀ hK0pos]
      calc F0 ≤ K0 * ρ ^ (1 / 4 : ℝ) * z ^ (1 / 20 : ℝ) := hF0_le_max.trans hmax_le
        _ ≤ K0 * 1 * z ^ (1 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρpow hK0pos.le) (Real.rpow_nonneg hzpos.le _)
        _ = z ^ (1 / 20 : ℝ) * K0 := by ring
    have h20 := pow_le_pow_left₀ (div_pos hF0pos hK0pos).le h1 20
    have hpow20 : (z ^ (1 / 20 : ℝ)) ^ (20 : ℕ) = z := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]; norm_num
    rwa [hpow20] at h20
  -- Step 2: Local concentration at every prime p ∈ allPrimes X Y
  have hlocal : ∀ p ∈ allPrimes X Y,
      p0 < p ∧ ∃ kp : ℕ,
        (((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
          ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))).card : ℝ) ≤
          CQ * (p : ℝ) ^ (-(1 + 11 / 105 : ℝ)) * (E.card : ℝ)) := by
    intro p hp_all
    have hp_prime : p.Prime := by
      obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hp_all
      exact Nat.prime_of_mem_primeFactors hu
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    -- Prove p ∤ dX * dY using hdisj!
    have hp_all0 : p ∈ allPrimes X0 Y0 := by
      obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hp_all
      have hpdvd := (Nat.mem_primeFactors.mp hpu).2.1
      rcases Finset.mem_union.mp hu with huX | huY
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp huX
        exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left Y0 (hXs_sub hx),
          Nat.mem_primeFactors.mpr ⟨hp_prime, hpdvd.trans (Nat.div_dvd_of_dvd (hdX_dvd x hx)),
            (hX0 x (hXs_sub hx)).1.ne'⟩⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp huY
        exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_union_right X0 (hYs_sub hy),
          Nat.mem_primeFactors.mpr ⟨hp_prime, hpdvd.trans (Nat.div_dvd_of_dvd (hdY_dvd y hy)),
            (hY0 y (hYs_sub hy)).1.ne'⟩⟩
    have hp_ndvd_prod : ¬ p ∣ dX * dY := by
      intro hpdvd
      have ⟨h1, h2⟩ := hdisj p hp_all0 hpdvd
      obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hp_all
      have hpdvd_u := (Nat.mem_primeFactors.mp hpu).2.1
      rcases Finset.mem_union.mp hu with huX | huY
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp huX
        exact h1 x hx hpdvd_u
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp huY
        exact h2 y hy hpdvd_u
    have hp_ndvd_dX : ¬ p ∣ dX := fun h => hp_ndvd_prod (dvd_mul_of_dvd_left h dY)
    have hp_ndvd_dY : ¬ p ∣ dY := fun h => hp_ndvd_prod (dvd_mul_of_dvd_right h dX)
    let maxE : ℕ := (X ∪ Y).sup (fun u => u.factorization p)
    let S : Finset ℤ := (Finset.range (maxE + 1)).image (fun i : ℕ => (i : ℤ))
    let Xi : ℤ → Finset ℕ := fun i => X.filter (fun x => (x.factorization p : ℤ) = i)
    let Yj : ℤ → Finset ℕ := fun j => Y.filter (fun y => (y.factorization p : ℤ) = j)
    let Eij : ℤ → ℤ → Finset (ℕ × ℕ) := fun i j => E.filter (fun e => e.1 ∈ Xi i ∧ e.2 ∈ Yj j)
    let α : ℤ → ℝ := fun i => ((Xi i).card : ℝ) / (X.card : ℝ)
    let β : ℤ → ℝ := fun j => ((Yj j).card : ℝ) / (Y.card : ℝ)
    let μ : ℤ × ℤ → ℝ := fun q => ((Eij q.1 q.2).card : ℝ) / (E.card : ℝ)
    have hα0 : ∀ i ∈ S, 0 ≤ α i := fun i _ => div_nonneg (Nat.cast_nonneg _) hXpos.le
    have hβ0 : ∀ j ∈ S, 0 ≤ β j := fun j _ => div_nonneg (Nat.cast_nonneg _) hYpos.le
    have hμ0 : ∀ q ∈ S ×ˢ S, 0 ≤ μ q := fun q _ => div_nonneg (Nat.cast_nonneg _) hEpos.le
    have hX_maps : ∀ x ∈ X, (x.factorization p : ℤ) ∈ S := fun x hx => by
      refine Finset.mem_image.mpr ⟨x.factorization p, Finset.mem_range.mpr ?_, rfl⟩
      have hle : x.factorization p ≤ maxE :=
        Finset.le_sup (f := fun u => u.factorization p) (Finset.mem_union_left Y hx)
      omega
    have hY_maps : ∀ y ∈ Y, (y.factorization p : ℤ) ∈ S := fun y hy => by
      refine Finset.mem_image.mpr ⟨y.factorization p, Finset.mem_range.mpr ?_, rfl⟩
      have hle : y.factorization p ≤ maxE :=
        Finset.le_sup (f := fun u => u.factorization p) (Finset.mem_union_right X hy)
      omega
    have hα1 : ∑ i ∈ S, α i = 1 := by
      simp only [α, ← Finset.sum_div]
      rw [div_eq_one_iff_eq hXpos.ne']
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise
        (f := fun x : ℕ => (x.factorization p : ℤ)) (s := X) (t := S) (fun x hx => hX_maps x hx)).symm
    have hβ1 : ∑ j ∈ S, β j = 1 := by
      simp only [β, ← Finset.sum_div]
      rw [div_eq_one_iff_eq hYpos.ne']
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise
        (f := fun y : ℕ => (y.factorization p : ℤ)) (s := Y) (t := S) (fun y hy => hY_maps y hy)).symm
    have hμ1 : ∑ q ∈ S ×ˢ S, μ q = 1 := by
      simp only [μ, ← Finset.sum_div]
      rw [div_eq_one_iff_eq hEpos.ne']
      have hE_maps : ∀ e ∈ E, ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)) ∈ S ×ˢ S := fun e he =>
        Finset.mem_product.mpr ⟨hX_maps e.1 (Finset.mem_product.mp (hEsub he)).1,
          hY_maps e.2 (Finset.mem_product.mp (hEsub he)).2⟩
      have hN : ∑ q ∈ S ×ˢ S, (Eij q.1 q.2).card = E.card := by
        have h1 := (Finset.card_eq_sum_card_fiberwise
          (f := fun e : ℕ × ℕ => ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)))
          (s := E) (t := S ×ˢ S) (fun e he => hE_maps e he)).symm
        rw [← h1]
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 1; ext e
        simp only [Eij, Xi, Yj, Finset.mem_filter, Prod.ext_iff]
        constructor
        · rintro ⟨he, ⟨_, h1'⟩, ⟨_, h2'⟩⟩; exact ⟨he, h1', h2'⟩
        · rintro ⟨he, h1', h2'⟩
          have hmem := Finset.mem_product.mp (hEsub he)
          exact ⟨he, ⟨hmem.1, h1'⟩, ⟨hmem.2, h2'⟩⟩
      exact_mod_cast hN
    set c_p : ℝ := if p ≤ p0 then (2000 : ℝ) ^ (-(2 / 5 : ℝ)) else 1 with hcp_def
    have hcp0 : 0 < c_p := by
      dsimp only [c_p]; split_ifs
      · exact Real.rpow_pos_of_pos (by norm_num) _
      · exact zero_lt_one
    have hcp1 : c_p ≤ 1 := by
      dsimp only [c_p]; split_ifs
      · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      · exact le_rfl
    set lam : ℝ := (p : ℝ) ^ (-(2 / 5 : ℝ)) with hlam_def
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hp_pos _
    have hlam1 : lam ≤ 4 / 5 := by
      have h1 : lam ≤ (2 : ℝ) ^ (-(2 / 5 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      have h2 : (2 : ℝ) ^ (-(2 / 5 : ℝ)) ≤ 4 / 5 := by
        rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
        have hpow : ((5 / 4 : ℝ) ^ (5 : ℕ)) ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
        have h5 : ((5 / 4 : ℝ) ^ (5 : ℝ)) ≤ ((2 : ℝ) ^ (2 / 5 : ℝ)) ^ (5 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num), show (2 / 5 : ℝ) * 5 = 2 by norm_num]
          exact_mod_cast hpow
        have hroot := Real.rpow_le_rpow (by positivity) h5 (by norm_num : (0 : ℝ) ≤ 1 / 5)
        rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by positivity),
            show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hroot
        calc ((4 / 5 : ℝ))⁻¹ = 5 / 4 := by norm_num
          _ ≤ (2 : ℝ) ^ (2 / 5 : ℝ) := hroot
      exact h1.trans h2
    have hμ_bd : ∀ i ∈ S, ∀ j ∈ S,
        μ (i, j) ≤ c_p * lam ^ (i - j).natAbs * (α i * β j) ^ (1 - 1 / (50 / 21 : ℝ)) := by
      intro i hiS j hjS
      by_cases hEij : (Eij i j).Nonempty
      · obtain ⟨in_, _, rfl⟩ := Finset.mem_image.mp hiS
        obtain ⟨jn_, _, rfl⟩ := Finset.mem_image.mp hjS
        have hXi_eq : Xi (in_ : ℤ) = X.filter (fun x => x.factorization p = in_) := by
          ext x; simp [Xi]
        have hYj_eq : Yj (jn_ : ℤ) = Y.filter (fun y => y.factorization p = jn_) := by
          ext y; simp [Yj]
        have hEij_eq : Eij (in_ : ℤ) (jn_ : ℤ) =
            E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
              e.2 ∈ Y.filter (fun y => y.factorization p = jn_)) := by
          simp [Eij, hXi_eq, hYj_eq]
        have hEij' : (E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
            e.2 ∈ Y.filter (fun y => y.factorization p = jn_))).Nonempty := hEij_eq ▸ hEij
        obtain ⟨hXbar_card, hYbar_card, hEbar_card, hXbar_ne, hYbar_ne, hEbar_ne, _,
          _, hall_sub, _, _, _, hratio⟩ :=
          padic_slice_props hp_prime hApos hBpos hDpos hEsub hXbd hYbd hEbd in_ jn_ hEij'
        let Xbar := (X.filter (fun x => x.factorization p = in_)).image (· / p ^ in_)
        let Ybar := (Y.filter (fun y => y.factorization p = jn_)).image (· / p ^ jn_)
        let Ebar := (E.filter (fun e => e.1 ∈ X.filter (fun x => x.factorization p = in_) ∧
          e.2 ∈ Y.filter (fun y => y.factorization p = jn_))).image (fun e => (e.1 / p ^ in_, e.2 / p ^ jn_))
        -- Construct corresponding new valid state s_new!
        let Xs_new := Xs.filter (fun x => (x / dX).factorization p = in_)
        let Ys_new := Ys.filter (fun y => (y / dY).factorization p = jn_)
        let Es_new := Es.filter (fun e => e.1 ∈ Xs_new ∧ e.2 ∈ Ys_new)
        let dX_new := dX * p ^ in_
        let dY_new := dY * p ^ jn_
        let s_new := (Xs_new, Ys_new, Es_new, dX_new, dY_new)
        have hXs_new_img : Xs_new.image (· / dX) = X.filter (fun u => u.factorization p = in_) := by
          ext u
          simp only [Xs_new, X, scX, Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨x, ⟨hx, hfac⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hfac⟩
          · rintro ⟨⟨x, hx, rfl⟩, hfac⟩; exact ⟨x, ⟨hx, hfac⟩, rfl⟩
        have hYs_new_img : Ys_new.image (· / dY) = Y.filter (fun v => v.factorization p = jn_) := by
          ext v
          simp only [Ys_new, Y, scY, Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨y, ⟨hy, hfac⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, hfac⟩
          · rintro ⟨⟨y, hy, rfl⟩, hfac⟩; exact ⟨y, ⟨hy, hfac⟩, rfl⟩
        have hscX_new : scX s_new = Xbar := by
          ext u
          simp only [scX, s_new, Xbar, dX_new, ← hXs_new_img, Finset.mem_image]
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x / dX, ⟨x, hx, rfl⟩, Nat.div_div_eq_div_mul x dX (p ^ in_)⟩
          · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, (Nat.div_div_eq_div_mul x dX (p ^ in_)).symm⟩
        have hscY_new : scY s_new = Ybar := by
          ext v
          simp only [scY, s_new, Ybar, dY_new, ← hYs_new_img, Finset.mem_image]
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨y / dY, ⟨y, hy, rfl⟩, Nat.div_div_eq_div_mul y dY (p ^ jn_)⟩
          · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
            exact ⟨y, hy, (Nat.div_div_eq_div_mul y dY (p ^ jn_)).symm⟩
        have hEs_new_ne : Es_new.Nonempty := by
          obtain ⟨e, he⟩ := hEij'
          have he' := Finset.mem_filter.mp he
          obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he'.1
          have he0' := Finset.mem_product.mp (hEs_sub he0)
          exact ⟨e0, Finset.mem_filter.mpr ⟨he0,
            Finset.mem_filter.mpr ⟨he0'.1, (Finset.mem_filter.mp he'.2.1).2⟩,
            Finset.mem_filter.mpr ⟨he0'.2, (Finset.mem_filter.mp he'.2.2).2⟩⟩⟩
        have hXs_new_ne : Xs_new.Nonempty := by
          obtain ⟨e0, he0⟩ := hEs_new_ne; exact ⟨e0.1, (Finset.mem_filter.mp he0).2.1⟩
        have hYs_new_ne : Ys_new.Nonempty := by
          obtain ⟨e0, he0⟩ := hEs_new_ne; exact ⟨e0.2, (Finset.mem_filter.mp he0).2.2⟩
        have hdX_new_dvd : ∀ x ∈ Xs_new, dX_new ∣ x := fun x hx => by
          have hx' := Finset.mem_filter.mp hx
          have h1 := hdX_dvd x hx'.1
          have h2 : p ^ in_ ∣ x / dX := by rw [← hx'.2]; exact Nat.ordProj_dvd (x / dX) p
          rw [← Nat.mul_div_cancel' h1]
          exact mul_dvd_mul_left dX h2
        have hdY_new_dvd : ∀ y ∈ Ys_new, dY_new ∣ y := fun y hy => by
          have hy' := Finset.mem_filter.mp hy
          have h1 := hdY_dvd y hy'.1
          have h2 : p ^ jn_ ∣ y / dY := by rw [← hy'.2]; exact Nat.ordProj_dvd (y / dY) p
          rw [← Nat.mul_div_cancel' h1]
          exact mul_dvd_mul_left dY h2
        have hs_new_mem : s_new ∈ ValidStates := by
          refine Finset.mem_filter.mpr ⟨?_, hXs_new_ne, hYs_new_ne, hEs_new_ne,
            fun e he => Finset.mem_product.mpr (Finset.mem_filter.mp he).2,
            Nat.mul_pos (by omega) (pow_pos hp_prime.pos in_),
            Nat.mul_pos (by omega) (pow_pos hp_prime.pos jn_),
            hdX_new_dvd, hdY_new_dvd, ?_⟩
          · obtain ⟨x0, hx0⟩ := hXs_new_ne
            obtain ⟨y0, hy0⟩ := hYs_new_ne
            have hdX_le : dX_new ≤ MX :=
              (Nat.le_of_dvd (hX0 x0 (hXs_sub (Finset.mem_filter.mp hx0).1)).1 (hdX_new_dvd x0 hx0)).trans
                (Finset.le_sup (f := id) (hXs_sub (Finset.mem_filter.mp hx0).1))
            have hdY_le : dY_new ≤ MY :=
              (Nat.le_of_dvd (hY0 y0 (hYs_sub (Finset.mem_filter.mp hy0).1)).1 (hdY_new_dvd y0 hy0)).trans
                (Finset.le_sup (f := id) (hYs_sub (Finset.mem_filter.mp hy0).1))
            refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ((Finset.filter_subset _ Xs).trans hXs_sub),
              Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ((Finset.filter_subset _ Ys).trans hYs_sub),
              Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ((Finset.filter_subset _ Es).trans hEs_sub0),
              Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) (pow_pos hp_prime.pos in_), hdX_le⟩,
              Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) (pow_pos hp_prime.pos jn_), hdY_le⟩⟩⟩⟩⟩
          · intro q hq_all0 hqdvd
            have hq_prime : q.Prime := by
              obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hq_all0
              exact Nat.prime_of_mem_primeFactors hu
            have hmul_eq : dX_new * dY_new = (dX * dY) * p ^ (in_ + jn_) := by
              dsimp only [dX_new, dY_new]; rw [pow_add]; ring
            rw [hmul_eq] at hqdvd
            rcases hq_prime.dvd_mul.mp hqdvd with hq1 | hq2
            · have ⟨h1, h2⟩ := hdisj q hq_all0 hq1
              refine ⟨fun x hx hdiv => ?_, fun y hy hdiv => ?_⟩
              · rw [← Nat.div_div_eq_div_mul] at hdiv
                have hpi_dvd : p ^ in_ ∣ x / dX := by
                  rw [← (Finset.mem_filter.mp hx).2]; exact Nat.ordProj_dvd _ p
                exact h1 x (Finset.mem_filter.mp hx).1 (hdiv.trans (Nat.div_dvd_of_dvd hpi_dvd))
              · rw [← Nat.div_div_eq_div_mul] at hdiv
                have hpj_dvd : p ^ jn_ ∣ y / dY := by
                  rw [← (Finset.mem_filter.mp hy).2]; exact Nat.ordProj_dvd _ p
                exact h2 y (Finset.mem_filter.mp hy).1 (hdiv.trans (Nat.div_dvd_of_dvd hpj_dvd))
            · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp (hq_prime.dvd_of_dvd_pow hq2)
              refine ⟨fun x hx hdiv => ?_, fun y hy hdiv => ?_⟩
              · rw [hqp, ← Nat.div_div_eq_div_mul] at hdiv
                have hx' := Finset.mem_filter.mp hx
                have hpi_dvd : p ^ in_ ∣ x / dX := by rw [← hx'.2]; exact Nat.ordProj_dvd _ p
                have hxd_pos : 0 < x / dX := Nat.div_pos (Nat.le_of_dvd (hX0 x (hXs_sub hx'.1)).1 (hdX_dvd x hx'.1)) (Nat.lt_of_lt_of_le zero_lt_one hdX1)
                have hsucc : p ^ (in_ + 1) ∣ x / dX := by
                  rw [pow_succ, ← Nat.mul_div_cancel' hpi_dvd]; exact mul_dvd_mul_left _ hdiv
                have := (hp_prime.pow_dvd_iff_le_factorization hxd_pos.ne').mp hsucc
                omega
              · rw [hqp, ← Nat.div_div_eq_div_mul] at hdiv
                have hy' := Finset.mem_filter.mp hy
                have hpj_dvd : p ^ jn_ ∣ y / dY := by rw [← hy'.2]; exact Nat.ordProj_dvd _ p
                have hyd_pos : 0 < y / dY := Nat.div_pos (Nat.le_of_dvd (hY0 y (hYs_sub hy'.1)).1 (hdY_dvd y hy'.1)) (Nat.lt_of_lt_of_le zero_lt_one hdY1)
                have hsucc : p ^ (jn_ + 1) ∣ y / dY := by
                  rw [pow_succ, ← Nat.mul_div_cancel' hpj_dvd]; exact mul_dvd_mul_left _ hdiv
                have := (hp_prime.pow_dvd_iff_le_factorization hyd_pos.ne').mp hsucc
                omega
        -- Compare cardinalities of Xs_new, Ys_new, Es_new with Xi, Yj, Eij
        have hXs_new_card : Xs_new.card = (Xi (in_ : ℤ)).card := by
          rw [hXi_eq, ← hXs_new_img]
          refine (Finset.card_image_of_injOn fun x1 hx1 x2 hx2 h => ?_).symm
          have h1 := hdX_dvd x1 (Finset.mem_filter.mp hx1).1
          have h2 := hdX_dvd x2 (Finset.mem_filter.mp hx2).1
          calc x1 = dX * (x1 / dX) := (Nat.mul_div_cancel' h1).symm
            _ = dX * (x2 / dX) := by rw [h]
            _ = x2 := Nat.mul_div_cancel' h2
        have hYs_new_card : Ys_new.card = (Yj (jn_ : ℤ)).card := by
          rw [hYj_eq, ← hYs_new_img]
          refine (Finset.card_image_of_injOn fun y1 hy1 y2 hy2 h => ?_).symm
          have h1 := hdY_dvd y1 (Finset.mem_filter.mp hy1).1
          have h2 := hdY_dvd y2 (Finset.mem_filter.mp hy2).1
          calc y1 = dY * (y1 / dY) := (Nat.mul_div_cancel' h1).symm
            _ = dY * (y2 / dY) := by rw [h]
            _ = y2 := Nat.mul_div_cancel' h2
        have hEs_new_card : Es_new.card = (Eij (in_ : ℤ) (jn_ : ℤ)).card := by
          have himg : Es_new.image (fun e => (e.1 / dX, e.2 / dY)) = Eij (in_ : ℤ) (jn_ : ℤ) := by
            rw [hEij_eq]
            ext e
            simp only [Es_new, Xs_new, Ys_new, E, scE, X, scX, Y, scY, Finset.mem_image, Finset.mem_filter]
            constructor
            · rintro ⟨e0, ⟨he0, ⟨hx0, hfx⟩, ⟨hy0, hfy⟩⟩, rfl⟩
              exact ⟨⟨e0, he0, rfl⟩, ⟨⟨e0.1, hx0, rfl⟩, hfx⟩, ⟨⟨e0.2, hy0, rfl⟩, hfy⟩⟩
            · rintro ⟨⟨e0, he0, rfl⟩, ⟨_, hfx⟩, ⟨_, hfy⟩⟩
              have he0' := Finset.mem_product.mp (hEs_sub he0)
              exact ⟨e0, ⟨he0, ⟨he0'.1, hfx⟩, ⟨he0'.2, hfy⟩⟩, rfl⟩
          rw [← himg]
          refine (Finset.card_image_of_injOn fun e1 he1 e2 he2 h => ?_).symm
          have he1' := Finset.mem_product.mp (hEs_sub (Finset.mem_filter.mp he1).1)
          have he2' := Finset.mem_product.mp (hEs_sub (Finset.mem_filter.mp he2).1)
          have h1 : e1.1 / dX = e2.1 / dX := congrArg Prod.fst h
          have h2 : e1.2 / dY = e2.2 / dY := congrArg Prod.snd h
          ext
          · calc e1.1 = dX * (e1.1 / dX) := (Nat.mul_div_cancel' (hdX_dvd _ he1'.1)).symm
              _ = dX * (e2.1 / dX) := by rw [h1]
              _ = e2.1 := Nat.mul_div_cancel' (hdX_dvd _ he2'.1)
          · calc e1.2 = dY * (e1.2 / dY) := (Nat.mul_div_cancel' (hdY_dvd _ he1'.2)).symm
              _ = dY * (e2.2 / dY) := by rw [h2]
              _ = e2.2 := Nat.mul_div_cancel' (hdY_dvd _ he2'.2)
        have hmax_le_s := hsmax_max s_new hs_new_mem
        -- Relate score s_new to score smax and call mp_slice_algebra!
        have hαpos : 0 < α in_ := div_pos (by exact_mod_cast hXs_new_card ▸ hXs_new_ne.card_pos) hXpos
        have hβpos : 0 < β jn_ := div_pos (by exact_mod_cast hYs_new_card ▸ hYs_new_ne.card_pos) hYpos
        have hμpos : 0 < μ (in_, jn_) := div_pos (by exact_mod_cast hEs_new_card ▸ hEs_new_ne.card_pos) hEpos
        have hXicard_eq : ((Xi (in_ : ℤ)).card : ℝ) = (X.card : ℝ) * α in_ := by
          dsimp only [α]; exact (mul_div_cancel₀ _ hXpos.ne').symm
        have hYjcard_eq : ((Yj (jn_ : ℤ)).card : ℝ) = (Y.card : ℝ) * β jn_ := by
          dsimp only [β]; exact (mul_div_cancel₀ _ hYpos.ne').symm
        have hEijcard_eq : ((Eij (in_ : ℤ) (jn_ : ℤ)).card : ℝ) = (E.card : ℝ) * μ (in_, jn_) := by
          dsimp only [μ]; exact (mul_div_cancel₀ _ hEpos.ne').symm
        have hXY_new : (Xs_new.card : ℝ) * (Ys_new.card : ℝ) = (X.card : ℝ) * (Y.card : ℝ) * (α in_ * β jn_) := by
          rw [hXs_new_card, hYs_new_card, hXicard_eq, hYjcard_eq]; ring
        have hρ_new : (Es_new.card : ℝ) / ((Xs_new.card : ℝ) * (Ys_new.card : ℝ)) =
            ρ * (μ (in_, jn_) / (α in_ * β jn_)) := by
          rw [hEs_new_card, hEijcard_eq, hXY_new, hρ_def]; exact mul_div_mul_comm _ _ _ _
        have hz_new : ((Xs_new.card : ℝ) * (Ys_new.card : ℝ)) / ((X0.card : ℝ) * (Y0.card : ℝ)) =
            z * (α in_ * β jn_) := by
          rw [hXY_new, hz_def]; exact mul_div_right_comm _ _ _
        have hgcd_new : Nat.gcd dX_new dY_new = Nat.gcd dX dY * p ^ min in_ jn_ :=
          gcd_mul_pow_eq (by omega) (by omega) hp_prime hp_ndvd_dX hp_ndvd_dY
        have hratio_new : (D0 / (Nat.gcd dX_new dY_new : ℝ)) ^ 2 /
            ((A0 / (dX_new : ℝ)) * (B0 / (dY_new : ℝ))) =
            (D ^ 2 / (A * B)) * (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs := by
          rw [hgcd_new]
          have h1 : D0 / ((Nat.gcd dX dY * p ^ min in_ jn_ : ℕ) : ℝ) = D / (p : ℝ) ^ min in_ jn_ := by
            push_cast; dsimp only [D]; rw [div_div]
          have h2 : A0 / (dX_new : ℝ) = A / (p : ℝ) ^ in_ := by
            dsimp only [dX_new, A]; push_cast; rw [div_div]
          have h3 : B0 / (dY_new : ℝ) = B / (p : ℝ) ^ jn_ := by
            dsimp only [dY_new, B]; push_cast; rw [div_div]
          rw [h1, h2, h3]; exact hratio
        have hsml_le : (smlPrimes p0 Xbar Ybar).card + (if p ≤ p0 then 1 else 0) ≤ r := by
          rw [hr_def]
          by_cases hple : p ≤ p0
          · rw [if_pos hple]
            have hsub : smlPrimes p0 Xbar Ybar ⊆ (smlPrimes p0 X Y).erase p := fun q hq => by
              have hq' := Finset.mem_filter.mp hq
              have hq2 := Finset.mem_erase.mp (hall_sub hq'.1)
              exact Finset.mem_erase.mpr ⟨hq2.1, Finset.mem_filter.mpr ⟨hq2.2, hq'.2⟩⟩
            have hp_sml : p ∈ smlPrimes p0 X Y := Finset.mem_filter.mpr ⟨hp_all, hple⟩
            have hle := Finset.card_le_card hsub
            have hlt := Finset.card_erase_add_one hp_sml
            omega
          · rw [if_neg hple, add_zero]
            refine Finset.card_le_card fun q hq => ?_
            have hq' := Finset.mem_filter.mp hq
            exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hall_sub hq'.1)).2, hq'.2⟩
        have hpow_cmp : (2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card * (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0) ≤
            (2000 : ℝ) ^ r := by
          rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hsml_le
        have hscore_new_eq : score s_new =
            ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) *
            ((ρ * (μ (in_, jn_) / (α in_ * β jn_))) ^ (5 / 2 : ℝ) * (α in_ * β jn_) *
              (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs * (z * (α in_ * β jn_)) ^ (1 / 20 : ℝ)) /
            (2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card := by
          dsimp only [score, s_new]
          rw [hscX_new, hscY_new, hρ_new, hz_new, mul_assoc ((ρ * _) ^ _), hXY_new, hratio_new]
          ring
        rw [hscore_new_eq, hscore_eq] at hmax_le_s
        have hM_pos : 0 < (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) :=
          mul_pos (mul_pos hXpos hYpos) (div_pos (pow_pos hDpos 2) (mul_pos hApos hBpos))
        have hKnew_pos : 0 < (2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card := pow_pos (by norm_num) _
        have hKr_pos : 0 < (2000 : ℝ) ^ r := pow_pos (by norm_num) _
        have hKstep_pos : 0 < (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0) := pow_pos (by norm_num) _
        have hmain_le : (ρ * (μ (in_, jn_) / (α in_ * β jn_))) ^ (5 / 2 : ℝ) * (α in_ * β jn_) *
            (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs * (z * (α in_ * β jn_)) ^ (1 / 20 : ℝ) *
            (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0) ≤
            ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ) := by
          have h1 := (div_le_div_iff₀ hKnew_pos hKr_pos).mp hmax_le_s
          have h2 : ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) * (2000 : ℝ) ^ r *
              ((ρ * (μ (in_, jn_) / (α in_ * β jn_))) ^ (5 / 2 : ℝ) * (α in_ * β jn_) *
                (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs * (z * (α in_ * β jn_)) ^ (1 / 20 : ℝ) *
                (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0)) ≤
              ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) * (2000 : ℝ) ^ r *
              (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) := by
            have hrhs_eq : ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) *
                z ^ (1 / 20 : ℝ) * (2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card =
                ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) *
                (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) * (2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card := by ring
            have hmul := mul_le_mul_of_nonneg_right h1 hKstep_pos.le
            calc _ = ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) *
                    ((ρ * (μ (in_, jn_) / (α in_ * β jn_))) ^ (5 / 2 : ℝ) * (α in_ * β jn_) *
                      (p : ℝ) ^ ((in_ : ℤ) - (jn_ : ℤ)).natAbs * (z * (α in_ * β jn_)) ^ (1 / 20 : ℝ)) *
                    (2000 : ℝ) ^ r) * (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0) := by ring
              _ ≤ (ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) *
                    z ^ (1 / 20 : ℝ) * (2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card) *
                    (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0) := hmul
              _ = ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) *
                    (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) *
                    ((2000 : ℝ) ^ (smlPrimes p0 Xbar Ybar).card * (2000 : ℝ) ^ (if p ≤ p0 then 1 else 0)) := by
                    rw [hrhs_eq]; ring
              _ ≤ ((X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) *
                    (ρ ^ (5 / 2 : ℝ) * z ^ (1 / 20 : ℝ)) * (2000 : ℝ) ^ r :=
                    mul_le_mul_of_nonneg_left hpow_cmp
                      (mul_nonneg hM_pos.le (mul_nonneg (Real.rpow_nonneg hρpos.le _) (Real.rpow_nonneg hzpos.le _)))
              _ = _ := by ring
          exact le_of_mul_le_mul_left h2 (mul_pos hM_pos hKr_pos)
        have halg := mp_slice_algebra hρpos hzpos hαpos hβpos hμpos hp_pos hKstep_pos hmain_le
        have hcp_eq : ((2000 : ℝ) ^ (if p ≤ p0 then 1 else 0)) ^ (-(2 / 5 : ℝ)) = c_p := by
          dsimp only [c_p]; split_ifs <;> simp only [pow_one, pow_zero, Real.one_rpow]
        rw [hcp_eq, ← hlam_def] at halg
        exact halg
      · have hzero : μ (i, j) = 0 := by
          dsimp only [μ]
          rw [Finset.not_nonempty_iff_eq_empty.mp hEij, Finset.card_empty, Nat.cast_zero, zero_div]
        rw [hzero]
        exact mul_nonneg (mul_nonneg hcp0.le (pow_nonneg hlam0.le _))
          (Real.rpow_nonneg (mul_nonneg (hα0 i hiS) (hβ0 j hjS)) _)
    obtain ⟨hcp_ge, k, hkS, hconc_bd⟩ := hCQ S α β μ hα0 hβ0 hα1 hβ1 hμ0 hμ1 hcp0 hcp1 hlam0 hlam1 hμ_bd
    have hp_gt : p0 < p := by
      by_contra hle
      push Not at hle
      rw [hcp_def, if_pos hle] at hcp_ge
      have h2000 : (2000 : ℝ) ^ (-(2 / 5 : ℝ)) < 1 / 9 := by
        rw [Real.rpow_neg (by norm_num), one_div, inv_lt_inv₀ (by positivity) (by norm_num)]
        have hpow : (9 : ℝ) ^ (5 : ℕ) < (2000 : ℝ) ^ (2 : ℕ) := by norm_num
        have h5 : (9 : ℝ) ^ (5 : ℝ) < ((2000 : ℝ) ^ (2 / 5 : ℝ)) ^ (5 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num), show (2 / 5 : ℝ) * 5 = 2 by norm_num]
          exact_mod_cast hpow
        have hroot := Real.rpow_lt_rpow (by positivity) h5 (by norm_num : (0 : ℝ) < 1 / 5)
        rwa [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by positivity),
          show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hroot
      linarith
    obtain ⟨kp, _, rfl⟩ := Finset.mem_image.mp hkS
    refine ⟨hp_gt, kp, ?_⟩
    have hlam_exp : lam ^ (2 * (50 / 21 : ℝ) - 2) = (p : ℝ) ^ (-(1 + 11 / 105 : ℝ)) := by
      rw [hlam_def, ← Real.rpow_mul hp_pos.le]; congr 1; norm_num
    rw [hlam_exp] at hconc_bd
    have hfilt_eq : (((E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
        ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))).card : ℝ) / (E.card : ℝ)) =
        ∑ q ∈ (S ×ˢ S).filter (fun q => 2 ≤ (q.1 - (kp : ℤ)).natAbs + (q.2 - (kp : ℤ)).natAbs), μ q := by
      simp only [μ, ← Finset.sum_div]
      congr 1
      let Ebad := E.filter (fun e => ¬ (((e.1.factorization p : ℤ) - (kp : ℤ)).natAbs +
        ((e.2.factorization p : ℤ) - (kp : ℤ)).natAbs ≤ 1))
      let Stail := (S ×ˢ S).filter (fun q => 2 ≤ (q.1 - (kp : ℤ)).natAbs + (q.2 - (kp : ℤ)).natAbs)
      have hmaps : ∀ e ∈ Ebad, ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)) ∈ Stail := fun e he => by
        have he' := Finset.mem_filter.mp he
        have hmem := Finset.mem_product.mp (hEsub he'.1)
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hX_maps _ hmem.1, hY_maps _ hmem.2⟩, by omega⟩
      have hN : Ebad.card = ∑ q ∈ Stail, (Eij q.1 q.2).card := by
        rw [Finset.card_eq_sum_card_fiberwise
          (f := fun e : ℕ × ℕ => ((e.1.factorization p : ℤ), (e.2.factorization p : ℤ)))
          (s := Ebad) (t := Stail) (fun e he => hmaps e he)]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq' := Finset.mem_filter.mp hq
        congr 1; ext e
        simp only [Ebad, Eij, Xi, Yj, Finset.mem_filter, Prod.ext_iff]
        constructor
        · rintro ⟨⟨he, _⟩, h1', h2'⟩
          have hmem := Finset.mem_product.mp (hEsub he)
          exact ⟨he, ⟨hmem.1, h1'⟩, ⟨hmem.2, h2'⟩⟩
        · rintro ⟨he, ⟨_, h1'⟩, ⟨_, h2'⟩⟩
          refine ⟨⟨he, ?_⟩, h1', h2'⟩
          rw [h1', h2']; omega
      have hNR : (Ebad.card : ℝ) = ∑ q ∈ Stail, ((Eij q.1 q.2).card : ℝ) := by exact_mod_cast hN
      exact hNR
    rw [← hfilt_eq, div_le_iff₀ hEpos] at hconc_bd
    exact hconc_bd
  -- Step 3-4: Delegate to mp_extract_box_of_local!
  have hY_ratio : z * (Y0.card : ℝ) ≤ (Y.card : ℝ) := by
    have hXle : (X.card : ℝ) ≤ (X0.card : ℝ) := by
      exact_mod_cast hX_card ▸ Finset.card_le_card hXs_sub
    rw [hz_def]
    have h1 : (X.card : ℝ) * (Y.card : ℝ) / ((X0.card : ℝ) * (Y0.card : ℝ)) * (Y0.card : ℝ) =
        ((X.card : ℝ) / (X0.card : ℝ)) * (Y.card : ℝ) := by
      rw [mul_div_mul_comm, mul_assoc, div_mul_cancel₀ _ hY0pos.ne']
    rw [h1]
    have hdiv : (X.card : ℝ) / (X0.card : ℝ) ≤ 1 := (div_le_one hX0pos).mpr hXle
    calc ((X.card : ℝ) / (X0.card : ℝ)) * (Y.card : ℝ) ≤ 1 * (Y.card : ℝ) :=
          mul_le_mul_of_nonneg_right hdiv hYpos.le
      _ = (Y.card : ℝ) := one_mul _
  have hF0_le_Q : F0 ≤ ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) := by
    have hFmax_le : score (Xs, Ys, Es, dX, dY) ≤ ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) := by
      rw [hscore_eq]
      have h2000_ge1 : (1 : ℝ) ≤ (2000 : ℝ) ^ r := one_le_pow₀ (by norm_num)
      have hρ2 : ρ ^ (5 / 2 : ℝ) ≤ ρ ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hρpos hρle1 (by norm_num)
      rw [Real.rpow_two] at hρ2
      have hz1 : z ^ (1 / 20 : ℝ) ≤ 1 := Real.rpow_le_one hzpos.le hzle1 (by norm_num)
      have h1 : ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) * z ^ (1 / 20 : ℝ) ≤
          ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) := by
        have hstep1 : ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤
            ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) := by
          have hnn : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) :=
            mul_nonneg (mul_nonneg hXpos.le hYpos.le) (div_nonneg (sq_nonneg _) (mul_nonneg hApos.le hBpos.le))
          have hm := mul_le_mul_of_nonneg_right hρ2 hnn
          linarith
        have hrhs_nn : 0 ≤ ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) :=
          mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hXpos.le) hYpos.le)
            (div_nonneg (sq_nonneg _) (mul_nonneg hApos.le hBpos.le))
        calc ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) * z ^ (1 / 20 : ℝ)
            ≤ (ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B))) * 1 :=
              mul_le_mul hstep1 hz1 (Real.rpow_nonneg hzpos.le _) hrhs_nn
          _ = ρ ^ 2 * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) := mul_one _
      have hnum_nn : 0 ≤ ρ ^ (5 / 2 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) * z ^ (1 / 20 : ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hρpos.le _) hXpos.le) hYpos.le)
          (div_nonneg (sq_nonneg _) (mul_nonneg hApos.le hBpos.le))) (Real.rpow_nonneg hzpos.le _)
      exact (div_le_self hnum_nn h2000_ge1).trans h1
    exact hF0_le_max.trans hFmax_le
  exact mp_extract_box_of_local hApos hBpos hDpos hF0pos hK0pos hCQ_pos hp0_tail
    hXne hYne hEne hEsub hXbd hYbd hEbd (by omega : 0 < dY) hYs_sub hdY_dvd rfl
    hρ_def hρpos hY_ratio hρ_lb hz_lb hF0_le_Q hlocal

end MPExtraction

section MPLinearTypeI

private lemma schur_exp_bound {J : ℕ} (f g : ℕ → ℝ) (_hf : ∀ j, 0 ≤ f j) (_hg : ∀ j, 0 ≤ g j)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs * g j * f k ≤
      (1 + 2 * r / (1 - r)) *
        Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2) * Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2) := by
  let B0 : ℝ := 1 + 2 * r / (1 - r)
  have hrow : ∀ j ∈ Finset.range J, ∑ k ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs ≤ B0 := by
    intro j _
    let M : Finset ℤ := (Finset.range J).image (fun k : ℕ => (j : ℤ) - (k : ℤ))
    have hinj : Set.InjOn (fun k : ℕ => (j : ℤ) - (k : ℤ)) (Finset.range J : Set ℕ) := by
      intro k1 _ k2 _ h; dsimp only at h; omega
    have hsum : ∑ k ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs = ∑ m ∈ M, r ^ m.natAbs :=
      (Finset.sum_image (f := fun m : ℤ => r ^ m.natAbs) (fun k1 hk1 k2 hk2 h => hinj hk1 hk2 h)).symm
    rw [hsum]
    exact sum_natAbs_pow_le hr0 hr1
  have hcol : ∀ k ∈ Finset.range J, ∑ j ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs ≤ B0 := by
    intro k _
    let M : Finset ℤ := (Finset.range J).image (fun j : ℕ => (j : ℤ) - (k : ℤ))
    have hinj : Set.InjOn (fun j : ℕ => (j : ℤ) - (k : ℤ)) (Finset.range J : Set ℕ) := by
      intro j1 _ j2 _ h; dsimp only at h; omega
    have hsum : ∑ j ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs = ∑ m ∈ M, r ^ m.natAbs :=
      (Finset.sum_image (f := fun m : ℤ => r ^ m.natAbs) (fun j1 hj1 j2 hj2 h => hinj hj1 hj2 h)).symm
    rw [hsum]
    exact sum_natAbs_pow_le hr0 hr1
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range J ×ˢ Finset.range J)
    (fun p => Real.sqrt (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs) * g p.1)
    (fun p => Real.sqrt (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs) * f p.2)
  have hlhs : ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs * g j * f k =
      ∑ p ∈ Finset.range J ×ˢ Finset.range J,
        (Real.sqrt (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs) * g p.1) *
        (Real.sqrt (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs) * f p.2) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hsq : Real.sqrt (r ^ ((j : ℤ) - (k : ℤ)).natAbs) * Real.sqrt (r ^ ((j : ℤ) - (k : ℤ)).natAbs) =
        r ^ ((j : ℤ) - (k : ℤ)).natAbs := Real.mul_self_sqrt (pow_nonneg hr0 _)
    calc r ^ ((j : ℤ) - (k : ℤ)).natAbs * g j * f k
        = (Real.sqrt (r ^ ((j : ℤ) - (k : ℤ)).natAbs) * Real.sqrt (r ^ ((j : ℤ) - (k : ℤ)).natAbs)) *
          g j * f k := by rw [hsq]
      _ = _ := by ring
  have h1 : ∑ p ∈ Finset.range J ×ˢ Finset.range J,
      (Real.sqrt (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs) * g p.1) ^ 2 ≤
      B0 * ∑ j ∈ Finset.range J, g j ^ 2 := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have heq : ∑ k ∈ Finset.range J, (Real.sqrt (r ^ ((j : ℤ) - (k : ℤ)).natAbs) * g j) ^ 2 =
        (∑ k ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs) * g j ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, Real.sq_sqrt (pow_nonneg hr0 _)]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hrow j hj) (sq_nonneg _)
  have h2 : ∑ p ∈ Finset.range J ×ˢ Finset.range J,
      (Real.sqrt (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs) * f p.2) ^ 2 ≤
      B0 * ∑ k ∈ Finset.range J, f k ^ 2 := by
    rw [Finset.sum_product_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have heq : ∑ j ∈ Finset.range J, (Real.sqrt (r ^ ((j : ℤ) - (k : ℤ)).natAbs) * f k) ^ 2 =
        (∑ j ∈ Finset.range J, r ^ ((j : ℤ) - (k : ℤ)).natAbs) * f k ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (pow_nonneg hr0 _)]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hcol k hk) (sq_nonneg _)
  have hB0_nn : 0 ≤ B0 := by dsimp only [B0]; have : 0 < 1 - r := sub_pos.mpr hr1; positivity
  rw [hlhs]
  calc _ ≤ Real.sqrt (B0 * ∑ j ∈ Finset.range J, g j ^ 2) *
          Real.sqrt (B0 * ∑ k ∈ Finset.range J, f k ^ 2) :=
        hcs.trans (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (Real.sqrt B0 * Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2)) *
          (Real.sqrt B0 * Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2)) := by
        rw [Real.sqrt_mul hB0_nn, Real.sqrt_mul hB0_nn]
    _ = (Real.sqrt B0 * Real.sqrt B0) *
          Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2) * Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2) := by ring
    _ = B0 * Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2) * Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2) := by
        rw [Real.mul_self_sqrt hB0_nn]

private lemma dyadic_block_gcd_bound
    {K0 C : ℝ} (hK0pos : 0 < K0) (hCpos : 0 < C)
    (hGCD : ∀ (A B D : ℝ), 0 < A → 0 < B → 0 < D →
      ∀ (X Y : Finset ℕ) (E : Finset (ℕ × ℕ)),
        X.Nonempty → Y.Nonempty → E.Nonempty → E ⊆ X ×ˢ Y →
        (∀ x ∈ X, 0 < x ∧ A ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A) →
        (∀ y ∈ Y, 0 < y ∧ B ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * B) →
        (∀ e ∈ E, D ≤ (Nat.gcd e.1 e.2 : ℝ)) →
        let ρ : ℝ := (E.card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))
        ρ ^ (9 / 4 : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (D ^ 2 / (A * B)) ≤ K0)
    {V : Finset ℕ} (hVpos : ∀ v ∈ V, 0 < v) (hn_pos : (0 : ℝ) < (V.card : ℝ))
    (j k : ℕ) :
    let Vj := V.filter (fun v => 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))
    let Vk := V.filter (fun v => 2 ^ k ≤ v ∧ v < 2 ^ (k + 1))
    let Eall := V.offDiag.filter (fun p => (max p.1 p.2 : ℝ) ≤ C * (V.card : ℝ) * (Nat.gcd p.1 p.2 : ℝ))
    let Ejk := Eall.filter (fun e => e.1 ∈ Vj ∧ e.2 ∈ Vk)
    ((Ejk.card : ℝ) ≤ (4 * K0 * C ^ 2) ^ (4 / 9 : ℝ) * (V.card : ℝ) ^ 2 *
      ((2 : ℝ) ^ (-(4 / 9 : ℝ))) ^ ((j : ℤ) - (k : ℤ)).natAbs *
      ((Vj.card : ℝ) / (V.card : ℝ)) ^ (5 / 9 : ℝ) * ((Vk.card : ℝ) / (V.card : ℝ)) ^ (5 / 9 : ℝ)) := by
  classical
  intro Vj Vk Eall Ejk
  let n : ℕ := V.card
  let aj : ℝ := (Vj.card : ℝ) / (n : ℝ)
  let ak : ℝ := (Vk.card : ℝ) / (n : ℝ)
  let r : ℝ := (2 : ℝ) ^ (-(4 / 9 : ℝ))
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  by_cases hEne : Ejk.Nonempty
  · have hXne : Vj.Nonempty := by obtain ⟨e, he⟩ := hEne; exact ⟨e.1, (Finset.mem_filter.mp he).2.1⟩
    have hYne : Vk.Nonempty := by obtain ⟨e, he⟩ := hEne; exact ⟨e.2, (Finset.mem_filter.mp he).2.2⟩
    let Aj : ℝ := (2 : ℝ) ^ j
    let Bk : ℝ := (2 : ℝ) ^ k
    let Djk : ℝ := max Aj Bk / (2 * C * (n : ℝ))
    have hAj : 0 < Aj := by dsimp only [Aj]; positivity
    have hBk : 0 < Bk := by dsimp only [Bk]; positivity
    have hDjk : 0 < Djk := div_pos (lt_of_lt_of_le hAj (le_max_left _ _)) (by positivity)
    have hXbd : ∀ u ∈ Vj, 0 < u ∧ Aj ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * Aj := fun u hu => by
      have hu' := Finset.mem_filter.mp hu
      refine ⟨hVpos u hu'.1, by dsimp only [Aj]; exact_mod_cast hu'.2.1, ?_⟩
      have hlt : (u : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast hu'.2.2
      rw [pow_succ, mul_comm] at hlt; exact hlt.le
    have hYbd : ∀ v ∈ Vk, 0 < v ∧ Bk ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * Bk := fun v hv => by
      have hv' := Finset.mem_filter.mp hv
      refine ⟨hVpos v hv'.1, by dsimp only [Bk]; exact_mod_cast hv'.2.1, ?_⟩
      have hlt : (v : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hv'.2.2
      rw [pow_succ, mul_comm] at hlt; exact hlt.le
    have hEbd : ∀ e ∈ Ejk, Djk ≤ (Nat.gcd e.1 e.2 : ℝ) := fun e he => by
      have he' := Finset.mem_filter.mp he
      have he_all := (Finset.mem_filter.mp he'.1).2
      have hmax_le : max Aj Bk ≤ max (e.1 : ℝ) (e.2 : ℝ) :=
        max_le_max (hXbd e.1 he'.2.1).2.1 (hYbd e.2 he'.2.2).2.1
      dsimp only [Djk]
      rw [div_le_iff₀ (by positivity)]
      have h1 : max Aj Bk ≤ C * (n : ℝ) * (Nat.gcd e.1 e.2 : ℝ) := hmax_le.trans he_all
      have hnn : 0 ≤ C * (n : ℝ) * (Nat.gcd e.1 e.2 : ℝ) := by positivity
      linarith
    have hgcd := hGCD Aj Bk Djk hAj hBk hDjk Vj Vk Ejk hXne hYne hEne
      (fun e he => Finset.mem_product.mpr (Finset.mem_filter.mp he).2) hXbd hYbd hEbd
    dsimp only at hgcd
    have hratio_jk : Djk ^ 2 / (Aj * Bk) = (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs / (4 * C ^ 2 * (n : ℝ) ^ 2) := by
      dsimp only [Djk, Aj, Bk]
      have hmax_sq : (max ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)) ^ 2 / ((2 : ℝ) ^ j * (2 : ℝ) ^ k) =
          (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs := by
        rcases le_total j k with hjk | hkj
        · have hle : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hjk
          rw [max_eq_right hle]
          have hexp : j + ((j : ℤ) - (k : ℤ)).natAbs = k := by omega
          have hpow : (2 : ℝ) ^ j * (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs = (2 : ℝ) ^ k := by
            rw [← pow_add, hexp]
          rw [div_eq_iff (by positivity)]
          calc ((2 : ℝ) ^ k) ^ 2 = (2 : ℝ) ^ k * (2 : ℝ) ^ k := sq _
            _ = ((2 : ℝ) ^ j * (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs) * (2 : ℝ) ^ k := by rw [hpow]
            _ = (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs * ((2 : ℝ) ^ j * (2 : ℝ) ^ k) := by ring
        · have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hkj
          rw [max_eq_left hle]
          have hexp : k + ((j : ℤ) - (k : ℤ)).natAbs = j := by omega
          have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs = (2 : ℝ) ^ j := by
            rw [← pow_add, hexp]
          rw [div_eq_iff (by positivity)]
          calc ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ j * (2 : ℝ) ^ j := sq _
            _ = (2 : ℝ) ^ j * ((2 : ℝ) ^ k * (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs) := by rw [hpow]
            _ = (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs * ((2 : ℝ) ^ j * (2 : ℝ) ^ k) := by ring
      calc (max ((2 : ℝ) ^ j) ((2 : ℝ) ^ k) / (2 * C * (n : ℝ))) ^ 2 / ((2 : ℝ) ^ j * (2 : ℝ) ^ k)
          = ((max ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)) ^ 2 / ((2 : ℝ) ^ j * (2 : ℝ) ^ k)) / (4 * C ^ 2 * (n : ℝ) ^ 2) := by
            field_simp [hCpos.ne', hn_pos.ne']; ring
        _ = (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs / (4 * C ^ 2 * (n : ℝ) ^ 2) := by rw [hmax_sq]
    rw [hratio_jk] at hgcd
    have haj_pos : 0 < aj := div_pos (by exact_mod_cast hXne.card_pos) hn_pos
    have hak_pos : 0 < ak := div_pos (by exact_mod_cast hYne.card_pos) hn_pos
    have he_pos : 0 < (Ejk.card : ℝ) / (n : ℝ) ^ 2 := div_pos (by exact_mod_cast hEne.card_pos) (pow_pos hn_pos 2)
    have hVj_eq_a : (Vj.card : ℝ) = aj * (n : ℝ) := by dsimp only [aj]; exact (div_mul_cancel₀ _ hn_pos.ne').symm
    have hVk_eq_a : (Vk.card : ℝ) = ak * (n : ℝ) := by dsimp only [ak]; exact (div_mul_cancel₀ _ hn_pos.ne').symm
    have hpow94 : ((Ejk.card : ℝ) / (n : ℝ) ^ 2) ^ (9 / 4 : ℝ) ≤
        (4 * K0 * C ^ 2) * ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs)⁻¹ * (aj * ak) ^ (5 / 4 : ℝ) := by
      have hrew : (Ejk.card : ℝ) / ((Vj.card : ℝ) * (Vk.card : ℝ)) =
          ((Ejk.card : ℝ) / (n : ℝ) ^ 2) / (aj * ak) := by
        rw [hVj_eq_a, hVk_eq_a]; field_simp [hn_pos.ne', haj_pos.ne', hak_pos.ne']
      rw [hrew, Real.div_rpow he_pos.le (mul_pos haj_pos hak_pos).le, hVj_eq_a, hVk_eq_a] at hgcd
      have hcomb : (aj * ak) / (aj * ak) ^ (9 / 4 : ℝ) = ((aj * ak) ^ (5 / 4 : ℝ))⁻¹ := by
        rw [← Real.rpow_neg (mul_pos haj_pos hak_pos).le]
        calc (aj * ak) / (aj * ak) ^ (9 / 4 : ℝ)
            = (aj * ak) ^ (1 : ℝ) / (aj * ak) ^ (9 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = (aj * ak) ^ ((1 : ℝ) - 9 / 4) := (Real.rpow_sub (mul_pos haj_pos hak_pos) _ _).symm
          _ = (aj * ak) ^ (-(5 / 4 : ℝ)) := by norm_num
      have hlhs_eq : ((Ejk.card : ℝ) / (n : ℝ) ^ 2) ^ (9 / 4 : ℝ) / (aj * ak) ^ (9 / 4 : ℝ) *
          (aj * (n : ℝ)) * (ak * (n : ℝ)) *
          ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs / (4 * C ^ 2 * (n : ℝ) ^ 2)) =
          (((Ejk.card : ℝ) / (n : ℝ) ^ 2) ^ (9 / 4 : ℝ) *
            (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs) /
            ((aj * ak) ^ (5 / 4 : ℝ) * (4 * C ^ 2)) := by
        have h1 : ((Ejk.card : ℝ) / (n : ℝ) ^ 2) ^ (9 / 4 : ℝ) / (aj * ak) ^ (9 / 4 : ℝ) *
            (aj * (n : ℝ)) * (ak * (n : ℝ)) *
            ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs / (4 * C ^ 2 * (n : ℝ) ^ 2)) =
            ((Ejk.card : ℝ) / (n : ℝ) ^ 2) ^ (9 / 4 : ℝ) *
            ((aj * ak) / (aj * ak) ^ (9 / 4 : ℝ)) *
            ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs / (4 * C ^ 2)) := by
          have hn2 : (n : ℝ) ^ 2 ≠ 0 := (pow_pos hn_pos 2).ne'
          calc _ = ((Ejk.card : ℝ) / (n : ℝ) ^ 2) ^ (9 / 4 : ℝ) *
                ((aj * ak) / (aj * ak) ^ (9 / 4 : ℝ)) *
                ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs / (4 * C ^ 2)) *
                ((n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
            _ = _ := by rw [div_self hn2, mul_one]
        rw [h1, hcomb]; ring
      have hden_pos : 0 < (aj * ak) ^ (5 / 4 : ℝ) * (4 * C ^ 2) :=
        mul_pos (Real.rpow_pos_of_pos (mul_pos haj_pos hak_pos) _) (mul_pos (by norm_num) (pow_pos hCpos 2))
      rw [hlhs_eq, div_le_iff₀ hden_pos] at hgcd
      rw [show (4 * K0 * C ^ 2) * ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs)⁻¹ * (aj * ak) ^ (5 / 4 : ℝ) =
          (K0 * ((aj * ak) ^ (5 / 4 : ℝ) * (4 * C ^ 2))) / (2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs by ring]
      exact (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr hgcd
    have h49 := Real.rpow_le_rpow (Real.rpow_nonneg he_pos.le _) hpow94 (by norm_num : (0 : ℝ) ≤ 4 / 9)
    have h4KC_nn : 0 ≤ 4 * K0 * C ^ 2 := by positivity
    have h2inv_nn : 0 ≤ ((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs)⁻¹ := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
    have hajak_nn : 0 ≤ (aj * ak) ^ (5 / 4 : ℝ) := Real.rpow_nonneg (mul_pos haj_pos hak_pos).le _
    rw [← Real.rpow_mul he_pos.le, show (9 / 4 : ℝ) * (4 / 9) = 1 by norm_num, Real.rpow_one,
        Real.mul_rpow (mul_nonneg h4KC_nn h2inv_nn) hajak_nn,
        Real.mul_rpow h4KC_nn h2inv_nn] at h49
    have hr_pow : (((2 : ℝ) ^ ((j : ℤ) - (k : ℤ)).natAbs)⁻¹) ^ (4 / 9 : ℝ) =
        r ^ ((j : ℤ) - (k : ℤ)).natAbs := by
      dsimp only [r]
      rw [Real.inv_rpow (pow_nonneg (by norm_num) _), ← Real.rpow_neg (pow_nonneg (by norm_num) _),
          ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    have ha_pow : ((aj * ak) ^ (5 / 4 : ℝ)) ^ (4 / 9 : ℝ) = aj ^ (5 / 9 : ℝ) * ak ^ (5 / 9 : ℝ) := by
      rw [← Real.rpow_mul (mul_pos haj_pos hak_pos).le, show (5 / 4 : ℝ) * (4 / 9) = 5 / 9 by norm_num,
          Real.mul_rpow haj_pos.le hak_pos.le]
    rw [hr_pow, ha_pow] at h49
    rw [div_le_iff₀ (pow_pos hn_pos 2)] at h49
    dsimp only [aj, ak, r, n] at h49 ⊢
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hEne, Finset.card_empty, Nat.cast_zero]
    have h1 : 0 ≤ (4 * K0 * C ^ 2) ^ (4 / 9 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (V.card : ℝ) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ ((2 : ℝ) ^ (-(4 / 9 : ℝ))) ^ ((j : ℤ) - (k : ℤ)).natAbs := pow_nonneg hr0.le _
    have h4 : 0 ≤ ((Vj.card : ℝ) / (V.card : ℝ)) ^ (5 / 9 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h5 : 0 ≤ ((Vk.card : ℝ) / (V.card : ℝ)) ^ (5 / 9 : ℝ) := Real.rpow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5

set_option maxHeartbeats 1200000 in
/-- Hu-Jing Theorem 7.2: Many pairs with bounded reduced ratio force linear Type I loss. -/
theorem hu_jing_typeILoss :
    ∀ (C : ℝ), 1 ≤ C → ∀ (ε : ℝ), 0 < ε → ∃ κ > 0,
      ∀ (V : Finset ℕ), 2 ≤ V.card → (∀ v ∈ V, 0 < v) →
        ε * (V.card : ℝ) ^ 2 ≤
          ((V.offDiag.filter (fun p => p.1 < p.2 ∧
            (max p.1 p.2 : ℝ) ≤ C * (V.card : ℝ) * (Nat.gcd p.1 p.2 : ℝ))).card : ℝ) →
        κ ≤ typeILoss V (1 / (2 * (V.card : ℝ))) := by
  classical
  -- Obtain concentration, GCD bound, and rational box extraction constants once!
  have hConc : ∀ {Q : ℝ}, 2 < Q → Q < 3 → ∃ C_Q > 0,
      ∀ (S : Finset ℤ) (α β : ℤ → ℝ) (μ : ℤ × ℤ → ℝ),
        (∀ i ∈ S, 0 ≤ α i) → (∀ j ∈ S, 0 ≤ β j) →
        (∑ i ∈ S, α i = 1) → (∑ j ∈ S, β j = 1) →
        (∀ p ∈ S ×ˢ S, 0 ≤ μ p) → (∑ p ∈ S ×ˢ S, μ p = 1) →
        ∀ {c lam : ℝ}, 0 < c → c ≤ 1 → 0 < lam → lam ≤ 4 / 5 →
        (∀ i ∈ S, ∀ j ∈ S, μ (i, j) ≤ c * lam ^ (i - j).natAbs * (α i * β j) ^ (1 - 1 / Q)) →
        (1 / 9 : ℝ) ≤ c ∧
        ∃ k ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun p => 2 ≤ (p.1 - k).natAbs + (p.2 - k).natAbs), μ p ≤
          C_Q * lam ^ (2 * Q - 2) := fun {Q} hQ2 hQ3 =>
    ⟨gwConst Q, gwConst_pos hQ2, fun S α β μ hα0 hβ0 hα1 hβ1 hμ0 hμ1 {_ _} hc0 hc1 hlam0 hlam1 hμ =>
      gw_concentration hQ2 hQ3 S α β μ hα0 hβ0 hα1 hβ1 hμ0 hμ1 hc0 hc1 hlam0 hlam1 hμ⟩
  obtain ⟨K0, hK0_ge, hGCD⟩ := gw_gcd_9_4 hConc
  obtain ⟨p0, _hp0_ge2, hExtract⟩ := mp_extraction hConc hK0_ge hGCD
  intro C hC ε hε
  have hCpos : 0 < C := by linarith
  have hK0pos : 0 < K0 := by linarith
  let r : ℝ := (2 : ℝ) ^ (-(4 / 9 : ℝ))
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  let B0 : ℝ := 1 + 2 * r / (1 - r)
  have hB0pos : 0 < B0 := by dsimp only [B0]; have : 0 < 1 - r := sub_pos.mpr hr1; positivity
  let LC : ℝ := (4 * K0 * C ^ 2) ^ (4 / 9 : ℝ)
  have hLCpos : 0 < LC := by dsimp only [LC]; positivity
  let η : ℝ := min (1 / 2) ((ε / (2 * LC * B0)) ^ (18 : ℕ))
  have hηpos : 0 < η := lt_min (by norm_num) (pow_pos (div_pos hε (by positivity)) 18)
  have hη_bound : 2 * LC * B0 * η ^ (1 / 18 : ℝ) ≤ ε := by
    have h1 : η ≤ (ε / (2 * LC * B0)) ^ (18 : ℕ) := min_le_right _ _
    have h2 : η ^ (1 / 18 : ℝ) ≤ ((ε / (2 * LC * B0)) ^ (18 : ℕ)) ^ (1 / 18 : ℝ) :=
      Real.rpow_le_rpow hηpos.le h1 (by norm_num)
    have h3 : ((ε / (2 * LC * B0)) ^ (18 : ℕ)) ^ (1 / 18 : ℝ) = ε / (2 * LC * B0) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hε (by positivity)).le]; norm_num
    rw [h3] at h2
    calc 2 * LC * B0 * η ^ (1 / 18 : ℝ)
        ≤ 2 * LC * B0 * (ε / (2 * LC * B0)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε := by field_simp [hLCpos.ne', hB0pos.ne']
  let f' : ℝ := (ε * η ^ 2) ^ (5 / 2 : ℝ) * η ^ 2 / (4 * C ^ 2 * (2000 : ℝ) ^ (p0 + 1))
  have hf'pos : 0 < f' := by dsimp only [f']; positivity
  let θ : ℝ := (η / 4) * (f' / K0) ^ (24 : ℕ)
  have hθpos : 0 < θ := by dsimp only [θ]; positivity
  let C' : ℝ := max 1 (512 / f')
  have hC'ge : 1 ≤ C' := le_max_left _ _
  obtain ⟨κ_box, hκ_box_pos, hBox⟩ := dense_rational_box hC'ge
  let n0 : ℕ := max 2 (Nat.ceil (2 / θ))
  have hn0_pos : (0 : ℝ) < (n0 : ℝ) := by exact_mod_cast (by omega : 0 < n0)
  let κ : ℝ := min (θ * κ_box) (1 / (C * (n0 : ℝ) ^ 2))
  have hκpos : 0 < κ := lt_min (mul_pos hθpos hκ_box_pos) (by positivity)
  refine ⟨κ, hκpos, ?_⟩
  intro V hVcard hVpos hPairs
  let n : ℕ := V.card
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- Case 1: Small n < n0 — use a single pair from hPairs
  by_cases hn_small : n < n0
  · let Unord := V.offDiag.filter (fun p => p.1 < p.2 ∧
      (max p.1 p.2 : ℝ) ≤ C * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ))
    have hUnord_ne : Unord.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < (Unord.card : ℝ) := lt_of_lt_of_le (by positivity) hPairs
      exact_mod_cast this
    obtain ⟨p, hp⟩ := hUnord_ne
    have hp' := Finset.mem_filter.mp hp
    have hp_od := Finset.mem_offDiag.mp hp'.1
    have hmax : (max p.1 p.2 : ℝ) = (p.2 : ℝ) := by
      have : p.1 ≤ p.2 := hp'.2.1.le
      rw [max_eq_right (by exact_mod_cast this)]
    have hp2_le : (p.2 : ℝ) ≤ C * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ) := hmax ▸ hp'.2.2
    let M : Finset (ℕ × ℕ) := {p}
    have hmatch := typeILoss_ge_of_matching hVpos (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ))) M
      (fun q hq => by
        rw [Finset.mem_singleton.mp hq]
        exact ⟨hp_od.1, hp_od.2.1, hp'.2.1⟩)
      (fun q1 hq1 q2 hq2 _ => by
        rw [Finset.mem_coe, Finset.mem_singleton] at hq1 hq2
        exact hq1.trans hq2.symm)
    rw [Finset.sum_singleton] at hmatch
    have hlow : 1 / (C * (n0 : ℝ) ^ 2) ≤ 2 * (1 / (2 * (n : ℝ))) * ((Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)) := by
      have hp2pos : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hVpos p.2 hp_od.2.1
      have hCn_pos : 0 < C * (n : ℝ) := mul_pos hCpos hn_pos
      have hfrac : 1 / (C * (n : ℝ)) ≤ (Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ) := by
        rw [div_le_div_iff₀ hCn_pos hp2pos]; linarith
      have hn0ge : (n : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hn_small.le
      have hCn2_pos : 0 < C * (n : ℝ) ^ 2 := mul_pos hCpos (pow_pos hn_pos 2)
      calc 1 / (C * (n0 : ℝ) ^ 2)
          ≤ 1 / (C * (n : ℝ) ^ 2) := by
            refine one_div_le_one_div_of_le hCn2_pos ?_
            have : (n : ℝ) ^ 2 ≤ (n0 : ℝ) ^ 2 := by nlinarith
            nlinarith
        _ = (1 / (n : ℝ)) * (1 / (C * (n : ℝ))) := by field_simp [hn_pos.ne', hCpos.ne']
        _ ≤ (1 / (n : ℝ)) * ((Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hfrac (one_div_nonneg.mpr hn_pos.le)
        _ = 2 * (1 / (2 * (n : ℝ))) * ((Nat.gcd p.1 p.2 : ℝ) / (p.2 : ℝ)) := by
            rw [show 2 * (1 / (2 * (n : ℝ))) = 1 / (n : ℝ) by field_simp [hn_pos.ne']]
    exact (min_le_right _ _).trans (hlow.trans hmatch)
  -- Case 2: Large n ≥ n0
  push Not at hn_small
  let Eall := V.offDiag.filter (fun p => (max p.1 p.2 : ℝ) ≤ C * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ))
  have hEall_card : 2 * ε * (n : ℝ) ^ 2 ≤ (Eall.card : ℝ) := by
    let Elt := V.offDiag.filter (fun p => p.1 < p.2 ∧
      (max p.1 p.2 : ℝ) ≤ C * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ))
    let Egt := Elt.image Prod.swap
    have hdisj_lt_gt : Disjoint Elt Egt := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (Finset.mem_filter.mp hp1).2.1
      obtain ⟨q, hq, hswap⟩ := Finset.mem_image.mp hp2
      have h2 := (Finset.mem_filter.mp hq).2.1
      have hp1_eq : p.1 = q.2 := congrArg Prod.fst hswap.symm
      have hp2_eq : p.2 = q.1 := congrArg Prod.snd hswap.symm
      omega
    have hsub : Elt ∪ Egt ⊆ Eall := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp1 | hp2
      · have h1 := Finset.mem_filter.mp hp1
        exact Finset.mem_filter.mpr ⟨h1.1, h1.2.2⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp2
        have hq' := Finset.mem_filter.mp hq
        have hqod := Finset.mem_offDiag.mp hq'.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hqod.2.1, hqod.1, hqod.2.2.symm⟩, ?_⟩
        simpa only [Prod.swap, max_comm, Nat.gcd_comm] using hq'.2.2
    have hcard_gt : Egt.card = Elt.card :=
      Finset.card_image_of_injOn fun _ _ _ _ h => Prod.swap_injective h
    have hleN : 2 * Elt.card ≤ Eall.card := by
      have h := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj_lt_gt, hcard_gt] at h
      omega
    have hleR : 2 * (Elt.card : ℝ) ≤ (Eall.card : ℝ) := by exact_mod_cast hleN
    linarith
  -- Dyadic partition of V
  let J : ℕ := Nat.log 2 (V.sup id) + 1
  let Vj : ℕ → Finset ℕ := fun j => V.filter (fun v => 2 ^ j ≤ v ∧ v < 2 ^ (j + 1))
  let a : ℕ → ℝ := fun j => ((Vj j).card : ℝ) / (n : ℝ)
  let Ejk : ℕ → ℕ → Finset (ℕ × ℕ) := fun j k => Eall.filter (fun e => e.1 ∈ Vj j ∧ e.2 ∈ Vj k)
  have hV_maps : ∀ v ∈ V, Nat.log 2 v ∈ Finset.range J := fun v hv => by
    rw [Finset.mem_range]
    have hle : v ≤ V.sup id := Finset.le_sup (f := id) hv
    have := Nat.log_mono_right (b := 2) hle
    omega
  have hVj_eq : ∀ j ∈ Finset.range J, Vj j = V.filter (fun v => Nat.log 2 v = j) := by
    intro j _
    ext v
    simp only [Vj, Finset.mem_filter]
    refine and_congr_right fun hv => ?_
    have hvpos := hVpos v hv
    constructor
    · rintro ⟨h1, h2⟩
      have hge : j ≤ Nat.log 2 v := (Nat.le_log_iff_pow_le (by norm_num) hvpos.ne').mpr h1
      have hlt : Nat.log 2 v < j + 1 := (Nat.log_lt_iff_lt_pow (by norm_num) hvpos.ne').mpr h2
      omega
    · intro heq; subst heq
      exact ⟨Nat.pow_log_le_self 2 hvpos.ne', Nat.lt_pow_succ_log_self (by norm_num) v⟩
  have hsum_a : ∑ j ∈ Finset.range J, a j = 1 := by
    simp only [a, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hn_pos.ne']
    have hN : ∑ j ∈ Finset.range J, (Vj j).card = V.card := by
      have h1 := (Finset.card_eq_sum_card_fiberwise
        (f := fun v : ℕ => Nat.log 2 v) (s := V) (t := Finset.range J) (fun v hv => hV_maps v hv)).symm
      rw [← h1]
      exact Finset.sum_congr rfl fun j hj => by rw [hVj_eq j hj]
    exact_mod_cast hN
  have ha0 : ∀ j, 0 ≤ a j := fun j => by positivity
  have ha1 : ∀ j ∈ Finset.range J, a j ≤ 1 := fun j _ => by
    dsimp only [a]; rw [div_le_one hn_pos]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ V)
  have hsum_Eall : (Eall.card : ℝ) = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ((Ejk j k).card : ℝ) := by
    have hE_maps : ∀ e ∈ Eall, (Nat.log 2 e.1, Nat.log 2 e.2) ∈ Finset.range J ×ˢ Finset.range J := fun e he => by
      have hod := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
      exact Finset.mem_product.mpr ⟨hV_maps e.1 hod.1, hV_maps e.2 hod.2.1⟩
    have hN0 : Eall.card = ∑ p ∈ Finset.range J ×ˢ Finset.range J, (Ejk p.1 p.2).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun e : ℕ × ℕ => (Nat.log 2 e.1, Nat.log 2 e.2))
        (s := Eall) (t := Finset.range J ×ˢ Finset.range J) (fun e he => hE_maps e he)]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.mem_product.mp hp
      congr 1; ext e
      simp only [Ejk, Finset.mem_filter, Prod.ext_iff, hVj_eq p.1 hp'.1, hVj_eq p.2 hp'.2]
      constructor
      · rintro ⟨he, h1, h2⟩
        have hod := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
        exact ⟨he, ⟨hod.1, h1⟩, ⟨hod.2.1, h2⟩⟩
      · rintro ⟨he, ⟨_, h1⟩, ⟨_, h2⟩⟩
        exact ⟨he, h1, h2⟩
    have hN : Eall.card = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, (Ejk j k).card := by
      simpa [Finset.sum_product] using hN0
    exact_mod_cast hN
  -- Green-Walker bound on each pair of dyadic blocks (j, k)
  have hEjk_bd : ∀ j ∈ Finset.range J, ∀ k ∈ Finset.range J,
      ((Ejk j k).card : ℝ) ≤ LC * (n : ℝ) ^ 2 * r ^ ((j : ℤ) - (k : ℤ)).natAbs *
        (a j) ^ (5 / 9 : ℝ) * (a k) ^ (5 / 9 : ℝ) := fun j _ k _ =>
    dyadic_block_gcd_bound hK0pos hCpos hGCD hVpos hn_pos j k
  -- Small vs large dyadic blocks via Schur's test!
  let Large := (Finset.range J).filter (fun j => η ≤ a j)
  let f : ℕ → ℝ := fun j => (a j) ^ (5 / 9 : ℝ)
  let g : ℕ → ℝ := fun j => if a j < η then (a j) ^ (5 / 9 : ℝ) else 0
  have hf_nn : ∀ j, 0 ≤ f j := fun j => Real.rpow_nonneg (ha0 j) _
  have hg_nn : ∀ j, 0 ≤ g j := fun j => by dsimp only [g]; split_ifs; exact hf_nn j; exact le_rfl
  have hf_l2 : ∑ j ∈ Finset.range J, f j ^ 2 ≤ 1 := by
    calc ∑ j ∈ Finset.range J, f j ^ 2
        ≤ ∑ j ∈ Finset.range J, a j := by
          refine Finset.sum_le_sum fun j hj => ?_
          dsimp only [f]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (ha0 j), show (5 / 9 : ℝ) * (2 : ℕ) = 10 / 9 by norm_num]
          by_cases h0 : a j = 0
          · rw [h0, Real.zero_rpow (by norm_num)]
          · have hpos : 0 < a j := lt_of_le_of_ne (ha0 j) (Ne.symm h0)
            calc (a j) ^ (10 / 9 : ℝ) ≤ (a j) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_ge hpos (ha1 j hj) (by norm_num)
              _ = a j := Real.rpow_one _
      _ = 1 := hsum_a
  have hg_l2 : ∑ j ∈ Finset.range J, g j ^ 2 ≤ η ^ (1 / 9 : ℝ) := by
    calc ∑ j ∈ Finset.range J, g j ^ 2
        ≤ ∑ j ∈ Finset.range J, η ^ (1 / 9 : ℝ) * a j := by
          refine Finset.sum_le_sum fun j _ => ?_
          dsimp only [g]
          split_ifs with hlt
          · rw [← Real.rpow_natCast, ← Real.rpow_mul (ha0 j),
                show (5 / 9 : ℝ) * (2 : ℕ) = 1 / 9 + 1 by norm_num]
            by_cases h0 : a j = 0
            · rw [h0, Real.zero_rpow (by norm_num), mul_zero]
            · have hpos : 0 < a j := lt_of_le_of_ne (ha0 j) (Ne.symm h0)
              rw [Real.rpow_add hpos, Real.rpow_one]
              exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos.le hlt.le (by norm_num)) hpos.le
          · rw [sq, zero_mul]; exact mul_nonneg (Real.rpow_nonneg hηpos.le _) (ha0 j)
      _ = η ^ (1 / 9 : ℝ) * ∑ j ∈ Finset.range J, a j := (Finset.mul_sum _ _ _).symm
      _ = η ^ (1 / 9 : ℝ) := by rw [hsum_a, mul_one]
  have hschur : ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
      r ^ ((j : ℤ) - (k : ℤ)).natAbs * g j * f k ≤ B0 * η ^ (1 / 18 : ℝ) := by
    have h1 := schur_exp_bound (J := J) f g hf_nn hg_nn hr0.le hr1
    have hsq_g : Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2) ≤ η ^ (1 / 18 : ℝ) := by
      calc Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2)
          ≤ Real.sqrt (η ^ (1 / 9 : ℝ)) := Real.sqrt_le_sqrt hg_l2
        _ = (η ^ (1 / 9 : ℝ)) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        _ = η ^ (1 / 18 : ℝ) := by rw [← Real.rpow_mul hηpos.le]; congr 1; norm_num
    have hsq_f : Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2) ≤ 1 := by
      calc Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hf_l2
        _ = 1 := Real.sqrt_one
    calc _ ≤ B0 * Real.sqrt (∑ j ∈ Finset.range J, g j ^ 2) * Real.sqrt (∑ k ∈ Finset.range J, f k ^ 2) := h1
      _ ≤ B0 * η ^ (1 / 18 : ℝ) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq_g hB0pos.le) hsq_f (Real.sqrt_nonneg _) (by positivity)
      _ = B0 * η ^ (1 / 18 : ℝ) := mul_one _
  -- Bound pairs not in Large ×ˢ Large by ε n²
  have hnot_large : ∑ p ∈ (Finset.range J ×ˢ Finset.range J) \ (Large ×ˢ Large), ((Ejk p.1 p.2).card : ℝ) ≤
      ε * (n : ℝ) ^ 2 := by
    have hpt : ∀ p ∈ (Finset.range J ×ˢ Finset.range J) \ (Large ×ˢ Large),
        ((Ejk p.1 p.2).card : ℝ) ≤
          LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2 +
            r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1) := by
      intro p hp
      have hp' := Finset.mem_sdiff.mp hp
      have hpr := Finset.mem_product.mp hp'.1
      have hbd := hEjk_bd p.1 hpr.1 p.2 hpr.2
      have hnot : ¬ (η ≤ a p.1 ∧ η ≤ a p.2) := fun h =>
        hp'.2 (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpr.1, h.1⟩, Finset.mem_filter.mpr ⟨hpr.2, h.2⟩⟩)
      have hlt : a p.1 < η ∨ a p.2 < η := by by_contra h; push Not at h; exact hnot h
      have hsymm : ((p.2 : ℤ) - (p.1 : ℤ)).natAbs = ((p.1 : ℤ) - (p.2 : ℤ)).natAbs := by
        rw [← Int.natAbs_neg, neg_sub]
      rcases hlt with h1 | h2
      · have hg1 : g p.1 = f p.1 := if_pos h1
        have hnn : 0 ≤ r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1 :=
          mul_nonneg (mul_nonneg (pow_nonneg hr0.le _) (hg_nn p.2)) (hf_nn p.1)
        calc ((Ejk p.1 p.2).card : ℝ)
            ≤ LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * f p.1 * f p.2) := by
              dsimp only [f]; linarith
          _ = LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2) := by rw [hg1]
          _ ≤ LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2 +
                r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1) := by
              refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnn) (by positivity)
      · have hg2 : g p.2 = f p.2 := if_pos h2
        have hnn : 0 ≤ r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2 :=
          mul_nonneg (mul_nonneg (pow_nonneg hr0.le _) (hg_nn p.1)) (hf_nn p.2)
        calc ((Ejk p.1 p.2).card : ℝ)
            ≤ LC * (n : ℝ) ^ 2 * (r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * f p.2 * f p.1) := by
              rw [hsymm]; dsimp only [f]; linarith
          _ = LC * (n : ℝ) ^ 2 * (r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1) := by rw [hg2]
          _ ≤ LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2 +
                r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1) := by
              refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hnn) (by positivity)
    calc ∑ p ∈ (Finset.range J ×ˢ Finset.range J) \ (Large ×ˢ Large), ((Ejk p.1 p.2).card : ℝ)
        ≤ ∑ p ∈ (Finset.range J ×ˢ Finset.range J) \ (Large ×ˢ Large),
            LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2 +
              r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1) := Finset.sum_le_sum hpt
      _ ≤ ∑ p ∈ Finset.range J ×ˢ Finset.range J,
            LC * (n : ℝ) ^ 2 * (r ^ ((p.1 : ℤ) - (p.2 : ℤ)).natAbs * g p.1 * f p.2 +
              r ^ ((p.2 : ℤ) - (p.1 : ℤ)).natAbs * g p.2 * f p.1) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p _ _ =>
            mul_nonneg (by positivity) (add_nonneg
              (mul_nonneg (mul_nonneg (pow_nonneg hr0.le _) (hg_nn p.1)) (hf_nn p.2))
              (mul_nonneg (mul_nonneg (pow_nonneg hr0.le _) (hg_nn p.2)) (hf_nn p.1)))
      _ = LC * (n : ℝ) ^ 2 * ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
              r ^ ((j : ℤ) - (k : ℤ)).natAbs * g j * f k) +
            (∑ k ∈ Finset.range J, ∑ j ∈ Finset.range J,
              r ^ ((k : ℤ) - (j : ℤ)).natAbs * g k * f j)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_product, Finset.sum_product_right]
      _ ≤ LC * (n : ℝ) ^ 2 * (B0 * η ^ (1 / 18 : ℝ) + B0 * η ^ (1 / 18 : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hschur hschur) (by positivity)
      _ = (2 * LC * B0 * η ^ (1 / 18 : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ ε * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hη_bound (sq_nonneg _)
  -- Hence Large ×ˢ Large holds at least ε n² ordered pairs
  have hlarge_sum : ε * (n : ℝ) ^ 2 ≤ ∑ p ∈ Large ×ˢ Large, ((Ejk p.1 p.2).card : ℝ) := by
    have hsub : Large ×ˢ Large ⊆ Finset.range J ×ˢ Finset.range J :=
      Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsplit := Finset.sum_sdiff hsub (f := fun p : ℕ × ℕ => ((Ejk p.1 p.2).card : ℝ))
    have htot : ∑ p ∈ Finset.range J ×ˢ Finset.range J, ((Ejk p.1 p.2).card : ℝ) = (Eall.card : ℝ) := by
      rw [Finset.sum_product]; exact hsum_Eall.symm
    linarith [hEall_card, hnot_large, hsplit, htot]
  have hLarge_ne : (Large ×ˢ Large).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hlarge_sum
    have : (0 : ℝ) < ε * (n : ℝ) ^ 2 := by positivity
    linarith
  have hLarge_card_le : (Large.card : ℝ) ≤ 1 / η := by
    rw [le_div_iff₀ hηpos]
    calc (Large.card : ℝ) * η = ∑ _j ∈ Large, η := by simp
      _ ≤ ∑ j ∈ Large, a j := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.range J, a j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => ha0 j
      _ = 1 := hsum_a
  obtain ⟨⟨j, k⟩, hjk_mem, hjk_max⟩ :=
    Finset.exists_max_image (Large ×ˢ Large) (fun p => ((Ejk p.1 p.2).card : ℝ)) hLarge_ne
  have hjL := (Finset.mem_product.mp hjk_mem).1
  have hkL := (Finset.mem_product.mp hjk_mem).2
  have hj_large : η ≤ a j := (Finset.mem_filter.mp hjL).2
  have hk_large : η ≤ a k := (Finset.mem_filter.mp hkL).2
  have hejk_lb : ε * η ^ 2 * (n : ℝ) ^ 2 ≤ ((Ejk j k).card : ℝ) := by
    have hcard_sq : ((Large ×ˢ Large).card : ℝ) ≤ 1 / η ^ 2 := by
      rw [Finset.card_product, Nat.cast_mul, show (1 : ℝ) / η ^ 2 = (1 / η) * (1 / η) by ring]
      exact mul_le_mul hLarge_card_le hLarge_card_le (Nat.cast_nonneg _) (by positivity)
    have hsum_le : ∑ p ∈ Large ×ˢ Large, ((Ejk p.1 p.2).card : ℝ) ≤
        ((Large ×ˢ Large).card : ℝ) * ((Ejk j k).card : ℝ) := by
      calc _ ≤ ∑ _p ∈ Large ×ˢ Large, ((Ejk j k).card : ℝ) := Finset.sum_le_sum fun p hp => hjk_max p hp
        _ = ((Large ×ˢ Large).card : ℝ) * ((Ejk j k).card : ℝ) := by simp
    have h1 : ε * (n : ℝ) ^ 2 ≤ (1 / η ^ 2) * ((Ejk j k).card : ℝ) :=
      hlarge_sum.trans (hsum_le.trans (mul_le_mul_of_nonneg_right hcard_sq (Nat.cast_nonneg _)))
    rw [one_div, inv_mul_eq_div, le_div_iff₀' (pow_pos hηpos 2)] at h1
    linarith
  -- Apply mp_extraction to (Vj j, Vj k, Ejk j k)!
  have hEne : (Ejk j k).Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < ((Ejk j k).card : ℝ) := lt_of_lt_of_le (by positivity) hejk_lb
    exact_mod_cast this
  have hXne : (Vj j).Nonempty := by obtain ⟨e, he⟩ := hEne; exact ⟨e.1, (Finset.mem_filter.mp he).2.1⟩
  have hYne : (Vj k).Nonempty := by obtain ⟨e, he⟩ := hEne; exact ⟨e.2, (Finset.mem_filter.mp he).2.2⟩
  let Aj : ℝ := (2 : ℝ) ^ j
  let Bk : ℝ := (2 : ℝ) ^ k
  let Djk : ℝ := max Aj Bk / (2 * C * (n : ℝ))
  have hAj : 0 < Aj := by dsimp only [Aj]; positivity
  have hBk : 0 < Bk := by dsimp only [Bk]; positivity
  have hDjk : 0 < Djk := div_pos (lt_of_lt_of_le hAj (le_max_left _ _)) (by positivity)
  have hXbd : ∀ u ∈ Vj j, 0 < u ∧ Aj ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * Aj := fun u hu => by
    have hu' := Finset.mem_filter.mp hu
    refine ⟨hVpos u hu'.1, by dsimp only [Aj]; exact_mod_cast hu'.2.1, ?_⟩
    have hlt : (u : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast hu'.2.2
    rw [pow_succ, mul_comm] at hlt; exact hlt.le
  have hYbd : ∀ v ∈ Vj k, 0 < v ∧ Bk ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * Bk := fun v hv => by
    have hv' := Finset.mem_filter.mp hv
    refine ⟨hVpos v hv'.1, by dsimp only [Bk]; exact_mod_cast hv'.2.1, ?_⟩
    have hlt : (v : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hv'.2.2
    rw [pow_succ, mul_comm] at hlt; exact hlt.le
  have hEbd : ∀ e ∈ Ejk j k, Djk ≤ (Nat.gcd e.1 e.2 : ℝ) := fun e he => by
    have he' := Finset.mem_filter.mp he
    have he_all := (Finset.mem_filter.mp he'.1).2
    have hmax_le : max Aj Bk ≤ max (e.1 : ℝ) (e.2 : ℝ) :=
      max_le_max (hXbd e.1 he'.2.1).2.1 (hYbd e.2 he'.2.2).2.1
    dsimp only [Djk]; rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) hCpos) hn_pos)]
    have h1 : max Aj Bk ≤ C * (n : ℝ) * (Nat.gcd e.1 e.2 : ℝ) := hmax_le.trans he_all
    have hnn : 0 ≤ C * (n : ℝ) * (Nat.gcd e.1 e.2 : ℝ) :=
      mul_nonneg (mul_nonneg hCpos.le hn_pos.le) (Nat.cast_nonneg _)
    linarith
  obtain ⟨U, ξ, AU, BU, hU_sub_Vk, hU_lb_Vk, hξ_pos, hAU_pos, hBU_pos, harea_F0, hU_rep⟩ :=
    hExtract Aj Bk Djk hAj hBk hDjk (Vj j) (Vj k) (Ejk j k) hXne hYne hEne
      (fun e he => Finset.mem_product.mpr (Finset.mem_filter.mp he).2) hXbd hYbd hEbd
  -- Lower bound F0 ≥ f'
  have hVj_lb : η * (n : ℝ) ≤ ((Vj j).card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hj_large hn_pos.le
    dsimp only [a] at this; rwa [div_mul_cancel₀ _ hn_pos.ne'] at this
  have hVk_lb : η * (n : ℝ) ≤ ((Vj k).card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hk_large hn_pos.le
    dsimp only [a] at this; rwa [div_mul_cancel₀ _ hn_pos.ne'] at this
  have hVj_ub : ((Vj j).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ V)
  have hVk_ub : ((Vj k).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ V)
  have hρjk_lb : ε * η ^ 2 ≤ ((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ)) := by
    rw [le_div_iff₀ (mul_pos (by exact_mod_cast hXne.card_pos) (by exact_mod_cast hYne.card_pos))]
    have hmul_ub : ((Vj j).card : ℝ) * ((Vj k).card : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
      mul_le_mul hVj_ub hVk_ub (Nat.cast_nonneg _) hn_pos.le
    calc ε * η ^ 2 * (((Vj j).card : ℝ) * ((Vj k).card : ℝ))
        ≤ ε * η ^ 2 * ((n : ℝ) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hmul_ub (mul_nonneg hε.le (sq_nonneg _))
      _ = ε * η ^ 2 * (n : ℝ) ^ 2 := by ring
      _ ≤ ((Ejk j k).card : ℝ) := hejk_lb
  have hratio_lb : 1 / (4 * C ^ 2 * (n : ℝ) ^ 2) ≤ Djk ^ 2 / (Aj * Bk) := by
    dsimp only [Djk]
    have hmax_ge : Aj * Bk ≤ (max Aj Bk) ^ 2 := by
      rcases le_total Aj Bk with hle | hle
      · rw [max_eq_right hle]; nlinarith
      · rw [max_eq_left hle]; nlinarith
    have hden_nn : 0 ≤ 4 * C ^ 2 * (n : ℝ) ^ 2 * (Aj * Bk) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)) (mul_nonneg hAj.le hBk.le)
    have h1 : (Aj * Bk) / (4 * C ^ 2 * (n : ℝ) ^ 2 * (Aj * Bk)) ≤
        (max Aj Bk) ^ 2 / (4 * C ^ 2 * (n : ℝ) ^ 2 * (Aj * Bk)) :=
      div_le_div_of_nonneg_right hmax_ge hden_nn
    have h2 : (Aj * Bk) / (4 * C ^ 2 * (n : ℝ) ^ 2 * (Aj * Bk)) = 1 / (4 * C ^ 2 * (n : ℝ) ^ 2) := by
      rw [show (Aj * Bk) / (4 * C ^ 2 * (n : ℝ) ^ 2 * (Aj * Bk)) =
        (1 * (Aj * Bk)) / ((4 * C ^ 2 * (n : ℝ) ^ 2) * (Aj * Bk)) by ring]
      exact mul_div_mul_right 1 _ (mul_pos hAj hBk).ne'
    have h3 : (max Aj Bk / (2 * C * (n : ℝ))) ^ 2 / (Aj * Bk) =
        (max Aj Bk) ^ 2 / (4 * C ^ 2 * (n : ℝ) ^ 2 * (Aj * Bk)) := by
      rw [div_pow, div_div]; congr 1; ring
    rw [h3, ← h2]; exact h1
  let F0_jk : ℝ := (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) *
    ((Vj j).card : ℝ) * ((Vj k).card : ℝ) * (Djk ^ 2 / (Aj * Bk)) / (2000 : ℝ) ^ (p0 + 1)
  have hf'_le_F0 : f' ≤ F0_jk := by
    dsimp only [f', F0_jk]
    have hεη_nn : 0 ≤ ε * η ^ 2 := mul_nonneg hε.le (sq_nonneg _)
    have hρjk_nn : 0 ≤ ((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ)) :=
      div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hρpow : (ε * η ^ 2) ^ (5 / 2 : ℝ) ≤
        (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hεη_nn hρjk_lb (by norm_num)
    have hρpow_nn : 0 ≤ (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) :=
      Real.rpow_nonneg hρjk_nn _
    have h1a : (ε * η ^ 2) ^ (5 / 2 : ℝ) * (η * (n : ℝ)) ≤
        (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) * ((Vj j).card : ℝ) :=
      mul_le_mul hρpow hVj_lb (mul_nonneg hηpos.le hn_pos.le) hρpow_nn
    have h1a_nn : 0 ≤ (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) *
        ((Vj j).card : ℝ) := mul_nonneg hρpow_nn (Nat.cast_nonneg _)
    have h1b : (ε * η ^ 2) ^ (5 / 2 : ℝ) * (η * (n : ℝ)) * (η * (n : ℝ)) ≤
        (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) *
        ((Vj j).card : ℝ) * ((Vj k).card : ℝ) :=
      mul_le_mul h1a hVk_lb (mul_nonneg hηpos.le hn_pos.le) h1a_nn
    have h1b_nn : 0 ≤ (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) *
        ((Vj j).card : ℝ) * ((Vj k).card : ℝ) := mul_nonneg h1a_nn (Nat.cast_nonneg _)
    have h1 : (ε * η ^ 2) ^ (5 / 2 : ℝ) * (η * (n : ℝ)) * (η * (n : ℝ)) * (1 / (4 * C ^ 2 * (n : ℝ) ^ 2)) ≤
        (((Ejk j k).card : ℝ) / (((Vj j).card : ℝ) * ((Vj k).card : ℝ))) ^ (5 / 2 : ℝ) *
        ((Vj j).card : ℝ) * ((Vj k).card : ℝ) * (Djk ^ 2 / (Aj * Bk)) :=
      mul_le_mul h1b hratio_lb (div_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))) h1b_nn
    have h2 : (ε * η ^ 2) ^ (5 / 2 : ℝ) * (η * (n : ℝ)) * (η * (n : ℝ)) * (1 / (4 * C ^ 2 * (n : ℝ) ^ 2)) /
        (2000 : ℝ) ^ (p0 + 1) =
        (ε * η ^ 2) ^ (5 / 2 : ℝ) * η ^ 2 / (4 * C ^ 2 * (2000 : ℝ) ^ (p0 + 1)) := by
      have hn2 : (n : ℝ) ^ 2 ≠ 0 := (pow_pos hn_pos 2).ne'
      calc (ε * η ^ 2) ^ (5 / 2 : ℝ) * (η * (n : ℝ)) * (η * (n : ℝ)) * (1 / (4 * C ^ 2 * (n : ℝ) ^ 2)) /
            (2000 : ℝ) ^ (p0 + 1)
          = ((ε * η ^ 2) ^ (5 / 2 : ℝ) * η ^ 2 / (4 * C ^ 2 * (2000 : ℝ) ^ (p0 + 1))) *
            ((n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
        _ = (ε * η ^ 2) ^ (5 / 2 : ℝ) * η ^ 2 / (4 * C ^ 2 * (2000 : ℝ) ^ (p0 + 1)) := by
            rw [div_self hn2, mul_one]
    rw [← h2]
    exact div_le_div_of_nonneg_right h1 (pow_nonneg (by norm_num) _)
  -- Deduce |U| ≥ θ * n ≥ 2 and apply dense_rational_box!
  have hU_sub_V : U ⊆ V := hU_sub_Vk.trans (Finset.filter_subset _ V)
  have hU_lb_n : θ * (n : ℝ) ≤ (U.card : ℝ) := by
    have hpow24 : (f' / K0) ^ (24 : ℕ) ≤ (F0_jk / K0) ^ (24 : ℕ) :=
      pow_le_pow_left₀ (div_nonneg hf'pos.le hK0pos.le) (div_le_div_of_nonneg_right hf'_le_F0 hK0pos.le) 24
    have hmul24 : (f' / K0) ^ (24 : ℕ) * (η * (n : ℝ)) ≤ (F0_jk / K0) ^ (24 : ℕ) * ((Vj k).card : ℝ) :=
      mul_le_mul hpow24 hVk_lb (mul_nonneg hηpos.le hn_pos.le) (pow_nonneg (div_nonneg (hf'pos.le.trans hf'_le_F0) hK0pos.le) 24)
    calc θ * (n : ℝ)
        = (1 / 4 : ℝ) * ((f' / K0) ^ (24 : ℕ) * (η * (n : ℝ))) := by dsimp only [θ]; ring
      _ ≤ (1 / 4 : ℝ) * ((F0_jk / K0) ^ (24 : ℕ) * ((Vj k).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hmul24 (by norm_num)
      _ = (1 / 4 : ℝ) * (F0_jk / K0) ^ (24 : ℕ) * ((Vj k).card : ℝ) := by ring
      _ ≤ (U.card : ℝ) := hU_lb_Vk
  have hU_ge2 : 2 ≤ U.card := by
    have h2_le_θn : (2 : ℝ) ≤ θ * (n : ℝ) := by
      have hceil : 2 / θ ≤ (n0 : ℝ) := (Nat.le_ceil (2 / θ)).trans (by exact_mod_cast le_max_right 2 _)
      have hn_ge : (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_small
      have h1 : 2 / θ ≤ (n : ℝ) := hceil.trans hn_ge
      rwa [div_le_iff₀ hθpos, mul_comm] at h1
    have h2R : (2 : ℝ) ≤ (U.card : ℝ) := h2_le_θn.trans hU_lb_n
    exact_mod_cast h2R
  have harea_C' : (AU : ℝ) * (BU : ℝ) ≤ C' * (U.card : ℝ) := by
    have hdiv512 : 512 / F0_jk ≤ 512 / f' := div_le_div_of_nonneg_left (by norm_num) hf'pos hf'_le_F0
    calc (AU : ℝ) * (BU : ℝ)
        ≤ (512 / F0_jk) * (U.card : ℝ) := harea_F0
      _ ≤ (512 / f') * (U.card : ℝ) := mul_le_mul_of_nonneg_right hdiv512 (Nat.cast_nonneg _)
      _ ≤ C' * (U.card : ℝ) := mul_le_mul_of_nonneg_right (le_max_right 1 _) (Nat.cast_nonneg _)
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => hVpos u (hU_sub_V hu)
  have hbox_U := hBox U hU_ge2 hUpos ξ hξ_pos AU BU hAU_pos hBU_pos harea_C' hU_rep
  -- Transfer Type I loss from U at 1/(2|U|) to V at 1/(2n)!
  have hU_card_pos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast (by omega : 0 < U.card)
  have hloss : θ * κ_box ≤ typeILoss V (1 / (2 * (n : ℝ))) := by
    have h2u_pos : (0 : ℝ) < 1 / (2 * (U.card : ℝ)) := div_pos zero_lt_one (mul_pos (by norm_num) hU_card_pos)
    have h2n_nn : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := div_nonneg zero_le_one (mul_nonneg (by norm_num) hn_pos.le)
    calc θ * κ_box
        ≤ ((U.card : ℝ) / (n : ℝ)) * κ_box := by
          refine mul_le_mul_of_nonneg_right ?_ hκ_box_pos.le
          rwa [le_div_iff₀ hn_pos]
      _ ≤ ((U.card : ℝ) / (n : ℝ)) * typeILoss U (1 / (2 * (U.card : ℝ))) :=
          mul_le_mul_of_nonneg_left hbox_U (div_nonneg hU_card_pos.le hn_pos.le)
      _ = ((1 / (2 * (n : ℝ))) / (1 / (2 * (U.card : ℝ)))) * typeILoss U (1 / (2 * (U.card : ℝ))) := by
          congr 1; rw [div_div_div_eq, one_mul, mul_one, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = typeILoss U (1 / (2 * (n : ℝ))) :=
          (typeILoss_linear U (1 / (2 * (n : ℝ))) (1 / (2 * (U.card : ℝ))) h2u_pos.ne').symm
      _ ≤ typeILoss V (1 / (2 * (n : ℝ))) := typeILoss_mono hU_sub_V hVpos h2n_nn
  exact (min_le_left _ _).trans hloss

end MPLinearTypeI

end LRMod1Extract

/-!
Dilation Spillover Inequality (Section 4 of Hu and Jing, arXiv:2610.23790).

Self-contained formalization of:
1. Lemma 4.1: Greedy k-coloring of half-open intervals on R.
2. Lemma 4.2a: Monotonicity of union measure under center scaling (derivative-free).
3. Lemma 4.2b: Real dilation inequality for excess multiplicity integrals.
4. Lemma 4.3: Periodic lift to [0, 1) via a two-sided integer-endpoint sandwich.
5. Proposition 4.4 (dilation_spillover): Dilation spillover inequality for pVol and wVol.
-/

namespace LRMod2

open MeasureTheory Finset BigOperators

def bohrLift (v : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ m : ℤ, Set.Ico (((m : ℝ) - δ) / (v : ℝ)) (((m : ℝ) + δ) / (v : ℝ))

noncomputable def multFunc (V : Finset ℕ) (δ : ℝ) (x : ℝ) : ℕ := by
  classical
  exact (V.filter (fun v => x ∈ bohrLift v δ)).card

noncomputable def wVol (V : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ x : ℝ) - 1) 0

noncomputable def pVol (V : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, (multFunc V δ x : ℝ) * ((multFunc V δ x : ℝ) - 1)

section GreedyColoring

private def rLt {m : ℕ} (r : Fin m → ℝ) (i j : Fin m) : Prop :=
  r i < r j ∨ (r i = r j ∧ i < j)

private lemma rLt_irrefl {m : ℕ} (r : Fin m → ℝ) (i : Fin m) : ¬ rLt r i i := by
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

private lemma rLt_trans {m : ℕ} (r : Fin m → ℝ) {i j k : Fin m}
    (hij : rLt r i j) (hjk : rLt r j k) : rLt r i k := by
  rcases hij with h1 | ⟨e1, h1⟩ <;> rcases hjk with h2 | ⟨e2, h2⟩
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1.symm ▸ h2)
  · exact Or.inr ⟨e1.trans e2, lt_trans h1 h2⟩

private lemma rLt_asymm {m : ℕ} (r : Fin m → ℝ) {i j : Fin m}
    (h : rLt r i j) : ¬ rLt r j i :=
  fun h' => rLt_irrefl r i (rLt_trans r h h')

private lemma rLt_trichotomy {m : ℕ} (r : Fin m → ℝ) {i j : Fin m} (hij : i ≠ j) :
    rLt r i j ∨ rLt r j i := by
  rcases lt_trichotomy (r i) (r j) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy i j with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact (hij h').elim
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

private lemma r_le_of_rLt {m : ℕ} (r : Fin m → ℝ) {i j : Fin m}
    (h : rLt r i j) : r i ≤ r j := by
  rcases h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

private lemma rLt_castSucc_iff {m : ℕ} (r : Fin (m + 1) → ℝ) (i j : Fin m) :
    rLt (r ∘ Fin.castSucc) i j ↔ rLt r i.castSucc j.castSucc := by
  simp only [rLt, Function.comp_apply, Fin.castSucc_lt_castSucc_iff]

private noncomputable def rRank {m : ℕ} (r : Fin m → ℝ) (S : Finset (Fin m)) (a : Fin m) : ℕ := by
  classical
  exact (S.filter (fun b => rLt r a b)).card

private noncomputable def topK {m : ℕ} (r : Fin m → ℝ) (k : ℕ) (S : Finset (Fin m)) :
    Finset (Fin m) := by
  classical
  exact S.filter (fun a => rRank r S a < k)

private lemma mem_topK {m : ℕ} (r : Fin m → ℝ) (k : ℕ) (S : Finset (Fin m)) (a : Fin m) :
    a ∈ topK r k S ↔ a ∈ S ∧ rRank r S a < k := by
  classical
  simp only [topK, Finset.mem_filter]

private lemma topK_subset {m : ℕ} (r : Fin m → ℝ) (k : ℕ) (S : Finset (Fin m)) :
    topK r k S ⊆ S := by
  intro a ha
  exact ((mem_topK r k S a).mp ha).1

private lemma rRank_lt_of_rLt {m : ℕ} (r : Fin m → ℝ) {S : Finset (Fin m)} {a b : Fin m}
    (hb : b ∈ S) (hab : rLt r a b) : rRank r S b < rRank r S a := by
  classical
  simp only [rRank]
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨b, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨hb, hab⟩
    · simp only [Finset.mem_filter]
      intro h
      exact rLt_irrefl r b h.2
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, rLt_trans r hab hc.2⟩

private lemma rRank_injOn {m : ℕ} (r : Fin m → ℝ) (S : Finset (Fin m)) :
    Set.InjOn (rRank r S) (S : Set (Fin m)) := by
  intro a ha b hb hEq
  by_contra hne
  rcases rLt_trichotomy r hne with h | h
  · exact (ne_of_lt (rRank_lt_of_rLt r hb h)) hEq.symm
  · exact (ne_of_lt (rRank_lt_of_rLt r ha h)) hEq

private lemma rRank_lt_card {m : ℕ} (r : Fin m → ℝ) {S : Finset (Fin m)} {a : Fin m}
    (ha : a ∈ S) : rRank r S a < S.card := by
  classical
  simp only [rRank]
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  refine ⟨a, ha, ?_⟩
  simp only [Finset.mem_filter]
  intro h
  exact rLt_irrefl r a h.2

private lemma image_rRank_eq_range {m : ℕ} (r : Fin m → ℝ) (S : Finset (Fin m)) :
    S.image (rRank r S) = Finset.range S.card := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (rRank_lt_card r ha)
  · rw [Finset.card_range, Finset.card_image_of_injOn (rRank_injOn r S)]

private lemma exists_rRank_eq {m : ℕ} (r : Fin m → ℝ) {S : Finset (Fin m)} {d : ℕ}
    (hd : d < S.card) : ∃ u ∈ S, rRank r S u = d := by
  have hmem : d ∈ S.image (rRank r S) := by
    rw [image_rRank_eq_range]
    exact Finset.mem_range.mpr hd
  exact Finset.mem_image.mp hmem

private lemma card_topK {m : ℕ} (r : Fin m → ℝ) (k : ℕ) (S : Finset (Fin m)) :
    (topK r k S).card = min S.card k := by
  have hinj : Set.InjOn (rRank r S) (topK r k S : Set (Fin m)) :=
    (rRank_injOn r S).mono (Finset.coe_subset.mpr (topK_subset r k S))
  rw [← Finset.card_image_of_injOn hinj]
  have himg : (topK r k S).image (rRank r S) = Finset.range (min S.card k) := by
    ext n
    simp only [Finset.mem_image, mem_topK, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
      exact ⟨rRank_lt_card r ha, hlt⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨a, ha, rfl⟩ := exists_rRank_eq r h1
      exact ⟨a, ⟨ha, h2⟩, rfl⟩
  rw [himg, Finset.card_range]

private lemma rRank_eq_of_upper {m : ℕ} (r : Fin m → ℝ) {S' A : Finset (Fin m)}
    (hsub : S' ⊆ A) (hup : ∀ a ∈ S', ∀ b ∈ A, rLt r a b → b ∈ S')
    {a : Fin m} (ha : a ∈ S') : rRank r S' a = rRank r A a := by
  classical
  simp only [rRank]
  congr 1
  ext b
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hb, hlt⟩ => ⟨hsub hb, hlt⟩, fun ⟨hb, hlt⟩ => ⟨hup a ha b hb hlt, hlt⟩⟩

private lemma rRank_map_castSucc {m : ℕ} (r : Fin (m + 1) → ℝ) (S' : Finset (Fin m)) (a : Fin m) :
    rRank r (S'.map Fin.castSuccEmb) a.castSucc = rRank (r ∘ Fin.castSucc) S' a := by
  classical
  simp only [rRank]
  have heq : (S'.map Fin.castSuccEmb).filter (fun b => rLt r a.castSucc b) =
      (S'.filter (fun b => rLt (r ∘ Fin.castSucc) a b)).map Fin.castSuccEmb := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_map, Fin.castSuccEmb_apply]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hlt⟩
      exact ⟨j, ⟨hj, (rLt_castSucc_iff r a j).mpr hlt⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hlt⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, (rLt_castSucc_iff r a j).mp hlt⟩
  rw [heq, Finset.card_map]

private lemma topK_map_castSucc {m : ℕ} (r : Fin (m + 1) → ℝ) (k : ℕ) (S' : Finset (Fin m)) :
    topK r k (S'.map Fin.castSuccEmb) = (topK (r ∘ Fin.castSucc) k S').map Fin.castSuccEmb := by
  ext b
  simp only [mem_topK, Finset.mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hlt⟩
    rw [rRank_map_castSucc] at hlt
    exact ⟨j, ⟨hj, hlt⟩, rfl⟩
  · rintro ⟨j, ⟨hj, hlt⟩, rfl⟩
    refine ⟨⟨j, hj, rfl⟩, ?_⟩
    rw [rRank_map_castSucc]
    exact hlt

private lemma greedy_coloring_monotone :
    ∀ (m : ℕ) (l r : Fin m → ℝ), Monotone l → ∀ (k : ℕ), 0 < k →
      ∃ col : Fin m → Fin k,
        ∀ x : ℝ,
          Set.InjOn col
            (topK r k (Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l i) (r i))) :
              Set (Fin m)) := by
  intro m
  induction m with
  | zero =>
    intro l r _ k _
    refine ⟨Fin.elim0, fun x a ha => ?_⟩
    exact Fin.elim0 a
  | succ m ih =>
    intro l r hl k hk
    classical
    let l' : Fin m → ℝ := l ∘ Fin.castSucc
    let r' : Fin m → ℝ := r ∘ Fin.castSucc
    have hl' : Monotone l' := fun i j hij => hl (Fin.castSucc_le_castSucc_iff.mpr hij)
    obtain ⟨col', hcol'⟩ := ih l' r' hl' k hk
    let S : ℝ → Finset (Fin (m + 1)) := fun x =>
      Finset.univ.filter (fun i : Fin (m + 1) => x ∈ Set.Ico (l i) (r i))
    let S' : ℝ → Finset (Fin m) := fun x =>
      Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l' i) (r' i))
    let A : Finset (Fin m) := S' (l (Fin.last m))
    have hS_not_mem : ∀ x : ℝ, x ∉ Set.Ico (l (Fin.last m)) (r (Fin.last m)) →
        S x = (S' x).map Fin.castSuccEmb := by
      intro x hx
      ext b
      simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Fin.castSuccEmb_apply]
      refine Fin.lastCases ?_ ?_ b
      · constructor
        · intro h; exact (hx h).elim
        · rintro ⟨j, _, hj⟩; exact (Fin.castSucc_ne_last j hj).elim
      · intro j
        constructor
        · intro h; exact ⟨j, h, rfl⟩
        · rintro ⟨i, hi, hij⟩
          have hEq : i = j := Fin.castSucc_injective m hij
          exact hEq ▸ hi
    have hS_mem : ∀ x : ℝ, x ∈ Set.Ico (l (Fin.last m)) (r (Fin.last m)) →
        S x = insert (Fin.last m) ((S' x).map Fin.castSuccEmb) := by
      intro x hx
      ext b
      simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_map, Fin.castSuccEmb_apply]
      refine Fin.lastCases ?_ ?_ b
      · exact ⟨fun _ => Or.inl rfl, fun _ => hx⟩
      · intro j
        constructor
        · intro h; exact Or.inr ⟨j, h, rfl⟩
        · rintro (h | ⟨i, hi, hij⟩)
          · exact (Fin.castSucc_ne_last j h).elim
          · have hEq : i = j := Fin.castSucc_injective m hij
            exact hEq ▸ hi
    have hS'_sub_A : ∀ x : ℝ, l (Fin.last m) ≤ x → S' x ⊆ A := by
      intro x hx i hi
      simp only [S', A, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at hi ⊢
      exact ⟨hl (Fin.le_last i.castSucc), lt_of_le_of_lt hx hi.2⟩
    have hS'_upper_A : ∀ x : ℝ, l (Fin.last m) ≤ x →
        ∀ a ∈ S' x, ∀ b ∈ A, rLt r' a b → b ∈ S' x := by
      intro x hx a ha b hb hab
      simp only [S', A, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at ha hb ⊢
      exact ⟨le_trans (hl (Fin.le_last b.castSucc)) hx, lt_of_lt_of_le ha.2 (r_le_of_rLt r' hab)⟩
    have hsnoc_not_mem : ∀ (c_last : Fin k) (x : ℝ),
        x ∉ Set.Ico (l (Fin.last m)) (r (Fin.last m)) →
        Set.InjOn (Fin.snoc col' c_last) (topK r k (S x) : Set (Fin (m + 1))) := by
      intro c_last x hx
      rw [hS_not_mem x hx, topK_map_castSucc]
      intro a ha b hb hEq
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Fin.castSuccEmb_apply] at ha hb
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      simp only [Fin.snoc_castSucc] at hEq
      exact congrArg Fin.castSucc (hcol' x hi hj hEq)
    by_cases hA : A.card < k
    · have hlt_univ : (A.image col').card < (Finset.univ : Finset (Fin k)).card := by
        calc (A.image col').card ≤ A.card := Finset.card_image_le
          _ < k := hA
          _ = (Finset.univ : Finset (Fin k)).card := (Finset.card_fin k).symm
      obtain ⟨c_last, _, hc_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_univ
      refine ⟨Fin.snoc col' c_last, fun x => ?_⟩
      by_cases hx : x ∈ Set.Ico (l (Fin.last m)) (r (Fin.last m))
      · refine Set.InjOn.mono (Finset.coe_subset.mpr (topK_subset r k (S x))) ?_
        rw [hS_mem x hx]
        have hsubA : S' x ⊆ A := hS'_sub_A x hx.1
        have htop_eq : topK r' k (S' x) = S' x := by
          ext i
          simp only [mem_topK, and_iff_left_iff_imp]
          intro hi
          exact lt_trans (rRank_lt_card r' hi) (lt_of_le_of_lt (Finset.card_le_card hsubA) hA)
        have hinjS' : Set.InjOn col' (S' x : Set (Fin m)) := by
          rw [← htop_eq]
          exact hcol' x
        intro a ha b hb hEq
        simp only [Finset.coe_insert, Finset.coe_map, Set.mem_insert_iff, Set.mem_image,
          Finset.mem_coe, Fin.castSuccEmb_apply] at ha hb
        rcases ha with rfl | ⟨i, hi, rfl⟩ <;> rcases hb with rfl | ⟨j, hj, rfl⟩
        · rfl
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hEq
          exfalso
          exact hc_not (Finset.mem_image.mpr ⟨j, hsubA hj, hEq.symm⟩)
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hEq
          exfalso
          exact hc_not (Finset.mem_image.mpr ⟨i, hsubA hi, hEq⟩)
        · simp only [Fin.snoc_castSucc] at hEq
          exact congrArg Fin.castSucc (hinjS' hi hj hEq)
      · exact hsnoc_not_mem c_last x hx
    · push Not at hA
      have hk1 : k - 1 < A.card := by omega
      obtain ⟨u, huA, huRank⟩ := exists_rRank_eq r' hk1
      have huTopA : u ∈ topK r' k A := (mem_topK r' k A u).mpr ⟨huA, by omega⟩
      let c_last : Fin k := col' u
      refine ⟨Fin.snoc col' c_last, fun x => ?_⟩
      by_cases hx : x ∈ Set.Ico (l (Fin.last m)) (r (Fin.last m))
      · have hsubA : S' x ⊆ A := hS'_sub_A x hx.1
        have hupA : ∀ a ∈ S' x, ∀ b ∈ A, rLt r' a b → b ∈ S' x := hS'_upper_A x hx.1
        have hrank_eq : ∀ a ∈ S' x, rRank r' (S' x) a = rRank r' A a :=
          fun a ha => rRank_eq_of_upper r' hsubA hupA ha
        by_cases hS'k : (S' x).card < k
        · refine Set.InjOn.mono (Finset.coe_subset.mpr (topK_subset r k (S x))) ?_
          rw [hS_mem x hx]
          have hS'_sub_topA : S' x ⊆ topK r' k A := by
            intro a ha
            rw [mem_topK]
            refine ⟨hsubA ha, ?_⟩
            rw [← hrank_eq a ha]
            exact lt_trans (rRank_lt_card r' ha) hS'k
          have hu_not_S' : u ∉ S' x := by
            intro huS'
            have hlt : rRank r' (S' x) u < (S' x).card := rRank_lt_card r' huS'
            rw [hrank_eq u huS', huRank] at hlt
            omega
          have hinjTopA : Set.InjOn col' (topK r' k A : Set (Fin m)) := hcol' (l (Fin.last m))
          intro a ha b hb hEq
          simp only [Finset.coe_insert, Finset.coe_map, Set.mem_insert_iff, Set.mem_image,
            Finset.mem_coe, Fin.castSuccEmb_apply] at ha hb
          rcases ha with rfl | ⟨i, hi, rfl⟩ <;> rcases hb with rfl | ⟨j, hj, rfl⟩
          · rfl
          · simp only [Fin.snoc_last, Fin.snoc_castSucc, c_last] at hEq
            have hju : u = j := hinjTopA huTopA (hS'_sub_topA hj) hEq
            exact (hu_not_S' (hju ▸ hj)).elim
          · simp only [Fin.snoc_last, Fin.snoc_castSucc, c_last] at hEq
            have hiu : i = u := hinjTopA (hS'_sub_topA hi) huTopA hEq
            exact (hu_not_S' (hiu ▸ hi)).elim
          · simp only [Fin.snoc_castSucc] at hEq
            exact congrArg Fin.castSucc (hinjTopA (hS'_sub_topA hi) (hS'_sub_topA hj) hEq)
        · push Not at hS'k
          have htopS'_sub : topK r' k (S' x) ⊆ topK r' k A := by
            intro a ha
            rw [mem_topK] at ha ⊢
            refine ⟨hsubA ha.1, ?_⟩
            rw [← hrank_eq a ha.1]
            exact ha.2
          have htopS'_eq : topK r' k (S' x) = topK r' k A := by
            refine Finset.eq_of_subset_of_card_le htopS'_sub ?_
            rw [card_topK, card_topK, min_eq_right hA, min_eq_right hS'k]
          have huTopS' : u ∈ topK r' k (S' x) := htopS'_eq ▸ huTopA
          have huS' : u ∈ S' x := topK_subset r' k (S' x) huTopS'
          have huRankS' : rRank r' (S' x) u = k - 1 := (hrank_eq u huS').trans huRank
          let U : Finset (Fin m) := (S' x).filter (fun b => rLt r' u b)
          have hU_card : U.card = k - 1 := huRankS'
          have hu_not_U : u ∉ U := by
            simp only [U, Finset.mem_filter]
            intro h
            exact rLt_irrefl r' u h.2
          have hU_sub_top : U ⊆ topK r' k (S' x) := by
            intro b hb
            simp only [U, Finset.mem_filter] at hb
            rw [mem_topK]
            refine ⟨hb.1, ?_⟩
            have hlt : rRank r' (S' x) b < rRank r' (S' x) u := rRank_lt_of_rLt r' hb.1 hb.2
            omega
          have htop_eq_ins : topK r' k (S' x) = insert u U := by
            refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
            · exact Finset.insert_subset huTopS' hU_sub_top
            · rw [card_topK, min_eq_right hS'k, Finset.card_insert_of_notMem hu_not_U, hU_card]
              omega
          have hS_card : (S x).card = (S' x).card + 1 := by
            rw [hS_mem x hx, Finset.card_insert_of_notMem, Finset.card_map]
            simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
            intro i _
            exact Fin.castSucc_ne_last i
          have htopS_card : (topK r k (S x)).card = k := by
            rw [card_topK, hS_card, min_eq_right (by omega)]
          have hne_last : Fin.last m ≠ u.castSucc := (Fin.castSucc_ne_last u).symm
          rcases rLt_trichotomy r hne_last with hlast_lt | hu_lt_last
          · have hsub_top : (topK r' k (S' x)).map Fin.castSuccEmb ⊆ topK r k (S x) := by
              intro b hb
              simp only [Finset.mem_map, Fin.castSuccEmb_apply] at hb
              obtain ⟨a, ha, rfl⟩ := hb
              rw [mem_topK]
              have haS' : a ∈ S' x := topK_subset r' k (S' x) ha
              refine ⟨?_, ?_⟩
              · rw [hS_mem x hx]
                exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem Fin.castSuccEmb haS')
              · have hlast_lt_a : rLt r (Fin.last m) a.castSucc := by
                  rw [htop_eq_ins, Finset.mem_insert] at ha
                  rcases ha with rfl | haU
                  · exact hlast_lt
                  · simp only [U, Finset.mem_filter] at haU
                    exact rLt_trans r hlast_lt ((rLt_castSucc_iff r u a).mp haU.2)
                have hfilt_eq : (S x).filter (fun c => rLt r a.castSucc c) =
                    ((S' x).map Fin.castSuccEmb).filter (fun c => rLt r a.castSucc c) := by
                  rw [hS_mem x hx, Finset.filter_insert]
                  rw [if_neg (rLt_asymm r hlast_lt_a)]
                have hrank_a : rRank r (S x) a.castSucc = rRank r' (S' x) a := by
                  calc rRank r (S x) a.castSucc
                      = ((S x).filter (fun c => rLt r a.castSucc c)).card := rfl
                    _ = (((S' x).map Fin.castSuccEmb).filter (fun c => rLt r a.castSucc c)).card :=
                        congrArg Finset.card hfilt_eq
                    _ = rRank r (S' x |>.map Fin.castSuccEmb) a.castSucc := rfl
                    _ = rRank r' (S' x) a := rRank_map_castSucc r (S' x) a
                rw [hrank_a]
                exact ((mem_topK r' k (S' x) a).mp ha).2
            have htopS_eq : topK r k (S x) = (topK r' k (S' x)).map Fin.castSuccEmb := by
              refine (Finset.eq_of_subset_of_card_le hsub_top ?_).symm
              rw [htopS_card, Finset.card_map, card_topK, min_eq_right hS'k]
            rw [htopS_eq]
            intro a ha b hb hEq
            simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
              Fin.castSuccEmb_apply] at ha hb
            obtain ⟨i, hi, rfl⟩ := ha
            obtain ⟨j, hj, rfl⟩ := hb
            simp only [Fin.snoc_castSucc] at hEq
            exact congrArg Fin.castSucc (hcol' x hi hj hEq)
          · have hlast_not_U : Fin.last m ∉ U.map Fin.castSuccEmb := by
              simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
              intro i _
              exact Fin.castSucc_ne_last i
            have hsub_top : insert (Fin.last m) (U.map Fin.castSuccEmb) ⊆ topK r k (S x) := by
              intro b hb
              rw [Finset.mem_insert] at hb
              rcases hb with rfl | hbU
              · rw [mem_topK]
                refine ⟨?_, ?_⟩
                · rw [hS_mem x hx]
                  exact Finset.mem_insert_self _ _
                · have hfilt_sub : (S x).filter (fun c => rLt r (Fin.last m) c) ⊆
                      U.map Fin.castSuccEmb := by
                    intro c hc
                    simp only [Finset.mem_filter] at hc
                    rw [hS_mem x hx, Finset.mem_insert] at hc
                    rcases hc.1 with rfl | hc'
                    · exact (rLt_irrefl r (Fin.last m) hc.2).elim
                    · simp only [Finset.mem_map, Fin.castSuccEmb_apply] at hc' ⊢
                      obtain ⟨j, hjS', rfl⟩ := hc'
                      refine ⟨j, ?_, rfl⟩
                      simp only [U, Finset.mem_filter]
                      exact ⟨hjS', (rLt_castSucc_iff r u j).mpr (rLt_trans r hu_lt_last hc.2)⟩
                  have hle : rRank r (S x) (Fin.last m) ≤ (U.map Fin.castSuccEmb).card :=
                    Finset.card_le_card hfilt_sub
                  rw [Finset.card_map, hU_card] at hle
                  omega
              · simp only [Finset.mem_map, Fin.castSuccEmb_apply] at hbU
                obtain ⟨a, haU, rfl⟩ := hbU
                have haS' : a ∈ S' x := (Finset.mem_filter.mp haU).1
                have hua : rLt r' u a := (Finset.mem_filter.mp haU).2
                rw [mem_topK]
                refine ⟨?_, ?_⟩
                · rw [hS_mem x hx]
                  exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem Fin.castSuccEmb haS')
                · have hfilt_sub : (S x).filter (fun c => rLt r a.castSucc c) ⊆
                      insert (Fin.last m)
                        (((S' x).map Fin.castSuccEmb).filter (fun c => rLt r a.castSucc c)) := by
                    intro c hc
                    simp only [Finset.mem_filter] at hc
                    rw [hS_mem x hx, Finset.mem_insert] at hc
                    rcases hc.1 with rfl | hc'
                    · exact Finset.mem_insert_self _ _
                    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hc', hc.2⟩)
                  have hle : rRank r (S x) a.castSucc ≤ rRank r' (S' x) a + 1 := by
                    calc rRank r (S x) a.castSucc
                        ≤ (insert (Fin.last m) (((S' x).map Fin.castSuccEmb).filter
                            (fun c => rLt r a.castSucc c))).card := Finset.card_le_card hfilt_sub
                      _ ≤ (((S' x).map Fin.castSuccEmb).filter
                            (fun c => rLt r a.castSucc c)).card + 1 := Finset.card_insert_le _ _
                      _ = rRank r' (S' x) a + 1 := by
                            exact congrArg (· + 1) (rRank_map_castSucc r (S' x) a)
                  have hlt_u : rRank r' (S' x) a < rRank r' (S' x) u :=
                    rRank_lt_of_rLt r' haS' hua
                  omega
            have htopS_eq : topK r k (S x) = insert (Fin.last m) (U.map Fin.castSuccEmb) := by
              refine (Finset.eq_of_subset_of_card_le hsub_top ?_).symm
              rw [htopS_card, Finset.card_insert_of_notMem hlast_not_U, Finset.card_map, hU_card]
              omega
            rw [htopS_eq]
            have hinjTopS' : Set.InjOn col' (topK r' k (S' x) : Set (Fin m)) := hcol' x
            intro a ha b hb hEq
            simp only [Finset.coe_insert, Finset.coe_map, Set.mem_insert_iff, Set.mem_image,
              Finset.mem_coe, Fin.castSuccEmb_apply] at ha hb
            rcases ha with rfl | ⟨i, hi, rfl⟩ <;> rcases hb with rfl | ⟨j, hj, rfl⟩
            · rfl
            · simp only [Fin.snoc_last, Fin.snoc_castSucc, c_last] at hEq
              have hju : u = j := hinjTopS' huTopS' (hU_sub_top hj) hEq
              exact (hu_not_U (hju ▸ hj)).elim
            · simp only [Fin.snoc_last, Fin.snoc_castSucc, c_last] at hEq
              have hiu : i = u := hinjTopS' (hU_sub_top hi) huTopS' hEq
              exact (hu_not_U (hiu ▸ hi)).elim
            · simp only [Fin.snoc_castSucc] at hEq
              exact congrArg Fin.castSucc (hinjTopS' (hU_sub_top hi) (hU_sub_top hj) hEq)
      · exact hsnoc_not_mem c_last x hx

/-- Lemma 4.1 (Greedy k-coloring of half-open intervals on R). -/
lemma greedy_interval_coloring {m : ℕ} (l r : Fin m → ℝ) {k : ℕ} (hk : 0 < k) :
    ∃ col : Fin m → Fin k,
      ∀ x : ℝ,
        ((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l i) (r i))).image col).card =
          min (Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l i) (r i))).card k := by
  classical
  let σ : Equiv.Perm (Fin m) := Tuple.sort l
  have hlσ : Monotone (l ∘ σ) := Tuple.monotone_sort l
  obtain ⟨col0, hcol0⟩ := greedy_coloring_monotone m (l ∘ σ) (r ∘ σ) hlσ k hk
  refine ⟨col0 ∘ σ.symm, fun x => ?_⟩
  let S : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l i) (r i))
  let S0 : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l (σ i)) (r (σ i)))
  have hS_eq : S = S0.map σ.toEmbedding := by
    ext i
    simp only [S, S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hi
      refine ⟨σ.symm i, ?_, σ.apply_symm_apply i⟩
      simpa only [σ.apply_symm_apply] using hi
    · rintro ⟨j, hj, rfl⟩
      exact hj
  have himg_eq : S.image (col0 ∘ σ.symm) = S0.image col0 := by
    rw [hS_eq]
    ext c
    simp only [Finset.mem_image, Finset.mem_map, Equiv.toEmbedding_apply, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, by rw [Equiv.symm_apply_apply]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨σ j, ⟨j, hj, rfl⟩, by rw [Equiv.symm_apply_apply]⟩
  have hcard_S : S.card = S0.card := by
    rw [hS_eq, Finset.card_map]
  rw [himg_eq, hcard_S]
  apply le_antisymm
  · rw [le_min_iff]
    refine ⟨Finset.card_image_le, ?_⟩
    calc (S0.image col0).card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_le_univ _
      _ = k := Finset.card_fin k
  · have hsub : (topK (r ∘ σ) k S0).image col0 ⊆ S0.image col0 :=
      Finset.image_subset_image (topK_subset (r ∘ σ) k S0)
    calc min S0.card k
        = (topK (r ∘ σ) k S0).card := (card_topK (r ∘ σ) k S0).symm
      _ = ((topK (r ∘ σ) k S0).image col0).card :=
          (Finset.card_image_of_injOn (hcol0 x)).symm
      _ ≤ (S0.image col0).card := Finset.card_le_card hsub

end GreedyColoring

section UnionMonotonicity

private lemma ico_union_ico_of_le {u v a b : ℝ} (hua : u ≤ a) (hav : a ≤ v) :
    Set.Ico u v ∪ Set.Ico a b = Set.Ico u (max v b) := by
  ext x
  simp only [Set.mem_union, Set.mem_Ico, lt_max_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨le_trans hua h1, Or.inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · by_cases hxv : x < v
      · exact Or.inl ⟨h1, hxv⟩
      · push Not at hxv
        exact Or.inr ⟨le_trans hav hxv, h2⟩

private lemma decompose_monotone_ico :
    ∀ (m : ℕ) (a b : Fin m → ℝ), Monotone a → (∀ i, a i < b i) →
      ∃ L : List (ℝ × ℝ),
        L.Pairwise (fun p q => q.2 ≤ p.1) ∧
        (∀ p ∈ L, p.1 < p.2) ∧
        (∀ p ∈ L, ∃ i : Fin m, p.1 = a i) ∧
        (⋃ p ∈ L, Set.Ico p.1 p.2) = (⋃ i : Fin m, Set.Ico (a i) (b i)) ∧
        (∀ i : Fin m, ∃ p ∈ L, Set.Ico (a i) (b i) ⊆ Set.Ico p.1 p.2) := by
  intro m
  induction m with
  | zero =>
    intro a b _ _
    refine ⟨[], List.Pairwise.nil, by simp, by simp, by simp, fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro a b ha hab
    let a' : Fin m → ℝ := a ∘ Fin.castSucc
    let b' : Fin m → ℝ := b ∘ Fin.castSucc
    have ha' : Monotone a' := fun i j hij => ha (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hab' : ∀ i, a' i < b' i := fun i => hab i.castSucc
    obtain ⟨L, hpair, hlt, hleft, hunion, hcov⟩ := ih a' b' ha' hab'
    have hunion_succ :
        (⋃ i : Fin (m + 1), Set.Ico (a i) (b i)) =
          Set.Ico (a (Fin.last m)) (b (Fin.last m)) ∪
            (⋃ i : Fin m, Set.Ico (a' i) (b' i)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        exact Fin.lastCases (fun h => Or.inl h) (fun j h => Or.inr ⟨j, h⟩) i hi
      · rintro (h | ⟨j, hj⟩)
        · exact ⟨Fin.last m, h⟩
        · exact ⟨j.castSucc, hj⟩
    cases L with
    | nil =>
      refine ⟨[(a (Fin.last m), b (Fin.last m))], ?_, ?_, ?_, ?_, ?_⟩
      · exact List.pairwise_singleton _ _
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact hab (Fin.last m)
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨Fin.last m, rfl⟩
      · rw [hunion_succ, ← hunion]
        simp
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · exact ⟨(a (Fin.last m), b (Fin.last m)), List.mem_singleton_self _, subset_rfl⟩
        · intro j
          obtain ⟨p, hp, _⟩ := hcov j
          exact (List.not_mem_nil hp).elim
    | cons hd rest =>
      rcases hd with ⟨u, v⟩
      have hu_lt_v : u < v := hlt (u, v) List.mem_cons_self
      have hpair_hd : ∀ q ∈ rest, q.2 ≤ u := (List.pairwise_cons.mp hpair).1
      have hpair_rest : rest.Pairwise (fun p q => q.2 ≤ p.1) := (List.pairwise_cons.mp hpair).2
      obtain ⟨i0, hi0⟩ := hleft (u, v) List.mem_cons_self
      dsimp only at hi0
      have hu_le_last : u ≤ a (Fin.last m) := by
        rw [hi0]
        exact ha (Fin.le_last i0.castSucc)
      by_cases hov : a (Fin.last m) ≤ v
      · refine ⟨(u, max v (b (Fin.last m))) :: rest, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨hpair_hd, hpair_rest⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact lt_of_lt_of_le hu_lt_v (le_max_left _ _)
          · exact hlt p (List.mem_cons_of_mem _ hp')
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨i0.castSucc, hi0⟩
          · obtain ⟨j, hj⟩ := hleft p (List.mem_cons_of_mem _ hp')
            exact ⟨j.castSucc, hj⟩
        · rw [hunion_succ, ← hunion]
          have h1 : (⋃ p ∈ (u, max v (b (Fin.last m))) :: rest, Set.Ico p.1 p.2) =
              Set.Ico u (max v (b (Fin.last m))) ∪ (⋃ p ∈ rest, Set.Ico p.1 p.2) := by
            ext x; simp
          have h2 : (⋃ p ∈ (u, v) :: rest, Set.Ico p.1 p.2) =
              Set.Ico u v ∪ (⋃ p ∈ rest, Set.Ico p.1 p.2) := by
            ext x; simp
          rw [h1, h2, ← ico_union_ico_of_le hu_le_last hov]
          ext x
          simp only [Set.mem_union]
          tauto
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · refine ⟨(u, max v (b (Fin.last m))), List.mem_cons_self, ?_⟩
            rw [← ico_union_ico_of_le hu_le_last hov]
            exact Set.subset_union_right
          · intro j
            obtain ⟨p, hp, hsub⟩ := hcov j
            rcases List.mem_cons.mp hp with rfl | hp'
            · refine ⟨(u, max v (b (Fin.last m))), List.mem_cons_self, ?_⟩
              exact hsub.trans (Set.Ico_subset_Ico_right (le_max_left _ _))
            · exact ⟨p, List.mem_cons_of_mem _ hp', hsub⟩
      · push Not at hov
        refine ⟨(a (Fin.last m), b (Fin.last m)) :: (u, v) :: rest, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, hpair⟩
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact le_of_lt hov
          · exact le_trans (hpair_hd q hq') (le_trans (le_of_lt hu_lt_v) (le_of_lt hov))
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hab (Fin.last m)
          · exact hlt p hp'
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨Fin.last m, rfl⟩
          · obtain ⟨j, hj⟩ := hleft p hp'
            exact ⟨j.castSucc, hj⟩
        · rw [hunion_succ, ← hunion]
          ext x
          simp
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · exact ⟨(a (Fin.last m), b (Fin.last m)), List.mem_cons_self, subset_rfl⟩
          · intro j
            obtain ⟨p, hp, hsub⟩ := hcov j
            exact ⟨p, List.mem_cons_of_mem _ hp, hsub⟩

private lemma decompose_ico {m : ℕ} (a b : Fin m → ℝ) (hab : ∀ i, a i < b i) :
    ∃ (n : ℕ) (u v : Fin n → ℝ),
      Pairwise (fun p q : Fin n => Disjoint (Set.Ico (u p) (v p)) (Set.Ico (u q) (v q))) ∧
      (∀ q : Fin n, u q < v q) ∧
      (⋃ q : Fin n, Set.Ico (u q) (v q)) = (⋃ i : Fin m, Set.Ico (a i) (b i)) ∧
      (∀ i : Fin m, ∃ q : Fin n, Set.Ico (a i) (b i) ⊆ Set.Ico (u q) (v q)) := by
  let σ : Equiv.Perm (Fin m) := Tuple.sort a
  obtain ⟨L, hpair, hlt, _, hunion, hcov⟩ :=
    decompose_monotone_ico m (a ∘ σ) (b ∘ σ) (Tuple.monotone_sort a) (fun i => hab (σ i))
  refine ⟨L.length, fun q => L[q].1, fun q => L[q].2, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    have hdisj : ∀ {p q : Fin L.length}, p < q →
        Disjoint (Set.Ico L[p].1 L[p].2) (Set.Ico L[q].1 L[q].2) := by
      intro p q hlt_pq
      have hle : L[q].2 ≤ L[p].1 :=
        (List.pairwise_iff_getElem.mp hpair) p.val q.val p.isLt q.isLt hlt_pq
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact not_lt.mpr (le_trans hx2.2.le hle) (lt_of_lt_of_le (lt_of_le_of_lt hx1.1 hx2.2) (by linarith [hx1.1, hx2.2, hle]))
    rcases lt_or_gt_of_ne hpq with h | h
    · exact hdisj h
    · exact (hdisj h).symm
  · intro q
    exact hlt L[q] (List.getElem_mem q.isLt)
  · have hL_eq : (⋃ q : Fin L.length, Set.Ico L[q].1 L[q].2) =
        (⋃ p ∈ L, Set.Ico p.1 p.2) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨L[q], List.getElem_mem q.isLt, hq⟩
      · rintro ⟨p, hp, hxp⟩
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hp
        exact ⟨⟨idx, hidx⟩, hxp⟩
    have hσ_eq : (⋃ i : Fin m, Set.Ico (a (σ i)) (b (σ i))) =
        (⋃ i : Fin m, Set.Ico (a i) (b i)) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨σ i, hi⟩
      · rintro ⟨i, hi⟩; exact ⟨σ.symm i, by simpa only [σ.apply_symm_apply] using hi⟩
    rw [hL_eq, hunion]
    exact hσ_eq
  · intro i
    obtain ⟨p, hp, hsub⟩ := hcov (σ.symm i)
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hp
    refine ⟨⟨idx, hidx⟩, ?_⟩
    change Set.Ico (a i) (b i) ⊆ Set.Ico L[idx].1 L[idx].2
    simpa only [Function.comp_apply, σ.apply_symm_apply] using hsub

/-- Lemma 4.2a: Monotonicity of union measure under center scaling (derivative-free). -/
lemma volume_iUnion_center_scale_mono {m : ℕ} (c r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    {t₁ t₂ : ℝ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂) :
    volume (⋃ i : Fin m, Set.Ico (t₁ * c i - r i) (t₁ * c i + r i)) ≤
      volume (⋃ i : Fin m, Set.Ico (t₂ * c i - r i) (t₂ * c i + r i)) := by
  classical
  let J : ℝ → Fin m → Set ℝ := fun lam i => Set.Ico (lam * c i - r i) (lam * c i + r i)
  have hab2 : ∀ i : Fin m, t₂ * c i - r i < t₂ * c i + r i := fun i => by linarith [hr i]
  obtain ⟨n, u, v, hdisj, huv, hunion, hcov⟩ :=
    decompose_ico (fun i => t₂ * c i - r i) (fun i => t₂ * c i + r i) hab2
  let K : Fin n → Set ℝ := fun q => Set.Ico (u q) (v q)
  let S : Fin n → Finset (Fin m) := fun q => Finset.univ.filter (fun i => J t₂ i ⊆ K q)
  have hsub_all : (⋃ i : Fin m, J t₁ i) ⊆ ⋃ q : Fin n, ⋃ i ∈ S q, J t₁ i := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    obtain ⟨q, hq⟩ := hcov i
    exact ⟨q, i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hq⟩, hi⟩
  have hpiece : ∀ q : Fin n, volume (⋃ i ∈ S q, J t₁ i) ≤ volume (K q) := by
    intro q
    by_cases hne : (S q).Nonempty
    · obtain ⟨i0, hi0, hmin⟩ := (S q).exists_min_image (fun i => t₁ * c i - r i) hne
      obtain ⟨j0, hj0, hmax⟩ := (S q).exists_max_image (fun i => t₁ * c i + r i) hne
      have hsub_q : (⋃ i ∈ S q, J t₁ i) ⊆
          Set.Ico (t₁ * c i0 - r i0) (t₁ * c j0 + r j0) := by
        intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨i, hi, hxi⟩ := hx
        exact ⟨le_trans (hmin i hi) hxi.1, lt_of_lt_of_le hxi.2 (hmax i hi)⟩
      have hi0_sub : J t₂ i0 ⊆ K q := (Finset.mem_filter.mp hi0).2
      have hj0_sub : J t₂ j0 ⊆ K q := (Finset.mem_filter.mp hj0).2
      have hi0_l : u q ≤ t₂ * c i0 - r i0 :=
        (hi0_sub ⟨le_rfl, hab2 i0⟩).1
      have hj0_l : u q ≤ t₂ * c j0 - r j0 :=
        (hj0_sub ⟨le_rfl, hab2 j0⟩).1
      have hright_bound : ∀ i : Fin m, J t₂ i ⊆ K q → t₂ * c i + r i ≤ v q := by
        intro i hi_sub
        by_contra hgt
        push Not at hgt
        have hmid_lt : max (t₂ * c i - r i) (v q) < t₂ * c i + r i :=
          max_lt (hab2 i) hgt
        let mid : ℝ := (max (t₂ * c i - r i) (v q) + (t₂ * c i + r i)) / 2
        have hmid_mem : mid ∈ J t₂ i := by
          refine ⟨?_, ?_⟩
          · have : t₂ * c i - r i ≤ max (t₂ * c i - r i) (v q) := le_max_left _ _
            dsimp only [mid]
            linarith
          · dsimp only [mid]
            linarith
        have hmid_lt_vq : mid < v q := (hi_sub hmid_mem).2
        have : v q ≤ max (t₂ * c i - r i) (v q) := le_max_right _ _
        dsimp only [mid] at hmid_lt_vq
        linarith
      have hi0_r : t₂ * c i0 + r i0 ≤ v q := hright_bound i0 hi0_sub
      have hj0_r : t₂ * c j0 + r j0 ≤ v q := hright_bound j0 hj0_sub
      have hlen_le : (t₁ * c j0 + r j0) - (t₁ * c i0 - r i0) ≤ v q - u q := by
        rcases le_total (c i0) (c j0) with hcij | hcji
        · have h1 : t₁ * (c j0 - c i0) ≤ t₂ * (c j0 - c i0) :=
            mul_le_mul_of_nonneg_right ht12 (sub_nonneg.mpr hcij)
          linarith
        · have h1 : t₁ * (c i0 - c j0) ≥ 0 := mul_nonneg ht1 (sub_nonneg.mpr hcji)
          have h2 : t₂ * (c i0 - c j0) ≥ 0 :=
            mul_nonneg (le_trans ht1 ht12) (sub_nonneg.mpr hcji)
          linarith
      calc volume (⋃ i ∈ S q, J t₁ i)
          ≤ volume (Set.Ico (t₁ * c i0 - r i0) (t₁ * c j0 + r j0)) := measure_mono hsub_q
        _ = ENNReal.ofReal ((t₁ * c j0 + r j0) - (t₁ * c i0 - r i0)) := Real.volume_Ico
        _ ≤ ENNReal.ofReal (v q - u q) := ENNReal.ofReal_le_ofReal hlen_le
        _ = volume (K q) := Real.volume_Ico.symm
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  calc volume (⋃ i : Fin m, J t₁ i)
      ≤ volume (⋃ q : Fin n, ⋃ i ∈ S q, J t₁ i) := measure_mono hsub_all
    _ ≤ ∑ q : Fin n, volume (⋃ i ∈ S q, J t₁ i) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ q : Fin n, volume (K q) := Finset.sum_le_sum (fun q _ => hpiece q)
    _ = volume (⋃ q : Fin n, K q) := by
        rw [measure_iUnion hdisj (fun _ => measurableSet_Ico), tsum_fintype]
    _ = volume (⋃ i : Fin m, J t₂ i) := by rw [hunion]

lemma volume_biUnion_center_scale_mono {α : Type*} (S : Finset α) (c r : α → ℝ)
    (hr : ∀ i ∈ S, 0 < r i) {t₁ t₂ : ℝ} (ht1 : 0 ≤ t₁) (ht12 : t₁ ≤ t₂) :
    volume (⋃ i ∈ S, Set.Ico (t₁ * c i - r i) (t₁ * c i + r i)) ≤
      volume (⋃ i ∈ S, Set.Ico (t₂ * c i - r i) (t₂ * c i + r i)) := by
  let e : S ≃ Fin S.card := S.equivFin
  have heq : ∀ lam : ℝ,
      (⋃ i ∈ S, Set.Ico (lam * c i - r i) (lam * c i + r i)) =
        (⋃ j : Fin S.card,
          Set.Ico (lam * c (e.symm j).1 - r (e.symm j).1)
            (lam * c (e.symm j).1 + r (e.symm j).1)) := by
    intro lam
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      refine ⟨e ⟨i, hi⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hx
    · rintro ⟨j, hj⟩
      exact ⟨(e.symm j).1, (e.symm j).2, hj⟩
  rw [heq t₁, heq t₂]
  exact volume_iUnion_center_scale_mono
    (fun j => c (e.symm j).1) (fun j => r (e.symm j).1)
    (fun j => hr (e.symm j).1 (e.symm j).2) ht1 ht12

end UnionMonotonicity

section RealDilation

private lemma volume_biUnion_ico_ne_top {α : Type*} (S : Finset α) (a b : α → ℝ) :
    volume (⋃ i ∈ S, Set.Ico (a i) (b i)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le S (fun i => Set.Ico (a i) (b i)))
  exact ENNReal.sum_ne_top.mpr (fun i _ => by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)

private lemma integrable_indicator_ico_union {α : Type*} (S : Finset α) (a b : α → ℝ) :
    Integrable (Set.indicator (⋃ i ∈ S, Set.Ico (a i) (b i)) (fun _ : ℝ => (1 : ℝ))) := by
  have hm : MeasurableSet (⋃ i ∈ S, Set.Ico (a i) (b i)) :=
    Finset.measurableSet_biUnion S (fun _ _ => measurableSet_Ico)
  rw [integrable_indicator_iff hm]
  exact integrableOn_const (hs := volume_biUnion_ico_ne_top S a b)

private lemma integral_indicator_ico_union {α : Type*} (S : Finset α) (a b : α → ℝ) :
    (∫ x : ℝ, Set.indicator (⋃ i ∈ S, Set.Ico (a i) (b i)) (fun _ : ℝ => (1 : ℝ)) x) =
      (volume (⋃ i ∈ S, Set.Ico (a i) (b i))).toReal := by
  have hm : MeasurableSet (⋃ i ∈ S, Set.Ico (a i) (b i)) :=
    Finset.measurableSet_biUnion S (fun _ _ => measurableSet_Ico)
  rw [MeasureTheory.integral_indicator hm, setIntegral_const, smul_eq_mul, mul_one, Measure.real]

private lemma card_filter_eq_sum_indicator {m : ℕ} (A : Fin m → Set ℝ) (x : ℝ)
    [DecidablePred fun i : Fin m => x ∈ A i] :
    ((Finset.univ.filter (fun i : Fin m => x ∈ A i)).card : ℝ) =
      ∑ i : Fin m, Set.indicator (A i) (fun _ : ℝ => (1 : ℝ)) x := by
  have h1 : ∀ i : Fin m, Set.indicator (A i) (fun _ : ℝ => (1 : ℝ)) x =
      if x ∈ A i then (1 : ℝ) else 0 := fun i => Set.indicator_apply (A i) (fun _ => (1 : ℝ)) x
  simp_rw [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma card_image_col_eq_sum_indicator {m k : ℕ} (A : Fin m → Set ℝ)
    (col : Fin m → Fin k) (x : ℝ) [DecidablePred fun i : Fin m => x ∈ A i] :
    (((Finset.univ.filter (fun i : Fin m => x ∈ A i)).image col).card : ℝ) =
      ∑ c : Fin k,
        Set.indicator (⋃ i ∈ Finset.univ.filter (fun i : Fin m => col i = c), A i)
          (fun _ : ℝ => (1 : ℝ)) x := by
  classical
  have hmem : ∀ c : Fin k,
      (x ∈ ⋃ i ∈ Finset.univ.filter (fun i : Fin m => col i = c), A i) ↔
        c ∈ (Finset.univ.filter (fun i : Fin m => x ∈ A i)).image col := by
    intro c
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨i, rfl, hxi⟩; exact ⟨i, hxi, rfl⟩
    · rintro ⟨i, hxi, rfl⟩; exact ⟨i, rfl, hxi⟩
  have h1 : ∀ c : Fin k,
      Set.indicator (⋃ i ∈ Finset.univ.filter (fun i : Fin m => col i = c), A i)
        (fun _ : ℝ => (1 : ℝ)) x =
        if c ∈ (Finset.univ.filter (fun i : Fin m => x ∈ A i)).image col then (1 : ℝ) else 0 := by
    intro c
    rw [Set.indicator_apply]
    simp only [hmem c]
  simp_rw [h1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

private lemma measurable_count_ico {m : ℕ} (a b : Fin m → ℝ) :
    Measurable (fun x : ℝ =>
      ((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (a i) (b i))).card : ℝ)) := by
  have heq : (fun x : ℝ =>
      ((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (a i) (b i))).card : ℝ)) =
      fun x : ℝ => ∑ i : Fin m, Set.indicator (Set.Ico (a i) (b i)) (fun _ : ℝ => (1 : ℝ)) x := by
    ext x
    exact card_filter_eq_sum_indicator (fun i => Set.Ico (a i) (b i)) x
  rw [heq]
  exact Finset.measurable_sum Finset.univ
    (fun i _ => measurable_const.indicator measurableSet_Ico)

private lemma integrable_count_ico {m : ℕ} (a b : Fin m → ℝ) :
    Integrable (fun x : ℝ =>
      ((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (a i) (b i))).card : ℝ)) := by
  have heq : (fun x : ℝ =>
      ((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (a i) (b i))).card : ℝ)) =
      fun x : ℝ => ∑ i : Fin m, Set.indicator (Set.Ico (a i) (b i)) (fun _ : ℝ => (1 : ℝ)) x := by
    ext x
    exact card_filter_eq_sum_indicator (fun i => Set.Ico (a i) (b i)) x
  rw [heq]
  refine integrable_finsetSum Finset.univ (fun i _ => ?_)
  rw [integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (hs := by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)

private lemma integrable_min_count_ico {m : ℕ} (a b : Fin m → ℝ) (k : ℕ) :
    Integrable (fun x : ℝ =>
      min ((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (a i) (b i))).card : ℝ) (k : ℝ)) := by
  refine (integrable_count_ico a b).mono'
    ((measurable_count_ico a b).min measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  exact min_le_left _ _

private lemma integrable_excess_count_ico {m : ℕ} (a b : Fin m → ℝ) (k : ℕ) :
    Integrable (fun x : ℝ =>
      max (((Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (a i) (b i))).card : ℝ) - (k : ℝ))
        0) := by
  refine (integrable_count_ico a b).mono'
    (((measurable_count_ico a b).sub measurable_const).max measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) (Nat.cast_nonneg _)

/-- Lemma 4.2b (Real dilation inequality). -/
lemma real_dilation_excess_mono {m : ℕ} (c r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (k : ℕ) (hk : 0 < k) {s₁ s₂ : ℝ} (hs1 : 0 < s₁) (hs12 : s₁ ≤ s₂) :
    (1 / s₁) *
        (∫ x : ℝ,
          max (((Finset.univ.filter (fun i : Fin m =>
            x ∈ Set.Ico (c i - s₁ * r i) (c i + s₁ * r i))).card : ℝ) - (k : ℝ)) 0) ≤
      (1 / s₂) *
        (∫ x : ℝ,
          max (((Finset.univ.filter (fun i : Fin m =>
            x ∈ Set.Ico (c i - s₂ * r i) (c i + s₂ * r i))).card : ℝ) - (k : ℝ)) 0) := by
  classical
  let J : ℝ → Fin m → Set ℝ := fun lam i => Set.Ico (lam * c i - r i) (lam * c i + r i)
  let Ntilde : ℝ → ℝ → ℕ := fun lam x =>
    (Finset.univ.filter (fun i : Fin m => x ∈ J lam i)).card
  have hsum_Ntilde : ∀ lam : ℝ, (∫ x : ℝ, (Ntilde lam x : ℝ)) = ∑ i : Fin m, 2 * r i := by
    intro lam
    have heq : (fun x : ℝ => (Ntilde lam x : ℝ)) =
        fun x : ℝ => ∑ i : Fin m, Set.indicator (J lam i) (fun _ : ℝ => (1 : ℝ)) x := by
      ext x
      exact card_filter_eq_sum_indicator (J lam) x
    rw [heq, integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul,
        mul_one, Measure.real, Real.volume_Ico]
      have hdiff : (lam * c i + r i) - (lam * c i - r i) = 2 * r i := by ring
      rw [hdiff, ENNReal.toReal_ofReal (by linarith [hr i])]
    · intro i _
      rw [integrable_indicator_iff measurableSet_Ico]
      exact integrableOn_const (hs := by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hmin_mono : ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ ≤ t₂ →
      (∫ x : ℝ, min (Ntilde t₁ x : ℝ) (k : ℝ)) ≤ (∫ x : ℝ, min (Ntilde t₂ x : ℝ) (k : ℝ)) := by
    intro t₁ t₂ ht1 ht12
    obtain ⟨col, hcol⟩ :=
      greedy_interval_coloring (fun i => t₁ * c i - r i) (fun i => t₁ * c i + r i) hk
    let cls : Fin k → Finset (Fin m) := fun a => Finset.univ.filter (fun i => col i = a)
    have hpt1 : (fun x : ℝ => min (Ntilde t₁ x : ℝ) (k : ℝ)) =
        fun x : ℝ => ∑ a : Fin k,
          Set.indicator (⋃ i ∈ cls a, J t₁ i) (fun _ : ℝ => (1 : ℝ)) x := by
      ext x
      rw [← card_image_col_eq_sum_indicator (J t₁) col x, hcol x, Nat.cast_min]
    have hpt2 : ∀ x : ℝ,
        (∑ a : Fin k, Set.indicator (⋃ i ∈ cls a, J t₂ i) (fun _ : ℝ => (1 : ℝ)) x) ≤
          min (Ntilde t₂ x : ℝ) (k : ℝ) := by
      intro x
      rw [← card_image_col_eq_sum_indicator (J t₂) col x]
      rw [le_min_iff]
      refine ⟨Nat.cast_le.mpr Finset.card_image_le, Nat.cast_le.mpr ?_⟩
      calc ((Finset.univ.filter (fun i : Fin m => x ∈ J t₂ i)).image col).card
          ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
        _ = k := Finset.card_fin k
    have hint1 : ∀ a : Fin k,
        Integrable (Set.indicator (⋃ i ∈ cls a, J t₁ i) (fun _ : ℝ => (1 : ℝ))) :=
      fun a => integrable_indicator_ico_union (cls a) _ _
    have hint2 : ∀ a : Fin k,
        Integrable (Set.indicator (⋃ i ∈ cls a, J t₂ i) (fun _ : ℝ => (1 : ℝ))) :=
      fun a => integrable_indicator_ico_union (cls a) _ _
    calc (∫ x : ℝ, min (Ntilde t₁ x : ℝ) (k : ℝ))
        = ∫ x : ℝ, ∑ a : Fin k,
            Set.indicator (⋃ i ∈ cls a, J t₁ i) (fun _ : ℝ => (1 : ℝ)) x := by rw [hpt1]
      _ = ∑ a : Fin k,
            ∫ x : ℝ, Set.indicator (⋃ i ∈ cls a, J t₁ i) (fun _ : ℝ => (1 : ℝ)) x :=
          integral_finsetSum Finset.univ (fun a _ => hint1 a)
      _ = ∑ a : Fin k, (volume (⋃ i ∈ cls a, J t₁ i)).toReal :=
          Finset.sum_congr rfl (fun a _ => integral_indicator_ico_union (cls a) _ _)
      _ ≤ ∑ a : Fin k, (volume (⋃ i ∈ cls a, J t₂ i)).toReal := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          exact ENNReal.toReal_mono (volume_biUnion_ico_ne_top (cls a) _ _)
            (volume_biUnion_center_scale_mono (cls a) c r (fun i _ => hr i) ht1 ht12)
      _ = ∑ a : Fin k,
            ∫ x : ℝ, Set.indicator (⋃ i ∈ cls a, J t₂ i) (fun _ : ℝ => (1 : ℝ)) x :=
          Finset.sum_congr rfl (fun a _ => (integral_indicator_ico_union (cls a) _ _).symm)
      _ = ∫ x : ℝ, ∑ a : Fin k,
            Set.indicator (⋃ i ∈ cls a, J t₂ i) (fun _ : ℝ => (1 : ℝ)) x :=
          (integral_finsetSum Finset.univ (fun a _ => hint2 a)).symm
      _ ≤ ∫ x : ℝ, min (Ntilde t₂ x : ℝ) (k : ℝ) :=
          integral_mono (integrable_finsetSum Finset.univ (fun a _ => hint2 a))
            (integrable_min_count_ico _ _ k) hpt2
  have hexcess_anti : ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ ≤ t₂ →
      (∫ x : ℝ, max ((Ntilde t₂ x : ℝ) - (k : ℝ)) 0) ≤
        (∫ x : ℝ, max ((Ntilde t₁ x : ℝ) - (k : ℝ)) 0) := by
    intro t₁ t₂ ht1 ht12
    have hsplit : ∀ lam : ℝ,
        (∫ x : ℝ, min (Ntilde lam x : ℝ) (k : ℝ)) +
          (∫ x : ℝ, max ((Ntilde lam x : ℝ) - (k : ℝ)) 0) = ∑ i : Fin m, 2 * r i := by
      intro lam
      rw [← integral_add (integrable_min_count_ico _ _ k) (integrable_excess_count_ico _ _ k)]
      have hpt : (fun x : ℝ => min (Ntilde lam x : ℝ) (k : ℝ) +
          max ((Ntilde lam x : ℝ) - (k : ℝ)) 0) = fun x : ℝ => (Ntilde lam x : ℝ) := by
        ext x
        by_cases hle : (Ntilde lam x : ℝ) ≤ (k : ℝ)
        · rw [min_eq_left hle, max_eq_right (sub_nonpos.mpr hle), add_zero]
        · push Not at hle
          rw [min_eq_right (le_of_lt hle), max_eq_left (sub_nonneg.mpr (le_of_lt hle))]
          ring
      rw [hpt, hsum_Ntilde lam]
    have h1 := hsplit t₁
    have h2 := hsplit t₂
    have hm := hmin_mono ht1 ht12
    linarith
  have hrescale : ∀ {s : ℝ}, 0 < s →
      (1 / s) *
        (∫ x : ℝ,
          max (((Finset.univ.filter (fun i : Fin m =>
            x ∈ Set.Ico (c i - s * r i) (c i + s * r i))).card : ℝ) - (k : ℝ)) 0) =
        ∫ y : ℝ, max ((Ntilde (1 / s) y : ℝ) - (k : ℝ)) 0 := by
    intro s hs
    let f : ℝ → ℝ := fun x =>
      max (((Finset.univ.filter (fun i : Fin m =>
        x ∈ Set.Ico (c i - s * r i) (c i + s * r i))).card : ℝ) - (k : ℝ)) 0
    have hcomp : ∀ y : ℝ, f (s * y) = max ((Ntilde (1 / s) y : ℝ) - (k : ℝ)) 0 := by
      intro y
      have hfilt :
          Finset.univ.filter (fun i : Fin m =>
            s * y ∈ Set.Ico (c i - s * r i) (c i + s * r i)) =
          Finset.univ.filter (fun i : Fin m => y ∈ J (1 / s) i) := by
        ext i
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
        constructor
        · rintro ⟨h1, h2⟩
          constructor
          · have h1' : (c i - s * r i) / s ≤ (s * y) / s := div_le_div_of_nonneg_right h1 hs.le
            have hs0 : s ≠ 0 := hs.ne'
            field_simp [hs0] at h1' ⊢
            linarith
          · have h2' : (s * y) / s < (c i + s * r i) / s := div_lt_div_of_pos_right h2 hs
            have hs0 : s ≠ 0 := hs.ne'
            field_simp [hs0] at h2' ⊢
            linarith
        · rintro ⟨h1, h2⟩
          have hs0 : s ≠ 0 := hs.ne'
          constructor
          · have h1' : s * ((1 / s) * c i - r i) ≤ s * y := mul_le_mul_of_nonneg_left h1 hs.le
            field_simp [hs0] at h1'
            linarith
          · have h2' : s * y < s * ((1 / s) * c i + r i) := mul_lt_mul_of_pos_left h2 hs
            field_simp [hs0] at h2'
            linarith
      simp only [f, Ntilde, hfilt]
    have hmul := Measure.integral_comp_mul_left f s
    rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hs), ← one_div] at hmul
    rw [← hmul]
    exact integral_congr_ae (Filter.Eventually.of_forall hcomp)
  have hs2 : 0 < s₂ := lt_of_lt_of_le hs1 hs12
  rw [hrescale hs1, hrescale hs2]
  have hinv_le : 1 / s₂ ≤ 1 / s₁ := one_div_le_one_div_of_le hs1 hs12
  exact hexcess_anti (by positivity) hinv_le

end RealDilation

section PeriodicLift

private lemma bohrLift_measurableSet (v : ℕ) (δ : ℝ) : MeasurableSet (bohrLift v δ) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ico)

private lemma bohrLift_add_int {v : ℕ} (hv : 0 < v) (δ : ℝ) (x : ℝ) (z : ℤ) :
    x + (z : ℝ) ∈ bohrLift v δ ↔ x ∈ bohrLift v δ := by
  have hv0 : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv.ne'
  simp only [bohrLift, Set.mem_iUnion, Set.mem_Ico]
  constructor
  · rintro ⟨m, h1, h2⟩
    refine ⟨m - z * (v : ℤ), ?_, ?_⟩
    · have heq : (((m - z * (v : ℤ) : ℤ) : ℝ) - δ) / (v : ℝ) =
          ((m : ℝ) - δ) / (v : ℝ) - (z : ℝ) := by
        push_cast
        field_simp [hv0]
        ring
      rw [heq]; linarith
    · have heq : (((m - z * (v : ℤ) : ℤ) : ℝ) + δ) / (v : ℝ) =
          ((m : ℝ) + δ) / (v : ℝ) - (z : ℝ) := by
        push_cast
        field_simp [hv0]
        ring
      rw [heq]; linarith
  · rintro ⟨m, h1, h2⟩
    refine ⟨m + z * (v : ℤ), ?_, ?_⟩
    · have heq : (((m + z * (v : ℤ) : ℤ) : ℝ) - δ) / (v : ℝ) =
          ((m : ℝ) - δ) / (v : ℝ) + (z : ℝ) := by
        push_cast
        field_simp [hv0]
        ring
      rw [heq]; linarith
    · have heq : (((m + z * (v : ℤ) : ℤ) : ℝ) + δ) / (v : ℝ) =
          ((m : ℝ) + δ) / (v : ℝ) + (z : ℝ) := by
        push_cast
        field_simp [hv0]
        ring
      rw [heq]; linarith

private lemma multFunc_add_int {V : Finset ℕ} (hV : ∀ v ∈ V, 0 < v) (δ : ℝ) (x : ℝ) (z : ℤ) :
    multFunc V δ (x + (z : ℝ)) = multFunc V δ x := by
  classical
  simp only [multFunc]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hv, hx⟩; exact ⟨hv, (bohrLift_add_int (hV v hv) δ x z).mp hx⟩
  · rintro ⟨hv, hx⟩; exact ⟨hv, (bohrLift_add_int (hV v hv) δ x z).mpr hx⟩

private lemma multFunc_le_card (V : Finset ℕ) (δ : ℝ) (x : ℝ) :
    multFunc V δ x ≤ V.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

private lemma measurable_multFunc (V : Finset ℕ) (δ : ℝ) :
    Measurable (fun x : ℝ => (multFunc V δ x : ℝ)) := by
  classical
  have heq : (fun x : ℝ => (multFunc V δ x : ℝ)) =
      fun x : ℝ => ∑ v ∈ V, Set.indicator (bohrLift v δ) (fun _ : ℝ => (1 : ℝ)) x := by
    ext x
    simp only [multFunc]
    have h1 : ∀ v : ℕ, Set.indicator (bohrLift v δ) (fun _ : ℝ => (1 : ℝ)) x =
        if x ∈ bohrLift v δ then (1 : ℝ) else 0 :=
      fun v => Set.indicator_apply (bohrLift v δ) (fun _ => (1 : ℝ)) x
    simp_rw [h1]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [heq]
  exact Finset.measurable_sum V (fun v _ => measurable_const.indicator (bohrLift_measurableSet v δ))

private lemma integrableOn_ico_of_measurable_bounded {f : ℝ → ℝ} {a b C : ℝ}
    (hf : Measurable f) (hC : ∀ x, ‖f x‖ ≤ C) :
    IntegrableOn f (Set.Ico a b) := by
  have hvol : volume (Set.Ico a b) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ => max C 0) (integrableOn_const (hs := hvol))
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  exact le_trans (hC x) (le_max_left _ _)

private lemma setIntegral_Ico_int_shift {f : ℝ → ℝ} (hper : ∀ x : ℝ, ∀ z : ℤ, f (x + (z : ℝ)) = f x)
    (c : ℤ) :
    (∫ x in Set.Ico (c : ℝ) ((c : ℝ) + 1), f x) = ∫ x in Set.Ico (0 : ℝ) 1, f x := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ico,
    ← MeasureTheory.integral_indicator measurableSet_Ico,
    ← MeasureTheory.integral_add_right_eq_self (f := Set.indicator (Set.Ico (c : ℝ) ((c : ℝ) + 1)) f)
      (c : ℝ)]
  congr 1
  ext x
  simp only [Set.indicator_apply, Set.mem_Ico]
  have hiff : ((c : ℝ) ≤ x + (c : ℝ) ∧ x + (c : ℝ) < (c : ℝ) + 1) ↔ (0 ≤ x ∧ x < 1) := by
    constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)
  by_cases hx : 0 ≤ x ∧ x < 1
  · rw [if_pos (hiff.mpr hx), if_pos hx, hper x c]
  · rw [if_neg (mt hiff.mp hx), if_neg hx]

private lemma setIntegral_Ico_int_length {f : ℝ → ℝ}
    (hper : ∀ x : ℝ, ∀ z : ℤ, f (x + (z : ℝ)) = f x)
    (hint : ∀ a b : ℝ, IntegrableOn f (Set.Ico a b))
    (a : ℤ) (n : ℕ) :
    (∫ x in Set.Ico (a : ℝ) ((a : ℝ) + (n : ℝ)), f x) =
      (n : ℝ) * ∫ x in Set.Ico (0 : ℝ) 1, f x := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hunion : Set.Ico (a : ℝ) ((a : ℝ) + ((n + 1 : ℕ) : ℝ)) =
        Set.Ico (a : ℝ) ((a : ℝ) + (n : ℝ)) ∪
          Set.Ico ((a : ℝ) + (n : ℝ)) ((a : ℝ) + (n : ℝ) + 1) := by
      ext x
      simp only [Set.mem_Ico, Set.mem_union, Nat.cast_add, Nat.cast_one]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hxn : x < (a : ℝ) + (n : ℝ)
        · exact Or.inl ⟨h1, hxn⟩
        · push Not at hxn
          exact Or.inr ⟨hxn, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, by linarith⟩
        · exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by linarith⟩
    have hdisj : Disjoint (Set.Ico (a : ℝ) ((a : ℝ) + (n : ℝ)))
        (Set.Ico ((a : ℝ) + (n : ℝ)) ((a : ℝ) + (n : ℝ) + 1)) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      linarith [hx1.2, hx2.1]
    rw [hunion, setIntegral_union hdisj measurableSet_Ico (hint _ _) (hint _ _), ih]
    have hshift : (∫ x in Set.Ico ((a : ℝ) + (n : ℝ)) ((a : ℝ) + (n : ℝ) + 1), f x) =
        ∫ x in Set.Ico (0 : ℝ) 1, f x := by
      have hcast : ((a + (n : ℤ) : ℤ) : ℝ) = (a : ℝ) + (n : ℝ) := by push_cast; rfl
      rw [← hcast]
      exact setIntegral_Ico_int_shift hper (a + (n : ℤ))
    rw [hshift]
    push_cast
    ring

private noncomputable def liftIdx (V : Finset ℕ) (L : ℕ) : Finset (ℕ × ℤ) :=
  V.biUnion (fun v =>
    (Finset.Ico (-(L : ℤ) * (v : ℤ)) (((L : ℤ) + 1) * (v : ℤ))).image (fun m => (v, m)))

private lemma mem_liftIdx {V : Finset ℕ} {L : ℕ} {p : ℕ × ℤ} :
    p ∈ liftIdx V L ↔ p.1 ∈ V ∧ -(L : ℤ) * (p.1 : ℤ) ≤ p.2 ∧ p.2 < ((L : ℤ) + 1) * (p.1 : ℤ) := by
  simp only [liftIdx, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨v, hv, m, ⟨h1, h2⟩, rfl⟩
    exact ⟨hv, h1, h2⟩
  · rintro ⟨hv, h1, h2⟩
    exact ⟨p.1, hv, p.2, ⟨h1, h2⟩, rfl⟩

/-- Lemma 4.3 (Periodic lift to [0, 1) for excess multiplicity of bohrLift). -/
lemma periodic_dilation_excess_mono (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
    (k : ℕ) (hk : 0 < k) {δ₀ δ₁ : ℝ} (hδ0 : 0 < δ₀) (hδ01 : δ₀ ≤ δ₁) (hδ1 : δ₁ < 1 / 2) :
    (1 / δ₀) * (∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₀ x : ℝ) - (k : ℝ)) 0) ≤
      (1 / δ₁) * (∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₁ x : ℝ) - (k : ℝ)) 0) := by
  classical
  have hδ0_lt : δ₀ < 1 / 2 := lt_of_le_of_lt hδ01 hδ1
  have hδ1_pos : 0 < δ₁ := lt_of_lt_of_le hδ0 hδ01
  let g : ℝ → ℝ → ℝ := fun δ x => max ((multFunc V δ x : ℝ) - (k : ℝ)) 0
  have hg_per : ∀ δ : ℝ, ∀ x : ℝ, ∀ z : ℤ, g δ (x + (z : ℝ)) = g δ x := by
    intro δ x z
    simp only [g, multFunc_add_int hV δ x z]
  have hg_int : ∀ δ a b : ℝ, IntegrableOn (g δ) (Set.Ico a b) := by
    intro δ a b
    refine integrableOn_ico_of_measurable_bounded (C := (V.card : ℝ)) ?_ ?_
    · exact ((measurable_multFunc V δ).sub measurable_const).max measurable_const
    · intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [Nat.cast_le (α := ℝ).mpr (multFunc_le_card V δ x),
        Nat.cast_nonneg (α := ℝ) k]) (Nat.cast_nonneg _)
  have hmain_L : ∀ L : ℕ, 1 ≤ L →
      ((2 * L - 1 : ℕ) : ℝ) * ((1 / δ₀) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x) ≤
        ((2 * L + 3 : ℕ) : ℝ) * ((1 / δ₁) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x) := by
    intro L hL
    let S : Finset (ℕ × ℤ) := liftIdx V L
    let e : S ≃ Fin S.card := S.equivFin
    let c : Fin S.card → ℝ := fun j => ((e.symm j).1.2 : ℝ) / ((e.symm j).1.1 : ℝ)
    let r : Fin S.card → ℝ := fun j => 1 / ((e.symm j).1.1 : ℝ)
    have hr : ∀ j : Fin S.card, 0 < r j := by
      intro j
      have hv : (e.symm j).1.1 ∈ V := (mem_liftIdx.mp (e.symm j).2).1
      have hpos : (0 : ℝ) < ((e.symm j).1.1 : ℝ) := Nat.cast_pos.mpr (hV _ hv)
      exact one_div_pos.mpr hpos
    have hI_eq : ∀ (δ : ℝ) (j : Fin S.card),
        Set.Ico (c j - δ * r j) (c j + δ * r j) =
          Set.Ico ((((e.symm j).1.2 : ℝ) - δ) / ((e.symm j).1.1 : ℝ))
            ((((e.symm j).1.2 : ℝ) + δ) / ((e.symm j).1.1 : ℝ)) := by
      intro δ j
      have hv : (e.symm j).1.1 ∈ V := (mem_liftIdx.mp (e.symm j).2).1
      have hv0 : ((e.symm j).1.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hV _ hv).ne'
      simp only [c, r]
      congr 1 <;> field_simp [hv0]
    let NL : ℝ → ℝ → ℕ := fun δ x =>
      (Finset.univ.filter (fun j : Fin S.card =>
        x ∈ Set.Ico (c j - δ * r j) (c j + δ * r j))).card
    have hNL_card : ∀ (δ : ℝ) (x : ℝ),
        NL δ x = (S.filter (fun p =>
          x ∈ Set.Ico (((p.2 : ℝ) - δ) / (p.1 : ℝ)) (((p.2 : ℝ) + δ) / (p.1 : ℝ)))).card := by
      intro δ x
      simp only [NL]
      have hbij : Finset.univ.filter (fun j : Fin S.card =>
          x ∈ Set.Ico (c j - δ * r j) (c j + δ * r j)) =
          (S.attach.filter (fun p =>
            x ∈ Set.Ico (((p.1.2 : ℝ) - δ) / (p.1.1 : ℝ))
              (((p.1.2 : ℝ) + δ) / (p.1.1 : ℝ)))).map e.toEmbedding := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Finset.mem_attach, Equiv.toEmbedding_apply, hI_eq δ j]
        constructor
        · intro hj
          exact ⟨e.symm j, hj, e.apply_symm_apply j⟩
        · rintro ⟨p, hp, rfl⟩
          simpa only [Equiv.symm_apply_apply] using hp
      rw [hbij, Finset.card_map]
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hp ⊢
        exact ⟨p.2, hp⟩
      · intro p1 _ p2 _ h
        exact Subtype.ext h
      · intro p hp
        simp only [Finset.mem_filter] at hp
        exact ⟨⟨p, hp.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hp.2⟩, rfl⟩
    have hNL_le : ∀ {δ : ℝ}, 0 < δ → δ < 1 / 2 → ∀ x : ℝ, NL δ x ≤ multFunc V δ x := by
      intro δ hδ_pos hδ_lt x
      rw [hNL_card δ x]
      simp only [multFunc]
      refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro p hp
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp ⊢
        refine ⟨(mem_liftIdx.mp hp.1).1, ?_⟩
        exact Set.mem_iUnion.mpr ⟨p.2, hp.2⟩
      · intro p1 hp1 p2 hp2 hfst
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_Ico] at hp1 hp2
        have hv1 : 0 < p1.1 := hV p1.1 (mem_liftIdx.mp hp1.1).1
        have hv1r : (0 : ℝ) < (p1.1 : ℝ) := Nat.cast_pos.mpr hv1
        have hlt1 : (((p1.2 : ℝ) - δ) / (p1.1 : ℝ)) < (((p2.2 : ℝ) + δ) / (p1.1 : ℝ)) :=
          lt_of_le_of_lt hp1.2.1 (hfst ▸ hp2.2.2)
        have hlt2 : (((p2.2 : ℝ) - δ) / (p1.1 : ℝ)) < (((p1.2 : ℝ) + δ) / (p1.1 : ℝ)) :=
          lt_of_le_of_lt (hfst ▸ hp2.2.1) hp1.2.2
        have h1 : (p1.2 : ℝ) - δ < (p2.2 : ℝ) + δ := by
          have := mul_lt_mul_of_pos_right hlt1 hv1r
          field_simp [hv1r.ne'] at this
          exact this
        have h2 : (p2.2 : ℝ) - δ < (p1.2 : ℝ) + δ := by
          have := mul_lt_mul_of_pos_right hlt2 hv1r
          field_simp [hv1r.ne'] at this
          exact this
        have hm_eq : p1.2 = p2.2 := by
          have hlt1' : (p1.2 : ℝ) < ((p2.2 + 1 : ℤ) : ℝ) := by push_cast; linarith
          have hlt2' : (p2.2 : ℝ) < ((p1.2 + 1 : ℤ) : ℝ) := by push_cast; linarith
          have hi1 : p1.2 < p2.2 + 1 := Int.cast_lt.mp hlt1'
          have hi2 : p2.2 < p1.2 + 1 := Int.cast_lt.mp hlt2'
          omega
        exact Prod.ext hfst hm_eq
    have hNL_eq_in : ∀ {δ : ℝ}, 0 < δ → δ < 1 / 2 →
        ∀ x ∈ Set.Ico (-(L : ℝ) + 1) (L : ℝ), NL δ x = multFunc V δ x := by
      intro δ hδ_pos hδ_lt x hx
      apply le_antisymm (hNL_le hδ_pos hδ_lt x)
      rw [hNL_card δ x]
      simp only [multFunc]
      have hcard_ge : (V.filter (fun v => x ∈ bohrLift v δ)).card ≤
          (S.filter (fun p =>
            x ∈ Set.Ico (((p.2 : ℝ) - δ) / (p.1 : ℝ)) (((p.2 : ℝ) + δ) / (p.1 : ℝ)))).card := by
        have hsurj : V.filter (fun v => x ∈ bohrLift v δ) ⊆
            (S.filter (fun p =>
              x ∈ Set.Ico (((p.2 : ℝ) - δ) / (p.1 : ℝ))
                (((p.2 : ℝ) + δ) / (p.1 : ℝ)))).image Prod.fst := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_image, Prod.exists] at hv ⊢
          obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hv.2
          refine ⟨v, m, ⟨?_, hm⟩, rfl⟩
          rw [mem_liftIdx]
          refine ⟨hv.1, ?_, ?_⟩
          · have hv1 : 1 ≤ v := hV v hv.1
            have hvr : (1 : ℝ) ≤ (v : ℝ) := Nat.one_le_cast.mpr hv1
            have hv0 : (0 : ℝ) < (v : ℝ) := by linarith
            have hx_lt : (-(L : ℝ) + 1) * (v : ℝ) < (m : ℝ) + δ := by
              have h1 : -(L : ℝ) + 1 < ((m : ℝ) + δ) / (v : ℝ) := lt_of_le_of_lt hx.1 hm.2
              have h2 := mul_lt_mul_of_pos_right h1 hv0
              field_simp [hv0.ne'] at h2
              exact h2
            have hgt : ((-(L : ℤ) * (v : ℤ) : ℤ) : ℝ) < (m : ℝ) := by
              push_cast
              nlinarith
            exact le_of_lt (Int.cast_lt.mp hgt)
          · have hv1 : 1 ≤ v := hV v hv.1
            have hvr : (1 : ℝ) ≤ (v : ℝ) := Nat.one_le_cast.mpr hv1
            have hv0 : (0 : ℝ) < (v : ℝ) := by linarith
            have hx_gt : (m : ℝ) - δ < (L : ℝ) * (v : ℝ) := by
              have h1 : ((m : ℝ) - δ) / (v : ℝ) < (L : ℝ) := lt_of_le_of_lt hm.1 hx.2
              have h2 := mul_lt_mul_of_pos_right h1 hv0
              field_simp [hv0.ne'] at h2
              linarith
            have hlt : (m : ℝ) < ((((L : ℤ) + 1) * (v : ℤ) : ℤ) : ℝ) := by
              push_cast
              nlinarith
            exact Int.cast_lt.mp hlt
        exact le_trans (Finset.card_le_card hsurj) Finset.card_image_le
      exact hcard_ge
    have hNL_zero_out : ∀ {δ : ℝ}, 0 < δ → δ < 1 / 2 →
        ∀ x : ℝ, x ∉ Set.Ico (-(L : ℝ) - 1) ((L : ℝ) + 2) → NL δ x = 0 := by
      intro δ hδ_pos hδ_lt x hx
      rw [hNL_card δ x, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp hxp
      apply hx
      obtain ⟨hv, hm1, hm2⟩ := mem_liftIdx.mp hp
      have hv1 : 1 ≤ p.1 := hV p.1 hv
      have hvr : (1 : ℝ) ≤ (p.1 : ℝ) := Nat.one_le_cast.mpr hv1
      have hv0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
      have hm1r : -(L : ℝ) * (p.1 : ℝ) ≤ (p.2 : ℝ) := by
        have := Int.cast_le (R := ℝ).mpr hm1
        push_cast at this
        exact this
      have hm2r : (p.2 : ℝ) < ((L : ℝ) + 1) * (p.1 : ℝ) := by
        have := Int.cast_lt (R := ℝ).mpr hm2
        push_cast at this
        exact this
      constructor
      · have h1 : (-(L : ℝ) - 1) * (p.1 : ℝ) ≤ (p.2 : ℝ) - δ := by nlinarith
        have h2 : -(L : ℝ) - 1 ≤ ((p.2 : ℝ) - δ) / (p.1 : ℝ) := by
          rw [le_div_iff₀ hv0]
          exact h1
        exact le_trans h2 hxp.1
      · have h1 : (p.2 : ℝ) + δ < ((L : ℝ) + 2) * (p.1 : ℝ) := by nlinarith
        have h2 : ((p.2 : ℝ) + δ) / (p.1 : ℝ) < (L : ℝ) + 2 := by
          rw [div_lt_iff₀ hv0]
          exact h1
        exact lt_trans hxp.2 h2
    have hlower : ((2 * L - 1 : ℕ) : ℝ) * (∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x) ≤
        ∫ x : ℝ, max ((NL δ₀ x : ℝ) - (k : ℝ)) 0 := by
      have h1 : (∫ x in Set.Ico (-(L : ℝ) + 1) (L : ℝ), g δ₀ x) =
          ((2 * L - 1 : ℕ) : ℝ) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x := by
        have ha : ((-(L : ℤ) + 1 : ℤ) : ℝ) = -(L : ℝ) + 1 := by push_cast; rfl
        have hb : ((-(L : ℤ) + 1 : ℤ) : ℝ) + ((2 * L - 1 : ℕ) : ℝ) = (L : ℝ) := by
          have h2L : 1 ≤ 2 * L := by omega
          rw [Nat.cast_sub h2L]
          push_cast
          ring
        rw [← ha, ← hb]
        exact setIntegral_Ico_int_length (hg_per δ₀) (hg_int δ₀) (-(L : ℤ) + 1) (2 * L - 1)
      rw [← h1, ← MeasureTheory.integral_indicator measurableSet_Ico]
      refine integral_mono ((integrable_indicator_iff measurableSet_Ico).mpr (hg_int δ₀ _ _))
        (integrable_excess_count_ico _ _ k) (fun x => ?_)
      by_cases hx : x ∈ Set.Ico (-(L : ℝ) + 1) (L : ℝ)
      · rw [Set.indicator_of_mem hx]
        simp only [g, hNL_eq_in hδ0 hδ0_lt x hx, le_refl]
      · rw [Set.indicator_of_notMem hx]
        exact le_max_right _ _
    have hupper : (∫ x : ℝ, max ((NL δ₁ x : ℝ) - (k : ℝ)) 0) ≤
        ((2 * L + 3 : ℕ) : ℝ) * (∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x) := by
      have h1 : (∫ x in Set.Ico (-(L : ℝ) - 1) ((L : ℝ) + 2), g δ₁ x) =
          ((2 * L + 3 : ℕ) : ℝ) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x := by
        have ha : ((-(L : ℤ) - 1 : ℤ) : ℝ) = -(L : ℝ) - 1 := by push_cast; rfl
        have hb : ((-(L : ℤ) - 1 : ℤ) : ℝ) + ((2 * L + 3 : ℕ) : ℝ) = (L : ℝ) + 2 := by
          push_cast
          ring
        rw [← ha, ← hb]
        exact setIntegral_Ico_int_length (hg_per δ₁) (hg_int δ₁) (-(L : ℤ) - 1) (2 * L + 3)
      rw [← h1, ← MeasureTheory.integral_indicator measurableSet_Ico]
      refine integral_mono (integrable_excess_count_ico _ _ k)
        ((integrable_indicator_iff measurableSet_Ico).mpr (hg_int δ₁ _ _)) (fun x => ?_)
      by_cases hx : x ∈ Set.Ico (-(L : ℝ) - 1) ((L : ℝ) + 2)
      · rw [Set.indicator_of_mem hx]
        simp only [g]
        exact max_le_max_right 0
          (sub_le_sub_right (Nat.cast_le.mpr (hNL_le hδ1_pos hδ1 x)) (k : ℝ))
      · rw [Set.indicator_of_notMem hx, hNL_zero_out hδ1_pos hδ1 x hx]
        simp only [Nat.cast_zero, zero_sub]
        exact max_le (neg_nonpos.mpr (Nat.cast_nonneg k)) le_rfl
    have hdil := real_dilation_excess_mono c r hr k hk hδ0 hδ01
    have hmul0 : ((2 * L - 1 : ℕ) : ℝ) * ((1 / δ₀) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x) ≤
        (1 / δ₀) * ∫ x : ℝ, max ((NL δ₀ x : ℝ) - (k : ℝ)) 0 := by
      calc ((2 * L - 1 : ℕ) : ℝ) * ((1 / δ₀) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x)
          = (1 / δ₀) * (((2 * L - 1 : ℕ) : ℝ) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x) := by ring
        _ ≤ (1 / δ₀) * ∫ x : ℝ, max ((NL δ₀ x : ℝ) - (k : ℝ)) 0 :=
            mul_le_mul_of_nonneg_left hlower (by positivity)
    have hmul1 : (1 / δ₁) * ∫ x : ℝ, max ((NL δ₁ x : ℝ) - (k : ℝ)) 0 ≤
        ((2 * L + 3 : ℕ) : ℝ) * ((1 / δ₁) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x) := by
      calc (1 / δ₁) * ∫ x : ℝ, max ((NL δ₁ x : ℝ) - (k : ℝ)) 0
          ≤ (1 / δ₁) * (((2 * L + 3 : ℕ) : ℝ) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x) :=
            mul_le_mul_of_nonneg_left hupper (by positivity)
        _ = ((2 * L + 3 : ℕ) : ℝ) * ((1 / δ₁) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x) := by ring
    exact le_trans hmul0 (le_trans hdil hmul1)
  let A0 : ℝ := (1 / δ₀) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₀ x
  let A1 : ℝ := (1 / δ₁) * ∫ x in Set.Ico (0 : ℝ) 1, g δ₁ x
  by_contra hgt
  push Not at hgt
  have hdiff : 0 < A0 - A1 := sub_pos.mpr hgt
  obtain ⟨N, hN⟩ := exists_nat_gt ((A0 + 3 * A1) / (2 * (A0 - A1)))
  let L : ℕ := max N 1
  have hL1 : 1 ≤ L := le_max_right N 1
  have hLN : (N : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr (le_max_left N 1)
  have hineq := hmain_L L hL1
  have h2L : 1 ≤ 2 * L := by omega
  rw [Nat.cast_sub h2L] at hineq
  push_cast at hineq
  have hmul_N : (A0 + 3 * A1) < (L : ℝ) * (2 * (A0 - A1)) := by
    have hlt1 : (A0 + 3 * A1) / (2 * (A0 - A1)) < (L : ℝ) := lt_of_lt_of_le hN hLN
    have h2pos : 0 < 2 * (A0 - A1) := by linarith
    exact (div_lt_iff₀ h2pos).mp hlt1
  linarith

end PeriodicLift

section MainTheorem

private lemma layer_cake_nat_identity :
    ∀ (a n : ℕ), a ≤ n →
      (a : ℝ) * ((a : ℝ) - 1) - 2 * max ((a : ℝ) - 1) 0 =
        2 * ∑ k ∈ Finset.Ico 2 n, max ((a : ℝ) - (k : ℝ)) 0 := by
  intro a
  induction a with
  | zero =>
    intro n _
    have hsum : ∑ k ∈ Finset.Ico 2 n, max ((0 : ℝ) - (k : ℝ)) 0 = 0 :=
      Finset.sum_eq_zero (fun k _ => max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) k]))
    simp only [Nat.cast_zero]
    rw [hsum]
    simp
  | succ a ih =>
    intro n han
    cases a with
    | zero =>
      have hsum : ∑ k ∈ Finset.Ico 2 n, max ((1 : ℝ) - (k : ℝ)) 0 = 0 := by
        refine Finset.sum_eq_zero (fun k hk => ?_)
        have hk2 : (2 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr (Finset.mem_Ico.mp hk).1
        exact max_eq_right (by linarith)
      simp [hsum]
    | succ a =>
      have hprev := ih n (by omega)
      have ha1 : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) a]
      have ha2 : (1 : ℝ) ≤ ((a + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) a]
      have hdiff_sum :
          (∑ k ∈ Finset.Ico 2 n, max (((a + 2 : ℕ) : ℝ) - (k : ℝ)) 0) -
            (∑ k ∈ Finset.Ico 2 n, max (((a + 1 : ℕ) : ℝ) - (k : ℝ)) 0) = (a : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        have hterm : ∀ k ∈ Finset.Ico 2 n,
            max (((a + 2 : ℕ) : ℝ) - (k : ℝ)) 0 - max (((a + 1 : ℕ) : ℝ) - (k : ℝ)) 0 =
              if k < a + 2 then (1 : ℝ) else 0 := by
          intro k _
          by_cases hlt : k < a + 2
          · rw [if_pos hlt]
            have hle1 : (k : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
            have hle2 : (k : ℝ) ≤ ((a + 2 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
            rw [max_eq_left (sub_nonneg.mpr hle2), max_eq_left (sub_nonneg.mpr hle1)]
            push_cast
            ring
          · rw [if_neg hlt]
            have hge2 : ((a + 2 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (by omega)
            have hge1 : ((a + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (by omega)
            rw [max_eq_right (sub_nonpos.mpr hge2), max_eq_right (sub_nonpos.mpr hge1), sub_self]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        have hfilt : (Finset.Ico 2 n).filter (fun k => k < a + 2) = Finset.Ico 2 (a + 2) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_Ico]
          omega
        rw [hfilt, Nat.card_Ico]
        have : a + 2 - 2 = a := by omega
        rw [this]
      rw [max_eq_left (sub_nonneg.mpr ha2)]
      rw [max_eq_left (sub_nonneg.mpr ha1)] at hprev
      have hcast2 : ((a + 1 + 1 : ℕ) : ℝ) = ((a + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast2]
      push_cast at hprev hdiff_sum ⊢
      linarith

theorem dilation_spillover (V : Finset ℕ) (hV : ∀ v ∈ V, 0 < v)
    {δ₀ δ₁ : ℝ} (hδ0 : 0 < δ₀) (hδ01 : δ₀ ≤ δ₁) (hδ1 : δ₁ < 1 / 2) :
    (δ₁ / δ₀) * (pVol V δ₀ - 2 * wVol V δ₀) ≤ pVol V δ₁ - 2 * wVol V δ₁ := by
  have hδ1_pos : 0 < δ₁ := lt_of_lt_of_le hδ0 hδ01
  let n : ℕ := V.card
  have hdecomp : ∀ δ : ℝ,
      pVol V δ - 2 * wVol V δ =
        2 * ∑ k ∈ Finset.Ico 2 n,
          ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ x : ℝ) - (k : ℝ)) 0 := by
    intro δ
    have hp_int : IntegrableOn
        (fun x : ℝ => (multFunc V δ x : ℝ) * ((multFunc V δ x : ℝ) - 1)) (Set.Ico (0 : ℝ) 1) := by
      refine integrableOn_ico_of_measurable_bounded (C := (n : ℝ) * ((n : ℝ) + 1)) ?_ ?_
      · exact (measurable_multFunc V δ).mul ((measurable_multFunc V δ).sub measurable_const)
      · intro x
        have hm : (multFunc V δ x : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (multFunc_le_card V δ x)
        have h0 : (0 : ℝ) ≤ (multFunc V δ x : ℝ) := Nat.cast_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
        have hsub : |(multFunc V δ x : ℝ) - 1| ≤ (n : ℝ) + 1 := by
          rw [abs_le]
          constructor <;> linarith
        exact mul_le_mul hm hsub (abs_nonneg _) (Nat.cast_nonneg _)
    have hw_int : IntegrableOn
        (fun x : ℝ => max ((multFunc V δ x : ℝ) - 1) 0) (Set.Ico (0 : ℝ) 1) := by
      refine integrableOn_ico_of_measurable_bounded (C := (n : ℝ)) ?_ ?_
      · exact ((measurable_multFunc V δ).sub measurable_const).max measurable_const
      · intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [Nat.cast_le (α := ℝ).mpr (multFunc_le_card V δ x)])
          (Nat.cast_nonneg _)
    have hk_int : ∀ k : ℕ, IntegrableOn
        (fun x : ℝ => max ((multFunc V δ x : ℝ) - (k : ℝ)) 0) (Set.Ico (0 : ℝ) 1) := by
      intro k
      refine integrableOn_ico_of_measurable_bounded (C := (n : ℝ)) ?_ ?_
      · exact ((measurable_multFunc V δ).sub measurable_const).max measurable_const
      · intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [Nat.cast_le (α := ℝ).mpr (multFunc_le_card V δ x),
          Nat.cast_nonneg (α := ℝ) k]) (Nat.cast_nonneg _)
    unfold pVol wVol
    rw [← integral_const_mul, ← integral_sub hp_int (hw_int.const_mul 2)]
    have hpt : (fun x : ℝ =>
        (multFunc V δ x : ℝ) * ((multFunc V δ x : ℝ) - 1) -
          2 * max ((multFunc V δ x : ℝ) - 1) 0) =
        fun x : ℝ =>
          2 * ∑ k ∈ Finset.Ico 2 n, max ((multFunc V δ x : ℝ) - (k : ℝ)) 0 := by
      ext x
      exact layer_cake_nat_identity (multFunc V δ x) n (multFunc_le_card V δ x)
    rw [hpt, integral_const_mul, integral_finsetSum _ (fun k _ => hk_int k)]
  rw [hdecomp δ₀, hdecomp δ₁]
  have hsum :
      (δ₁ / δ₀) *
          (∑ k ∈ Finset.Ico 2 n,
            ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₀ x : ℝ) - (k : ℝ)) 0) ≤
        ∑ k ∈ Finset.Ico 2 n,
          ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₁ x : ℝ) - (k : ℝ)) 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk_pos : 0 < k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    have hper := periodic_dilation_excess_mono V hV k hk_pos hδ0 hδ01 hδ1
    have hmul := mul_le_mul_of_nonneg_left hper hδ1_pos.le
    have h1 : δ₁ * ((1 / δ₀) * ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₀ x : ℝ) - (k : ℝ)) 0) =
        (δ₁ / δ₀) * ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₀ x : ℝ) - (k : ℝ)) 0 := by
      ring
    have h2 : δ₁ * ((1 / δ₁) * ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₁ x : ℝ) - (k : ℝ)) 0) =
        ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ₁ x : ℝ) - (k : ℝ)) 0 := by
      field_simp [hδ1_pos.ne']
    linarith
  linarith

end MainTheorem

end LRMod2

/-!
Module 3 of the Hu-Jing proof of Tao's 2017 theorem on the Lonely Runner Conjecture.

This file proves:
1. Single Bohr set measure and base identities for multiplicity, uncovered measure, excess
   multiplicity, and pair overlaps (Section 3.1, Lemma 3.1).
2. Type I loss bound `typeILoss V (1 / (2 * V.card)) ≤ gVol V (1 / (2 * V.card))`.
3. Type II pair intersection bounds (Section 3.2, Lemma 3.3).
4. Main assembly `tao_2017_of_inputs` combining the arithmetic theorem (Module 1) and the
   dilation spillover inequality (Module 2) to prove Tao's 2017 Lonely Runner theorem.
-/

namespace LRMod3

open MeasureTheory Set Filter
open scoped BigOperators

/- ### Core definitions (shared with Modules 1 and 2) -/

def bohrLift (v : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ m : ℤ, Set.Ico (((m : ℝ) - δ) / (v : ℝ)) (((m : ℝ) + δ) / (v : ℝ))

noncomputable def multFunc (V : Finset ℕ) (δ : ℝ) (x : ℝ) : ℕ := by
  classical
  exact (V.filter (fun v => x ∈ bohrLift v δ)).card

noncomputable def gVol (V : Finset ℕ) (δ : ℝ) : ℝ :=
  MeasureTheory.volume.real {x ∈ Set.Ico (0 : ℝ) 1 | multFunc V δ x = 0}

noncomputable def wVol (V : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, max ((multFunc V δ x : ℝ) - 1) 0

noncomputable def pVol (V : Finset ℕ) (δ : ℝ) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, (multFunc V δ x : ℝ) * ((multFunc V δ x : ℝ) - 1)

noncomputable def typeILoss (V : Finset ℕ) (δ : ℝ) : ℝ := by
  classical
  exact 2 * δ * ∑ q ∈ V.biUnion Nat.divisors, (Nat.totient q : ℝ) *
    ((∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
      if h : (V.filter (q ∣ ·)).Nonempty then (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ) else 0)

/- ### Section 1: Bohr cells and single Bohr set measure -/

def bohrCell (v : ℕ) (δ : ℝ) (m : ℤ) : Set ℝ :=
  Set.Ico (((m : ℝ) - δ) / (v : ℝ)) (((m : ℝ) + δ) / (v : ℝ))

lemma bohrLift_eq_iUnion (v : ℕ) (δ : ℝ) :
    bohrLift v δ = ⋃ m : ℤ, bohrCell v δ m := rfl

lemma measurableSet_bohrCell (v : ℕ) (δ : ℝ) (m : ℤ) :
    MeasurableSet (bohrCell v δ m) :=
  measurableSet_Ico

lemma measurableSet_bohrLift (v : ℕ) (δ : ℝ) :
    MeasurableSet (bohrLift v δ) :=
  MeasurableSet.iUnion fun _ => measurableSet_Ico

lemma mem_bohrCell_iff {v : ℕ} (hv : 0 < v) {δ : ℝ} {m : ℤ} {x : ℝ} :
    x ∈ bohrCell v δ m ↔ (m : ℝ) - δ ≤ (v : ℝ) * x ∧ (v : ℝ) * x < (m : ℝ) + δ := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  simp only [bohrCell, mem_Ico, div_le_iff₀ hvR, lt_div_iff₀ hvR, mul_comm x (v : ℝ)]

lemma bohrCell_mono {v : ℕ} (hv : 0 < v) {δ₀ δ₁ : ℝ} (hδ : δ₀ ≤ δ₁) (m : ℤ) :
    bohrCell v δ₀ m ⊆ bohrCell v δ₁ m := by
  intro x hx
  rw [mem_bohrCell_iff hv] at hx ⊢
  exact ⟨by linarith, by linarith⟩

lemma bohrLift_mono {v : ℕ} (hv : 0 < v) {δ₀ δ₁ : ℝ} (hδ : δ₀ ≤ δ₁) :
    bohrLift v δ₀ ⊆ bohrLift v δ₁ :=
  iUnion_mono fun m => bohrCell_mono hv hδ m

lemma bohrCell_pairwiseDisjoint {v : ℕ} (hv : 0 < v) {δ : ℝ} (hδ : δ < 1 / 2) :
    Pairwise fun m₁ m₂ => Disjoint (bohrCell v δ m₁) (bohrCell v δ m₂) := by
  intro m₁ m₂ hne
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rw [mem_bohrCell_iff hv] at hx₁ hx₂
  have h1 : ((m₁ - m₂ : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h2 : ((m₂ - m₁ : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h1' : m₁ - m₂ < 1 := by exact_mod_cast h1
  have h2' : m₂ - m₁ < 1 := by exact_mod_cast h2
  omega

lemma mem_bohrCell_add_int {v : ℕ} (hv : 0 < v) {δ : ℝ} {m k : ℤ} {x : ℝ} :
    x + (k : ℝ) ∈ bohrCell v δ (m + (v : ℤ) * k) ↔ x ∈ bohrCell v δ m := by
  rw [mem_bohrCell_iff hv, mem_bohrCell_iff hv]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma mem_bohrLift_add_int {v : ℕ} (hv : 0 < v) {δ : ℝ} (k : ℤ) {x : ℝ} :
    x + (k : ℝ) ∈ bohrLift v δ ↔ x ∈ bohrLift v δ := by
  simp only [bohrLift_eq_iUnion, mem_iUnion]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m - (v : ℤ) * k, ?_⟩
    have hm' : x + (k : ℝ) ∈ bohrCell v δ ((m - (v : ℤ) * k) + (v : ℤ) * k) := by
      simpa using hm
    exact (mem_bohrCell_add_int hv).mp hm'
  · rintro ⟨m, hm⟩
    exact ⟨m + (v : ℤ) * k, (mem_bohrCell_add_int hv).mpr hm⟩

lemma mem_bohrLift_mul {d u : ℕ} (hd : 0 < d) (hu : 0 < u) {δ : ℝ} {x : ℝ} :
    x ∈ bohrLift (d * u) δ ↔ (d : ℝ) * x ∈ bohrLift u δ := by
  have hdu : 0 < d * u := Nat.mul_pos hd hu
  simp only [bohrLift_eq_iUnion, mem_iUnion, mem_bohrCell_iff hdu, mem_bohrCell_iff hu]
  have hmul : ((d * u : ℕ) : ℝ) * x = (u : ℝ) * ((d : ℝ) * x) := by push_cast; ring
  simp only [hmul]

lemma volume_real_Ico_eq {a b : ℝ} (hab : a ≤ b) :
    volume.real (Set.Ico a b) = b - a := by
  simp [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

def wrappedCell (v : ℕ) (δ : ℝ) (a : ℕ) : Set ℝ :=
  if a = 0 then
    Set.Ico 0 (δ / (v : ℝ)) ∪ Set.Ico (1 - δ / (v : ℝ)) 1
  else
    Set.Ico (((a : ℝ) - δ) / (v : ℝ)) (((a : ℝ) + δ) / (v : ℝ))

lemma measurableSet_wrappedCell (v : ℕ) (δ : ℝ) (a : ℕ) :
    MeasurableSet (wrappedCell v δ a) := by
  unfold wrappedCell
  split_ifs
  · exact measurableSet_Ico.union measurableSet_Ico
  · exact measurableSet_Ico

lemma Ico_inter_bohrLift_eq_biUnion_wrappedCell {v : ℕ} (hv : 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ = ⋃ a ∈ Finset.range v, wrappedCell v δ a := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  ext x
  simp only [mem_inter_iff, mem_Ico, bohrLift_eq_iUnion, mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, m, hm⟩
    rw [mem_bohrCell_iff hv] at hm
    have hvx0 : 0 ≤ (v : ℝ) * x := mul_nonneg hvR.le hx0
    have hvx1 : (v : ℝ) * x < (v : ℝ) := (mul_lt_iff_lt_one_right hvR).mpr hx1
    have hm_gt : (-1 : ℝ) < (m : ℝ) := by linarith
    have hm_lt : (m : ℝ) < (v : ℝ) + 1 := by linarith
    have hm_ge : (0 : ℤ) ≤ m := by
      have : (-1 : ℤ) < m := by exact_mod_cast hm_gt
      omega
    have hm_le : m ≤ (v : ℤ) := by
      have : m < (v : ℤ) + 1 := by exact_mod_cast hm_lt
      omega
    by_cases hm0 : m = 0
    · refine ⟨0, hv, ?_⟩
      simp only [wrappedCell, ↓reduceIte, mem_union, mem_Ico]
      left
      refine ⟨hx0, (lt_div_iff₀ hvR).mpr ?_⟩
      subst hm0; simp at hm; linarith
    · by_cases hmv : m = (v : ℤ)
      · refine ⟨0, hv, ?_⟩
        simp only [wrappedCell, ↓reduceIte, mem_union, mem_Ico]
        right
        refine ⟨?_, hx1⟩
        have h1 : (v : ℝ) - δ ≤ (v : ℝ) * x := by subst hmv; push_cast at hm; linarith
        have h2 : 1 - x ≤ δ / (v : ℝ) := by rw [le_div_iff₀ hvR]; linarith
        linarith
      · have hpos : 0 < m := lt_of_le_of_ne hm_ge (Ne.symm hm0)
        have hltv : m < (v : ℤ) := lt_of_le_of_ne hm_le hmv
        refine ⟨m.toNat, by omega, ?_⟩
        have hne : m.toNat ≠ 0 := by omega
        have hcast : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm_ge
        simp only [wrappedCell, hne, ↓reduceIte, mem_Ico, hcast, div_le_iff₀ hvR, lt_div_iff₀ hvR]
        exact ⟨by linarith, by linarith⟩
  · rintro ⟨a, ha, hxa⟩
    unfold wrappedCell at hxa
    split_ifs at hxa with ha0
    · rcases hxa with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : (v : ℝ) * x < δ := by rwa [lt_div_iff₀ hvR, mul_comm] at h2
        have hdv : δ / (v : ℝ) < 1 := (div_lt_one hvR).mpr (by linarith)
        refine ⟨⟨h1, h2.trans hdv⟩, 0, ?_⟩
        rw [mem_bohrCell_iff hv]
        simp; exact ⟨by linarith [mul_nonneg hvR.le h1], h2'⟩
      · have h1' : (v : ℝ) - δ ≤ (v : ℝ) * x := by
          have : 1 - x ≤ δ / (v : ℝ) := by linarith
          rw [le_div_iff₀ hvR] at this
          linarith
        have hdv : δ / (v : ℝ) < 1 := (div_lt_one hvR).mpr (by linarith)
        refine ⟨⟨by linarith, h2⟩, (v : ℤ), ?_⟩
        rw [mem_bohrCell_iff hv]
        push_cast
        have hvx : (v : ℝ) * x < (v : ℝ) := (mul_lt_iff_lt_one_right hvR).mpr h2
        exact ⟨h1', by linarith only [hvx, hδ0]⟩
    · have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast Nat.pos_of_ne_zero ha0
      have hav : (a : ℝ) ≤ (v : ℝ) - 1 := by
        have : a + 1 ≤ v := ha
        have : (a : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast this
        linarith
      rcases hxa with ⟨h1, h2⟩
      have hx0 : 0 ≤ x := by
        have : 0 ≤ ((a : ℝ) - δ) / (v : ℝ) := div_nonneg (by linarith) hvR.le
        linarith
      have hx1 : x < 1 := by
        have : ((a : ℝ) + δ) / (v : ℝ) < 1 := (div_lt_one hvR).mpr (by linarith)
        linarith
      refine ⟨⟨hx0, hx1⟩, (a : ℤ), ?_⟩
      rw [mem_bohrCell_iff hv]
      rw [div_le_iff₀ hvR, mul_comm] at h1
      rw [lt_div_iff₀ hvR, mul_comm] at h2
      exact ⟨by push_cast; exact h1, by push_cast; exact h2⟩

lemma wrappedCell_pairwiseDisjoint {v : ℕ} (hv : 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    (Finset.range v : Set ℕ).PairwiseDisjoint (wrappedCell v δ) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hsub0 : wrappedCell v δ 0 ⊆ bohrCell v δ 0 ∪ bohrCell v δ (v : ℤ) := by
    intro x hx
    simp only [wrappedCell, ↓reduceIte, mem_union, mem_Ico] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [mem_bohrCell_iff hv]
      rw [lt_div_iff₀ hvR, mul_comm] at h2
      exact ⟨by simp; linarith [mul_nonneg hvR.le h1], by simp; exact h2⟩
    · right
      rw [mem_bohrCell_iff hv]
      have : 1 - x ≤ δ / (v : ℝ) := by linarith
      rw [le_div_iff₀ hvR] at this
      push_cast
      have hvx : (v : ℝ) * x < (v : ℝ) := (mul_lt_iff_lt_one_right hvR).mpr h2
      exact ⟨by linarith only [this], by linarith only [hvx, hδ0]⟩
  have hsubPos : ∀ a ≠ 0, wrappedCell v δ a = bohrCell v δ (a : ℤ) := by
    intro a ha
    simp [wrappedCell, ha, bohrCell]
  have hpd := bohrCell_pairwiseDisjoint hv hδ
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  rw [Function.onFun]
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := hab.symm
    rw [hsubPos b hb0]
    refine Disjoint.mono_left hsub0 ?_
    rw [disjoint_union_left]
    exact ⟨hpd (by omega), hpd (by omega)⟩
  · by_cases hb0 : b = 0
    · subst hb0
      rw [hsubPos a ha0]
      refine Disjoint.mono_right hsub0 ?_
      rw [disjoint_union_right]
      exact ⟨hpd (by omega), hpd (by omega)⟩
    · rw [hsubPos a ha0, hsubPos b hb0]
      exact hpd (by exact_mod_cast hab)

lemma volume_real_wrappedCell {v : ℕ} (hv : 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (a : ℕ) :
    volume.real (wrappedCell v δ a) = 2 * δ / (v : ℝ) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  unfold wrappedCell
  split_ifs with ha0
  · have hdisj : Disjoint (Set.Ico (0 : ℝ) (δ / (v : ℝ))) (Set.Ico (1 - δ / (v : ℝ)) 1) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have hdv : δ / (v : ℝ) < 1 / 2 := by
        calc δ / (v : ℝ) ≤ δ / 1 := div_le_div_of_nonneg_left hδ0.le one_pos hv1
          _ = δ := div_one δ
          _ < 1 / 2 := hδ
      linarith [hx1.2, hx2.1]
    have hfin1 : volume (Set.Ico (0 : ℝ) (δ / (v : ℝ))) ≠ ⊤ := by simp [Real.volume_Ico]
    have hfin2 : volume (Set.Ico (1 - δ / (v : ℝ)) 1) ≠ ⊤ := by simp [Real.volume_Ico]
    rw [measureReal_union hdisj measurableSet_Ico hfin1 hfin2]
    rw [volume_real_Ico_eq (by positivity), volume_real_Ico_eq (by linarith [div_pos hδ0 hvR])]
    ring
  · have hle : ((a : ℝ) - δ) / (v : ℝ) ≤ ((a : ℝ) + δ) / (v : ℝ) := by
      apply div_le_div_of_nonneg_right _ hvR.le
      linarith
    rw [volume_real_Ico_eq hle]
    ring

lemma volume_real_Ico_inter_bohrLift {v : ℕ} (hv : 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    volume.real (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) = 2 * δ := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [Ico_inter_bohrLift_eq_biUnion_wrappedCell hv hδ0 hδ]
  rw [measureReal_biUnion_finset (wrappedCell_pairwiseDisjoint hv hδ0 hδ)
    (fun a _ => measurableSet_wrappedCell v δ a)
    (fun a _ => by
      unfold wrappedCell
      split_ifs
      · exact (measure_union_le _ _).trans_lt (by simp [Real.volume_Ico]) |>.ne
      · simp [Real.volume_Ico])]
  calc
    ∑ a ∈ Finset.range v, volume.real (wrappedCell v δ a)
        = ∑ _a ∈ Finset.range v, (2 * δ / (v : ℝ)) :=
      Finset.sum_congr rfl fun a _ => volume_real_wrappedCell hv hδ0 hδ a
    _ = (v : ℝ) * (2 * δ / (v : ℝ)) := by simp
    _ = 2 * δ := by field_simp

/- ### Section 2: Base identities and Type I loss bound (Section 3.1) -/

lemma multFunc_eq_sum_indicator (V : Finset ℕ) (δ : ℝ) (x : ℝ) :
    (multFunc V δ x : ℝ) = ∑ v ∈ V, (bohrLift v δ).indicator (fun _ => (1 : ℝ)) x := by
  classical
  unfold multFunc
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hx : x ∈ bohrLift v δ <;> simp [hx]

lemma setIntegral_indicator_one_Ico {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in Set.Ico (0 : ℝ) 1, s.indicator (fun _ => (1 : ℝ)) x =
      volume.real (Set.Ico (0 : ℝ) 1 ∩ s) := by
  have h1 : (fun x => s.indicator (fun _ => (1 : ℝ)) x) = s.indicator (1 : ℝ → ℝ) := rfl
  rw [h1, integral_indicator_one hs]
  simp only [Measure.real, Measure.restrict_apply hs, Set.inter_comm]

lemma integrableOn_indicator_one_Ico {s : Set ℝ} (hs : MeasurableSet s) :
    IntegrableOn (s.indicator (fun _ => (1 : ℝ))) (Set.Ico (0 : ℝ) 1) volume := by
  have : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    simp [Real.volume_Ico]
  exact (integrable_const (1 : ℝ)).indicator hs

lemma zero_multFunc_eq_compl_biUnion (V : Finset ℕ) (δ : ℝ) :
    {x : ℝ | multFunc V δ x = 0} = (⋃ v ∈ V, bohrLift v δ)ᶜ := by
  classical
  ext x
  simp only [mem_ofPred_eq, multFunc, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    mem_compl_iff, mem_iUnion, not_exists]

lemma measurableSet_zero_multFunc (V : Finset ℕ) (δ : ℝ) :
    MeasurableSet {x : ℝ | multFunc V δ x = 0} := by
  rw [zero_multFunc_eq_compl_biUnion]
  exact (Finset.measurableSet_biUnion V fun v _ => measurableSet_bohrLift v δ).compl

lemma gVol_eq_one_sub_union (V : Finset ℕ) (δ : ℝ) :
    gVol V δ = 1 - volume.real (Set.Ico (0 : ℝ) 1 ∩ ⋃ v ∈ V, bohrLift v δ) := by
  unfold gVol
  have hset : {x ∈ Set.Ico (0 : ℝ) 1 | multFunc V δ x = 0} =
      Set.Ico (0 : ℝ) 1 \ (Set.Ico (0 : ℝ) 1 ∩ ⋃ v ∈ V, bohrLift v δ) := by
    ext x
    have := Set.ext_iff.mp (zero_multFunc_eq_compl_biUnion V δ) x
    simp only [mem_ofPred_eq, mem_compl_iff] at this
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff, this]
    tauto
  rw [hset]
  have hm : MeasurableSet (Set.Ico (0 : ℝ) 1 ∩ ⋃ v ∈ V, bohrLift v δ) :=
    measurableSet_Ico.inter (Finset.measurableSet_biUnion V fun v _ => measurableSet_bohrLift v δ)
  have hfin : volume (Set.Ico (0 : ℝ) 1) ≠ ⊤ := by simp [Real.volume_Ico]
  rw [measureReal_sdiff (μ := volume) inter_subset_left hm hfin,
    volume_real_Ico_eq (by norm_num : (0 : ℝ) ≤ 1)]
  ring

lemma setIntegral_multFunc {V : Finset ℕ} (hV : ∀ v ∈ V, 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∫ x in Set.Ico (0 : ℝ) 1, (multFunc V δ x : ℝ) = 2 * δ * (V.card : ℝ) := by
  have hfun : (fun x => (multFunc V δ x : ℝ)) =
      fun x => ∑ v ∈ V, (bohrLift v δ).indicator (fun _ => (1 : ℝ)) x := by
    ext x; exact multFunc_eq_sum_indicator V δ x
  rw [hfun, integral_finsetSum V (fun v _ => integrableOn_indicator_one_Ico (measurableSet_bohrLift v δ))]
  calc
    ∑ v ∈ V, ∫ x in Set.Ico (0 : ℝ) 1, (bohrLift v δ).indicator (fun _ => (1 : ℝ)) x
        = ∑ v ∈ V, volume.real (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) :=
      Finset.sum_congr rfl fun v _ => setIntegral_indicator_one_Ico (measurableSet_bohrLift v δ)
    _ = ∑ _v ∈ V, (2 * δ) :=
      Finset.sum_congr rfl fun v hv => volume_real_Ico_inter_bohrLift (hV v hv) hδ0 hδ
    _ = 2 * δ * (V.card : ℝ) := by simp [mul_comm]

lemma wVol_eq {V : Finset ℕ} (hV : ∀ v ∈ V, 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    wVol V δ = 2 * δ * (V.card : ℝ) - 1 + gVol V δ := by
  have : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    simp [Real.volume_Ico]
  let Z : Set ℝ := {x : ℝ | multFunc V δ x = 0}
  have hZm : MeasurableSet Z := measurableSet_zero_multFunc V δ
  have hpt : ∀ x : ℝ, max ((multFunc V δ x : ℝ) - 1) 0 =
      ((multFunc V δ x : ℝ) - (1 : ℝ)) + Z.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : multFunc V δ x = 0
    · have hxZ : x ∈ Z := hx
      simp [hx, hxZ]
    · have hxZ : x ∉ Z := hx
      have hge : (1 : ℝ) ≤ (multFunc V δ x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hx
      simp [hxZ, max_eq_left (sub_nonneg.mpr hge)]
  have hintM : IntegrableOn (fun x => (multFunc V δ x : ℝ)) (Set.Ico (0 : ℝ) 1) volume := by
    have hfun : (fun x => (multFunc V δ x : ℝ)) =
        fun x => ∑ v ∈ V, (bohrLift v δ).indicator (fun _ => (1 : ℝ)) x := by
      ext x; exact multFunc_eq_sum_indicator V δ x
    rw [hfun]
    exact integrable_finsetSum V fun v _ => integrableOn_indicator_one_Ico (measurableSet_bohrLift v δ)
  have hint1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ico (0 : ℝ) 1) volume :=
    integrable_const (1 : ℝ)
  have hintM1 : IntegrableOn (fun x => (multFunc V δ x : ℝ) - (1 : ℝ)) (Set.Ico (0 : ℝ) 1) volume :=
    hintM.sub hint1
  have hintZ : IntegrableOn (Z.indicator (fun _ => (1 : ℝ))) (Set.Ico (0 : ℝ) 1) volume :=
    integrableOn_indicator_one_Ico hZm
  unfold wVol
  simp_rw [hpt]
  rw [integral_add hintM1 hintZ, integral_sub hintM hint1]
  rw [setIntegral_multFunc hV hδ0 hδ, setIntegral_const, setIntegral_indicator_one_Ico hZm]
  rw [volume_real_Ico_eq (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [smul_eq_mul, mul_one, sub_zero]
  have hZeq : Set.Ico (0 : ℝ) 1 ∩ Z = {x ∈ Set.Ico (0 : ℝ) 1 | multFunc V δ x = 0} := rfl
  rw [hZeq]
  rfl

noncomputable def pairInter (u v : ℕ) (δ : ℝ) : ℝ :=
  MeasureTheory.volume.real (Set.Ico (0 : ℝ) 1 ∩ bohrLift u δ ∩ bohrLift v δ)

noncomputable def pairQ (u v : ℕ) (δ : ℝ) : ℝ :=
  pairInter u v δ - 2 * δ * (Nat.gcd u v : ℝ) / (max u v : ℝ)

noncomputable def qVol (V : Finset ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ V.offDiag, pairQ p.1 p.2 δ

lemma pVol_eq_sum_pairInter (V : Finset ℕ) (δ : ℝ) :
    pVol V δ = ∑ p ∈ V.offDiag, pairInter p.1 p.2 δ := by
  classical
  have hpt : ∀ x : ℝ, (multFunc V δ x : ℝ) * ((multFunc V δ x : ℝ) - 1) =
      ∑ p ∈ V.offDiag, (bohrLift p.1 δ ∩ bohrLift p.2 δ).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    let S := V.filter (fun v => x ∈ bohrLift v δ)
    have hS : multFunc V δ x = S.card := rfl
    have hfilt : V.offDiag.filter (fun p => x ∈ bohrLift p.1 δ ∩ bohrLift p.2 δ) = S.offDiag := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, mem_inter_iff, S]
      tauto
    have hsum : ∑ p ∈ V.offDiag, (bohrLift p.1 δ ∩ bohrLift p.2 δ).indicator (fun _ => (1 : ℝ)) x =
        (S.offDiag.card : ℝ) := by
      rw [← hfilt, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : x ∈ bohrLift p.1 δ ∩ bohrLift p.2 δ <;> simp [hp]
    rw [hsum, hS, Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self S.card), Nat.cast_mul]
    ring
  unfold pVol
  simp_rw [hpt]
  rw [integral_finsetSum V.offDiag fun p _ =>
    integrableOn_indicator_one_Ico ((measurableSet_bohrLift p.1 δ).inter (measurableSet_bohrLift p.2 δ))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [setIntegral_indicator_one_Ico ((measurableSet_bohrLift p.1 δ).inter (measurableSet_bohrLift p.2 δ))]
  unfold pairInter
  rw [Set.inter_assoc]

lemma pVol_sub_qVol (V : Finset ℕ) (δ : ℝ) :
    pVol V δ - qVol V δ =
      2 * δ * ∑ p ∈ V.offDiag, (Nat.gcd p.1 p.2 : ℝ) / (max p.1 p.2 : ℝ) := by
  rw [pVol_eq_sum_pairInter, qVol, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold pairQ
  ring

/- ### Type I loss bound (Lemma 3.1) -/

def reducedCell (δ : ℝ) (v q r : ℕ) : Set ℝ :=
  if r = 0 then
    Set.Ico 0 (δ / (v : ℝ)) ∪ Set.Ico (1 - δ / (v : ℝ)) 1
  else
    Set.Ico ((r : ℝ) / (q : ℝ) - δ / (v : ℝ)) ((r : ℝ) / (q : ℝ) + δ / (v : ℝ))

lemma volume_real_reducedCell_le {δ : ℝ} (hδ0 : 0 < δ) {v q r : ℕ} (hv : 0 < v) :
    volume.real (reducedCell δ v q r) ≤ 2 * δ / (v : ℝ) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdv : 0 < δ / (v : ℝ) := div_pos hδ0 hvR
  unfold reducedCell
  split_ifs with hr
  · calc
      volume.real (Set.Ico (0 : ℝ) (δ / (v : ℝ)) ∪ Set.Ico (1 - δ / (v : ℝ)) 1)
          ≤ volume.real (Set.Ico (0 : ℝ) (δ / (v : ℝ))) +
            volume.real (Set.Ico (1 - δ / (v : ℝ)) 1) := measureReal_union_le _ _
      _ = δ / (v : ℝ) + (1 - (1 - δ / (v : ℝ))) := by
        rw [volume_real_Ico_eq hdv.le, volume_real_Ico_eq (by linarith)]
        ring
      _ = 2 * δ / (v : ℝ) := by ring
  · rw [volume_real_Ico_eq (by linarith)]
    ring_nf; rfl

lemma reducedCell_anti {δ : ℝ} (hδ0 : 0 < δ) {v₀ v q r : ℕ} (hv₀ : 0 < v₀) (hle : v₀ ≤ v) :
    reducedCell δ v q r ⊆ reducedCell δ v₀ q r := by
  have hv₀R : (0 : ℝ) < v₀ := by exact_mod_cast hv₀
  have hleR : (v₀ : ℝ) ≤ v := by exact_mod_cast hle
  have hdiv : δ / (v : ℝ) ≤ δ / (v₀ : ℝ) := div_le_div_of_nonneg_left hδ0.le hv₀R hleR
  unfold reducedCell
  split_ifs with hr
  · intro x hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2.trans_le hdiv⟩
    · exact Or.inr ⟨by linarith, h2⟩
  · intro x ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

lemma sum_totient_div_eq_card {V : Finset ℕ} (hV : ∀ v ∈ V, 0 < v) :
    ∑ q ∈ V.biUnion Nat.divisors, (Nat.totient q : ℝ) *
      (∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) = (V.card : ℝ) := by
  classical
  let D := V.biUnion Nat.divisors
  calc
    ∑ q ∈ D, (Nat.totient q : ℝ) * (∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ))
        = ∑ q ∈ D, ∑ v ∈ V, if q ∣ v then (Nat.totient q : ℝ) / (v : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    _ = ∑ v ∈ V, ∑ q ∈ D, if q ∣ v then (Nat.totient q : ℝ) / (v : ℝ) else 0 :=
      Finset.sum_comm
    _ = ∑ v ∈ V, ∑ q ∈ v.divisors, (Nat.totient q : ℝ) / (v : ℝ) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext q
      simp only [Finset.mem_filter, D, Finset.mem_biUnion, Nat.mem_divisors]
      have hv0 : v ≠ 0 := (hV v hv).ne'
      constructor
      · rintro ⟨_, hqv⟩; exact ⟨hqv, hv0⟩
      · rintro ⟨hqv, _⟩; exact ⟨⟨v, hv, hqv, hv0⟩, hqv⟩
    _ = ∑ v ∈ V, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_totient]
      have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast (hV v hv).ne'
      exact div_self hvR
    _ = (V.card : ℝ) := by simp

lemma typeILoss_le_gVol {V : Finset ℕ} (hV : ∀ v ∈ V, 0 < v) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    typeILoss V δ ≤ gVol V δ + 2 * δ * (V.card : ℝ) - 1 := by
  classical
  let D := V.biUnion Nat.divisors
  let minDiv (q : ℕ) : ℕ :=
    if h : (V.filter (q ∣ ·)).Nonempty then (V.filter (q ∣ ·)).min' h else 1
  have hcover : Set.Ico (0 : ℝ) 1 ∩ ⋃ v ∈ V, bohrLift v δ ⊆
      ⋃ q ∈ D, ⋃ r ∈ (Finset.range q).filter (q.Coprime ·),
        reducedCell δ (minDiv q) q r := by
    intro x ⟨hxIco, hxU⟩
    simp only [mem_iUnion] at hxU
    rcases hxU with ⟨v, hv, hxv⟩
    have hxI : x ∈ Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ := ⟨hxIco, hxv⟩
    rw [Ico_inter_bohrLift_eq_biUnion_wrappedCell (hV v hv) hδ0 hδ] at hxI
    simp only [mem_iUnion, Finset.mem_range] at hxI
    rcases hxI with ⟨a, ha, hxa⟩
    let g := Nat.gcd a v
    let q := v / g
    let r := a / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_right a (hV v hv)
    have hqv_mul : q * g = v := Nat.div_mul_cancel (Nat.gcd_dvd_right a v)
    have hra_mul : r * g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a v)
    have hqv : q ∣ v := ⟨g, hqv_mul.symm⟩
    have hqD : q ∈ D := Finset.mem_biUnion.mpr ⟨v, hv, Nat.mem_divisors.mpr ⟨hqv, (hV v hv).ne'⟩⟩
    have hrq : r < q := by
      by_contra h
      push Not at h
      have : v ≤ a := by
        calc v = q * g := hqv_mul.symm
          _ ≤ r * g := Nat.mul_le_mul_right g h
          _ = a := hra_mul
      omega
    have hcop : q.Coprime r := (Nat.coprime_div_gcd_div_gcd hg).symm
    have hne : (V.filter (q ∣ ·)).Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, hqv⟩⟩
    have hmin_mem : minDiv q ∈ V.filter (q ∣ ·) := by
      simp only [minDiv, hne, ↓reduceDIte]
      exact Finset.min'_mem _ hne
    have hmin_pos : 0 < minDiv q := hV _ (Finset.mem_filter.mp hmin_mem).1
    have hmin_le : minDiv q ≤ v := by
      simp only [minDiv, hne, ↓reduceDIte]
      exact Finset.min'_le _ v (Finset.mem_filter.mpr ⟨hv, hqv⟩)
    have hwrap_eq : wrappedCell v δ a = reducedCell δ v q r := by
      have ha0_iff : a = 0 ↔ r = 0 := by
        constructor
        · intro ha0; subst ha0; simp [r]
        · intro hr0; rw [← hra_mul, hr0, zero_mul]
      have hdiv_eq : (a : ℝ) / (v : ℝ) = (r : ℝ) / (q : ℝ) := by
        have haR : (a : ℝ) = (r : ℝ) * (g : ℝ) := by exact_mod_cast hra_mul.symm
        have hvR : (v : ℝ) = (q : ℝ) * (g : ℝ) := by exact_mod_cast hqv_mul.symm
        have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
        rw [haR, hvR, mul_div_mul_right _ _ hgR]
      unfold wrappedCell reducedCell
      by_cases ha0 : a = 0
      · have hr0 : r = 0 := ha0_iff.mp ha0
        simp [ha0, hr0]
      · have hr0 : r ≠ 0 := mt ha0_iff.mpr ha0
        simp only [ha0, hr0, ↓reduceIte, sub_div, add_div, hdiv_eq]
    rw [hwrap_eq] at hxa
    have hsub := reducedCell_anti hδ0 hmin_pos hmin_le hxa
    simp only [mem_iUnion, Finset.mem_filter, Finset.mem_range]
    exact ⟨q, hqD, r, ⟨hrq, hcop⟩, hsub⟩
  have hfin_red : ∀ (q r : ℕ), volume (reducedCell δ (minDiv q) q r) < ⊤ := by
    intro q r
    unfold reducedCell
    split_ifs
    · exact (measure_union_le _ _).trans_lt (by simp [Real.volume_Ico])
    · simp [Real.volume_Ico]
  have hfin_U : volume (⋃ q ∈ D, ⋃ r ∈ (Finset.range q).filter (q.Coprime ·),
      reducedCell δ (minDiv q) q r) ≠ ⊤ := by
    refine ((measure_biUnion_finset_le D _).trans_lt ?_).ne
    refine ENNReal.sum_lt_top.mpr fun q _ => ?_
    exact (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun r _ => hfin_red q r)
  have hvol_le : volume.real (Set.Ico (0 : ℝ) 1 ∩ ⋃ v ∈ V, bohrLift v δ) ≤
      ∑ q ∈ D, (Nat.totient q : ℝ) * (2 * δ / (minDiv q : ℝ)) := by
    calc
      volume.real (Set.Ico (0 : ℝ) 1 ∩ ⋃ v ∈ V, bohrLift v δ)
          ≤ volume.real (⋃ q ∈ D, ⋃ r ∈ (Finset.range q).filter (q.Coprime ·),
              reducedCell δ (minDiv q) q r) :=
        measureReal_mono hcover hfin_U
      _ ≤ ∑ q ∈ D, volume.real (⋃ r ∈ (Finset.range q).filter (q.Coprime ·),
              reducedCell δ (minDiv q) q r) :=
        measureReal_biUnion_finset_le D _
      _ ≤ ∑ q ∈ D, ∑ r ∈ (Finset.range q).filter (q.Coprime ·),
              volume.real (reducedCell δ (minDiv q) q r) :=
        Finset.sum_le_sum fun q _ => measureReal_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ D, ∑ _r ∈ (Finset.range q).filter (q.Coprime ·),
              (2 * δ / (minDiv q : ℝ)) := by
        refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r _ => ?_
        have hmin_pos : 0 < minDiv q := by
          unfold minDiv
          split_ifs with hne
          · exact hV _ (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
          · norm_num
        exact volume_real_reducedCell_le hδ0 hmin_pos
      _ = ∑ q ∈ D, (Nat.totient q : ℝ) * (2 * δ / (minDiv q : ℝ)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime]
  have hloss : typeILoss V δ =
      2 * δ * (V.card : ℝ) - ∑ q ∈ D, (Nat.totient q : ℝ) * (2 * δ / (minDiv q : ℝ)) := by
    unfold typeILoss
    have hsplit : ∑ q ∈ D, (Nat.totient q : ℝ) *
        ((∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
          if h : (V.filter (q ∣ ·)).Nonempty then
            (1 : ℝ) / ((V.filter (q ∣ ·)).min' h : ℝ)
          else 0) =
        (∑ q ∈ D, (Nat.totient q : ℝ) * ∑ v ∈ V.filter (q ∣ ·), (1 : ℝ) / (v : ℝ)) -
        (∑ q ∈ D, (Nat.totient q : ℝ) * ((1 : ℝ) / (minDiv q : ℝ))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hne : (V.filter (q ∣ ·)).Nonempty := by
        rcases Finset.mem_biUnion.mp hq with ⟨v, hv, hqv⟩
        exact ⟨v, Finset.mem_filter.mpr ⟨hv, (Nat.mem_divisors.mp hqv).1⟩⟩
      simp only [minDiv, hne, ↓reduceDIte]
      ring
    rw [hsplit, sum_totient_div_eq_card hV, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [gVol_eq_one_sub_union]
  linarith

lemma typeILoss_le_gVol_baseline {V : Finset ℕ} (hn : 2 ≤ V.card) (hV : ∀ v ∈ V, 0 < v) :
    typeILoss V (1 / (2 * (V.card : ℝ))) ≤ gVol V (1 / (2 * (V.card : ℝ))) := by
  have hnR : (2 : ℝ) ≤ V.card := by exact_mod_cast hn
  have hδ0 : 0 < 1 / (2 * (V.card : ℝ)) := by positivity
  have hδ : 1 / (2 * (V.card : ℝ)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h := typeILoss_le_gVol hV hδ0 hδ
  have hcancel : 2 * (1 / (2 * (V.card : ℝ))) * (V.card : ℝ) = 1 := by
    field_simp
  linarith

/- ### Section 3: Type II pair intersection bounds (Section 3.2, Lemma 3.3) -/

lemma volume_real_Ico_inter_mul_periodic {S : Set ℝ} (hSm : MeasurableSet S)
    (hSper : ∀ k : ℤ, ∀ x : ℝ, x + (k : ℝ) ∈ S ↔ x ∈ S) {d : ℕ} (hd : 0 < d) :
    volume.real (Set.Ico (0 : ℝ) 1 ∩ ((fun x => (d : ℝ) * x) ⁻¹' S)) =
      volume.real (Set.Ico (0 : ℝ) 1 ∩ S) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpre : Set.Ico (0 : ℝ) 1 ∩ ((fun x => (d : ℝ) * x) ⁻¹' S) =
      (fun x => (d : ℝ) * x) ⁻¹' (Set.Ico (0 : ℝ) (d : ℝ) ∩ S) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Ico]
    constructor
    · rintro ⟨⟨h0, h1⟩, hxS⟩
      exact ⟨⟨mul_nonneg hdR.le h0, (mul_lt_iff_lt_one_right hdR).mpr h1⟩, hxS⟩
    · rintro ⟨⟨h0, h1⟩, hxS⟩
      exact ⟨⟨nonneg_of_mul_nonneg_right h0 hdR, (mul_lt_iff_lt_one_right hdR).mp h1⟩, hxS⟩
  have hsplit : Set.Ico (0 : ℝ) (d : ℝ) ∩ S =
      ⋃ k ∈ Finset.range d, (Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ S) := by
    ext y
    simp only [mem_inter_iff, mem_Ico, mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨⟨h0, hd_lt⟩, hyS⟩
      refine ⟨⌊y⌋₊, ?_, ⟨Nat.floor_le h0, Nat.lt_floor_add_one y⟩, hyS⟩
      exact (Nat.floor_lt h0).mpr hd_lt
    · rintro ⟨k, hk, ⟨hk1, hk2⟩, hyS⟩
      have hk_le : (k : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hk
      exact ⟨⟨le_trans (Nat.cast_nonneg k) hk1, lt_of_lt_of_le hk2 hk_le⟩, hyS⟩
  have hdisj : (Finset.range d : Set ℕ).PairwiseDisjoint
      (fun k => Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ S) := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y ⟨⟨h1, h2⟩, _⟩ ⟨⟨h3, h4⟩, _⟩
    have hk1 : (k₁ : ℝ) < (k₂ : ℝ) + 1 := by linarith
    have hk2 : (k₂ : ℝ) < (k₁ : ℝ) + 1 := by linarith
    have hk1' : k₁ < k₂ + 1 := by exact_mod_cast hk1
    have hk2' : k₂ < k₁ + 1 := by exact_mod_cast hk2
    omega
  have hshift : ∀ k : ℕ, volume (Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ S) =
      volume (Set.Ico (0 : ℝ) 1 ∩ S) := by
    intro k
    have hset : (fun x : ℝ => x + (k : ℝ)) ⁻¹' (Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ S) =
        Set.Ico (0 : ℝ) 1 ∩ S := by
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_Ico]
      have hp := hSper (k : ℤ) x
      push_cast at hp
      exact ⟨fun ⟨⟨h1, h2⟩, hS⟩ => ⟨⟨by linarith, by linarith⟩, hp.mp hS⟩,
        fun ⟨⟨h1, h2⟩, hS⟩ => ⟨⟨by linarith, by linarith⟩, hp.mpr hS⟩⟩
    rw [← hset, measure_preimage_add_right]
  have hvol_d : volume (Set.Ico (0 : ℝ) (d : ℝ) ∩ S) =
      (d : ENNReal) * volume (Set.Ico (0 : ℝ) 1 ∩ S) := by
    rw [hsplit, measure_biUnion_finset hdisj (fun k _ => measurableSet_Ico.inter hSm)]
    calc
      ∑ k ∈ Finset.range d, volume (Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ S)
          = ∑ _k ∈ Finset.range d, volume (Set.Ico (0 : ℝ) 1 ∩ S) :=
        Finset.sum_congr rfl fun k _ => hshift k
      _ = (d : ENNReal) * volume (Set.Ico (0 : ℝ) 1 ∩ S) := by simp
  rw [hpre, Measure.real, Real.volume_preimage_mul_left hdR.ne', hvol_d]
  rw [abs_of_pos (inv_pos.mpr hdR), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hdR.le), ENNReal.toReal_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ hdR.ne', one_mul]
  rfl

lemma pairInter_mul_left {d u v : ℕ} (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (δ : ℝ) :
    pairInter (d * u) (d * v) δ = pairInter u v δ := by
  unfold pairInter
  have h1 : Set.Ico (0 : ℝ) 1 ∩ bohrLift (d * u) δ ∩ bohrLift (d * v) δ =
      Set.Ico (0 : ℝ) 1 ∩ ((fun x => (d : ℝ) * x) ⁻¹' (bohrLift u δ ∩ bohrLift v δ)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_bohrLift_mul hd hu, mem_bohrLift_mul hd hv]
    tauto
  have h2 : Set.Ico (0 : ℝ) 1 ∩ bohrLift u δ ∩ bohrLift v δ =
      Set.Ico (0 : ℝ) 1 ∩ (bohrLift u δ ∩ bohrLift v δ) := Set.inter_assoc _ _ _
  rw [h1, h2]
  refine volume_real_Ico_inter_mul_periodic
    ((measurableSet_bohrLift u δ).inter (measurableSet_bohrLift v δ)) ?_ hd
  intro k x
  simp only [mem_inter_iff, mem_bohrLift_add_int hu k, mem_bohrLift_add_int hv k]

lemma pairQ_reduce_gcd {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (δ : ℝ) :
    pairQ u v δ = pairQ (u / Nat.gcd u v) (v / Nat.gcd u v) δ := by
  let d := Nat.gcd u v
  let u' := u / d
  let v' := v / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left v hu
  have hu_eq : d * u' = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hv_eq : d * v' = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hu' : 0 < u' := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hu_eq; exact hu.ne' hu_eq.symm
  have hv' : 0 < v' := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hv_eq; exact hv.ne' hv_eq.symm
  have hcop : Nat.gcd u' v' = 1 := Nat.coprime_div_gcd_div_gcd hd
  have hmaxN : max u v = d * max u' v' := by
    rw [← hu_eq, ← hv_eq, Nat.mul_max_mul_left]
  have hmax : max (u : ℝ) (v : ℝ) = (d : ℝ) * max (u' : ℝ) (v' : ℝ) := by
    rw [← Nat.cast_max, hmaxN, Nat.cast_mul, Nat.cast_max]
  unfold pairQ
  have hpi : pairInter u v δ = pairInter u' v' δ := by
    conv_lhs => rw [← hu_eq, ← hv_eq]
    exact pairInter_mul_left hd hu' hv' δ
  change pairInter u v δ - 2 * δ * (d : ℝ) / max (u : ℝ) (v : ℝ) =
    pairInter u' v' δ - 2 * δ * (Nat.gcd u' v' : ℝ) / max (u' : ℝ) (v' : ℝ)
  rw [hpi, hcop, hmax]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

lemma volume_Ico_inter_iUnion_int_translate {I : Set ℝ} (hIm : MeasurableSet I)
    (hdisj : Pairwise fun l₁ l₂ : ℤ =>
      Disjoint ((fun x => x - (l₁ : ℝ)) ⁻¹' I) ((fun x => x - (l₂ : ℝ)) ⁻¹' I)) :
    volume (Set.Ico (0 : ℝ) 1 ∩ ⋃ l : ℤ, (fun x => x - (l : ℝ)) ⁻¹' I) = volume I := by
  rw [Set.inter_iUnion]
  have hdisj1 : Pairwise fun l₁ l₂ : ℤ =>
      Disjoint (Set.Ico (0 : ℝ) 1 ∩ (fun x => x - (l₁ : ℝ)) ⁻¹' I)
        (Set.Ico (0 : ℝ) 1 ∩ (fun x => x - (l₂ : ℝ)) ⁻¹' I) := fun l₁ l₂ hne =>
    (hdisj hne).mono inter_subset_right inter_subset_right
  have hm1 : ∀ l : ℤ, MeasurableSet (Set.Ico (0 : ℝ) 1 ∩ (fun x => x - (l : ℝ)) ⁻¹' I) := fun l =>
    measurableSet_Ico.inter (hIm.preimage (measurable_id.sub measurable_const))
  rw [measure_iUnion hdisj1 hm1]
  have hshift : ∀ l : ℤ, volume (Set.Ico (0 : ℝ) 1 ∩ (fun x => x - (l : ℝ)) ⁻¹' I) =
      volume (Set.Ico (-(l : ℝ)) (1 - (l : ℝ)) ∩ I) := by
    intro l
    have hset : (fun y : ℝ => y + (l : ℝ)) ⁻¹' (Set.Ico (0 : ℝ) 1 ∩ (fun x => x - (l : ℝ)) ⁻¹' I) =
        Set.Ico (-(l : ℝ)) (1 - (l : ℝ)) ∩ I := by
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_Ico, add_sub_cancel_right]
      exact ⟨fun ⟨⟨h1, h2⟩, hI⟩ => ⟨⟨by linarith, by linarith⟩, hI⟩,
        fun ⟨⟨h1, h2⟩, hI⟩ => ⟨⟨by linarith, by linarith⟩, hI⟩⟩
    rw [← hset, measure_preimage_add_right]
  simp_rw [hshift]
  have hdisj2 : Pairwise fun l₁ l₂ : ℤ =>
      Disjoint (Set.Ico (-(l₁ : ℝ)) (1 - (l₁ : ℝ)) ∩ I)
        (Set.Ico (-(l₂ : ℝ)) (1 - (l₂ : ℝ)) ∩ I) := by
    intro l₁ l₂ hne
    rw [Set.disjoint_left]
    intro y ⟨⟨h1, h2⟩, _⟩ ⟨⟨h3, h4⟩, _⟩
    have hl1 : ((l₂ - l₁ : ℤ) : ℝ) < 1 := by push_cast; linarith
    have hl2 : ((l₁ - l₂ : ℤ) : ℝ) < 1 := by push_cast; linarith
    have hl1' : l₂ - l₁ < 1 := by exact_mod_cast hl1
    have hl2' : l₁ - l₂ < 1 := by exact_mod_cast hl2
    omega
  have hm2 : ∀ l : ℤ, MeasurableSet (Set.Ico (-(l : ℝ)) (1 - (l : ℝ)) ∩ I) := fun _ =>
    measurableSet_Ico.inter hIm
  rw [← measure_iUnion hdisj2 hm2]
  congr 1
  ext y
  simp only [mem_iUnion, mem_inter_iff, mem_Ico]
  constructor
  · rintro ⟨_, _, hyI⟩; exact hyI
  · intro hyI
    refine ⟨-⌊y⌋, ⟨?_, ?_⟩, hyI⟩
    · simp [Int.floor_le y]
    · simp only [Int.cast_neg, sub_neg_eq_add]
      linarith [Int.lt_floor_add_one y]

def overlapF (r₁ r₂ y : ℝ) : ℝ :=
  max 0 (min (2 * min r₁ r₂) (r₁ + r₂ - |y|))

lemma overlapF_even (r₁ r₂ y : ℝ) : overlapF r₁ r₂ (-y) = overlapF r₁ r₂ y := by
  simp [overlapF]

lemma overlapF_nonneg (r₁ r₂ y : ℝ) : 0 ≤ overlapF r₁ r₂ y :=
  le_max_left _ _

lemma volume_real_Ico_inter_Ico (c₁ c₂ r₁ r₂ : ℝ) :
    volume.real (Set.Ico (c₁ - r₁) (c₁ + r₁) ∩ Set.Ico (c₂ - r₂) (c₂ + r₂)) =
      overlapF r₁ r₂ (c₁ - c₂) := by
  rw [Set.Ico_inter_Ico, Measure.real, Real.volume_Ico]
  have halg : min (c₁ + r₁) (c₂ + r₂) - max (c₁ - r₁) (c₂ - r₂) =
      min (2 * min r₁ r₂) (r₁ + r₂ - |c₁ - c₂|) := by
    apply le_antisymm
    · refine le_min ?_ ?_
      · rcases le_total r₁ r₂ with hr | hr
        · rw [min_eq_left hr]
          linarith [min_le_left (c₁ + r₁) (c₂ + r₂), le_max_left (c₁ - r₁) (c₂ - r₂)]
        · rw [min_eq_right hr]
          linarith [min_le_right (c₁ + r₁) (c₂ + r₂), le_max_right (c₁ - r₁) (c₂ - r₂)]
      · rcases le_total c₁ c₂ with hc | hc
        · rw [abs_of_nonpos (sub_nonpos.mpr hc)]
          linarith [min_le_left (c₁ + r₁) (c₂ + r₂), le_max_right (c₁ - r₁) (c₂ - r₂)]
        · rw [abs_of_nonneg (sub_nonneg.mpr hc)]
          linarith [min_le_right (c₁ + r₁) (c₂ + r₂), le_max_left (c₁ - r₁) (c₂ - r₂)]
    · have hle1 : min (2 * min r₁ r₂) (r₁ + r₂ - |c₁ - c₂|) ≤ 2 * r₁ :=
        (min_le_left _ _).trans (by linarith [min_le_left r₁ r₂])
      have hle2 : min (2 * min r₁ r₂) (r₁ + r₂ - |c₁ - c₂|) ≤ 2 * r₂ :=
        (min_le_left _ _).trans (by linarith [min_le_right r₁ r₂])
      have hle3 : min (2 * min r₁ r₂) (r₁ + r₂ - |c₁ - c₂|) ≤ r₁ + r₂ - (c₁ - c₂) :=
        (min_le_right _ _).trans (by linarith [le_abs_self (c₁ - c₂)])
      have hle4 : min (2 * min r₁ r₂) (r₁ + r₂ - |c₁ - c₂|) ≤ r₁ + r₂ - (c₂ - c₁) :=
        (min_le_right _ _).trans (by linarith [neg_le_abs (c₁ - c₂)])
      rw [le_sub_iff_add_le, add_comm]
      refine le_min ?_ ?_
      · rcases max_choice (c₁ - r₁) (c₂ - r₂) with hmax | hmax <;> rw [hmax] <;> linarith
      · rcases max_choice (c₁ - r₁) (c₂ - r₂) with hmax | hmax <;> rw [hmax] <;> linarith
  rw [halg]
  unfold overlapF
  by_cases h : 0 ≤ min (2 * min r₁ r₂) (r₁ + r₂ - |c₁ - c₂|)
  · rw [ENNReal.toReal_ofReal h, max_eq_right h]
  · push Not at h
    rw [ENNReal.ofReal_of_nonpos h.le, ENNReal.toReal_zero, max_eq_left h.le]

lemma sum_Icc_neg_pos (M : ℕ) (g : ℤ → ℝ) (heven : ∀ j : ℤ, g (-j) = g j) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), g j =
      g 0 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) M, g (j : ℤ) := by
  induction M with
  | zero =>
    simp
  | succ k ih =>
    have h1 : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k + 1 : ℕ) : ℤ))
          (insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hmem1 : -((k + 1 : ℕ) : ℤ) ∉
        insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hmem2 : ((k + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have h2 : Finset.Icc (1 : ℕ) (k + 1) = insert (k + 1) (Finset.Icc (1 : ℕ) k) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hmem3 : k + 1 ∉ Finset.Icc (1 : ℕ) k := by simp
    rw [h1, Finset.sum_insert hmem1, Finset.sum_insert hmem2, ih, heven,
      h2, Finset.sum_insert hmem3]
    ring

lemma pairQ_coprime_eq_sum {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    pairQ u v δ = 2 * ∑ j ∈ Finset.Icc (1 : ℕ) (u + v),
      overlapF (δ / (u : ℝ)) (δ / (v : ℝ)) ((j : ℝ) / ((u : ℝ) * (v : ℝ))) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  let m0 (j : ℤ) : ℤ := j * Nat.gcdB u v
  let n0 (j : ℤ) : ℤ := -(j * Nat.gcdA u v)
  have hbez : ∀ j : ℤ, (v : ℤ) * m0 j - (u : ℤ) * n0 j = j := by
    intro j
    have hg := Nat.gcd_eq_gcd_ab u v
    rw [hcop.gcd_eq_one, Nat.cast_one] at hg
    dsimp only [m0, n0]
    have h1 : (u : ℤ) * Nat.gcdA u v + (v : ℤ) * Nat.gcdB u v = 1 := hg.symm
    calc
      (v : ℤ) * (j * Nat.gcdB u v) - (u : ℤ) * (-(j * Nat.gcdA u v))
          = j * ((u : ℤ) * Nat.gcdA u v + (v : ℤ) * Nat.gcdB u v) := by ring
      _ = j * 1 := by rw [h1]
      _ = j := mul_one j
  have hsol : ∀ j m n : ℤ, (v : ℤ) * m - (u : ℤ) * n = j ↔
      ∃ l : ℤ, m = m0 j + (u : ℤ) * l ∧ n = n0 j + (v : ℤ) * l := by
    intro j m n
    constructor
    · intro h
      have hdiff : (v : ℤ) * (m - m0 j) = (u : ℤ) * (n - n0 j) := by
        linarith [hbez j]
      have hdvd : (u : ℤ) ∣ (v : ℤ) * (m - m0 j) := ⟨n - n0 j, hdiff⟩
      have hdvd' : (u : ℤ) ∣ m - m0 j := hcop.isCoprime.dvd_of_dvd_mul_left hdvd
      rcases hdvd' with ⟨l, hl⟩
      refine ⟨l, by linarith, ?_⟩
      have hmul : (u : ℤ) * ((v : ℤ) * l) = (u : ℤ) * (n - n0 j) := by
        calc
          (u : ℤ) * ((v : ℤ) * l) = (v : ℤ) * ((u : ℤ) * l) := by ring
          _ = (v : ℤ) * (m - m0 j) := by rw [← hl]
          _ = (u : ℤ) * (n - n0 j) := hdiff
      have huZ : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
      have hcancel := mul_left_cancel₀ huZ hmul
      linarith
    · rintro ⟨l, rfl, rfl⟩
      linarith [hbez j]
  let J (j : ℤ) : Set ℝ := bohrCell u δ (m0 j) ∩ bohrCell v δ (n0 j)
  let B (j : ℤ) : Set ℝ := Set.Ico (0 : ℝ) 1 ∩ ⋃ l : ℤ, (fun x => x - (l : ℝ)) ⁻¹' J j
  have htrans : ∀ j l : ℤ, (fun x => x - (l : ℝ)) ⁻¹' J j =
      bohrCell u δ (m0 j + (u : ℤ) * l) ∩ bohrCell v δ (n0 j + (v : ℤ) * l) := by
    intro j l
    ext x
    simp only [mem_preimage, mem_inter_iff, J]
    have h1 := mem_bohrCell_add_int hu (δ := δ) (m := m0 j) (k := l) (x := x - (l : ℝ))
    have h2 := mem_bohrCell_add_int hv (δ := δ) (m := n0 j) (k := l) (x := x - (l : ℝ))
    rw [sub_add_cancel] at h1 h2
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩, fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩⟩
  let M : ℕ := u + v
  have hdecomp : Set.Ico (0 : ℝ) 1 ∩ bohrLift u δ ∩ bohrLift v δ =
      ⋃ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), B j := by
    ext x
    simp only [mem_inter_iff, bohrLift_eq_iUnion, mem_iUnion, Finset.mem_Icc, B]
    constructor
    · rintro ⟨⟨hxIco, m, hm⟩, n, hn⟩
      let j : ℤ := (v : ℤ) * m - (u : ℤ) * n
      have hmn : (v : ℤ) * m - (u : ℤ) * n = j := rfl
      rw [mem_bohrCell_iff hu] at hm
      rw [mem_bohrCell_iff hv] at hn
      have hj_lt : (j : ℝ) < δ * ((u : ℝ) + (v : ℝ)) := by
        have h1 : (v : ℝ) * ((m : ℝ) - δ) ≤ (v : ℝ) * ((u : ℝ) * x) :=
          mul_le_mul_of_nonneg_left hm.1 hvR.le
        have h2 : (u : ℝ) * ((v : ℝ) * x) < (u : ℝ) * ((n : ℝ) + δ) :=
          mul_lt_mul_of_pos_left hn.2 huR
        have : (j : ℝ) = (v : ℝ) * (m : ℝ) - (u : ℝ) * (n : ℝ) := by push_cast [j]; ring
        linarith
      have hj_gt : -(δ * ((u : ℝ) + (v : ℝ))) < (j : ℝ) := by
        have h1 : (v : ℝ) * ((u : ℝ) * x) < (v : ℝ) * ((m : ℝ) + δ) :=
          mul_lt_mul_of_pos_left hm.2 hvR
        have h2 : (u : ℝ) * ((n : ℝ) - δ) ≤ (u : ℝ) * ((v : ℝ) * x) :=
          mul_le_mul_of_nonneg_left hn.1 huR.le
        have : (j : ℝ) = (v : ℝ) * (m : ℝ) - (u : ℝ) * (n : ℝ) := by push_cast [j]; ring
        linarith
      have hM : δ * ((u : ℝ) + (v : ℝ)) ≤ (M : ℝ) := by
        have hMc : (M : ℝ) = (u : ℝ) + (v : ℝ) := by push_cast [M]; ring
        rw [hMc]
        exact mul_le_of_le_one_left (by positivity) (by linarith only [hδ])
      have hj_le : j ≤ (M : ℤ) := by
        have : (j : ℝ) < (M : ℝ) := lt_of_lt_of_le hj_lt hM
        exact_mod_cast this.le
      have hj_ge : -(M : ℤ) ≤ j := by
        have : -(M : ℝ) < (j : ℝ) := lt_of_le_of_lt (neg_le_neg hM) hj_gt
        exact_mod_cast this.le
      rcases (hsol j m n).mp hmn with ⟨l, hm_eq, hn_eq⟩
      refine ⟨j, ⟨hj_ge, hj_le⟩, hxIco, l, ?_⟩
      rw [htrans, ← hm_eq, ← hn_eq]
      exact ⟨(mem_bohrCell_iff hu).mpr hm, (mem_bohrCell_iff hv).mpr hn⟩
    · rintro ⟨j, _, hxIco, l, hx⟩
      rw [htrans] at hx
      exact ⟨⟨hxIco, m0 j + (u : ℤ) * l, hx.1⟩, n0 j + (v : ℤ) * l, hx.2⟩
  have hdisjB : (Finset.Icc (-(M : ℤ)) (M : ℤ) : Set ℤ).PairwiseDisjoint B := by
    intro j₁ _ j₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x ⟨_, hx₁⟩ ⟨_, hx₂⟩
    simp only [mem_iUnion] at hx₁ hx₂
    rcases hx₁ with ⟨l₁, hl₁⟩
    rcases hx₂ with ⟨l₂, hl₂⟩
    rw [htrans] at hl₁ hl₂
    have hm_eq : m0 j₁ + (u : ℤ) * l₁ = m0 j₂ + (u : ℤ) * l₂ := by
      by_contra h
      exact Set.disjoint_left.mp (bohrCell_pairwiseDisjoint hu hδ h) hl₁.1 hl₂.1
    have hn_eq : n0 j₁ + (v : ℤ) * l₁ = n0 j₂ + (v : ℤ) * l₂ := by
      by_contra h
      exact Set.disjoint_left.mp (bohrCell_pairwiseDisjoint hv hδ h) hl₁.2 hl₂.2
    have h1 := (hsol j₁ _ _).mpr ⟨l₁, rfl, rfl⟩
    have h2 := (hsol j₂ _ _).mpr ⟨l₂, rfl, rfl⟩
    rw [hm_eq, hn_eq] at h1
    exact hne (h1.symm.trans h2)
  have hvolB : ∀ j : ℤ, volume.real (B j) =
      overlapF (δ / (u : ℝ)) (δ / (v : ℝ)) ((j : ℝ) / ((u : ℝ) * (v : ℝ))) := by
    intro j
    have hdisjL : Pairwise fun l₁ l₂ : ℤ =>
        Disjoint ((fun x => x - (l₁ : ℝ)) ⁻¹' J j) ((fun x => x - (l₂ : ℝ)) ⁻¹' J j) := by
      intro l₁ l₂ hne
      rw [htrans, htrans]
      have hm_ne : m0 j + (u : ℤ) * l₁ ≠ m0 j + (u : ℤ) * l₂ := by
        intro heq
        have huZ : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
        exact hne (mul_left_cancel₀ huZ (add_left_cancel heq))
      exact (bohrCell_pairwiseDisjoint hu hδ hm_ne).mono inter_subset_left inter_subset_left
    have hJm : MeasurableSet (J j) :=
      (measurableSet_bohrCell u δ _).inter (measurableSet_bohrCell v δ _)
    have hvB : volume (B j) = volume (J j) :=
      volume_Ico_inter_iUnion_int_translate hJm hdisjL
    rw [Measure.real, hvB]
    have hJeq : J j = Set.Ico ((m0 j : ℝ) / (u : ℝ) - δ / (u : ℝ))
        ((m0 j : ℝ) / (u : ℝ) + δ / (u : ℝ)) ∩
        Set.Ico ((n0 j : ℝ) / (v : ℝ) - δ / (v : ℝ))
        ((n0 j : ℝ) / (v : ℝ) + δ / (v : ℝ)) := by
      simp only [J, bohrCell, sub_div, add_div]
    change volume.real (J j) = _
    rw [hJeq, volume_real_Ico_inter_Ico]
    congr 1
    have hbj : ((v : ℤ) * m0 j - (u : ℤ) * n0 j : ℝ) = (j : ℝ) := by exact_mod_cast hbez j
    push_cast at hbj
    field_simp
    linarith
  have hmB : ∀ j : ℤ, MeasurableSet (B j) := fun j =>
    measurableSet_Ico.inter (MeasurableSet.iUnion fun _ =>
      ((measurableSet_bohrCell u δ _).inter (measurableSet_bohrCell v δ _)).preimage
        (measurable_id.sub measurable_const))
  have hfinB : ∀ j : ℤ, volume (B j) ≠ ⊤ := fun j =>
    (measure_mono inter_subset_left).trans_lt (by simp [Real.volume_Ico]) |>.ne
  have hpi : pairInter u v δ =
      ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        overlapF (δ / (u : ℝ)) (δ / (v : ℝ)) ((j : ℝ) / ((u : ℝ) * (v : ℝ))) := by
    unfold pairInter
    rw [hdecomp, measureReal_biUnion_finset hdisjB (fun j _ => hmB j) (fun j _ => hfinB j)]
    exact Finset.sum_congr rfl fun j _ => hvolB j
  have heven : ∀ j : ℤ,
      overlapF (δ / (u : ℝ)) (δ / (v : ℝ)) (((-j : ℤ) : ℝ) / ((u : ℝ) * (v : ℝ))) =
      overlapF (δ / (u : ℝ)) (δ / (v : ℝ)) ((j : ℝ) / ((u : ℝ) * (v : ℝ))) := by
    intro j
    rw [Int.cast_neg, neg_div, overlapF_even]
  rw [sum_Icc_neg_pos M _ heven] at hpi
  have hj0 : overlapF (δ / (u : ℝ)) (δ / (v : ℝ)) (((0 : ℤ) : ℝ) / ((u : ℝ) * (v : ℝ))) =
      2 * δ * (Nat.gcd u v : ℝ) / (max u v : ℝ) := by
    rw [hcop.gcd_eq_one]
    simp only [Int.cast_zero, zero_div, overlapF, abs_zero, sub_zero, Nat.cast_one, mul_one]
    have hmin_le : 2 * min (δ / (u : ℝ)) (δ / (v : ℝ)) ≤ δ / (u : ℝ) + δ / (v : ℝ) := by
      linarith [min_le_left (δ / (u : ℝ)) (δ / (v : ℝ)), min_le_right (δ / (u : ℝ)) (δ / (v : ℝ))]
    have hmin_nonneg : 0 ≤ 2 * min (δ / (u : ℝ)) (δ / (v : ℝ)) := by
      have : 0 ≤ min (δ / (u : ℝ)) (δ / (v : ℝ)) := le_min (by positivity) (by positivity)
      linarith
    rw [min_eq_left hmin_le, max_eq_right hmin_nonneg]
    rcases le_total u v with huv | hvu
    · have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
      have hdiv : δ / (v : ℝ) ≤ δ / (u : ℝ) := div_le_div_of_nonneg_left hδ0.le huR huvR
      rw [min_eq_right hdiv, max_eq_right huvR]
      ring
    · have hvuR : (v : ℝ) ≤ (u : ℝ) := by exact_mod_cast hvu
      have hdiv : δ / (u : ℝ) ≤ δ / (v : ℝ) := div_le_div_of_nonneg_left hδ0.le hvR hvuR
      rw [min_eq_left hdiv, max_eq_left hvuR]
      ring
  unfold pairQ
  rw [hpi, hj0]
  push_cast
  ring

/- ### Elementary trapezoid antiderivative for Riemann sum comparison -/

def trapF (a b y : ℝ) : ℝ :=
  max 0 (min (2 * a) (a + b - y))

noncomputable def trapG (a b y : ℝ) : ℝ :=
  if y ≤ b - a then 2 * a * y
  else if y ≤ a + b then 2 * a * b - (a + b - y) ^ 2 / 2
  else 2 * a * b

lemma trapF_anti {a b x y : ℝ} (hxy : x ≤ y) :
    trapF a b y ≤ trapF a b x := by
  unfold trapF
  exact max_le_max_left 0 (min_le_min_left _ (by linarith))

lemma trapG_step_seg1 {a b x y : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) (hy : y ≤ b - a) :
    trapF a b y * (y - x) ≤ trapG a b y - trapG a b x ∧
    trapG a b y - trapG a b x ≤ trapF a b x * (y - x) := by
  have hx' : x ≤ b - a := hxy.trans hy
  have hGx : trapG a b x = 2 * a * x := if_pos hx'
  have hGy : trapG a b y = 2 * a * y := if_pos hy
  have hFx : trapF a b x = 2 * a := by
    unfold trapF
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have hFy : trapF a b y = 2 * a := by
    unfold trapF
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  rw [hGx, hGy, hFx, hFy]
  exact ⟨by linarith, by linarith⟩

lemma trapG_step_seg2 {a b x y : ℝ} (hx1 : b - a ≤ x) (hxy : x ≤ y) (hy2 : y ≤ a + b) :
    trapF a b y * (y - x) ≤ trapG a b y - trapG a b x ∧
    trapG a b y - trapG a b x ≤ trapF a b x * (y - x) := by
  have hx2 : x ≤ a + b := hxy.trans hy2
  have hy1 : b - a ≤ y := hx1.trans hxy
  have hGx : trapG a b x = 2 * a * b - (a + b - x) ^ 2 / 2 := by
    unfold trapG
    split_ifs with h1
    · have : x = b - a := le_antisymm h1 hx1
      subst this; ring
    · rfl
  have hGy : trapG a b y = 2 * a * b - (a + b - y) ^ 2 / 2 := by
    unfold trapG
    split_ifs with h1
    · have : y = b - a := le_antisymm h1 hy1
      subst this; ring
    · rfl
  have hFx : trapF a b x = a + b - x := by
    unfold trapF
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  have hFy : trapF a b y = a + b - y := by
    unfold trapF
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  rw [hGx, hGy, hFx, hFy]
  exact ⟨by nlinarith, by nlinarith⟩

lemma trapG_step_seg3 {a b x y : ℝ} (ha : 0 ≤ a) (hx : a + b ≤ x) (hxy : x ≤ y) :
    trapF a b y * (y - x) ≤ trapG a b y - trapG a b x ∧
    trapG a b y - trapG a b x ≤ trapF a b x * (y - x) := by
  have hy : a + b ≤ y := hx.trans hxy
  have hGx : trapG a b x = 2 * a * b := by
    unfold trapG
    split_ifs with h1 h2
    · have : a = 0 := by linarith
      subst this; ring
    · have : x = a + b := le_antisymm h2 hx
      subst this; ring
    · rfl
  have hGy : trapG a b y = 2 * a * b := by
    unfold trapG
    split_ifs with h1 h2
    · have : a = 0 := by linarith
      subst this; ring
    · have : y = a + b := le_antisymm h2 hy
      subst this; ring
    · rfl
  have hFx : trapF a b x = 0 := by
    unfold trapF
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have hFy : trapF a b y = 0 := by
    unfold trapF
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  rw [hGx, hGy, hFx, hFy]
  exact ⟨by linarith, by linarith⟩

lemma trapG_step_trans {a b x z y : ℝ} (hxz : x ≤ z) (hzy : z ≤ y)
    (h1 : trapF a b z * (z - x) ≤ trapG a b z - trapG a b x ∧
          trapG a b z - trapG a b x ≤ trapF a b x * (z - x))
    (h2 : trapF a b y * (y - z) ≤ trapG a b y - trapG a b z ∧
          trapG a b y - trapG a b z ≤ trapF a b z * (y - z)) :
    trapF a b y * (y - x) ≤ trapG a b y - trapG a b x ∧
    trapG a b y - trapG a b x ≤ trapF a b x * (y - x) := by
  have hFyFz : trapF a b y ≤ trapF a b z := trapF_anti hzy
  have hFzFx : trapF a b z ≤ trapF a b x := trapF_anti hxz
  constructor <;> nlinarith

lemma trapG_step_bounds {a b x y : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) :
    trapF a b y * (y - x) ≤ trapG a b y - trapG a b x ∧
    trapG a b y - trapG a b x ≤ trapF a b x * (y - x) := by
  by_cases hx1 : x ≤ b - a
  · by_cases hy1 : y ≤ b - a
    · exact trapG_step_seg1 ha hxy hy1
    · push Not at hy1
      by_cases hy2 : y ≤ a + b
      · exact trapG_step_trans hx1 hy1.le
          (trapG_step_seg1 ha hx1 le_rfl)
          (trapG_step_seg2 le_rfl hy1.le hy2)
      · push Not at hy2
        have hba_ab : b - a ≤ a + b := by linarith
        exact trapG_step_trans (hx1.trans hba_ab) hy2.le
          (trapG_step_trans hx1 hba_ab
            (trapG_step_seg1 ha hx1 le_rfl)
            (trapG_step_seg2 le_rfl hba_ab le_rfl))
          (trapG_step_seg3 ha le_rfl hy2.le)
  · push Not at hx1
    by_cases hx2 : x ≤ a + b
    · by_cases hy2 : y ≤ a + b
      · exact trapG_step_seg2 hx1.le hxy hy2
      · push Not at hy2
        exact trapG_step_trans hx2 hy2.le
          (trapG_step_seg2 hx1.le hx2 le_rfl)
          (trapG_step_seg3 ha le_rfl hy2.le)
    · push Not at hx2
      exact trapG_step_seg3 ha hx2.le hxy

lemma pairQ_bounds_coprime {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    0 ≤ pairQ u v δ ∧
    4 * δ ^ 2 - 4 * δ / (max u v : ℝ) ≤ pairQ u v δ ∧
    pairQ u v δ ≤ 4 * δ ^ 2 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  let r₁ := δ / (u : ℝ)
  let r₂ := δ / (v : ℝ)
  let a := min r₁ r₂
  let b := max r₁ r₂
  have ha : 0 ≤ a := le_min (by positivity) (by positivity)
  have hab : a ≤ b := min_le_max
  have hab_add : a + b = r₁ + r₂ := min_add_max r₁ r₂
  have hab_mul : a * b = r₁ * r₂ := min_mul_max r₁ r₂
  have hof : ∀ y : ℝ, 0 ≤ y → overlapF r₁ r₂ y = trapF a b y := by
    intro y hy
    simp only [overlapF, trapF, abs_of_nonneg hy, a, b, hab_add]
  let h : ℝ := 1 / ((u : ℝ) * (v : ℝ))
  have hh : 0 < h := by positivity
  let M : ℕ := u + v
  have hG0 : trapG a b 0 = 0 := by
    unfold trapG
    rw [if_pos (by linarith)]
    ring
  have hMh_ge : a + b ≤ (M : ℝ) * h := by
    have hM : (M : ℝ) * h = 1 / (u : ℝ) + 1 / (v : ℝ) := by
      dsimp only [M, h]; push_cast; field_simp; ring
    rw [hM, hab_add]
    dsimp only [r₁, r₂]
    have h1 : δ / (u : ℝ) ≤ 1 / (u : ℝ) := div_le_div_of_nonneg_right (by linarith) huR.le
    have h2 : δ / (v : ℝ) ≤ 1 / (v : ℝ) := div_le_div_of_nonneg_right (by linarith) hvR.le
    linarith
  have hGM : trapG a b ((M : ℝ) * h) = 2 * a * b := by
    unfold trapG
    split_ifs with h1 h2
    · have ha0 : a = 0 := by linarith
      rw [ha0]; ring
    · have : (M : ℝ) * h = a + b := le_antisymm h2 hMh_ge
      rw [this]; ring
    · rfl
  have htele : ∑ k ∈ Finset.range M,
      (trapG a b (((k + 1 : ℕ) : ℝ) * h) - trapG a b ((k : ℝ) * h)) = 2 * a * b := by
    rw [Finset.sum_range_sub (fun k => trapG a b ((k : ℝ) * h)) M]
    simp [hG0, hGM]
  have hsum_lower :
      (∑ k ∈ Finset.range M, trapF a b (((k + 1 : ℕ) : ℝ) * h)) * h ≤ 2 * a * b := by
    rw [← htele, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hh.le
    have hstep := trapG_step_bounds ha (b := b) hle
    have hdiff : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
    rw [hdiff] at hstep
    exact hstep.1
  have hsum_upper :
      2 * a * b ≤ (∑ k ∈ Finset.range M, trapF a b ((k : ℝ) * h)) * h := by
    rw [← htele, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hh.le
    have hstep := trapG_step_bounds ha (b := b) hle
    have hdiff : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
    rw [hdiff] at hstep
    exact hstep.2
  have hshift_sum : ∑ k ∈ Finset.range M, trapF a b (((k + 1 : ℕ) : ℝ) * h) =
      ∑ j ∈ Finset.Icc (1 : ℕ) M, trapF a b ((j : ℝ) * h) := by
    refine Finset.sum_nbij (· + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]; omega
    · intro k₁ _ k₂ _ heq
      dsimp at heq; omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_Icc] at hj
      exact ⟨j - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
    · intro k _; rfl
  have hQ_eq : pairQ u v δ = 2 * ∑ j ∈ Finset.Icc (1 : ℕ) M, trapF a b ((j : ℝ) * h) := by
    rw [pairQ_coprime_eq_sum hu hv hcop hδ0 hδ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have harg : (j : ℝ) / ((u : ℝ) * (v : ℝ)) = (j : ℝ) * h := by dsimp only [h]; ring
    rw [harg, hof _ (by positivity)]
  have hrange_le : ∑ k ∈ Finset.range M, trapF a b ((k : ℝ) * h) ≤
      trapF a b 0 + ∑ j ∈ Finset.Icc (1 : ℕ) M, trapF a b ((j : ℝ) * h) := by
    have hMpos : 0 < M := by omega
    rw [Finset.sum_range_eq_add_Ico _ hMpos]
    simp only [Nat.cast_zero, zero_mul, add_le_add_iff_left]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => le_max_left _ _)
    intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_Icc]; omega
  have h2ab : 2 * (2 * a * b) / h = 4 * δ ^ 2 := by
    rw [mul_assoc 2 a b, hab_mul]
    dsimp only [r₁, r₂, h]
    field_simp
    ring
  have hF0 : trapF a b 0 = 2 * δ / max (u : ℝ) (v : ℝ) := by
    unfold trapF
    rw [sub_zero, min_eq_left (by linarith), max_eq_right (by linarith)]
    dsimp only [a, r₁, r₂]
    rcases le_total u v with huv | hvu
    · have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
      have hdiv : δ / (v : ℝ) ≤ δ / (u : ℝ) := div_le_div_of_nonneg_left hδ0.le huR huvR
      rw [min_eq_right hdiv, max_eq_right huvR]; ring
    · have hvuR : (v : ℝ) ≤ (u : ℝ) := by exact_mod_cast hvu
      have hdiv : δ / (u : ℝ) ≤ δ / (v : ℝ) := div_le_div_of_nonneg_left hδ0.le hvR hvuR
      rw [min_eq_left hdiv, max_eq_left hvuR]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ_eq]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  · rw [hQ_eq]
    have h1 : 2 * a * b ≤ (trapF a b 0 + ∑ j ∈ Finset.Icc (1 : ℕ) M, trapF a b ((j : ℝ) * h)) * h :=
      hsum_upper.trans (mul_le_mul_of_nonneg_right hrange_le hh.le)
    have h2 : 2 * (2 * a * b) / h ≤
        2 * trapF a b 0 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) M, trapF a b ((j : ℝ) * h) := by
      rw [div_le_iff₀ hh]
      linarith
    rw [h2ab, hF0] at h2
    have h4 : 2 * (2 * δ / max (u : ℝ) (v : ℝ)) = 4 * δ / max (u : ℝ) (v : ℝ) := by ring
    linarith
  · rw [hQ_eq]
    rw [hshift_sum] at hsum_lower
    have h1 : 2 * ∑ j ∈ Finset.Icc (1 : ℕ) M, trapF a b ((j : ℝ) * h) ≤ 2 * (2 * a * b) / h := by
      rw [le_div_iff₀ hh]
      linarith
    rwa [h2ab] at h1

theorem pair_intersection_bounds {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    0 ≤ pairQ u v δ ∧
    4 * δ ^ 2 - 4 * δ * (Nat.gcd u v : ℝ) / (max u v : ℝ) ≤ pairQ u v δ ∧
    pairQ u v δ ≤ 4 * δ ^ 2 := by
  let d := Nat.gcd u v
  let u' := u / d
  let v' := v / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left v hu
  have hu_eq : d * u' = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hv_eq : d * v' = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hu' : 0 < u' := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hu_eq; exact hu.ne' hu_eq.symm
  have hv' : 0 < v' := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hv_eq; exact hv.ne' hv_eq.symm
  have hcop : Nat.Coprime u' v' := Nat.coprime_div_gcd_div_gcd hd
  have hmaxN : max u v = d * max u' v' := by
    rw [← hu_eq, ← hv_eq, Nat.mul_max_mul_left]
  have hmax : max (u : ℝ) (v : ℝ) = (d : ℝ) * max (u' : ℝ) (v' : ℝ) := by
    rw [← Nat.cast_max, hmaxN, Nat.cast_mul, Nat.cast_max]
  have hb := pairQ_bounds_coprime hu' hv' hcop hδ0 hδ
  rw [← pairQ_reduce_gcd hu hv δ] at hb
  refine ⟨hb.1, ?_, hb.2.2⟩
  have hfrac : 4 * δ * (Nat.gcd u v : ℝ) / max (u : ℝ) (v : ℝ) = 4 * δ / max (u' : ℝ) (v' : ℝ) := by
    change 4 * δ * (d : ℝ) / max (u : ℝ) (v : ℝ) = 4 * δ / max (u' : ℝ) (v' : ℝ)
    rw [hmax]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  rw [hfrac]
  exact hb.2.1

/- ### Section 4: Assembly of Tao's 2017 theorem (Section 8) -/

lemma offDiag_symm_card (V : Finset ℕ) (P : ℕ → ℕ → Prop) [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)]
    (hPsym : ∀ a b, P a b ↔ P b a) :
    (V.offDiag.filter (fun p => P p.1 p.2)).card =
      2 * (V.offDiag.filter (fun p => p.1 < p.2 ∧ P p.1 p.2)).card := by
  classical
  let S := V.offDiag.filter (fun p => P p.1 p.2)
  let S1 := V.offDiag.filter (fun p => p.1 < p.2 ∧ P p.1 p.2)
  let S2 := V.offDiag.filter (fun p => p.2 < p.1 ∧ P p.1 p.2)
  have hunion : S = S1 ∪ S2 := by
    ext ⟨a, b⟩
    simp only [S, S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨ha, hb, hne⟩, hP⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨ha, hb, hne⟩, h, hP⟩
      · exact Or.inr ⟨⟨ha, hb, hne⟩, h, hP⟩
    · rintro (⟨h, _, hP⟩ | ⟨h, _, hP⟩) <;> exact ⟨h, hP⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S1, S2, Finset.mem_filter] at hp1 hp2
    omega
  have hcard_eq : S2.card = S1.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro ⟨a, b⟩ h
      simp only [S1, S2, Finset.mem_filter, Finset.mem_offDiag] at h ⊢
      exact ⟨⟨h.1.2.1, h.1.1, h.1.2.2.symm⟩, h.2.1, (hPsym a b).mp h.2.2⟩
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2 heq.1
    · intro ⟨a, b⟩ h
      refine ⟨(b, a), ?_, rfl⟩
      simp only [S1, S2, Finset.mem_filter, Finset.mem_offDiag] at h ⊢
      exact ⟨⟨h.1.2.1, h.1.1, h.1.2.2.symm⟩, h.2.1, (hPsym a b).mp h.2.2⟩
  change S.card = 2 * S1.card
  rw [hunion, Finset.card_union_of_disjoint hdisj, hcard_eq, two_mul]

lemma gVol_lower_bound_of_inputs
    (hArith : ∀ (C : ℝ), 1 ≤ C → ∀ (ε : ℝ), 0 < ε → ∃ κ > 0,
      ∀ (V : Finset ℕ), 2 ≤ V.card → (∀ v ∈ V, 0 < v) →
        ε * (V.card : ℝ) ^ 2 ≤
          ((V.offDiag.filter (fun p => p.1 < p.2 ∧
            (max p.1 p.2 : ℝ) ≤ C * (V.card : ℝ) * (Nat.gcd p.1 p.2 : ℝ))).card : ℝ) →
        κ ≤ typeILoss V (1 / (2 * (V.card : ℝ))))
    (hSpill : ∀ (V : Finset ℕ), (∀ v ∈ V, 0 < v) →
      ∀ {δ₀ δ₁ : ℝ}, 0 < δ₀ → δ₀ ≤ δ₁ → δ₁ < 1 / 2 →
        (δ₁ / δ₀) * (pVol V δ₀ - 2 * wVol V δ₀) ≤ pVol V δ₁ - 2 * wVol V δ₁) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 5 / 96 ∧
      ∀ (V : Finset ℕ), 2 ≤ V.card → (∀ v ∈ V, 0 < v) →
        κ₀ ≤ gVol V (1 / (2 * (V.card : ℝ))) := by
  classical
  obtain ⟨κ₁, hκ₁, hDense⟩ := hArith 64 (by norm_num) (1 / 64) (by norm_num)
  refine ⟨min κ₁ (5 / 96), lt_min hκ₁ (by norm_num), min_le_right _ _, ?_⟩
  intro V hn hV
  let n : ℕ := V.card
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  let δ₀ : ℝ := 1 / (2 * (n : ℝ))
  let δ₁ : ℝ := 3 / (4 * (n : ℝ))
  have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀_le : δ₀ ≤ δ₁ := by
    dsimp [δ₀, δ₁]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hδ₁_lt : δ₁ < 1 / 2 := by
    dsimp [δ₁]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ₀_lt : δ₀ < 1 / 2 := lt_of_le_of_lt hδ₀_le hδ₁_lt
  have hδ₁_pos : 0 < δ₁ := lt_of_lt_of_le hδ₀_pos hδ₀_le
  let Sunord := V.offDiag.filter (fun p => p.1 < p.2 ∧
    (max p.1 p.2 : ℝ) ≤ 64 * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ))
  by_cases hcase : (1 / 64 : ℝ) * (n : ℝ) ^ 2 ≤ (Sunord.card : ℝ)
  · exact (min_le_left _ _).trans ((hDense V hn hV hcase).trans (typeILoss_le_gVol_baseline hn hV))
  · push Not at hcase
    let Sord := V.offDiag.filter (fun p =>
      (max p.1 p.2 : ℝ) ≤ 64 * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ))
    let Sgood := V.offDiag.filter (fun p =>
      ¬ ((max p.1 p.2 : ℝ) ≤ 64 * (n : ℝ) * (Nat.gcd p.1 p.2 : ℝ)))
    have hSord_card : Sord.card = 2 * Sunord.card :=
      offDiag_symm_card V (fun a b => (max a b : ℝ) ≤ 64 * (n : ℝ) * (Nat.gcd a b : ℝ))
        (fun a b => by rw [max_comm, Nat.gcd_comm])
    have hSord_lt : (Sord.card : ℝ) < (1 / 32 : ℝ) * (n : ℝ) ^ 2 := by
      have : (Sord.card : ℝ) = 2 * (Sunord.card : ℝ) := by exact_mod_cast hSord_card
      linarith
    have hcard_split : Sord.card + Sgood.card = V.offDiag.card := by
      have hun : Sord ∪ Sgood = V.offDiag := by
        ext p
        simp only [Sord, Sgood, Finset.mem_union, Finset.mem_filter]
        tauto
      have hdj : Disjoint Sord Sgood := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Sord, Sgood, Finset.mem_filter] at hp1 hp2
        exact hp2.2 hp1.2
      rw [← Finset.card_union_of_disjoint hdj, hun]
    have hoffDiag_card : (V.offDiag.card : ℝ) = (n : ℝ) ^ 2 - (n : ℝ) := by
      rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self V.card), Nat.cast_mul]
      dsimp [n]; ring
    have hSgood_ge : (n : ℝ) ^ 2 - (n : ℝ) - (1 / 32 : ℝ) * (n : ℝ) ^ 2 ≤ (Sgood.card : ℝ) := by
      have hcast : (Sord.card : ℝ) + (Sgood.card : ℝ) = (V.offDiag.card : ℝ) := by
        exact_mod_cast hcard_split
      linarith
    have hQ0_lower : 1 - 1 / (n : ℝ) - 1 / 16 ≤ qVol V δ₀ := by
      have hsub : Sgood ⊆ V.offDiag := Finset.filter_subset _ _
      have hnonneg : ∀ p ∈ V.offDiag, 0 ≤ pairQ p.1 p.2 δ₀ := fun p hp => by
        rcases Finset.mem_offDiag.mp hp with ⟨h1, h2, _⟩
        exact (pair_intersection_bounds (hV _ h1) (hV _ h2) hδ₀_pos hδ₀_lt).1
      have hgood_term : ∀ p ∈ Sgood, (31 / 32 : ℝ) / (n : ℝ) ^ 2 ≤ pairQ p.1 p.2 δ₀ := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpO, hngt⟩
        rcases Finset.mem_offDiag.mp hpO with ⟨h1, h2, _⟩
        push Not at hngt
        have hpb := (pair_intersection_bounds (hV _ h1) (hV _ h2) hδ₀_pos hδ₀_lt).2.1
        have hmax_pos : (0 : ℝ) < (max p.1 p.2 : ℝ) := by
          exact_mod_cast lt_of_lt_of_le (hV _ h1) (le_max_left _ _)
        have hfrac : (Nat.gcd p.1 p.2 : ℝ) / (max p.1 p.2 : ℝ) ≤ 1 / (64 * (n : ℝ)) := by
          rw [div_le_div_iff₀ hmax_pos (by positivity)]
          linarith
        have h4d2 : 4 * δ₀ ^ 2 = 1 / (n : ℝ) ^ 2 := by dsimp [δ₀]; field_simp; ring
        have h4d : 4 * δ₀ * (Nat.gcd p.1 p.2 : ℝ) / (max p.1 p.2 : ℝ) ≤
            (1 / 32 : ℝ) / (n : ℝ) ^ 2 := by
          have : 4 * δ₀ * (Nat.gcd p.1 p.2 : ℝ) / (max p.1 p.2 : ℝ) =
              (2 / (n : ℝ)) * ((Nat.gcd p.1 p.2 : ℝ) / (max p.1 p.2 : ℝ)) := by
            dsimp [δ₀]; field_simp; ring
          rw [this]
          calc
            (2 / (n : ℝ)) * ((Nat.gcd p.1 p.2 : ℝ) / (max p.1 p.2 : ℝ))
                ≤ (2 / (n : ℝ)) * (1 / (64 * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ = (1 / 32 : ℝ) / (n : ℝ) ^ 2 := by field_simp; ring
        have hsub31 : (31 / 32 : ℝ) / (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 2 - (1 / 32 : ℝ) / (n : ℝ) ^ 2 := by
          ring
        linarith
      calc
        1 - 1 / (n : ℝ) - 1 / 16
            ≤ (31 / 32 : ℝ) * (1 - 1 / (n : ℝ) - 1 / 32) := by
          have : 0 ≤ 1 / (n : ℝ) := by positivity
          linarith
        _ = ((n : ℝ) ^ 2 - (n : ℝ) - (1 / 32 : ℝ) * (n : ℝ) ^ 2) *
              ((31 / 32 : ℝ) / (n : ℝ) ^ 2) := by
          field_simp
        _ ≤ (Sgood.card : ℝ) * ((31 / 32 : ℝ) / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hSgood_ge (by positivity)
        _ = ∑ _p ∈ Sgood, ((31 / 32 : ℝ) / (n : ℝ) ^ 2) := by simp
        _ ≤ ∑ p ∈ Sgood, pairQ p.1 p.2 δ₀ := Finset.sum_le_sum hgood_term
        _ ≤ ∑ p ∈ V.offDiag, pairQ p.1 p.2 δ₀ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnonneg p hp
    have hQ1_upper : qVol V δ₁ ≤ (9 / 4 : ℝ) * (1 - 1 / (n : ℝ)) := by
      calc
        qVol V δ₁ = ∑ p ∈ V.offDiag, pairQ p.1 p.2 δ₁ := rfl
        _ ≤ ∑ _p ∈ V.offDiag, (4 * δ₁ ^ 2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rcases Finset.mem_offDiag.mp hp with ⟨h1, h2, _⟩
          exact (pair_intersection_bounds (hV _ h1) (hV _ h2) hδ₁_pos hδ₁_lt).2.2
        _ = (V.offDiag.card : ℝ) * (4 * δ₁ ^ 2) := by simp
        _ = ((n : ℝ) ^ 2 - (n : ℝ)) * (4 * (3 / (4 * (n : ℝ))) ^ 2) := by rw [hoffDiag_card]
        _ = (9 / 4 : ℝ) * (1 - 1 / (n : ℝ)) := by field_simp; ring
    have hratio : δ₁ / δ₀ = 3 / 2 := by dsimp [δ₀, δ₁]; field_simp; ring
    have hw0 : wVol V δ₀ = gVol V δ₀ := by
      rw [wVol_eq hV hδ₀_pos hδ₀_lt]
      have : 2 * δ₀ * (n : ℝ) = 1 := by dsimp [δ₀]; field_simp
      change 2 * δ₀ * (n : ℝ) - 1 + gVol V δ₀ = gVol V δ₀
      linarith
    have hw1 : (1 / 2 : ℝ) ≤ wVol V δ₁ := by
      rw [wVol_eq hV hδ₁_pos hδ₁_lt]
      have : 2 * δ₁ * (n : ℝ) = 3 / 2 := by dsimp [δ₁]; field_simp; ring
      have hg1 : 0 ≤ gVol V δ₁ := MeasureTheory.measureReal_nonneg
      change (1 / 2 : ℝ) ≤ 2 * δ₁ * (n : ℝ) - 1 + gVol V δ₁
      linarith
    have hsp := hSpill V hV hδ₀_pos hδ₀_le hδ₁_lt
    have hlin0 := pVol_sub_qVol V δ₀
    have hlin1 := pVol_sub_qVol V δ₁
    have hlin_cancel : pVol V δ₁ - (δ₁ / δ₀) * pVol V δ₀ =
        qVol V δ₁ - (δ₁ / δ₀) * qVol V δ₀ := by
      have h1 : pVol V δ₁ - qVol V δ₁ = (δ₁ / δ₀) * (pVol V δ₀ - qVol V δ₀) := by
        rw [hlin0, hlin1]
        field_simp [hδ₀_pos.ne']
      linarith
    have hspQ : (3 / 2 : ℝ) * (qVol V δ₀ - 2 * gVol V δ₀) ≤ qVol V δ₁ - 2 * wVol V δ₁ := by
      rw [hratio, hw0] at hsp
      rw [hratio] at hlin_cancel
      linarith only [hsp, hlin_cancel]
    have h3g : (5 / 32 : ℝ) ≤ 3 * gVol V δ₀ := by
      have hnpos_inv : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith only [hspQ, hQ0_lower, hQ1_upper, hw1, hnpos_inv]
    exact (min_le_right _ _).trans (by linarith only [h3g])

lemma exists_lonely_time_pos {V : Finset ℕ} (hn : 2 ≤ V.card) (hV : ∀ v ∈ V, 0 < v)
    {κ₀ : ℝ} (hκ₀_pos : 0 < κ₀) (hκ₀_le : κ₀ ≤ 5 / 96)
    (hg : κ₀ ≤ gVol V (1 / (2 * (V.card : ℝ)))) :
    ∃ t : AddCircle (1 : ℝ), ∀ v ∈ V,
      1 / (2 * (V.card : ℝ)) + (κ₀ / 4) / (V.card : ℝ) ≤ dist ((v : ℤ) • t) 0 := by
  let n : ℕ := V.card
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let δ₀ : ℝ := 1 / (2 * (n : ℝ))
  let δ : ℝ := 1 / (2 * (n : ℝ)) + (κ₀ / 4) / (n : ℝ)
  have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀_le : δ₀ ≤ δ := by dsimp [δ₀, δ]; linarith [show 0 < (κ₀ / 4) / (n : ℝ) by positivity]
  have hδ_pos : 0 < δ := lt_of_lt_of_le hδ₀_pos hδ₀_le
  have hδ_lt : δ < 1 / 2 := by
    dsimp [δ]
    have h1 : 1 / (2 * (n : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h2 : (κ₀ / 4) / (n : ℝ) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h3 : (κ₀ / 4) / (n : ℝ) < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hδ₀_lt : δ₀ < 1 / 2 := lt_of_le_of_lt hδ₀_le hδ_lt
  have hsub : Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ) ⊆
      (Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ₀)) ∪
        ⋃ v ∈ V, (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \ (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀) := by
    intro x ⟨hxI, hxU⟩
    by_cases h0 : x ∈ ⋃ v ∈ V, bohrLift v δ₀
    · exact Or.inl ⟨hxI, h0⟩
    · right
      simp only [mem_iUnion] at hxU h0 ⊢
      push Not at h0
      rcases hxU with ⟨v, hv, hxv⟩
      exact ⟨v, hv, ⟨hxI, hxv⟩, fun h => h0 v hv h.2⟩
  have hvol_diff : ∀ v ∈ V,
      volume.real ((Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \ (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀)) =
        2 * (δ - δ₀) := by
    intro v hv
    have hmono : Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀ ⊆ Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ :=
      inter_subset_inter_right _ (bohrLift_mono (hV v hv) hδ₀_le)
    have hm0 : MeasurableSet (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀) :=
      measurableSet_Ico.inter (measurableSet_bohrLift v δ₀)
    have hfin : volume (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) ≠ ⊤ :=
      (measure_mono inter_subset_left).trans_lt (by simp [Real.volume_Ico]) |>.ne
    rw [measureReal_sdiff (μ := volume) hmono hm0 hfin,
      volume_real_Ico_inter_bohrLift (hV v hv) hδ_pos hδ_lt,
      volume_real_Ico_inter_bohrLift (hV v hv) hδ₀_pos hδ₀_lt]
    ring
  have hvol_lt : volume.real (Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ)) < 1 := by
    have h1 : volume.real (Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ₀)) ≤ 1 - κ₀ := by
      have := gVol_eq_one_sub_union V δ₀
      linarith
    have hsub_Ico :
        (Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ₀)) ∪
          ⋃ v ∈ V, (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \ (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀) ⊆
        Set.Ico (0 : ℝ) 1 := by
      refine union_subset inter_subset_left ?_
      refine iUnion₂_subset fun v _ => Set.sdiff_subset.trans inter_subset_left
    have hfin_rhs :
        volume ((Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ₀)) ∪
          ⋃ v ∈ V, (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \ (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀)) ≠ ⊤ :=
      ((measure_mono hsub_Ico).trans_lt (by simp [Real.volume_Ico])).ne
    have h2 : volume.real (Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ)) ≤
        volume.real (Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ₀)) +
        ∑ v ∈ V, volume.real ((Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \
          (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀)) :=
      (measureReal_mono hsub hfin_rhs).trans
        ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_biUnion_finset_le V _)))
    have hsum : ∑ v ∈ V, volume.real ((Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \
          (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀)) = κ₀ / 2 := by
      calc
        ∑ v ∈ V, volume.real ((Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ) \
            (Set.Ico (0 : ℝ) 1 ∩ bohrLift v δ₀))
            = ∑ _v ∈ V, (2 * (δ - δ₀)) := Finset.sum_congr rfl hvol_diff
        _ = (n : ℝ) * (2 * (δ - δ₀)) := by simp [n]
        _ = κ₀ / 2 := by dsimp [δ, δ₀]; field_simp; ring
    linarith
  have hne : (Set.Ico (0 : ℝ) 1 \ ⋃ v ∈ V, bohrLift v δ).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hempty
    have heq : Set.Ico (0 : ℝ) 1 ∩ (⋃ v ∈ V, bohrLift v δ) = Set.Ico (0 : ℝ) 1 :=
      Set.inter_eq_left.mpr hempty
    rw [heq, volume_real_Ico_eq (by norm_num : (0 : ℝ) ≤ 1)] at hvol_lt
    linarith
  rcases hne with ⟨x, _, hx_not⟩
  refine ⟨(x : AddCircle (1 : ℝ)), fun v hv => ?_⟩
  have hxv : x ∉ bohrLift v δ := fun h => hx_not (mem_iUnion₂.mpr ⟨v, hv, h⟩)
  have hdist_m : ∀ m : ℤ, δ ≤ |(v : ℝ) * x - (m : ℝ)| := by
    intro m
    by_contra hlt
    push Not at hlt
    rw [abs_lt] at hlt
    apply hxv
    rw [bohrLift_eq_iUnion, mem_iUnion]
    refine ⟨m, ?_⟩
    rw [mem_bohrCell_iff (hV v hv)]
    exact ⟨by linarith, by linarith⟩
  rw [← AddCircle.coe_zsmul 1, dist_zero_right, AddCircle.norm_eq 1]
  simp only [inv_one, one_mul, mul_one, zsmul_eq_mul, Int.cast_natCast]
  exact hdist_m (round ((v : ℝ) * x))

private lemma signed_speeds_of_positive {n : ℕ} {d : ℝ}
    (hpos : ∀ v : Fin n ↪ ℕ, (∀ i, 0 < v i) →
      ∃ t : AddCircle (1 : ℝ), ∀ i, d ≤ dist ((v i : ℤ) • t) 0)
    (v : Fin n → ℤ) (hv : ∀ i, v i ≠ 0) :
    ∃ t : AddCircle (1 : ℝ), ∀ i, d ≤ dist (v i • t) 0 := by
  classical
  let s : Finset ℕ := Finset.univ.image fun i : Fin n => (v i).natAbs - 1
  have hs : s.card ≤ n := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (v i).natAbs - 1))
  obtain ⟨S, hS, hcard⟩ := Infinite.exists_superset_card_eq s n hs
  let e := (S.equivFinOfCardEq hcard).symm
  let w : Fin n ↪ ℕ := ⟨fun j => (e j).val + 1, by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact Nat.add_right_cancel hij⟩
  obtain ⟨t, ht⟩ := hpos w (fun _ => Nat.zero_lt_succ _)
  refine ⟨t, fun i => ?_⟩
  have hi : (v i).natAbs - 1 ∈ S := hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let a : S := ⟨(v i).natAbs - 1, hi⟩
  have hw : w (e.symm a) = (v i).natAbs := by
    change (e (e.symm a)).val + 1 = _
    rw [Equiv.apply_symm_apply]
    change (v i).natAbs - 1 + 1 = (v i).natAbs
    exact Nat.sub_add_cancel (Int.natAbs_pos.mpr (hv i))
  have htime := ht (e.symm a)
  rw [hw] at htime
  rcases le_or_gt 0 (v i) with hi | hi
  · have he : ((v i).natAbs : ℤ) = v i := Int.natAbs_of_nonneg hi
    simpa only [he] using htime
  · have he : ((v i).natAbs : ℤ) = -(v i) := by
      simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg (neg_nonneg.mpr hi.le)
    simpa only [he, neg_zsmul, dist_zero_right, norm_neg] using htime

private lemma log_gain_le (x k : ℝ) (hx : Real.exp (Real.exp 1) ≤ x) (hk : 0 ≤ k) :
    k * Real.log x / (x ^ 2 * Real.log (Real.log x) ^ 2) ≤ k / x := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : Real.exp 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
  have hloglog : 1 ≤ Real.log (Real.log x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlog
  have hsq : (1 : ℝ) ≤ Real.log (Real.log x) ^ 2 := by nlinarith
  have hxlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
  apply (div_le_div_iff₀ (by positivity) hxpos).2
  calc
    k * Real.log x * x ≤ k * x * x := by gcongr
    _ = k * x ^ 2 := by ring
    _ ≤ k * (x ^ 2 * Real.log (Real.log x) ^ 2) := by
      rw [← mul_assoc]
      exact le_mul_of_one_le_right (by positivity) hsq

theorem tao_2017_of_inputs
    (hArith : ∀ (C : ℝ), 1 ≤ C → ∀ (ε : ℝ), 0 < ε → ∃ κ > 0,
      ∀ (V : Finset ℕ), 2 ≤ V.card → (∀ v ∈ V, 0 < v) →
        ε * (V.card : ℝ) ^ 2 ≤
          ((V.offDiag.filter (fun p => p.1 < p.2 ∧
            (max p.1 p.2 : ℝ) ≤ C * (V.card : ℝ) * (Nat.gcd p.1 p.2 : ℝ))).card : ℝ) →
        κ ≤ typeILoss V (1 / (2 * (V.card : ℝ))))
    (hSpill : ∀ (V : Finset ℕ), (∀ v ∈ V, 0 < v) →
      ∀ {δ₀ δ₁ : ℝ}, 0 < δ₀ → δ₀ ≤ δ₁ → δ₁ < 1 / 2 →
        (δ₁ / δ₀) * (pVol V δ₀ - 2 * wVol V δ₀) ≤ pVol V δ₁ - 2 * wVol V δ₁) :
    type_of% @LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017 := by
  obtain ⟨κ₀, hκ₀_pos, hκ₀_le, hG⟩ := gVol_lower_bound_of_inputs hArith hSpill
  refine ⟨κ₀ / 4, by positivity, ?_⟩
  have hcast : ∀ᶠ n : ℕ in atTop, Real.exp (Real.exp 1) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 : ℕ), hcast] with n hn hnx
  have hnpos : 0 < n := by omega
  unfold LonelyRunnerConjecture.deltaGap
  apply le_csInf
  · let w : Fin n ↪ ℤ := ⟨fun i => (i.val : ℤ) + 1, by
      intro i j h
      change (i.val : ℤ) + 1 = (j.val : ℤ) + 1 at h
      apply Fin.ext
      omega⟩
    exact ⟨LonelyRunnerConjecture.deltaTuple w, w,
      fun i => by change (i.val : ℤ) + 1 ≠ 0; omega, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have ht : ∃ t : AddCircle (1 : ℝ), ∀ i : Fin n,
        1 / (2 * (n : ℝ)) + (κ₀ / 4) / (n : ℝ) ≤ dist (v i • t) 0 := by
      refine signed_speeds_of_positive (fun w hw => ?_) v hv
      let V : Finset ℕ := Finset.univ.image w
      have hcard : V.card = n := by
        rw [Finset.card_image_of_injective _ w.injective, Finset.card_fin]
      have hVpos : ∀ u ∈ V, 0 < u := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨i, _, rfl⟩
        exact hw i
      have hVn : 2 ≤ V.card := by omega
      obtain ⟨t, ht⟩ := exists_lonely_time_pos hVn hVpos hκ₀_pos hκ₀_le (hG V hVn hVpos)
      rw [hcard] at ht
      exact ⟨t, fun i => ht (w i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
    unfold LonelyRunnerConjecture.deltaTuple
    refine (add_le_add le_rfl (log_gain_le (n : ℝ) (κ₀ / 4) hnx (by positivity))).trans ?_
    apply le_csSup
    · refine ⟨1 / 2, ?_⟩
      rintro r ⟨t, htr⟩
      refine (htr ⟨0, hnpos⟩).trans ?_
      simpa [dist_zero_right] using AddCircle.norm_le_half_period (1 : ℝ) (by norm_num)
        (x := v ⟨0, hnpos⟩ • t)
    · exact ht

end LRMod3

theorem OMA.solution :
    type_of% @LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017 :=
  LRMod3.tao_2017_of_inputs LRMod1Extract.hu_jing_typeILoss LRMod2.dilation_spillover
