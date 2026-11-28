import FormalConjectures.ErdosProblems.«36»
import Mathlib

/-!
# Core mathematical lemmas for Erdos Problem 36 lower bound

All arguments are 100% discrete (finite sums over `Finset ℤ`) with zero measure theory.
-/

namespace Erdos36Lower

open Filter Real Finset

/- ## Section 1: Discrete Setup and Exact Identities -/

def KSet (n : ℕ) : Finset ℤ := Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))

noncomputable def uCoord (n : ℕ) (t : ℤ) : ℝ :=
  (2 * (t : ℝ) - (2 * (n : ℝ) + 1)) / (2 * (n : ℝ))

noncomputable def mVal (n : ℕ) (A B : Finset ℤ) (k : ℤ) : ℝ :=
  (Erdos36.Overlap A B k : ℝ) / (n : ℝ)

noncomputable def EVal (n : ℕ) (A : Finset ℤ) : ℝ :=
  (2 / (n : ℝ)) * ∑ a ∈ A, uCoord n a

noncomputable def CVal (n : ℕ) (A : Finset ℤ) (ω : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ a ∈ A, Real.cos (ω * uCoord n a)

noncomputable def SVal (n : ℕ) (A : Finset ℤ) (ω : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ a ∈ A, Real.sin (ω * uCoord n a)

noncomputable def DVal (n : ℕ) (ω : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.cos (ω * uCoord n t)

lemma card_eq_n {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (hcard : A.card = B.card) :
    A.card = n ∧ B.card = n := by
  have h1 := Finset.card_union_of_disjoint hdisj
  rw [hunion, Int.card_Icc] at h1
  omega

lemma uCoord_sub {n : ℕ} (hn : 1 ≤ n) (a b : ℤ) :
    uCoord n a - uCoord n b = ((a - b : ℤ) : ℝ) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold uCoord
  push_cast
  field_simp
  ring

lemma uCoord_reflect (n : ℕ) (t : ℤ) :
    uCoord n (2 * (n : ℤ) + 1 - t) = -uCoord n t := by
  unfold uCoord
  push_cast
  ring

lemma uCoord_shift_n {n : ℕ} (hn : 1 ≤ n) (t : ℤ) :
    uCoord n (t + (n : ℤ)) = uCoord n t + 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold uCoord
  push_cast
  field_simp
  ring

lemma sum_overlap_mul {n : ℕ} {A B : Finset ℤ}
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (g : ℤ → ℝ) :
    ∑ k ∈ KSet n, g k * (Erdos36.Overlap A B k : ℝ) = ∑ a ∈ A, ∑ b ∈ B, g (a - b) := by
  have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * (n : ℤ)) := hunion ▸ Finset.subset_union_left
  have hB : B ⊆ Finset.Icc (1 : ℤ) (2 * (n : ℤ)) := hunion ▸ Finset.subset_union_right
  have hmaps : ∀ p ∈ A ×ˢ B, p.1 - p.2 ∈ KSet n := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have ha' := Finset.mem_Icc.mp (hA ha)
    have hb' := Finset.mem_Icc.mp (hB hb)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℤ × ℤ => g (p.1 - p.2))]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc
    g k * (Erdos36.Overlap A B k : ℝ)
        = ∑ _p ∈ (A ×ˢ B).filter (fun p : ℤ × ℤ => p.1 - p.2 = k), g k := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          rfl
    _ = ∑ p ∈ (A ×ˢ B).filter (fun p : ℤ × ℤ => p.1 - p.2 = k), g (p.1 - p.2) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [(Finset.mem_filter.mp hp).2]

lemma sum_uCoord_Icc (n : ℕ) :
    ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), uCoord n t = 0 := by
  have hbij : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), uCoord n t =
      ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), uCoord n (2 * (n : ℤ) + 1 - t) := by
    refine Finset.sum_bij (fun t _ => 2 * (n : ℤ) + 1 - t) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro b hb
      rcases Finset.mem_Icc.mp hb with ⟨h1, h2⟩
      exact ⟨2 * (n : ℤ) + 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro t _; congr 1; omega
  have hneg : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), uCoord n (2 * (n : ℤ) + 1 - t) =
      -(∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), uCoord n t) := by
    simp_rw [uCoord_reflect, Finset.sum_neg_distrib]
  linarith

lemma sum_sin_uCoord_Icc (n : ℕ) (ω : ℝ) :
    ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.sin (ω * uCoord n t) = 0 := by
  have hbij : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.sin (ω * uCoord n t) =
      ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.sin (ω * uCoord n (2 * (n : ℤ) + 1 - t)) := by
    refine Finset.sum_bij (fun t _ => 2 * (n : ℤ) + 1 - t) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro b hb
      rcases Finset.mem_Icc.mp hb with ⟨h1, h2⟩
      exact ⟨2 * (n : ℤ) + 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro t _; have : 2 * (n : ℤ) + 1 - (2 * (n : ℤ) + 1 - t) = t := by omega
      rw [this]
  have hneg : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.sin (ω * uCoord n (2 * (n : ℤ) + 1 - t)) =
      -(∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.sin (ω * uCoord n t)) := by
    simp_rw [uCoord_reflect, mul_neg, Real.sin_neg, Finset.sum_neg_distrib]
  linarith

private lemma sum_odd_sq_aux (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n), ((2 * (k : ℝ) + 1 - 2 * (n : ℝ)) ^ 2) =
      (2 * (n : ℝ)) * (4 * (n : ℝ) ^ 2 - 1) / 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.range (2 * (m + 1)) =
        insert 0 (insert (2 * m + 1) ((Finset.range (2 * m)).image (· + 1))) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro hx
        by_cases h0 : x = 0
        · left; exact h0
        · by_cases h1 : x = 2 * m + 1
          · right; left; exact h1
          · right; right; exact ⟨x - 1, by omega, by omega⟩
      · rintro (rfl | rfl | ⟨y, hy, rfl⟩) <;> omega
    rw [hsplit, Finset.sum_insert, Finset.sum_insert, Finset.sum_image]
    · have hmid : ∑ x ∈ Finset.range (2 * m),
          (2 * ((x + 1 : ℕ) : ℝ) + 1 - 2 * ((m + 1 : ℕ) : ℝ)) ^ 2 =
          ∑ x ∈ Finset.range (2 * m), (2 * (x : ℝ) + 1 - 2 * (m : ℝ)) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        push_cast; ring
      rw [hmid, ih]
      push_cast
      ring
    · intro a _ b _ h; dsimp at h; omega
    · simp only [Finset.mem_image, Finset.mem_range]
      rintro ⟨y, hy, h⟩; omega
    · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      rintro (h | ⟨y, _, h⟩) <;> omega

lemma sum_uCoord_sq_Icc {n : ℕ} (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), (uCoord n t) ^ 2 =
      2 / 3 - 1 / (6 * (n : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hbij : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), (uCoord n t) ^ 2 =
      ∑ k ∈ Finset.range (2 * n), ((2 * (k : ℝ) + 1 - 2 * (n : ℝ)) ^ 2) / (4 * (n : ℝ) ^ 2) := by
    refine Finset.sum_bij (fun t _ => (t - 1).toNat) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
      exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb h
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      omega
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      exact ⟨(k : ℤ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro t ht
      have ht' := Finset.mem_Icc.mp ht
      have hcast : (((t - 1).toNat : ℕ) : ℝ) = (t : ℝ) - 1 := by
        have h1 : ((t - 1).toNat : ℤ) = t - 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h1
      rw [hcast, uCoord]
      field_simp
      ring
  rw [hbij, ← Finset.sum_div, sum_odd_sq_aux]
  field_simp
  ring

lemma mass_eq {n : ℕ} {A B : Finset ℤ} (hn : 1 ≤ n)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (hcard : A.card = B.card) :
    (1 / (n : ℝ)) * ∑ k ∈ KSet n, mVal n A B k = 1 := by
  have ⟨hA, hB⟩ := card_eq_n hdisj hunion hcard
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h := sum_overlap_mul hunion (fun _ => (1 : ℝ))
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hA, hB] at h
  unfold mVal
  rw [← Finset.sum_div, h]
  field_simp

lemma mean_eq {n : ℕ} {A B : Finset ℤ} (hn : 1 ≤ n)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (hcard : A.card = B.card) :
    (1 / (n : ℝ)) * ∑ k ∈ KSet n, ((k : ℝ) / (n : ℝ)) * mVal n A B k = EVal n A := by
  have ⟨hA, hB⟩ := card_eq_n hdisj hunion hcard
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hsum_u : ∑ b ∈ B, uCoord n b = -(∑ a ∈ A, uCoord n a) := by
    have h1 := Finset.sum_union hdisj (f := uCoord n)
    rw [hunion, sum_uCoord_Icc] at h1
    linarith
  have h := sum_overlap_mul hunion (fun k : ℤ => (k : ℝ) / (n : ℝ))
  have h1 : ∑ k ∈ KSet n, ((k : ℝ) / (n : ℝ)) * mVal n A B k =
      (∑ a ∈ A, ∑ b ∈ B, (uCoord n a - uCoord n b)) / (n : ℝ) := by
    unfold mVal
    simp_rw [← mul_div_assoc, ← Finset.sum_div, h]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact (uCoord_sub hn a b).symm
  rw [h1]
  have h2 : ∑ a ∈ A, ∑ b ∈ B, (uCoord n a - uCoord n b) =
      (B.card : ℝ) * ∑ a ∈ A, uCoord n a - (A.card : ℝ) * ∑ b ∈ B, uCoord n b := by
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [h2, hA, hB, hsum_u]
  unfold EVal
  field_simp
  ring

lemma mom2_eq {n : ℕ} {A B : Finset ℤ} (hn : 1 ≤ n)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (hcard : A.card = B.card) :
    (1 / (n : ℝ)) * ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k =
      2 / 3 + (EVal n A) ^ 2 / 2 - 1 / (6 * (n : ℝ) ^ 2) := by
  have ⟨hA, hB⟩ := card_eq_n hdisj hunion hcard
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hsum_u : ∑ b ∈ B, uCoord n b = -(∑ a ∈ A, uCoord n a) := by
    have h1 := Finset.sum_union hdisj (f := uCoord n)
    rw [hunion, sum_uCoord_Icc] at h1
    linarith
  have hsum_sq : ∑ a ∈ A, (uCoord n a) ^ 2 + ∑ b ∈ B, (uCoord n b) ^ 2 =
      ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), (uCoord n t) ^ 2 := by
    rw [← Finset.sum_union hdisj, hunion]
  have h := sum_overlap_mul hunion (fun k : ℤ => ((k : ℝ) / (n : ℝ)) ^ 2)
  have h1 : ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k =
      (∑ a ∈ A, ∑ b ∈ B, (uCoord n a - uCoord n b) ^ 2) / (n : ℝ) := by
    unfold mVal
    simp_rw [← mul_div_assoc, ← Finset.sum_div, h]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← uCoord_sub hn a b]
  have h2 : ∑ a ∈ A, ∑ b ∈ B, (uCoord n a - uCoord n b) ^ 2 =
      (n : ℝ) * (∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), (uCoord n t) ^ 2) +
        2 * (∑ a ∈ A, uCoord n a) ^ 2 := by
    have hexp : ∀ a b : ℤ, (uCoord n a - uCoord n b) ^ 2 =
        (uCoord n a) ^ 2 - 2 * uCoord n a * uCoord n b + (uCoord n b) ^ 2 := fun a b => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have h2a : ∑ a ∈ A, 2 * uCoord n a = 2 * ∑ a ∈ A, uCoord n a := (Finset.mul_sum _ _ _).symm
    rw [hA, hB, hsum_u, h2a]
    linear_combination (n : ℝ) * hsum_sq
  rw [h1, h2]
  have hsq := sum_uCoord_sq_Icc hn
  unfold EVal
  field_simp at hsq ⊢
  nlinarith

lemma cos_eq {n : ℕ} {A B : Finset ℤ} (hn : 1 ≤ n)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (_hcard : A.card = B.card) (ω : ℝ) :
    (1 / (n : ℝ)) * ∑ k ∈ KSet n, Real.cos (ω * ((k : ℝ) / (n : ℝ))) * mVal n A B k =
      DVal n ω * CVal n A ω - (CVal n A ω) ^ 2 - (SVal n A ω) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hsum_c : ∑ b ∈ B, Real.cos (ω * uCoord n b) =
      (∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.cos (ω * uCoord n t)) -
        ∑ a ∈ A, Real.cos (ω * uCoord n a) := by
    have h1 := Finset.sum_union hdisj (f := fun t => Real.cos (ω * uCoord n t))
    rw [hunion] at h1; linarith
  have hsum_s : ∑ b ∈ B, Real.sin (ω * uCoord n b) = -(∑ a ∈ A, Real.sin (ω * uCoord n a)) := by
    have h1 := Finset.sum_union hdisj (f := fun t => Real.sin (ω * uCoord n t))
    rw [hunion, sum_sin_uCoord_Icc] at h1; linarith
  have h := sum_overlap_mul hunion (fun k : ℤ => Real.cos (ω * ((k : ℝ) / (n : ℝ))))
  have h1 : ∑ k ∈ KSet n, Real.cos (ω * ((k : ℝ) / (n : ℝ))) * mVal n A B k =
      (∑ a ∈ A, ∑ b ∈ B, Real.cos (ω * uCoord n a - ω * uCoord n b)) / (n : ℝ) := by
    have hdiv : ∑ k ∈ KSet n, Real.cos (ω * ((k : ℝ) / (n : ℝ))) * mVal n A B k =
        (∑ k ∈ KSet n, Real.cos (ω * ((k : ℝ) / (n : ℝ))) * (Erdos36.Overlap A B k : ℝ)) / (n : ℝ) := by
      unfold mVal; rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [hdiv, h]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_sub, uCoord_sub hn a b]
  rw [h1]
  simp_rw [Real.cos_sub, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hsum_c, hsum_s]
  unfold DVal CVal SVal
  field_simp
  ring

lemma sin_eq {n : ℕ} {A B : Finset ℤ} (hn : 1 ≤ n)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (_hcard : A.card = B.card) (ω : ℝ) :
    (1 / (n : ℝ)) * ∑ k ∈ KSet n, Real.sin (ω * ((k : ℝ) / (n : ℝ))) * mVal n A B k =
      DVal n ω * SVal n A ω := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hsum_c : ∑ b ∈ B, Real.cos (ω * uCoord n b) =
      (∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.cos (ω * uCoord n t)) -
        ∑ a ∈ A, Real.cos (ω * uCoord n a) := by
    have h1 := Finset.sum_union hdisj (f := fun t => Real.cos (ω * uCoord n t))
    rw [hunion] at h1; linarith
  have hsum_s : ∑ b ∈ B, Real.sin (ω * uCoord n b) = -(∑ a ∈ A, Real.sin (ω * uCoord n a)) := by
    have h1 := Finset.sum_union hdisj (f := fun t => Real.sin (ω * uCoord n t))
    rw [hunion, sum_sin_uCoord_Icc] at h1; linarith
  have h := sum_overlap_mul hunion (fun k : ℤ => Real.sin (ω * ((k : ℝ) / (n : ℝ))))
  have h1 : ∑ k ∈ KSet n, Real.sin (ω * ((k : ℝ) / (n : ℝ))) * mVal n A B k =
      (∑ a ∈ A, ∑ b ∈ B, Real.sin (ω * uCoord n a - ω * uCoord n b)) / (n : ℝ) := by
    have hdiv : ∑ k ∈ KSet n, Real.sin (ω * ((k : ℝ) / (n : ℝ))) * mVal n A B k =
        (∑ k ∈ KSet n, Real.sin (ω * ((k : ℝ) / (n : ℝ))) * (Erdos36.Overlap A B k : ℝ)) / (n : ℝ) := by
      unfold mVal; rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [hdiv, h]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_sub, uCoord_sub hn a b]
  rw [h1]
  simp_rw [Real.sin_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hsum_c, hsum_s]
  unfold DVal SVal
  field_simp
  ring

lemma DVal_pi_eq_zero {n : ℕ} (hn : 1 ≤ n) : DVal n Real.pi = 0 := by
  unfold DVal
  have hsplit : Finset.Icc (1 : ℤ) (2 * (n : ℤ)) =
      Finset.Icc (1 : ℤ) (n : ℤ) ∪ Finset.Icc ((n : ℤ) + 1) (2 * (n : ℤ)) := by
    ext t; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc (1 : ℤ) (n : ℤ)) (Finset.Icc ((n : ℤ) + 1) (2 * (n : ℤ))) := by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hshift : ∑ t ∈ Finset.Icc ((n : ℤ) + 1) (2 * (n : ℤ)), Real.cos (Real.pi * uCoord n t) =
      -(∑ t ∈ Finset.Icc (1 : ℤ) (n : ℤ), Real.cos (Real.pi * uCoord n t)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun t _ => t - (n : ℤ)) ?_ ?_ ?_ ?_
    · intro t ht; rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro b hb; rcases Finset.mem_Icc.mp hb with ⟨h1, h2⟩
      exact ⟨b + (n : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro t _
      have hu : uCoord n t = uCoord n (t - (n : ℤ)) + 1 := by
        simpa [sub_add_cancel] using uCoord_shift_n hn (t - (n : ℤ))
      rw [hu, mul_add, mul_one, Real.cos_add_pi]
  rw [hshift, add_neg_cancel, mul_zero]

/- ## Section 2: Alternating-Derivative Taylor Bounds for Cos and Sin -/

lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ}
    (hf : ∀ x ≥ 0, HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0)
    (hder : ∀ x ≥ 0, 0 ≤ f' x) :
    ∀ x ≥ 0, 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y hy => (hf y hy).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ici] at hy
      exact (hf y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · intro y hy; rw [interior_Ici] at hy
      rw [(hf y (le_of_lt hy)).deriv]
      exact hder y (le_of_lt hy)
  exact h0.trans (hmono (Set.mem_Ici.mpr le_rfl) hx hx)

lemma sin_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x := by
  have := nonneg_of_deriv_nonneg (f := fun t => t - Real.sin t) (f' := fun t => 1 - Real.cos t)
    (fun t _ => (hasDerivAt_id t).sub (Real.hasDerivAt_sin t))
    (by simp) (fun t _ => sub_nonneg.mpr (Real.cos_le_one t)) x hx
  linarith

lemma cos_ge_t2 {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 ≤ Real.cos x := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2))
    (f' := fun t => t - Real.sin t)
    (fun t _ => by
      have h1 := (Real.hasDerivAt_cos t).sub ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2))
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (sin_le_self_of_nonneg ht)) x hx
  linarith

lemma sin_ge_t3 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2))
    (fun t _ => by
      have h1 := (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6))
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (cos_ge_t2 ht)) x hx
  linarith

lemma cos_le_t4 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
    (f' := fun t => Real.sin t - (t - t ^ 3 / 6))
    (fun t _ => by
      have h1 := (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (sin_ge_t3 ht)) x hx
  linarith

lemma sin_le_t5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
    (f' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
    (fun t _ => by
      have h1 := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (cos_le_t4 ht)) x hx
  linarith

lemma cos_ge_t6 {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (f' := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
    (fun t _ => by
      have h1 := (Real.hasDerivAt_cos t).sub
        ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720))
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (sin_le_t5 ht)) x hx
  linarith

lemma sin_ge_t7 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (fun t _ => by
      have h1 := (Real.hasDerivAt_sin t).sub
        ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040))
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (cos_ge_t6 ht)) x hx
  linarith

lemma cos_le_t8 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - Real.cos t)
    (f' := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
    (fun t _ => by
      have h1 := (((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
          ((hasDerivAt_pow 8 t).div_const 40320)).sub (Real.hasDerivAt_cos t)
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (sin_ge_t7 ht)) x hx
  linarith

lemma sin_le_t9 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - Real.sin t)
    (f' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - Real.cos t)
    (fun t _ => by
      have h1 := (((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
          ((hasDerivAt_pow 9 t).div_const 362880)).sub (Real.hasDerivAt_sin t)
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (cos_le_t8 ht)) x hx
  linarith

lemma cos_ge_t10 {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 ≤ Real.cos x := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800))
    (f' := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - Real.sin t)
    (fun t _ => by
      have h1 := (Real.hasDerivAt_cos t).sub
        ((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
          ((hasDerivAt_pow 8 t).div_const 40320)).sub ((hasDerivAt_pow 10 t).div_const 3628800))
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (sin_le_t9 ht)) x hx
  linarith

lemma sin_ge_t11 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 ≤ Real.sin x := by
  have := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800))
    (fun t _ => by
      have h1 := (Real.hasDerivAt_sin t).sub
        ((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
          ((hasDerivAt_pow 9 t).div_const 362880)).sub ((hasDerivAt_pow 11 t).div_const 39916800))
      exact h1.congr_deriv (by norm_num; ring))
    (by simp) (fun t ht => sub_nonneg.mpr (cos_ge_t10 ht)) x hx
  linarith

lemma DVal_approx {n : ℕ} {ω : ℝ} (hn : 1 ≤ n) (hω : 0 < ω) (hωn : ω ≤ (n : ℝ)) :
    |DVal n ω - 2 * Real.sin ω / ω| ≤ ω / (10 * (n : ℝ) ^ 2) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hstep : 0 < ω / (2 * (n : ℝ)) := by positivity
  have hstep_le : ω / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hsin_lo : (5 / 6 : ℝ) * (ω / (2 * (n : ℝ))) ≤ Real.sin (ω / (2 * (n : ℝ))) := by
    have h3 := sin_ge_t3 hstep.le
    nlinarith [sq_nonneg (ω / (2 * (n : ℝ)))]
  have hsin_pos : 0 < Real.sin (ω / (2 * (n : ℝ))) := by linarith
  have hsin_hi : Real.sin (ω / (2 * (n : ℝ))) ≤ ω / (2 * (n : ℝ)) :=
    sin_le_self_of_nonneg hstep.le
  -- Exact telescoping sum: 2 sin(ω/(2n)) * ∑_{t=1}^{2n} cos(ω u_t) = 2 sin(ω)
  have hteles : 2 * Real.sin (ω / (2 * (n : ℝ))) *
      (∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.cos (ω * uCoord n t)) = 2 * Real.sin ω := by
    rw [Finset.mul_sum]
    have hterm : ∀ t : ℤ, 2 * Real.sin (ω / (2 * (n : ℝ))) * Real.cos (ω * uCoord n t) =
        Real.sin (ω * (((t : ℝ) - (n : ℝ)) / (n : ℝ))) -
          Real.sin (ω * ((((t - 1 : ℤ) : ℝ) - (n : ℝ)) / (n : ℝ))) := by
      intro t
      have ha : ω * (((t : ℝ) - (n : ℝ)) / (n : ℝ)) = ω * uCoord n t + ω / (2 * (n : ℝ)) := by
        unfold uCoord; field_simp; ring
      have hb : ω * ((((t - 1 : ℤ) : ℝ) - (n : ℝ)) / (n : ℝ)) = ω * uCoord n t - ω / (2 * (n : ℝ)) := by
        unfold uCoord; push_cast; field_simp; ring
      rw [ha, hb, Real.sin_add, Real.sin_sub]; ring
    simp_rw [hterm]
    have hbij : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
          (Real.sin (ω * (((t : ℝ) - (n : ℝ)) / (n : ℝ))) -
            Real.sin (ω * ((((t - 1 : ℤ) : ℝ) - (n : ℝ)) / (n : ℝ)))) =
        ∑ k ∈ Finset.range (2 * n),
          (Real.sin (ω * ((((k + 1 : ℕ) : ℝ) - (n : ℝ)) / (n : ℝ))) -
            Real.sin (ω * (((k : ℝ) - (n : ℝ)) / (n : ℝ)))) := by
      refine Finset.sum_bij (fun t _ => (t - 1).toNat) ?_ ?_ ?_ ?_
      · intro t ht; rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩; exact Finset.mem_range.mpr (by omega)
      · intro a ha b hb h; rcases Finset.mem_Icc.mp ha with ⟨_, _⟩; rcases Finset.mem_Icc.mp hb with ⟨_, _⟩; omega
      · intro k hk; have hk' := Finset.mem_range.mp hk
        exact ⟨(k : ℤ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro t ht
        have ht' := Finset.mem_Icc.mp ht
        have hcast : (((t - 1).toNat : ℕ) : ℝ) = (t : ℝ) - 1 := by
          have h1 : ((t - 1).toNat : ℤ) = t - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast h1
        push_cast [hcast]; ring_nf
    rw [hbij, Finset.sum_range_sub (fun k : ℕ => Real.sin (ω * (((k : ℝ) - (n : ℝ)) / (n : ℝ)))) (2 * n)]
    have htop : ω * ((((2 * n : ℕ) : ℝ) - (n : ℝ)) / (n : ℝ)) = ω := by
      push_cast; field_simp; ring
    have hbot : ω * ((((0 : ℕ) : ℝ) - (n : ℝ)) / (n : ℝ)) = -ω := by
      push_cast; field_simp; ring
    rw [htop, hbot, Real.sin_neg]; ring
  have hD_eq : DVal n ω = Real.sin ω / ((n : ℝ) * Real.sin (ω / (2 * (n : ℝ)))) := by
    unfold DVal
    have : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.cos (ω * uCoord n t) =
        Real.sin ω / Real.sin (ω / (2 * (n : ℝ))) := by
      rw [eq_div_iff hsin_pos.ne']; linarith
    rw [this]; field_simp
  rw [hD_eq]
  have hdiff : Real.sin ω / ((n : ℝ) * Real.sin (ω / (2 * (n : ℝ)))) - 2 * Real.sin ω / ω =
      Real.sin ω * ((ω / (2 * (n : ℝ)) - Real.sin (ω / (2 * (n : ℝ)))) /
        ((n : ℝ) * (ω / (2 * (n : ℝ))) * Real.sin (ω / (2 * (n : ℝ))))) := by
    set sv := Real.sin (ω / (2 * (n : ℝ)))
    have hsv : sv ≠ 0 := hsin_pos.ne'
    field_simp [hsv, hω.ne', hn_pos.ne']
  rw [hdiff, abs_mul]
  have hnum : ω / (2 * (n : ℝ)) - Real.sin (ω / (2 * (n : ℝ))) ≤ (ω / (2 * (n : ℝ))) ^ 3 / 6 := by
    linarith [sin_ge_t3 hstep.le]
  have hnum_nn : 0 ≤ ω / (2 * (n : ℝ)) - Real.sin (ω / (2 * (n : ℝ))) := sub_nonneg.mpr hsin_hi
  have hden_pos : 0 < (n : ℝ) * (ω / (2 * (n : ℝ))) * Real.sin (ω / (2 * (n : ℝ))) := by positivity
  rw [abs_of_nonneg (div_nonneg hnum_nn hden_pos.le)]
  calc |Real.sin ω| * ((ω / (2 * (n : ℝ)) - Real.sin (ω / (2 * (n : ℝ)))) /
        ((n : ℝ) * (ω / (2 * (n : ℝ))) * Real.sin (ω / (2 * (n : ℝ)))))
      ≤ 1 * ((ω / (2 * (n : ℝ))) ^ 3 / 6 /
        ((n : ℝ) * (ω / (2 * (n : ℝ))) * ((5 / 6 : ℝ) * (ω / (2 * (n : ℝ)))))) := by
        apply mul_le_mul (Real.abs_sin_le_one ω)
        · apply div_le_div₀ (by positivity) hnum (by positivity)
          exact mul_le_mul_of_nonneg_left hsin_lo (by positivity)
        · exact div_nonneg hnum_nn hden_pos.le
        · norm_num
    _ = ω / (10 * (n : ℝ) ^ 2) := by field_simp; ring

/- ## Section 3: Klein-4 Symmetries -/

lemma overlap_reflect {n : ℕ} (A B : Finset ℤ) (k : ℤ) :
    Erdos36.Overlap (A.image (fun t => 2 * (n : ℤ) + 1 - t))
      (B.image (fun t => 2 * (n : ℤ) + 1 - t)) (-k) = Erdos36.Overlap A B k := by
  unfold Erdos36.Overlap
  refine Finset.card_bij (fun p _ => (2 * (n : ℤ) + 1 - p.1, 2 * (n : ℤ) + 1 - p.2)) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp1, hpk⟩
    rcases Finset.mem_product.mp hp1 with ⟨ha, hb⟩
    rcases Finset.mem_image.mp ha with ⟨a, haA, haeq⟩
    rcases Finset.mem_image.mp hb with ⟨b, hbB, hbeq⟩
    have ha' : 2 * (n : ℤ) + 1 - p.1 = a := by omega
    have hb' : 2 * (n : ℤ) + 1 - p.2 = b := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by dsimp at hpk ⊢; omega⟩
    · rwa [ha']
    · rwa [hb']
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hq1, hqk⟩
    rcases Finset.mem_product.mp hq1 with ⟨ha, hb⟩
    refine ⟨(2 * (n : ℤ) + 1 - q.1, 2 * (n : ℤ) + 1 - q.2), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨q.1, ha, rfl⟩, Finset.mem_image.mpr ⟨q.2, hb, rfl⟩⟩, by omega⟩
    · exact Prod.ext (by omega) (by omega)

lemma overlap_comp_reflect {n : ℕ} (A B : Finset ℤ) (k : ℤ) :
    Erdos36.Overlap (B.image (fun t => 2 * (n : ℤ) + 1 - t))
      (A.image (fun t => 2 * (n : ℤ) + 1 - t)) k = Erdos36.Overlap A B k := by
  unfold Erdos36.Overlap
  refine Finset.card_bij (fun p _ => (2 * (n : ℤ) + 1 - p.2, 2 * (n : ℤ) + 1 - p.1)) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp1, hpk⟩
    rcases Finset.mem_product.mp hp1 with ⟨hb, ha⟩
    rcases Finset.mem_image.mp hb with ⟨b, hbB, hbeq⟩
    rcases Finset.mem_image.mp ha with ⟨a, haA, haeq⟩
    have ha' : 2 * (n : ℤ) + 1 - p.2 = a := by omega
    have hb' : 2 * (n : ℤ) + 1 - p.1 = b := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by dsimp at hpk ⊢; omega⟩
    · rwa [ha']
    · rwa [hb']
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hq1, hqk⟩
    rcases Finset.mem_product.mp hq1 with ⟨ha, hb⟩
    refine ⟨(2 * (n : ℤ) + 1 - q.2, 2 * (n : ℤ) + 1 - q.1), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨q.2, hb, rfl⟩, Finset.mem_image.mpr ⟨q.1, ha, rfl⟩⟩, by omega⟩
    · exact Prod.ext (by omega) (by omega)

private lemma bddAbove_overlap (A B : Finset ℤ) : BddAbove (Set.range (Erdos36.Overlap A B)) := by
  refine ⟨A.card * B.card, ?_⟩
  rintro x ⟨k, rfl⟩
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.product_eq_sprod, Finset.card_product])

lemma maxOverlap_reflect {n : ℕ} (A B : Finset ℤ) :
    Erdos36.MaxOverlap (A.image (fun t => 2 * (n : ℤ) + 1 - t))
      (B.image (fun t => 2 * (n : ℤ) + 1 - t)) = Erdos36.MaxOverlap A B := by
  unfold Erdos36.MaxOverlap
  apply le_antisymm
  · refine ciSup_le fun k => ?_
    have h := overlap_reflect (n := n) A B (-k)
    rw [neg_neg] at h
    rw [h]
    exact le_ciSup (bddAbove_overlap A B) (-k)
  · refine ciSup_le fun k => ?_
    rw [← overlap_reflect (n := n) A B k]
    exact le_ciSup (bddAbove_overlap _ _) (-k)

lemma maxOverlap_comp_reflect {n : ℕ} (A B : Finset ℤ) :
    Erdos36.MaxOverlap (B.image (fun t => 2 * (n : ℤ) + 1 - t))
      (A.image (fun t => 2 * (n : ℤ) + 1 - t)) = Erdos36.MaxOverlap A B := by
  unfold Erdos36.MaxOverlap
  congr 1; funext k; exact overlap_comp_reflect A B k

private lemma reflect_inj (n : ℕ) : Function.Injective (fun t : ℤ => 2 * (n : ℤ) + 1 - t) := by
  intro a b h; dsimp at h; omega

private lemma disjoint_reflect {n : ℕ} {A B : Finset ℤ} (h : Disjoint A B) :
    Disjoint (A.image (fun t => 2 * (n : ℤ) + 1 - t)) (B.image (fun t => 2 * (n : ℤ) + 1 - t)) := by
  rw [Finset.disjoint_left]; intro x h1 h2
  rcases Finset.mem_image.mp h1 with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨b, hb, hab⟩
  have : b = a := reflect_inj n hab; subst this
  exact Finset.disjoint_left.mp h ha hb

private lemma reflect_Icc (n : ℕ) :
    (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).image (fun t => 2 * (n : ℤ) + 1 - t) =
      Finset.Icc (1 : ℤ) (2 * (n : ℤ)) := by
  ext t; simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨2 * (n : ℤ) + 1 - t, ⟨by omega, by omega⟩, by omega⟩

lemma exists_normalized_partition {n : ℕ} (hn : 1 ≤ n) {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (hcard : A.card = B.card) :
    ∃ A' B' : Finset ℤ,
      Disjoint A' B' ∧
      A' ∪ B' = Finset.Icc (1 : ℤ) (2 * (n : ℤ)) ∧
      A'.card = B'.card ∧
      Erdos36.MaxOverlap A' B' = Erdos36.MaxOverlap A B ∧
      0 ≤ EVal n A' ∧
      0 ≤ CVal n A' Real.pi ∧ CVal n A' Real.pi ≤ 1 ∧
      -1 ≤ SVal n A' Real.pi ∧ SVal n A' Real.pi ≤ 1 := by
  -- Step 1: Make EVal >= 0 via reflection if needed
  have hstep1 : ∃ A1 B1 : Finset ℤ,
      Disjoint A1 B1 ∧ A1 ∪ B1 = Finset.Icc (1 : ℤ) (2 * (n : ℤ)) ∧ A1.card = B1.card ∧
      Erdos36.MaxOverlap A1 B1 = Erdos36.MaxOverlap A B ∧ 0 ≤ EVal n A1 := by
    by_cases hE : 0 ≤ EVal n A
    · exact ⟨A, B, hdisj, hunion, hcard, rfl, hE⟩
    · refine ⟨A.image (fun t => 2 * (n : ℤ) + 1 - t), B.image (fun t => 2 * (n : ℤ) + 1 - t),
        disjoint_reflect hdisj, ?_, ?_, maxOverlap_reflect A B, ?_⟩
      · rw [← Finset.image_union, hunion, reflect_Icc]
      · rw [Finset.card_image_of_injective _ (reflect_inj n),
            Finset.card_image_of_injective _ (reflect_inj n), hcard]
      · unfold EVal
        rw [Finset.sum_image (fun a _ b _ h => reflect_inj n h)]
        simp_rw [uCoord_reflect, Finset.sum_neg_distrib, mul_neg]
        unfold EVal at hE; linarith
  rcases hstep1 with ⟨A1, B1, hd1, hu1, hc1, hm1, hE1⟩
  -- Step 2: Make CVal n · pi >= 0 via complement+reflection (preserving EVal!)
  have hstep2 : ∃ A2 B2 : Finset ℤ,
      Disjoint A2 B2 ∧ A2 ∪ B2 = Finset.Icc (1 : ℤ) (2 * (n : ℤ)) ∧ A2.card = B2.card ∧
      Erdos36.MaxOverlap A2 B2 = Erdos36.MaxOverlap A B ∧ 0 ≤ EVal n A2 ∧ 0 ≤ CVal n A2 Real.pi := by
    by_cases hC : 0 ≤ CVal n A1 Real.pi
    · exact ⟨A1, B1, hd1, hu1, hc1, hm1, hE1, hC⟩
    · refine ⟨B1.image (fun t => 2 * (n : ℤ) + 1 - t), A1.image (fun t => 2 * (n : ℤ) + 1 - t),
        disjoint_reflect hd1.symm, ?_, ?_,
        (maxOverlap_comp_reflect A1 B1).trans hm1, ?_, ?_⟩
      · rw [← Finset.image_union, Finset.union_comm, hu1, reflect_Icc]
      · rw [Finset.card_image_of_injective _ (reflect_inj n),
            Finset.card_image_of_injective _ (reflect_inj n), hc1]
      · unfold EVal
        rw [Finset.sum_image (fun a _ b _ h => reflect_inj n h)]
        simp_rw [uCoord_reflect, Finset.sum_neg_distrib]
        have hsum_u : ∑ b ∈ B1, uCoord n b = -(∑ a ∈ A1, uCoord n a) := by
          have h1 := Finset.sum_union hd1 (f := uCoord n)
          rw [hu1, sum_uCoord_Icc] at h1; linarith
        rw [hsum_u, neg_neg]
        exact hE1
      · unfold CVal
        rw [Finset.sum_image (fun a _ b _ h => reflect_inj n h)]
        simp_rw [uCoord_reflect, mul_neg, Real.cos_neg]
        have hsum_c : ∑ b ∈ B1, Real.cos (Real.pi * uCoord n b) =
            -(∑ a ∈ A1, Real.cos (Real.pi * uCoord n a)) := by
          have h1 := Finset.sum_union hd1 (f := fun t => Real.cos (Real.pi * uCoord n t))
          have hD := DVal_pi_eq_zero hn
          unfold DVal at hD
          have hn' : (1 / (n : ℝ)) ≠ 0 := by positivity
          have h0 : ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), Real.cos (Real.pi * uCoord n t) = 0 :=
            (mul_eq_zero.mp hD).resolve_left hn'
          rw [hu1, h0] at h1; linarith
        rw [hsum_c, mul_neg]
        unfold CVal at hC; linarith
  rcases hstep2 with ⟨A2, B2, hd2, hu2, hc2, hm2, hE2, hC2⟩
  have ⟨hA2, _⟩ := card_eq_n hd2 hu2 hc2
  have hn_pos : (0 : ℝ) < n := by positivity
  refine ⟨A2, B2, hd2, hu2, hc2, hm2, hE2, hC2, ?_, ?_, ?_⟩
  · unfold CVal
    calc (1 / (n : ℝ)) * ∑ a ∈ A2, Real.cos (Real.pi * uCoord n a)
        ≤ (1 / (n : ℝ)) * ∑ _a ∈ A2, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Real.cos_le_one _) (by positivity)
      _ = 1 := by simp [hA2]; field_simp
  · unfold SVal
    have hlo : (1 / (n : ℝ)) * ∑ _a ∈ A2, (-1 : ℝ) ≤
        (1 / (n : ℝ)) * ∑ a ∈ A2, Real.sin (Real.pi * uCoord n a) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Real.neg_one_le_sin _) (by positivity)
    have hval : (1 / (n : ℝ)) * ∑ _a ∈ A2, (-1 : ℝ) = -1 := by simp [hA2]; field_simp
    linarith
  · unfold SVal
    calc (1 / (n : ℝ)) * ∑ a ∈ A2, Real.sin (Real.pi * uCoord n a)
        ≤ (1 / (n : ℝ)) * ∑ _a ∈ A2, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Real.sin_le_one _) (by positivity)
      _ = 1 := by simp [hA2]; field_simp

/- ## Section 4: Second-Derivative Envelope & Telescoping Discrete Sum Bound -/

lemma taylor_order2_le {f f' f'' : ℝ → ℝ} {B : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hB : ∀ x, f'' x ≤ B) (m x : ℝ) :
    f x ≤ f m + f' m * (x - m) + (B / 2) * (x - m) ^ 2 := by
  let g : ℝ → ℝ := fun t => f m + f' m * (t - m) + (B / 2) * (t - m) ^ 2 - f t
  let g' : ℝ → ℝ := fun t => f' m + B * (t - m) - f' t
  let g'' : ℝ → ℝ := fun t => B - f'' t
  have hg : ∀ t, HasDerivAt g (g' t) t := fun t => by
    have h1 : HasDerivAt (fun s => f m + f' m * (s - m)) (f' m) t := by
      simpa using (((hasDerivAt_id t).sub_const m).const_mul (f' m))
    have h2 : HasDerivAt (fun s => (B / 2) * (s - m) ^ 2) (B * (t - m)) t := by
      have := (((hasDerivAt_id t).sub_const m).pow 2).const_mul (B / 2)
      exact this.congr_deriv (by norm_num; ring)
    exact (h1.add h2).sub (hf t)
  have hg' : ∀ t, HasDerivAt g' (g'' t) t := fun t => by
    have h1 : HasDerivAt (fun s => f' m + B * (s - m)) B t := by
      simpa using (((hasDerivAt_id t).sub_const m).const_mul B)
    exact h1.sub (hf' t)
  have hg'mono : Monotone g' := by
    apply monotone_of_deriv_nonneg (fun t => (hg' t).differentiableAt)
    intro t; rw [(hg' t).deriv]; exact sub_nonneg.mpr (hB t)
  have hgm : g m = 0 := by simp [g]
  have hg'm : g' m = 0 := by simp [g']
  suffices h0 : 0 ≤ g x by simp only [g] at h0; linarith
  rcases le_total m x with hmx | hxm
  · have hmono : MonotoneOn g (Set.Ici m) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici m)
        (fun t _ => (hg t).continuousAt.continuousWithinAt)
        (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
      intro t ht; rw [interior_Ici] at ht; rw [(hg t).deriv, ← hg'm]; exact hg'mono (le_of_lt ht)
    rw [← hgm]; exact hmono (Set.mem_Ici.mpr le_rfl) hmx hmx
  · have hanti : AntitoneOn g (Set.Iic m) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic m)
        (fun t _ => (hg t).continuousAt.continuousWithinAt)
        (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
      intro t ht; rw [interior_Iic] at ht; rw [(hg t).deriv, ← hg'm]; exact hg'mono (le_of_lt ht)
    rw [← hgm]; exact hanti hxm (Set.mem_Iic.mpr le_rfl) hxm

/-- Exact integral of `max (α + β * s) 0` on `[-d/2, d/2]` for `β ≥ 0, d > 0`. -/
noncomputable def uArea (α β d : ℝ) : ℝ :=
  if α + β * (d / 2) ≤ 0 then 0
  else if 0 ≤ α - β * (d / 2) then α * d
  else (α + β * (d / 2)) ^ 2 / (2 * β)

lemma uArea_nonneg (α : ℝ) {β d : ℝ} (_hβ : 0 ≤ β) (hd : 0 < d) : 0 ≤ uArea α β d := by
  unfold uArea
  split_ifs with h1 h2
  · exact le_rfl
  · have : 0 ≤ α := by nlinarith
    exact mul_nonneg this hd.le
  · push Not at h1 h2
    have hβpos : 0 < β := by nlinarith
    positivity

lemma uArea_mono {α₁ α₂ β₁ β₂ d : ℝ} (hα : α₁ ≤ α₂) (hβ1 : 0 ≤ β₁) (hβ : β₁ ≤ β₂) (hd : 0 < d) :
    uArea α₁ β₁ d ≤ uArea α₂ β₂ d := by
  have hmono_a : ∀ α a' β, α ≤ a' → 0 ≤ β → uArea α β d ≤ uArea a' β d := by
    intro α a' β haa hb
    unfold uArea
    by_cases h1 : α + β * (d / 2) ≤ 0
    · rw [if_pos h1]
      exact uArea_nonneg a' hb hd
    · rw [if_neg h1]
      have h1' : ¬ (a' + β * (d / 2) ≤ 0) := by linarith
      rw [if_neg h1']
      by_cases h2 : 0 ≤ α - β * (d / 2)
      · rw [if_pos h2, if_pos (by linarith)]
        exact mul_le_mul_of_nonneg_right haa hd.le
      · rw [if_neg h2]
        push Not at h1 h2
        have hbpos : 0 < β := by nlinarith
        by_cases h2' : 0 ≤ a' - β * (d / 2)
        · rw [if_pos h2', div_le_iff₀ (by positivity)]
          have hgap : 0 ≤ β * (d / 2) - α := by linarith
          have hle : β * (d / 2) - α ≤ a' - α := by linarith
          have hle2 : β * (d / 2) - α ≤ β * d := by linarith
          have hid : (α + β * (d / 2)) ^ 2 - 2 * β * (a' * d) =
              (α - β * (d / 2)) ^ 2 - 2 * β * d * (a' - α) := by ring
          nlinarith
        · rw [if_neg h2']
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
  have hmono_b : ∀ α β b', 0 ≤ β → β ≤ b' → uArea α β d ≤ uArea α b' d := by
    intro α β b' hb hbb
    have hb' : 0 ≤ b' := hb.trans hbb
    unfold uArea
    by_cases h1 : α + β * (d / 2) ≤ 0
    · rw [if_pos h1]
      exact uArea_nonneg α hb' hd
    · rw [if_neg h1]
      have h1' : ¬ (α + b' * (d / 2) ≤ 0) := by nlinarith
      rw [if_neg h1']
      by_cases h2 : 0 ≤ α - β * (d / 2)
      · rw [if_pos h2]
        by_cases h2' : 0 ≤ α - b' * (d / 2)
        · rw [if_pos h2']
        · rw [if_neg h2']
          push Not at h1' h2'
          have hb'pos : 0 < b' := by nlinarith
          rw [le_div_iff₀ (by positivity)]
          have hid : (α + b' * (d / 2)) ^ 2 - α * d * (2 * b') = (α - b' * (d / 2)) ^ 2 := by ring
          nlinarith [sq_nonneg (α - b' * (d / 2))]
      · rw [if_neg h2]
        push Not at h1 h2
        have h2' : ¬ (0 ≤ α - b' * (d / 2)) := by nlinarith
        rw [if_neg h2']
        have hbpos : 0 < β := by nlinarith
        have hb'pos : 0 < b' := hbpos.trans_le hbb
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hfac : (α + b' * (d / 2)) ^ 2 * (2 * β) - (α + β * (d / 2)) ^ 2 * (2 * b') =
            2 * (b' - β) * (β * b' * (d / 2) ^ 2 - α ^ 2) := by ring
        have hsq : α ^ 2 ≤ (β * (d / 2)) ^ 2 := by nlinarith
        have hpos : α ^ 2 ≤ β * b' * (d / 2) ^ 2 := by nlinarith
        nlinarith
  exact (hmono_a α₁ α₂ β₁ hα hβ1).trans (hmono_b α₂ β₁ β₂ hβ1 hβ)

/-- Elementary telescoping lemma for monotone-increasing linear sums on a lattice `x0 + k / n`. -/
private lemma discrete_linear_pos_sum_le_nonneg {n : ℕ} (hn : 1 ≤ n)
    (x0 a b α β : ℝ) (hab : a < b) (hβ : 0 ≤ β)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, a ≤ x0 + (k : ℝ) / (n : ℝ) ∧ x0 + (k : ℝ) / (n : ℝ) < b) :
    (1 / (n : ℝ)) * ∑ k ∈ S, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 ≤
      uArea α β (b - a) + max (α + β * ((b - a) / 2)) 0 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  set d := b - a
  set m := (a + b) / 2
  have hd : 0 < d := sub_pos.mpr hab
  have hm_lo : a - m = -(d / 2) := by simp only [d, m]; ring
  have hm_hi : b - m = d / 2 := by simp only [d, m]; ring
  -- Case 1: α + β * (d / 2) ≤ 0 -> every term is 0!
  by_cases h1 : α + β * (d / 2) ≤ 0
  · have hzero : ∀ k ∈ S, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) 0 = 0 := by
      intro k hk
      rw [max_eq_right_iff]
      have hb' := (hS k hk).2
      nlinarith
    rw [Finset.sum_eq_zero hzero, mul_zero]
    have hu := uArea_nonneg α hβ hd
    have hm : 0 ≤ max (α + β * (d / 2)) 0 / (n : ℝ) := by positivity
    linarith
  push Not at h1
  -- Filter S to positive terms (or keep all terms if α - β*(d/2) ≥ 0)
  let s0 : ℝ := if 0 ≤ α - β * (d / 2) then a else m - α / β
  have hs0_ge_a : a ≤ s0 := by
    dsimp only [s0]; split_ifs with h2
    · exact le_rfl
    · push Not at h2
      have hβpos : 0 < β := by nlinarith
      have hdiv : α / β ≤ m - a := by rw [div_le_iff₀ hβpos]; nlinarith
      linarith
  have hs0_le_b : s0 ≤ b := by
    dsimp only [s0]; split_ifs with h2
    · exact hab.le
    · push Not at h2
      have hβpos : 0 < β := by nlinarith
      have hdiv : m - b ≤ α / β := by rw [le_div_iff₀ hβpos]; nlinarith
      linarith
  let T : Finset ℤ := S.filter (fun k : ℤ => s0 ≤ x0 + (k : ℝ) / (n : ℝ))
  have hST : ∑ k ∈ S, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) 0 =
      ∑ k ∈ T, (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun k : ℤ => s0 ≤ x0 + (k : ℝ) / (n : ℝ))]
    have hrest : ∑ k ∈ S.filter (fun k : ℤ => ¬ s0 ≤ x0 + (k : ℝ) / (n : ℝ)),
        max (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) 0 = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rcases Finset.mem_filter.mp hk with ⟨hkS, hlt⟩
      push Not at hlt
      rw [max_eq_right_iff]
      dsimp only [s0] at hlt
      split_ifs at hlt with h2
      · exfalso; linarith [(hS k hkS).1]
      · push Not at h2
        have hβpos : 0 < β := by nlinarith
        have : (x0 + (k : ℝ) / (n : ℝ) - m) < -(α / β) := by linarith
        have := mul_lt_mul_of_pos_left this hβpos
        rw [mul_neg, mul_div_cancel₀ _ hβpos.ne'] at this
        linarith
    rw [hrest, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_filter.mp hk with ⟨hkS, hge⟩
    rw [max_eq_left_iff]
    dsimp only [s0] at hge
    split_ifs at hge with h2
    · nlinarith [(hS k hkS).1]
    · push Not at h2
      have hβpos : 0 < β := by nlinarith
      have : -(α / β) ≤ x0 + (k : ℝ) / (n : ℝ) - m := by linarith
      have := mul_le_mul_of_nonneg_left this hβpos.le
      rw [mul_neg, mul_div_cancel₀ _ hβpos.ne'] at this
      linarith
  rw [hST]
  by_cases hT : T.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty, mul_zero]
    have hu := uArea_nonneg α hβ hd
    have hm : 0 ≤ max (α + β * (d / 2)) 0 / (n : ℝ) := by positivity
    linarith
  -- Let kmin = T.min' hT, kmax = T.max' hT; then T ⊆ Icc kmin kmax
  -- And every k ∈ Icc kmin (kmax - 1) telescopes via antiderivative H(s) = α*s + (β/2)*(s - m)^2!
  let kmin := T.min' hT
  let kmax := T.max' hT
  have hkmin_mem : kmin ∈ T := Finset.min'_mem T hT
  have hkmax_mem : kmax ∈ T := Finset.max'_mem T hT
  have hT_nonneg : ∀ k ∈ Finset.Icc kmin kmax, 0 ≤ α + β * (x0 + (k : ℝ) / (n : ℝ) - m) := by
    intro k hk
    have hklo : kmin ≤ k := (Finset.mem_Icc.mp hk).1
    have hge : s0 ≤ x0 + (kmin : ℝ) / (n : ℝ) := (Finset.mem_filter.mp hkmin_mem).2
    have hge' : s0 ≤ x0 + (k : ℝ) / (n : ℝ) := by
      have : (kmin : ℝ) ≤ (k : ℝ) := by exact_mod_cast hklo
      have : (kmin : ℝ) / (n : ℝ) ≤ (k : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right this hn_pos.le
      linarith
    dsimp only [s0] at hge'
    split_ifs at hge' with h2
    · nlinarith
    · push Not at h2
      have hβpos : 0 < β := by nlinarith
      have : -(α / β) ≤ x0 + (k : ℝ) / (n : ℝ) - m := by linarith
      have := mul_le_mul_of_nonneg_left this hβpos.le
      rw [mul_neg, mul_div_cancel₀ _ hβpos.ne'] at this
      linarith
  have hsub : T ⊆ Finset.Icc kmin kmax := fun k hk =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le T k hk, Finset.le_max' T k hk⟩
  have hsum_le : ∑ k ∈ T, (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) ≤
      ∑ k ∈ Finset.Icc kmin kmax, (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hT_nonneg k hk)
  -- Split off kmax from Icc kmin kmax:
  have hIcc_split : Finset.Icc kmin kmax = insert kmax (Finset.Ico kmin kmax) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    have hle : kmin ≤ kmax := Finset.min'_le T kmax hkmax_mem
    omega
  rw [hIcc_split, Finset.sum_insert (by simp)] at hsum_le
  -- Bound the single kmax term by max(α + β*(d/2), 0):
  have hlast : α + β * (x0 + (kmax : ℝ) / (n : ℝ) - m) ≤ max (α + β * (d / 2)) 0 := by
    have hb' := (hS kmax (Finset.mem_filter.mp hkmax_mem).1).2
    exact le_trans (by nlinarith) (le_max_left _ _)
  -- Bound the Ico kmin kmax sum by H(x0 + kmax/n) - H(x0 + kmin/n) <= H(b) - H(s0) = uArea α β d!
  let H : ℝ → ℝ := fun s => α * s + (β / 2) * (s - m) ^ 2
  have hstep : ∀ k ∈ Finset.Ico kmin kmax,
      (1 / (n : ℝ)) * (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) ≤
        H (x0 + ((k + 1 : ℤ) : ℝ) / (n : ℝ)) - H (x0 + (k : ℝ) / (n : ℝ)) := by
    intro k _
    have hdiff : H (x0 + ((k + 1 : ℤ) : ℝ) / (n : ℝ)) - H (x0 + (k : ℝ) / (n : ℝ)) =
        (1 / (n : ℝ)) * (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) + β / (2 * (n : ℝ) ^ 2) := by
      simp only [H]; push_cast; field_simp; ring
    rw [hdiff]
    have : 0 ≤ β / (2 * (n : ℝ) ^ 2) := by positivity
    linarith
  have hteles : (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico kmin kmax, (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) ≤
      H (x0 + (kmax : ℝ) / (n : ℝ)) - H (x0 + (kmin : ℝ) / (n : ℝ)) := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ Finset.Ico kmin kmax, (1 / (n : ℝ)) * (α + β * (x0 + (k : ℝ) / (n : ℝ) - m))
        ≤ ∑ k ∈ Finset.Ico kmin kmax,
            (H (x0 + ((k + 1 : ℤ) : ℝ) / (n : ℝ)) - H (x0 + (k : ℝ) / (n : ℝ))) :=
          Finset.sum_le_sum hstep
      _ = H (x0 + (kmax : ℝ) / (n : ℝ)) - H (x0 + (kmin : ℝ) / (n : ℝ)) := by
          have hle : kmin ≤ kmax := Finset.min'_le T kmax hkmax_mem
          let N : ℕ := (kmax - kmin).toNat
          have hbij : ∑ k ∈ Finset.Ico kmin kmax,
                (H (x0 + ((k + 1 : ℤ) : ℝ) / (n : ℝ)) - H (x0 + (k : ℝ) / (n : ℝ))) =
              ∑ i ∈ Finset.range N,
                (H (x0 + (((kmin + (i + 1 : ℕ) : ℤ) : ℝ) / (n : ℝ))) -
                  H (x0 + (((kmin + (i : ℕ) : ℤ) : ℝ) / (n : ℝ)))) := by
            refine Finset.sum_bij (fun k _ => (k - kmin).toNat) ?_ ?_ ?_ ?_
            · intro k hk; rcases Finset.mem_Ico.mp hk with ⟨h1, h2⟩
              exact Finset.mem_range.mpr (by dsimp [N]; omega)
            · intro a ha b hb h; rcases Finset.mem_Ico.mp ha with ⟨_, _⟩; rcases Finset.mem_Ico.mp hb with ⟨_, _⟩; omega
            · intro i hi; have hi' := Finset.mem_range.mp hi
              exact ⟨kmin + i, Finset.mem_Ico.mpr ⟨by omega, by dsimp [N] at hi'; omega⟩, by omega⟩
            · intro k hk
              have hk' := Finset.mem_Ico.mp hk
              have h1 : kmin + ((k - kmin).toNat : ℤ) = k := by omega
              have h2 : kmin + (((k - kmin).toNat + 1 : ℕ) : ℤ) = k + 1 := by omega
              rw [h1, h2]
          rw [hbij, Finset.sum_range_sub (fun i : ℕ => H (x0 + (((kmin + (i : ℕ) : ℤ) : ℝ) / (n : ℝ)))) N]
          have htop : (kmin : ℤ) + (N : ℤ) = kmax := by dsimp [N]; omega
          have htopR : ((kmin + (N : ℕ) : ℤ) : ℝ) = (kmax : ℝ) := by exact_mod_cast htop
          simp [htopR]
  -- H is monotone increasing on [s0, b] (since H'(s) = α + β*(s - m) ≥ 0 on [s0, b])!
  have hH_mono : ∀ u v, s0 ≤ u → u ≤ v → H u ≤ H v := by
    intro u v hu huv
    have hdiff : H v - H u = (v - u) * (α + β * ((u + v) / 2 - m)) := by simp only [H]; ring
    have hge : s0 ≤ (u + v) / 2 := by linarith
    have hpos : 0 ≤ α + β * ((u + v) / 2 - m) := by
      dsimp only [s0] at hge
      split_ifs at hge with h2
      · nlinarith
      · push Not at h2
        have hβpos : 0 < β := by nlinarith
        have : -(α / β) ≤ (u + v) / 2 - m := by linarith
        have := mul_le_mul_of_nonneg_left this hβpos.le
        rw [mul_neg, mul_div_cancel₀ _ hβpos.ne'] at this
        linarith
    linarith [mul_nonneg (sub_nonneg.mpr huv) hpos]
  have hHb : H (x0 + (kmax : ℝ) / (n : ℝ)) ≤ H b := by
    have hm1 : s0 ≤ x0 + (kmax : ℝ) / (n : ℝ) := (Finset.mem_filter.mp hkmax_mem).2
    have hm2 : x0 + (kmax : ℝ) / (n : ℝ) ≤ b := (hS kmax (Finset.mem_filter.mp hkmax_mem).1).2.le
    exact hH_mono _ _ hm1 hm2
  have hHs0 : H s0 ≤ H (x0 + (kmin : ℝ) / (n : ℝ)) :=
    hH_mono _ _ le_rfl (Finset.mem_filter.mp hkmin_mem).2
  have hH_eq : H b - H s0 = uArea α β d := by
    unfold uArea
    rw [if_neg (not_le.mpr h1)]
    dsimp only [H, s0]
    split_ifs with h2
    · simp only [d, m]; ring
    · push Not at h2
      have hβpos : 0 < β := by nlinarith
      simp only [d, m]; field_simp; ring
  have hmain : (1 / (n : ℝ)) * ∑ k ∈ T, (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) ≤
      (1 / (n : ℝ)) * (α + β * (x0 + (kmax : ℝ) / (n : ℝ) - m)) +
        (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico kmin kmax, (α + β * (x0 + (k : ℝ) / (n : ℝ) - m)) := by
    have := mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ 1 / (n : ℝ))
    linarith
  have hlast_div : (1 / (n : ℝ)) * (α + β * (x0 + (kmax : ℝ) / (n : ℝ) - m)) ≤
      max (α + β * (d / 2)) 0 / (n : ℝ) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hlast hn_pos.le
  linarith

lemma discrete_linear_pos_sum_le {n : ℕ} (hn : 1 ≤ n)
    (x0 a b α β : ℝ) (hab : a < b)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, a ≤ x0 + (k : ℝ) / (n : ℝ) ∧ x0 + (k : ℝ) / (n : ℝ) < b) :
    (1 / (n : ℝ)) * ∑ k ∈ S, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 ≤
      uArea α |β| (b - a) + 2 * max (α + |β| * ((b - a) / 2)) 0 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  by_cases hβ : 0 ≤ β
  · rw [abs_of_nonneg hβ]
    have h1 := discrete_linear_pos_sum_le_nonneg hn x0 a b α β hab hβ S hS
    have hnn : 0 ≤ max (α + β * ((b - a) / 2)) 0 / (n : ℝ) := by positivity
    have h2 : 2 * max (α + β * ((b - a) / 2)) 0 / (n : ℝ) =
        max (α + β * ((b - a) / 2)) 0 / (n : ℝ) + max (α + β * ((b - a) / 2)) 0 / (n : ℝ) := by ring
    linarith
  · push Not at hβ
    rw [abs_of_neg hβ]
    let S_eq : Finset ℤ := S.filter (fun k : ℤ => x0 + (k : ℝ) / (n : ℝ) = a)
    let S_gt : Finset ℤ := S.filter (fun k : ℤ => x0 + (k : ℝ) / (n : ℝ) ≠ a)
    have hsplit : ∑ k ∈ S, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 =
        ∑ k ∈ S_eq, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 +
        ∑ k ∈ S_gt, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 :=
      (Finset.sum_filter_add_sum_filter_not S (fun k : ℤ => x0 + (k : ℝ) / (n : ℝ) = a) _).symm
    rw [hsplit, mul_add]
    have hcard_eq : S_eq.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro k1 hk1 k2 hk2
      have h1 := (Finset.mem_filter.mp hk1).2
      have h2 := (Finset.mem_filter.mp hk2).2
      have hdiv : (k1 : ℝ) / (n : ℝ) = (k2 : ℝ) / (n : ℝ) := by linarith
      have heq : (k1 : ℝ) = (k2 : ℝ) := (div_left_inj' hn_pos.ne').mp hdiv
      exact_mod_cast heq
    have hbound_eq : (1 / (n : ℝ)) * ∑ k ∈ S_eq, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 ≤
        max (α + -β * ((b - a) / 2)) 0 / (n : ℝ) := by
      have hterm : ∀ k ∈ S_eq,
          max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 =
            max (α + -β * ((b - a) / 2)) 0 := by
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
        congr 1; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      have hc : (S_eq.card : ℝ) ≤ 1 := by exact_mod_cast hcard_eq
      have hm : 0 ≤ max (α + -β * ((b - a) / 2)) 0 := le_max_right _ _
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hn_pos.le
    let S' : Finset ℤ := S_gt.image (fun k => -k)
    have hS' : ∀ k' ∈ S', a ≤ (a + b - x0) + (k' : ℝ) / (n : ℝ) ∧ (a + b - x0) + (k' : ℝ) / (n : ℝ) < b := by
      intro k' hk'
      rcases Finset.mem_image.mp hk' with ⟨k, hk, rfl⟩
      rcases Finset.mem_filter.mp hk with ⟨hkS, hne⟩
      rcases hS k hkS with ⟨hlo, hhi⟩
      have hlt : a < x0 + (k : ℝ) / (n : ℝ) := lt_of_le_of_ne hlo (Ne.symm hne)
      push_cast; rw [neg_div]
      constructor <;> linarith
    have hsum_gt : ∑ k ∈ S_gt, max (α + β * (x0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 =
        ∑ k' ∈ S', max (α + (-β) * ((a + b - x0) + (k' : ℝ) / (n : ℝ) - (a + b) / 2)) 0 := by
      dsimp only [S']
      rw [Finset.sum_image (fun x _ y _ h => by omega)]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1; push_cast; ring
    rw [hsum_gt]
    have hbound_gt := discrete_linear_pos_sum_le_nonneg hn (a + b - x0) a b α (-β) hab (by linarith) S' hS'
    have h2 : 2 * max (α + -β * ((b - a) / 2)) 0 / (n : ℝ) =
        max (α + -β * ((b - a) / 2)) 0 / (n : ℝ) + max (α + -β * ((b - a) / 2)) 0 / (n : ℝ) := by ring
    linarith

/- ## Section 5: Moser Variance Bound for E ≥ 45 / 100 -/

private lemma moser_half_sum_le {n : ℕ} (hn : 1 ≤ n) (L0 E : ℝ) (hL0 : 1 ≤ L0)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, 0 ≤ (k : ℝ) / (n : ℝ) - E ∧ (k : ℝ) / (n : ℝ) - E ≤ L0) :
    (1 / (n : ℝ)) * ∑ k ∈ S, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) ≤
      (2 / 3 : ℝ) * L0 ^ 3 + 2 * L0 ^ 2 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  by_cases hne : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]; positivity
  let kmin := S.min' hne
  let kmax := S.max' hne
  have hkmin_p := hS kmin (Finset.min'_mem S hne)
  have hkmax_p := hS kmax (Finset.max'_mem S hne)
  have hle_mm : kmin ≤ kmax := Finset.min'_le S kmax (Finset.max'_mem S hne)
  have hsub : S ⊆ Finset.Icc kmin kmax := fun k hk =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
  have hge0 : ∀ k ∈ Finset.Icc kmin kmax, 0 ≤ L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2 := by
    intro k hk
    have h1 : (kmin : ℝ) / (n : ℝ) ≤ (k : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hk).1) hn_pos.le
    have h2 : (k : ℝ) / (n : ℝ) ≤ (kmax : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hn_pos.le
    nlinarith [hkmin_p.1, hkmax_p.2]
  have hle_icc := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hge0 k hk)
  have hsplit_k : Finset.Icc kmin kmax = insert kmin (Finset.Ioc kmin kmax) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hsplit_k, Finset.sum_insert (by simp)] at hle_icc
  let H : ℝ → ℝ := fun s => L0 ^ 2 * s - s ^ 3 / 3
  have hstep : ∀ k ∈ Finset.Ioc kmin kmax,
      (1 / (n : ℝ)) * (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) ≤
        (H ((k : ℝ) / (n : ℝ) - E) - H (((k - 1 : ℤ) : ℝ) / (n : ℝ) - E)) + 1 / (3 * (n : ℝ) ^ 3) := by
    intro k hk
    have h1 : (kmin : ℝ) / (n : ℝ) ≤ (k : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Ioc.mp hk).1.le) hn_pos.le
    have hsk : 0 ≤ (k : ℝ) / (n : ℝ) - E := by linarith [hkmin_p.1]
    have hdiff : H ((k : ℝ) / (n : ℝ) - E) - H (((k - 1 : ℤ) : ℝ) / (n : ℝ) - E) =
        (1 / (n : ℝ)) * (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) +
          ((k : ℝ) / (n : ℝ) - E) / (n : ℝ) ^ 2 - 1 / (3 * (n : ℝ) ^ 3) := by
      simp only [H]; push_cast; field_simp; ring
    have hpos : 0 ≤ ((k : ℝ) / (n : ℝ) - E) / (n : ℝ) ^ 2 := by positivity
    linarith
  have hcard_le : ((Finset.Ioc kmin kmax).card : ℝ) ≤ L0 * (n : ℝ) := by
    rw [Int.card_Ioc]
    have hcast : ((kmax - kmin).toNat : ℝ) = (kmax : ℝ) - (kmin : ℝ) := by
      have : ((kmax - kmin).toNat : ℤ) = kmax - kmin := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hcast]
    have hdiv : ((kmax : ℝ) - (kmin : ℝ)) / (n : ℝ) ≤ L0 := by
      rw [sub_div]; linarith [hkmin_p.1, hkmax_p.2]
    rwa [div_le_iff₀ hn_pos] at hdiv
  let N : ℕ := (kmax - kmin).toNat
  have hbij : ∑ k ∈ Finset.Ioc kmin kmax,
        (H ((k : ℝ) / (n : ℝ) - E) - H (((k - 1 : ℤ) : ℝ) / (n : ℝ) - E)) =
      ∑ i ∈ Finset.range N,
        (H (((kmin + ((i + 1 : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ) - E) -
          H (((kmin + (i : ℤ) : ℤ) : ℝ) / (n : ℝ) - E)) := by
    refine Finset.sum_bij (fun k _ => (k - kmin - 1).toNat) ?_ ?_ ?_ ?_
    · intro k hk; rcases Finset.mem_Ioc.mp hk with ⟨_, _⟩
      exact Finset.mem_range.mpr (by dsimp [N]; omega)
    · intro a ha b hb h
      rcases Finset.mem_Ioc.mp ha with ⟨_, _⟩; rcases Finset.mem_Ioc.mp hb with ⟨_, _⟩; omega
    · intro i hi; have hi' := Finset.mem_range.mp hi
      exact ⟨kmin + (i : ℤ) + 1, Finset.mem_Ioc.mpr ⟨by omega, by dsimp [N] at hi'; omega⟩, by omega⟩
    · intro k hk
      have hk' := Finset.mem_Ioc.mp hk
      have h1 : kmin + ((k - kmin - 1).toNat : ℤ) = k - 1 := by omega
      have h2 : kmin + (((k - kmin - 1).toNat + 1 : ℕ) : ℤ) = k := by omega
      rw [h1, h2]
  have hteles_eq : ∑ k ∈ Finset.Ioc kmin kmax,
        (H ((k : ℝ) / (n : ℝ) - E) - H (((k - 1 : ℤ) : ℝ) / (n : ℝ) - E)) =
      H ((kmax : ℝ) / (n : ℝ) - E) - H ((kmin : ℝ) / (n : ℝ) - E) := by
    rw [hbij, Finset.sum_range_sub (fun i : ℕ => H (((kmin + (i : ℤ) : ℤ) : ℝ) / (n : ℝ) - E)) N]
    have htop : (kmin : ℤ) + (N : ℤ) = kmax := by dsimp [N]; omega
    simp [htop]
  have hteles : (1 / (n : ℝ)) * ∑ k ∈ Finset.Ioc kmin kmax, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) ≤
      H ((kmax : ℝ) / (n : ℝ) - E) - H ((kmin : ℝ) / (n : ℝ) - E) +
        ((Finset.Ioc kmin kmax).card : ℝ) / (3 * (n : ℝ) ^ 3) := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ Finset.Ioc kmin kmax, (1 / (n : ℝ)) * (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2)
        ≤ ∑ k ∈ Finset.Ioc kmin kmax,
            ((H ((k : ℝ) / (n : ℝ) - E) - H (((k - 1 : ℤ) : ℝ) / (n : ℝ) - E)) + 1 / (3 * (n : ℝ) ^ 3)) :=
          Finset.sum_le_sum hstep
      _ = H ((kmax : ℝ) / (n : ℝ) - E) - H ((kmin : ℝ) / (n : ℝ) - E) +
            ((Finset.Ioc kmin kmax).card : ℝ) / (3 * (n : ℝ) ^ 3) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hteles_eq]; ring
  have hH_inc : ∀ u v, 0 ≤ u → u ≤ v → v ≤ L0 → H u ≤ H v := by
    intro u v hu huv hv
    have hdiff : H v - H u = (v - u) * (L0 ^ 2 - (u ^ 2 + u * v + v ^ 2) / 3) := by simp only [H]; ring
    have h1 : u ^ 2 ≤ L0 ^ 2 := by nlinarith
    have h2 : v ^ 2 ≤ L0 ^ 2 := by nlinarith
    have h3 : u * v ≤ L0 ^ 2 := by nlinarith
    have hpos : 0 ≤ L0 ^ 2 - (u ^ 2 + u * v + v ^ 2) / 3 := by linarith
    linarith [mul_nonneg (sub_nonneg.mpr huv) hpos]
  have hHtop : H ((kmax : ℝ) / (n : ℝ) - E) ≤ H L0 := hH_inc _ _ hkmax_p.1 hkmax_p.2 le_rfl
  have hHbot : H 0 ≤ H ((kmin : ℝ) / (n : ℝ) - E) := hH_inc _ _ le_rfl hkmin_p.1 hkmin_p.2
  have hH0 : H L0 - H 0 = (2 / 3 : ℝ) * L0 ^ 3 := by simp only [H]; ring
  have herr : ((Finset.Ioc kmin kmax).card : ℝ) / (3 * (n : ℝ) ^ 3) ≤ L0 ^ 2 / (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : ((Finset.Ioc kmin kmax).card : ℝ) / (3 * (n : ℝ) ^ 3) ≤ L0 * (n : ℝ) / (3 * (n : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right hcard_le (by positivity)
    have h2 : L0 * (n : ℝ) / (3 * (n : ℝ) ^ 3) ≤ L0 ^ 2 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hn_pos]
      have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
      have hL : L0 ≤ 3 * L0 ^ 2 := by nlinarith
      nlinarith
    exact h1.trans h2
  have hfirst_le : (1 / (n : ℝ)) * (L0 ^ 2 - ((kmin : ℝ) / (n : ℝ) - E) ^ 2) ≤ L0 ^ 2 / (n : ℝ) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ((kmin : ℝ) / (n : ℝ) - E)]) hn_pos.le
  have htot := mul_le_mul_of_nonneg_left hle_icc (by positivity : 0 ≤ 1 / (n : ℝ))
  rw [mul_add] at htot
  have h2 : 2 * L0 ^ 2 / (n : ℝ) = L0 ^ 2 / (n : ℝ) + L0 ^ 2 / (n : ℝ) := by ring
  linarith

lemma moser_lower_bound {n : ℕ} (hn : 1 ≤ n) {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (hcard : A.card = B.card)
    (hE : (45 / 100 : ℝ) ≤ EVal n A) :
    (38 / 100 : ℝ) - 5 / (n : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  set Ω : ℝ := (Erdos36.MaxOverlap A B : ℝ) / (n : ℝ)
  set E : ℝ := EVal n A
  set L0 : ℝ := 131 / 100
  have hL0_ge1 : 1 ≤ L0 := by norm_num [L0]
  have hm_le : ∀ k : ℤ, mVal n A B k ≤ Ω := by
    intro k; unfold mVal
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_ciSup (bddAbove_overlap A B) k) hn_pos.le
  have hm_nn : ∀ k : ℤ, 0 ≤ mVal n A B k := fun k => by unfold mVal; positivity
  have hpt : ∀ k : ℤ,
      (((k : ℝ) / (n : ℝ) - E) ^ 2 - L0 ^ 2) * mVal n A B k ≥
        -Ω * max (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) 0 := by
    intro k
    by_cases h : ((k : ℝ) / (n : ℝ) - E) ^ 2 ≤ L0 ^ 2
    · rw [max_eq_left (sub_nonneg.mpr h)]; nlinarith [hm_le k]
    · push Not at h; rw [max_eq_right (by linarith), mul_zero]
      exact mul_nonneg (by linarith) (hm_nn k)
  have hsum_lhs : (1 / (n : ℝ)) * ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ) - E) ^ 2 - L0 ^ 2) * mVal n A B k =
      2 / 3 - E ^ 2 / 2 - L0 ^ 2 - 1 / (6 * (n : ℝ) ^ 2) := by
    have h1 := mass_eq hn hdisj hunion hcard
    have h2 := mean_eq hn hdisj hunion hcard
    have h3 := mom2_eq hn hdisj hunion hcard
    have hexp : ∀ k : ℤ, (((k : ℝ) / (n : ℝ) - E) ^ 2 - L0 ^ 2) * mVal n A B k =
        (((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k - (2 * E) * (((k : ℝ) / (n : ℝ)) * mVal n A B k) +
          (E ^ 2 - L0 ^ 2) * mVal n A B k := fun k => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [mul_add, mul_sub]
    rw [show (1 / (n : ℝ)) * (2 * E * ∑ k ∈ KSet n, (k : ℝ) / (n : ℝ) * mVal n A B k) =
        2 * E * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, (k : ℝ) / (n : ℝ) * mVal n A B k) by ring]
    rw [show (1 / (n : ℝ)) * ((E ^ 2 - L0 ^ 2) * ∑ k ∈ KSet n, mVal n A B k) =
        (E ^ 2 - L0 ^ 2) * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, mVal n A B k) by ring]
    rw [h1, h2, h3]; change _ = _; ring
  have hsum_rhs : (1 / (n : ℝ)) * ∑ k ∈ KSet n, max (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) 0 ≤
      (4 / 3 : ℝ) * L0 ^ 3 + 4 * L0 ^ 2 / (n : ℝ) := by
    let SL : Finset ℤ := (KSet n).filter (fun k : ℤ => -L0 ≤ (k : ℝ) / (n : ℝ) - E ∧ (k : ℝ) / (n : ℝ) - E ≤ 0)
    let SR : Finset ℤ := (KSet n).filter (fun k : ℤ => 0 < (k : ℝ) / (n : ℝ) - E ∧ (k : ℝ) / (n : ℝ) - E ≤ L0)
    have hdisj_LR : Disjoint SL SR := by
      rw [Finset.disjoint_left]; intro k h1 h2
      linarith [(Finset.mem_filter.mp h1).2.2, (Finset.mem_filter.mp h2).2.1]
    have hsplit_sum : ∑ k ∈ KSet n, max (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) 0 =
        ∑ k ∈ SL, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) +
        ∑ k ∈ SR, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) := by
      have hsubLR : SL ∪ SR ⊆ KSet n := Finset.union_subset (Finset.filter_subset _ (KSet n)) (Finset.filter_subset _ (KSet n))
      rw [← Finset.sum_subset hsubLR]
      · rw [Finset.sum_union hdisj_LR]; congr 1
        · refine Finset.sum_congr rfl fun k hk => ?_
          have h := (Finset.mem_filter.mp hk).2
          rw [max_eq_left]; nlinarith
        · refine Finset.sum_congr rfl fun k hk => ?_
          have h := (Finset.mem_filter.mp hk).2
          rw [max_eq_left]; nlinarith
      · intro k hk hnot
        rw [Finset.mem_union] at hnot; push Not at hnot
        rw [max_eq_right_iff]
        have h1 : ¬ (-L0 ≤ (k : ℝ) / (n : ℝ) - E ∧ (k : ℝ) / (n : ℝ) - E ≤ 0) :=
          fun hp => hnot.1 (Finset.mem_filter.mpr ⟨hk, hp⟩)
        have h2 : ¬ (0 < (k : ℝ) / (n : ℝ) - E ∧ (k : ℝ) / (n : ℝ) - E ≤ L0) :=
          fun hp => hnot.2 (Finset.mem_filter.mpr ⟨hk, hp⟩)
        by_cases h0 : (k : ℝ) / (n : ℝ) - E ≤ 0
        · have : (k : ℝ) / (n : ℝ) - E < -L0 := by by_contra hc; push Not at hc; exact h1 ⟨hc, h0⟩
          nlinarith
        · push Not at h0
          have : L0 < (k : ℝ) / (n : ℝ) - E := by by_contra hc; push Not at hc; exact h2 ⟨h0, hc⟩
          nlinarith
    rw [hsplit_sum, mul_add]
    have hR : (1 / (n : ℝ)) * ∑ k ∈ SR, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) ≤
        (2 / 3 : ℝ) * L0 ^ 3 + 2 * L0 ^ 2 / (n : ℝ) :=
      moser_half_sum_le hn L0 E hL0_ge1 SR (fun k hk =>
        ⟨(Finset.mem_filter.mp hk).2.1.le, (Finset.mem_filter.mp hk).2.2⟩)
    let SL' : Finset ℤ := SL.image (fun k => -k)
    have hSL_eq : ∑ k ∈ SL, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) =
        ∑ k' ∈ SL', (L0 ^ 2 - ((k' : ℝ) / (n : ℝ) - (-E)) ^ 2) := by
      dsimp only [SL']
      rw [Finset.sum_image (fun x _ y _ h => by omega)]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    have hL : (1 / (n : ℝ)) * ∑ k ∈ SL, (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) ≤
        (2 / 3 : ℝ) * L0 ^ 3 + 2 * L0 ^ 2 / (n : ℝ) := by
      rw [hSL_eq]
      refine moser_half_sum_le hn L0 (-E) hL0_ge1 SL' fun k' hk' => ?_
      rcases Finset.mem_image.mp hk' with ⟨k, hk, rfl⟩
      have h := (Finset.mem_filter.mp hk).2
      push_cast; rw [neg_div]
      constructor <;> linarith
    have h4 : 4 * L0 ^ 2 / (n : ℝ) = 2 * L0 ^ 2 / (n : ℝ) + 2 * L0 ^ 2 / (n : ℝ) := by ring
    linarith
  have hΩ_nn : 0 ≤ Ω := by positivity
  have hcomb : -Ω * ((4 / 3 : ℝ) * L0 ^ 3 + 4 * L0 ^ 2 / (n : ℝ)) ≤
      2 / 3 - E ^ 2 / 2 - L0 ^ 2 - 1 / (6 * (n : ℝ) ^ 2) := by
    rw [← hsum_lhs]
    calc -Ω * ((4 / 3 : ℝ) * L0 ^ 3 + 4 * L0 ^ 2 / (n : ℝ))
        ≤ -Ω * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, max (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) 0) :=
          mul_le_mul_of_nonpos_left hsum_rhs (by linarith)
      _ = (1 / (n : ℝ)) * ∑ k ∈ KSet n, (-Ω * max (L0 ^ 2 - ((k : ℝ) / (n : ℝ) - E) ^ 2) 0) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (1 / (n : ℝ)) * ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ) - E) ^ 2 - L0 ^ 2) * mVal n A B k :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpt k) (by positivity)
  have hΩ_le1 : Ω ≤ 1 := by
    have ⟨hA, _⟩ := card_eq_n hdisj hunion hcard
    have hmo : Erdos36.MaxOverlap A B ≤ n := by
      unfold Erdos36.MaxOverlap
      refine ciSup_le fun k => ?_
      rw [← hA]
      unfold Erdos36.Overlap
      refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq h => ?_)
      · exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · have hp' := (Finset.mem_filter.mp hp).2
        have hq' := (Finset.mem_filter.mp hq).2
        dsimp at hp' hq'
        exact Prod.ext h (by omega)
    dsimp [Ω]; rw [div_le_one hn_pos]; exact_mod_cast hmo
  have hE2 : (45 / 100 : ℝ) ^ 2 ≤ E ^ 2 := by nlinarith
  have hinv_nn : 0 ≤ 1 / (6 * (n : ℝ) ^ 2) := by positivity
  have hnum : (4 / 3 : ℝ) * L0 ^ 3 * (38 / 100 : ℝ) ≤ L0 ^ 2 - 2 / 3 + (45 / 100 : ℝ) ^ 2 / 2 := by
    norm_num [L0]
  have herr : 4 * L0 ^ 2 ≤ (4 / 3 : ℝ) * L0 ^ 3 * 5 := by norm_num [L0]
  have hmul : Ω * ((4 / 3 : ℝ) * L0 ^ 3) + 4 * L0 ^ 2 / (n : ℝ) ≥
      (4 / 3 : ℝ) * L0 ^ 3 * (38 / 100 : ℝ) := by
    have h1 : Ω * (4 * L0 ^ 2 / (n : ℝ)) ≤ 4 * L0 ^ 2 / (n : ℝ) :=
      mul_le_of_le_one_left (by positivity) hΩ_le1
    nlinarith
  have hden_pos : 0 < (4 / 3 : ℝ) * L0 ^ 3 := by positivity
  have herr_div : 4 * L0 ^ 2 / (n : ℝ) ≤ (4 / 3 : ℝ) * L0 ^ 3 * (5 / (n : ℝ)) := by
    rw [show (4 / 3 : ℝ) * L0 ^ 3 * (5 / (n : ℝ)) = ((4 / 3 : ℝ) * L0 ^ 3 * 5) / (n : ℝ) by ring]
    exact div_le_div_of_nonneg_right herr hn_pos.le
  nlinarith




inductive NatTree where
  | leaf (v : Nat)
  | node (l r : NatTree)

def NatTree.get : NatTree → Nat → Nat → Nat
  | .leaf v, _, _ => v
  | .node l r, half, idx =>
      if Nat.blt idx half then l.get (half / 2) idx
      else r.get (half / 2) (idx - half)

def cosTree : NatTree := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 10000000) (.leaf 9999953)) (.node (.leaf 9999812) (.leaf 9999576))) (.node (.node (.leaf 9999247) (.leaf 9998823)) (.node (.leaf 9998306) (.leaf 9997694)))) (.node (.node (.node (.leaf 9996988) (.leaf 9996188)) (.node (.leaf 9995294) (.leaf 9994306))) (.node (.node (.leaf 9993224) (.leaf 9992048)) (.node (.leaf 9990777) (.leaf 9989413))))) (.node (.node (.node (.node (.leaf 9987955) (.leaf 9986402)) (.node (.leaf 9984756) (.leaf 9983015))) (.node (.node (.leaf 9981181) (.leaf 9979253)) (.node (.leaf 9977231) (.leaf 9975115)))) (.node (.node (.node (.leaf 9972905) (.leaf 9970601)) (.node (.leaf 9968203) (.leaf 9965711))) (.node (.node (.leaf 9963126) (.leaf 9960447)) (.node (.leaf 9957674) (.leaf 9954808)))))) (.node (.node (.node (.node (.node (.leaf 9951847) (.leaf 9948793)) (.node (.leaf 9945646) (.leaf 9942404))) (.node (.node (.leaf 9939070) (.leaf 9935641)) (.node (.leaf 9932119) (.leaf 9928504)))) (.node (.node (.node (.leaf 9924795) (.leaf 9920993)) (.node (.leaf 9917098) (.leaf 9913109))) (.node (.node (.leaf 9909026) (.leaf 9904851)) (.node (.leaf 9900582) (.leaf 9896220))))) (.node (.node (.node (.node (.leaf 9891765) (.leaf 9887217)) (.node (.leaf 9882576) (.leaf 9877841))) (.node (.node (.leaf 9873014) (.leaf 9868094)) (.node (.leaf 9863081) (.leaf 9857975)))) (.node (.node (.node (.leaf 9852776) (.leaf 9847485)) (.node (.leaf 9842101) (.leaf 9836624))) (.node (.node (.leaf 9831055) (.leaf 9825393)) (.node (.leaf 9819639) (.leaf 9813792))))))) (.node (.node (.node (.node (.node (.node (.leaf 9807853) (.leaf 9801821)) (.node (.leaf 9795698) (.leaf 9789482))) (.node (.node (.leaf 9783174) (.leaf 9776774)) (.node (.leaf 9770281) (.leaf 9763697)))) (.node (.node (.node (.leaf 9757021) (.leaf 9750253)) (.node (.leaf 9743394) (.leaf 9736442))) (.node (.node (.leaf 9729400) (.leaf 9722265)) (.node (.leaf 9715039) (.leaf 9707721))))) (.node (.node (.node (.node (.leaf 9700313) (.leaf 9692812)) (.node (.leaf 9685221) (.leaf 9677538))) (.node (.node (.leaf 9669765) (.leaf 9661900)) (.node (.leaf 9653944) (.leaf 9645898)))) (.node (.node (.node (.leaf 9637761) (.leaf 9629533)) (.node (.leaf 9621214) (.leaf 9612805))) (.node (.node (.leaf 9604305) (.leaf 9595715)) (.node (.leaf 9587035) (.leaf 9578264)))))) (.node (.node (.node (.node (.node (.leaf 9569403) (.leaf 9560453)) (.node (.leaf 9551412) (.leaf 9542281))) (.node (.node (.leaf 9533060) (.leaf 9523750)) (.node (.leaf 9514350) (.leaf 9504861)))) (.node (.node (.node (.leaf 9495282) (.leaf 9485613)) (.node (.leaf 9475856) (.leaf 9466009))) (.node (.node (.leaf 9456073) (.leaf 9446048)) (.node (.leaf 9435935) (.leaf 9425732))))) (.node (.node (.node (.node (.leaf 9415441) (.leaf 9405061)) (.node (.leaf 9394592) (.leaf 9384035))) (.node (.node (.leaf 9373390) (.leaf 9362657)) (.node (.leaf 9351835) (.leaf 9340926)))) (.node (.node (.node (.leaf 9329928) (.leaf 9318843)) (.node (.leaf 9307670) (.leaf 9296409))) (.node (.node (.leaf 9285061) (.leaf 9273625)) (.node (.leaf 9262102) (.leaf 9250492)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 9238795) (.leaf 9227011)) (.node (.leaf 9215140) (.leaf 9203183))) (.node (.node (.leaf 9191139) (.leaf 9179008)) (.node (.leaf 9166791) (.leaf 9154487)))) (.node (.node (.node (.leaf 9142098) (.leaf 9129622)) (.node (.leaf 9117060) (.leaf 9104413))) (.node (.node (.leaf 9091680) (.leaf 9078861)) (.node (.leaf 9065957) (.leaf 9052968))))) (.node (.node (.node (.node (.leaf 9039893) (.leaf 9026733)) (.node (.leaf 9013488) (.leaf 9000159))) (.node (.node (.leaf 8986745) (.leaf 8973246)) (.node (.leaf 8959662) (.leaf 8945995)))) (.node (.node (.node (.leaf 8932243) (.leaf 8918407)) (.node (.leaf 8904487) (.leaf 8890484))) (.node (.node (.leaf 8876396) (.leaf 8862225)) (.node (.leaf 8847971) (.leaf 8833633)))))) (.node (.node (.node (.node (.node (.leaf 8819213) (.leaf 8804709)) (.node (.leaf 8790122) (.leaf 8775453))) (.node (.node (.leaf 8760701) (.leaf 8745867)) (.node (.leaf 8730950) (.leaf 8715951)))) (.node (.node (.node (.leaf 8700870) (.leaf 8685707)) (.node (.leaf 8670462) (.leaf 8655136))) (.node (.node (.leaf 8639729) (.leaf 8624240)) (.node (.leaf 8608669) (.leaf 8593018))))) (.node (.node (.node (.node (.leaf 8577286) (.leaf 8561473)) (.node (.leaf 8545580) (.leaf 8529606))) (.node (.node (.leaf 8513552) (.leaf 8497418)) (.node (.leaf 8481203) (.leaf 8464909)))) (.node (.node (.node (.leaf 8448536) (.leaf 8432082)) (.node (.leaf 8415550) (.leaf 8398938))) (.node (.node (.leaf 8382247) (.leaf 8365477)) (.node (.leaf 8348629) (.leaf 8331702))))))) (.node (.node (.node (.node (.node (.node (.leaf 8314696) (.leaf 8297612)) (.node (.leaf 8280450) (.leaf 8263211))) (.node (.node (.leaf 8245893) (.leaf 8228498)) (.node (.leaf 8211025) (.leaf 8193475)))) (.node (.node (.node (.leaf 8175848) (.leaf 8158144)) (.node (.leaf 8140363) (.leaf 8122506))) (.node (.node (.leaf 8104572) (.leaf 8086562)) (.node (.leaf 8068476) (.leaf 8050313))))) (.node (.node (.node (.node (.leaf 8032075) (.leaf 8013762)) (.node (.leaf 7995373) (.leaf 7976908))) (.node (.node (.leaf 7958369) (.leaf 7939755)) (.node (.leaf 7921066) (.leaf 7902302)))) (.node (.node (.node (.leaf 7883464) (.leaf 7864552)) (.node (.leaf 7845566) (.leaf 7826506))) (.node (.node (.leaf 7807372) (.leaf 7788165)) (.node (.leaf 7768885) (.leaf 7749531)))))) (.node (.node (.node (.node (.node (.leaf 7730105) (.leaf 7710605)) (.node (.leaf 7691033) (.leaf 7671389))) (.node (.node (.leaf 7651673) (.leaf 7631884)) (.node (.leaf 7612024) (.leaf 7592092)))) (.node (.node (.node (.leaf 7572088) (.leaf 7552014)) (.node (.leaf 7531868) (.leaf 7511651))) (.node (.node (.leaf 7491364) (.leaf 7471006)) (.node (.leaf 7450578) (.leaf 7430080))))) (.node (.node (.node (.node (.leaf 7409511) (.leaf 7388873)) (.node (.leaf 7368166) (.leaf 7347389))) (.node (.node (.leaf 7326543) (.leaf 7305628)) (.node (.leaf 7284644) (.leaf 7263592)))) (.node (.node (.node (.leaf 7242471) (.leaf 7221282)) (.node (.leaf 7200025) (.leaf 7178700))) (.node (.node (.leaf 7157308) (.leaf 7135849)) (.node (.leaf 7114322) (.leaf 7092728)))))))))
def sinTree : NatTree := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 30680)) (.node (.leaf 61359) (.leaf 92038))) (.node (.node (.leaf 122715) (.leaf 153392)) (.node (.leaf 184067) (.leaf 214741)))) (.node (.node (.node (.leaf 245412) (.leaf 276081)) (.node (.leaf 306748) (.leaf 337412))) (.node (.node (.leaf 368072) (.leaf 398729)) (.node (.leaf 429383) (.leaf 460032))))) (.node (.node (.node (.node (.leaf 490677) (.leaf 521317)) (.node (.leaf 551952) (.leaf 582583))) (.node (.node (.leaf 613207) (.leaf 643826)) (.node (.leaf 674439) (.leaf 705046)))) (.node (.node (.node (.leaf 735646) (.leaf 766239)) (.node (.leaf 796824) (.leaf 827403))) (.node (.node (.leaf 857973) (.leaf 888536)) (.node (.leaf 919090) (.leaf 949635)))))) (.node (.node (.node (.node (.node (.leaf 980171) (.leaf 1010699)) (.node (.leaf 1041216) (.leaf 1071724))) (.node (.node (.leaf 1102222) (.leaf 1132710)) (.node (.leaf 1163186) (.leaf 1193652)))) (.node (.node (.node (.leaf 1224107) (.leaf 1254550)) (.node (.leaf 1284981) (.leaf 1315400))) (.node (.node (.leaf 1345807) (.leaf 1376201)) (.node (.leaf 1406582) (.leaf 1436950))))) (.node (.node (.node (.node (.leaf 1467305) (.leaf 1497645)) (.node (.leaf 1527972) (.leaf 1558284))) (.node (.node (.leaf 1588581) (.leaf 1618864)) (.node (.leaf 1649131) (.leaf 1679383)))) (.node (.node (.node (.leaf 1709619) (.leaf 1739839)) (.node (.leaf 1770042) (.leaf 1800229))) (.node (.node (.leaf 1830399) (.leaf 1860552)) (.node (.leaf 1890687) (.leaf 1920804))))))) (.node (.node (.node (.node (.node (.node (.leaf 1950903) (.leaf 1980984)) (.node (.leaf 2011046) (.leaf 2041090))) (.node (.node (.leaf 2071114) (.leaf 2101118)) (.node (.leaf 2131103) (.leaf 2161068)))) (.node (.node (.node (.leaf 2191012) (.leaf 2220936)) (.node (.leaf 2250839) (.leaf 2280721))) (.node (.node (.leaf 2310581) (.leaf 2340420)) (.node (.leaf 2370236) (.leaf 2400030))))) (.node (.node (.node (.node (.leaf 2429802) (.leaf 2459551)) (.node (.leaf 2489276) (.leaf 2518978))) (.node (.node (.leaf 2548657) (.leaf 2578311)) (.node (.leaf 2607941) (.leaf 2637547)))) (.node (.node (.node (.leaf 2667128) (.leaf 2696683)) (.node (.leaf 2726214) (.leaf 2755718))) (.node (.node (.leaf 2785197) (.leaf 2814649)) (.node (.leaf 2844075) (.leaf 2873475)))))) (.node (.node (.node (.node (.node (.leaf 2902847) (.leaf 2932192)) (.node (.leaf 2961509) (.leaf 2990798))) (.node (.node (.leaf 3020059) (.leaf 3049292)) (.node (.leaf 3078496) (.leaf 3107672)))) (.node (.node (.node (.leaf 3136817) (.leaf 3165934)) (.node (.leaf 3195020) (.leaf 3224077))) (.node (.node (.leaf 3253103) (.leaf 3282098)) (.node (.leaf 3311063) (.leaf 3339997))))) (.node (.node (.node (.node (.leaf 3368899) (.leaf 3397769)) (.node (.leaf 3426607) (.leaf 3455413))) (.node (.node (.leaf 3484187) (.leaf 3512928)) (.node (.leaf 3541635) (.leaf 3570310)))) (.node (.node (.node (.leaf 3598950) (.leaf 3627557)) (.node (.leaf 3656130) (.leaf 3684668))) (.node (.node (.leaf 3713172) (.leaf 3741641)) (.node (.leaf 3770074) (.leaf 3798472)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 3826834) (.leaf 3855161)) (.node (.leaf 3883450) (.leaf 3911704))) (.node (.node (.leaf 3939920) (.leaf 3968100)) (.node (.leaf 3996242) (.leaf 4024347)))) (.node (.node (.node (.leaf 4052413) (.leaf 4080442)) (.node (.leaf 4108432) (.leaf 4136383))) (.node (.node (.leaf 4164296) (.leaf 4192169)) (.node (.leaf 4220003) (.leaf 4247797))))) (.node (.node (.node (.node (.leaf 4275551) (.leaf 4303265)) (.node (.leaf 4330938) (.leaf 4358571))) (.node (.node (.leaf 4386162) (.leaf 4413713)) (.node (.leaf 4441221) (.leaf 4468688)))) (.node (.node (.node (.leaf 4496113) (.leaf 4523496)) (.node (.leaf 4550836) (.leaf 4578133))) (.node (.node (.leaf 4605387) (.leaf 4632598)) (.node (.leaf 4659765) (.leaf 4686888)))))) (.node (.node (.node (.node (.node (.leaf 4713967) (.leaf 4741002)) (.node (.leaf 4767992) (.leaf 4794938))) (.node (.node (.leaf 4821838) (.leaf 4848692)) (.node (.leaf 4875502) (.leaf 4902265)))) (.node (.node (.node (.leaf 4928982) (.leaf 4955653)) (.node (.leaf 4982277) (.leaf 5008854))) (.node (.node (.leaf 5035384) (.leaf 5061866)) (.node (.leaf 5088301) (.leaf 5114689))))) (.node (.node (.node (.node (.leaf 5141027) (.leaf 5167318)) (.node (.leaf 5193560) (.leaf 5219753))) (.node (.node (.leaf 5245897) (.leaf 5271991)) (.node (.leaf 5298036) (.leaf 5324031)))) (.node (.node (.node (.leaf 5349976) (.leaf 5375871)) (.node (.leaf 5401715) (.leaf 5427508))) (.node (.node (.leaf 5453250) (.leaf 5478941)) (.node (.leaf 5504580) (.leaf 5530167))))))) (.node (.node (.node (.node (.node (.node (.leaf 5555702) (.leaf 5581185)) (.node (.leaf 5606616) (.leaf 5631993))) (.node (.node (.leaf 5657318) (.leaf 5682590)) (.node (.leaf 5707807) (.leaf 5732972)))) (.node (.node (.node (.leaf 5758082) (.leaf 5783138)) (.node (.leaf 5808140) (.leaf 5833087))) (.node (.node (.leaf 5857979) (.leaf 5882815)) (.node (.leaf 5907597) (.leaf 5932323))))) (.node (.node (.node (.node (.leaf 5956993) (.leaf 5981607)) (.node (.leaf 6006165) (.leaf 6030666))) (.node (.node (.leaf 6055110) (.leaf 6079498)) (.node (.leaf 6103828) (.leaf 6128101)))) (.node (.node (.node (.leaf 6152316) (.leaf 6176473)) (.node (.leaf 6200572) (.leaf 6224613))) (.node (.node (.leaf 6248595) (.leaf 6272518)) (.node (.leaf 6296382) (.leaf 6320187)))))) (.node (.node (.node (.node (.node (.leaf 6343933) (.leaf 6367619)) (.node (.leaf 6391244) (.leaf 6414810))) (.node (.node (.leaf 6438315) (.leaf 6461760)) (.node (.leaf 6485144) (.leaf 6508467)))) (.node (.node (.node (.leaf 6531728) (.leaf 6554929)) (.node (.leaf 6578067) (.leaf 6601143))) (.node (.node (.leaf 6624158) (.leaf 6647110)) (.node (.leaf 6669999) (.leaf 6692826))))) (.node (.node (.node (.node (.leaf 6715590) (.leaf 6738290)) (.node (.leaf 6760927) (.leaf 6783500))) (.node (.node (.leaf 6806010) (.leaf 6828455)) (.node (.leaf 6850837) (.leaf 6873153)))) (.node (.node (.node (.leaf 6895405) (.leaf 6917593)) (.node (.leaf 6939715) (.leaf 6961771))) (.node (.node (.leaf 6983762) (.leaf 7005688)) (.node (.leaf 7027547) (.leaf 7049341)))))))))

def cosTab (i : Nat) : Nat :=
  if Nat.beq i 256 then 7071068 else cosTree.get 128 i

def sinTab (i : Nat) : Nat :=
  if Nat.beq i 256 then 7071068 else sinTree.get 128 i

def natDiff (a b : Nat) : Nat :=
  if Nat.ble a b then b - a else a - b

def checkTrigOne (r : Nat) : Bool :=
  let th := (r * 3141592653) / 1024
  let s9 := 1000000000
  let x2 := (th * th) / s9
  let x4 := (x2 * x2) / s9
  let x6 := (x4 * x2) / s9
  let x8 := (x4 * x4) / s9
  let x10 := (x8 * x2) / s9
  let cApp := s9 + x4 / 24 + x8 / 40320 - x2 / 2 - x6 / 720 - x10 / 3628800
  let x3 := (x2 * th) / s9
  let x5 := (x4 * th) / s9
  let x7 := (x6 * th) / s9
  let x9 := (x8 * th) / s9
  let sApp := th + x5 / 120 + x9 / 362880 - x3 / 6 - x7 / 5040
  Nat.ble (natDiff cApp (cosTab r * 100)) 55 && Nat.ble (natDiff sApp (sinTab r * 100)) 55 &&
    Nat.ble (cosTab r) 10000000 && Nat.ble (sinTab r) 10000000

def checkAllPow2 (p : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => p lo
  | k + 1 => checkAllPow2 p lo k && checkAllPow2 p (lo + 2 ^ k) k

theorem trig_ok : checkAllPow2 checkTrigOne 0 8 && checkTrigOne 256 = true := by
  decide +kernel

-- Fast exact ceil/floor Int division by positive Nat using GMP Nat.div!
def intFdiv (x : Int) (d : Nat) : Int :=
  match x with
  | Int.ofNat n => Int.ofNat (n / d)
  | Int.negSucc n => Int.negSucc (n / d)

def intCdiv (x : Int) (d : Nat) : Int :=
  match x with
  | Int.ofNat n => Int.ofNat ((n + d - 1) / d)
  | Int.negSucc n => Int.negOfNat ((n + 1) / d)

def cosQNat (r : Nat) : Int :=
  let m := r % 2048
  if Nat.ble m 256 then Int.ofNat (cosTab m)
  else if Nat.ble m 512 then Int.ofNat (sinTab (512 - m))
  else if Nat.ble m 768 then Int.negOfNat (sinTab (m - 512))
  else if Nat.ble m 1024 then Int.negOfNat (cosTab (1024 - m))
  else if Nat.ble m 1280 then Int.negOfNat (cosTab (m - 1024))
  else if Nat.ble m 1536 then Int.negOfNat (sinTab (1536 - m))
  else if Nat.ble m 1792 then Int.ofNat (sinTab (m - 1536))
  else Int.ofNat (cosTab (2048 - m))

def sinQNat (r : Nat) : Int := cosQNat (r + 1536)

-- Pure Nat upperIntPos when bHi : Nat!
def upperIntPos (aHi : Int) (bHi dDen : Nat) : Int :=
  let hi2 : Int := 2 * Int.ofNat dDen * aHi + Int.ofNat bHi
  match hi2 with
  | Int.negSucc _ => 0
  | Int.ofNat 0 => 0
  | Int.ofNat h =>
      let lo2 : Int := 2 * Int.ofNat dDen * aHi - Int.ofNat bHi
      match lo2 with
      | Int.ofNat _ => aHi
      | Int.negSucc _ =>
          let den := 8 * dDen * bHi
          Int.ofNat ((h * h + den - 1) / den)

structure Cert where
  h1 : Int
  h2 : Int
  p1 : Int
  p2 : Int
  q1 : Int
  q2 : Int
  mQuad : Nat
  fQuad : Nat
  nuMassM : Int
  nuMassf : Int
  nuEM : Int
  nuElo : Int
  nuEhi : Int
  nuMhi : Int
  nuMlo : Int
  alpha : List Int
  beta : List Int
  gamma : Int
  nuPlo : Int
  nuPhi : Int
  nuQlo : Int
  nuQhi : Int
  u : List Int
  v : List Int
  e0 : Int

def dIntList : List Int := [12732395, 0, -4244132, 0, 2546479, 0, -1818914, 0, 1414711, 0]
def omIntList : List Nat := [15707963, 31415927, 47123890, 62831853, 78539816, 94247780, 109955743, 125663706, 141371669, 157079633]
def omSqHiList : List Nat := [24674014, 98696054, 222066111, 394784188, 616850286, 888264423, 1209026564, 1579136726, 1998594908, 2467401142]

-- Store each frequency term in a flat inductive list (no Prod!)
inductive TermList where
  | nil
  | cons (m : Nat) (cc cs : Int) (om : Nat) (tail : TermList)

def buildTermsM : Nat → List Int → List Int → List Nat → Int → TermList
  | m, a :: as_, b :: bs, om :: oms, gamma =>
      let cc := if Nat.beq m 2 then -a + gamma else -a
      .cons m cc (-b) om (buildTermsM (m + 1) as_ bs oms gamma)
  | _, _, _, _, _ => .nil

def evalMVal (baseAng : Nat) : TermList → Int → Int
  | .nil, acc => acc
  | .cons m cc cs _ tl, acc =>
      let r := m * baseAng
      evalMVal baseAng tl (acc + cc * cosQNat r + cs * sinQNat r)

def evalMDer (baseAng : Nat) : TermList → Int → Int
  | .nil, acc => acc
  | .cons m cc cs om tl, acc =>
      let r := m * baseAng
      evalMDer baseAng tl (acc + (-cc * sinQNat r + cs * cosQNat r) * Int.ofNat om)

def oneMQuad (nuMassM nuEM lam2 padPhi : Int) (errPhiDer dMDen stepM : Nat)
    (terms : TermList) (j : Nat) : Int :=
  let xmNum : Int := 2 * Int.ofNat j + 1 - 4 * Int.ofNat dMDen
  let xmDen : Nat := 2 * dMDen
  let xmDenI : Int := Int.ofNat xmDen
  let xmDen2 : Nat := xmDen * xmDen
  let sT : Int := 10000000
  let polyVal := intCdiv ((-nuMassM * Int.ofNat xmDen2 - nuEM * xmNum * xmDenI - lam2 * xmNum * xmNum) * sT) xmDen2
  let baseAng : Nat := stepM * (2 * j + 1) + 1024
  let tv := evalMVal baseAng terms 0
  let tdRaw := evalMDer baseAng terms 0
  let td := intFdiv tdRaw 10000000
  let polyDerQ := intFdiv ((-nuEM * xmDenI - 2 * lam2 * xmNum) * sT) xmDen
  let bHi : Nat := (polyDerQ + td).natAbs + 2 + errPhiDer
  let aHi : Int := polyVal + tv + padPhi
  upperIntPos aHi bHi dMDen

def sumPow2 (f : Nat → Int) (lo : Nat) : Nat → Int
  | 0 => f lo
  | k + 1 => sumPow2 f lo k + sumPow2 f (lo + 2 ^ k) k

def buildTermsF (c : Cert) : Nat → List Int → List Int → List Int → List Int → List Int → List Nat → TermList
  | m, a :: as_, b :: bs, u :: us, v :: vs, di :: dis, om :: oms =>
      let cc0 := 2 * a * u * 10 - a * di
      let cc := if Nat.beq m 2 then cc0 - c.gamma * (c.p1 + c.p2) * 100000 - c.nuPlo * 10000000 + c.nuPhi * 10000000 else cc0
      let cs0 := 2 * a * v * 10 - b * di
      let cs := if Nat.beq m 2 then cs0 - c.gamma * (c.q1 + c.q2) * 100000 - c.nuQlo * 10000000 + c.nuQhi * 10000000 else cs0
      .cons m cc cs om (buildTermsF c (m + 1) as_ bs us vs dis oms)
  | _, _, _, _, _, _, _ => .nil

def evalFVal (baseAng : Nat) : TermList → Int → Int
  | .nil, acc => acc
  | .cons m cc cs _ tl, acc =>
      let r := m * baseAng
      evalFVal baseAng tl (acc - cc * cosQNat r - cs * sinQNat r)

def evalFDer (baseAng : Nat) : TermList → Int → Int
  | .nil, acc => acc
  | .cons m cc cs om tl, acc =>
      let r := m * baseAng
      evalFDer baseAng tl (acc + (cc * sinQNat r - cs * cosQNat r) * Int.ofNat om)

def oneFQuad (nuMassf linF padPsi : Int) (errPsiDer dFDen stepF : Nat)
    (terms : TermList) (i : Nat) : Int :=
  let tmNum : Int := 2 * Int.ofNat i + 1 - 2 * Int.ofNat dFDen
  let tmDen : Nat := 2 * dFDen
  let sT : Int := 10000000
  let polyVal := intCdiv (-nuMassf * sT * Int.ofNat tmDen - linF * tmNum) tmDen
  let baseAng : Nat := stepF * (2 * i + 1) + 1536
  let tvRaw := evalFVal baseAng terms 0
  let tv := intCdiv tvRaw 10000000
  let tdRaw := evalFDer baseAng terms 0
  let td := intFdiv tdRaw 100000000000000
  let bHi : Nat := (-linF + td).natAbs + 1 + errPsiDer
  let aHi : Int := polyVal + tv + padPsi
  upperIntPos aHi bHi dFDen

def sumB2M : TermList → List Nat → Nat → Nat
  | .cons _ cc cs _ tl, osq :: osqs, acc => sumB2M tl osqs (acc + (cc.natAbs + cs.natAbs) * osq)
  | _, _, acc => acc

def sumErrValM : TermList → Nat → Nat
  | .cons _ cc cs _ tl, acc => sumErrValM tl (acc + cc.natAbs + cs.natAbs)
  | .nil, acc => acc

def sumErrDerM : TermList → Nat → Nat
  | .cons _ cc cs om tl, acc =>
      sumErrDerM tl (acc + (cc.natAbs + cs.natAbs) * ((om + 1 + 10000000 + 10000000 - 1) / 10000000))
  | .nil, acc => acc

def sumB2F : Nat → TermList → List Int → List Int → List Nat → Nat → Nat
  | m, .cons _ cc cs _ tl, a :: as_, b :: bs, osq :: osqs, acc =>
      let ec := if Nat.beq (m % 2) 0 then 0 else a.natAbs
      let es := if Nat.beq (m % 2) 0 then 0 else b.natAbs
      let t := ((cc.natAbs + ec + cs.natAbs + es) * osq + 9999999) / 10000000
      sumB2F (m + 1) tl as_ bs osqs (acc + t)
  | _, _, _, _, _, acc => acc

def sumErrValF : Nat → TermList → List Int → List Int → Nat → Nat
  | m, .cons _ cc cs _ tl, a :: as_, b :: bs, acc =>
      let ec := if Nat.beq (m % 2) 0 then 0 else a.natAbs
      let es := if Nat.beq (m % 2) 0 then 0 else b.natAbs
      let t := ec + es + (cc.natAbs + cs.natAbs + 9999999) / 10000000
      sumErrValF (m + 1) tl as_ bs (acc + t)
  | _, _, _, _, acc => acc

def sumErrDerF : Nat → TermList → List Int → List Int → Nat → Nat
  | m, .cons _ cc cs om tl, a :: as_, b :: bs, acc =>
      let ec := if Nat.beq (m % 2) 0 then 0 else a.natAbs
      let es := if Nat.beq (m % 2) 0 then 0 else b.natAbs
      let t1 := ((ec + es) * (om + 1) + 9999999) / 10000000
      let t2 := ((cc.natAbs + cs.natAbs) * (om + 1 + 10000000) + 99999999999999) / 100000000000000
      sumErrDerF (m + 1) tl as_ bs (acc + t1 + t2)
  | _, _, _, _, acc => acc

def sumQuadTerms : List Int → List Int → List Int → Int → Int
  | a :: as_, u :: us, v :: vs, acc =>
      sumQuadTerms as_ us vs (acc + intFdiv (-a * (u * u + v * v) * 10000000) 1000000000000)
  | _, _, _, acc => acc

def checkCert (c : Cert) : Bool :=
  let sT : Int := 10000000
  let lam2 := c.nuMhi - c.nuMlo
  let termsM := buildTermsM 1 c.alpha c.beta omIntList c.gamma
  let b2Phi : Nat := 2 * lam2.natAbs * 10000000 + sumB2M termsM omSqHiList 0
  let errPhiVal : Nat := sumErrValM termsM 0
  let errPhiDer : Nat := sumErrDerM termsM 0
  let dMDen : Nat := c.mQuad / 4
  let stepM : Nat := 1024 / c.mQuad
  let padPhi : Int := Int.ofNat ((b2Phi + 8 * dMDen * dMDen - 1) / (8 * dMDen * dMDen) + errPhiVal)
  let logM : Nat := if Nat.beq c.mQuad 512 then 9 else 10
  let uPhi := sumPow2 (oneMQuad c.nuMassM c.nuEM lam2 padPhi errPhiDer dMDen stepM termsM) 0 logM

  let linF := -2 * c.nuEM * sT - c.nuMhi * (c.h1 + c.h2) * 100000 + 2 * c.nuMlo * c.e0 * 10
    - 2 * c.nuElo * sT + 2 * c.nuEhi * sT
  let termsF := buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList
  let b2Psi : Nat := sumB2F 1 termsF c.alpha c.beta omSqHiList 0
  let errPsiVal : Nat := sumErrValF 1 termsF c.alpha c.beta 0
  let errPsiDer : Nat := sumErrDerF 1 termsF c.alpha c.beta 0
  let dFDen : Nat := c.fQuad / 2
  let stepF : Nat := 512 / c.fQuad
  let padPsi : Int := Int.ofNat ((b2Psi + 8 * dFDen * dFDen - 1) / (8 * dFDen * dFDen) + errPsiVal)
  let logF : Nat := if Nat.beq c.fQuad 256 then 8 else 9
  let uNegPsi := sumPow2 (oneFQuad c.nuMassf linF padPsi errPsiDer dFDen stepF termsF) 0 logF

  let quadTerms := sumQuadTerms c.alpha c.u c.v 0
  let constRhs :=
    (-c.nuMassM - c.nuMassf) * sT
    + (c.nuElo * c.h1 - c.nuEhi * c.h2) * 100000
    + intFdiv (-2 * lam2 * sT) 3
    + intFdiv (c.nuMhi * c.h1 * c.h2 * sT) 20000
    + intFdiv (-c.nuMlo * c.e0 * c.e0 * sT) 2000000000000
    + quadTerms
    + intFdiv (c.gamma * (c.p1 * c.p2 + c.q1 * c.q2) * sT) 10000
    + (c.nuPlo * c.p1 - c.nuPhi * c.p2 + c.nuQlo * c.q1 - c.nuQhi * c.q2) * 100000
  let lhsNum := constRhs * Int.ofNat dMDen - uNegPsi
  let sideOk : Bool :=
    (Nat.beq c.mQuad 512 || Nat.beq c.mQuad 1024) &&
    Nat.beq (c.fQuad * 2) c.mQuad &&
    Nat.beq c.alpha.length 10 &&
    Nat.beq c.beta.length 10 &&
    Nat.beq c.u.length 10 &&
    Nat.beq c.v.length 10 &&
    decide (0 ≤ c.nuElo ∧ 0 ≤ c.nuEhi ∧ 0 ≤ c.nuMhi ∧ 0 ≤ c.nuMlo ∧
            0 ≤ c.gamma ∧ 0 ≤ c.nuPlo ∧ 0 ≤ c.nuPhi ∧ 0 ≤ c.nuQlo ∧ 0 ≤ c.nuQhi ∧
            c.h1 ≤ c.h2 ∧ c.p1 ≤ c.p2 ∧ c.q1 ≤ c.q2) &&
    c.alpha.all (fun a => decide (0 ≤ a))
  sideOk && decide (0 < uPhi ∧ 38 * uPhi ≤ 100 * lhsNum)

def cert0 : Cert := { h1 := 0, h2 := 45, p1 := 0, p2 := 33, q1 := -100, q2 := 0, mQuad := 512, fQuad := 256, nuMassM := -597365, nuMassf := 11087, nuEM := -312144, nuElo := 103701, nuEhi := 0, nuMhi := 469819, nuMlo := 173797, alpha := [0, 0, 70716, 222347, 106782, 102239, 0, 37039, 8174, 20156], beta := [243042, -404029, -135980, -235792, -61359, -45536, 15588, 12594, 10154, 5149], gamma := 164588, nuPlo := 0, nuPhi := 19962, nuQlo := 0, nuQhi := 0, u := [780602, 330000, 23695, -8684, 58136, 47177, -13722, -17685, 24406, 17262], v := [-5108, -24663, -29965, -4706, 3679, -41149, -75036, -15336, 73872, 16294], e0 := 0 }
theorem cert0_ok : checkCert cert0 = true := by decide +kernel

def cert1 : Cert := { h1 := 0, h2 := 45, p1 := 0, p2 := 33, q1 := 0, q2 := 25, mQuad := 512, fQuad := 256, nuMassM := -569656, nuMassf := 21552, nuEM := 57994, nuElo := 0, nuEhi := 0, nuMhi := 245253, nuMlo := 0, alpha := [0, 0, 152307, 204610, 189352, 107128, 54207, 32695, 18023, 9333], beta := [-181865, -82492, -43868, 92965, 98557, 69296, -592, -20945, -19540, -4498], gamma := 203127, nuPlo := 0, nuPhi := 0, nuQlo := 0, nuQhi := 0, u := [783683, 329414, 6787, -26847, 64751, 59937, -42990, -74877, 27060, 101865], v := [18063, 33026, 41709, 42263, 35003, 20797, 74, -23480, -38260, -28920], e0 := 23627 }
theorem cert1_ok : checkCert cert1 = true := by decide +kernel

def cert2 : Cert := { h1 := 0, h2 := 45, p1 := 0, p2 := 33, q1 := 25, q2 := 100, mQuad := 512, fQuad := 256, nuMassM := -500220, nuMassf := 1570, nuEM := 42598, nuElo := 0, nuEhi := 0, nuMhi := 190820, nuMlo := 0, alpha := [0, 0, 222898, 83459, 0, 0, 44240, 41589, 18109, 4971], beta := [-322192, -189302, 35125, 210054, 135362, 48137, 7933, 20381, 12497, 5276], gamma := 15210, nuPlo := 0, nuPhi := 0, nuQlo := 289617, nuQhi := 0, u := [646819, 22789, -199889, -13236, 104080, -9693, -87468, -309, 65153, 7315], v := [121497, 250000, 249676, 84013, -28247, 49907, 116631, -4097, -84843, 151077], e0 := 140402 }
theorem cert2_ok : checkCert cert2 = true := by decide +kernel

def cert3 : Cert := { h1 := 0, h2 := 45, p1 := 45, p2 := 100, q1 := -100, q2 := 100, mQuad := 512, fQuad := 256, nuMassM := -520764, nuMassf := 44977, nuEM := 218494, nuElo := 0, nuEhi := 0, nuMhi := 233171, nuMlo := 0, alpha := [0, 53970, 243077, 203900, 0, 0, 0, 33458, 7838, 0], beta := [-330606, 59431, -80489, 49990, -14751, 6042, -252, 11492, 8057, -45], gamma := 0, nuPlo := 182988, nuPhi := 0, nuQlo := 0, nuQhi := 0, u := [837278, 450000, 67005, -118639, -76744, 63140, 133030, 62542, -78045, -153405], v := [750, 1158, 1820, 3582, 5924, 6985, 6440, 8866, 23161, 56059], e0 := 1090 }
theorem cert3_ok : checkCert cert3 = true := by decide +kernel

def cert4 : Cert := { h1 := 0, h2 := 45, p1 := 33, p2 := 45, q1 := -100, q2 := -4, mQuad := 512, fQuad := 256, nuMassM := -553745, nuMassf := 37962, nuEM := -88256, nuElo := 113964, nuEhi := 0, nuMhi := 381454, nuMlo := 145987, alpha := [0, 0, 183412, 191918, 126468, 57398, 33773, 37729, 23858, 10960], beta := [32326, -234145, -235279, -261743, -101619, 20603, 97150, 73884, 34284, 6220], gamma := 142146, nuPlo := 0, nuPhi := 0, nuQlo := 0, nuQhi := 85873, u := [796823, 373314, 58982, -25264, 12914, 50137, 42766, -3723, -27887, 60107], v := [-8586, -40000, -45427, -7423, -9058, -90420, -141631, -62432, 65189, 92980], e0 := 0 }
theorem cert4_ok : checkCert cert4 = true := by decide +kernel

def cert5 : Cert := { h1 := 0, h2 := 45, p1 := 33, p2 := 45, q1 := 4, q2 := 100, mQuad := 512, fQuad := 256, nuMassM := -545041, nuMassf := 30102, nuEM := 72858, nuElo := 0, nuEhi := 0, nuMhi := 227096, nuMlo := 0, alpha := [0, 0, 211953, 201198, 123727, 42820, 23573, 29078, 20198, 8877], beta := [-253221, -112001, -25219, 151823, 126030, 55719, -29408, -35366, -20259, -2630], gamma := 119291, nuPlo := 0, nuPhi := 0, nuQlo := 0, nuQhi := 0, u := [796587, 354524, 9601, -57046, 48083, 104817, 36354, -41843, -6897, 99391], v := [23142, 46374, 61896, 63393, 58289, 57840, 54063, 22637, -36947, -72513], e0 := 28852 }
theorem cert5_ok : checkCert cert5 = true := by decide +kernel

def cert6 : Cert := { h1 := 5, h2 := 45, p1 := 33, p2 := 45, q1 := -4, q2 := 4, mQuad := 512, fQuad := 256, nuMassM := -547794, nuMassf := 31102, nuEM := -19352, nuElo := 199782, nuEhi := 0, nuMhi := 395759, nuMlo := 164661, alpha := [0, 0, 204265, 200935, 120020, 39887, 15869, 21527, 14568, 6024], beta := [-285563, -400874, -240958, -43193, 56177, 54756, 16795, 10644, 6904, 8394], gamma := 120878, nuPlo := 0, nuPhi := 0, nuQlo := 0, nuQhi := 77214, u := [795785, 355007, 14831, -51660, 47037, 104167, 48713, -25138, -12721, 76073], v := [32745, 40000, 38127, 51423, 59045, 21185, -44029, -58532, 13159, 87859], e0 := 50000 }
theorem cert6_ok : checkCert cert6 = true := by decide +kernel

def cert7 : Cert := { h1 := 0, h2 := 5, p1 := 33, p2 := 37, q1 := -4, q2 := 4, mQuad := 1024, fQuad := 512, nuMassM := -564260, nuMassf := 27487, nuEM := 42830, nuElo := 0, nuEhi := 0, nuMhi := 249836, nuMlo := 0, alpha := [0, 0, 187610, 250720, 162527, 74741, 0, 11200, 6029, 12191], beta := [-61585, 15488, -19870, 11049, -3433, 5592, -3552, 469, -1227, 683], gamma := 139807, nuPlo := 0, nuPhi := 11586, nuQlo := 0, nuQhi := 0, u := [802436, 370000, 26594, -45346, 57378, 112926, 29864, -79129, -66836, 50044], v := [429, 727, 1043, 1503, 1787, 1420, 571, 60, 38, -1197], e0 := 594 }
theorem cert7_ok : checkCert cert7 = true := by decide +kernel

def cert8 : Cert := { h1 := 0, h2 := 5, p1 := 37, p2 := 41, q1 := -4, q2 := 4, mQuad := 1024, fQuad := 512, nuMassM := -557407, nuMassf := 31508, nuEM := 62310, nuElo := 0, nuEhi := 0, nuMhi := 242848, nuMlo := 0, alpha := [0, 0, 203068, 244050, 150514, 59794, 0, 11210, 7739, 9653], beta := [-85359, 27574, -25531, 15467, -6400, 6832, -3966, 2079, -482, 1187], gamma := 125533, nuPlo := 0, nuPhi := 0, nuQlo := 0, nuQhi := 0, u := [809983, 386926, 35815, -53281, 51458, 136874, 80153, -40753, -63069, 58855], v := [296, 556, 833, 1171, 1464, 1564, 1556, 1702, 1819, 689], e0 := 391 }
theorem cert8_ok : checkCert cert8 = true := by decide +kernel

def cert9 : Cert := { h1 := 0, h2 := 5, p1 := 41, p2 := 45, q1 := -4, q2 := 4, mQuad := 512, fQuad := 256, nuMassM := -518831, nuMassf := 49366, nuEM := -760, nuElo := 0, nuEhi := 0, nuMhi := 202911, nuMlo := 0, alpha := [0, 0, 264985, 181014, 82323, 0, 18136, 21580, 15519, 0], beta := [-5236, -6797, -1578, 861, 751, -631, 62, 941, 1041, 366], gamma := 57466, nuPlo := 96175, nuPhi := 0, nuQlo := 0, nuQhi := 0, u := [820550, 410000, 43887, -80556, 12803, 138134, 139213, 28391, -50421, 14837], v := [90, 140, 224, 429, 673, 759, 723, 1067, 2421, 4720], e0 := 130 }
theorem cert9_ok : checkCert cert9 = true := by decide +kernel


/- Section 6: Soundness Bridge from Integer Kernel Certificate to Discrete Lower Bound -/

/- Subsection 6A: Basic Nat/Int Division, Tree, and Range Helpers -/

private lemma abs_sin_le_abs_self (x : ℝ) : |Real.sin x| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_le]
    constructor
    · linarith [sin_ge_t3 hx, sin_le_self_of_nonneg hx, Real.neg_one_le_sin x,
        show -(x) ≤ Real.sin x by
          by_cases hx1 : x ≤ 1
          · have h3 := sin_ge_t3 hx
            nlinarith [sq_nonneg x]
          · linarith [Real.neg_one_le_sin x]]
    · exact sin_le_self_of_nonneg hx
  · have hnx : 0 ≤ -x := by linarith
    rw [abs_of_nonpos hx]
    have h1 : |Real.sin (-x)| ≤ -x := by
      rw [abs_le]
      constructor
      · by_cases hx1 : -x ≤ 1
        · have h3 := sin_ge_t3 hnx; nlinarith [sq_nonneg (-x)]
        · linarith [Real.neg_one_le_sin (-x)]
      · exact sin_le_self_of_nonneg hnx
    rwa [Real.sin_neg, abs_neg] at h1

private lemma abs_cos_sub_cos_le_self (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_two]
  have h1 : |Real.sin ((x + y) / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := abs_sin_le_abs_self _
  have h3 : |(x - y) / 2| = |x - y| / 2 := by rw [abs_div, abs_two]
  nlinarith [abs_nonneg (Real.sin ((x - y) / 2))]

private lemma abs_sin_sub_sin_le_self (x y : ℝ) : |Real.sin x - Real.sin y| ≤ |x - y| := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul, abs_two]
  have h1 : |Real.cos ((x + y) / 2)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := abs_sin_le_abs_self _
  have h3 : |(x - y) / 2| = |x - y| / 2 := by rw [abs_div, abs_two]
  nlinarith [abs_nonneg (Real.sin ((x - y) / 2))]

private lemma checkAllPow2_true {p : Nat → Bool} :
    ∀ k lo, checkAllPow2 p lo k = true → ∀ r, lo ≤ r → r < lo + 2 ^ k → p r = true
  | 0, lo, h, r, hlo, hhi => by
      have hr : r = lo := by omega
      subst hr; simpa [checkAllPow2] using h
  | k + 1, lo, h, r, hlo, hhi => by
      simp only [checkAllPow2, Bool.and_eq_true] at h
      by_cases hlt : r < lo + 2 ^ k
      · exact checkAllPow2_true k lo h.1 r hlo hlt
      · exact checkAllPow2_true k (lo + 2 ^ k) h.2 r (by omega) (by rw [pow_succ] at hhi; omega)

private lemma sumPow2_eq_sum_range (f : Nat → Int) :
    ∀ k lo, sumPow2 f lo k = ∑ i ∈ Finset.range (2 ^ k), f (lo + i)
  | 0, lo => by simp [sumPow2]
  | k + 1, lo => by
      simp only [sumPow2, sumPow2_eq_sum_range f k lo, sumPow2_eq_sum_range f k (lo + 2 ^ k)]
      rw [pow_succ, mul_two, Finset.sum_range_add]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_assoc]

private lemma cast_negOfNat (n : ℕ) : ((Int.negOfNat n : ℤ) : ℝ) = -(n : ℝ) := by
  cases n with
  | zero => simp [Int.negOfNat]
  | succ m => simp [Int.negOfNat]

private lemma nat_div_bounds (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (a : ℝ) / (d : ℝ) - 1 < ((a / d : ℕ) : ℝ) ∧ ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
  have hd_pos : (0 : ℝ) < d := by positivity
  have hdm : d * (a / d) + a % d = a := Nat.div_add_mod a d
  have hmod : a % d < d := Nat.mod_lt a hd
  have hdmR : (d : ℝ) * ((a / d : ℕ) : ℝ) + ((a % d : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast hdm
  have hmodR : ((a % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
  have hmod0 : (0 : ℝ) ≤ ((a % d : ℕ) : ℝ) := by positivity
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_pos]; nlinarith
  · rw [le_div_iff₀ hd_pos]; nlinarith

private lemma nat_cdiv_ge (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (a : ℝ) / (d : ℝ) ≤ (((a + d - 1) / d : ℕ) : ℝ) := by
  have hd_pos : (0 : ℝ) < d := by positivity
  rw [div_le_iff₀ hd_pos]
  have h1 : a ≤ ((a + d - 1) / d) * d := by
    have hdm := Nat.div_add_mod (a + d - 1) d
    have hlt := Nat.mod_lt (a + d - 1) hd
    rw [Nat.mul_comm]
    omega
  exact_mod_cast h1

private lemma nat_cdiv_ge_sub (a d d1 : ℕ) (hd : 0 < d) (hd1 : d1 + 1 = d) :
    (a : ℝ) / (d : ℝ) ≤ (((a + d1) / d : ℕ) : ℝ) := by
  have h := nat_cdiv_ge a hd
  have heq : a + d - 1 = a + d1 := by omega
  rwa [heq] at h

private lemma intFdiv_bounds (x : Int) {d : Nat} (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) - 1 < (intFdiv x d : ℝ) ∧ (intFdiv x d : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hd_pos : (0 : ℝ) < d := by positivity
  cases x with
  | ofNat n =>
      simp only [intFdiv, Int.ofNat_eq_natCast, Int.cast_natCast]
      exact nat_div_bounds n hd
  | negSucc n =>
      simp only [intFdiv, Int.cast_negSucc]
      push_cast
      have hdm : d * (n / d) + n % d = n := Nat.div_add_mod n d
      have hmod : n % d < d := Nat.mod_lt n hd
      have hdmR : (d : ℝ) * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
      have hmodR : ((n % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
      have hmod1 : ((n % d : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hmod
      have hmod0 : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) := by positivity
      constructor
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_pos]; nlinarith
      · rw [le_div_iff₀ hd_pos]; nlinarith

private lemma intFdiv_le (x : Int) {d : Nat} (hd : 0 < d) :
    (intFdiv x d : ℝ) ≤ (x : ℝ) / (d : ℝ) := (intFdiv_bounds x hd).2

private lemma intFdiv_abs_sub_le (x : Int) {d : Nat} (hd : 0 < d) :
    |(x : ℝ) / (d : ℝ) - (intFdiv x d : ℝ)| ≤ 1 := by
  have ⟨h1, h2⟩ := intFdiv_bounds x hd
  rw [abs_le]; constructor <;> linarith

private lemma le_intCdiv (x : Int) {d : Nat} (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) ≤ (intCdiv x d : ℝ) := by
  cases x with
  | ofNat n =>
      simp only [intCdiv, Int.ofNat_eq_natCast, Int.cast_natCast]
      exact nat_cdiv_ge n hd
  | negSucc n =>
      simp only [intCdiv, Int.cast_negSucc, cast_negOfNat]
      have h2 := (nat_div_bounds (n + 1) hd).2
      rw [neg_div]
      linarith

private lemma upperIntPos_sound (aHi : Int) (bHi dDen : Nat) (hd : 0 < dDen) {S : ℝ} (hS : 0 < S) :
    uArea ((aHi : ℝ) / S) ((bHi : ℝ) / S) (1 / (dDen : ℝ)) ≤
      (upperIntPos aHi bHi dDen : ℝ) / (S * (dDen : ℝ)) := by
  have hdR : (0 : ℝ) < dDen := by positivity
  have hSd : (0 : ℝ) < S * (dDen : ℝ) := by positivity
  unfold upperIntPos uArea
  dsimp only
  generalize hhi : (2 * Int.ofNat dDen * aHi + Int.ofNat bHi) = hi2
  have hhi2R : (hi2 : ℝ) = 2 * (dDen : ℝ) * (aHi : ℝ) + (bHi : ℝ) := by
    rw [← hhi]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  have hfrac_hi : (aHi : ℝ) / S + (bHi : ℝ) / S * (1 / (dDen : ℝ) / 2) = (hi2 : ℝ) / (2 * S * (dDen : ℝ)) := by
    rw [hhi2R]; field_simp
  cases hi2 with
  | negSucc k =>
      have hle : ((Int.negSucc k : ℤ) : ℝ) ≤ 0 := by
        simp only [Int.cast_negSucc]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [if_pos (by rw [hfrac_hi]; exact div_nonpos_of_nonpos_of_nonneg hle (by positivity))]
      simp
  | ofNat h =>
      cases h with
      | zero =>
          have hle : ((Int.ofNat 0 : ℤ) : ℝ) ≤ 0 := by simp
          rw [if_pos (by rw [hfrac_hi]; exact div_nonpos_of_nonpos_of_nonneg hle (by positivity))]
          change (0 : ℝ) ≤ ((0 : Int) : ℝ) / (S * (dDen : ℝ))
          simp
      | succ h' =>
          have hm_pos : (0 : ℝ) < ((h' + 1 : ℕ) : ℝ) := by positivity
          have hhi_pos : (0 : ℝ) < ((Int.ofNat (h' + 1) : ℤ) : ℝ) := by
            simp only [Int.ofNat_eq_natCast, Int.cast_natCast]; exact hm_pos
          rw [if_neg (by rw [hfrac_hi]; exact not_le.mpr (div_pos hhi_pos (by positivity)))]
          generalize hlo : (2 * Int.ofNat dDen * aHi - Int.ofNat bHi) = lo2
          have hlo2R : (lo2 : ℝ) = 2 * (dDen : ℝ) * (aHi : ℝ) - (bHi : ℝ) := by
            rw [← hlo]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
          have hfrac_lo : (aHi : ℝ) / S - (bHi : ℝ) / S * (1 / (dDen : ℝ) / 2) = (lo2 : ℝ) / (2 * S * (dDen : ℝ)) := by
            rw [hlo2R]; field_simp
          cases lo2 with
          | ofNat l =>
              have hge : (0 : ℝ) ≤ ((Int.ofNat l : ℤ) : ℝ) := by
                simp only [Int.ofNat_eq_natCast, Int.cast_natCast]; positivity
              rw [if_pos (by rw [hfrac_lo]; exact div_nonneg hge (by positivity))]
              change (aHi : ℝ) / S * (1 / (dDen : ℝ)) ≤ (aHi : ℝ) / (S * (dDen : ℝ))
              exact le_of_eq (by ring)
          | negSucc l =>
              have hlt : ((Int.negSucc l : ℤ) : ℝ) < 0 := by
                simp only [Int.cast_negSucc]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) l]
              rw [if_neg (by rw [hfrac_lo]; exact not_le.mpr (div_neg_of_neg_of_pos hlt (by positivity)))]
              have hb_pos : 0 < bHi := by
                have : (0 : ℝ) < (bHi : ℝ) := by linarith
                exact_mod_cast this
              have hden_pos : 0 < 8 * dDen * bHi := by positivity
              have hmR : ((h' + 1 : ℕ) : ℝ) = 2 * (dDen : ℝ) * (aHi : ℝ) + (bHi : ℝ) := by
                have : ((Int.ofNat (h' + 1) : ℤ) : ℝ) = ((h' + 1 : ℕ) : ℝ) := by simp
                linarith
              have hlhs : ((aHi : ℝ) / S + (bHi : ℝ) / S * (1 / (dDen : ℝ) / 2)) ^ 2 / (2 * ((bHi : ℝ) / S)) =
                  (((h' + 1) * (h' + 1) : ℕ) : ℝ) / ((8 * dDen * bHi : ℕ) : ℝ) / (S * (dDen : ℝ)) := by
                have hbR : (0 : ℝ) < bHi := by positivity
                push_cast at hmR ⊢
                rw [hmR]
                field_simp [hS.ne', hdR.ne', hbR.ne']
                ring
              rw [hlhs]
              dsimp only
              apply div_le_div_of_nonneg_right _ hSd.le
              simp only [Int.ofNat_eq_natCast]
              exact nat_cdiv_ge ((h' + 1) * (h' + 1)) hden_pos

/- Subsection 6B: Trig Table Soundness -/

private lemma natDiff_le_iff {a b k : ℕ} (h : natDiff a b ≤ k) :
    |(a : ℝ) - (b : ℝ)| ≤ (k : ℝ) := by
  unfold natDiff at h
  by_cases hab : a ≤ b
  · rw [if_pos (Nat.ble_eq.mpr hab)] at h
    have h1 : (b : ℝ) - (a : ℝ) ≤ (k : ℝ) := by
      have : b - a ≤ k := h
      have : b ≤ a + k := by omega
      exact_mod_cast (show (b : ℤ) - (a : ℤ) ≤ (k : ℤ) by omega)
    rw [abs_le]; constructor <;> linarith [show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab]
  · rw [if_neg (by rw [Nat.ble_eq]; exact hab)] at h
    have h1 : (a : ℝ) - (b : ℝ) ≤ (k : ℝ) := by
      have : a - b ≤ k := h
      have : a ≤ b + k := by omega
      exact_mod_cast (show (a : ℤ) - (b : ℤ) ≤ (k : ℤ) by omega)
    rw [abs_le]; constructor <;> linarith [show (b : ℝ) ≤ (a : ℝ) by exact_mod_cast (Nat.le_of_not_ge hab)]

private lemma trig_table_sound :
    ∀ r : ℕ, r ≤ 256 →
      |Real.cos ((r : ℝ) * Real.pi / 1024) - (cosTab r : ℝ) / 10000000| ≤ 1 / 10000000 ∧
      |Real.sin ((r : ℝ) * Real.pi / 1024) - (sinTab r : ℝ) / 10000000| ≤ 1 / 10000000 ∧
      cosTab r ≤ 10000000 ∧ sinTab r ≤ 10000000 := by
  intro r hr
  have hchk : checkTrigOne r = true := by
    have h := trig_ok
    simp only [Bool.and_eq_true] at h
    by_cases hlt : r < 256
    · exact checkAllPow2_true 8 0 h.1 r (Nat.zero_le r) (by omega)
    · have heq : r = 256 := by omega
      subst heq; exact h.2
  set th : ℕ := (r * 3141592653) / 1024
  set s9 : ℕ := 1000000000
  set x2 : ℕ := (th * th) / s9
  set x4 : ℕ := (x2 * x2) / s9
  set x6 : ℕ := (x4 * x2) / s9
  set x8 : ℕ := (x4 * x4) / s9
  set x10 : ℕ := (x8 * x2) / s9
  set cApp : ℕ := s9 + x4 / 24 + x8 / 40320 - x2 / 2 - x6 / 720 - x10 / 3628800
  set x3 : ℕ := (x2 * th) / s9
  set x5 : ℕ := (x4 * th) / s9
  set x7 : ℕ := (x6 * th) / s9
  set x9 : ℕ := (x8 * th) / s9
  set sApp : ℕ := th + x5 / 120 + x9 / 362880 - x3 / 6 - x7 / 5040
  have hchk' : (Nat.ble (natDiff cApp (cosTab r * 100)) 55 &&
      Nat.ble (natDiff sApp (sinTab r * 100)) 55 &&
      Nat.ble (cosTab r) 10000000 && Nat.ble (sinTab r) 10000000) = true := hchk
  simp only [Bool.and_eq_true, Nat.ble_eq] at hchk'
  rcases hchk' with ⟨⟨⟨hcDiff, hsDiff⟩, hcLe⟩, hsLe⟩
  have hth_le : th ≤ 785400000 := by dsimp [th]; omega
  have hx2_le : x2 ≤ 620000000 := by
    dsimp [x2, s9]
    have : th * th ≤ 785400000 * 785400000 := Nat.mul_le_mul hth_le hth_le
    omega
  have hx4_le : x4 ≤ 390000000 := by
    dsimp [x4, s9]
    have : x2 * x2 ≤ 620000000 * 620000000 := Nat.mul_le_mul hx2_le hx2_le
    omega
  have hx6_le : x6 ≤ 250000000 := by
    dsimp [x6, s9]
    have : x4 * x2 ≤ 390000000 * 620000000 := Nat.mul_le_mul hx4_le hx2_le
    omega
  have hx8_le : x8 ≤ 160000000 := by
    dsimp [x8, s9]
    have : x4 * x4 ≤ 390000000 * 390000000 := Nat.mul_le_mul hx4_le hx4_le
    omega
  have hx10_le : x10 ≤ 100000000 := by
    dsimp [x10, s9]
    have : x8 * x2 ≤ 160000000 * 620000000 := Nat.mul_le_mul hx8_le hx2_le
    omega
  have hx3_le : x3 ≤ th := by
    dsimp [x3, s9]
    have : x2 * th ≤ 1000000000 * th := Nat.mul_le_mul_right th (by omega)
    exact Nat.div_le_of_le_mul this
  have hx7_le : x7 ≤ th := by
    dsimp [x7, s9]
    have : x6 * th ≤ 1000000000 * th := Nat.mul_le_mul_right th (by omega)
    exact Nat.div_le_of_le_mul this
  set x : ℝ := (th : ℝ) / (s9 : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx_le : x ≤ 8 / 10 := by
    have : (th : ℝ) ≤ 785400000 := by exact_mod_cast hth_le
    have hs9R : (s9 : ℝ) = 1000000000 := by norm_num [s9]
    dsimp [x]; rw [hs9R]; linarith
  have hpi_lo : (3141592653 : ℝ) / 1000000000 < Real.pi := by linarith [Real.pi_gt_d20]
  have hpi_hi : Real.pi < (3141592654 : ℝ) / 1000000000 := by linarith [Real.pi_lt_d20]
  have hth_diff : |(r : ℝ) * Real.pi / 1024 - x| ≤ 2 / (1000000000 : ℝ) := by
    have ⟨hlo, hhi⟩ := nat_div_bounds (r * 3141592653) (by norm_num : 0 < 1024)
    have hrR : (r : ℝ) ≤ 256 := by exact_mod_cast hr
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have hs9R : (s9 : ℝ) = 1000000000 := by norm_num [s9]
    dsimp [x, th]
    rw [hs9R, abs_le]
    push_cast at hlo hhi
    constructor <;> nlinarith
  have hstep_pow : ∀ (a b : ℕ) (A B : ℝ) (ea eb : ℝ),
      0 ≤ A → A ≤ 1 → 0 ≤ B → B ≤ 1 →
      0 ≤ A - (a : ℝ) / (s9 : ℝ) → A - (a : ℝ) / (s9 : ℝ) ≤ ea / (s9 : ℝ) →
      0 ≤ B - (b : ℝ) / (s9 : ℝ) → B - (b : ℝ) / (s9 : ℝ) ≤ eb / (s9 : ℝ) →
      0 ≤ A * B - (((a * b) / s9 : ℕ) : ℝ) / (s9 : ℝ) ∧
        A * B - (((a * b) / s9 : ℕ) : ℝ) / (s9 : ℝ) ≤ (ea + eb + 1) / (s9 : ℝ) := by
    intro a b A B ea eb hA0 hA1 hB0 hB1 ha0 ha1 hb0 hb1
    have hs9pos : (0 : ℝ) < s9 := by positivity
    have ⟨hd1, hd2⟩ := nat_div_bounds (a * b) (by norm_num [s9] : 0 < s9)
    have haR : (0 : ℝ) ≤ (a : ℝ) / (s9 : ℝ) := by positivity
    have hbR : (0 : ℝ) ≤ (b : ℝ) / (s9 : ℝ) := by positivity
    have haR1 : (a : ℝ) / (s9 : ℝ) ≤ 1 := by linarith
    have hbR1 : (b : ℝ) / (s9 : ℝ) ≤ 1 := by linarith
    have hprod_lo : ((a * b : ℕ) : ℝ) / (s9 : ℝ) / (s9 : ℝ) = ((a : ℝ) / (s9 : ℝ)) * ((b : ℝ) / (s9 : ℝ)) := by
      push_cast; ring
    have hd1' : ((a : ℝ) / (s9 : ℝ)) * ((b : ℝ) / (s9 : ℝ)) - 1 / (s9 : ℝ) <
        (((a * b) / s9 : ℕ) : ℝ) / (s9 : ℝ) := by
      rw [← hprod_lo, ← sub_div]
      exact (div_lt_div_iff_of_pos_right hs9pos).mpr hd1
    have hd2' : (((a * b) / s9 : ℕ) : ℝ) / (s9 : ℝ) ≤ ((a : ℝ) / (s9 : ℝ)) * ((b : ℝ) / (s9 : ℝ)) := by
      rw [← hprod_lo]; exact div_le_div_of_nonneg_right hd2 hs9pos.le
    have hdiff : A * B - ((a : ℝ) / (s9 : ℝ)) * ((b : ℝ) / (s9 : ℝ)) =
        (A - (a : ℝ) / (s9 : ℝ)) * B + ((a : ℝ) / (s9 : ℝ)) * (B - (b : ℝ) / (s9 : ℝ)) := by ring
    constructor
    · nlinarith
    · have h1 : (A - (a : ℝ) / (s9 : ℝ)) * B ≤ ea / (s9 : ℝ) := by
        have := mul_le_mul_of_nonneg_right ha1 hB0
        have : ea / (s9 : ℝ) * B ≤ ea / (s9 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hB1 (by have : 0 ≤ ea / (s9 : ℝ) := ha0.trans ha1; exact this)
        linarith
      have h2 : ((a : ℝ) / (s9 : ℝ)) * (B - (b : ℝ) / (s9 : ℝ)) ≤ eb / (s9 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hb1 haR
        have : (a : ℝ) / (s9 : ℝ) * (eb / (s9 : ℝ)) ≤ 1 * (eb / (s9 : ℝ)) :=
          mul_le_mul_of_nonneg_right haR1 (by have : 0 ≤ eb / (s9 : ℝ) := hb0.trans hb1; exact this)
        linarith
      have hadd : (ea + eb + 1) / (s9 : ℝ) = ea / (s9 : ℝ) + eb / (s9 : ℝ) + 1 / (s9 : ℝ) := by ring
      linarith
  have hx1 : x ≤ 1 := by linarith
  have hx2b : 0 ≤ x ^ 2 - (x2 : ℝ) / (s9 : ℝ) ∧ x ^ 2 - (x2 : ℝ) / (s9 : ℝ) ≤ 1 / (s9 : ℝ) := by
    simpa [pow_two, x] using hstep_pow th th x x 0 0 hx0 hx1 hx0 hx1 (by simp [x]) (by simp [x]) (by simp [x]) (by simp [x])
  have hx4b : 0 ≤ x ^ 4 - (x4 : ℝ) / (s9 : ℝ) ∧ x ^ 4 - (x4 : ℝ) / (s9 : ℝ) ≤ 3 / (s9 : ℝ) := by
    have h := hstep_pow x2 x2 (x ^ 2) (x ^ 2) 1 1 (by positivity) (pow_le_one₀ hx0 hx1) (by positivity) (pow_le_one₀ hx0 hx1) hx2b.1 hx2b.2 hx2b.1 hx2b.2
    convert h using 2 <;> ring
  have hx6b : 0 ≤ x ^ 6 - (x6 : ℝ) / (s9 : ℝ) ∧ x ^ 6 - (x6 : ℝ) / (s9 : ℝ) ≤ 5 / (s9 : ℝ) := by
    have h := hstep_pow x4 x2 (x ^ 4) (x ^ 2) 3 1 (by positivity) (pow_le_one₀ hx0 hx1) (by positivity) (pow_le_one₀ hx0 hx1) hx4b.1 hx4b.2 hx2b.1 hx2b.2
    convert h using 2 <;> ring
  have hx8b : 0 ≤ x ^ 8 - (x8 : ℝ) / (s9 : ℝ) ∧ x ^ 8 - (x8 : ℝ) / (s9 : ℝ) ≤ 7 / (s9 : ℝ) := by
    have h := hstep_pow x4 x4 (x ^ 4) (x ^ 4) 3 3 (by positivity) (pow_le_one₀ hx0 hx1) (by positivity) (pow_le_one₀ hx0 hx1) hx4b.1 hx4b.2 hx4b.1 hx4b.2
    convert h using 2 <;> ring
  have hx10b : 0 ≤ x ^ 10 - (x10 : ℝ) / (s9 : ℝ) ∧ x ^ 10 - (x10 : ℝ) / (s9 : ℝ) ≤ 9 / (s9 : ℝ) := by
    have h := hstep_pow x8 x2 (x ^ 8) (x ^ 2) 7 1 (by positivity) (pow_le_one₀ hx0 hx1) (by positivity) (pow_le_one₀ hx0 hx1) hx8b.1 hx8b.2 hx2b.1 hx2b.2
    convert h using 2 <;> ring
  have hx3b : 0 ≤ x ^ 3 - (x3 : ℝ) / (s9 : ℝ) ∧ x ^ 3 - (x3 : ℝ) / (s9 : ℝ) ≤ 2 / (s9 : ℝ) := by
    have h := hstep_pow x2 th (x ^ 2) x 1 0 (by positivity) (pow_le_one₀ hx0 hx1) hx0 hx1 hx2b.1 hx2b.2 (by simp [x]) (by simp [x])
    convert h using 2 <;> ring
  have hx5b : 0 ≤ x ^ 5 - (x5 : ℝ) / (s9 : ℝ) ∧ x ^ 5 - (x5 : ℝ) / (s9 : ℝ) ≤ 4 / (s9 : ℝ) := by
    have h := hstep_pow x4 th (x ^ 4) x 3 0 (by positivity) (pow_le_one₀ hx0 hx1) hx0 hx1 hx4b.1 hx4b.2 (by simp [x]) (by simp [x])
    convert h using 2 <;> ring
  have hx7b : 0 ≤ x ^ 7 - (x7 : ℝ) / (s9 : ℝ) ∧ x ^ 7 - (x7 : ℝ) / (s9 : ℝ) ≤ 6 / (s9 : ℝ) := by
    have h := hstep_pow x6 th (x ^ 6) x 5 0 (by positivity) (pow_le_one₀ hx0 hx1) hx0 hx1 hx6b.1 hx6b.2 (by simp [x]) (by simp [x])
    convert h using 2 <;> ring
  have hx9b : 0 ≤ x ^ 9 - (x9 : ℝ) / (s9 : ℝ) ∧ x ^ 9 - (x9 : ℝ) / (s9 : ℝ) ≤ 8 / (s9 : ℝ) := by
    have h := hstep_pow x8 th (x ^ 8) x 7 0 (by positivity) (pow_le_one₀ hx0 hx1) hx0 hx1 hx8b.1 hx8b.2 (by simp [x]) (by simp [x])
    convert h using 2 <;> ring
  have hcAppR : (cApp : ℝ) = (s9 : ℝ) + ((x4 / 24 : ℕ) : ℝ) + ((x8 / 40320 : ℕ) : ℝ) -
      ((x2 / 2 : ℕ) : ℝ) - ((x6 / 720 : ℕ) : ℝ) - ((x10 / 3628800 : ℕ) : ℝ) := by
    have ha : x2 / 2 ≤ 310000000 := Nat.div_le_of_le_mul (by omega)
    have hb : x6 / 720 ≤ 350000 := Nat.div_le_of_le_mul (by omega)
    have hc : x10 / 3628800 ≤ 100 := Nat.div_le_of_le_mul (by omega)
    have hle1 : x2 / 2 + x6 / 720 + x10 / 3628800 ≤ s9 := by
      have : s9 = 1000000000 := rfl; omega
    have hsub1 : x2 / 2 + x6 / 720 + x10 / 3628800 ≤ s9 + x4 / 24 + x8 / 40320 :=
      hle1.trans (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))
    have hcast : cApp + (x2 / 2 + x6 / 720 + x10 / 3628800) = s9 + x4 / 24 + x8 / 40320 := by
      have hcdef : cApp = s9 + x4 / 24 + x8 / 40320 - x2 / 2 - x6 / 720 - x10 / 3628800 := rfl
      rw [hcdef]; omega
    have hcastR : ((cApp + (x2 / 2 + x6 / 720 + x10 / 3628800) : ℕ) : ℝ) =
        ((s9 + x4 / 24 + x8 / 40320 : ℕ) : ℝ) := by exact_mod_cast hcast
    push_cast at hcastR; linarith
  have hsAppR : (sApp : ℝ) = (th : ℝ) + ((x5 / 120 : ℕ) : ℝ) + ((x9 / 362880 : ℕ) : ℝ) -
      ((x3 / 6 : ℕ) : ℝ) - ((x7 / 5040 : ℕ) : ℝ) := by
    have ha : x3 / 6 ≤ th / 6 := Nat.div_le_div_right hx3_le
    have hb : x7 / 5040 ≤ th / 5040 := Nat.div_le_div_right hx7_le
    have hle1 : x3 / 6 + x7 / 5040 ≤ th := by omega
    have hsub1 : x3 / 6 + x7 / 5040 ≤ th + x5 / 120 + x9 / 362880 :=
      hle1.trans (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))
    have hcast : sApp + (x3 / 6 + x7 / 5040) = th + x5 / 120 + x9 / 362880 := by
      have hsdef : sApp = th + x5 / 120 + x9 / 362880 - x3 / 6 - x7 / 5040 := rfl
      rw [hsdef]; omega
    have hcastR : ((sApp + (x3 / 6 + x7 / 5040) : ℕ) : ℝ) =
        ((th + x5 / 120 + x9 / 362880 : ℕ) : ℝ) := by exact_mod_cast hcast
    push_cast at hcastR; linarith
  have hs9R : (s9 : ℝ) = 1000000000 := by norm_num [s9]
  have hcos_approx : |Real.cos x - (cApp : ℝ) / (s9 : ℝ)| ≤ 37 / (1000000000 : ℝ) := by
    have ht8 := cos_le_t8 hx0
    have ht10 := cos_ge_t10 hx0
    have hx10_hi : x ^ 10 ≤ (8 / 10 : ℝ) ^ 10 := pow_le_pow_left₀ hx0 hx_le 10
    have hd2 := nat_div_bounds x2 (by norm_num : 0 < 2)
    have hd4 := nat_div_bounds x4 (by norm_num : 0 < 24)
    have hd6 := nat_div_bounds x6 (by norm_num : 0 < 720)
    have hd8 := nat_div_bounds x8 (by norm_num : 0 < 40320)
    have hd10 := nat_div_bounds x10 (by norm_num : 0 < 3628800)
    rw [hcAppR, hs9R]
    rw [hs9R] at hx2b hx4b hx6b hx8b hx10b
    norm_num at hx10_hi hd2 hd4 hd6 hd8 hd10
    rw [abs_le]
    constructor <;> linarith only [ht8, ht10, hx10_hi, hd2.1, hd2.2, hd4.1, hd4.2,
      hd6.1, hd6.2, hd8.1, hd8.2, hd10.1, hd10.2, hx2b.1, hx2b.2, hx4b.1, hx4b.2,
      hx6b.1, hx6b.2, hx8b.1, hx8b.2, hx10b.1, hx10b.2]
  have hsin_approx : |Real.sin x - (sApp : ℝ) / (s9 : ℝ)| ≤ 8 / (1000000000 : ℝ) := by
    have ht9 := sin_le_t9 hx0
    have ht11 := sin_ge_t11 hx0
    have hx11_hi : x ^ 11 ≤ (8 / 10 : ℝ) ^ 11 := pow_le_pow_left₀ hx0 hx_le 11
    have hd3 := nat_div_bounds x3 (by norm_num : 0 < 6)
    have hd5 := nat_div_bounds x5 (by norm_num : 0 < 120)
    have hd7 := nat_div_bounds x7 (by norm_num : 0 < 5040)
    have hd9 := nat_div_bounds x9 (by norm_num : 0 < 362880)
    have hx_eq : x = (th : ℝ) / 1000000000 := by dsimp [x]; rw [hs9R]
    rw [hsAppR, hs9R]
    rw [hs9R] at hx3b hx5b hx7b hx9b
    norm_num at hx11_hi hd3 hd5 hd7 hd9
    rw [abs_le]
    constructor <;> linarith only [ht9, ht11, hx11_hi, hd3.1, hd3.2, hd5.1, hd5.2,
      hd7.1, hd7.2, hd9.1, hd9.2, hx3b.1, hx3b.2, hx5b.1, hx5b.2, hx7b.1, hx7b.2,
      hx9b.1, hx9b.2, hx_eq]
  have hcDiffR : |(cApp : ℝ) - (cosTab r : ℝ) * 100| ≤ 55 := by
    have h := natDiff_le_iff hcDiff
    push_cast at h; exact h
  have hsDiffR : |(sApp : ℝ) - (sinTab r : ℝ) * 100| ≤ 55 := by
    have h := natDiff_le_iff hsDiff
    push_cast at h; exact h
  have hcos_shift : |Real.cos ((r : ℝ) * Real.pi / 1024) - Real.cos x| ≤ 2 / (1000000000 : ℝ) :=
    (abs_cos_sub_cos_le_self _ _).trans hth_diff
  have hsin_shift : |Real.sin ((r : ℝ) * Real.pi / 1024) - Real.sin x| ≤ 2 / (1000000000 : ℝ) :=
    (abs_sin_sub_sin_le_self _ _).trans hth_diff
  refine ⟨?_, ?_, hcLe, hsLe⟩
  · have h1 : |(cApp : ℝ) / (1000000000 : ℝ) - (cosTab r : ℝ) / 10000000| ≤ 55 / (1000000000 : ℝ) := by
      have : (cApp : ℝ) / (1000000000 : ℝ) - (cosTab r : ℝ) / 10000000 =
          ((cApp : ℝ) - (cosTab r : ℝ) * 100) / 1000000000 := by ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000000000)]
      exact div_le_div_of_nonneg_right hcDiffR (by norm_num)
    rw [hs9R] at hcos_approx
    calc |Real.cos ((r : ℝ) * Real.pi / 1024) - (cosTab r : ℝ) / 10000000|
        ≤ |Real.cos ((r : ℝ) * Real.pi / 1024) - Real.cos x| +
          |Real.cos x - (cosTab r : ℝ) / 10000000| := abs_sub_le _ _ _
      _ ≤ |Real.cos ((r : ℝ) * Real.pi / 1024) - Real.cos x| +
          (|Real.cos x - (cApp : ℝ) / 1000000000| +
            |(cApp : ℝ) / 1000000000 - (cosTab r : ℝ) / 10000000|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
      _ ≤ 2 / 1000000000 + (37 / 1000000000 + 55 / 1000000000) :=
          add_le_add hcos_shift (add_le_add hcos_approx h1)
      _ ≤ 1 / 10000000 := by norm_num
  · have h1 : |(sApp : ℝ) / (1000000000 : ℝ) - (sinTab r : ℝ) / 10000000| ≤ 55 / (1000000000 : ℝ) := by
      have : (sApp : ℝ) / (1000000000 : ℝ) - (sinTab r : ℝ) / 10000000 =
          ((sApp : ℝ) - (sinTab r : ℝ) * 100) / 1000000000 := by ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000000000)]
      exact div_le_div_of_nonneg_right hsDiffR (by norm_num)
    rw [hs9R] at hsin_approx
    calc |Real.sin ((r : ℝ) * Real.pi / 1024) - (sinTab r : ℝ) / 10000000|
        ≤ |Real.sin ((r : ℝ) * Real.pi / 1024) - Real.sin x| +
          |Real.sin x - (sinTab r : ℝ) / 10000000| := abs_sub_le _ _ _
      _ ≤ |Real.sin ((r : ℝ) * Real.pi / 1024) - Real.sin x| +
          (|Real.sin x - (sApp : ℝ) / 1000000000| +
            |(sApp : ℝ) / 1000000000 - (sinTab r : ℝ) / 10000000|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
      _ ≤ 2 / 1000000000 + (8 / 1000000000 + 55 / 1000000000) :=
          add_le_add hsin_shift (add_le_add hsin_approx h1)
      _ ≤ 1 / 10000000 := by norm_num

private lemma cosQNat_sound (r : ℕ) :
    |Real.cos ((r : ℝ) * Real.pi / 1024) - (cosQNat r : ℝ) / 10000000| ≤ 1 / 10000000 ∧
    |(cosQNat r : ℝ) / 10000000| ≤ 1 := by
  set m : ℕ := r % 2048
  have hm_lt : m < 2048 := Nat.mod_lt r (by norm_num)
  have hcos_mod : Real.cos ((r : ℝ) * Real.pi / 1024) = Real.cos ((m : ℝ) * Real.pi / 1024) := by
    have hdm : 2048 * (r / 2048) + m = r := Nat.div_add_mod r 2048
    have harg : (r : ℝ) * Real.pi / 1024 = (m : ℝ) * Real.pi / 1024 + ((r / 2048 : ℕ) : ℝ) * (2 * Real.pi) := by
      have hdmR : (2048 : ℝ) * ((r / 2048 : ℕ) : ℝ) + (m : ℝ) = (r : ℝ) := by exact_mod_cast hdm
      rw [← hdmR]; ring
    rw [harg, Real.cos_add_nat_mul_two_pi]
  rw [hcos_mod]
  unfold cosQNat
  dsimp only
  have hm_def : r % 2048 = m := rfl
  rw [hm_def]
  have hpos_div : ∀ k : ℕ, k ≤ 10000000 → |((Int.ofNat k : ℤ) : ℝ) / 10000000| ≤ 1 := by
    intro k hk
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, abs_div,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), abs_of_pos (by norm_num : (0 : ℝ) < 10000000)]
    rw [div_le_one (by norm_num)]; exact_mod_cast hk
  have hneg_div : ∀ k : ℕ, k ≤ 10000000 → |((Int.negOfNat k : ℤ) : ℝ) / 10000000| ≤ 1 := by
    intro k hk
    rw [cast_negOfNat, neg_div, abs_neg, abs_div,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), abs_of_pos (by norm_num : (0 : ℝ) < 10000000)]
    rw [div_le_one (by norm_num)]; exact_mod_cast hk
  by_cases h1 : m ≤ 256
  · rw [if_pos (Nat.ble_eq.mpr h1)]
    have ⟨hc, _, hcle, _⟩ := trig_table_sound m h1
    exact ⟨by simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hc, hpos_div _ hcle⟩
  rw [if_neg (by rw [Nat.ble_eq]; exact h1)]
  by_cases h2 : m ≤ 512
  · rw [if_pos (Nat.ble_eq.mpr h2)]
    have ⟨_, hs, _, hsle⟩ := trig_table_sound (512 - m) (by omega)
    have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = Real.sin (((512 - m : ℕ) : ℝ) * Real.pi / 1024) := by
      have hcast : ((512 - m : ℕ) : ℝ) = 512 - (m : ℝ) := by rw [Nat.cast_sub h2]; norm_num
      rw [hcast, show (512 - (m : ℝ)) * Real.pi / 1024 = Real.pi / 2 - (m : ℝ) * Real.pi / 1024 by ring, Real.sin_pi_div_two_sub]
    rw [harg]
    exact ⟨by simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hs, hpos_div _ hsle⟩
  rw [if_neg (by rw [Nat.ble_eq]; exact h2)]
  by_cases h3 : m ≤ 768
  · rw [if_pos (Nat.ble_eq.mpr h3)]
    have h512 : 512 ≤ m := by omega
    have ⟨_, hs, _, hsle⟩ := trig_table_sound (m - 512) (by omega)
    have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = -Real.sin (((m - 512 : ℕ) : ℝ) * Real.pi / 1024) := by
      have hcast : ((m - 512 : ℕ) : ℝ) = (m : ℝ) - 512 := by rw [Nat.cast_sub h512]; norm_num
      rw [hcast, show (m : ℝ) * Real.pi / 1024 = ((m : ℝ) - 512) * Real.pi / 1024 + Real.pi / 2 by ring, Real.cos_add_pi_div_two]
    rw [harg]
    refine ⟨?_, hneg_div _ hsle⟩
    rw [cast_negOfNat, neg_div, sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm]; exact hs
  rw [if_neg (by rw [Nat.ble_eq]; exact h3)]
  by_cases h4 : m ≤ 1024
  · rw [if_pos (Nat.ble_eq.mpr h4)]
    have ⟨hc, _, hcle, _⟩ := trig_table_sound (1024 - m) (by omega)
    have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = -Real.cos (((1024 - m : ℕ) : ℝ) * Real.pi / 1024) := by
      have hcast : ((1024 - m : ℕ) : ℝ) = 1024 - (m : ℝ) := by rw [Nat.cast_sub h4]; norm_num
      rw [hcast, show (1024 - (m : ℝ)) * Real.pi / 1024 = Real.pi - (m : ℝ) * Real.pi / 1024 by ring, Real.cos_pi_sub, neg_neg]
    rw [harg]
    refine ⟨?_, hneg_div _ hcle⟩
    rw [cast_negOfNat, neg_div, sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm]; exact hc
  rw [if_neg (by rw [Nat.ble_eq]; exact h4)]
  by_cases h5 : m ≤ 1280
  · rw [if_pos (Nat.ble_eq.mpr h5)]
    have h1024 : 1024 ≤ m := by omega
    have ⟨hc, _, hcle, _⟩ := trig_table_sound (m - 1024) (by omega)
    have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = -Real.cos (((m - 1024 : ℕ) : ℝ) * Real.pi / 1024) := by
      have hcast : ((m - 1024 : ℕ) : ℝ) = (m : ℝ) - 1024 := by rw [Nat.cast_sub h1024]; norm_num
      rw [hcast, show (m : ℝ) * Real.pi / 1024 = ((m : ℝ) - 1024) * Real.pi / 1024 + Real.pi by ring, Real.cos_add_pi]
    rw [harg]
    refine ⟨?_, hneg_div _ hcle⟩
    rw [cast_negOfNat, neg_div, sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm]; exact hc
  rw [if_neg (by rw [Nat.ble_eq]; exact h5)]
  by_cases h6 : m ≤ 1536
  · rw [if_pos (Nat.ble_eq.mpr h6)]
    have ⟨_, hs, _, hsle⟩ := trig_table_sound (1536 - m) (by omega)
    have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = -Real.sin (((1536 - m : ℕ) : ℝ) * Real.pi / 1024) := by
      have hcast : ((1536 - m : ℕ) : ℝ) = 1536 - (m : ℝ) := by rw [Nat.cast_sub h6]; norm_num
      rw [hcast, show (m : ℝ) * Real.pi / 1024 = (Real.pi / 2 - (1536 - (m : ℝ)) * Real.pi / 1024) + Real.pi by ring,
        Real.cos_add_pi, Real.cos_pi_div_two_sub]
    rw [harg]
    refine ⟨?_, hneg_div _ hsle⟩
    rw [cast_negOfNat, neg_div, sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm]; exact hs
  rw [if_neg (by rw [Nat.ble_eq]; exact h6)]
  by_cases h7 : m ≤ 1792
  · rw [if_pos (Nat.ble_eq.mpr h7)]
    have h1536 : 1536 ≤ m := by omega
    have ⟨_, hs, _, hsle⟩ := trig_table_sound (m - 1536) (by omega)
    have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = Real.sin (((m - 1536 : ℕ) : ℝ) * Real.pi / 1024) := by
      have hcast : ((m - 1536 : ℕ) : ℝ) = (m : ℝ) - 1536 := by rw [Nat.cast_sub h1536]; norm_num
      rw [hcast, show (m : ℝ) * Real.pi / 1024 = (((m : ℝ) - 1536) * Real.pi / 1024 - Real.pi / 2) + 2 * Real.pi by ring,
        Real.cos_add_two_pi, Real.cos_sub_pi_div_two]
    rw [harg]
    exact ⟨by simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hs, hpos_div _ hsle⟩
  rw [if_neg (by rw [Nat.ble_eq]; exact h7)]
  have ⟨hc, _, hcle, _⟩ := trig_table_sound (2048 - m) (by omega)
  have harg : Real.cos ((m : ℝ) * Real.pi / 1024) = Real.cos (((2048 - m : ℕ) : ℝ) * Real.pi / 1024) := by
    have hcast : ((2048 - m : ℕ) : ℝ) = 2048 - (m : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast, show (2048 - (m : ℝ)) * Real.pi / 1024 = 2 * Real.pi - (m : ℝ) * Real.pi / 1024 by ring, Real.cos_two_pi_sub]
  rw [harg]
  exact ⟨by simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hc, hpos_div _ hcle⟩

private lemma sinQNat_sound (r : ℕ) :
    |Real.sin ((r : ℝ) * Real.pi / 1024) - (sinQNat r : ℝ) / 10000000| ≤ 1 / 10000000 ∧
    |(sinQNat r : ℝ) / 10000000| ≤ 1 := by
  unfold sinQNat
  have harg : Real.sin ((r : ℝ) * Real.pi / 1024) = Real.cos (((r + 1536 : ℕ) : ℝ) * Real.pi / 1024) := by
    push_cast
    rw [show ((r : ℝ) + 1536) * Real.pi / 1024 = ((r : ℝ) * Real.pi / 1024 - Real.pi / 2) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_sub_pi_div_two]
  rw [harg]
  exact cosQNat_sound (r + 1536)

/- Subsection 6C: Frequency and Continuous Sinc Table Soundness -/

noncomputable def omReal (m : ℕ) : ℝ := (m : ℝ) * Real.pi / 2

noncomputable def dCont (m : ℕ) : ℝ :=
  if m = 0 then 0 else 2 * Real.sin (omReal m) / omReal m

private lemma omReal_pos {m : ℕ} (hm : 1 ≤ m) : 0 < omReal m := by
  unfold omReal
  have : (0 : ℝ) < m := by positivity
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

private lemma omIntList_sound (i : Fin 10) :
    (omIntList.getD i.1 0 : ℝ) - 1 ≤ omReal (i.1 + 1) * 10000000 ∧
    omReal (i.1 + 1) * 10000000 ≤ (omIntList.getD i.1 0 : ℝ) + 1 := by
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  fin_cases i <;>
    (simp only [omIntList, omReal, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.cast_ofNat]; norm_num; constructor <;> linarith)

private lemma omSqHiList_sound (i : Fin 10) :
    (omReal (i.1 + 1)) ^ 2 ≤ (omSqHiList.getD i.1 0 : ℝ) / 10000000 := by
  have ⟨_, hhi⟩ := omIntList_sound i
  have hpos : 0 ≤ omReal (i.1 + 1) := (omReal_pos (Nat.succ_pos i.1)).le
  fin_cases i <;>
    (simp only [omSqHiList, omIntList, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Nat.cast_ofNat] at hhi ⊢; nlinarith)

private lemma sin_omReal_odd (k : ℕ) :
    Real.sin (omReal (2 * k + 1)) = (-1 : ℝ) ^ k := by
  unfold omReal
  rw [show ((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2 = Real.pi / 2 + (k : ℝ) * Real.pi by push_cast; ring,
    Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  ring

private lemma sin_omReal_even (k : ℕ) :
    Real.sin (omReal (2 * k)) = 0 := by
  unfold omReal
  rw [show ((2 * k : ℕ) : ℝ) * Real.pi / 2 = (k : ℝ) * Real.pi by push_cast; ring, Real.sin_nat_mul_pi]

private lemma dCont_even (k : ℕ) : dCont (2 * k) = 0 := by
  unfold dCont
  split_ifs with h
  · rfl
  · rw [sin_omReal_even, mul_zero, zero_div]

private lemma dCont_odd (k : ℕ) : dCont (2 * k + 1) = (-1 : ℝ) ^ k * 4 / ((2 * k + 1 : ℕ) * Real.pi) := by
  unfold dCont
  rw [if_neg (Nat.succ_ne_zero _), sin_omReal_odd, omReal]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hk : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hpi, hk]
  ring

private lemma dIntList_sound (i : Fin 10) :
    |dCont (i.1 + 1) * 10000000 - (dIntList.getD i.1 0 : ℝ)| ≤
      if (i.1 + 1) % 2 = 0 then 0 else 1 := by
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  fin_cases i
  · -- m = 1
    have hd := dCont_odd 0
    simp only [dIntList, List.getD, List.getElem?_cons_zero, Option.getD_some] at hd ⊢
    norm_num at hd ⊢; rw [hd, abs_le]
    have h1 : (4 : ℝ) / Real.pi * 10000000 = 40000000 / Real.pi := by ring
    rw [h1]; constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hpi]; linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hpi]; linarith
  · -- m = 2
    have hd := dCont_even 1
    simp [dIntList, hd]
  · -- m = 3
    have hd := dCont_odd 1
    simp only [dIntList, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hd ⊢
    norm_num at hd ⊢; rw [hd, abs_le]
    have h1 : -(4 : ℝ) / (3 * Real.pi) * 10000000 = -(40000000 / (3 * Real.pi)) := by ring
    rw [h1]; constructor
    · have : 40000000 / (3 * Real.pi) ≤ 4244133 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · have : 4244131 ≤ 40000000 / (3 * Real.pi) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
  · -- m = 4
    have hd := dCont_even 2
    simp [dIntList, hd]
  · -- m = 5
    have hd := dCont_odd 2
    simp only [dIntList, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hd ⊢
    norm_num at hd ⊢; rw [hd, abs_le]
    have h1 : (4 : ℝ) / (5 * Real.pi) * 10000000 = 8000000 / Real.pi := by ring
    rw [h1]; constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hpi]; linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hpi]; linarith
  · -- m = 6
    have hd := dCont_even 3
    simp [dIntList, hd]
  · -- m = 7
    have hd := dCont_odd 3
    simp only [dIntList, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hd ⊢
    norm_num at hd ⊢; rw [hd, abs_le]
    have h1 : -(4 : ℝ) / (7 * Real.pi) * 10000000 = -(40000000 / (7 * Real.pi)) := by ring
    rw [h1]; constructor
    · have : 40000000 / (7 * Real.pi) ≤ 1818915 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · have : 1818913 ≤ 40000000 / (7 * Real.pi) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
  · -- m = 8
    have hd := dCont_even 4
    simp [dIntList, hd]
  · -- m = 9
    have hd := dCont_odd 4
    simp only [dIntList, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hd ⊢
    norm_num at hd ⊢; rw [hd, abs_le]
    have h1 : (4 : ℝ) / (9 * Real.pi) * 10000000 = 40000000 / (9 * Real.pi) := by ring
    rw [h1]; constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]; linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; linarith
  · -- m = 10
    have hd := dCont_even 5
    simp [dIntList, hd]

/- Subsection 6D: Real Dual Functions Phi and NegPsi and TermList Soundness -/

def SC_R : ℝ := 1000000
def ST_R : ℝ := 10000000
def SVAL_R : ℝ := 10000000000000

noncomputable def alphaR (c : Cert) (i : Fin 10) : ℝ := (c.alpha.getD i.1 0 : ℝ) / SC_R
noncomputable def betaR (c : Cert) (i : Fin 10) : ℝ := (c.beta.getD i.1 0 : ℝ) / SC_R
noncomputable def uR (c : Cert) (i : Fin 10) : ℝ := (c.u.getD i.1 0 : ℝ) / SC_R
noncomputable def vR (c : Cert) (i : Fin 10) : ℝ := (c.v.getD i.1 0 : ℝ) / SC_R

noncomputable def cCosMR (c : Cert) (i : Fin 10) : ℝ :=
  if i.1 = 1 then -alphaR c i + (c.gamma : ℝ) / SC_R else -alphaR c i

noncomputable def cSinMR (c : Cert) (i : Fin 10) : ℝ := -betaR c i

noncomputable def cCosFR (c : Cert) (i : Fin 10) : ℝ :=
  2 * alphaR c i * uR c i - alphaR c i * dCont (i.1 + 1) +
    if i.1 = 1 then -((c.gamma : ℝ) / SC_R) * (((c.p1 + c.p2 : ℤ) : ℝ) / 100) -
      (c.nuPlo : ℝ) / SC_R + (c.nuPhi : ℝ) / SC_R else 0

noncomputable def cSinFR (c : Cert) (i : Fin 10) : ℝ :=
  2 * alphaR c i * vR c i - betaR c i * dCont (i.1 + 1) +
    if i.1 = 1 then -((c.gamma : ℝ) / SC_R) * (((c.q1 + c.q2 : ℤ) : ℝ) / 100) -
      (c.nuQlo : ℝ) / SC_R + (c.nuQhi : ℝ) / SC_R else 0

def linFInt (c : Cert) : Int :=
  -2 * c.nuEM * 10000000 - c.nuMhi * (c.h1 + c.h2) * 100000 + 2 * c.nuMlo * c.e0 * 10
    - 2 * c.nuElo * 10000000 + 2 * c.nuEhi * 10000000

noncomputable def Phi (c : Cert) (x : ℝ) : ℝ :=
  -((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * x -
    (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * x ^ 2 +
    ∑ i : Fin 10, (cCosMR c i * Real.cos (omReal (i.1 + 1) * x) +
      cSinMR c i * Real.sin (omReal (i.1 + 1) * x))

noncomputable def Phi' (c : Cert) (x : ℝ) : ℝ :=
  -((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * x +
    ∑ i : Fin 10, ((-cCosMR c i * Real.sin (omReal (i.1 + 1) * x) +
      cSinMR c i * Real.cos (omReal (i.1 + 1) * x)) * omReal (i.1 + 1))

noncomputable def Phi'' (c : Cert) (x : ℝ) : ℝ :=
  -2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) +
    ∑ i : Fin 10, (-(cCosMR c i * Real.cos (omReal (i.1 + 1) * x) +
      cSinMR c i * Real.sin (omReal (i.1 + 1) * x)) * (omReal (i.1 + 1)) ^ 2)

noncomputable def NegPsi (c : Cert) (t : ℝ) : ℝ :=
  -((c.nuMassf : ℝ) / SC_R) - ((linFInt c : ℝ) / SVAL_R) * t -
    ∑ i : Fin 10, (cCosFR c i * Real.cos (omReal (i.1 + 1) * t) +
      cSinFR c i * Real.sin (omReal (i.1 + 1) * t))

noncomputable def NegPsi' (c : Cert) (t : ℝ) : ℝ :=
  -((linFInt c : ℝ) / SVAL_R) +
    ∑ i : Fin 10, ((cCosFR c i * Real.sin (omReal (i.1 + 1) * t) -
      cSinFR c i * Real.cos (omReal (i.1 + 1) * t)) * omReal (i.1 + 1))

noncomputable def NegPsi'' (c : Cert) (t : ℝ) : ℝ :=
  ∑ i : Fin 10, ((cCosFR c i * Real.cos (omReal (i.1 + 1) * t) +
    cSinFR c i * Real.sin (omReal (i.1 + 1) * t)) * (omReal (i.1 + 1)) ^ 2)

private lemma hasDerivAt_trig_pair (a b ω x : ℝ) :
    HasDerivAt (fun s => a * Real.cos (ω * s) + b * Real.sin (ω * s))
      ((-a * Real.sin (ω * x) + b * Real.cos (ω * x)) * ω) x := by
  have h1 : HasDerivAt (fun s => ω * s) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  have hc := (Real.hasDerivAt_cos (ω * x)).comp x h1
  have hs := (Real.hasDerivAt_sin (ω * x)).comp x h1
  exact ((hc.const_mul a).add (hs.const_mul b)).congr_deriv (by ring)

private lemma hasDerivAt_Phi (c : Cert) (x : ℝ) : HasDerivAt (Phi c) (Phi' c x) x := by
  unfold Phi Phi'
  have hpoly : HasDerivAt
      (fun s => -((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * s -
        (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * s ^ 2)
      (-((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * x) x := by
    have h1 := hasDerivAt_const x (-((c.nuMassM : ℝ) / SC_R))
    have h2 := (hasDerivAt_id x).const_mul ((c.nuEM : ℝ) / SC_R)
    have h3 := (hasDerivAt_pow 2 x).const_mul (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R)
    exact ((h1.sub h2).sub h3).congr_deriv (by norm_num; ring)
  have hsum : HasDerivAt
      (fun s => ∑ i : Fin 10, (cCosMR c i * Real.cos (omReal (i.1 + 1) * s) +
        cSinMR c i * Real.sin (omReal (i.1 + 1) * s)))
      (∑ i : Fin 10, ((-cCosMR c i * Real.sin (omReal (i.1 + 1) * x) +
        cSinMR c i * Real.cos (omReal (i.1 + 1) * x)) * omReal (i.1 + 1))) x := by
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_trig_pair (cCosMR c i) (cSinMR c i) (omReal (i.1 + 1)) x
  exact hpoly.add hsum

private lemma hasDerivAt_Phi' (c : Cert) (x : ℝ) : HasDerivAt (Phi' c) (Phi'' c x) x := by
  unfold Phi' Phi''
  have hpoly : HasDerivAt
      (fun s => -((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * s)
      (-2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R)) x := by
    have h1 := hasDerivAt_const x (-((c.nuEM : ℝ) / SC_R))
    have h2 := (hasDerivAt_id x).const_mul (2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R))
    exact (h1.sub h2).congr_deriv (by ring)
  have hsum : HasDerivAt
      (fun s => ∑ i : Fin 10, ((-cCosMR c i * Real.sin (omReal (i.1 + 1) * s) +
        cSinMR c i * Real.cos (omReal (i.1 + 1) * s)) * omReal (i.1 + 1)))
      (∑ i : Fin 10, (-(cCosMR c i * Real.cos (omReal (i.1 + 1) * x) +
        cSinMR c i * Real.sin (omReal (i.1 + 1) * x)) * (omReal (i.1 + 1)) ^ 2)) x := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h := (hasDerivAt_trig_pair (cSinMR c i) (-cCosMR c i) (omReal (i.1 + 1)) x).mul_const (omReal (i.1 + 1))
    have heq : (fun s => (cSinMR c i * Real.cos (omReal (i.1 + 1) * s) +
        -cCosMR c i * Real.sin (omReal (i.1 + 1) * s)) * omReal (i.1 + 1)) =
        (fun s => (-cCosMR c i * Real.sin (omReal (i.1 + 1) * s) +
        cSinMR c i * Real.cos (omReal (i.1 + 1) * s)) * omReal (i.1 + 1)) := by
      funext s; ring
    rw [heq] at h
    exact h.congr_deriv (by ring)
  exact hpoly.add hsum

private lemma hasDerivAt_NegPsi (c : Cert) (t : ℝ) : HasDerivAt (NegPsi c) (NegPsi' c t) t := by
  unfold NegPsi NegPsi'
  have hpoly : HasDerivAt
      (fun s => -((c.nuMassf : ℝ) / SC_R) - ((linFInt c : ℝ) / SVAL_R) * s)
      (-((linFInt c : ℝ) / SVAL_R)) t := by
    have h1 := hasDerivAt_const t (-((c.nuMassf : ℝ) / SC_R))
    have h2 := (hasDerivAt_id t).const_mul ((linFInt c : ℝ) / SVAL_R)
    exact (h1.sub h2).congr_deriv (by ring)
  have hsum : HasDerivAt
      (fun s => ∑ i : Fin 10, (cCosFR c i * Real.cos (omReal (i.1 + 1) * s) +
        cSinFR c i * Real.sin (omReal (i.1 + 1) * s)))
      (∑ i : Fin 10, ((-cCosFR c i * Real.sin (omReal (i.1 + 1) * t) +
        cSinFR c i * Real.cos (omReal (i.1 + 1) * t)) * omReal (i.1 + 1))) t :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_trig_pair (cCosFR c i) (cSinFR c i) (omReal (i.1 + 1)) t
  refine (hpoly.sub hsum).congr_deriv ?_
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1; refine Finset.sum_congr rfl fun i _ => by ring

private lemma hasDerivAt_NegPsi' (c : Cert) (t : ℝ) : HasDerivAt (NegPsi' c) (NegPsi'' c t) t := by
  unfold NegPsi' NegPsi''
  have hpoly := hasDerivAt_const t (-((linFInt c : ℝ) / SVAL_R))
  have hsum : HasDerivAt
      (fun s => ∑ i : Fin 10, ((cCosFR c i * Real.sin (omReal (i.1 + 1) * s) -
        cSinFR c i * Real.cos (omReal (i.1 + 1) * s)) * omReal (i.1 + 1)))
      (∑ i : Fin 10, ((cCosFR c i * Real.cos (omReal (i.1 + 1) * t) +
        cSinFR c i * Real.sin (omReal (i.1 + 1) * t)) * (omReal (i.1 + 1)) ^ 2)) t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h := (hasDerivAt_trig_pair (-cSinFR c i) (cCosFR c i) (omReal (i.1 + 1)) t).mul_const (omReal (i.1 + 1))
    have heq : (fun s => (-cSinFR c i * Real.cos (omReal (i.1 + 1) * s) +
        cCosFR c i * Real.sin (omReal (i.1 + 1) * s)) * omReal (i.1 + 1)) =
        (fun s => (cCosFR c i * Real.sin (omReal (i.1 + 1) * s) -
        cSinFR c i * Real.cos (omReal (i.1 + 1) * s)) * omReal (i.1 + 1)) := by
      funext s; ring
    rw [heq] at h
    exact h.congr_deriv (by ring)
  exact (hpoly.add hsum).congr_deriv (by ring)

/- Clean 10-element list helper so TermList sums match Fin 10 sums directly! -/

private lemma list_eq_10 {α : Type*} (l : List α) (h : l.length = 10) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] := by
  rcases l with _ | ⟨x0, l⟩; · simp at h
  rcases l with _ | ⟨x1, l⟩; · simp at h
  rcases l with _ | ⟨x2, l⟩; · simp at h
  rcases l with _ | ⟨x3, l⟩; · simp at h
  rcases l with _ | ⟨x4, l⟩; · simp at h
  rcases l with _ | ⟨x5, l⟩; · simp at h
  rcases l with _ | ⟨x6, l⟩; · simp at h
  rcases l with _ | ⟨x7, l⟩; · simp at h
  rcases l with _ | ⟨x8, l⟩; · simp at h
  rcases l with _ | ⟨x9, l⟩; · simp at h
  rcases l with _ | ⟨_, _⟩
  · exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩
  · simp at h

/- Helper to convert `buildTermsM` and `buildTermsF` to Fin 10 sums in O(1) elaboration time! -/

private def cCosMInt (c : Cert) (i : Fin 10) : Int :=
  if i.1 = 1 then -c.alpha.getD i.1 0 + c.gamma else -c.alpha.getD i.1 0

private def cSinMInt (c : Cert) (i : Fin 10) : Int :=
  -c.beta.getD i.1 0

private def cCosFInt (c : Cert) (i : Fin 10) : Int :=
  let a := c.alpha.getD i.1 0
  let u := c.u.getD i.1 0
  let di := dIntList.getD i.1 0
  let cc0 := 2 * a * u * 10 - a * di
  if i.1 = 1 then cc0 - c.gamma * (c.p1 + c.p2) * 100000 - c.nuPlo * 10000000 + c.nuPhi * 10000000 else cc0

private def cSinFInt (c : Cert) (i : Fin 10) : Int :=
  let a := c.alpha.getD i.1 0
  let b := c.beta.getD i.1 0
  let v := c.v.getD i.1 0
  let di := dIntList.getD i.1 0
  let cs0 := 2 * a * v * 10 - b * di
  if i.1 = 1 then cs0 - c.gamma * (c.q1 + c.q2) * 100000 - c.nuQlo * 10000000 + c.nuQhi * 10000000 else cs0

private lemma cCosMR_eq (c : Cert) (i : Fin 10) :
    cCosMR c i = (cCosMInt c i : ℝ) / SC_R := by
  unfold cCosMR cCosMInt alphaR
  split_ifs <;> push_cast <;> ring

private lemma cSinMR_eq (c : Cert) (i : Fin 10) :
    cSinMR c i = (cSinMInt c i : ℝ) / SC_R := by
  unfold cSinMR cSinMInt betaR; push_cast; ring

private lemma cCosFR_approx (c : Cert) (i : Fin 10) :
    |SVAL_R * cCosFR c i - (cCosFInt c i : ℝ)| ≤
      if (i.1 + 1) % 2 = 0 then 0 else ((c.alpha.getD i.1 0).natAbs : ℝ) := by
  have hd := dIntList_sound i
  have hdiff : SVAL_R * cCosFR c i - (cCosFInt c i : ℝ) =
      -((c.alpha.getD i.1 0 : ℝ) * (dCont (i.1 + 1) * 10000000 - (dIntList.getD i.1 0 : ℝ))) := by
    unfold cCosFR cCosFInt alphaR uR SVAL_R SC_R
    split_ifs <;> push_cast <;> ring
  rw [hdiff, abs_neg, abs_mul]
  have ha : |(c.alpha.getD i.1 0 : ℝ)| = ((c.alpha.getD i.1 0).natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [ha]
  split_ifs with hev
  · rw [if_pos hev] at hd
    have h0 : |dCont (i.1 + 1) * 10000000 - (dIntList.getD i.1 0 : ℝ)| = 0 :=
      le_antisymm hd (abs_nonneg _)
    rw [h0, mul_zero]
  · rw [if_neg hev] at hd
    nlinarith [Nat.cast_nonneg (α := ℝ) (c.alpha.getD i.1 0).natAbs]

private lemma cSinFR_approx (c : Cert) (i : Fin 10) :
    |SVAL_R * cSinFR c i - (cSinFInt c i : ℝ)| ≤
      if (i.1 + 1) % 2 = 0 then 0 else ((c.beta.getD i.1 0).natAbs : ℝ) := by
  have hd := dIntList_sound i
  have hdiff : SVAL_R * cSinFR c i - (cSinFInt c i : ℝ) =
      -((c.beta.getD i.1 0 : ℝ) * (dCont (i.1 + 1) * 10000000 - (dIntList.getD i.1 0 : ℝ))) := by
    unfold cSinFR cSinFInt alphaR betaR vR SVAL_R SC_R
    split_ifs <;> push_cast <;> ring
  rw [hdiff, abs_neg, abs_mul]
  have hb : |(c.beta.getD i.1 0 : ℝ)| = ((c.beta.getD i.1 0).natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [hb]
  split_ifs with hev
  · rw [if_pos hev] at hd
    have h0 : |dCont (i.1 + 1) * 10000000 - (dIntList.getD i.1 0 : ℝ)| = 0 :=
      le_antisymm hd (abs_nonneg _)
    rw [h0, mul_zero]
  · rw [if_neg hev] at hd
    nlinarith [Nat.cast_nonneg (α := ℝ) (c.beta.getD i.1 0).natAbs]

private lemma buildTermsM_eq (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) :
    buildTermsM 1 c.alpha c.beta omIntList c.gamma =
      .cons 1 (cCosMInt c 0) (cSinMInt c 0) (omIntList.getD 0 0) (
      .cons 2 (cCosMInt c 1) (cSinMInt c 1) (omIntList.getD 1 0) (
      .cons 3 (cCosMInt c 2) (cSinMInt c 2) (omIntList.getD 2 0) (
      .cons 4 (cCosMInt c 3) (cSinMInt c 3) (omIntList.getD 3 0) (
      .cons 5 (cCosMInt c 4) (cSinMInt c 4) (omIntList.getD 4 0) (
      .cons 6 (cCosMInt c 5) (cSinMInt c 5) (omIntList.getD 5 0) (
      .cons 7 (cCosMInt c 6) (cSinMInt c 6) (omIntList.getD 6 0) (
      .cons 8 (cCosMInt c 7) (cSinMInt c 7) (omIntList.getD 7 0) (
      .cons 9 (cCosMInt c 8) (cSinMInt c 8) (omIntList.getD 8 0) (
      .cons 10 (cCosMInt c 9) (cSinMInt c 9) (omIntList.getD 9 0) .nil))))))))) := by
  rcases list_eq_10 c.alpha ha with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hA⟩
  rcases list_eq_10 c.beta hb with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hB⟩
  simp [cCosMInt, cSinMInt, hA, hB, buildTermsM, omIntList, Nat.beq]

private lemma buildTermsF_eq (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) :
    buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList =
      .cons 1 (cCosFInt c 0) (cSinFInt c 0) (omIntList.getD 0 0) (
      .cons 2 (cCosFInt c 1) (cSinFInt c 1) (omIntList.getD 1 0) (
      .cons 3 (cCosFInt c 2) (cSinFInt c 2) (omIntList.getD 2 0) (
      .cons 4 (cCosFInt c 3) (cSinFInt c 3) (omIntList.getD 3 0) (
      .cons 5 (cCosFInt c 4) (cSinFInt c 4) (omIntList.getD 4 0) (
      .cons 6 (cCosFInt c 5) (cSinFInt c 5) (omIntList.getD 5 0) (
      .cons 7 (cCosFInt c 6) (cSinFInt c 6) (omIntList.getD 6 0) (
      .cons 8 (cCosFInt c 7) (cSinFInt c 7) (omIntList.getD 7 0) (
      .cons 9 (cCosFInt c 8) (cSinFInt c 8) (omIntList.getD 8 0) (
      .cons 10 (cCosFInt c 9) (cSinFInt c 9) (omIntList.getD 9 0) .nil))))))))) := by
  rcases list_eq_10 c.alpha ha with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hA⟩
  rcases list_eq_10 c.beta hb with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hB⟩
  rcases list_eq_10 c.u hu with ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, hU⟩
  rcases list_eq_10 c.v hv with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, hV⟩
  simp [cCosFInt, cSinFInt, hA, hB, hU, hV, buildTermsF, dIntList, omIntList, Nat.beq]

private lemma list_getD_10 {α : Type*} (l : List α) (d : α) (h : l.length = 10) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d, l.getD 4 d,
         l.getD 5 d, l.getD 6 d, l.getD 7 d, l.getD 8 d, l.getD 9 d] := by
  rcases list_eq_10 l h with ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩
  rfl

private lemma fin10_sum {M : Type*} [AddCommMonoid M] (f : Fin 10 → M) :
    ∑ i : Fin 10, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  have huniv : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  rw [huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  ac_rfl

private lemma fin10_v0 : ((0 : Fin 10) : ℕ) = 0 := rfl
private lemma fin10_v1 : ((1 : Fin 10) : ℕ) = 1 := rfl
private lemma fin10_v2 : ((2 : Fin 10) : ℕ) = 2 := rfl
private lemma fin10_v3 : ((3 : Fin 10) : ℕ) = 3 := rfl
private lemma fin10_v4 : ((4 : Fin 10) : ℕ) = 4 := rfl
private lemma fin10_v5 : ((5 : Fin 10) : ℕ) = 5 := rfl
private lemma fin10_v6 : ((6 : Fin 10) : ℕ) = 6 := rfl
private lemma fin10_v7 : ((7 : Fin 10) : ℕ) = 7 := rfl
private lemma fin10_v8 : ((8 : Fin 10) : ℕ) = 8 := rfl
private lemma fin10_v9 : ((9 : Fin 10) : ℕ) = 9 := rfl

private lemma evalMVal_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) (baseAng : Nat) :
    evalMVal baseAng (buildTermsM 1 c.alpha c.beta omIntList c.gamma) 0 =
      ∑ i : Fin 10, (cCosMInt c i * cosQNat ((i.1 + 1) * baseAng) +
        cSinMInt c i * sinQNat ((i.1 + 1) * baseAng)) := by
  rw [buildTermsM_eq c ha hb, fin10_sum]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [evalMVal]
  abel

private lemma evalMDer_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) (baseAng : Nat) :
    evalMDer baseAng (buildTermsM 1 c.alpha c.beta omIntList c.gamma) 0 =
      ∑ i : Fin 10, ((-cCosMInt c i * sinQNat ((i.1 + 1) * baseAng) +
        cSinMInt c i * cosQNat ((i.1 + 1) * baseAng)) * Int.ofNat (omIntList.getD i.1 0)) := by
  rw [buildTermsM_eq c ha hb, fin10_sum]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [evalMDer]
  rw [zero_add]

private lemma sumB2M_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) :
    sumB2M (buildTermsM 1 c.alpha c.beta omIntList c.gamma) omSqHiList 0 =
      ∑ i : Fin 10, (((cCosMInt c i).natAbs + (cSinMInt c i).natAbs) * omSqHiList.getD i.1 0) := by
  rw [buildTermsM_eq c ha hb, fin10_sum]
  conv_lhs => rw [list_getD_10 omSqHiList 0 (by decide)]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [sumB2M]
  rw [Nat.zero_add]

private lemma sumErrValM_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) :
    sumErrValM (buildTermsM 1 c.alpha c.beta omIntList c.gamma) 0 =
      ∑ i : Fin 10, ((cCosMInt c i).natAbs + (cSinMInt c i).natAbs) := by
  rw [buildTermsM_eq c ha hb, fin10_sum]
  dsimp only [sumErrValM]
  ac_rfl

private lemma sumErrDerM_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) :
    sumErrDerM (buildTermsM 1 c.alpha c.beta omIntList c.gamma) 0 =
      ∑ i : Fin 10, (((cCosMInt c i).natAbs + (cSinMInt c i).natAbs) *
        ((omIntList.getD i.1 0 + 1 + 10000000 + 10000000 - 1) / 10000000)) := by
  rw [buildTermsM_eq c ha hb, fin10_sum]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [sumErrDerM]
  rw [Nat.zero_add]

private lemma evalFVal_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) (baseAng : Nat) :
    evalFVal baseAng (buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList) 0 =
      ∑ i : Fin 10, (-cCosFInt c i * cosQNat ((i.1 + 1) * baseAng) -
        cSinFInt c i * sinQNat ((i.1 + 1) * baseAng)) := by
  rw [buildTermsF_eq c ha hb hu hv, fin10_sum]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [evalFVal]
  simp only [neg_mul]
  abel

private lemma evalFDer_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) (baseAng : Nat) :
    evalFDer baseAng (buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList) 0 =
      ∑ i : Fin 10, ((cCosFInt c i * sinQNat ((i.1 + 1) * baseAng) -
        cSinFInt c i * cosQNat ((i.1 + 1) * baseAng)) * Int.ofNat (omIntList.getD i.1 0)) := by
  rw [buildTermsF_eq c ha hb hu hv, fin10_sum]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [evalFDer]
  rw [zero_add]

private lemma nat_beq_iff : ∀ a b : ℕ, Nat.beq a b = true ↔ a = b
  | 0, 0 => by simp [Nat.beq]
  | 0, _ + 1 => by simp [Nat.beq]
  | _ + 1, 0 => by simp [Nat.beq]
  | a + 1, b + 1 => by simp [Nat.beq, nat_beq_iff a b]

private lemma beq_mod2_eq_ite (m x : ℕ) :
    (if Nat.beq (m % 2) 0 then 0 else x) = (if m % 2 = 0 then 0 else x) := by
  by_cases h : m % 2 = 0
  · rw [if_pos ((nat_beq_iff _ _).mpr h), if_pos h]
  · rw [if_neg (by rw [nat_beq_iff]; exact h), if_neg h]

private lemma sumB2F_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) :
    sumB2F 1 (buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList) c.alpha c.beta omSqHiList 0 =
      ∑ i : Fin 10,
        ((((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
          (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs)) *
          omSqHiList.getD i.1 0 + 9999999) / 10000000) := by
  rw [buildTermsF_eq c ha hb hu hv, fin10_sum]
  conv_lhs =>
    rw [list_getD_10 c.alpha 0 ha, list_getD_10 c.beta 0 hb, list_getD_10 omSqHiList 0 (by decide)]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [sumB2F]
  rw [Nat.zero_add]
  repeat rw [beq_mod2_eq_ite]

private lemma sumErrValF_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) :
    sumErrValF 1 (buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList) c.alpha c.beta 0 =
      ∑ i : Fin 10,
        ((if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
         (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs) +
         ((cCosFInt c i).natAbs + (cSinFInt c i).natAbs + 9999999) / 10000000) := by
  rw [buildTermsF_eq c ha hb hu hv, fin10_sum]
  conv_lhs =>
    rw [list_getD_10 c.alpha 0 ha, list_getD_10 c.beta 0 hb]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [sumErrValF]
  rw [Nat.zero_add]
  repeat rw [beq_mod2_eq_ite]

private lemma sumErrDerF_eq_sum (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) :
    sumErrDerF 1 (buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList) c.alpha c.beta 0 =
      ∑ i : Fin 10,
        ((((if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
           (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs)) *
            (omIntList.getD i.1 0 + 1) + 9999999) / 10000000 +
         (((cCosFInt c i).natAbs + (cSinFInt c i).natAbs) *
            (omIntList.getD i.1 0 + 1 + 10000000) + 99999999999999) / 100000000000000) := by
  rw [buildTermsF_eq c ha hb hu hv, fin10_sum]
  conv_lhs =>
    rw [list_getD_10 c.alpha 0 ha, list_getD_10 c.beta 0 hb]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [sumErrDerF]
  rw [Nat.zero_add]
  repeat rw [beq_mod2_eq_ite]
  repeat rw [Nat.add_assoc]

private lemma sumQuadTerms_eq_sum (c : Cert) (ha : c.alpha.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) :
    sumQuadTerms c.alpha c.u c.v 0 =
      ∑ i : Fin 10, intFdiv (-c.alpha.getD i.1 0 *
        (c.u.getD i.1 0 * c.u.getD i.1 0 + c.v.getD i.1 0 * c.v.getD i.1 0) * 10000000) 1000000000000 := by
  rw [fin10_sum]
  conv_lhs =>
    rw [list_getD_10 c.alpha 0 ha, list_getD_10 c.u 0 hu, list_getD_10 c.v 0 hv]
  rw [fin10_v0, fin10_v1, fin10_v2, fin10_v3, fin10_v4, fin10_v5, fin10_v6, fin10_v7, fin10_v8, fin10_v9]
  dsimp only [sumQuadTerms]
  rw [zero_add]

/- Second-derivative upper bounds for Phi and NegPsi -/

private lemma Phi''_le (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10) (x : ℝ) :
    Phi'' c x ≤
      ((2 * (c.nuMhi - c.nuMlo).natAbs * 10000000 +
        sumB2M (buildTermsM 1 c.alpha c.beta omIntList c.gamma) omSqHiList 0 : ℕ) : ℝ) / SVAL_R := by
  unfold Phi''
  rw [sumB2M_eq_sum c ha hb]
  push_cast
  have h1 : -2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) ≤
      (2 * ((c.nuMhi - c.nuMlo).natAbs : ℝ) * 10000000) / SVAL_R := by
    have habs : -((c.nuMhi - c.nuMlo : ℤ) : ℝ) ≤ ((c.nuMhi - c.nuMlo).natAbs : ℝ) := by
      have := neg_le_abs ((c.nuMhi - c.nuMlo : ℤ) : ℝ)
      rwa [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at this
    unfold SC_R SVAL_R; linarith
  have h2 : ∑ i : Fin 10, (-(cCosMR c i * Real.cos (omReal (i.1 + 1) * x) +
        cSinMR c i * Real.sin (omReal (i.1 + 1) * x)) * (omReal (i.1 + 1)) ^ 2) ≤
      (∑ i : Fin 10, ((((cCosMInt c i).natAbs : ℝ) + ((cSinMInt c i).natAbs : ℝ)) *
        (omSqHiList.getD i.1 0 : ℝ))) / SVAL_R := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsq := omSqHiList_sound i
    have hcc : |cCosMR c i| = ((cCosMInt c i).natAbs : ℝ) / SC_R := by
      rw [cCosMR_eq, abs_div, abs_of_pos (by norm_num [SC_R] : (0 : ℝ) < SC_R),
        ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hcs : |cSinMR c i| = ((cSinMInt c i).natAbs : ℝ) / SC_R := by
      rw [cSinMR_eq, abs_div, abs_of_pos (by norm_num [SC_R] : (0 : ℝ) < SC_R),
        ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have htri : -(cCosMR c i * Real.cos (omReal (i.1 + 1) * x) +
        cSinMR c i * Real.sin (omReal (i.1 + 1) * x)) ≤
        (((cCosMInt c i).natAbs : ℝ) + ((cSinMInt c i).natAbs : ℝ)) / SC_R := by
      have ha1 : -cCosMR c i * Real.cos (omReal (i.1 + 1) * x) ≤ |cCosMR c i| := by
        calc -cCosMR c i * Real.cos (omReal (i.1 + 1) * x)
            ≤ |-cCosMR c i * Real.cos (omReal (i.1 + 1) * x)| := le_abs_self _
          _ = |cCosMR c i| * |Real.cos (omReal (i.1 + 1) * x)| := by rw [abs_mul, abs_neg]
          _ ≤ |cCosMR c i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ = |cCosMR c i| := mul_one _
      have hb1 : -cSinMR c i * Real.sin (omReal (i.1 + 1) * x) ≤ |cSinMR c i| := by
        calc -cSinMR c i * Real.sin (omReal (i.1 + 1) * x)
            ≤ |-cSinMR c i * Real.sin (omReal (i.1 + 1) * x)| := le_abs_self _
          _ = |cSinMR c i| * |Real.sin (omReal (i.1 + 1) * x)| := by rw [abs_mul, abs_neg]
          _ ≤ |cSinMR c i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
          _ = |cSinMR c i| := mul_one _
      rw [hcc] at ha1; rw [hcs] at hb1; rw [add_div]
      have hneg : -(cCosMR c i * Real.cos (omReal (i.1 + 1) * x) + cSinMR c i * Real.sin (omReal (i.1 + 1) * x)) =
          -cCosMR c i * Real.cos (omReal (i.1 + 1) * x) + -cSinMR c i * Real.sin (omReal (i.1 + 1) * x) := by ring
      linarith
    have hSC_pos : (0 : ℝ) < SC_R := by norm_num [SC_R]
    have hmul := mul_le_mul htri hsq (sq_nonneg _) (by positivity)
    have hrhs : ((((cCosMInt c i).natAbs : ℝ) + ((cSinMInt c i).natAbs : ℝ)) / SC_R) *
        ((omSqHiList.getD i.1 0 : ℝ) / 10000000) =
        (((cCosMInt c i).natAbs : ℝ) + ((cSinMInt c i).natAbs : ℝ)) * (omSqHiList.getD i.1 0 : ℝ) / SVAL_R := by
      unfold SC_R SVAL_R; ring
    linarith
  push_cast at h1; rw [add_div]; linarith

private lemma NegPsi''_le (c : Cert) (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) (t : ℝ) :
    NegPsi'' c t ≤
      ((sumB2F 1 (buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList)
        c.alpha c.beta omSqHiList 0 : ℕ) : ℝ) / SVAL_R := by
  unfold NegPsi''
  rw [sumB2F_eq_sum c ha hb hu hv]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsq := omSqHiList_sound i
  have hca := cCosFR_approx c i
  have hsa := cSinFR_approx c i
  have hSpos : (0 : ℝ) < SVAL_R := by norm_num [SVAL_R]
  have hcc_le : |SVAL_R * cCosFR c i| ≤ ((cCosFInt c i).natAbs : ℝ) +
      ((if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs : ℕ) : ℝ) := by
    have h1 := abs_sub_abs_le_abs_sub (SVAL_R * cCosFR c i) (cCosFInt c i : ℝ)
    have h2 : |(cCosFInt c i : ℝ)| = ((cCosFInt c i).natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    split_ifs at hca ⊢ <;> push_cast <;> linarith
  have hcs_le : |SVAL_R * cSinFR c i| ≤ ((cSinFInt c i).natAbs : ℝ) +
      ((if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs : ℕ) : ℝ) := by
    have h1 := abs_sub_abs_le_abs_sub (SVAL_R * cSinFR c i) (cSinFInt c i : ℝ)
    have h2 : |(cSinFInt c i : ℝ)| = ((cSinFInt c i).natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    split_ifs at hsa ⊢ <;> push_cast <;> linarith
  have htri : cCosFR c i * Real.cos (omReal (i.1 + 1) * t) + cSinFR c i * Real.sin (omReal (i.1 + 1) * t) ≤
      (((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
        (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs) : ℕ) : ℝ) / SVAL_R := by
    rw [le_div_iff₀ hSpos]
    have ha1 : SVAL_R * cCosFR c i * Real.cos (omReal (i.1 + 1) * t) ≤ |SVAL_R * cCosFR c i| := by
      calc SVAL_R * cCosFR c i * Real.cos (omReal (i.1 + 1) * t)
          ≤ |SVAL_R * cCosFR c i * Real.cos (omReal (i.1 + 1) * t)| := le_abs_self _
        _ = |SVAL_R * cCosFR c i| * |Real.cos (omReal (i.1 + 1) * t)| := abs_mul _ _
        _ ≤ |SVAL_R * cCosFR c i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |SVAL_R * cCosFR c i| := mul_one _
    have hb1 : SVAL_R * cSinFR c i * Real.sin (omReal (i.1 + 1) * t) ≤ |SVAL_R * cSinFR c i| := by
      calc SVAL_R * cSinFR c i * Real.sin (omReal (i.1 + 1) * t)
          ≤ |SVAL_R * cSinFR c i * Real.sin (omReal (i.1 + 1) * t)| := le_abs_self _
        _ = |SVAL_R * cSinFR c i| * |Real.sin (omReal (i.1 + 1) * t)| := abs_mul _ _
        _ ≤ |SVAL_R * cSinFR c i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |SVAL_R * cSinFR c i| := mul_one _
    push_cast at hcc_le hcs_le ⊢
    have hdist : (cCosFR c i * Real.cos (omReal (i.1 + 1) * t) + cSinFR c i * Real.sin (omReal (i.1 + 1) * t)) * SVAL_R =
        SVAL_R * cCosFR c i * Real.cos (omReal (i.1 + 1) * t) + SVAL_R * cSinFR c i * Real.sin (omReal (i.1 + 1) * t) := by ring
    linarith
  have hmul := mul_le_mul htri hsq (sq_nonneg _) (by positivity)
  have hcdiv := nat_cdiv_ge_sub
    (((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
      (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs)) *
      omSqHiList.getD i.1 0) 10000000 9999999 (by norm_num) (by norm_num)
  have hstep : (((((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
      (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs) : ℕ) : ℝ) / SVAL_R) *
      ((omSqHiList.getD i.1 0 : ℝ) / 10000000)) ≤
      (((((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
      (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs)) *
      omSqHiList.getD i.1 0 + 9999999) / 10000000 : ℕ) : ℝ) / SVAL_R := by
    have : (((((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
        (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs) : ℕ) : ℝ) / SVAL_R) *
        ((omSqHiList.getD i.1 0 : ℝ) / 10000000)) =
        ((((((cCosFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.alpha.getD i.1 0).natAbs) +
        (cSinFInt c i).natAbs + (if (i.1 + 1) % 2 = 0 then 0 else (c.beta.getD i.1 0).natAbs)) *
        omSqHiList.getD i.1 0 : ℕ) : ℝ) / 10000000)) / SVAL_R := by simp only [Nat.cast_mul]; ring
    rw [this]
    exact div_le_div_of_nonneg_right hcdiv hSpos.le
  exact hmul.trans hstep

/- Subsection 6E: Partitioning Intervals and Soundness of uPhi and uNegPsi -/

private lemma sum_partition_intervals (a0 d : ℝ) (S : Finset ℤ) (x : ℤ → ℝ) (f : ℤ → ℝ) :
    ∀ M : ℕ, (∀ k ∈ S, a0 ≤ x k ∧ x k < a0 + (M : ℝ) * d) →
      ∑ k ∈ S, f k =
        ∑ j ∈ Finset.range M,
          ∑ k ∈ S.filter (fun k : ℤ => a0 + (j : ℝ) * d ≤ x k ∧ x k < a0 + ((j + 1 : ℕ) : ℝ) * d), f k
  | 0, hS => by
      have hempty : S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk; have := hS k hk; simp at this; linarith
      subst hempty; simp
  | M + 1, hS => by
      let S1 := S.filter (fun k : ℤ => x k < a0 + (M : ℝ) * d)
      let S2 := S.filter (fun k : ℤ => ¬ x k < a0 + (M : ℝ) * d)
      have hsplit : ∑ k ∈ S, f k = ∑ k ∈ S1, f k + ∑ k ∈ S2, f k :=
        (Finset.sum_filter_add_sum_filter_not S (fun k : ℤ => x k < a0 + (M : ℝ) * d) f).symm
      rw [hsplit, Finset.sum_range_succ]
      congr 1
      · rw [sum_partition_intervals a0 d S1 x f M (fun k hk =>
            ⟨(hS k (Finset.mem_filter.mp hk).1).1, (Finset.mem_filter.mp hk).2⟩)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjM : j < M := Finset.mem_range.mp hj
        congr 1; ext k; simp only [S1, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hkS, _⟩, h1, h2⟩; exact ⟨hkS, h1, h2⟩
        · rintro ⟨hkS, h1, h2⟩
          have hd : 0 ≤ d := by
            have := hS k hkS
            have hjp : ((j + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hjM
            by_contra hdneg; push Not at hdneg
            have h1' : a0 + ((j + 1 : ℕ) : ℝ) * d ≤ a0 + (j : ℝ) * d := by push_cast; nlinarith
            linarith
          have hjp : ((j + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hjM
          exact ⟨⟨hkS, by nlinarith⟩, h1, h2⟩
      · congr 1; ext k; simp only [S2, Finset.mem_filter]
        constructor
        · rintro ⟨hkS, hge⟩; push Not at hge; exact ⟨hkS, hge, (hS k hkS).2⟩
        · rintro ⟨hkS, h1, _⟩; exact ⟨hkS, not_lt.mpr h1⟩

private lemma oneMQuad_sound (c : Cert)
    (hm : c.mQuad = 512 ∨ c.mQuad = 1024)
    (ha : c.alpha.length = 10) (hb : c.beta.length = 10) (j : ℕ) :
    let lam2 := c.nuMhi - c.nuMlo
    let termsM := buildTermsM 1 c.alpha c.beta omIntList c.gamma
    let b2Phi : Nat := 2 * lam2.natAbs * 10000000 + sumB2M termsM omSqHiList 0
    let errPhiVal : Nat := sumErrValM termsM 0
    let errPhiDer : Nat := sumErrDerM termsM 0
    let dMDen : Nat := c.mQuad / 4
    let stepM : Nat := 1024 / c.mQuad
    let padPhi : Int := Int.ofNat ((b2Phi + 8 * dMDen * dMDen - 1) / (8 * dMDen * dMDen) + errPhiVal)
    let xm : ℝ := -2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))
    let dM : ℝ := 1 / (dMDen : ℝ)
    (∀ x, |x - xm| ≤ dM / 2 →
      Phi c x ≤ Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) + Phi' c xm * (x - xm)) ∧
    uArea (Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8)) |Phi' c xm| dM ≤
      (oneMQuad c.nuMassM c.nuEM lam2 padPhi errPhiDer dMDen stepM termsM j : ℝ) / (SVAL_R * (dMDen : ℝ)) := by
  intro lam2 termsM b2Phi errPhiVal errPhiDer dMDen stepM padPhi xm dM
  have hdM_pos : 0 < dMDen := by rcases hm with h | h <;> simp [dMDen, h]
  have hdMR : (0 : ℝ) < dMDen := by positivity
  have hdM_real_pos : 0 < dM := by positivity
  have hSpos : (0 : ℝ) < SVAL_R := by norm_num [SVAL_R]
  have hstep_eq : (stepM : ℝ) * (dMDen : ℝ) = 256 := by
    rcases hm with h | h <;> norm_num [stepM, dMDen, h]
  have hB2 : ∀ x, Phi'' c x ≤ (b2Phi : ℝ) / SVAL_R := Phi''_le c ha hb
  constructor
  · intro x hx
    have ht := taylor_order2_le (hasDerivAt_Phi c) (hasDerivAt_Phi' c) hB2 xm x
    have hsq : (x - xm) ^ 2 ≤ (dM / 2) ^ 2 := by
      have h1 := abs_le.mp hx
      nlinarith
    have hb2_nn : (0 : ℝ) ≤ (b2Phi : ℝ) / SVAL_R := by positivity
    nlinarith
  · -- Show Phi c xm + b2/SVAL * dM^2/8 <= aHi / SVAL and |Phi' c xm| <= bHi / SVAL!
    unfold oneMQuad
    set xmNum : Int := 2 * Int.ofNat j + 1 - 4 * Int.ofNat dMDen
    set xmDen : Nat := 2 * dMDen
    set xmDenI : Int := Int.ofNat xmDen
    set xmDen2 : Nat := xmDen * xmDen
    set polyVal : Int := intCdiv ((-c.nuMassM * Int.ofNat xmDen2 - c.nuEM * xmNum * xmDenI - lam2 * xmNum * xmNum) * 10000000) xmDen2
    set baseAng : Nat := stepM * (2 * j + 1) + 1024
    set tv : Int := evalMVal baseAng termsM 0
    set tdRaw : Int := evalMDer baseAng termsM 0
    set td : Int := intFdiv tdRaw 10000000
    set polyDerQ : Int := intFdiv ((-c.nuEM * xmDenI - 2 * lam2 * xmNum) * 10000000) xmDen
    set bHi : Nat := (polyDerQ + td).natAbs + 2 + errPhiDer
    set aHi : Int := polyVal + tv + padPhi
    have hxm_eq : xm = (xmNum : ℝ) / (xmDen : ℝ) := by
      simp only [xm, xmNum, xmDen, Int.ofNat_eq_natCast]; push_cast; field_simp; ring
    have hang : ∀ i : Fin 10,
        Real.cos (omReal (i.1 + 1) * xm) = Real.cos ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) ∧
        Real.sin (omReal (i.1 + 1) * xm) = Real.sin ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) := by
      intro i
      have harg : (((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024 =
          omReal (i.1 + 1) * xm + ((i.1 + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
        simp only [baseAng, omReal, xm]
        push_cast
        have hstep_div : (stepM : ℝ) = 256 / (dMDen : ℝ) := by
          rw [eq_div_iff hdMR.ne']; exact hstep_eq
        rw [hstep_div]; field_simp [hdMR.ne']; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
      exact ⟨rfl, rfl⟩
    -- Bound SVAL * Phi(xm) + b2Phi * dM^2/8 <= aHi:
    have ha_le : Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) ≤ (aHi : ℝ) / SVAL_R := by
      rw [le_div_iff₀ hSpos]
      have hpoly_le : SVAL_R * (-((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * xm -
          (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm ^ 2) ≤ (polyVal : ℝ) := by
        have h1 := le_intCdiv ((-c.nuMassM * Int.ofNat xmDen2 - c.nuEM * xmNum * xmDenI - lam2 * xmNum * xmNum) * 10000000)
          (by positivity : 0 < xmDen2)
        have heq : SVAL_R * (-((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * xm -
            (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm ^ 2) =
            (((-c.nuMassM * Int.ofNat xmDen2 - c.nuEM * xmNum * xmDenI - lam2 * xmNum * xmNum) * 10000000 : ℤ) : ℝ) /
              (xmDen2 : ℝ) := by
          rw [hxm_eq]
          simp only [xmDenI, xmDen2, lam2, SVAL_R, SC_R, Int.ofNat_eq_natCast]
          have hxd : (xmDen : ℝ) ≠ 0 := by positivity
          push_cast; field_simp [hxd]; ring
        rw [heq]; exact h1
      have htrig_le : SVAL_R * (∑ i : Fin 10, (cCosMR c i * Real.cos (omReal (i.1 + 1) * xm) +
          cSinMR c i * Real.sin (omReal (i.1 + 1) * xm))) ≤ (tv : ℝ) + (errPhiVal : ℝ) := by
        have htv_eq : (tv : ℝ) = ∑ i : Fin 10, ((cCosMInt c i : ℝ) * (cosQNat ((i.1 + 1) * baseAng) : ℝ) +
            (cSinMInt c i : ℝ) * (sinQNat ((i.1 + 1) * baseAng) : ℝ)) := by
          dsimp [tv, termsM]; rw [evalMVal_eq_sum c ha hb baseAng]; push_cast; rfl
        have herr_eq : (errPhiVal : ℝ) = ∑ i : Fin 10, (((cCosMInt c i).natAbs : ℝ) + ((cSinMInt c i).natAbs : ℝ)) := by
          dsimp [errPhiVal, termsM]; rw [sumErrValM_eq_sum c ha hb]; push_cast; rfl
        rw [htv_eq, herr_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have ⟨hca, _⟩ := cosQNat_sound ((i.1 + 1) * baseAng)
        have ⟨hsa, _⟩ := sinQNat_sound ((i.1 + 1) * baseAng)
        have ⟨hcang, hsang⟩ := hang i
        rw [hcang, hsang, cCosMR_eq, cSinMR_eq]
        have hdiff : SVAL_R * ((cCosMInt c i : ℝ) / SC_R * Real.cos ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) +
              (cSinMInt c i : ℝ) / SC_R * Real.sin ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024)) -
            ((cCosMInt c i : ℝ) * (cosQNat ((i.1 + 1) * baseAng) : ℝ) +
              (cSinMInt c i : ℝ) * (sinQNat ((i.1 + 1) * baseAng) : ℝ)) =
            (cCosMInt c i : ℝ) * (10000000 * (Real.cos ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
              (cosQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000)) +
            (cSinMInt c i : ℝ) * (10000000 * (Real.sin ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
              (sinQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000)) := by
          unfold SVAL_R SC_R; ring
        have hc1 : |(cCosMInt c i : ℝ) * (10000000 * (Real.cos ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
            (cosQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000))| ≤ ((cCosMInt c i).natAbs : ℝ) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10000000),
            ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          have h10 : 10000000 * |Real.cos ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
              (cosQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000| ≤ 1 := by linarith
          exact (mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg _)).trans_eq (mul_one _)
        have hs1 : |(cSinMInt c i : ℝ) * (10000000 * (Real.sin ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
            (sinQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000))| ≤ ((cSinMInt c i).natAbs : ℝ) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10000000),
            ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          have h10 : 10000000 * |Real.sin ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
              (sinQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000| ≤ 1 := by linarith
          exact (mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg _)).trans_eq (mul_one _)
        have hle1 := le_abs_self ((cCosMInt c i : ℝ) * (10000000 * (Real.cos ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
            (cosQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000)))
        have hle2 := le_abs_self ((cSinMInt c i : ℝ) * (10000000 * (Real.sin ((((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) -
            (sinQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000)))
        linarith only [hdiff, hc1, hs1, hle1, hle2]
      have hpad_le : (b2Phi : ℝ) * (dM ^ 2 / 8) ≤ (((b2Phi + 8 * dMDen * dMDen - 1) / (8 * dMDen * dMDen) : ℕ) : ℝ) := by
        have h1 := nat_cdiv_ge b2Phi (by positivity : 0 < 8 * dMDen * dMDen)
        have heq : (b2Phi : ℝ) * (dM ^ 2 / 8) = (b2Phi : ℝ) / ((8 * dMDen * dMDen : ℕ) : ℝ) := by
          dsimp [dM]; push_cast; ring
        rw [heq]; exact h1
      have haHiR : (aHi : ℝ) = (polyVal : ℝ) + (tv : ℝ) +
          (((b2Phi + 8 * dMDen * dMDen - 1) / (8 * dMDen * dMDen) : ℕ) : ℝ) + (errPhiVal : ℝ) := by
        dsimp only [aHi, padPhi]
        rw [Int.cast_add, Int.cast_add, Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_add]
        ring
      have hphi_mul : (Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8)) * SVAL_R =
          SVAL_R * (-((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * xm -
            (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm ^ 2) +
          SVAL_R * (∑ i : Fin 10, (cCosMR c i * Real.cos (omReal (i.1 + 1) * xm) +
            cSinMR c i * Real.sin (omReal (i.1 + 1) * xm))) +
          (b2Phi : ℝ) * (dM ^ 2 / 8) := by
        unfold Phi; field_simp [hSpos.ne']
      linarith
    -- Bound |Phi' c xm| <= bHi / SVAL:
    have hb_le : |Phi' c xm| ≤ (bHi : ℝ) / SVAL_R := by
      rw [le_div_iff₀ hSpos, ← abs_of_pos hSpos, ← abs_mul]
      have hpd_err : |SVAL_R * (-((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm) -
          (polyDerQ : ℝ)| ≤ 1 := by
        have h1 := intFdiv_abs_sub_le ((-c.nuEM * xmDenI - 2 * lam2 * xmNum) * 10000000) (by positivity : 0 < xmDen)
        have heq : SVAL_R * (-((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm) =
            (((-c.nuEM * xmDenI - 2 * lam2 * xmNum) * 10000000 : ℤ) : ℝ) / (xmDen : ℝ) := by
          rw [hxm_eq]; simp only [xmDenI, lam2, SVAL_R, SC_R, Int.ofNat_eq_natCast]
          have hxd : (xmDen : ℝ) ≠ 0 := by positivity
          push_cast; field_simp [hxd]; ring
        rw [heq]; exact h1
      have htd_err1 : |(tdRaw : ℝ) / 10000000 - (td : ℝ)| ≤ 1 := by
        have h := intFdiv_abs_sub_le tdRaw (by norm_num : 0 < 10000000)
        rwa [Nat.cast_ofNat] at h
      have htd_err2 : |SVAL_R * (∑ i : Fin 10, ((-cCosMR c i * Real.sin (omReal (i.1 + 1) * xm) +
          cSinMR c i * Real.cos (omReal (i.1 + 1) * xm)) * omReal (i.1 + 1))) - (tdRaw : ℝ) / 10000000| ≤
          (errPhiDer : ℝ) := by
        have htdRaw_eq : (tdRaw : ℝ) / 10000000 = ∑ i : Fin 10,
            ((-(cCosMInt c i : ℝ) * (sinQNat ((i.1 + 1) * baseAng) : ℝ) +
              (cSinMInt c i : ℝ) * (cosQNat ((i.1 + 1) * baseAng) : ℝ)) * (omIntList.getD i.1 0 : ℝ) / 10000000) := by
          dsimp [tdRaw, termsM]; rw [evalMDer_eq_sum c ha hb baseAng]; simp only [Int.ofNat_eq_natCast]; push_cast; rw [Finset.sum_div]
        have herr_eq : (errPhiDer : ℝ) = ∑ i : Fin 10,
            ((((cCosMInt c i).natAbs : ℝ) + ((cSinMInt c i).natAbs : ℝ)) *
              (((omIntList.getD i.1 0 + 1 + 10000000 + 10000000 - 1) / 10000000 : ℕ) : ℝ)) := by
          dsimp only [errPhiDer, termsM]; rw [sumErrDerM_eq_sum c ha hb]
          rw [Nat.cast_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.cast_mul, Nat.cast_add]
        rw [htdRaw_eq, herr_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have ⟨hca, hcb⟩ := cosQNat_sound ((i.1 + 1) * baseAng)
        have ⟨hsa, hsb⟩ := sinQNat_sound ((i.1 + 1) * baseAng)
        have ⟨hcang, hsang⟩ := hang i
        have ⟨hom_lo, hom_hi⟩ := omIntList_sound i
        have hom_nn : 0 ≤ omReal (i.1 + 1) := (omReal_pos (Nat.succ_pos i.1)).le
        rw [hcang, hsang, cCosMR_eq, cSinMR_eq]
        set θ : ℝ := (((i.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024
        set cQ : ℝ := (cosQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000
        set sQ : ℝ := (sinQNat ((i.1 + 1) * baseAng) : ℝ) / 10000000
        set omQ : ℝ := (omIntList.getD i.1 0 : ℝ) / 10000000
        have hsin_prod : |omReal (i.1 + 1) * Real.sin θ - omQ * sQ| ≤
            ((omIntList.getD i.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000 := by
          have hid : omReal (i.1 + 1) * Real.sin θ - omQ * sQ =
              omReal (i.1 + 1) * (Real.sin θ - sQ) + (omReal (i.1 + 1) - omQ) * sQ := by ring
          rw [hid]
          have h1 : |omReal (i.1 + 1) * (Real.sin θ - sQ)| ≤ omReal (i.1 + 1) * (1 / 10000000) := by
            rw [abs_mul, abs_of_nonneg hom_nn]; exact mul_le_mul_of_nonneg_left hsa hom_nn
          have h2 : |(omReal (i.1 + 1) - omQ) * sQ| ≤ 1 / 10000000 := by
            rw [abs_mul]
            have homd : |omReal (i.1 + 1) - omQ| ≤ 1 / 10000000 := by
              rw [abs_le]; dsimp [omQ]; constructor <;> linarith
            calc |omReal (i.1 + 1) - omQ| * |sQ|
                ≤ (1 / 10000000) * 1 := mul_le_mul homd hsb (abs_nonneg _) (by norm_num)
              _ = 1 / 10000000 := mul_one _
          have htri := abs_add_le (omReal (i.1 + 1) * (Real.sin θ - sQ)) ((omReal (i.1 + 1) - omQ) * sQ)
          push_cast; linarith
        have hcos_prod : |omReal (i.1 + 1) * Real.cos θ - omQ * cQ| ≤
            ((omIntList.getD i.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000 := by
          have hid : omReal (i.1 + 1) * Real.cos θ - omQ * cQ =
              omReal (i.1 + 1) * (Real.cos θ - cQ) + (omReal (i.1 + 1) - omQ) * cQ := by ring
          rw [hid]
          have h1 : |omReal (i.1 + 1) * (Real.cos θ - cQ)| ≤ omReal (i.1 + 1) * (1 / 10000000) := by
            rw [abs_mul, abs_of_nonneg hom_nn]; exact mul_le_mul_of_nonneg_left hca hom_nn
          have h2 : |(omReal (i.1 + 1) - omQ) * cQ| ≤ 1 / 10000000 := by
            rw [abs_mul]
            have homd : |omReal (i.1 + 1) - omQ| ≤ 1 / 10000000 := by
              rw [abs_le]; dsimp [omQ]; constructor <;> linarith
            calc |omReal (i.1 + 1) - omQ| * |cQ|
                ≤ (1 / 10000000) * 1 := mul_le_mul homd hcb (abs_nonneg _) (by norm_num)
              _ = 1 / 10000000 := mul_one _
          have htri := abs_add_le (omReal (i.1 + 1) * (Real.cos θ - cQ)) ((omReal (i.1 + 1) - omQ) * cQ)
          push_cast; linarith
        have hterm : SVAL_R * ((-((cCosMInt c i : ℝ) / SC_R) * Real.sin θ + (cSinMInt c i : ℝ) / SC_R * Real.cos θ) * omReal (i.1 + 1)) -
            (-(cCosMInt c i : ℝ) * (sinQNat ((i.1 + 1) * baseAng) : ℝ) + (cSinMInt c i : ℝ) * (cosQNat ((i.1 + 1) * baseAng) : ℝ)) *
              (omIntList.getD i.1 0 : ℝ) / 10000000 =
            -(cCosMInt c i : ℝ) * (10000000 * (omReal (i.1 + 1) * Real.sin θ - omQ * sQ)) +
            (cSinMInt c i : ℝ) * (10000000 * (omReal (i.1 + 1) * Real.cos θ - omQ * cQ)) := by
          dsimp [cQ, sQ, omQ, SVAL_R, SC_R]; ring
        rw [hterm]
        have hcdiv := nat_cdiv_ge (omIntList.getD i.1 0 + 1 + 10000000) (by norm_num : 0 < 10000000)
        rw [Nat.cast_ofNat] at hcdiv
        have htri := abs_add_le (-(cCosMInt c i : ℝ) * (10000000 * (omReal (i.1 + 1) * Real.sin θ - omQ * sQ)))
          ((cSinMInt c i : ℝ) * (10000000 * (omReal (i.1 + 1) * Real.cos θ - omQ * cQ)))
        rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10000000),
          abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10000000),
          ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast,
          ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at htri
        have hbd : 10000000 * |omReal (i.1 + 1) * Real.sin θ - omQ * sQ| ≤
            (((omIntList.getD i.1 0 + 1 + 10000000 + 10000000 - 1) / 10000000 : ℕ) : ℝ) := by
          have : 10000000 * (((omIntList.getD i.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000) =
              ((omIntList.getD i.1 0 + 1 + 10000000 : ℕ) : ℝ) / 10000000 := by ring
          linarith only [hsin_prod, hcdiv, this]
        have hbd2 : 10000000 * |omReal (i.1 + 1) * Real.cos θ - omQ * cQ| ≤
            (((omIntList.getD i.1 0 + 1 + 10000000 + 10000000 - 1) / 10000000 : ℕ) : ℝ) := by
          have : 10000000 * (((omIntList.getD i.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000) =
              ((omIntList.getD i.1 0 + 1 + 10000000 : ℕ) : ℝ) / 10000000 := by ring
          linarith only [hcos_prod, hcdiv, this]
        have hmul1 := mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg (α := ℝ) (cCosMInt c i).natAbs)
        have hmul2 := mul_le_mul_of_nonneg_left hbd2 (Nat.cast_nonneg (α := ℝ) (cSinMInt c i).natAbs)
        linarith
      have htot : |Phi' c xm * SVAL_R - ((polyDerQ : ℝ) + (td : ℝ))| ≤ 2 + (errPhiDer : ℝ) := by
        have hrew : Phi' c xm * SVAL_R - ((polyDerQ : ℝ) + (td : ℝ)) =
            (SVAL_R * (-((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm) - (polyDerQ : ℝ)) +
            (SVAL_R * (∑ i : Fin 10, ((-cCosMR c i * Real.sin (omReal (i.1 + 1) * xm) +
              cSinMR c i * Real.cos (omReal (i.1 + 1) * xm)) * omReal (i.1 + 1))) - (tdRaw : ℝ) / 10000000) +
            ((tdRaw : ℝ) / 10000000 - (td : ℝ)) := by unfold Phi'; ring
        rw [hrew]
        refine (abs_add_le _ _).trans ?_
        have h12 := abs_add_le
          (SVAL_R * (-((c.nuEM : ℝ) / SC_R) - 2 * (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * xm) - (polyDerQ : ℝ))
          (SVAL_R * (∑ i : Fin 10, ((-cCosMR c i * Real.sin (omReal (i.1 + 1) * xm) +
            cSinMR c i * Real.cos (omReal (i.1 + 1) * xm)) * omReal (i.1 + 1))) - (tdRaw : ℝ) / 10000000)
        linarith only [h12, hpd_err, htd_err1, htd_err2]
      have hbHiR : (bHi : ℝ) = |(polyDerQ : ℝ) + (td : ℝ)| + 2 + (errPhiDer : ℝ) := by
        dsimp [bHi]; push_cast
        have : ((polyDerQ + td).natAbs : ℝ) = |(polyDerQ : ℝ) + (td : ℝ)| := by
          rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs, Int.cast_add]
        linarith
      have hsub := abs_sub_abs_le_abs_sub (Phi' c xm * SVAL_R) ((polyDerQ : ℝ) + (td : ℝ))
      linarith
    exact (uArea_mono ha_le (abs_nonneg _) hb_le hdM_real_pos).trans (upperIntPos_sound aHi bHi dMDen hdM_pos hSpos)

private lemma oneFQuad_sound (c : Cert)
    (hm : c.mQuad = 512 ∨ c.mQuad = 1024) (hf : c.fQuad * 2 = c.mQuad)
    (ha : c.alpha.length = 10) (hb : c.beta.length = 10)
    (hu : c.u.length = 10) (hv : c.v.length = 10) (i : ℕ) :
    let linF := linFInt c
    let termsF := buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList
    let b2Psi : Nat := sumB2F 1 termsF c.alpha c.beta omSqHiList 0
    let errPsiVal : Nat := sumErrValF 1 termsF c.alpha c.beta 0
    let errPsiDer : Nat := sumErrDerF 1 termsF c.alpha c.beta 0
    let dFDen : Nat := c.fQuad / 2
    let stepF : Nat := 512 / c.fQuad
    let padPsi : Int := Int.ofNat ((b2Psi + 8 * dFDen * dFDen - 1) / (8 * dFDen * dFDen) + errPsiVal)
    let tm : ℝ := -1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ))
    let dF : ℝ := 1 / (dFDen : ℝ)
    (∀ t, |t - tm| ≤ dF / 2 →
      NegPsi c t ≤ NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8) + NegPsi' c tm * (t - tm)) ∧
    uArea (NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8)) |NegPsi' c tm| dF ≤
      (oneFQuad c.nuMassf linF padPsi errPsiDer dFDen stepF termsF i : ℝ) / (SVAL_R * (dFDen : ℝ)) := by
  intro linF termsF b2Psi errPsiVal errPsiDer dFDen stepF padPsi tm dF
  have hf_cases : c.fQuad = 256 ∨ c.fQuad = 512 := by omega
  have hdF_pos : 0 < dFDen := by rcases hf_cases with h | h <;> simp [dFDen, h]
  have hdFR : (0 : ℝ) < dFDen := by positivity
  have hdF_real_pos : 0 < dF := by positivity
  have hSpos : (0 : ℝ) < SVAL_R := by norm_num [SVAL_R]
  have hstep_eq : (stepF : ℝ) * (dFDen : ℝ) = 256 := by
    rcases hf_cases with h | h <;> norm_num [stepF, dFDen, h]
  have hB2 : ∀ t, NegPsi'' c t ≤ (b2Psi : ℝ) / SVAL_R := NegPsi''_le c ha hb hu hv
  constructor
  · intro t ht
    have htaylor := taylor_order2_le (hasDerivAt_NegPsi c) (hasDerivAt_NegPsi' c) hB2 tm t
    have hsq : (t - tm) ^ 2 ≤ (dF / 2) ^ 2 := by
      have h1 := abs_le.mp ht
      nlinarith
    have hb2_nn : (0 : ℝ) ≤ (b2Psi : ℝ) / SVAL_R := by positivity
    nlinarith
  · unfold oneFQuad
    set tmNum : Int := 2 * Int.ofNat i + 1 - 2 * Int.ofNat dFDen
    set tmDen : Nat := 2 * dFDen
    set polyVal : Int := intCdiv (-c.nuMassf * 10000000 * Int.ofNat tmDen - linF * tmNum) tmDen
    set baseAng : Nat := stepF * (2 * i + 1) + 1536
    set tvRaw : Int := evalFVal baseAng termsF 0
    set tv : Int := intCdiv tvRaw 10000000
    set tdRaw : Int := evalFDer baseAng termsF 0
    set td : Int := intFdiv tdRaw 100000000000000
    set bHi : Nat := (-linF + td).natAbs + 1 + errPsiDer
    set aHi : Int := polyVal + tv + padPsi
    have htm_eq : tm = (tmNum : ℝ) / (tmDen : ℝ) := by
      simp only [tm, tmNum, tmDen, Int.ofNat_eq_natCast]; push_cast; field_simp; ring
    have hang : ∀ m : Fin 10,
        Real.cos (omReal (m.1 + 1) * tm) = Real.cos ((((m.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) ∧
        Real.sin (omReal (m.1 + 1) * tm) = Real.sin ((((m.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024) := by
      intro m
      have harg : (((m.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024 =
          omReal (m.1 + 1) * tm + ((m.1 + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
        simp only [baseAng, omReal, tm]
        push_cast
        have hstep_div : (stepF : ℝ) = 256 / (dFDen : ℝ) := by
          rw [eq_div_iff hdFR.ne']; exact hstep_eq
        rw [hstep_div]; field_simp [hdFR.ne']; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
      exact ⟨rfl, rfl⟩
    have ha_le : NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8) ≤ (aHi : ℝ) / SVAL_R := by
      rw [le_div_iff₀ hSpos]
      have hpoly_le : SVAL_R * (-((c.nuMassf : ℝ) / SC_R) - ((linF : ℝ) / SVAL_R) * tm) ≤ (polyVal : ℝ) := by
        have h1 := le_intCdiv (-c.nuMassf * 10000000 * Int.ofNat tmDen - linF * tmNum) (by positivity : 0 < tmDen)
        have heq : SVAL_R * (-((c.nuMassf : ℝ) / SC_R) - ((linF : ℝ) / SVAL_R) * tm) =
            ((-c.nuMassf * 10000000 * Int.ofNat tmDen - linF * tmNum : ℤ) : ℝ) / (tmDen : ℝ) := by
          rw [htm_eq]
          have htd : (tmDen : ℝ) ≠ 0 := by positivity
          simp only [SVAL_R, SC_R, Int.ofNat_eq_natCast]; push_cast; field_simp [htd]; ring
        rw [heq]; exact h1
      have htv_le : (tvRaw : ℝ) / 10000000 ≤ (tv : ℝ) :=
        le_intCdiv tvRaw (by norm_num : 0 < 10000000)
      have htrig_le : -SVAL_R * (∑ m : Fin 10, (cCosFR c m * Real.cos (omReal (m.1 + 1) * tm) +
          cSinFR c m * Real.sin (omReal (m.1 + 1) * tm))) ≤ (tvRaw : ℝ) / 10000000 + (errPsiVal : ℝ) := by
        have htvRaw_eq : (tvRaw : ℝ) / 10000000 = ∑ m : Fin 10,
            ((-(cCosFInt c m : ℝ) * (cosQNat ((m.1 + 1) * baseAng) : ℝ) -
              (cSinFInt c m : ℝ) * (sinQNat ((m.1 + 1) * baseAng) : ℝ)) / 10000000) := by
          dsimp [tvRaw, termsF]; rw [evalFVal_eq_sum c ha hb hu hv baseAng]; push_cast; rw [Finset.sum_div]
        have herr_eq : (errPsiVal : ℝ) = ∑ m : Fin 10,
            (((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs : ℕ) : ℝ) +
             ((if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs : ℕ) : ℝ) +
             ((((cCosFInt c m).natAbs + (cSinFInt c m).natAbs + 9999999) / 10000000 : ℕ) : ℝ)) := by
          dsimp [errPsiVal, termsF]; rw [sumErrValF_eq_sum c ha hb hu hv]; push_cast; rfl
        rw [htvRaw_eq, herr_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun m _ => ?_
        have ⟨hca, _⟩ := cosQNat_sound ((m.1 + 1) * baseAng)
        have ⟨hsa, _⟩ := sinQNat_sound ((m.1 + 1) * baseAng)
        have ⟨hcang, hsang⟩ := hang m
        have hcc_err := cCosFR_approx c m
        have hcs_err := cSinFR_approx c m
        rw [hcang, hsang]
        set θ : ℝ := (((m.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024
        set cQ : ℝ := (cosQNat ((m.1 + 1) * baseAng) : ℝ) / 10000000
        set sQ : ℝ := (sinQNat ((m.1 + 1) * baseAng) : ℝ) / 10000000
        have hdiff : -SVAL_R * (cCosFR c m * Real.cos θ + cSinFR c m * Real.sin θ) -
            (-(cCosFInt c m : ℝ) * (cosQNat ((m.1 + 1) * baseAng) : ℝ) -
              (cSinFInt c m : ℝ) * (sinQNat ((m.1 + 1) * baseAng) : ℝ)) / 10000000 =
            -((SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * Real.cos θ) -
            (cCosFInt c m : ℝ) * (Real.cos θ - cQ) -
            ((SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * Real.sin θ) -
            (cSinFInt c m : ℝ) * (Real.sin θ - sQ) := by dsimp [cQ, sQ]; ring
        have ht1 : |-((SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * Real.cos θ)| ≤
            ((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs : ℕ) : ℝ) := by
          rw [abs_neg, abs_mul]
          calc |SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)| * |Real.cos θ|
              ≤ |SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
            _ = |SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)| := mul_one _
            _ ≤ _ := by split_ifs at hcc_err ⊢ <;> push_cast <;> exact hcc_err
        have ht2 : |-((SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * Real.sin θ)| ≤
            ((if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs : ℕ) : ℝ) := by
          rw [abs_neg, abs_mul]
          calc |SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)| * |Real.sin θ|
              ≤ |SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
            _ = |SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)| := mul_one _
            _ ≤ _ := by split_ifs at hcs_err ⊢ <;> push_cast <;> exact hcs_err
        have ht3 : |-(cCosFInt c m : ℝ) * (Real.cos θ - cQ)| ≤ ((cCosFInt c m).natAbs : ℝ) / 10000000 := by
          rw [abs_mul, abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          calc ((cCosFInt c m).natAbs : ℝ) * |Real.cos θ - cQ|
              ≤ ((cCosFInt c m).natAbs : ℝ) * (1 / 10000000) :=
                mul_le_mul_of_nonneg_left hca (Nat.cast_nonneg _)
            _ = ((cCosFInt c m).natAbs : ℝ) / 10000000 := by ring
        have ht4 : |-(cSinFInt c m : ℝ) * (Real.sin θ - sQ)| ≤ ((cSinFInt c m).natAbs : ℝ) / 10000000 := by
          rw [abs_mul, abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          calc ((cSinFInt c m).natAbs : ℝ) * |Real.sin θ - sQ|
              ≤ ((cSinFInt c m).natAbs : ℝ) * (1 / 10000000) :=
                mul_le_mul_of_nonneg_left hsa (Nat.cast_nonneg _)
            _ = ((cSinFInt c m).natAbs : ℝ) / 10000000 := by ring
        have hcdiv := nat_cdiv_ge_sub ((cCosFInt c m).natAbs + (cSinFInt c m).natAbs) 10000000 9999999 (by norm_num) (by norm_num)
        simp only [Nat.cast_add] at hcdiv
        have hle1 := le_abs_self (-((SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * Real.cos θ))
        have hle2 := le_abs_self (-((SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * Real.sin θ))
        have hle3 := le_abs_self (-(cCosFInt c m : ℝ) * (Real.cos θ - cQ))
        have hle4 := le_abs_self (-(cSinFInt c m : ℝ) * (Real.sin θ - sQ))
        linarith [add_div ((cCosFInt c m).natAbs : ℝ) ((cSinFInt c m).natAbs : ℝ) 10000000]
      have hpad_le : (b2Psi : ℝ) * (dF ^ 2 / 8) ≤ (((b2Psi + 8 * dFDen * dFDen - 1) / (8 * dFDen * dFDen) : ℕ) : ℝ) := by
        have h1 := nat_cdiv_ge b2Psi (by positivity : 0 < 8 * dFDen * dFDen)
        have heq : (b2Psi : ℝ) * (dF ^ 2 / 8) = (b2Psi : ℝ) / ((8 * dFDen * dFDen : ℕ) : ℝ) := by
          dsimp [dF]; push_cast; ring
        rw [heq]; exact h1
      have haHiR : (aHi : ℝ) = (polyVal : ℝ) + (tv : ℝ) +
          (((b2Psi + 8 * dFDen * dFDen - 1) / (8 * dFDen * dFDen) : ℕ) : ℝ) + (errPsiVal : ℝ) := by
        dsimp only [aHi, padPsi]
        rw [Int.cast_add, Int.cast_add, Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_add]
        ring
      have hpsi_mul : (NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8)) * SVAL_R =
          SVAL_R * (-((c.nuMassf : ℝ) / SC_R) - ((linF : ℝ) / SVAL_R) * tm) +
          -SVAL_R * (∑ m : Fin 10, (cCosFR c m * Real.cos (omReal (m.1 + 1) * tm) +
            cSinFR c m * Real.sin (omReal (m.1 + 1) * tm))) +
          (b2Psi : ℝ) * (dF ^ 2 / 8) := by
        unfold NegPsi; dsimp [linF]; field_simp [hSpos.ne']; ring
      linarith
    have hb_le : |NegPsi' c tm| ≤ (bHi : ℝ) / SVAL_R := by
      rw [le_div_iff₀ hSpos, ← abs_of_pos hSpos, ← abs_mul]
      have htd_err1 : |(tdRaw : ℝ) / 100000000000000 - (td : ℝ)| ≤ 1 :=
        intFdiv_abs_sub_le tdRaw (by norm_num : 0 < 100000000000000)
      have htd_err2 : |SVAL_R * (∑ m : Fin 10, ((cCosFR c m * Real.sin (omReal (m.1 + 1) * tm) -
          cSinFR c m * Real.cos (omReal (m.1 + 1) * tm)) * omReal (m.1 + 1))) -
          (tdRaw : ℝ) / 100000000000000| ≤ (errPsiDer : ℝ) := by
        have htdRaw_eq : (tdRaw : ℝ) / 100000000000000 = ∑ m : Fin 10,
            (((cCosFInt c m : ℝ) * (sinQNat ((m.1 + 1) * baseAng) : ℝ) -
              (cSinFInt c m : ℝ) * (cosQNat ((m.1 + 1) * baseAng) : ℝ)) *
              (omIntList.getD m.1 0 : ℝ) / 100000000000000) := by
          dsimp [tdRaw, termsF]; rw [evalFDer_eq_sum c ha hb hu hv baseAng]; simp only [Int.ofNat_eq_natCast]; push_cast; rw [Finset.sum_div]
        have herr_eq : (errPsiDer : ℝ) = ∑ m : Fin 10,
            ((((((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs) +
                (if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs)) *
                (omIntList.getD m.1 0 + 1) + 9999999) / 10000000 : ℕ) : ℝ) +
             (((((cCosFInt c m).natAbs + (cSinFInt c m).natAbs) *
                (omIntList.getD m.1 0 + 1 + 10000000) + 99999999999999) / 100000000000000 : ℕ) : ℝ)) := by
          dsimp [errPsiDer, termsF]; rw [sumErrDerF_eq_sum c ha hb hu hv]; push_cast; rfl
        rw [htdRaw_eq, herr_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        have ⟨hca, hcb⟩ := cosQNat_sound ((m.1 + 1) * baseAng)
        have ⟨hsa, hsb⟩ := sinQNat_sound ((m.1 + 1) * baseAng)
        have ⟨hcang, hsang⟩ := hang m
        have ⟨hom_lo, hom_hi⟩ := omIntList_sound m
        have hcc_err := cCosFR_approx c m
        have hcs_err := cSinFR_approx c m
        have hom_nn : 0 ≤ omReal (m.1 + 1) := (omReal_pos (Nat.succ_pos m.1)).le
        rw [hcang, hsang]
        set θ : ℝ := (((m.1 + 1) * baseAng : ℕ) : ℝ) * Real.pi / 1024
        set cQ : ℝ := (cosQNat ((m.1 + 1) * baseAng) : ℝ) / 10000000
        set sQ : ℝ := (sinQNat ((m.1 + 1) * baseAng) : ℝ) / 10000000
        set omQ : ℝ := (omIntList.getD m.1 0 : ℝ) / 10000000
        have hom_ub : omReal (m.1 + 1) ≤ ((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000 := by
          push_cast; linarith
        have hsin_prod : |omReal (m.1 + 1) * Real.sin θ - omQ * sQ| ≤
            ((omIntList.getD m.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000 := by
          have hid : omReal (m.1 + 1) * Real.sin θ - omQ * sQ =
              omReal (m.1 + 1) * (Real.sin θ - sQ) + (omReal (m.1 + 1) - omQ) * sQ := by ring
          rw [hid]
          have h1 : |omReal (m.1 + 1) * (Real.sin θ - sQ)| ≤ omReal (m.1 + 1) * (1 / 10000000) := by
            rw [abs_mul, abs_of_nonneg hom_nn]; exact mul_le_mul_of_nonneg_left hsa hom_nn
          have h2 : |(omReal (m.1 + 1) - omQ) * sQ| ≤ 1 / 10000000 := by
            rw [abs_mul]
            have homd : |omReal (m.1 + 1) - omQ| ≤ 1 / 10000000 := by rw [abs_le]; dsimp [omQ]; constructor <;> linarith
            calc |omReal (m.1 + 1) - omQ| * |sQ|
                ≤ (1 / 10000000) * 1 := mul_le_mul homd hsb (abs_nonneg _) (by norm_num)
              _ = 1 / 10000000 := mul_one _
          have htri := abs_add_le (omReal (m.1 + 1) * (Real.sin θ - sQ)) ((omReal (m.1 + 1) - omQ) * sQ)
          push_cast; linarith
        have hcos_prod : |omReal (m.1 + 1) * Real.cos θ - omQ * cQ| ≤
            ((omIntList.getD m.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000 := by
          have hid : omReal (m.1 + 1) * Real.cos θ - omQ * cQ =
              omReal (m.1 + 1) * (Real.cos θ - cQ) + (omReal (m.1 + 1) - omQ) * cQ := by ring
          rw [hid]
          have h1 : |omReal (m.1 + 1) * (Real.cos θ - cQ)| ≤ omReal (m.1 + 1) * (1 / 10000000) := by
            rw [abs_mul, abs_of_nonneg hom_nn]; exact mul_le_mul_of_nonneg_left hca hom_nn
          have h2 : |(omReal (m.1 + 1) - omQ) * cQ| ≤ 1 / 10000000 := by
            rw [abs_mul]
            have homd : |omReal (m.1 + 1) - omQ| ≤ 1 / 10000000 := by rw [abs_le]; dsimp [omQ]; constructor <;> linarith
            calc |omReal (m.1 + 1) - omQ| * |cQ|
                ≤ (1 / 10000000) * 1 := mul_le_mul homd hcb (abs_nonneg _) (by norm_num)
              _ = 1 / 10000000 := mul_one _
          have htri := abs_add_le (omReal (m.1 + 1) * (Real.cos θ - cQ)) ((omReal (m.1 + 1) - omQ) * cQ)
          push_cast; linarith
        have hterm : SVAL_R * ((cCosFR c m * Real.sin θ - cSinFR c m * Real.cos θ) * omReal (m.1 + 1)) -
            ((cCosFInt c m : ℝ) * (sinQNat ((m.1 + 1) * baseAng) : ℝ) -
              (cSinFInt c m : ℝ) * (cosQNat ((m.1 + 1) * baseAng) : ℝ)) *
              (omIntList.getD m.1 0 : ℝ) / 100000000000000 =
            ((SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.sin θ) -
              (SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.cos θ)) +
            ((cCosFInt c m : ℝ) * (omReal (m.1 + 1) * Real.sin θ - omQ * sQ) -
              (cSinFInt c m : ℝ) * (omReal (m.1 + 1) * Real.cos θ - omQ * cQ)) := by
          dsimp [cQ, sQ, omQ]; ring
        rw [hterm]
        have hpart1 : |(SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.sin θ) -
            (SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.cos θ)| ≤
            ((((((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs) +
                (if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs)) *
                (omIntList.getD m.1 0 + 1) + 9999999) / 10000000 : ℕ) : ℝ)) := by
          have ht1 : |(SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.sin θ)| ≤
              ((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs : ℕ) : ℝ) *
                (((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hom_nn]
            have ha' : |SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)| ≤
                ((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs : ℕ) : ℝ) := by
              split_ifs at hcc_err ⊢ <;> push_cast <;> exact hcc_err
            have hb' : omReal (m.1 + 1) * |Real.sin θ| ≤ ((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000 :=
              (mul_le_of_le_one_right hom_nn (Real.abs_sin_le_one _)).trans hom_ub
            exact mul_le_mul ha' hb' (by positivity) (Nat.cast_nonneg _)
          have ht2 : |(SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.cos θ)| ≤
              ((if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs : ℕ) : ℝ) *
                (((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hom_nn]
            have ha' : |SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)| ≤
                ((if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs : ℕ) : ℝ) := by
              split_ifs at hcs_err ⊢ <;> push_cast <;> exact hcs_err
            have hb' : omReal (m.1 + 1) * |Real.cos θ| ≤ ((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000 :=
              (mul_le_of_le_one_right hom_nn (Real.abs_cos_le_one _)).trans hom_ub
            exact mul_le_mul ha' hb' (by positivity) (Nat.cast_nonneg _)
          have hcdiv := nat_cdiv_ge_sub
            (((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs) +
              (if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs)) *
              (omIntList.getD m.1 0 + 1)) 10000000 9999999 (by norm_num) (by norm_num)
          have htri := abs_sub ((SVAL_R * cCosFR c m - (cCosFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.sin θ))
            ((SVAL_R * cSinFR c m - (cSinFInt c m : ℝ)) * (omReal (m.1 + 1) * Real.cos θ))
          have hsum_eq : ((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs : ℕ) : ℝ) *
              (((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000) +
              ((if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs : ℕ) : ℝ) *
              (((omIntList.getD m.1 0 + 1 : ℕ) : ℝ) / 10000000) =
              ((((if (m.1 + 1) % 2 = 0 then 0 else (c.alpha.getD m.1 0).natAbs) +
                (if (m.1 + 1) % 2 = 0 then 0 else (c.beta.getD m.1 0).natAbs)) *
                (omIntList.getD m.1 0 + 1) : ℕ) : ℝ) / 10000000 := by
            simp only [Nat.cast_mul, Nat.cast_add]; ring
          linarith only [ht1, ht2, htri, hcdiv, hsum_eq]
        have hpart2 : |(cCosFInt c m : ℝ) * (omReal (m.1 + 1) * Real.sin θ - omQ * sQ) -
            (cSinFInt c m : ℝ) * (omReal (m.1 + 1) * Real.cos θ - omQ * cQ)| ≤
            ((((((cCosFInt c m).natAbs + (cSinFInt c m).natAbs) *
                (omIntList.getD m.1 0 + 1 + 10000000) + 99999999999999) / 100000000000000 : ℕ) : ℝ)) := by
          have ht1 : |(cCosFInt c m : ℝ) * (omReal (m.1 + 1) * Real.sin θ - omQ * sQ)| ≤
              ((cCosFInt c m).natAbs : ℝ) * (((omIntList.getD m.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000) := by
            rw [abs_mul, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
            exact mul_le_mul_of_nonneg_left hsin_prod (Nat.cast_nonneg _)
          have ht2 : |(cSinFInt c m : ℝ) * (omReal (m.1 + 1) * Real.cos θ - omQ * cQ)| ≤
              ((cSinFInt c m).natAbs : ℝ) * (((omIntList.getD m.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000) := by
            rw [abs_mul, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
            exact mul_le_mul_of_nonneg_left hcos_prod (Nat.cast_nonneg _)
          have hcdiv := nat_cdiv_ge_sub
            (((cCosFInt c m).natAbs + (cSinFInt c m).natAbs) * (omIntList.getD m.1 0 + 1 + 10000000))
            100000000000000 99999999999999 (by norm_num) (by norm_num)
          have htri := abs_sub ((cCosFInt c m : ℝ) * (omReal (m.1 + 1) * Real.sin θ - omQ * sQ))
            ((cSinFInt c m : ℝ) * (omReal (m.1 + 1) * Real.cos θ - omQ * cQ))
          have hsum_eq : ((cCosFInt c m).natAbs : ℝ) * (((omIntList.getD m.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000) +
              ((cSinFInt c m).natAbs : ℝ) * (((omIntList.getD m.1 0 + 1 + 10000000 : ℕ) : ℝ) / 100000000000000) =
              ((((cCosFInt c m).natAbs + (cSinFInt c m).natAbs) * (omIntList.getD m.1 0 + 1 + 10000000) : ℕ) : ℝ) /
                100000000000000 := by
            simp only [Nat.cast_mul, Nat.cast_add]; ring
          linarith only [ht1, ht2, htri, hcdiv, hsum_eq]
        exact (abs_add_le _ _).trans (add_le_add hpart1 hpart2)
      have htot : |NegPsi' c tm * SVAL_R - (-(linF : ℝ) + (td : ℝ))| ≤ 1 + (errPsiDer : ℝ) := by
        have hrew : NegPsi' c tm * SVAL_R - (-(linF : ℝ) + (td : ℝ)) =
            (SVAL_R * (∑ m : Fin 10, ((cCosFR c m * Real.sin (omReal (m.1 + 1) * tm) -
              cSinFR c m * Real.cos (omReal (m.1 + 1) * tm)) * omReal (m.1 + 1))) -
              (tdRaw : ℝ) / 100000000000000) +
            ((tdRaw : ℝ) / 100000000000000 - (td : ℝ)) := by
          unfold NegPsi'; dsimp [linF]
          rw [add_mul, neg_mul, div_mul_cancel₀ _ hSpos.ne', mul_comm _ SVAL_R]
          ring
        rw [hrew]
        have h := (abs_add_le _ _).trans (add_le_add htd_err2 htd_err1)
        linarith only [h]
      have hbHiR : (bHi : ℝ) = |-(linF : ℝ) + (td : ℝ)| + 1 + (errPsiDer : ℝ) := by
        dsimp [bHi]; push_cast
        have : ((-linF + td).natAbs : ℝ) = |-(linF : ℝ) + (td : ℝ)| := by
          rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs, Int.cast_add, Int.cast_neg]
        linarith
      have hsub := abs_sub_abs_le_abs_sub (NegPsi' c tm * SVAL_R) (-(linF : ℝ) + (td : ℝ))
      linarith
    exact (uArea_mono ha_le (abs_nonneg _) hb_le hdF_real_pos).trans (upperIntPos_sound aHi bHi dFDen hdF_pos hSpos)

/- Subsection 6F: Discrete Master Dual Identity and cert_sound -/

private lemma cert_L_lower (c : Cert)
    (haLen : c.alpha.length = 10) (huLen : c.u.length = 10) (hvLen : c.v.length = 10)
    (hnuElo : 0 ≤ c.nuElo) (hnuEhi : 0 ≤ c.nuEhi) (hnuMhi : 0 ≤ c.nuMhi) (hnuMlo : 0 ≤ c.nuMlo)
    (hgamma : 0 ≤ c.gamma) (hnuPlo : 0 ≤ c.nuPlo) (hnuPhi : 0 ≤ c.nuPhi)
    (hnuQlo : 0 ≤ c.nuQlo) (hnuQhi : 0 ≤ c.nuQhi)
    (halpha_nnR : ∀ i : Fin 10, 0 ≤ alphaR c i)
    (n : ℕ) (hn : 20 ≤ n) (A B : Finset ℤ)
    (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ))) (hcard : A.card = B.card)
    (hElo : (c.h1 : ℝ) / 100 ≤ EVal n A) (hEhi : EVal n A ≤ (c.h2 : ℝ) / 100)
    (hPlo : (c.p1 : ℝ) / 100 ≤ CVal n A Real.pi) (hPhi : CVal n A Real.pi ≤ (c.p2 : ℝ) / 100)
    (hQlo : (c.q1 : ℝ) / 100 ≤ SVal n A Real.pi) (hQhi : SVal n A Real.pi ≤ (c.q2 : ℝ) / 100) :
    let lam2 := c.nuMhi - c.nuMlo
    let quadTerms : Int := sumQuadTerms c.alpha c.u c.v 0
    let constRhs : Int :=
      (-c.nuMassM - c.nuMassf) * 10000000
      + (c.nuElo * c.h1 - c.nuEhi * c.h2) * 100000
      + intFdiv (-2 * lam2 * 10000000) 3
      + intFdiv (c.nuMhi * c.h1 * c.h2 * 10000000) 20000
      + intFdiv (-c.nuMlo * c.e0 * c.e0 * 10000000) 2000000000000
      + quadTerms
      + intFdiv (c.gamma * (c.p1 * c.p2 + c.q1 * c.q2) * 10000000) 10000
      + (c.nuPlo * c.p1 - c.nuPhi * c.p2 + c.nuQlo * c.q1 - c.nuQhi * c.q2) * 100000
    let C_D : ℝ := |((lam2 : ℝ) / SC_R)| / 6 +
      ∑ i : Fin 10, (|alphaR c i| + |betaR c i|) * (omReal (i.1 + 1) / 10)
    (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) ≤
      (1 / (n : ℝ)) * ∑ k ∈ KSet n, Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k +
      (1 / (n : ℝ)) * ∑ a ∈ A, NegPsi c (uCoord n a) := by
  intro lam2 quadTerms constRhs C_D
  set linF : Int := linFInt c
  have hSpos : (0 : ℝ) < SVAL_R := by norm_num [SVAL_R]
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by positivity
  have ⟨hAcard, _⟩ := card_eq_n hdisj hunion hcard
  set E : ℝ := EVal n A
  set p : ℝ := CVal n A Real.pi
  set q : ℝ := SVal n A Real.pi
  have hPhi_sum : (1 / (n : ℝ)) * ∑ k ∈ KSet n, Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k =
      -((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * E -
      (((lam2 : ℝ) / SC_R)) * (2 / 3 + E ^ 2 / 2 - 1 / (6 * (n : ℝ) ^ 2)) +
      ∑ i : Fin 10, (cCosMR c i * (DVal n (omReal (i.1 + 1)) * CVal n A (omReal (i.1 + 1)) -
          (CVal n A (omReal (i.1 + 1))) ^ 2 - (SVal n A (omReal (i.1 + 1))) ^ 2) +
        cSinMR c i * (DVal n (omReal (i.1 + 1)) * SVal n A (omReal (i.1 + 1)))) := by
    have h1 := mass_eq hn1 hdisj hunion hcard
    have h2 := mean_eq hn1 hdisj hunion hcard
    have h3 := mom2_eq hn1 hdisj hunion hcard
    unfold Phi
    have hexp : ∀ k : ℤ,
        (-((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * ((k : ℝ) / (n : ℝ)) -
          (((c.nuMhi - c.nuMlo : ℤ) : ℝ) / SC_R) * ((k : ℝ) / (n : ℝ)) ^ 2 +
          ∑ i : Fin 10, (cCosMR c i * Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) +
            cSinMR c i * Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))))) * mVal n A B k =
        -((c.nuMassM : ℝ) / SC_R) * mVal n A B k -
        ((c.nuEM : ℝ) / SC_R) * (((k : ℝ) / (n : ℝ)) * mVal n A B k) -
        ((lam2 : ℝ) / SC_R) * ((((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k) +
        ∑ i : Fin 10, (cCosMR c i * (Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) +
          cSinMR c i * (Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k)) := by
      intro k; dsimp [lam2]; rw [add_mul, Finset.sum_mul]
      have : ∑ i : Fin 10, (cCosMR c i * Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) +
            cSinMR c i * Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ)))) * mVal n A B k =
          ∑ i : Fin 10, (cCosMR c i * (Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) +
            cSinMR c i * (Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k)) :=
        Finset.sum_congr rfl fun _ _ => by ring
      rw [this]; ring
    simp_rw [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have htrig_comm : ∀ i : Fin 10,
        ∑ k ∈ KSet n, (cCosMR c i * (Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) +
          cSinMR c i * (Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k)) =
        cCosMR c i * (∑ k ∈ KSet n, Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) +
        cSinMR c i * (∑ k ∈ KSet n, Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) := fun i => by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp_rw [htrig_comm]
    rw [mul_add, mul_sub, mul_sub]
    have ht1 : (1 / (n : ℝ)) * (-((c.nuMassM : ℝ) / SC_R) * ∑ k ∈ KSet n, mVal n A B k) = -((c.nuMassM : ℝ) / SC_R) := by
      rw [show (1 / (n : ℝ)) * (-((c.nuMassM : ℝ) / SC_R) * ∑ k ∈ KSet n, mVal n A B k) =
          -((c.nuMassM : ℝ) / SC_R) * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, mVal n A B k) by ring, h1, mul_one]
    have ht2 : (1 / (n : ℝ)) * (((c.nuEM : ℝ) / SC_R) * ∑ k ∈ KSet n, ((k : ℝ) / (n : ℝ)) * mVal n A B k) =
        ((c.nuEM : ℝ) / SC_R) * E := by
      rw [show (1 / (n : ℝ)) * (((c.nuEM : ℝ) / SC_R) * ∑ k ∈ KSet n, ((k : ℝ) / (n : ℝ)) * mVal n A B k) =
          ((c.nuEM : ℝ) / SC_R) * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, ((k : ℝ) / (n : ℝ)) * mVal n A B k) by ring, h2]
    have ht3 : (1 / (n : ℝ)) * (((lam2 : ℝ) / SC_R) * ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k) =
        ((lam2 : ℝ) / SC_R) * (2 / 3 + E ^ 2 / 2 - 1 / (6 * (n : ℝ) ^ 2)) := by
      rw [show (1 / (n : ℝ)) * (((lam2 : ℝ) / SC_R) * ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k) =
          ((lam2 : ℝ) / SC_R) * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, (((k : ℝ) / (n : ℝ)) ^ 2) * mVal n A B k) by ring, h3]
    rw [ht1, ht2, ht3]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add]
    have hc_i := cos_eq hn1 hdisj hunion hcard (omReal (i.1 + 1))
    have hs_i := sin_eq hn1 hdisj hunion hcard (omReal (i.1 + 1))
    rw [show (1 / (n : ℝ)) * (cCosMR c i * ∑ k ∈ KSet n, Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) =
        cCosMR c i * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, Real.cos (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) by ring, hc_i]
    rw [show (1 / (n : ℝ)) * (cSinMR c i * ∑ k ∈ KSet n, Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) =
        cSinMR c i * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, Real.sin (omReal (i.1 + 1) * ((k : ℝ) / (n : ℝ))) * mVal n A B k) by ring, hs_i]
  have hPsi_sum : (1 / (n : ℝ)) * ∑ a ∈ A, NegPsi c (uCoord n a) =
      -((c.nuMassf : ℝ) / SC_R) - ((linF : ℝ) / SVAL_R) * (E / 2) -
      ∑ i : Fin 10, (cCosFR c i * CVal n A (omReal (i.1 + 1)) + cSinFR c i * SVal n A (omReal (i.1 + 1))) := by
    unfold NegPsi
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have htrig_comm : ∀ i : Fin 10,
        ∑ a ∈ A, (cCosFR c i * Real.cos (omReal (i.1 + 1) * uCoord n a) +
          cSinFR c i * Real.sin (omReal (i.1 + 1) * uCoord n a)) =
        cCosFR c i * (∑ a ∈ A, Real.cos (omReal (i.1 + 1) * uCoord n a)) +
        cSinFR c i * (∑ a ∈ A, Real.sin (omReal (i.1 + 1) * uCoord n a)) := fun i => by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp_rw [htrig_comm]
    rw [mul_sub, mul_sub]
    have h1 : (1 / (n : ℝ)) * ((A.card : ℝ) * -((c.nuMassf : ℝ) / SC_R)) = -((c.nuMassf : ℝ) / SC_R) := by
      rw [hAcard]; field_simp
    have h2 : (1 / (n : ℝ)) * (((linFInt c : ℝ) / SVAL_R) * ∑ a ∈ A, uCoord n a) = ((linF : ℝ) / SVAL_R) * (E / 2) := by
      dsimp [E, EVal, linF]; field_simp
    rw [h1, h2]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold CVal SVal; ring
  -- Now compare exact algebraic RHS with constRhs / SVAL_R - C_D / n!
  have hconst_le : (constRhs : ℝ) / SVAL_R ≤
      -((c.nuMassM : ℝ) / SC_R) - ((c.nuMassf : ℝ) / SC_R) +
      ((c.nuElo : ℝ) / SC_R) * ((c.h1 : ℝ) / 100) - ((c.nuEhi : ℝ) / SC_R) * ((c.h2 : ℝ) / 100) -
      (2 / 3 : ℝ) * ((lam2 : ℝ) / SC_R) +
      ((c.nuMhi : ℝ) / SC_R) * ((c.h1 : ℝ) / 100) * ((c.h2 : ℝ) / 100) / 2 -
      ((c.nuMlo : ℝ) / SC_R) * ((c.e0 : ℝ) / SC_R) ^ 2 / 2 -
      (∑ i : Fin 10, alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2)) +
      ((c.gamma : ℝ) / SC_R) * (((c.p1 : ℝ) / 100) * ((c.p2 : ℝ) / 100) + ((c.q1 : ℝ) / 100) * ((c.q2 : ℝ) / 100)) +
      ((c.nuPlo : ℝ) / SC_R) * ((c.p1 : ℝ) / 100) - ((c.nuPhi : ℝ) / SC_R) * ((c.p2 : ℝ) / 100) +
      ((c.nuQlo : ℝ) / SC_R) * ((c.q1 : ℝ) / 100) - ((c.nuQhi : ℝ) / SC_R) * ((c.q2 : ℝ) / 100) := by
    have hf1 := intFdiv_le (-2 * lam2 * 10000000) (by norm_num : 0 < 3)
    have hf2 := intFdiv_le (c.nuMhi * c.h1 * c.h2 * 10000000) (by norm_num : 0 < 20000)
    have hf3 := intFdiv_le (-c.nuMlo * c.e0 * c.e0 * 10000000) (by norm_num : 0 < 2000000000000)
    have hf4 := intFdiv_le (c.gamma * (c.p1 * c.p2 + c.q1 * c.q2) * 10000000) (by norm_num : 0 < 10000)
    have hfq : (quadTerms : ℝ) / SVAL_R ≤ -(∑ i : Fin 10, alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2)) := by
      dsimp [quadTerms]; rw [sumQuadTerms_eq_sum c haLen huLen hvLen]
      push_cast; rw [Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hfi := intFdiv_le (-c.alpha.getD i.1 0 *
        (c.u.getD i.1 0 * c.u.getD i.1 0 + c.v.getD i.1 0 * c.v.getD i.1 0) * 10000000)
        (by norm_num : 0 < 1000000000000)
      have hdiv := div_le_div_of_nonneg_right hfi hSpos.le
      have heq : (((-c.alpha.getD i.1 0 * (c.u.getD i.1 0 * c.u.getD i.1 0 + c.v.getD i.1 0 * c.v.getD i.1 0) * 10000000 : ℤ) : ℝ) /
          (1000000000000 : ℝ)) / SVAL_R = -(alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2)) := by
        unfold alphaR uR vR SC_R SVAL_R; push_cast; ring
      linarith
    dsimp [constRhs]
    push_cast at hf1 hf2 hf3 hf4 ⊢
    rw [div_le_iff₀ hSpos]
    have hfq' : (quadTerms : ℝ) ≤ -(∑ i : Fin 10, alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2)) * SVAL_R := by
      rwa [div_le_iff₀ hSpos] at hfq
    unfold SC_R SVAL_R at *
    linarith only [hf1, hf2, hf3, hf4, hfq']
  -- Show the exact algebraic excess + DVal approximation error is >= -C_D / n!
  have hL_lower : (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) ≤
      (1 / (n : ℝ)) * ∑ k ∈ KSet n, Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k +
      (1 / (n : ℝ)) * ∑ a ∈ A, NegPsi c (uCoord n a) := by
    rw [hPhi_sum, hPsi_sum]
    -- Bound the DVal - dCont error term and the 1/(6n^2) term:
    have hn_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      simpa [sq] using mul_le_mul_of_nonneg_left h1 hn_pos.le
    have hD_err : ∑ i : Fin 10,
        (alphaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * CVal n A (omReal (i.1 + 1)) +
         betaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * SVal n A (omReal (i.1 + 1))) ≥
        -(∑ i : Fin 10, (|alphaR c i| + |betaR c i|) * (omReal (i.1 + 1) / 10)) / (n : ℝ) := by
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hom_pos : 0 < omReal (i.1 + 1) := omReal_pos (Nat.succ_pos i.1)
      have hom_le_n : omReal (i.1 + 1) ≤ (n : ℝ) := by
        have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_d20]
        have hi : ((i.1 + 1 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast Nat.succ_le_of_lt i.2
        have hn20 : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hm1 : ((i.1 + 1 : ℕ) : ℝ) * Real.pi ≤ 10 * 4 := mul_le_mul hi hpi Real.pi_pos.le (by norm_num)
        unfold omReal; linarith
      have hda := DVal_approx hn1 hom_pos hom_le_n
      have hdcont_eq : dCont (i.1 + 1) = 2 * Real.sin (omReal (i.1 + 1)) / omReal (i.1 + 1) := by
        unfold dCont; rw [if_neg (Nat.succ_ne_zero _)]
      rw [← hdcont_eq, abs_sub_comm] at hda
      have hC_le1 : |CVal n A (omReal (i.1 + 1))| ≤ 1 := by
        unfold CVal
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
        calc (1 / (n : ℝ)) * |∑ a ∈ A, Real.cos (omReal (i.1 + 1) * uCoord n a)|
            ≤ (1 / (n : ℝ)) * ∑ a ∈ A, |Real.cos (omReal (i.1 + 1) * uCoord n a)| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
          _ ≤ (1 / (n : ℝ)) * ∑ _a ∈ A, (1 : ℝ) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => Real.abs_cos_le_one _) (by positivity)
          _ = 1 := by simp [hAcard]; field_simp
      have hS_le1 : |SVal n A (omReal (i.1 + 1))| ≤ 1 := by
        unfold SVal
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
        calc (1 / (n : ℝ)) * |∑ a ∈ A, Real.sin (omReal (i.1 + 1) * uCoord n a)|
            ≤ (1 / (n : ℝ)) * ∑ a ∈ A, |Real.sin (omReal (i.1 + 1) * uCoord n a)| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
          _ ≤ (1 / (n : ℝ)) * ∑ _a ∈ A, (1 : ℝ) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => Real.abs_sin_le_one _) (by positivity)
          _ = 1 := by simp [hAcard]; field_simp
      have h1 : |alphaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * CVal n A (omReal (i.1 + 1))| ≤
          |alphaR c i| * (omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2)) := by
        rw [abs_mul, abs_mul]
        calc |alphaR c i| * |dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))| * |CVal n A (omReal (i.1 + 1))|
            ≤ |alphaR c i| * (omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2)) * 1 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hda (abs_nonneg _)) hC_le1 (abs_nonneg _) (by positivity)
          _ = |alphaR c i| * (omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2)) := mul_one _
      have h2 : |betaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * SVal n A (omReal (i.1 + 1))| ≤
          |betaR c i| * (omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2)) := by
        rw [abs_mul, abs_mul]
        calc |betaR c i| * |dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))| * |SVal n A (omReal (i.1 + 1))|
            ≤ |betaR c i| * (omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2)) * 1 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hda (abs_nonneg _)) hS_le1 (abs_nonneg _) (by positivity)
          _ = |betaR c i| * (omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2)) := mul_one _
      have hdiv_le : omReal (i.1 + 1) / (10 * (n : ℝ) ^ 2) ≤ omReal (i.1 + 1) / 10 / (n : ℝ) := by
        rw [div_div]
        exact div_le_div_of_nonneg_left hom_pos.le (by positivity) (mul_le_mul_of_nonneg_left hn_sq (by norm_num))
      have hneg1 := neg_abs_le (alphaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * CVal n A (omReal (i.1 + 1)))
      have hneg2 := neg_abs_le (betaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * SVal n A (omReal (i.1 + 1)))
      have hmul1 := mul_le_mul_of_nonneg_left hdiv_le (abs_nonneg (alphaR c i))
      have hmul2 := mul_le_mul_of_nonneg_left hdiv_le (abs_nonneg (betaR c i))
      have hring : -((|alphaR c i| + |betaR c i|) * (omReal (i.1 + 1) / 10) / (n : ℝ)) =
          -(|alphaR c i| * (omReal (i.1 + 1) / 10 / (n : ℝ)) + |betaR c i| * (omReal (i.1 + 1) / 10 / (n : ℝ))) := by ring
      linarith only [h1, h2, hneg1, hneg2, hmul1, hmul2, hring]
    have hlam_err : ((lam2 : ℝ) / SC_R) * (1 / (6 * (n : ℝ) ^ 2)) ≥ -(|((lam2 : ℝ) / SC_R)| / 6) / (n : ℝ) := by
      have hdiv_le : 1 / (6 * (n : ℝ) ^ 2) ≤ 1 / (6 * (n : ℝ)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hn_sq (by norm_num))
      have h1 : |((lam2 : ℝ) / SC_R) * (1 / (6 * (n : ℝ) ^ 2))| ≤ |((lam2 : ℝ) / SC_R)| / 6 / (n : ℝ) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (6 * (n : ℝ) ^ 2))]
        calc |((lam2 : ℝ) / SC_R)| * (1 / (6 * (n : ℝ) ^ 2))
            ≤ |((lam2 : ℝ) / SC_R)| * (1 / (6 * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hdiv_le (abs_nonneg _)
          _ = |((lam2 : ℝ) / SC_R)| / 6 / (n : ℝ) := by ring
      rw [neg_div]
      linarith only [h1, neg_abs_le (((lam2 : ℝ) / SC_R) * (1 / (6 * (n : ℝ) ^ 2)))]
    -- Nonnegativity of all box + quadratic slack terms!
    have hquad_nn : 0 ≤ ∑ i : Fin 10, alphaR c i *
        ((CVal n A (omReal (i.1 + 1)) - uR c i) ^ 2 + (SVal n A (omReal (i.1 + 1)) - vR c i) ^ 2) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (halpha_nnR i) (by positivity)
    have hbox_nn : 0 ≤
        ((c.nuElo : ℝ) / SC_R) * (E - (c.h1 : ℝ) / 100) +
        ((c.nuEhi : ℝ) / SC_R) * ((c.h2 : ℝ) / 100 - E) +
        ((c.nuMhi : ℝ) / SC_R) * ((E - (c.h1 : ℝ) / 100) * ((c.h2 : ℝ) / 100 - E) / 2) +
        ((c.nuMlo : ℝ) / SC_R) * ((E - (c.e0 : ℝ) / SC_R) ^ 2 / 2) +
        ((c.gamma : ℝ) / SC_R) * ((p - (c.p1 : ℝ) / 100) * ((c.p2 : ℝ) / 100 - p) +
          (q - (c.q1 : ℝ) / 100) * ((c.q2 : ℝ) / 100 - q)) +
        ((c.nuPlo : ℝ) / SC_R) * (p - (c.p1 : ℝ) / 100) +
        ((c.nuPhi : ℝ) / SC_R) * ((c.p2 : ℝ) / 100 - p) +
        ((c.nuQlo : ℝ) / SC_R) * (q - (c.q1 : ℝ) / 100) +
        ((c.nuQhi : ℝ) / SC_R) * ((c.q2 : ℝ) / 100 - q) := by
      have hSC : (0 : ℝ) < SC_R := by norm_num [SC_R]
      have h1 : (0 : ℝ) ≤ (c.nuElo : ℝ) := by exact_mod_cast hnuElo
      have h2 : (0 : ℝ) ≤ (c.nuEhi : ℝ) := by exact_mod_cast hnuEhi
      have h3 : (0 : ℝ) ≤ (c.nuMhi : ℝ) := by exact_mod_cast hnuMhi
      have h4 : (0 : ℝ) ≤ (c.nuMlo : ℝ) := by exact_mod_cast hnuMlo
      have h5 : (0 : ℝ) ≤ (c.gamma : ℝ) := by exact_mod_cast hgamma
      have h6 : (0 : ℝ) ≤ (c.nuPlo : ℝ) := by exact_mod_cast hnuPlo
      have h7 : (0 : ℝ) ≤ (c.nuPhi : ℝ) := by exact_mod_cast hnuPhi
      have h8 : (0 : ℝ) ≤ (c.nuQlo : ℝ) := by exact_mod_cast hnuQlo
      have h9 : (0 : ℝ) ≤ (c.nuQhi : ℝ) := by exact_mod_cast hnuQhi
      have t1 : 0 ≤ ((c.nuElo : ℝ) / SC_R) * (E - (c.h1 : ℝ) / 100) := mul_nonneg (by positivity) (sub_nonneg.mpr hElo)
      have t2 : 0 ≤ ((c.nuEhi : ℝ) / SC_R) * ((c.h2 : ℝ) / 100 - E) := mul_nonneg (by positivity) (sub_nonneg.mpr hEhi)
      have t3 : 0 ≤ ((c.nuMhi : ℝ) / SC_R) * ((E - (c.h1 : ℝ) / 100) * ((c.h2 : ℝ) / 100 - E) / 2) :=
        mul_nonneg (by positivity) (div_nonneg (mul_nonneg (sub_nonneg.mpr hElo) (sub_nonneg.mpr hEhi)) (by norm_num))
      have t4 : 0 ≤ ((c.nuMlo : ℝ) / SC_R) * ((E - (c.e0 : ℝ) / SC_R) ^ 2 / 2) := mul_nonneg (by positivity) (by positivity)
      have t5 : 0 ≤ ((c.gamma : ℝ) / SC_R) * ((p - (c.p1 : ℝ) / 100) * ((c.p2 : ℝ) / 100 - p) +
          (q - (c.q1 : ℝ) / 100) * ((c.q2 : ℝ) / 100 - q)) :=
        mul_nonneg (by positivity) (add_nonneg (mul_nonneg (sub_nonneg.mpr hPlo) (sub_nonneg.mpr hPhi))
          (mul_nonneg (sub_nonneg.mpr hQlo) (sub_nonneg.mpr hQhi)))
      have t6 : 0 ≤ ((c.nuPlo : ℝ) / SC_R) * (p - (c.p1 : ℝ) / 100) := mul_nonneg (by positivity) (sub_nonneg.mpr hPlo)
      have t7 : 0 ≤ ((c.nuPhi : ℝ) / SC_R) * ((c.p2 : ℝ) / 100 - p) := mul_nonneg (by positivity) (sub_nonneg.mpr hPhi)
      have t8 : 0 ≤ ((c.nuQlo : ℝ) / SC_R) * (q - (c.q1 : ℝ) / 100) := mul_nonneg (by positivity) (sub_nonneg.mpr hQlo)
      have t9 : 0 ≤ ((c.nuQhi : ℝ) / SC_R) * ((c.q2 : ℝ) / 100 - q) := mul_nonneg (by positivity) (sub_nonneg.mpr hQhi)
      linarith only [t1, t2, t3, t4, t5, t6, t7, t8, t9]
    -- Verify the exact Fourier sum identity!
    have hfour_id :
        ∑ i : Fin 10, (cCosMR c i * (DVal n (omReal (i.1 + 1)) * CVal n A (omReal (i.1 + 1)) -
            (CVal n A (omReal (i.1 + 1))) ^ 2 - (SVal n A (omReal (i.1 + 1))) ^ 2) +
          cSinMR c i * (DVal n (omReal (i.1 + 1)) * SVal n A (omReal (i.1 + 1)))) -
        ∑ i : Fin 10, (cCosFR c i * CVal n A (omReal (i.1 + 1)) + cSinFR c i * SVal n A (omReal (i.1 + 1))) =
        (∑ i : Fin 10, alphaR c i * ((CVal n A (omReal (i.1 + 1)) - uR c i) ^ 2 + (SVal n A (omReal (i.1 + 1)) - vR c i) ^ 2)) -
        (∑ i : Fin 10, alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2)) +
        (∑ i : Fin 10, (alphaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * CVal n A (omReal (i.1 + 1)) +
          betaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * SVal n A (omReal (i.1 + 1)))) +
        (((c.gamma : ℝ) / SC_R) * (-p ^ 2 - q ^ 2 + ((c.p1 : ℝ) / 100 + (c.p2 : ℝ) / 100) * p +
          ((c.q1 : ℝ) / 100 + (c.q2 : ℝ) / 100) * q) +
          ((c.nuPlo : ℝ) / SC_R - (c.nuPhi : ℝ) / SC_R) * p +
          ((c.nuQlo : ℝ) / SC_R - (c.nuQhi : ℝ) / SC_R) * q) := by
      have hom2 : omReal (1 + 1) = Real.pi := by unfold omReal; norm_num
      have hD2 : DVal n (omReal (1 + 1)) = 0 := by rw [hom2]; exact DVal_pi_eq_zero hn1
      have hp_eq : CVal n A (omReal (1 + 1)) = p := by rw [hom2]
      have hq_eq : SVal n A (omReal (1 + 1)) = q := by rw [hom2]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hsplit1 : ∀ i : Fin 10,
          (cCosMR c i * (DVal n (omReal (i.1 + 1)) * CVal n A (omReal (i.1 + 1)) -
              (CVal n A (omReal (i.1 + 1))) ^ 2 - (SVal n A (omReal (i.1 + 1))) ^ 2) +
            cSinMR c i * (DVal n (omReal (i.1 + 1)) * SVal n A (omReal (i.1 + 1)))) -
          (cCosFR c i * CVal n A (omReal (i.1 + 1)) + cSinFR c i * SVal n A (omReal (i.1 + 1))) =
          (alphaR c i * ((CVal n A (omReal (i.1 + 1)) - uR c i) ^ 2 + (SVal n A (omReal (i.1 + 1)) - vR c i) ^ 2) -
            alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2) +
            (alphaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * CVal n A (omReal (i.1 + 1)) +
              betaR c i * (dCont (i.1 + 1) - DVal n (omReal (i.1 + 1))) * SVal n A (omReal (i.1 + 1)))) +
          if i = ⟨1, by omega⟩ then
            ((c.gamma : ℝ) / SC_R) * (-p ^ 2 - q ^ 2 + ((c.p1 : ℝ) / 100 + (c.p2 : ℝ) / 100) * p +
              ((c.q1 : ℝ) / 100 + (c.q2 : ℝ) / 100) * q) +
            ((c.nuPlo : ℝ) / SC_R - (c.nuPhi : ℝ) / SC_R) * p +
            ((c.nuQlo : ℝ) / SC_R - (c.nuQhi : ℝ) / SC_R) * q
          else 0 := by
        intro i
        by_cases hi1 : i = ⟨1, by omega⟩
        · subst hi1
          simp only [if_true]
          unfold cCosMR cSinMR cCosFR cSinFR
          simp only [if_true, hD2, hp_eq, hq_eq, Int.cast_add]
          ring
        · have hval : i.1 ≠ 1 := fun h => hi1 (Fin.ext h)
          simp only [if_neg hi1]
          unfold cCosMR cSinMR cCosFR cSinFR
          simp only [if_neg hval]
          ring
      simp_rw [hsplit1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hlin_id : -((c.nuEM : ℝ) / SC_R) * E - ((lam2 : ℝ) / SC_R) * (2 / 3 + E ^ 2 / 2 - 1 / (6 * (n : ℝ) ^ 2)) -
        ((linF : ℝ) / SVAL_R) * (E / 2) =
        -(2 / 3 : ℝ) * ((lam2 : ℝ) / SC_R) + ((lam2 : ℝ) / SC_R) * (1 / (6 * (n : ℝ) ^ 2)) +
        ((c.nuElo : ℝ) / SC_R) * (E - (c.h1 : ℝ) / 100) + ((c.nuElo : ℝ) / SC_R) * ((c.h1 : ℝ) / 100) +
        ((c.nuEhi : ℝ) / SC_R) * ((c.h2 : ℝ) / 100 - E) - ((c.nuEhi : ℝ) / SC_R) * ((c.h2 : ℝ) / 100) +
        ((c.nuMhi : ℝ) / SC_R) * ((E - (c.h1 : ℝ) / 100) * ((c.h2 : ℝ) / 100 - E) / 2) +
        ((c.nuMhi : ℝ) / SC_R) * ((c.h1 : ℝ) / 100) * ((c.h2 : ℝ) / 100) / 2 +
        ((c.nuMlo : ℝ) / SC_R) * ((E - (c.e0 : ℝ) / SC_R) ^ 2 / 2) -
        ((c.nuMlo : ℝ) / SC_R) * ((c.e0 : ℝ) / SC_R) ^ 2 / 2 := by
      dsimp [lam2, linF, linFInt, SC_R, SVAL_R]
      push_cast; ring
    have hpq_id : ((c.gamma : ℝ) / SC_R) * (-p ^ 2 - q ^ 2 + ((c.p1 : ℝ) / 100 + (c.p2 : ℝ) / 100) * p +
          ((c.q1 : ℝ) / 100 + (c.q2 : ℝ) / 100) * q) +
        ((c.nuPlo : ℝ) / SC_R - (c.nuPhi : ℝ) / SC_R) * p +
        ((c.nuQlo : ℝ) / SC_R - (c.nuQhi : ℝ) / SC_R) * q =
        ((c.gamma : ℝ) / SC_R) * ((p - (c.p1 : ℝ) / 100) * ((c.p2 : ℝ) / 100 - p) +
          (q - (c.q1 : ℝ) / 100) * ((c.q2 : ℝ) / 100 - q)) +
        ((c.gamma : ℝ) / SC_R) * (((c.p1 : ℝ) / 100) * ((c.p2 : ℝ) / 100) + ((c.q1 : ℝ) / 100) * ((c.q2 : ℝ) / 100)) +
        ((c.nuPlo : ℝ) / SC_R) * (p - (c.p1 : ℝ) / 100) + ((c.nuPlo : ℝ) / SC_R) * ((c.p1 : ℝ) / 100) +
        ((c.nuPhi : ℝ) / SC_R) * ((c.p2 : ℝ) / 100 - p) - ((c.nuPhi : ℝ) / SC_R) * ((c.p2 : ℝ) / 100) +
        ((c.nuQlo : ℝ) / SC_R) * (q - (c.q1 : ℝ) / 100) + ((c.nuQlo : ℝ) / SC_R) * ((c.q1 : ℝ) / 100) +
        ((c.nuQhi : ℝ) / SC_R) * ((c.q2 : ℝ) / 100 - q) - ((c.nuQhi : ℝ) / SC_R) * ((c.q2 : ℝ) / 100) := by
      ring
    have hCD_div : C_D / (n : ℝ) = (|((lam2 : ℝ) / SC_R)| / 6) / (n : ℝ) +
        (∑ i : Fin 10, (|alphaR c i| + |betaR c i|) * (omReal (i.1 + 1) / 10)) / (n : ℝ) := by
      dsimp [C_D]; rw [add_div]
    have halg : (-((c.nuMassM : ℝ) / SC_R) - ((c.nuEM : ℝ) / SC_R) * E -
        ((lam2 : ℝ) / SC_R) * (2 / 3 + E ^ 2 / 2 - 1 / (6 * (n : ℝ) ^ 2)) +
        ∑ i : Fin 10, (cCosMR c i * (DVal n (omReal (i.1 + 1)) * CVal n A (omReal (i.1 + 1)) -
            (CVal n A (omReal (i.1 + 1))) ^ 2 - (SVal n A (omReal (i.1 + 1))) ^ 2) +
          cSinMR c i * (DVal n (omReal (i.1 + 1)) * SVal n A (omReal (i.1 + 1))))) +
        (-((c.nuMassf : ℝ) / SC_R) - ((linF : ℝ) / SVAL_R) * (E / 2) -
        ∑ i : Fin 10, (cCosFR c i * CVal n A (omReal (i.1 + 1)) + cSinFR c i * SVal n A (omReal (i.1 + 1)))) =
        (-((c.nuMassM : ℝ) / SC_R) - ((c.nuMassf : ℝ) / SC_R)) +
        (-((c.nuEM : ℝ) / SC_R) * E - ((lam2 : ℝ) / SC_R) * (2 / 3 + E ^ 2 / 2 - 1 / (6 * (n : ℝ) ^ 2)) -
          ((linF : ℝ) / SVAL_R) * (E / 2)) +
        (∑ i : Fin 10, (cCosMR c i * (DVal n (omReal (i.1 + 1)) * CVal n A (omReal (i.1 + 1)) -
            (CVal n A (omReal (i.1 + 1))) ^ 2 - (SVal n A (omReal (i.1 + 1))) ^ 2) +
          cSinMR c i * (DVal n (omReal (i.1 + 1)) * SVal n A (omReal (i.1 + 1)))) -
        ∑ i : Fin 10, (cCosFR c i * CVal n A (omReal (i.1 + 1)) + cSinFR c i * SVal n A (omReal (i.1 + 1)))) := by
      ring
    have hconst_part : (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) ≤
        (-((c.nuMassM : ℝ) / SC_R) - ((c.nuMassf : ℝ) / SC_R) +
        ((c.nuElo : ℝ) / SC_R) * ((c.h1 : ℝ) / 100) - ((c.nuEhi : ℝ) / SC_R) * ((c.h2 : ℝ) / 100) -
        (2 / 3 : ℝ) * ((lam2 : ℝ) / SC_R) +
        ((c.nuMhi : ℝ) / SC_R) * ((c.h1 : ℝ) / 100) * ((c.h2 : ℝ) / 100) / 2 -
        ((c.nuMlo : ℝ) / SC_R) * ((c.e0 : ℝ) / SC_R) ^ 2 / 2 -
        (∑ i : Fin 10, alphaR c i * ((uR c i) ^ 2 + (vR c i) ^ 2)) +
        ((c.gamma : ℝ) / SC_R) * (((c.p1 : ℝ) / 100) * ((c.p2 : ℝ) / 100) + ((c.q1 : ℝ) / 100) * ((c.q2 : ℝ) / 100)) +
        ((c.nuPlo : ℝ) / SC_R) * ((c.p1 : ℝ) / 100) - ((c.nuPhi : ℝ) / SC_R) * ((c.p2 : ℝ) / 100) +
        ((c.nuQlo : ℝ) / SC_R) * ((c.q1 : ℝ) / 100) - ((c.nuQhi : ℝ) / SC_R) * ((c.q2 : ℝ) / 100)) +
        0 + 0 +
        (-(|((lam2 : ℝ) / SC_R)| / 6) / (n : ℝ)) +
        (-(∑ i : Fin 10, (|alphaR c i| + |betaR c i|) * (omReal (i.1 + 1) / 10)) / (n : ℝ)) := by
      rw [hCD_div, add_zero, add_zero, neg_div, neg_div]
      exact (sub_le_sub_right hconst_le _).trans_eq (by ring)
    refine (hconst_part.trans (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hbox_nn) hquad_nn) hlam_err) hD_err)).trans_eq ?_
    rw [halg, hlin_id, hfour_id, hpq_id]
    ring
  exact hL_lower

private lemma cert_sound (c : Cert) (hcert : checkCert c = true) :
    ∃ C_err : ℝ, ∀ n : ℕ, 20 ≤ n → ∀ A B : Finset ℤ,
      Disjoint A B →
      A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)) →
      A.card = B.card →
      (c.h1 : ℝ) / 100 ≤ EVal n A → EVal n A ≤ (c.h2 : ℝ) / 100 →
      (c.p1 : ℝ) / 100 ≤ CVal n A Real.pi → CVal n A Real.pi ≤ (c.p2 : ℝ) / 100 →
      (c.q1 : ℝ) / 100 ≤ SVal n A Real.pi → SVal n A Real.pi ≤ (c.q2 : ℝ) / 100 →
      (38 / 100 : ℝ) - C_err / (n : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) / (n : ℝ) := by
  -- Unpack checkCert c = true
  unfold checkCert at hcert
  dsimp only at hcert
  simp only [Bool.and_eq_true, Bool.or_eq_true, nat_beq_iff, decide_eq_true_eq, List.all_eq_true] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨⟨⟨hmQuad, hfQuad⟩, haLen⟩, hbLen⟩, huLen⟩, hvLen⟩, hnonneg⟩, halpha_nn⟩, ⟨huPhi_pos, h38⟩⟩
  rcases hnonneg with ⟨hnuElo, hnuEhi, hnuMhi, hnuMlo, hgamma, hnuPlo, hnuPhi, hnuQlo, hnuQhi, _, _, _⟩
  set lam2 := c.nuMhi - c.nuMlo
  set termsM := buildTermsM 1 c.alpha c.beta omIntList c.gamma
  set b2Phi : Nat := 2 * lam2.natAbs * 10000000 + sumB2M termsM omSqHiList 0
  set errPhiVal : Nat := sumErrValM termsM 0
  set errPhiDer : Nat := sumErrDerM termsM 0
  set dMDen : Nat := c.mQuad / 4
  set stepM : Nat := 1024 / c.mQuad
  set padPhi : Int := Int.ofNat ((b2Phi + 8 * dMDen * dMDen - 1) / (8 * dMDen * dMDen) + errPhiVal)
  set logM : Nat := if c.mQuad = 512 then 9 else 10
  set uPhi : Int := sumPow2 (oneMQuad c.nuMassM c.nuEM lam2 padPhi errPhiDer dMDen stepM termsM) 0 logM
  set linF : Int := linFInt c
  set termsF := buildTermsF c 1 c.alpha c.beta c.u c.v dIntList omIntList
  set b2Psi : Nat := sumB2F 1 termsF c.alpha c.beta omSqHiList 0
  set errPsiVal : Nat := sumErrValF 1 termsF c.alpha c.beta 0
  set errPsiDer : Nat := sumErrDerF 1 termsF c.alpha c.beta 0
  set dFDen : Nat := c.fQuad / 2
  set stepF : Nat := 512 / c.fQuad
  set padPsi : Int := Int.ofNat ((b2Psi + 8 * dFDen * dFDen - 1) / (8 * dFDen * dFDen) + errPsiVal)
  set logF : Nat := if c.fQuad = 256 then 8 else 9
  set uNegPsi : Int := sumPow2 (oneFQuad c.nuMassf linF padPsi errPsiDer dFDen stepF termsF) 0 logF
  set quadTerms : Int := sumQuadTerms c.alpha c.u c.v 0
  set constRhs : Int :=
    (-c.nuMassM - c.nuMassf) * 10000000
    + (c.nuElo * c.h1 - c.nuEhi * c.h2) * 100000
    + intFdiv (-2 * lam2 * 10000000) 3
    + intFdiv (c.nuMhi * c.h1 * c.h2 * 10000000) 20000
    + intFdiv (-c.nuMlo * c.e0 * c.e0 * 10000000) 2000000000000
    + quadTerms
    + intFdiv (c.gamma * (c.p1 * c.p2 + c.q1 * c.q2) * 10000000) 10000
    + (c.nuPlo * c.p1 - c.nuPhi * c.p2 + c.nuQlo * c.q1 - c.nuQhi * c.q2) * 100000
  have hd_eq : dFDen = dMDen := by dsimp [dFDen, dMDen]; omega
  have hdM_pos : 0 < dMDen := by rcases hmQuad with h | h <;> simp [dMDen, h]
  have hdMR : (0 : ℝ) < dMDen := by positivity
  have hSpos : (0 : ℝ) < SVAL_R := by norm_num [SVAL_R]
  have h2logM : 2 ^ logM = c.mQuad := by rcases hmQuad with h | h <;> simp [logM, h]
  have h2logF : 2 ^ logF = c.fQuad := by
    have hf_cases : c.fQuad = 256 ∨ c.fQuad = 512 := by omega
    rcases hf_cases with h | h <;> simp [logF, h]
  have hM_mul : (c.mQuad : ℝ) * (1 / (dMDen : ℝ)) = 4 := by
    rcases hmQuad with h | h <;> norm_num [dMDen, h]
  have hF_mul : (c.fQuad : ℝ) * (1 / (dFDen : ℝ)) = 2 := by
    have hf_cases : c.fQuad = 256 ∨ c.fQuad = 512 := by omega
    rcases hf_cases with h | h <;> norm_num [dFDen, h]
  have halpha_nnR : ∀ i : Fin 10, 0 ≤ alphaR c i := by
    intro i
    unfold alphaR
    have hmem : c.alpha.getD i.1 0 ∈ c.alpha := by
      have hi : i.1 < c.alpha.length := by omega
      simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    have hge : (0 : ℤ) ≤ c.alpha.getD i.1 0 := halpha_nn _ hmem
    have : (0 : ℝ) ≤ (c.alpha.getD i.1 0 : ℝ) := by exact_mod_cast hge
    unfold SC_R; positivity
  -- Define n-independent error constants C_M, C_F, C_D:
  set dM : ℝ := 1 / (dMDen : ℝ)
  set dF : ℝ := 1 / (dFDen : ℝ)
  set C_M : ℝ := max (Phi c 2) 0 + ∑ j ∈ Finset.range c.mQuad,
    2 * max (Phi c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))) +
      (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) +
      |Phi' c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ)))| * (dM / 2)) 0
  set C_F : ℝ := ∑ i ∈ Finset.range c.fQuad,
    2 * max (NegPsi c (-1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ))) +
      (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8) +
      |NegPsi' c (-1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ)))| * (dF / 2)) 0
  set C_D : ℝ := |((lam2 : ℝ) / SC_R)| / 6 +
    ∑ i : Fin 10, (|alphaR c i| + |betaR c i|) * (omReal (i.1 + 1) / 10)
  have huPhiR_pos : (0 : ℝ) < (uPhi : ℝ) / (SVAL_R * (dMDen : ℝ)) := by
    have : (0 : ℝ) < (uPhi : ℝ) := by exact_mod_cast huPhi_pos
    positivity
  refine ⟨(C_M + C_F + C_D) / ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))), ?_⟩
  intro n hn A B hdisj hunion hcard hElo hEhi hPlo hPhi hQlo hQhi
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by positivity
  have ⟨hAcard, _⟩ := card_eq_n hdisj hunion hcard
  set Ω : ℝ := (Erdos36.MaxOverlap A B : ℝ) / (n : ℝ)
  have hΩ_nn : 0 ≤ Ω := by positivity
  have hΩ_le1 : Ω ≤ 1 := by
    have hmo : Erdos36.MaxOverlap A B ≤ n := by
      unfold Erdos36.MaxOverlap
      refine ciSup_le fun k => ?_
      rw [← hAcard]; unfold Erdos36.Overlap
      refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
        (fun p hp q hq h => ?_)
      have hp' := (Finset.mem_filter.mp hp).2; have hq' := (Finset.mem_filter.mp hq).2
      dsimp at hp' hq'; exact Prod.ext h (by omega)
    dsimp [Ω]; rw [div_le_one hn_pos]; exact_mod_cast hmo
  have hCM_nn : 0 ≤ C_M := by
    apply add_nonneg (le_max_right _ _)
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (by norm_num) (le_max_right _ _)
  -- Step 1: Upper bound on (1/n) ∑_{k ∈ KSet n} max(Phi(k/n), 0) ≤ uPhi/(SVAL*dMDen) + C_M/n
  have hM_quad_bound : (1 / (n : ℝ)) * ∑ k ∈ KSet n, max (Phi c ((k : ℝ) / (n : ℝ))) 0 ≤
      (uPhi : ℝ) / (SVAL_R * (dMDen : ℝ)) + C_M / (n : ℝ) := by
    let K0 : Finset ℤ := (KSet n).erase (2 * (n : ℤ))
    have h2n_mem : 2 * (n : ℤ) ∈ KSet n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hsplit_top : ∑ k ∈ KSet n, max (Phi c ((k : ℝ) / (n : ℝ))) 0 =
        max (Phi c 2) 0 + ∑ k ∈ K0, max (Phi c ((k : ℝ) / (n : ℝ))) 0 := by
      rw [← Finset.add_sum_erase (KSet n) _ h2n_mem]
      congr 2; push_cast; field_simp
    rw [hsplit_top, mul_add]
    have hK0_rng : ∀ k ∈ K0, (-2 : ℝ) ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) < -2 + (c.mQuad : ℝ) * dM := by
      intro k hk
      rcases Finset.mem_erase.mp hk with ⟨hne, hmem⟩
      rcases Finset.mem_Icc.mp hmem with ⟨hlo, hhi⟩
      rw [hM_mul]
      constructor
      · rw [le_div_iff₀ hn_pos]; exact_mod_cast (show -(2 * (n : ℤ)) ≤ k by omega)
      · rw [show (-2 : ℝ) + 4 = 2 by ring, div_lt_iff₀ hn_pos]
        exact_mod_cast (show k < 2 * (n : ℤ) by omega)
    rw [sum_partition_intervals (-2) dM K0 (fun k => (k : ℝ) / (n : ℝ)) (fun k => max (Phi c ((k : ℝ) / (n : ℝ))) 0) c.mQuad hK0_rng]
    rw [Finset.mul_sum]
    have huPhi_eq : (uPhi : ℝ) / (SVAL_R * (dMDen : ℝ)) =
        ∑ j ∈ Finset.range c.mQuad,
          (oneMQuad c.nuMassM c.nuEM lam2 padPhi errPhiDer dMDen stepM termsM j : ℝ) / (SVAL_R * (dMDen : ℝ)) := by
      dsimp [uPhi]; rw [sumPow2_eq_sum_range, h2logM]; simp only [Nat.zero_add]; push_cast; rw [Finset.sum_div]
    rw [huPhi_eq]
    have hsum_buckets : ∑ j ∈ Finset.range c.mQuad,
          (1 / (n : ℝ)) * ∑ k ∈ K0.filter (fun k : ℤ => -2 + (j : ℝ) * dM ≤ (k : ℝ) / (n : ℝ) ∧
            (k : ℝ) / (n : ℝ) < -2 + ((j + 1 : ℕ) : ℝ) * dM), max (Phi c ((k : ℝ) / (n : ℝ))) 0 ≤
        ∑ j ∈ Finset.range c.mQuad,
          ((oneMQuad c.nuMassM c.nuEM lam2 padPhi errPhiDer dMDen stepM termsM j : ℝ) / (SVAL_R * (dMDen : ℝ)) +
            2 * max (Phi c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))) +
              (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) +
              |Phi' c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ)))| * (dM / 2)) 0 / (n : ℝ)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      set a := -2 + (j : ℝ) * dM
      set b := -2 + ((j + 1 : ℕ) : ℝ) * dM
      set xm := -2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))
      have hab : a < b := by
        dsimp [a, b, dM]; push_cast; rw [add_mul, one_mul]
        linarith only [show (0 : ℝ) < 1 / (dMDen : ℝ) by positivity]
      have hba : b - a = dM := by dsimp [a, b]; push_cast; ring
      have hmid : (a + b) / 2 = xm := by dsimp [a, b, xm, dM]; push_cast; ring
      have ⟨henv, huArea_le⟩ := oneMQuad_sound c hmQuad haLen hbLen j
      set Sj := K0.filter (fun k : ℤ => a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) < b)
      have hpt : ∀ k ∈ Sj, max (Phi c ((k : ℝ) / (n : ℝ))) 0 ≤
          max ((Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8)) +
            Phi' c xm * (0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 := by
        intro k hk
        have ⟨hlo, hhi⟩ := (Finset.mem_filter.mp hk).2
        have hdist : |(k : ℝ) / (n : ℝ) - xm| ≤ dM / 2 := by
          rw [abs_le]; constructor <;> (dsimp [a, b, xm, dM] at hlo hhi ⊢; push_cast at hhi; linarith)
        have hle := henv ((k : ℝ) / (n : ℝ)) hdist
        rw [hmid, zero_add]
        exact max_le_max_right 0 hle
      have h1 : (1 / (n : ℝ)) * ∑ k ∈ Sj, max (Phi c ((k : ℝ) / (n : ℝ))) 0 ≤
          (1 / (n : ℝ)) * ∑ k ∈ Sj, max ((Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8)) +
            Phi' c xm * (0 + (k : ℝ) / (n : ℝ) - (a + b) / 2)) 0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
      have h2 := discrete_linear_pos_sum_le hn1 0 a b
        (Phi c xm + (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8)) (Phi' c xm) hab Sj
        (fun k hk => by simpa using (Finset.mem_filter.mp hk).2)
      rw [hba] at h2
      linarith only [h1, h2, huArea_le]
    rw [Finset.sum_add_distrib] at hsum_buckets
    have hCM_sum : ∑ j ∈ Finset.range c.mQuad,
        2 * max (Phi c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))) +
          (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) +
          |Phi' c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ)))| * (dM / 2)) 0 / (n : ℝ) =
        (∑ j ∈ Finset.range c.mQuad,
          2 * max (Phi c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))) +
            (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) +
            |Phi' c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ)))| * (dM / 2)) 0) / (n : ℝ) := by
      rw [Finset.sum_div]
    rw [hCM_sum] at hsum_buckets
    have hCM_div : C_M / (n : ℝ) = max (Phi c 2) 0 / (n : ℝ) +
        (∑ j ∈ Finset.range c.mQuad,
          2 * max (Phi c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ))) +
            (b2Phi : ℝ) / SVAL_R * (dM ^ 2 / 8) +
            |Phi' c (-2 + (2 * (j : ℝ) + 1) / (2 * (dMDen : ℝ)))| * (dM / 2)) 0) / (n : ℝ) := by
      dsimp [C_M]; rw [add_div]
    rw [hCM_div, one_div_mul_eq_div]
    linarith only [hsum_buckets]
  -- Step 2: Upper bound on (1/n) ∑_{t ∈ Icc 1 (2n)} max(NegPsi(u_t), 0) ≤ uNegPsi/(SVAL*dMDen) + C_F/n
  have hF_quad_bound : (1 / (n : ℝ)) * ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), max (NegPsi c (uCoord n t)) 0 ≤
      (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) + C_F / (n : ℝ) := by
    have hIcc_rng : ∀ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
        (-1 : ℝ) ≤ uCoord n t ∧ uCoord n t < -1 + (c.fQuad : ℝ) * dF := by
      intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨hlo, hhi⟩
      rw [hF_mul]
      have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hlo
      have h2 : (t : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hhi
      unfold uCoord
      constructor
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [show (-1 : ℝ) + 2 = 1 by ring, div_lt_iff₀ (by positivity)]; linarith
    rw [sum_partition_intervals (-1) dF (Finset.Icc (1 : ℤ) (2 * (n : ℤ))) (uCoord n)
      (fun t => max (NegPsi c (uCoord n t)) 0) c.fQuad hIcc_rng]
    rw [Finset.mul_sum]
    have huF_eq : (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) =
        ∑ i ∈ Finset.range c.fQuad,
          (oneFQuad c.nuMassf linF padPsi errPsiDer dFDen stepF termsF i : ℝ) / (SVAL_R * (dFDen : ℝ)) := by
      rw [← hd_eq]
      dsimp [uNegPsi]; rw [sumPow2_eq_sum_range, h2logF]; simp only [Nat.zero_add]; push_cast; rw [Finset.sum_div]
    rw [huF_eq]
    have hsum_buckets : ∑ i ∈ Finset.range c.fQuad,
          (1 / (n : ℝ)) * ∑ t ∈ (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).filter
            (fun t : ℤ => -1 + (i : ℝ) * dF ≤ uCoord n t ∧ uCoord n t < -1 + ((i + 1 : ℕ) : ℝ) * dF),
            max (NegPsi c (uCoord n t)) 0 ≤
        ∑ i ∈ Finset.range c.fQuad,
          ((oneFQuad c.nuMassf linF padPsi errPsiDer dFDen stepF termsF i : ℝ) / (SVAL_R * (dFDen : ℝ)) +
            2 * max (NegPsi c (-1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ))) +
              (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8) +
              |NegPsi' c (-1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ)))| * (dF / 2)) 0 / (n : ℝ)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      set a := -1 + (i : ℝ) * dF
      set b := -1 + ((i + 1 : ℕ) : ℝ) * dF
      set tm := -1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ))
      have hdF_pos : 0 < dFDen := by omega
      have hab : a < b := by
        dsimp [a, b, dF]; push_cast; rw [add_mul, one_mul]
        linarith only [show (0 : ℝ) < 1 / (dFDen : ℝ) by positivity]
      have hba : b - a = dF := by dsimp [a, b]; push_cast; ring
      have hmid : (a + b) / 2 = tm := by dsimp [a, b, tm, dF]; push_cast; ring
      have ⟨henv, huArea_le⟩ := oneFQuad_sound c hmQuad hfQuad haLen hbLen huLen hvLen i
      set Ti := (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).filter (fun t : ℤ => a ≤ uCoord n t ∧ uCoord n t < b)
      have hu_lat : ∀ t : ℤ, uCoord n t = (-1 - 1 / (2 * (n : ℝ))) + (t : ℝ) / (n : ℝ) := by
        intro t; unfold uCoord; field_simp; ring
      have hpt : ∀ t ∈ Ti, max (NegPsi c (uCoord n t)) 0 ≤
          max ((NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8)) +
            NegPsi' c tm * ((-1 - 1 / (2 * (n : ℝ))) + (t : ℝ) / (n : ℝ) - (a + b) / 2)) 0 := by
        intro t ht
        have ⟨hlo, hhi⟩ := (Finset.mem_filter.mp ht).2
        have hdist : |uCoord n t - tm| ≤ dF / 2 := by
          rw [abs_le]; constructor <;> (dsimp [a, b, tm, dF] at hlo hhi ⊢; push_cast at hhi; linarith)
        have hle := henv (uCoord n t) hdist
        rw [hmid, ← hu_lat t]
        exact max_le_max_right 0 hle
      have h1 : (1 / (n : ℝ)) * ∑ t ∈ Ti, max (NegPsi c (uCoord n t)) 0 ≤
          (1 / (n : ℝ)) * ∑ t ∈ Ti, max ((NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8)) +
            NegPsi' c tm * ((-1 - 1 / (2 * (n : ℝ))) + (t : ℝ) / (n : ℝ) - (a + b) / 2)) 0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
      have h2 := discrete_linear_pos_sum_le hn1 (-1 - 1 / (2 * (n : ℝ))) a b
        (NegPsi c tm + (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8)) (NegPsi' c tm) hab Ti
        (fun t ht => by rw [← hu_lat t]; exact (Finset.mem_filter.mp ht).2)
      rw [hba] at h2
      linarith only [h1, h2, huArea_le]
    rw [Finset.sum_add_distrib] at hsum_buckets
    have hCF_sum : ∑ i ∈ Finset.range c.fQuad,
        2 * max (NegPsi c (-1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ))) +
          (b2Psi : ℝ) / SVAL_R * (dF ^ 2 / 8) +
          |NegPsi' c (-1 + (2 * (i : ℝ) + 1) / (2 * (dFDen : ℝ)))| * (dF / 2)) 0 / (n : ℝ) =
        C_F / (n : ℝ) := by
      dsimp [C_F]; rw [Finset.sum_div]
    rw [hCF_sum] at hsum_buckets
    exact hsum_buckets
  -- Step 3: Discrete Dual Identity + Nonnegativity -> constRhs / SVAL - C_D / n <= L_alt
  have hL_upper : (1 / (n : ℝ)) * ∑ k ∈ KSet n, Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k +
      (1 / (n : ℝ)) * ∑ a ∈ A, NegPsi c (uCoord n a) ≤
      Ω * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ)) + C_M / (n : ℝ)) +
      ((uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) + C_F / (n : ℝ)) := by
    have hM1 : (1 / (n : ℝ)) * ∑ k ∈ KSet n, Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k ≤
        Ω * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, max (Phi c ((k : ℝ) / (n : ℝ))) 0) := by
      rw [show Ω * ((1 / (n : ℝ)) * ∑ k ∈ KSet n, max (Phi c ((k : ℝ) / (n : ℝ))) 0) =
          (1 / (n : ℝ)) * ∑ k ∈ KSet n, (max (Phi c ((k : ℝ) / (n : ℝ))) 0 * Ω) by
            rw [← Finset.sum_mul]; ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine Finset.sum_le_sum fun k _ => ?_
      have hm_nn : 0 ≤ mVal n A B k := by unfold mVal; positivity
      have hm_le : mVal n A B k ≤ Ω := by
        unfold mVal
        exact div_le_div_of_nonneg_right (by exact_mod_cast le_ciSup (bddAbove_overlap A B) k) hn_pos.le
      calc Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k
          ≤ max (Phi c ((k : ℝ) / (n : ℝ))) 0 * mVal n A B k :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hm_nn
        _ ≤ max (Phi c ((k : ℝ) / (n : ℝ))) 0 * Ω :=
            mul_le_mul_of_nonneg_left hm_le (le_max_right _ _)
    have hF1 : (1 / (n : ℝ)) * ∑ a ∈ A, NegPsi c (uCoord n a) ≤
        (1 / (n : ℝ)) * ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), max (NegPsi c (uCoord n t)) 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hAsub : A ⊆ Finset.Icc (1 : ℤ) (2 * (n : ℤ)) := hunion ▸ Finset.subset_union_left
      calc ∑ a ∈ A, NegPsi c (uCoord n a)
          ≤ ∑ a ∈ A, max (NegPsi c (uCoord n a)) 0 := Finset.sum_le_sum fun a _ => le_max_left _ _
        _ ≤ ∑ t ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), max (NegPsi c (uCoord n t)) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => le_max_right _ _)
    have hM2 := mul_le_mul_of_nonneg_left hM_quad_bound hΩ_nn
    linarith only [hM1, hM2, hF1, hF_quad_bound]
  -- Step 4: Lower bound via standalone cert_L_lower
  have hL_lower : (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) ≤
      (1 / (n : ℝ)) * ∑ k ∈ KSet n, Phi c ((k : ℝ) / (n : ℝ)) * mVal n A B k +
      (1 / (n : ℝ)) * ∑ a ∈ A, NegPsi c (uCoord n a) :=
    cert_L_lower c haLen huLen hvLen hnuElo hnuEhi hnuMhi hnuMlo hgamma hnuPlo hnuPhi hnuQlo hnuQhi halpha_nnR
      n hn A B hdisj hunion hcard hElo hEhi hPlo hPhi hQlo hQhi
  -- Step 5: Combine hL_lower, hL_upper, Ω ≤ 1, and 38 * uPhi ≤ 100 * (constRhs * dMDen - uNegPsi)!
  have h38R : (38 / 100 : ℝ) * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) ≤
      (constRhs : ℝ) / SVAL_R - (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) := by
    have h38_int : (38 : ℤ) * uPhi ≤ 100 * (constRhs * (dMDen : ℤ) - uNegPsi) := h38
    have h38' : (38 : ℝ) * (uPhi : ℝ) ≤ 100 * ((constRhs : ℝ) * (dMDen : ℝ) - (uNegPsi : ℝ)) := by
      have h := (Int.cast_le (R := ℝ)).mpr h38_int
      rw [Int.cast_mul, Int.cast_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        Int.cast_ofNat, Int.cast_ofNat] at h
      exact h
    have hrew : (constRhs : ℝ) / SVAL_R - (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) =
        ((constRhs : ℝ) * (dMDen : ℝ) - (uNegPsi : ℝ)) / (SVAL_R * (dMDen : ℝ)) := by
      rw [sub_div, mul_div_mul_right _ _ hdMR.ne']
    rw [hrew]
    have : (38 / 100 : ℝ) * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) =
        ((38 : ℝ) * (uPhi : ℝ)) / (100 * (SVAL_R * (dMDen : ℝ))) := by ring
    have hSd : (0 : ℝ) < SVAL_R * (dMDen : ℝ) := mul_pos hSpos hdMR
    have h100Sd : (0 : ℝ) < 100 * (SVAL_R * (dMDen : ℝ)) := mul_pos (by norm_num) hSd
    rw [this, div_le_div_iff₀ h100Sd hSd]
    have hmul := mul_le_mul_of_nonneg_right h38' hSd.le
    have h1 : 100 * ((constRhs : ℝ) * (dMDen : ℝ) - (uNegPsi : ℝ)) * (SVAL_R * (dMDen : ℝ)) =
        ((constRhs : ℝ) * (dMDen : ℝ) - (uNegPsi : ℝ)) * (100 * (SVAL_R * (dMDen : ℝ))) := by ring
    linarith only [hmul, h1]
  have hΩ_CM : Ω * (C_M / (n : ℝ)) ≤ C_M / (n : ℝ) :=
    mul_le_of_le_one_left (div_nonneg hCM_nn hn_pos.le) hΩ_le1
  have hfinal_mul : (38 / 100 : ℝ) * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) - (C_M + C_F + C_D) / (n : ℝ) ≤
      Ω * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) := by
    have h1 : (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) ≤
        Ω * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) + C_M / (n : ℝ) +
        ((uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) + C_F / (n : ℝ)) := by
      have h0 := hL_lower.trans hL_upper
      rw [mul_add] at h0
      exact h0.trans (add_le_add (add_le_add le_rfl hΩ_CM) le_rfl)
    have h2 : (38 / 100 : ℝ) * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) - (C_M + C_F + C_D) / (n : ℝ) ≤
        (constRhs : ℝ) / SVAL_R - (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) - (C_M + C_F + C_D) / (n : ℝ) :=
      sub_le_sub_right h38R _
    have h3 : (constRhs : ℝ) / SVAL_R - (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) - (C_M + C_F + C_D) / (n : ℝ) ≤
        Ω * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) := by
      rw [show (C_M + C_F + C_D) / (n : ℝ) = C_M / (n : ℝ) + C_F / (n : ℝ) + C_D / (n : ℝ) by ring]
      have h1'' : (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) ≤
          Ω * ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) +
          ((uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) + (C_M / (n : ℝ) + C_F / (n : ℝ))) :=
        h1.trans_eq (by ring)
      have h1' := sub_le_iff_le_add.mpr h1''
      have heq2 : (constRhs : ℝ) / SVAL_R - (uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) -
          (C_M / (n : ℝ) + C_F / (n : ℝ) + C_D / (n : ℝ)) =
          (constRhs : ℝ) / SVAL_R - C_D / (n : ℝ) -
          ((uNegPsi : ℝ) / (SVAL_R * (dMDen : ℝ)) + (C_M / (n : ℝ) + C_F / (n : ℝ))) := by ring
      rw [heq2]
      exact h1'
    exact h2.trans h3
  have hfinal_div := div_le_div_of_nonneg_right hfinal_mul huPhiR_pos.le
  rw [mul_div_cancel_right₀ _ huPhiR_pos.ne', sub_div, mul_div_cancel_right₀ _ huPhiR_pos.ne'] at hfinal_div
  have hrew_err : (C_M + C_F + C_D) / (n : ℝ) / ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) =
      (C_M + C_F + C_D) / ((uPhi : ℝ) / (SVAL_R * (dMDen : ℝ))) / (n : ℝ) := by ring
  rwa [hrew_err] at hfinal_div

/- Subsection 6G: Global 10-Box + Moser Cover and Liminf Lower Bound -/

theorem global_lower_bound
    (h0 : checkCert cert0 = true) (h1 : checkCert cert1 = true)
    (h2 : checkCert cert2 = true) (h3 : checkCert cert3 = true)
    (h4 : checkCert cert4 = true) (h5 : checkCert cert5 = true)
    (h6 : checkCert cert6 = true) (h7 : checkCert cert7 = true)
    (h8 : checkCert cert8 = true) (h9 : checkCert cert9 = true) :
    ∃ C_err : ℝ, ∀ n : ℕ, 20 ≤ n →
      (38 / 100 : ℝ) - C_err / (n : ℝ) ≤ Erdos36.MinOverlapQuotient n := by
  obtain ⟨C0, hC0⟩ := cert_sound cert0 h0
  obtain ⟨C1, hC1⟩ := cert_sound cert1 h1
  obtain ⟨C2, hC2⟩ := cert_sound cert2 h2
  obtain ⟨C3, hC3⟩ := cert_sound cert3 h3
  obtain ⟨C4, hC4⟩ := cert_sound cert4 h4
  obtain ⟨C5, hC5⟩ := cert_sound cert5 h5
  obtain ⟨C6, hC6⟩ := cert_sound cert6 h6
  obtain ⟨C7, hC7⟩ := cert_sound cert7 h7
  obtain ⟨C8, hC8⟩ := cert_sound cert8 h8
  obtain ⟨C9, hC9⟩ := cert_sound cert9 h9
  let Cmax : ℝ := max 5 (max C0 (max C1 (max C2 (max C3 (max C4 (max C5 (max C6 (max C7 (max C8 C9)))))))))
  have h5_le : 5 ≤ Cmax := le_max_left _ _
  have h0_le : C0 ≤ Cmax := (le_max_left _ _).trans (le_max_right _ _)
  have h1_le : C1 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h2_le : C2 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have h3_le : C3 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have h4_le : C4 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))
  have h5c_le : C5 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
  have h6_le : C6 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))))
  have h7_le : C7 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))))
  have h8_le : C8 ≤ Cmax := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))))))
  have h9_le : C9 ≤ Cmax := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))))))
  refine ⟨Cmax, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by positivity
  -- M n is attained by some balanced partition (A0, B0)!
  let S_n : Set ℕ := {Erdos36.MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)))
    (_same_card : A.card = B.card)}
  have hne : S_n.Nonempty := by
    refine ⟨Erdos36.MaxOverlap (Finset.Icc (1 : ℤ) (n : ℤ)) (Finset.Icc ((n : ℤ) + 1) (2 * (n : ℤ))),
      Finset.Icc (1 : ℤ) (n : ℤ), Finset.Icc ((n : ℤ) + 1) (2 * (n : ℤ)), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    · ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Int.card_Icc, Int.card_Icc]; omega
  have hmem : Erdos36.M n ∈ S_n := Nat.sInf_mem hne
  rcases hmem with ⟨A0, B0, hd0, hu0, hc0, hmo0⟩
  unfold Erdos36.MinOverlapQuotient
  rw [← hmo0]
  obtain ⟨A, B, hdisj, hunion, hcard, hmo_eq, hE0, hC0_lo, hC0_hi, hS0_lo, hS0_hi⟩ :=
    exists_normalized_partition hn1 hd0 hu0 hc0
  rw [← hmo_eq]
  have hstep : ∀ C : ℝ, C ≤ Cmax → (38 / 100 : ℝ) - C / (n : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) / (n : ℝ) →
      (38 / 100 : ℝ) - Cmax / (n : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) / (n : ℝ) := by
    intro C hC hbd
    have : C / (n : ℝ) ≤ Cmax / (n : ℝ) := div_le_div_of_nonneg_right hC hn_pos.le
    linarith
  set E := EVal n A
  set p := CVal n A Real.pi
  set q := SVal n A Real.pi
  by_cases hE45 : (45 / 100 : ℝ) ≤ E
  · exact hstep 5 h5_le (moser_lower_bound hn1 hdisj hunion hcard hE45)
  push Not at hE45
  by_cases hp33 : p ≤ 33 / 100
  · by_cases hq0 : q ≤ 0
    · exact hstep C0 h0_le (hC0 n hn A B hdisj hunion hcard
        (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
        (by change ((0 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((33 : ℤ) : ℝ) / 100; norm_num; linarith)
        (by change ((-100 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((0 : ℤ) : ℝ) / 100; norm_num; linarith))
    push Not at hq0
    by_cases hq25 : q ≤ 25 / 100
    · exact hstep C1 h1_le (hC1 n hn A B hdisj hunion hcard
        (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
        (by change ((0 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((33 : ℤ) : ℝ) / 100; norm_num; linarith)
        (by change ((0 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((25 : ℤ) : ℝ) / 100; norm_num; linarith))
    · push Not at hq25
      exact hstep C2 h2_le (hC2 n hn A B hdisj hunion hcard
        (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
        (by change ((0 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((33 : ℤ) : ℝ) / 100; norm_num; linarith)
        (by change ((25 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((100 : ℤ) : ℝ) / 100; norm_num; linarith))
  push Not at hp33
  by_cases hp45 : (45 / 100 : ℝ) ≤ p
  · exact hstep C3 h3_le (hC3 n hn A B hdisj hunion hcard
      (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((45 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((100 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((-100 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((100 : ℤ) : ℝ) / 100; norm_num; linarith))
  push Not at hp45
  by_cases hqm4 : q ≤ -(4 / 100)
  · exact hstep C4 h4_le (hC4 n hn A B hdisj hunion hcard
      (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((33 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((-100 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((-4 : ℤ) : ℝ) / 100; norm_num; linarith))
  push Not at hqm4
  by_cases hqp4 : (4 / 100 : ℝ) ≤ q
  · exact hstep C5 h5c_le (hC5 n hn A B hdisj hunion hcard
      (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((33 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((4 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((100 : ℤ) : ℝ) / 100; norm_num; linarith))
  push Not at hqp4
  by_cases hE5 : (5 / 100 : ℝ) ≤ E
  · exact hstep C6 h6_le (hC6 n hn A B hdisj hunion hcard
      (by change ((5 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((33 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((-4 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((4 : ℤ) : ℝ) / 100; norm_num; linarith))
  push Not at hE5
  by_cases hp37 : p ≤ 37 / 100
  · exact hstep C7 h7_le (hC7 n hn A B hdisj hunion hcard
      (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((5 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((33 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((37 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((-4 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((4 : ℤ) : ℝ) / 100; norm_num; linarith))
  push Not at hp37
  by_cases hp41 : p ≤ 41 / 100
  · exact hstep C8 h8_le (hC8 n hn A B hdisj hunion hcard
      (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((5 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((37 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((41 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((-4 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((4 : ℤ) : ℝ) / 100; norm_num; linarith))
  · push Not at hp41
    exact hstep C9 h9_le (hC9 n hn A B hdisj hunion hcard
      (by change ((0 : ℤ) : ℝ) / 100 ≤ E; norm_num; linarith) (by change E ≤ ((5 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((41 : ℤ) : ℝ) / 100 ≤ p; norm_num; linarith) (by change p ≤ ((45 : ℤ) : ℝ) / 100; norm_num; linarith)
      (by change ((-4 : ℤ) : ℝ) / 100 ≤ q; norm_num; linarith) (by change q ≤ ((4 : ℤ) : ℝ) / 100; norm_num; linarith))

theorem liminf_lower_bound
    (h0 : checkCert cert0 = true) (h1 : checkCert cert1 = true)
    (h2 : checkCert cert2 = true) (h3 : checkCert cert3 = true)
    (h4 : checkCert cert4 = true) (h5 : checkCert cert5 = true)
    (h6 : checkCert cert6 = true) (h7 : checkCert cert7 = true)
    (h8 : checkCert cert8 = true) (h9 : checkCert cert9 = true) :
    (38 / 100 : ℝ) ≤ Filter.atTop.liminf Erdos36.MinOverlapQuotient := by
  obtain ⟨C, hC⟩ := global_lower_bound h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have h_nn : ∀ n : ℕ, (0 : ℝ) ≤ Erdos36.MinOverlapQuotient n := fun n => by
    unfold Erdos36.MinOverlapQuotient; positivity
  have h_le1 : ∀ n : ℕ, Erdos36.MinOverlapQuotient n ≤ 1 := by
    intro n
    unfold Erdos36.MinOverlapQuotient
    by_cases hn0 : n = 0
    · subst hn0; simp
    have hn_pos : (0 : ℝ) < n := by positivity
    let A := Finset.Icc (1 : ℤ) (n : ℤ)
    let B := Finset.Icc ((n : ℤ) + 1) (2 * (n : ℤ))
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]; intro x h1 h2; simp only [A, B, Finset.mem_Icc] at h1 h2; omega
    have hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * (n : ℤ)) := by
      ext x; simp only [A, B, Finset.mem_union, Finset.mem_Icc]; omega
    have hc : A.card = B.card := by simp only [A, B, Int.card_Icc]; omega
    have hMle : Erdos36.M n ≤ Erdos36.MaxOverlap A B :=
      Nat.sInf_le ⟨A, B, hd, hu, hc, rfl⟩
    have hMOle : Erdos36.MaxOverlap A B ≤ n := by
      have ⟨hA, _⟩ := card_eq_n hd hu hc
      unfold Erdos36.MaxOverlap
      refine ciSup_le fun k => ?_
      rw [← hA]; unfold Erdos36.Overlap
      refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
        (fun p hp q hq h => ?_)
      have hp' := (Finset.mem_filter.mp hp).2; have hq' := (Finset.mem_filter.mp hq).2
      dsimp at hp' hq'; exact Prod.ext h (by omega)
    rw [div_le_one hn_pos]
    exact_mod_cast hMle.trans hMOle
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop Erdos36.MinOverlapQuotient := by
    refine ⟨1, fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_map.mp ha)
    exact le_trans (hN N le_rfl) (h_le1 N)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hle_eps : (38 / 100 : ℝ) - ε ≤ Filter.atTop.liminf Erdos36.MinOverlapQuotient := by
    apply Filter.le_liminf_of_le hcobdd
    refine Filter.eventually_atTop.mpr ⟨max 20 (Nat.ceil (max C 0 / ε) + 1), fun n hn => ?_⟩
    have hn20 : 20 ≤ n := le_trans (le_max_left _ _) hn
    have hng : Nat.ceil (max C 0 / ε) + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn_pos : (0 : ℝ) < n := by positivity
    have hC_div : C / (n : ℝ) ≤ ε := by
      have h1 : C ≤ max C 0 := le_max_left _ _
      have h2 : max C 0 / ε < (n : ℝ) := by
        have hceil : max C 0 / ε ≤ (Nat.ceil (max C 0 / ε) : ℝ) := Nat.le_ceil _
        have hnR : (Nat.ceil (max C 0 / ε) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hng
        linarith
      have h3 : max C 0 / (n : ℝ) < ε := by
        rw [div_lt_iff₀ hn_pos]; rwa [div_lt_iff₀ hε, mul_comm] at h2
      have h4 : C / (n : ℝ) ≤ max C 0 / (n : ℝ) := div_le_div_of_nonneg_right h1 hn_pos.le
      linarith
    linarith [hC n hn20]
  linarith


end Erdos36Lower

noncomputable def OMA.answer : ℝ := 38 / 100

theorem OMA.solution :
    Erdos36.erdos_36.variants.lower.answer = OMA.answer →
      type_of% @Erdos36.erdos_36.variants.lower := by
  intro hans
  refine ⟨38 / 100, by norm_num, ?_, ?_⟩
  · exact Erdos36Lower.liminf_lower_bound
      Erdos36Lower.cert0_ok Erdos36Lower.cert1_ok Erdos36Lower.cert2_ok
      Erdos36Lower.cert3_ok Erdos36Lower.cert4_ok Erdos36Lower.cert5_ok
      Erdos36Lower.cert6_ok Erdos36Lower.cert7_ok Erdos36Lower.cert8_ok
      Erdos36Lower.cert9_ok
  · rw [hans]; rfl
