import OMAStatements.S_oeis_a039824
import Mathlib

/-!
# Distinct coefficients of Stephan's polynomial product

The first and last coefficients give four forced repetitions. All nonconstant
coefficients in the remaining interval are at least n. The original equation
is therefore equivalent to injectivity on one contiguous interval of degrees.
Source: https://oeis.org/A039824
-/

namespace OMA.R_oeis_a039824_R1
open Polynomial Finset OMA.S_oeis_a039824

lemma representative_card (n : ℕ) (hn : 6 < n) :
    (insert (n^2-2) (range (n^2-4))).card = n^2-3 := by
  have big : 49 ≤ n^2 := by nlinarith
  rw [card_insert_of_notMem (by simp only [mem_range]; omega), card_range]
  omega

lemma two_terms (p q : ℕ[X]) (i a j b : ℕ) (he : i+a = j+b) (hne : i ≠ j) :
    p.coeff i * q.coeff a + p.coeff j * q.coeff b ≤ (p*q).coeff (i+a) := by
  have hs : ({(i,a), (j,b)} : Finset (ℕ × ℕ)) ⊆ antidiagonal (i+a) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [he]
  rw [coeff_mul]
  simpa [hne] using (sum_le_sum_of_subset_of_nonneg (f := fun z : ℕ × ℕ =>
    p.coeff z.1 * q.coeff z.2) hs (by intros; omega))

section Factors
variable {factor : ℕ → ℕ[X]} (spec : ∀ i, factor i = 1 + ∑ j ∈ range i, (X : ℕ[X]) ^ (2*j+1))
include spec

lemma factor_step (i : ℕ) : factor (i + 1) = factor i + X ^ (2 * i + 1) := by
  simp [spec, sum_range_succ, add_assoc]

lemma factor_data (i : ℕ) :
    (factor i).Monic ∧ (factor i).natDegree = 2 * i - 1 := by
  induction i with
  | zero => simp [spec]
  | succ i ih =>
    have lt : (factor i).natDegree < (X ^ (2 * i + 1) : ℕ[X]).natDegree := by
      rw [ih.2, natDegree_X_pow]
      omega
    rw [factor_step spec]
    exact ⟨(monic_X_pow _).add_of_right (degree_lt_degree lt), by
      rw [natDegree_add_eq_right_of_natDegree_lt lt, natDegree_X_pow]
      omega⟩

lemma product_step (n : ℕ) : P (n + 1) = P n * factor (n + 1) := by
  rw [spec (n + 1)]
  exact prod_Icc_succ_top (by omega : 1 ≤ n + 1) (fun i => 1 + ∑ j ∈ range i, (X : ℕ[X]) ^ (2*j+1))

lemma product_data (n : ℕ) : (P n).Monic ∧ (P n).natDegree = n^2 := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    have f := factor_data spec (n + 1)
    rw [product_step spec]
    exact ⟨ih.1.mul f.1, by
      rw [ih.1.natDegree_mul f.1, ih.2, f.2, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      ring⟩

lemma factor_zero (i : ℕ) : (factor i).coeff 0 = 1 := by
  induction i with
  | zero => simp [spec]
  | succ i ih => simp [factor_step spec, ih, coeff_X_pow]

lemma product_zero (n : ℕ) : (P n).coeff 0 = 1 := by
  induction n with
  | zero => simp [P]
  | succ n ih => simp [product_step spec, mul_coeff_zero, factor_zero spec, ih]

lemma first_collision (n : ℕ) : (P n).coeff (n^2) = (P n).coeff 0 := by
  rw [← (product_data spec n).2, coeff_natDegree, product_zero spec]
  exact (product_data spec n).1

lemma factor_coeff (i k : ℕ) :
    (factor i).coeff k = (if k = 0 then 1 else 0) +
      (if k % 2 = 1 ∧ k / 2 < i then 1 else 0) := by
  induction i with
  | zero => simp [spec, coeff_one]
  | succ i ih =>
    rw [factor_step spec, coeff_add, ih, coeff_X_pow]
    split_ifs <;> omega

lemma low (n : ℕ) : (P n).coeff 1 = n ∧ (P n).coeff 2 = n.choose 2 := by
  induction n with
  | zero => simp [P, coeff_one]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have f1 : (factor (n + 1)).coeff 1 = 1 := by simp [factor_coeff spec]
    have f2 : (factor (n + 1)).coeff 2 = 0 := by simp [factor_coeff spec]
    rw [product_step spec]
    constructor
    · rw [mul_coeff_one]
      simp [h1, product_zero spec, factor_zero spec, f1, Nat.add_comm]
    · simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        sum_range_succ, product_zero spec, h1, h2, factor_zero spec, f1, f2,
        Nat.choose_succ_succ]

lemma reverse_factor_low (i k : ℕ) (hi : 3 ≤ i) (hk : k ≤ 4) :
    (factor i).reverse.coeff k = if k % 2 = 0 then 1 else 0 := by
  rw [coeff_reverse, (factor_data spec i).2, revAt_le (by omega), factor_coeff spec]
  split_ifs <;> omega

lemma reverse_product (n : ℕ) : (P (n + 1)).reverse =
    (P n).reverse * (factor (n + 1)).reverse := by
  rw [product_step spec, reverse_mul_of_domain]

lemma reverse_low (n : ℕ) (hn : 2 ≤ n) :
    (P n).reverse.coeff 0 = 1 ∧ (P n).reverse.coeff 1 = 1 ∧
    (P n).reverse.coeff 2 = n - 1 ∧ (P n).reverse.coeff 3 = n ∧
    (P n).reverse.coeff 4 = n.choose 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have p : P 0 = 1 := by simp [P]
    have f : factor 0 = 1 := by simp [spec]
    have eq : P 2 = (1 + X) * ((1 + X) + X^3) := by
      rw [product_step spec 1, product_step spec 0, p, factor_step spec 1, factor_step spec 0, f]
      simp
    simp (disch := decide) only [coeff_reverse, (product_data spec 2).2, revAt_le]
    norm_num [eq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ, coeff_add, coeff_one, coeff_X, coeff_X_pow, Nat.choose]
  | succ n hn ih =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih
    have hf (k : ℕ) (hk : k ≤ 4) := reverse_factor_low spec (n + 1) k (by omega) hk
    have e0 := hf 0 (by decide)
    have e1 := hf 1 (by decide)
    have e2 := hf 2 (by decide)
    have e3 := hf 3 (by decide)
    have e4 := hf 4 (by decide)
    rw [reverse_product spec]
    norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ, h0, h1, h2, h3, h4, e0, e1, e2, e3, e4, Nat.choose_succ_succ]
    omega

lemma fifth (n : ℕ) (hn : 3 ≤ n) : n ≤ (P n).reverse.coeff 5 := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨_, h1, _, h3, _⟩ := reverse_low spec n (by omega)
    have e2 := reverse_factor_low spec (n + 1) 2 hn (by decide)
    have e4 := reverse_factor_low spec (n + 1) 4 hn (by decide)
    rw [reverse_product spec]
    norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ, h1, h3, e2, e4]
    omega

lemma edges (n : ℕ) (hn : 6 < n) :
    (P n).natDegree = n^2 ∧
    (P n).coeff 0 = 1 ∧ (P n).coeff 1 = n ∧
    (P n).coeff (n^2) = (P n).coeff 0 ∧
    (P n).coeff (n^2-1) = (P n).coeff 0 ∧
    (P n).coeff (n^2-2) = n - 1 ∧
    (P n).coeff (n^2-3) = (P n).coeff 1 ∧
    (P n).coeff (n^2-4) = (P n).coeff 2 ∧
    n ≤ (P n).coeff (n^2-5) := by
  have big : 49 ≤ n^2 := by nlinarith
  have turn (k : ℕ) (hk : k ≤ 5) : (P n).reverse.coeff k = (P n).coeff (n^2-k) := by
    rw [coeff_reverse, (product_data spec n).2, revAt_le (by omega)]
  obtain ⟨_, h1, h2, h3, h4⟩ := reverse_low spec n (by omega)
  have h5 := fifth spec n (by omega)
  rw [turn 1 (by decide)] at h1
  rw [turn 2 (by decide)] at h2
  rw [turn 3 (by decide)] at h3
  rw [turn 4 (by decide)] at h4
  rw [turn 5 (by decide)] at h5
  exact ⟨(product_data spec n).2, product_zero spec n, (low spec n).1, first_collision spec n,
    h1.trans (product_zero spec n).symm, h2, h3.trans (low spec n).1.symm,
    h4.trans (low spec n).2.symm, h5⟩

lemma representative_image (n : ℕ) (hn : 6 < n) :
    (range (n^2+1)).image (P n).coeff =
      (insert (n^2-2) (range (n^2-4))).image (P n).coeff := by
  have big : 49 ≤ n^2 := by nlinarith
  obtain ⟨_, _, _, e0, e1, _, e3, e4, _⟩ := edges spec n hn
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    have h := mem_range.mp hi
    by_cases hm : i ∈ insert (n^2-2) (range (n^2-4))
    · exact mem_image.mpr ⟨i, hm, rfl⟩
    · simp only [mem_insert, mem_range, not_or] at hm
      rcases (show i = n^2 ∨ i = n^2-1 ∨ i = n^2-3 ∨ i = n^2-4 by omega) with rfl | rfl | rfl | rfl
      · exact mem_image.mpr ⟨0, mem_insert_of_mem (mem_range.mpr (by omega)), e0.symm⟩
      · exact mem_image.mpr ⟨0, mem_insert_of_mem (mem_range.mpr (by omega)), e1.symm⟩
      · exact mem_image.mpr ⟨1, mem_insert_of_mem (mem_range.mpr (by omega)), e3.symm⟩
      · exact mem_image.mpr ⟨2, mem_insert_of_mem (mem_range.mpr (by omega)), e4.symm⟩
  · apply image_subset_image
    intro i hi
    simp only [mem_insert, mem_range] at hi ⊢
    omega

/-- The four endpoint repetitions establish the upper bound unconditionally. -/
theorem upper_bound_aux (n : ℕ) (hn : 6 < n) : a n ≤ n^2-3 := by
  unfold a
  rw [(edges spec n hn).1, representative_image spec n hn, ← representative_card n hn]
  exact Finset.card_image_le

lemma front_terms (n k : ℕ) (hk : 1 ≤ k) :
    (P n).coeff k + (P n).coeff (k-1) ≤ (P (n+1)).coeff k := by
  have e := two_terms (P n) (factor (n+1)) k 0 (k-1) 1 (by omega) (by omega)
  have f1 : (factor (n+1)).coeff 1 = 1 := by simp [factor_coeff spec]
  simpa [product_step spec, factor_zero spec, f1] using e

lemma back_terms (n i : ℕ) (hn : 1 ≤ n) :
    (P n).coeff i + (P n).coeff (i+2) ≤ (P (n+1)).coeff (i+(2*n+1)) := by
  have e := two_terms (P n) (factor (n+1)) i (2*n+1) (i+2) (2*n-1) (by omega) (by omega)
  have deg : (factor (n+1)).natDegree = 2*n+1 := (factor_data spec _).2.trans (by omega)
  have f : (factor (n+1)).coeff (2*n+1) = 1 := by
    rw [← deg, coeff_natDegree]
    exact (factor_data spec _).1
  have g : (factor (n+1)).coeff (2*n-1) = 1 := by rw [factor_coeff spec]; split_ifs <;> omega
  simpa [product_step spec, f, g] using e

/-- Except near the last coefficients, every nonconstant coefficient is at least n. -/
lemma interior_lower (n : ℕ) (hn : 3 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n^2-3 → n ≤ (P n).coeff k := by
  induction n, hn using Nat.le_induction with
  | base =>
    have p : P 0 = 1 := by simp [P]
    have f : factor 0 = 1 := by simp [spec]
    have eq : P 3 = ((1+X)*(1+X+X^3))*(1+X+X^3+X^5) := by
      rw [product_step spec 2, product_step spec 1, product_step spec 0, p, factor_step spec 2, factor_step spec 1,
        factor_step spec 0, f]
      simp
    intro k hk hl
    norm_num at hl
    interval_cases k <;> norm_num [eq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  | succ n hn ih =>
    intro k hk limit
    have big : 9 ≤ n^2 := by nlinarith
    have dn : (n+1)^2 = n^2+2*n+1 := by ring
    rw [dn] at limit
    have b : 3*n ≤ n^2 := by simpa [sq] using Nat.mul_le_mul_right n hn
    obtain ⟨_, r1, r2, _, _⟩ := reverse_low spec n (by omega)
    rw [coeff_reverse, (product_data spec n).2, revAt_le (by omega)] at r1 r2
    by_cases low_side : k ≤ n^2-2
    · have e := front_terms spec n k hk
      by_cases h : k ≤ n^2-3
      · have main := ih k hk h
        by_cases one : k = 1
        · subst k
          simp [product_zero spec] at e
          omega
        · have := ih (k-1) (by omega) (by omega)
          omega
      · have main := ih (k-1) (by omega) (by omega)
        have val_at : (P n).coeff k = n-1 := by rw [show k = n^2-2 by omega, r2]
        rw [val_at] at e
        omega
    · let i := k-(2*n+1)
      have he : k = i+(2*n+1) := by dsimp [i]; omega
      have hi : 1 ≤ i ∧ i ≤ n^2-3 := by dsimp [i]; omega
      have main := ih i hi.1 hi.2
      have near : 0 < (P n).coeff (i+2) := by
        by_cases h : i+2 ≤ n^2-3
        · have := ih (i+2) (by omega) h
          omega
        · rcases (show i+2 = n^2-1 ∨ i+2 = n^2-2 by omega) with h | h
          · rw [h, r1]; decide
          · rw [h, r2]; omega
      have e := back_terms spec n i (by omega)
      rw [he]
      omega

/-- Removing the four forced repetitions leaves one isolated value, n-1. It is
smaller than every nonconstant coefficient in the contiguous remaining range. -/
lemma core_iff_aux (n : ℕ) (hn : 6 < n) : a n = n^2-3 ↔
    Set.InjOn (P n).coeff (Set.Icc 0 (n^2-5)) := by
  have big : 49 ≤ n^2 := by nlinarith
  obtain ⟨hd, zero, _, _, _, last, _, _, _⟩ := edges spec n hn
  have isolated (k : ℕ) (hk : k < n^2-4) : (P n).coeff k ≠ n-1 := by
    by_cases h : k = 0
    · rw [h, zero]; omega
    · have := interior_lower spec n (by omega) k (by omega) (by omega)
      omega
  unfold a
  rw [hd, representative_image spec n hn, ← representative_card n hn, card_image_iff]
  constructor
  · intro inj i hi j hj e
    exact inj (mem_insert_of_mem (mem_range.mpr (by have := hi.2; omega)))
      (mem_insert_of_mem (mem_range.mpr (by have := hj.2; omega))) e
  · intro inj i hi j hj e
    simp only [mem_coe, mem_insert, mem_range] at hi hj
    rcases hi with rfl | hi <;> rcases hj with rfl | hj
    · rfl
    · exact False.elim (isolated _ hj (e.symm.trans last))
    · exact False.elim (isolated _ hi (e.trans last))
    · exact inj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ e

end Factors

/-- Four forced repetitions give an unconditional upper bound. -/
theorem upper_bound (n : ℕ) (hn : 6 < n) : a n ≤ n^2-3 :=
  upper_bound_aux (factor := fun i => 1 + ∑ j ∈ range i, (X : ℕ[X]) ^ (2*j+1)) (fun _ => rfl) n hn

/-- Exact reformulation after accounting for all endpoint coefficients. -/
theorem core_iff (n : ℕ) (hn : 6 < n) : a n = n^2-3 ↔
    Set.InjOn (P n).coeff (Set.Icc 0 (n^2-5)) :=
  core_iff_aux (factor := fun i => 1 + ∑ j ∈ range i, (X : ℕ[X]) ^ (2*j+1)) (fun _ => rfl) n hn

/-- Coefficients on each side of a maximum are distinct. -/
def H1 : Prop :=
  ∀ n m : ℕ, 6 < n → m ≤ n^2-5 →
    (∀ k : ℕ, k ≤ n^2-5 → (P n).coeff k ≤ (P n).coeff m) →
    Set.InjOn (P n).coeff (Set.Icc 0 m) ∧ Set.InjOn (P n).coeff (Set.Icc m (n^2-5))

/-- A coefficient strictly before a maximum cannot reappear strictly after it. -/
def H2 : Prop :=
  ∀ n i m j : ℕ, 6 < n → i < m → m < j → j ≤ n^2-5 →
    (∀ k : ℕ, k ≤ n^2-5 → (P n).coeff k ≤ (P n).coeff m) →
    (P n).coeff i ≠ (P n).coeff j

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a039824.main := by
  intro h1 h2 n hn
  apply (core_iff n hn).mpr
  obtain ⟨m, hm, maximum⟩ := exists_max_image (Finset.Icc 0 (n^2-5)) (P n).coeff
    ⟨0, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have limit := (mem_Icc.mp hm).2
  have maximal (k : ℕ) (hk : k ≤ n^2-5) := maximum k (mem_Icc.mpr ⟨by omega, hk⟩)
  obtain ⟨left, right⟩ := h1 n m hn limit maximal
  have distinct {i j : ℕ} (h : i < j) (hj : j ≤ n^2-5) : (P n).coeff i ≠ (P n).coeff j := by
    by_cases hl : j ≤ m
    · exact fun e => Nat.ne_of_lt h (left ⟨by omega, by omega⟩ ⟨by omega, hl⟩ e)
    by_cases hr : m ≤ i
    · exact fun e => Nat.ne_of_lt h (right ⟨hr, by omega⟩ ⟨by omega, hj⟩ e)
    exact h2 n i m j hn (by omega) (by omega) hj maximal
  intro i hi j hj e
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (distinct h hj.2 e)
  · exact h
  · exact False.elim (distinct h hi.2 e.symm)

end OMA.R_oeis_a039824_R1
