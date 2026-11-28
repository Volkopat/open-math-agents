import OMAStatements.S_oeis_a292689
import Mathlib

open OMA.S_oeis_a292689


theorem black_eq (i j : ℕ) (h : ¬ (i = 0 ∧ j = 0)) :
    black i j = ((!(i % 3 = 1 && j % 3 = 1)) && black (i / 3) (j / 3)) := by
  rw [black, dif_neg h]

theorem b00 : black 0 0 = true := by rw [black, dif_pos ⟨rfl, rfl⟩]

theorem b01 : black 0 1 = true := by
  rw [black_eq 0 1 (by omega), b00]
  decide

theorem b10 : black 1 0 = true := by
  rw [black_eq 1 0 (by omega), b00]
  decide

/-- R m = (3^m - 1)/2 satisfies 2 R m + 1 = 3^m. -/
theorem R_succ (m : ℕ) : (3 ^ (m + 1) - 1) / 2 = 3 * ((3 ^ m - 1) / 2) + 1 := by
  have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have h2 : (3 ^ m - 1) % 2 = 0 := by
    have : 3 ^ m % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    omega
  rw [pow_succ]
  omega

theorem key : ∀ m : ℕ, 1 ≤ m → ∀ i j : ℕ,
    (i + j = (3 ^ m - 1) / 2 ∨ i + j + 1 = (3 ^ m - 1) / 2) → black i j = true := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    intro i j hij
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · -- level 1: R = 1
      norm_num at hij
      rcases hij with h | h
      · rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact b01
        · exact b10
      · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
        exact b00
    · have ih' := ih hm0
      rw [R_succ m] at hij
      set R := (3 ^ m - 1) / 2 with hR
      have hR1 : 1 ≤ R := by
        have : 3 ≤ 3 ^ m := by
          calc 3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm0
        omega
      have hne : ¬ (i = 0 ∧ j = 0) := by omega
      rw [black_eq i j hne]
      have hmod : ¬ (i % 3 = 1 ∧ j % 3 = 1) := by omega
      have hcoarse : black (i / 3) (j / 3) = true := by
        apply ih'
        omega
      rw [hcoarse]
      simp only [Bool.and_true, Bool.not_eq_true']
      simpa using hmod

theorem geom (K : ℕ) : (∑ k ∈ Finset.range K, 2 ^ k) + 1 = 2 ^ K := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a292689.main := by
  intro m hm
  set K := (3 ^ m - 1) / 2 with hK
  have hK1 : 1 ≤ K := by
    have : 3 ≤ 3 ^ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hA : a K = ∑ k ∈ Finset.range K, 2 ^ k := by
    unfold a
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [key m hm k (K - 1 - k) (Or.inr (by omega)), if_pos rfl]
  have hB : a (K + 1) = ∑ k ∈ Finset.range (K + 1), 2 ^ k := by
    unfold a
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [key m hm k (K + 1 - 1 - k) (Or.inl (by omega)), if_pos rfl]
  rw [hA, hB]
  have g1 := geom K
  have g2 := geom (K + 1)
  rw [pow_succ] at g2
  omega
