import OMAStatements.S_oeis_a208342
import Mathlib

open OMA.S_oeis_a208342

open Polynomial

private noncomputable def P (m : ℕ) : ℤ[X] := (uv m).1
private noncomputable def Q (m : ℕ) : ℤ[X] := (uv m).2

private lemma P_succ (m : ℕ) : P (m + 1) = P m + X * Q m := rfl
private lemma Q_succ (m : ℕ) : Q (m + 1) = X * P m + X * Q m := rfl

private lemma P_rec (m : ℕ) : P (m + 2) = P (m + 1) + X * P (m + 1) + X * (X * P m) - X * P m := by
  have e2 := P_succ (m + 1)
  have e3 := Q_succ m
  have e1 := P_succ m
  linear_combination e2 + X * e3 - X * e1

private lemma deg0 (m : ℕ) : ∀ i, m < i → (P m).coeff i = 0 ∧ (Q m).coeff i = 0 := by
  induction m with
  | zero =>
    intro i hi
    simp [P, Q, uv, coeff_one]; omega
  | succ m ih =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [P_succ, Q_succ, coeff_add, coeff_add]
    simp only [coeff_X_mul]
    have h1 := ih (j + 1) (by omega)
    have h2 := ih j (by omega)
    rw [h1.1, h2.1, h2.2]; simp

private def g (i E : ℕ) : ℤ := ∑ j ∈ Finset.range (i + 1), ((i - j).choose j : ℤ) * ((E + j).choose j : ℤ)

private def f (m i : ℕ) : ℤ := if i ≤ m then g i (m - i) else 0

private lemma g0 (E : ℕ) : g 0 E = 1 := by simp [g]

private lemma g1 (E : ℕ) : g 1 E = 1 := by simp [g, Finset.sum_range_succ]

private def s (I : ℕ) : ℤ := ∑ j ∈ Finset.range (I + 1), ((I - j).choose j : ℤ)

private lemma g_zero (I : ℕ) : g I 0 = s I := by
  unfold g s; apply Finset.sum_congr rfl; intro j _; simp

private lemma gfib (i : ℕ) : g (i + 2) 0 = g (i + 1) 0 + g i 0 := by
  rw [g_zero, g_zero, g_zero]
  have e2 : s (i + 2) = ∑ j ∈ Finset.range (i + 2), ((i - j).choose j : ℤ) +
      ∑ j ∈ Finset.range (i + 2), ((i - j).choose (j + 1) : ℤ) + 1 := by
    unfold s
    rw [Finset.sum_range_succ' (fun j => ((i + 2 - j).choose j : ℤ)) (i + 2)]
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
    rw [← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp at hj
    rcases Nat.lt_or_ge i j with h | h
    · rw [show i + 2 - (j + 1) = 0 by omega, show i - j = 0 by omega]
      simp [Nat.choose_eq_zero_of_lt (show 0 < j by omega)]
    · rw [show i + 2 - (j + 1) = (i - j) + 1 by omega, Nat.choose_succ_succ]; push_cast; ring
  have e1 : s (i + 1) = ∑ j ∈ Finset.range (i + 2), ((i - j).choose (j + 1) : ℤ) + 1 := by
    unfold s
    rw [Finset.sum_range_succ' (fun j => ((i + 1 - j).choose j : ℤ)) (i + 1)]
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
    congr 1
    rw [Finset.sum_range_succ (fun j => ((i - j).choose (j + 1) : ℤ)) (i + 1), show i - (i + 1) = 0 by omega,
      Nat.choose_zero_succ]
    simp only [Nat.cast_zero, add_zero]
    apply Finset.sum_congr rfl; intro j _; rw [show i + 1 - (j + 1) = i - j by omega]
  have e0 : s i = ∑ j ∈ Finset.range (i + 2), ((i - j).choose j : ℤ) := by
    unfold s
    rw [Finset.sum_range_succ (fun j => ((i - j).choose j : ℤ)) (i + 1), show i - (i + 1) = 0 by omega,
      Nat.choose_zero_succ]
    simp
  rw [e2, e1, e0]; ring

private lemma gexp (I E : ℕ) : g (I + 1) E =
    ∑ j ∈ Finset.range (I + 1), ((I - j).choose (j + 1) : ℤ) * ((E + (j + 1)).choose (j + 1) : ℤ) + 1 := by
  unfold g
  rw [Finset.sum_range_succ' (fun j => ((I + 1 - j).choose j : ℤ) * ((E + j).choose j : ℤ)) (I + 1)]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, add_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show I + 1 - (j + 1) = I - j by omega]

private lemma L1 (I E : ℕ) : g (I + 1) (E + 1) - g (I + 1) E =
    ∑ j ∈ Finset.range (I + 1), ((I - j).choose (j + 1) : ℤ) * ((E + 1 + j).choose j : ℤ) := by
  rw [gexp, gexp]
  rw [show ∀ a b c : ℤ, a + c - (b + c) = a - b from fun a b c => by ring, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show E + 1 + (j + 1) = (E + 1 + j) + 1 by ring,
    show E + (j + 1) = E + 1 + j by ring, Nat.choose_succ_succ]
  push_cast; ring

private lemma gid (i D : ℕ) : g (i + 2) (D + 1) = g (i + 2) D + g (i + 1) (D + 1) + g i (D + 1) - g (i + 1) D := by
  have a1 := L1 (i + 1) D
  have a2 := L1 i D
  have key : (∑ j ∈ Finset.range (i + 1 + 1), ((i + 1 - j).choose (j + 1) : ℤ) * ((D + 1 + j).choose j : ℤ)) -
      ∑ j ∈ Finset.range (i + 1), ((i - j).choose (j + 1) : ℤ) * ((D + 1 + j).choose j : ℤ) = g i (D + 1) := by
    rw [Finset.sum_range_succ _ (i + 1), show i + 1 - (i + 1) = 0 by omega, Nat.choose_zero_succ]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [← Finset.sum_sub_distrib]
    unfold g
    apply Finset.sum_congr rfl
    intro j hj
    simp at hj
    rw [show i + 1 - j = (i - j) + 1 by omega, Nat.choose_succ_succ, show D + 1 + j = D + 1 + j from rfl]
    push_cast; ring
  rw [show i + 2 = i + 1 + 1 by ring] at *
  linear_combination a1 - a2 + key

private lemma cform : ∀ m, (∀ i, (P m).coeff i = f m i) ∧ (∀ i, (P (m + 1)).coeff i = f (m + 1) i) := by
  intro m
  induction m with
  | zero =>
    constructor
    · intro i
      rcases i with _ | i
      · simp [P, uv, f, g0]
      · simp [P, uv, f, coeff_one]
    · intro i
      rcases i with _ | _ | i
      · simp [P, uv, f, g0]
      · simp [P, uv, f, g1, coeff_one]
      · rw [(deg0 1 (i + 2) (by omega)).1]; simp [f]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    intro i
    have hA := ih.1
    have hB := ih.2
    rw [show m + 1 + 1 = m + 2 by ring, P_rec]
    rcases i with _ | _ | i
    · rw [coeff_sub, coeff_add, coeff_add, coeff_X_mul_zero, coeff_X_mul_zero, coeff_X_mul_zero, hB]
      simp [f, g0]
    · rw [coeff_sub, coeff_add, coeff_add, coeff_X_mul, coeff_X_mul, coeff_X_mul_zero, coeff_X_mul, hB, hB, hA]
      simp [f, g0, g1]
    · rw [coeff_sub, coeff_add, coeff_add, show i + 1 + 1 = i + 2 by ring, coeff_X_mul, coeff_X_mul,
        coeff_X_mul, coeff_X_mul, hB, hB, hA, hA]
      unfold f
      rcases Nat.lt_or_ge m i with h | h
      · rw [if_neg (show ¬ (i + 2 ≤ m + 1) by omega), if_neg (show ¬ (i + 1 ≤ m + 1) by omega),
          if_neg (show ¬ (i ≤ m) by omega), if_neg (show ¬ (i + 1 ≤ m) by omega),
          if_neg (show ¬ (i + 2 ≤ m + 2) by omega)]
        ring
      · rcases Nat.eq_or_lt_of_le h with h2 | h2
        · subst h2
          rw [if_neg (show ¬ (i + 2 ≤ i + 1) by omega), if_pos (show i + 1 ≤ i + 1 by omega),
            if_pos (show i ≤ i by omega), if_neg (show ¬ (i + 1 ≤ i) by omega),
            if_pos (show i + 2 ≤ i + 2 by omega)]
          simp only [Nat.sub_self]
          rw [gfib]
          ring
        · obtain ⟨D, rfl⟩ : ∃ D, m = i + 1 + D := ⟨m - i - 1, by omega⟩
          rw [if_pos (show i + 2 ≤ i + 1 + D + 1 by omega), if_pos (show i + 1 ≤ i + 1 + D + 1 by omega),
            if_pos (show i ≤ i + 1 + D by omega), if_pos (show i + 1 ≤ i + 1 + D by omega),
            if_pos (show i + 2 ≤ i + 1 + D + 2 by omega)]
          rw [show i + 1 + D + 2 - (i + 2) = D + 1 by omega, show i + 1 + D + 1 - (i + 2) = D by omega,
            show i + 1 + D + 1 - (i + 1) = D + 1 by omega, show i + 1 + D - i = D + 1 by omega,
            show i + 1 + D - (i + 1) = D by omega, gid]

theorem OMA.solution : type_of% @OMA.S_oeis_a208342.main := by
  intro n k hk hkn
  unfold T u
  have h := (cform (n - 1)).1 (k - 1)
  unfold P at h
  rw [h]
  unfold f g
  rw [if_pos (by omega), show n - 1 - (k - 1) = n - k by omega, show k - 1 + 1 = k by omega]
  symm
  apply Finset.sum_subset
  · intro x hx; simp at hx ⊢; omega
  · intro x hx hx'
    simp at hx hx'
    rw [Nat.choose_eq_zero_of_lt (show k - 1 - x < x by omega)]; simp
