import OMAStatements.S_oeis_a006231
import Mathlib

-- Problem: A006231: a(n) = Sum_{k=2..n} n(n-1)...(n-k+1)/k.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a006231.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Proof of R. J. Mathar's recurrence for A006231.

In `ℚ` put `B n = Sum_{k=0..n} n^(k falling)/k` (the `k = 0` term is `0`, the `k = 1` term is `n`),
so `a n = B n - n`, and `e m = Sum_{j=0..m} m^(j falling)` (A000522). The identities
`(j+1)^((i+1) falling) = (j+1) j^(i falling)` and `j^((i+1) falling) = (j-i) j^(i falling)` give
`B (j+1) - B j = e j`, and `e (m+1) = (m+1) e m + 1`. Hence for `m ≥ 2`
`R(m) : a m - m a(m-1) + (m-1) a(m-2) - (m-1) = 0`, and Mathar's recurrence is
`R(n) - 2 R(n-1) + R(n-2)`.
-/

namespace A006231Proof

open OMA.S_oeis_a006231 Finset

/-- `B n = Sum_{k=0..n} n(n-1)...(n-k+1)/k` in `ℚ` (the `k = 0` term is `0`). -/
noncomputable def B (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), (n.descFactorial k : ℚ) / k

/-- `e m = Sum_{j=0..m} m(m-1)...(m-j+1)` (OEIS A000522). -/
noncomputable def e (m : ℕ) : ℚ := ∑ j ∈ range (m + 1), (m.descFactorial j : ℚ)

lemma e_succ (m : ℕ) : e (m + 1) = (m + 1) * e m + 1 := by
  unfold e
  rw [sum_range_succ']
  simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero, Nat.cast_mul, Nat.cast_one,
    mul_sum]
  push_cast
  ring

lemma B_succ (j : ℕ) : B (j + 1) - B j = e j := by
  have h1 : B (j + 1) = ∑ i ∈ range (j + 1), ((j + 1 : ℚ) * (j.descFactorial i : ℚ)) / (i + 1) := by
    unfold B
    rw [sum_range_succ']
    simp only [Nat.succ_descFactorial_succ, Nat.cast_zero, div_zero, add_zero]
    apply sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : B j = ∑ i ∈ range (j + 1), (((j : ℚ) - i) * (j.descFactorial i : ℚ)) / (i + 1) := by
    unfold B
    rw [show (∑ k ∈ range (j + 1), (j.descFactorial k : ℚ) / k) =
        ∑ k ∈ range (j + 2), (j.descFactorial k : ℚ) / k by
      rw [sum_range_succ (n := j + 1), Nat.descFactorial_of_lt (by omega : j < j + 1),
        Nat.cast_zero, zero_div, add_zero]]
    rw [sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    apply sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hij]
    push_cast
    ring
  rw [h1, h2, ← sum_sub_distrib]
  unfold e
  apply sum_congr rfl
  intro i _
  field_simp
  ring

lemma a_eq (n : ℕ) : (a n : ℚ) = B n - n := by
  unfold a B
  rw [Nat.cast_sum]
  have hterm : ∀ k ∈ Icc 2 n, ((n.descFactorial k / k : ℕ) : ℚ) = (n.descFactorial k : ℚ) / k := by
    intro k hk
    have hk1 : 0 < k := by have := (mem_Icc.mp hk).1; omega
    rw [Nat.cast_div ((Nat.dvd_factorial hk1 le_rfl).trans (Nat.factorial_dvd_descFactorial n k))
      (by exact_mod_cast hk1.ne')]
  rw [sum_congr rfl hterm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), sum_eq_sum_Ico_succ_bot (by omega),
      Finset.Ico_add_one_right_eq_Icc]
    simp

lemma diff (j : ℕ) : (a (j + 1) : ℚ) - a j = e j - 1 := by
  rw [a_eq, a_eq]
  have := B_succ j
  push_cast
  linarith

/-- The first-order relation `a m - m a(m-1) + (m-1) a(m-2) = m - 1`, written at `m = j + 2`. -/
lemma rel (j : ℕ) :
    (a (j + 2) : ℚ) - (j + 2) * a (j + 1) + (j + 1) * a j - (j + 1) = 0 := by
  have d1 := diff (j + 1)
  have d0 := diff j
  have es := e_succ j
  linear_combination d1 - (j + 1 : ℚ) * d0 + es

end A006231Proof

open A006231Proof OMA.S_oeis_a006231

theorem OMA.solution : type_of% @OMA.S_oeis_a006231.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
  have r2 := rel (j + 3)
  have r1 := rel (j + 2)
  have r0 := rel (j + 1)
  simp only [show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
    show j + 5 - 3 = j + 2 by omega, show j + 5 - 4 = j + 1 by omega]
  have key : ((a (j + 5) : ℤ) + (-((j + 5 : ℕ) : ℤ) - 2) * a (j + 4) +
      (3 * ((j + 5 : ℕ) : ℤ) - 2) * a (j + 3) + 3 * (-((j + 5 : ℕ) : ℤ) + 2) * a (j + 2) +
      (((j + 5 : ℕ) : ℤ) - 3) * a (j + 1) : ℚ) = 0 := by
    push_cast at r2 r1 r0 ⊢
    linear_combination r2 - 2 * r1 + r0
  exact_mod_cast key
