import OMAStatements.S_oeis_a267879
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 233 from a single ON cell: stage 1 is ON except cells -1, 0, 1; stage 2 is ON
-- except -1 and 1; stage 3 is ON except 0; every cell is ON from stage 4 on. So the middle cells
-- are 1, 0, 1, 0, 1, 1, 1, ... and a(n+1) = 10 a(n) + c(n+1). The closed form follows by
-- induction, the recurrence from a(n) = 10 a(n-1) + 1 for n >= 4, and the g.f. by comparing
-- coefficients of A * (1 - X) * (1 - 10 X).

open PowerSeries

namespace OMA.A267879Proof

open OMA.S_oeis_a267879

lemma s1 (x : ℤ) : state 233 1 x = decide (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) := by
  show step 233 (state 233 0) x = _
  simp only [step, state]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s2 (x : ℤ) : state 233 2 x = decide (x ≠ -1 ∧ x ≠ 1) := by
  show step 233 (state 233 1) x = _
  simp only [step, s1]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s3 (x : ℤ) : state 233 3 x = decide (x ≠ 0) := by
  show step 233 (state 233 2) x = _
  simp only [step, s2]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s4 (x : ℤ) : state 233 4 x = true := by
  show step 233 (state 233 3) x = _
  simp only [step, s3]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma sge (n : ℕ) (x : ℤ) : state 233 (n + 4) x = true := by
  induction n generalizing x with
  | zero => exact s4 x
  | succ n ih =>
    show step 233 (state 233 (n + 4)) x = _
    simp only [step, ih]; decide

lemma c0 : c 0 = 1 := by decide
lemma c1 : c 1 = 0 := by simp [c, s1]
lemma c2 : c 2 = 1 := by simp [c, s2]
lemma c3 : c 3 = 0 := by simp [c, s3]
lemma cge (n : ℕ) : c (n + 4) = 1 := by simp [c, sge]

lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

lemma a0 : a 0 = 1 := by simp [a, c0]
lemma a1 : a 1 = 10 := by rw [a_succ, a0, c1]
lemma a2 : a 2 = 101 := by rw [a_succ, a1, c2]
lemma a3 : a 3 = 1010 := by rw [a_succ, a2, c3]
lemma a_ge (n : ℕ) : a (n + 4) = 10 * a (n + 3) + 1 := by
  rw [a_succ, show n + 3 + 1 = n + 4 by ring, cge]

lemma closed (n : ℕ) : (a (n + 3) : ℚ) = (9091 * 10 ^ n - 1) / 9 := by
  induction n with
  | zero => rw [a3]; norm_num
  | succ n ih =>
    rw [show n + 1 + 3 = n + 4 by ring, a_ge, show n + 3 = n + 3 by rfl]
    push_cast
    rw [ih, pow_succ]
    ring

theorem main' :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    A = (1 - X + X ^ 2 - X ^ 3 + X ^ 4) * ((1 - X) * (1 - 10 * X))⁻¹ ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (9091 * 10 ^ (n - 3) - 1) / 9) := by
  have hrec : ∀ n : ℕ, 4 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    simp only [show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega]
    rw [show j + 5 = (j + 1) + 4 by ring, a_ge, show j + 1 + 3 = j + 4 by ring, a_ge]
    push_cast; ring
  refine ⟨hrec, ?_, ?_⟩
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    have e : A * ((1 - X) * (1 - 10 * X)) = A - C (11:ℚ) * (A * X ^ 1) + C (10:ℚ) * (A * X ^ 2) := by
      simp only [map_ofNat]; ring
    have e2 : (1 - X + X ^ 2 - X ^ 3 + X ^ 4 : ℚ⟦X⟧) = 1 - X ^ 1 + X ^ 2 - X ^ 3 + X ^ 4 := by ring
    rw [e, e2]
    ext n
    simp only [A, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mk, coeff_C,
      coeff_one]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h | h | h | h
    · subst h; simp [a0]
    · subst h; simp [a0, a1]; norm_num
    · subst h; simp [a0, a1, a2]; norm_num
    · subst h; simp [a1, a2, a3]; norm_num
    · subst h
      have : a 4 = 10101 := by rw [a_ge 0, a3]
      simp [a2, a3, this]; norm_num
    · have := hrec n (by omega)
      have hq : (a n : ℚ) = 11 * a (n - 1) - 10 * a (n - 2) := by exact_mod_cast this
      simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega,
        show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, hq]
      all_goals ring
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    rw [closed, Nat.add_sub_cancel]

end OMA.A267879Proof

open OMA.A267879Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a267879.main := main'
