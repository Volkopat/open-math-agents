import OMAStatements.S_oeis_a266680
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 175 from a single ON cell: stage 1 is ON except cell 1, and for n >= 0 stage n + 2
-- is ON except the single cell -n (the OFF cell moves one step left per stage; induction on n).
-- So the middle cells are 1, 1, 0, 1, 1, 1, ... and a(n+1) = 10 a(n) + c(n+1), hence
-- a(n) = 10 a(n-1) + 1 for n >= 3, which gives the recurrence and, by comparing coefficients,
-- the g.f.

open PowerSeries

namespace OMA.A266680Proof

open OMA.S_oeis_a266680

lemma s1 (x : ℤ) : state 175 1 x = decide (x ≠ 1) := by
  show step 175 (state 175 0) x = _
  simp only [step, state]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s2 (x : ℤ) : state 175 2 x = decide (x ≠ 0) := by
  show step 175 (state 175 1) x = _
  simp only [step, s1]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma sgen (n : ℕ) (x : ℤ) : state 175 (n + 2) x = decide (x ≠ -(n : ℤ)) := by
  induction n generalizing x with
  | zero => simpa using s2 x
  | succ n ih =>
    show step 175 (state 175 (n + 2)) x = _
    simp only [step, ih]
    rcases (show x = -(n : ℤ) - 1 ∨ x = -(n : ℤ) ∨ x = -(n : ℤ) + 1 ∨ x < -(n : ℤ) - 1 ∨
        -(n : ℤ) + 1 < x by omega) with h | h | h | h | h <;>
      (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide)

lemma c0 : c 0 = 1 := by decide
lemma c1 : c 1 = 1 := by simp [c, s1]
lemma c2 : c 2 = 0 := by simp [c, s2]
lemma cge (n : ℕ) : c (n + 3) = 1 := by
  have := sgen (n + 1) 0
  simp only [show n + 1 + 2 = n + 3 by ring] at this
  simp only [c, this]
  simp
  omega

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
lemma a1 : a 1 = 11 := by rw [a_succ, a0, c1]
lemma a2 : a 2 = 110 := by rw [a_succ, a1, c2]
lemma a_ge (n : ℕ) : a (n + 3) = 10 * a (n + 2) + 1 := by
  rw [a_succ, show n + 2 + 1 = n + 3 by ring, cge]

theorem main' :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    A = (1 - X ^ 2 + X ^ 3) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  have hrec : ∀ n : ℕ, 3 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    simp only [show j + 4 - 1 = j + 3 by omega, show j + 4 - 2 = j + 2 by omega]
    rw [show j + 4 = (j + 1) + 3 by ring, a_ge, show j + 1 + 2 = j + 3 by ring, a_ge]
    push_cast; ring
  refine ⟨hrec, ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have e : A * ((1 - X) * (1 - 10 * X)) = A - C (11:ℚ) * (A * X ^ 1) + C (10:ℚ) * (A * X ^ 2) := by
    simp only [map_ofNat]; ring
  rw [e]
  ext n
  simp only [A, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mk, coeff_one]
  have a3 : a 3 = 1101 := by rw [a_ge 0, a2]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h | h | h
  · subst h; simp [a0]
  · subst h; simp [a0, a1] <;> norm_num
  · subst h; simp [a0, a1, a2] <;> norm_num
  · subst h; simp [a1, a2, a3] <;> norm_num
  · have := hrec n (by omega)
    have hq : (a n : ℚ) = 11 * a (n - 1) - 10 * a (n - 2) := by exact_mod_cast this
    simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, hq]
    all_goals ring

end OMA.A266680Proof

open OMA.A266680Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a266680.main := main'
