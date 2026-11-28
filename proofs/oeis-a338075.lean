import OMAStatements.S_oeis_a338075
import Mathlib

/-!
# A338075: generating function and recurrence for `t(n-1) + t(n)`, `t(n) = (3n)! / n!³`

The generating-function identity is just `a(n) = t(n-1) + t(n)` read coefficientwise.
For the recurrence, the ratio

  `t(n+1) / t(n) = 3 (3n+1)(3n+2) / (n+1)²`

expresses `t(n+1), …, t(n+4)` as rational multiples of `t(n)`; after substituting, the claimed
relation becomes a polynomial identity in `n`.
-/

namespace OMA.S_oeis_a338075

/-- The ratio of consecutive terms of `t`. -/
lemma t_succ (n : ℕ) :
    t (n + 1) = t n * (3 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2)) / ((n : ℚ) + 1) ^ 2 := by
  unfold t
  have e : 3 * (n + 1) = 3 * n + 2 + 1 := by ring
  have h1 : ((3 * n).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [e, Nat.factorial_succ (3 * n + 2), Nat.factorial_succ (3 * n + 1), Nat.factorial_succ (3 * n),
    Nat.factorial_succ n]
  push_cast
  field_simp
  ring

end OMA.S_oeis_a338075

open OMA.S_oeis_a338075 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a338075.main := by
  refine ⟨?_, ?_⟩
  · ext n
    rw [add_mul, one_mul, map_add, coeff_mk, coeff_mk]
    rcases n with _ | n
    · simp [a]
    · rw [coeff_succ_X_mul, coeff_mk]
      simp [a]
      ring
  · intro n
    have a1 : a (n + 1) = t n + t (n + 1) := by simp [a]
    have a2 : a (n + 2) = t (n + 1) + t (n + 2) := by simp [a]
    have a3 : a (n + 3) = t (n + 2) + t (n + 3) := by simp [a]
    have a4 : a (n + 4) = t (n + 3) + t (n + 4) := by simp [a]
    have s1 := t_succ n
    have s2 := t_succ (n + 1)
    have s3 := t_succ (n + 2)
    have s4 := t_succ (n + 3)
    push_cast at s2 s3 s4
    have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    have p1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have p2 : ((n : ℚ) + 1 + 1) ≠ 0 := by positivity
    have p3 : ((n : ℚ) + 2 + 1) ≠ 0 := by positivity
    have p4 : ((n : ℚ) + 3 + 1) ≠ 0 := by positivity
    rw [a1, a2, a3, a4, s4, s3, s2, s1]
    field_simp
    ring
