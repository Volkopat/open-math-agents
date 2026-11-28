import OMAStatements.S_oeis_a098664
import Mathlib

-- Problem: A098664, Mathar's conjectured recurrence
-- (n+1) a(n) + 8 (n-1) a(n-1) - 16 n a(n-2) + 128 (2-n) a(n-3) = 0.
-- Upstream: formal-conjectures statements/oeis-a098664.lean (declaration OMA.S_oeis_a098664.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: a(2m) = 4^m (2m)!/(m!)^2 and a(2m+1) = 4^m (2m+1)!/(m! (m+1)!). Splitting on the parity of
-- n, all four terms are explicit multiples of one factorial quotient, and the recurrence reduces to
-- an identity of rational functions.

namespace OMA.P_oeis_a098664

open OMA.S_oeis_a098664

theorem A_even (m : ℕ) : a (2 * m) = (4 : ℚ) ^ m * ((2 * m).factorial : ℚ) / ((m.factorial : ℚ) ^ 2) := by
  unfold a i0 i1
  have he : Even (2 * m) := even_two_mul m
  have ho : ¬ Odd (2 * m) := Nat.not_odd_iff_even.mpr he
  rw [if_pos he, if_neg ho, show 2 * m / 2 = m by omega, pow_mul]
  norm_num
  ring

theorem A_odd (m : ℕ) : a (2 * m + 1) = (4 : ℚ) ^ m * ((2 * m + 1).factorial : ℚ)
    / ((m.factorial : ℚ) * ((m + 1).factorial : ℚ)) := by
  unfold a i0 i1
  have ho : Odd (2 * m + 1) := odd_two_mul_add_one m
  have he : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr ho
  rw [if_neg he, if_pos ho, show (2 * m + 1 - 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
    pow_succ, pow_mul]
  norm_num
  ring

theorem main' : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + 8 * ((n : ℚ) - 1) * a (n - 1) - 16 * (n : ℚ) * a (n - 2)
      + 128 * (2 - (n : ℚ)) * a (n - 3) = 0 := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [show 2 * (j + 2) - 1 = 2 * (j + 1) + 1 by omega, show 2 * (j + 2) - 2 = 2 * (j + 1) by omega,
      show 2 * (j + 2) - 3 = 2 * j + 1 by omega]
    rw [A_even, A_odd, A_even, A_odd]
    rw [show 2 * (j + 2) = 2 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
      show 2 * (j + 1) = 2 * j + 2 by ring]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (j + 1) + 1 - 1 = 2 * (j + 1) by omega, show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 1 - 3 = 2 * j by omega]
    rw [A_odd, A_even, A_odd, A_even]
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a098664

theorem OMA.solution : type_of% @OMA.S_oeis_a098664.main := OMA.P_oeis_a098664.main'
