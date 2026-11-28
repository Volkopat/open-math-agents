import OMAStatements.S_oeis_a203232
import Mathlib

-- Problem: A203232, the recurrence and generating function of the elementary symmetric function
-- of degree n-1 of the repeating sequence 2, 3, 2, 3, ...
-- Upstream: formal-conjectures statements/oeis-a203232.lean (declaration OMA.S_oeis_a203232.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: two consecutive factors multiply to 6 and add to 5, so the pair (product, symmetric sum)
-- satisfies (p, e) -> (6p, 6e + 5p) every two steps; eliminating p gives the recurrence.

namespace OMA.P_oeis_a203232

open OMA.S_oeis_a203232

theorem digit_pair (n : ℕ) : digit n * digit (n + 1) = 6 ∧ digit n + digit (n + 1) = 5 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [digit, h, Nat.add_mod]

theorem two_step (n : ℕ) :
    products (n + 2) = (6 * (products n).1, 6 * (products n).2 + 5 * (products n).1) := by
  obtain ⟨h1, h2⟩ := digit_pair n
  show (let (p, e) := products (n + 1); (p * digit (n + 1), e * digit (n + 1) + p)) = _
  rw [show products (n + 1) =
      (let (p, e) := products n; (p * digit n, e * digit n + p)) from rfl]
  obtain ⟨p, e⟩ := products n
  simp only [Prod.mk.injEq]
  constructor
  · rw [mul_assoc, h1, mul_comm]
  · linear_combination e * h1 + p * h2

theorem rec4 (k : ℕ) : a (k + 4) = 12 * a (k + 2) - 36 * a k := by
  simp only [a, two_step]
  ring

end OMA.P_oeis_a203232

open PowerSeries OMA.S_oeis_a203232 OMA.P_oeis_a203232 in
theorem OMA.solution : type_of% @OMA.S_oeis_a203232.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using rec4 m
  · rw [show (1 - C 6 * X ^ 2 : ℤ⟦X⟧) ^ 2 * mk a = mk a - C 12 * (X ^ 2 * mk a) + C 36 * (X ^ 4 * mk a) by
      simp; ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      simp [rec4 m]
