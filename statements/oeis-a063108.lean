import Mathlib

/-!
# A063108: a(1) = 1; thereafter a(n+1) = a(n) + product of nonzero digits of a(n).

Source: https://oeis.org/A063108
Credit: @gblacher2

The source comment: "Conjecture: no matter what the starting term is, the sequence eventually
joins this one." (base 10; the remark about other bases is not part of this statement).

Reading: the terms of OEIS sequences here are positive integers, so the starting term `s` ranges
over positive integers. "Eventually joins this one" means that some term of the sequence started
at `s` equals some term of A063108; from there on both sequences coincide, since each term
determines the next.
-/

namespace OMA.S_oeis_a063108

/-- Product of the nonzero decimal digits of `n` (A051801). -/
def prodNonzeroDigits (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· ≠ 0)).prod

/-- One step of the recurrence: `x ↦ x + (product of nonzero digits of x)` (A063114). -/
def step (n : ℕ) : ℕ :=
  n + prodNonzeroDigits n

/-- A063108 with offset 1: `a 1 = 1`, `a (n + 1) = step (a n)`. -/
def a (n : ℕ) : ℕ :=
  step^[n - 1] 1

theorem main :
    ∀ s : ℕ, 0 < s → ∃ i n : ℕ, 1 ≤ n ∧ step^[i] s = a n := by
  sorry

end OMA.S_oeis_a063108
