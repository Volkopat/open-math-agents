import Mathlib

/-!
# OEIS A108770: Numbers k such that k^2 + (k+1)^2 is a brilliant number

Source: https://oeis.org/A108770
Credit: @unserus

OEIS: "Consecutive terms are (254,255) (4099,4100) (11159,11160) (25094,25095)
(31754,31755) (40189,40190) ... Conjecture: There are infinitely many consecutive
values."

A brilliant number (A078972) is a product `p * q` of two primes (not necessarily
distinct) with the same number of decimal digits. The terms of A108770 are the
`k` for which `k^2 + (k+1)^2` is brilliant. The conjecture is that there are
infinitely many `k` such that both `k` and `k + 1` are terms.
-/

namespace OMA.S_oeis_a108770

/-- `m` is a brilliant number: a product of two primes with equally many decimal
digits. -/
def IsBrilliant (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q ∧
    (Nat.digits 10 p).length = (Nat.digits 10 q).length

/-- The terms of A108770. -/
def a108770Set : Set ℕ :=
  {k | IsBrilliant (k ^ 2 + (k + 1) ^ 2)}

/-- There are infinitely many pairs of consecutive terms `k, k + 1` in A108770. -/
theorem main : {k | k ∈ a108770Set ∧ k + 1 ∈ a108770Set}.Infinite := by
  sorry

end OMA.S_oeis_a108770
