import Mathlib

/-!
# OEIS A233341: least m that n applications of r(k) = k - gpf(k) map to 0

Source: https://oeis.org/A233341
Credit: @unserus

OEIS: "r(m) = 1 if and only if m = 1 or m is a prime. Conjecture: Every positive
integer divides infinitely many terms of this sequence."

The map is `r(k) = k - gpf(k)`, where `gpf(k)` is the greatest prime divisor of
`k`, with `gpf(1) = 1` (so that `r(1) = 0`, as a(1) = 1 requires); `r(0) = 0`.
`m` reaches 0 in exactly `n` steps when `r^[n] m = 0` and `r^[j] m ≠ 0` for
`j < n`, and a(n) (n ≥ 1) is the least such `m`. (The "r(m) = 1" in the comment
counts the steps of `m`, not the value of `r`.)

The conjecture: for every `d ≥ 1` there are infinitely many `n` such that the
least `m` reaching 0 in exactly `n` steps exists and is divisible by `d`.
Stating it with `IsLeast` avoids any convention for an empty set.
-/

namespace OMA.S_oeis_a233341

/-- The greatest prime divisor, with `gpf 1 = 1` (and `gpf 0 = 0`). -/
def gpf (k : ℕ) : ℕ := if k = 1 then 1 else k.primeFactors.sup id

/-- The map `r(k) = k - gpf(k)`. -/
def r (k : ℕ) : ℕ := k - gpf k

/-- `m` is mapped to 0 by exactly `n` applications of `r`, and not fewer. -/
def ZeroAfter (n m : ℕ) : Prop := r^[n] m = 0 ∧ ∀ j < n, r^[j] m ≠ 0

/-- Every positive integer divides infinitely many terms of A233341. -/
theorem main :
    ∀ d : ℕ, 1 ≤ d →
      {n : ℕ | 1 ≤ n ∧ ∃ m, IsLeast {m | ZeroAfter n m} m ∧ d ∣ m}.Infinite := by
  sorry

end OMA.S_oeis_a233341
