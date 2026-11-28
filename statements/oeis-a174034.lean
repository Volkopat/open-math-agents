import Mathlib

/-!
# Prime suffixes of concatenated consecutive primes

Eva-Maria Zschorn's OEIS A174034 conjectures that for infinitely many positive indices `n`,
`3` is the least prime suffix that makes the concatenation of the `n`-th prime, the next
prime, and that suffix prime.

Source: https://oeis.org/A174034
-/

namespace OMA.S_oeis_a174034

/-- The prime at positive index `n` in the one-based prime sequence. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Appends the decimal digits of `b` to `a`, counting zero as one digit. -/
def concat10 (a b : ℕ) : ℕ := a * 10 ^ (max 1 (Nat.digits 10 b).length) + b

theorem main :
    {n : ℕ | 1 ≤ n ∧ IsLeast
      {p : ℕ | p.Prime ∧ (concat10 (concat10 (primeAt n) (primeAt (n + 1))) p).Prime}
      3}.Infinite := by
  sorry

end OMA.S_oeis_a174034
