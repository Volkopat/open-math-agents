import Mathlib

/-!
# OEIS A046060: 5-multiperfect numbers

Source: https://oeis.org/A046060 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

A046060 lists the 5-multiperfect numbers, the positive integers `n` with `σ(n) = 5 n`,
where `σ` is the sum of divisors. The entry states:

  Conjectured finite and probably these are the only terms; cf. Flammenkamp's link.

We formalize the finiteness conjecture: the set of positive `n` with `σ(n) = 5 n` is finite.
(Completeness of the explicitly listed terms is a separate, weaker-hedged remark and is not
stated here.)
-/

namespace OMA.S_oeis_a046060

/-- The five-multiperfect numbers: positive `n` whose divisor sum is `5 n`. -/
def multiperfect : Set ℕ := {n | 0 < n ∧ ∑ d ∈ n.divisors, d = 5 * n}

/-- Conjecture of A046060: there are only finitely many 5-multiperfect numbers. -/
theorem main : multiperfect.Finite := by
  sorry

end OMA.S_oeis_a046060
