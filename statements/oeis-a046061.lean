import Mathlib

/-!
# OEIS A046061: 6-multiperfect numbers

Source: https://oeis.org/A046061 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

A046061 lists the 6-multiperfect numbers, the positive integers `n` with `σ(n) = 6 n`,
where `σ` is the sum of divisors. The entry states:

  Conjectured finite and probably these are the only terms; cf. Flammenkamp's link.

We formalize the finiteness conjecture: the set of positive `n` with `σ(n) = 6 n` is finite.
(Completeness of the explicitly listed terms is a separate, weaker-hedged remark and is not
stated here.)
-/

namespace OMA.S_oeis_a046061

/-- The six-multiperfect numbers: positive `n` whose divisor sum is `6 n`. -/
def multiperfect : Set ℕ := {n | 0 < n ∧ ∑ d ∈ n.divisors, d = 6 * n}

/-- Conjecture of A046061: there are only finitely many 6-multiperfect numbers. -/
theorem main : multiperfect.Finite := by
  sorry

end OMA.S_oeis_a046061
