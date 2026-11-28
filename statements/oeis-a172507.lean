import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Rat.Lemmas

/-!
# The denominator conjecture in OEIS A172507

Sources: https://oeis.org/A172507 and https://oeis.org/A078267.
Credit: @jiyongparkphysics.

A172507 tabulates numerators. Its comment separately conjectures that its
sequence of denominators differs from A078267. The first denominator is that
of the finite decimal formed by writing n on both sides of the point. For
example, the entry gives 6.6 as 33/5. A078267 is the least positive integer
that clears the decimal formed by writing n after the point; we use Michael
S. Branicky's 2021 gcd formula from that entry. Both indices start at one.

The denominator list printed in the A172507 comment is inconsistent with
its own 6.6 example. We use the denominator of the specified decimal, as
in the example. The existential inequality below states the conjectured
difference between the two sequences.
-/

namespace OMA.S_oeis_a172507

def scale (n : ℕ) : ℕ := 10 ^ (Nat.digits 10 n).length

def repeatedDecimal (n : ℕ) : ℚ := (n : ℚ) + mkRat n (scale n)

def clearingFactor (n : ℕ) : ℕ := scale n / Nat.gcd n (scale n)

theorem main : ∃ n : ℕ, 1 ≤ n ∧ (repeatedDecimal n).den ≠ clearingFactor n := by
  sorry

end OMA.S_oeis_a172507
