import Mathlib

/-!
# A220951: sexy primes bracketing a power of two

Source: https://oeis.org/A220951 (Brad Clardy, 2013)
Credit: @btodder

A220951 lists the primes $p$ such that $p + 6$ is also prime and there is a power of two in the
open interval $(p, p + 6)$. Its known terms are $5, 7, 11, 13, 31, 61, 251, 4093$. The entry
states: it is conjectured that this is a finite sequence.

`main` states that the set of such $p$ is finite. A power of two is $2^k$ with $k : ℕ$, so it can
be $1 = 2^0$; this does not change the set, since $p \ge 2$.
-/

namespace OMA.S_oeis_a220951

/-- `p` and `p + 6` are both prime, and some power of two lies strictly between them. -/
def IsA220951 (p : ℕ) : Prop :=
  p.Prime ∧ (p + 6).Prime ∧ ∃ k : ℕ, p < 2 ^ k ∧ 2 ^ k < p + 6

/-- The sequence A220951 is finite. -/
theorem main : {p : ℕ | IsA220951 p}.Finite := by
  sorry

end OMA.S_oeis_a220951
