import Mathlib

/-!
# A222227: primes at distance 16 bracketing a power of two

Source: https://oeis.org/A222227 (Brad Clardy, 2013)
Credit: @btodder

A222227 lists the numbers $n$ such that $n$ and $n + 16$ are prime and there is a power of two
in the open interval $(n, n + 16)$. Its known terms are
$3, 7, 13, 31, 241, 65521, 1048573, 2305843009213693951$.
The entry states: it is a conjecture that this is a finite sequence.

`main` states that the set of such $n$ is finite. A power of two is $2^k$ with $k : ℕ$, so it can
be $1 = 2^0$; this does not change the set, since $n \ge 2$.
-/

namespace OMA.S_oeis_a222227

/-- `n` and `n + 16` are both prime, and some power of two lies strictly between them. -/
def IsA222227 (n : ℕ) : Prop :=
  n.Prime ∧ (n + 16).Prime ∧ ∃ k : ℕ, n < 2 ^ k ∧ 2 ^ k < n + 16

/-- The sequence A222227 is finite. -/
theorem main : {n : ℕ | IsA222227 n}.Finite := by
  sorry

end OMA.S_oeis_a222227
