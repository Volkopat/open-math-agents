import Mathlib

/-!
# A213677: primes at distance 12 bracketing a power of two

Source: https://oeis.org/A213677 (Brad Clardy, 2013)
Credit: @btodder

A213677 lists the numbers $n$ such that $n$ and $n + 12$ are prime and there is a power of two
in the open interval $(n, n + 12)$. Its known terms are $5, 7, 11, 29, 31, 59, 61, 127, 251,
509, 1019, 1021, 262139, 1048571, 2147483647$. The entry states: it is a conjecture that this is
a finite sequence.

`main` states that the set of such $n$ is finite. A power of two is $2^k$ with $k : ℕ$, so it can
be $1 = 2^0$; this does not change the set, since $n \ge 2$.
-/

namespace OMA.S_oeis_a213677

/-- `n` and `n + 12` are both prime, and some power of two lies strictly between them. -/
def IsA213677 (n : ℕ) : Prop :=
  n.Prime ∧ (n + 12).Prime ∧ ∃ k : ℕ, n < 2 ^ k ∧ 2 ^ k < n + 12

/-- The sequence A213677 is finite. -/
theorem main : {n : ℕ | IsA213677 n}.Finite := by
  sorry

end OMA.S_oeis_a213677
