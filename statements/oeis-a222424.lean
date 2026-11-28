import Mathlib

/-!
# A222424: primes at distance 14 bracketing a power of two

Source: https://oeis.org/A222424 (Brad Clardy, 2013)
Credit: @btodder

A222424 lists the numbers $n$ such that $n$ and $n + 14$ are prime and there is a power of two
in the open interval $(n, n + 14)$. Its known terms are
$3, 5, 23, 29, 53, 59, 509, 1019, 2039, 262133, 262139, 536870909,
73786976294838206459, 2787593149816327892691964784081045188247543$.
The entry states: it is a conjecture that this is a finite sequence.

`main` states that the set of such $n$ is finite. A power of two is $2^k$ with $k : ℕ$, so it can
be $1 = 2^0$; this does not change the set, since $n \ge 2$.
-/

namespace OMA.S_oeis_a222424

/-- `n` and `n + 14` are both prime, and some power of two lies strictly between them. -/
def IsA222424 (n : ℕ) : Prop :=
  n.Prime ∧ (n + 14).Prime ∧ ∃ k : ℕ, n < 2 ^ k ∧ 2 ^ k < n + 14

/-- The sequence A222424 is finite. -/
theorem main : {n : ℕ | IsA222424 n}.Finite := by
  sorry

end OMA.S_oeis_a222424
