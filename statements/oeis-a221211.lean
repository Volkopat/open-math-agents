import Mathlib

/-!
# A221211: cousin primes bracketing a power of two

Source: https://oeis.org/A221211 (Brad Clardy, 2013)
Credit: @btodder

A221211 lists the numbers $n$ such that $n$ and $n + 4$ are prime and there is a power of two in
the open interval $(n, n + 4)$. Its known terms are $3, 7, 13, 127$. The entry states: it is a
conjecture that this is a finite sequence.

`main` states that the set of such $n$ is finite. A power of two is $2^k$ with $k : ℕ$, so it can
be $1 = 2^0$; this does not change the set, since $n \ge 2$.
-/

namespace OMA.S_oeis_a221211

/-- `n` and `n + 4` are both prime, and some power of two lies strictly between them. -/
def IsA221211 (n : ℕ) : Prop :=
  n.Prime ∧ (n + 4).Prime ∧ ∃ k : ℕ, n < 2 ^ k ∧ 2 ^ k < n + 4

/-- The sequence A221211 is finite. -/
theorem main : {n : ℕ | IsA221211 n}.Finite := by
  sorry

end OMA.S_oeis_a221211
