import Mathlib

/-!
# A237659: Primes p with pi(p) and pi(p^2) both prime, where pi(.) is given by A000720

Source: https://oeis.org/A237659
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A237659): The sequence has infinitely many terms.

Conventions:
* pi(x) is the number of primes <= x, Mathlib's `Nat.primeCounting`.
-/

namespace OMA.S_oeis_a237659

/-- Sun's conjecture on A237659: there are infinitely many primes `p` with `pi(p)` and `pi(p^2)`
both prime. -/
theorem main :
    {p : ℕ | p.Prime ∧ (Nat.primeCounting p).Prime ∧ (Nat.primeCounting (p ^ 2)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a237659
