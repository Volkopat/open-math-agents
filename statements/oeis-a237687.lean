import Mathlib

/-!
# A237687: Primes p with pi(p), pi(pi(p)) and pi(p^2) all prime, where pi(.) is given by A000720

Source: https://oeis.org/A237687
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A237687): The sequence has infinitely many terms.

Conventions:
* pi(x) is the number of primes <= x, Mathlib's `Nat.primeCounting`.
-/

namespace OMA.S_oeis_a237687

/-- Sun's conjecture on A237687: there are infinitely many primes `p` with `pi(p)`, `pi(pi(p))`
and `pi(p^2)` all prime. -/
theorem main :
    {p : ℕ | p.Prime ∧ (Nat.primeCounting p).Prime ∧
      (Nat.primeCounting (Nat.primeCounting p)).Prime ∧
      (Nat.primeCounting (p ^ 2)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a237687
