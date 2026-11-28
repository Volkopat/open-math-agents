import Mathlib

/-!
# Weak version of Fortune's conjecture

Source: https://math.stackexchange.com/questions/49627/weak-version-of-fortunes-conjecture
Credit: @mgv27

Let $p\# = 2\cdot 3\cdot 5\cdots p$ denote the primorial and $N(x)$ the smallest prime
greater than or equal to $x$. Fortune's conjecture is that $N(p\#+2) - p\#$ is prime for all
$p$. A much weaker version asks if $N(p\#+2) - p\#$ is prime infinitely often. Can this be
proved? (The question is explicitly about this third, weakest version.)

Formalization notes:
* `main` states the weakest version: there are infinitely many primes `p` such that
  `N(p# + 2) - p#` is prime.
* `p#` is Mathlib's `primorial p` (product of the primes `≤ p`).
* `N x` is defined via `Nat.find` on `Nat.exists_infinite_primes x`, the least prime `≥ x`.
  Since `N(p#+2) ≥ p# + 2`, the natural-number subtraction is the true difference.
* For `p = 2, 3, 5, 7, 11, 13, 17` the differences are `3, 5, 7, 13, 23, 17, 19`
  (the Fortunate numbers, OEIS A005235).
-/

namespace OMA.S_mse_49627

/-- `N x`: the smallest prime greater than or equal to `x`. -/
noncomputable def N (x : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes x)

/-- Weak Fortune: `N(p# + 2) - p#` is prime for infinitely many primes `p`. -/
theorem main :
    Set.Infinite {p : ℕ | p.Prime ∧ (N (primorial p + 2) - primorial p).Prime} := by
  sorry

end OMA.S_mse_49627
