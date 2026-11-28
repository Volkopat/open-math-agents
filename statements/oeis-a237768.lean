import Mathlib

/-!
# A237768: Number of primes p < n with pi(n-p) a Sophie Germain prime, where pi(.) is given by A000720.

Source: https://oeis.org/A237768
Credit: @eltociear

`a(n)` (offset 1) counts the primes `p < n` such that `π(n - p)` is a Sophie Germain prime (a prime
`r` with `2r + 1` prime). The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 4, and a(n) = 1 only for n = 5, 12, 20, 21, 26, 27, 30, 31, 32, 60, 61, 68,
  69, 80, 81.

`main` is the conjunction of the two parts. `π(x)` is `Nat.primeCounting x`.
-/

namespace OMA.S_oeis_a237768

/-- `r` is a Sophie Germain prime. -/
abbrev IsSophieGermain (r : ℕ) : Prop := r.Prime ∧ (2 * r + 1).Prime

/-- OEIS A237768: the number of primes `p < n` with `π(n - p)` a Sophie Germain prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => p.Prime ∧ IsSophieGermain (Nat.primeCounting (n - p)))).card

/-- The conjecture in OEIS A237768. -/
theorem main : (∀ n : ℕ, 4 < n → 0 < a n) ∧
    (∀ n : ℕ, 4 < n → a n = 1 →
      n ∈ ({5, 12, 20, 21, 26, 27, 30, 31, 32, 60, 61, 68, 69, 80, 81} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a237768
