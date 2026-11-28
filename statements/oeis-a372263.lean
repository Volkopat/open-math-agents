import Mathlib

/-!
# OEIS A372263: least odd prime factor of prime(n) + prime(n+1)

Source: https://oeis.org/A372263
Credit: @unserus

OEIS (Robert Israel, Dec 29 2024): "Dickson's conjecture implies that every odd
prime occurs infinitely many times in the sequence."

a(n) is the least odd prime factor of `prime(n) + prime(n+1)` (2 if there is
none). With the 0-indexed `Nat.nth Nat.Prime i`, the `n`-th sum is
`Nat.nth Nat.Prime i + Nat.nth Nat.Prime (i + 1)` with `i = n - 1`. The
statement: every odd prime `ℓ` is the least odd prime factor of infinitely many
of these sums. It is stated with `IsLeast`, so the "2 if none" convention is not
needed.
-/

namespace OMA.S_oeis_a372263

/-- The odd prime factors of the sum of the `i`-th and `(i+1)`-th primes
(0-indexed). -/
def oddPrimeFactors (i : ℕ) : Set ℕ :=
  {r | r.Prime ∧ Odd r ∧ r ∣ Nat.nth Nat.Prime i + Nat.nth Nat.Prime (i + 1)}

/-- Every odd prime occurs infinitely many times in A372263. -/
theorem main :
    ∀ ℓ : ℕ, ℓ.Prime → Odd ℓ → {i : ℕ | IsLeast (oddPrimeFactors i) ℓ}.Infinite := by
  sorry

end OMA.S_oeis_a372263
