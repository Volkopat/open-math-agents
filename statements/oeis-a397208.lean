import Mathlib

/-!
# A397208: primes `q < p` with `(p + q)/4` prime

Source: https://oeis.org/A397208
Credit: @Bondyboy2001

Conventions: the offset is `1`, so `prime(1) = 2`; this is represented by
`Nat.nth Nat.Prime (n - 1)`. Saying that `(p + q)/4` is prime means that the quotient is an
integer prime, so divisibility by `4` is part of the counting predicate.
-/

namespace OMA.S_oeis_a397208

/-- The `n`-th prime, with the OEIS convention `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `a n` is the number of primes `q < prime n` for which `(prime n + q) / 4`
is an integer prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  let p := prime n
  ((Finset.range p).filter fun q =>
    q.Prime ∧ 4 ∣ p + q ∧ ((p + q) / 4).Prime).card

/-- The two conjectures: the only zero terms occur at the primes `2, 3, 11, 19, 43, 67`,
and every nonnegative integer occurs as a term of the sequence. -/
theorem main :
    (∀ n : ℕ, 0 < n →
      (a n = 0 ↔ prime n ∈ ({2, 3, 11, 19, 43, 67} : Finset ℕ))) ∧
      ∀ m : ℕ, ∃ n : ℕ, 0 < n ∧ a n = m := by
  sorry

end OMA.S_oeis_a397208
