import Mathlib

/-!
# A137328: `a(n) = prime(n) - primorial(k)` for the greatest `k` with `primorial(k) ≤ prime(n)`.

Source: https://oeis.org/A137328
Credit: @cjchaffin

Here `primorial(k)` is the product of the first `k` primes (A002110), as in the example
`a(6) = prime(6) - primorial(2) = 13 - 6 = 7`.

Conjecture (on the OEIS page): each prime number appears in this sequence at least once.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`. The empty
product `primorial(0) = 1` is available but is never the greatest admissible `k` for
`n ≥ 1`, since `primorial(1) = 2 ≤ prime(n)`.
-/

namespace OMA.S_oeis_a137328

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Product of the first `k` primes (`k#` in the A002110 sense). -/
noncomputable def primorialFirst (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- Greatest `k` such that `primorialFirst k ≤ prime n`. -/
noncomputable def greatestK (n : ℕ) : ℕ :=
  sSup {k : ℕ | primorialFirst k ≤ prime n}

noncomputable def a (n : ℕ) : ℕ := prime n - primorialFirst (greatestK n)

theorem main : ∀ p : ℕ, p.Prime → ∃ n : ℕ, 1 ≤ n ∧ a n = p := by
  sorry

end OMA.S_oeis_a137328
