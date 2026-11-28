import Mathlib

/-!
# A062772: smallest prime larger than `prime(n)^2`.

Source: https://oeis.org/A062772 (and A054270)
Credit: @cjchaffin

`a(n)` is the smallest prime `> prime(n)^2`. The companion sequence A054270 is the
largest prime `< prime(n)^2`.

Conjecture (Clark Kimberling, Dec 23 2025): if `k` is an even integer greater than 4,
then `a(n) - A054270(n) = k` for infinitely many `n`.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`. Next and
previous primes are written as `sInf` / `sSup` of the obvious sets (nonempty for
`n ≥ 1`, since `prime(n)^2 ≥ 4`).
-/

namespace OMA.S_oeis_a062772

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Smallest prime strictly larger than `m`. -/
noncomputable def nextPrimeAbove (m : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ m < p}

/-- Largest prime strictly smaller than `m`. -/
noncomputable def prevPrimeBelow (m : ℕ) : ℕ := sSup {q : ℕ | q.Prime ∧ q < m}

/-- Smallest prime larger than `prime(n)^2` (A062772). -/
noncomputable def a (n : ℕ) : ℕ := nextPrimeAbove (prime n ^ 2)

/-- Largest prime below `prime(n)^2` (A054270). -/
noncomputable def b (n : ℕ) : ℕ := prevPrimeBelow (prime n ^ 2)

theorem main : ∀ k : ℕ, Even k → 4 < k →
    {n : ℕ | 1 ≤ n ∧ a n - b n = k}.Infinite := by
  sorry

end OMA.S_oeis_a062772
