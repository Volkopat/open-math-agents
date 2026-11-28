import Mathlib

/-!
# A236249: Primes of the form C(2*m, m) - prime(m), where C(2*m, m) = (2*m)!/(m!)^2.

Source: https://oeis.org/A236249
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A236249): "Though the primes in this sequence are very rare,
according to the conjecture in A236256 there should be infinitely many such primes." That is, there
are infinitely many primes of the form `C(2*m, m) - prime(m)`.

Conventions: `m` ranges over positive integers, since `prime(m)` is the `m`-th prime with
`prime(1) = 2` (OEIS convention), written `Nat.nth Nat.Prime (m - 1)`. `C(2*m, m)` is
`Nat.choose (2 * m) m`. The difference is taken in `ℤ`, so no truncated subtraction is involved.
With these conventions the values of `m` giving primes start 2, 5, 6, 10, 29, 132, as in A236248
(all its terms up to 1000 are reproduced), and the primes start 3, 241, 911, 184727, as in the
data of A236249.
-/

namespace OMA.S_oeis_a236249

/-- `prime m`: the `m`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- The terms of A236249: primes of the form `C(2*m, m) - prime(m)` with `m > 0`. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ m : ℕ, 0 < m ∧ (p : ℤ) = (Nat.choose (2 * m) m : ℤ) - (prime m : ℤ)}

/-- There are infinitely many primes of the form `C(2*m, m) - prime(m)`. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a236249
