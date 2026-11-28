import Mathlib

/-!
# A236245: Primes of the form C(2*m, m) + prime(m), where C(2*m, m) = (2*m)!/(m!)^2.

Source: https://oeis.org/A236245
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A236245): "Although the primes in this sequence are very
rare, by the conjecture in A236241 there should be infinitely many such primes." That is, there
are infinitely many primes of the form `C(2*m, m) + prime(m)`.

Conventions: `m` ranges over positive integers, since `prime(m)` is the `m`-th prime with
`prime(1) = 2` (OEIS convention), written `Nat.nth Nat.Prime (m - 1)`. `C(2*m, m)` is
`Nat.choose (2 * m) m`. With these conventions the values of `m` giving primes start
5, 6, 7, 8, 12, 13, as in A236242, and the primes start 263, 937, 3449, 12889, as in A236245.
-/

namespace OMA.S_oeis_a236245

/-- `prime m`: the `m`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- The terms of A236245: primes of the form `C(2*m, m) + prime(m)` with `m > 0`. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ m : ℕ, 0 < m ∧ p = Nat.choose (2 * m) m + prime m}

/-- There are infinitely many primes of the form `C(2*m, m) + prime(m)`. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a236245
