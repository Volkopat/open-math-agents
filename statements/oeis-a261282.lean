import Mathlib

/-!
# A261282: Least positive integer k such that prime(k)*prime(k*n) = prime(p)+2 for some prime p.

Source: https://oeis.org/A261282
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261282): any positive rational number `r` can be written as `m/n`, where `m` and `n` are positive integers such that `prime(m) prime(n) = prime(p) + 2` for some prime `p`. (The existence of `a(n)` for every `n > 0` is
the case `r = n`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* `S` is the set of pairs `(m, n)` of positive integers with `prime m * prime n = prime p + 2` for a prime `p`; the conjecture says every
  positive rational is `m/n` for some `(m, n) ∈ S`.
-/

namespace OMA.S_oeis_a261282

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- The pairs `(m, n)` in Sun's conjecture. -/
def Good (m n : ℕ) : Prop := 0 < m ∧ 0 < n ∧ ∃ p : ℕ, p.Prime ∧ prime m * prime n = prime p + 2

/-- Sun's conjecture: every positive rational is `m/n` with `Good m n`. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m n : ℕ, Good m n ∧ r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a261282
