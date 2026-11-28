import Mathlib

/-!
# A237260: Least positive integer m < n with prime(prime(m)) + 2 and prime(n-m) + 2 both prime, or 0 if such a number m does not exist.

Source: https://oeis.org/A237260
Credit: @eltociear

`a(n)` (offset 1) is the least `m` with `0 < m < n` such that `prime(prime(m)) + 2` and
`prime(n - m) + 2` are both prime, or `0` if there is none. The entry conjectures (Zhi-Wei Sun):

  a(n) < sqrt(6*n)*log(3*n) for all n > 0.

`a n` is written as `sInf` of the set of admissible values; `sInf ∅ = 0` in `ℕ`, which is the
entry's convention "or 0 if such a number does not exist". `log` is the natural logarithm. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a237260

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A237260 (`0` when no admissible `m` exists). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ m < n ∧ (prime (prime m) + 2).Prime ∧ (prime (n - m) + 2).Prime}

/-- The conjecture in OEIS A237260: `a(n) < √(6n) log(3n)` for all `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → (a n : ℝ) < Real.sqrt (6 * n) * Real.log (3 * n) := by
  sorry

end OMA.S_oeis_a237260
