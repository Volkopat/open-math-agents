import Mathlib

/-!
# A237259: Least positive integer k < n such that prime(k) + 2 and prime(prime(n-k)) + 2 are both prime, or 0 if such a number k does not exist.

Source: https://oeis.org/A237259
Credit: @eltociear

`a(n)` (offset 1) is the least `k` with `0 < k < n` such that `prime(k) + 2` and
`prime(prime(n - k)) + 2` are both prime, or `0` if there is none. The entry conjectures
(Zhi-Wei Sun):

  a(n) < 2*sqrt(n)*log(3*n) for all n > 0.

`a n` is written as `sInf` of the set of admissible values; `sInf ∅ = 0` in `ℕ`, which is the
entry's convention "or 0 if such a number does not exist". `log` is the natural logarithm. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a237259

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A237259 (`0` when no admissible `k` exists). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ k < n ∧ (prime k + 2).Prime ∧ (prime (prime (n - k)) + 2).Prime}

/-- The conjecture in OEIS A237259: `a(n) < 2 √n log(3n)` for all `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → (a n : ℝ) < 2 * Real.sqrt n * Real.log (3 * n) := by
  sorry

end OMA.S_oeis_a237259
