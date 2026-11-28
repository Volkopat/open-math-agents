import Mathlib

/-!
# A237203: Least positive integer k < n/2 with phi(k)*phi(n-k) a square, or 0 if such a number k does not exist.

Source: https://oeis.org/A237203
Credit: @eltociear

`a(n)` (offset 1) is the least `k` with `0 < k < n/2` such that `φ(k) φ(n - k)` is a perfect
square, or `0` if there is none. The entry conjectures (Zhi-Wei Sun):

  a(n) < sqrt(n)*log(2*n) for all n > 0.

`a n` is written as `sInf` of the set of admissible values; `sInf ∅ = 0` in `ℕ`, which is the
entry's convention "or 0 if such a number does not exist". `log` is the natural logarithm. `k < n/2` is written `2 * k < n`; `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a237203

/-- OEIS A237203 (`0` when no admissible `k` exists). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ 2 * k < n ∧ IsSquare (Nat.totient k * Nat.totient (n - k))}

/-- The conjecture in OEIS A237203: `a(n) < √n log(2n)` for all `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → (a n : ℝ) < Real.sqrt n * Real.log (2 * n) := by
  sorry

end OMA.S_oeis_a237203
