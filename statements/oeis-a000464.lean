import Mathlib

/-!
# A000464: Expansion of e.g.f. sin(x)/cos(2x)

Source: https://oeis.org/A000464
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the coefficient of `x^(2n+1)/(2n+1)!` in `sin(x)/cos(2x)`: `1, 11, 361, 24611, …`
(offset `0`). Conjecture 1 of Peter Bala (OEIS, Dec 2021): taking `(a(n))_{n ≥ 1}` modulo an
integer `k` gives a purely periodic sequence with period dividing `φ(k)`.

## Encoding

* The e.g.f. is built in `ℚ⟦X⟧` from Mathlib's `PowerSeries.sin`, `PowerSeries.cos` and
  `PowerSeries.rescale 2`; `a n = (2n+1)! · [x^(2n+1)] (sin x / cos 2x)` as a rational number
  (it is an integer).
* "Purely periodic with period dividing `φ(k)`" is equivalent to
  `a(n + φ(k)) ≡ a(n) (mod k)` for all `n ≥ 1`; congruence of the rationals `a(·)` modulo `k`
  means the difference is `k` times an integer. `k` ranges over positive integers.
* The other conjectures of the same comment are not stated here.
-/

namespace OMA.S_oeis_a000464

open PowerSeries

/-- The e.g.f. `sin x / cos 2x` in `ℚ⟦X⟧`. -/
noncomputable def egf : PowerSeries ℚ := sin ℚ * (rescale (2 : ℚ) (cos ℚ))⁻¹

/-- `a n = (2n+1)! · [x^(2n+1)] egf`. -/
noncomputable def a (n : ℕ) : ℚ := ((2 * n + 1).factorial : ℚ) * coeff (2 * n + 1) egf

theorem main :
    ∀ k : ℕ, 0 < k → ∀ n : ℕ, 1 ≤ n →
      ∃ z : ℤ, a (n + Nat.totient k) - a n = (k : ℚ) * z := by
  sorry

end OMA.S_oeis_a000464
