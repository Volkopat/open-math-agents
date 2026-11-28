import Mathlib

/-!
# A002439: Glaisher's T numbers

Source: https://oeis.org/A002439
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Glaisher's T numbers `1, 23, 1681, 257543, …` (offset `0`) have e.g.f.
`sin(2x) / (2 cos(3x)) = ∑ a(n) x^(2n+1) / (2n+1)!`. Conjecture 1 of Peter Bala (OEIS,
Dec 2021): taking the sequence modulo an integer `k` gives an eventually periodic sequence with
period dividing `φ(k)`.

## Encoding

* The e.g.f. is built in `ℚ⟦X⟧` from `PowerSeries.sin`, `PowerSeries.cos` and
  `PowerSeries.rescale`; `a n = (2n+1)! · [x^(2n+1)] (sin 2x / (2 cos 3x))` as a rational
  number (it is an integer).
* "Eventually periodic with period dividing `φ(k)`" is equivalent to: there is `N` with
  `a(n + φ(k)) ≡ a(n) (mod k)` for all `n ≥ N`; congruence of the rationals `a(·)` modulo `k`
  means the difference is `k` times an integer. `k` ranges over positive integers.
* The other conjectures of the same comment are not stated here.
-/

namespace OMA.S_oeis_a002439

open PowerSeries

/-- The e.g.f. `sin 2x / (2 cos 3x)` in `ℚ⟦X⟧`. -/
noncomputable def egf : PowerSeries ℚ :=
  rescale (2 : ℚ) (sin ℚ) * (C (2 : ℚ) * rescale (3 : ℚ) (cos ℚ))⁻¹

/-- `a n = (2n+1)! · [x^(2n+1)] egf`. -/
noncomputable def a (n : ℕ) : ℚ := ((2 * n + 1).factorial : ℚ) * coeff (2 * n + 1) egf

theorem main :
    ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ z : ℤ, a (n + Nat.totient k) - a n = (k : ℚ) * z := by
  sorry

end OMA.S_oeis_a002439
