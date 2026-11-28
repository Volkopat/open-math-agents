import Mathlib

/-!
# A380056: expansion of e.g.f. (exp(x) - 1)/cos(2x)

Source: https://oeis.org/A380056
Credit: @sntntHb

A380056 (offset 1) is defined by `a(n) = n! [x^n] (exp(x) - 1)/cos(2x)`:
`1, 13, 25, 441, 1261, 30213, ...` (and `a(0) = 0`).

Formalizes the two conjectures in OEIS A380056:
* `a(n) == 1 (mod 4)` for every `n >= 1`;
* `a(4n)` is divisible by `5` for every `n >= 1`.
Both are stated with an explicit integer witness, so they include that `a(n)` is an integer.
-/

namespace OMA.S_oeis_a380056

open PowerSeries

/-- The e.g.f. `(exp(x) - 1) / cos(2x)` as a formal power series over `ℚ`. -/
noncomputable def egf : PowerSeries ℚ :=
  (exp ℚ - 1) * (rescale (2 : ℚ) (cos ℚ))⁻¹

/-- A380056: `a(n) = n! * [x^n] egf`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n egf

/-- The two conjectures of A380056. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, a n = 4 * (m : ℚ) + 1) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, a (4 * n) = 5 * (m : ℚ)) := by
  sorry

end OMA.S_oeis_a380056
