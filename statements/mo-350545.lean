import Mathlib

/-!
# Critical points of a polynomial with nonnegative coefficients in an open sector

Source: https://mathoverflow.net/questions/350545 (user159888, CC BY-SA 4.0).
Credit: @connoranderson

The angular interval runs counterclockwise from the positive real axis. The radius in the
question is nonnegative, so the origin belongs whenever the angular interval is nonempty.
As in the Gauss–Lucas theorem, the polynomial has positive degree.
-/

namespace OMA.S_mo_350545

/-- Polar angle in the interval from zero inclusive to two pi exclusive. -/
noncomputable def angle (z : ℂ) : ℝ :=
  if z.arg<0 then z.arg + 2*Real.pi else z.arg

def sector (φ : ℝ) (z : ℂ) : Prop :=
  0<φ ∧ (z=0 ∨ (0<angle z ∧ angle z<φ))

theorem main : ∀ (p : Polynomial ℝ) (φ : ℝ), 0<p.natDegree →
    (∀ k, 0≤p.coeff k) → 0≤φ → φ≤2*Real.pi →
    (∀ z : ℂ, Polynomial.aeval z p=0 → sector φ z) →
    ∀ z : ℂ, Polynomial.aeval z p.derivative=0 → sector φ z := by
  sorry

end OMA.S_mo_350545
