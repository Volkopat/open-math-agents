import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Root separation for polynomials of bounded height

Source: https://mathoverflow.net/questions/468250
Credit: @MMexicann
-/

namespace OMA.S_mo_468250

theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d H : ℕ) (p : Polynomial ℤ), 0 < H →
        p.natDegree ≤ d → (∀ i : ℕ, (p.coeff i).natAbs ≤ H) →
        Irreducible (p.map (Int.castRingHom ℚ)) →
        ∀ z w : ℂ, z ≠ w →
          p.eval₂ (Int.castRingHom ℂ) z = 0 →
          p.eval₂ (Int.castRingHom ℂ) w = 0 →
          Real.rpow (2 * (H : ℝ)) (-(C * (d : ℝ))) < ‖z - w‖ := by
  sorry

end OMA.S_mo_468250
