import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-! Source: https://mathoverflow.net/questions/462681 -/

namespace OMA.S_mo_462681

theorem main :
    ∀ f : Polynomial ℤ, f.Monic → 0 < f.natDegree →
      (∀ x : ℚ, f.eval₂ (Int.castRingHom ℚ) x ≠ 0) →
      ∀ α β : ℝ, 0 < α → α < β → β < 1 →
        Set.Infinite {p : ℕ | p.Prime ∧
          let g := f.map (Int.castRingHom (ZMod p))
          g.Splits ∧ ∀ r : ZMod p, g.IsRoot r →
            (r.val : ℝ) ∉ Set.Icc (α * (p : ℝ)) (β * (p : ℝ))} := by
  sorry

end OMA.S_mo_462681
