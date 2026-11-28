import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

/-! Source: https://mathoverflow.net/questions/474015 -/

namespace OMA.S_mo_474015

open Polynomial

theorem main :
    ∃ ε : ℝ, 0 < ε ∧
      {p : ℕ | p.Prime ∧ ((X : Polynomial (ZMod p)) ^ 3 - C 2).Splits ∧
        ∀ a : ZMod p, a ^ 3 = 2 → ε * (p : ℝ) < (a.val : ℝ)}.Infinite := by
  sorry

end OMA.S_mo_474015
