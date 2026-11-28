import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped ComplexOrder

namespace OMA.S_mo_172684

/-- Tensor-product basis indices for the three systems, all of positive dimension. -/
abbrev BasisIndex (a b c : ℕ) :=
  Fin (a + 1) × Fin (b + 1) × Fin (c + 1)

/-- Spectral power on the support, with zero action on the kernel. -/
noncomputable def supportPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Matrix ι ι ℂ) (exponent : ℝ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else x ^ exponent) m

/-- Von Neumann entropy in natural logarithms. -/
noncomputable def vonNeumannEntropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Matrix ι ι ℂ) : ℝ :=
  -(Matrix.trace (cfc (fun x : ℝ => x * Real.log x) m)).re

/-- The ordered trace expression in the second conjecture, extended by
ordinary conditional mutual information at exponent one. -/
noncomputable def renyiConditionalInfo {a b c : ℕ}
    (state : Matrix (BasisIndex a b c) (BasisIndex a b c) ℂ) (exponent : ℝ) : ℝ :=
  let ac : Matrix (Fin (a + 1) × Fin (c + 1)) (Fin (a + 1) × Fin (c + 1)) ℂ :=
    fun x y => ∑ j : Fin (b + 1), state (x.1, j, x.2) (y.1, j, y.2)
  let bc : Matrix (Fin (b + 1) × Fin (c + 1)) (Fin (b + 1) × Fin (c + 1)) ℂ :=
    fun x y => ∑ i : Fin (a + 1), state (i, x.1, x.2) (i, y.1, y.2)
  let cState : Matrix (Fin (c + 1)) (Fin (c + 1)) ℂ :=
    fun x y => ∑ i : Fin (a + 1), ∑ j : Fin (b + 1), state (i, j, x) (i, j, y)
  if exponent = 1 then
    vonNeumannEntropy ac + vonNeumannEntropy bc -
      vonNeumannEntropy cState - vonNeumannEntropy state
  else
    let acPower := supportPower ac ((1 - exponent) / 2)
    let cPower := supportPower cState ((exponent - 1) / 2)
    let bcPower := supportPower bc (1 - exponent)
    let onAC : Matrix (BasisIndex a b c) (BasisIndex a b c) ℂ :=
      fun x y => if x.2.1 = y.2.1 then acPower (x.1, x.2.2) (y.1, y.2.2) else 0
    let onC : Matrix (BasisIndex a b c) (BasisIndex a b c) ℂ :=
      fun x y => if x.1 = y.1 ∧ x.2.1 = y.2.1 then cPower x.2.2 y.2.2 else 0
    let onBC : Matrix (BasisIndex a b c) (BasisIndex a b c) ℂ :=
      fun x y => if x.1 = y.1 then bcPower x.2 y.2 else 0
    Real.log (Matrix.trace
      (supportPower state exponent * onAC * onC * onBC * onC * onAC)).re /
      (exponent - 1)

/-- The second conjecture of the original question, concerning monotonicity
in the Rényi parameter. -/
theorem main :
    ∀ (a b c : ℕ) (state : Matrix (BasisIndex a b c) (BasisIndex a b c) ℂ),
      state.PosSemidef → Matrix.trace state = 1 →
        MonotoneOn (renyiConditionalInfo state) (Set.Ici 0) := by
  sorry

end OMA.S_mo_172684
