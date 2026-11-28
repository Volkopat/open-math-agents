import Mathlib

/-!
# The product of principal sines on a real Grassmannian

Source: Jiaji Huang, https://mathoverflow.net/questions/187427 (CC BY-SA),
including the request in the comments for pairwise disjoint subspaces.
Helmholz asked the related question https://mathoverflow.net/questions/149200.
Credit: @connoranderson.
-/
namespace OMA.S_mo_187427
open Matrix
abbrev Rect (n d : ℕ) := Matrix (Fin n) (Fin d) ℝ
def frame {n d} (U : Rect n d) : Prop := Uᵀ*U=1
noncomputable def gap {n d} (U V : Rect n d) : ℝ :=
  Real.sqrt (1-(Uᵀ*V)*(Vᵀ*U)).det
def apart {n d} (U V : Rect n d) : Prop :=
  Disjoint (LinearMap.range U.mulVecLin) (LinearMap.range V.mulVecLin)
def triangle (n d : ℕ) : Prop := ∀ U V W : Rect n d,
  frame U → frame V → frame W → gap U W ≤ gap U V+gap V W

theorem main : (∀ n d : ℕ, triangle n d ↔ d≤1 ∨ n<2*d) ∧
    ∀ n d : ℕ, 2≤d → 2*d≤n → ∀ ε : ℝ, 0<ε →
      ∃ U V W : Rect n d, frame U ∧ frame V ∧ frame W ∧
        apart U V ∧ apart V W ∧ apart U W ∧ gap U W=1 ∧
        0<gap U V ∧ 0<gap V W ∧ gap U V+gap V W<ε := by
  sorry
end OMA.S_mo_187427
