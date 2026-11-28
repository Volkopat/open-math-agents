import Mathlib

/-!
# Moore–Penrose partial isometries in a finite-dimensional Banach algebra

Source: Hannes Thiel, https://mathoverflow.net/questions/481469 (CC BY-SA 4.0).
Counterexample by @connoranderson.

The operator algebra on the five-dimensional space below has a contractive
Moore–Penrose pair and a hermitian projection whose conjugate by the pair
fails the exponential norm test at π. A graph subspace of a product with
an ℓ¹ factor realizes the norm
`max ‖u‖∞ (max ‖v‖∞ (|(v₁+v₂)/2|+|w|))`.
-/

namespace OMA.S_mo_481469
abbrev Pair := ℂ × ℂ
abbrev Aux := WithLp 1 (ℂ × ℂ)
abbrev Ambient := Pair × Aux
def plane : Submodule ℂ Ambient where
  carrier := {x | (WithLp.ofLp x.2).1=(x.1.1+x.1.2)/2}
  zero_mem' := by change 0=(0+0)/2;ring
  add_mem' := by
    intro x y hx hy
    change (WithLp.ofLp x.2).1+(WithLp.ofLp y.2).1=((x.1.1+y.1.1)+(x.1.2+y.1.2))/2
    change (WithLp.ofLp x.2).1=_ at hx
    change (WithLp.ofLp y.2).1=_ at hy
    rw [hx,hy];ring
  smul_mem' := by
    intro a x hx
    change a*(WithLp.ofLp x.2).1=(a*x.1.1+a*x.1.2)/2
    change (WithLp.ofLp x.2).1=_ at hx
    rw [hx];ring
abbrev X := Pair × plane
abbrev Op := X →L[ℂ] X
noncomputable def phaseNorm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (b : A) (t : ℝ) : ℝ :=
  ‖NormedSpace.exp (((t:ℂ)*Complex.I) • b)‖
noncomputable def herm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (b : A) : Prop :=
  ∀ t : ℝ, phaseNorm b t=1
def mp {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (a g : A) : Prop :=
  a*g*a=a ∧ g*a*g=g ∧ herm (a*g) ∧ herm (g*a) ∧ ‖a‖≤1 ∧ ‖g‖≤1
theorem main : CompleteSpace X ∧ CompleteSpace Op ∧ Module.finrank ℂ X=5 ∧
    ∃ a g b : Op, mp a g ∧ herm b ∧ ¬herm (a*b*g) ∧
      2 ≤ phaseNorm (a*b*g) Real.pi := by
  sorry
end OMA.S_mo_481469
