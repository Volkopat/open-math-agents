import Mathlib

/-!
# Binary matrices with badly conditioned Jordan bases

Source: Daniel86, https://mathoverflow.net/questions/300617 (CC BY-SA 4.0).
Credit: @connoranderson.

The condition number uses the Euclidean operator norm over ℂ. In dimension
3m, m ≥ 2, a binary matrix forces the condition number of every Jordan
change of basis to be at least F_(m−1)^m/(2m). The 300-dimensional
example exceeds 300^300. The same bounds even hold if a Jordan form is
replaced by any upper triangular matrix whose nonzero off-diagonal
entries join equal diagonal entries. Every standard Jordan form has
this property, regardless of its block order.

The binary triangular building block is the transpose of the
Ilmonen–Haukkanen–Merikoski matrix. Its inverse has signed Fibonacci
entries as in Altınışık, Keskin, Yıldız and Demirbüken,
https://arxiv.org/abs/1507.05112. A symmetric dilation and an attached
nilpotent shift amplify its inverse entry into the stated bound.
-/
namespace OMA.S_mo_300617
open Matrix
open scoped Matrix.Norms.L2Operator
abbrev Axis (m : ℕ) := Fin m ⊕ (Fin m ⊕ Fin m)
abbrev Sq (ι : Type) := Matrix ι ι ℂ
def primaryUpper {n : ℕ} (J : Sq (Fin n)) : Prop :=
  ∀ i j, i ≠ j → J i j ≠ 0 → i < j ∧ J i i = J j j
def lower {ι : Type} [Fintype ι] [DecidableEq ι] (A : Sq ι) (c : ℝ) : Prop :=
  ∀ (V : Matrix ι (Fin (Fintype.card ι)) ℂ) (W : Matrix (Fin (Fintype.card ι)) ι ℂ)
    (J : Sq (Fin (Fintype.card ι))), V*W=1 → W*V=1 → A*V=V*J →
    primaryUpper J → c ≤ ‖V‖*‖W‖
def binary {ι : Type} (A : Sq ι) : Prop := ∀ i j, A i j=0 ∨ A i j=1

theorem main :
    (∀ p : ℕ, ∃ A : Sq (Axis (p+2)), binary A ∧
      lower A ((Nat.fib (p+1):ℝ)^(p+2)/(2*(p+2):ℕ))) ∧
    (∃ A : Sq (Axis 100), binary A ∧ lower A ((300:ℝ)^300+1)) := by
  sorry
end OMA.S_mo_300617
