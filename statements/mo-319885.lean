import Mathlib

/-!
# Spectral norm growth under soft thresholding of a real symmetric matrix

Source: Student, https://mathoverflow.net/questions/319885 (CC BY-SA 4.0).
Explicit ternary family and norm calculations by @connoranderson.

The family is indexed by vectors over the field of three elements. An entry is
2 for an orthogonal pair and −1 otherwise. At threshold one this becomes the
zero–one incidence matrix of orthogonality. The formulas below locate the
first strict increase in this family at dimension 27. They also exhibit
growth of order √n, matching the dimension dependence of the universal bound.
-/

namespace OMA.S_mo_319885
abbrev G (k : ℕ) := Fin k → ZMod 3
abbrev Sq (ι : Type*) := Matrix ι ι ℝ
noncomputable def op {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Sq ι) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖
noncomputable def soft {ι : Type*} (r : ℝ) (A : Sq ι) : Sq ι :=
  Matrix.of fun i j => Real.sign (A i j) * max (|A i j|-r) 0
def pair {k : ℕ} (x y : G k) : ZMod 3 := ∑ i,x i*y i
noncomputable def ternary (k : ℕ) : Sq (G k) :=
  Matrix.of fun x y => if pair x y=0 then 2 else -1
theorem main : (∀ (n : ℕ) (A : Sq (Fin n)), A.IsSymm → ∀ r : ℝ, 0 ≤ r →
      op (soft r A) ≤ Real.sqrt n*op A) ∧
    (∀ k : ℕ, let n : ℝ := (3:ℝ)^k
      (ternary k).IsSymm ∧ op (ternary k)=2*Real.sqrt n ∧
      op (soft 1 (ternary k))=(n+Real.sqrt (n^2+24*n))/6 ∧
      (op (ternary k)<op (soft 1 (ternary k)) ↔ 25<n)) := by
  sorry
end OMA.S_mo_319885
