import Mathlib

/-!
# Rank and Boolean sup norm of signed homogeneous quadratic polynomials

Source: Turbo, https://mathoverflow.net/questions/210790 (CC BY-SA 3.0).
Credit: @connoranderson.

The upper bound is rank ≤ (8d)^(2/3), and the exponent is optimal. The
four Boolean corner evaluations isolate the bilinear cross term. The
classical sign-matrix switching estimate supplies the order n^(3/2);
see Brown and Spencer, Colloquium Mathematicum 23 (1971), 165–171,
https://doi.org/10.4064/cm-23-1-165-171. The proof here uses elementary
second and fourth moments. Symmetric Sylvester matrices yield quadratics
with full evaluation rank and Boolean norm at most 5 n^(3/2) for n=2^k.

The two symmetric within-block matrices encode the coefficients of the
unordered distinct pairs. The explicit diagonal subtraction and division
by two count each of those monomials once. The remaining vectors specify
the square coefficients. We treat both conventions suggested by the
question: signed square coefficients and the multilinear case. On a
two-variable input, squared terms contribute their two coefficients in
addition to the cross coefficient. The examples obtain full rank under
both conventions.
-/

namespace OMA.S_mo_210790
open Matrix
abbrev V (n : ℕ) := Fin n → ℝ
abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def sign (s : ℝ) : Prop := s=1 ∨ s= -1
def cube {n : ℕ} (x : V n) : Prop := ∀ i,x i=0 ∨ x i=1
structure Form (n : ℕ) where
  left : Sq n
  right : Sq n
  cross : Sq n
  leftSq : V n
  rightSq : V n
def admissible {n : ℕ} (f : Form n) : Prop :=
  f.left.IsSymm ∧ f.right.IsSymm ∧ (∀ i j, i≠j → sign (f.left i j) ∧ sign (f.right i j)) ∧
  (∀ i j,sign (f.cross i j)) ∧
  ((∀ i,sign (f.leftSq i) ∧ sign (f.rightSq i)) ∨ (∀ i, f.leftSq i=0 ∧ f.rightSq i=0))
noncomputable def pureForm {n : ℕ} (M : Sq n) (d x : V n) : ℝ :=
  (x ⬝ᵥ (M *ᵥ x) - ∑ i,M i i*x i^2)/2 + ∑ i,d i*x i^2
noncomputable def value {n : ℕ} (f : Form n) (x y : V n) : ℝ :=
  pureForm f.left f.leftSq x + pureForm f.right f.rightSq y + x ⬝ᵥ (f.cross *ᵥ y)
noncomputable def evaluated {n : ℕ} (f : Form n) : Sq n :=
  Matrix.of fun i j => value f (Pi.single i 1) (Pi.single j 1)

theorem main :
    (∀ n : ℕ, ∀ f : Form n, ∀ i j, evaluated f i j=f.leftSq i+f.rightSq j+f.cross i j) ∧
    (∀ n : ℕ, ∀ f : Form n, admissible f → ∀ d : ℝ,
      (∀ x y : V n,cube x → cube y → |value f x y|≤d) →
      (n:ℝ)*Real.sqrt n ≤ 8*d ∧
      ((evaluated f).rank:ℝ)*Real.sqrt ((evaluated f).rank:ℝ) ≤ 8*d) ∧
    ∀ k : ℕ, ∀ s : ℝ, s=0 ∨ s=1 → ∃ f : Form (2^k), admissible f ∧
      (∀ i,f.leftSq i=s ∧ f.rightSq i= -s) ∧ (evaluated f).rank=2^k ∧
      ∀ x y,cube x → cube y → |value f x y| ≤ 5*(2^k : ℕ)*Real.sqrt (2^k : ℕ) := by
  sorry
end OMA.S_mo_210790
