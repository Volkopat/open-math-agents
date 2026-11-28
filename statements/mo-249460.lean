import Mathlib

/-!
# Determinants of horizontal restrictions of perfect quadratic forms

Source: Yoav Kallus, https://mathoverflow.net/questions/249460 (CC BY-SA 3.0).
Credit: @connoranderson.

The allowed heights are differences of two elements of the standard basis
augmented by zero. Feasibility requires every nonzero admissible integer point
to have value at least one. Perfection means that the equations at the points
of value exactly one determine the entire real symmetric quadratic form.

For each n and m the determinant of the restriction to the first n coordinates
takes only finitely many values, so in particular has a uniform upper bound.
The complete form can be indefinite. The proof uses integer shears to center
the height layers, bounds integer minors of contact vectors by counting lattice
cosets, and applies Cramer's rule to reduce the determining equations to a
finite grid. No positivity hypothesis on the full form is needed.
-/
namespace OMA.S_mo_249460
open Matrix Finset
abbrev ZV (n : ℕ) := Fin n → ℤ
abbrev RV (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def rv {n : ℕ} (x : ZV n) : RV n := fun i => x i
def bil {n : ℕ} (G : Mat n) (x z : ZV n) : ℝ := rv x ⬝ᵥ (G *ᵥ rv z)
structure Form (n m : ℕ) where
  G : Mat n
  B : Matrix (Fin n) (Fin m) ℝ
  D : Mat m
  symG : G.IsHermitian
  symD : D.IsHermitian
def val {n m : ℕ} (Q : Form n m) (x : ZV n) (y : ZV m) : ℝ :=
  bil Q.G x x + 2*(rv x ⬝ᵥ (Q.B *ᵥ rv y)) + bil Q.D y y
def site {m : ℕ} : Option (Fin m) → ZV m
  | none => 0
  | some i => Pi.single i 1
def allowed {m : ℕ} (y : ZV m) : Prop := ∃ i j : Option (Fin m), y=site i-site j
def feasible {n m : ℕ} (Q : Form n m) : Prop :=
  ∀ x y, allowed y → (x≠0 ∨ y≠0) → 1≤val Q x y
def perfect {n m : ℕ} (Q : Form n m) : Prop := ∀ R : Form n m,
  (∀ x y, allowed y → val Q x y=1 → val R x y=1) → R=Q
def normal {n : ℕ} (G : Mat n) (x : ZV n) : Prop :=
  ∀ z, |2*bil G x z| ≤ 3*bil G z z
theorem main :
    (∀ n m : ℕ, {t : ℝ | ∃ Q : Form n m, feasible Q ∧ perfect Q ∧ Q.G.det=t}.Finite) ∧
    (∀ n m : ℕ, ∃ C : ℝ, ∀ Q : Form n m, feasible Q → perfect Q → Q.G.det ≤ C) := by
  sorry
end OMA.S_mo_249460
