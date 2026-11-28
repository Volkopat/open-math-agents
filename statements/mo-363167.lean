import Mathlib

/-!
# Sums of squares with missing powers

Source: https://mathoverflow.net/questions/363167 (Chivul, CC BY-SA 4.0).
Credit: @connoranderson

The source defines positive by pointwise nonnegativity. The first part gives the
coefficient form of the Gram matrix criterion. The second refutes the proposed
weighted representation using a square which vanishes at four real points.
-/

namespace OMA.S_mo_363167
open Polynomial

def supported (A : Finset ℕ) (p : ℝ[X]) : Prop := p.support ⊆ A

def ordinarySOS (A : Finset ℕ) (f : ℝ[X]) : Prop :=
  ∃ m : ℕ, ∃ p : Fin m → ℝ[X], (∀ i, supported A (p i)) ∧ f = ∑ i, (p i)^2

def weightedSOS (A : Finset ℕ) (f : ℝ[X]) : Prop :=
  ∃ m : ℕ, ∃ p g : Fin m → ℝ[X],
    (∀ i, supported A (p i) ∧ supported A (g i * p i) ∧ ∀ x : ℝ, 0 ≤ (g i).eval x) ∧
    f = ∑ i, g i * (p i)^2

def sumSupport (A : Finset ℕ) : Finset ℕ := (A.product A).image fun ij => ij.1 + ij.2

def exponents : Finset ℕ := {0, 1, 3, 4}

noncomputable def examplePoly : ℝ[X] := ((X^2 - 1) * (X^2 - 4))^2

theorem main :
    (∀ (A : Finset ℕ) (f : ℝ[X]), ordinarySOS A f ↔
      ∃ Q : Matrix A A ℝ, Q.PosSemidef ∧
        ∀ k, f.coeff k = ∑ i : A, ∑ j : A, if i.val + j.val = k then Q i j else 0) ∧
    0 ∈ exponents ∧ supported (sumSupport exponents) examplePoly ∧
    (∀ x : ℝ, 0 ≤ examplePoly.eval x) ∧ ¬ weightedSOS exponents examplePoly := by
  sorry

end OMA.S_mo_363167
