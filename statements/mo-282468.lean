import Mathlib

/-!
# A least-degree monic polynomial in a sum of matrix left ideals

Source: Mikhail Goltvanitsa, https://mathoverflow.net/questions/282468 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)

For square matrices of positive size over a finite field, view a polynomial with
matrix coefficients as a matrix of scalar polynomials. Reduce every entry modulo
the determinant of the first monic input. The left-ideal membership test then
takes place in a finite ring. Enumerate monic candidates by their lower coefficient
matrices and increasing degree, up to the smaller degree of the two inputs.
-/

namespace OMA.S_mo_282468
open Polynomial

abbrev Sq (n : ℕ) (K : Type*) := Matrix (Fin (n+1)) (Fin (n+1)) K
noncomputable def asMatrix {K : Type*} [Field K] {n : ℕ} (p : (Sq n K)[X]) :
    Sq n K[X] := matPolyEquiv.symm p
abbrev Residue {K : Type*} [Field K] {n : ℕ} (A : (Sq n K)[X]) :=
  AdjoinRoot (asMatrix A).det
noncomputable def reduce {K : Type*} [Field K] {n : ℕ} (A p : (Sq n K)[X]) :
    Sq n (Residue A) := (AdjoinRoot.mk (asMatrix A).det).mapMatrix (asMatrix p)

def feasible {K : Type*} [Field K] {n : ℕ} (A B p : (Sq n K)[X]) : Prop :=
  ∃ U V : Sq n (Residue A), reduce A p = U * reduce A A + V * reduce A B

noncomputable def candidate {K : Type*} [Field K] {n : ℕ} (d : ℕ)
    (c : Fin d → Sq n K) : (Sq n K)[X] := X^d + ∑ i : Fin d, monomial i (c i)

theorem main : ∀ (K : Type) [Field K] [Fintype K] (n : ℕ) (A B : (Sq n K)[X]),
    A.Monic → B.Monic → Finite (Residue A) ∧
    (∀ p, feasible A B p ↔ ∃ U V, p = U*A+V*B) ∧
    ∃ d ≤ min A.natDegree B.natDegree, ∃ c : Fin d → Sq n K,
      feasible A B (candidate d c) ∧ (candidate d c).Monic ∧ (candidate d c).natDegree = d ∧
      ∀ p : (Sq n K)[X], p.Monic → (∃ U V, p=U*A+V*B) → d ≤ p.natDegree := by
  sorry
end OMA.S_mo_282468
