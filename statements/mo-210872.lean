import Mathlib

/-!
# Exact distribution of zero sums among independent uniform integers

Source: https://mathoverflow.net/questions/210872 (Igor Rivin, CC BY-SA 3.0).
Credit: @connoranderson

Coordinates are independent draws, so subsets are subsets of positions,
as clarified by the author. We count nonempty zero sums Y; the variable
including the empty set is 1+Y. Divide the counts by Q^n, Q=2L+1.
Each joint count is the constant coefficient of an explicit product in an
additive monoid algebra (a multivariate Laurent polynomial). Subset-family
inversion gives every point mass exactly. The first moment needs only a
one-variable polynomial. Distinct nonempty incidence vectors determine two
coordinates from the others, giving an explicit uniform second-order error:
for fixed n the chance of two or more nonempty zero sums is O(Q⁻²), and
the chance of exactly one differs from the displayed mean by O(Q⁻²).
-/

namespace OMA.S_mo_210872
open Finset Polynomial
noncomputable section

abbrev Box (n L : ℕ) := Fin n → Fin (2*L+1)
abbrev Mask (n : ℕ) := Finset (Fin n)
def val {L : ℕ} (a : Fin (2*L+1)) : ℤ := (a.val:ℤ)-L
def summ {n L : ℕ} (x : Box n L) (s : Mask n) := ∑ i ∈ s, val (x i)
def labels (n : ℕ) : Finset (Mask n) := univ.erase ∅
def hits {n L : ℕ} (x : Box n L) := (labels n).filter (fun s => summ x s=0)
def mass (n L m : ℕ) := (univ.filter (fun x : Box n L => (hits x).card=m)).card
def tail (n L : ℕ) := (univ.filter (fun x : Box n L => 2 ≤ (hits x).card)).card

abbrev GroupAlg (n : ℕ) := AddMonoidAlgebra ℕ (Mask n → ℤ)
def col {n L : ℕ} (T : Finset (Mask n)) (i : Fin n) (a : Fin (2*L+1)) : Mask n → ℤ :=
  fun s => if s∈T ∧ i∈s then val a else 0
def joint {n : ℕ} (L : ℕ) (T : Finset (Mask n)) : ℕ :=
  (∏ i : Fin n, ∑ a : Fin (2*L+1), (AddMonoidAlgebra.single (col T i a) 1 : GroupAlg n)).coeff 0
def step (L : ℕ) : AddMonoidAlgebra ℕ ℤ := ∑ a : Fin (2*L+1), AddMonoidAlgebra.single (val a) 1
def meanCount (n L : ℕ) := ∑ s ∈ labels n, ((step L)^s.card).coeff 0 * (2*L+1)^(n-s.card)
def law (n L : ℕ) : ℤ[X] :=
  ∑ T ∈ (labels n).powerset, C (joint L T : ℤ) * (X-1)^T.card

theorem main : ∀ n L : ℕ,
    (∀ m, (mass n L m : ℤ)=(law n L).coeff m) ∧
    (∑ x : Box n L,(hits x).card) = meanCount n L ∧
    2*tail n L ≤ (labels n).card*((labels n).card-1)*(2*L+1)^(n-2) ∧
    mass n L 1 ≤ meanCount n L ∧
    meanCount n L ≤ mass n L 1 + (labels n).card*((labels n).card-1)*(2*L+1)^(n-2) := by
  sorry
end
end OMA.S_mo_210872
