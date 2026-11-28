import Mathlib

/-!
# Permutation similarity with many distinct matrix entries

Source: joro, https://mathoverflow.net/questions/448509 (CC BY-SA 4.0).
Nathaniel Johnston noted that distinct diagonal entries pin the permutation.
Contribution by @connoranderson.

A label that occurs exactly once pins both coordinates of its position. The
finite relation `forced` records all such requirements. Once multiplicities
match, the requirements extend to a permutation exactly when consistent. The
remaining indices can then be enumerated in arbitrary order, giving exactly
the stated factorial number of candidates. Padding a binary input with
distinct new labels preserves the original simultaneous permutation problem.
-/
namespace OMA.S_mo_448509
open Finset
abbrev Mat (ι : Type*) := Matrix ι ι ℕ

def entry {ι : Type*} (A : Mat ι) (p : ι × ι) := A p.1 p.2
def labels {ι : Type*} [Fintype ι] (A : Mat ι) : Finset ℕ := univ.image (entry A)
def freq {ι : Type*} [Fintype ι] (A : Mat ι) (v : ℕ) : ℕ :=
  (univ.filter (fun p => entry A p=v)).card
def free {ι : Type*} [Fintype ι] (A : Mat ι) : Finset ι :=
  univ.filter (fun i => ∀ j, freq A (A i j)≠1 ∧ freq A (A j i)≠1)

def similar {ι : Type*} (A B : Mat ι) : Prop :=
  ∃ p : Equiv.Perm ι, ∀ i j, B (p i) (p j) = A i j
noncomputable def cand {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Mat ι) : Finset (Equiv.Perm ι) := by
  classical
  exact univ.filter (fun (p : Equiv.Perm ι) => ∀ i j, freq A (A i j)=1 → B (p i) (p j)=A i j)

def forced {ι : Type*} [Fintype ι] (A B : Mat ι) (i t : ι) : Prop :=
  (∃ j u,freq A (A i j)=1 ∧ B t u=A i j) ∨ (∃ j u,freq A (A j i)=1 ∧ B u t=A j i)
def consistent {ι : Type*} [Fintype ι] (A B : Mat ι) : Prop :=
  (∀ i t u, forced A B i t → forced A B i u → t=u) ∧
  (∀ i j t, forced A B i t → forced A B j t → i=j)

def padded {n : ℕ} (A : Mat (Fin n)) (m : ℕ) : Mat (Fin n ⊕ Fin m) :=
  Matrix.of fun i j => match i,j with
    | .inl x,.inl y => A x y
    | .inr x,.inr y => 3 + (finProdFinEquiv (x,y)).val
    | _,_ => 2

theorem main :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Mat ι),
      ((Fintype.card ι)^2-(Fintype.card ι-(free A).card)^2 ≤ 2*((Fintype.card ι)^2-(labels A).card)) ∧
      (0<Fintype.card ι → (free A).card ≤ 2*((Fintype.card ι)^2-(labels A).card)/(Fintype.card ι)) ∧
      (similar A B ↔ (∀ v,freq A v=freq B v) ∧ ∃ p ∈ cand A B,∀ i j,B (p i) (p j)=A i j) ∧
      ((∀ v,freq A v=freq B v) →
        ((cand A B).Nonempty ↔ consistent A B) ∧ ∀ p ∈ cand A B,
          (cand A B).card=(free A).card.factorial ∧
          ∀ q : Equiv.Perm ι, q ∈ cand A B ↔ ∀ i ∉ free A, q i=p i)) ∧
    (∀ (n m : ℕ) (A B : Mat (Fin n)), (∀ i j,A i j≤1) → (∀ i j,B i j≤1) →
      (similar (padded A m) (padded B m) ↔ similar A B) ∧ m^2 ≤ (labels (padded A m)).card ∧
      ∀ h : ℕ, ((n+n^h)^2-(labels (padded A (n^h))).card)^h ≤ 2^h*(n+n^h)^(h+1)) := by sorry

end OMA.S_mo_448509
