import Mathlib

/-!
# Characteristic polynomials after different row and column deletions

Source: GChromodynamics, https://mathoverflow.net/questions/509136 (CC BY-SA 4.0).
Credit: @connoranderson.

The rows and columns retain their original order after deletion. Let p be the
characteristic polynomial previously computed for A. Only adjugate entries in
the interval from the deleted row to the deleted column are required. If H is
this interval submatrix of adj(XI−A), and T shifts the surviving row labels to
the surviving column labels there, the determinant of pT+XH(I−T) is exactly
X times the desired characteristic polynomial times a known power of p.
Consequently even at zeros of p the complete polynomial is recovered by exact
polynomial division. For adjacent indices the last formula takes only four
adjugate entries and scalar polynomial arithmetic.
-/
namespace OMA.S_mo_509136
open Matrix Polynomial Finset

def minor {n : ℕ} {R : Type} (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r c : Fin (n+1)) :
    Matrix (Fin n) (Fin n) R := A.submatrix r.succAbove c.succAbove

abbrev Window {n : ℕ} (r c : Fin (n+1)) := ↥(Finset.uIcc r c)

def select {ι κ R : Type} [DecidableEq ι] [Zero R] [One R] (f : κ → ι) : Matrix ι κ R :=
  fun i j => if i=f j then 1 else 0

def transfer {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1)) :
    Matrix (Fin (n+1)) (Fin (n+1)) R := select (R := R) c.succAbove * (select (R := R) r.succAbove)ᵀ

def shift {n : ℕ} {R : Type} [CommRing R] (r c : Fin (n+1)) :
    Matrix (Window r c) (Window r c) R := (transfer r c).submatrix Subtype.val Subtype.val

noncomputable def adjWindow {n : ℕ} {R : Type} [CommRing R]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r c : Fin (n+1)) :
    Matrix (Window r c) (Window r c) R[X] := A.charmatrix.adjugate.submatrix Subtype.val Subtype.val

theorem main : ∀ {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R),
    (∀ r c : Fin (n+1), X*(minor A r c).charpoly*A.charpoly^(Fintype.card (Window r c)-1) =
      (A.charpoly • shift (R := R[X]) r c +
        (X:R[X]) • (adjWindow A r c*(1-shift (R := R[X]) r c))).det) ∧
    (∀ (r c : Fin (n+1)) (u v : Window r c), shift (R := R[X]) r c u v =
      if (c<r ∧ u.val.val=v.val.val+1) ∨ (r<c ∧ v.val.val=u.val.val+1) then 1 else 0) ∧
    (∀ k : Fin n, A.charpoly*(minor A k.succ k.castSucc).charpoly =
      X*(A.charmatrix.adjugate k.castSucc k.castSucc*A.charmatrix.adjugate k.succ k.succ -
        A.charmatrix.adjugate k.castSucc k.succ*A.charmatrix.adjugate k.succ k.castSucc) -
      A.charpoly*A.charmatrix.adjugate k.castSucc k.succ) := by
  sorry

end OMA.S_mo_509136
