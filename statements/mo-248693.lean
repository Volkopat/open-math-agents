import Mathlib

/-!
# Solving the quadratic equation X (Xᵀ ⊙ A) + (X ⊙ A) Xᵀ = B

Source: R. Ho, https://mathoverflow.net/questions/248693 (CC BY-SA 3.0).
Credit: @connoranderson.

For arbitrary real A and B we give a finite system in symmetric column
Gram matrices. The equations involving B are linear in these new
unknowns. Nonnegative diagonals and vanishing 2-by-2 minors characterize
the matrices that can be factored as xxᵀ, including zero. A positive
diagonal pivot recovers each nonzero column by a single square root.

For symmetric weights with positive diagonal and Aᵢᵢ+Aⱼᵢ nonzero for i<j
and for every positive definite B, the recursive function solve gives the
unique lower triangular solution with positive diagonal. Its pivots are
well-defined because its remaining right-hand side is the usual positive
Schur complement plus a positive semidefinite rank-at-most-one correction.
-/

namespace OMA.S_mo_248693
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def equation {n : ℕ} (A X : Mat n) : Mat n :=
  X*(Xᵀ.hadamard A)+(X.hadamard A)*Xᵀ
def gramCode {n : ℕ} (G : Mat n) : Prop := G.IsSymm ∧ (∀ i,0≤G i i) ∧
  ∀ i j k l,G i j*G k l=G i l*G k j
def goodWeight {n : ℕ} (A : Mat n) : Prop :=
  A.IsSymm ∧ (∀ i,0<A i i) ∧ ∀ i j,i<j → A i i+A j i≠0
def lowerPositive {n : ℕ} (X : Mat n) : Prop := (∀ i j,i<j → X i j=0) ∧ ∀ i,0<X i i
def tailM {n : ℕ} (A : Mat (n+1)) : Mat n := A.submatrix Fin.succ Fin.succ
noncomputable def pivot {n : ℕ} (A B : Mat (n+1)) : ℝ := Real.sqrt (B 0 0/(2*A 0 0))
noncomputable def lowerCol {n : ℕ} (A B : Mat (n+1)) (i : Fin n) : ℝ :=
  B i.succ 0/((A 0 0+A i.succ 0)*pivot A B)
noncomputable def residual {n : ℕ} (A B : Mat (n+1)) : Mat n :=
  .of fun i j => B i.succ j.succ-(A i.succ 0+A j.succ 0)*lowerCol A B i*lowerCol A B j
noncomputable def solve : (n : ℕ) → Mat n → Mat n → Mat n
  | 0,_,_ => 0
  | n+1,A,B => .of fun i j => Fin.cases (Fin.cases (pivot A B) (lowerCol A B) i)
      (fun l => Fin.cases 0 (fun k => solve n (tailM A) (residual A B) k l) i) j

theorem main :
    (∀ n : ℕ, ∀ A B : Mat n, (∃ X : Mat n,equation A X=B) ↔
      ∃ G : Fin n → Mat n, (∀ k,gramCode (G k)) ∧
        ∀ i j,B i j=∑ k,(A i k+A k j)*G k i j) ∧
    ∀ n : ℕ, ∀ A B : Mat n, goodWeight A → B.PosDef →
      lowerPositive (solve n A B) ∧ equation A (solve n A B)=B ∧
      ∀ X : Mat n, lowerPositive X → equation A X=B → X=solve n A B := by
  sorry
end OMA.S_mo_248693
