import Mathlib

/-!
# A sharp bound for the average of inverse principal pairs

Source: Hans, https://mathoverflow.net/questions/289475 (CC BY-SA 3.0).
Credit: @connoranderson. The coordinate selector extracts a two-by-two
principal matrix. Its transpose embeds the inverse into the original
space. Summing over ordered distinct pairs counts each principal block twice.

If the original diagonal preconditioner has least eigenvalue λ on multiplication
by A, the averaged pair inverse has least eigenvalue at least
(n−1)λ/(n−2+λ) on multiplication by A. Equicorrelation matrices realize
equality for every admissible dimension and every 0<λ≤1.
-/
namespace OMA.S_mo_289475
open Matrix Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

def vertices {n : ℕ} (i j : Fin n) : Fin 2 → Fin n := ![i,j]
def selectPair {n : ℕ} (i j : Fin n) : Matrix (Fin 2) (Fin n) ℝ :=
  fun k l => if vertices i j k=l then 1 else 0
noncomputable def principal {n : ℕ} (A : Mat n) (i j : Fin n) : Mat 2 :=
  A.submatrix (vertices i j) (vertices i j)
noncomputable def liftInv {n : ℕ} (A : Mat n) (i j : Fin n) : Mat n :=
  (selectPair i j)ᵀ * (principal A i j)⁻¹ * selectPair i j
noncomputable def pairAverage {n : ℕ} (A : Mat n) : Mat n :=
  (2*((n:ℝ)-1))⁻¹ • ∑ i, ∑ j ∈ (univ.erase i), liftInv A i j
def diagPart {n : ℕ} (A : Mat n) : Mat n := diagonal (fun i => A i i)
noncomputable def sharp (n : ℕ) (l : ℝ) : ℝ := ((n:ℝ)-1)*l/((n:ℝ)-2+l)

theorem main :
    (∀ (n : ℕ), 2 ≤ n → ∀ A : Mat n, A.PosDef →
      ∃ l m : ℝ, IsLeast (spectrum ℝ ((diagPart A)⁻¹*A)) l ∧
        IsLeast (spectrum ℝ (pairAverage A*A)) m ∧ 0 < l ∧ l ≤ 1 ∧ l ≤ sharp n l ∧ sharp n l ≤ m) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ l : ℝ, 0 < l → l ≤ 1 → ∃ A : Mat n, A.PosDef ∧
      (∀ i, A i i=1) ∧ IsLeast (spectrum ℝ ((diagPart A)⁻¹*A)) l ∧
      IsLeast (spectrum ℝ (pairAverage A*A)) (sharp n l)) := by
  sorry
end OMA.S_mo_289475
