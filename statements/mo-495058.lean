import Mathlib

/-!
# Quadratic-time bounds on the largest singular value

Source: Weather Report, https://mathoverflow.net/questions/495058 (CC BY-SA 4.0).
Credit: @connoranderson.

For a real matrix the exact unit-norm decision and the decision whether a
symmetric matrix is positive semidefinite reduce to one another with quadratic
work. Whether either exact decision itself takes quadratic time is left open.

Pair consecutive rows and sum the largest eigenvalues of their two-by-two
Gram matrices, with a singleton row at the end when needed. The square root
of this sum is an upper bound with worst-case factor sqrt(ceil(n/2)), attained
at the identity. Each pair uses three row inner products and one real square
root, so a dense n-by-m matrix takes O(nm) real arithmetic operations.

For selectable diagonal expansions, the maximum row length gives a lower
bound within any prescribed factor 1+ε after scaling one longest row. The
choice and the bound take O(n²) work for a square matrix. We also give the
sharp lower bound for fixed lower limits on the absolute diagonal entries.
-/
namespace OMA.S_mo_495058
open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
abbrev Rect (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ
abbrev Mat (n : ℕ) := Rect n n
def rowSq {m : ℕ} (r : Fin m → ℝ) : ℝ := ∑ j, (r j)^2
def rowDot {m : ℕ} (r s : Fin m → ℝ) : ℝ := ∑ j,r j*s j
noncomputable def pairTop {m : ℕ} (r s : Fin m → ℝ) : ℝ :=
  (rowSq r+rowSq s+Real.sqrt ((rowSq r-rowSq s)^2+4*(rowDot r s)^2))/2

noncomputable def upperSq {m : ℕ} : {n : ℕ} → Rect n m → ℝ
  | 0,_ => 0
  | 1,A => rowSq (A 0)
  | n+2,A => pairTop (A 0) (A 1) + upperSq (n:=n) (fun i j => A i.succ.succ j)
noncomputable def decisionScale {n : ℕ} (H : Mat n) : ℝ :=
  1 + Real.sqrt (∑ i, ∑ j, (H i j)^2)
noncomputable def maxRow (n : ℕ) (A : Mat n) : ℝ := ‖fun i => Real.sqrt (rowSq (A i))‖
def scale {n : ℕ} (d c : Fin n → ℝ) (A : Mat n) : Mat n := diagonal d*A*diagonal c
theorem main :
    (∀ n m (A : Rect n m), ‖A‖ ≤ 1 ↔
      (fromBlocks (1:Mat n) A A.transpose (1:Mat m)).PosSemidef) ∧
    (∀ n (H : Mat n), H.IsHermitian → (H.PosSemidef ↔
      ‖(1:Mat n) - (decisionScale H)⁻¹ • H‖ ≤ 1)) ∧
    (∀ n m (A : Rect n m), ‖A‖^2 ≤ upperSq A ∧
      upperSq A ≤ (((n+1)/2:ℕ):ℝ)*‖A‖^2) ∧
    (∀ n, upperSq (1:Mat n) = (((n+1)/2:ℕ):ℝ)) ∧
    (∀ n (A : Mat n), maxRow n A ≤ ‖A‖) ∧
    (∀ n (d c : Fin n → ℝ) (a b : ℝ), 0<a → 0<b →
      (∀ i, a≤|d i|) → (∀ j, b≤|c j|) → ∀ A : Mat n, a*b*‖A‖ ≤ ‖scale d c A‖) ∧
    (∀ n (d c : Fin n → ℝ) (i j : Fin n),
      ∃ A : Mat n, ‖A‖=1 ∧ ‖scale d c A‖= |d i| * |c j|) ∧
    (∀ n, 0<n → ∀ (A : Mat n) (ε : ℝ), 0<ε →
      ∃ i : Fin n, Real.sqrt (rowSq (A i))=maxRow n A ∧
        let d : Fin n → ℝ := fun j => if j=i then 2+2*n/ε else 2
        (∀ j, 2≤d j) ∧ ‖scale d (fun _ => 2) A‖ ≤ (1+ε)*maxRow n (scale d (fun _ => 2) A)) := by
  sorry
end OMA.S_mo_495058
