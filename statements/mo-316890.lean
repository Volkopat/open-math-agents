import Mathlib

/-!
# Singular values of invertible binary matrices

Source: Jacqueline de Beaudrap, https://mathoverflow.net/questions/316890 (CC BY-SA 4.0).
Credit: @connoranderson.

For general invertible zero-one matrices we bound each singular value in terms
of its index and the number of ones. For unit upper triangular zero-one matrices
the Fibonacci envelope bounds every entry of the inverse. One alternating
upper triangular matrix attains the worst inverse Euclidean operator norm, and
hence the smallest possible last singular value, in every positive dimension.
The triangular extremizer is the transpose of the Ilmonen–Haukkanen–Merikoski
matrix, whose extremality was proved by Altınışık, Keskin, Yıldız and Demirbüken
(https://arxiv.org/abs/1507.05112).
-/

namespace OMA.S_mo_316890
open Matrix Finset
open scoped Matrix.Norms.L2Operator
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def binary {n : ℕ} (A : Mat n) : Prop := ∀ i j, A i j=0 ∨ A i j=1
def mass {n : ℕ} (A : Mat n) : ℝ := ∑ i,∑ j,A i j
def unitUpper {n : ℕ} (A : Mat n) : Prop :=
  binary A ∧ (∀ i, A i i=1) ∧ (∀ (i j : Fin n), j < i → A i j = 0)
def fibEnvelope (n : ℕ) : Mat n := fun i j =>
  if i=j then 1 else if i<j then (Nat.fib (j.val-i.val):ℝ) else 0
def extreme (n : ℕ) : Mat n := fun i j =>
  if i=j ∨ (i<j ∧ (j.val-i.val)%2=1) then 1 else 0
def signs (n : ℕ) : Mat n := Matrix.diagonal fun i => (-1:ℝ)^i.val
noncomputable def sv {n : ℕ} (A : Mat n) (i : ℕ) : ℝ := A.toEuclideanLin.singularValues i

theorem main :
    (∀ (n : ℕ), 1≤n → ∀ (A : Mat n), binary A → A.det≠0 → ∀ i : Fin n,
      ((i.val:ℝ)+1)*(sv A i.val)^2 ≤ mass A ∧
      (((n-1 : ℕ):ℝ))^(n-1) ≤ (sv A i.val)^2*(mass A)^(n-1)) ∧
    (∀ (n : ℕ) (A : Mat n), unitUpper A → ∀ i j, |A⁻¹ i j| ≤ fibEnvelope n i j) ∧
    (∀ (n : ℕ), unitUpper (extreme n) ∧ ‖(extreme n)⁻¹‖=‖fibEnvelope n‖ ∧
      ∀ (A : Mat n), unitUpper A → ‖A⁻¹‖ ≤ ‖(extreme n)⁻¹‖) ∧
    (∀ (n : ℕ), 0<n → ∀ A : Mat n, unitUpper A →
      sv (extreme n) (n-1) ≤ sv A (n-1)) := by
  sorry
end OMA.S_mo_316890
