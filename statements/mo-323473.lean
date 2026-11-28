import Mathlib

/-!
# Smallest eigenvalue of a Gram matrix of symmetric contractions

Source: zotachidil, https://mathoverflow.net/questions/323473 (CC BY-SA 4.0).
Credit: @connoranderson. Mikael de la Salle suggested tensor products of four
real orthogonal two-by-two matrices in the source comments. Selecting tensors
with positive transpose sign gives symmetric matrices all the way up to the
dimension of the real symmetric matrix space.

The norm constraint uses the Euclidean operator norm. The Gram matrix uses
the entrywise real inner product specified by the author. At powers of two
its smallest eigenvalue can equal the matrix size, even as the ratio of the
family size to the matrix size diverges. Above the symmetric dimension the
Gram matrix is necessarily singular.
-/

namespace OMA.S_mo_323473
open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator Topology

abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℝ
def gram {n k : ℕ} (A : Fin n → Mat k) : Mat n :=
  fun i j => ∑ x, ∑ y, A i x y * A j x y
def admissible {n k : ℕ} (A : Fin n → Mat k) : Prop :=
  ∀ i, (A i).IsSymm ∧ ‖A i‖ ≤ 1

theorem main :
    (∀ r n : ℕ, n ≤ (2^r+1).choose 2 → ∃ A : Fin n → Mat (2^r),
      admissible A ∧ gram A = (2^r : ℝ) • (1 : Mat n)) ∧
    (∀ k n : ℕ, (k+1).choose 2 < n → ∀ A : Fin n → Mat k,
      (∀ i, (A i).IsSymm) → (gram A).det = 0) ∧
    (∀ (C : ℝ) (F : ℝ → ℝ), Tendsto F atTop atTop →
      ∃ k n : ℕ, 0 < k ∧ k ≤ n ∧ n ≤ k^2 ∧
        C*(k:ℝ)/F ((n:ℝ)/k) < k ∧ ∃ A : Fin n → Mat k,
          admissible A ∧ gram A = (k:ℝ) • (1 : Mat n)) := by
  sorry
end OMA.S_mo_323473
