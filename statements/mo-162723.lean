import Mathlib

/-!
# Selecting a principal Hermitian submatrix of maximum Frobenius norm

Source: mohi, https://mathoverflow.net/questions/162723 (CC BY-SA).
The binary objective and clique reduction follow Suvrit's answer. Suvrit
credits S. Jegelka for the discussion leading to the reduction.
Credit: @connoranderson.

The decision equivalence uses an unweighted graph adjacency matrix. More
generally one may add a fixed nonnegative integer to each diagonal entry.
Shifting by the number of vertices makes every input positive semidefinite.
-/

namespace OMA.S_mo_162723
open Finset Matrix
open scoped Matrix.Norms.Frobenius ComplexOrder Classical
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

noncomputable def principalNorm {n : ℕ} (A : Mat n) (S : Finset (Fin n)) : ℝ :=
  ‖A.submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n))‖
noncomputable def binary {n : ℕ} (A : Mat n) (b : Fin n → Bool) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖^2 * (if b i then 1 else 0) * (if b j then 1 else 0)
noncomputable def input {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : Mat n := by
  classical exact fun i j => if i=j then (d:ℂ) else if G.Adj i j then 1 else 0

def threshold (s d : ℕ) : ℝ := (s:ℝ)*d^2 + ((s*(s-1):ℕ):ℝ)

theorem main : ∀ n : ℕ,
    (∀ (A : Mat n), A.IsHermitian →
      (∀ b : Fin n → Bool, (principalNorm A (univ.filter (fun i => b i)))^2 = binary A b) ∧
      ∀ s ≤ n, ∃ S : Finset (Fin n), S.card=s ∧
        ∀ J : Finset (Fin n), J.card ≤ s → principalNorm A J ≤ principalNorm A S) ∧
    ∀ G : SimpleGraph (Fin n), (input G n).PosSemidef ∧
      ∀ d : ℕ, (input G d).IsHermitian ∧ ∀ s ≤ n,
        (∃ S : Finset (Fin n), S.card ≤ s ∧ threshold s d ≤ (principalNorm (input G d) S)^2) ↔
        ∃ S : Finset (Fin n), S.card=s ∧ G.IsClique (S : Set (Fin n)) := by
  sorry

end OMA.S_mo_162723
