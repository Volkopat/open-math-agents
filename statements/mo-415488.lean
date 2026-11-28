import Mathlib

/-!
# Size of commutators of unitary matrices near the identity

Source: BharatRam, https://mathoverflow.net/questions/415488 (CC BY-SA 4.0).
Credit: @connoranderson. The deterministic block-sum obstruction is due to
Christian Remling in the source discussion. The Frobenius norm is squared below.

The example has k two-dimensional blocks in a space of dimension 2k+k². Its
input distances grow as 2√k and its commutator grows as √(8k), even though the
distances divided by the square root of the dimension tend to zero.

For the statistical question the source specifies no sampling law. Work in an
eigenbasis of the first unitary, and permute the coordinates of the other one
uniformly. The exact average and ensuing bound quantify the shrinkage for this
explicit experiment. They also hold for general diagonal generators and B.
-/

namespace OMA.S_mo_415488
open Finset Matrix
abbrev Sq (I : Type*) := Matrix I I ℂ
abbrev Axis (k : ℕ) := (Fin 2 × Fin k) ⊕ Fin (k*k)
noncomputable def froSq {I : Type*} [Fintype I] (A : Sq I) : ℝ := ∑ i, ∑ j, ‖A i j‖^2
def commutator {I : Type*} [Fintype I] (A B : Sq I) : Sq I := A*B-B*A

noncomputable def meanComm {n : ℕ} (a : Fin n → ℂ) (B : Sq (Fin n)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), froSq (commutator (diagonal a) (B.submatrix σ σ))) /
    (Fintype.card (Equiv.Perm (Fin n)):ℝ)

theorem main :
    (∀ n (A B : unitaryGroup (Fin n) ℂ),
      froSq (commutator (A:Sq (Fin n)) (B:Sq (Fin n))) ≤
        4 * min (froSq ((A:Sq (Fin n))-1)) (froSq ((B:Sq (Fin n))-1))) ∧
    (∀ k : ℕ, ∃ A B : unitaryGroup (Axis k) ℂ,
      froSq ((A:Sq (Axis k))-1)=4*(k:ℝ) ∧ froSq ((B:Sq (Axis k))-1)=4*(k:ℝ) ∧
        froSq (commutator (A:Sq (Axis k)) (B:Sq (Axis k)))=8*(k:ℝ)) ∧
    (∀ (n : ℕ), 2≤n → ∀ (a : Fin n → ℂ) (B : Sq (Fin n)),
      meanComm a B =
        (∑ i, ∑ j, ‖a i-a j‖^2) * (∑ i,∑ j, if i=j then 0 else ‖B i j‖^2) /
          ((n:ℝ)*(n-1)) ∧
      meanComm a B ≤ 2/((n:ℝ)-1) * froSq (diagonal a-1) * froSq (B-1)) := by
  sorry
end OMA.S_mo_415488
