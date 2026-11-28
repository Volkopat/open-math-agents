import Mathlib

/-!
# Sharp row-norm bound for a Hermitian resolvent

Source: https://mathoverflow.net/questions/163012 (neil, CC BY-SA 4.0).
Credit: @connoranderson

The maximum absolute row sum is the induced infinity norm. The bound holds
for all Hermitian matrices and is asymptotically sharp even for real symmetric
matrices with distinct eigenvalues in [0,1]. The extremizing eigenbasis and
matrix are fixed as the positive imaginary shift tends to zero.
-/

namespace OMA.S_mo_163012
open Matrix Filter Topology
abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def shift (δ : ℝ) : ℂ := (δ:ℂ)*Complex.I
noncomputable def resolvent {n : ℕ} (A : CMat n) (δ : ℝ) : CMat n := (shift δ • 1 - A)⁻¹
noncomputable def rowSize {n : ℕ} (M : CMat n) (i : Fin n) : ℝ := ∑ j, ‖M i j‖
def complexify {n : ℕ} (M : RMat n) : CMat n := M.map Complex.ofReal

theorem main :
    (∀ (n : ℕ) (A : CMat n) (δ : ℝ), A.IsHermitian → 0 < δ →
      IsUnit (shift δ • 1-A) ∧
      ∀ i : Fin n, rowSize (resolvent A δ) i ≤ (1+Real.sqrt n)/(2*δ)) ∧
    (∀ (n : ℕ) [NeZero n], ∃ (Q : RMat n) (d : Fin n → ℝ),
      Qᵀ*Q=1 ∧ Q*Qᵀ=1 ∧ Function.Injective d ∧ (∀ i, d i ∈ Set.Icc (0:ℝ) 1) ∧
      Tendsto (fun δ : ℝ => δ*rowSize (resolvent (complexify (Q*diagonal d*Qᵀ)) δ) 0)
        (𝓝[>] 0) (𝓝 ((1+Real.sqrt n)/2))) := by
  sorry
end OMA.S_mo_163012
