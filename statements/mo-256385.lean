import Mathlib

/-!
# Sharp bounds for the extreme eigenvalues of weighted Gram matrices

Source: Samrat Mukhopadhyay, https://mathoverflow.net/questions/256385 (CC BY-SA 3.0).
Credit: @connoranderson.

Let e₀ ≥ ⋯ ≥ eₙ₋₁ be the eigenvalues of AᵀA, and sort the m row weights
d₀ ≥ ⋯ ≥ dₘ₋₁ ≥ 0. The least eigenvalue of AᵀDA is at most every
eᵢ dₙ₋₁₋ᵢ. Its greatest eigenvalue is at least every eᵢ dₘ₋₁₋ᵢ. These
give upper bounds on the two gaps in the usual extreme-weight estimates.
For prescribed squared singular values and weights, the minimum of the first
products and maximum of the second products are attained by explicit matrices.
A two-row example shows that the elementary estimates can miss both extremes
by arbitrarily large multiplicative factors.
-/
namespace OMA.S_mo_256385
open Matrix
abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
noncomputable def gram {m n : ℕ} (A : Rect m n) := Aᵀ*A
noncomputable def weighted {m n : ℕ} (A : Rect m n) (d : Fin m → ℝ) := Aᵀ*diagonal d*A
noncomputable def low {n : ℕ} (M : Rect n n) := sInf (spectrum ℝ M)
noncomputable def high {n : ℕ} (M : Rect n n) := sSup (spectrum ℝ M)
noncomputable def ordered {m n : ℕ} (A : Rect m n) (i : Fin n) : ℝ :=
  let h : (gram A).IsHermitian := by simpa [gram] using isHermitian_conjTranspose_mul_self A
  h.eigenvalues₀ ⟨i.val,by simp⟩
def reverseTop {m n : ℕ} (h : n ≤ m) (i : Fin n) : Fin m := ⟨n-1-i.val,by omega⟩
def reverseBottom {m n : ℕ} (h : n ≤ m) (i : Fin n) : Fin m := ⟨m-1-i.val,by omega⟩

theorem main :
    (∀ {m n : ℕ} (h : n+1 ≤ m+1) (A : Rect (m+1) (n+1)) (d : Fin (m+1) → ℝ),
      Antitone d → (∀ j, 0 ≤ d j) → ∀ i : Fin (n+1),
      d (Fin.last m)*low (gram A) ≤ low (weighted A d) ∧
      low (weighted A d) ≤ d (reverseTop h i)*ordered A i ∧
      d (reverseBottom h i)*ordered A i ≤ high (weighted A d) ∧
      high (weighted A d) ≤ d 0*high (gram A)) ∧
    (∀ {m n : ℕ} (h : n+1 ≤ m+1) (e : Fin (n+1) → ℝ) (d : Fin (m+1) → ℝ),
      (∀ i, 0 ≤ e i) → ∃ L H : Rect (m+1) (n+1), gram L = diagonal e ∧ gram H = diagonal e ∧
        low (weighted L d) = sInf (Set.range fun i => d (reverseTop h i)*e i) ∧
        high (weighted H d) = sSup (Set.range fun i => d (reverseBottom h i)*e i)) ∧
    (∀ t : ℝ, 1 ≤ t → ∃ A : Rect 2 2, A 0 1=1 ∧ gram A=diagonal ![t^2,1] ∧
      weighted A ![1,(t^2)⁻¹]=1) := by
  sorry
end OMA.S_mo_256385
