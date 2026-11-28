import Mathlib

/-!
# Fitting two matrices with an invertible change of coordinates

The matrices in the question can be rectangular. A nonzero single row has
full rank even when it has more than one column. We distinguish this case
from the assumption that each fitting matrix has a left inverse. The square
matrices A and B describe the change of coordinates and its inverse. Under the
left-inverse hypothesis, the equations in `critical` give a real polynomial
system whose least objective value selects exactly the global minimizers.
The final clause tests the proposed Sylvester equation for the orthogonal
scalar example X₁=Y₁=2 and X₂=Y₂=1.

Source: Gautam, https://mathoverflow.net/questions/492407 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_492407
open Matrix
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
def inversePair {d : ℕ} (A B : Mat d d) : Prop := A * B = 1 ∧ B * A = 1
def froSq {m d : ℕ} (U : Mat m d) : ℝ := ∑ i, ∑ j, (U i j)^2
noncomputable def loss {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d) (A B : Mat d d) : ℝ :=
  (froSq (X₁-X₂*A) + froSq (Y₁-Y₂*B))/2
def optimal {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d) (A B : Mat d d) : Prop :=
  inversePair A B ∧ ∀ U V, inversePair U V → loss X₁ X₂ Y₁ Y₂ A B ≤ loss X₁ X₂ Y₁ Y₂ U V

def froInner {m d : ℕ} (U V : Mat m d) : ℝ := ∑ i, ∑ j, U i j * V i j

/-- Polynomial first-order equations obtained by each elementary right variation of A. -/
def critical {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d) (A B : Mat d d) : Prop :=
  inversePair A B ∧ ∀ i j : Fin d,
    froInner (X₁ - X₂*A) ((X₂*A)*Matrix.single i j (1:ℝ)) =
    froInner (Y₁ - Y₂*B) ((Y₂*Matrix.single i j (1:ℝ))*B)

/-- The orthogonality restriction in one dimension compares the two scalar signs. -/
noncomputable def scalarOrthogonalLoss (a : ℝ) : ℝ := ((2-a)^2 + (2-a⁻¹)^2)/2

theorem main :
    (∃ X₁ X₂ Y₁ Y₂ : Mat 1 2, X₁.rank=1 ∧ X₂.rank=1 ∧ Y₁.rank=1 ∧ Y₂.rank=1 ∧
      (∀ A B, inversePair A B → 0 < loss X₁ X₂ Y₁ Y₂ A B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A B, inversePair A B ∧ loss X₁ X₂ Y₁ Y₂ A B < ε) ∧
    (∀ {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d),
      (∃ L : Mat d m, L*X₂=1) → (∃ L : Mat d n, L*Y₂=1) →
      (∃ A B, optimal X₁ X₂ Y₁ Y₂ A B) ∧
      ∀ A B, optimal X₁ X₂ Y₁ Y₂ A B ↔ critical X₁ X₂ Y₁ Y₂ A B ∧
        ∀ U V, critical X₁ X₂ Y₁ Y₂ U V → loss X₁ X₂ Y₁ Y₂ A B ≤ loss X₁ X₂ Y₁ Y₂ U V) ∧
    (∃ a : ℝ, a^2=1 ∧ (∀ b : ℝ, b^2=1 → scalarOrthogonalLoss a ≤ scalarOrthogonalLoss b) ∧
      1*a+a*1 ≠ 1*2+2*1) := by
  sorry

end OMA.S_mo_492407
