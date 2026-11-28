import Mathlib

/-!
# Sharp time growth for inverse-weighted unit vectors

Source: Matrix9994, https://mathoverflow.net/questions/354351 (CC BY-SA 4.0).
Credit: @connoranderson.

Start with the identity and add the outer product of a unit vector at every
step. The cost sums the Euclidean length of each incoming vector after
multiplication by the inverse of the matrix accumulated at the preceding step.
The worst-case time dependence in dimension two is of square-root order.
Alternating two nearly parallel vectors gives the lower bound. For the upper
bound, the rank-one inverse identity controls the squared lengths by the drop
in the inverse trace, and summation telescopes.
-/
namespace OMA.S_mo_354351
open Matrix Finset
abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

noncomputable def outer {d : ℕ} (x : Vec d) : Mat d := vecMulVec x x
noncomputable def gram {d : ℕ} (x : ℕ → Vec d) (t : ℕ) : Mat d :=
  1 + ∑ i ∈ range t, outer (x i)
noncomputable def length {d : ℕ} (x : Vec d) : ℝ := Real.sqrt (x ⬝ᵥ x)
noncomputable def cost {d : ℕ} (x : ℕ → Vec d) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, length ((gram x t)⁻¹ *ᵥ x t)

theorem main :
    (∀ {d : ℕ} (x : ℕ → Vec d), (∀ i, length (x i)=1) → ∀ T : ℕ,
      (cost x T)^2 ≤ 2*d*T) ∧
    (∀ T : ℕ, 2 ≤ T → ∃ x : ℕ → Vec 2,
      (∀ t, length (x t)=1) ∧ Real.sqrt T ≤ 9*cost x T) ∧
    (∀ (C : ℝ) (T₀ : ℕ), ∃ T : ℕ, T₀ ≤ T ∧ ∃ x : ℕ → Vec 2,
      (∀ t, length (x t)=1) ∧ C*Real.log ((T:ℝ)+1) < cost x T) := by
  sorry

end OMA.S_mo_354351
