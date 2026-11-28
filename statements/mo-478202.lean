import Mathlib

/-!
# Determinant of a finite group representation

WhatsUp asks how to compute the determinant of a general complex group-algebra
element in a representation using only its character. In the answer, following
Dave Benson's hint, WhatsUp writes out the trace formula in dimension two. The
Newton recursion below applies in every dimension. Its input consists solely of
the coefficients of powers of the group-algebra element and the character values.

Source: https://mathoverflow.net/questions/478202
-/

namespace OMA.S_mo_478202

/-- Newton's recurrence for the elementary symmetric functions, given the power sums. -/
noncomputable def newton (s : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 1 else (-1 : ℂ)^(k+1) / (k : ℂ) *
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k, if _h : a.1 < k then
      (-1 : ℂ)^a.1 * newton s a.1 * s a.2 else 0
termination_by k

/-- Extend a character linearly to the powers of a group-algebra element. -/
noncomputable def characterPowers {G : Type*} [Group G] (χ : G → ℂ)
    (γ : MonoidAlgebra ℂ G) (k : ℕ) : ℂ :=
  (γ^k).coeff.sum fun g x => x * χ g

/-- For a complex representation in any chosen basis, evaluate the character on
powers of the input, then apply the Newton recurrence up to the dimension. -/
theorem main : ∀ (G : Type) [Group G] [Fintype G] (d : ℕ)
    (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (γ : MonoidAlgebra ℂ G),
    (MonoidAlgebra.lift ℂ _ G ρ γ).det =
      newton (characterPowers (fun g => (ρ g).trace) γ) d := by
  sorry

end OMA.S_mo_478202
