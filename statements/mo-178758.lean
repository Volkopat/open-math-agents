import Mathlib

/-!
# Regular polygons maximize the sum of chord lengths

Source: John Jiang, https://mathoverflow.net/questions/178758
Credit: @connoranderson.

Half the ordered sum of distances counts each unordered pair once, since
the diagonal distances are zero. Rotating a regular polygon preserves
all its chord lengths, so we fix its first vertex at 1.
-/
namespace OMA.S_mo_178758

noncomputable def distanceSum {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, ‖z j - z i‖) / 2

noncomputable def regular (n : ℕ) (i : Fin n) : ℂ :=
  Complex.exp (Complex.I * ((2*Real.pi*i.val/n : ℝ) : ℂ))

theorem main : ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖=1) →
    distanceSum z ≤ distanceSum (regular n) := by
  sorry
end OMA.S_mo_178758
