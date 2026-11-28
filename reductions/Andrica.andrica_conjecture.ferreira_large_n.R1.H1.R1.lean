import OMAReductions.R_Andrica_andrica_conjecture_ferreira_large_n_R1
import Mathlib

-- Credit: @LordMike
-- Port of reductions/Brocard.brocard_conjecture.ferreira_large_n.R1.H1.R1.lean by its author onto the identical hypothesis statement Andrica.andrica_conjecture.ferreira_large_n.R1.H1.

/-!
# Reduction `Brocard.brocard_conjecture.ferreira_large_n.R1.H1`

`H1` of the parent reduction is Oppermann's conjecture for all sufficiently large `x`: for
every large `x`, the pronic interval `(x (x - 1), x ^ 2)` contains a prime and the square
interval `(x ^ 2, x (x + 1))` contains a prime. The two intervals are disjoint, the two
existences are independent, and the parent statement is their conjunction, so it splits into
exactly two closed propositions.

Neither half implies the other: the first lives strictly below `x ^ 2` and the second strictly
above it.
-/

open Filter

namespace OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1_H1_R1

/-- A prime in the pronic interval below `x ^ 2`, for all large `x`. -/
def H1 : Prop := ∀ᶠ x : ℕ in Filter.atTop,
  ∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime

/-- A prime in the square interval above `x ^ 2`, for all large `x`. -/
def H2 : Prop := ∀ᶠ x : ℕ in Filter.atTop,
  ∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime

theorem main : H1 → H2 → OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1.H1 := by
  intro h1 h2
  unfold OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1.H1
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

end OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1_H1_R1
