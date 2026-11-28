import OMAStatements.S_oeis_a106303

-- Reduction oeis-a106303.R1 of oeis-a106303: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a106303_R1

open OMA.S_oeis_a106303

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, 0 < k → a (5 ^ k) = 781 * 5 ^ (k - 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p : ℕ, p.Prime → a p ≠ a (p ^ 2) → ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a106303.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a106303_R1
