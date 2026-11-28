import FormalConjectures.GreensOpenProblems.«66»

-- Credit: @PetrouilFan
-- Reduction of Green's problem 66.  The weak bound with an arbitrary positive
-- constant is already proved upstream (variants.trivial_bound).  The genuinely
-- open content is strengthening that constant to 1/10, isolated as H2.

open Filter Set

namespace OMA.R_Green66_green_66_R1

-- Upstream-proved weak bound: some interval of width C * X^(1/4) works.
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
    ∃ n : ℕ, Green66.IsSumOfTwoSquares n ∧
      (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X

-- Open core: the constant can always be improved to 1/10.
def H2 : Prop :=
  ∀ C : ℝ, 0 < C →
    (∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, Green66.IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X) →
    ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, Green66.IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - (1 / 10 : ℝ) * X ^ (1 / 4 : ℝ)) X

theorem main : H1 → H2 → type_of% @Green66.green_66 := by
  intro h1 h2
  rcases h1 with ⟨C, hC, hbound⟩
  exact h2 C hC hbound

end OMA.R_Green66_green_66_R1
