import OMAStatements.S_oeis_a005432

/-!
# Lower and upper bounds for A005432

The normalized logarithm converges when it eventually exceeds every strict lower
threshold and stays below every strict upper threshold.
-/

namespace OMA.R_oeis_a005432_R1

open Filter OMA.S_oeis_a005432

/-- Every threshold below the proposed limit is an eventual lower bound. -/
def H1 : Prop :=
  ∀ b : ℝ, b < Real.log 2 / 16 →
    ∀ᶠ n : ℕ in atTop, b < Real.log (a n) / (n : ℝ) ^ 2

/-- Every threshold above the proposed limit is an eventual upper bound. -/
def H2 : Prop :=
  ∀ b : ℝ, Real.log 2 / 16 < b →
    ∀ᶠ n : ℕ in atTop, Real.log (a n) / (n : ℝ) ^ 2 < b

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a005432.main := by
  intro lower upper
  exact tendsto_order.2 ⟨lower, upper⟩

end OMA.R_oeis_a005432_R1
