import FormalConjectures.ErdosProblems.«1119»

-- Reduction Erdos1119.erdos_1119.R1 of Erdős Problem 1119
-- Credit: @arindale
-- The headline is independent of ZFC; this splits it into the provable ZFC-positive
-- range succ m < c and the independent remaining case succ m = c.

namespace OMA.R_Erdos1119_erdos_1119_R1
open Cardinal Order
open scoped Cardinal

/-- The ZFC-positive easy case: the answer is yes when `succ m < 𝔠`. -/
def H1 : Prop :=
  ∀ (m : Cardinal.{0}), ℵ₀ < m → succ m < 𝔠 →
  ∀ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) →
    (∀ z₀ : ℂ, #{y : ℂ | ∃ f ∈ F, f z₀ = y} ≤ m) →
    #F ≤ m

/-- The remaining case `succ m = 𝔠`, which is independent of ZFC. -/
def H2 : Prop :=
  ∀ (m : Cardinal.{0}), ℵ₀ < m → succ m = 𝔠 →
  ∀ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) →
    (∀ z₀ : ℂ, #{y : ℂ | ∃ f ∈ F, f z₀ = y} ≤ m) →
    #F ≤ m

theorem main : H1 → H2 → type_of% @Erdos1119.erdos_1119 := by
  intro h1 h2 m hm hlt F hF hval
  by_cases hs : succ m < 𝔠
  · exact h1 m hm hs F hF hval
  · have hle : succ m ≤ 𝔠 := Order.succ_le_iff.2 hlt
    have he : succ m = 𝔠 := le_antisymm hle (le_of_not_gt hs)
    exact h2 m hm he F hF hval

end OMA.R_Erdos1119_erdos_1119_R1
