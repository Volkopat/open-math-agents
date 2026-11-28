import FormalConjectures.ErdosProblems.«270»

/-! The locations where a monotone order crosses successive integers restrict rational values. -/
namespace OMA.R_Erdos270_erdos_270_variants_monotone_R2
open Filter Erdos270

/-- A rational value forces a quantitative lower growth rate on the order. -/
def H1 : Prop := ∀ f : ℕ → ℕ, Monotone f → Tendsto f atTop atTop → ∀ q : ℚ, series f = (q:ℝ) →
  ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ((f n : ℝ)+1) * (Real.log ((n:ℝ)+1))^2 ≤ K * (4:ℝ)^(f n)

/-- The remaining orders grow at least as fast as the rationality obstruction permits. -/
def H2 : Prop := ∀ f : ℕ → ℕ, Monotone f → Tendsto f atTop atTop →
  (∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ((f n : ℝ)+1) * (Real.log ((n:ℝ)+1))^2 ≤ K * (4:ℝ)^(f n)) →
  Irrational (series f)

theorem main : H1 → H2 → type_of% @Erdos270.erdos_270.variants.monotone := by
  rintro h1 h2 f hm ht ⟨q,hq⟩
  exact h2 f hm ht (h1 f hm ht q hq.symm) ⟨q,hq⟩

end OMA.R_Erdos270_erdos_270_variants_monotone_R2
