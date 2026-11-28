import FormalConjectures.Wikipedia.GoodmanConjecture

/-!
# Goodman's conjecture: the p-valent coefficient bound

The target quantifies over all valencies `p`. The pinned module proves the bridge
`goodmanBound_one`: for `p = 1` the Goodman bound simplifies exactly to `n * ‖coeff f 1‖`.
This reduction separates that proved simplification from the two genuinely open coefficient
bounds: the univalent (`p = 1`) Bieberbach-type case and the remaining `p ≥ 2` case.
-/

open GoodmanConjecture

-- Reduction GoodmanConjecture.goodman_conjecture.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_GoodmanConjecture_goodman_conjecture_R1

/-- Open core, valency one: the classical Bieberbach-type coefficient bound. -/
def H1 : Prop :=
  ∀ f : ℂ → ℂ, ∀ n : ℕ, IsPValent f 1 → IsNormalized f → 1 < n →
    ‖coeff f n‖ ≤ n * ‖coeff f 1‖

/-- Open core, higher valency: the coefficient bound for every `p ≥ 2`. -/
def H2 : Prop :=
  ∀ f : ℂ → ℂ, ∀ p n : ℕ, 2 ≤ p → IsPValent f p → IsNormalized f → p < n →
    ‖coeff f n‖ ≤ goodmanBound f p n

theorem main : H1 → H2 → type_of% @GoodmanConjecture.goodman_conjecture := by
  intro h1 h2 f p n hf hf' hn
  by_cases hp : p = 1
  · subst p
    rw [GoodmanConjecture.goodmanBound_one f n hn]
    exact h1 f n hf hf' hn
  · have hp1 : 1 ≤ p := hf.one_le_p
    exact h2 f p n (by omega) hf hf' hn

end OMA.R_GoodmanConjecture_goodman_conjecture_R1
