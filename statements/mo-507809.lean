import Mathlib

/-!
# A Collatz-type problem

Source: Vassilis Papanicolaou, https://mathoverflow.net/questions/507809 (CC BY-SA 4.0).
Credit: @Dolcruz
-/

namespace OMA.S_mo_507809

/-- The odd integers reachable after exactly `n` steps. Each step removes all
factors of two from either `3 * x + 1` or `3 * x + 3`. -/
def layer : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let previous := layer n
    previous.image (fun x => (3 * x + 1).divMaxPow 2) ∪
      previous.image (fun x => (3 * x + 3).divMaxPow 2)

/-- Does the union of all layers equal the set of positive odd integers? -/
theorem main : (⋃ n : ℕ, (layer n : Set ℕ)) = {x : ℕ | 0 < x ∧ Odd x} := by
  sorry

end OMA.S_mo_507809
