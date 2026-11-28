import Mathlib

/-!
# Inventory independent of the initial state of a permutation

Source: HolyMonk, MathOverflow question 257899 (CC BY-SA 3.0),
https://mathoverflow.net/questions/257899.
Credit: @connoranderson.

The increasing thresholds are indexed by the n+1 states of the permutation,
including state zero. The exact characterization uses the total of all
thresholds. Marshall Hall's theorem on prescribed differences of permutations
provides the labeling for a cyclic permutation in the sufficient direction.
-/

namespace OMA.S_mo_257899

def inventory {n : ℕ} (k : Fin (n+1) → ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (s : Fin (n+1)) : ℕ :=
  ∑ j ∈ Finset.range (k (Fin.last n)), if j < k ((σ ^ (k (Fin.last n)-j-1)) s) then 1 else 0

theorem main : ∀ (n : ℕ) (k : Fin (n+1) → ℕ), StrictMono k → k 0 = 0 →
    ((∃ σ : Equiv.Perm (Fin (n+1)), ∀ s t, inventory k σ s = inventory k σ t) ↔
      n+1 ∣ ∑ i, k i) := by
  sorry

end OMA.S_mo_257899
