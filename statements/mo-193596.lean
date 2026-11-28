import Mathlib

/-!
# Rounding to five cents: is the stationary distribution of the residue chain uniform?

Source: https://mathoverflow.net/questions/193596
Credit: @koolkao

Question (Yann Ponty, MathOverflow 193596, 2015; CC BY-SA 3.0). A consumer chooses a product
uniformly at random within a collection `𝒜 = {a_i}_{i=1}^k` of products. Consider the Markov chain
over states `Q = {q_0, …, q_4}` which remembers the value of the grand total modulo `5`¢. Its
transitions are `q_i → q_{i + a_j mod 5}` with probability `1/|𝒜|`, for all `i ∈ [0,4]` and
`j ∈ [1,k]`. For any non-degenerate collection `𝒜` (`∃ a ∈ 𝒜` such that `a mod 5 ≠ 0`), I obtained
(and subsequently conjecture) that `π(q_0) = π(q_1) = π(q_2) = π(q_3) = π(q_4) = 1/5`, where `π`
is the stationary distribution.

`main` states that the conjecture holds: every stationary distribution of the chain is uniform.
A disproof is a non-degenerate collection of prices with a non-uniform stationary distribution.

Translation choices:
* the products are indexed by `Fin k` and `a j : ℕ` is the price of product `j` in cents
  (several products may have the same price); the states are `ZMod 5`;
* the transition probability from `r` to `s` is `#{j | r + a j = s (mod 5)} / k`, which is the
  source's chain (each product is chosen with probability `1/k`);
* "non-degenerate" is `∃ j, ¬ 5 ∣ a j` (in particular `k ≥ 1`);
* a stationary distribution is `π : ZMod 5 → ℝ` with `π ≥ 0`, `∑ π = 1` and `π P = π`; `main`
  states that every such `π` is uniform (so "the" stationary distribution in the source, which
  is unique for non-degenerate collections, is uniform).
-/

namespace OMA.S_mo_193596

/-- For a non-degenerate collection of prices, every stationary distribution of the
total-modulo-five chain is uniform. -/
theorem main :
    ∀ (k : ℕ) (a : Fin k → ℕ), (∃ j, ¬ 5 ∣ a j) →
      ∀ π : ZMod 5 → ℝ, (∀ s, 0 ≤ π s) → ∑ s, π s = 1 →
      (∀ s, ∑ r, π r *
          (((Finset.univ.filter (fun j => r + (a j : ZMod 5) = s)).card : ℝ) / k) = π s) →
      ∀ s, π s = 1 / 5 := by
  sorry

end OMA.S_mo_193596
