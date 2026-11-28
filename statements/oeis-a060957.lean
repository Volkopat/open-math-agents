import Mathlib

/-!
# A060957: Number of different products of subsets of {1, …, n}

Source: https://oeis.org/A060957
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Yan Sheng Ang, OEIS, 2020): let `p ≤ n` be prime. If `m` and `p^a · m` are both
products of subsets of `{1, 2, …, n}`, then so is `p^k · m` for all `0 < k < a`.

## Encoding

* `P n` is the set of products `∏_{i ∈ S} i` over subsets `S ⊆ {1, …, n}` (the empty product
  `1` included).
-/

namespace OMA.S_oeis_a060957

/-- Products of subsets of `{1, …, n}`. -/
def P (n : ℕ) : Set ℕ := {m | ∃ S ⊆ Finset.Icc 1 n, ∏ i ∈ S, i = m}

theorem main :
    ∀ n p a m k : ℕ, p.Prime → p ≤ n → m ∈ P n → p ^ a * m ∈ P n → 0 < k → k < a →
      p ^ k * m ∈ P n := by
  sorry

end OMA.S_oeis_a060957
