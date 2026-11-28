import Mathlib

/-!
# A033502: Chernick's Carmichael numbers

Source: https://oeis.org/A033502
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Carmichael numbers of the form `(6k+1)(12k+1)(18k+1)` with `6k+1`, `12k+1` and `18k+1` all prime.
Dickson's conjecture implies (Chernick) that this sequence is infinite; `main` states that it is
infinite.

## Encoding

* By Chernick's observation such a product is automatically a Carmichael number whenever the
  three factors are prime, so the sequence is infinite iff there are infinitely many `k ≥ 1`
  with `6k+1`, `12k+1`, `18k+1` all prime; `main` states the latter.
-/

namespace OMA.S_oeis_a033502

theorem main :
    {k : ℕ | 1 ≤ k ∧ (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a033502
