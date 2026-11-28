import Mathlib

/-!
# A018890: Numbers requiring exactly eight positive cubes

Source: https://oeis.org/A018890
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Numbers whose smallest expression as a sum of positive cubes requires exactly eight cubes. It is
conjectured that `a(121) = 8042` is the last term.

## Encoding

* Since only `23` and `239` need nine cubes and no positive integer needs more, "`8042` is the
  last term" is equivalent to: every `n > 8042` is a sum of at most `7` positive cubes. A sum of at
  most `7` positive cubes is a list of length `≤ 7` of positive integers whose cubes sum to `n`.
-/

namespace OMA.S_oeis_a018890

theorem main :
    ∀ n : ℕ, 8042 < n →
      ∃ l : List ℕ, l.length ≤ 7 ∧ (∀ x ∈ l, 1 ≤ x) ∧ (l.map (· ^ 3)).sum = n := by
  sorry

end OMA.S_oeis_a018890
