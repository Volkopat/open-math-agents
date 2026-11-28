import Mathlib

/-!
# Singular cardinals hypothesis: the bound for `2 ^ ℵ_ω`

Source: https://en.wikipedia.org/wiki/Singular_cardinals_hypothesis
If `ℵ_ω` is a strong limit cardinal, is `2 ^ ℵ_ω < ℵ_{ω₁}`? (Shelah's pcf theory gives
`2 ^ ℵ_ω < ℵ_{ω₄}`.) `main` states the affirmative answer.

Conventions. `ℵ_ω = Cardinal.aleph ω` and `ℵ_{ω₁} = Cardinal.aleph (ℵ₁.ord)`, with `ω₁` the
initial ordinal of `ℵ₁`; strong limit is Mathlib's `Cardinal.IsStrongLimit`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_singular_cardinals_hypothesis

open Cardinal Ordinal

theorem main :
    (aleph ω).IsStrongLimit → (2 : Cardinal) ^ aleph ω < aleph (aleph 1).ord := by
  sorry

end OMA.S_wp_singular_cardinals_hypothesis
