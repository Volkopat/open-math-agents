import Mathlib

/-!
# A122036: no odd weird numbers

Source: https://oeis.org/A122036
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A122036): there are no odd weird numbers, i.e. all odd abundant numbers are
pseudoperfect.

Conventions:
* `n` is abundant if the sum of its proper divisors exceeds `n`; pseudoperfect (semiperfect) if
  `n` is the sum of some subset of its proper divisors; weird = abundant and not pseudoperfect.
-/

namespace OMA.S_oeis_a122036

theorem main :
    ∀ n : ℕ, Odd n → n < ∑ d ∈ n.properDivisors, d →
      ∃ s ⊆ n.properDivisors, ∑ d ∈ s, d = n := by
  sorry

end OMA.S_oeis_a122036
