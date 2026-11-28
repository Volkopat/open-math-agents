import Mathlib

/-!
# A345128: Number of squarefree products s*t from all positive integer pairs (s,t), such that s + t = n, s <= t.

Source: https://oeis.org/A345128
Credit: @keiichisince1986-bot

A345128 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- `a(n) > 0` means that there are positive integers `s ≤ t` with `s + t = n` and `s t`
  squarefree.
-/

namespace OMA.S_oeis_a345128

theorem main :
    ∀ n : ℕ, 1 < n → ∃ s t : ℕ, 0 < s ∧ s ≤ t ∧ s + t = n ∧ Squarefree (s * t) := by
  sorry

end OMA.S_oeis_a345128
