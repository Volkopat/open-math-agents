import Mathlib

/-!
# Eventual cycles for OEIS A353313

Antti Karttunen, A353313, OEIS Foundation, CC BY-SA 4.0.
Source: https://oeis.org/A353313
Lean formalization: @connoranderson.
-/

namespace OMA.S_oeis_a353313

/-- Divide multiples of three by three. Otherwise send 3k+r to 5k+3+r. -/
def step (n : ℕ) : ℕ :=
  let k := n / 3
  let r := n % 3
  if r = 0 then k else 5 * k + 3 + r

/-- Every orbit reaches a multiple of three that recurs after a positive period. -/
theorem main : ∀ n : ℕ, ∃ t p : ℕ, 0 < p ∧
    3 ∣ step^[t] n ∧ step^[p] (step^[t] n) = step^[t] n := by
  sorry

end OMA.S_oeis_a353313
