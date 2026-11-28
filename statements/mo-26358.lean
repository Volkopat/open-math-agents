import Mathlib

/-!
# Colouring the positive integers so that `a, 2a, …, na` get distinct colours

Source: https://mathoverflow.net/questions/26358
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (domotorp, MathOverflow): can we colour `ℤ⁺` with `n` colours such that
`a, 2a, …, na` all have different colours, for all `a`?

Conventions:
* For every `n ≥ 1` (the question is asked for each `n`; it is known when `n + 1` is prime).
* The source asks a yes/no question; `main` states the answer yes for every `n`, and a disproof
  would answer no.
-/

namespace OMA.S_mo_26358

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ+ → Fin n, ∀ a : ℕ+,
      Function.Injective (fun i : Fin n => c (a * ⟨i.val + 1, Nat.succ_pos _⟩)) := by
  sorry

end OMA.S_mo_26358
