import Mathlib

/-!
# Is every prime `p ≥ 3` expressible as `2p₁ - p₂` for distinct primes?

Source: https://mathoverflow.net/questions/515744 (CC BY-SA 4.0).

A "difference" analogue of Lemoine's conjecture: for every prime `p ≥ 3`, are there distinct
primes `p₁ ≠ p₂` with `p = 2p₁ - p₂`? Equivalently `p, p₁, p₂` is a non-constant three-term
arithmetic progression of primes. Example: `13 = 2 · 37 - 61`. The asker found no exception
among the primes `3 ≤ p ≤ 10^10`. The answers place it among the twin-prime/Goldbach-type
problems (a special case of Conjecture 1.4 of Green–Tao, *Linear equations in primes*), not
known.

We state the affirmative answer to the question.

Formalization notes:
* The equation is stated in `ℕ` as `p + p₂ = 2 * p₁`, which avoids truncated subtraction and is
  equivalent to `p = 2p₁ - p₂` over `ℤ` for natural numbers.
-/

namespace OMA.S_mo_515744

/-- Every prime `p ≥ 3` is `2p₁ - p₂` for some distinct primes `p₁ ≠ p₂`. -/
theorem main : ∀ p : ℕ, p.Prime → 3 ≤ p →
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ p + p₂ = 2 * p₁ := by
  sorry

end OMA.S_mo_515744
