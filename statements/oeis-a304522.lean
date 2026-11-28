import Mathlib

/-!
# A304522: Number of ordered ways to write n as the sum of a Fibonacci number and a positive odd squarefree number.

Source: https://oeis.org/A304522
Credit: @EtienneLefranc

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a304522

/-- The ways to write `n` as `f + s` with `f` a Fibonacci number and `s` a positive odd
squarefree number, recorded by the Fibonacci part `f` (which determines `s = n - f`). -/
def reps (n : ℕ) : Set ℕ :=
  {f | (∃ i : ℕ, Nat.fib i = f) ∧ f < n ∧ Odd (n - f) ∧ Squarefree (n - f)}

/-- `a n` is A304522(n): the number of ordered ways to write `n` as the sum of a Fibonacci
number and a positive odd squarefree number. -/
noncomputable def a (n : ℕ) : ℕ := (reps n).ncard

/-- Conjecture (Zhi-Wei Sun): a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 2, 27, 83, 31509. -/

theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      ∀ n : ℕ, 0 < n → a n = 1 → n = 1 ∨ n = 2 ∨ n = 27 ∨ n = 83 ∨ n = 31509 := by
  sorry

end OMA.S_oeis_a304522

