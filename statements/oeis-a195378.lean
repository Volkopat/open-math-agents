import Mathlib

/-!
# A195378: Numbers n such that n-th Fibonacci number has all digits 0 to 9.

Source: https://oeis.org/A195378
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 1 and data `61, 63, 74, 92, 98, 100, 105, 107, 109, 113, 118, …`.
It records two conjectures:

  Comments: Brian Trial conjectures that all Fibonacci numbers greater than F285 are pandigital.
  Formula: Conjecture: a(n) = n + 131 for n > 154.

Both are formalized, as a conjunction.

Conventions.
- `Nat.fib` is the Fibonacci sequence with `fib 0 = 0`, `fib 1 = 1`, as in OEIS A000045.
- "Has all digits 0 to 9" (pandigital) means each of `0, …, 9` occurs among its decimal digits.
- "Fibonacci numbers greater than F285" is read as `F(n)` for every index `n > 285`.
- `a n` is the `n`-th index, counting from `1`: `Nat.nth IsTerm (n - 1)`. This reproduces the
  53 terms listed in the entry (up to `176`); there are 154 terms up to `285`, and `a 155 = 286`
  (checked by computer up to index 400).
-/

namespace OMA.S_oeis_a195378

/-- Every decimal digit `0, …, 9` occurs in `m`. -/
def IsPandigital (m : ℕ) : Prop :=
  ∀ d < 10, d ∈ Nat.digits 10 m

/-- `n` is a term: the `n`-th Fibonacci number is pandigital. -/
def IsTerm (n : ℕ) : Prop :=
  IsPandigital (Nat.fib n)

/-- `a n`, the `n`-th term of A195378 (offset 1, so `a 1 = 61`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsTerm (n - 1)

/-- Brian Trial's conjecture (every `F(n)` with `n > 285` is pandigital) and the formula
conjecture `a(n) = n + 131` for `n > 154`. -/
theorem main :
    (∀ n : ℕ, 285 < n → IsPandigital (Nat.fib n)) ∧
    (∀ n : ℕ, 154 < n → a n = n + 131) := by
  sorry

end OMA.S_oeis_a195378
