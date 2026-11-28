import Mathlib

/-!
# A000079: Powers of 2: a(n) = 2^n.

Source: https://oeis.org/A000079
Credit: @rabdelaal

OEIS A000079 remarks that the Collatz conjecture (the hailstone sequence will eventually
reach the number 1, regardless of which positive integer is chosen initially) may be
restated as (the hailstone sequence will eventually reach a power of 2, regardless of which
positive integer is chosen initially). This file states that restatement: the hailstone
iteration of any positive integer eventually lands on a number of the form `2 ^ m`.

The hailstone map used is the classical one: halve when even, otherwise send `n` to
`3 * n + 1`.
-/

namespace OMA.S_oeis_a000079

/-- One step of the hailstone (Collatz) iteration: `n ↦ n / 2` for even `n`,
`n ↦ 3 * n + 1` for odd `n`. -/
def hailstoneStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` is a power of 2 (a term of OEIS A000079). -/
def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ m, n = 2 ^ m

/-- The hailstone sequence eventually reaches a power of `2`, regardless of which positive
integer is chosen initially (OEIS A000079 restatement of the Collatz conjecture). -/
theorem main : ∀ n > 0, ∃ k, IsPowerOfTwo (hailstoneStep^[k] n) := by
  sorry

end OMA.S_oeis_a000079
