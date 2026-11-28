import Mathlib

/-!
# A132634: Fibonacci(n) mod n^2 vanishes only for n = 1 and n = 12

Source: https://oeis.org/A132634
Credit: @sntntHb

`a(n) = Fibonacci(n) mod n^2` (offset 1), with `Fibonacci(n)` the Fibonacci numbers A000045.
The entry records the conjecture
  `a(n) = 0` for `n = 1` and `n = 12` only.

`a(n) = 0` means that `n^2` divides `Fibonacci(n)`. Formalized with Mathlib's `Nat.fib` for every
`n ≥ 1` (the range of the sequence): `n^2 ∣ fib n` iff `n = 1` or `n = 12`
(indeed `fib 12 = 144 = 12^2`).
-/

namespace OMA.S_oeis_a132634

/-- `a n = Fibonacci(n) mod n^2` (OEIS A132634). -/
def a (n : ℕ) : ℕ := Nat.fib n % n ^ 2

/-- The conjecture in OEIS A132634: for `n ≥ 1`, `a(n) = 0` iff `n = 1` or `n = 12`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 1 ∨ n = 12) := by
  sorry

end OMA.S_oeis_a132634
