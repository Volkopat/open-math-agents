import Mathlib

/-!
# A104863: Stephan's conjectured recurrence for floor(sqrt(a(n-1)^2 + a(n-2)^2))

Source: https://oeis.org/A104863
Credit: @ivillar

A104863 (offset 1): a(1) = 10, a(2) = 30, a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2));
data 10, 30, 31, 43, 53, 68, 86, 109, 138, 175, 222, 282, 358, 455, 578, 735, 935, 1189, ...
Conjecture (Ralf Stephan, Nov 15 2010): for n >= 17, a(n) = a(n-2) + a(n-4) + 1.

Formalization notes.
* For a natural number m, floor(sqrt(m)) is Mathlib's `Nat.sqrt m`.
* The sequence starts at n = 1; the value `a 0` is a placeholder (0) that the recurrence for
  n ≥ 3 never uses, and the conjecture only involves indices n - 4 ≥ 13.

Status: the conjecture is false as stated. It fails at its first index: a(17) = 935, while
a(15) + a(13) + 1 = 578 + 358 + 1 = 937. `main` is the literal statement, kept as the target
of a disproof.
-/

namespace OMA.S_oeis_a104863

/-- A104863: a(1) = 10, a(2) = 30, a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2)) (a 0 unused). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 10
  | 2 => 30
  | n + 3 => Nat.sqrt (a (n + 2) ^ 2 + a (n + 1) ^ 2)

/-- Stephan's conjecture: a(n) = a(n-2) + a(n-4) + 1 for n ≥ 17. -/
theorem main : ∀ n : ℕ, 17 ≤ n → a n = a (n - 2) + a (n - 4) + 1 := by
  sorry

end OMA.S_oeis_a104863
