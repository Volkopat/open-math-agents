import Mathlib

/-!
# A159021: the squares in a(n) = a(n-1) + floor(sqrt(a(n-1))), a(0) = 19

Source: https://oeis.org/A159021 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Philippe Deléham, Apr 02 2009), offset 0:
a(0)=19; a(n) = a(n-1) + floor(sqrt(a(n-1))), n > 0. Data
19, 23, 27, 32, 37, 43, 49, 56, 63, 70, 78, 86, 95, 104, ...

Comment: Conjecture: The squares are of the form (7*2^k)^2 (see A005009).
- Vincenzo Librandi, Apr 10 2009

Formalization notes.
* floor(sqrt(m)) is the integer square root `Nat.sqrt m`.
* "The squares" are the terms a(n) that are perfect squares. `main` states that each of them
  equals (7*2^k)^2 for some k >= 0 (A005009 is 7*2^k; the first square term is a(6) = 49).
* A different comment of the entry says that the sequence has infinitely many squares. It is
  not part of the conjecture and is not stated here.
-/

namespace OMA.S_oeis_a159021

/-- A159021: a(0) = 19 and a(n) = a(n-1) + floor(sqrt(a(n-1))). -/
def a : ℕ → ℕ
  | 0 => 19
  | n + 1 => a n + Nat.sqrt (a n)

/-- Librandi's conjecture: every square term is (7*2^k)^2 for some k. -/
theorem main : ∀ n : ℕ, IsSquare (a n) → ∃ k : ℕ, a n = (7 * 2 ^ k) ^ 2 := by
  sorry

end OMA.S_oeis_a159021
