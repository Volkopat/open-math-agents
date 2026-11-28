import Mathlib

/-!
# A343099: sums of three distinct odd squares

Source: https://oeis.org/A343099
Credit: @jagraj28

A343099 lists the numbers that are sums of three distinct odd squares. Robert Israel (2021)
notes that all terms are `≡ 3 (mod 8)` and records:

  Conjecture: the sequence contains all numbers `≡ 3 (mod 8)` except
  `3, 11, 19, 27, 43, 51, 67, 99, 123, 163, 187, 267, 627`.

`main` states this as an equivalence for every `n ≡ 3 (mod 8)`: `n` is a sum of three distinct
odd squares if and only if `n` is not one of the 13 listed exceptions. The direction "an
exception is not such a sum" is the part of the claim that says the list is exactly the set of
missing numbers; it is a finite check. A brute-force search confirms the whole statement for all
`n ≤ 200000`.

Conventions.
* An odd square is `(2 * a + 1) ^ 2` with `a : ℕ`, that is the square of a positive odd number.
* "Distinct" means three different odd squares; this is written `a < b < c`, which loses no
  generality because the sum is symmetric.
-/

namespace OMA.S_oeis_a343099

/-- `n` is a sum of three distinct odd squares. -/
def IsSumThreeDistinctOddSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a < b ∧ b < c ∧ n = (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 + (2 * c + 1) ^ 2

/-- The numbers `≡ 3 (mod 8)` conjectured not to be sums of three distinct odd squares. -/
def exceptions : Finset ℕ := {3, 11, 19, 27, 43, 51, 67, 99, 123, 163, 187, 267, 627}

/-- Conjecture in OEIS A343099 (Robert Israel): every `n ≡ 3 (mod 8)` outside the 13 listed
exceptions is a sum of three distinct odd squares, and the exceptions are not. -/
theorem main : ∀ n : ℕ, n % 8 = 3 → (IsSumThreeDistinctOddSquares n ↔ n ∉ exceptions) := by
  sorry

end OMA.S_oeis_a343099
