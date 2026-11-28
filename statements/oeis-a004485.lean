import Mathlib

/-!
# OEIS A004485: conjectured recurrence and generating function

Conjectures by Chai Wah Wu, April 5, 2021, in https://oeis.org/A004485.
The Wythoff game and its Sprague–Grundy table are defined in https://oeis.org/A004481.
Credit: @sassmama27
-/

namespace OMA.S_oeis_a004485

/-- A move reduces one heap, or reduces both by the same positive amount. -/
def Move (a b c d : ℕ) : Prop :=
  (c < a ∧ d = b) ∨ (c = a ∧ d < b) ∨
    ∃ k : ℕ, 0 < k ∧ a = c + k ∧ b = d + k

/-- At each position the value is the least natural number absent from its options. -/
def IsGrundy (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b : ℕ,
    (∀ c d : ℕ, Move a b c d → g c d ≠ g a b) ∧
    (∀ m : ℕ, m < g a b → ∃ c d : ℕ, Move a b c d ∧ g c d = m)

/-- The row indexed by 4, with the recurrence interpreted over the integers. -/
def a (g : ℕ → ℕ → ℕ) (n : ℕ) : ℤ := Int.ofNat (g 4 n)

/-- Coefficients of the numerator, in increasing order of degree. -/
def numeratorCoeff (n : ℕ) : ℤ :=
  ([4, 1, -2, -1, 5, -1, 3, -9, 1, 7, 5, -1, -5, 4, 1, -4, 4, 0,
    -4, 6, 6, -8] : List ℤ)[n]?.getD 0

/-- Coefficient at degree n after shifting the series up by k degrees. -/
def shifted (g : ℕ → ℕ → ℕ) (k n : ℕ) : ℤ :=
  if k ≤ n then a g (n - k) else 0

/-- The generating-function identity is expressed coefficientwise after
multiplication by the denominator 1 - x - x^12 + x^13. -/
theorem main : ∀ (g : ℕ → ℕ → ℕ), IsGrundy g →
    (∀ n : ℕ, 21 < n → a g n = a g (n - 1) + a g (n - 12) - a g (n - 13)) ∧
    (∀ n : ℕ, a g n - shifted g 1 n - shifted g 12 n + shifted g 13 n =
      numeratorCoeff n) := by
  sorry

end OMA.S_oeis_a004485
