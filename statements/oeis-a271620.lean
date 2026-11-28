import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Bounds.Basic

/-!
# 3-pile Sharing Nim, first row

Sources: https://oeis.org/A271620 and https://arxiv.org/abs/1506.06961, §4.
-/

namespace OMA.S_oeis_a271620

abbrev Position := Fin 3 → ℕ

/-- Transfer a positive number of tokens without making the receiving pile larger
than the donating pile. -/
def IsMove (p q : Position) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ ∃ k : ℕ, 0 < k ∧ p j + 2 * k ≤ p i ∧
    q i = p i - k ∧ q j = p j + k ∧
    ∀ l : Fin 3, l ≠ i → l ≠ j → q l = p l

/-- A position's value is the least natural number missing among its options' values. -/
def IsGrundy (g : Position → ℕ) : Prop :=
  ∀ p : Position, IsLeast {m : ℕ | ∀ q : Position, IsMove p q → g q ≠ m} (g p)

theorem main :
    ∃ g : Position → ℕ, IsGrundy g ∧ ∃ B : ℕ, ∀ n : ℕ, g ![0, 0, n] ≤ B := by
  sorry

end OMA.S_oeis_a271620
