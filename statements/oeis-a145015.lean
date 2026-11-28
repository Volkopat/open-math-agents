import Mathlib.Data.Nat.Digits.Defs

/-!
# Lengths of runs with the same sign in the binary digit imbalance

Denis Boigelot's A145015 records the lengths of runs in A037861. The
example counts neutral entries with the preceding nonzero sign. In
particular the imbalance at index zero is +1 from the binary digit 0.
Sources: https://oeis.org/A145015 and https://oeis.org/A037861
-/

namespace OMA.S_oeis_a145015

/-- Number of zero digits minus number of one digits. -/
def balance (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    let digits := Nat.digits 2 n
    (digits.count 0 : ℤ) - (digits.count 1 : ℤ)

/-- Retain the preceding sign when the imbalance is zero. -/
def positive : ℕ → Bool
  | 0 => true
  | n+1 => if balance (n+1) = 0 then positive n else decide (0 < balance (n+1))

/-- A nonempty maximal run, including the initial run starting at zero. -/
def IsRunLength (k : ℕ) : Prop :=
  0 < k ∧ ∃ s : ℕ, (s = 0 ∨ positive (s-1) ≠ positive s) ∧
    (∀ i < k, positive (s+i) = positive s) ∧ positive (s+k) ≠ positive s

theorem main : ∀ k : ℕ, IsRunLength k →
    (∃ j : ℕ, 1 ≤ j ∧ k = 2^j-1) ∨ (∃ j : ℕ, 3 ≤ j ∧ k = 2^j-3) := by
  sorry

end OMA.S_oeis_a145015
