import Mathlib

/-!
# A356995: a(n) = b(n) - b(b(n)) - b(n - b(n)) for n >= 3, where b(n) = A356988(n).

Source: https://oeis.org/A356995
Credit: @alexandreeberhardt

`main` states the comment: starting at n = 7, the sequence consists of successive blocks
1, 2, ..., F(k) - 1, F(k), F(k) - 1, ..., 2, 1 (k >= 1, F = Fibonacci), each followed by a string
of zeros, conjecturally of length 1 + 2 F(k+1).

Reading choices.
* b = A356988 is given by b(1) = 1 and b(n) = n - b(b(n - b(b(b(n-1))))) for n >= 2. Rather than
  a recursive definition, `main` holds for every function `b` satisfying exactly these two
  equations. It is known that 1 <= b(n) <= n - 1 for n >= 2, so every index used by the recurrence
  (and the index n - b(n) below) lies between 1 and n - 1. Hence the equations determine b(n) for
  every n >= 1 (and such a `b` exists), the value b(0) is never used, and the truncated subtraction
  of ℕ in these indices never truncates.
* The value a(n) is computed in ℤ, so that a negative value could not be hidden by truncated
  subtraction and read as a zero.
* Successive means that each block starts right after the previous zero string. The block for k
  has 2 F(k) - 1 terms and its zero string 1 + 2 F(k+1) terms, so the block for k starts at
  7 plus the lengths of the earlier blocks and zero strings (`blockStart`). In closed form this is
  L(k+3) - F(k) + 1, with L the Lucas numbers: the peak F(k) sits at n = L(k+3), as in the
  Formula section, and the zero string starts at L(k+3) + F(k) (8, 12, 20, 32, 52, ...).
* The zero string has exactly this length: the term just before it is the last 1 of the block,
  and the term just after it is not zero (this last fact is also the first 1 of the next block;
  it is written out to make the maximality explicit).
-/

namespace OMA.S_oeis_a356995

/-- The sequence A356995 in ℤ, built from a function `b` playing the role of A356988
(used for n >= 3). -/
def a (b : ℕ → ℕ) (n : ℕ) : ℤ := (b n : ℤ) - b (b n) - b (n - b n)

/-- Index where the block with peak F(k) starts (k >= 1): 7 plus, for each earlier block
i = 1, ..., k - 1, its length 2 F(i) - 1 and the length 1 + 2 F(i+1) of its zero string. -/
def blockStart (k : ℕ) : ℕ :=
  7 + ∑ i ∈ Finset.Ico 1 k, ((2 * Nat.fib i - 1) + (1 + 2 * Nat.fib (i + 1)))

/-- Index where the zero string after the block with peak F(k) starts. -/
def zeroStart (k : ℕ) : ℕ := blockStart k + (2 * Nat.fib k - 1)

theorem main :
    ∀ b : ℕ → ℕ, b 1 = 1 →
      (∀ n, 2 ≤ n → b n = n - b (b (n - b (b (b (n - 1)))))) →
      ∀ k, 1 ≤ k →
        -- the block rises 1, 2, ..., F(k)
        (∀ j, j < Nat.fib k → a b (blockStart k + j) = (j : ℤ) + 1) ∧
        -- then falls F(k), F(k) - 1, ..., 1
        (∀ j, j < Nat.fib k → a b (blockStart k + (Nat.fib k - 1) + j) = (Nat.fib k : ℤ) - j) ∧
        -- then 1 + 2 F(k+1) zeros
        (∀ j, j < 1 + 2 * Nat.fib (k + 1) → a b (zeroStart k + j) = 0) ∧
        -- and the zero string ends there
        a b (zeroStart k + (1 + 2 * Nat.fib (k + 1))) ≠ 0 := by
  sorry

end OMA.S_oeis_a356995
