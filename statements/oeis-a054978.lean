import Mathlib

/-!
# A054978: Gilbreath transform of the lucky numbers (A000959).

Source: https://oeis.org/A054978
Credit: @tczyzycki

Obtained from the sequence of lucky numbers `1, 3, 7, 9, 13, 15, 21, ...` (A000959) by taking
iterated absolute differences of consecutive terms and extracting the leading (0-th) entry of
each row (offset 0: `a(0) = 1, a(1) = 2, a(2) = 2, a(3) = 0, ...`).

Conjecture (N. J. A. Sloane, May 07 2023, analog of the Gilbreath-Proth conjecture for primes):
apart from the initial term `a(0) = 1`, every term `a(n)` (`n ≥ 1`) is `0` or `2`.
-/

namespace OMA.S_oeis_a054978

/-- Stage `s` of the lucky-number sieve, 0-indexed: stage `0` is the odd positive integers
    `2 * k + 1`, and stage `s + 1` removes every `r`-th entry (1-indexed) where
    `r = luckySieve s (s + 1)`. -/
def luckySieve : ℕ → ℕ → ℕ
  | 0, k => 2 * k + 1
  | s + 1, k =>
      let r := luckySieve s (s + 1)
      luckySieve s (k + k / (r - 1))

/-- The `n`-th lucky number (A000959, 0-indexed: `lucky 0 = 1`, `lucky 1 = 3`, `lucky 2 = 7`, ...).
    Since `luckySieve s (s + 1) > s + 1`, the `n`-th entry stabilizes by stage `n`. -/
def lucky (n : ℕ) : ℕ :=
  luckySieve n n

/-- The `j`-th entry of the `k`-th iterated absolute difference row of the lucky numbers. -/
def gilbreathRow : ℕ → ℕ → ℕ
  | 0, j => lucky j
  | k + 1, j => Int.natAbs ((gilbreathRow k (j + 1) : ℤ) - (gilbreathRow k j : ℤ))

/-- `A054978(n)`: the leading entry of the `n`-th iterated absolute difference row of A000959. -/
def a (n : ℕ) : ℕ :=
  gilbreathRow n 0

/-- Conjecture (OEIS A054978): every term after `a(0) = 1` is either `0` or `2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 ∨ a n = 2 := by
  sorry

end OMA.S_oeis_a054978
