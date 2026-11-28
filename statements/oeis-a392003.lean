import Mathlib

/-!
# A392003: a(n) = (7*2^n - 9 + 5*(-1)^n) / 6.

Source: https://oeis.org/A392003
Credit: @agchua

Formula section of A392003:
  Conjecture: a(2*n) = A266753(n).

A392003 has offset 1 (a(1) = 0, a(2) = 4, a(3) = 7, a(4) = 18, ...). A266753 has offset 0 and is
the decimal representation of the n-th iteration of the Rule 163 elementary cellular automaton
starting with a single ON cell at position 0, read over the central 2*n + 1 cells from -n to n
(most significant bit at -n), matching the entry's Mathematica program (A266753(0) = 1,
A266753(1) = 4, A266753(2) = 18, A266753(3) = 74, ...). The conjecture ranges over all n >= 1
so that 2*n >= 2 lies within the offset-1 domain of A392003.
-/

namespace OMA.S_oeis_a392003

/-- A392003(n) = (7*2^n - 9 + 5*(-1)^n) / 6. -/
def a (n : ℕ) : ℤ :=
  (7 * (2 : ℤ) ^ n - 9 + 5 * (-1 : ℤ) ^ n) / 6

/-- Elementary cellular automaton Rule 163 (binary 10100011):
    maps neighborhood (left, center, right) to the next cell state. -/
def rule163 (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => true
  | true,  true,  false => false
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => false
  | false, true,  false => false
  | false, false, true  => true
  | false, false, false => true

/-- Generation n of the Rule 163 cellular automaton on ℤ starting from a single ON cell at 0. -/
def ca163 : ℕ → ℤ → Bool
  | 0, i => i == 0
  | n + 1, i => rule163 (ca163 n (i - 1)) (ca163 n i) (ca163 n (i + 1))

/-- A266753(n): base-2 value of cells -n through n (MSB at -n, LSB at n) in generation n. -/
def A266753 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1),
    (if ca163 n ((k : ℤ) - (n : ℤ)) then 1 else 0) * 2 ^ (2 * n - k)

/-- Conjecture of A392003: a(2*n) = A266753(n) for all n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (2 * n) = (A266753 n : ℤ) := by
  sorry

end OMA.S_oeis_a392003
