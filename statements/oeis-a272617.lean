import Mathlib

/-!
# A272617: Concatenation of the numbers from n down to 1 with numbers from 1 to n.

Source: https://oeis.org/A272617
Credit: @prasledi

Conjecture (in the COMMENTS of A272617): a(1) is the only prime number.

Formalization notes:
* Offset 1. `a n` is the decimal concatenation of n, n-1, ..., 1, 1, 2, ..., n, e.g.
  a(1) = 11, a(2) = 2112, a(10) = 1098765432112345678910.
* Concatenating `acc` with `m` is `acc * 10 ^ (number of decimal digits of m) + m`; the number of
  decimal digits of `m ≥ 1` is `(Nat.digits 10 m).length`. All concatenated numbers are >= 1.
* The definition reproduces the OEIS data 11, 2112, 321123, ..., 121110987654321123456789101112
  (checked with #eval for n = 1..12).
* "a(1) is the only prime" is stated as: for n >= 1, a(n) is prime iff n = 1 (this includes that
  a(1) = 11 is prime).
-/

namespace OMA.S_oeis_a272617

/-- Decimal concatenation of the numbers in a list, left to right. -/
def concatDigits (l : List ℕ) : ℕ :=
  l.foldl (fun acc m => acc * 10 ^ (Nat.digits 10 m).length + m) 0

/-- `a n`: the concatenation of n, n-1, ..., 1 followed by 1, 2, ..., n. -/
def a (n : ℕ) : ℕ :=
  concatDigits ((List.range n).reverse.map (· + 1) ++ (List.range n).map (· + 1))

/-- The conjecture of A272617: a(1) is the only prime term. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ((a n).Prime ↔ n = 1) := by
  sorry

end OMA.S_oeis_a272617
