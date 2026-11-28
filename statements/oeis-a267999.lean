import Mathlib

/-!
# A267999: numbers n > 1 such that gcd(n, 2^n - 2) = 1

Source: https://oeis.org/A267999 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A267999 (Thomas Ordowski and Robert Israel, Jan 24 2016), offset 1: numbers n > 1 such
that gcd(n, 2^n - 2) = 1. Data
35, 55, 77, 95, 115, 119, 143, 155, 161, 187, 203, 209, 215, 221, 235, 247, 253, 275, ...
Entry A121707: numbers n > 1 such that n^3 divides Sum_{k=1..n-1} k^n = A121706(n). Data
35, 55, 77, 95, 115, 119, 143, 155, 161, 187, 203, 209, 215, 221, 235, 247, 253, 275, ...

Comments of A267999: Conjecture: this is a subsequence of A121707. Tested for all terms <= 10^5.

Formalization notes.
* A term of A267999 is a natural number n > 1 with `Nat.gcd n (2 ^ n - 2) = 1`. The natural
  subtraction is exact, because 2 ^ n >= 2 for n > 1.
* A term of A121707 is a natural number n > 1 such that n^3 divides Sum_{k=1..n-1} k^n. The sum is
  over `Finset.Icc 1 (n - 1)`.
* `main` says that each term of A267999 is a term of A121707.
-/

namespace OMA.S_oeis_a267999

/-- Each n > 1 with gcd(n, 2^n - 2) = 1 satisfies n^3 | Sum_{k=1..n-1} k^n. -/
theorem main : ∀ n : ℕ, 1 < n → Nat.gcd n (2 ^ n - 2) = 1 →
    n ^ 3 ∣ ∑ k ∈ Finset.Icc 1 (n - 1), k ^ n := by
  sorry

end OMA.S_oeis_a267999
