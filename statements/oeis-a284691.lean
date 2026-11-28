import Mathlib

/-!
# A284691: products with factors from A074992 are palindromes

Source: https://oeis.org/A284691
Credit: @avivorly

A284691: Numbers of the form (10^c-1)*the product any two (not necessarily distinct) terms of A074992.

A074992: a(n) = (10^(2*n) + 10^n + 1)/3 (offset 0; data 1, 37, 3367, 333667, ...).

Conjecture 1 (Ahmad J. Masad, in the entry): all terms are palindromic in base 10.

Conventions:
- `A074992 n = (10^(2n) + 10^n + 1)/3` for `n ≥ 0`, as in its entry (offset 0, `A074992 0 = 1`). The division is
  exact, since `10^m ≡ 1 (mod 3)`.
- A term of A284691 is a number `(10^c - 1) * A074992 i * A074992 j` with `c ≥ 1` and any indices `i, j ≥ 0` (two not
  necessarily distinct terms; `i = j` allowed). `c ≥ 1` matches the data, whose first term is `9 = (10^1 - 1) * 1 * 1`
  (`c = 0` would add the term `0`), and the Mathematica program of the entry, which starts at `c = 1`. The sequence lists
  these numbers in increasing order; the conjecture concerns all of them, so `main` quantifies over the term set.
- Palindromic in base 10: the list of base-10 digits equals its reverse, `(Nat.digits 10 k).reverse = Nat.digits 10 k`.
- Conjecture 2 of the entry (the sequence A074992 is the maximally dense sequence with this palindromic products
  property) is not precise (no notion of density or of the class of competing sequences is given), so it is not
  formalized here.
-/

namespace OMA.S_oeis_a284691

/-- A074992 (offset 0): `a(n) = (10^(2n) + 10^n + 1)/3`. -/
def A074992 (n : ℕ) : ℕ := (10 ^ (2 * n) + 10 ^ n + 1) / 3

/-- `k` is a term of A284691: `k = (10^c - 1) * A074992 i * A074992 j` for some `c ≥ 1` and some indices `i, j`. -/
def IsTerm (k : ℕ) : Prop :=
  ∃ c i j : ℕ, 1 ≤ c ∧ k = (10 ^ c - 1) * A074992 i * A074992 j

/-- Conjecture 1: every term of A284691 is a palindrome in base 10. -/
theorem main : ∀ k : ℕ, IsTerm k → (Nat.digits 10 k).reverse = Nat.digits 10 k := by
  sorry

end OMA.S_oeis_a284691
