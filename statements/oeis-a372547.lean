import Mathlib

/-!
# A372547: Palindromic Zumkeller numbers in base 10.

Source: https://oeis.org/A372547
Credit: @agchua

Comment of A372547 (the entry is by Ivan N. Ianakiev, May 05 2024), verbatim:
  Based on the conjecture that there are infinitely many repunit primes, one may conjecture there
  are infinitely many repdigit terms, since 2*3*y (where y is a repunit prime) is a repdigit
  palindromic Zumkeller number.

Formalisation. A372547 is the intersection of A002113 (palindromes in base 10) and A083207
(Zumkeller numbers: numbers n whose set of divisors can be partitioned into two disjoint sets
with equal sum). A repunit (A002275) is (10^k - 1)/9, and a repdigit is a number whose decimal
digits are all equal. The statement has two parts: the supporting claim (for every repunit
prime y, 2*3*y is a repdigit term) and the conjecture (there are infinitely many repdigit
terms).
-/

namespace OMA.S_oeis_a372547

/-- The divisors of `n` can be split into two disjoint sets with equal sums (A083207). -/
def IsZumkeller (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ n.divisors ∧ ∑ d ∈ s, d = ∑ d ∈ n.divisors \ s, d

/-- `n` is a palindrome in base 10 (A002113). -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- All decimal digits of `n` are equal. -/
def IsRepdigit (n : ℕ) : Prop := ∃ c : ℕ, ∀ x ∈ Nat.digits 10 n, x = c

/-- The repunit (10^k - 1)/9 (A002275). -/
def repunit (k : ℕ) : ℕ := (10 ^ k - 1) / 9

/-- The terms of A372547: positive palindromic Zumkeller numbers. -/
def A372547 : Set ℕ := {n | 0 < n ∧ IsPalindrome n ∧ IsZumkeller n}

/-- For every repunit prime y, 2*3*y is a repdigit term, and there are infinitely many
repdigit terms. -/
theorem main :
    (∀ k : ℕ, (repunit k).Prime →
      2 * 3 * repunit k ∈ A372547 ∧ IsRepdigit (2 * 3 * repunit k)) ∧
    Set.Infinite {n : ℕ | n ∈ A372547 ∧ IsRepdigit n} := by
  sorry

end OMA.S_oeis_a372547
