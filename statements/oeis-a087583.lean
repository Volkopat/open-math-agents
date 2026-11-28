import Mathlib

/-!
# A087583: greedy distinct primes with distinct palindromic successive differences.

Source: https://oeis.org/A087583
Credit: @cjchaffin

The sequence starts at 2. Each later term is a new prime whose absolute difference
from the previous term is a palindrome that has not already occurred as a difference.
If any such prime smaller than the current term exists, one takes the candidate
minimizing the drop; otherwise one takes the least larger eligible prime. The
sequence of absolute differences begins `1, 2, 6, 4, 22, 8, 66, 44, …`.

Conjecture (on the OEIS page): this difference sequence is infinite and contains
every even palindrome.

Conventions: official offset 0, with `a 0 = 2`. Palindromes are in base 10
(`Nat.digits 10`). Even palindromes in the conjecture are the positive even ones
(differences of distinct primes are positive). Infinitude of the differences is
expressed by the existence of a total greedy listing.
-/

namespace OMA.S_oeis_a087583

def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

def absDiff (m n : ℕ) : ℕ := Int.natAbs ((m : ℤ) - n)

/-- Differences `|a 1 - a 0|, …, |a n - a (n-1)|` already used after the terms `a 0, …, a n`. -/
def usedDiffs (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun k => absDiff (a (k + 1)) (a k))

def usedPrimes (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image a

def eligible (a : ℕ → ℕ) (n p : ℕ) : Prop :=
  p.Prime ∧ p ∉ usedPrimes a n ∧
    IsPalindrome (absDiff p (a n)) ∧ absDiff p (a n) ∉ usedDiffs a n

def prefersDown (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ p : ℕ, eligible a n p ∧ p < a n

/-- `a` follows the greedy rule on the OEIS page, starting at `a 0 = 2`. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  a 0 = 2 ∧
    ∀ n : ℕ,
      eligible a n (a (n + 1)) ∧
        (prefersDown a n →
          a (n + 1) < a n ∧
            ∀ p : ℕ, eligible a n p → p < a n → absDiff (a n) (a (n + 1)) ≤ absDiff (a n) p) ∧
        (¬ prefersDown a n →
          a n < a (n + 1) ∧ ∀ p : ℕ, eligible a n p → a (n + 1) ≤ p)

theorem main :
    ∃ a : ℕ → ℕ, IsGreedy a ∧
      ∀ r : ℕ, Even r → 0 < r → IsPalindrome r →
        ∃ k : ℕ, absDiff (a (k + 1)) (a k) = r := by
  sorry

end OMA.S_oeis_a087583
