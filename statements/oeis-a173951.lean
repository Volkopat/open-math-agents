import Mathlib

/-!
# A173951: Positive integers with the property that if the base-3 representation is reversed the result is twice the original number.

Source: https://oeis.org/A173951

Conjecture in the entry (John W. Layman, Mar 03 2010):
All terms of sequence A173952, defined by b(1)=32 and, for n>1, b(n)=9*b(n-1)+32, appear to be
terms of the above sequence {a(n)}.

Formalization notes:
* A173951 is defined by its name, as a set of natural numbers: m is a term when m > 0 and the
  number whose base-3 digits are those of m in reverse order equals 2*m. `Nat.digits 3 m` lists
  the base-3 digits of m from the least significant one, with no leading zero; reversing that
  list and reading it back with `Nat.ofDigits 3` gives the reversed base-3 representation. Being
  a term of the sequence {a(n)} means being an element of this set, since the sequence lists the
  elements of the set in increasing order.
* A173952 is defined by the recurrence in its name, b(1) = 32 and b(n) = 9*b(n-1) + 32 for n > 1.
  Here `b 0 = 0` is a junk value that is never used in the claim; with it the rule
  b(n+1) = 9*b(n) + 32 also gives b(1) = 32. Offset 1, so the claim is made for every n >= 1.
* The same comment goes on to say that each b(n) appears to be the largest term of A173951 with
  2n+2 digits in base 3. That stronger claim is not restated here; this statement is the first
  claim of the comment, which is also the conjecture stated in A173952.
-/

namespace OMA.S_oeis_a173951

/-- A173951: positive integers m such that reversing the base-3 representation of m gives 2*m. -/
def A173951 : Set ℕ :=
  {m : ℕ | 0 < m ∧ Nat.ofDigits 3 (Nat.digits 3 m).reverse = 2 * m}

/-- A173952: b(1) = 32 and b(n) = 9*b(n-1) + 32 for n > 1 (with the unused value b(0) = 0). -/
def b : ℕ → ℕ
  | 0 => 0
  | (n + 1) => 9 * b n + 32

/-- Layman's conjecture on A173951: every term of A173952 is a term of A173951. -/
theorem main : ∀ n : ℕ, 1 ≤ n → b n ∈ A173951 := by
  sorry

end OMA.S_oeis_a173951
