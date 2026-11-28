import Mathlib

/-!
# A290136: Positive numbers that are not the sum of two nonprime squarefree numbers (A000469).

Source: https://oeis.org/A290136
Credit: @darealpandaboi

Conjecture: the sequence is complete.

Translation notes.
* A000469 lists the nonprime squarefree numbers: 1 and the squarefree composites. In Mathlib,
  Squarefree 0 is false, so x is in A000469 exactly when Squarefree x and x is not prime.
  The two summands may be equal (2 = 1 + 1 is not a term).
* Complete is stated as: the set of positive integers that are not such a sum is exactly the set
  of the 19 listed terms. This reproduces the data and finds no other term up to 100000
  (checked by computer).
-/

namespace OMA.S_oeis_a290136

/-- x is squarefree and not prime (A000469). -/
def IsNonprimeSquarefree (x : ℕ) : Prop := Squarefree x ∧ ¬ x.Prime

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ a b : ℕ, IsNonprimeSquarefree a ∧ IsNonprimeSquarefree b ∧ n = a + b} =
      {1, 3, 4, 5, 6, 8, 9, 10, 13, 14, 17, 18, 19, 26, 33, 38, 46, 62, 82} := by
  sorry

end OMA.S_oeis_a290136
