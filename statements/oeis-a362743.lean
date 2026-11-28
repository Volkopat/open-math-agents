import Mathlib

/-!
# A362743: Positive integers which cannot be written as a sum of distinct numbers of the form 4^a + 5^b (a,b >= 0)

Source: https://oeis.org/A362743
Credit: @niclorusso

Conjecture 1 (Zhi-Wei Sun, in the comments of A362743): The only terms of the current sequence are
1, 3, 4, 10, 12, 18.

(Conjecture 1 continues with a statement on sums in which no summand divides another, and the
entry has Conjectures 2 and 3; only the first sentence of Conjecture 1 is formalized here.)

Conventions:
* A sum of distinct numbers of the form 4^a + 5^b is the sum of a finite set S of such numbers
  (`Finset`), with a, b >= 0.
* "The only terms are 1, 3, 4, 10, 12, 18" is stated as a set equality for the positive integers
  that are not such a sum.
-/

namespace OMA.S_oeis_a362743

/-- `n` is a sum of distinct numbers of the form `4^a + 5^b`. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, ∃ a b : ℕ, x = 4 ^ a + 5 ^ b) ∧ ∑ x ∈ S, x = n

/-- Sun's Conjecture 1 on A362743 (first sentence): the positive integers that are not a sum of
distinct numbers `4^a + 5^b` are exactly `1, 3, 4, 10, 12, 18`. -/
theorem main : {n : ℕ | 0 < n ∧ ¬ IsRepresentable n} = {1, 3, 4, 10, 12, 18} := by
  sorry

end OMA.S_oeis_a362743
