import Mathlib

/-!
# A378495: Triangle read by rows: T(n,k) is the number of derangements in S_n with no k-cycles.
1 <= k <= n.

Source: https://oeis.org/A378495
Credit: @Squee451

Data, by rows: 0; 0, 0; 0, 2, 0; 0, 6, 9, 3; 0, 24, 24, 44, 20; 0, 160, 225, 175, 265, 145; ...

The entry contains three separate conjectures. This statement is the third one, in full:
Conjecture: T(n,n-2) - T(n,n) = (n-3)!*(n-4)*(n-1)/2 for n >= 5.
(In the data: T(5,3) - T(5,5) = 24 - 20 = 4 = 2!*1*4/2 and T(6,4) - T(6,6) = 175 - 145 = 30 = 3!*2*5/2.)
The other two conjectures of the entry (the gcd of the n-th row, and T(n,n-1) - T(n,n-2)) are not
part of this statement.

Conventions.
* A derangement is a permutation without fixed points; "no k-cycles" means that `k` does not occur
  in the cycle type (the multiset of lengths of the nontrivial cycles), `Equiv.Perm.cycleType`.
* For `k = 1` this definition gives the number of all derangements, whereas the entry's table lists
  T(n,1) = 0; the conjecture only involves `k = n - 2 ≥ 3` and `k = n`, where the two agree with the
  data (T(5,3) = 24, T(5,5) = 20, T(6,4) = 175, T(6,6) = 145).
* The identity is written over the integers, and with the division cleared:
  `2 * (T n (n-2) - T n n) = (n-3)! * (n-4) * (n-1)`.
-/

namespace OMA.S_oeis_a378495

/-- The number of derangements of `Fin n` with no `k`-cycle. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Equiv.Perm (Fin n) => (∀ i, p i ≠ i) ∧ k ∉ p.cycleType).card

theorem main : ∀ n : ℕ, 5 ≤ n →
    2 * ((T n (n - 2) : ℤ) - (T n n : ℤ)) = ((n - 3).factorial : ℤ) * ((n : ℤ) - 4) * ((n : ℤ) - 1) := by
  sorry

end OMA.S_oeis_a378495
