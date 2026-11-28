import Mathlib

/-!
# A214799: Let S be a set of n positive numbers such that all n choose 2 pairwise GCD's are distinct, and let max(S) denote the largest element of S; a(n) is the minimal value of max(S) over all choices for S.

Source: https://oeis.org/A214799
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A214799 (N. J. A. Sloane, Mar 07 2013): a(n) = 15 *
2^(n-3) for n >= 6 (Robert Israel).

Conventions:
* The sequence has offset 1 (data 1, 2, 6, 18, 54, 120, 240, 480, 960, 1920, ...).
* A set S of n positive numbers is a finset of n positive natural numbers. `Good S` says that all
  pairwise GCDs are distinct: if a < b and c < d are two pairs of elements of S with gcd(a,b) =
  gcd(c,d), then the pairs coincide. a(n) is the least possible value of max(S), stated with
  `IsLeast` (M is the maximum of S when M is in S and every element of S is at most M).
-/

namespace OMA.S_oeis_a214799

/-- S consists of positive numbers and all pairwise GCDs of distinct elements are distinct. -/
def Good (S : Finset ℕ) : Prop :=
  (∀ x ∈ S, 0 < x) ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a < b → c < d → Nat.gcd a b = Nat.gcd c d → a = c ∧ b = d

/-- The conjecture recorded in A214799. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    IsLeast {M : ℕ | ∃ S : Finset ℕ, S.card = n ∧ Good S ∧ M ∈ S ∧ ∀ x ∈ S, x ≤ M}
      (15 * 2 ^ (n - 3)) := by
  sorry

end OMA.S_oeis_a214799
