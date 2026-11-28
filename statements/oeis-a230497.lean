import Mathlib

/-!
# A230497: a(n), n>=2, is the minimal odd evil k, such that k^i, i=2,3,...,n, all are odious, and a(n)=0, if there is no such k

Source: https://oeis.org/A230497
Credit: @niclorusso

Conjecture (in the comments of A230497): For all n, a(n) > 0.

Conventions:
* A number is evil when its binary expansion has an even number of 1's (A001969) and odious when
  it has an odd number of 1's (A000069); the number of 1's of m is `(Nat.digits 2 m).count 1`.
* The sequence has offset 2: for n >= 2, k is odd and evil, and k^2, ..., k^n are all odious.
* a(n) > 0 means that such a k exists (a(n) is then the least one).
-/

namespace OMA.S_oeis_a230497

/-- `m` is evil: an even number of 1's in binary. -/
def IsEvil (m : ℕ) : Prop := Even ((Nat.digits 2 m).count 1)

/-- `m` is odious: an odd number of 1's in binary. -/
def IsOdious (m : ℕ) : Prop := Odd ((Nat.digits 2 m).count 1)

/-- The conjecture on A230497: for every `n >= 2` there is an odd evil `k` such that `k^i` is
odious for all `i = 2, ..., n`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, Odd k ∧ IsEvil k ∧
    ∀ i : ℕ, 2 ≤ i → i ≤ n → IsOdious (k ^ i) := by
  sorry

end OMA.S_oeis_a230497
