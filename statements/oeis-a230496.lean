import Mathlib

/-!
# A230496: a(n) is the minimal odd odious k > 1, such that k^i, i=1,2,...,n, all are odious, or a(n)=0, if there is no such k

Source: https://oeis.org/A230496
Credit: @niclorusso

Conjecture (in the comments of A230496): for all n, a(n) > 0.

Conventions:
* A number is evil when its binary expansion has an even number of 1's (A001969) and odious when
  it has an odd number of 1's (A000069); the number of 1's of m is `(Nat.digits 2 m).count 1`.
* The sequence has offset 1: for n >= 1, k > 1 is odd and k^1, ..., k^n are all odious (i = 1 says k itself is odious).
* a(n) > 0 means that such a k exists (a(n) is then the least one).
-/

namespace OMA.S_oeis_a230496

/-- `m` is evil: an even number of 1's in binary. -/
def IsEvil (m : ℕ) : Prop := Even ((Nat.digits 2 m).count 1)

/-- `m` is odious: an odd number of 1's in binary. -/
def IsOdious (m : ℕ) : Prop := Odd ((Nat.digits 2 m).count 1)

/-- The conjecture on A230496: for every `n >= 1` there is an odd `k > 1` such that `k^i` is odious
for all `i = 1, ..., n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, Odd k ∧ 1 < k ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n → IsOdious (k ^ i) := by
  sorry

end OMA.S_oeis_a230496
