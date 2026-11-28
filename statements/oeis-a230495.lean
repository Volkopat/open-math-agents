import Mathlib

/-!
# A230495: a(n) is the minimal odd evil k, such that k^i, i=1,2,...,n, all are evil, and a(n)=0, if there is no such k

Source: https://oeis.org/A230495
Credit: @niclorusso

Conjecture (in the comments of A230495): We conjecture that a(n)>0 for all n.

Conventions:
* A number is evil when its binary expansion has an even number of 1's (A001969) and odious when
  it has an odd number of 1's (A000069); the number of 1's of m is `(Nat.digits 2 m).count 1`.
* The sequence has offset 1: for n >= 1, k is odd and k^1, ..., k^n are all evil (i = 1 says k itself is evil).
* a(n) > 0 means that such a k exists (a(n) is then the least one).
-/

namespace OMA.S_oeis_a230495

/-- `m` is evil: an even number of 1's in binary. -/
def IsEvil (m : ℕ) : Prop := Even ((Nat.digits 2 m).count 1)

/-- `m` is odious: an odd number of 1's in binary. -/
def IsOdious (m : ℕ) : Prop := Odd ((Nat.digits 2 m).count 1)

/-- The conjecture on A230495: for every `n >= 1` there is an odd `k` such that `k^i` is evil for
all `i = 1, ..., n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, Odd k ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n → IsEvil (k ^ i) := by
  sorry

end OMA.S_oeis_a230495
