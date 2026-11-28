import Mathlib

/-!
# A364608: Smallest k such that there are as many 0's as 1's in the binary representation of (2*n+1)^k, or -1 if no such k exists.

Source: https://oeis.org/A364608
Credit: @azmiozgen

Conjecture (from the entry): a(n) != -1 for all n.

Formalization notes:
* The binary digits are `Nat.digits 2`. a(n) ≠ -1 means some k ≥ 1 makes (2n+1)^k have equally many
  0's and 1's. The offset is 1, so the statement is for n ≥ 1 (for n = 0, 1^k = 1 is never balanced).
* Controls (computed): a(1..29) = 2, 4, 2, 1, 4, 2, 2, 21, 8, 5, 10, 2, 4, 2, 2, 61, 1, 1, 34, 1, 18,
  12, 6, 1, 63, 11, 49, 2, 496, as in the entry; a(n) exists for n < 120 (with k < 3000).
-/

namespace OMA.S_oeis_a364608

/-- For every `n ≥ 1` some power `(2n+1)^k`, `k ≥ 1`, has equally many binary 0's and 1's. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧
      (Nat.digits 2 ((2 * n + 1) ^ k)).count 0 = (Nat.digits 2 ((2 * n + 1) ^ k)).count 1 := by
  sorry

end OMA.S_oeis_a364608
