import Mathlib

/-!
# A213381: a(n) = n^n mod (n+2).

Source: https://oeis.org/A213381
Credit: @max-otc

The OEIS entry lists conjectures on a(n) = n^n mod (n+2), n ≥ 0 (offset 0: 1, 1, 0, 2, 4, 3, 0, 7, ...):
  1. the indices of zeros are 2^(x+2) - 2, x ≥ 0;
  2. a(n) = n if n is in A176003, the numbers 3 q - 2 with q the n-th noncomposite number
     (q = 1 or q prime: 1, 4, 7, 13, 19, ...).
Robert Israel (May 05 2015) states that both are true and adds: if p is an odd prime then a(p+2) = (p-1)/2.
That last remark is printed with a sign slip: for p = 3 it gives a(5) = 3125 mod 7 = 3 ≠ 1. Its argument
(a(n) = (-2)^n mod (n+2)) gives a(p-2) = (-2)^(p-2) mod p = (p-1)/2, which holds for every odd prime
(p = 3, 5, 7, 11, 13: a(1) = 1, a(3) = 2, a(5) = 3, a(9) = 5, a(11) = 6). The statement below uses p-2.
-/

namespace OMA.S_oeis_a213381

/-- A213381: a(n) = n^n mod (n+2). -/
def a (n : ℕ) : ℕ := n ^ n % (n + 2)

/-- Membership in A176003: n = 3 q - 2 with q a noncomposite number (q = 1 or q prime). -/
def InA176003 (n : ℕ) : Prop := ∃ q : ℕ, (q = 1 ∨ q.Prime) ∧ n = 3 * q - 2

/-- Conjecture 1 (zeros), conjecture 2 (A176003) and Israel's remark on odd primes. -/
theorem main :
    (∀ n : ℕ, a n = 0 ↔ ∃ x : ℕ, n = 2 ^ (x + 2) - 2) ∧
    (∀ n : ℕ, InA176003 n → a n = n) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → a (p - 2) = (p - 1) / 2) := by
  sorry

end OMA.S_oeis_a213381
