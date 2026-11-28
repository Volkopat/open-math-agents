import Mathlib

/-!
# A144837: Bala's 5-adic congruence for Lucas(5^n)

Source: https://oeis.org/A144837
Credit: @ivillar

A144837 (offset 1): a(n) = Lucas(5^n), where Lucas = A000032 (L(0) = 2, L(1) = 1,
L(n) = L(n-1) + L(n-2)); data 11, 167761, ...
From Peter Bala (Nov 14 2022): a(n+1) == a(n) (mod 5^(n+1)) for n >= 1 (a particular case of the
Gauss congruences for the Lucas numbers). Conjecture: a(n+1) == a(n) (mod 5^(n+r+1)) for n >= r.

Formalization notes.
* `lucas` is A000032 computed in ℤ, and a(n) = lucas (5^n); the sequence starts at n = 1.
* The conjecture is stated for all n ≥ 1 and all r ≥ 0 with r ≤ n.
-/

namespace OMA.S_oeis_a144837

/-- The Lucas numbers A000032: L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n). -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- A144837: a(n) = Lucas(5^n) (offset 1). -/
def a (n : ℕ) : ℤ := lucas (5 ^ n)

/-- Bala's conjecture: a(n+1) ≡ a(n) (mod 5^(n+r+1)) whenever 1 ≤ n and r ≤ n. -/
theorem main : ∀ n r : ℕ, 1 ≤ n → r ≤ n → a (n + 1) ≡ a n [ZMOD 5 ^ (n + r + 1)] := by
  sorry

end OMA.S_oeis_a144837
