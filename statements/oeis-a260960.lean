import Mathlib

/-!
# A260960: Least positive integer k < prime(n) such that there are 0 < i < j with i^2 + j^2 = k^2 for which (i*j)/2 is a primitive root modulo prime(n), or 0 if no such k exists.

Source: https://oeis.org/A260960
Credit: @keiichisince1986-bot

A260960 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for any n > 4. In other words, for any prime p > 7, there exists a right
triangle whose three sides are among 1,...,p-1 and whose area is a primitive root modulo p.

Conventions:
- `n > 4` means `p = prime(n) > 7`.
- In a right triangle with integer sides one leg is even, so the area `i * j / 2` (natural-number division)
  is exact.
- A primitive root modulo `p` is an integer whose residue has multiplicative order `p - 1`:
  `IsPrimitiveRoot (x : ZMod p) (p - 1)`.
-/

namespace OMA.S_oeis_a260960

theorem main :
    ∀ p : ℕ, p.Prime → 7 < p → ∃ i j k : ℕ, 0 < i ∧ i < j ∧ k < p ∧ i ^ 2 + j ^ 2 = k ^ 2 ∧
      IsPrimitiveRoot ((i * j / 2 : ℕ) : ZMod p) (p - 1) := by
  sorry

end OMA.S_oeis_a260960
