import Mathlib

/-!
# A260946: Least k < prime(n) with i^2 + j^2 = k^2, 0 < i < j, and i*j*k a primitive root.

Source: https://oeis.org/A260946

`a(n)` is the least positive integer `k < prime(n)` such that `i^2 + j^2 = k^2` for some
`0 < i < j` with `i*j*k` a primitive root modulo `prime(n)`, or `0` if no such `k` exists.

Conjecture (Zhi-Wei Sun, Aug 05 2015): `a(n) > 0` for all `n > 11`. In the words of the entry:
for any prime `p > 31` there are `a, b, c` among `1, …, p - 1` with `a^2 + b^2 = c^2` such that
`a*b*c` is a primitive root modulo `p`.

The sequence has offset 1 and begins `0, 0, 0, 0, 10, 0, 15, 5, 5, 5, 0, 17, …`; for example
`a(5) = 10`, since `6^2 + 8^2 = 10^2` and `6*8*10 = 480 ≡ 7` is a primitive root modulo `11`.
The bound is sharp: `a(11) = 0`, where `prime(11) = 31`. A numeric check over all primes below
`10^5` finds exactly `2, 3, 5, 7, 13, 31` without such a triple.

Encoding:
- The statement uses the entry's second form, over primes `p > 31`. Since `prime(11) = 31`, the
  indices `n > 11` are exactly the primes `prime(n) > 31`, and `a(n) > 0` says that some `k` has
  the defining property.
- The triple is `0 < a < b` and `c < p` with `a ^ 2 + b ^ 2 = c ^ 2`, as in the definition of the
  sequence. Then `0 < b < c`, so all three lie in `1, …, p - 1`; and `a ≠ b` always holds for a
  Pythagorean triple, so asking for `a < b` loses nothing.
- Being a primitive root modulo `p` is `IsPrimitiveRoot ((a * b * c : ℕ) : ZMod p) (p - 1)`: the
  residue has multiplicative order `p - 1`.
-/

namespace OMA.S_oeis_a260946

/-- Sun's conjecture: for every prime `p > 31` there is a Pythagorean triple
`a ^ 2 + b ^ 2 = c ^ 2` with `0 < a < b` and `c < p` such that `a * b * c` is a primitive root
modulo `p`. -/
theorem main : ∀ p : ℕ, p.Prime → 31 < p →
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ c < p ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
      IsPrimitiveRoot ((a * b * c : ℕ) : ZMod p) (p - 1) := by
  sorry

end OMA.S_oeis_a260946
