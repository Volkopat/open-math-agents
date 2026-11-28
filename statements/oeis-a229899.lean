import Mathlib

/-!
# A229899: a(n) = |{0<g<p_n: g-1, g, g+1 are primitive roots mod p_n}|, where p_n denotes the n-th prime.

Source: https://oeis.org/A229899
Credit: @keiichisince1986-bot

A229899 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 except for n = 1, 2, 3, 4, 6, 10, 18. In other words, for any prime p > 7 not
equal to 13 or 29 or 61, there are three consecutive integers which are primitive roots modulo p.
The entry adds that this follows from Theorem 1 of Cohen, Oliveira e Silva and Trudgian (2015),
so it is a known result.

Conventions:
- The primes `p_n` for the exceptional indices `n = 1, 2, 3, 4, 6, 10, 18` are
  `2, 3, 5, 7, 13, 29, 61`; we state the conjecture in terms of the prime `p = p_n`.
- A primitive root modulo `p` is an integer whose residue has multiplicative order `p - 1`:
  `IsPrimitiveRoot (x : ZMod p) (p - 1)`. The residue `0` is never one, since `0 ^ (p - 1) = 0 ≠ 1`.
  For `p = 2` the only primitive root is `1`, so `a(1) = 0` (one of `g - 1, g, g + 1` is even), as in
  the data.
- Since `0 < g`, the natural-number subtraction `g - 1` is exact.
- The conjecture says that the set of primes `p` with no `0 < g < p` such that `g - 1`, `g`, `g + 1`
  are all primitive roots modulo `p` is exactly `{2, 3, 5, 7, 13, 29, 61}`.
-/

namespace OMA.S_oeis_a229899

theorem main :
    {p : ℕ | p.Prime ∧ ¬ ∃ g : ℕ, 0 < g ∧ g < p ∧
        IsPrimitiveRoot ((g - 1 : ℕ) : ZMod p) (p - 1) ∧ IsPrimitiveRoot ((g : ℕ) : ZMod p) (p - 1) ∧
        IsPrimitiveRoot ((g + 1 : ℕ) : ZMod p) (p - 1)} = {2, 3, 5, 7, 13, 29, 61} := by
  sorry

end OMA.S_oeis_a229899
