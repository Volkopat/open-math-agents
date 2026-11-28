import Mathlib

/-!
# A091817: (2*numerator(H(p-3)) - 3*denominator(H(p-3)))/p with H(m) = 1 + 1/2 + ... + 1/m

Source: https://oeis.org/A091817
Credit: @xor2k

Formalizes the OEIS A091817 conjecture: Leroy Quet conjectures that the terms are always integral.
That is, for every prime `p ≥ 3`, `p` divides `2*numerator(H(p-3)) - 3*denominator(H(p-3))`.

Conventions:
* The sequence runs over the primes `p ≥ 3` (offset 1, `a(1) = -1` comes from `p = 3`, as in the
  PARI program `forprime(p=3, ...)`), so the range is all primes `p ≥ 3`.
* `H(m)` is Mathlib's `harmonic m : ℚ` (with `H(0) = 0`); numerator and denominator are
  `Rat.num` and `Rat.den` of the reduced fraction, as in OEIS (A001008, A002805).
* Integral means divisibility in `ℤ`. Since `p ≥ 3`, the natural subtraction `p - 3` is exact.
-/

namespace OMA.S_oeis_a091817

/-- For every prime `p ≥ 3`, `p ∣ 2 * num(H(p-3)) - 3 * den(H(p-3))`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 3 ≤ p →
      (p : ℤ) ∣ 2 * (harmonic (p - 3)).num - 3 * ((harmonic (p - 3)).den : ℤ) := by
  sorry

end OMA.S_oeis_a091817
