import Mathlib

/-!
# A364822: Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x))

Source: https://oeis.org/A364822

`a(n) = n! * [x^n] cosh(x) / (1 - 2*sinh(x))`, offset 0. The first terms are
1, 2, 9, 56, 465, 4832, 60249, 876416, 14570145, 272502272, 5662834089.

The comment section of the entry reads (unsigned, hence by the author of the entry, Mélika Tebni,
Nov 07 2023):

    Conjectures: For p prime (p > 2), a(p) == 2 (mod p).
    For n = 2^m (m natural number), a(n) == 1 (mod n).

Both sentences stand under the heading `Conjectures:`, so this file states both, as a conjunction in
the order of the entry. The entry does not say that either of them has been proved.

Formalized:
* `sinhSeries` and `coshSeries` are the Maclaurin series of sinh and cosh over the rationals, given by
  their coefficients (`1 / n!` at odd, respectively even, `n`, and `0` elsewhere), in the same way as
  Mathlib defines `PowerSeries.sin` and `PowerSeries.cos`; Mathlib has no power series sinh or cosh.
* The quotient is the product with the power series inverse of `1 - 2*sinh(x)`. Its constant
  coefficient is `1`, so this is the genuine inverse.
* `a n` is the rational number `n! * [x^n] egf`, following the convention of the other e.g.f. entries.
  A congruence `a(n) == c (mod k)` is stated as: `a n` is (the cast of) an integer `z`, and `k`
  divides `z - c` in the integers. So each claim includes that the term in question is an integer.
* First claim: all primes `p` with `2 < p`.
* Second claim: all natural numbers `m`, zero included (for `m = 0` the modulus is `1` and the
  congruence is trivially true, so it does not matter whether `0` counts as a natural number).
-/

namespace OMA.S_oeis_a364822

/-- The Maclaurin series of sinh: `Sum_{n odd} x^n / n!`. -/
noncomputable def sinhSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Even n then 0 else 1 / (n.factorial : ℚ)

/-- The Maclaurin series of cosh: `Sum_{n even} x^n / n!`. -/
noncomputable def coshSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Even n then 1 / (n.factorial : ℚ) else 0

/-- The exponential generating function `cosh(x) / (1 - 2*sinh(x))`. -/
noncomputable def egf : PowerSeries ℚ := coshSeries * (1 - 2 * sinhSeries)⁻¹

/-- A364822: `a(n) = n! * [x^n] cosh(x) / (1 - 2*sinh(x))`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * PowerSeries.coeff n egf

/-- The two conjectures of the entry: `a(p) == 2 (mod p)` for every prime `p > 2`, and
`a(2^m) == 1 (mod 2^m)` for every natural number `m`. -/
theorem main :
    (∀ p : ℕ, p.Prime → 2 < p → ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z - 2) ∧
    (∀ m : ℕ, ∃ z : ℤ, a (2 ^ m) = (z : ℚ) ∧ ((2 : ℤ) ^ m) ∣ z - 1) := by
  sorry

end OMA.S_oeis_a364822
