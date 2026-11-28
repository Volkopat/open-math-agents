import Mathlib

/-!
# A179077: a(n) is the residue ((2^p - 2)/p) mod p, where p is the n-th prime.

Source: https://oeis.org/A179077

`a(n) = ((2^p - 2)/p) mod p` with `p = prime(n)`, offset 1 (`prime(1) = 2`); first terms
`1, 2, 1, 4, 10, 6, 9, 6, 11, 2, 12, 2, 5, 7, 41, 19`.

Claim (comment of Felix Fröhlich, Sep 13 2019), in OEIS notation:
`Conjecture: a(n) is the residue A036968(p-1) (mod p) for p = prime(n).`
A036968 is the sequence of Genocchi numbers of the first kind, the expansion of `2*x/(exp(x)+1)` as an
exponential generating function, offset 1: `G(1), G(2), ... = 1, -1, 0, 1, 0, -3, 0, 17, 0, -155`.

The comment continues: if the above conjecture is true, then `a(n) = 0` if and only if `p` is a Wieferich
prime (cf. Hu et al., 2019, section 1.3). That sentence is a conditional remark with a citation, not a
conjecture, so it is not part of the target; this file states the one conjecture. The entry does not say
that the conjecture has been proved. It is a direct consequence of the von Staudt-Clausen theorem
(`p * B(p-1) == -1 (mod p)`) and of the formula `G(n) = 2*(1 - 2^n)*B(n)` given in A036968, so it should
not be described as open.

Formalized:
* `prime n` is the `n`-th prime with the offset of the entry: `prime n = Nat.nth Nat.Prime (n - 1)`,
  so `prime 1 = 2`, `prime 2 = 3`; the claim is stated for `1 ≤ n`.
* `a n` is computed in the integers: `(2^p - 2) / p` is the integer quotient (exact, since `p` divides
  `2^p - 2`), and `%` is the least nonnegative residue modulo `p > 0`.
* `genocchi n` is `n!` times the coefficient of `x^n` in `2*x*(exp(x) + 1)⁻¹`, in the power series over
  the rationals (the inverse exists since the constant coefficient of `exp(x) + 1` is `2`). It is a
  rational number by construction; the claim therefore says that `genocchi (p - 1)` is an integer `g`
  and that `a n` is the least nonnegative residue of `g` modulo `p`. The natural-number subtraction
  `p - 1` is exact for a prime `p`.
-/

namespace OMA.S_oeis_a179077

open PowerSeries

/-- A036968: the Genocchi number `G(n) = n! * [x^n] 2*x/(exp(x) + 1)`, as a rational number. -/
noncomputable def genocchi (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n (2 * X * (exp ℚ + 1)⁻¹ : PowerSeries ℚ)

/-- The `n`-th prime with offset 1: `prime 1 = 2`, `prime 2 = 3`, ... -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A179077: `a(n) = ((2^p - 2)/p) mod p`, where `p` is the `n`-th prime. -/
noncomputable def a (n : ℕ) : ℤ :=
  (((2 : ℤ) ^ prime n - 2) / (prime n : ℤ)) % (prime n : ℤ)

/-- Fröhlich's conjecture: `a(n)` is the residue of the Genocchi number `A036968(p - 1)` modulo
`p = prime(n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ g : ℤ, (g : ℚ) = genocchi (prime n - 1) ∧ a n = g % (prime n : ℤ) := by
  sorry

end OMA.S_oeis_a179077
