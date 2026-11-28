import Mathlib

/-!
# A211163: Numerator of (-1/Pi^n) * integral_{0..1} (log(1-1/x)^n) dx.

Source: https://oeis.org/A211163 (OEIS Foundation, CC BY-SA 4.0)
Credit: @bmendonca3

[Lean proof of this statement](https://github.com/bmendonca3/open-math-agents/blob/feb8870c7e2d2891de8fb595d09f4d383c55925f/proofs/oeis-a211163.lean)

Entry A211163 (Jean-François Alcover, Jan 30 2013), offset 2, data 2, 0, 8, 0, 32, 0, 128, 0,
2560, 0, 1415168, ...
Comment section:
Conjecture: sequence of denominators is A141459.

The same conjecture is in entry A141459 (https://oeis.org/A141459): a(n) = denominator of
integral_{0..1}(log(1-1/x)^n) dx. - Jean-François Alcover, Feb 01 2013

## Reading of the statement

* Write r(n) = (-1/Pi^n) * integral_{0..1} log(1-1/x)^n dx. The entry lists the numerators of
  r(n) for n >= 2. Its example line gives 2/3, 0, 8/15, 0, 32/21, 0, 128/15, 0, 2560/33 (each
  shown with the factor Pi^n) for n = 2, ..., 10. The conjecture says that the denominator of
  r(n) is A141459(n), with the same index n: A141459(2), ..., A141459(10) are
  3, 1, 15, 1, 21, 1, 15, 1, 33.
* For 0 < x < 1 the number 1 - 1/x is a negative real, so the logarithm is a complex logarithm.
  The entry computes with the Mathematica function `Log`, which is the principal branch:
  log(1 - 1/x) = ln((1-x)/x) + i*Pi. This is `Complex.log` of Mathlib, whose imaginary part is
  in the interval (-Pi, Pi] and is Pi on the negative reals. The integral is thus a complex
  number, and r(n) is computed in `ℂ`.
* The source speaks of the numerator and the denominator of r(n). This says that r(n) is a
  rational number, and the denominator is that of the rational in lowest terms (`Rat.den`,
  positive, and equal to 1 for the rational 0). `main` states exactly this: there is a rational
  `q` equal to r(n), with denominator A141459(n). Such a `q` is unique.
* integral_{0..1} is the interval integral of Mathlib, the integral over `Set.Ioc 0 1`. The
  single point 1 does not change the value. The integrand has only logarithmic singularities at
  0 and 1, so the integral converges for every n.
* Range: n >= 2, the offset of A211163. (For n = 1 the value r(1) is -i, which is not rational.)
* `A141459 n` is OEIS A141459 (offset 0, data 1, 1, 3, 1, 15, 1, 21, 1, 15, 1, 33, 1, 1365, ...):
  a(n) = Product_{p-1 divides n} p, where p is an odd prime. For n >= 1 such a prime satisfies
  p - 1 <= n, so the product over the primes p < n + 2 is the whole product. For n = 0 every
  number divides 0 and the entry sets a(0) = 1. The definition gives 1 there, because no prime
  is less than 2. `main` uses only n >= 2. For a prime `p`, the subtraction `p - 1` in `ℕ` is
  exact.
-/

namespace OMA.S_oeis_a211163

/-- OEIS A141459: the product of the odd primes `p` such that `p - 1` divides `n`
(and the value `1` at `n = 0`, as in the entry). -/
def A141459 (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ Odd p ∧ (p - 1) ∣ n), p

/-- Alcover's conjecture: for `n ≥ 2` the number `(-1/π^n) * ∫_0^1 log(1 - 1/x)^n dx`, with the
principal branch of the complex logarithm, is rational and its denominator is `A141459(n)`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ q : ℚ,
    (q : ℂ) = (-1 / (Real.pi : ℂ) ^ n) * ∫ x in (0 : ℝ)..1, Complex.log (1 - 1 / (x : ℂ)) ^ n ∧
    q.den = A141459 n := by
  sorry

end OMA.S_oeis_a211163
