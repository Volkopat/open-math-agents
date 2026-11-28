import Mathlib

/-!
# A074355: Coefficient of q^1 in nu(n), with (b, lambda) = (1, 3)

Source: https://oeis.org/A074355
Credit: @jagong-cmu

THE CONJECTURE AS STATED IS FALSE. It fails at the coefficient of x^4: the conjectured
g.f. gives 27, but a(4) = 15 (the OEIS example gives nu(4) = 19 + 15q + 12q^2).

The entry has the formula line
G.f.: (9x^4+3x^3)/(1-3x-3x^2)^2 (conjectured). - Ralf Stephan, May 09 2004
This file states that line exactly as written, so that it can be refuted. The expansion of
the conjectured g.f. is 3x^3 + 27x^4 + 153x^5 + ..., while the data is
0, 0, 0, 3, 15, 45, 147, .... (Numerically, the denominator (1-x-3x^2)^2 fits the data;
the stated denominator (1-3x-3x^2)^2 does not.)

Definition (offset 0): nu(0) = 1, nu(1) = b and, for n >= 2,
nu(n) = b*nu(n-1) + lambda*(1+q+q^2+...+q^(n-2))*nu(n-2), with (b, lambda) = (1, 3);
a(n) is the coefficient of q^1 in nu(n).

Conventions:
* `nu b lam n` is a polynomial in `q` over `ℤ` (`Polynomial ℤ`, with `q = Polynomial.X`).
  For `n + 2` the sum `1 + q + ... + q^n` is `∑ i ∈ Finset.range (n + 1), q ^ i`.
* The g.f. is `A = Sum_{n ≥ 0} a(n) x^n` in `PowerSeries ℤ`, and the conjecture is stated with
  the denominator cleared: `A * (1 - 3x - 3x^2)^2 = 9x^4 + 3x^3`. The denominator has constant
  term `1`, so it is a unit and this is equivalent to the quotient form.
-/

namespace OMA.S_oeis_a074355

/-- `nu(0) = 1`, `nu(1) = b`, `nu(n) = b*nu(n-1) + lambda*(1+q+...+q^(n-2))*nu(n-2)`. -/
noncomputable def nu (b lam : ℤ) : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => Polynomial.C b
  | n + 2 => Polynomial.C b * nu b lam (n + 1) +
      Polynomial.C lam * (∑ i ∈ Finset.range (n + 1), Polynomial.X ^ i) * nu b lam n

/-- `a(n)` is the coefficient of `q^1` in `nu(n)` for `(b, lambda) = (1, 3)`. -/
noncomputable def a (n : ℕ) : ℤ := (nu 1 3 n).coeff 1

/-- The conjectured g.f. `(9x^4+3x^3)/(1-3x-3x^2)^2`, as written in OEIS.
It is false (the coefficient of `x^4` is `27`, but `a(4) = 15`). -/
theorem main :
    PowerSeries.mk a * (1 - 3 * (PowerSeries.X : PowerSeries ℤ) - 3 * PowerSeries.X ^ 2) ^ 2 =
      9 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 3 := by
  sorry

end OMA.S_oeis_a074355
