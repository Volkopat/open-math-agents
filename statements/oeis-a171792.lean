import Mathlib

/-!
# A171792: a recurrence for the series with A(x) = (x + A(x + x^2))/2

Source: https://oeis.org/A171792 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Paul D. Hanna, Jan 25 2010), offset 1:
G.f. A(x) satisfies: A(x) = (x + A(x+x^2))/2 with A(0)=0. Data
1, 1, 2, 7, 34, 214, 1652, 15121, 160110, ...

Formula section: Conjecture: a(n) = Sum_{r=ceiling(n/2)..n-1} binomial(r, n-r)*a(r) with
a(1) = 1. See [Aspenberg, Perez]. - Michel Marcus, Jun 26 2019

Formalization notes.
* `A` is a formal power series over the rationals with constant coefficient 0, and a(n) is its
  coefficient of x^n. A(x + x^2) is the substitution `A.subst (X + X ^ 2)`, which is defined
  because x + x^2 has constant coefficient 0.
* The functional equation and A(0) = 0 determine A. `main` is stated for every power series
  that satisfies them, so it does not depend on a construction of A.
* ceiling(n/2) is `(n + 1) / 2`. The recurrence is claimed for n >= 2: for n = 1 the sum is
  empty and the entry gives the value a(1) = 1 separately.
-/

namespace OMA.S_oeis_a171792

open PowerSeries

/-- Marcus's conjecture: a(1) = 1 and a(n) = Sum_{r=ceiling(n/2)..n-1} binomial(r, n-r) a(r)
for n >= 2. -/
theorem main : ∀ A : ℚ⟦X⟧, constantCoeff A = 0 →
    A = (1 / 2 : ℚ) • (X + A.subst (X + X ^ 2 : ℚ⟦X⟧)) →
    coeff 1 A = 1 ∧ ∀ n : ℕ, 2 ≤ n →
      coeff n A = ∑ r ∈ Finset.Icc ((n + 1) / 2) (n - 1), (r.choose (n - r) : ℚ) * coeff r A := by
  sorry

end OMA.S_oeis_a171792
