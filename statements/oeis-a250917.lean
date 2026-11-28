import Mathlib

/-!
# A250917: Mathar's recurrence

Source: https://oeis.org/A250917
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A250917 (offset 0): expansion of e.g.f. exp( x*C(x)^3 ) where C(x) = (1 - sqrt(1-4*x))/(2*x) is the g.f. of the Catalan numbers, A000108;
data 1, 1, 7, 73, 1033, 18541, 403831, 10351237, 305355793, 10192132153, 379819484551, 15634219476481, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
+2*a(n) +(-11*n+20)*a(n-1) +(n^3+9*n^2-116*n+164)*a(n-2) +(-4*n^4+35*n^3+n^2-317*n+342)*a(n-3)
-6*(n-3)*(6*n^3-50*n^2+147*n-176)*a(n-4) +12*(n-5)*(2*n-9)*(n-3)*(n-4)*a(n-5) = 0.

Formalization: the title gives the e.g.f. exp(x*C(x)^3) with C(x) = (1 - sqrt(1-4*x))/(2*x) the Catalan g.f., and this is
used as the definition here. S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1,
that is S = sqrt(1-4x) (the constant term selects the branch of the square root); c is the Catalan
g.f. C(x), determined by 2*x*c = 1 - S; U = x*c^3 has zero constant term, so the composition exp(U) of
the exponential series with U is defined (`(PowerSeries.exp ℚ).subst U`); and the e.g.f. is G = exp(U);
a(n) = n! [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (2)*(18541) + (-35)*(1033) + (-66)*(73) + (657)*(7) + (-708)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a250917

open PowerSeries

/-- The sequence with exponential generating function G: a(n) = n! [x^n] G. -/
noncomputable def a (G : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n G

/-- Mathar's conjectured recurrence for A250917 (a(n) = n! [x^n] G), for n ≥ 5. -/
theorem main : ∀ S c U G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    U = X * c ^ 3 →
    G = (PowerSeries.exp ℚ).subst U →
    ∀ n : ℕ, 5 ≤ n →
      (2) * a G n + (20 - 11 * (n : ℚ)) * a G (n - 1) +
        (164 - 116 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * a G (n - 2) + (342 - 317 * (n : ℚ) + (n : ℚ) ^ 2 + 35 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4) * a G (n - 3) +
        (-3168 + 3702 * (n : ℚ) - 1782 * (n : ℚ) ^ 2 + 408 * (n : ℚ) ^ 3 - 36 * (n : ℚ) ^ 4) * a G (n - 4) + (6480 - 6516 * (n : ℚ) + 2424 * (n : ℚ) ^ 2 - 396 * (n : ℚ) ^ 3 + 24 * (n : ℚ) ^ 4) * a G (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a250917
