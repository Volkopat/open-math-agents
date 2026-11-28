import Mathlib

/-!
# A110320: McGarvey's formula a(n) = (A051292(n+2) - A051286(n+1))/2

Source: https://oeis.org/A110320
Credit: @ivillar

Status: open conjecture (Gerald McGarvey, Jan 14 2007); the entry records it as a conjecture and notes no proof or
verification of it. It is an identity between the generating functions recorded in the three entries, which
are used here as the definitions.

A110320 (offset 1): number of blocks in all RNA secondary structures with n nodes (an RNA secondary
structure can be viewed as a restricted noncrossing partition);
data 1, 2, 5, 13, 32, 80, 201, 505, 1273, 3217, 8146, 20668, ...

Conjecture (Gerald McGarvey, Jan 14 2007): a(n) = (A051292(n+2)-A051286(n+1))/2.

Formalization: the three sequences are defined by the generating functions recorded in their entries, with
S = sqrt(1 - 2*x - x^2 - 2*x^3 + x^4):
  A110320 (offset 1): G.f. (1-z-z^2)/(2*z^2*S) - 1/(2*z^2);
  A051292 (offset 0; 2, 1, 1, 4, 9, 21, 52, ...): G.f. (1 - t^2 + S)/S;
  A051286 (offset 0; 1, 1, 2, 5, 11, 26, 63, ...): G.f. 1/S.
S is the formal power series over ℚ with S^2 = 1 - 2*x - x^2 - 2*x^3 + x^4 and constant term 1 (the constant
term selects the branch of the square root); A is determined by 2*x^2*S*A = (1 - x - x^2) - S, B by
B*S = 1 - x^2 + S and C by C*S = 1 (the stated expressions multiplied by their denominators, which are nonzero
power series); a(n) = [x^n] A, A051292(n) = [x^n] B and A051286(n) = [x^n] C. `main` is stated for n ≥ 1, the
offset of A110320; it is checked by the data, for example a(1) = 1 = (4 - 2)/2, a(2) = 2 = (9 - 5)/2 and
a(3) = 5 = (21 - 11)/2.
-/

namespace OMA.S_oeis_a110320

open PowerSeries

/-- McGarvey's conjectured formula a(n) = (A051292(n+2) - A051286(n+1))/2 for A110320, for n ≥ 1,
with the three sequences given by their generating functions A, B, C. -/
theorem main : ∀ S A B C : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    2 * X ^ 2 * S * A = (1 - X - X ^ 2) - S →
    B * S = 1 - X ^ 2 + S →
    C * S = 1 →
    ∀ n : ℕ, 1 ≤ n →
      coeff n A = (coeff (n + 2) B - coeff (n + 1) C) / 2 := by
  sorry

end OMA.S_oeis_a110320
