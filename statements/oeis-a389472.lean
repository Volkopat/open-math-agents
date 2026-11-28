import Mathlib

/-!
# A389472: G.f. satisfies A(x) = A(x^2 + x^3)/x^2 - 1.

Source: https://oeis.org/A389472
Credit: @agchua

Comments of A389472 (unsigned; the entry is by Paul D. Hanna, Oct 15 2025):
  Conjecture: a(2*n-1) = 0 (mod 2) for n > 1.
  Conjecture: a(3*n-1) = 0 (mod 3) for n > 1.
The sequence has offset 1 and A(x) = Sum_{n>=1} a(n)*x^n, so a(0) = 0. The functional equation
says A(x^2 + x^3) = x^2 + x^2*A(x). Since (x^2 + x^3)^k = Sum_j binomial(k,j)*x^(2k+j), comparing
the coefficients of x^(N+2) gives Sum_{k with 2k <= N+2} a(k)*binomial(k, N+2-2k) = a(N) + [N = 0].
For N = 0 this forces a(1) = 1; for N = 1 and N = 2 it reads a(1) = a(1) and a(2) = a(2), so the
equation leaves a(2) free, and a(2) = 1 as in the entry's data and its PARI program (which starts
from x + x^2). For N >= 3 the terms with k >= N vanish (2k > N + 2), so
a(N) = Sum_{k < N, 2k <= N+2} a(k)*binomial(k, N+2-2k), the recursion below (with N = n + 3).
The claims are stated for n > 1, as in the entry.
-/

namespace OMA.S_oeis_a389472

/-- A389472, with a(0) = 0 (the constant term of A), a(1) = a(2) = 1 and, for N = n + 3 >= 3,
a(N) = Sum over k < N with 2k <= N + 2 of a(k) * binomial(k, N + 2 - 2k). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => ∑ k : Fin (n + 3),
      if 2 * (k : ℕ) ≤ n + 5 then a k * (k : ℕ).choose (n + 5 - 2 * (k : ℕ)) else 0

/-- The entry's two conjectures: a(2n-1) is divisible by 2 and a(3n-1) is divisible by 3 for
n > 1. -/
theorem main : (∀ n : ℕ, 1 < n → 2 ∣ a (2 * n - 1)) ∧ (∀ n : ℕ, 1 < n → 3 ∣ a (3 * n - 1)) := by
  sorry

end OMA.S_oeis_a389472
