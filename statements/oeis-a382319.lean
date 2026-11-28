import Mathlib

/-!
# A382319: G.f. A(x) satisfies A(x) = x/(1-x) + Sum_{n>=1} A(x^n)^3.

Source: https://oeis.org/A382319
Credit: @agchua

Comment of A382319 (unsigned; the entry is by Paul D. Hanna, Apr 10 2025):
  Conjecture: a(n) == A382318(3*n) (mod 3) for n >= 0.
The sequence has offset 1 and A(x) = Sum_{n>=1} a(n)*x^n, so a(0) = 0 (needed for n = 0).
Comparing coefficients of x^m (m >= 1) in the name: a(m) = 1 + Sum_{d | m} [x^d] A(x)^3, since
[x^m] A(x^e)^3 = [x^(m/e)] A(x)^3 when e divides m and 0 otherwise. As a(0) = 0, [x^d] A(x)^3
only involves a(i) for i < d, so A may be cut after x^(m-1) when computing a(m); the definition
below does this. A382318 is given by the entry's own formula (2): A(x) = Sum_{n>=1} B(x^n) where
B(x) = x + A(x)^3 is the g.f. of A382318. So A382318(n) = [n = 1] + [x^n] A(x)^3 (A382318 has
offset 1 and value 0 at n = 0, the case n = 0 of the claim), and A may be cut after x^n.
-/

namespace OMA.S_oeis_a382319

/-- A382319: a(0) = 0 and a(m+1) = 1 + Sum_{d | m+1} [x^d] (Sum_{i <= m} a(i)*x^i)^3. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + ∑ d ∈ Nat.divisors (m + 1),
      ((∑ i : Fin (m + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) ^ 3).coeff d

/-- A382318: A382318(n) = [n = 1] + [x^n] (Sum_{i <= n} a(i)*x^i)^3, that is, the coefficients
of x + A(x)^3. -/
noncomputable def A382318 (n : ℕ) : ℕ :=
  (if n = 1 then 1 else 0) +
    ((∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ i) ^ 3).coeff n

/-- The comment's conjecture: a(n) = A382318(3n) (mod 3) for n >= 0. -/
theorem main : ∀ n : ℕ, a n % 3 = A382318 (3 * n) % 3 := by
  sorry

end OMA.S_oeis_a382319
