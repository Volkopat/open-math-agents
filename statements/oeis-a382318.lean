import Mathlib

/-!
# A382318: G.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3.

Source: https://oeis.org/A382318
Credit: @agchua

Comment of A382318 (unsigned; the entry is by Paul D. Hanna, Apr 10 2025):
  Conjectures: a(3*n) == A382319(n) (mod 3) for n >= 0; a(3*n+1) == 0 (mod 3) and a(3*n+2) == 0 (mod 3) for n >= 1.
The sequence has offset 1 and A(x) = Sum_{n>=1} a(n)*x^n, so a(0) = 0. A382319 has the g.f.
B(x) = Sum_{n>=1} b(n)*x^n with B(x) = x/(1-x) + Sum_{n>=1} B(x^n)^3 (its name), and both entries
give A(x) = x + B(x)^3 and B(x) = A(x) + A(x^2) + A(x^3) + ...: if A = x + B^3, then
Sum_{n>=1} A(x^n) = x/(1-x) + Sum_{n>=1} B(x^n)^3 = B, so A = x + (Sum_{n>=1} A(x^n))^3, and each
functional equation determines its coefficients one by one. So b(0) = 0, b(m) = 1 +
Sum_{d | m} [x^d] B(x)^3 for m >= 1, and a(n) = [n = 1] + [x^n] B(x)^3. The coefficient [x^d] B(x)^3
only involves b(i) for i < d (as b(0) = 0), so B may be cut after x^m when computing b(m+1), and
after x^n when computing a(n); the definitions below do this. b(0) = 0 is also the value of
A382319 at 0 needed for the case n = 0 of the first claim (a(0) = 0).
-/

namespace OMA.S_oeis_a382318

/-- A382319: b(0) = 0 and b(m+1) = 1 + Sum_{d | m+1} [x^d] (Sum_{i <= m} b(i)*x^i)^3. -/
noncomputable def b : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + ∑ d ∈ Nat.divisors (m + 1),
      ((∑ i : Fin (m + 1), Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)) ^ 3).coeff d

/-- A382318: a(n) = [n = 1] + [x^n] (Sum_{i <= n} b(i)*x^i)^3, that is, the coefficients of
x + B(x)^3. -/
noncomputable def a (n : ℕ) : ℕ :=
  (if n = 1 then 1 else 0) +
    ((∑ i ∈ Finset.range (n + 1), Polynomial.C (b i) * Polynomial.X ^ i) ^ 3).coeff n

/-- The comment's conjectures: a(3n) = A382319(n) (mod 3) for n >= 0, and a(3n+1) = a(3n+2) = 0
(mod 3) for n >= 1. -/
theorem main : (∀ n : ℕ, a (3 * n) % 3 = b n % 3) ∧
    (∀ n : ℕ, 1 ≤ n → a (3 * n + 1) % 3 = 0 ∧ a (3 * n + 2) % 3 = 0) := by
  sorry

end OMA.S_oeis_a382318
