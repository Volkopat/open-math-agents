import Mathlib

/-!
# A274719: Expansion of Product_{k >= 1} (1-q^(2*k)).

Source: https://oeis.org/A274719
Credit: @agchua

Conjecture in the formula section of A274719 (verbatim):
  Conjecture: |a(n)| = A089806(n).
Both sequences have offset 0, and the claim is stated for all n >= 0.
a(n) is the coefficient of q^n in Product_{k >= 1} (1 - q^(2k)). The factors with 2k > n do not
change this coefficient, so it is the coefficient of q^n in the finite product over k = 1..n;
that is the definition below (a power series over ℤ).
A089806 (offset 0) is the expansion of the theta quotient
(theta_3(q^(1/3)) - theta_2(q^3))/2/q^(1/12). Its entry gives the explicit formula
(Michael Somos, Jun 06 2005): a(n) = b(12n+1) where b(n) is multiplicative and b(3^e)=0^e,
b(p^e)=(1+(-1)^e)/2 if p<>3. This formula is the definition used below: `b m` is the product,
over the prime factors p of m, of b(p^e), where e is the exponent of p in m (so b 1 = 1).
-/

namespace OMA.S_oeis_a274719

/-- A274719: the coefficient of q^n in Product_{k = 1..n} (1 - q^(2k)). -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.range n, (1 - PowerSeries.X ^ (2 * (k + 1)) : PowerSeries ℤ))

/-- The multiplicative function with b(3^e) = 0^e and b(p^e) = (1+(-1)^e)/2 for primes p ≠ 3. -/
noncomputable def b (m : ℕ) : ℤ :=
  ∏ p ∈ m.primeFactors,
    (if p = 3 then 0 ^ (m.factorization p) else (1 + (-1) ^ (m.factorization p)) / 2)

/-- A089806(n) = b(12n+1). -/
noncomputable def A089806 (n : ℕ) : ℤ := b (12 * n + 1)

/-- The conjecture: |a(n)| = A089806(n) for all n. -/
theorem main : ∀ n : ℕ, |a n| = A089806 n := by
  sorry

end OMA.S_oeis_a274719
