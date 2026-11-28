import Mathlib

/-!
# A001724: Generalized Stirling numbers, [n+9,9]_5.

Source: https://oeis.org/A001724
Credit: @ivillar

Offset 0, data 1, 35, 835, 17360, 342769, 6687009, ... We take the formula of Borislav Crstici from the entry (also the
entry's PARI program) as the definition:
a(n) = Sum_{k=0..n} (-1)^(n+k)*binomial(k+4, 4)*5^k*Stirling1(n+4, k+4),
where Stirling1 is the signed Stirling number of the first kind, s(n,m) = (-1)^(n+m) * c(n,m) with
c(n,m) = Nat.stirlingFirst n m the unsigned one. It reproduces the listed terms.

Conjecture (R. J. Mathar, Jul 20 2026):
a(n) +5*(-n-6)*a(n-1) +5*(2*n^2+22*n+61)*a(n-2) -5*(n+5)*(2*n^2+20*n+51)*a(n-3)
+(5*n^4+90*n^3+610*n^2+1845*n+2101)*a(n-4) -(n+4)^5*a(n-5)=0.
It is stated for n ≥ 5 (all indices at least the offset 0), over the integers.
-/

namespace OMA.S_oeis_a001724

/-- The signed Stirling number of the first kind s(n,m). -/
def s (n m : ℕ) : ℤ := (-1) ^ (n + m) * (Nat.stirlingFirst n m : ℤ)

/-- Crstici's formula for a(n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n + k) * (Nat.choose (k + 4) 4 : ℤ) * 5 ^ k * s (n + 4) (k + 4)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + 5 * (-(n : ℤ) - 6) * a (n - 1) + 5 * (2 * (n : ℤ) ^ 2 + 22 * n + 61) * a (n - 2) -
      5 * ((n : ℤ) + 5) * (2 * (n : ℤ) ^ 2 + 20 * n + 51) * a (n - 3) +
      (5 * (n : ℤ) ^ 4 + 90 * (n : ℤ) ^ 3 + 610 * (n : ℤ) ^ 2 + 1845 * n + 2101) * a (n - 4) -
      ((n : ℤ) + 4) ^ 5 * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a001724
