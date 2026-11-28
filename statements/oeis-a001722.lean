import Mathlib

/-!
# A001722: Generalized Stirling numbers, [n+7,7]_5.

Source: https://oeis.org/A001722
Credit: @ivillar

Offset 0, data 1, 18, 251, 3325, 44524, 617624, ... We take the formula of Borislav Crstici from the entry (also the
entry's PARI program) as the definition:
a(n) = Sum_{k=0..n} (-1)^(n+k)*binomial(k+2, 2)*5^k*Stirling1(n+2, k+2),
where Stirling1 is the signed Stirling number of the first kind, s(n,m) = (-1)^(n+m) * c(n,m) with
c(n,m) = Nat.stirlingFirst n m the unsigned one. It reproduces the listed terms.

Conjecture (R. J. Mathar, Jul 20 2026):
a(n) +3*(-n-5)*a(n-1) +(3*n^2+27*n+61)*a(n-2) -(n+4)^3*a(n-3)=0.
It is stated for n ≥ 3 (all indices at least the offset 0), over the integers.
-/

namespace OMA.S_oeis_a001722

/-- The signed Stirling number of the first kind s(n,m). -/
def s (n m : ℕ) : ℤ := (-1) ^ (n + m) * (Nat.stirlingFirst n m : ℤ)

/-- Crstici's formula for a(n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n + k) * (Nat.choose (k + 2) 2 : ℤ) * 5 ^ k * s (n + 2) (k + 2)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + 3 * (-(n : ℤ) - 5) * a (n - 1) + (3 * (n : ℤ) ^ 2 + 27 * n + 61) * a (n - 2) -
      ((n : ℤ) + 4) ^ 3 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a001722
