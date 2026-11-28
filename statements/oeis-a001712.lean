import Mathlib

/-!
# A001712: Generalized Stirling numbers, [n+5,5]_3.

Source: https://oeis.org/A001712
Credit: @ivillar

Offset 0, data 1, 12, 119, 1175, 12154, 133938, ... We take the formula of Borislav Crstici from the entry (also the
entry's PARI program) as the definition:
a(n) = Sum_{k=0..n} (-1)^(n+k)*binomial(k+2, 2)*3^k*Stirling1(n+2, k+2),
where Stirling1 is the signed Stirling number of the first kind, s(n,m) = (-1)^(n+m) * c(n,m) with
c(n,m) = Nat.stirlingFirst n m the unsigned one. It reproduces the listed terms.

Conjecture (R. J. Mathar, Jun 09 2018):
a(n) + 3*(-n-3)*a(n-1) + (3*n^2 + 15*n + 19)*a(n-2) - (n+2)^3*a(n-3)=0.
Status: known result: Petros Hadjicostas (Jun 11 2020) derives this recurrence in the entry,
from R_{n+2}^2(a=-3,b=-1) = R_{n+1}^1(a=-3,b=-1) + (n+4)*R_{n+1}^2(a=-3,b=-1).
It is stated for n ≥ 3 (all indices at least the offset 0), over the integers.
-/

namespace OMA.S_oeis_a001712

/-- The signed Stirling number of the first kind s(n,m). -/
def s (n m : ℕ) : ℤ := (-1) ^ (n + m) * (Nat.stirlingFirst n m : ℤ)

/-- Crstici's formula for a(n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n + k) * (Nat.choose (k + 2) 2 : ℤ) * 3 ^ k * s (n + 2) (k + 2)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + 3 * (-(n : ℤ) - 3) * a (n - 1) + (3 * (n : ℤ) ^ 2 + 15 * n + 19) * a (n - 2) -
      ((n : ℤ) + 2) ^ 3 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a001712
