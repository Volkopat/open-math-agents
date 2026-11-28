import Mathlib

/-!
# A352905: Yanev's Dobinski-type formula for the e.g.f. sin(x)*exp(exp(x) - 1)

Source: https://oeis.org/A352905
Credit: @ivillar

Status: known result: the entry records that the conjecture is true (Sela Fried, Dec 07 2025).

A352905 (offset 0) is the expansion of the e.g.f. sin(x) * exp(exp(x) - 1);
data 0, 1, 2, 5, 16, 56, 218, 937, 4376, ... The entry gives the formula
a(n) = Sum_{k=0..floor((n-1)/2)} (-1)^k * binomial(n,2*k+1) * Bell(n-2*k-1).

Conjecture (Velin Yanev, Jul 06 2024):
a(n) = (i/(2*e))*Sum_{k=0..oo} ((k - i)^n - (k + i)^n)/(k!), where i = sqrt(-1) and e = exp(1).
Sela Fried (Dec 07 2025) records in the entry that the conjecture is true.

Formalization: a(n) is defined by the entry's formula as an integer. Bell(m), the number of
partitions of an m-set, is the sum over j of the Stirling numbers of the second kind
`Nat.stirlingSecond m j`. In the natural-number indices, n - 2*k - 1 is truncated subtraction;
the binomial coefficient vanishes whenever 2*k + 1 > n, and for n = 0 the only term is 0. The
infinite sum is the sum of the (absolutely convergent) complex series, written with `tsum`.
-/

namespace OMA.S_oeis_a352905

/-- Bell(m) as the sum of the Stirling numbers of the second kind S(m, j), 0 ≤ j ≤ m. -/
def bell (m : ℕ) : ℕ := ∑ j ∈ Finset.range (m + 1), Nat.stirlingSecond m j

/-- a(n) = ∑_{k=0}^{⌊(n-1)/2⌋} (-1)^k binomial(n, 2k+1) Bell(n - 2k - 1). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range ((n - 1) / 2 + 1),
    (-1) ^ k * (n.choose (2 * k + 1) : ℤ) * (bell (n - 2 * k - 1) : ℤ)

/-- Yanev's conjecture. -/
theorem main : ∀ n : ℕ,
    ((a n : ℤ) : ℂ) = Complex.I / (2 * (Real.exp 1 : ℂ)) *
      ∑' k : ℕ, (((k : ℂ) - Complex.I) ^ n - ((k : ℂ) + Complex.I) ^ n) / (k.factorial : ℂ) := by
  sorry

end OMA.S_oeis_a352905
