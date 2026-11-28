import Mathlib

/-!
# A007840: an integral formula for the number of ordered cycle factorizations

Source: https://oeis.org/A007840
Credit: @ivillar

Status: known result: the entry records that the conjecture is true (Sela Fried, Feb 14 2026).

A007840 (offset 0) is the number of factorizations of permutations of n letters into ordered
cycles, that is, the number of ways to split n letters into cycles and then to order the cycles
linearly; data 1, 1, 3, 14, 88, 694, 6578, ... The entry gives the formula
a(n) = Sum_{k=1..n} k! * s(n, k), where s(n, k) is the unsigned Stirling number of the first kind
(the number of permutations of n letters with exactly k cycles).

Conjecture (Velin Yanev, Jan 10 2026):
a(n) = Integral_{x=0..oo} Gamma(x + n)/(exp(x)*Gamma(x)) dx.
Sela Fried (Feb 14 2026) records in the entry that the conjecture is true.

Formalization: `Nat.stirlingFirst n k` is Mathlib's unsigned Stirling number of the first kind.
The sum runs over k = 0, ..., n; the k = 0 term vanishes for n ≥ 1 and gives a(0) = 1. The integral
is the Lebesgue integral over the open half-line (0, ∞), on which Gamma(x) > 0, and the equality
is stated in ℝ for every n ≥ 0.
-/

namespace OMA.S_oeis_a007840

/-- a(n) = ∑_{k=0}^{n} k! · s(n, k), with the unsigned Stirling numbers of the first kind. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingFirst n k

/-- Yanev's conjecture: a(n) = ∫_0^∞ Γ(x + n) / (e^x Γ(x)) dx. -/
theorem main : ∀ n : ℕ,
    (a n : ℝ) = ∫ x in Set.Ioi (0 : ℝ), Real.Gamma (x + n) / (Real.exp x * Real.Gamma x) := by
  sorry

end OMA.S_oeis_a007840
