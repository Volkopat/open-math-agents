import Mathlib

/-!
# A284475: parts in equal-part partitions minus parts in consecutive-part partitions
Source: https://oeis.org/A284475 (conjecture in the entry of Omar E. Pol, May 03 2017)

a(n) (offset 1) is the total number of parts in all partitions of n into equal parts, minus the
total number of parts in all partitions of n into consecutive parts.
Conjecture: a(n) = A000203(n) - A204217(n) for n >= 1.

Conventions.
* A partition of n into equal parts is a partition all of whose parts coincide (the one-part
  partition counts). A partition into consecutive parts is one whose parts are
  a, a+1, ..., a+m-1 for some a and m, each once (the one-part partition counts).
* A000203 is sigma(n), the sum of the divisors of n.
* A204217 is defined by its title g.f. Sum_{m>=1} m*x^(m(m+1)/2)/(1-x^m), taken in Q[[x]];
  the terms with m > n have order > n, so the coefficient of x^n is that of the finite sum
  over 1 <= m <= n used here.
-/

namespace OMA.S_oeis_a284475

open PowerSeries

/-- Partitions of n into equal parts. -/
def IsEqualParts {n : ℕ} (p : Nat.Partition n) : Prop := ∀ i ∈ p.parts, ∀ j ∈ p.parts, i = j

/-- Partitions of n into consecutive parts. -/
def IsConsecutive {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∃ a m : ℕ, p.parts = (Multiset.range m).map (fun i => a + i)

open Classical in
/-- A284475. -/
noncomputable def a (n : ℕ) : ℤ :=
  (∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter IsEqualParts, (p.parts.card : ℤ)) -
  (∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter IsConsecutive, (p.parts.card : ℤ))

/-- A204217 via its generating function. -/
noncomputable def A204217 (n : ℕ) : ℚ :=
  coeff n (∑ m ∈ Finset.Icc 1 n, (C (m : ℚ)) * X ^ (m * (m + 1) / 2) * (1 - X ^ m)⁻¹)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (ArithmeticFunction.sigma 1 n : ℚ) - A204217 n := by
  sorry

end OMA.S_oeis_a284475
