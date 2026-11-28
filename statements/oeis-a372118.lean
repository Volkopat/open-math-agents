import Mathlib

/-!
# A372118: three properties of the arrays A(m; n, k) (OEIS A372118)

Source: https://oeis.org/A372118 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

The comments of the entry define, for a fixed integer m >= 0, the square array
  A(m; n, k) = (Sum_{i=0..m} (-1)^i * binomial(m, i) * (k + m - i)^(n+m)) / m!
for n, k >= 0 (`fam m n k` below, as a rational number). The array of the title
is the case m = 2: A(n, k) = ((k+2)^(n+2) - 2*(k+1)^(n+2) + k^(n+2)) / 2 (`A n k`).

The comments conjecture three properties for every m, and the formula section
repeats them for m = 2 (both are reported true by Sela Fried, Jul 2024):
  (1) the o.g.f. of column k is Prod_{i=k..k+m} 1 / (1 - i*t);
  (2) the e.g.f. of row n is
      exp(x) * Sum_{k=0..n} binomial(k+m, m) * S2(n+m, k+m) * x^k;
  (3) A(m; n, k) = Sum_{i=0..k} L(m; n, i) * binomial(k, i), where
      L(m; n, i) = S2(n+m, i+m) * (i+m)! / m!   (the LU decomposition with U the
      transpose of Pascal's triangle A007318).
Here S2 is A048993, the Stirling numbers of the second kind
(`Nat.stirlingSecond`). Generating functions are formal power series over the
rationals: the o.g.f. of column k is the series with n-th coefficient
A(m; n, k), and the e.g.f. of row n has k-th coefficient A(m; n, k) / k!.

`main` conjoins the three general statements (all m) and then the three
statements of the formula section for the array of the title.
-/

namespace OMA.S_oeis_a372118

open Finset

/-- The family A(m; n, k) of the comments. -/
def fam (m n k : ℕ) : ℚ :=
  (∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (m.choose i : ℚ) * ((k : ℚ) + m - i) ^ (n + m))
    / (m.factorial : ℚ)

/-- The array of the title, the case m = 2. -/
def A (n k : ℕ) : ℚ :=
  (((k : ℚ) + 2) ^ (n + 2) - 2 * ((k : ℚ) + 1) ^ (n + 2) + (k : ℚ) ^ (n + 2)) / 2

theorem main :
    (∀ m k : ℕ, PowerSeries.mk (fun n => fam m n k) =
      (∏ i ∈ Icc k (k + m), (1 - PowerSeries.C (i : ℚ) * PowerSeries.X))⁻¹) ∧
    (∀ m n : ℕ, PowerSeries.mk (fun k => fam m n k / (k.factorial : ℚ)) =
      PowerSeries.exp ℚ * ∑ k ∈ range (n + 1),
        PowerSeries.C (((k + m).choose m : ℚ) * (Nat.stirlingSecond (n + m) (k + m) : ℚ))
          * PowerSeries.X ^ k) ∧
    (∀ m n k : ℕ, fam m n k = ∑ i ∈ range (k + 1),
      (Nat.stirlingSecond (n + m) (i + m) : ℚ) * ((i + m).factorial : ℚ) / (m.factorial : ℚ)
        * (k.choose i : ℚ)) ∧
    (∀ k : ℕ, PowerSeries.mk (fun n => A n k) =
      (∏ i ∈ Icc k (k + 2), (1 - PowerSeries.C (i : ℚ) * PowerSeries.X))⁻¹) ∧
    (∀ n : ℕ, PowerSeries.mk (fun k => A n k / (k.factorial : ℚ)) =
      PowerSeries.exp ℚ * ∑ k ∈ range (n + 1),
        PowerSeries.C (((k + 2).choose 2 : ℚ) * (Nat.stirlingSecond (n + 2) (k + 2) : ℚ))
          * PowerSeries.X ^ k) ∧
    (∀ n k : ℕ, A n k = ∑ i ∈ range (k + 1),
      (Nat.stirlingSecond (n + 2) (i + 2) : ℚ) * ((i + 2).factorial : ℚ) / 2
        * (k.choose i : ℚ)) := by
  sorry

end OMA.S_oeis_a372118
