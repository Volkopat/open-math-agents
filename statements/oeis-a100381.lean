import Mathlib

/-!
# A100381: a(n) = 2^n*binomial(n,2).

Source: https://oeis.org/A100381
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 4, 24, 96, 320, 960, 2688, 7168, ...

Statements (Peter Bala, Mar 04 2024, formula section of the entry):
Sum_{k = 2..n+2} 1/a(k) = 1/(4 - 4/(7 - 12/(10 - ... - 2*n*(n + 1)/(3*n + 4)))).
Sum_{k = 2..n+2} (-1)^k/a(k) = 1/(4 + 4/(5 + 12/(6 + ... + 2*n*(n + 1)/(n + 4)))).
Letting n -> oo in the above gives the continued fraction representations
1 - log(2) = Sum_{k >= 2} 1/a(k) = 1/(4 - 4/(7 - 12/(10 - ... - 2*n*(n + 1)/((3*n + 4) - ... ))))
(an equivalent continued fraction for 1 - log(2) was conjectured by the Ramanujan machine) and
3*log(3/2) - 1 = Sum_{k >= 2} (-1)^k/a(k) = 1/(4 + 4/(5 + 12/(6 + ... + 2*n*(n + 1)/((n + 4) + ... )))).

Formalization. The finite continued fractions are defined by recursion on their depth:
`K j m` is the continued fraction with partial denominators 3*i + 4 and partial numerators
-2*i*(i + 1) that starts at level i = j and has m further levels, so that
`K 0 n = 4 - 4/(7 - 12/(10 - ... - 2*n*(n + 1)/(3*n + 4)))`; `L j m` is the same with partial
denominators i + 4 and partial numerators +2*i*(i + 1), so that
`L 0 n = 4 + 4/(5 + 12/(6 + ... + 2*n*(n + 1)/(n + 4)))`.
The infinite continued fractions are read as the limits of these finite ones (their convergents),
and the infinite series as `HasSum` statements over k = 2, 3, ... (indexed by k - 2).
-/

namespace OMA.S_oeis_a100381

/-- A100381: a(n) = 2^n * binomial(n,2). -/
def a (n : ℕ) : ℕ := 2 ^ n * n.choose 2

/-- `K j m = (3j+4) - 2(j+1)(j+2)/((3(j+1)+4) - 2(j+2)(j+3)/( ... - 2(j+m)(j+m+1)/(3(j+m)+4)))`. -/
noncomputable def K : ℕ → ℕ → ℝ
  | j, 0 => 3 * (j : ℝ) + 4
  | j, m + 1 => (3 * (j : ℝ) + 4) - 2 * ((j : ℝ) + 1) * ((j : ℝ) + 2) / K (j + 1) m

/-- `L j m = (j+4) + 2(j+1)(j+2)/((j+1+4) + 2(j+2)(j+3)/( ... + 2(j+m)(j+m+1)/(j+m+4)))`. -/
noncomputable def L : ℕ → ℕ → ℝ
  | j, 0 => (j : ℝ) + 4
  | j, m + 1 => ((j : ℝ) + 4) + 2 * ((j : ℝ) + 1) * ((j : ℝ) + 2) / L (j + 1) m

/-- Bala's finite continued fractions for the partial sums of 1/a(k) and (-1)^k/a(k), and the
continued fraction representations of 1 - log(2) and 3*log(3/2) - 1 obtained from them. -/
theorem main :
    (∀ n : ℕ, ∑ k ∈ Finset.Icc 2 (n + 2), (1 : ℝ) / (a k : ℝ) = 1 / K 0 n) ∧
    (∀ n : ℕ, ∑ k ∈ Finset.Icc 2 (n + 2), (-1 : ℝ) ^ k / (a k : ℝ) = 1 / L 0 n) ∧
    HasSum (fun k : ℕ => (1 : ℝ) / (a (k + 2) : ℝ)) (1 - Real.log 2) ∧
    Filter.Tendsto (fun n : ℕ => 1 / K 0 n) Filter.atTop (nhds (1 - Real.log 2)) ∧
    HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + 2) / (a (k + 2) : ℝ)) (3 * Real.log (3 / 2) - 1) ∧
    Filter.Tendsto (fun n : ℕ => 1 / L 0 n) Filter.atTop (nhds (3 * Real.log (3 / 2) - 1)) := by
  sorry

end OMA.S_oeis_a100381
