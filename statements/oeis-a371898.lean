import Mathlib

/-!
# A371898: Triangle read by rows: T(n, k) = n * k * (T(n-1, k-1) + T(n-1, k)) for k > 0 with initial values T(n, 0) = 1 and T(i, j) = 0 for j > i.

Source: https://oeis.org/A371898
Credit: @agchua

Two conjectures in the formula section of A371898 (entry by Werner Schulte, Apr 11 2024):
  Conjecture: E.g.f. of column k is exp(t) * t^k * k! / (Prod_{i=0..k} (1 - i*t)).
  Conjecture: Sum_{k=0..n} (-1)^(n-k) * T(n, k) = A000166(n).
This file states both, for every k ≥ 0 and every n ≥ 0 (offset 0: rows n ≥ 0, columns 0 ≤ k ≤ n).
Definition: exactly the rule of the name and of the entry's PARI program,
T(n, k) = if k = 0 then 1, else if k > n then 0, else n * k * (T(n-1, k-1) + T(n-1, k)).
The e.g.f. of column k is the formal power series with coefficients T(n, k)/n! over ℚ. Since the
product Prod_{i=0..k} (1 - i*t) has constant term 1, the first conjecture is stated in the equivalent
form (Sum_n T(n, k) t^n / n!) * Prod_{i=0..k} (1 - i*t) = k! * t^k * exp(t), with PowerSeries.exp ℚ.
A000166(n) is the number of derangements of n elements (1, 0, 1, 2, 9, 44, ... from n = 0), which is
Mathlib's numDerangements n.
-/

namespace OMA.S_oeis_a371898

/-- A371898: T(n, 0) = 1, T(0, k) = 0 for k > 0, and for n, k > 0:
T(n, k) = 0 if k > n, else n * k * (T(n-1, k-1) + T(n-1, k)). -/
def T : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => if n + 1 < k + 1 then 0 else (n + 1) * (k + 1) * (T n k + T n (k + 1))

/-- The two conjectures: the e.g.f. of column k times Prod_{i=0..k} (1 - i t) is k! t^k exp(t), and
Sum_{k=0..n} (-1)^(n-k) T(n, k) is the number of derangements of n elements (A000166). -/
theorem main :
    (∀ k : ℕ, PowerSeries.mk (fun n => (T n k : ℚ) / (n.factorial : ℚ)) *
        ∏ i ∈ Finset.range (k + 1), (1 - (i : PowerSeries ℚ) * PowerSeries.X) =
      (k.factorial : PowerSeries ℚ) * PowerSeries.X ^ k * PowerSeries.exp ℚ) ∧
    ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (T n k : ℤ) =
      (numDerangements n : ℤ) := by
  sorry

end OMA.S_oeis_a371898
