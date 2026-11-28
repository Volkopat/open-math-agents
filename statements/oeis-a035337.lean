import Mathlib

/-!
# A035337: the third column of the Wythoff array is 3*AA(n) - n + 1

Source: https://oeis.org/A035337
Credit: @ivillar

Status: known result: the entry records that the formula is correct (Aug 31 2017 comment).

The Wythoff array W(n,k) (rows n ≥ 1, columns k ≥ 1) has first column
W(n,1) = floor(floor(n*phi)*phi), second column W(n,2) = floor(floor(n*phi)*phi^2), and
W(n,k) = W(n,k-1) + W(n,k-2) for k ≥ 3, where phi = (1+sqrt(5))/2. A035337 is its third column;
data 3, 11, 16, 24, 32, 37, 45, 50, ...
A003622 is the Wythoff compound sequence AA: A003622(n) = floor(n*phi^2) - 1 for n ≥ 1;
data 1, 4, 6, 9, 12, 14, ...

Conjecture (John W. Layman, Aug 25 2011): a(n) = 3*A003622(n) - n + 1. Michel Dekking
(Aug 31 2017) records in the entry that the formula is correct.

Formalization: rows are indexed by n ≥ 1 as in the array and in Layman's formula (the n-th row
gives the n-th term 3, 11, 16, ...; the entry itself lists the terms with offset 0). The third
column is W(n,1) + W(n,2). All values are integers.
-/

namespace OMA.S_oeis_a035337

open Real

/-- The first column of the Wythoff array: W(n,1) = floor(floor(n*phi)*phi). -/
noncomputable def col1 (n : ℕ) : ℤ := ⌊((⌊(n : ℝ) * goldenRatio⌋ : ℤ) : ℝ) * goldenRatio⌋

/-- The second column of the Wythoff array: W(n,2) = floor(floor(n*phi)*phi^2). -/
noncomputable def col2 (n : ℕ) : ℤ := ⌊((⌊(n : ℝ) * goldenRatio⌋ : ℤ) : ℝ) * goldenRatio ^ 2⌋

/-- The third column of the Wythoff array: W(n,3) = W(n,1) + W(n,2). -/
noncomputable def a (n : ℕ) : ℤ := col1 n + col2 n

/-- A003622(n) = floor(n*phi^2) - 1. -/
noncomputable def AA (n : ℕ) : ℤ := ⌊(n : ℝ) * goldenRatio ^ 2⌋ - 1

/-- Layman's formula. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 3 * AA n - (n : ℤ) + 1 := by
  sorry

end OMA.S_oeis_a035337
