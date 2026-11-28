import Mathlib

/-!
# A094336: Product of next n numbers divided by the largest factorial divisor.

Source: https://oeis.org/A094336
Credit: @EmircanEsen

Conjecture (OEIS A094336): a(n) > 1 for n > 4.

Formalization notes:
* The positive integers are cut into consecutive blocks of lengths `1, 2, 3, …`: block `n` is
  `T(n-1)+1, …, T(n)` with `T(k) = k(k+1)/2`. For example block 5 is `11, …, 15` and block 6 is
  `16, …, 21` (the OEIS examples).
* `a n` is the block product divided by the largest factorial `k!` dividing it. Since `k! ∣ P`
  forces `k! ≤ P`, the set of such `k` is bounded and `sSup` is a true maximum. These definitions
  reproduce the OEIS data `1, 1, 1, 1, 3003, 969, 16445, …`.
* `a n > 1` says exactly that the block product is not itself a factorial. Among `n < 400` only
  `n = 1, 2, 3, 4` give a factorial.
-/

namespace OMA.S_oeis_a094336

/-- The product of block `n`: the `n` consecutive integers after `n(n-1)/2`. -/
def blockProd (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (n * (n - 1) / 2 + 1 + i)

/-- The largest `k` with `k! ∣ blockProd n`. -/
noncomputable def largestFact (n : ℕ) : ℕ := sSup {k : ℕ | k.factorial ∣ blockProd n}

/-- A094336, offset 1: the block product divided by its largest factorial divisor. -/
noncomputable def a (n : ℕ) : ℕ := blockProd n / (largestFact n).factorial

/-- For every `n > 4`, `a n > 1`. -/
theorem main : ∀ n : ℕ, 4 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a094336
