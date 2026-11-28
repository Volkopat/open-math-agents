import Mathlib

/-!
# A299438: a(n) is the smallest number k such that there do not exist k numbers in the range [1..n]
whose product is equal to their sum or -1 if no such number exists.

Source: https://oeis.org/A299438
Credit: @Squee451

Data (offset 1): 2, 3, 4, 6, 6, 15, 15, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 80, ...

The entry's comments: If a(n) > 0 for all n, then sequence is nondecreasing and a(n) > n.
Conjecture: a(n) > 0 for all n.

By the definition, a(n) > 0 means exactly that the "-1" case does not occur: there is some k for
which no k numbers from [1..n] have product equal to their sum. That is what is stated.

Conventions.
* The k numbers may repeat (for n = 1 the data has a(1) = 2: the single number 1 works for k = 1, and
  1, 1 does not work for k = 2). They are given as a function `Fin k → ℕ` with values in [1, n].
* k is a positive integer, as in the data.
-/

namespace OMA.S_oeis_a299438

/-- There are `k` numbers in the range `[1..n]` whose product equals their sum. -/
def Represents (n k : ℕ) : Prop :=
  ∃ v : Fin k → ℕ, (∀ j, 1 ≤ v j ∧ v j ≤ n) ∧ ∏ j, v j = ∑ j, v j

/-- For every `n ≥ 1` some positive `k` is not represented, i.e. `a(n) > 0`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ ¬ Represents n k := by
  sorry

end OMA.S_oeis_a299438
