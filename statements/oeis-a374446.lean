import Mathlib

/-!
# A374446: Positions of zeros in the expansion of Product_{k>=0} (1 - x^(2^k))^3; A373308(a(n)) = 0 for n >= 1.

Source: https://oeis.org/A374446
Credit: @esracummings31-blip

Conjecture (OEIS, A374446): a(n) = A001196(n) - 1 for n >= 1, where A001196 lists numbers
with only even length runs in their binary expansion.

Conventions.
* `A373308 n` is the coefficient of `x^n` in `Product_{k>=0} (1 - x^(2^k))^3`. Factors with
  `2^k > n` do not affect that coefficient, so we read it off the finite product over
  `k < n + 1` (note `2^(n+1) > n`).
* `a n` (offset 1, as in OEIS: a(1) = 2) is the `n`-th zero position, i.e. `Nat.nth` of the
  zero set at index `n - 1`.
* `A001196 n` (offset 0, A001196(0) = 0) is the `n`-th number (in increasing order) all of
  whose maximal runs of equal binary digits have even length; `0` (empty expansion) qualifies.
-/

namespace OMA.S_oeis_a374446

open Polynomial

/-- The finite product `∏_{k < K} (1 - x^(2^k))^3`. -/
noncomputable def P (K : ℕ) : ℤ[X] := ∏ k ∈ Finset.range K, (1 - X ^ (2 ^ k)) ^ 3

/-- A373308: coefficient of `x^n` in `∏_{k ≥ 0} (1 - x^(2^k))^3`. -/
noncomputable def A373308 (n : ℕ) : ℤ := (P (n + 1)).coeff n

/-- A374446 (offset 1): the `n`-th position of a zero of A373308. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => A373308 m = 0) (n - 1)

/-- Only even length runs in the binary expansion. -/
def EvenRuns (m : ℕ) : Prop :=
  ∀ r ∈ (Nat.digits 2 m).splitBy (· == ·), Even r.length

/-- A001196 (offset 0): numbers with only even length runs in their binary expansion. -/
noncomputable def A001196 (n : ℕ) : ℕ := Nat.nth EvenRuns n

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A001196 n - 1 := by
  sorry

end OMA.S_oeis_a374446
