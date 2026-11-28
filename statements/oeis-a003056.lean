import Mathlib

/-!
# Amdeberhan's generating function for A003056

Let `b n` be the largest number of distinct parts in a partition of `n`.
Each distinct row length contributes one cell of hook length one, so this is
the maximum number of one-hooks used in Conjecture 1.1 of Fan, Yang and Yu.

For its ordinary generating function B, the conjecture is
`B(q) = ((q²;q²)∞² / (q;q)∞ - 1) / (1-q)`.
The statement clears denominators and equates coefficients in each degree D.
All factors beyond D have constant term one and no other terms through D.

Source: https://oeis.org/A003056 (OEIS Foundation, CC BY-SA 4.0)
Reference: https://arxiv.org/abs/1212.3505
Credit: @connoranderson
-/

namespace OMA.S_oeis_a003056

open Finset Polynomial

noncomputable def b (n : ℕ) : ℕ :=
  (univ : Finset n.Partition).sup fun p => p.parts.toFinset.card

noncomputable def truncB (D : ℕ) : Polynomial ℤ :=
  ∑ n ∈ range (D+1), monomial n (b n : ℤ)

noncomputable def eulerProd (D step : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range D, (1 - X^(step*(j+1)))

theorem main : ∀ D : ℕ,
    (((1-X)*truncB D + 1)*eulerProd D 1).coeff D = ((eulerProd D 2)^2).coeff D := by
  sorry

end OMA.S_oeis_a003056
