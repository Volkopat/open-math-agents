import Mathlib

/-!
# OEIS A134143

Source: https://oeis.org/A134143
Let `S n` be the sum of the `n`-th pair of twin primes in increasing order.
For each `n ≥ 3`, the number of pairs `1 ≤ i ≤ j < n` with
`S i + S j = S n` is positive. The source's example specifies the bound `j < n`.
-/

namespace OMA.S_oeis_a134143

noncomputable def twinPrimeSum (n : ℕ) : ℕ :=
  let p := Nat.nth (fun p : ℕ => p.Prime ∧ (p + 2).Prime) (n - 1)
  p + (p + 2)

noncomputable def countRepresentations (n : ℕ) : ℕ :=
  let indices := Finset.Ico 1 n
  ((indices ×ˢ indices).filter fun (i, j) =>
    i ≤ j ∧ twinPrimeSum i + twinPrimeSum j = twinPrimeSum n).card

theorem main : ∀ n : ℕ, 3 ≤ n → 0 < countRepresentations n := by
  sorry

end OMA.S_oeis_a134143
