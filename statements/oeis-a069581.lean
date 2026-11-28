import Mathlib

/-!
# A069581: Odd greedy Egyptian fraction expansion termination and parity conjecture

Source: https://oeis.org/A069581
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069581: Triangle T(m,n) giving number of unit fractions (with odd denominators)
needed to represent m/n, rational (n odd), using the greedy algorithm.

Statement:
If m/n, a rational number (n odd, 1 < m < n) is expressed as sum (1/x_i), where the x_i are
successively chosen to be the least possible odd integers which leave a nonnegative remainder,
is the sum always finite? Conjecture: odd m needs odd, even m needs even unit fractions.
-/

namespace OMA.S_oeis_a069581

/-- One step of the odd greedy algorithm on a positive rational `q`: subtract `1 / x` where
    `x` is the smallest positive odd integer with `1 / x <= q`. -/
noncomputable def oddGreedyStep (q : ℚ) : ℚ :=
  if q ≤ 0 then 0
  else
    let x := sInf {d : ℕ | Odd d ∧ (1 : ℚ) / (d : ℚ) ≤ q}
    q - (1 : ℚ) / (x : ℚ)

theorem main :
    ∀ m n : ℕ, Odd n → 1 < m → m < n →
      ∃ k : ℕ,
        Nat.iterate oddGreedyStep k ((m : ℚ) / (n : ℚ)) = 0 ∧
        (∀ j : ℕ, j < k → Nat.iterate oddGreedyStep j ((m : ℚ) / (n : ℚ)) ≠ 0) ∧
        (Odd m ↔ Odd k) := by
  sorry

end OMA.S_oeis_a069581
