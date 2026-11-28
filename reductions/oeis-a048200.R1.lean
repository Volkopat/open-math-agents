import OMAStatements.S_oeis_a048200

-- Reduction oeis-a048200.R1 of the Kuppili-Chitturi reversal-length formula.
-- Credit: @Ciphore
-- The lower bound is the optimality half; the upper bound is the constructive half.

namespace OMA.R_oeis_a048200_R1

open OMA.S_oeis_a048200

/-- Lower bounds for the minimal reversal length, in the parity-cleared forms. -/
def H1 : Prop := ∀ n : ℕ, 4 ≤ n →
    (Even n → 3 * n ^ 2 ≤ 4 * a n + 8 * n) ∧
    (Odd n → 3 * n ^ 2 + 15 ≤ 4 * a n + 10 * n)

/-- Upper bounds for the minimal reversal length, in the parity-cleared forms. -/
def H2 : Prop := ∀ n : ℕ, 4 ≤ n →
    (Even n → 4 * a n + 8 * n ≤ 3 * n ^ 2) ∧
    (Odd n → 4 * a n + 10 * n ≤ 3 * n ^ 2 + 15)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a048200.main := by
  intro h1 h2 n hn
  obtain ⟨loEven, loOdd⟩ := h1 n hn
  obtain ⟨hiEven, hiOdd⟩ := h2 n hn
  constructor
  · intro he
    have lo := loEven he
    have hi := hiEven he
    omega
  · intro ho
    have lo := loOdd ho
    have hi := hiOdd ho
    omega

end OMA.R_oeis_a048200_R1
