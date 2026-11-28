import OMAStatements.S_oeis_a263998

-- Reduction oeis-a263998.R1 of A263998: Number of ordered ways to write n as x^2 + 2*y^2 + p*(p+d)/2, where x and y are nonnegative integers, d is 1 or -1, and p is prime
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a263998_R1

open OMA.S_oeis_a263998

/-- Even `n > 40`: `a n ≥ 2`. -/
def H1 : Prop := ∀ n : ℕ, 40 < n → Even n → 2 ≤ a n

/-- Odd `n > 40`: `a n ≥ 2`. -/
def H2 : Prop := ∀ n : ℕ, 40 < n → Odd n → 2 ≤ a n

/-- Every `n ≤ 40` is checked by direct computation. -/
theorem small : ∀ n ≤ 40, 0 < n → 0 < a n ∧ (a n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 8) := by decide +kernel

/-- Both conjuncts hold for `n ≤ 40` by computation; for `n > 40` they follow from `a n ≥ 2`, which
is split by parity into `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a263998.main := by
  intro h1 h2
  have two : ∀ n : ℕ, 40 < n → 2 ≤ a n := fun n hn => by
    rcases Nat.even_or_odd n with he | ho
    · exact h1 n hn he
    · exact h2 n hn ho
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rcases (show n ≤ 40 ∨ 40 < n by omega) with hs | hl
    · exact (small n hs hn).1
    · have := two n hl
      omega
  · rcases (show n ≤ 40 ∨ 40 < n by omega) with hs | hl
    · exact (small n hs hn).2
    · have := two n hl
      constructor
      · intro h
        omega
      · intro hmem
        try simp at hmem
        omega

end OMA.R_oeis_a263998_R1
