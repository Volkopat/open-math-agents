import OMAStatements.S_oeis_a239430

-- Reduction oeis-a239430.R1 of A239430: Number of ways to write n = k + m with k > 0 and m > 0 such that pi(2*k) - pi(k) is prime and pi(2*m) - pi(m) is a square, where p
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a239430_R1

open OMA.S_oeis_a239430

/-- Even `n > 30`: `a n ≥ 2`. -/
def H1 : Prop := ∀ n : ℕ, 30 < n → Even n → 2 ≤ a n

/-- Odd `n > 30`: `a n ≥ 2`. -/
def H2 : Prop := ∀ n : ℕ, 30 < n → Odd n → 2 ≤ a n

/-- Every `n ≤ 30` is checked by direct computation. -/
theorem small : ∀ n ≤ 30, 1 ≤ n → (4 < n → 0 < a n) ∧ (a n = 1 ↔ n ∈ ([5, 6, 20] : List ℕ)) := by decide +kernel

/-- Both conjuncts hold for `n ≤ 30` by computation; for `n > 30` they follow from `a n ≥ 2`, which
is split by parity into `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a239430.main := by
  intro h1 h2
  have two : ∀ n : ℕ, 30 < n → 2 ≤ a n := fun n hn => by
    rcases Nat.even_or_odd n with he | ho
    · exact h1 n hn he
    · exact h2 n hn ho
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rcases (show n ≤ 30 ∨ 30 < n by omega) with hs | hl
    · exact (small n hs (by omega)).1 hn
    · have := two n hl
      omega
  · rcases (show n ≤ 30 ∨ 30 < n by omega) with hs | hl
    · exact (small n hs hn).2
    · have := two n hl
      constructor
      · intro h
        omega
      · intro hmem
        simp at hmem
        omega

end OMA.R_oeis_a239430_R1
