import OMAStatements.S_oeis_a238645

-- Reduction oeis-a238645.R1 of A238645: Number of odd primes p < 2*n such that the number of squarefree numbers among 1, ..., ((p-1)/2)*n is prime.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a238645_R1

open OMA.S_oeis_a238645

/-- Even `n > 40`: `a n ≥ 2`. -/
def H1 : Prop := ∀ n : ℕ, 40 < n → Even n → 2 ≤ a n

/-- Odd `n > 40`: `a n ≥ 2`. -/
def H2 : Prop := ∀ n : ℕ, 40 < n → Odd n → 2 ≤ a n

/-- Every `n ≤ 40` is checked by direct computation. -/
theorem small : ∀ n ≤ 40, 1 ≤ n → (1 < n → 0 < a n) ∧ (a n = 1 ↔ n ∈ ({2, 4, 7, 14, 19, 29} : Finset ℕ)) := by decide +kernel

/-- Both conjuncts hold for `n ≤ 40` by computation; for `n > 40` they follow from `a n ≥ 2`, which
is split by parity into `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a238645.main := by
  intro h1 h2
  have two : ∀ n : ℕ, 40 < n → 2 ≤ a n := fun n hn => by
    rcases Nat.even_or_odd n with he | ho
    · exact h1 n hn he
    · exact h2 n hn ho
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rcases (show n ≤ 40 ∨ 40 < n by omega) with hs | hl
    · exact (small n hs (by omega)).1 hn
    · have := two n hl
      omega
  · rcases (show n ≤ 40 ∨ 40 < n by omega) with hs | hl
    · exact (small n hs hn).2
    · have := two n hl
      constructor
      · intro h
        omega
      · intro hmem
        simp at hmem
        omega

end OMA.R_oeis_a238645_R1
