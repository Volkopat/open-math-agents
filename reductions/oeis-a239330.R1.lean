import OMAStatements.S_oeis_a239330

-- Reduction oeis-a239330.R1 of A239330: Number of odd primes p <= n with pi(n*(p+1)/2) - pi(n*(p-1)/2) prime, where pi(x) denotes the number of primes not exceeding x.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a239330_R1

open OMA.S_oeis_a239330

/-- Even `n > 25`: `a n ≥ 2`. -/
def H1 : Prop := ∀ n : ℕ, 25 < n → Even n → 2 ≤ a n

/-- Odd `n > 25`: `a n ≥ 2`. -/
def H2 : Prop := ∀ n : ℕ, 25 < n → Odd n → 2 ≤ a n

/-- Every `n ≤ 25` is checked by direct computation. -/
theorem small : ∀ n ≤ 25, 1 ≤ n → (3 < n → 0 < a n) ∧ (a n = 1 ↔ n ∈ ([4, 5, 17] : List ℕ)) := by decide +kernel

/-- Both conjuncts hold for `n ≤ 25` by computation; for `n > 25` they follow from `a n ≥ 2`, which
is split by parity into `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a239330.main := by
  intro h1 h2
  have two : ∀ n : ℕ, 25 < n → 2 ≤ a n := fun n hn => by
    rcases Nat.even_or_odd n with he | ho
    · exact h1 n hn he
    · exact h2 n hn ho
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rcases (show n ≤ 25 ∨ 25 < n by omega) with hs | hl
    · exact (small n hs (by omega)).1 hn
    · have := two n hl
      omega
  · rcases (show n ≤ 25 ∨ 25 < n by omega) with hs | hl
    · exact (small n hs hn).2
    · have := two n hl
      constructor
      · intro h
        omega
      · intro hmem
        simp at hmem
        omega

end OMA.R_oeis_a239330_R1
