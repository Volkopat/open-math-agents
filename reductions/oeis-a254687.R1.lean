import OMAStatements.S_oeis_a254687

-- Reduction oeis-a254687.R1 of A254687: Number of decompositions of 2n into sums of two primes p1 < p2 such that p2-p1-1 is also a prime.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a254687_R1

open OMA.S_oeis_a254687

/-- Even `n > 150`: `a n ≠ 0`. -/
def H1 : Prop := ∀ n : ℕ, 150 < n → Even n → 0 < a n

/-- Odd `n > 150`: `a n ≠ 0`. -/
def H2 : Prop := ∀ n : ℕ, 150 < n → Odd n → 0 < a n

/-- Every `n ≤ 150` is checked by direct computation. -/
theorem small : ∀ n ≤ 150, 1 ≤ n → (a n = 0 ↔ n ∈ ({1, 2, 3, 4, 6, 18, 79} : Finset ℕ)) := by
  decide +kernel

/-- All `n ≤ 150`, which include every exception, are settled by computation; `n > 150` is split
by parity. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a254687.main := by
  intro h1 h2 n hn
  rcases (show n ≤ 150 ∨ 150 < n by omega) with hs | hl
  · exact small n hs hn
  · have hpos : 0 < a n := by
      rcases Nat.even_or_odd n with he | ho
      · exact h1 n hl he
      · exact h2 n hl ho
    constructor
    · intro h
      omega
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega

end OMA.R_oeis_a254687_R1
