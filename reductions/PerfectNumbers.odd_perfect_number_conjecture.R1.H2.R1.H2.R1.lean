import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1

-- Reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1.H2.R1
-- of step PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1.H2
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers not divisible by 3: exactly six prime factors, and the open rest

The parent step concerns odd perfect numbers with at least six distinct prime factors whose least
prime factor is one of `5, 7, 11, 13, 17`; in particular they are not divisible by `3`.

* `H1` (classical, Sylvester 1888 with seven instead of eight): an odd perfect number not
  divisible by `3` has at least seven distinct prime factors, because its prime factors are
  coprime to `6` and `(5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2`. So the case of exactly six
  prime factors does not occur.
* `H2`: seven or more distinct prime factors, which stays open.
-/

namespace OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1_H2_R1

/-- Exactly six distinct prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card = 6 →
    Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ)

/-- The open part: seven or more distinct prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → 7 ≤ n.primeFactors.card →
    Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ)

theorem main : H1 → H2 →
    OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1.H2 := by
  intro h1 h2 n hperf hodd hc
  by_cases h6 : n.primeFactors.card = 6
  · exact h1 n hperf hodd h6
  · exact h2 n hperf hodd (by omega)

end OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1_H2_R1
