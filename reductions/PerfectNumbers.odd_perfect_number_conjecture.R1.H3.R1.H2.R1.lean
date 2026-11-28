import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H3_R1

-- Reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H3.R1.H2.R1 of step PerfectNumbers.odd_perfect_number_conjecture.R1.H3.R1.H2
-- Credit: @eltociear

/-!
# Odd perfect numbers with at least 27 distinct prime factors: the elementary range and the open rest

The parent step `H2` asks that an odd perfect number with at least `27` distinct prime factors
has least prime factor below `19`. The divisor-sum bound behind the parent reduction already
settles the range `27 ≤ ω(n) ≤ 84`: if the least prime factor is at least `19` then every prime
factor is at least `19`, so

  `σ(n) / n < ∏_{p ∣ n} p / (p - 1) ≤ ∏_{j=1}^{ω(n)} P_j / (P_j - 1)`,

where `P_j` is the `j`-th prime at least `19`; that product is `1.9981…` for `ω(n) = 84` and
first exceeds `2` at `ω(n) = 85` (`P_85 = 479`, product `2.0023…`). So within the range the
hypothesis `minFac n ≥ 19` contradicts `σ(n) = 2n`.

* `H1` (elementary): the case of `27` to `84` distinct prime factors.
* `H2`: the open part, `85` or more distinct prime factors. Any odd perfect number with least
  prime factor at least `19` automatically has at least `85` distinct prime factors, so this
  hypothesis is the residual branch of the odd perfect number problem, with the known bounds
  (Nielsen, Ochem–Rao, Goto–Ohno) all pointing the other way.
-/

namespace OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H3_R1_H2_R1

/-- Between `27` and `84` distinct prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → 27 ≤ n.primeFactors.card → n.primeFactors.card ≤ 84 →
    Nat.minFac n < 19

/-- The open part: `85` or more distinct prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → 85 ≤ n.primeFactors.card → Nat.minFac n < 19

theorem main : H1 → H2 → OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H3_R1.H2 := by
  intro h1 h2 n hperf hodd hc
  by_cases h : n.primeFactors.card ≤ 84
  · exact h1 n hperf hodd hc h
  · exact h2 n hperf hodd (by omega)

end OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H3_R1_H2_R1
-- ci: re-run check-proof
