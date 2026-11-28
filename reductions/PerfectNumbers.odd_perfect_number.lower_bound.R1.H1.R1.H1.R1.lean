import OMAReductions.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1

/-! Divisor and exponent constraints on odd perfect numbers coprime to 105. -/

namespace OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105

def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105 →
    10^1238 < (∏ p ∈ n.primeFactors, p^(if p ≤ 23815 then min (n.factorization p)
      (if p = 17 then 24 else if p = 19 then 38 else 42) else n.factorization p)) → (n.factorization 11 ≤ 148 ∧ n.factorization 13 ≤ 154 ∧ n.factorization 17 ≤ 124 ∧
      n.factorization 19 ≤ 132 ∧ n.factorization 23 ≤ 120) → ¬ 11^6 * 13^4 * 17^2 * 19^4 * 23^4 ∣ n

def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105 →
    10^1238 < (∏ p ∈ n.primeFactors, p^(if p ≤ 23815 then min (n.factorization p)
      (if p = 17 then 24 else if p = 19 then 38 else 42) else n.factorization p)) ∧ (n.factorization 11 ≤ 148 ∧ n.factorization 13 ≤ 154 ∧ n.factorization 17 ≤ 124 ∧
      n.factorization 19 ≤ 132 ∧ n.factorization 23 ≤ 120) ∧ 11^6 * 13^4 * 17^2 * 19^4 * 23^4 ∣ n

theorem main : H1 → H2 → H3 → OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1.H1 := by
  intro small exclude force n ho hn hs
  have hc := small n ho hn hs
  obtain ⟨lower, bounds, divisibility⟩ := force n ho hn hs hc
  exact (exclude n ho hn hs hc lower bounds divisibility).elim

end OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1_H1_R1
