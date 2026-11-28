import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3.R1

Credit: @aroth01.

The step is: for unitary perfect numbers `n = 2 ^ a * 5 ^ 2 * (simple odd primes)` with `4 ∣ a` (and conditions on
the 2-adic valuation of `a`), `a` is bounded. This reduction drops every condition on `a` and splits on which
simple prime `q` has `3 ∣ q + 1`.

Background. `13 ∣ 1 + 5 ^ 2` and `7 ∣ 13 + 1` are simple primes. If `3` is a simple prime it divides exactly one
`q + 1` with `q` a simple prime, and the small candidates for `q` are `11`, `23` and `47`
(`12 = 4 * 3`, `24 = 8 * 3`, `48 = 16 * 3`). An exact search (the "frontier" search of the proofs of steps
`...H4.R1.H2.R1.H1` and `...H1.R1.H2`) closes each of the four cases below; it is too long for one file, which
is the reason for this split:
* `H1`: `11 ∣ n`,
* `H2`: `23 ∣ n`,
* `H3`: `47 ∣ n`,
* `H4`: none of `11`, `23`, `47` divides `n`.
Each hypothesis keeps only `n.factorization 5 = 2` from the step: no condition on `a` is needed.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1

-- H1: 11 divides n.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    11 ∣ n → padicValNat 2 n ≤ A

-- H2: 23 divides n.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    23 ∣ n → padicValNat 2 n ≤ A

-- H3: 47 divides n.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    47 ∣ n → padicValNat 2 n ≤ A

-- H4: none of 11, 23, 47 divides n.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    ¬ 11 ∣ n → ¬ 23 ∣ n → ¬ 47 ∣ n → padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max (max A1 A2) (max A3 A4), fun n h hS he _ _ _ _ => ?_⟩
  by_cases c1 : 11 ∣ n
  · exact (h1 n h hS he c1).trans (le_max_of_le_left (le_max_left _ _))
  by_cases c2 : 23 ∣ n
  · exact (h2 n h hS he c2).trans (le_max_of_le_left (le_max_right _ _))
  by_cases c3 : 47 ∣ n
  · exact (h3 n h hS he c3).trans (le_max_of_le_right (le_max_left _ _))
  · exact (h4 n h hS he c1 c2 c3).trans (le_max_of_le_right (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R1
