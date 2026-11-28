import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H1.R1.H1.R1

Credit: @aroth01.

The step is: for unitary perfect numbers `n = 2 ^ a * 3 ^ 5 * (simple odd primes)` with `a` odd (and sieve
conditions on `a`), `a` is bounded. This reduction keeps only `a` odd and splits on whether the primes
`367`, `5503` and `5503` divide `n`:
* `H1`: `367 ∣ n` and `5503 ∣ n`,
* `H2`: `367 ∣ n` and not `5503 ∣ n`,
* `H3`: not `367 ∣ n` and `5503 ∣ n`,
* `H4`: not `367 ∣ n` and not `5503 ∣ n`.

Why these primes. An exact search (the "frontier" search of the proofs of steps `...H4.R1.H2.R1.H1` and
`...H2.R1.H1.R1.H2`, run by the kernel in the proofs of the sub-steps of `...H2.R1.H1.R1.H3.R1`) closes the
whole case `3 ^ 5`, `a` odd, in about 290000 steps; that is too long for one file. The three primes cut the search
into four parts of comparable length; each hypothesis is then one file.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H1_R1

-- H1: 367 divides n, 5503 divides n.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) → n.factorization 3 = 5 →
    padicValNat 2 n % 2 = 1 →
    367 ∣ n → 5503 ∣ n → padicValNat 2 n ≤ A

-- H2: 367 divides n, 5503 does not divide n.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) → n.factorization 3 = 5 →
    padicValNat 2 n % 2 = 1 →
    367 ∣ n → ¬ 5503 ∣ n → padicValNat 2 n ≤ A

-- H3: 367 does not divide n, 5503 divides n.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) → n.factorization 3 = 5 →
    padicValNat 2 n % 2 = 1 →
    ¬ 367 ∣ n → 5503 ∣ n → padicValNat 2 n ≤ A

-- H4: 367 does not divide n, 5503 does not divide n.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) → n.factorization 3 = 5 →
    padicValNat 2 n % 2 = 1 →
    ¬ 367 ∣ n → ¬ 5503 ∣ n → padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max (max A1 A2) (max A3 A4), fun n h hS he _ hodd _ _ _ => ?_⟩
  by_cases c1 : 367 ∣ n
  · by_cases c2 : 5503 ∣ n
    · exact (h1 n h hS he hodd c1 c2).trans (le_max_of_le_left (le_max_left _ _))
    · exact (h2 n h hS he hodd c1 c2).trans (le_max_of_le_left (le_max_right _ _))
  · by_cases c3 : 5503 ∣ n
    · exact (h3 n h hS he hodd c1 c3).trans (le_max_of_le_right (le_max_left _ _))
    · exact (h4 n h hS he hodd c1 c3).trans (le_max_of_le_right (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H1_R1
