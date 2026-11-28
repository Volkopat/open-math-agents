import OMAReductions.R_Erdos1140_erdos_1140_R1_H1_R1_H2_R1
import Mathlib

/-!
# Polynomial obstructions to class number two

The two inputs specialize Proposition 2.4 and the character table in §4 of
Byeon and Lee, *Class number 2 problem for certain real quadratic fields of
Richaud-Degert type*. Outside U₁₇₅, the local square tests use 5 and 7.
Inside U₁₇₅ the compatible rows force ±11 or ±19 modulo 61, or ±4 modulo
1861. Squaring removes the sign. The proper divisors below are verified here.
-/

namespace OMA.R_Erdos1140_erdos_1140_R1_H1_R1_H2_R1_H1_R1

/-- The necessary direction of the prime-values criterion, restricted to the
arguments needed for the residue obstructions. -/
def H1 : Prop :=
  ∀ (n t : ℕ), n.Prime → t.Prime → Odd t → 2 * n = t ^ 2 + 1 → 3045 < t →
    ∀ (K : Type) [Field K] [NumberField K] (s : K),
      s ^ 2 = ((t ^ 2 + 1 : ℕ) : K) → Algebra.adjoin ℚ ({s} : Set K) = ⊤ →
      NumberField.classNumber K = 2 → ∀ j : ℕ, j ≤ 339 → (n - 2 * j ^ 2).Prime

/-- Local alternatives outside U₁₇₅ and the surviving character-table
congruences inside U₁₇₅, expressed as residues of the square. -/
def H2 : Prop :=
  ∀ (n t : ℕ), n.Prime → t.Prime → Odd t → 2 * n = t ^ 2 + 1 → 3045 < t →
    ∀ (K : Type) [Field K] [NumberField K] (s : K),
      s ^ 2 = ((t ^ 2 + 1 : ℕ) : K) → Algebra.adjoin ℚ ({s} : Set K) = ⊤ →
      NumberField.classNumber K = 2 →
      t ^ 2 % 5 = 0 ∨ t ^ 2 % 5 = 4 ∨ t ^ 2 % 7 = 0 ∨ t ^ 2 % 7 = 1 ∨
      t ^ 2 % 61 = 60 ∨ t ^ 2 % 61 = 56 ∨ t ^ 2 % 1861 = 16

theorem main : H1 → H2 → OMA.R_Erdos1140_erdos_1140_R1_H1_R1_H2_R1.H1 := by
  intro criterion residues n t hn ht hodd hshape hlarge K _ _ s hsq hgen hclass
  have primes := criterion n t hn ht hodd hshape hlarge K s hsq hgen hclass
  have hmin : 3046 ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have exclude (p j : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hpmax : p ≤ 1861)
      (hj : j ≤ 339) (hres : Nat.ModEq p (4 * j ^ 2) (t ^ 2 + 1)) : False := by
    have hjsq : j ^ 2 ≤ 339 ^ 2 := Nat.pow_le_pow_left hj 2
    have hlt : p < n - 2 * j ^ 2 := by omega
    rw [← hshape] at hres
    have hdiv := hres.dvd'
    have heq : 2 * n - 4 * j ^ 2 = 2 * (n - 2 * j ^ 2) := by omega
    rw [heq] at hdiv
    have hd := (hp.dvd_mul.mp hdiv).resolve_left (fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega)
    rcases (Nat.dvd_prime (primes j hj)).mp hd with hone | hself <;> omega
  rcases residues n t hn ht hodd hshape hlarge K s hsq hgen hclass with
    h | h | h | h | h | h | h
  · apply exclude 5 2 (by decide) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]
  · apply exclude 5 0 (by decide) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]
  · apply exclude 7 3 (by decide) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]
  · apply exclude 7 2 (by decide) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]
  · apply exclude 61 0 (by decide) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]
  · apply exclude 61 11 (by decide) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]
  · apply exclude 1861 339 (by norm_num) (by decide) (by decide) (by decide)
    simp [Nat.ModEq, Nat.add_mod, h]

end OMA.R_Erdos1140_erdos_1140_R1_H1_R1_H2_R1_H1_R1
