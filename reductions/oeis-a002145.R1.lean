import OMAStatements.S_oeis_a002145
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Remove the cases that admit a representation using fixed small primes. -/

namespace OMA.R_oeis_a002145_R1

open OMA.S_oeis_a002145

/-- Residue three modulo eight, after the three explicit pairs have been excluded. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 23 ≤ p → p % 8 = 3 →
    ¬ (p - 10).Prime → ¬ (p - 18).Prime → ¬ (p - 26).Prime →
    SumOfThreePrimesOneModFour p

/-- Residue seven modulo eight, with the same three exclusions. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 23 ≤ p → p % 8 = 7 →
    ¬ (p - 10).Prime → ¬ (p - 18).Prime → ¬ (p - 26).Prime →
    SumOfThreePrimesOneModFour p

lemma of_prime_remainder {p a b : ℕ}
    (hp : p % 4 = 3) (ha : a.Prime) (hb : b.Prime)
    (ha₄ : a % 4 = 1) (hb₄ : b % 4 = 1) (hc : (p - (a + b)).Prime) :
    SumOfThreePrimesOneModFour p := by
  have hpos := hc.two_le
  exact ⟨a, b, p - (a + b), ha, hb, hc, ha₄, hb₄, by omega, by omega⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002145.main := by
  intro hThree hSeven n hn
  let P : ℕ → Prop := fun p => p.Prime ∧ p % 4 = 3
  have hInf : (Set.ofPred P).Infinite := by
    simpa [P, Set.ofPred, Nat.ModEq] using
      (Nat.infinite_setOfPred_prime_and_modEq (q := 4) (a := 3) (by decide) (by decide))
  let p := Nat.nth P n
  have hmem : p.Prime ∧ p % 4 = 3 := Nat.nth_mem_of_infinite hInf n
  have hCount : Nat.count (fun p => p.Prime ∧ p % 4 = 3) 23 = 4 := by decide +kernel
  have hSize : 23 ≤ p := (Nat.count_le_iff_le_nth hInf).mp (by simpa [P, hCount] using hn)
  change SumOfThreePrimesOneModFour p
  by_cases h10 : (p - 10).Prime
  · exact of_prime_remainder (a := 5) (b := 5) hmem.2 (by decide) (by decide)
      (by decide) (by decide) h10
  by_cases h18 : (p - 18).Prime
  · exact of_prime_remainder (a := 5) (b := 13) hmem.2 (by decide) (by decide)
      (by decide) (by decide) h18
  by_cases h26 : (p - 26).Prime
  · exact of_prime_remainder (a := 13) (b := 13) hmem.2 (by decide) (by decide)
      (by decide) (by decide) h26
  have hmod := hmem.2
  rcases (show p % 8 = 3 ∨ p % 8 = 7 by omega) with hp | hp
  · exact hThree p hmem.1 hSize hp h10 h18 h26
  · exact hSeven p hmem.1 hSize hp h10 h18 h26

end OMA.R_oeis_a002145_R1
