import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3

open Finset Real

/-- The cyclic extremal bound for sets with no nonconstant progression. -/
def H1 : Prop := ∀ k : ℕ, 4 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
  ∀ (p : ℕ) (hp : p.Prime), letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ B : Finset (ZMod p),
      (∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ B) → d = 0) →
      (B.card : ℝ) ≤ C * p * exp (-c * log (p : ℝ) ^ ε)

/-- Extract a progression-free subset using the full ordered progression count. -/
def H2 : Prop := ∀ (p : ℕ) (hp : p.Prime), letI : NeZero p := ⟨hp.ne_zero⟩
  ∀ k : ℕ, 2 ≤ k → ∀ A : Finset (ZMod p), ∃ B ⊆ A,
    (∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ B) → d = 0) ∧
    A.card ^ 2 ≤ B.card * (univ.filter fun u : ZMod p × ZMod p =>
      ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card

theorem main : H1 → H2 →
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H1 := by
  classical
  intro extremal extract k hk
  obtain ⟨C, c, ε, hC, hc, hε, bound⟩ := extremal k hk
  refine ⟨sqrt C, c / 2, ε, sqrt_pos.mpr hC, by positivity, hε, ?_⟩
  intro p hp
  let _ : NeZero p := ⟨hp.ne_zero⟩
  intro A hdense
  by_contra! hfew
  obtain ⟨B, _, hfree, hcount⟩ := extract p hp k (by omega) A
  have hnat : A.card ^ 2 ≤ B.card * p := hcount.trans (Nat.mul_le_mul_left _ hfew)
  have hreal : (A.card : ℝ) ^ 2 ≤ (B.card : ℝ) * (p : ℝ) := by exact_mod_cast hnat
  let t := exp (-(c / 2) * log (p : ℝ) ^ ε)
  have hsq : exp (-c * log (p : ℝ) ^ ε) = t ^ 2 := by
    dsimp [t]
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hB := bound p hp B hfree
  rw [hsq] at hB
  have hupper : (A.card : ℝ) ^ 2 ≤ (sqrt C * (p : ℝ) * t) ^ 2 := calc
    _ ≤ (B.card : ℝ) * (p : ℝ) := hreal
    _ ≤ (C * p * t ^ 2) * p := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg p)
    _ = _ := by rw [mul_pow, mul_pow, sq_sqrt hC.le]; ring
  change sqrt C * (p : ℝ) * t < (A.card : ℝ) at hdense
  have ht : 0 < t := exp_pos _
  have hpos : 0 ≤ sqrt C * (p : ℝ) * t := by positivity
  nlinarith only [hupper, mul_self_lt_mul_self hpos hdense]

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3
