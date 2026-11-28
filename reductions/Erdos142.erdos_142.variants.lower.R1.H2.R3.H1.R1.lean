import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3
import Mathlib

-- Credit: @eilamc14
namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1

open Finset Real Erdos142

/-- Above the density threshold, the ordered progression count exceeds the
maximum possible number of zero-step progressions in the whole group. -/
def H1 : Prop := ∀ k : ℕ, 4 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
  ∀ (p : ℕ) (hp : p.Prime), letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ A : Finset (ZMod p), C * p * exp (-c * log (p : ℝ) ^ ε) < A.card →
      p < (univ.filter fun u : ZMod p × ZMod p =>
        ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card

/-- Embed an interval extremizer in a prime cyclic group of comparable size
without introducing progressions of nonzero common difference. -/
def H2 : Prop := ∀ k N : ℕ, 4 ≤ k → 2 ≤ N →
  ∃ (p : ℕ) (_ : p.Prime) (A : Finset (ZMod p)), 2*N < p ∧ p ≤ 4*N ∧
    r k N = A.card ∧ ∀ a d : ZMod p, (∀ i : Fin k, a+(i.val : ZMod p)*d ∈ A) → d=0

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H1 := by
  classical
  intro count lift k hk
  obtain ⟨C,c,ε,hC,hc,hε,threshold⟩ := count k hk
  refine ⟨4*C,c,ε,by positivity,hc,hε,?_⟩
  intro N hN
  obtain ⟨p,hp,A,lo,hi,size,free⟩ := lift k N hk hN
  letI : NeZero p := ⟨hp.ne_zero⟩
  let solutions := univ.filter fun u : ZMod p × ZMod p =>
    ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A
  have sub : solutions ⊆ (univ : Finset (ZMod p)) ×ˢ {0} := by
    intro u hu
    exact mem_product.mpr ⟨mem_univ _, mem_singleton.mpr (free _ _ (mem_filter.mp hu).2)⟩
  have few : solutions.card ≤ p := by simpa [ZMod.card] using card_le_card sub
  have density := le_of_not_gt (fun h => (few.not_gt (threshold p hp A h)))
  have hN' : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (N : ℝ) ≤ p := by exact_mod_cast (show N ≤ p by omega)
  have logs := log_le_log (by positivity : 0 < (N : ℝ)) hNp
  have powers := rpow_le_rpow (log_nonneg hN') logs hε.le
  have exps : exp (-c * log (p : ℝ) ^ ε) ≤ exp (-c * log (N : ℝ) ^ ε) :=
    exp_le_exp.mpr (mul_le_mul_of_nonpos_left powers (by linarith))
  have hscale : (p : ℝ) ≤ 4*(N : ℝ) := by exact_mod_cast hi
  rw [size]
  calc
    (A.card : ℝ) ≤ C*p*exp (-c * log (p : ℝ) ^ ε) := density
    _ ≤ C*(4*N)*exp (-c * log (N : ℝ) ^ ε) := by gcongr
    _ = _ := by ring

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
