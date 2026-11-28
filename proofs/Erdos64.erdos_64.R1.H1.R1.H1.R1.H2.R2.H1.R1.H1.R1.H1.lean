import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1
import Mathlib

-- Step Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H1.R1.H1
-- Credit: @arindale
-- The commuting branch of the non-free odd-group regular-matching step. If p and q commute then
-- p (q x) = q (p x) for every x, so the set of points where they differ is empty; the cardinality
-- hypothesis then forces card X <= 0, contradicting Nonempty X. Hence the branch is vacuous.

open SimpleGraph

theorem OMA.solution :
    OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1.H1 := by
  intro X _ _ p q hcomm hsep hcard hodd hall
  exfalso
  have hempty : {x : X | p (q x) ≠ q (p x)} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact hx (congrArg (fun e : Equiv.Perm X => e x) hcomm.eq)
  rw [hempty] at hcard
  simp only [Set.ncard_empty, mul_zero] at hcard
  have hpos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  omega
