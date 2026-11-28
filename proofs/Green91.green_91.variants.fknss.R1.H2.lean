import OMAReductions.R_Green91_green_91_variants_fknss_R1
import Mathlib

-- Step Green91.green_91.variants.fknss.R1.H2: hypothesis H2 of reduction Green91.green_91.variants.fknss.R1
-- Credit: @ivillar

/-! Choose a threshold for the `k`th sequence at tolerance `1/k`. At time `n`,
use the largest index whose threshold and index are both at most `n`. -/

open Filter in
theorem OMA.solution : OMA.R_Green91_green_91_variants_fknss_R1.H2 := by
  unfold OMA.R_Green91_green_91_variants_fknss_R1.H2
  intro P hP
  choose N hN using fun k => eventually_atTop.mp
    ((ENNReal.tendsto_nhds ENNReal.one_ne_top).mp (hP k) ((k : ENNReal)⁻¹)
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k)))
  let M (k : ℕ) := N k + k
  let kk (n : ℕ) := Nat.findGreatest (fun k => M k ≤ n) n
  have hkk_ge {K n : ℕ} (h : M K ≤ n) : K ≤ kk n :=
    Nat.le_findGreatest ((Nat.le_add_left K (N K)).trans h) h
  refine ⟨kk, ?_, ?_⟩
  · rw [tendsto_atTop_atTop]
    exact fun K => ⟨M K, fun _ hn => hkk_ge hn⟩
  · rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
    intro ε hε
    obtain ⟨K, hK⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    filter_upwards [eventually_ge_atTop (M K)] with n hn
    have hKn : K ≤ n := (Nat.le_add_left K (N K)).trans hn
    have hk : M (kk n) ≤ n :=
      Nat.findGreatest_spec (P := fun k => M k ≤ n) hKn hn
    have hin := hN (kk n) n ((Nat.le_add_right _ _).trans hk)
    have hεle : ((kk n : ENNReal))⁻¹ ≤ ε :=
      (ENNReal.inv_le_inv.mpr (by exact_mod_cast hkk_ge hn)).trans hK.le
    exact ⟨(tsub_le_tsub_left hεle 1).trans hin.1, hin.2.trans (add_le_add_right hεle 1)⟩
