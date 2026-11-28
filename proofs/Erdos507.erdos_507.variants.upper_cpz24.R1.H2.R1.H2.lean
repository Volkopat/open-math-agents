import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1
import Mathlib

/-!
Diagonal argument. For `ε = 1 / (k + 1)` pick `C_k` and a threshold `N_k`; for `n ≥ max(C_k, 1)^(k+1)`
we have `C_k n^(1/(k+1)) ≤ n^(2/(k+1))`. With an increasing sequence of thresholds `M k`, let
`k(n)` be the largest `k` with `M k ≤ n` and `e n = 2 / (k(n) + 1)`, which tends to `0`.
-/
open Filter Topology

namespace OMA.Diag507

theorem diag (W : ℕ → ℝ → Prop) (hmono : ∀ n, ∀ ⦃a b : ℝ⦄, a ≤ b → W n a → W n b)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n in atTop, W n (C * (n : ℝ) ^ ε)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop, W n ((n : ℝ) ^ e n) := by
  classical
  choose C hC using fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity)
  choose N hN using fun k => Filter.eventually_atTop.mp (hC k)
  let T : ℕ → ℕ := fun k => ⌈(max (C k) 1) ^ (k + 1)⌉₊
  obtain ⟨M, hM0, hMs⟩ : ∃ M : ℕ → ℕ, M 0 = max (N 0) (T 0) ∧
      ∀ k, M (k + 1) = max (max (N (k + 1)) (T (k + 1))) (M k + 1) :=
    ⟨fun k => Nat.rec (motive := fun _ => ℕ) (max (N 0) (T 0))
      (fun k m => max (max (N (k + 1)) (T (k + 1))) (m + 1)) k, rfl, fun _ => rfl⟩
  have hMN : ∀ k, N k ≤ M k ∧ T k ≤ M k := by
    intro k; cases k with
    | zero => rw [hM0]; omega
    | succ k => rw [hMs]; omega
  have hMk : ∀ k, k ≤ M k := by
    intro k; induction k with
    | zero => omega
    | succ k ih => rw [hMs]; omega
  let kk : ℕ → ℕ := fun n : ℕ => Nat.findGreatest (fun k : ℕ => M k ≤ n) n
  have hkk : ∀ n, M 0 ≤ n → M (kk n) ≤ n := by
    intro n hn
    exact Nat.findGreatest_spec (P := fun k : ℕ => M k ≤ n) (Nat.zero_le n) hn
  have hkkge : ∀ K n, M K ≤ n → K ≤ kk n := by
    intro K n hn
    exact Nat.le_findGreatest (P := fun k : ℕ => M k ≤ n) ((hMk K).trans hn) hn
  refine ⟨fun n => 2 / ((kk n : ℝ) + 1), ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / δ)
    refine ⟨M K, fun n hn => ?_⟩
    have hK' : K ≤ kk n := hkkge K n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    have hpos : (0 : ℝ) < (kk n : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hpos]
    have : (K : ℝ) ≤ kk n := by exact_mod_cast hK'
    have h2 : 2 < δ * K := by rwa [div_lt_iff₀ hδ, mul_comm] at hK
    nlinarith
  · rw [Filter.eventually_atTop]
    refine ⟨max (M 0) 1, fun n hn => ?_⟩
    set k := kk n with hkdef
    have hMn : M k ≤ n := hkk n (le_of_max_le_left hn)
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hW := hN k n ((hMN k).1.trans hMn)
    apply hmono n _ hW
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hT : ((max (C k) 1) ^ (k + 1) : ℝ) ≤ n := by
      have : T k ≤ n := (hMN k).2.trans hMn
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    have hroot : max (C k) 1 ≤ (n : ℝ) ^ (1 / ((k : ℝ) + 1)) := by
      have h0 : (0 : ℝ) ≤ max (C k) 1 := le_trans zero_le_one (le_max_right _ _)
      have := Real.rpow_le_rpow (by positivity) hT (by positivity : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul h0, Nat.cast_add, Nat.cast_one,
        mul_one_div_cancel (by positivity), Real.rpow_one] at this
    have hsplit : (n : ℝ) ^ (2 / ((k : ℝ) + 1)) =
        (n : ℝ) ^ (1 / ((k : ℝ) + 1)) * (n : ℝ) ^ (1 / ((k : ℝ) + 1)) := by
      rw [← Real.rpow_add hnpos]; ring_nf
    rw [hsplit]
    have hp : (0 : ℝ) ≤ (n : ℝ) ^ (1 / ((k : ℝ) + 1)) := by positivity
    nlinarith [le_max_left (C k) 1]

end OMA.Diag507

theorem OMA.solution : OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1.H2 :=
  fun W hmono h => OMA.Diag507.diag W hmono h
