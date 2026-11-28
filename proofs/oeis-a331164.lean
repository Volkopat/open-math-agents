import OMAStatements.S_oeis_a331164
import Mathlib

namespace OMA.FibonacciCalls331164

open OMA.S_oeis_a331164 Finset Filter Asymptotics

private theorem child_bound {m p : ℕ} (h : p ∈ children m) :
    m/2 ≤ p+1 ∧ p ≤ m/2+1 := by
  unfold children at h
  split at h
  · simp at h
  · split at h <;> simp only [mem_insert,mem_singleton] at h <;> omega

private theorem layer_bound {n d m : ℕ} (h : m ∈ layer n d) :
    n / 2^d ≤ m+3 ∧ m ≤ n / 2^d + 2 := by
  induction d generalizing m with
  | zero =>
    have eq : m=n := by simpa [layer] using h
    simp [eq]
  | succ d ih =>
    rw [layer, mem_biUnion] at h
    obtain ⟨p,hp,hm⟩ := h
    obtain ⟨lo,hi⟩ := ih hp
    obtain ⟨lc,hc⟩ := child_bound hm
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    omega

private def band (n d : ℕ) := Icc (n/2^d-3) (n/2^d+2)

private theorem expanded_bound (n : ℕ) : (expanded n).card ≤ (Nat.log 2 n + 1)*6 := by
  have sub : expanded n ⊆ (range (Nat.log 2 n+1)).biUnion (band n) := by
    intro m hm
    obtain ⟨hl,ht⟩ := mem_filter.mp hm
    obtain ⟨d,_,hd⟩ := mem_biUnion.mp hl
    obtain ⟨lo,hi⟩ := layer_bound hd
    have hp : 2^d ≤ n := by
      by_contra! h
      rw [Nat.div_eq_of_lt h] at hi
      omega
    have hn : n ≠ 0 := by
      have pos : 0 < 2^d := by positivity
      omega
    have dep := (Nat.le_log_iff_pow_le (by decide : 1 < 2) hn).mpr hp
    exact mem_biUnion.mpr ⟨d,mem_range.mpr (by omega),mem_Icc.mpr ⟨by omega,hi⟩⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _d ∈ range (Nat.log 2 n+1), 6 := by
      apply sum_le_sum
      intro d _
      rw [band,Nat.card_Icc]
      omega
    _ = _ := by simp

private theorem calls_bound (n : ℕ) : calls n ≤ 1 + (Nat.log 2 n+1)*18 := by
  have children_card (m : ℕ) : (children m).card ≤ 3 := by
    unfold children
    split
    · simp
    · split
      · exact card_le_three
      · exact card_le_two.trans (by decide)
  have h := sum_le_sum (s := expanded n) (fun m _ => children_card m)
  simp only [sum_const, smul_eq_mul] at h
  have b := expanded_bound n
  unfold calls
  omega

theorem result : (fun n : ℕ => (calls n : ℝ)) =O[atTop]
    (fun n : ℕ => Real.log (n : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨37 / Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 1 ≤ Nat.log 2 n :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : n ≠ 0)).mpr (by simpa)
  have hb := calls_bound n
  have scaled : calls n ≤ 37 * Nat.log 2 n := by omega
  have approx := Real.log2_le_logb n
  rw [Nat.log2_eq_log_two] at approx
  change ‖(calls n : ℝ)‖ ≤ 37 / Real.log 2 * ‖Real.log (n : ℝ)‖
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
  calc
    (calls n : ℝ) ≤ 37 * (Nat.log 2 n : ℝ) := by exact_mod_cast scaled
    _ ≤ 37 * Real.logb 2 n := by linarith
    _ = _ := by rw [Real.logb]; ring

end OMA.FibonacciCalls331164

theorem OMA.solution : type_of% @OMA.S_oeis_a331164.main :=
  OMA.FibonacciCalls331164.result
