import OMAReductions.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2

/-! From local multiplicative blocks to the 48 fixed bands.
The remaining inputs are local sieve estimates corresponding to equation
(19) of Erdős, Graham, Ivić and Pomerance, On the number of divisors of n!.
A ceiling over the logarithmic width gives the exact additive allowance. -/

namespace OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2_H1_R1

open Finset Real Filter
open scoped Classical

private theorem log_cover {α : Type*} [DecidableEq α] (S : Finset α) (w : α → ℝ)
    {a b L C : ℝ} (ab : a ≤ b) (Lpos : 0 < L) (Cnonneg : 0 ≤ C)
    (estimate : ∀ s : ℝ, a * L ≤ s → s ≤ b * L →
      ((S.filter (fun x ↦ s < w x ∧ w x ≤ s + 1)).card : ℝ) ≤ C) :
    ((S.filter (fun x ↦ a * L < w x ∧ w x ≤ b * L)).card : ℝ) ≤
      ((b - a) * L + 1) * C := by
  classical
  let m := ⌈(b - a) * L⌉₊
  let blocks (k : ℕ) := S.filter fun x ↦ a * L + k < w x ∧ w x ≤ a * L + k + 1
  have hcover : S.filter (fun x ↦ a * L < w x ∧ w x ≤ b * L) ⊆
      (range m).biUnion blocks := by
    intro x hx
    obtain ⟨hS, hl, hu⟩ := mem_filter.mp hx
    let v := w x - a * L
    let k := ⌈v⌉₊ - 1
    have hvp : 0 < v := sub_pos.mpr hl
    have cvp : 0 < ⌈v⌉₊ := Nat.ceil_pos.mpr hvp
    have kl : k < ⌈v⌉₊ := by dsimp [k]; omega
    have kr : k + 1 = ⌈v⌉₊ := by dsimp [k]; omega
    have hl' : (k : ℝ) < v := Nat.lt_ceil.mp kl
    have hu' : v ≤ (k : ℝ) + 1 := by
      have hk : (k : ℝ) + 1 = (⌈v⌉₊ : ℝ) := by exact_mod_cast kr
      rw [hk]
      exact Nat.le_ceil _
    have hkm : k < m := kl.trans_le (Nat.ceil_mono (by dsimp [v]; nlinarith only [hu]))
    refine mem_biUnion.mpr ⟨k, mem_range.mpr hkm, mem_filter.mpr ⟨hS, ?_⟩⟩
    dsimp [v] at hl' hu'
    exact ⟨by linarith, by linarith⟩
  have hlocal (k : ℕ) (hk : k ∈ range m) : ((blocks k).card : ℝ) ≤ C := by
    have hku := Nat.lt_ceil.mp (mem_range.mp hk)
    apply estimate (a * L + k) (le_add_of_nonneg_right (Nat.cast_nonneg k))
    nlinarith only [hku]
  have hm : (m : ℝ) ≤ (b - a) * L + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (sub_nonneg.mpr ab) Lpos.le)).le
  calc
    _ ≤ (((range m).biUnion blocks).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ k ∈ range m, ((blocks k).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ range m, C := sum_le_sum hlocal
    _ = (m : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hm Cnonneg

private theorem absorb_rounding {L W T H : ℝ} (hL : 26000000 ≤ L)
    (hW : W ≤ 1) (hT : T ≤ 12) (hH : 0 ≤ H) :
    (W * L + 1) * ((T + 1/2000000) * H / L) ≤
      (W * T + 1/1000000) * H := by
  have Lpos : 0 < L := by linarith
  have h₁ : W * (1/2000000 : ℝ) ≤ 1/2000000 := by linarith
  have h₂ : (T + 1/2000000) / L ≤ 1/2000000 :=
    (div_le_iff₀ Lpos).2 (by linarith)
  calc
    _ = (W * T + W * (1/2000000) + (T + 1/2000000) / L) * H := by
      field_simp [Lpos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hH

/-- The two exponent pairs for the lower and middle logarithmic bands. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let rate (j : ℕ) : ℚ :=
    let v := edge (j+1)
    if j < 16 then (4/7)/(17/42-(5/7)*v)
    else if j < 32 then 1/(19/54-v/2) else 12
  let h := ⌊(n : ℝ) ^ (4/9 : ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n : ℝ) ^ (4/9 : ℝ) < p ∧ (p : ℝ) ≤ (n : ℝ) ^ (5/9+1/10000 : ℝ)))
  ∀ j < 32, ∀ s : ℝ, (edge j : ℝ) * log n ≤ s → s ≤ (edge (j+1) : ℝ) * log n →
    ((S.filter (fun z ↦ s < log (z.2 : ℝ) ∧ log (z.2 : ℝ) ≤ s+1)).card : ℝ) ≤
      ((rate j : ℝ) + η) * h / log n

/-- The exponent pair with constant twelve for the upper logarithmic bands. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let h := ⌊(n : ℝ) ^ (4/9 : ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n : ℝ) ^ (4/9 : ℝ) < p ∧ (p : ℝ) ≤ (n : ℝ) ^ (5/9+1/10000 : ℝ)))
  ∀ j : ℕ, 32 ≤ j → j < 48 →
    ∀ s : ℝ, (edge j : ℝ) * log n ≤ s → s ≤ (edge (j+1) : ℝ) * log n →
      ((S.filter (fun z ↦ s < log (z.2 : ℝ) ∧ log (z.2 : ℝ) ≤ s+1)).card : ℝ) ≤
        (12 + η) * h / log n

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1 := by
  intro low high
  have huge : ∀ᶠ n : ℕ in atTop, (26000000 : ℝ) ≤ log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)).eventually
        (eventually_ge_atTop _)
  filter_upwards [low (1/2000000) (by norm_num), high (1/2000000) (by norm_num),
    huge, eventually_ge_atTop (2 : ℕ)] with n hlow hhigh hL hn
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let rate (j : ℕ) : ℚ :=
    let v := edge (j+1)
    if j < 16 then (4/7)/(17/42-(5/7)*v)
    else if j < 32 then 1/(19/54-v/2) else 12
  let h := ⌊(n : ℝ) ^ (4/9 : ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n : ℝ) ^ (4/9 : ℝ) < p ∧ (p : ℝ) ≤ (n : ℝ) ^ (5/9+1/10000 : ℝ)))
  change ∀ j < 48,
    ((S.filter (fun z ↦ (n : ℝ) ^ (edge j : ℝ) < (z.2 : ℝ) ∧
      (z.2 : ℝ) ≤ (n : ℝ) ^ (edge (j+1) : ℝ))).card : ℝ) ≤
      (((edge (j+1) - edge j) * rate j + 1/1000000 : ℚ) : ℝ) * h
  intro j hj
  have numerics : edge j ≤ edge (j+1) ∧ edge (j+1) - edge j ≤ 1 ∧
      0 ≤ rate j ∧ rate j ≤ 12 := by
    interval_cases j <;> norm_num [edge, rate]
  let a : ℝ := edge j
  let b : ℝ := edge (j+1)
  let T : ℝ := rate j
  let L : ℝ := log n
  let C := (T + 1/2000000) * (h : ℝ) / L
  have hab : a ≤ b := by
    change (edge j : ℝ) ≤ (edge (j+1) : ℝ)
    exact_mod_cast numerics.1
  have hW : b - a ≤ 1 := by
    change (edge (j+1) : ℝ) - (edge j : ℝ) ≤ 1
    exact_mod_cast numerics.2.1
  have hT₀ : 0 ≤ T := by
    change (0 : ℝ) ≤ rate j
    exact_mod_cast numerics.2.2.1
  have hT : T ≤ 12 := by
    change (rate j : ℝ) ≤ 12
    exact_mod_cast numerics.2.2.2
  have Lpos : 0 < L := by dsimp [L]; linarith
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have local_bound (s : ℝ) (ha : a * L ≤ s) (hb : s ≤ b * L) :
      ((S.filter (fun z ↦ s < log (z.2 : ℝ) ∧ log (z.2 : ℝ) ≤ s + 1)).card : ℝ) ≤ C := by
    by_cases hj' : j < 32
    · exact hlow j hj' s ha hb
    · have hr : T = 12 := by dsimp [T, rate]; simp [hj', show ¬ j < 16 by omega]
      simpa [C, hr, S, h, L] using hhigh j (by omega) hj s ha hb
  have covered := log_cover S (fun z ↦ log (z.2 : ℝ)) hab Lpos
    (show 0 ≤ C by dsimp [C]; positivity) local_bound
  have sub :
      S.filter (fun z ↦ (n : ℝ) ^ a < (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ (n : ℝ) ^ b) ⊆
        S.filter (fun z ↦ a * L < log (z.2 : ℝ) ∧ log (z.2 : ℝ) ≤ b * L) := by
    intro z hz
    obtain ⟨hzS, hlo, hhi⟩ := mem_filter.mp hz
    have ap : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnp _
    have zp := ap.trans hlo
    refine mem_filter.mpr ⟨hzS, ?_, ?_⟩
    · simpa [L, Real.log_rpow hnp] using Real.log_lt_log ap hlo
    · simpa [L, Real.log_rpow hnp] using Real.log_le_log zp hhi
  calc
    _ ≤ ((S.filter (fun z ↦ a * L < log (z.2 : ℝ) ∧ log (z.2 : ℝ) ≤ b * L)).card : ℝ) :=
      by exact_mod_cast card_le_card sub
    _ ≤ ((b - a) * L + 1) * C := covered
    _ ≤ ((b - a) * T + 1/1000000) * (h : ℝ) :=
      absorb_rounding hL hW hT (Nat.cast_nonneg h)
    _ = _ := by push_cast; rfl

end OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2_H1_R1
