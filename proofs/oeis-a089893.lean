import OMAStatements.S_oeis_a089893
import Mathlib

namespace A089893Aux
open OMA.S_oeis_a089893 Finset Filter Topology

lemma map_shift (s : ℕ) (L : List ℕ) :
    (L.map (· + 1)).map (fun i => Nat.fermatNumber (s + i)) =
      L.map (fun i => Nat.fermatNumber (s + 1 + i)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  show Nat.fermatNumber (s + (i + 1)) = Nat.fermatNumber (s + 1 + i)
  rw [show s + (i + 1) = s + 1 + i by omega]

lemma bp_zero (s : ℕ) : bitProduct s 0 = 1 := by simp [bitProduct]

lemma bp_two_mul (s y : ℕ) : bitProduct s (2 * y) = bitProduct (s + 1) y := by
  unfold bitProduct
  rw [Nat.bitIndices_two_mul, map_shift]

lemma bp_two_mul_add_one (s y : ℕ) :
    bitProduct s (2 * y + 1) = Nat.fermatNumber s * bitProduct (s + 1) y := by
  unfold bitProduct
  rw [Nat.bitIndices_two_mul_add_one, List.map_cons, List.prod_cons, map_shift, Nat.add_zero]

lemma bp_two_pow_mul (u : ℕ) : ∀ s x, bitProduct s (2 ^ u * x) = bitProduct (s + u) x := by
  induction u with
  | zero => intro s x; simp
  | succ u ih =>
    intro s x
    rw [show 2 ^ (u + 1) * x = 2 * (2 ^ u * x) by ring, bp_two_mul, ih,
      show s + 1 + u = s + (u + 1) by omega]

lemma bp_block (u : ℕ) : ∀ s x, bitProduct s (2 ^ u * x + (2 ^ u - 1)) =
    (∏ i ∈ range u, Nat.fermatNumber (s + i)) * bitProduct (s + u) x := by
  induction u with
  | zero => intro s x; simp
  | succ u ih =>
    intro s x
    have hpos : 1 ≤ 2 ^ u := Nat.one_le_two_pow
    have e : 2 ^ (u + 1) * x + (2 ^ (u + 1) - 1) = 2 * (2 ^ u * x + (2 ^ u - 1)) + 1 := by
      have h2 : 2 ^ (u + 1) = 2 * 2 ^ u := by ring
      rw [h2, mul_assoc]; omega
    have h1 : ∏ k ∈ range u, Nat.fermatNumber (s + (k + 1)) =
        ∏ i ∈ range u, Nat.fermatNumber (s + 1 + i) :=
      Finset.prod_congr rfl (fun i _ => by rw [show s + (i + 1) = s + 1 + i by omega])
    rw [e, bp_two_mul_add_one, ih, Finset.prod_range_succ', h1,
      show s + 1 + u = s + (u + 1) by omega, Nat.add_zero]
    ring_nf

lemma fermat_mod (s : ℕ) (hs : 1 ≤ s) : Nat.fermatNumber s % 4 = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hp : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hk : 2 ^ (t + 1) = 2 + (2 * 2 ^ t - 2) := by
    rw [pow_succ]; omega
  unfold Nat.fermatNumber
  rw [hk, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
  omega

lemma bp_mod (n : ℕ) : ∀ s, 1 ≤ s → bitProduct s n % 4 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    obtain ⟨y, hy⟩ := Nat.even_or_odd' n
    rcases hy with rfl | rfl
    · rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [bp_zero]
      · rw [bp_two_mul]; exact ih y (by omega) (s + 1) (by omega)
    · rw [bp_two_mul_add_one, Nat.mul_mod, ih y (by omega) (s + 1) (by omega), fermat_mod s hs]

lemma four_a (n : ℕ) : 4 * a n + 1 = bitProduct 1 n := by
  unfold a
  have := bp_mod n 1 le_rfl
  omega

lemma a_real (x : ℕ) : (a x : ℝ) = ((bitProduct 1 x : ℝ) - 1) / 4 := by
  have h := four_a x
  have h' : (4 * (a x : ℝ) + 1) = (bitProduct 1 x : ℝ) := by exact_mod_cast h
  linarith

lemma part1 (k : ℕ) : a (2 ^ k) = 2 ^ (2 ^ (k + 1) - 2) := by
  have hb : bitProduct 1 (2 ^ k) = Nat.fermatNumber (1 + k) := by simp [bitProduct]
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (k + 1) = m + 2 := ⟨2 ^ (k + 1) - 2, by
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega⟩
  unfold a
  rw [hb]
  unfold Nat.fermatNumber
  rw [show 1 + k = k + 1 by omega, hm, Nat.add_sub_cancel, Nat.add_sub_cancel, pow_add,
    show (2 : ℕ) ^ 2 = 4 by norm_num]
  exact Nat.mul_div_cancel _ (by norm_num)

lemma part2 (n u : ℕ) :
    (4 * (a (2 ^ (u + 1) * n + 2 ^ u) : ℝ) + 1) /
      (4 * (a (2 ^ (u + 1) * n + 2 ^ u - 1) : ℝ) + 1) =
      3 * (Nat.fermatNumber (u + 1) : ℝ) / ((Nat.fermatNumber (u + 1) : ℝ) - 2) := by
  have h1 : (4 * (a (2 ^ (u + 1) * n + 2 ^ u) : ℝ) + 1) =
      (bitProduct 1 (2 ^ (u + 1) * n + 2 ^ u) : ℝ) := by exact_mod_cast four_a _
  have h2 : (4 * (a (2 ^ (u + 1) * n + 2 ^ u - 1) : ℝ) + 1) =
      (bitProduct 1 (2 ^ (u + 1) * n + 2 ^ u - 1) : ℝ) := by exact_mod_cast four_a _
  have e1 : 2 ^ (u + 1) * n + 2 ^ u = 2 ^ u * (2 * n + 1) := by ring
  have e2 : 2 ^ (u + 1) * n + 2 ^ u - 1 = 2 ^ u * (2 * n) + (2 ^ u - 1) := by
    have hp : 1 ≤ 2 ^ u := Nat.one_le_two_pow
    have h3 : 2 ^ (u + 1) * n = 2 ^ u * (2 * n) := by ring
    omega
  have b1 : bitProduct 1 (2 ^ u * (2 * n + 1)) =
      Nat.fermatNumber (1 + u) * bitProduct (1 + u + 1) n := by
    rw [bp_two_pow_mul, bp_two_mul_add_one]
  have b2 : bitProduct 1 (2 ^ u * (2 * n) + (2 ^ u - 1)) =
      (∏ i ∈ range u, Nat.fermatNumber (1 + i)) * bitProduct (1 + u + 1) n := by
    rw [bp_block, bp_two_mul]
  have hprod : (∏ i ∈ range u, Nat.fermatNumber (1 + i)) * 3 = Nat.fermatNumber (u + 1) - 2 := by
    have h := Nat.prod_fermatNumber (u + 1)
    rw [Finset.prod_range_succ', Nat.fermatNumber_zero] at h
    rw [← h]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => by rw [add_comm])
  have hF := Nat.three_le_fermatNumber (u + 1)
  have hQ : 0 < bitProduct (1 + u + 1) n := by
    have := bp_mod n (1 + u + 1) (by omega)
    omega
  obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ, ∏ i ∈ range u, Nat.fermatNumber (1 + i) = Pi := ⟨_, rfl⟩
  rw [hPi] at b2 hprod
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, bitProduct (1 + u + 1) n = Q := ⟨_, rfl⟩
  rw [hQdef] at b1 b2 hQ
  rw [show 1 + u = u + 1 by omega] at b1
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ, Nat.fermatNumber (u + 1) = F := ⟨_, rfl⟩
  rw [hFdef] at b1 hprod hF ⊢
  rw [h1, h2, e2, e1, b1, b2]
  have hPi3 : (Pi : ℝ) * 3 = (F : ℝ) - 2 := by
    have h4 : ((Pi * 3 : ℕ) : ℝ) = ((F - 2 : ℕ) : ℝ) := by rw [hprod]
    rw [Nat.cast_sub (by omega)] at h4
    push_cast at h4
    exact h4
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hF' : (3 : ℝ) ≤ F := by exact_mod_cast hF
  have hPi' : (0 : ℝ) < Pi := by nlinarith
  push_cast
  rw [div_eq_div_iff (mul_pos hPi' hQ').ne' (by linarith : (0 : ℝ) < (F : ℝ) - 2).ne']
  rw [← hPi3]; ring

lemma fermat_ge (s : ℕ) : 2 ^ s + 1 ≤ Nat.fermatNumber s := by
  unfold Nat.fermatNumber
  have : 2 ^ s ≤ 2 ^ 2 ^ s := Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le
  omega

lemma bp_ge (n : ℕ) : ∀ s, 2 ^ s * n + 1 ≤ bitProduct s n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s
    obtain ⟨y, hy⟩ := Nat.even_or_odd' n
    rcases hy with rfl | rfl
    · rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [bp_zero]
      · have h := ih y (by omega) (s + 1)
        rw [bp_two_mul]
        have e : 2 ^ (s + 1) * y = 2 ^ s * (2 * y) := by ring
        omega
    · have h := ih y (by omega) (s + 1)
      have hf := fermat_ge s
      rw [bp_two_mul_add_one]
      have e : 2 ^ (s + 1) * y = 2 ^ s * (2 * y) := by ring
      have e2 : 2 ^ s * (2 * y + 1) = 2 ^ s * (2 * y) + 2 ^ s := by ring
      have h3 : (2 ^ s + 1) * (2 ^ s * (2 * y) + 1) ≤
          Nat.fermatNumber s * bitProduct (s + 1) y := Nat.mul_le_mul hf (by omega)
      have h4 : (2 ^ s + 1) * (2 ^ s * (2 * y) + 1) =
          2 ^ s * (2 ^ s * (2 * y) + 1) + (2 ^ s * (2 * y) + 1) := by ring
      have h5 : 2 ^ s ≤ 2 ^ s * (2 ^ s * (2 * y) + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega

lemma bp_tendsto (s : ℕ) : Tendsto (fun n : ℕ => (bitProduct s n : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have h := bp_ge n s
  have hp : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h2 : n ≤ 2 ^ s * n := Nat.le_mul_of_pos_left _ (by omega)
  exact_mod_cast (by omega : n ≤ bitProduct s n)

lemma lim_ratio (c1 c2 : ℝ) (hc2 : 0 < c2) (P : ℕ → ℝ) (hP : Tendsto P atTop atTop) :
    Tendsto (fun n => ((c1 * P n - 1) / 4) / ((c2 * P n - 1) / 4)) atTop (𝓝 (c1 / c2)) := by
  have h1 : Tendsto (fun n => (P n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hP
  have hnum : Tendsto (fun n => c1 - (P n)⁻¹) atTop (𝓝 (c1 - 0)) := tendsto_const_nhds.sub h1
  have hden : Tendsto (fun n => c2 - (P n)⁻¹) atTop (𝓝 (c2 - 0)) := tendsto_const_nhds.sub h1
  rw [sub_zero] at hnum hden
  have hdiv := hnum.div hden hc2.ne'
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [hP.eventually_gt_atTop 0] with n hn
  have hne : P n ≠ 0 := hn.ne'
  have e1 : c1 - (P n)⁻¹ = (c1 * P n - 1) / P n := by field_simp
  have e2 : c2 - (P n)⁻¹ = (c2 * P n - 1) / P n := by field_simp
  show (c1 - (P n)⁻¹) / (c2 - (P n)⁻¹) = ((c1 * P n - 1) / 4) / ((c2 * P n - 1) / 4)
  rw [div_div_div_cancel_right₀ (by norm_num : (4 : ℝ) ≠ 0), e1, e2,
    div_div_div_cancel_right₀ hne]

lemma F3 : Nat.fermatNumber 3 = 257 := by norm_num [Nat.fermatNumber]

lemma lim3 : Tendsto (fun n : ℕ => (a (2 * n + 1) : ℝ) / (a (2 * n) : ℝ)) atTop (𝓝 5) := by
  have key : (fun n : ℕ => (a (2 * n + 1) : ℝ) / (a (2 * n) : ℝ)) =
      fun n => ((5 * (bitProduct 2 n : ℝ) - 1) / 4) / ((1 * (bitProduct 2 n : ℝ) - 1) / 4) := by
    funext n
    rw [a_real, a_real, bp_two_mul_add_one, bp_two_mul]
    norm_num
  rw [key]
  have h := lim_ratio 5 1 one_pos _ (bp_tendsto 2)
  rwa [div_one] at h

lemma lim4 : Tendsto (fun n : ℕ => (a (4 * n + 2) : ℝ) / (a (4 * n + 1) : ℝ)) atTop
    (𝓝 (17 / 5)) := by
  have key : (fun n : ℕ => (a (4 * n + 2) : ℝ) / (a (4 * n + 1) : ℝ)) =
      fun n => ((17 * (bitProduct 3 n : ℝ) - 1) / 4) / ((5 * (bitProduct 3 n : ℝ) - 1) / 4) := by
    funext n
    rw [a_real, a_real, show 4 * n + 2 = 2 * (2 * n + 1) by ring,
      show 4 * n + 1 = 2 * (2 * n) + 1 by ring, bp_two_mul, bp_two_mul_add_one,
      bp_two_mul_add_one, bp_two_mul]
    norm_num
  rw [key]
  exact lim_ratio 17 5 (by norm_num) _ (bp_tendsto 3)

lemma lim5 : Tendsto (fun n : ℕ => (a (8 * n + 4) : ℝ) / (a (8 * n + 3) : ℝ)) atTop
    (𝓝 (257 / 85)) := by
  have key : (fun n : ℕ => (a (8 * n + 4) : ℝ) / (a (8 * n + 3) : ℝ)) =
      fun n => ((257 * (bitProduct 4 n : ℝ) - 1) / 4) / ((85 * (bitProduct 4 n : ℝ) - 1) / 4) := by
    funext n
    have b1 : bitProduct 1 (8 * n + 4) = 257 * bitProduct 4 n := by
      rw [show 8 * n + 4 = 2 * (2 * (2 * n + 1)) by ring, bp_two_mul, bp_two_mul,
        bp_two_mul_add_one]
      show Nat.fermatNumber 3 * bitProduct 4 n = 257 * bitProduct 4 n
      rw [F3]
    have b2 : bitProduct 1 (8 * n + 3) = 85 * bitProduct 4 n := by
      rw [show 8 * n + 3 = 2 * (2 * (2 * n) + 1) + 1 by ring, bp_two_mul_add_one,
        bp_two_mul_add_one, bp_two_mul]
      show Nat.fermatNumber 1 * (Nat.fermatNumber 2 * bitProduct 4 n) = 85 * bitProduct 4 n
      rw [Nat.fermatNumber_one, Nat.fermatNumber_two]; ring
    rw [a_real, a_real, b1, b2]
    push_cast
    rfl
  rw [key]
  exact lim_ratio 257 85 (by norm_num) _ (bp_tendsto 4)
end A089893Aux

open A089893Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a089893.main := by
  refine ⟨part1, ?_, lim3, lim4, lim5⟩
  intro n t ht
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact part2 n u
