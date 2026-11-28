import OMAStatements.S_oeis_a025273

namespace OMA.P_oeis_a025273

open PowerSeries

private noncomputable def psDeriv (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f

private lemma coeff_psDeriv (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (psDeriv f) = ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f :=
  PowerSeries.coeff_mk n _

private lemma psDeriv_sub (f g : PowerSeries ℚ) :
    psDeriv (f - g) = psDeriv f - psDeriv g := by
  ext n
  simp only [map_sub, coeff_psDeriv]
  ring

private lemma psDeriv_sq (f : PowerSeries ℚ) :
    psDeriv (f * f) = C 2 * f * psDeriv f := by
  ext n
  rw [coeff_psDeriv, PowerSeries.coeff_mul, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j (psDeriv f))]
  have hsplit :
      ((n + 1 : ℕ) : ℚ) * ∑ k ∈ Finset.range (n + 2), PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) f =
      (∑ k ∈ Finset.range (n + 2), (k : ℚ) * (PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) f)) +
      (∑ k ∈ Finset.range (n + 2), ((n + 1 - k : ℕ) : ℚ) * (PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) f)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hcast : ((n + 1 : ℕ) : ℚ) = (k : ℚ) + ((n + 1 - k : ℕ) : ℚ) := by
      exact_mod_cast (Nat.add_sub_of_le hk_le).symm
    rw [hcast]
    ring
  have hsymm :
      (∑ k ∈ Finset.range (n + 2), (k : ℚ) * (PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) f)) =
      (∑ k ∈ Finset.range (n + 2), ((n + 1 - k : ℕ) : ℚ) * (PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) f)) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_lt : k < n + 2 := Finset.mem_range.mp hk
    have h1 : n + 2 - 1 - k = n + 1 - k := by omega
    have h2 : n + 1 - (n + 1 - k) = k := by omega
    rw [h1, h2]
    ring
  have hshift :
      (∑ k ∈ Finset.range (n + 2), ((n + 1 - k : ℕ) : ℚ) * (PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) f)) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff (n - k) (psDeriv f) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_lt : k < n + 1 := Finset.mem_range.mp hk
    have hsub : n + 1 - k = n - k + 1 := by omega
    rw [hsub, coeff_psDeriv]
    ring
  rw [hsplit, hsymm, hshift]
  ring

private lemma coeff_P (n : ℕ) :
    PowerSeries.coeff n ((X : PowerSeries ℚ) - X ^ 2 + X ^ 3 - X ^ 4) =
      if n = 1 then 1 else if n = 2 then -1 else if n = 3 then 1 else if n = 4 then -1 else 0 := by
  have hX1 : (X : PowerSeries ℚ) = X ^ 1 := (pow_one X).symm
  rw [map_sub, map_add, map_sub, hX1]
  simp only [PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | n
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have h2 : n + 5 ≠ 2 := by omega
    have h3 : n + 5 ≠ 3 := by omega
    have h4 : n + 5 ≠ 4 := by omega
    simp [h2, h3, h4]

private lemma psDeriv_P :
    psDeriv ((X : PowerSeries ℚ) - X ^ 2 + X ^ 3 - X ^ 4) =
      (1 : PowerSeries ℚ) - C 2 * X ^ 1 + C 3 * X ^ 2 - C 4 * X ^ 3 := by
  ext n
  rw [coeff_psDeriv, coeff_P]
  simp only [map_sub, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | n
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have h2 : n + 4 ≠ 2 := by omega
    have h3 : n + 4 ≠ 3 := by omega
    have h2' : n + 4 + 1 ≠ 2 := by omega
    have h3' : n + 4 + 1 ≠ 3 := by omega
    have h4' : n + 4 + 1 ≠ 4 := by omega
    simp [h2, h3, h2', h3', h4']

end OMA.P_oeis_a025273

open OMA.P_oeis_a025273 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a025273.main := by
  intro a ha1 ha2 ha3 ha4 hrec n hn
  let b : ℕ → ℚ := fun k => if k = 0 then 0 else a k
  let F : PowerSeries ℚ := PowerSeries.mk b
  let P : PowerSeries ℚ := (X : PowerSeries ℚ) - X ^ 2 + X ^ 3 - X ^ 4
  have hb0 : b 0 = 0 := rfl
  have hb_pos : ∀ k : ℕ, 1 ≤ k → b k = a k := by
    intro k hk
    simp only [b, Nat.ne_of_gt hk, ↓reduceIte]
  have hF_coeff : ∀ k : ℕ, PowerSeries.coeff k F = b k := fun k => PowerSeries.coeff_mk k b
  have hEq : F - F * F = P := by
    ext k
    rw [map_sub, hF_coeff, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i F * PowerSeries.coeff j F),
      coeff_P]
    simp only [hF_coeff]
    rcases k with _ | _ | _ | _ | _ | m
    · simp [b]
    · simp [Finset.sum_range_succ, b, ha1]
    · simp [Finset.sum_range_succ, b, ha1, ha2]
    · simp [Finset.sum_range_succ, b, ha1, ha2, ha3]
    · simp [Finset.sum_range_succ, b, ha1, ha2, ha3, ha4]
    · have hk5 : 5 ≤ m + 5 := Nat.le_add_left 5 m
      have hsum_eq :
          ∑ i ∈ Finset.range (m + 5 + 1), b i * b (m + 5 - i) =
          ∑ i ∈ Finset.Icc 1 (m + 4), a i * a (m + 5 - i) := by
        rw [Finset.sum_range_succ, Nat.sub_self, hb0, mul_zero, add_zero]
        rw [Finset.sum_range_succ', hb0, zero_mul, add_zero]
        have hIcc : Finset.Icc 1 (m + 4) = (Finset.range (m + 4)).map ⟨Nat.succ, Nat.succ_injective⟩ := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
          constructor
          · intro ⟨hx1, hx2⟩
            exact ⟨x - 1, by omega, by omega⟩
          · rintro ⟨y, hy, rfl⟩
            omega
        rw [hIcc, Finset.sum_map]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt : i < m + 4 := Finset.mem_range.mp hi
        simp only [Function.Embedding.coeFn_mk]
        rw [hb_pos (i + 1) (by omega), hb_pos (m + 5 - (i + 1)) (by omega)]
      rw [hsum_eq, hb_pos (m + 5) (by omega)]
      have hrec_m := hrec (m + 5) hk5
      have hm4 : m + 5 - 1 = m + 4 := by omega
      rw [hm4] at hrec_m
      rw [← hrec_m]
      split_ifs <;> first | omega | ring
  have hD : (1 - C 2 * F) * psDeriv F = psDeriv P := by
    have h1 : psDeriv (F - F * F) = psDeriv P := congrArg psDeriv hEq
    rw [psDeriv_sub, psDeriv_sq] at h1
    calc
      (1 - C 2 * F) * psDeriv F = psDeriv F - C 2 * F * psDeriv F := by ring
      _ = psDeriv P := h1
  have hQ : (1 - C 4 * P) * psDeriv F + C 2 * psDeriv P * F = psDeriv P := by
    have hsq : (1 - C 2 * F) * (1 - C 2 * F) = 1 - C 4 * P := by
      have hC2 : (C 2 : PowerSeries ℚ) = 2 := map_ofNat (C (R := ℚ)) 2
      have hC4 : (C 4 : PowerSeries ℚ) = 4 := map_ofNat (C (R := ℚ)) 4
      rw [hC2, hC4, ← hEq]
      ring
    have hmul : (1 - C 2 * F) * ((1 - C 2 * F) * psDeriv F) = (1 - C 2 * F) * psDeriv P :=
      congrArg (fun z => (1 - C 2 * F) * z) hD
    rw [← mul_assoc, hsq] at hmul
    linear_combination hmul
  have hQ_exp :
      (1 - C 4 * P) * psDeriv F + C 2 * psDeriv P * F =
        psDeriv F
        - C 4 * (X ^ 1 * psDeriv F)
        + C 4 * (X ^ 2 * psDeriv F)
        - C 4 * (X ^ 3 * psDeriv F)
        + C 4 * (X ^ 4 * psDeriv F)
        + C 2 * F
        - C 4 * (X ^ 1 * F)
        + C 6 * (X ^ 2 * F)
        - C 8 * (X ^ 3 * F) := by
    rw [psDeriv_P]
    have hC2 : (C 2 : PowerSeries ℚ) = 2 := map_ofNat (C (R := ℚ)) 2
    have hC3 : (C 3 : PowerSeries ℚ) = 3 := map_ofNat (C (R := ℚ)) 3
    have hC4 : (C 4 : PowerSeries ℚ) = 4 := map_ofNat (C (R := ℚ)) 4
    have hC6 : (C 6 : PowerSeries ℚ) = 6 := map_ofNat (C (R := ℚ)) 6
    have hC8 : (C 8 : PowerSeries ℚ) = 8 := map_ofNat (C (R := ℚ)) 8
    dsimp only [P]
    rw [hC2, hC3, hC4, hC6, hC8]
    ring
  rw [hQ_exp, psDeriv_P] at hQ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hcoeff := congrArg (PowerSeries.coeff (m + 4)) hQ
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_psDeriv, hF_coeff] at hcoeff
  have hm1 : 1 ≤ m + 4 := by omega
  have hm2 : 2 ≤ m + 4 := by omega
  have hm3 : 3 ≤ m + 4 := by omega
  have hm4 : 4 ≤ m + 4 := by omega
  simp only [hm1, hm2, hm3, hm4, ↓reduceIte] at hcoeff
  have hne0 : m + 4 ≠ 0 := by omega
  have hne1 : m + 4 ≠ 1 := by omega
  have hne2 : m + 4 ≠ 2 := by omega
  have hne3 : m + 4 ≠ 3 := by omega
  simp only [hne0, hne1, hne2, hne3, ↓reduceIte] at hcoeff
  have hs1 : m + 4 - 1 = m + 3 := by omega
  have hs2 : m + 4 - 2 = m + 2 := by omega
  have hs3 : m + 4 - 3 = m + 1 := by omega
  have hs4 : m + 4 - 4 = m := by omega
  have ht1 : m + 5 - 1 = m + 4 := by omega
  have ht2 : m + 5 - 2 = m + 3 := by omega
  have ht3 : m + 5 - 3 = m + 2 := by omega
  have ht4 : m + 5 - 4 = m + 1 := by omega
  rw [hs1, hs2, hs3, hs4] at hcoeff
  rw [ht1, ht2, ht3, ht4]
  rw [hb_pos (m + 5) (by omega), hb_pos (m + 4) (by omega), hb_pos (m + 3) (by omega),
    hb_pos (m + 2) (by omega), hb_pos (m + 1) (by omega)] at hcoeff
  push_cast at hcoeff ⊢
  linarith
