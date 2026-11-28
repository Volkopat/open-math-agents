import OMAStatements.S_oeis_a199944

namespace OMA.P_oeis_a199944

open Finset OMA.S_oeis_a199944

lemma card_Icc_int (u v : ℤ) (h : u ≤ v + 1) : ((Icc u v).card : ℤ) = v + 1 - u := by
  rw [Int.card_Icc]; omega

lemma sum_symm (g : ℤ → ℤ) (m : ℕ) :
    ∑ k ∈ Icc (-(m : ℤ)) m, g k = g 0 + ∑ j ∈ range m, (g (j + 1) + g (-(j + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert ((m : ℤ) + 1) (insert (-((m : ℤ) + 1)) (Icc (-(m : ℤ)) m)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hs, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih, sum_range_succ]
    ring

/-- inner count over `x2` -/
lemma inner (n : ℕ) (x0 x1 : ℤ) (_h0 : x0 ∈ Icc (-(n : ℤ)) n) (h1 : x1 ∈ Icc (-(n : ℤ)) n) :
    ((((Icc (-(n : ℤ)) n).filter fun x2 => x0 ≠ 0 ∧ x1 ≠ 0 ∧ x2 ≠ 0 ∧ x1 - x0 ≠ 0 ∧
        x2 - x1 ≠ 0 ∧ x2 - 2 * x1 + x0 ≠ 0).card : ℕ) : ℤ) =
      (if x0 ≠ 0 ∧ x1 ≠ 0 ∧ x1 ≠ x0 then (2 * n - 1 : ℤ) else 0) -
        (if x0 ≠ 0 ∧ x1 ≠ 0 ∧ x1 ≠ x0 ∧ 2 * x1 - x0 ∈ Icc (-(n : ℤ)) n ∧ 2 * x1 - x0 ≠ 0
          then 1 else 0) := by
  simp only [mem_Icc] at h1
  by_cases h : x0 ≠ 0 ∧ x1 ≠ 0 ∧ x1 ≠ x0
  · have hT : ((Icc (-(n : ℤ)) n).card : ℤ) = 2 * n + 1 := by
      rw [card_Icc_int _ _ (by omega)]; ring
    have he : ((Icc (-(n : ℤ)) n).filter fun x2 => x0 ≠ 0 ∧ x1 ≠ 0 ∧ x2 ≠ 0 ∧ x1 - x0 ≠ 0 ∧
        x2 - x1 ≠ 0 ∧ x2 - 2 * x1 + x0 ≠ 0) =
        (((Icc (-(n : ℤ)) n).erase 0).erase x1).erase (2 * x1 - x0) := by
      ext x; simp only [mem_filter, mem_erase, mem_Icc]; omega
    rw [he]
    have c1 : (((Icc (-(n : ℤ)) n).erase 0).card : ℤ) = 2 * n := by
      have h0m : (0 : ℤ) ∈ Icc (-(n : ℤ)) n := by simp only [mem_Icc]; omega
      have h' : ((((Icc (-(n : ℤ)) n).erase 0).card : ℕ) : ℤ) + 1 = 2 * n + 1 := by
        rw [← hT]; exact_mod_cast card_erase_add_one h0m
      linarith
    have c2 : ((((Icc (-(n : ℤ)) n).erase 0).erase x1).card : ℤ) = 2 * n - 1 := by
      have : x1 ∈ (Icc (-(n : ℤ)) n).erase 0 := by simp only [mem_erase, mem_Icc]; omega
      rw [← c1, ← card_erase_add_one this]; push_cast; ring
    by_cases hm : 2 * x1 - x0 ∈ Icc (-(n : ℤ)) n ∧ 2 * x1 - x0 ≠ 0
    · have : 2 * x1 - x0 ∈ ((Icc (-(n : ℤ)) n).erase 0).erase x1 := by
        simp only [mem_erase, mem_Icc] at hm ⊢; omega
      rw [← c2, ← card_erase_add_one this, if_pos h, if_pos ⟨h.1, h.2.1, h.2.2, hm⟩]
      push_cast; ring
    · have : 2 * x1 - x0 ∉ ((Icc (-(n : ℤ)) n).erase 0).erase x1 := by
        simp only [mem_erase, mem_Icc] at hm ⊢; omega
      rw [erase_eq_of_notMem this, c2, if_pos h,
        if_neg (fun h' => hm ⟨h'.2.2.2.1, h'.2.2.2.2⟩)]
      ring
  · have he : ((Icc (-(n : ℤ)) n).filter fun x2 => x0 ≠ 0 ∧ x1 ≠ 0 ∧ x2 ≠ 0 ∧ x1 - x0 ≠ 0 ∧
        x2 - x1 ≠ 0 ∧ x2 - 2 * x1 + x0 ≠ 0) = ∅ := by
      rw [filter_eq_empty_iff]; intro x _; omega
    rw [he, if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩)]
    simp

lemma G (u v k : ℤ) (hk : k ≠ 0) (hu : u ≤ k) (hv : k ≤ v) :
    (((Icc u v).filter fun x => x ≠ 0 ∧ x ≠ k ∧ x ≠ 2 * k).card : ℤ) =
      v - u - (if u ≤ 0 ∧ 0 ≤ v then 1 else 0) - (if u ≤ 2 * k ∧ 2 * k ≤ v then 1 else 0) := by
  have he : ((Icc u v).filter fun x => x ≠ 0 ∧ x ≠ k ∧ x ≠ 2 * k) =
      (((Icc u v).erase k).erase 0).erase (2 * k) := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc]; omega
  rw [he]
  have c0 : (((Icc u v).erase k).card : ℤ) = v - u := by
    have h' : ((((Icc u v).erase k).card : ℕ) : ℤ) + 1 = v + 1 - u := by
      rw [← card_Icc_int u v (by omega)]
      exact_mod_cast card_erase_add_one (by simp only [mem_Icc]; omega)
    linarith
  have c1 : ((((Icc u v).erase k).erase 0).card : ℤ) =
      v - u - (if u ≤ 0 ∧ 0 ≤ v then 1 else 0) := by
    by_cases h : u ≤ 0 ∧ 0 ≤ v
    · have h' : (((((Icc u v).erase k).erase 0).card : ℕ) : ℤ) + 1 = v - u := by
        rw [← c0]
        exact_mod_cast card_erase_add_one (by simp only [mem_erase, mem_Icc]; omega)
      rw [if_pos h]; linarith
    · rw [erase_eq_of_notMem (by simp only [mem_erase, mem_Icc]; omega), c0, if_neg h]; ring
  by_cases h : u ≤ 2 * k ∧ 2 * k ≤ v
  · have h' : ((((((Icc u v).erase k).erase 0).erase (2 * k)).card : ℕ) : ℤ) + 1 =
        v - u - (if u ≤ 0 ∧ 0 ≤ v then 1 else 0) := by
      rw [← c1]
      exact_mod_cast card_erase_add_one (by simp only [mem_erase, mem_Icc]; omega)
    rw [if_pos h]; linarith
  · rw [erase_eq_of_notMem (by simp only [mem_erase, mem_Icc]; omega), c1, if_neg h]; ring

/-- the number of `x0` completing a nonconstant progression with middle term `k` -/
def g (n : ℕ) (k : ℤ) : ℤ :=
  if k = 0 then 0 else if 0 < k then 2 * n - 2 * k - (if 2 * k ≤ n then 2 else 0)
  else 2 * n + 2 * k - (if -2 * k ≤ n then 2 else 0)

lemma rk (n : ℕ) (k : ℤ) (hk : k ∈ Icc (-(n : ℤ)) n) :
    (((Icc (-(n : ℤ)) n).filter fun x0 => x0 ≠ 0 ∧ k ≠ 0 ∧ k ≠ x0 ∧
        2 * k - x0 ∈ Icc (-(n : ℤ)) n ∧ 2 * k - x0 ≠ 0).card : ℤ) = g n k := by
  simp only [mem_Icc] at hk
  unfold g
  by_cases h0 : k = 0
  · rw [if_pos h0, filter_eq_empty_iff.mpr (fun x _ => by omega)]; simp
  rw [if_neg h0]
  by_cases hp : 0 < k
  · have he : ((Icc (-(n : ℤ)) n).filter fun x0 => x0 ≠ 0 ∧ k ≠ 0 ∧ k ≠ x0 ∧
        2 * k - x0 ∈ Icc (-(n : ℤ)) n ∧ 2 * k - x0 ≠ 0) =
        (Icc (2 * k - n) n).filter fun x => x ≠ 0 ∧ x ≠ k ∧ x ≠ 2 * k := by
      ext x; simp only [mem_filter, mem_Icc]; omega
    rw [he, G _ _ _ h0 (by omega) (by omega), if_pos hp]
    by_cases h2 : 2 * k ≤ n
    · rw [if_pos (by omega), if_pos (by omega), if_pos h2]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg h2]; ring
  · have he : ((Icc (-(n : ℤ)) n).filter fun x0 => x0 ≠ 0 ∧ k ≠ 0 ∧ k ≠ x0 ∧
        2 * k - x0 ∈ Icc (-(n : ℤ)) n ∧ 2 * k - x0 ≠ 0) =
        (Icc (-(n : ℤ)) (2 * k + n)).filter fun x => x ≠ 0 ∧ x ≠ k ∧ x ≠ 2 * k := by
      ext x; simp only [mem_filter, mem_Icc]; omega
    rw [he, G _ _ _ h0 (by omega) (by omega), if_neg hp]
    by_cases h2 : -2 * k ≤ n
    · rw [if_pos (by omega), if_pos (by omega), if_pos h2]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg h2]; ring

lemma S1 (n m : ℕ) : ∑ j ∈ range m, (2 * (n : ℤ) - 2 * ((j : ℤ) + 1)) =
    2 * n * m - m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

lemma S2 (n m : ℕ) : ∑ j ∈ range m, (if 2 * ((j : ℤ) + 1) ≤ n then (2 : ℤ) else 0) =
    2 * ((min m (n / 2) : ℕ) : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs with h <;> omega

lemma R (n : ℕ) : ∑ k ∈ Icc (-(n : ℤ)) n, g n k = 2 * n ^ 2 - 4 * n + 2 * ((n % 2 : ℕ) : ℤ) := by
  rw [sum_symm]
  have hg : ∀ j ∈ range n, g n ((j : ℤ) + 1) + g n (-((j : ℤ) + 1)) =
      2 * (2 * (n : ℤ) - 2 * ((j : ℤ) + 1)) -
        2 * (if 2 * ((j : ℤ) + 1) ≤ n then (2 : ℤ) else 0) := by
    intro j _
    unfold g
    have a1 : ¬ ((j : ℤ) + 1 = 0) := by omega
    have a2 : (0 : ℤ) < (j : ℤ) + 1 := by omega
    have a3 : ¬ (-((j : ℤ) + 1) = 0) := by omega
    have a4 : ¬ ((0 : ℤ) < -((j : ℤ) + 1)) := by omega
    rw [if_neg a1, if_pos a2, if_neg a3, if_neg a4]
    split_ifs <;> omega
  rw [sum_congr rfl hg, sum_sub_distrib, ← mul_sum, ← mul_sum, S1, S2]
  have h0 : g n 0 = 0 := by unfold g; simp
  have : min n (n / 2) = n / 2 := by omega
  rw [this, h0]
  have h2 : ((n / 2 : ℕ) : ℤ) * 2 = n - ((n % 2 : ℕ) : ℤ) := by omega
  linear_combination (-2 : ℤ) * h2

lemma A (n : ℕ) : ∑ x0 ∈ Icc (-(n : ℤ)) n, ∑ x1 ∈ Icc (-(n : ℤ)) n,
    (if x0 ≠ 0 ∧ x1 ≠ 0 ∧ x1 ≠ x0 then (2 * n - 1 : ℤ) else 0) =
      2 * n * (2 * n - 1) * (2 * n - 1) := by
  have hT : ((Icc (-(n : ℤ)) n).card : ℤ) = 2 * n + 1 := by
    rw [card_Icc_int _ _ (by omega)]; ring
  have c1 : ((((Icc (-(n : ℤ)) n).erase 0).card : ℕ) : ℤ) + 1 = 2 * n + 1 := by
    rw [← hT]; exact_mod_cast card_erase_add_one (by simp only [mem_Icc]; omega)
  have inner1 : ∀ x0 ∈ Icc (-(n : ℤ)) n, ∑ x1 ∈ Icc (-(n : ℤ)) n,
      (if x0 ≠ 0 ∧ x1 ≠ 0 ∧ x1 ≠ x0 then (2 * n - 1 : ℤ) else 0) =
      if x0 ≠ 0 then (2 * n - 1 : ℤ) * (2 * n - 1) else 0 := by
    intro x0 hx0
    simp only [mem_Icc] at hx0
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    by_cases h : x0 ≠ 0
    · have he : (Icc (-(n : ℤ)) n).filter (fun x1 => x0 ≠ 0 ∧ x1 ≠ 0 ∧ x1 ≠ x0) =
          ((Icc (-(n : ℤ)) n).erase 0).erase x0 := by
        ext x; simp only [mem_filter, mem_erase, mem_Icc]; omega
      have c2 : (((((Icc (-(n : ℤ)) n).erase 0).erase x0).card : ℕ) : ℤ) + 1 =
          (((Icc (-(n : ℤ)) n).erase 0).card : ℕ) := by
        exact_mod_cast card_erase_add_one (by simp only [mem_erase, mem_Icc]; omega)
      rw [he, if_pos h]
      have : (((((Icc (-(n : ℤ)) n).erase 0).erase x0).card : ℕ) : ℤ) = 2 * n - 1 := by
        linarith
      rw [this]
    · rw [filter_eq_empty_iff.mpr (fun x _ => by omega), if_neg h]; simp
  rw [sum_congr rfl inner1, ← sum_filter, sum_const, nsmul_eq_mul]
  have he : (Icc (-(n : ℤ)) n).filter (fun x0 => x0 ≠ 0) = (Icc (-(n : ℤ)) n).erase 0 := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc]; omega
  rw [he]
  have : ((((Icc (-(n : ℤ)) n).erase 0).card : ℕ) : ℤ) = 2 * n := by linarith
  rw [this]; ring

lemma closed (n : ℕ) :
    (a n : ℤ) = 8 * n ^ 3 - 10 * n ^ 2 + 6 * n - 2 * ((n % 2 : ℕ) : ℤ) := by
  have h1 : (a n : ℤ) = ∑ x0 ∈ Icc (-(n : ℤ)) n, ∑ x1 ∈ Icc (-(n : ℤ)) n,
      ((((Icc (-(n : ℤ)) n).filter fun x2 => x0 ≠ 0 ∧ x1 ≠ 0 ∧ x2 ≠ 0 ∧ x1 - x0 ≠ 0 ∧
        x2 - x1 ≠ 0 ∧ x2 - 2 * x1 + x0 ≠ 0).card : ℕ) : ℤ) := by
    unfold a
    rw [card_filter, sum_product]
    push_cast
    refine sum_congr rfl fun x0 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun x1 _ => ?_
    rw [card_filter]; push_cast; rfl
  rw [h1, sum_congr rfl fun x0 h0 => sum_congr rfl fun x1 h1 => inner n x0 x1 h0 h1]
  simp only [sum_sub_distrib]
  rw [A, sum_comm]
  have hB : ∀ k ∈ Icc (-(n : ℤ)) n, ∑ x0 ∈ Icc (-(n : ℤ)) n,
      (if x0 ≠ 0 ∧ k ≠ 0 ∧ k ≠ x0 ∧ 2 * k - x0 ∈ Icc (-(n : ℤ)) n ∧ 2 * k - x0 ≠ 0
        then (1 : ℤ) else 0) = g n k := by
    intro k hk
    rw [sum_boole]; exact rk n k hk
  rw [sum_congr rfl hB, R]
  ring

lemma closed' (n : ℕ) : (a n : ℤ) = 8 * n ^ 3 - 10 * n ^ 2 + 6 * n - 1 + (-1) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [closed, Nat.even_iff.mp h, h.neg_one_pow]; push_cast; ring
  · rw [closed, Nat.odd_iff.mp h, h.neg_one_pow]; push_cast; ring

end OMA.P_oeis_a199944

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a199944.main := by
  refine ⟨?_, ?_, ?_⟩
  · have key : ((1 - X) ^ 4 * (1 + X) : PowerSeries ℤ) *
        mk (fun n => (OMA.S_oeis_a199944.a n : ℤ)) =
        mk (fun n => (OMA.S_oeis_a199944.a n : ℤ)) -
          (3 : ℤ) • (X ^ 1 * mk (fun n => (OMA.S_oeis_a199944.a n : ℤ))) +
          (2 : ℤ) • (X ^ 2 * mk (fun n => (OMA.S_oeis_a199944.a n : ℤ))) +
          (2 : ℤ) • (X ^ 3 * mk (fun n => (OMA.S_oeis_a199944.a n : ℤ))) -
          (3 : ℤ) • (X ^ 4 * mk (fun n => (OMA.S_oeis_a199944.a n : ℤ))) +
          X ^ 5 * mk (fun n => (OMA.S_oeis_a199944.a n : ℤ)) := by
      simp only [zsmul_eq_mul]; push_cast; ring
    have key2 : (2 * X * (1 + 15 * X + 19 * X ^ 2 + 13 * X ^ 3) : PowerSeries ℤ) =
        (2 : ℤ) • X ^ 1 + (30 : ℤ) • X ^ 2 + (38 : ℤ) • X ^ 3 + (26 : ℤ) • X ^ 4 := by
      simp only [zsmul_eq_mul]; push_cast; ring
    have hc1 : ∀ (f : PowerSeries ℤ) (c : ℤ) (k m : ℕ),
        coeff m (c • (X ^ k * f)) = c * (if k ≤ m then coeff (m - k) f else 0) := by
      intro f c k m; rw [map_zsmul, coeff_X_pow_mul', smul_eq_mul]
    have hc2 : ∀ (c : ℤ) (k m : ℕ),
        coeff m (c • (X ^ k : PowerSeries ℤ)) = c * (if m = k then 1 else 0) := by
      intro c k m; rw [map_zsmul, coeff_X_pow, smul_eq_mul]
    rw [key, key2]
    ext m
    simp only [map_add, map_sub, hc1, hc2, coeff_X_pow_mul', coeff_mk,
      OMA.P_oeis_a199944.closed']
    rcases m with _ | _ | _ | _ | _ | m
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simp only [show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega,
        show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, if_true,
        show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega,
        show m + 5 ≠ 4 by omega, if_false,
        show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
        show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
        show m + 5 - 5 = m by omega]
      push_cast; ring
  · intro n _ he
    rw [OMA.P_oeis_a199944.closed, Nat.even_iff.mp he]; push_cast; ring
  · intro n _ ho
    rw [OMA.P_oeis_a199944.closed, Nat.odd_iff.mp ho]; push_cast; ring
