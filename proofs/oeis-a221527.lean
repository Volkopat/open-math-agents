import OMAStatements.S_oeis_a221527

namespace OMA.S_oeis_a221527

open PowerSeries Finset



/-- The values u and v differ by at most 1 (a bad pair: they do not differ by 2 or more). -/
def bad (u v : ℕ) : Prop := u ≤ v + 1 ∧ v ≤ u + 1

instance (u v : ℕ) : Decidable (bad u v) := by unfold bad; infer_instance

theorem bad_comm (u v : ℕ) : bad u v ↔ bad v u := by unfold bad; omega

theorem good_iff (x : Fin 7 → ℕ) : good x ↔
    ¬ (bad (x 2) (x 3) ∧ bad (x 3) (x 4)) ∧
    (¬ (bad (x 1) (x 2) ∧ bad (x 2) (x 3)) ∧ ¬ bad (x 0) (x 1)) ∧
    (¬ (bad (x 3) (x 4) ∧ bad (x 4) (x 5)) ∧ ¬ bad (x 5) (x 6)) := by
  unfold good
  constructor
  · intro h
    have e0 : ¬ bad (x 0) (x 1) := by
      obtain ⟨j, hj, h1⟩ := h 0
      have hv : j.val = 1 := by simp at hj; omega
      have : j = 1 := Fin.ext hv
      subst this; unfold bad; omega
    have e6 : ¬ bad (x 5) (x 6) := by
      obtain ⟨j, hj, h1⟩ := h 6
      have hv : j.val = 5 := by simp at hj; omega
      have : j = 5 := Fin.ext hv
      subst this; unfold bad; omega
    have e2 : ¬ (bad (x 1) (x 2) ∧ bad (x 2) (x 3)) := by
      obtain ⟨j, hj, h1⟩ := h 2
      have hv : j.val = 3 ∨ j.val = 1 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 3 := Fin.ext hv
        subst this; unfold bad; omega
      · have : j = 1 := Fin.ext hv
        subst this; unfold bad; omega
    have e3 : ¬ (bad (x 2) (x 3) ∧ bad (x 3) (x 4)) := by
      obtain ⟨j, hj, h1⟩ := h 3
      have hv : j.val = 4 ∨ j.val = 2 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 4 := Fin.ext hv
        subst this; unfold bad; omega
      · have : j = 2 := Fin.ext hv
        subst this; unfold bad; omega
    have e4 : ¬ (bad (x 3) (x 4) ∧ bad (x 4) (x 5)) := by
      obtain ⟨j, hj, h1⟩ := h 4
      have hv : j.val = 5 ∨ j.val = 3 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 5 := Fin.ext hv
        subst this; unfold bad; omega
      · have : j = 3 := Fin.ext hv
        subst this; unfold bad; omega
    exact ⟨e3, ⟨e2, e0⟩, ⟨e4, e6⟩⟩
  · rintro ⟨h23, ⟨h12, h01⟩, ⟨h34, h56⟩⟩ i
    unfold bad at *
    fin_cases i
    · exact ⟨1, by decide, show (x 0 + 2 ≤ x 1 ∨ x 1 + 2 ≤ x 0) by omega⟩
    · exact ⟨0, by decide, show (x 1 + 2 ≤ x 0 ∨ x 0 + 2 ≤ x 1) by omega⟩
    · by_cases hc : x 1 ≤ x 2 + 1 ∧ x 2 ≤ x 1 + 1
      · exact ⟨3, by decide, show (x 2 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 2) by omega⟩
      · exact ⟨1, by decide, show (x 2 + 2 ≤ x 1 ∨ x 1 + 2 ≤ x 2) by omega⟩
    · by_cases hc : x 2 ≤ x 3 + 1 ∧ x 3 ≤ x 2 + 1
      · exact ⟨4, by decide, show (x 3 + 2 ≤ x 4 ∨ x 4 + 2 ≤ x 3) by omega⟩
      · exact ⟨2, by decide, show (x 3 + 2 ≤ x 2 ∨ x 2 + 2 ≤ x 3) by omega⟩
    · by_cases hc : x 3 ≤ x 4 + 1 ∧ x 4 ≤ x 3 + 1
      · exact ⟨5, by decide, show (x 4 + 2 ≤ x 5 ∨ x 5 + 2 ≤ x 4) by omega⟩
      · exact ⟨3, by decide, show (x 4 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 4) by omega⟩
    · exact ⟨6, by decide, show (x 5 + 2 ≤ x 6 ∨ x 6 + 2 ≤ x 5) by omega⟩
    · exact ⟨5, by decide, show (x 6 + 2 ≤ x 5 ∨ x 5 + 2 ≤ x 6) by omega⟩

/-- The tuples of a good array with values in 0..n: the middle values and the two arms. -/
def T (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  ((range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)) ×ˢ (range (n + 1) ×ˢ range (n + 1)) ×ˢ
    (range (n + 1) ×ˢ range (n + 1))).filter fun t =>
      ¬ (bad t.1.1 t.1.2.1 ∧ bad t.1.2.1 t.1.2.2) ∧
      (¬ (bad t.2.1.1 t.1.1 ∧ bad t.1.1 t.1.2.1) ∧ ¬ bad t.2.1.2 t.2.1.1) ∧
      (¬ (bad t.1.2.1 t.1.2.2 ∧ bad t.1.2.2 t.2.2.1) ∧ ¬ bad t.2.2.1 t.2.2.2)

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Fin 7 → ℕ :=
  ![t.2.1.2, t.2.1.1, t.1.1, t.1.2.1, t.1.2.2, t.2.2.1, t.2.2.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a2, a3, a4⟩, ⟨a1, a0⟩, ⟨a5, a6⟩⟩ ⟨⟨b2, b3, b4⟩, ⟨b1, b0⟩, ⟨b5, b6⟩⟩ h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  have e6 := congrFun h 6
  simp only [ψ, Matrix.cons_val] at e0 e1 e2 e3 e4 e5 e6
  subst e0 e1 e2 e3 e4 e5 e6
  rfl

theorem set_eq (n : ℕ) : {x : Fin 7 → ℕ | (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hb, hg⟩
    rw [good_iff] at hg
    refine ⟨((x 2, x 3, x 4), (x 1, x 0), (x 5, x 6)), ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 3)
    · exact Nat.lt_succ_of_le (hb 4)
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 0)
    · exact Nat.lt_succ_of_le (hb 5)
    · exact Nat.lt_succ_of_le (hb 6)
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨⟨⟨x2, x3, x4⟩, ⟨x1, x0⟩, ⟨x5, x6⟩⟩, ⟨⟨⟨h2, h3, h4⟩, ⟨h1, h0⟩, ⟨h5, h6⟩⟩, hc⟩,
      rfl⟩
    dsimp only at h0 h1 h2 h3 h4 h5 h6
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ψ] <;> omega
    · rw [good_iff]
      exact hc

theorem a_eq (n : ℕ) : a n = (T n).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injective _ ψ_inj, Set.ncard_coe_finset]

/-- The number of values in 0..n whose pair with y is not bad. -/
def f (n y : ℕ) : ℕ := ((range (n + 1)).filter fun w => ¬ bad w y).card

/-- F = the sum of f over 0..n. -/
def F (n : ℕ) : ℤ := ∑ y ∈ range (n + 1), (f n y : ℤ)

/-- D(y) = the sum of f over the bad partners of y. -/
def D (n y : ℕ) : ℤ := ∑ w ∈ range (n + 1), if bad w y then (f n w : ℤ) else 0

/-- The completions (x1, x0) of (u, v) = (x2, x3) on the left. -/
def Lf (n u v : ℕ) : ℕ :=
  ((range (n + 1) ×ˢ range (n + 1)).filter fun l => ¬ (bad l.1 u ∧ bad u v) ∧ ¬ bad l.2 l.1).card

theorem Lf_int (n u v : ℕ) : (Lf n u v : ℤ) = F n - if bad u v then D n u else 0 := by
  have hL : Lf n u v = ∑ x1 ∈ range (n + 1), if ¬ (bad x1 u ∧ bad u v) then f n x1 else 0 := by
    unfold Lf f
    rw [card_filter, sum_product]
    refine sum_congr rfl (fun x1 _ => ?_)
    by_cases h : ¬ (bad x1 u ∧ bad u v)
    · rw [if_pos h, card_filter]
      refine sum_congr rfl (fun x0 _ => ?_)
      simp only [h, not_false_eq_true, true_and]
    · rw [if_neg h]
      simp [h]
  rw [hL]
  push_cast
  unfold F D
  by_cases h : bad u v
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun x1 _ => ?_)
    by_cases h1 : bad x1 u <;> simp [h, h1]
  · rw [if_neg h, sub_zero]
    refine sum_congr rfl (fun x1 _ => ?_)
    simp [h]

/-- The completions (r1, r2) of (u, v) on the right. -/
def Rt (n u v : ℕ) : ℕ :=
  ((range (n + 1) ×ˢ range (n + 1)).filter fun r => ¬ (bad u v ∧ bad v r.1) ∧ ¬ bad r.1 r.2).card

theorem Rt_int (n u v : ℕ) : (Rt n u v : ℤ) = F n - if bad u v then D n v else 0 := by
  have hR : Rt n u v = ∑ r1 ∈ range (n + 1), if ¬ (bad u v ∧ bad v r1) then f n r1 else 0 := by
    unfold Rt f
    rw [card_filter, sum_product]
    refine sum_congr rfl (fun r1 _ => ?_)
    by_cases h : ¬ (bad u v ∧ bad v r1)
    · rw [if_pos h, card_filter]
      refine sum_congr rfl (fun r2 _ => ?_)
      simp only [h, not_false_eq_true, true_and, bad_comm r1 r2]
    · rw [if_neg h]
      simp [h]
  rw [hR]
  push_cast
  unfold F D
  by_cases h : bad u v
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun r1 _ => ?_)
    by_cases h1 : bad v r1 <;> simp [h, h1, bad_comm r1 v]
  · rw [if_neg h, sub_zero]
    refine sum_congr rfl (fun r1 _ => ?_)
    simp [h]

/-- P(z) = the sum over y of (F - [bad y z] D(y)). -/
def P (n z : ℕ) : ℤ := ∑ y ∈ range (n + 1), (F n - if bad y z then D n y else 0)

/-- Q(z) = the sum over the bad partners y of z of (F - D(y)). -/
def Q (n z : ℕ) : ℤ := ∑ y ∈ range (n + 1), if bad y z then F n - D n y else 0

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1),
    if ¬ (bad m.1 m.2.1 ∧ bad m.2.1 m.2.2) then Lf n m.1 m.2.1 * Rt n m.2.1 m.2.2 else 0 := by
  unfold T
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  by_cases hP : ¬ (bad m.1 m.2.1 ∧ bad m.2.1 m.2.2)
  · rw [if_pos hP]
    unfold Lf Rt
    rw [card_filter, card_filter, sum_mul_sum, sum_product]
    refine sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_))
    simp only [hP, true_and]
    split_ifs <;> simp_all
  · rw [if_neg hP]
    simp [hP]

theorem a_sum (n : ℕ) : (a n : ℤ) = ∑ z ∈ range (n + 1), (P n z * P n z - Q n z * Q n z) := by
  rw [a_eq, card_T]
  push_cast
  simp only [Lf_int, Rt_int]
  rw [sum_product]
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl (fun z _ => ?_)
  have hpt : ∀ y w : ℕ, (if ¬ (bad y z ∧ bad z w) then
      (F n - if bad y z then D n y else 0) * (F n - if bad z w then D n w else 0) else 0) =
      (F n - if bad y z then D n y else 0) * (F n - if bad w z then D n w else 0) -
      (if bad y z then F n - D n y else 0) * (if bad w z then F n - D n w else 0) := by
    intro y w
    have hc : bad w z ↔ bad z w := bad_comm w z
    by_cases hA : bad y z <;> by_cases hB : bad z w <;> simp [hA, hB, hc]
  simp only [hpt, sum_sub_distrib]
  rw [← sum_mul_sum, ← sum_mul_sum]
  rfl

theorem bsum (n : ℕ) (g : ℕ → ℤ) (z : ℕ) (hz : z ≤ n) :
    ∑ y ∈ range (n + 1), (if bad y z then g y else 0) =
      (if 0 < z then g (z - 1) else 0) + g z + (if z < n then g (z + 1) else 0) := by
  have h1 : ∀ y, (if bad y z then g y else 0) = (if y = z - 1 ∧ 0 < z then g y else 0) +
      (if y = z then g y else 0) + (if y = z + 1 then g y else 0) := by
    intro y
    by_cases ha : y = z + 1
    · have hb : ¬ (y = z - 1 ∧ 0 < z) := by omega
      have hb' : ¬ y = z := by omega
      have hc : bad y z := by unfold bad; omega
      rw [if_pos hc, if_neg hb, if_neg hb', if_pos ha, zero_add, zero_add]
    · by_cases hb : y = z - 1 ∧ 0 < z
      · have hb' : ¬ y = z := by omega
        have hc : bad y z := by unfold bad; omega
        rw [if_pos hc, if_pos hb, if_neg hb', if_neg ha, add_zero, add_zero]
      · by_cases hb' : y = z
        · have hc : bad y z := by unfold bad; omega
          rw [if_pos hc, if_neg hb, if_pos hb', if_neg ha, zero_add, add_zero]
        · have hc : ¬ bad y z := by unfold bad; omega
          rw [if_neg hc, if_neg hb, if_neg hb', if_neg ha, add_zero, add_zero]
  rw [sum_congr rfl (fun y _ => h1 y), sum_add_distrib, sum_add_distrib]
  congr 1
  congr 1
  · by_cases hz0 : 0 < z
    · rw [if_pos hz0]
      have : ∀ y, (if y = z - 1 ∧ 0 < z then g y else 0) = (if y = z - 1 then g y else 0) := by
        intro y
        simp only [hz0, and_true]
      rw [sum_congr rfl (fun y _ => this y), sum_ite_eq', if_pos (mem_range.2 (by omega))]
    · rw [if_neg hz0]
      refine sum_eq_zero (fun y _ => ?_)
      rw [if_neg (by omega)]
  · rw [sum_ite_eq', if_pos (mem_range.2 (by omega))]
  · rw [sum_ite_eq']
    by_cases h : z < n
    · rw [if_pos (mem_range.2 (by omega)), if_pos h]
    · rw [if_neg (by rw [mem_range]; omega), if_neg h]

theorem f_val (n y : ℕ) (hy : y ≤ n) : (f n y : ℤ) = n - (if 0 < y then 1 else 0) - (if y < n then 1 else 0) := by
  have h := bsum n (fun _ => 1) y hy
  unfold f
  rw [card_filter]
  push_cast
  have : ∀ w, (if ¬ bad w y then (1 : ℤ) else 0) = 1 - (if bad w y then 1 else 0) := by
    intro w
    by_cases hw : bad w y <;> simp [hw]
  rw [sum_congr rfl (fun w _ => this w), sum_sub_distrib, h, sum_const, card_range, nsmul_eq_mul,
    mul_one]
  push_cast
  split_ifs <;> ring

theorem F_val (n : ℕ) : F n = n ^ 2 - n := by
  unfold F
  rw [sum_congr rfl (fun y hy => f_val n y (Nat.lt_succ_iff.1 (mem_range.1 hy)))]
  have h1 : ∑ y ∈ range (n + 1), (if 0 < y then (1 : ℤ) else 0) = n := by
    rw [sum_range_succ']
    simp
  have h2 : ∑ y ∈ range (n + 1), (if y < n then (1 : ℤ) else 0) = n := by
    rw [sum_range_succ, if_neg (lt_irrefl n), add_zero,
      sum_congr rfl (fun y hy => if_pos (mem_range.1 hy))]
    simp
  simp only [sum_add_distrib, sum_sub_distrib, h1, h2, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem D_val (n y : ℕ) (hy : y ≤ n) :
    D n y = (if 0 < y then (f n (y - 1) : ℤ) else 0) + (f n y : ℤ) +
      (if y < n then (f n (y + 1) : ℤ) else 0) :=
  bsum n (fun w => (f n w : ℤ)) y hy

theorem P_val (n z : ℕ) (hz : z ≤ n) : P n z = (n + 1) * F n -
    ((if 0 < z then D n (z - 1) else 0) + D n z + (if z < n then D n (z + 1) else 0)) := by
  unfold P
  rw [sum_sub_distrib, bsum n (D n) z hz, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem Q_val (n z : ℕ) (hz : z ≤ n) : Q n z = (if 0 < z then F n - D n (z - 1) else 0) + (F n - D n z) +
    (if z < n then F n - D n (z + 1) else 0) :=
  bsum n (fun y => F n - D n y) z hz

theorem mid (m zz : ℕ) (h1 : 3 ≤ zz) (h2 : zz ≤ m + 3) :
    P (m + 6) zz * P (m + 6) zz - Q (m + 6) zz * Q (m + 6) zz = (m : ℤ) ^ 6 + 36 * (m : ℤ) ^ 5 + 511 * (m : ℤ) ^ 4 + 3732 * (m : ℤ) ^ 3 + 14968 * (m : ℤ) ^ 2 + 31512 * (m : ℤ) + 27360 := by
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 6. -/
theorem a_big (m : ℕ) : (a (m + 6) : ℤ) = ((m + 6 : ℕ) : ℤ) ^ 7 + ((m + 6 : ℕ) : ℤ) ^ 6 - 29 * ((m + 6 : ℕ) : ℤ) ^ 5 + 109 * ((m + 6 : ℕ) : ℤ) ^ 4 - 204 * ((m + 6 : ℕ) : ℤ) ^ 3 + 202 * ((m + 6 : ℕ) : ℤ) ^ 2 - 80 * ((m + 6 : ℕ) : ℤ) := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ', sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1),
      P (m + 6) (i + 1 + 1 + 1) * P (m + 6) (i + 1 + 1 + 1) - Q (m + 6) (i + 1 + 1 + 1) * Q (m + 6) (i + 1 + 1 + 1) = (m : ℤ) ^ 6 + 36 * (m : ℤ) ^ 5 + 511 * (m : ℤ) ^ 4 + 3732 * (m : ℤ) ^ 3 + 14968 * (m : ℤ) ^ 2 + 31512 * (m : ℤ) + 27360 := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  push_cast
  ring

theorem small1 : (a 1 : ℤ) = 0 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  norm_num

theorem small2 : (a 2 : ℤ) = 16 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  norm_num

theorem small3 : (a 3 : ℤ) = 768 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  norm_num

theorem small4 : (a 4 : ℤ) = 8544 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  norm_num

theorem small5 : (a 5 : ℤ) = 50400 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  norm_num

/-- The closed form for n >= 3 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 7 + (n : ℤ) ^ 6 - 29 * (n : ℤ) ^ 5 + 109 * (n : ℤ) ^ 4 - 204 * (n : ℤ) ^ 3 + 202 * (n : ℤ) ^ 2 - 80 * (n : ℤ) := by
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | h
  · rw [small3]; norm_num
  · rw [small4]; norm_num
  · rw [small5]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  simp only [ show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
    show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
    show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega,
    show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega]
  rw [ a_poly (q + 11) (by omega), a_poly (q + 10) (by omega), a_poly (q + 9) (by omega),
    a_poly (q + 8) (by omega), a_poly (q + 7) (by omega), a_poly (q + 6) (by omega),
    a_poly (q + 5) (by omega), a_poly (q + 4) (by omega), a_poly (q + 3) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 3 ≤ n) (h : (n : ℤ) ^ 7 + (n : ℤ) ^ 6 - 29 * (n : ℤ) ^ 5 + 109 * (n : ℤ) ^ 4 - 204 * (n : ℤ) ^ 3 + 202 * (n : ℤ) ^ 2 - 80 * (n : ℤ) = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^8 = 8 * X ^ 2 * (2 + 80 * X + 356 * X ^ 2 + 332 * X ^ 3 - 97 * X ^ 4 - 22 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7 - X ^ 8) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
    8 * X ^ 2 * (2 + 80 * X + 356 * X ^ 2 + 332 * X ^ 3 - 97 * X ^ 4 - 22 * X ^ 5 - 28 * X ^ 6 +
      8 * X ^ 7 - X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 8 = A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3)
      + C 70 * (A * X ^ 4) - C 56 * (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7)
      + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (8 * X ^ 2 * (2 + 80 * X + 356 * X ^ 2 + 332 * X ^ 3 - 97 * X ^ 4 - 22 * X ^ 5 -
      28 * X ^ 6 + 8 * X ^ 7 - X ^ 8) : ℤ⟦X⟧) =
      X ^ 2 * C 16 + X ^ 3 * C 640 + X ^ 4 * C 2848 + X ^ 5 * C 2656 - X ^ 6 * C 776 -
      X ^ 7 * C 176 - X ^ 8 * C 224 + X ^ 9 * C 64 - X ^ 10 * C 8 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 0 := by exact_mod_cast small1
  have v2 : a 2 = 16 := by exact_mod_cast small2
  have v3 : a 3 = 768 := by exact_mod_cast small3
  have v4 : a 4 = 8544 := by exact_mod_cast small4
  have v5 : a 5 = 50400 := by exact_mod_cast small5
  have v6 : a 6 = 205080 := val 6 _ (by norm_num) (by norm_num)
  have v7 : a 7 = 654864 := val 7 _ (by norm_num) (by norm_num)
  have v8 : a 8 = 1763328 := val 8 _ (by norm_num) (by norm_num)
  have v9 : a 9 = 4184064 := val 9 _ (by norm_num) (by norm_num)
  have v10 : a 10 = 9005400 := val 10 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [ v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [ show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
      show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
      show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega,
      show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega] at h ⊢
    simp only [ show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega,
      show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega,
      show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega,
      show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show 3 ≤ q + 11 by omega,
      show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega, show 6 ≤ q + 11 by omega,
      show 7 ≤ q + 11 by omega, show 8 ≤ q + 11 by omega, show ¬ q + 11 = 1 by omega,
      show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega, show ¬ q + 11 = 4 by omega,
      show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega, show ¬ q + 11 = 7 by omega,
      show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by omega, if_true,
      if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..24). -/
theorem controls : a 1 = 0 ∧ a 2 = 16 ∧ a 3 = 768 ∧ a 4 = 8544 ∧ a 5 = 50400 ∧ a 6 = 205080 ∧
    a 7 = 654864 ∧ a 8 = 1763328 ∧ a 9 = 4184064 ∧ a 10 = 9005400 ∧ a 11 = 17936160 ∧
    a 12 = 33537504 ∧ a 13 = 59505888 ∧ a 14 = 101012184 ∧ a 15 = 165102000 ∧ a 16 = 261162240 ∧
    a 17 = 401458944 ∧ a 18 = 601751448 ∧ a 19 = 881987904 ∧ a 20 = 1267087200 ∧ a 21 = 1787812320 ∧
    a 22 = 2481740184 ∧ a 23 = 3394333008 ∧ a 24 = 4580116224 :=
  ⟨ by exact_mod_cast small1, by exact_mod_cast small2, by exact_mod_cast small3,
    by exact_mod_cast small4, by exact_mod_cast small5, val 6 _ (by norm_num) (by norm_num),
    val 7 _ (by norm_num) (by norm_num), val 8 _ (by norm_num) (by norm_num),
    val 9 _ (by norm_num) (by norm_num), val 10 _ (by norm_num) (by norm_num),
    val 11 _ (by norm_num) (by norm_num), val 12 _ (by norm_num) (by norm_num),
    val 13 _ (by norm_num) (by norm_num), val 14 _ (by norm_num) (by norm_num),
    val 15 _ (by norm_num) (by norm_num), val 16 _ (by norm_num) (by norm_num),
    val 17 _ (by norm_num) (by norm_num), val 18 _ (by norm_num) (by norm_num),
    val 19 _ (by norm_num) (by norm_num), val 20 _ (by norm_num) (by norm_num),
    val 21 _ (by norm_num) (by norm_num), val 22 _ (by norm_num) (by norm_num),
    val 23 _ (by norm_num) (by norm_num), val 24 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      8 * X ^ 2 * (2 + 80 * X + 356 * X ^ 2 + 332 * X ^ 3 - 97 * X ^ 4 - 22 * X ^ 5 - 28 * X ^ 6 +
        8 * X ^ 7 - X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221527

theorem OMA.solution : type_of% @OMA.S_oeis_a221527.main :=
  OMA.S_oeis_a221527.conjecture
