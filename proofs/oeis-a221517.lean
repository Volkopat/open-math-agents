import OMAStatements.S_oeis_a221517

namespace OMA.S_oeis_a221517

open PowerSeries Finset



/-- The values u and v differ by at most 1 (a bad pair: they do not differ by 2 or more). -/
def bad (u v : ℕ) : Prop := u ≤ v + 1 ∧ v ≤ u + 1

instance (u v : ℕ) : Decidable (bad u v) := by unfold bad; infer_instance

theorem bad_comm (u v : ℕ) : bad u v ↔ bad v u := by unfold bad; omega

theorem good_iff (x : Fin 6 → ℕ) : good x ↔
    (¬ (bad (x 1) (x 2) ∧ bad (x 2) (x 3)) ∧ ¬ bad (x 0) (x 1)) ∧
    (¬ (bad (x 2) (x 3) ∧ bad (x 3) (x 4)) ∧ ¬ bad (x 4) (x 5)) := by
  unfold good
  constructor
  · intro h
    have e0 : ¬ bad (x 0) (x 1) := by
      obtain ⟨j, hj, h1⟩ := h 0
      have hv : j.val = 1 := by simp at hj; omega
      have : j = 1 := Fin.ext hv
      subst this; unfold bad; omega
    have e5 : ¬ bad (x 4) (x 5) := by
      obtain ⟨j, hj, h1⟩ := h 5
      have hv : j.val = 4 := by simp at hj; omega
      have : j = 4 := Fin.ext hv
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
    exact ⟨⟨e2, e0⟩, ⟨e3, e5⟩⟩
  · rintro ⟨⟨h12, h01⟩, ⟨h23, h45⟩⟩ i
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
    · exact ⟨5, by decide, show (x 4 + 2 ≤ x 5 ∨ x 5 + 2 ≤ x 4) by omega⟩
    · exact ⟨4, by decide, show (x 5 + 2 ≤ x 4 ∨ x 4 + 2 ≤ x 5) by omega⟩

/-- The tuples of a good array with values in 0..n, starting with 0: the middle values and the two arms. -/
def T (n : ℕ) : Finset ((ℕ × ℕ) × ℕ × (ℕ × ℕ)) :=
  ((range (n + 1) ×ˢ range (n + 1)) ×ˢ range (n + 1) ×ˢ (range (n + 1) ×ˢ range (n + 1))).filter fun t =>
      (¬ (bad t.2.1 t.1.1 ∧ bad t.1.1 t.1.2) ∧ ¬ bad 0 t.2.1) ∧
      (¬ (bad t.1.1 t.1.2 ∧ bad t.1.2 t.2.2.1) ∧ ¬ bad t.2.2.1 t.2.2.2)

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ) × ℕ × (ℕ × ℕ)) : Fin 6 → ℕ :=
  ![0, t.2.1, t.1.1, t.1.2, t.2.2.1, t.2.2.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a2, a3⟩, a1, ⟨a4, a5⟩⟩ ⟨⟨b2, b3⟩, b1, ⟨b4, b5⟩⟩ h
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  simp only [ψ, Matrix.cons_val] at e1 e2 e3 e4 e5
  subst e1 e2 e3 e4 e5
  rfl

theorem set_eq (n : ℕ) :
    {x : Fin 6 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨h0, hb, hg⟩
    rw [good_iff, h0] at hg
    refine ⟨((x 2, x 3), x 1, (x 4, x 5)), ⟨⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 3)
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 4)
    · exact Nat.lt_succ_of_le (hb 5)
    · funext i
      fin_cases i
      · exact h0.symm
      all_goals rfl
  · rintro ⟨⟨⟨x2, x3⟩, x1, ⟨x4, x5⟩⟩, ⟨⟨⟨h2, h3⟩, h1, ⟨h4, h5⟩⟩, hc⟩, rfl⟩
    dsimp only at h1 h2 h3 h4 h5
    refine ⟨rfl, fun i => ?_, ?_⟩
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

/-- The indicator of the values x1 whose pair with x0 = 0 is not bad. -/
def gz (y : ℕ) : ℤ := if ¬ bad 0 y then 1 else 0

/-- G = the sum of gz over 0..n. -/
def G (n : ℕ) : ℤ := ∑ y ∈ range (n + 1), gz y

/-- E(y) = the sum of gz over the bad partners of y. -/
def E (n y : ℕ) : ℤ := ∑ w ∈ range (n + 1), if bad w y then gz w else 0

/-- The completions x1 of (u, v) = (x2, x3) on the left, with x0 = 0. -/
def Lc (n u v : ℕ) : ℕ :=
  ((range (n + 1)).filter fun x1 => ¬ (bad x1 u ∧ bad u v) ∧ ¬ bad 0 x1).card

theorem Lc_int (n u v : ℕ) : (Lc n u v : ℤ) = G n - if bad u v then E n u else 0 := by
  unfold Lc G E gz
  rw [card_filter]
  push_cast
  by_cases h : bad u v
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun x1 _ => ?_)
    by_cases h1 : bad x1 u <;> by_cases h0 : bad 0 x1 <;> simp [h, h1, h0]
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

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
    Lc n m.1 m.2 * Rt n m.1 m.2 := by
  unfold T
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  unfold Lc Rt
  rw [card_filter, card_filter, sum_mul_sum, sum_product]
  refine sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_))
  split_ifs <;> simp_all

theorem a_sum (n : ℕ) : (a n : ℤ) = ∑ y ∈ range (n + 1), (G n * P n y - E n y * Q n y) := by
  rw [a_eq, card_T]
  push_cast
  simp only [Lc_int, Rt_int]
  rw [sum_product]
  refine sum_congr rfl (fun y _ => ?_)
  have hpt : ∀ z : ℕ, (G n - if bad y z then E n y else 0) * (F n - if bad y z then D n z else 0) =
      G n * (F n - if bad z y then D n z else 0) - E n y * (if bad z y then F n - D n z else 0) := by
    intro z
    have hc : bad z y ↔ bad y z := bad_comm z y
    by_cases hA : bad y z
    · simp only [hA, hc, if_true]
      ring
    · simp only [hA, hc, if_false]
      ring
  rw [sum_congr rfl (fun z _ => hpt z), sum_sub_distrib, ← mul_sum, ← mul_sum]
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

theorem gz_val (y : ℕ) : gz y = if 2 ≤ y then 1 else 0 := by
  unfold gz
  by_cases h : 2 ≤ y
  · rw [if_pos h, if_pos (show ¬ bad 0 y by unfold bad; omega)]
  · rw [if_neg h, if_neg (not_not_intro (show bad 0 y by unfold bad; omega))]

theorem G_val (n : ℕ) (hn : 1 ≤ n) : G n = n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold G
  rw [sum_range_succ', sum_range_succ']
  simp only [gz_val]
  rw [sum_congr rfl (fun i _ => if_pos (by omega))]
  simp

theorem E_val (n y : ℕ) (hy : y ≤ n) :
    E n y = (if 0 < y then gz (y - 1) else 0) + gz y + (if y < n then gz (y + 1) else 0) :=
  bsum n gz y hy

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
    G (m + 6) * P (m + 6) zz - E (m + 6) zz * Q (m + 6) zz = (m : ℤ) ^ 4 + 23 * (m : ℤ) ^ 3 + 179 * (m : ℤ) ^ 2 + 592 * (m : ℤ) + 708 := by
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 6. -/
theorem a_big (m : ℕ) : (a (m + 6) : ℤ) = ((m + 6 : ℕ) : ℤ) ^ 5 - 20 * ((m + 6 : ℕ) : ℤ) ^ 3 + 78 * ((m + 6 : ℕ) : ℤ) ^ 2 - 146 * ((m + 6 : ℕ) : ℤ) + 125 := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ', sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1),
      G (m + 6) * P (m + 6) (i + 1 + 1 + 1) - E (m + 6) (i + 1 + 1 + 1) * Q (m + 6) (i + 1 + 1 + 1) = (m : ℤ) ^ 4 + 23 * (m : ℤ) ^ 3 + 179 * (m : ℤ) ^ 2 + 592 * (m : ℤ) + 708 := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  push_cast
  ring

theorem small1 : (a 1 : ℤ) = 0 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small2 : (a 2 : ℤ) = 5 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small3 : (a 3 : ℤ) = 89 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small4 : (a 4 : ℤ) = 532 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small5 : (a 5 : ℤ) = 1970 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

/-- The closed form for n >= 5 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 5 - 20 * (n : ℤ) ^ 3 + 78 * (n : ℤ) ^ 2 - 146 * (n : ℤ) + 125 := by
  rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h
  · rw [small5]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  simp only [ show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
    show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
    show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega]
  rw [ a_poly (q + 11) (by omega), a_poly (q + 10) (by omega), a_poly (q + 9) (by omega),
    a_poly (q + 8) (by omega), a_poly (q + 7) (by omega), a_poly (q + 6) (by omega),
    a_poly (q + 5) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 5 ≤ n) (h : (n : ℤ) ^ 5 - 20 * (n : ℤ) ^ 3 + 78 * (n : ℤ) ^ 2 - 146 * (n : ℤ) + 125 = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^6 = X ^ 2 * (5 + 59 * X + 73 * X ^ 2 + 13 * X ^ 3 - 32 * X ^ 4 + 9 * X ^ 5 - 9 * X ^ 6 + 3 * X ^ 7 - X ^ 8) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
    X ^ 2 * (5 + 59 * X + 73 * X ^ 2 + 13 * X ^ 3 - 32 * X ^ 4 + 9 * X ^ 5 - 9 * X ^ 6 + 3 * X ^ 7 -
      X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 = A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3)
      + C 15 * (A * X ^ 4) - C 6 * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X ^ 2 * (5 + 59 * X + 73 * X ^ 2 + 13 * X ^ 3 - 32 * X ^ 4 + 9 * X ^ 5 - 9 * X ^ 6 +
      3 * X ^ 7 - X ^ 8) : ℤ⟦X⟧) =
      X ^ 2 * C 5 + X ^ 3 * C 59 + X ^ 4 * C 73 + X ^ 5 * C 13 - X ^ 6 * C 32 + X ^ 7 * C 9 -
      X ^ 8 * C 9 + X ^ 9 * C 3 - X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 0 := by exact_mod_cast small1
  have v2 : a 2 = 5 := by exact_mod_cast small2
  have v3 : a 3 = 89 := by exact_mod_cast small3
  have v4 : a 4 = 532 := by exact_mod_cast small4
  have v5 : a 5 = 1970 := by exact_mod_cast small5
  have v6 : a 6 = 5513 := val 6 _ (by norm_num) (by norm_num)
  have v7 : a 7 = 12872 := val 7 _ (by norm_num) (by norm_num)
  have v8 : a 8 = 26477 := val 8 _ (by norm_num) (by norm_num)
  have v9 : a 9 = 49598 := val 9 _ (by norm_num) (by norm_num)
  have v10 : a 10 = 86465 := val 10 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [ v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [ show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
      show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
      show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega] at h ⊢
    simp only [ show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega,
      show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega,
      show ¬ q + 5 = 0 by omega, show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega,
      show 3 ≤ q + 11 by omega, show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega,
      show 6 ≤ q + 11 by omega, show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega,
      show ¬ q + 11 = 3 by omega, show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega,
      show ¬ q + 11 = 6 by omega, show ¬ q + 11 = 7 by omega, show ¬ q + 11 = 8 by omega,
      show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..30). -/
theorem controls : a 1 = 0 ∧ a 2 = 5 ∧ a 3 = 89 ∧ a 4 = 532 ∧ a 5 = 1970 ∧ a 6 = 5513 ∧
    a 7 = 12872 ∧ a 8 = 26477 ∧ a 9 = 49598 ∧ a 10 = 86465 ∧ a 11 = 142388 ∧ a 12 = 223877 ∧
    a 13 = 338762 ∧ a 14 = 496313 ∧ a 15 = 707360 ∧ a 16 = 984413 ∧ a 17 = 1341782 ∧
    a 18 = 1795697 ∧ a 19 = 2364428 ∧ a 20 = 3068405 ∧ a 21 = 3930338 ∧ a 22 = 4975337 ∧
    a 23 = 6231032 ∧ a 24 = 7727693 ∧ a 25 = 9498350 ∧ a 26 = 11578913 ∧ a 27 = 14008292 ∧
    a 28 = 16828517 ∧ a 29 = 20084858 ∧ a 30 = 23825945 :=
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
    val 23 _ (by norm_num) (by norm_num), val 24 _ (by norm_num) (by norm_num),
    val 25 _ (by norm_num) (by norm_num), val 26 _ (by norm_num) (by norm_num),
    val 27 _ (by norm_num) (by norm_num), val 28 _ (by norm_num) (by norm_num),
    val 29 _ (by norm_num) (by norm_num), val 30 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X ^ 2 * (5 + 59 * X + 73 * X ^ 2 + 13 * X ^ 3 - 32 * X ^ 4 + 9 * X ^ 5 - 9 * X ^ 6 +
        3 * X ^ 7 - X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221517

theorem OMA.solution : type_of% @OMA.S_oeis_a221517.main :=
  OMA.S_oeis_a221517.conjecture
