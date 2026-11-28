import OMAStatements.S_oeis_a221597

namespace OMA.S_oeis_a221597

open PowerSeries Finset



/-- The values u and v differ by 2 or more (a bad pair: they do not differ by 1 or less). -/
def bad (u v : ℕ) : Prop := u + 2 ≤ v ∨ v + 2 ≤ u

instance (u v : ℕ) : Decidable (bad u v) := by unfold bad; infer_instance

theorem bad_comm (u v : ℕ) : bad u v ↔ bad v u := by unfold bad; omega

theorem good_iff (x : Fin 5 → ℕ) : good x ↔
    ¬ (bad (x 1) (x 2) ∧ bad (x 2) (x 3)) ∧ ¬ bad (x 0) (x 1) ∧ ¬ bad (x 4) (x 3) := by
  unfold good
  constructor
  · intro h
    have e0 : ¬ bad (x 0) (x 1) := by
      obtain ⟨j, hj, h1⟩ := h 0
      have hv : j.val = 1 := by simp at hj; omega
      have : j = 1 := Fin.ext hv
      subst this; unfold bad; omega
    have e4 : ¬ bad (x 4) (x 3) := by
      obtain ⟨j, hj, h1⟩ := h 4
      have hv : j.val = 3 := by simp at hj; omega
      have : j = 3 := Fin.ext hv
      subst this; unfold bad; omega
    have e2 : ¬ (bad (x 1) (x 2) ∧ bad (x 2) (x 3)) := by
      obtain ⟨j, hj, h1⟩ := h 2
      have hv : j.val = 3 ∨ j.val = 1 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 3 := Fin.ext hv
        subst this; unfold bad; omega
      · have : j = 1 := Fin.ext hv
        subst this; unfold bad; omega
    exact ⟨e2, e0, e4⟩
  · rintro ⟨h12, h01, h43⟩ i
    unfold bad at *
    fin_cases i
    · exact ⟨1, by decide, show (x 0 ≤ x 1 + 1 ∧ x 1 ≤ x 0 + 1) by omega⟩
    · exact ⟨0, by decide, show (x 1 ≤ x 0 + 1 ∧ x 0 ≤ x 1 + 1) by omega⟩
    · by_cases hc : x 1 + 2 ≤ x 2 ∨ x 2 + 2 ≤ x 1
      · exact ⟨3, by decide, show (x 2 ≤ x 3 + 1 ∧ x 3 ≤ x 2 + 1) by omega⟩
      · exact ⟨1, by decide, show (x 2 ≤ x 1 + 1 ∧ x 1 ≤ x 2 + 1) by omega⟩
    · exact ⟨4, by decide, show (x 3 ≤ x 4 + 1 ∧ x 4 ≤ x 3 + 1) by omega⟩
    · exact ⟨3, by decide, show (x 4 ≤ x 3 + 1 ∧ x 3 ≤ x 4 + 1) by omega⟩

/-- The tuples of a good array with values in 0..n: the middle values and the two arms. -/
def T (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × ℕ × ℕ) :=
  ((range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)) ×ˢ range (n + 1) ×ˢ range (n + 1)).filter fun t =>
      ¬ (bad t.1.1 t.1.2.1 ∧ bad t.1.2.1 t.1.2.2) ∧ ¬ bad t.2.1 t.1.1 ∧ ¬ bad t.2.2 t.1.2.2

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ × ℕ) × ℕ × ℕ) : Fin 5 → ℕ :=
  ![t.2.1, t.1.1, t.1.2.1, t.1.2.2, t.2.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a1, a2, a3⟩, a0, a4⟩ ⟨⟨b1, b2, b3⟩, b0, b4⟩ h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  simp only [ψ, Matrix.cons_val] at e0 e1 e2 e3 e4
  subst e0 e1 e2 e3 e4
  rfl

theorem set_eq (n : ℕ) : {x : Fin 5 → ℕ | (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hb, hg⟩
    rw [good_iff] at hg
    refine ⟨((x 1, x 2, x 3), x 0, x 4), ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 3)
    · exact Nat.lt_succ_of_le (hb 0)
    · exact Nat.lt_succ_of_le (hb 4)
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨⟨⟨x1, x2, x3⟩, x0, x4⟩, ⟨⟨⟨h1, h2, h3⟩, h0, h4⟩, hc⟩, rfl⟩
    dsimp only at h0 h1 h2 h3 h4
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

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1),
    if ¬ (bad m.1 m.2.1 ∧ bad m.2.1 m.2.2) then f n m.1 * f n m.2.2 else 0 := by
  unfold T
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  by_cases hP : ¬ (bad m.1 m.2.1 ∧ bad m.2.1 m.2.2)
  · rw [if_pos hP]
    unfold f
    rw [card_filter, card_filter, sum_mul_sum, sum_product]
    refine sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_))
    simp only [hP, true_and]
    split_ifs <;> simp_all
  · rw [if_neg hP]
    simp [hP]

theorem a_sum (n : ℕ) : (a n : ℤ) = ∑ z ∈ range (n + 1), (F n * F n - D n z * D n z) := by
  rw [a_eq, card_T]
  push_cast
  rw [sum_product]
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl (fun z _ => ?_)
  have hpt : ∀ y w : ℕ, (if ¬ (bad y z ∧ bad z w) then (f n y : ℤ) * (f n w : ℤ) else 0) =
      (f n y : ℤ) * (f n w : ℤ) - (if bad y z then (f n y : ℤ) else 0) *
        (if bad w z then (f n w : ℤ) else 0) := by
    intro y w
    have hc : bad w z ↔ bad z w := bad_comm w z
    by_cases hA : bad y z <;> by_cases hB : bad z w <;> simp [hA, hB, hc]
  simp only [hpt, sum_sub_distrib]
  rw [← sum_mul_sum, ← sum_mul_sum]
  rfl

theorem csum (n : ℕ) (g : ℕ → ℤ) (z : ℕ) (hz : z ≤ n) :
    ∑ y ∈ range (n + 1), (if ¬ bad y z then g y else 0) =
      (if 0 < z then g (z - 1) else 0) + g z + (if z < n then g (z + 1) else 0) := by
  have h1 : ∀ y, (if ¬ bad y z then g y else 0) = (if y = z - 1 ∧ 0 < z then g y else 0) +
      (if y = z then g y else 0) + (if y = z + 1 then g y else 0) := by
    intro y
    by_cases ha : y = z + 1
    · have hb : ¬ (y = z - 1 ∧ 0 < z) := by omega
      have hb' : ¬ y = z := by omega
      have hc : ¬ bad y z := by unfold bad; omega
      rw [if_pos hc, if_neg hb, if_neg hb', if_pos ha, zero_add, zero_add]
    · by_cases hb : y = z - 1 ∧ 0 < z
      · have hb' : ¬ y = z := by omega
        have hc : ¬ bad y z := by unfold bad; omega
        rw [if_pos hc, if_pos hb, if_neg hb', if_neg ha, add_zero, add_zero]
      · by_cases hb' : y = z
        · have hc : ¬ bad y z := by unfold bad; omega
          rw [if_pos hc, if_neg hb, if_pos hb', if_neg ha, zero_add, add_zero]
        · have hc : bad y z := by unfold bad; omega
          rw [if_neg (not_not_intro hc), if_neg hb, if_neg hb', if_neg ha, add_zero, add_zero]
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

theorem bsum (n : ℕ) (g : ℕ → ℤ) (z : ℕ) (hz : z ≤ n) :
    ∑ y ∈ range (n + 1), (if bad y z then g y else 0) =
      (∑ y ∈ range (n + 1), g y) -
        ((if 0 < z then g (z - 1) else 0) + g z + (if z < n then g (z + 1) else 0)) := by
  rw [← csum n g z hz, ← sum_sub_distrib]
  refine sum_congr rfl (fun y _ => ?_)
  by_cases h : bad y z <;> simp [h]

theorem totb (n : ℕ) (g : ℕ → ℤ) :
    ∑ z ∈ range (n + 1), ∑ y ∈ range (n + 1), (if bad y z then g y else 0) =
      (n - 2) * (∑ y ∈ range (n + 1), g y) + g 0 + g n := by
  rw [sum_congr rfl (fun z hz => bsum n g z (Nat.lt_succ_iff.1 (mem_range.1 hz))),
    sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_add_distrib, sum_add_distrib]
  have h1 : ∑ z ∈ range (n + 1), (if 0 < z then g (z - 1) else 0) =
      (∑ y ∈ range (n + 1), g y) - g n := by
    rw [sum_range_succ', sum_range_succ, if_neg (lt_irrefl 0), add_zero]
    simp
  have h2 : ∑ z ∈ range (n + 1), (if z < n then g (z + 1) else 0) =
      (∑ y ∈ range (n + 1), g y) - g 0 := by
    rw [sum_range_succ, if_neg (lt_irrefl n), add_zero,
      sum_congr rfl (fun z hz => if_pos (mem_range.1 hz)), sum_range_succ' (fun y => g y) n]
    ring
  rw [h1, h2]
  push_cast
  ring

theorem f_val (n y : ℕ) (hy : y ≤ n) : (f n y : ℤ) = 1 + (if 0 < y then 1 else 0) + (if y < n then 1 else 0) := by
  have h := csum n (fun _ => 1) y hy
  unfold f
  rw [card_filter]
  push_cast
  rw [h]
  split_ifs <;> ring

theorem F_val (n : ℕ) : F n = 3 * n + 1 := by
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
    D n y = F n - ((if 0 < y then (f n (y - 1) : ℤ) else 0) + (f n y : ℤ) +
      (if y < n then (f n (y + 1) : ℤ) else 0)) :=
  bsum n (fun w => (f n w : ℤ)) y hy

theorem TD_val (n : ℕ) : ∑ y ∈ range (n + 1), D n y = (n - 2) * F n + f n 0 + f n n := by
  unfold D F
  exact totb n (fun w => (f n w : ℤ))

theorem mid (m zz : ℕ) (h1 : 2 ≤ zz) (h2 : zz ≤ m + 2) :
    F (m + 4) * F (m + 4) - D (m + 4) zz * D (m + 4) zz = 54 * (m : ℤ) + 153 := by
  simp (disch := omega) only [D_val, f_val, F_val, TD_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 4. -/
theorem a_big (m : ℕ) : (a (m + 4) : ℤ) = 54 * ((m + 4 : ℕ) : ℤ) ^ 2 - 69 * ((m + 4 : ℕ) : ℤ) + 63 := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1),
      F (m + 4) * F (m + 4) - D (m + 4) (i + 1 + 1) * D (m + 4) (i + 1 + 1) = 54 * (m : ℤ) + 153 := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [D_val, f_val, F_val, TD_val, if_pos, if_neg]
  push_cast
  ring

theorem small1 : (a 1 : ℤ) = 32 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, TD_val, if_pos, if_neg]
  norm_num

theorem small2 : (a 2 : ℤ) = 139 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, TD_val, if_pos, if_neg]
  norm_num

theorem small3 : (a 3 : ℤ) = 342 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, TD_val, if_pos, if_neg]
  norm_num

/-- The closed form for n >= 3 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = 54 * (n : ℤ) ^ 2 - 69 * (n : ℤ) + 63 := by
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | h
  · rw [small3]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
  simp only [ show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega,
    show q + 6 - 3 = q + 3 by omega]
  rw [ a_poly (q + 6) (by omega), a_poly (q + 5) (by omega), a_poly (q + 4) (by omega),
    a_poly (q + 3) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 3 ≤ n) (h : 54 * (n : ℤ) ^ 2 - 69 * (n : ℤ) + 63 = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^3 = X * (32 + 43 * X + 21 * X ^ 2 + 10 * X ^ 3 + 2 * X ^ 4) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
    X * (32 + 43 * X + 21 * X ^ 2 + 10 * X ^ 3 + 2 * X ^ 4) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (32 + 43 * X + 21 * X ^ 2 + 10 * X ^ 3 + 2 * X ^ 4) : ℤ⟦X⟧) =
      X ^ 1 * C 32 + X ^ 2 * C 43 + X ^ 3 * C 21 + X ^ 4 * C 10 + X ^ 5 * C 2 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 32 := by exact_mod_cast small1
  have v2 : a 2 = 139 := by exact_mod_cast small2
  have v3 : a 3 = 342 := by exact_mod_cast small3
  have v4 : a 4 = 651 := val 4 _ (by norm_num) (by norm_num)
  have v5 : a 5 = 1068 := val 5 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [ v1, v2, v3, v4, v5]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
    have h := recurrence (q + 6) (by omega)
    simp only [ show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega,
      show q + 6 - 3 = q + 3 by omega] at h ⊢
    simp only [ show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega,
      show ¬ q + 3 = 0 by omega, show 1 ≤ q + 6 by omega, show 2 ≤ q + 6 by omega,
      show 3 ≤ q + 6 by omega, show ¬ q + 6 = 1 by omega, show ¬ q + 6 = 2 by omega,
      show ¬ q + 6 = 3 by omega, show ¬ q + 6 = 4 by omega, show ¬ q + 6 = 5 by omega, if_true,
      if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..39). -/
theorem controls : a 1 = 32 ∧ a 2 = 139 ∧ a 3 = 342 ∧ a 4 = 651 ∧ a 5 = 1068 ∧ a 6 = 1593 ∧
    a 7 = 2226 ∧ a 8 = 2967 ∧ a 9 = 3816 ∧ a 10 = 4773 ∧ a 11 = 5838 ∧ a 12 = 7011 ∧ a 13 = 8292 ∧
    a 14 = 9681 ∧ a 15 = 11178 ∧ a 16 = 12783 ∧ a 17 = 14496 ∧ a 18 = 16317 ∧ a 19 = 18246 ∧
    a 20 = 20283 ∧ a 21 = 22428 ∧ a 22 = 24681 ∧ a 23 = 27042 ∧ a 24 = 29511 ∧ a 25 = 32088 ∧
    a 26 = 34773 ∧ a 27 = 37566 ∧ a 28 = 40467 ∧ a 29 = 43476 ∧ a 30 = 46593 ∧ a 31 = 49818 ∧
    a 32 = 53151 ∧ a 33 = 56592 ∧ a 34 = 60141 ∧ a 35 = 63798 ∧ a 36 = 67563 ∧ a 37 = 71436 ∧
    a 38 = 75417 ∧ a 39 = 79506 :=
  ⟨ by exact_mod_cast small1, by exact_mod_cast small2, by exact_mod_cast small3,
    val 4 _ (by norm_num) (by norm_num), val 5 _ (by norm_num) (by norm_num),
    val 6 _ (by norm_num) (by norm_num), val 7 _ (by norm_num) (by norm_num),
    val 8 _ (by norm_num) (by norm_num), val 9 _ (by norm_num) (by norm_num),
    val 10 _ (by norm_num) (by norm_num), val 11 _ (by norm_num) (by norm_num),
    val 12 _ (by norm_num) (by norm_num), val 13 _ (by norm_num) (by norm_num),
    val 14 _ (by norm_num) (by norm_num), val 15 _ (by norm_num) (by norm_num),
    val 16 _ (by norm_num) (by norm_num), val 17 _ (by norm_num) (by norm_num),
    val 18 _ (by norm_num) (by norm_num), val 19 _ (by norm_num) (by norm_num),
    val 20 _ (by norm_num) (by norm_num), val 21 _ (by norm_num) (by norm_num),
    val 22 _ (by norm_num) (by norm_num), val 23 _ (by norm_num) (by norm_num),
    val 24 _ (by norm_num) (by norm_num), val 25 _ (by norm_num) (by norm_num),
    val 26 _ (by norm_num) (by norm_num), val 27 _ (by norm_num) (by norm_num),
    val 28 _ (by norm_num) (by norm_num), val 29 _ (by norm_num) (by norm_num),
    val 30 _ (by norm_num) (by norm_num), val 31 _ (by norm_num) (by norm_num),
    val 32 _ (by norm_num) (by norm_num), val 33 _ (by norm_num) (by norm_num),
    val 34 _ (by norm_num) (by norm_num), val 35 _ (by norm_num) (by norm_num),
    val 36 _ (by norm_num) (by norm_num), val 37 _ (by norm_num) (by norm_num),
    val 38 _ (by norm_num) (by norm_num), val 39 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (32 + 43 * X + 21 * X ^ 2 + 10 * X ^ 3 + 2 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221597

theorem OMA.solution : type_of% @OMA.S_oeis_a221597.main :=
  OMA.S_oeis_a221597.conjecture
