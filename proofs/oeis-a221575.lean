import OMAStatements.S_oeis_a221575

namespace OMA.S_oeis_a221575

open PowerSeries Finset



/-- The values u and v differ by exactly 1 (a bad pair: they differ by 1). -/
def bad (u v : ℕ) : Prop := u = v + 1 ∨ v = u + 1

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
    · exact ⟨1, by decide, show x 0 ≠ x 1 + 1 ∧ x 1 ≠ x 0 + 1 by omega⟩
    · exact ⟨0, by decide, show x 1 ≠ x 0 + 1 ∧ x 0 ≠ x 1 + 1 by omega⟩
    · by_cases hc : x 1 = x 2 + 1 ∨ x 2 = x 1 + 1
      · exact ⟨3, by decide, show x 2 ≠ x 3 + 1 ∧ x 3 ≠ x 2 + 1 by omega⟩
      · exact ⟨1, by decide, show x 2 ≠ x 1 + 1 ∧ x 1 ≠ x 2 + 1 by omega⟩
    · exact ⟨4, by decide, show x 3 ≠ x 4 + 1 ∧ x 4 ≠ x 3 + 1 by omega⟩
    · exact ⟨3, by decide, show x 4 ≠ x 3 + 1 ∧ x 3 ≠ x 4 + 1 by omega⟩

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

theorem bsum (n : ℕ) (g : ℕ → ℤ) (z : ℕ) (hz : z ≤ n) :
    ∑ y ∈ range (n + 1), (if bad y z then g y else 0) =
      (if 0 < z then g (z - 1) else 0) + (if z < n then g (z + 1) else 0) := by
  have h1 : ∀ y, (if bad y z then g y else 0) =
      (if y = z - 1 ∧ 0 < z then g y else 0) + (if y = z + 1 then g y else 0) := by
    intro y
    by_cases ha : y = z + 1
    · have hb : ¬ (y = z - 1 ∧ 0 < z) := by omega
      have hc : bad y z := by unfold bad; omega
      rw [if_pos hc, if_neg hb, if_pos ha, zero_add]
    · by_cases hb : y = z - 1 ∧ 0 < z
      · have hc : bad y z := by unfold bad; omega
        rw [if_pos hc, if_pos hb, if_neg ha, add_zero]
      · have hc : ¬ bad y z := by unfold bad; omega
        rw [if_neg hc, if_neg hb, if_neg ha, add_zero]
  rw [sum_congr rfl (fun y _ => h1 y), sum_add_distrib]
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
  · rw [sum_ite_eq']
    by_cases h : z < n
    · rw [if_pos (mem_range.2 (by omega)), if_pos h]
    · rw [if_neg (by rw [mem_range]; omega), if_neg h]

theorem f_val (n y : ℕ) (hy : y ≤ n) : (f n y : ℤ) = n + 1 - (if 0 < y then 1 else 0) - (if y < n then 1 else 0) := by
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

theorem F_val (n : ℕ) : F n = n ^ 2 + 1 := by
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
    D n y = (if 0 < y then (f n (y - 1) : ℤ) else 0) + (if y < n then (f n (y + 1) : ℤ) else 0) :=
  bsum n (fun w => (f n w : ℤ)) y hy

theorem mid (m zz : ℕ) (h1 : 2 ≤ zz) (h2 : zz ≤ m + 2) :
    F (m + 4) * F (m + 4) - D (m + 4) zz * D (m + 4) zz = (m : ℤ) ^ 4 + 16 * (m : ℤ) ^ 3 + 94 * (m : ℤ) ^ 2 + 248 * (m : ℤ) + 253 := by
  simp (disch := omega) only [D_val, f_val, F_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 4. -/
theorem a_big (m : ℕ) : (a (m + 4) : ℤ) = ((m + 4 : ℕ) : ℤ) ^ 5 + ((m + 4 : ℕ) : ℤ) ^ 4 - 2 * ((m + 4 : ℕ) : ℤ) ^ 3 + 12 * ((m + 4 : ℕ) : ℤ) ^ 2 - 15 * ((m + 4 : ℕ) : ℤ) + 9 := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1),
      F (m + 4) * F (m + 4) - D (m + 4) (i + 1 + 1) * D (m + 4) (i + 1 + 1) = (m : ℤ) ^ 4 + 16 * (m : ℤ) ^ 3 + 94 * (m : ℤ) ^ 2 + 248 * (m : ℤ) + 253 := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [D_val, f_val, F_val, if_pos, if_neg]
  push_cast
  ring

theorem small1 : (a 1 : ℤ) = 6 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, if_pos, if_neg]
  norm_num

theorem small2 : (a 2 : ℤ) = 57 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, if_pos, if_neg]
  norm_num

theorem small3 : (a 3 : ℤ) = 342 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, if_pos, if_neg]
  norm_num

/-- The closed form for n >= 3 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 5 + (n : ℤ) ^ 4 - 2 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 - 15 * (n : ℤ) + 9 := by
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | h
  · rw [small3]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  simp only [ show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega,
    show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega,
    show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega]
  rw [ a_poly (q + 9) (by omega), a_poly (q + 8) (by omega), a_poly (q + 7) (by omega),
    a_poly (q + 6) (by omega), a_poly (q + 5) (by omega), a_poly (q + 4) (by omega),
    a_poly (q + 3) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 3 ≤ n) (h : (n : ℤ) ^ 5 + (n : ℤ) ^ 4 - 2 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 - 15 * (n : ℤ) + 9 = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^6 = X * (6 + 21 * X + 90 * X ^ 2 - 24 * X ^ 3 + 56 * X ^ 4 - 39 * X ^ 5 + 12 * X ^ 6 - 2 * X ^ 7) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
    X * (6 + 21 * X + 90 * X ^ 2 - 24 * X ^ 3 + 56 * X ^ 4 - 39 * X ^ 5 + 12 * X ^ 6 -
      2 * X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 = A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3)
      + C 15 * (A * X ^ 4) - C 6 * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (6 + 21 * X + 90 * X ^ 2 - 24 * X ^ 3 + 56 * X ^ 4 - 39 * X ^ 5 + 12 * X ^ 6 -
      2 * X ^ 7) : ℤ⟦X⟧) =
      X ^ 1 * C 6 + X ^ 2 * C 21 + X ^ 3 * C 90 - X ^ 4 * C 24 + X ^ 5 * C 56 - X ^ 6 * C 39 +
      X ^ 7 * C 12 - X ^ 8 * C 2 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 6 := by exact_mod_cast small1
  have v2 : a 2 = 57 := by exact_mod_cast small2
  have v3 : a 3 = 342 := by exact_mod_cast small3
  have v4 : a 4 = 1293 := val 4 _ (by norm_num) (by norm_num)
  have v5 : a 5 = 3734 := val 5 _ (by norm_num) (by norm_num)
  have v6 : a 6 = 8991 := val 6 _ (by norm_num) (by norm_num)
  have v7 : a 7 = 19014 := val 7 _ (by norm_num) (by norm_num)
  have v8 : a 8 = 36497 := val 8 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [ v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (q + 9) (by omega)
    simp only [ show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega,
      show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega,
      show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega] at h ⊢
    simp only [ show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega,
      show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega,
      show ¬ q + 3 = 0 by omega, show 1 ≤ q + 9 by omega, show 2 ≤ q + 9 by omega,
      show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega,
      show 6 ≤ q + 9 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega,
      show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega,
      show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true,
      if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..30). -/
theorem controls : a 1 = 6 ∧ a 2 = 57 ∧ a 3 = 342 ∧ a 4 = 1293 ∧ a 5 = 3734 ∧ a 6 = 8991 ∧
    a 7 = 19014 ∧ a 8 = 36497 ∧ a 9 = 64998 ∧ a 10 = 109059 ∧ a 11 = 174326 ∧ a 12 = 267669 ∧
    a 13 = 397302 ∧ a 14 = 572903 ∧ a 15 = 805734 ∧ a 16 = 1108761 ∧ a 17 = 1496774 ∧
    a 18 = 1986507 ∧ a 19 = 2596758 ∧ a 20 = 3348509 ∧ a 21 = 4265046 ∧ a 22 = 5372079 ∧
    a 23 = 6697862 ∧ a 24 = 8273313 ∧ a 25 = 10132134 ∧ a 26 = 12310931 ∧ a 27 = 14849334 ∧
    a 28 = 17790117 ∧ a 29 = 21179318 ∧ a 30 = 25066359 :=
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
    val 30 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (6 + 21 * X + 90 * X ^ 2 - 24 * X ^ 3 + 56 * X ^ 4 - 39 * X ^ 5 + 12 * X ^ 6 -
        2 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221575

theorem OMA.solution : type_of% @OMA.S_oeis_a221575.main :=
  OMA.S_oeis_a221575.conjecture
