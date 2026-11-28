import OMAStatements.S_oeis_a221516

namespace OMA.S_oeis_a221516

open PowerSeries Finset



/-- The values u and v differ by at most 1 (a bad pair: they do not differ by 2 or more). -/
def bad (u v : ℕ) : Prop := u ≤ v + 1 ∧ v ≤ u + 1

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
    · exact ⟨1, by decide, show (x 0 + 2 ≤ x 1 ∨ x 1 + 2 ≤ x 0) by omega⟩
    · exact ⟨0, by decide, show (x 1 + 2 ≤ x 0 ∨ x 0 + 2 ≤ x 1) by omega⟩
    · by_cases hc : x 1 ≤ x 2 + 1 ∧ x 2 ≤ x 1 + 1
      · exact ⟨3, by decide, show (x 2 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 2) by omega⟩
      · exact ⟨1, by decide, show (x 2 + 2 ≤ x 1 ∨ x 1 + 2 ≤ x 2) by omega⟩
    · exact ⟨4, by decide, show (x 3 + 2 ≤ x 4 ∨ x 4 + 2 ≤ x 3) by omega⟩
    · exact ⟨3, by decide, show (x 4 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 4) by omega⟩

/-- The tuples of a good array with values in 0..n, starting with 0: the middle values and the two arms. -/
def T (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × ℕ) :=
  ((range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)) ×ˢ range (n + 1)).filter fun t =>
      ¬ (bad t.1.1 t.1.2.1 ∧ bad t.1.2.1 t.1.2.2) ∧ ¬ bad 0 t.1.1 ∧ ¬ bad t.2 t.1.2.2

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ × ℕ) × ℕ) : Fin 5 → ℕ :=
  ![0, t.1.1, t.1.2.1, t.1.2.2, t.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a1, a2, a3⟩, a4⟩ ⟨⟨b1, b2, b3⟩, b4⟩ h
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  simp only [ψ, Matrix.cons_val] at e1 e2 e3 e4
  subst e1 e2 e3 e4
  rfl

theorem set_eq (n : ℕ) :
    {x : Fin 5 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨h0, hb, hg⟩
    rw [good_iff, h0] at hg
    refine ⟨((x 1, x 2, x 3), x 4), ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 3)
    · exact Nat.lt_succ_of_le (hb 4)
    · funext i
      fin_cases i
      · exact h0.symm
      all_goals rfl
  · rintro ⟨⟨⟨x1, x2, x3⟩, x4⟩, ⟨⟨⟨h1, h2, h3⟩, h4⟩, hc⟩, rfl⟩
    dsimp only at h1 h2 h3 h4
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

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1),
    if ¬ (bad m.1 m.2.1 ∧ bad m.2.1 m.2.2) ∧ ¬ bad 0 m.1 then f n m.2.2 else 0 := by
  unfold T
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  by_cases hP : ¬ (bad m.1 m.2.1 ∧ bad m.2.1 m.2.2) ∧ ¬ bad 0 m.1
  · rw [if_pos hP]
    obtain ⟨hA, hB⟩ := hP
    unfold f
    rw [card_filter]
    refine sum_congr rfl (fun r _ => ?_)
    simp only [hA, hB, not_false_eq_true, true_and]
  · rw [if_neg hP]
    refine sum_eq_zero (fun r _ => if_neg ?_)
    exact fun h => hP ⟨h.1, h.2.1⟩

theorem a_sum (n : ℕ) : (a n : ℤ) = ∑ z ∈ range (n + 1), (G n * F n - E n z * D n z) := by
  rw [a_eq, card_T]
  push_cast
  rw [sum_product]
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl (fun z _ => ?_)
  have hpt : ∀ y w : ℕ, (if ¬ (bad y z ∧ bad z w) ∧ ¬ bad 0 y then (f n w : ℤ) else 0) =
      gz y * (f n w : ℤ) - (if bad y z then gz y else 0) * (if bad w z then (f n w : ℤ) else 0) := by
    intro y w
    have hc : bad w z ↔ bad z w := bad_comm w z
    unfold gz
    by_cases hA : bad y z <;> by_cases hB : bad z w <;> by_cases h0 : bad 0 y <;> simp [hA, hB, hc, h0]
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

theorem mid (m zz : ℕ) (h1 : 3 ≤ zz) (h2 : zz ≤ m + 3) :
    G (m + 5) * F (m + 5) - E (m + 5) zz * D (m + 5) zz = (m : ℤ) ^ 3 + 13 * (m : ℤ) ^ 2 + 47 * (m : ℤ) + 53 := by
  simp (disch := omega) only [D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 5. -/
theorem a_big (m : ℕ) : (a (m + 5) : ℤ) = ((m + 5 : ℕ) : ℤ) ^ 4 - ((m + 5 : ℕ) : ℤ) ^ 3 - 10 * ((m + 5 : ℕ) : ℤ) ^ 2 + 33 * ((m + 5 : ℕ) : ℤ) - 34 := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ', sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1),
      G (m + 5) * F (m + 5) - E (m + 5) (i + 1 + 1 + 1) * D (m + 5) (i + 1 + 1 + 1) = (m : ℤ) ^ 3 + 13 * (m : ℤ) ^ 2 + 47 * (m : ℤ) + 53 := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  push_cast
  ring

theorem small1 : (a 1 : ℤ) = 0 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small2 : (a 2 : ℤ) = 3 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small3 : (a 3 : ℤ) = 30 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

theorem small4 : (a 4 : ℤ) = 130 := by
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero]
  simp (disch := omega) only [D_val, f_val, F_val, gz_val, G_val, E_val, if_pos, if_neg]
  norm_num

/-- The closed form for n >= 4 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 4 - (n : ℤ) ^ 3 - 10 * (n : ℤ) ^ 2 + 33 * (n : ℤ) - 34 := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h
  · rw [small4]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  simp only [ show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega,
    show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega,
    show q + 9 - 5 = q + 4 by omega]
  rw [ a_poly (q + 9) (by omega), a_poly (q + 8) (by omega), a_poly (q + 7) (by omega),
    a_poly (q + 6) (by omega), a_poly (q + 5) (by omega), a_poly (q + 4) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 4 ≤ n) (h : (n : ℤ) ^ 4 - (n : ℤ) ^ 3 - 10 * (n : ℤ) ^ 2 + 33 * (n : ℤ) - 34 = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^5 = X ^ 2 * (3 + 15 * X + 10 * X ^ 2 + X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 - X ^ 6) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
    X ^ 2 * (3 + 15 * X + 10 * X ^ 2 + X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 - X ^ 6) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 5 = A - C 5 * (A * X ^ 1) + C 10 * (A * X ^ 2) - C 10 * (A * X ^ 3)
      + C 5 * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]; ring
  have e2 : (X ^ 2 * (3 + 15 * X + 10 * X ^ 2 + X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 - X ^ 6) : ℤ⟦X⟧) =
      X ^ 2 * C 3 + X ^ 3 * C 15 + X ^ 4 * C 10 + X ^ 5 - X ^ 6 * C 6 + X ^ 7 * C 2 - X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 0 := by exact_mod_cast small1
  have v2 : a 2 = 3 := by exact_mod_cast small2
  have v3 : a 3 = 30 := by exact_mod_cast small3
  have v4 : a 4 = 130 := by exact_mod_cast small4
  have v5 : a 5 = 381 := val 5 _ (by norm_num) (by norm_num)
  have v6 : a 6 = 884 := val 6 _ (by norm_num) (by norm_num)
  have v7 : a 7 = 1765 := val 7 _ (by norm_num) (by norm_num)
  have v8 : a 8 = 3174 := val 8 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [ v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (q + 9) (by omega)
    simp only [ show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega,
      show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega,
      show q + 9 - 5 = q + 4 by omega] at h ⊢
    simp only [ show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega,
      show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega,
      show 1 ≤ q + 9 by omega, show 2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega,
      show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega, show ¬ q + 9 = 1 by omega,
      show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega,
      show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega,
      show ¬ q + 9 = 8 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..34). -/
theorem controls : a 1 = 0 ∧ a 2 = 3 ∧ a 3 = 30 ∧ a 4 = 130 ∧ a 5 = 381 ∧ a 6 = 884 ∧ a 7 = 1765 ∧
    a 8 = 3174 ∧ a 9 = 5285 ∧ a 10 = 8296 ∧ a 11 = 12429 ∧ a 12 = 17930 ∧ a 13 = 25069 ∧
    a 14 = 34140 ∧ a 15 = 45461 ∧ a 16 = 59374 ∧ a 17 = 76245 ∧ a 18 = 96464 ∧ a 19 = 120445 ∧
    a 20 = 148626 ∧ a 21 = 181469 ∧ a 22 = 219460 ∧ a 23 = 263109 ∧ a 24 = 312950 ∧ a 25 = 369541 ∧
    a 26 = 433464 ∧ a 27 = 505325 ∧ a 28 = 585754 ∧ a 29 = 675405 ∧ a 30 = 774956 ∧ a 31 = 885109 ∧
    a 32 = 1006590 ∧ a 33 = 1140149 ∧ a 34 = 1286560 :=
  ⟨ by exact_mod_cast small1, by exact_mod_cast small2, by exact_mod_cast small3,
    by exact_mod_cast small4, val 5 _ (by norm_num) (by norm_num),
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
    val 34 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X ^ 2 * (3 + 15 * X + 10 * X ^ 2 + X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 - X ^ 6) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221516

theorem OMA.solution : type_of% @OMA.S_oeis_a221516.main :=
  OMA.S_oeis_a221516.conjecture
