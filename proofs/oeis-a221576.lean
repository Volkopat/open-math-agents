import OMAStatements.S_oeis_a221576

namespace OMA.S_oeis_a221576

open PowerSeries Finset



/-- The values u and v differ by exactly 1. -/
def adj (u v : ℕ) : Prop := u = v + 1 ∨ v = u + 1

instance (u v : ℕ) : Decidable (adj u v) := by unfold adj; infer_instance

theorem adj_comm (u v : ℕ) : adj u v ↔ adj v u := by unfold adj; omega

theorem good_iff (x : Fin 6 → ℕ) : good x ↔
    (¬ (adj (x 1) (x 2) ∧ adj (x 2) (x 3)) ∧ ¬ adj (x 0) (x 1)) ∧
    (¬ (adj (x 2) (x 3) ∧ adj (x 3) (x 4)) ∧ ¬ adj (x 4) (x 5)) := by
  unfold good adj
  constructor
  · intro h
    have e0 : ¬ (x 0 = x 1 + 1 ∨ x 1 = x 0 + 1) := by
      obtain ⟨j, hj, h1, h2⟩ := h 0
      have hv : j.val = 1 := by simp at hj; omega
      have : j = 1 := Fin.ext hv
      subst this; omega
    have e5 : ¬ (x 4 = x 5 + 1 ∨ x 5 = x 4 + 1) := by
      obtain ⟨j, hj, h1, h2⟩ := h 5
      have hv : j.val = 4 := by simp at hj; omega
      have : j = 4 := Fin.ext hv
      subst this; omega
    have e2 : ¬ ((x 1 = x 2 + 1 ∨ x 2 = x 1 + 1) ∧ (x 2 = x 3 + 1 ∨ x 3 = x 2 + 1)) := by
      obtain ⟨j, hj, h1, h2⟩ := h 2
      have hv : j.val = 3 ∨ j.val = 1 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 3 := Fin.ext hv
        subst this; omega
      · have : j = 1 := Fin.ext hv
        subst this; omega
    have e3 : ¬ ((x 2 = x 3 + 1 ∨ x 3 = x 2 + 1) ∧ (x 3 = x 4 + 1 ∨ x 4 = x 3 + 1)) := by
      obtain ⟨j, hj, h1, h2⟩ := h 3
      have hv : j.val = 4 ∨ j.val = 2 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 4 := Fin.ext hv
        subst this; omega
      · have : j = 2 := Fin.ext hv
        subst this; omega
    exact ⟨⟨e2, e0⟩, ⟨e3, e5⟩⟩
  · rintro ⟨⟨h12, h01⟩, ⟨h23, h45⟩⟩ i
    fin_cases i
    · exact ⟨1, by decide, show x 0 ≠ x 1 + 1 by omega, show x 1 ≠ x 0 + 1 by omega⟩
    · exact ⟨0, by decide, show x 1 ≠ x 0 + 1 by omega, show x 0 ≠ x 1 + 1 by omega⟩
    · by_cases hc : x 1 = x 2 + 1 ∨ x 2 = x 1 + 1
      · exact ⟨3, by decide, show x 2 ≠ x 3 + 1 by omega, show x 3 ≠ x 2 + 1 by omega⟩
      · exact ⟨1, by decide, show x 2 ≠ x 1 + 1 by omega, show x 1 ≠ x 2 + 1 by omega⟩
    · by_cases hc : x 2 = x 3 + 1 ∨ x 3 = x 2 + 1
      · exact ⟨4, by decide, show x 3 ≠ x 4 + 1 by omega, show x 4 ≠ x 3 + 1 by omega⟩
      · exact ⟨2, by decide, show x 3 ≠ x 2 + 1 by omega, show x 2 ≠ x 3 + 1 by omega⟩
    · exact ⟨5, by decide, show x 4 ≠ x 5 + 1 by omega, show x 5 ≠ x 4 + 1 by omega⟩
    · exact ⟨4, by decide, show x 5 ≠ x 4 + 1 by omega, show x 4 ≠ x 5 + 1 by omega⟩

/-- The pairs (x2, x3), (x1, x0) and (x4, x5) of a good array with values in 0..n. -/
def T (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  ((range (n + 1) ×ˢ range (n + 1)) ×ˢ (range (n + 1) ×ˢ range (n + 1)) ×ˢ
    (range (n + 1) ×ˢ range (n + 1))).filter fun t =>
      (¬ (adj t.2.1.1 t.1.1 ∧ adj t.1.1 t.1.2) ∧ ¬ adj t.2.1.2 t.2.1.1) ∧
      (¬ (adj t.1.1 t.1.2 ∧ adj t.1.2 t.2.2.1) ∧ ¬ adj t.2.2.1 t.2.2.2)

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Fin 6 → ℕ :=
  ![t.2.1.2, t.2.1.1, t.1.1, t.1.2, t.2.2.1, t.2.2.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a2, a3⟩, ⟨a1, a0⟩, ⟨a4, a5⟩⟩ ⟨⟨b2, b3⟩, ⟨b1, b0⟩, ⟨b4, b5⟩⟩ h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  simp only [ψ, Matrix.cons_val] at e0 e1 e2 e3 e4 e5
  subst e0 e1 e2 e3 e4 e5
  rfl

theorem set_eq (n : ℕ) : {x : Fin 6 → ℕ | (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hb, hg⟩
    rw [good_iff] at hg
    refine ⟨((x 2, x 3), (x 1, x 0), (x 4, x 5)), ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 3)
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 0)
    · exact Nat.lt_succ_of_le (hb 4)
    · exact Nat.lt_succ_of_le (hb 5)
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨⟨⟨x2, x3⟩, ⟨x1, x0⟩, ⟨x4, x5⟩⟩, ⟨⟨⟨h2, h3⟩, ⟨h1, h0⟩, ⟨h4, h5⟩⟩, hc⟩, rfl⟩
    dsimp only at h0 h1 h2 h3 h4 h5
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ψ] <;> omega
    · rw [good_iff]
      exact hc

theorem a_eq (n : ℕ) : a n = (T n).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injective _ ψ_inj, Set.ncard_coe_finset]

/-- The number of values in 0..n not adjacent to y. -/
def f (n y : ℕ) : ℕ := ((range (n + 1)).filter fun w => ¬ adj w y).card

/-- The completions (x1, x0) of (x2, x3) on the left. -/
def L (n x2 x3 : ℕ) : ℕ :=
  ((range (n + 1) ×ˢ range (n + 1)).filter fun l => ¬ (adj l.1 x2 ∧ adj x2 x3) ∧ ¬ adj l.2 l.1).card

/-- The completions (x4, x5) of (x2, x3) on the right. -/
def Rt (n x2 x3 : ℕ) : ℕ :=
  ((range (n + 1) ×ˢ range (n + 1)).filter fun r => ¬ (adj x2 x3 ∧ adj x3 r.1) ∧ ¬ adj r.1 r.2).card

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
    L n m.1 m.2 * Rt n m.1 m.2 := by
  unfold T
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  unfold L Rt
  rw [card_filter, card_filter, sum_mul_sum, sum_product]
  refine sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_))
  split_ifs <;> simp_all

theorem L_eq (n x2 x3 : ℕ) :
    L n x2 x3 = ∑ x1 ∈ range (n + 1), if ¬ (adj x1 x2 ∧ adj x2 x3) then f n x1 else 0 := by
  unfold L f
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun x1 _ => ?_)
  by_cases h : ¬ (adj x1 x2 ∧ adj x2 x3)
  · rw [if_pos h, card_filter]
    refine sum_congr rfl (fun x0 _ => ?_)
    simp only [h, not_false_eq_true, true_and]
  · rw [if_neg h]
    simp [h]

theorem Rt_eq (n x2 x3 : ℕ) :
    Rt n x2 x3 = ∑ x4 ∈ range (n + 1), if ¬ (adj x2 x3 ∧ adj x3 x4) then f n x4 else 0 := by
  unfold Rt f
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun x4 _ => ?_)
  by_cases h : ¬ (adj x2 x3 ∧ adj x3 x4)
  · rw [if_pos h, card_filter]
    refine sum_congr rfl (fun x5 _ => ?_)
    simp only [h, not_false_eq_true, true_and, adj_comm x4 x5]
  · rw [if_neg h]
    simp [h]

/-- F = the sum of f over 0..n. -/
def F (n : ℕ) : ℤ := ∑ y ∈ range (n + 1), (f n y : ℤ)

/-- D(y) = the sum of f over the values adjacent to y. -/
def D (n y : ℕ) : ℤ := ∑ w ∈ range (n + 1), if adj w y then (f n w : ℤ) else 0

theorem L_int (n x2 x3 : ℕ) : (L n x2 x3 : ℤ) = F n - if adj x2 x3 then D n x2 else 0 := by
  rw [L_eq]
  push_cast
  unfold F D
  by_cases h : adj x2 x3
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun x1 _ => ?_)
    by_cases h1 : adj x1 x2 <;> simp [h, h1]
  · rw [if_neg h, sub_zero]
    refine sum_congr rfl (fun x1 _ => ?_)
    simp [h]

theorem Rt_int (n x2 x3 : ℕ) : (Rt n x2 x3 : ℤ) = F n - if adj x2 x3 then D n x3 else 0 := by
  rw [Rt_eq]
  push_cast
  unfold F D
  by_cases h : adj x2 x3
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun x4 _ => ?_)
    by_cases h1 : adj x3 x4 <;> simp [h, h1, adj_comm x4 x3]
  · rw [if_neg h, sub_zero]
    refine sum_congr rfl (fun x4 _ => ?_)
    simp [h]

/-- P(y) = the sum over z of (F - [z ~ y] D(z)). -/
def P (n y : ℕ) : ℤ := ∑ z ∈ range (n + 1), (F n - if adj z y then D n z else 0)

/-- Q(y) = the sum over the z adjacent to y of (F - D(z)). -/
def Q (n y : ℕ) : ℤ := ∑ z ∈ range (n + 1), if adj z y then F n - D n z else 0

theorem a_sum (n : ℕ) : (a n : ℤ) = ∑ y ∈ range (n + 1), (F n * P n y - D n y * Q n y) := by
  rw [a_eq, card_T]
  push_cast
  simp only [L_int, Rt_int]
  rw [sum_product]
  refine sum_congr rfl (fun y _ => ?_)
  have hpt : ∀ z : ℕ, (F n - if adj y z then D n y else 0) * (F n - if adj y z then D n z else 0) =
      F n * (F n - if adj z y then D n z else 0) - D n y * (if adj z y then F n - D n z else 0) := by
    intro z
    have hc : adj z y ↔ adj y z := adj_comm z y
    by_cases hA : adj y z
    · simp only [hA, hc, if_true]
      ring
    · simp only [hA, hc, if_false]
      ring
  rw [sum_congr rfl (fun z _ => hpt z), sum_sub_distrib, ← mul_sum, ← mul_sum]
  rfl

theorem nsum (n : ℕ) (g : ℕ → ℤ) (z : ℕ) (hz : z ≤ n) :
    ∑ y ∈ range (n + 1), (if adj y z then g y else 0) =
      (if 0 < z then g (z - 1) else 0) + (if z < n then g (z + 1) else 0) := by
  have h1 : ∀ y, (if adj y z then g y else 0) =
      (if y = z - 1 ∧ 0 < z then g y else 0) + (if y = z + 1 then g y else 0) := by
    intro y
    by_cases ha : y = z + 1
    · have hb : ¬ (y = z - 1 ∧ 0 < z) := by omega
      have hc : adj y z := Or.inl ha
      rw [if_pos hc, if_neg hb, if_pos ha, zero_add]
    · by_cases hb : y = z - 1 ∧ 0 < z
      · have hc : adj y z := by unfold adj; omega
        rw [if_pos hc, if_pos hb, if_neg ha, add_zero]
      · have hc : ¬ adj y z := by unfold adj; omega
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

theorem f_val (n y : ℕ) (hy : y ≤ n) :
    (f n y : ℤ) = n + 1 - (if 0 < y then 1 else 0) - (if y < n then 1 else 0) := by
  have h := nsum n (fun _ => 1) y hy
  unfold f
  rw [card_filter]
  push_cast
  have : ∀ w, (if ¬ adj w y then (1 : ℤ) else 0) = 1 - (if adj w y then 1 else 0) := by
    intro w
    by_cases hw : adj w y <;> simp [hw]
  rw [sum_congr rfl (fun w _ => this w), sum_sub_distrib, h, sum_const, card_range, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

theorem F_val (n : ℕ) : F n = n ^ 2 + 1 := by
  unfold F
  rw [sum_congr rfl (fun y hy => f_val n y (Nat.lt_succ_iff.1 (mem_range.1 hy))), sum_sub_distrib,
    sum_sub_distrib]
  have h1 : ∑ y ∈ range (n + 1), (if 0 < y then (1 : ℤ) else 0) = n := by
    rw [sum_range_succ']
    simp
  have h2 : ∑ y ∈ range (n + 1), (if y < n then (1 : ℤ) else 0) = n := by
    rw [sum_range_succ, if_neg (lt_irrefl n), add_zero,
      sum_congr rfl (fun y hy => if_pos (mem_range.1 hy))]
    simp
  rw [h1, h2, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem D_val (n y : ℕ) (hy : y ≤ n) :
    D n y = (if 0 < y then (f n (y - 1) : ℤ) else 0) + (if y < n then (f n (y + 1) : ℤ) else 0) :=
  nsum n (fun w => (f n w : ℤ)) y hy

theorem P_val (n y : ℕ) (hy : y ≤ n) :
    P n y = (n + 1) * F n - ((if 0 < y then D n (y - 1) else 0) + (if y < n then D n (y + 1) else 0)) := by
  unfold P
  rw [sum_sub_distrib, nsum n (D n) y hy, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem Q_val (n y : ℕ) (hy : y ≤ n) :
    Q n y = (if 0 < y then F n - D n (y - 1) else 0) + (if y < n then F n - D n (y + 1) else 0) :=
  nsum n (fun z => F n - D n z) y hy

theorem mid (m y : ℕ) (h1 : 3 ≤ y) (h2 : y ≤ m + 3) :
    F (m + 6) * P (m + 6) y - D (m + 6) y * Q (m + 6) y =
      ((m + 6) ^ 2 + 1) * ((m + 7) * ((m + 6) ^ 2 + 1) - 4 * (m + 5)) -
      2 * (m + 5) * (2 * ((m + 6) ^ 2 + 1) - 4 * (m + 5)) := by
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 6. -/
theorem a_big (m : ℕ) : (a (m + 6) : ℤ) = ((m + 6 : ℕ) : ℤ) ^ 6 + 2 * ((m + 6 : ℕ) : ℤ) ^ 5 -
    5 * ((m + 6 : ℕ) : ℤ) ^ 4 + 24 * ((m + 6 : ℕ) : ℤ) ^ 3 - 41 * ((m + 6 : ℕ) : ℤ) ^ 2 +
    50 * ((m + 6 : ℕ) : ℤ) - 31 := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ',
    sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1), F (m + 6) * P (m + 6) (i + 1 + 1 + 1) -
      D (m + 6) (i + 1 + 1 + 1) * Q (m + 6) (i + 1 + 1 + 1) =
      ((m + 6) ^ 2 + 1) * ((m + 7) * ((m + 6) ^ 2 + 1) - 4 * (m + 5)) -
      2 * (m + 5) * (2 * ((m + 6) ^ 2 + 1) - 4 * (m + 5)) := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg]
  push_cast
  ring

theorem small : (a 1 : ℤ) = 10 ∧ (a 2 : ℤ) = 141 ∧ (a 3 : ℤ) = 1210 ∧ (a 4 : ℤ) = 5913 ∧
    (a 5 : ℤ) = 20944 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_sum] <;> simp only [sum_range_succ, sum_range_zero] <;>
    simp (disch := omega) only [P_val, Q_val, D_val, f_val, F_val, if_pos, if_neg] <;> norm_num

/-- The closed form for n >= 4 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 6 + 2 * (n : ℤ) ^ 5 - 5 * (n : ℤ) ^ 4 +
    24 * (n : ℤ) ^ 3 - 41 * (n : ℤ) ^ 2 + 50 * (n : ℤ) - 31 := by
  rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h
  · rw [small.2.2.2.1]; norm_num
  · rw [small.2.2.2.2]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
    show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
    show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega,
    show q + 11 - 7 = q + 4 by omega]
  rw [a_poly (q + 11) (by omega), a_poly (q + 10) (by omega), a_poly (q + 9) (by omega),
    a_poly (q + 8) (by omega), a_poly (q + 7) (by omega), a_poly (q + 6) (by omega),
    a_poly (q + 5) (by omega), a_poly (q + 4) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 4 ≤ n) (h : (n : ℤ) ^ 6 + 2 * (n : ℤ) ^ 5 - 5 * (n : ℤ) ^ 4 +
    24 * (n : ℤ) ^ 3 - 41 * (n : ℤ) ^ 2 + 50 * (n : ℤ) - 31 = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^7 = x (10 + 71x + ... - 2x^9) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
    X * (10 + 71 * X + 433 * X ^ 2 + 54 * X ^ 3 + 378 * X ^ 4 - 355 * X ^ 5 + 193 * X ^ 6 -
      80 * X ^ 7 + 18 * X ^ 8 - 2 * X ^ 9) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 7 = A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) +
      C 35 * (A * X ^ 4) - C 21 * (A * X ^ 5) + C 7 * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (10 + 71 * X + 433 * X ^ 2 + 54 * X ^ 3 + 378 * X ^ 4 - 355 * X ^ 5 +
      193 * X ^ 6 - 80 * X ^ 7 + 18 * X ^ 8 - 2 * X ^ 9) : ℤ⟦X⟧) =
      X ^ 1 * C 10 + X ^ 2 * C 71 + X ^ 3 * C 433 + X ^ 4 * C 54 + X ^ 5 * C 378 -
      X ^ 6 * C 355 + X ^ 7 * C 193 - X ^ 8 * C 80 + X ^ 9 * C 18 - X ^ 10 * C 2 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  obtain ⟨v1, v2, v3, v4, v5⟩ := small
  have v6 : a 6 = 59705 := val 6 _ (by norm_num) (by norm_num)
  have v7 : a 7 = 145800 := val 7 _ (by norm_num) (by norm_num)
  have v8 : a 8 = 317233 := val 8 _ (by norm_num) (by norm_num)
  have v9 : a 9 = 631328 := val 9 _ (by norm_num) (by norm_num)
  have v10 : a 10 = 1170369 := val 10 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
      show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
      show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega,
      show q + 11 - 7 = q + 4 by omega] at h ⊢
    simp only [show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega,
      show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega,
      show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega,
      show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show 3 ≤ q + 11 by omega,
      show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega, show 6 ≤ q + 11 by omega,
      show 7 ≤ q + 11 by omega, show ¬ q + 11 = 1 by omega,
      show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega, show ¬ q + 11 = 4 by omega,
      show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega, show ¬ q + 11 = 7 by omega,
      show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by omega,
      if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..26). -/
theorem controls : a 1 = 10 ∧ a 2 = 141 ∧ a 3 = 1210 ∧ a 4 = 5913 ∧ a 5 = 20944 ∧
    a 6 = 59705 ∧ a 7 = 145800 ∧ a 8 = 317233 ∧ a 9 = 631328 ∧ a 10 = 1170369 ∧
    a 11 = 2047960 ∧ a 12 = 3416105 ∧ a 13 = 5473008 ∧ a 14 = 8471593 ∧ a 15 = 12728744 ∧
    a 16 = 18635265 ∧ a 17 = 26666560 ∧ a 18 = 37394033 ∧ a 19 = 51497208 ∧ a 20 = 69776569 ∧
    a 21 = 93167120 ∧ a 22 = 122752665 ∧ a 23 = 159780808 ∧ a 24 = 205678673 ∧
    a 25 = 262069344 ∧ a 26 = 330789025 := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := small
  exact ⟨by exact_mod_cast v1, by exact_mod_cast v2, by exact_mod_cast v3, by exact_mod_cast v4,
    by exact_mod_cast v5, val 6 _ (by norm_num) (by norm_num), val 7 _ (by norm_num) (by norm_num),
    val 8 _ (by norm_num) (by norm_num), val 9 _ (by norm_num) (by norm_num),
    val 10 _ (by norm_num) (by norm_num), val 11 _ (by norm_num) (by norm_num),
    val 12 _ (by norm_num) (by norm_num), val 13 _ (by norm_num) (by norm_num),
    val 14 _ (by norm_num) (by norm_num), val 15 _ (by norm_num) (by norm_num),
    val 16 _ (by norm_num) (by norm_num), val 17 _ (by norm_num) (by norm_num),
    val 18 _ (by norm_num) (by norm_num), val 19 _ (by norm_num) (by norm_num),
    val 20 _ (by norm_num) (by norm_num), val 21 _ (by norm_num) (by norm_num),
    val 22 _ (by norm_num) (by norm_num), val 23 _ (by norm_num) (by norm_num),
    val 24 _ (by norm_num) (by norm_num), val 25 _ (by norm_num) (by norm_num),
    val 26 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (10 + 71 * X + 433 * X ^ 2 + 54 * X ^ 3 + 378 * X ^ 4 - 355 * X ^ 5 + 193 * X ^ 6 -
        80 * X ^ 7 + 18 * X ^ 8 - 2 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221576

theorem OMA.solution : type_of% @OMA.S_oeis_a221576.main :=
  OMA.S_oeis_a221576.conjecture
