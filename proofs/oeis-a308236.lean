import OMAStatements.S_oeis_a308236

namespace OMA.S_oeis_a308236

open PowerSeries


/-- Controls: a(0) = 0 and the entry's terms a(1..24). -/
theorem controls : (List.range 25).map a =
    [0, 0, 0, 6, 0, 16, 24, 62, 42, 154, 130, 304, 280, 530, 504, 990, 820, 1448, 1452, 2260, 2040, 3318, 3080, 4634, 4398] := by
  decide

theorem sign_div (x y : ℕ) (hy : 0 < y) :
    Int.sign (((x / y : ℕ)) : ℤ) = if y ≤ x then 1 else 0 := by
  split_ifs with h
  · exact Int.sign_eq_one_of_pos (by exact_mod_cast Nat.div_pos h hy)
  · rw [Nat.div_eq_of_lt (by omega)]; rfl

/-- The triangles k <= i <= n - k - i with k + i > n - k - i, as pairs (k, i). -/
def tri (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (n / 3)) ×ˢ (Finset.range (n + 1))).filter
    (fun x => x.1 ≤ x.2 ∧ x.2 ≤ (n - x.1) / 2 ∧ n - x.2 - x.1 < x.2 + x.1)

theorem a_tri (n : ℕ) : a n = ∑ x ∈ tri n, 2 * ((x.2 * x.1 + x.2 * (n - x.2 - x.1) + x.1 * (n - x.2 - x.1) : ℕ) : ℤ) := by
  unfold a tri
  simp only [Finset.mul_sum]
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hI : Finset.Icc k ((n - k) / 2) =
      (Finset.range (n + 1)).filter (fun i => k ≤ i ∧ i ≤ (n - k) / 2) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
  rw [hI, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only
  by_cases h1 : k ≤ i ∧ i ≤ (n - k) / 2
  · rw [if_pos h1, sign_div _ _ (by omega)]
    by_cases h2 : n - i - k < i + k
    · rw [if_pos (show n - i - k + 1 ≤ i + k by omega),
        if_pos (show k ≤ i ∧ i ≤ (n - k) / 2 ∧ n - i - k < i + k from ⟨h1.1, h1.2, h2⟩)]
      ring
    · rw [if_neg (show ¬(n - i - k + 1 ≤ i + k) by omega),
        if_neg (show ¬(k ≤ i ∧ i ≤ (n - k) / 2 ∧ n - i - k < i + k) by omega)]
      ring
  · rw [if_neg h1, if_neg (show ¬(k ≤ i ∧ i ≤ (n - k) / 2 ∧ n - i - k < i + k) by tauto)]

/-- The weight 2 (ik + ic + kc) in terms of (a, b, p). -/
def Wt (a b p : ℕ) : ℤ :=
  6 + 12 * (a : ℤ) + 16 * (b : ℤ) + 8 * (p : ℤ) +
    6 * (a : ℤ) ^ 2 + 10 * (b : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2 + 16 * (a : ℤ) * (b : ℤ) +
    8 * (a : ℤ) * (p : ℤ) + 10 * (b : ℤ) * (p : ℤ)

theorem Wt_congr {a b p a' b' p' : ℕ} (h1 : a = a') (h2 : b = b') (h3 : p = p') :
    Wt a b p = Wt a' b' p' := by
  rw [h1, h2, h3]

theorem w_poly (n k i a b p : ℕ) (hk : k = 1 + a + b) (hi : i = k + p) (hc : n - i - k = i + b) :
    2 * ((i * k + i * (n - i - k) + k * (n - i - k) : ℕ) : ℤ) = Wt a b p := by
  rw [hc, hi, hk]
  unfold Wt
  push_cast
  ring

theorem a_wt (n : ℕ) : a n = ∑ x ∈ tri n, Wt (x.1 - 1 - (n - x.1 - 2 * x.2)) (n - x.1 - 2 * x.2) (x.2 - x.1) := by
  rw [a_tri]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx
  exact w_poly n x.1 x.2 _ _ _ (by omega) (by omega) (by omega)

/-- Indicator of the multiples of r. -/
def d0 (r u : ℕ) : ℤ := if u % r = 0 then 1 else 0

/-- u / r on the multiples of r, 0 elsewhere. -/
def d1 (r u : ℕ) : ℤ := if u % r = 0 then ((u / r : ℕ) : ℤ) else 0

/-- (u / r)^2 on the multiples of r, 0 elsewhere. -/
def d2 (r u : ℕ) : ℤ := if u % r = 0 then ((u / r : ℕ) : ℤ) ^ 2 else 0

theorem g0 (r : ℕ) (hr : r = 2 ∨ r = 3 ∨ r = 4) : mk (d0 r) * (1 - X ^ r) = 1 := by
  ext u
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_mk, coeff_one]
  rcases hr with rfl | rfl | rfl <;> (unfold d0; split_ifs <;> omega)

theorem g1 (r : ℕ) (hr : r = 2 ∨ r = 3 ∨ r = 4) : mk (d1 r) * (1 - X ^ r) ^ 2 = X ^ r := by
  have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have e : mk (d1 r) * (1 - X ^ r) ^ 2 =
      mk (d1 r) - C 2 * (mk (d1 r) * X ^ r) + mk (d1 r) * X ^ (2 * r) := by
    rw [h2]; ring
  rw [e]
  ext u
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases hr with rfl | rfl | rfl <;> (unfold d1; split_ifs <;> omega)

theorem g2a_2 : mk (d2 2) * (1 - X ^ 2) = C 2 * mk (d1 2) - mk (d0 2) + 1 := by
  ext u
  simp only [mul_sub, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_one]
  unfold d0 d1 d2
  by_cases h : u % 2 = 0
  · by_cases hu : 2 ≤ u
    · have k0 : (u - 2) / 2 + 1 = u / 2 := by omega
      have k1 : (((u - 2) / 2 : ℕ) : ℤ) + 1 = ((u / 2 : ℕ) : ℤ) := by exact_mod_cast k0
      simp only [if_pos h, if_pos hu, if_pos (show (u - 2) % 2 = 0 by omega),
        if_neg (show u ≠ 0 by omega)]
      linear_combination (-(((u / 2 : ℕ) : ℤ) + (((u - 2) / 2 : ℕ) : ℤ) - 1)) * k1
    · simp only [if_pos h, if_neg hu, if_pos (show u = 0 by omega), show u / 2 = 0 by omega]
      norm_num
  · simp only [if_neg h, if_neg (show u ≠ 0 by omega)]
    split_ifs <;> omega

theorem g2a_3 : mk (d2 3) * (1 - X ^ 3) = C 2 * mk (d1 3) - mk (d0 3) + 1 := by
  ext u
  simp only [mul_sub, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_one]
  unfold d0 d1 d2
  by_cases h : u % 3 = 0
  · by_cases hu : 3 ≤ u
    · have k0 : (u - 3) / 3 + 1 = u / 3 := by omega
      have k1 : (((u - 3) / 3 : ℕ) : ℤ) + 1 = ((u / 3 : ℕ) : ℤ) := by exact_mod_cast k0
      simp only [if_pos h, if_pos hu, if_pos (show (u - 3) % 3 = 0 by omega),
        if_neg (show u ≠ 0 by omega)]
      linear_combination (-(((u / 3 : ℕ) : ℤ) + (((u - 3) / 3 : ℕ) : ℤ) - 1)) * k1
    · simp only [if_pos h, if_neg hu, if_pos (show u = 0 by omega), show u / 3 = 0 by omega]
      norm_num
  · simp only [if_neg h, if_neg (show u ≠ 0 by omega)]
    split_ifs <;> omega

theorem g2a_4 : mk (d2 4) * (1 - X ^ 4) = C 2 * mk (d1 4) - mk (d0 4) + 1 := by
  ext u
  simp only [mul_sub, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_one]
  unfold d0 d1 d2
  by_cases h : u % 4 = 0
  · by_cases hu : 4 ≤ u
    · have k0 : (u - 4) / 4 + 1 = u / 4 := by omega
      have k1 : (((u - 4) / 4 : ℕ) : ℤ) + 1 = ((u / 4 : ℕ) : ℤ) := by exact_mod_cast k0
      simp only [if_pos h, if_pos hu, if_pos (show (u - 4) % 4 = 0 by omega),
        if_neg (show u ≠ 0 by omega)]
      linear_combination (-(((u / 4 : ℕ) : ℤ) + (((u - 4) / 4 : ℕ) : ℤ) - 1)) * k1
    · simp only [if_pos h, if_neg hu, if_pos (show u = 0 by omega), show u / 4 = 0 by omega]
      norm_num
  · simp only [if_neg h, if_neg (show u ≠ 0 by omega)]
    split_ifs <;> omega

theorem g2' (r : ℕ) (h2a : mk (d2 r) * (1 - X ^ r) = C 2 * mk (d1 r) - mk (d0 r) + 1)
    (h0 : mk (d0 r) * (1 - X ^ r) = 1) (h1 : mk (d1 r) * (1 - X ^ r) ^ 2 = X ^ r) :
    mk (d2 r) * (1 - X ^ r) ^ 3 = X ^ r + X ^ (2 * r) := by
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  calc mk (d2 r) * (1 - X ^ r) ^ 3 = (mk (d2 r) * (1 - X ^ r)) * (1 - X ^ r) ^ 2 := by ring
    _ = (C 2 * mk (d1 r) - mk (d0 r) + 1) * (1 - X ^ r) ^ 2 := by rw [h2a]
    _ = C 2 * (mk (d1 r) * (1 - X ^ r) ^ 2) - (mk (d0 r) * (1 - X ^ r)) * (1 - X ^ r) +
        (1 - X ^ r) ^ 2 := by ring
    _ = X ^ r + X ^ (2 * r) := by rw [h1, h0, c2]; ring

theorem g2 (r : ℕ) (hr : r = 2 ∨ r = 3 ∨ r = 4) :
    mk (d2 r) * (1 - X ^ r) ^ 3 = X ^ r + X ^ (2 * r) := by
  rcases hr with rfl | rfl | rfl
  · exact g2' 2 g2a_2 (g0 2 (by norm_num)) (g1 2 (by norm_num))
  · exact g2' 3 g2a_3 (g0 3 (by norm_num)) (g1 3 (by norm_num))
  · exact g2' 4 g2a_4 (g0 4 (by norm_num)) (g1 4 (by norm_num))

theorem coeff_triple (f g h : ℕ → ℤ) (m : ℕ) :
    coeff m (mk f * mk g * mk h) = ∑ s ∈ Finset.range (m + 1), ∑ u ∈ Finset.range (s + 1),
      f u * g (s - u) * h (m - s) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk f * mk g) * coeff j (mk h)) m]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk f) * coeff j (mk g)) s, Finset.sum_mul]
  simp only [coeff_mk]

/-- The weight Wt(a, b, p) over the triples (a, b, p), with x^(3a + 4b + 2p). -/
noncomputable def P : PowerSeries ℤ :=
  C 6 * (mk (d0 3) * mk (d0 4) * mk (d0 2)) +
    C 12 * (mk (d1 3) * mk (d0 4) * mk (d0 2)) +
    C 16 * (mk (d0 3) * mk (d1 4) * mk (d0 2)) +
    C 8 * (mk (d0 3) * mk (d0 4) * mk (d1 2)) +
    C 6 * (mk (d2 3) * mk (d0 4) * mk (d0 2)) +
    C 10 * (mk (d0 3) * mk (d2 4) * mk (d0 2)) +
    C 2 * (mk (d0 3) * mk (d0 4) * mk (d2 2)) +
    C 16 * (mk (d1 3) * mk (d1 4) * mk (d0 2)) +
    C 8 * (mk (d1 3) * mk (d0 4) * mk (d1 2)) +
    C 10 * (mk (d0 3) * mk (d1 4) * mk (d1 2))

/-- The triples, as pairs (s, u) = (3a + 4b, 3a) with 3a + 4b + 2p = m. -/
def prodSet (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun y => y.2 ≤ y.1 ∧ y.2 % 3 = 0 ∧ (y.1 - y.2) % 4 = 0 ∧ (m - y.1) % 2 = 0)

theorem coeff_P (m : ℕ) :
    coeff m P = ∑ y ∈ prodSet m, Wt (y.2 / 3) ((y.1 - y.2) / 4) ((m - y.1) / 2) := by
  have hT : coeff m P = ∑ s ∈ Finset.range (m + 1), ∑ u ∈ Finset.range (s + 1),
      (if u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0 then
        Wt (u / 3) ((s - u) / 4) ((m - s) / 2) else 0) := by
    unfold P
    simp only [map_add, coeff_C_mul, coeff_triple, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun u _ => ?_))
    unfold d0 d1 d2 Wt
    by_cases h1 : u % 3 = 0
    · by_cases h2 : (s - u) % 4 = 0
      · by_cases h3 : (m - s) % 2 = 0
        · simp only [if_pos h1, if_pos h2, if_pos h3, if_pos (show u % 3 = 0 ∧ (s - u) % 4 = 0 ∧
            (m - s) % 2 = 0 from ⟨h1, h2, h3⟩)]
          ring
        · simp only [if_pos h1, if_pos h2, if_neg h3, if_neg (show ¬(u % 3 = 0 ∧ (s - u) % 4 = 0 ∧
            (m - s) % 2 = 0) from fun h => h3 h.2.2)]
          ring
      · simp only [if_pos h1, if_neg h2, if_neg (show ¬(u % 3 = 0 ∧ (s - u) % 4 = 0 ∧
          (m - s) % 2 = 0) from fun h => h2 h.2.1)]
        ring
    · simp only [if_neg h1, if_neg (show ¬(u % 3 = 0 ∧ (s - u) % 4 = 0 ∧
        (m - s) % 2 = 0) from fun h => h1 h.1)]
      ring
  rw [hT, prodSet, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  dsimp only
  simp only [Finset.mem_range] at hs
  have e1 : ∑ u ∈ Finset.range (s + 1), (if u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0 then
      Wt (u / 3) ((s - u) / 4) ((m - s) / 2) else 0) =
      ∑ u ∈ Finset.range (s + 1), (if u ≤ s ∧ u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0 then
      Wt (u / 3) ((s - u) / 4) ((m - s) / 2) else 0) :=
    Finset.sum_congr rfl (fun u hu => by
      simp only [Finset.mem_range] at hu
      simp only [show u ≤ s by omega, true_and])
  rw [e1]
  exact Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    (fun u _ hu' => by
      simp only [Finset.mem_range] at hu'
      rw [if_neg (show ¬(u ≤ s ∧ u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0) by omega)])

theorem tri_prod (n : ℕ) (hn : 3 ≤ n) :
    ∑ x ∈ tri n, Wt (x.1 - 1 - (n - x.1 - 2 * x.2)) (n - x.1 - 2 * x.2) (x.2 - x.1) =
      ∑ y ∈ prodSet (n - 3), Wt (y.2 / 3) ((y.1 - y.2) / 4) ((n - 3 - y.1) / 2) := by
  apply Finset.sum_nbij' (fun x => (n - 3 - 2 * (x.2 - x.1), 3 * (x.1 - 1 - (n - x.1 - 2 * x.2))))
    (fun y => (1 + y.2 / 3 + (y.1 - y.2) / 4, 1 + y.2 / 3 + (y.1 - y.2) / 4 + (n - 3 - y.1) / 2))
  · intro x hx
    simp only [tri, prodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at hx ⊢
    omega
  · intro y hy
    simp only [tri, prodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at hy ⊢
    omega
  · intro x hx
    simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx
    ext <;> simp only <;> omega
  · intro y hy
    simp only [prodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    ext <;> simp only <;> omega
  · intro x hx
    simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx
    dsimp only
    exact Wt_congr (by omega) (by omega) (by omega)

theorem a_coeff (n : ℕ) : a n = if 3 ≤ n then coeff (n - 3) P else 0 := by
  split_ifs with h
  · rw [a_wt, tri_prod n h, coeff_P]
  · rw [a_wt]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx
    omega

theorem hA : mk a = X ^ 3 * P := by
  ext n
  rw [coeff_mk, a_coeff, coeff_X_pow_mul']

/-- The common denominator of the series in P. -/
noncomputable def Q : PowerSeries ℤ := (1 - X ^ 3) ^ 3 * (1 - X ^ 4) ^ 3 * (1 - X ^ 2) ^ 3

theorem t000 : mk (d0 3) * mk (d0 4) * mk (d0 2) * Q =
    (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2 := by
  have e : mk (d0 3) * mk (d0 4) * mk (d0 2) * Q =
      (mk (d0 3) * (1 - X ^ 3)) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) := by
    unfold Q; ring
  rw [e, g0 3 (by norm_num), g0 4 (by norm_num), g0 2 (by norm_num)]
  ring

theorem t100 : mk (d1 3) * mk (d0 4) * mk (d0 2) * Q =
    X ^ 3 * (1 - X ^ 3) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2 := by
  have e : mk (d1 3) * mk (d0 4) * mk (d0 2) * Q =
      (mk (d1 3) * (1 - X ^ 3) ^ 2) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) := by
    unfold Q; ring
  rw [e, g1 3 (by norm_num), g0 4 (by norm_num), g0 2 (by norm_num)]
  ring

theorem t010 : mk (d0 3) * mk (d1 4) * mk (d0 2) * Q =
    X ^ 4 * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) * (1 - X ^ 2) ^ 2 := by
  have e : mk (d0 3) * mk (d1 4) * mk (d0 2) * Q =
      (mk (d0 3) * (1 - X ^ 3)) * (mk (d1 4) * (1 - X ^ 4) ^ 2) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) * (1 - X ^ 2) ^ 2) := by
    unfold Q; ring
  rw [e, g0 3 (by norm_num), g1 4 (by norm_num), g0 2 (by norm_num)]
  ring

theorem t001 : mk (d0 3) * mk (d0 4) * mk (d1 2) * Q =
    X ^ 2 * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) := by
  have e : mk (d0 3) * mk (d0 4) * mk (d1 2) * Q =
      (mk (d0 3) * (1 - X ^ 3)) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d1 2) * (1 - X ^ 2) ^ 2) *
        ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2)) := by
    unfold Q; ring
  rw [e, g0 3 (by norm_num), g0 4 (by norm_num), g1 2 (by norm_num)]
  ring

theorem t200 : mk (d2 3) * mk (d0 4) * mk (d0 2) * Q =
    (X ^ 3 + X ^ (2 * 3)) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2 := by
  have e : mk (d2 3) * mk (d0 4) * mk (d0 2) * Q =
      (mk (d2 3) * (1 - X ^ 3) ^ 3) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) := by
    unfold Q; ring
  rw [e, g2 3 (by norm_num), g0 4 (by norm_num), g0 2 (by norm_num)]
  ring

theorem t020 : mk (d0 3) * mk (d2 4) * mk (d0 2) * Q =
    (X ^ 4 + X ^ (2 * 4)) * (1 - X ^ 3) ^ 2 * (1 - X ^ 2) ^ 2 := by
  have e : mk (d0 3) * mk (d2 4) * mk (d0 2) * Q =
      (mk (d0 3) * (1 - X ^ 3)) * (mk (d2 4) * (1 - X ^ 4) ^ 3) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) ^ 2 * (1 - X ^ 2) ^ 2) := by
    unfold Q; ring
  rw [e, g0 3 (by norm_num), g2 4 (by norm_num), g0 2 (by norm_num)]
  ring

theorem t002 : mk (d0 3) * mk (d0 4) * mk (d2 2) * Q =
    (X ^ 2 + X ^ (2 * 2)) * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 := by
  have e : mk (d0 3) * mk (d0 4) * mk (d2 2) * Q =
      (mk (d0 3) * (1 - X ^ 3)) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d2 2) * (1 - X ^ 2) ^ 3) *
        ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2) := by
    unfold Q; ring
  rw [e, g0 3 (by norm_num), g0 4 (by norm_num), g2 2 (by norm_num)]
  ring

theorem t110 : mk (d1 3) * mk (d1 4) * mk (d0 2) * Q =
    X ^ 3 * X ^ 4 * (1 - X ^ 3) * (1 - X ^ 4) * (1 - X ^ 2) ^ 2 := by
  have e : mk (d1 3) * mk (d1 4) * mk (d0 2) * Q =
      (mk (d1 3) * (1 - X ^ 3) ^ 2) * (mk (d1 4) * (1 - X ^ 4) ^ 2) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) * (1 - X ^ 4) * (1 - X ^ 2) ^ 2) := by
    unfold Q; ring
  rw [e, g1 3 (by norm_num), g1 4 (by norm_num), g0 2 (by norm_num)]
  ring

theorem t101 : mk (d1 3) * mk (d0 4) * mk (d1 2) * Q =
    X ^ 3 * X ^ 2 * (1 - X ^ 3) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) := by
  have e : mk (d1 3) * mk (d0 4) * mk (d1 2) * Q =
      (mk (d1 3) * (1 - X ^ 3) ^ 2) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d1 2) * (1 - X ^ 2) ^ 2) *
        ((1 - X ^ 3) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2)) := by
    unfold Q; ring
  rw [e, g1 3 (by norm_num), g0 4 (by norm_num), g1 2 (by norm_num)]
  ring

theorem t011 : mk (d0 3) * mk (d1 4) * mk (d1 2) * Q =
    X ^ 4 * X ^ 2 * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) * (1 - X ^ 2) := by
  have e : mk (d0 3) * mk (d1 4) * mk (d1 2) * Q =
      (mk (d0 3) * (1 - X ^ 3)) * (mk (d1 4) * (1 - X ^ 4) ^ 2) * (mk (d1 2) * (1 - X ^ 2) ^ 2) *
        ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) * (1 - X ^ 2)) := by
    unfold Q; ring
  rw [e, g0 3 (by norm_num), g1 4 (by norm_num), g1 2 (by norm_num)]
  ring

theorem hPQ : P * Q =
    6 * ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) +
      12 * (X ^ 3 * (1 - X ^ 3) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) +
      16 * (X ^ 4 * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) * (1 - X ^ 2) ^ 2) +
      8 * (X ^ 2 * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2)) +
      6 * ((X ^ 3 + X ^ (2 * 3)) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) +
      10 * ((X ^ 4 + X ^ (2 * 4)) * (1 - X ^ 3) ^ 2 * (1 - X ^ 2) ^ 2) +
      2 * ((X ^ 2 + X ^ (2 * 2)) * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2) +
      16 * (X ^ 3 * X ^ 4 * (1 - X ^ 3) * (1 - X ^ 4) * (1 - X ^ 2) ^ 2) +
      8 * (X ^ 3 * X ^ 2 * (1 - X ^ 3) * (1 - X ^ 4) ^ 2 * (1 - X ^ 2)) +
      10 * (X ^ 4 * X ^ 2 * (1 - X ^ 3) ^ 2 * (1 - X ^ 4) * (1 - X ^ 2)) := by
  have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have h6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have h8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have h10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have h12 : (C (12 : ℤ) : PowerSeries ℤ) = 12 := map_ofNat C 12
  have h16 : (C (16 : ℤ) : PowerSeries ℤ) = 16 := map_ofNat C 16
  have h : P * Q =
      6 * (mk (d0 3) * mk (d0 4) * mk (d0 2) * Q) +
      12 * (mk (d1 3) * mk (d0 4) * mk (d0 2) * Q) +
      16 * (mk (d0 3) * mk (d1 4) * mk (d0 2) * Q) +
      8 * (mk (d0 3) * mk (d0 4) * mk (d1 2) * Q) +
      6 * (mk (d2 3) * mk (d0 4) * mk (d0 2) * Q) +
      10 * (mk (d0 3) * mk (d2 4) * mk (d0 2) * Q) +
      2 * (mk (d0 3) * mk (d0 4) * mk (d2 2) * Q) +
      16 * (mk (d1 3) * mk (d1 4) * mk (d0 2) * Q) +
      8 * (mk (d1 3) * mk (d0 4) * mk (d1 2) * Q) +
      10 * (mk (d0 3) * mk (d1 4) * mk (d1 2) * Q) := by
    unfold P; rw [h2, h6, h8, h10, h12, h16]; ring
  rw [h, t000, t100, t010, t001, t200, t020, t002, t110, t101, t011]

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk a * ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X ^ 2) ^ 3 * (1 + X + X ^ 2) ^ 3) =
    2 * X ^ 3 * (3 + 6 * X + 14 * X ^ 2 + 25 * X ^ 3 + 50 * X ^ 4 + 69 * X ^ 5 + 92 * X ^ 6 +
        81 * X ^ 7 + 73 * X ^ 8 + 53 * X ^ 9 + 41 * X ^ 10 + 22 * X ^ 11 + 11 * X ^ 12) := by
  have hE : (((1 - X) ^ 4 * (1 + X) ^ 2) : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (fun p : PowerSeries ℤ => constantCoeff p) h
    simp at this
  apply mul_right_cancel₀ hE
  rw [hA]
  calc X ^ 3 * P * ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X ^ 2) ^ 3 * (1 + X + X ^ 2) ^ 3) * ((1 - X) ^ 4 * (1 + X) ^ 2) =
      X ^ 3 * (P * Q) := by unfold Q; ring
    _ = 2 * X ^ 3 * (3 + 6 * X + 14 * X ^ 2 + 25 * X ^ 3 + 50 * X ^ 4 + 69 * X ^ 5 + 92 * X ^ 6 +
        81 * X ^ 7 + 73 * X ^ 8 + 53 * X ^ 9 + 41 * X ^ 10 + 22 * X ^ 11 + 11 * X ^ 12) * ((1 - X) ^ 4 * (1 + X) ^ 2) := by
      rw [hPQ]; ring

/-- Barker's recurrence, the coefficient of x^n of the g.f. identity for n > 21. -/
theorem recurrence (n : ℕ) (hn : 21 < n) :
    a n = -2 * a (n - 1) - 2 * a (n - 2) + a (n - 3) + 7 * a (n - 4) + 10 * a (n - 5)
      + 7 * a (n - 6) - 5 * a (n - 7) - 17 * a (n - 8) - 19 * a (n - 9)
      - 9 * a (n - 10) + 9 * a (n - 11) + 19 * a (n - 12) + 17 * a (n - 13)
      + 5 * a (n - 14) - 7 * a (n - 15) - 10 * a (n - 16) - 7 * a (n - 17)
      - a (n - 18) + 2 * a (n - 19) + 2 * a (n - 20) + a (n - 21) := by
  set A : PowerSeries ℤ := mk a with hAdef
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c5 : (C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat C 5
  have c7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c9 : (C (9 : ℤ) : PowerSeries ℤ) = 9 := map_ofNat C 9
  have c10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have c17 : (C (17 : ℤ) : PowerSeries ℤ) = 17 := map_ofNat C 17
  have c19 : (C (19 : ℤ) : PowerSeries ℤ) = 19 := map_ofNat C 19
  have n6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have n12 : (C (12 : ℤ) : PowerSeries ℤ) = 12 := map_ofNat C 12
  have n22 : (C (22 : ℤ) : PowerSeries ℤ) = 22 := map_ofNat C 22
  have n28 : (C (28 : ℤ) : PowerSeries ℤ) = 28 := map_ofNat C 28
  have n44 : (C (44 : ℤ) : PowerSeries ℤ) = 44 := map_ofNat C 44
  have n50 : (C (50 : ℤ) : PowerSeries ℤ) = 50 := map_ofNat C 50
  have n82 : (C (82 : ℤ) : PowerSeries ℤ) = 82 := map_ofNat C 82
  have n100 : (C (100 : ℤ) : PowerSeries ℤ) = 100 := map_ofNat C 100
  have n106 : (C (106 : ℤ) : PowerSeries ℤ) = 106 := map_ofNat C 106
  have n138 : (C (138 : ℤ) : PowerSeries ℤ) = 138 := map_ofNat C 138
  have n146 : (C (146 : ℤ) : PowerSeries ℤ) = 146 := map_ofNat C 146
  have n162 : (C (162 : ℤ) : PowerSeries ℤ) = 162 := map_ofNat C 162
  have n184 : (C (184 : ℤ) : PowerSeries ℤ) = 184 := map_ofNat C 184
  have hD : A * ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X ^ 2) ^ 3 * (1 + X + X ^ 2) ^ 3) =
      A + C 2 * (A * X ^ 1) + C 2 * (A * X ^ 2) - A * X ^ 3 - C 7 * (A * X ^ 4)
        - C 10 * (A * X ^ 5) - C 7 * (A * X ^ 6) + C 5 * (A * X ^ 7) + C 17 * (A * X ^ 8) + C 19 * (A * X ^ 9)
        + C 9 * (A * X ^ 10) - C 9 * (A * X ^ 11) - C 19 * (A * X ^ 12) - C 17 * (A * X ^ 13) - C 5 * (A * X ^ 14)
        + C 7 * (A * X ^ 15) + C 10 * (A * X ^ 16) + C 7 * (A * X ^ 17) + A * X ^ 18 - C 2 * (A * X ^ 19)
        - C 2 * (A * X ^ 20) - A * X ^ 21 := by
    rw [c2, c5, c7, c9, c10, c17, c19]; ring
  have hN : (2 * X ^ 3 * (3 + 6 * X + 14 * X ^ 2 + 25 * X ^ 3 + 50 * X ^ 4 + 69 * X ^ 5 + 92 * X ^ 6 +
        81 * X ^ 7 + 73 * X ^ 8 + 53 * X ^ 9 + 41 * X ^ 10 + 22 * X ^ 11 + 11 * X ^ 12) : PowerSeries ℤ) =
      X ^ 3 * C 6 + X ^ 4 * C 12 + X ^ 5 * C 28 + X ^ 6 * C 50 + X ^ 7 * C 100 + X ^ 8 * C 138 + X ^ 9 * C 184 + X ^ 10 * C 162 + X ^ 11 * C 146 + X ^ 12 * C 106 + X ^ 13 * C 82 + X ^ 14 * C 44 + X ^ 15 * C 22 := by
    rw [n6, n12, n22, n28, n44, n50, n82, n100, n106, n138, n146, n162, n184]; ring
  have h := congrArg (coeff n) ((hD.symm.trans gf).trans hN)
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hAdef, coeff_mk,
    coeff_X_pow] at h
  simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega, show 13 ≤ n by omega, show 14 ≤ n by omega, show 15 ≤ n by omega, show 16 ≤ n by omega, show 17 ≤ n by omega, show 18 ≤ n by omega, show 19 ≤ n by omega, show 20 ≤ n by omega, show 21 ≤ n by omega, if_true,
    show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega, if_false] at h
  linear_combination h

/-- Both of Barker's conjectures. -/
theorem conjecture :
    mk a * ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X ^ 2) ^ 3 * (1 + X + X ^ 2) ^ 3) =
      2 * X ^ 3 * (3 + 6 * X + 14 * X ^ 2 + 25 * X ^ 3 + 50 * X ^ 4 + 69 * X ^ 5 + 92 * X ^ 6 +
        81 * X ^ 7 + 73 * X ^ 8 + 53 * X ^ 9 + 41 * X ^ 10 + 22 * X ^ 11 + 11 * X ^ 12) ∧
    (∀ n : ℕ, 21 < n → a n = -2 * a (n - 1) - 2 * a (n - 2) + a (n - 3) + 7 * a (n - 4) + 10 * a (n - 5)
      + 7 * a (n - 6) - 5 * a (n - 7) - 17 * a (n - 8) - 19 * a (n - 9)
      - 9 * a (n - 10) + 9 * a (n - 11) + 19 * a (n - 12) + 17 * a (n - 13)
      + 5 * a (n - 14) - 7 * a (n - 15) - 10 * a (n - 16) - 7 * a (n - 17)
      - a (n - 18) + 2 * a (n - 19) + 2 * a (n - 20) + a (n - 21)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a308236

theorem OMA.solution : type_of% @OMA.S_oeis_a308236.main :=
  OMA.S_oeis_a308236.conjecture
