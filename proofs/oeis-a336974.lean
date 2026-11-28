import OMAStatements.S_oeis_a336974

namespace OMA.S_oeis_a336974

open PowerSeries


/-- Controls: a(0) = 0 and the entry's terms a(1..23). -/
theorem controls : (List.range 24).map a = [0, 0, 0, 2, 0, 4, 4, 11, 6, 21, 15, 35, 27, 52, 43, 83, 62, 109, 97, 152, 125, 201, 172, 258] := by
  decide

theorem sign_div (x y : ℕ) (hy : 0 < y) :
    Int.sign (((x / y : ℕ)) : ℤ) = if y ≤ x then 1 else 0 := by
  split_ifs with h
  · exact Int.sign_eq_one_of_pos (by exact_mod_cast Nat.div_pos h hy)
  · rw [Nat.div_eq_of_lt (by omega)]; rfl

/-- the triangles k <= i <= c = n - k - i with k + i > c, as pairs (k, i). -/
def tri (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (n / 3)) ×ˢ (Finset.range (n + 1))).filter
    (fun x => x.1 ≤ x.2 ∧ x.2 ≤ (n - x.1) / 2 ∧ n - x.2 - x.1 < x.2 + x.1)

theorem a_tri (n : ℕ) : a n = ∑ x ∈ tri n, ((n - x.1 : ℕ) : ℤ) := by
  unfold a tri
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

/-- Indicator of the multiples of r. -/
def d0 (r u : ℕ) : ℤ := if u % r = 0 then 1 else 0

/-- u / r on the multiples of r, 0 elsewhere. -/
def d1 (r u : ℕ) : ℤ := if u % r = 0 then ((u / r : ℕ) : ℤ) else 0

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

theorem coeff_triple (f g h : ℕ → ℤ) (m : ℕ) :
    coeff m (mk f * mk g * mk h) = ∑ s ∈ Finset.range (m + 1), ∑ u ∈ Finset.range (s + 1),
      f u * g (s - u) * h (m - s) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk f * mk g) * coeff j (mk h)) m]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk f) * coeff j (mk g)) s, Finset.sum_mul]
  simp only [coeff_mk]

/-- The weight over the triples (a, b, p), with x^(3a + 4b + 2p). -/
noncomputable def P : PowerSeries ℤ :=
  C 2 * (mk (d0 3) * mk (d0 4) * mk (d0 2)) +
    C 2 * (mk (d1 3) * mk (d0 4) * mk (d0 2)) +
    C 3 * (mk (d0 3) * mk (d1 4) * mk (d0 2)) +
    C 2 * (mk (d0 3) * mk (d0 4) * mk (d1 2))

/-- The triples, as pairs (s, u) = (3a + 4b, 3a) with 3a + 4b + 2p = m. -/
def prodSet (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun y => y.2 ≤ y.1 ∧ y.2 % 3 = 0 ∧ (y.1 - y.2) % 4 = 0 ∧ (m - y.1) % 2 = 0)

theorem coeff_P (m : ℕ) : coeff m P = ∑ y ∈ prodSet m, (2 + 2 * ((y.2 / 3 : ℕ) : ℤ) + 3 * (((y.1 - y.2) / 4 : ℕ) : ℤ) + 2 * (((m - y.1) / 2 : ℕ) : ℤ)) := by
  have hT : coeff m P = ∑ s ∈ Finset.range (m + 1), ∑ u ∈ Finset.range (s + 1),
      (if u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0 then (2 + 2 * ((u / 3 : ℕ) : ℤ) + 3 * (((s - u) / 4 : ℕ) : ℤ) + 2 * (((m - s) / 2 : ℕ) : ℤ)) else 0) := by
    unfold P
    simp only [map_add, coeff_C_mul, coeff_triple, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun u _ => ?_))
    unfold d0 d1
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
      (2 + 2 * ((u / 3 : ℕ) : ℤ) + 3 * (((s - u) / 4 : ℕ) : ℤ) + 2 * (((m - s) / 2 : ℕ) : ℤ)) else 0) =
      ∑ u ∈ Finset.range (s + 1), (if u ≤ s ∧ u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0 then
      (2 + 2 * ((u / 3 : ℕ) : ℤ) + 3 * (((s - u) / 4 : ℕ) : ℤ) + 2 * (((m - s) / 2 : ℕ) : ℤ)) else 0) :=
    Finset.sum_congr rfl (fun u hu => by
      simp only [Finset.mem_range] at hu
      simp only [show u ≤ s by omega, true_and])
  rw [e1]
  exact Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    (fun u _ hu' => by
      simp only [Finset.mem_range] at hu'
      rw [if_neg (show ¬(u ≤ s ∧ u % 3 = 0 ∧ (s - u) % 4 = 0 ∧ (m - s) % 2 = 0) by omega)])

theorem tri_prod (n : ℕ) (hn : 3 ≤ n) :
    ∑ x ∈ tri n, ((n - x.1 : ℕ) : ℤ) = ∑ y ∈ prodSet (n - 3), (2 + 2 * ((y.2 / 3 : ℕ) : ℤ) + 3 * (((y.1 - y.2) / 4 : ℕ) : ℤ) + 2 * (((n - 3 - y.1) / 2 : ℕ) : ℤ)) := by
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
    push_cast
    omega

theorem a_coeff (n : ℕ) : a n = if 3 ≤ n then coeff (n - 3) P else 0 := by
  split_ifs with h
  · rw [a_tri, tri_prod n h, coeff_P]
  · rw [a_tri]
    apply Finset.sum_eq_zero
    intro x hx
    simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hx
    omega

theorem hA : mk a = X ^ 3 * P := by
  ext n
  rw [coeff_mk, a_coeff, coeff_X_pow_mul']

theorem hP : P * ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) =
    2 * ((1 - X ^ 3) * (1 - X ^ 4) * (1 - X ^ 2)) +
      2 * (X ^ 3 * ((1 - X ^ 4) * (1 - X ^ 2))) +
      3 * (X ^ 4 * ((1 - X ^ 3) * (1 - X ^ 2))) +
      2 * (X ^ 2 * ((1 - X ^ 3) * (1 - X ^ 4))) := by
  have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have h3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have e : P * ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2) =
      2 * ((mk (d0 3) * (1 - X ^ 3)) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) * (1 - X ^ 4) * (1 - X ^ 2))) +
      2 * ((mk (d1 3) * (1 - X ^ 3) ^ 2) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 4) * (1 - X ^ 2))) +
      3 * ((mk (d0 3) * (1 - X ^ 3)) * (mk (d1 4) * (1 - X ^ 4) ^ 2) * (mk (d0 2) * (1 - X ^ 2)) *
        ((1 - X ^ 3) * (1 - X ^ 2))) +
      2 * ((mk (d0 3) * (1 - X ^ 3)) * (mk (d0 4) * (1 - X ^ 4)) * (mk (d1 2) * (1 - X ^ 2) ^ 2) *
        ((1 - X ^ 3) * (1 - X ^ 4))) := by
    unfold P; rw [h2, h3]; ring
  rw [e, g0 3 (by norm_num), g0 4 (by norm_num), g0 2 (by norm_num), g1 3 (by norm_num), g1 4 (by norm_num), g1 2 (by norm_num)]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk a * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
    X ^ 3 * (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 5 * X ^ 5 + 5 * X ^ 6) := by
  have hE : ((1 - X) ^ 2 * (1 + X) : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (fun p : PowerSeries ℤ => constantCoeff p) h
    simp at this
  apply mul_right_cancel₀ hE
  rw [hA]
  calc X ^ 3 * P * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) *
        ((1 - X) ^ 2 * (1 + X)) =
      X ^ 3 * (P * ((1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * (1 - X ^ 2) ^ 2)) := by ring
    _ = X ^ 3 * (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 5 * X ^ 5 + 5 * X ^ 6) * ((1 - X) ^ 2 * (1 + X)) := by
      rw [hP]; ring

/-- Barker's recurrence, the coefficient of x^n of the g.f. identity for n > 15. -/
theorem recurrence (n : ℕ) (hn : 15 < n) :
    a n = -a (n - 1) + 2 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5) -
      a (n - 6) - 5 * a (n - 7) - 5 * a (n - 8) - a (n - 9) + 2 * a (n - 10) + 4 * a (n - 11) +
      2 * a (n - 12) - a (n - 14) - a (n - 15) := by
  set A : PowerSeries ℤ := mk a with hAdef
  have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have h5 : (C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat C 5
  have h7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have c5 : (C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat C 5
  have hD : A * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      A + A * X ^ 1 - C 2 * (A * X ^ 3) - C 4 * (A * X ^ 4) - C 2 * (A * X ^ 5) + A * X ^ 6 +
        C 5 * (A * X ^ 7) + C 5 * (A * X ^ 8) + A * X ^ 9 - C 2 * (A * X ^ 10) -
        C 4 * (A * X ^ 11) - C 2 * (A * X ^ 12) + A * X ^ 14 + A * X ^ 15 := by
    rw [c2, c4, c5]; ring
  have hN : (X ^ 3 * (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 5 * X ^ 5 + 5 * X ^ 6) : PowerSeries ℤ) = X ^ 3 * C 2 + X ^ 4 * C 2 + X ^ 5 * C 4 + X ^ 6 * C 4 + X ^ 7 * C 7 + X ^ 8 * C 5 + X ^ 9 * C 5 := by
    rw [h2, h4, h5, h7]; ring
  have h := congrArg (coeff n) ((hD.symm.trans gf).trans hN)
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hAdef, coeff_mk,
    coeff_X_pow] at h
  simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
    show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega,
    show 10 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega, show 14 ≤ n by omega,
    show 15 ≤ n by omega, if_true, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, if_false] at h
  linear_combination h

/-- Both of Barker's conjectures. -/
theorem conjecture :
    mk a * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      X ^ 3 * (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 5 * X ^ 5 + 5 * X ^ 6) ∧
    (∀ n : ℕ, 15 < n → a n = -a (n - 1) + 2 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5) -
      a (n - 6) - 5 * a (n - 7) - 5 * a (n - 8) - a (n - 9) + 2 * a (n - 10) + 4 * a (n - 11) +
      2 * a (n - 12) - a (n - 14) - a (n - 15)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a336974

theorem OMA.solution : type_of% @OMA.S_oeis_a336974.main :=
  OMA.S_oeis_a336974.conjecture
