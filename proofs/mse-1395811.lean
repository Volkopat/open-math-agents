import OMAStatements.S_mse_1395811

namespace OMA.P_mse_1395811

open OMA.S_mse_1395811 Polynomial

private noncomputable def factorZ3 (k : ℕ) : Polynomial (ZMod 3) :=
  ∑ m ∈ Finset.range 28,
    Polynomial.C (((m + 2).choose m : ℕ) : ZMod 3) * (Polynomial.X : Polynomial (ZMod 3)) ^ ((4 * k + 1) * m)

private lemma choose_add_two_zmod3 (m : ℕ) :
    (((m + 2).choose m : ℕ) : ZMod 3) = if m % 3 = 0 then 1 else 0 := by
  have h : 2 * (m + 2).choose m = (m + 2) * (m + 1) := by
    have h1 : (2 + m).choose 2 = (2 + m).choose m := Nat.choose_symm_add
    rw [add_comm 2 m] at h1
    rw [← h1, Nat.choose_two_right]
    have hd : 2 ∣ (m + 2) * (m + 1) := by
      rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact ⟨(r + 1) * (2 * r + 1), by ring⟩
      · exact ⟨(2 * r + 3) * (r + 1), by ring⟩
    have := Nat.mul_div_cancel' hd
    simpa [Nat.add_sub_cancel] using this
  have hm3 : (2 * (m + 2).choose m) % 3 = ((m + 2) * (m + 1)) % 3 := congrArg (· % 3) h
  have hmod : (m + 2).choose m % 3 = if m % 3 = 0 then 1 else 0 := by
    have hdiv : 3 * (m / 3) + m % 3 = m := Nat.div_add_mod m 3
    set q := m / 3
    have hrem : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hrem with h0 | h1 | h2
    · have hm_eq : m = 3 * q := by omega
      have hprod : (m + 2) * (m + 1) = 3 * (3 * q ^ 2 + 3 * q) + 2 := by rw [hm_eq]; ring
      rw [hprod] at hm3
      simp only [h0, ↓reduceIte]
      omega
    · have hm_eq : m = 3 * q + 1 := by omega
      have hprod : (m + 2) * (m + 1) = 3 * ((q + 1) * (3 * q + 2)) := by rw [hm_eq]; ring
      rw [hprod, Nat.mul_mod_right] at hm3
      have hne : m % 3 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      omega
    · have hm_eq : m = 3 * q + 2 := by omega
      have hprod : (m + 2) * (m + 1) = 3 * ((3 * q + 4) * (q + 1)) := by rw [hm_eq]; ring
      rw [hprod, Nat.mul_mod_right] at hm3
      have hne : m % 3 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      omega
  rw [← ZMod.natCast_mod, hmod]
  split_ifs <;> simp

private lemma coeff_mul_congr {R : Type*} [CommSemiring R] {N : ℕ}
    {P₁ P₂ Q₁ Q₂ : Polynomial R}
    (hP : ∀ j ≤ N, P₁.coeff j = P₂.coeff j)
    (hQ : ∀ j ≤ N, Q₁.coeff j = Q₂.coeff j) :
    ∀ j ≤ N, (P₁ * Q₁).coeff j = (P₂ * Q₂).coeff j := by
  intro j hj
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum : x.1 + x.2 = j := by simpa using hx
  rw [hP x.1 (by omega), hQ x.2 (by omega)]

private lemma coeff_prod_congr {R : Type*} [CommSemiring R] {ι : Type*}
    {s : Finset ι} {N : ℕ} {f g : ι → Polynomial R}
    (h : ∀ i ∈ s, ∀ j ≤ N, (f i).coeff j = (g i).coeff j) :
    ∀ j ≤ N, (∏ i ∈ s, f i).coeff j = (∏ i ∈ s, g i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => intro j _; simp
  | insert a s ha ih =>
    intro j hj
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coeff_mul_congr (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))) j hj

private lemma factorZ3_coeff_ge3 (k : ℕ) (hk : 3 ≤ k) (j : ℕ) (hj : j ≤ 27) :
    (factorZ3 k).coeff j = (1 : Polynomial (ZMod 3)).coeff j := by
  unfold factorZ3
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp [Polynomial.coeff_one]
  · intro m hm hm0
    rw [choose_add_two_zmod3]
    by_cases h3 : m % 3 = 0
    · simp only [h3, ↓reduceIte, map_one, one_mul, Polynomial.coeff_X_pow]
      have hgt : 27 < (4 * k + 1) * m := by
        have hm3 : 3 ≤ m := by omega
        have hk13 : 13 ≤ 4 * k + 1 := by omega
        nlinarith
      rw [if_neg (by omega)]
    · simp [h3]
  · intro h; exact absurd (by simp) h

private noncomputable def f0 : Polynomial (ZMod 3) :=
  1 + X ^ 3 + X ^ 6 + X ^ 9 + X ^ 12 + X ^ 15 + X ^ 18 + X ^ 21 + X ^ 24 + X ^ 27

private noncomputable def f1 : Polynomial (ZMod 3) :=
  1 + X ^ 15

private noncomputable def f2 : Polynomial (ZMod 3) :=
  1 + X ^ 27

private lemma factorZ3_coeff_0 (j : ℕ) (hj : j ≤ 27) :
    (factorZ3 0).coeff j = f0.coeff j := by
  unfold factorZ3 f0
  rw [Polynomial.finsetSum_coeff]
  simp_rw [choose_add_two_zmod3, Nat.mul_zero, zero_add, one_mul]
  have hsum : (∑ m ∈ Finset.range 28,
      (Polynomial.C (if m % 3 = 0 then (1 : ZMod 3) else 0) * (X : Polynomial (ZMod 3)) ^ m).coeff j) =
      if j % 3 = 0 then (1 : ZMod 3) else 0 := by
    rw [Finset.sum_eq_single j]
    · by_cases h3 : j % 3 = 0 <;> simp [h3, Polynomial.coeff_X_pow]
    · intro m _ hmj
      by_cases h3 : m % 3 = 0 <;> simp [h3, hmj.symm, Polynomial.coeff_X_pow]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  rw [hsum]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  interval_cases j <;> decide

private lemma factorZ3_coeff_1 (j : ℕ) (hj : j ≤ 27) :
    (factorZ3 1).coeff j = f1.coeff j := by
  unfold factorZ3 f1
  rw [Polynomial.finsetSum_coeff]
  simp_rw [choose_add_two_zmod3]
  have hsum : (∑ m ∈ Finset.range 28,
      (Polynomial.C (if m % 3 = 0 then (1 : ZMod 3) else 0) *
        (X : Polynomial (ZMod 3)) ^ ((4 * 1 + 1) * m)).coeff j) =
      if j = 0 ∨ j = 15 then (1 : ZMod 3) else 0 := by
    have h0 : ∀ m ∈ Finset.range 28, m ≠ 0 → m ≠ 3 →
        (Polynomial.C (if m % 3 = 0 then (1 : ZMod 3) else 0) *
          (X : Polynomial (ZMod 3)) ^ ((4 * 1 + 1) * m)).coeff j = 0 := by
      intro m _ h0 h3
      by_cases hm3 : m % 3 = 0
      · simp only [hm3, ↓reduceIte, map_one, one_mul, Polynomial.coeff_X_pow]
        have : 27 < 5 * m := by omega
        rw [if_neg (by omega)]
      · simp [hm3]
    rw [← Finset.add_sum_erase _ _ (by simp : 0 ∈ Finset.range 28)]
    rw [← Finset.add_sum_erase _ _ (by decide : 3 ∈ (Finset.range 28).erase 0)]
    have hrest : ∑ x ∈ ((Finset.range 28).erase 0).erase 3,
        (Polynomial.C (if x % 3 = 0 then (1 : ZMod 3) else 0) *
          (X : Polynomial (ZMod 3)) ^ ((4 * 1 + 1) * x)).coeff j = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_erase] at hx
      exact h0 x hx.2.2 hx.2.1 hx.1
    rw [hrest, add_zero]
    simp only [Nat.zero_mod, ↓reduceIte, map_one, one_mul, mul_zero, pow_zero, Polynomial.coeff_one,
      Nat.mod_self, Polynomial.coeff_X_pow]
    interval_cases j <;> decide
  rw [hsum]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  interval_cases j <;> decide

private lemma factorZ3_coeff_2 (j : ℕ) (hj : j ≤ 27) :
    (factorZ3 2).coeff j = f2.coeff j := by
  unfold factorZ3 f2
  rw [Polynomial.finsetSum_coeff]
  simp_rw [choose_add_two_zmod3]
  have hsum : (∑ m ∈ Finset.range 28,
      (Polynomial.C (if m % 3 = 0 then (1 : ZMod 3) else 0) *
        (X : Polynomial (ZMod 3)) ^ ((4 * 2 + 1) * m)).coeff j) =
      if j = 0 ∨ j = 27 then (1 : ZMod 3) else 0 := by
    have h0 : ∀ m ∈ Finset.range 28, m ≠ 0 → m ≠ 3 →
        (Polynomial.C (if m % 3 = 0 then (1 : ZMod 3) else 0) *
          (X : Polynomial (ZMod 3)) ^ ((4 * 2 + 1) * m)).coeff j = 0 := by
      intro m _ h0 h3
      by_cases hm3 : m % 3 = 0
      · simp only [hm3, ↓reduceIte, map_one, one_mul, Polynomial.coeff_X_pow]
        have : 27 < 9 * m := by omega
        rw [if_neg (by omega)]
      · simp [hm3]
    rw [← Finset.add_sum_erase _ _ (by simp : 0 ∈ Finset.range 28)]
    rw [← Finset.add_sum_erase _ _ (by decide : 3 ∈ (Finset.range 28).erase 0)]
    have hrest : ∑ x ∈ ((Finset.range 28).erase 0).erase 3,
        (Polynomial.C (if x % 3 = 0 then (1 : ZMod 3) else 0) *
          (X : Polynomial (ZMod 3)) ^ ((4 * 2 + 1) * x)).coeff j = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_erase] at hx
      exact h0 x hx.2.2 hx.2.1 hx.1
    rw [hrest, add_zero]
    simp only [Nat.zero_mod, ↓reduceIte, map_one, one_mul, mul_zero, pow_zero, Polynomial.coeff_one,
      Nat.mod_self, Polynomial.coeff_X_pow]
    interval_cases j <;> decide
  rw [hsum]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  interval_cases j <;> decide

private lemma phiCoeff_3_27_mod3 : ((phiCoeff 3 27 : ℕ) : ZMod 3) = 0 := by
  unfold phiCoeff
  have hmap : ((∏ k ∈ Finset.range 27,
      ∑ m ∈ Finset.range 28,
        Polynomial.C ((m + 3 - 1).choose m) * (X : Polynomial ℕ) ^ ((4 * k + 1) * m)).coeff 27 : ZMod 3) =
      (∏ k ∈ Finset.range 27, factorZ3 k).coeff 27 := by
    change (Nat.castRingHom (ZMod 3)) ((∏ k ∈ Finset.range 27,
      ∑ m ∈ Finset.range 28,
        Polynomial.C ((m + 3 - 1).choose m) * (X : Polynomial ℕ) ^ ((4 * k + 1) * m)).coeff 27) = _
    rw [← Polynomial.coeff_map]
    congr 1
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro k _
    rw [Polynomial.map_sum]
    apply Finset.sum_congr rfl
    intro m _
    simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  rw [hmap]
  let g : ℕ → Polynomial (ZMod 3) := fun k =>
    if k = 0 then f0 else if k = 1 then f1 else if k = 2 then f2 else 1
  have hcongr : (∏ k ∈ Finset.range 27, factorZ3 k).coeff 27 =
      (∏ k ∈ Finset.range 27, g k).coeff 27 := by
    apply coeff_prod_congr (N := 27) _ 27 le_rfl
    intro k _ j hj
    by_cases h0 : k = 0
    · subst h0; simp only [g, ↓reduceIte]; exact factorZ3_coeff_0 j hj
    · by_cases h1 : k = 1
      · subst h1; simp only [g, h0, ↓reduceIte]; exact factorZ3_coeff_1 j hj
      · by_cases h2 : k = 2
        · subst h2; simp only [g, h0, h1, ↓reduceIte]; exact factorZ3_coeff_2 j hj
        · simp only [g, h0, h1, h2, ↓reduceIte]; exact factorZ3_coeff_ge3 k (by omega) j hj
  rw [hcongr]
  have hprod_g : ∏ k ∈ Finset.range 27, g k = f0 * f1 * f2 := by
    have hsplit : Finset.range 27 = {0, 1, 2} ∪ Finset.Ico 3 27 := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_Ico]; omega
    rw [hsplit, Finset.prod_union (Finset.disjoint_left.mpr (fun x hx1 hx2 => by
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico] at hx1 hx2; omega))]
    have htail : ∏ k ∈ Finset.Ico 3 27, g k = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      simp only [Finset.mem_Ico] at hk
      have h0 : k ≠ 0 := by omega
      have h1 : k ≠ 1 := by omega
      have h2 : k ≠ 2 := by omega
      simp [g, h0, h1, h2]
    rw [htail, mul_one]
    have h012 : ∏ k ∈ ({0, 1, 2} : Finset ℕ), g k = g 0 * (g 1 * g 2) := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    rw [h012]
    simp [g, mul_assoc]
  rw [hprod_g]
  -- Compute coeff 27 of f0 * f1 * f2 directly!
  have hmul1 : (f0 * f1 * f2).coeff 27 =
      (f0 * f1).coeff 27 + (f0 * f1).coeff 0 := by
    unfold f2
    rw [mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow]
  have hmul2 : ∀ d : ℕ, (f0 * f1).coeff d = f0.coeff d + (if 15 ≤ d then f0.coeff (d - 15) else 0) := by
    intro d
    unfold f1
    rw [mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
  rw [hmul1, hmul2 27, hmul2 0]
  simp only [show 15 ≤ 27 by norm_num, ↓reduceIte, show ¬ (15 ≤ 0) by norm_num, add_zero]
  have hc27 : f0.coeff 27 = 1 := by unfold f0; simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  have hc12 : f0.coeff (27 - 15) = 1 := by unfold f0; simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  have hc0 : f0.coeff 0 = 1 := by unfold f0; simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  rw [hc27, hc12, hc0]
  decide

private theorem main_disproof : ¬ (type_of% @OMA.S_mse_1395811.main) := by
  intro hmain
  have h := hmain 3 (by norm_num) ⟨1, by norm_num⟩ 27 (by norm_num)
  have hdvd : 3 ∣ phiCoeff 3 27 := (ZMod.natCast_eq_zero_iff (phiCoeff 3 27) 3).mp phiCoeff_3_27_mod3
  have hndvd : ¬ (3 ∣ 27) := h.mp hdvd
  exact hndvd ⟨9, by norm_num⟩

end OMA.P_mse_1395811

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_1395811.main) :=
  OMA.P_mse_1395811.main_disproof
