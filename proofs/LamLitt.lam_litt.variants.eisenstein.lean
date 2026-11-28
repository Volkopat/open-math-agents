import FormalConjectures.LittProblems.«1»

/-! Eisenstein theorem proof, following @LordMike (#706) and @joshuadc11 (#15808). -/

open PowerSeries Polynomial

theorem OMA.solution : type_of% @LamLitt.lam_litt.variants.eisenstein := by
  classical
  intro f ⟨P0, hP0, hP0'⟩
  have hexP : ∃ d, ∃ P : ℚ[X][X], P ≠ 0 ∧ Polynomial.aeval f P = 0 ∧ P.natDegree = d :=
    ⟨_, P0, hP0, hP0', rfl⟩
  obtain ⟨P, hPne, hPa, hPd⟩ := Nat.find_spec hexP
  have hDa : Polynomial.aeval f (Polynomial.derivative P) ≠ 0 := fun hD => by
    by_cases h0 : P.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at hPa hPne
      simp only [Polynomial.aeval_C] at hPa
      have h0' : P.coeff 0 = 0 := Polynomial.coe_eq_zero_iff.mp (hPa : ((P.coeff 0 : ℚ[X]) : ℚ⟦X⟧) = 0)
      exact hPne (by rw [h0']; simp)
    · exact Nat.find_min hexP (m := (Polynomial.derivative P).natDegree)
        (by have := Polynomial.natDegree_derivative_lt h0; omega)
        ⟨_, fun h => h0 (Polynomial.derivative_eq_zero.mp h), hD, rfl⟩
  set Pm : ℚ⟦X⟧[X] := P.map (algebraMap ℚ[X] ℚ⟦X⟧) with hPm
  have hP : Pm.eval f = 0 := by rw [hPm, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hPa
  have hD : Pm.derivative.eval f ≠ 0 := by
    rw [hPm, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hDa
  set D := Pm.derivative.eval f
  set m := D.order.toNat
  set u0 := PowerSeries.coeff m D
  have hu0 : u0 ≠ 0 := PowerSeries.coeff_order hD
  have hlt : ∀ i < m, PowerSeries.coeff i D = 0 :=
    fun i hi => PowerSeries.coeff_of_lt_order_toNat i hi
  set s0 : Finset ℚ := P.support.biUnion fun i => (P.coeff i).support.image (P.coeff i).coeff with hs0
  set s : Finset ℚ := insert 0 (insert u0⁻¹ (s0 ∪ (Finset.range (m + 1)).image (PowerSeries.coeff · f))) with hs
  have hspos : (∏ q ∈ s, q.den) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => q.den_nz
  refine ⟨∏ q ∈ s, q.den, ?_⟩
  set N := ∏ q ∈ s, q.den
  set R : Subring ℚ := (LamLitt.ℤAdjoinInvNat N).toSubring
  have hRmem : ∀ q ∈ s, q ∈ R := fun q hq => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun x : ℚ => x.den) hq
    have hq' : q = ((q.num * c : ℤ) : ℚ) * (1 / N) := by
      have hcN : (N : ℚ) = q.den * c := by exact_mod_cast hc
      rw [mul_one_div, eq_div_iff (by exact_mod_cast hspos : (N : ℚ) ≠ 0),
        hcN, ← mul_assoc, Rat.mul_den_eq_num]
      push_cast
      rfl
    exact hq' ▸ Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Algebra.subset_adjoin rfl)
  let serR : Subring ℚ⟦X⟧ := (PowerSeries.map R.subtype).range
  have mser {p : ℚ⟦X⟧} : p ∈ serR ↔ ∀ n, PowerSeries.coeff n p ∈ R :=
    ⟨by rintro ⟨q, rfl⟩ n; simp, fun h => ⟨p.toSubring R h, p.map_toSubring R h⟩⟩
  have hPcoef (i : ℕ) : Pm.coeff i ∈ serR := mser.2 fun n => by
    rw [hPm, Polynomial.coeff_map, show PowerSeries.coeff n (algebraMap ℚ[X] ℚ⟦X⟧ (P.coeff i)) =
      (P.coeff i).coeff n from Polynomial.coeff_coe _ _]
    by_cases h1 : P.coeff i = 0
    · rw [h1]; simp
    · by_cases h2 : (P.coeff i).coeff n = 0
      · rw [h2]; exact R.zero_mem
      · exact hRmem _ (by
          simp only [hs, hs0, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, Polynomial.mem_support_iff]
          exact Or.inr (Or.inr (Or.inl ⟨i, h1, n, h2, rfl⟩)))
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ m
    · exact hRmem _ (by
        simp only [hs, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inr (Or.inr (Or.inr ⟨k, by omega, rfl⟩)))
    · push Not at hk
      set g : ℚ⟦X⟧ := ((trunc k f : ℚ[X]) : ℚ⟦X⟧) with hg
      have hcg i : PowerSeries.coeff i g = if i < k then PowerSeries.coeff i f else 0 := by
        rw [hg, Polynomial.coeff_coe, coeff_trunc]
      have hy : (X : ℚ⟦X⟧) ^ k ∣ f - g := PowerSeries.X_pow_dvd_iff.2 fun i hi => by
        rw [map_sub, hcg, if_pos hi, sub_self]
      obtain ⟨y', hy'⟩ := hy
      have hy0 : PowerSeries.coeff 0 y' = PowerSeries.coeff k f := by
        have := congrArg (PowerSeries.coeff k) hy'
        rw [map_sub, hcg, if_neg (lt_irrefl k), sub_zero, PowerSeries.coeff_X_pow_mul'] at this
        simpa using this.symm
      obtain ⟨K, hK⟩ := Polynomial.binomExpansion Pm g (f - g)
      rw [add_sub_cancel, hP] at hK
      have hDc : ∀ i < k, PowerSeries.coeff i (Pm.derivative.eval g) = PowerSeries.coeff i D :=
        fun i hi => by
          have := PowerSeries.X_pow_dvd_iff.mp
            (dvd_trans ⟨y', hy'⟩ (Polynomial.sub_dvd_eval_sub f g Pm.derivative)) i hi
          rw [map_sub, sub_eq_zero] at this; exact this.symm
      have h2 := congrArg (PowerSeries.coeff (k + m)) hK
      rw [map_zero, map_add, map_add] at h2
      have e1 : PowerSeries.coeff (k + m) (Pm.derivative.eval g * (f - g)) = u0 * PowerSeries.coeff k f := by
        rw [hy', mul_left_comm, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left,
          PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]
        · simp only; rw [hDc m hk, hy0]
        · rintro ⟨a, b⟩ hab hne
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
          by_cases ha : a < m
          · rw [hDc a (by omega), hlt a ha, zero_mul]
          · exfalso; apply hne
            have : a = m ∧ b = 0 := by simp at hab ⊢; omega
            simp [this.1, this.2]
        · exact fun h => absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) h
      have e2 : PowerSeries.coeff (k + m) (K * (f - g) ^ 2) = 0 :=
        PowerSeries.X_pow_dvd_iff.mp (dvd_mul_of_dvd_right (by
          rw [hy', mul_pow, ← pow_mul, mul_comm k 2]; exact dvd_mul_right _ _) _) _ (by omega)
      rw [e1, e2] at h2
      have hgR : g ∈ serR := mser.2 fun n => by rw [hcg]; split_ifs with h; exact ih n h; exact R.zero_mem
      have hmem : PowerSeries.coeff (k + m) (Pm.eval g) ∈ R := mser.1 (by
        rw [Polynomial.eval_eq_sum_range]
        exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hPcoef i) (Subring.pow_mem _ hgR i)) (k + m)
      have hkf : PowerSeries.coeff k f = -u0⁻¹ * PowerSeries.coeff (k + m) (Pm.eval g) := by
        field_simp; linarith
      rw [hkf]; exact R.mul_mem (R.neg_mem (hRmem _ (by simp [hs]))) hmem
