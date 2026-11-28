import OMAReductions.R_wp_monomial_conjecture_on_noetherian_local_rings_R1

/-!
# Proof of `wp-monomial-conjecture-on-noetherian-local-rings.R1.H1`

Low cases of Hochster's monomial conjecture for any Noetherian local ring `R`:
- `t = 0`: `1 ∉ Ideal.span (Set.range x) ≤ maximalIdeal R`.
- `d = 0`: `1 ∉ (⊥ : Ideal R)` since `R` is nontrivial.
- `d = 1`: if `a ^ t ∈ Ideal.span {a ^ (t + 1)}` for `a = x 0`, then `a ^ t * (1 - a * r) = 0`.
  Since `a ∈ maximalIdeal R`, `1 - a * r` is a unit, so `a ^ t = 0`. Hence every element of
  `maximalIdeal R = (Ideal.span {a}).radical` is nilpotent, forcing every prime ideal of `R` to
  equal `maximalIdeal R`. Thus `PrimeSpectrum R` is a nonempty subsingleton, so `ringKrullDim R = 0`,
  contradicting `ringKrullDim R = 1`.
-/

open IsLocalRing

theorem OMA.solution : OMA.R_wp_monomial_conjecture_on_noetherian_local_rings_R1.H1 := by
  intro R _ _ _ d hd x hx t hdt
  rcases hdt with hd1 | rfl
  · obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    · simp only [Finset.univ_eq_empty, Finset.prod_empty, one_pow, Set.range_eq_empty,
        Ideal.span_empty, Ideal.mem_bot]
      exact one_ne_zero
    · intro hmem
      set a : R := x 0
      have hprod : (∏ i : Fin 1, x i) = a := Fin.prod_univ_one x
      have hrange_x : Set.range x = {a} := by
        ext y
        simp only [Set.mem_range, Set.mem_singleton_iff]
        exact ⟨fun ⟨i, hi⟩ => by rw [Fin.eq_zero i] at hi; exact hi.symm, fun h => ⟨0, h.symm⟩⟩
      have hrange_pow : Set.range (fun i : Fin 1 => x i ^ (t + 1)) = {a ^ (t + 1)} := by
        ext y
        simp only [Set.mem_range, Set.mem_singleton_iff]
        exact ⟨fun ⟨i, hi⟩ => by rw [Fin.eq_zero i] at hi; exact hi.symm, fun h => ⟨0, h.symm⟩⟩
      rw [hprod, hrange_pow, Ideal.mem_span_singleton] at hmem
      obtain ⟨r, hr⟩ := hmem
      have ha_mem : a ∈ maximalIdeal R := by
        rw [← hx]
        exact Ideal.le_radical (Ideal.subset_span ⟨0, rfl⟩)
      have har_mem : a * r ∈ maximalIdeal R := Ideal.mul_mem_right r _ ha_mem
      have hu_notMem : 1 - a * r ∉ maximalIdeal R := by
        intro hu
        have h1 : (1 : R) ∈ maximalIdeal R := by
          have := (maximalIdeal R).add_mem hu har_mem
          rw [sub_add_cancel] at this
          exact this
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      have hu : IsUnit (1 - a * r) := IsLocalRing.notMem_maximalIdeal.mp hu_notMem
      have hzero : a ^ t * (1 - a * r) = 0 := by
        rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← hr, sub_self]
      have hat0 : a ^ t = 0 := by
        obtain ⟨u, hu_eq⟩ := hu
        rw [← hu_eq] at hzero
        calc a ^ t = a ^ t * (u : R) * (u⁻¹ : Rˣ) := by
              rw [mul_assoc, Units.mul_inv, mul_one]
          _ = 0 * (u⁻¹ : Rˣ) := by rw [hzero]
          _ = 0 := zero_mul _
      have hP_eq : ∀ P : PrimeSpectrum R,
          P = ⟨maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩ := by
        intro P
        ext y
        constructor
        · intro hy
          exact IsLocalRing.le_maximalIdeal P.isPrime.ne_top hy
        · intro hy
          dsimp only at hy
          rw [← hx, hrange_x, Ideal.mem_radical_iff] at hy
          obtain ⟨m, hm⟩ := hy
          rw [Ideal.mem_span_singleton] at hm
          obtain ⟨s, hs⟩ := hm
          have hpow0 : y ^ (m * t) = 0 := by
            rw [pow_mul, hs, mul_pow, hat0, zero_mul]
          exact P.isPrime.mem_of_pow_mem (m * t) (hpow0.symm ▸ P.asIdeal.zero_mem)
      have hsub : Subsingleton (PrimeSpectrum R) :=
        ⟨fun P Q => (hP_eq P).trans (hP_eq Q).symm⟩
      have hne : Nonempty (PrimeSpectrum R) :=
        ⟨⟨maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩⟩
      have hdim0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
      rw [hdim0] at hd
      norm_num at hd
  · simp only [pow_zero, zero_add, pow_one]
    intro hmem
    have h1 : (1 : R) ∈ maximalIdeal R := by
      rw [← hx]
      exact Ideal.le_radical hmem
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
