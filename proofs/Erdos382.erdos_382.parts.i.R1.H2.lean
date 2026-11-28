import OMAReductions.R_Erdos382_erdos_382_parts_i_R1

-- Step H2 of reduction Erdos382.erdos_382.parts.i.R1: if the largest prime of the interval product
-- occurs at least twice, there is no prime in (u, v]. Such a prime q forces the largest prime P to
-- satisfy u < q ≤ P ≤ v < 2u, so P is the only multiple of P in [u, v] and appears only once.
-- Credit: @GiridhariPradeep (agent: Claude Code)

theorem OMA.solution : OMA.R_Erdos382_erdos_382_parts_i_R1.H2 := by
  intro u v h q hq huq hqv
  have h2u : v < 2 * u := Erdos382.lt_two_mul_of_largestPrimeRepeated h
  obtain ⟨hu, -, hv, hdvd⟩ := h
  have hP0 : ∏ m ∈ Finset.Icc u v, m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm ↦ by have := (Finset.mem_Icc.1 hm).1; omega
  have hqP : q ∣ ∏ m ∈ Finset.Icc u v, m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hP1 : 1 < ∏ m ∈ Finset.Icc u v, m :=
    lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hP0) hqP)
  set p := Nat.maxPrimeFac (∏ m ∈ Finset.Icc u v, m)
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt _ hP1
  have hpq : q ≤ p := Nat.le_maxPrimeFac hP0 hq hqP
  have hv2 : v < 2 * p := by omega
  have key : ∀ m ∈ Finset.Icc u v, p ∣ m → m = p := by
    rintro m hm ⟨k, rfl⟩
    have hm' := Finset.mem_Icc.1 hm
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> omega
    · have := Nat.mul_le_mul_left p hk
      linarith [hm'.2]
  have hpmem : p ∈ Finset.Icc u v := by
    obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1
      (Nat.maxPrimeFac_dvd (n := ∏ m ∈ Finset.Icc u v, m))
    rwa [← key m hm hpm]
  rw [← Finset.mul_prod_erase _ _ hpmem, pow_two] at hdvd
  obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1
    ((mul_dvd_mul_iff_left hp.ne_zero).1 hdvd)
  exact (Finset.mem_erase.1 hm).1 (key m (Finset.mem_of_mem_erase hm) hpm)
