import OMAStatements.S_oeis_a025527

open OMA.S_oeis_a025527

private lemma totient_ratio (m : ℕ) :
    m.factorial / L m = m.factorial.totient / (L m).totient := by
  have hd : L m ∣ m.factorial := by
    apply Finset.lcm_dvd
    intro d hd
    exact Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
  have hL : 0 < L m := Nat.pos_of_dvd_of_pos hd (Nat.factorial_pos _)
  have hpf : m.factorial.primeFactors = (L m).primeFactors := by
    ext q
    rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hq, hdq, _⟩
      refine ⟨hq, ?_, hL.ne'⟩
      exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hq.pos, hq.dvd_factorial.mp hdq⟩)
    · rintro ⟨hq, hdq, _⟩
      exact ⟨hq, hdq.trans hd, Nat.factorial_ne_zero m⟩
  obtain ⟨k, hk⟩ := hd
  have hphi : m.factorial.totient = (L m).totient * k := by
    have h : (m.factorial.totient : ℚ) = ((L m).totient : ℚ) * k := by
      rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors, hpf, hk]
      push_cast
      ring
    exact_mod_cast h
  rw [hphi, hk]
  simp [hL, Nat.totient_pos.mpr hL]

theorem OMA.solution : type_of% @OMA.S_oeis_a025527.main := by
  intro p _
  exact totient_ratio (p - 1)

