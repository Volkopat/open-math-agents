import OMAReductions.R_Erdos470_erdos_470_parts_i_R2

-- Step Erdos470.erdos_470.parts.i.R2.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.i.R2
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_i_R2.H1 := by
  intro m t E hm ht hmt hE hsig hp hs
  have hm0 : 0 < m := hm.pos
  have ht0 : 0 < t := ht.pos
  have hn0 : 0 < m * t := Nat.mul_pos hm0 ht0
  have hsum : ∑ d ∈ (m * t).divisors, d = 2 * (m * t) + E := by
    have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hmt
    simp only [ArithmeticFunction.sigma_one_apply] at h
    rw [h, hsig]; ring
  have hprop : ∑ d ∈ (m * t).properDivisors, d = m * t + E := by
    have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m * t)
    omega
  refine ⟨⟨?_, ?_⟩, hm.mul ht⟩
  · show m * t < ∑ i ∈ (m * t).properDivisors, i
    omega
  · rintro ⟨-, s, hsub, hss⟩
    set c := (m * t).properDivisors \ s with hc
    have hcsum : ∑ d ∈ c, d = E := by
      have h2 : ∑ d ∈ c, d + ∑ d ∈ s, d = ∑ d ∈ (m * t).properDivisors, d :=
        Finset.sum_sdiff hsub
      omega
    apply hs c _ hcsum
    intro d hd
    have hd' : d ∈ (m * t).properDivisors := (Finset.mem_sdiff.1 hd).1
    have hdvd : d ∣ m * t := (Nat.mem_properDivisors.1 hd').1
    have hdle : d ≤ E := by
      rw [← hcsum]
      exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) hd
    have hcop : Nat.Coprime d t := by
      apply Nat.coprime_of_dvd
      intro p hpp hpd hpt
      have := hp p (Nat.mem_primeFactors.2 ⟨hpp, hpt, ht0.ne'⟩)
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn0
      have := Nat.le_of_dvd hd0 hpd
      omega
    exact Nat.mem_divisors.2 ⟨hcop.dvd_of_dvd_mul_right hdvd, hm0.ne'⟩
