import OMAStatements.S_oeis_a360068

-- Problem: A360068: Number of integer partitions of n such that the parts have the same mean as the multiplicities.
-- Upstream: formal-conjectures statements/oeis-a360068.lean:0 (declaration OMA.S_oeis_a360068.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let L be the number of parts and k the number of distinct parts of a partition
-- of n. The multiplicities sum to L, so equal means give n / L = L / k, i.e. n * k = L ^ 2.
-- As n is squarefree, n divides L; as every part is at least 1, L <= n; so L = n and k = n.
-- But L = n forces every part to be 1, so k <= 1 < 2 <= n, a contradiction.

open OMA.S_oeis_a360068 in
theorem OMA.solution : type_of% @OMA.S_oeis_a360068.main := by
  intro n hn hsq
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hp
  unfold meanParts meanMult at hp
  rw [Multiset.toFinset_sum_count_eq, p.parts_sum] at hp
  have hne : p.parts ≠ 0 := by
    intro h
    have hs := p.parts_sum
    rw [h, Multiset.sum_zero] at hs
    omega
  have hL0 : 0 < Multiset.card p.parts := Multiset.card_pos.mpr hne
  have hk0 : 0 < p.parts.toFinset.card :=
    Finset.card_pos.mpr (Multiset.toFinset_nonempty.mpr hne)
  have hLq : (Multiset.card p.parts : ℚ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hkq : (p.parts.toFinset.card : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [div_eq_div_iff hLq hkq] at hp
  have hnk : n * p.parts.toFinset.card = Multiset.card p.parts * Multiset.card p.parts := by
    exact_mod_cast hp
  have hpos1 : ∀ x ∈ p.parts, 1 ≤ x := by
    intro x hx
    have := p.parts_pos hx
    omega
  have hLn : Multiset.card p.parts ≤ n := by
    have h := Multiset.card_nsmul_le_sum hpos1
    rw [p.parts_sum, smul_eq_mul, mul_one] at h
    exact h
  have hdvd : n ∣ Multiset.card p.parts ^ 2 := ⟨p.parts.toFinset.card, by rw [sq, hnk]⟩
  have hdvd' : n ∣ Multiset.card p.parts := (hsq.dvd_pow_iff_dvd two_ne_zero).mp hdvd
  have hLeq : Multiset.card p.parts = n := le_antisymm hLn (Nat.le_of_dvd hL0 hdvd')
  have hkeq : p.parts.toFinset.card = n := by
    rw [hLeq] at hnk
    exact Nat.eq_of_mul_eq_mul_left (by omega) hnk
  have hall : ∀ x ∈ p.parts, x = 1 := by
    intro x hx
    have h1 := hpos1 x hx
    have hce := Multiset.cons_erase hx
    have hs : x + (p.parts.erase x).sum = n := by
      rw [← Multiset.sum_cons x, hce, p.parts_sum]
    have hc : Multiset.card (p.parts.erase x) + 1 = Multiset.card p.parts := by
      rw [← Multiset.card_cons x, hce]
    have hle : Multiset.card (p.parts.erase x) ≤ (p.parts.erase x).sum := by
      have h : Multiset.card (p.parts.erase x) • 1 ≤ (p.parts.erase x).sum :=
        Multiset.card_nsmul_le_sum (fun y hy => hpos1 y (Multiset.mem_of_mem_erase hy))
      rw [smul_eq_mul, mul_one] at h
      exact h
    omega
  have hk1 : p.parts.toFinset.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Multiset.mem_toFinset] at hx hy
    rw [hall x hx, hall y hy]
  omega
