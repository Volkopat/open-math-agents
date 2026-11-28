import OMAStatements.S_oeis_a195334

theorem OMA.solution : type_of% @OMA.S_oeis_a195334.main := by
  have hodd : ∀ k : ℕ, ¬ Even k → OMA.S_oeis_a195334.evenDivSum k = 0 := by
    intro k hk
    unfold OMA.S_oeis_a195334.evenDivSum
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨c, hc⟩ := hd.1.1
    exact absurd (hc ▸ hd.2.mul_right c) hk
  have heven : ∀ m : ℕ, OMA.S_oeis_a195334.evenDivSum (2 * m) = 2 * ∑ d ∈ m.divisors, d := by
    intro m
    unfold OMA.S_oeis_a195334.evenDivSum
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun d _ => d / 2) (fun e _ => 2 * e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdv, hne⟩, e, he⟩ := hd
      rw [Nat.mem_divisors]
      subst he
      have h1 : (e + e) / 2 = e := by omega
      have h2 : 2 * e ∣ 2 * m := by rwa [two_mul e]
      show (e + e) / 2 ∣ m ∧ m ≠ 0
      rw [h1]
      exact ⟨(Nat.mul_dvd_mul_iff_left (by norm_num)).mp h2, by omega⟩
    · intro e he
      rw [Nat.mem_divisors] at he
      have hm := he.2
      show 2 * e ∈ Finset.filter Even (2 * m).divisors
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.mul_dvd_mul_left 2 he.1, by omega⟩, ⟨e, by ring⟩⟩
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨_, e, he⟩ := hd
      show 2 * (d / 2) = d
      omega
    · intro e he
      show 2 * e / 2 = e
      omega
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨_, e, he⟩ := hd
      show d = 2 * (d / 2)
      omega
  have hP : ∀ m : ℕ, OMA.S_oeis_a195334.InA195334 (2 * m) ↔ OMA.S_oeis_a195334.InA023194 m := by
    intro m
    unfold OMA.S_oeis_a195334.InA195334 OMA.S_oeis_a195334.InA023194
    rw [heven m]
    constructor
    · rintro ⟨q, hq, h⟩
      have h' : ∑ d ∈ m.divisors, d = q := by omega
      rw [h']
      exact hq
    · intro h
      exact ⟨_, h, rfl⟩
  have hrange : ∀ k : ℕ, OMA.S_oeis_a195334.InA195334 k → k ∈ Set.range (fun i : ℕ => 2 * i) := by
    intro k hk
    by_contra hne
    have hkodd : ¬ Even k := by
      rintro ⟨e, he⟩
      exact hne ⟨e, by show 2 * e = k; omega⟩
    obtain ⟨q, hq, h⟩ := hk
    rw [hodd k hkodd] at h
    have h2 := hq.two_le
    omega
  have hQ : (fun i : ℕ => OMA.S_oeis_a195334.InA195334 ((fun i : ℕ => 2 * i) i))
      = OMA.S_oeis_a195334.InA023194 := funext fun m => propext (hP m)
  have hmono : StrictMono (fun i : ℕ => 2 * i) := by
    intro a b h
    show 2 * a < 2 * b
    omega
  intro n hn
  generalize n - 1 = N
  by_cases hfin : (setOf OMA.S_oeis_a195334.InA195334).Finite
  · by_cases hN : N < hfin.toFinset.card
    · have key := Nat.nth_comp_of_strictMono (p := OMA.S_oeis_a195334.InA195334) (n := N)
        hmono hrange (fun _ => hN)
      rw [hQ] at key
      exact key.symm
    · have hN' : hfin.toFinset.card ≤ N := Nat.le_of_not_lt hN
      have hfinQ : (setOf OMA.S_oeis_a195334.InA023194).Finite := by
        have h1 : ((fun i : ℕ => 2 * i) ⁻¹' setOf OMA.S_oeis_a195334.InA195334).Finite :=
          hfin.preimage (fun a _ b _ h => by
            have h' : 2 * a = 2 * b := h
            omega)
        have h2 : (fun i : ℕ => 2 * i) ⁻¹' setOf OMA.S_oeis_a195334.InA195334
            = setOf OMA.S_oeis_a195334.InA023194 := by
          ext m
          exact hP m
        rw [h2] at h1
        exact h1
      have hcard : hfinQ.toFinset.card ≤ hfin.toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun i : ℕ => 2 * i)
        · intro m hm
          have hm1 : m ∈ hfinQ.toFinset := hm
          have hm' : OMA.S_oeis_a195334.InA023194 m := (Set.Finite.mem_toFinset hfinQ).mp hm1
          have h2 : 2 * m ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr ((hP m).mpr hm')
          exact h2
        · intro a _ b _ h
          have h' : 2 * a = 2 * b := h
          omega
      rw [Nat.nth_of_card_le hfin hN', Nat.nth_of_card_le hfinQ (le_trans hcard hN')]
  · have key := Nat.nth_comp_of_strictMono (p := OMA.S_oeis_a195334.InA195334) (n := N)
      hmono hrange (fun h => absurd h hfin)
    rw [hQ] at key
    exact key.symm
