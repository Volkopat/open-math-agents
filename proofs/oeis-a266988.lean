import OMAStatements.S_oeis_a266988

/-! Primitive-root averages, following @agchua (#21832).
The finite-set negation and averaging argument is retained. The order of the
negative of a primitive root now follows from Mathlib's primitive-root power
lemmas and coprimality, replacing the explicit reverse-power calculation. -/

open OMA.S_oeis_a266988 in
theorem OMA.solution : type_of% @OMA.S_oeis_a266988.main := by
  intro p hp hlt
  by_contra h3
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcase : p = 2 ∨ p % 4 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      omega
  -- for p = 4t + 1, negation preserves the order p - 1
  have hneg : p % 4 = 1 → ∀ x : ZMod p, orderOf x = p - 1 → orderOf (-x) = p - 1 := by
    intro h1 x hx
    obtain ⟨t, ht⟩ : ∃ t, p - 1 = 4 * t := ⟨(p - 1) / 4, by omega⟩
    have ht0 : 0 < t := by omega
    have hx' : IsPrimitiveRoot x (4 * t) := by
      simpa [hx, ht] using IsPrimitiveRoot.orderOf x
    have hy : x ^ (2 * t) = -1 :=
      (IsPrimitiveRoot.pow (by omega : 0 < 4 * t) hx' (by ring : 4 * t = 2 * t * 2)).eq_neg_one_of_two_right
    have hc : (2 * t + 1).Coprime (4 * t) := by
      rw [show 4 * t = 2 * (2 * t) by ring, Nat.coprime_mul_iff_right]
      exact ⟨Nat.coprime_two_right.mpr ⟨t, rfl⟩, by simp⟩
    have hnx : -x = x ^ (2 * t + 1) := by rw [pow_succ, hy]; ring
    rw [hnx, ← (hx'.pow_of_coprime _ hc).eq_orderOf, ← ht]
  -- g -> p - g maps primitive roots to primitive roots
  have hsym : ∀ g ∈ primRoots p, p - g ∈ primRoots p := by
    intro g hg
    unfold primRoots at hg ⊢
    simp only [Finset.mem_filter, Finset.mem_Icc] at hg ⊢
    obtain ⟨⟨hg1, hg2⟩, hgo⟩ := hg
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rcases hcase with h2 | h1
    · have hpg : p - g = g := by omega
      rw [hpg]
      exact hgo
    · have hcast : ((p - g : ℕ) : ZMod p) = -((g : ℕ) : ZMod p) := by
        rw [Nat.cast_sub (by omega : g ≤ p), ZMod.natCast_self, zero_sub]
      rw [hcast]
      exact hneg h1 _ hgo
  -- there is a primitive root
  have hne : (primRoots p).Nonempty := by
    have := ZMod.isCyclic_units_prime hp
    obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hou : orderOf (u : ZMod p) = p - 1 := by
      rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
        ZMod.card_units p]
    refine ⟨(u : ZMod p).val, ?_⟩
    unfold primRoots
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_contra h0
      have h0' : (u : ZMod p).val = 0 := by omega
      rw [ZMod.val_eq_zero] at h0'
      exact u.ne_zero h0'
    · have hlt' := ZMod.val_lt (u : ZMod p)
      omega
    · rw [ZMod.natCast_zmod_val]
      exact hou
  have hS : ∀ g ∈ primRoots p, g ≤ p := by
    intro g hg
    unfold primRoots at hg
    simp only [Finset.mem_filter, Finset.mem_Icc] at hg
    obtain ⟨⟨_, hg2⟩, _⟩ := hg
    omega
  have hsum : ∑ g ∈ primRoots p, (g : ℚ) = ∑ g ∈ primRoots p, ((p : ℚ) - (g : ℚ)) := by
    refine Finset.sum_nbij' (fun g => p - g) (fun g => p - g) hsym hsym ?_ ?_ ?_
    · intro g hg
      have hgp := hS g hg
      show p - (p - g) = g
      omega
    · intro g hg
      have hgp := hS g hg
      show p - (p - g) = g
      omega
    · intro g hg
      have hgp := hS g hg
      show (g : ℚ) = (p : ℚ) - ((p - g : ℕ) : ℚ)
      rw [Nat.cast_sub hgp]
      ring
  have hsub : ∑ g ∈ primRoots p, ((p : ℚ) - (g : ℚ)) =
      ((primRoots p).card : ℚ) * (p : ℚ) - ∑ g ∈ primRoots p, (g : ℚ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℚ) < ((primRoots p).card : ℚ) := by
    exact_mod_cast hne.card_pos
  have havg : avg p = (p : ℚ) / 2 := by
    unfold avg
    rw [div_eq_iff hcard.ne']
    linear_combination (hsum + hsub) / 2
  rw [havg] at hlt
  exact lt_irrefl _ hlt
