import OMAStatements.S_oeis_a091817

namespace OMA.P_oeis_a091817

/-- In `ZMod p`, the sum of the inverses of `1, ..., p-1` vanishes. -/
lemma sum_inv_eq_zero (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    ∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod p))⁻¹ = 0 := by
  set U := ∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod p))⁻¹ with hU
  have hrefl := Finset.sum_range_reflect (fun i => (((i + 1 : ℕ) : ZMod p))⁻¹) (p - 1)
  have hneg : ∑ j ∈ Finset.range (p - 1), (((p - 1 - 1 - j + 1 : ℕ) : ZMod p))⁻¹ = -U := by
    rw [hU, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have : p - 1 - 1 - j + 1 = p - (j + 1) := by omega
    rw [this, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, inv_neg]
  have hUU : U = -U := by
    rw [← hneg]
    exact hrefl.symm
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
    exact h2 this
  have : (2 : ZMod p) * U = 0 := by
    have : U + U = 0 := by
      nth_rewrite 2 [hUU]
      ring
    rw [two_mul]; exact this
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2ne
  · exact h

end OMA.P_oeis_a091817

theorem OMA.solution : type_of% @OMA.S_oeis_a091817.main := by
  intro p hp h3
  have := Fact.mk hp
  have h2 : p ≠ 2 := by omega
  set n := p - 3 with hn
  set F := n.factorial with hF
  set H := harmonic n with hH
  set S : ℕ := ∑ i ∈ Finset.range n, F / (i + 1) with hSdef
  have hdvd : ∀ i ∈ Finset.range n, (i + 1) ∣ F := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact Nat.dvd_factorial (by omega) (by omega)
  -- `F * H = S` in `ℚ`
  have hS : (F : ℚ) * H = S := by
    rw [hH, harmonic, Finset.mul_sum, hSdef, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_div (hdvd i hi) (by positivity), div_eq_mul_inv]
  have hden : (H.den : ℚ) ≠ 0 := by exact_mod_cast H.den_nz
  have hND : (F : ℤ) * H.num = (S : ℤ) * (H.den : ℤ) := by
    have h1 : (F : ℚ) * (H.num / H.den) = S := by rw [Rat.num_div_den]; exact hS
    have h2' : (F : ℚ) * H.num = S * H.den := by
      field_simp at h1
      linear_combination h1
    exact_mod_cast h2'
  -- reduce mod `p`
  set T := ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ZMod p))⁻¹ with hTdef
  have hne : ∀ i ∈ Finset.range n, (((i + 1 : ℕ) : ZMod p)) ≠ 0 := by
    intro i hi h
    rw [Finset.mem_range] at hi
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hSz : ((S : ℕ) : ZMod p) = (F : ZMod p) * T := by
    rw [hSdef, Nat.cast_sum, hTdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [eq_mul_inv_iff_mul_eq₀ (hne i hi)]
    rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd i hi)]
  have hU := OMA.P_oeis_a091817.sum_inv_eq_zero p h2
  have hp1 : p - 1 = n + 1 + 1 := by omega
  rw [hp1, Finset.sum_range_succ, Finset.sum_range_succ, ← hTdef] at hU
  have e1 : ((n + 1 : ℕ) : ZMod p) = -2 := by
    apply eq_neg_of_add_eq_zero_left
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ← Nat.cast_add,
      show n + 1 + 2 = p by omega, ZMod.natCast_self]
  have e2 : ((n + 1 + 1 : ℕ) : ZMod p) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by norm_num, ← Nat.cast_add,
      show n + 1 + 1 + 1 = p by omega, ZMod.natCast_self]
  rw [e1, e2] at hU
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hT : 2 * T = 3 := by
    have : T = 2⁻¹ + 1 := by
      rw [inv_neg, inv_neg, inv_one] at hU
      linear_combination hU
    rw [this, mul_add, mul_inv_cancel₀ h2ne]
    norm_num
  have hFne : (F : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hF, hp.dvd_factorial]
    omega
  have hNDz : (F : ZMod p) * (H.num : ZMod p) = (F : ZMod p) * T * (H.den : ZMod p) := by
    rw [← hSz]
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hND
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have : (F : ZMod p) * (2 * (H.num : ZMod p) - 3 * (H.den : ZMod p)) = 0 := by
    linear_combination 2 * hNDz + (F : ZMod p) * (H.den : ZMod p) * hT
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hFne
  · exact h
