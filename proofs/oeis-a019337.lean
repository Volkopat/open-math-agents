import OMAStatements.S_oeis_a019337

namespace OMA.A019337

/-- The squares modulo 7 are 0, 1, 2 and 4. -/
lemma sq_mod_seven (r : ℕ) (hr : r < 7) :
    IsSquare ((r : ℕ) : ZMod 7) ↔ (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 4) := by
  interval_cases r <;> decide

lemma seven_eq_zero : (7 : ZMod 7) = 0 := by decide

end OMA.A019337

theorem OMA.solution : type_of% @OMA.S_oeis_a019337.main := by
  rintro p ⟨hp, hord⟩ hp2
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by
    have := hp.two_le; omega
  have hp7 : p ≠ 7 := by
    rintro rfl
    rw [OMA.A019337.seven_eq_zero, orderOf_eq_zero_iff'.mpr] at hord
    · norm_num at hord
    · intro n hn h
      rw [zero_pow hn.ne'] at h
      exact zero_ne_one h
  have h7ne : (7 : ZMod p) ≠ 0 := by
    intro h
    have : ((7 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this
    exact hp7 this
  have hnsq : ¬ IsSquare (7 : ZMod p) := by
    intro hsq
    rw [ZMod.euler_criterion p h7ne] at hsq
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at hdvd
    have hpos : 0 < p / 2 := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hcast : ((7 : ℕ) : ZMod p) = 7 := by norm_num
  set r := p % 7 with hr
  have hpr : ((p : ℕ) : ZMod 7) = ((r : ℕ) : ZMod 7) := by
    rw [hr, ZMod.natCast_mod]
  have hr7 : r < 7 := Nat.mod_lt _ (by norm_num)
  have hr0 : r ≠ 0 := by
    intro h0
    have h7 : 7 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h7).symm
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h4 with h4 | h4
  · have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 7) h4 (by norm_num)
    rw [hcast, hpr] at key
    have hns : ¬ IsSquare ((r : ℕ) : ZMod 7) := fun h => hnsq (key.mpr h)
    rw [OMA.A019337.sq_mod_seven r hr7] at hns
    omega
  · have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 7) h4
      (by norm_num) hp7
    rw [hcast, hpr] at key
    have hs : IsSquare ((r : ℕ) : ZMod 7) := by
      by_contra h
      exact hnsq (key.mpr h)
    rw [OMA.A019337.sq_mod_seven r hr7] at hs
    omega
