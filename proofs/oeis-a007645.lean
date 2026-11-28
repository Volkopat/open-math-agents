import OMAStatements.S_oeis_a007645
import Mathlib

namespace A007645

lemma mod3_of_dvd {p k : ℕ} (hp : p.Prime) (h : p ∣ k ^ 2 + k + 1) :
    p % 3 = 0 ∨ p % 3 = 1 := by
  by_contra hcon
  have h2 : p % 3 = 2 := by omega
  have hfp : Fact p.Prime := ⟨hp⟩
  have hz : (k : ZMod p) ^ 2 + (k : ZMod p) + 1 = 0 := by
    have h' := (ZMod.natCast_eq_zero_iff (k ^ 2 + k + 1) p).mpr h
    push_cast at h'
    exact h'
  have hk0 : (k : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hz
    simp at hz
  have hk3 : (k : ZMod p) ^ 3 = 1 := by linear_combination ((k : ZMod p) - 1) * hz
  have hf := ZMod.pow_card_sub_one_eq_one hk0
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 3 * m + 1 := ⟨(p - 1) / 3, by have := hp.two_le; omega⟩
  rw [hm, pow_succ, pow_mul, hk3, one_pow, one_mul] at hf
  rw [hf] at hz
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination hz
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  omega

lemma exists_k {p : ℕ} (hp : p.Prime) (h : p % 3 = 0 ∨ p % 3 = 1) :
    ∃ k : ℕ, p ∣ k ^ 2 + k + 1 := by
  rcases h with h | h
  · have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have hp3 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    exact ⟨1, by subst hp3; norm_num⟩
  · have hfp : Fact p.Prime := ⟨hp⟩
    have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
      rw [ZMod.card_units p]
      have := hp.two_le
      omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcard
    have hu3 : u ^ 3 = 1 := by
      rw [← hu]
      exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu
      omega
    have hv3 : (u : ZMod p) ^ 3 = 1 := by
      have h' := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hu3
      simpa using h'
    have hv1 : (u : ZMod p) ≠ 1 := fun h1 => hu1 (Units.ext h1)
    have hz : (u : ZMod p) ^ 2 + (u : ZMod p) + 1 = 0 := by
      have hprod : ((u : ZMod p) - 1) * ((u : ZMod p) ^ 2 + (u : ZMod p) + 1) = 0 := by
        linear_combination hv3
      rcases mul_eq_zero.mp hprod with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hv1
      · exact h0
    refine ⟨(u : ZMod p).val, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz

end A007645

theorem OMA.solution : type_of% @OMA.S_oeis_a007645.main := by
  intro p
  constructor
  · rintro ⟨hp, h⟩
    obtain ⟨k, hk⟩ := A007645.exists_k hp h
    by_cases hA : OMA.S_oeis_a007645.IsA002383 p
    · exact Or.inl hA
    · exact Or.inr ⟨⟨hp, k, hk⟩, hA⟩
  · rintro (⟨hp, k, rfl⟩ | ⟨⟨hp, k, hk⟩, -⟩)
    · exact ⟨hp, A007645.mod3_of_dvd hp (dvd_refl _)⟩
    · exact ⟨hp, A007645.mod3_of_dvd hp hk⟩
