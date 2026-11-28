import OMAStatements.S_oeis_a133907
import Mathlib

namespace OMA.P133907

open OMA.S_oeis_a133907

/-- Lucas: binomial(n+p, p) ≡ ⌊n/p⌋ + 1 (mod p). -/
lemma binom_iff (n p : ℕ) (hp : p.Prime) : (n + p).choose p % p = 1 ↔ p ∣ n / p := by
  have : Fact p.Prime := Fact.mk hp
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n + p) (k := p) (p := p)
  rw [Nat.mod_self, Nat.choose_zero_right, Nat.div_self hp.pos, Nat.choose_one_right, one_mul,
    Nat.add_div_right n hp.pos] at h
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
  have key : (n + p).choose p ≡ 1 [MOD p] ↔ p ∣ n / p := by
    constructor
    · intro hc
      have h2 : n / p + 1 ≡ 0 + 1 [MOD p] := by simpa using h.symm.trans hc
      exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 h2)
    · intro hd
      have h2 : n / p ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hd
      simpa using h.trans (h2.add_right 1)
  rw [← key]
  unfold Nat.ModEq
  rw [h1]

/-- Fermat: 1^(p-1) + ... + n^(p-1) ≡ n - ⌊n/p⌋ (mod p). -/
lemma sum_iff (n p : ℕ) (hp : p.Prime) :
    powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)] ↔ p ∣ n / p := by
  have : Fact p.Prime := Fact.mk hp
  rw [← ZMod.intCast_eq_intCast_iff]
  have hterm : ∀ j : ℕ, ((j : ZMod p)) ^ (p - 1) = if p ∣ j then 0 else 1 := by
    intro j
    by_cases hj : p ∣ j
    · have hz : (j : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff j p).mpr hj
      have hp1 : p - 1 ≠ 0 := by
        have := hp.two_le
        omega
      rw [if_pos hj, hz, zero_pow hp1]
    · rw [if_neg hj]
      apply ZMod.pow_card_sub_one_eq_one
      intro hz
      exact hj ((ZMod.natCast_eq_zero_iff j p).mp hz)
  have hc : ((Finset.Icc 1 n).filter (fun j => ¬ p ∣ j)).card + n / p = n := by
    have e1 := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 n) (p := fun j => p ∣ j)
    have e2 : ((Finset.Icc 1 n).filter (fun j => p ∣ j)).card = n / p := by
      have hI : Finset.Icc 1 n = Finset.Ioc 0 n := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hI]
      exact Nat.Ioc_filter_dvd_card_eq_div n p
    rw [Nat.card_Icc] at e1
    omega
  have hsum : ((powerSum n p : ℤ) : ZMod p) = ((n : ℕ) : ZMod p) - ((n / p : ℕ) : ZMod p) := by
    unfold powerSum
    push_cast
    simp only [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [eq_sub_iff_add_eq]
    exact_mod_cast congrArg (fun x : ℕ => (x : ZMod p)) hc
  rw [hsum, Int.cast_natCast, sub_eq_self, ZMod.natCast_eq_zero_iff]

end OMA.P133907

theorem OMA.solution : type_of% @OMA.S_oeis_a133907.main := by
  intro n hn
  unfold OMA.S_oeis_a133907.a OMA.S_oeis_a133907.A317358
  have hset : {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}
      = {p : ℕ | p.Prime ∧ OMA.S_oeis_a133907.powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)]} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, (OMA.P133907.sum_iff n p hp).mpr ((OMA.P133907.binom_iff n p hp).mp h)⟩
    · rintro ⟨hp, h⟩
      exact ⟨hp, (OMA.P133907.binom_iff n p hp).mpr ((OMA.P133907.sum_iff n p hp).mp h)⟩
  have hne : {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}.Nonempty := by
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
    refine ⟨p, hp, (OMA.P133907.binom_iff n p hp).mpr ?_⟩
    rw [Nat.div_eq_of_lt (by omega)]
    exact dvd_zero p
  have hmem := Nat.sInf_mem hne
  have hmem' : sInf {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}
      ∈ {p : ℕ | p.Prime ∧ OMA.S_oeis_a133907.powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)]} := by
    rw [← hset]
    exact hmem
  refine ⟨⟨hmem', ?_⟩, ?_⟩
  · intro q hq
    rw [← hset] at hq
    exact Nat.sInf_le hq
  · exact Nat.sInf_le ⟨hmem'.1.one_lt, hmem'.2⟩
