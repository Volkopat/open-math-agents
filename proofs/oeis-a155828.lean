import OMAStatements.S_oeis_a155828
import Mathlib

-- Proof of John W. Layman's conjecture in OEIS A155828 (statement by @ivillar).
-- Idea (Zhi-Wei Sun's remark in the entry): for n ≥ 2, k ↦ sqrt(k*n+1) mod n is a bijection onto
-- the square roots of 1 modulo n other than 1; these form the 2-torsion subgroup of (ℤ/nℤ)ˣ, a
-- 2-group, so their number is a power of 2.

namespace OMAA155828Helpers

open OMA.S_oeis_a155828

theorem card_sqrt_one (n : ℕ) [NeZero n] :
    ∃ m : ℕ, Nat.card {y : ZMod n // y ^ 2 = 1} = 2 ^ m := by
  classical
  let H := (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).ker
  have hP : IsPGroup 2 H := by
    intro g
    refine ⟨1, ?_⟩
    have hg := g.2
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hg
    ext
    simp [hg]
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  refine ⟨m, ?_⟩
  rw [← hm]
  symm
  apply Nat.card_congr
  exact {
    toFun := fun u => ⟨((u.1 : (ZMod n)ˣ) : ZMod n), by
      have hu := u.2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hu
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]⟩
    invFun := fun y => ⟨Units.mkOfMulEqOne y.1 y.1 (by rw [← sq]; exact y.2), by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, Units.val_one]
      exact y.2⟩
    left_inv := fun u => by
      ext
      simp [Units.val_mkOfMulEqOne]
    right_inv := fun y => by
      ext
      simp [Units.val_mkOfMulEqOne] }

theorem not_sq_two : ¬ IsSquare (2 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 1 := by nlinarith
  interval_cases r <;> omega

theorem count_eq (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    a n + 1 = ((Finset.univ : Finset (ZMod n)).filter (fun y => y ^ 2 = 1)).card := by
  classical
  have : Fact (1 < n) := ⟨by omega⟩
  set T := (Finset.univ : Finset (ZMod n)).filter (fun y => y ^ 2 = 1)
  have h1 : (1 : ZMod n) ∈ T := by simp [T]
  rw [← Finset.card_erase_add_one h1]
  congr 1
  unfold a
  symm
  refine Finset.card_bij' (fun y _ => (y.val ^ 2 - 1) / n)
    (fun k _ => ((Nat.sqrt (k * n + 1) : ℕ) : ZMod n)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hy1, hy2⟩ := hy
    set v := y.val with hv
    have hvlt : v < n := ZMod.val_lt y
    have hv0 : v ≠ 0 := by
      intro h0
      rw [hv, ZMod.val_eq_zero] at h0
      rw [h0] at hy2
      simp at hy2
    have hv1 : v ≠ 1 := by
      intro h1'
      apply hy1
      rw [← ZMod.natCast_zmod_val y, ← hv, h1', Nat.cast_one]
    have hsq : 1 ≤ v ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hdvd : n ∣ v ^ 2 - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hsq, Nat.cast_pow, hv, ZMod.natCast_zmod_val, hy2,
        Nat.cast_one, sub_self]
    obtain ⟨k, hk⟩ := hdvd
    have hn0 : 0 < n := by omega
    rw [hk, Nat.mul_div_cancel_left _ hn0]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨v, by rw [mul_comm k n, ← hk]; rw [Nat.sub_add_cancel hsq]; ring⟩⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        have : v ^ 2 = 1 := by omega
        have : v = 1 := by
          rcases v with _ | _ | v
          · simp at this
          · rfl
          · nlinarith
        exact absurd this hv1
      · exact h
    · by_contra hkn
      push Not at hkn
      have : n * n < n * k := Nat.mul_lt_mul_of_pos_left hkn hn0
      have : v ^ 2 < n * n := by nlinarith
      omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, r, hr⟩ := hk
    rw [hr, Nat.sqrt_eq]
    have hr2 : 2 ≤ r := by
      by_contra h
      push Not at h
      interval_cases r <;> nlinarith
    have hrn : r < n := by
      by_contra h
      push Not at h
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [← h'] at hr
        have : n * (n - k) = 1 := by
          rw [Nat.mul_sub, ← hr]; rw [mul_comm n k]; omega
        have : n ∣ 1 := ⟨n - k, this.symm⟩
        have := Nat.le_of_dvd one_pos this
        omega
      · have : (n + 1) * (n + 1) ≤ r * r := Nat.mul_le_mul h' h'
        nlinarith
    simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrn, ZMod.val_one] at this
      omega
    · have : ((r * r : ℕ) : ZMod n) = ((k * n + 1 : ℕ) : ZMod n) := by rw [hr]
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, zero_add] at this
      rw [sq]; exact this
  · intro y hy
    simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hy1, hy2⟩ := hy
    set v := y.val with hv
    have hsq : 1 ≤ v ^ 2 := by
      have hv0 : v ≠ 0 := by
        intro h0
        rw [hv, ZMod.val_eq_zero] at h0
        rw [h0] at hy2
        simp at hy2
      exact Nat.one_le_pow _ _ (by omega)
    have hdvd : n ∣ v ^ 2 - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hsq, Nat.cast_pow, hv, ZMod.natCast_zmod_val, hy2,
        Nat.cast_one, sub_self]
    rw [Nat.div_mul_cancel hdvd, Nat.sub_add_cancel hsq, Nat.sqrt_eq', hv, ZMod.natCast_zmod_val]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, r, hr⟩ := hk
    rw [hr, Nat.sqrt_eq]
    have hrn : r < n := by
      by_contra h
      push Not at h
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [← h'] at hr
        have : n * (n - k) = 1 := by
          rw [Nat.mul_sub, ← hr]; rw [mul_comm n k]; omega
        have : n ∣ 1 := ⟨n - k, this.symm⟩
        have := Nat.le_of_dvd one_pos this
        omega
      · have : (n + 1) * (n + 1) ≤ r * r := Nat.mul_le_mul h' h'
        nlinarith
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrn, sq, ← hr, Nat.add_sub_cancel,
      Nat.mul_div_cancel _ (by omega)]

end OMAA155828Helpers

open OMA.S_oeis_a155828 OMAA155828Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a155828.main := by
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h
    refine ⟨0, ?_⟩
    have : a 1 = 0 := by
      unfold a
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have : k = 1 := by omega
      subst this
      exact not_sq_two
    simp [this]
  · have : NeZero n := ⟨by omega⟩
    obtain ⟨m, hm⟩ := card_sqrt_one n
    refine ⟨m, ?_⟩
    have h1 := count_eq n (by omega)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hm
    rw [hm] at h1
    omega

