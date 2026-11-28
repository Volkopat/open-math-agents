import OMAStatements.S_oeis_a395839
import Mathlib

namespace A395839aux

open OMA.S_oeis_a395839 in
/-- The Catalan series with coefficients reduced modulo `p`. -/
noncomputable def cz (p : ℕ) : PowerSeries (ZMod p) :=
  PowerSeries.map (Int.castRingHom (ZMod p)) catalanZ

open OMA.S_oeis_a395839 in
lemma cz_coeff (p n : ℕ) : PowerSeries.coeff n (cz p) = (catalan n : ZMod p) := by
  unfold cz catalanZ
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff]
  simp

open OMA.S_oeis_a395839 in
lemma cz_eq (p : ℕ) : cz p ^ 2 * PowerSeries.X + 1 = cz p := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  have h2 := congrArg (PowerSeries.map (Int.castRingHom (ZMod p))) h
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h2
  exact h2

open OMA.S_oeis_a395839 in
lemma cz_sq_coeff (p n : ℕ) :
    PowerSeries.coeff n (cz p ^ 2) = (catalan (n + 1) : ZMod p) := by
  have h := congrArg (PowerSeries.coeff (n + 1)) (cz_eq p)
  rw [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_one, if_neg (by omega), add_zero,
    cz_coeff] at h
  exact h

open OMA.S_oeis_a395839 in
lemma frob (p : ℕ) [hp : Fact p.Prime] (f : PowerSeries (ZMod p)) :
    f ^ p = PowerSeries.expand p hp.out.ne_zero f := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) p hp.out.ne_zero
    (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

open OMA.S_oeis_a395839 in
lemma coeff_formula (p n : ℕ) : ((series.coeff n : ℤ) : ZMod p)
    = (10 : ZMod p) * (catalan (n + 1) : ZMod p) - (catalan n : ZMod p) := by
  have h10 : (10 : PowerSeries (ZMod p)) = PowerSeries.C (10 : ZMod p) :=
    (map_ofNat _ 10).symm
  have hmap : PowerSeries.map (Int.castRingHom (ZMod p)) series = 10 * cz p ^ 2 - cz p := by
    unfold series cz
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  have h1 : ((series.coeff n : ℤ) : ZMod p)
      = PowerSeries.coeff n (PowerSeries.map (Int.castRingHom (ZMod p)) series) := by
    rw [PowerSeries.coeff_map]
    rfl
  rw [h1, hmap, h10, map_sub, PowerSeries.coeff_C_mul, cz_sq_coeff, cz_coeff]

open OMA.S_oeis_a395839 in
lemma cat3 (j : ℕ) : (catalan (j + 2) : ZMod 3) - (catalan (j + 1) : ZMod 3)
    = if 3 ∣ j then (catalan (j / 3) : ZMod 3) else 0 := by
  have hf : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : cz 3 ^ 2 - cz 3 = PowerSeries.X * cz 3 ^ 3 := by
    linear_combination (-(cz 3)) * cz_eq 3
  rw [frob 3 (cz 3)] at key
  have h := congrArg (PowerSeries.coeff (j + 1)) key
  rw [map_sub, cz_sq_coeff, cz_coeff, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand,
    cz_coeff] at h
  exact h

open OMA.S_oeis_a395839 in
lemma cat2 (j : ℕ) : (catalan (j + 1) : ZMod 2)
    = if 2 ∣ j then (catalan (j / 2) : ZMod 2) else 0 := by
  have hf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := cz_eq 2
  rw [frob 2 (cz 2)] at key
  have h := congrArg (PowerSeries.coeff (j + 1)) key
  rw [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_one, if_neg (by omega), add_zero,
    PowerSeries.coeff_expand, cz_coeff, cz_coeff] at h
  exact h.symm

open OMA.S_oeis_a395839 in
lemma odd_iff (n : ℕ) : (catalan n : ZMod 2) = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      constructor
      · intro _
        exact ⟨0, by norm_num⟩
      · intro _
        simp
    | succ j =>
      rw [cat2 j]
      by_cases hj : 2 ∣ j
      · rw [if_pos hj, ih (j / 2) (by omega)]
        obtain ⟨i, rfl⟩ := hj
        rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          rw [pow_succ]
          omega
        · rintro ⟨k, hk⟩
          cases k with
          | zero =>
            rw [pow_zero] at hk
            omega
          | succ k' =>
            rw [pow_succ] at hk
            exact ⟨k', by omega⟩
      · rw [if_neg hj]
        constructor
        · intro h
          exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          exfalso
          cases k with
          | zero =>
            rw [pow_zero] at hk
            omega
          | succ k' =>
            rw [pow_succ] at hk
            omega

end A395839aux

theorem OMA.solution : type_of% @OMA.S_oeis_a395839.main := by
  constructor
  · intro n
    rw [A395839aux.coeff_formula 2 n, show (10 : ZMod 2) = 0 by decide, zero_mul, zero_sub,
      ZMod.neg_eq_self_mod_two]
    exact A395839aux.odd_iff n
  · intro n
    have h10 : (10 : ZMod 3) = 1 := by decide
    refine ⟨?_, ?_, ?_⟩
    · rw [A395839aux.coeff_formula 3 (3 * n + 1), h10, one_mul]
      have h := A395839aux.cat3 (3 * n)
      rw [if_pos (Dvd.intro n rfl), Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at h
      exact h
    · rw [A395839aux.coeff_formula 3 (3 * n), h10, one_mul]
      cases n with
      | zero => simp
      | succ m =>
        have h := A395839aux.cat3 (3 * m + 2)
        rw [if_neg (by omega)] at h
        rw [show 3 * (m + 1) + 1 = 3 * m + 2 + 2 by ring,
          show 3 * (m + 1) = 3 * m + 2 + 1 by ring]
        exact h
    · rw [A395839aux.coeff_formula 3 (3 * n + 2), h10, one_mul]
      have h := A395839aux.cat3 (3 * n + 1)
      rw [if_neg (by omega)] at h
      exact h
