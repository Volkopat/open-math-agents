import OMAStatements.S_oeis_a380708
import Mathlib

open OMA.S_oeis_a380708
open PowerSeries

namespace P380708

open Finset

theorem sym (f : ℕ → ZMod 2) (m : ℕ) :
    ∑ p ∈ antidiagonal m, f p.1 * f p.2 = if Even m then f (m / 2) * f (m / 2) else 0 := by
  have key : ∀ s : Finset (ℕ × ℕ), (∀ p ∈ s, p.1 ≠ p.2) → (∀ p ∈ s, p.swap ∈ s) →
      ∑ p ∈ s, f p.1 * f p.2 = 0 := by
    intro s hne hsw
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p hp => hsw p hp) ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm (f p.2)]
      exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      apply hne p hp
      have := congrArg Prod.fst h
      simpa using this.symm
    · intro p _; simp
  split_ifs with he
  · obtain ⟨k, rfl⟩ := he
    have hk : (k + k) / 2 = k := by omega
    rw [hk]
    have hmem : (k, k) ∈ antidiagonal (k + k) := by simp
    rw [← Finset.add_sum_erase _ _ hmem]
    rw [key, add_zero]
    · intro p hp
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      intro h
      apply hp.1
      ext <;> simp <;> omega
    · intro p hp
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      refine ⟨?_, by simp; omega⟩
      intro h
      apply hp.1
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp at h1 h2
      ext <;> simp <;> omega
  · apply key
    · intro p hp h
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      apply he
      exact ⟨p.1, by omega⟩
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp; omega

theorem fib_iff (n : ℕ) : Fibbinary n ↔
    ¬ (n.testBit 0 = true ∧ n.testBit 1 = true) ∧ Fibbinary (n / 2) := by
  unfold Fibbinary
  constructor
  · intro H
    refine ⟨H 0, fun i => ?_⟩
    have := H (i + 1)
    rwa [Nat.testBit_add_one, Nat.testBit_add_one n (i + 1)] at this
  · rintro ⟨H0, H⟩ i
    rcases i with _ | i
    · exact H0
    · rw [Nat.testBit_add_one, Nat.testBit_add_one n (i + 1)]
      exact H i

theorem fib_even (k : ℕ) : Fibbinary (2 * k) ↔ Fibbinary k := by
  rw [fib_iff, Nat.mul_div_cancel_left _ (by norm_num), Nat.testBit_zero]
  simp

theorem fib_odd (k : ℕ) : Fibbinary (2 * k + 1) ↔ Even k ∧ Fibbinary k := by
  rw [fib_iff, show (2 * k + 1) / 2 = k by omega, Nat.testBit_zero, Nat.testBit_add_one,
    show (2 * k + 1) / 2 = k by omega, Nat.testBit_zero]
  simp only [decide_eq_true_eq, Nat.even_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

abbrev φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

theorem two_eq_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  rw [← map_ofNat (C (R := ZMod 2)) 2, show (OfNat.ofNat 2 : ZMod 2) = 0 by decide, map_zero]

theorem map_abs (F : PowerSeries ℤ) : map φ (absPS F) = map φ F := by
  ext n
  simp only [coeff_map, absPS, coeff_mk]
  rcases abs_choice (coeff n F) with h | h <;> rw [h]
  simp [ZMod.neg_eq_self_mod_two]

theorem cube_rel (A : PowerSeries ℤ) (h : IsGF A) :
    (map φ A) ^ 3 = (map φ A) ^ 2 + X := by
  obtain ⟨B, hB, hA⟩ := h
  have h1 : map φ A * map φ B = 1 := by rw [← map_mul, hB, map_one]
  have h2 : map φ A = 1 + X * (map φ B) ^ 2 := by
    conv_lhs => rw [hA]
    rw [map_add, map_mul, map_pow, map_abs, map_one, map_X]
  linear_combination (map φ A) ^ 2 * h2 + X * (map φ A * map φ B + 1) * h1

theorem frob (F : PowerSeries (ZMod 2)) : F ^ 2 = expand 2 two_ne_zero F := by
  ext n
  rw [pow_two, coeff_mul, sym (fun i => coeff i F) n, coeff_expand]
  have hx : ∀ x : ZMod 2, x * x = x := by decide
  simp only [hx, even_iff_two_dvd]

open Classical in
noncomputable def V : PowerSeries (ZMod 2) := PowerSeries.mk fun k => if Fibbinary k then 1 else 0

open Classical in
theorem coeff_V (k : ℕ) : coeff k V = if Fibbinary k then 1 else 0 := by
  rw [V, coeff_mk]

theorem V_rec : V = expand 2 two_ne_zero V + X * expand 2 two_ne_zero (expand 2 two_ne_zero V) := by
  ext n
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · rw [map_add, coeff_expand, if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ two_pos,
      coeff_V, coeff_V, fib_even]
    rcases k with _ | k
    · simp
    · rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, coeff_succ_X_mul, coeff_expand,
        if_neg (show ¬ 2 ∣ 2 * k + 1 by omega)]
      simp
  · rw [map_add, coeff_expand, if_neg (show ¬ 2 ∣ 2 * k + 1 by omega), coeff_succ_X_mul,
      coeff_expand, if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ two_pos, coeff_expand,
      coeff_V, fib_odd]
    obtain ⟨m, rfl | rfl⟩ : ∃ m, k = 2 * m ∨ k = 2 * m + 1 := ⟨k / 2, by omega⟩
    · rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left _ two_pos, coeff_V, fib_even, zero_add]
      by_cases hf : Fibbinary m
      · rw [if_pos ⟨even_two_mul m, hf⟩, if_pos hf]
      · rw [if_neg (fun h => hf h.2), if_neg hf]
    · rw [if_neg (show ¬ 2 ∣ 2 * m + 1 by omega)]
      have : ¬ Even (2 * m + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m
      simp [this]

theorem V_const : constantCoeff V = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_V, if_pos]
  intro i; simp

theorem V_eq : V + X * V ^ 3 = 1 := by
  have hV : V = V ^ 2 + X * V ^ 4 := by
    conv_lhs => rw [V_rec]
    rw [frob, show V ^ 4 = (V ^ 2) ^ 2 by ring, frob, frob]
  have h0 : V * (V + X * V ^ 3 - 1) = 0 := by linear_combination (-1 : PowerSeries (ZMod 2)) * hV
  have hu : IsUnit V := by
    rw [PowerSeries.isUnit_iff_constantCoeff, V_const]; exact isUnit_one
  have := (hu.mul_right_eq_zero).mp h0
  exact sub_eq_zero.mp this

noncomputable def Z : PowerSeries (ZMod 2) := 1 + X * expand 2 two_ne_zero V

theorem Z_rel : Z ^ 3 = Z ^ 2 + X := by
  have he : expand 2 two_ne_zero V + X ^ 2 * (expand 2 two_ne_zero V) ^ 3 = 1 := by
    have := congrArg (expand 2 two_ne_zero) V_eq
    simpa only [map_add, map_mul, map_pow, expand_X, map_one] using this
  unfold Z
  linear_combination X * he + X ^ 2 * (expand 2 two_ne_zero V) ^ 2 * two_eq_zero

theorem uniq (W : PowerSeries (ZMod 2)) (hW : W ^ 3 = W ^ 2 + X) (h0 : constantCoeff W = 1) :
    W = Z := by
  have hZ := Z_rel
  have hZ0 : constantCoeff Z = 1 := by simp [Z]
  set Q := W ^ 2 + W * Z + Z ^ 2 - W - Z with hQ
  have hprod : (W - Z) * Q = 0 := by rw [hQ]; linear_combination hW - hZ
  have hu : IsUnit Q := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hQ]
    simp only [map_sub, map_add, map_mul, map_pow, h0, hZ0]
    decide
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hprod)

open Classical in
theorem coeff_Z (m : ℕ) :
    coeff (m + 1) Z = if 2 ∣ m then (if Fibbinary (m / 2) then 1 else 0) else 0 := by
  rw [Z, map_add, coeff_succ_X_mul, coeff_expand, coeff_one, if_neg (by omega), zero_add]
  split_ifs <;> simp_all [coeff_V]

theorem parity (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) (hn : 0 < n) :
    Odd (coeff n A) ↔ ∃ k : ℕ, Fibbinary k ∧ n = 2 * k + 1 := by
  have h0 : constantCoeff (map φ A) = 1 := by
    obtain ⟨B, _, hA⟩ := h
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hA]
    simp
  have hAZ := uniq _ (cube_rel A h) h0
  have hc : ((coeff n A : ℤ) : ZMod 2) = coeff n (map φ A) := by rw [coeff_map]; rfl
  rw [← ZMod.intCast_eq_one_iff_odd, hc, hAZ]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coeff_Z]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
  · rw [if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ (by norm_num)]
    constructor
    · intro h1
      refine ⟨k, ?_, rfl⟩
      by_contra hf
      rw [if_neg hf] at h1
      exact zero_ne_one h1
    · rintro ⟨k', hk', hkk⟩
      have : k' = k := by omega
      subst this
      rw [if_pos hk']
  · rw [if_neg (show ¬ 2 ∣ 2 * k + 1 by omega)]
    simp only [zero_ne_one, false_iff, not_exists, not_and]
    intro k' _ hk'
    omega

def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ i : Fin (n + 1), b i * ∑ j : Fin (n - i + 1), |b j| * |b (n - i - j)|
decreasing_by all_goals omega

theorem D_eq : PowerSeries.mk b = 1 - X * PowerSeries.mk b * (absPS (PowerSeries.mk b)) ^ 2 := by
  ext n
  rcases n with _ | n
  · simp [b]
  · rw [map_sub, mul_assoc, coeff_succ_X_mul, coeff_one, if_neg (by omega), zero_sub, coeff_mul,
      coeff_mk, b, Fin.sum_univ_eq_sum_range (fun i => b i * ∑ j : Fin (n - i + 1),
        |b j| * |b (n - i - j)|), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_mk, pow_two, coeff_mul, Fin.sum_univ_eq_sum_range (fun j => |b j| * |b (n - i - j)|),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [absPS]

theorem exists_gf : ∃ A, IsGF A := by
  have hc : constantCoeff (PowerSeries.mk b) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; simp [b]
  set A := invOfUnit (PowerSeries.mk b) 1 with hAdef
  have hAD : A * PowerSeries.mk b = 1 := by
    rw [mul_comm]; exact mul_invOfUnit (PowerSeries.mk b) 1 (by rw [hc]; rfl)
  refine ⟨A, PowerSeries.mk b, hAD, ?_⟩
  have := congrArg (A * ·) D_eq
  linear_combination -this + (1 + X * (absPS (PowerSeries.mk b)) ^ 2) * hAD

end P380708

theorem OMA.solution : type_of% @OMA.S_oeis_a380708.main :=
  ⟨P380708.exists_gf, fun A h n hn => P380708.parity A h n hn⟩
