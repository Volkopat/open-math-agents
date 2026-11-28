import OMAStatements.S_oeis_a380711
import Mathlib

open OMA.S_oeis_a380711
open PowerSeries

namespace P380711

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
  have h1 : (map φ A) ^ 3 * map φ B = 1 := by rw [← map_pow, ← map_mul, hB, map_one]
  have h2 : map φ A = 1 + X * map φ A * map φ B := by
    conv_lhs => rw [hA]
    rw [map_add, map_mul, map_mul, map_abs, map_one, map_X]
  linear_combination (map φ A) ^ 2 * h2 + X * h1

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

theorem modZ (A : PowerSeries ℤ) (h : IsGF A) : map φ A = Z := by
  have h0 : constantCoeff (map φ A) = 1 := by
    obtain ⟨B, _, hA⟩ := h
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hA]
    simp
  exact uniq _ (cube_rel A h) h0

theorem luc (n k : ℕ) :
    (n.choose k : ZMod 2) = ((n % 2).choose (k % 2) : ZMod 2) * ((n / 2).choose (k / 2) : ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (p := 2) (n := n) (k := k)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  push_cast at h
  exact h

theorem luc' (a b r s : ℕ) (hr : r < 2) (hs : s < 2) :
    ((2 * a + r).choose (2 * b + s) : ZMod 2) = (r.choose s : ZMod 2) * (a.choose b : ZMod 2) := by
  rw [luc, show (2 * a + r) % 2 = r by omega, show (2 * b + s) % 2 = s by omega,
    show (2 * a + r) / 2 = a by omega, show (2 * b + s) / 2 = b by omega]

open Classical in
theorem T1 (k : ℕ) : ((3 * k).choose k : ZMod 2) = if Fibbinary k then 1 else 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
    · rcases j with _ | j
      · rw [if_pos (by intro i; simp)]; simp
      · rw [show 3 * (2 * (j + 1)) = 2 * (3 * (j + 1)) + 0 by ring,
          show 2 * (j + 1) = 2 * (j + 1) + 0 by ring, luc' _ _ _ _ (by norm_num) (by norm_num),
          ih (j + 1) (by omega), add_zero, fib_even]
        simp
    · rw [show 3 * (2 * j + 1) = 2 * (3 * j + 1) + 1 by ring,
        luc' _ _ _ _ (by norm_num) (by norm_num), fib_odd]
      obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
      · rw [show 3 * (2 * i) + 1 = 2 * (3 * i) + 1 by ring, show 2 * i = 2 * i + 0 by ring,
          luc' _ _ _ _ (by norm_num) (by norm_num), ih i (by omega), add_zero, fib_even]
        simp
      · rw [show 3 * (2 * i + 1) + 1 = 2 * (3 * i + 2) + 0 by ring,
          luc' _ _ _ _ (by norm_num) (by norm_num)]
        have : ¬ Even (2 * i + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one i
        simp [this]

open Classical in
theorem T2 (m : ℕ) : ((3 * m + 1).choose m : ZMod 2) = coeff (m + 1) Z := by
  rw [coeff_Z]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
  · rw [if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ two_pos,
      show 3 * (2 * k) + 1 = 2 * (3 * k) + 1 by ring, show 2 * k = 2 * k + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num), T1]
    simp
  · rw [if_neg (show ¬ 2 ∣ 2 * k + 1 by omega),
      show 3 * (2 * k + 1) + 1 = 2 * (3 * k + 2) + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp

/-- `q m = binomial(3m+2, m+1)/(3m+2)`, written without division. -/
def q (m : ℕ) : ℤ := ((3 * m + 1).choose m : ℤ) - 2 * (if m = 0 then 0 else ((3 * m + 1).choose (m - 1) : ℤ))

theorem q_mul (m : ℕ) : ((3 * m + 2 : ℕ) : ℤ) * q m = ((3 * m + 2).choose (m + 1) : ℤ) := by
  have key : ((m + 1 : ℕ) : ℤ) * q m = ((3 * m + 1).choose m : ℤ) := by
    rcases m with _ | k
    · simp [q]
    · simp only [q, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
      have h := Nat.choose_succ_right_eq (3 * (k + 1) + 1) k
      rw [show 3 * (k + 1) + 1 - k = 2 * k + 4 by omega] at h
      have h' : ((3 * (k + 1) + 1).choose (k + 1) : ℤ) * (k + 1) =
          ((3 * (k + 1) + 1).choose k : ℤ) * (2 * k + 4) := by exact_mod_cast h
      push_cast
      linear_combination h'
  have h2 := Nat.add_one_mul_choose_eq (3 * m + 1) m
  have h2' : ((3 * m + 1 + 1 : ℕ) : ℤ) * ((3 * m + 1).choose m : ℤ) =
      ((3 * m + 1 + 1).choose (m + 1) : ℤ) * ((m + 1 : ℕ) : ℤ) := by exact_mod_cast h2
  have hm : ((m + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm
  rw [← key] at h2'
  rw [show 3 * m + 2 = 3 * m + 1 + 1 by ring]
  linear_combination h2'

theorem conj1 (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) :
    coeff n A ≡ ((3 * n - 1).choose n : ℤ) / ((3 * n : ℤ) - 1) [ZMOD 2] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
  have hc : ((coeff n A : ℤ) : ZMod 2) = coeff n (map φ A) := by rw [coeff_map]; rfl
  rw [hc, modZ A h]
  rcases n with _ | m
  · simp [Z]
  · have hq : ((3 * (m + 1) - 1).choose (m + 1) : ℤ) / ((3 * ((m + 1 : ℕ) : ℤ)) - 1) = q m := by
      rw [show 3 * (m + 1) - 1 = 3 * m + 2 by omega, ← q_mul m]
      push_cast
      rw [show (3 * ((m : ℤ) + 1) - 1) = 3 * (m : ℤ) + 2 by ring]
      exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [hq, ← T2, q]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide]
    ring

def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 2), (if (i : ℕ) = 0 then 1 else -|b (i - 1)|) *
      ∑ j : Fin (n + 2 - i), (if (j : ℕ) = 0 then 1 else -|b (j - 1)|) *
        (if n + 1 - i - j = 0 then 1 else -|b (n + 1 - i - j - 1)|)
decreasing_by all_goals omega

noncomputable def U : PowerSeries ℤ := 1 - X * absPS (PowerSeries.mk b)

theorem coeff_U (k : ℕ) : coeff k U = if k = 0 then 1 else -|b (k - 1)| := by
  rcases k with _ | k
  · simp [U]
  · simp [U, absPS, coeff_succ_X_mul]

theorem D_eq : PowerSeries.mk b = U ^ 3 := by
  ext n
  rcases n with _ | n
  · simp [b, U]
  · rw [coeff_mk, b, pow_succ', coeff_mul, Fin.sum_univ_eq_sum_range (fun i =>
      (if i = 0 then 1 else -|b (i - 1)|) * ∑ j : Fin (n + 2 - i), (if (j : ℕ) = 0 then 1 else
        -|b (j - 1)|) * (if n + 1 - i - j = 0 then 1 else -|b (n + 1 - i - j - 1)|)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [coeff_U, pow_two, coeff_mul, Fin.sum_univ_eq_sum_range (fun j =>
      (if j = 0 then 1 else -|b (j - 1)|) * (if n + 1 - i - j = 0 then 1 else
        -|b (n + 1 - i - j - 1)|)), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      show n + 2 - i = n + 1 - i + 1 by omega]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_U, coeff_U]

theorem exists_gf : ∃ A, IsGF A := by
  have hc : constantCoeff U = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_U]; simp
  set A := invOfUnit U 1 with hAdef
  have hAU : A * U = 1 := by
    rw [mul_comm]; exact mul_invOfUnit U 1 (by rw [hc]; rfl)
  refine ⟨A, PowerSeries.mk b, ?_, ?_⟩
  · rw [D_eq, ← mul_pow, hAU, one_pow]
  · have : A * (1 - X * absPS (PowerSeries.mk b)) = 1 := hAU
    linear_combination this

end P380711

theorem OMA.solution : type_of% @OMA.S_oeis_a380711.main :=
  ⟨P380711.exists_gf, fun A h => ⟨fun n => P380711.conj1 A h n, fun n hn => P380711.parity A h n hn⟩⟩
