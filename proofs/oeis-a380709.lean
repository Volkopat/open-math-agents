import OMAStatements.S_oeis_a380709
import Mathlib

open OMA.S_oeis_a380709
open PowerSeries

namespace P380709

open Finset

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

abbrev φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

theorem two_eq_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  rw [← map_ofNat (C (R := ZMod 2)) 2, show (OfNat.ofNat 2 : ZMod 2) = 0 by decide, map_zero]

theorem map_abs (F : PowerSeries ℤ) : map φ (absPS F) = map φ F := by
  ext n
  simp only [coeff_map, absPS, coeff_mk]
  rcases abs_choice (coeff n F) with h | h <;> rw [h]
  simp [ZMod.neg_eq_self_mod_two]

theorem frob (F : PowerSeries (ZMod 2)) : F ^ 2 = expand 2 two_ne_zero F := by
  ext n
  rw [pow_two, coeff_mul, sym (fun i => coeff i F) n, coeff_expand]
  have hx : ∀ x : ZMod 2, x * x = x := by decide
  simp only [hx, even_iff_two_dvd]

theorem split (F F0 F1 : PowerSeries (ZMod 2)) (h0 : ∀ m, coeff (2 * m) F = coeff m F0)
    (h1 : ∀ m, coeff (2 * m + 1) F = coeff m F1) :
    F = F0 ^ 2 + X * F1 ^ 2 := by
  rw [frob, frob]
  ext n
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · rw [map_add, coeff_expand, if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ two_pos, h0]
    rcases k with _ | k
    · simp
    · rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, coeff_succ_X_mul, coeff_expand,
        if_neg (show ¬ 2 ∣ 2 * k + 1 by omega)]
      simp
  · rw [map_add, coeff_expand, if_neg (show ¬ 2 ∣ 2 * k + 1 by omega), coeff_succ_X_mul,
      coeff_expand, if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ two_pos, h1, zero_add]

noncomputable def Cs : PowerSeries (ZMod 2) := PowerSeries.mk fun n => ((4 * n - 1).choose n : ZMod 2)
noncomputable def Ds : PowerSeries (ZMod 2) := PowerSeries.mk fun n => ((4 * n + 1).choose n : ZMod 2)
noncomputable def Es : PowerSeries (ZMod 2) := PowerSeries.mk fun n => ((4 * n).choose n : ZMod 2)
noncomputable def Gs : PowerSeries (ZMod 2) := PowerSeries.mk fun n => ((4 * n + 2).choose n : ZMod 2)

theorem Cs_split : Cs = Cs ^ 2 + X * Ds ^ 2 := by
  apply split
  · intro m
    rcases m with _ | m
    · simp [Cs]
    · simp only [Cs, coeff_mk]
      rw [show 4 * (2 * (m + 1)) - 1 = 2 * (4 * m + 3) + 1 by omega,
        show 2 * (m + 1) = 2 * (m + 1) + 0 by ring, luc' _ _ _ _ (by norm_num) (by norm_num),
        show 4 * (m + 1) - 1 = 4 * m + 3 by omega]
      simp
  · intro m
    simp only [Cs, Ds, coeff_mk]
    rw [show 4 * (2 * m + 1) - 1 = 2 * (4 * m + 1) + 1 by omega,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp

theorem Ds_split : Ds = Es ^ 2 + X * Gs ^ 2 := by
  apply split
  · intro m
    simp only [Ds, Es, coeff_mk]
    rw [show 4 * (2 * m) + 1 = 2 * (4 * m) + 1 by ring, show 2 * m = 2 * m + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp
  · intro m
    simp only [Ds, Gs, coeff_mk]
    rw [show 4 * (2 * m + 1) + 1 = 2 * (4 * m + 2) + 1 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp

theorem Es_split : Es = Es ^ 2 + X * 0 ^ 2 := by
  apply split
  · intro m
    simp only [Es, coeff_mk]
    rw [show 4 * (2 * m) = 2 * (4 * m) + 0 by ring, show 2 * m = 2 * m + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp
  · intro m
    simp only [Es, coeff_mk, map_zero]
    rw [show 4 * (2 * m + 1) = 2 * (4 * m + 2) + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp

theorem Gs_split : Gs = Ds ^ 2 + X * 0 ^ 2 := by
  apply split
  · intro m
    simp only [Ds, Gs, coeff_mk]
    rw [show 4 * (2 * m) + 2 = 2 * (4 * m + 1) + 0 by ring, show 2 * m = 2 * m + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp
  · intro m
    simp only [Gs, coeff_mk, map_zero]
    rw [show 4 * (2 * m + 1) + 2 = 2 * (4 * m + 3) + 0 by ring,
      luc' _ _ _ _ (by norm_num) (by norm_num)]
    simp

theorem Es_one : Es = 1 := by
  have h := Es_split
  have hu : IsUnit Es := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply]
    simp [Es]
  have h0 : Es * (Es - 1) = 0 := by linear_combination (-1 : PowerSeries (ZMod 2)) * h
  exact sub_eq_zero.mp ((hu.mul_right_eq_zero).mp h0)

theorem Ds_eq : Ds = 1 + X * Ds ^ 4 := by
  have h := Ds_split
  rw [Es_one, Gs_split] at h
  linear_combination h


theorem Cs_const : constantCoeff Cs = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [Cs]

theorem Ds_const : constantCoeff Ds = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [Ds]

theorem CD : Cs * Ds = 1 := by
  have hC := Cs_split
  have hD := Ds_eq
  set P := Cs * Ds with hP
  have h : (P - 1) * (Ds - P - 1) = 0 := by
    rw [hP]
    linear_combination Ds ^ 2 * hC - hD
  have hu : IsUnit (Ds - P - 1) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hP]
    simp only [map_sub, map_mul, map_one, Cs_const, Ds_const]
    decide
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp h)

theorem uniqD (U : PowerSeries (ZMod 2)) (hU : U = 1 + X * U ^ 4) : U = Ds := by
  have hD := Ds_eq
  have h : (U - Ds) * (1 - X * (U ^ 3 + U ^ 2 * Ds + U * Ds ^ 2 + Ds ^ 3)) = 0 := by
    linear_combination hU - hD
  have hu : IsUnit (1 - X * (U ^ 3 + U ^ 2 * Ds + U * Ds ^ 2 + Ds ^ 3)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp h)

theorem modA (A : PowerSeries ℤ) (h : IsGF A) : map φ A = Cs := by
  obtain ⟨B, hB, hA⟩ := h
  have h1 : map φ A * map φ B = 1 := by rw [← map_mul, hB, map_one]
  have h2 : map φ A = 1 + X * (map φ B) ^ 3 := by
    conv_lhs => rw [hA]
    rw [map_add, map_mul, map_pow, map_abs, map_one, map_X]
  have h3 : map φ B = 1 + X * (map φ B) ^ 4 := by
    linear_combination (-(map φ B)) * h2 + h1 - X * (map φ B) ^ 4 * two_eq_zero
  have h4 := uniqD _ h3
  rw [h4] at h1
  linear_combination Cs * h1 - (map φ A) * CD

theorem parity (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) :
    coeff n A ≡ ((4 * n - 1).choose n : ℤ) [ZMOD 2] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
  have hc : ((coeff n A : ℤ) : ZMod 2) = coeff n (map φ A) := by rw [coeff_map]; rfl
  rw [hc, modA A h, Cs, coeff_mk]
  push_cast
  rfl

def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ i : Fin (n + 1), b i * ∑ j : Fin (n - i + 1), |b j| *
      ∑ l : Fin (n - i - j + 1), |b l| * |b (n - i - j - l)|
decreasing_by all_goals omega

theorem D_eq : PowerSeries.mk b = 1 - X * PowerSeries.mk b * (absPS (PowerSeries.mk b)) ^ 3 := by
  ext n
  rcases n with _ | n
  · simp [b]
  · rw [map_sub, mul_assoc, coeff_succ_X_mul, coeff_one, if_neg (by omega), zero_sub, coeff_mul,
      coeff_mk, b, Fin.sum_univ_eq_sum_range (fun i => b i * ∑ j : Fin (n - i + 1), |b j| *
        ∑ l : Fin (n - i - j + 1), |b l| * |b (n - i - j - l)|),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_mk, pow_succ', coeff_mul, Fin.sum_univ_eq_sum_range (fun j => |b j| *
        ∑ l : Fin (n - i - j + 1), |b l| * |b (n - i - j - l)|),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_two, coeff_mul, Fin.sum_univ_eq_sum_range (fun l => |b l| * |b (n - i - j - l)|),
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
  linear_combination -this + (1 + X * (absPS (PowerSeries.mk b)) ^ 3) * hAD

end P380709

theorem OMA.solution : type_of% @OMA.S_oeis_a380709.main :=
  ⟨P380709.exists_gf, fun A h n => P380709.parity A h n⟩
