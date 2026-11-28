import OMAStatements.S_oeis_a211435
import Mathlib

/-!
Credit: @ivillar
Proof: w = -(4x+5y) is determined by (x, y), so a(n) counts the pairs (x, y) in [-n, n]^2 with
|4x+5y| ≤ n. For |s| ≤ n the pairs with 4x + 5y = s are (5t - s, s - 4t) with t = x + y and
s - n ≤ 5t ≤ s + n, so there are floor((n+s)/5) + floor((n-s)/5) + 1 of them. Hence
a(n) = 2n + 1 + 2*Sum_{j=0..2n} floor(j/5), so a(n+5) = a(n) + 8n + 24; this gives the recurrence
(the denominator is (1-x)^2 (1-x^5)), and with the first seven terms the g.f.
-/

namespace OMAA211435Helpers
open PowerSeries OMA.S_oeis_a211435

/-- The pairs (x, y) in [-n, n]^2 with -n ≤ 4x + 5y ≤ n. -/
noncomputable def P (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => -(n : ℤ) ≤ 4 * p.1 + 5 * p.2 ∧ 4 * p.1 + 5 * p.2 ≤ n)

theorem a_eq_P (n : ℕ) : a n = (P n).card := by
  unfold a P
  exact Finset.card_bij' (fun t _ => (t.2.1, t.2.2)) (fun p _ => (-4 * p.1 - 5 * p.2, p.1, p.2))
    (fun t ht => by
      obtain ⟨w, x, y⟩ := t
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
      omega)
    (fun p hp => by
      obtain ⟨x, y⟩ := p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega)
    (fun t ht => by
      obtain ⟨w, x, y⟩ := t
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
      exact Prod.ext (by dsimp only; omega) rfl)
    (fun p _ => rfl)

theorem fiber_card (n : ℕ) (s : ℤ) (hs1 : -(n : ℤ) ≤ s) (hs2 : s ≤ n) :
    (((P n).filter (fun p => 4 * p.1 + 5 * p.2 = s)).card : ℤ) =
      ((n : ℤ) + s) / 5 + ((n : ℤ) - s) / 5 + 1 := by
  have hc : ((P n).filter (fun p => 4 * p.1 + 5 * p.2 = s)).card =
      (Finset.Icc (-(((n : ℤ) - s) / 5)) (((n : ℤ) + s) / 5)).card := by
    exact Finset.card_bij' (fun p _ => p.1 + p.2) (fun t _ => (5 * t - s, s - 4 * t))
      (fun p hp => by
        obtain ⟨x, y⟩ := p
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
        omega)
      (fun t ht => by
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
        omega)
      (fun p hp => by
        obtain ⟨x, y⟩ := p
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega))
      (fun t _ => by dsimp only; ring)
  rw [hc, Int.card_Icc]
  omega

/-- V(n) = Sum_{j=0..2n} floor(j/5). -/
def V (n : ℕ) : ℤ := ∑ j ∈ Finset.range (2 * n + 1), ((j : ℤ) / 5)

theorem reindex_plus (n : ℕ) :
    ∑ s ∈ Finset.Icc (-(n : ℤ)) n, (((n : ℤ) + s) / 5) = V n := by
  unfold V
  exact Finset.sum_nbij' (fun s => ((n : ℤ) + s).toNat) (fun j => (j : ℤ) - n)
    (fun s hs => by simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢; omega)
    (fun j hj => by simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega)
    (fun s hs => by simp only [Finset.mem_Icc] at hs; omega)
    (fun j hj => by simp only [Finset.mem_range] at hj; omega)
    (fun s hs => by simp only [Finset.mem_Icc] at hs; rw [Int.toNat_of_nonneg (by omega)])

theorem reindex_minus (n : ℕ) :
    ∑ s ∈ Finset.Icc (-(n : ℤ)) n, (((n : ℤ) - s) / 5) = V n := by
  unfold V
  exact Finset.sum_nbij' (fun s => ((n : ℤ) - s).toNat) (fun j => (n : ℤ) - j)
    (fun s hs => by simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢; omega)
    (fun j hj => by simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega)
    (fun s hs => by simp only [Finset.mem_Icc] at hs; omega)
    (fun j hj => by simp only [Finset.mem_range] at hj; omega)
    (fun s hs => by simp only [Finset.mem_Icc] at hs; rw [Int.toNat_of_nonneg (by omega)])

theorem a_closed (n : ℕ) : (a n : ℤ) = 2 * V n + 2 * n + 1 := by
  rw [a_eq_P]
  have hmaps : ∀ p ∈ P n, 4 * p.1 + 5 * p.2 ∈ Finset.Icc (-(n : ℤ)) n := by
    rintro ⟨x, y⟩ hp
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    omega
  have hf := Finset.card_eq_sum_card_fiberwise hmaps
  have hf' : ((P n).card : ℤ) = ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
      (((P n).filter (fun p => 4 * p.1 + 5 * p.2 = s)).card : ℤ) := by
    rw [hf]
    push_cast
    rfl
  have hsum : ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
      (((P n).filter (fun p => 4 * p.1 + 5 * p.2 = s)).card : ℤ) =
      ∑ s ∈ Finset.Icc (-(n : ℤ)) n, ((((n : ℤ) + s) / 5 + ((n : ℤ) - s) / 5) + 1) :=
    Finset.sum_congr rfl (fun s hs => fiber_card n s
      (by simp only [Finset.mem_Icc] at hs; omega) (by simp only [Finset.mem_Icc] at hs; omega))
  have hcard : ((((n : ℤ) + 1 - -(n : ℤ))).toNat : ℤ) = 2 * (n : ℤ) + 1 := by omega
  rw [hf', hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, reindex_plus, reindex_minus,
    Finset.sum_const, Int.card_Icc, nsmul_eq_mul, hcard]
  ring

theorem floor_shift (M k : ℤ) : (M + k) / 5 = M / 5 + (M % 5 + k) / 5 := by
  have h : M = M % 5 + 5 * (M / 5) := (Int.emod_add_mul_ediv M 5).symm
  conv_lhs => rw [h]
  rw [show M % 5 + 5 * (M / 5) + k = (M % 5 + k) + (M / 5) * 5 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

theorem ten_floor (M : ℤ) :
    M / 5 + (M % 5 + 1) / 5 + (M % 5 + 2) / 5 + (M % 5 + 3) / 5 + (M % 5 + 4) / 5 +
      (M % 5 + 5) / 5 + (M % 5 + 6) / 5 + (M % 5 + 7) / 5 + (M % 5 + 8) / 5 +
        (M % 5 + 9) / 5 + 9 * (M / 5) = 2 * M + 5 := by
  have h := Int.emod_add_mul_ediv M 5
  have hr : M % 5 = 0 ∨ M % 5 = 1 ∨ M % 5 = 2 ∨ M % 5 = 3 ∨ M % 5 = 4 := by omega
  rcases hr with hr | hr | hr | hr | hr <;> rw [hr] at h ⊢ <;> omega

theorem V_step (n : ℕ) : V (n + 5) = V n + 4 * n + 7 := by
  unfold V
  rw [show 2 * (n + 5) + 1 = (2 * n + 1) + 10 by ring, Finset.sum_range_add]
  have key : ∑ x ∈ Finset.range 10, (((2 * n + 1 + x : ℕ) : ℤ) / 5) = 4 * n + 7 := by
    have t := ten_floor (2 * (n : ℤ) + 1)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
    push_cast
    rw [floor_shift (2 * (n : ℤ) + 1) 1, floor_shift (2 * (n : ℤ) + 1) 2,
      floor_shift (2 * (n : ℤ) + 1) 3, floor_shift (2 * (n : ℤ) + 1) 4,
      floor_shift (2 * (n : ℤ) + 1) 5, floor_shift (2 * (n : ℤ) + 1) 6,
      floor_shift (2 * (n : ℤ) + 1) 7, floor_shift (2 * (n : ℤ) + 1) 8,
      floor_shift (2 * (n : ℤ) + 1) 9]
    linarith
  rw [key]
  ring

theorem d5 (k : ℕ) : (a (k + 5) : ℤ) = a k + 8 * k + 24 := by
  rw [a_closed, a_closed, V_step]
  push_cast
  ring

theorem rec (m : ℕ) :
    (a (m + 7) : ℤ) = 2 * a (m + 6) - a (m + 5) + a (m + 2) - 2 * a (m + 1) + a m := by
  have e2 := d5 (m + 2)
  have e1 := d5 (m + 1)
  have e0 := d5 m
  rw [show m + 2 + 5 = m + 7 by ring] at e2
  rw [show m + 1 + 5 = m + 6 by ring] at e1
  push_cast at e2 e1 e0
  linarith

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℤ) (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℤ) (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at f n k j h]

end OMAA211435Helpers

open PowerSeries OMAA211435Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a211435.main := by
  have hrec : ∀ n : ℕ, 6 < n → (OMA.S_oeis_a211435.a n : ℤ) =
      2 * OMA.S_oeis_a211435.a (n - 1) - OMA.S_oeis_a211435.a (n - 2) +
        OMA.S_oeis_a211435.a (n - 5) - 2 * OMA.S_oeis_a211435.a (n - 6) +
          OMA.S_oeis_a211435.a (n - 7) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega,
      show k + 7 - 7 = k by omega]
    exact rec k
  refine ⟨?_, hrec⟩
  set f : ℕ → ℤ := fun n => (OMA.S_oeis_a211435.a n : ℤ) with hfdef
  ext n
  have hD : ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      X ^ 0 - C 2 * X ^ 1 + X ^ 2 - X ^ 5 + C 2 * X ^ 6 - X ^ 7 := by
    rw [map_ofNat C 2]; ring
  have hN : (1 + X + 4 * X ^ 3 + X ^ 5 + X ^ 6 : PowerSeries ℤ) =
      X ^ 0 + X ^ 1 + C 4 * X ^ 3 + X ^ 5 + X ^ 6 := by
    rw [map_ofNat C 4]; ring
  rw [hD, hN]
  have v0 : f 0 = 1 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  have v1 : f 1 = 3 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  have v2 : f 2 = 5 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  have v3 : f 3 = 11 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  have v4 : f 4 = 17 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  have v5 : f 5 = 25 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  have v6 : f 6 = 35 := by simp only [hfdef, a_closed, V]; norm_num [Finset.sum_range_succ]
  rcases Nat.lt_or_ge n 7 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v1, v2, v3]
    · norm_num [v2, v3, v4]
    · norm_num [v0, v3, v4, v5]
    · norm_num [v0, v1, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at f (m + 7) 0 (m + 7) (by omega), coeff_at_C f 2 (m + 7) 1 (m + 6) (by omega),
      coeff_at f (m + 7) 2 (m + 5) (by omega), coeff_at f (m + 7) 5 (m + 2) (by omega),
      coeff_at_C f 2 (m + 7) 6 (m + 1) (by omega), coeff_at f (m + 7) 7 m (by omega),
      coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    have hr := rec m
    simp only [hfdef]
    linear_combination hr
