import OMAStatements.S_oeis_a211439
import Mathlib

/-!
Credit: @ivillar
Proof: w = -3(x+y) is determined by (x, y), so a(n) counts the pairs (x, y) in [-n, n]^2 with
|3(x+y)| ≤ n, i.e. |x+y| ≤ m with m = floor(n/3). The pairs with x + y = s (|s| ≤ m ≤ n) number
2n + 1 - |s|, so a(n) = (2m+1)(2n+1) - m(m+1). Along steps of 3 in n (and 1 in m) the second
difference of this quadratic is the constant 22, which gives Barker's recurrence; with the first
seven terms it gives the g.f.
-/

namespace OMAA211439Helpers
open PowerSeries OMA.S_oeis_a211439

/-- The pairs (x, y) in [-n, n]^2 with -n ≤ 3(x+y) ≤ n. -/
noncomputable def P (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => -(n : ℤ) ≤ 3 * (p.1 + p.2) ∧ 3 * (p.1 + p.2) ≤ n)

theorem a_eq_P (n : ℕ) : a n = (P n).card := by
  unfold a P
  exact Finset.card_bij' (fun t _ => (t.2.1, t.2.2)) (fun p _ => (-3 * (p.1 + p.2), p.1, p.2))
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

theorem fiber_card (n : ℕ) (s : ℤ) (hs1 : -(n : ℤ) ≤ 3 * s) (hs2 : 3 * s ≤ n) :
    (((P n).filter (fun p => p.1 + p.2 = s)).card : ℤ) = 2 * n + 1 - |s| := by
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h]
    have hc : ((P n).filter (fun p => p.1 + p.2 = s)).card = (Finset.Icc (s - n) n).card := by
      exact Finset.card_bij' (fun p _ => p.1) (fun x _ => (x, s - x))
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
          omega)
        (fun x hx => by
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx ⊢
          omega)
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
          exact Prod.ext rfl (by dsimp only; omega))
        (fun x _ => rfl)
    rw [hc, Int.card_Icc]
    omega
  · rw [abs_of_neg h]
    have hc : ((P n).filter (fun p => p.1 + p.2 = s)).card = (Finset.Icc (-(n : ℤ)) (s + n)).card := by
      exact Finset.card_bij' (fun p _ => p.1) (fun x _ => (x, s - x))
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
          omega)
        (fun x hx => by
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx ⊢
          omega)
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
          exact Prod.ext rfl (by dsimp only; omega))
        (fun x _ => rfl)
    rw [hc, Int.card_Icc]
    omega

theorem sum_abs (N : ℤ) (m : ℕ) :
    ∑ s ∈ Finset.Icc (-(m : ℤ)) m, (N - |s|) = (2 * (m : ℤ) + 1) * N - m * ((m : ℤ) + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hI : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k : ℤ) + 1)) (insert ((k : ℤ) + 1) (Finset.Icc (-(k : ℤ)) k)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      abs_of_neg (by omega), abs_of_pos (by omega)]
    push_cast
    ring

theorem a_closed (n : ℕ) :
    (a n : ℤ) = (2 * ((n / 3 : ℕ) : ℤ) + 1) * (2 * n + 1) - ((n / 3 : ℕ) : ℤ) * ((n / 3 : ℕ) + 1) := by
  rw [a_eq_P]
  have hmaps : ∀ p ∈ P n, p.1 + p.2 ∈ Finset.Icc (-((n / 3 : ℕ) : ℤ)) ((n / 3 : ℕ) : ℤ) := by
    rintro ⟨x, y⟩ hp
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    omega
  have hf := Finset.card_eq_sum_card_fiberwise hmaps
  have hf' : ((P n).card : ℤ) = ∑ s ∈ Finset.Icc (-((n / 3 : ℕ) : ℤ)) ((n / 3 : ℕ) : ℤ),
      (((P n).filter (fun p => p.1 + p.2 = s)).card : ℤ) := by
    rw [hf]
    push_cast
    rfl
  have hsum : ∑ s ∈ Finset.Icc (-((n / 3 : ℕ) : ℤ)) ((n / 3 : ℕ) : ℤ),
      (((P n).filter (fun p => p.1 + p.2 = s)).card : ℤ) =
      ∑ s ∈ Finset.Icc (-((n / 3 : ℕ) : ℤ)) ((n / 3 : ℕ) : ℤ), ((2 * (n : ℤ) + 1) - |s|) :=
    Finset.sum_congr rfl (fun s hs => fiber_card n s
      (by simp only [Finset.mem_Icc] at hs; omega) (by simp only [Finset.mem_Icc] at hs; omega))
  rw [hf', hsum, sum_abs]

theorem rec (k : ℕ) :
    (a (k + 7) : ℤ) = a (k + 6) + 2 * a (k + 4) - 2 * a (k + 3) - a (k + 1) + a k := by
  rw [a_closed, a_closed, a_closed, a_closed, a_closed, a_closed]
  have d4 : (((k + 4) / 3 : ℕ) : ℤ) = (((k + 7) / 3 : ℕ) : ℤ) - 1 := by omega
  have d1 : (((k + 1) / 3 : ℕ) : ℤ) = (((k + 7) / 3 : ℕ) : ℤ) - 2 := by omega
  have d3 : (((k + 3) / 3 : ℕ) : ℤ) = (((k + 6) / 3 : ℕ) : ℤ) - 1 := by omega
  have d0 : ((k / 3 : ℕ) : ℤ) = (((k + 6) / 3 : ℕ) : ℤ) - 2 := by omega
  rw [d4, d1, d3, d0]
  push_cast
  ring

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

end OMAA211439Helpers

open PowerSeries OMAA211439Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a211439.main := by
  have hrec : ∀ n : ℕ, 6 < n → (OMA.S_oeis_a211439.a n : ℤ) =
      OMA.S_oeis_a211439.a (n - 1) + 2 * OMA.S_oeis_a211439.a (n - 3) -
        2 * OMA.S_oeis_a211439.a (n - 4) - OMA.S_oeis_a211439.a (n - 6) +
          OMA.S_oeis_a211439.a (n - 7) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 3 = k + 4 by omega,
      show k + 7 - 4 = k + 3 by omega, show k + 7 - 6 = k + 1 by omega,
      show k + 7 - 7 = k by omega]
    exact rec k
  refine ⟨?_, hrec⟩
  set f : ℕ → ℤ := fun n => (OMA.S_oeis_a211439.a n : ℤ) with hfdef
  ext n
  have hD : ((1 - X) ^ 3 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℤ) =
      X ^ 0 - X ^ 1 - C 2 * X ^ 3 + C 2 * X ^ 4 + X ^ 6 - X ^ 7 := by
    rw [map_ofNat C 2]; ring
  have hN : (1 + 2 * X + 2 * X ^ 2 + 12 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 : PowerSeries ℤ) =
      X ^ 0 + C 2 * X ^ 1 + C 2 * X ^ 2 + C 12 * X ^ 3 + C 2 * X ^ 4 + C 2 * X ^ 5 + X ^ 6 := by
    rw [map_ofNat C 2, map_ofNat C 12]; ring
  rw [hD, hN]
  have v0 : f 0 = 1 := by simp only [hfdef, a_closed]; norm_num
  have v1 : f 1 = 3 := by simp only [hfdef, a_closed]; norm_num
  have v2 : f 2 = 5 := by simp only [hfdef, a_closed]; norm_num
  have v3 : f 3 = 19 := by simp only [hfdef, a_closed]; norm_num
  have v4 : f 4 = 25 := by simp only [hfdef, a_closed]; norm_num
  have v5 : f 5 = 31 := by simp only [hfdef, a_closed]; norm_num
  have v6 : f 6 = 59 := by simp only [hfdef, a_closed]; norm_num
  rcases Nat.lt_or_ge n 7 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v1, v2]
    · norm_num [v0, v2, v3]
    · norm_num [v0, v1, v3, v4]
    · norm_num [v1, v2, v4, v5]
    · norm_num [v0, v2, v3, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at f (m + 7) 0 (m + 7) (by omega), coeff_at f (m + 7) 1 (m + 6) (by omega),
      coeff_at_C f 2 (m + 7) 3 (m + 4) (by omega), coeff_at_C f 2 (m + 7) 4 (m + 3) (by omega),
      coeff_at f (m + 7) 6 (m + 1) (by omega), coeff_at f (m + 7) 7 m (by omega),
      coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow,
      coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    have hr := rec m
    simp only [hfdef]
    linear_combination hr
