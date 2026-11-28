import OMAStatements.S_oeis_a211433
import Mathlib

/-!
Credit: @ivillar
Proof: w = -2(x+2y) is determined by (x, y), so a(n) counts the pairs (x, y) in [-n, n]^2 with
|2(x+2y)| ≤ n, i.e. |s| ≤ m := floor(n/2) for s = x + 2y. For such s the pairs with x + 2y = s
correspond to the y with s - n ≤ 2y ≤ s + n; there are n + 1 of them when s ≡ n (mod 2) and n
otherwise. Summing over |s| ≤ m gives a closed form, from which a(n+4) = a(n) + 8n + 22 for even
n and a(n+4) = a(n) + 8n + 18 for odd n. This gives the recurrence (as in Pontus von Brömssen's
remark in the OEIS entry, the linear and parity parts are annihilated), and with the first seven
terms the g.f.
-/

namespace OMAA211433Helpers
open PowerSeries OMA.S_oeis_a211433

/-- The pairs (x, y) in [-n, n]^2 with -n ≤ 2(x+2y) ≤ n. -/
noncomputable def P (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => -(n : ℤ) ≤ 2 * (p.1 + 2 * p.2) ∧ 2 * (p.1 + 2 * p.2) ≤ n)

theorem a_eq_P (n : ℕ) : a n = (P n).card := by
  unfold a P
  exact Finset.card_bij' (fun t _ => (t.2.1, t.2.2)) (fun p _ => (-2 * p.1 - 4 * p.2, p.1, p.2))
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

theorem fiber_card (n : ℕ) (s : ℤ) (hs1 : -(n : ℤ) ≤ 2 * s) (hs2 : 2 * s ≤ n) :
    (((P n).filter (fun p => p.1 + 2 * p.2 = s)).card : ℤ) = n + 1 - (s + n) % 2 := by
  have hc : ((P n).filter (fun p => p.1 + 2 * p.2 = s)).card =
      (Finset.Icc (-((n - s) / 2)) ((s + n) / 2)).card := by
    exact Finset.card_bij' (fun p _ => p.2) (fun y _ => (s - 2 * y, y))
      (fun p hp => by
        obtain ⟨x, y⟩ := p
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
        omega)
      (fun y hy => by
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hy ⊢
        omega)
      (fun p hp => by
        obtain ⟨x, y⟩ := p
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        exact Prod.ext (by dsimp only; omega) rfl)
      (fun y _ => rfl)
  rw [hc, Int.card_Icc]
  omega

/-- The number of s in [-m, m] with s + n odd. -/
def E (n m : ℕ) : ℤ := if n % 2 = 0 then 2 * (((m + 1) / 2 : ℕ) : ℤ) else 2 * ((m / 2 : ℕ) : ℤ) + 1

theorem sum_mod (n m : ℕ) :
    ∑ s ∈ Finset.Icc (-(m : ℤ)) m, ((s + n) % 2) = E n m := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton, E]
    split_ifs <;> omega
  | succ k ih =>
    have hI : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k : ℤ) + 1)) (insert ((k : ℤ) + 1) (Finset.Icc (-(k : ℤ)) k)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
    simp only [E]
    split_ifs <;> omega

theorem a_closed (n : ℕ) :
    (a n : ℤ) = (2 * ((n / 2 : ℕ) : ℤ) + 1) * ((n : ℤ) + 1) - E n (n / 2) := by
  rw [a_eq_P]
  have hmaps : ∀ p ∈ P n, p.1 + 2 * p.2 ∈ Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ) := by
    rintro ⟨x, y⟩ hp
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    omega
  have hf := Finset.card_eq_sum_card_fiberwise hmaps
  have hf' : ((P n).card : ℤ) = ∑ s ∈ Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ),
      (((P n).filter (fun p => p.1 + 2 * p.2 = s)).card : ℤ) := by
    rw [hf]
    push_cast
    rfl
  have hsum : ∑ s ∈ Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ),
      (((P n).filter (fun p => p.1 + 2 * p.2 = s)).card : ℤ) =
      ∑ s ∈ Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ), ((n : ℤ) + 1 - (s + n) % 2) :=
    Finset.sum_congr rfl (fun s hs => fiber_card n s
      (by simp only [Finset.mem_Icc] at hs; omega) (by simp only [Finset.mem_Icc] at hs; omega))
  have hcard : ((((n / 2 : ℕ) : ℤ) + 1 - -((n / 2 : ℕ) : ℤ)).toNat : ℤ) =
      2 * ((n / 2 : ℕ) : ℤ) + 1 := by omega
  rw [hf', hsum, Finset.sum_sub_distrib, Finset.sum_const, Int.card_Icc, sum_mod, nsmul_eq_mul,
    hcard]

theorem d4 (k : ℕ) : (a (k + 4) : ℤ) = a k + 8 * k + 18 + 4 * (((k : ℤ) + 1) % 2) := by
  rw [a_closed, a_closed]
  have hm : (k + 4) / 2 = k / 2 + 2 := by omega
  rw [hm]
  have hE : E (k + 4) (k / 2 + 2) = E k (k / 2) + 2 := by
    unfold E
    have h1 : (k + 4) % 2 = k % 2 := by omega
    have h2 : (k / 2 + 2 + 1) / 2 = (k / 2 + 1) / 2 + 1 := by omega
    have h3 : (k / 2 + 2) / 2 = k / 2 / 2 + 1 := by omega
    rw [h1, h2, h3]
    split_ifs <;> push_cast <;> ring
  rw [hE]
  have hk2 : 2 * ((k / 2 : ℕ) : ℤ) = (k : ℤ) - (k : ℤ) % 2 := by omega
  have hpar : ((k : ℤ) + 1) % 2 = 1 - (k : ℤ) % 2 := by omega
  push_cast at hk2 hpar ⊢
  linear_combination (4 : ℤ) * hk2 - 4 * hpar

theorem rec (m : ℕ) :
    (a (m + 7) : ℤ) = a (m + 6) + a (m + 5) - a (m + 4) + a (m + 3) - a (m + 2) - a (m + 1) +
      a m := by
  have e3 := d4 (m + 3)
  have e2 := d4 (m + 2)
  have e1 := d4 (m + 1)
  have e0 := d4 m
  rw [show m + 3 + 4 = m + 7 by ring] at e3
  rw [show m + 2 + 4 = m + 6 by ring] at e2
  rw [show m + 1 + 4 = m + 5 by ring] at e1
  push_cast at e3 e2 e1 e0
  omega

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℤ) (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

end OMAA211433Helpers

open PowerSeries OMAA211433Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a211433.main := by
  have hrec : ∀ n : ℕ, 6 < n → (OMA.S_oeis_a211433.a n : ℤ) =
      OMA.S_oeis_a211433.a (n - 1) + OMA.S_oeis_a211433.a (n - 2) -
        OMA.S_oeis_a211433.a (n - 3) + OMA.S_oeis_a211433.a (n - 4) -
          OMA.S_oeis_a211433.a (n - 5) - OMA.S_oeis_a211433.a (n - 6) +
            OMA.S_oeis_a211433.a (n - 7) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega,
      show k + 7 - 7 = k by omega]
    exact rec k
  refine ⟨?_, hrec⟩
  set f : ℕ → ℤ := fun n => (OMA.S_oeis_a211433.a n : ℤ) with hfdef
  ext n
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) : PowerSeries ℤ) =
      X ^ 0 - X ^ 1 - X ^ 2 + X ^ 3 - X ^ 4 + X ^ 5 + X ^ 6 - X ^ 7 := by
    ring
  have hN : (1 + 5 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 + X ^ 6 : PowerSeries ℤ) =
      X ^ 0 + C 5 * X ^ 2 + C 4 * X ^ 3 + C 5 * X ^ 4 + X ^ 6 := by
    rw [map_ofNat C 5, map_ofNat C 4]; ring
  rw [hD, hN]
  have v0 : f 0 = 1 := by simp only [hfdef, a_closed, E]; norm_num
  have v1 : f 1 = 1 := by simp only [hfdef, a_closed, E]; norm_num
  have v2 : f 2 = 7 := by simp only [hfdef, a_closed, E]; norm_num
  have v3 : f 3 = 11 := by simp only [hfdef, a_closed, E]; norm_num
  have v4 : f 4 = 23 := by simp only [hfdef, a_closed, E]; norm_num
  have v5 : f 5 = 27 := by simp only [hfdef, a_closed, E]; norm_num
  have v6 : f 6 = 45 := by simp only [hfdef, a_closed, E]; norm_num
  rcases Nat.lt_or_ge n 7 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_X_pow, coeff_C_mul, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v1, v2, v3]
    · norm_num [v0, v1, v2, v3, v4]
    · norm_num [v0, v1, v2, v3, v4, v5]
    · norm_num [v0, v1, v2, v3, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at f (m + 7) 0 (m + 7) (by omega), coeff_at f (m + 7) 1 (m + 6) (by omega),
      coeff_at f (m + 7) 2 (m + 5) (by omega), coeff_at f (m + 7) 3 (m + 4) (by omega),
      coeff_at f (m + 7) 4 (m + 3) (by omega), coeff_at f (m + 7) 5 (m + 2) (by omega),
      coeff_at f (m + 7) 6 (m + 1) (by omega), coeff_at f (m + 7) 7 m (by omega),
      coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow,
      coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    have hr := rec m
    simp only [hfdef]
    linear_combination hr
