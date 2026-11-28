import OMAStatements.S_oeis_a024401
import Mathlib

-- Problem: A024401: a(n) = [ (3rd elementary symmetric function of S(n))/(2nd elementary symmetric function of S(n)) ], where S(n) = {first n+2 positive integers congruent to 2 mod 3}.
-- Upstream: formal-conjectures statements/oeis-a024401.lean:0 (declaration OMA.S_oeis_a024401.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Adding the element x = 3 n + 8 to S(n) gives e_k(S(n+1)) = e_k(S(n)) + x e_(k-1)(S(n)), so by
induction 2 e_1 = 3n^2 + 13n + 14, 8 e_2 = D := 9n^4 + 66n^3 + 175n^2 + 198n + 80 and
48 e_3 = Q D + R with Q = 3n^2 + 5n - 2 and R = 32n^3 + 176n^2 + 304n + 160. Since Q is even,
Q = 6 F + rho with rho in {0, 2, 4}, and 0 < R < 2 D for n >= 1, so the floor of e_3/e_2 is
F = floor(Q/6). Hence a(n+3) = a(n) + 3n + 7 for n >= 1, which gives the recurrence, and the
generating function identity is the recurrence together with a(0), ..., a(5) = 0, 1, 3, 6, 11, 16. -/

namespace A024401Aux

open PowerSeries OMA.S_oeis_a024401

theorem esymm_cons (x : ℤ) (s : Multiset ℤ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t _
  simp

theorem esymm_zero' (s : Multiset ℤ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_left]

theorem esymm_nil (k : ℕ) : (0 : Multiset ℤ).esymm (k + 1) = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_right]

theorem S_succ (n : ℕ) : S (n + 1) = (3 * ((n : ℤ) + 2) + 2) ::ₘ S n := by
  unfold S
  rw [Multiset.range_succ, Multiset.map_cons]
  push_cast
  rfl

theorem S_zero : S 0 = (5 : ℤ) ::ₘ (2 : ℤ) ::ₘ 0 := by
  unfold S
  rw [show (0 + 2 : ℕ) = Nat.succ (Nat.succ 0) from rfl, Multiset.range_succ, Multiset.range_succ,
    Multiset.range_zero, Multiset.map_cons, Multiset.map_cons, Multiset.map_zero]
  norm_num

theorem closed (n : ℕ) :
    2 * (S n).esymm 1 = 3 * (n : ℤ) ^ 2 + 13 * n + 14 ∧
    8 * (S n).esymm 2 = 9 * (n : ℤ) ^ 4 + 66 * n ^ 3 + 175 * n ^ 2 + 198 * n + 80 ∧
    48 * (S n).esymm 3 = 27 * (n : ℤ) ^ 6 + 243 * n ^ 5 + 837 * n ^ 4 + 1369 * n ^ 3 +
      1056 * n ^ 2 + 308 * n := by
  induction n with
  | zero =>
    rw [S_zero]
    simp only [esymm_cons, esymm_zero', esymm_nil]
    norm_num
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [S_succ]
    simp only [esymm_cons, esymm_zero']
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2 + 4 * (3 * ((n : ℤ) + 2) + 2) * h1
    · linear_combination h3 + 6 * (3 * ((n : ℤ) + 2) + 2) * h2

/-- The closed form floor((3n^2 + 5n - 2)/6) for n ≥ 1. -/
theorem a_closed (n : ℕ) (hn : 1 ≤ n) : a n = (3 * (n : ℤ) ^ 2 + 5 * n - 2) / 6 := by
  obtain ⟨_, h2, h3⟩ := closed n
  have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  set e2 : ℤ := (S n).esymm 2 with he2
  set e3 : ℤ := (S n).esymm 3 with he3
  set Q : ℤ := 3 * (n : ℤ) ^ 2 + 5 * n - 2 with hQ
  set F : ℤ := Q / 6 with hF
  have hD0 : (0 : ℤ) < 9 * (n : ℤ) ^ 4 + 66 * n ^ 3 + 175 * n ^ 2 + 198 * n + 80 := by positivity
  have he2pos : (0 : ℤ) < e2 := by linarith
  have heven : (2 : ℤ) ∣ Q := by
    have h := Int.even_mul_succ_self (n : ℤ)
    obtain ⟨c, hc⟩ := h
    refine ⟨3 * c + n - 1, ?_⟩
    rw [hQ]
    linear_combination 3 * hc
  have hdm := Int.emod_add_mul_ediv Q 6
  have hr0 := Int.emod_nonneg Q (by norm_num : (6 : ℤ) ≠ 0)
  have hr6 := Int.emod_lt_of_pos Q (by norm_num : (0 : ℤ) < 6)
  have hrho0 : 0 ≤ Q - 6 * F := by omega
  have hrho4 : Q - 6 * F ≤ 4 := by omega
  have hN : 48 * e3 = Q * (8 * e2) + (32 * (n : ℤ) ^ 3 + 176 * n ^ 2 + 304 * n + 160) := by
    rw [h3, h2, hQ]
    ring
  have hR0 : (0 : ℤ) < 32 * (n : ℤ) ^ 3 + 176 * n ^ 2 + 304 * n + 160 := by positivity
  have hRD : 32 * (n : ℤ) ^ 3 + 176 * n ^ 2 + 304 * n + 160 < 2 * (8 * e2) := by
    rw [h2]
    nlinarith [pow_pos (by linarith : (0 : ℤ) < n) 2, pow_pos (by linarith : (0 : ℤ) < n) 3,
      pow_pos (by linarith : (0 : ℤ) < n) 4]
  have hlow : F * e2 ≤ e3 := by
    nlinarith [mul_nonneg hrho0 he2pos.le]
  have hhigh : e3 < (F + 1) * e2 := by
    nlinarith [mul_le_mul_of_nonneg_right hrho4 he2pos.le]
  unfold a
  rw [← he2, ← he3, Int.floor_eq_iff]
  have he2q : (0 : ℚ) < (e2 : ℚ) := by exact_mod_cast he2pos
  constructor
  · rw [le_div_iff₀ he2q]
    exact_mod_cast hlow
  · rw [div_lt_iff₀ he2q]
    exact_mod_cast hhigh

theorem a_zero : a 0 = 0 := by
  obtain ⟨_, _, h3⟩ := closed 0
  have h : (S 0).esymm 3 = 0 := by
    norm_num at h3
    exact h3
  unfold a
  rw [h]
  simp

theorem a_add_three (n : ℕ) (hn : 1 ≤ n) : a (n + 3) = a n + 3 * (n : ℤ) + 7 := by
  rw [a_closed (n + 3) (by omega), a_closed n hn]
  have e : 3 * ((n + 3 : ℕ) : ℤ) ^ 2 + 5 * ((n + 3 : ℕ) : ℤ) - 2 =
      (3 * (n : ℤ) ^ 2 + 5 * n - 2) + (3 * (n : ℤ) + 7) * 6 := by
    push_cast
    ring
  rw [e, Int.add_mul_ediv_right _ _ (by norm_num : (6 : ℤ) ≠ 0)]
  ring

theorem rec (m : ℕ) : a (m + 6) = 2 * a (m + 5) - a (m + 4) + a (m + 3) - 2 * a (m + 2) + a (m + 1) := by
  have h6 := a_add_three (m + 3) (by omega)
  have h5 := a_add_three (m + 2) (by omega)
  have h4 := a_add_three (m + 1) (by omega)
  have e6 : m + 3 + 3 = m + 6 := by ring
  have e5 : m + 2 + 3 = m + 5 := by ring
  have e4 : m + 1 + 3 = m + 4 := by ring
  rw [e6] at h6
  rw [e5] at h5
  rw [e4] at h4
  push_cast at h6 h5 h4
  linarith

theorem c_succ (f : ℤ⟦X⟧) (c : ℤ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℤ⟦X⟧) (c : ℤ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem c_cube (f : ℤ⟦X⟧) (m : ℕ) :
    coeff m (f * (1 - X ^ 3)) = coeff m f - if 3 ≤ m then coeff (m - 3) f else 0 := by
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']

theorem coeff_quintic (u0 u1 u2 u3 u4 u5 : ℤ) (m : ℕ) :
    coeff m (C u0 + C u1 * X + C u2 * X * X + C u3 * X * X * X + C u4 * X * X * X * X +
        C u5 * X * X * X * X * X : ℤ⟦X⟧) =
      if m = 0 then u0 else if m = 1 then u1 else if m = 2 then u2 else if m = 3 then u3
        else if m = 4 then u4 else if m = 5 then u5 else 0 := by
  rcases m with _ | _ | _ | _ | _ | _ | m
  · simp only [map_add, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_C, add_zero, if_true]
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp

theorem G_coeff (f : ℕ → ℤ) (k : ℕ) :
    coeff (k + 1 + 1) (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X)) =
      f (k + 1 + 1) - 2 * f (k + 1) + f k := by
  simp only [c_succ, PowerSeries.coeff_mk]
  ring

theorem G_coeff_one (f : ℕ → ℤ) :
    coeff (0 + 1) (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X)) = f (0 + 1) - 2 * f 0 := by
  simp only [c_succ, c_zero, PowerSeries.coeff_mk]
  ring

theorem G_coeff_zero (f : ℕ → ℤ) :
    coeff 0 (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X)) = f 0 := by
  simp only [c_zero, PowerSeries.coeff_mk]

theorem gf :
    PowerSeries.mk a * ((1 + X + X ^ 2) * (X - 1) ^ 3) = X * (-1 - X - X ^ 3 - X ^ 2 + X ^ 4) := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℤ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h0 : (C 0 : ℤ⟦X⟧) = 0 := map_zero C
  have hl : PowerSeries.mk a * ((1 + X + X ^ 2) * (X - 1) ^ 3) =
      -(PowerSeries.mk a * (1 - C 1 * X) * (1 - C 1 * X) * (1 - X ^ 3)) := by
    rw [h1]
    ring
  have hr : (X * (-1 - X - X ^ 3 - X ^ 2 + X ^ 4) : ℤ⟦X⟧) =
      -(C 0 + C 1 * X + C 1 * X * X + C 1 * X * X * X + C 1 * X * X * X * X +
        C (-1) * X * X * X * X * X) := by
    rw [h1, hm1, h0]
    ring
  rw [hl, hr, neg_inj]
  ext m
  rw [coeff_quintic, c_cube]
  have v0 := a_zero
  have v1 : a 1 = 1 := by rw [a_closed 1 (by norm_num)]; norm_num
  have v2 : a 2 = 3 := by rw [a_closed 2 (by norm_num)]; norm_num
  have v3 : a 3 = 6 := by rw [a_closed 3 (by norm_num)]; norm_num
  have v4 : a 4 = 11 := by rw [a_closed 4 (by norm_num)]; norm_num
  have v5 : a 5 = 16 := by rw [a_closed 5 (by norm_num)]; norm_num
  rcases m with _ | _ | _ | _ | _ | _ | m
  · rw [if_neg (show ¬ (3 ≤ 0) by norm_num), G_coeff_zero]
    simp [v0]
  · rw [if_neg (show ¬ (3 ≤ 0 + 1) by norm_num), G_coeff_one]
    simp [v0, v1]
  · rw [if_neg (show ¬ (3 ≤ 0 + 1 + 1) by norm_num), G_coeff]
    simp [v0, v1, v2]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 by norm_num), show 0 + 1 + 1 + 1 - 3 = 0 from rfl, G_coeff,
      G_coeff_zero]
    simp [v0, v1, v2, v3]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 + 1 by norm_num),
      show 0 + 1 + 1 + 1 + 1 - 3 = 0 + 1 from rfl, G_coeff, G_coeff_one]
    simp [v0, v1, v2, v3, v4]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 + 1 + 1 by norm_num),
      show 0 + 1 + 1 + 1 + 1 + 1 - 3 = 0 + 1 + 1 from rfl, G_coeff, G_coeff]
    simp [v0, v1, v2, v3, v4, v5]
  · have hr6 := rec m
    rw [if_pos (show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      show m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 from by omega, G_coeff, G_coeff]
    have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 = m + 6 := by ring
    have e5 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by ring
    have e4 : m + 1 + 1 + 1 + 1 = m + 4 := by ring
    have e3' : m + 1 + 1 + 1 = m + 3 := by ring
    have e2 : m + 1 + 1 = m + 2 := by ring
    rw [e6, e5, e4, e3', e2]
    simp
    linarith

end A024401Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a024401.main := by
  refine ⟨?_, A024401Aux.gf⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  exact A024401Aux.rec m
