import OMAStatements.S_oeis_a192748

-- Problem: A192748: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.
-- Upstream: formal-conjectures statements/oeis-a192748.lean:0 (declaration OMA.S_oeis_a192748.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: p(n) mod (x^2 - x - 1) = v(n) x + u(n) with u(0) = 1, v(0) = 0,
-- u(n+1) = v(n) + 3(n+1), v(n+1) = u(n) + v(n), because x (v x + u) = v (x^2 - x - 1) + (u + v) x + v
-- (uniqueness of the remainder, div_modByMonic_unique). So a(n+1) = v(n), and
-- v(m+2) = v(m+1) + v(m) + 3(m+1), hence v(k+4) = 3v(k+3) - 2v(k+2) - v(k+1) + v(k), the recurrence of
-- the denominator 1 - 3x + 2x^2 + x^3 - x^4 = (1-x)^2 (1-x-x^2). Both identities then follow by
-- comparing coefficients, with the first four or five coefficients computed directly.

namespace P1A192748

open Polynomial OMA.S_oeis_a192748

/-- The reduction of p(n,x) as the pair (constant term, coefficient of x). -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((uv n).2 + 3 * ((n : ℤ) + 1), (uv n).1 + (uv n).2)

theorem hM : (X ^ 2 - X - 1 : Polynomial ℤ).Monic := by
  monicity!

theorem hdeg : (X ^ 2 - X - 1 : Polynomial ℤ).degree = 2 := by
  compute_degree!

theorem modM (f q : Polynomial ℤ) (u v : ℤ) (h : C v * X + C u + (X ^ 2 - X - 1) * q = f) :
    f %ₘ (X ^ 2 - X - 1) = C v * X + C u :=
  (div_modByMonic_unique q (C v * X + C u) hM ⟨h, by rw [hdeg]; exact degree_linear_lt⟩).2

theorem red (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (uv n).2 * X + C (uv n).1 := by
  induction n with
  | zero =>
    apply modM (p 0) 0
    show C (0 : ℤ) * X + C 1 + (X ^ 2 - X - 1) * 0 = (1 : Polynomial ℤ)
    simp
  | succ k ih =>
    obtain ⟨q, hq⟩ : ∃ q, C (uv k).2 * X + C (uv k).1 + (X ^ 2 - X - 1) * q = p k :=
      ⟨p k /ₘ (X ^ 2 - X - 1), by rw [← ih]; exact modByMonic_add_div (p k) _⟩
    apply modM (p (k + 1)) (X * q + C (uv k).2)
    show C ((uv k).1 + (uv k).2) * X + C ((uv k).2 + 3 * ((k : ℤ) + 1)) +
        (X ^ 2 - X - 1) * (X * q + C (uv k).2) = X * p k + C (3 * ((k : ℤ) + 1))
    rw [← hq]
    simp only [map_add]
    ring

theorem a_eq (n : ℕ) : a (n + 1) = (uv n).2 := by
  show (p (n + 1 - 1) %ₘ (X ^ 2 - X - 1)).coeff 1 = (uv n).2
  rw [show n + 1 - 1 = n by omega, red n, coeff_add, coeff_C_mul_X, coeff_C,
    if_pos (show (1 : ℕ) = 1 from rfl), if_neg (show ¬ ((1 : ℕ) = 0) by omega), add_zero]

theorem v_rec (m : ℕ) : (uv (m + 2)).2 = (uv (m + 1)).2 + (uv m).2 + 3 * ((m : ℤ) + 1) := by
  show ((uv m).2 + 3 * ((m : ℤ) + 1)) + (uv (m + 1)).2 = (uv (m + 1)).2 + (uv m).2 + 3 * ((m : ℤ) + 1)
  ring

theorem v_rec4 (k : ℕ) :
    (uv (k + 4)).2 = 3 * (uv (k + 3)).2 - 2 * (uv (k + 2)).2 - (uv (k + 1)).2 + (uv k).2 := by
  have h4 : (uv (k + 4)).2 = (uv (k + 3)).2 + (uv (k + 2)).2 + 3 * (((k + 2 : ℕ) : ℤ) + 1) :=
    v_rec (k + 2)
  have h3 : (uv (k + 3)).2 = (uv (k + 2)).2 + (uv (k + 1)).2 + 3 * (((k + 1 : ℕ) : ℤ) + 1) :=
    v_rec (k + 1)
  have h2 : (uv (k + 2)).2 = (uv (k + 1)).2 + (uv k).2 + 3 * ((k : ℤ) + 1) := v_rec k
  push_cast at h4 h3
  linear_combination h4 - 2 * h3 + h2

end P1A192748

open OMA.S_oeis_a192748 P1A192748 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192748.main := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℚ, ∀ n, s n = ((uv n).2 : ℚ) := ⟨_, fun _ => rfl⟩
  have srec : ∀ k, s (k + 4) = 3 * s (k + 3) - 2 * s (k + 2) - s (k + 1) + s k := by
    intro k
    rw [hs, hs, hs, hs, hs]
    exact_mod_cast v_rec4 k
  have s0 : s 0 = 0 := by
    rw [hs]
    exact_mod_cast (show (uv 0).2 = 0 by decide)
  have s1 : s 1 = 1 := by
    rw [hs]
    exact_mod_cast (show (uv 1).2 = 1 by decide)
  have s2 : s 2 = 4 := by
    rw [hs]
    exact_mod_cast (show (uv 2).2 = 4 by decide)
  have s3 : s 3 = 11 := by
    rw [hs]
    exact_mod_cast (show (uv 3).2 = 11 by decide)
  have e1 : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk s := by
    congr 1
    funext n
    show (a (n + 1) : ℚ) = s n
    rw [hs, a_eq]
  have e2 : PowerSeries.mk (fun n => (a (n + 2) : ℚ) - (a (n + 1) : ℚ)) =
      PowerSeries.mk (fun n => s (n + 1) - s n) := by
    congr 1
    funext n
    show (a (n + 1 + 1) : ℚ) - (a (n + 1) : ℚ) = s (n + 1) - s n
    rw [hs, hs, a_eq, a_eq]
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · have e : PowerSeries.X * PowerSeries.mk s *
        ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) =
        PowerSeries.mk s * PowerSeries.X ^ 5 - PowerSeries.mk s * PowerSeries.X ^ 4
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk s * PowerSeries.X ^ 3)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (PowerSeries.mk s * PowerSeries.X ^ 2)
          - PowerSeries.mk s * PowerSeries.X ^ 1 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
      ring
    have e' : -(PowerSeries.X ^ 2 * (1 + PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℚ) =
        -(PowerSeries.X ^ 2) - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 := by
      ring
    rw [e, e']
    ext m
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m
      · norm_num
      · norm_num [s0]
      · norm_num [s0, s1]
      · norm_num [s0, s1, s2]
      · norm_num [s0, s1, s2, s3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
      rw [if_pos (show 5 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
        if_pos (show 3 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
        if_pos (show 1 ≤ k + 5 by omega), if_neg (show ¬ (k + 5 = 2) by omega),
        if_neg (show ¬ (k + 5 = 3) by omega), if_neg (show ¬ (k + 5 = 4) by omega),
        show k + 5 - 5 = k by omega, show k + 5 - 4 = k + 1 by omega,
        show k + 5 - 3 = k + 2 by omega, show k + 5 - 2 = k + 3 by omega,
        show k + 5 - 1 = k + 4 by omega, srec k]
      ring
  · have e : PowerSeries.mk (fun n => s (n + 1) - s n) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
        PowerSeries.mk (fun n => s (n + 1) - s n)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
            (PowerSeries.mk (fun n => s (n + 1) - s n) * PowerSeries.X ^ 1)
          + PowerSeries.mk (fun n => s (n + 1) - s n) * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    have e' : (1 + PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1 + PowerSeries.X ^ 1 + PowerSeries.X ^ 2 := by
      rw [map_one]
      ring
    rw [e, e']
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m
      · norm_num [s0, s1]
      · norm_num [s0, s1, s2]
      · norm_num [s1, s2, s3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 3 ≤ k + 3 by omega),
        if_neg (show ¬ (k + 3 = 0) by omega), if_neg (show ¬ (k + 3 = 1) by omega),
        if_neg (show ¬ (k + 3 = 2) by omega), show k + 3 - 1 = k + 2 by omega,
        show k + 3 - 3 = k by omega, show k + 3 + 1 = k + 4 by omega,
        show k + 2 + 1 = k + 3 by omega, srec k]
      ring
