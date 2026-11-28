import OMAStatements.S_oeis_a085640

-- Problem: A085640: Resultant of the polynomial x^3-1 and the Chebyshev polynomial of the first kind T_n(x).
-- Upstream: formal-conjectures statements/oeis-a085640.lean:0 (declaration OMA.S_oeis_a085640.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: over the complex numbers X^3 - 1 = (X - 1)(X - w)(X - w') with w = (-1 + i sqrt 3)/2 and
-- w' = -1 - w, so by resultant_eq_prod_eval (and resultant_map_map from the integers) the resultant is
-- T_n(1) T_n(w) T_n(w') = T_n(w) T_n(w'). The sequences t(n) = T_n(w), s(n) = T_n(w') satisfy
-- t(n+2) = 2 w t(n+1) - t(n) and s(n+2) = 2 w' s(n+1) - s(n), and then the products satisfy
-- p(n+4) = 4 p(n+3) + 6 p(n+2) + 4 p(n+1) - p(n), a polynomial identity modulo w^2 + w + 1 (certificate
-- below). With a(0..3) = 1, 1, 7, 37 the generating function follows by comparing coefficients.

namespace P1A085640

open OMA.S_oeis_a085640

/-- A series times a finite sum of monomials, coefficient by coefficient. -/
theorem gf_poly (f c e : ℕ → ℚ) (d D : ℕ)
    (h : ∀ m, (∑ j ∈ Finset.range d, if j ≤ m then c j * f (m - j) else 0) =
      if m < D then e m else 0) :
    PowerSeries.mk f * (∑ j ∈ Finset.range d, PowerSeries.C (c j) * PowerSeries.X ^ j) =
      ∑ j ∈ Finset.range D, PowerSeries.C (e j) * PowerSeries.X ^ j := by
  ext m
  have hl : ∀ j, PowerSeries.coeff m (PowerSeries.mk f * (PowerSeries.C (c j) * PowerSeries.X ^ j)) =
      if j ≤ m then c j * f (m - j) else 0 := by
    intro j
    rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    by_cases hj : j ≤ m
    · rw [if_pos hj, if_pos hj, PowerSeries.coeff_mk]
    · rw [if_neg hj, if_neg hj, mul_zero]
  have hr : ∀ j, PowerSeries.coeff m (PowerSeries.C (e j) * PowerSeries.X ^ j) =
      if m = j then e j else 0 := fun j => PowerSeries.coeff_C_mul_X_pow (e j) j m
  rw [Finset.mul_sum, map_sum, map_sum, Finset.sum_congr rfl (fun j _ => hl j),
    Finset.sum_congr rfl (fun j _ => hr j), h m, Finset.sum_ite_eq]
  simp only [Finset.mem_range]

/-- Coefficients of 1 - 4x - 6x^2 - 4x^3 + x^4. -/
def cd : ℕ → ℚ
  | 0 => 1
  | 1 => -4
  | 2 => -6
  | 3 => -4
  | 4 => 1
  | _ => 0

/-- Coefficients of 1 + 3x + 3x^2 - x^3. -/
def cn : ℕ → ℚ
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => -1
  | _ => 0

theorem cd0 : cd 0 = 1 := rfl
theorem cd1 : cd 1 = -4 := rfl
theorem cd2 : cd 2 = -6 := rfl
theorem cd3 : cd 3 = -4 := rfl
theorem cd4 : cd 4 = 1 := rfl
theorem cn0 : cn 0 = 1 := rfl
theorem cn1 : cn 1 = 3 := rfl
theorem cn2 : cn 2 = 3 := rfl
theorem cn3 : cn 3 = -1 := rfl

theorem hden : (1 - 4 * PowerSeries.X - 6 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4 : PowerSeries ℚ) =
    ∑ j ∈ Finset.range 5, PowerSeries.C (cd j) * PowerSeries.X ^ j := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cd0, cd1, cd2, cd3, cd4]
  simp only [map_neg, map_one]
  rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
  ring

theorem hnum : (1 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 : PowerSeries ℚ) =
    ∑ j ∈ Finset.range 4, PowerSeries.C (cn j) * PowerSeries.X ^ j := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, cn0, cn1, cn2, cn3]
  simp only [map_neg, map_one]
  rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
  ring

open Polynomial

/-- A primitive cube root of unity exists: w = (-1 + i sqrt 3)/2. -/
theorem cube_root : ∃ w : ℂ, w ^ 2 + w + 1 = 0 := by
  refine ⟨(-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2, ?_⟩
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by exact_mod_cast h3'
  linear_combination ((Real.sqrt 3 : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * h3

theorem fac (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    (X ^ 3 - 1 : ℂ[X]) = (X - C 1) * (X - C w) * (X - C (-1 - w)) := by
  have e : (X - C 1) * (X - C w) * (X - C (-1 - w)) =
      (X ^ 3 - 1 : ℂ[X]) - (X - C 1) * C (w ^ 2 + w + 1) := by
    simp only [map_sub, map_neg, map_one, map_add, map_pow]
    ring
  rw [e, hw, map_zero, mul_zero, sub_zero]

theorem roots_eq (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    (X ^ 3 - 1 : ℂ[X]).roots = {1} + {w} + {-1 - w} := by
  have h1 : (X - C (1 : ℂ)) * (X - C w) ≠ 0 := mul_ne_zero (X_sub_C_ne_zero 1) (X_sub_C_ne_zero w)
  have h2 : (X - C (1 : ℂ)) * (X - C w) * (X - C (-1 - w)) ≠ 0 :=
    mul_ne_zero h1 (X_sub_C_ne_zero _)
  rw [fac w hw, roots_mul h2, roots_mul h1, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]

theorem splits3 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : (X ^ 3 - 1 : ℂ[X]).Splits := by
  rw [fac w hw]
  exact ((Splits.X_sub_C (1 : ℂ)).mul (Splits.X_sub_C w)).mul (Splits.X_sub_C (-1 - w))

/-- The resultant over the complex numbers: a(n) = T_n(w) T_n(-1-w). -/
theorem a_eq (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (n : ℕ) : ((a n : ℤ) : ℂ) =
    (Chebyshev.T ℂ (n : ℤ)).eval w * (Chebyshev.T ℂ (n : ℤ)).eval (-1 - w) := by
  have hm := resultant_map_map (X ^ 3 - 1 : ℤ[X]) (Chebyshev.T ℤ (n : ℤ))
    (X ^ 3 - 1 : ℤ[X]).natDegree (Chebyshev.T ℤ (n : ℤ)).natDegree (Int.castRingHom ℂ)
  have hf : (X ^ 3 - 1 : ℤ[X]).map (Int.castRingHom ℂ) = (X ^ 3 - 1 : ℂ[X]) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have hg : (Chebyshev.T ℤ (n : ℤ)).map (Int.castRingHom ℂ) = Chebyshev.T ℂ (n : ℤ) :=
    Chebyshev.map_T _ _
  have e1 : ((a n : ℤ) : ℂ) = resultant (X ^ 3 - 1 : ℂ[X]) (Chebyshev.T ℂ (n : ℤ))
      (X ^ 3 - 1 : ℤ[X]).natDegree (Chebyshev.T ℤ (n : ℤ)).natDegree := by
    rw [← hf, ← hg, hm]
    rfl
  have d1 : (X ^ 3 - 1 : ℤ[X]).natDegree = 3 := by
    rw [← C_1]
    exact natDegree_X_pow_sub_C
  have d2 : (X ^ 3 - 1 : ℂ[X]).natDegree = 3 := by
    rw [← C_1]
    exact natDegree_X_pow_sub_C
  have hgdeg : (Chebyshev.T ℂ (n : ℤ)).natDegree ≤ (Chebyshev.T ℤ (n : ℤ)).natDegree := by
    rw [← hg]
    exact natDegree_map_le
  have hlc : (X ^ 3 - 1 : ℂ[X]).leadingCoeff = 1 := by
    rw [← C_1]
    exact (monic_X_pow_sub_C (1 : ℂ) (by norm_num : (3 : ℕ) ≠ 0)).leadingCoeff
  rw [e1, show (X ^ 3 - 1 : ℤ[X]).natDegree = (X ^ 3 - 1 : ℂ[X]).natDegree from d1.trans d2.symm,
    resultant_eq_prod_eval _ _ _ hgdeg (splits3 w hw), hlc, one_pow, one_mul, roots_eq w hw,
    Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.map_singleton,
    Multiset.prod_singleton, Multiset.prod_singleton, Multiset.prod_singleton,
    Chebyshev.T_eval_one, one_mul]

theorem Trec (x : ℂ) (m : ℤ) :
    (Chebyshev.T ℂ (m + 2)).eval x =
      2 * x * (Chebyshev.T ℂ (m + 1)).eval x - (Chebyshev.T ℂ m).eval x := by
  rw [Chebyshev.T_add_two]
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat]

/-- The order-four recurrence of the products, a polynomial identity modulo u^2 + u + 1. -/
theorem alg (u t0 t1 t2 t3 t4 s0 s1 s2 s3 s4 : ℂ) (hu : u ^ 2 + u + 1 = 0)
    (h2 : t2 = 2 * u * t1 - t0) (h3 : t3 = 2 * u * t2 - t1) (h4 : t4 = 2 * u * t3 - t2)
    (g2 : s2 = 2 * (-1 - u) * s1 - s0) (g3 : s3 = 2 * (-1 - u) * s2 - s1)
    (g4 : s4 = 2 * (-1 - u) * s3 - s2) :
    t4 * s4 = 4 * (t3 * s3) + 6 * (t2 * s2) + 4 * (t1 * s1) - t0 * s0 := by
  subst h4 g4
  subst h3 g3
  subst h2 g2
  linear_combination (8 * t1 * s1 + 64 * t1 * s1 * u - 128 * t1 * s1 * u ^ 3 - 64 * t1 * s1 * u ^ 4 +
    8 * t1 * s0 + 24 * t1 * s0 * u - 32 * t1 * s0 * u ^ 2 - 32 * t1 * s0 * u ^ 3 -
    16 * t0 * s1 + 8 * t0 * s1 * u + 64 * t0 * s1 * u ^ 2 + 32 * t0 * s1 * u ^ 3 -
    8 * t0 * s0 + 16 * t0 * s0 * u + 16 * t0 * s0 * u ^ 2) * hu

theorem ini (u : ℂ) (hu : u ^ 2 + u + 1 = 0) :
    u * (-1 - u) = 1 ∧ (2 * u * u - 1) * (2 * (-1 - u) * (-1 - u) - 1) = 7 ∧
    (2 * u * (2 * u * u - 1) - u) *
      (2 * (-1 - u) * (2 * (-1 - u) * (-1 - u) - 1) - (-1 - u)) = 37 := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 : ℂ) * hu
  · linear_combination (-8 + 4 * u + 4 * u ^ 2) * hu
  · linear_combination (-37 + 40 * u + 24 * u ^ 2 - 32 * u ^ 3 - 16 * u ^ 4) * hu

theorem Tvals (x : ℂ) : (Chebyshev.T ℂ 0).eval x = 1 ∧ (Chebyshev.T ℂ 1).eval x = x ∧
    (Chebyshev.T ℂ 2).eval x = 2 * x * x - 1 ∧
    (Chebyshev.T ℂ 3).eval x = 2 * x * (2 * x * x - 1) - x := by
  have e0 : (Chebyshev.T ℂ 0).eval x = 1 := by rw [Chebyshev.T_zero, eval_one]
  have e1 : (Chebyshev.T ℂ 1).eval x = x := by rw [Chebyshev.T_one, eval_X]
  have h2 := Trec x 0
  rw [show (0 : ℤ) + 2 = 2 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num, e0, e1] at h2
  have h3 := Trec x 1
  rw [show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, h2, e1] at h3
  exact ⟨e0, e1, h2, h3⟩

theorem arec (n : ℕ) : a (n + 4) = 4 * a (n + 3) + 6 * a (n + 2) + 4 * a (n + 1) - a n := by
  obtain ⟨w, hw⟩ := cube_root
  have hc : ((a (n + 4) : ℤ) : ℂ) = 4 * ((a (n + 3) : ℤ) : ℂ) + 6 * ((a (n + 2) : ℤ) : ℂ) +
      4 * ((a (n + 1) : ℤ) : ℂ) - ((a n : ℤ) : ℂ) := by
    rw [a_eq w hw (n + 4), a_eq w hw (n + 3), a_eq w hw (n + 2), a_eq w hw (n + 1), a_eq w hw n]
    push_cast
    have h2 := Trec w (n : ℤ)
    have h3 := Trec w ((n : ℤ) + 1)
    have h4 := Trec w ((n : ℤ) + 2)
    have g2 := Trec (-1 - w) (n : ℤ)
    have g3 := Trec (-1 - w) ((n : ℤ) + 1)
    have g4 := Trec (-1 - w) ((n : ℤ) + 2)
    rw [show (n : ℤ) + 1 + 2 = (n : ℤ) + 3 by ring, show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring]
      at h3 g3
    rw [show (n : ℤ) + 2 + 2 = (n : ℤ) + 4 by ring, show (n : ℤ) + 2 + 1 = (n : ℤ) + 3 by ring]
      at h4 g4
    linear_combination alg w _ _ _ _ _ _ _ _ _ _ hw h2 h3 h4 g2 g3 g4
  exact_mod_cast hc

theorem avals : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 7 ∧ a 3 = 37 := by
  obtain ⟨w, hw⟩ := cube_root
  obtain ⟨e0, e1, e2, e3⟩ := Tvals w
  obtain ⟨f0, f1, f2, f3⟩ := Tvals (-1 - w)
  obtain ⟨i1, i2, i3⟩ := ini w hw
  have c0 : ((a 0 : ℤ) : ℂ) = 1 := by
    rw [a_eq w hw 0]
    push_cast
    rw [e0, f0, one_mul]
  have c1 : ((a 1 : ℤ) : ℂ) = 1 := by
    rw [a_eq w hw 1]
    push_cast
    rw [e1, f1]
    linear_combination i1
  have c2 : ((a 2 : ℤ) : ℂ) = 7 := by
    rw [a_eq w hw 2]
    push_cast
    rw [e2, f2]
    linear_combination i2
  have c3 : ((a 3 : ℤ) : ℂ) = 37 := by
    rw [a_eq w hw 3]
    push_cast
    rw [e3, f3]
    linear_combination i3
  exact ⟨by exact_mod_cast c0, by exact_mod_cast c1, by exact_mod_cast c2, by exact_mod_cast c3⟩

theorem a4 : a 4 = 193 := by
  have h := arec 0
  simp only [Nat.zero_add] at h
  obtain ⟨h0, h1, h2, h3⟩ := avals
  rw [h0, h1, h2, h3] at h
  linarith

theorem v1 : (a 1 : ℚ) = 1 := by exact_mod_cast avals.2.1
theorem v2 : (a 2 : ℚ) = 7 := by exact_mod_cast avals.2.2.1
theorem v3 : (a 3 : ℚ) = 37 := by exact_mod_cast avals.2.2.2
theorem v4 : (a 4 : ℚ) = 193 := by exact_mod_cast a4

/-- The coefficients of x^(k+4) vanish. -/
theorem high (k : ℕ) :
    (∑ j ∈ Finset.range 5, if j ≤ k + 4 then cd j * (a (k + 4 - j + 1) : ℚ) else 0) = 0 := by
  have hs : ∀ j ∈ Finset.range 5, (if j ≤ k + 4 then cd j * (a (k + 4 - j + 1) : ℚ) else 0) =
      cd j * (a (k + 4 - j + 1) : ℚ) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [if_pos (show j ≤ k + 4 by omega)]
  rw [Finset.sum_congr rfl hs]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show k + 4 - 0 + 1 = k + 5 by omega, show k + 4 - 1 + 1 = k + 4 by omega,
    show k + 4 - 2 + 1 = k + 3 by omega, show k + 4 - 3 + 1 = k + 2 by omega,
    show k + 4 - 4 + 1 = k + 1 by omega]
  rw [cd0, cd1, cd2, cd3, cd4]
  have h := arec (k + 1)
  rw [show k + 1 + 4 = k + 5 by omega, show k + 1 + 3 = k + 4 by omega,
    show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at h
  have hq : ((a (k + 5) : ℤ) : ℚ) = 4 * (a (k + 4) : ℚ) + 6 * (a (k + 3) : ℚ) +
      4 * (a (k + 2) : ℚ) - (a (k + 1) : ℚ) := by exact_mod_cast h
  linear_combination hq

end P1A085640

open OMA.S_oeis_a085640 P1A085640 in
theorem OMA.solution : type_of% @OMA.S_oeis_a085640.main := by
  rw [hden, hnum]
  refine gf_poly (fun n => (a (n + 1) : ℚ)) cd cn 5 4 ?_
  intro m
  rcases Nat.lt_or_ge m 4 with hm | hm
  · interval_cases m <;>
      norm_num [Finset.sum_range_succ, cd0, cd1, cd2, cd3, cd4, cn0, cn1, cn2, cn3, v1, v2, v3, v4]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    rw [if_neg (show ¬ (k + 4 < 4) by omega)]
    exact high k
