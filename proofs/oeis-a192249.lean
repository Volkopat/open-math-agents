import OMAStatements.S_oeis_a192249

-- Problem: A192249: 1-sequence of reduction of binomial coefficient sequence B(n,4)=A000332 by x^2 -> x+1.
-- Upstream: formal-conjectures statements/oeis-a192249.lean:0 (declaration OMA.S_oeis_a192249.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: x^k = F(k) x + (F(k+1) - F(k)) modulo x^2 - x - 1, so p(n,x) mod (x^2 - x - 1) has
-- x-coefficient v(n) = Sum_{k<=n} B(k+4,4) F(k) (uniqueness of the remainder, div_modByMonic_unique),
-- and a(n+1) = v(n). With b(k) = B(k+4,4) F(k) we have (1 - x) V(x) = B(x), and
-- B(k+4,4) = (k+1)(k+2)(k+3)(k+4)/24 gives Sum_j c_j b(m+10-j) = 0 for the coefficients c_j of
-- (1 - x - x^2)^5 (a polynomial identity in m, F(m), F(m+1)). So B(x) (1 - x - x^2)^5 is the polynomial
-- 5x - 10x^2 + 20x^3 - 15x^4 + 5x^5 (first ten coefficients computed), and the g.f. follows.

namespace P1A192249

open OMA.S_oeis_a192249

section poly

open Polynomial

theorem hM : (X ^ 2 - X - 1 : Polynomial ℤ).Monic := by
  monicity!

theorem hdeg : (X ^ 2 - X - 1 : Polynomial ℤ).degree = 2 := by
  compute_degree!

theorem modM (f q : Polynomial ℤ) (u v : ℤ) (h : C v * X + C u + (X ^ 2 - X - 1) * q = f) :
    f %ₘ (X ^ 2 - X - 1) = C v * X + C u :=
  (div_modByMonic_unique q (C v * X + C u) hM ⟨h, by rw [hdeg]; exact degree_linear_lt⟩).2

/-- The coefficients B(k+4,4). -/
def s (k : ℕ) : ℤ := ((Nat.choose (k + 4) 4 : ℕ) : ℤ)

/-- The coefficient of x in the reduction of p(n,x). -/
def vv (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), s k * (Nat.fib k : ℤ)

/-- The constant term of the reduction of p(n,x). -/
def uu (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), s k * ((Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ))

theorem xpow (k : ℕ) : ∃ r : Polynomial ℤ, C (Nat.fib k : ℤ) * X +
    C ((Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ)) + (X ^ 2 - X - 1) * r = X ^ k := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨C (Nat.fib k : ℤ) + X * r, ?_⟩
    have hf : (Nat.fib (k + 1 + 1) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    rw [pow_succ (X : Polynomial ℤ) k, ← hr, hf]
    simp only [map_add, map_sub]
    ring

theorem red (n : ℕ) :
    ∃ q : Polynomial ℤ, C (vv n) * X + C (uu n) + (X ^ 2 - X - 1) * q = p n := by
  induction n with
  | zero => exact ⟨0, by simp [vv, uu, s, p]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨r, hr⟩ := xpow (n + 1)
    refine ⟨q + C (s (n + 1)) * r, ?_⟩
    have hp : p (n + 1) = p n + C (s (n + 1)) * X ^ (n + 1) :=
      Finset.sum_range_succ (fun k => C ((Nat.choose (k + 4) 4 : ℕ) : ℤ) * X ^ k) (n + 1)
    have hv : vv (n + 1) = vv n + s (n + 1) * (Nat.fib (n + 1) : ℤ) :=
      Finset.sum_range_succ (fun k => s k * (Nat.fib k : ℤ)) (n + 1)
    have hu : uu (n + 1) =
        uu n + s (n + 1) * ((Nat.fib (n + 1 + 1) : ℤ) - (Nat.fib (n + 1) : ℤ)) :=
      Finset.sum_range_succ (fun k => s k * ((Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ))) (n + 1)
    rw [hp, ← hq, ← hr, hv, hu]
    simp only [map_add, map_mul, map_sub]
    ring

theorem a_eq (n : ℕ) : a (n + 1) = vv n := by
  obtain ⟨q, hq⟩ := red n
  show (p (n + 1 - 1) %ₘ (X ^ 2 - X - 1)).coeff 1 = vv n
  rw [show n + 1 - 1 = n by omega, modM (p n) q (uu n) (vv n) hq, coeff_add, coeff_C_mul_X,
    coeff_C, if_pos (show (1 : ℕ) = 1 from rfl), if_neg (show ¬ ((1 : ℕ) = 0) by omega), add_zero]

end poly

/-- b(k) = B(k+4,4) F(k) in ℚ. -/
def bq (k : ℕ) : ℚ := ((Nat.choose (k + 4) 4 : ℕ) : ℚ) * (Nat.fib k : ℚ)

/-- v(n) in ℚ, as partial sums of b. -/
def wq (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), bq k

theorem vv_q (n : ℕ) : ((vv n : ℤ) : ℚ) = wq n := by
  simp [vv, wq, bq, s]

theorem wq_succ (n : ℕ) : wq (n + 1) = wq n + bq (n + 1) :=
  Finset.sum_range_succ bq (n + 1)

theorem wq_zero : wq 0 = bq 0 := by
  simp [wq]

theorem sN (m : ℕ) : 24 * Nat.choose (m + 4) 4 = (m + 1) * (m + 2) * (m + 3) * (m + 4) := by
  induction m with
  | zero => decide
  | succ k ih =>
    have h := Nat.choose_mul_succ_eq (k + 4) 4
    rw [show k + 4 + 1 - 4 = k + 1 by omega] at h
    rw [show k + 1 + 4 = k + 4 + 1 by omega]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 1 by omega)
    calc (k + 1) * (24 * Nat.choose (k + 4 + 1) 4)
        = 24 * (Nat.choose (k + 4 + 1) 4 * (k + 1)) := by ring
      _ = 24 * (Nat.choose (k + 4) 4 * (k + 4 + 1)) := by rw [h]
      _ = (24 * Nat.choose (k + 4) 4) * (k + 4 + 1) := by ring
      _ = (k + 1) * ((k + 1 + 1) * (k + 1 + 2) * (k + 1 + 3) * (k + 4 + 1)) := by
        rw [ih]
        ring

theorem chq (m : ℕ) : ((Nat.choose (m + 4) 4 : ℕ) : ℚ) =
    ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4) / 24 := by
  have h' : (24 : ℚ) * ((Nat.choose (m + 4) 4 : ℕ) : ℚ) =
      ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4) := by
    exact_mod_cast sN m
  linarith

theorem bq_eq (k : ℕ) : bq k = ((k : ℚ) + 1) * ((k : ℚ) + 2) * ((k : ℚ) + 3) * ((k : ℚ) + 4) / 24 *
    (Nat.fib k : ℚ) := by
  show ((Nat.choose (k + 4) 4 : ℕ) : ℚ) * (Nat.fib k : ℚ) = _
  rw [chq k]

theorem fq (m : ℕ) : (Nat.fib (m + 2) : ℚ) = (Nat.fib m : ℚ) + (Nat.fib (m + 1) : ℚ) := by
  exact_mod_cast Nat.fib_add_two

theorem brec (m : ℕ) : bq (m + 10) - 5 * bq (m + 9) + 5 * bq (m + 8) + 10 * bq (m + 7) -
    15 * bq (m + 6) - 11 * bq (m + 5) + 15 * bq (m + 4) + 10 * bq (m + 3) - 5 * bq (m + 2) -
    5 * bq (m + 1) - bq m = 0 := by
  rw [bq_eq (m + 10), bq_eq (m + 9), bq_eq (m + 8), bq_eq (m + 7), bq_eq (m + 6), bq_eq (m + 5),
    bq_eq (m + 4), bq_eq (m + 3), bq_eq (m + 2), bq_eq (m + 1), bq_eq m]
  have f2 : (Nat.fib (m + 2) : ℚ) = (Nat.fib m : ℚ) + (Nat.fib (m + 1) : ℚ) := fq m
  have f3 : (Nat.fib (m + 3) : ℚ) = (Nat.fib (m + 1) : ℚ) + (Nat.fib (m + 2) : ℚ) := fq (m + 1)
  have f4 : (Nat.fib (m + 4) : ℚ) = (Nat.fib (m + 2) : ℚ) + (Nat.fib (m + 3) : ℚ) := fq (m + 2)
  have f5 : (Nat.fib (m + 5) : ℚ) = (Nat.fib (m + 3) : ℚ) + (Nat.fib (m + 4) : ℚ) := fq (m + 3)
  have f6 : (Nat.fib (m + 6) : ℚ) = (Nat.fib (m + 4) : ℚ) + (Nat.fib (m + 5) : ℚ) := fq (m + 4)
  have f7 : (Nat.fib (m + 7) : ℚ) = (Nat.fib (m + 5) : ℚ) + (Nat.fib (m + 6) : ℚ) := fq (m + 5)
  have f8 : (Nat.fib (m + 8) : ℚ) = (Nat.fib (m + 6) : ℚ) + (Nat.fib (m + 7) : ℚ) := fq (m + 6)
  have f9 : (Nat.fib (m + 9) : ℚ) = (Nat.fib (m + 7) : ℚ) + (Nat.fib (m + 8) : ℚ) := fq (m + 7)
  have f10 : (Nat.fib (m + 10) : ℚ) = (Nat.fib (m + 8) : ℚ) + (Nat.fib (m + 9) : ℚ) := fq (m + 8)
  rw [f10, f9, f8, f7, f6, f5, f4, f3, f2]
  push_cast
  ring

theorem bq_of (i v : ℕ) (h : Nat.choose (i + 4) 4 * Nat.fib i = v) : bq i = (v : ℚ) := by
  show ((Nat.choose (i + 4) 4 : ℕ) : ℚ) * (Nat.fib i : ℚ) = (v : ℚ)
  exact_mod_cast h

theorem w_mul : PowerSeries.mk wq * (1 - PowerSeries.X) = PowerSeries.mk bq := by
  have e : PowerSeries.mk wq * (1 - PowerSeries.X) =
      PowerSeries.mk wq - PowerSeries.mk wq * PowerSeries.X ^ 1 := by
    ring
  rw [e]
  ext n
  simp only [map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  cases n with
  | zero =>
    rw [if_neg (show ¬ (1 ≤ 0) by omega), wq_zero, sub_zero]
  | succ m =>
    rw [if_pos (show 1 ≤ m + 1 by omega), show m + 1 - 1 = m by omega, wq_succ]
    ring

theorem b_mul : PowerSeries.mk bq * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 5 =
    5 * PowerSeries.X - 10 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 -
      15 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 := by
  have b0 : bq 0 = 0 := by exact_mod_cast bq_of 0 0 (by decide)
  have b1 : bq 1 = 5 := by exact_mod_cast bq_of 1 5 (by decide)
  have b2 : bq 2 = 15 := by exact_mod_cast bq_of 2 15 (by decide)
  have b3 : bq 3 = 70 := by exact_mod_cast bq_of 3 70 (by decide)
  have b4 : bq 4 = 210 := by exact_mod_cast bq_of 4 210 (by decide)
  have b5 : bq 5 = 630 := by exact_mod_cast bq_of 5 630 (by decide)
  have b6 : bq 6 = 1680 := by exact_mod_cast bq_of 6 1680 (by decide)
  have b7 : bq 7 = 4290 := by exact_mod_cast bq_of 7 4290 (by decide)
  have b8 : bq 8 = 10395 := by exact_mod_cast bq_of 8 10395 (by decide)
  have b9 : bq 9 = 24310 := by exact_mod_cast bq_of 9 24310 (by decide)
  have e : PowerSeries.mk bq * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 5 =
      PowerSeries.mk bq
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk bq * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk bq * PowerSeries.X ^ 2)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * (PowerSeries.mk bq * PowerSeries.X ^ 3)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 * (PowerSeries.mk bq * PowerSeries.X ^ 4)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 11 * (PowerSeries.mk bq * PowerSeries.X ^ 5)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 * (PowerSeries.mk bq * PowerSeries.X ^ 6)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * (PowerSeries.mk bq * PowerSeries.X ^ 7)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk bq * PowerSeries.X ^ 8)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk bq * PowerSeries.X ^ 9)
        - PowerSeries.mk bq * PowerSeries.X ^ 10 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 11]
    ring
  have e2 : (5 * PowerSeries.X - 10 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 -
      15 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 : PowerSeries ℚ) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * PowerSeries.X ^ 1
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20 * PowerSeries.X ^ 3
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 * PowerSeries.X ^ 4
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * PowerSeries.X ^ 5 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15]
    ring
  rw [e, e2]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n
    · norm_num [b0]
    · norm_num [b0, b1]
    · norm_num [b0, b1, b2]
    · norm_num [b0, b1, b2, b3]
    · norm_num [b0, b1, b2, b3, b4]
    · norm_num [b0, b1, b2, b3, b4, b5]
    · norm_num [b0, b1, b2, b3, b4, b5, b6]
    · norm_num [b0, b1, b2, b3, b4, b5, b6, b7]
    · norm_num [b0, b1, b2, b3, b4, b5, b6, b7, b8]
    · norm_num [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [if_pos (show 1 ≤ k + 10 by omega), if_pos (show 2 ≤ k + 10 by omega),
      if_pos (show 3 ≤ k + 10 by omega), if_pos (show 4 ≤ k + 10 by omega),
      if_pos (show 5 ≤ k + 10 by omega), if_pos (show 6 ≤ k + 10 by omega),
      if_pos (show 7 ≤ k + 10 by omega), if_pos (show 8 ≤ k + 10 by omega),
      if_pos (show 9 ≤ k + 10 by omega), if_pos (show 10 ≤ k + 10 by omega),
      if_pos (show 1 ≤ k + 10 by omega), if_pos (show 2 ≤ k + 10 by omega),
      if_pos (show 3 ≤ k + 10 by omega), if_pos (show 4 ≤ k + 10 by omega),
      if_pos (show 5 ≤ k + 10 by omega),
      show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega,
      show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega,
      show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega,
      show k + 10 - 7 = k + 3 by omega, show k + 10 - 8 = k + 2 by omega,
      show k + 10 - 9 = k + 1 by omega, show k + 10 - 10 = k by omega,
      if_neg (show ¬ (k + 9 = 0) by omega), if_neg (show ¬ (k + 8 = 0) by omega),
      if_neg (show ¬ (k + 7 = 0) by omega), if_neg (show ¬ (k + 6 = 0) by omega),
      if_neg (show ¬ (k + 5 = 0) by omega)]
    linear_combination brec k

end P1A192249

open OMA.S_oeis_a192249 P1A192249 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192249.main := by
  have e1 : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk wq := by
    congr 1
    funext n
    show (a (n + 1) : ℚ) = wq n
    rw [a_eq, vv_q]
  have e2 : ((PowerSeries.X : PowerSeries ℚ) - 1) *
      ((PowerSeries.X : PowerSeries ℚ) ^ 2 + PowerSeries.X - 1) ^ 5 =
      (1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 5 := by
    ring
  rw [e1, e2]
  calc PowerSeries.X * PowerSeries.mk wq *
        ((1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 5)
      = PowerSeries.X * ((PowerSeries.mk wq * (1 - PowerSeries.X)) *
          (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 5) := by ring
    _ = PowerSeries.X * (PowerSeries.mk bq * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 5) := by
      rw [w_mul]
    _ = PowerSeries.X * (5 * PowerSeries.X - 10 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 -
          15 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5) := by
      rw [b_mul]
    _ = 5 * PowerSeries.X ^ 2 * (1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 -
          3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) := by
      ring
