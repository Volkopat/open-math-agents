import OMAStatements.S_oeis_a193649
import Mathlib

-- Problem: A193649, Q-residue of the (n+1)st Fibonacci polynomial with t(i,j) = 1; the g.f.
-- Credit: @xor2k
-- The argument follows the accepted proof of the template entry A193661 (downstep lemmas reused).
-- Proof: one downstep keeps p(2) + p(0) and the degree drops, so 2 * residue(p) = p(2) + p(0).
-- For row n, p(0) = 1 and p(2) = 2^n * F(n+1)(1/2) = g(n) with g(n+2) = g(n+1) + 4 g(n), so
-- 2 * a(n) = g(n) + 1, and the g.f. follows by comparison of coefficients.
namespace OMAa193649

open OMA.S_oeis_a193649 Polynomial Finset

theorem q_eval_two (k : ℕ) : (q k).eval 2 = 2 ^ (k + 1) - 1 := by
  rw [q, eval_finsetSum]
  simp only [eval_pow, eval_X]
  have hg := geom_sum_mul (2 : ℤ) (k + 1)
  have e : ∑ j ∈ range (k + 1), (2 : ℤ) ^ (k - j) = ∑ j ∈ range (k + 1), (2 : ℤ) ^ j := by
    rw [← sum_range_reflect (fun j => (2 : ℤ) ^ j) (k + 1)]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    congr 1
  rw [e]
  linarith

theorem q_eval_zero (k : ℕ) : (q k).eval 0 = 1 := by
  rw [q, eval_finsetSum, sum_eq_single k]
  · simp
  · intro j hj hjk
    rw [mem_range] at hj
    rw [eval_pow, eval_X, zero_pow (by omega)]
  · intro h
    simp at h

theorem q_deg (k : ℕ) : (q k).natDegree ≤ k := by
  rw [q]
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_X_pow_le _).trans (by omega)

theorem down_deg (p : ℤ[X]) : (down p).natDegree ≤ p.natDegree - 1 := by
  rw [down]
  split_ifs with h
  · omega
  · apply (natDegree_add_le _ _).trans
    rw [natDegree_C, max_le_iff]
    refine ⟨?_, by omega⟩
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [mem_range] at hi
    exact (natDegree_C_mul_le _ _).trans ((q_deg _).trans (by omega))

theorem eval_sum_shift (p : ℤ[X]) :
    ∑ i ∈ range p.natDegree, p.coeff (p.natDegree - i) * 2 ^ (p.natDegree - 1 - i + 1) +
      p.coeff 0 = p.eval 2 := by
  rw [eval_eq_sum_range, sum_range_succ']
  simp only [pow_zero, mul_one]
  congr 1
  rw [← sum_range_reflect (fun j => p.coeff (j + 1) * (2 : ℤ) ^ (j + 1)) p.natDegree]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  have e1 : p.natDegree - 1 - i + 1 = p.natDegree - i := by omega
  rw [e1]

theorem down_inv (p : ℤ[X]) :
    (down p).eval 2 + (down p).eval 0 = p.eval 2 + p.eval 0 := by
  rw [down]
  split_ifs with h
  · rfl
  · simp only [eval_add, eval_finsetSum, eval_mul, eval_C, q_eval_two, q_eval_zero]
    have key : ∑ i ∈ range p.natDegree,
          p.coeff (p.natDegree - i) * (2 ^ (p.natDegree - 1 - i + 1) - 1) +
        ∑ i ∈ range p.natDegree, p.coeff (p.natDegree - i) * 1 =
          ∑ i ∈ range p.natDegree, p.coeff (p.natDegree - i) * 2 ^ (p.natDegree - 1 - i + 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    have h2 := eval_sum_shift p
    have h3 := coeff_zero_eq_eval_zero p
    linarith

theorem iter (m : ℕ) : ∀ p : ℤ[X],
    ((down^[m]) p).natDegree ≤ p.natDegree - m ∧
      ((down^[m]) p).eval 2 + ((down^[m]) p).eval 0 = p.eval 2 + p.eval 0 := by
  induction m with
  | zero => intro p; simp
  | succ m ih =>
    intro p
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := ih (down p)
    refine ⟨h1.trans ?_, h2.trans (down_inv p)⟩
    have := down_deg p
    omega

theorem two_residue (p : ℤ[X]) : 2 * residue p = p.eval 2 + p.eval 0 := by
  obtain ⟨h1, h2⟩ := iter p.natDegree p
  have h0 : ((down^[p.natDegree]) p).natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero h0] at h2
  rw [residue, ← h2]
  simp only [eval_C]
  ring

theorem F_deg : ∀ n : ℕ, (F (n + 1)).natDegree ≤ n ∧ (F (n + 1)).coeff n = 1
  | 0 => by simp [F]
  | 1 => by simp [F]
  | n + 2 => by
    obtain ⟨h1, h2⟩ := F_deg (n + 1)
    obtain ⟨h3, h4⟩ := F_deg n
    have h1' : (F (n + 2)).natDegree ≤ n + 1 := h1
    have h2' : (F (n + 2)).coeff (n + 1) = 1 := h2
    have e : F (n + 3) = X * F (n + 2) + F (n + 1) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · apply (natDegree_add_le _ _).trans
      rw [max_le_iff]
      refine ⟨(natDegree_mul_le).trans ?_, by omega⟩
      rw [natDegree_X]
      omega
    · rw [coeff_add, coeff_X_mul, h2', coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

/-- `g n = 2^n * F (n+1) (1/2)`. -/
def g : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => g (n + 1) + 4 * g n

theorem F_half : ∀ n : ℕ,
    (2 : ℚ) ^ n * ((F (n + 1)).map (Int.castRingHom ℚ)).eval (1 / 2) = g n
  | 0 => by simp [F, g]
  | 1 => by simp [F, g]
  | n + 2 => by
    have h1 := F_half (n + 1)
    have h0 := F_half n
    have e : F (n + 3) = X * F (n + 2) + F (n + 1) := rfl
    rw [e, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, eval_add, eval_mul, eval_X]
    simp only [g, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    rw [← h1, ← h0]
    ring

theorem P_eval_two (n : ℕ) : (P n).eval 2 = g n := by
  have hq : (((P n).eval 2 : ℤ) : ℚ) = (2 : ℚ) ^ n *
      ((F (n + 1)).map (Int.castRingHom ℚ)).eval (1 / 2) := by
    rw [P, eval_finsetSum, eval_eq_sum_range' (n := n + 1)]
    · push_cast
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      simp only [eval_mul, eval_C, eval_pow, eval_X, coeff_map, T]
      push_cast
      have : (2 : ℚ) ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
      rw [this, div_pow, one_pow]
      field_simp
      rfl
    · have := (F_deg n).1
      have := natDegree_map_le (f := Int.castRingHom ℚ) (p := F (n + 1))
      omega
  rw [F_half] at hq
  exact_mod_cast hq

theorem P_eval_zero (n : ℕ) : (P n).eval 0 = 1 := by
  rw [P, eval_finsetSum, sum_eq_single n]
  · simp [T, (F_deg n).2]
  · intro k hk hkn
    rw [mem_range] at hk
    rw [eval_mul, eval_pow, eval_X, zero_pow (by omega), mul_zero]
  · intro h
    simp at h

theorem two_a (n : ℕ) : 2 * a n = g n + 1 := by
  have h := two_residue (P n)
  rw [P_eval_zero, P_eval_two] at h
  rw [a]
  exact h

theorem gf :
    PowerSeries.mk a * ((PowerSeries.X - 1) * (4 * PowerSeries.X ^ 2 + PowerSeries.X - 1)) =
      -((1 + PowerSeries.X) * (2 * PowerSeries.X - 1)) := by
  have e : PowerSeries.mk a * ((PowerSeries.X - 1) * (4 * PowerSeries.X ^ 2 + PowerSeries.X - 1)) =
      PowerSeries.C (4 : ℤ) * (PowerSeries.X ^ 3 * PowerSeries.mk a) -
        PowerSeries.C (3 : ℤ) * (PowerSeries.X ^ 2 * PowerSeries.mk a) -
        PowerSeries.C (2 : ℤ) * (PowerSeries.X ^ 1 * PowerSeries.mk a) + PowerSeries.mk a := by
    rw [show PowerSeries.C (4 : ℤ) = 4 by simp, show PowerSeries.C (3 : ℤ) = 3 by simp,
      show PowerSeries.C (2 : ℤ) = 2 by simp]
    ring
  have e2 : -((1 + PowerSeries.X) * (2 * PowerSeries.X - 1) : PowerSeries ℤ) =
      PowerSeries.C (1 : ℤ) - PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 1 -
        PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 := by
    rw [show PowerSeries.C (2 : ℤ) = 2 by simp]
    simp
    ring
  rw [e, e2]
  ext n
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  have h0 := two_a 0
  have h1 := two_a 1
  have h2 := two_a 2
  simp only [g] at h0 h1 h2
  rcases n with _ | _ | _ | n
  · simp
    omega
  · simp [PowerSeries.coeff_mk]
    omega
  · simp [PowerSeries.coeff_mk]
    omega
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, show n + 3 - 3 = n by omega, show n + 3 - 2 = n + 1 by omega,
      show n + 3 - 1 = n + 2 by omega]
    have k0 := two_a n
    have k1 := two_a (n + 1)
    have k2 := two_a (n + 2)
    have k3 := two_a (n + 3)
    have r2 : g (n + 2) = g (n + 1) + 4 * g n := rfl
    have r3 : g (n + 3) = g (n + 2) + 4 * g (n + 1) := rfl
    have : 2 * (4 * a n - 3 * a (n + 1) - 2 * a (n + 2) + a (n + 3)) = 0 := by
      linear_combination 4 * k0 - 3 * k1 - 2 * k2 + k3 + r3 - r2
    linarith

end OMAa193649

theorem OMA.solution : type_of% @OMA.S_oeis_a193649.main :=
  OMAa193649.gf
