import OMAStatements.S_oeis_a193656
import Mathlib

-- Problem: A193656, Q-residue of rows 2^(n-k)*5^k with t(i,j) = 1; closed form and g.f.
-- Credit: @jagong-cmu
-- Proof: q(k) takes the values 2^(k+1)-1 at 2 and 1 at 0, so one downstep keeps
-- p(2) + p(0). The degree drops at each step, so 2 * residue(p) = p(2) + p(0). For row n
-- this is 5^(n+1) - 4^(n+1) + 5^n. The g.f. follows from the closed form.
namespace OMAa193656

open OMA.S_oeis_a193656 Polynomial Finset

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

theorem P_eval_two (n : ℕ) : (P n).eval 2 = 5 ^ (n + 1) - 4 ^ (n + 1) := by
  rw [P, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have e : ∀ k ∈ range (n + 1), (2 : ℤ) ^ (n - k) * 5 ^ k * 2 ^ (n - k) =
      5 ^ k * 4 ^ (n + 1 - 1 - k) := by
    intro k hk
    rw [show n + 1 - 1 - k = n - k by omega, show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
    ring
  rw [sum_congr rfl e, ← mul_one (∑ k ∈ range (n + 1), (5 : ℤ) ^ k * 4 ^ (n + 1 - 1 - k)),
    show (1 : ℤ) = 5 - 4 by norm_num, geom_sum₂_mul]

theorem P_eval_zero (n : ℕ) : (P n).eval 0 = 5 ^ n := by
  rw [P, eval_finsetSum, sum_eq_single n]
  · simp
  · intro k hk hkn
    rw [mem_range] at hk
    rw [eval_mul, eval_pow, eval_X, zero_pow (by omega), mul_zero]
  · intro h
    simp at h

theorem closed (n : ℕ) : a n = 3 * 5 ^ n - 2 * 4 ^ n := by
  have h := two_residue (P n)
  rw [P_eval_two, P_eval_zero] at h
  rw [a]
  have : (2 : ℤ) * residue (P n) = 2 * (3 * 5 ^ n - 2 * 4 ^ n) := by
    rw [h, pow_succ, pow_succ]
    ring
  linarith

theorem gf :
    PowerSeries.mk a * ((5 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1)) =
      1 - 2 * PowerSeries.X := by
  have e : PowerSeries.mk a * ((5 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1)) =
      PowerSeries.C (20 : ℤ) * (PowerSeries.X ^ 2 * PowerSeries.mk a) -
        PowerSeries.C (9 : ℤ) * (PowerSeries.X ^ 1 * PowerSeries.mk a) + PowerSeries.mk a := by
    rw [show PowerSeries.C (20 : ℤ) = 20 by simp, show PowerSeries.C (9 : ℤ) = 9 by simp]
    ring
  have e2 : (1 : PowerSeries ℤ) - 2 * PowerSeries.X =
      PowerSeries.C (1 : ℤ) - PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 1 := by
    rw [show PowerSeries.C (2 : ℤ) = 2 by simp]
    simp
  rw [e, e2]
  ext n
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | n
  · simp [closed]
  · simp [closed]
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, closed, closed, closed,
      show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega]
    ring

theorem sol :
    (∀ n : ℕ, a n = 3 * 5 ^ n - 2 * 4 ^ n) ∧
      PowerSeries.mk a * ((5 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1)) =
        1 - 2 * PowerSeries.X :=
  ⟨closed, gf⟩

end OMAa193656

theorem OMA.solution : type_of% @OMA.S_oeis_a193656.main :=
  OMAa193656.sol
