import OMAStatements.S_oeis_a193661
import Mathlib

-- Problem: A193661, Q-residue of the triangle A193673 with t(i,j) = 1; the g.f.
-- Credit: @jagong-cmu
-- Proof: one downstep keeps p(2) + p(0) and the degree drops, so 2 * residue(p) = p(2) + p(0).
-- For row n, 2 * T(n,k) = C(n,k) * (3^(n-k) + 1), so 4 * a(n) = 7^n + 3^n + 2, and the
-- g.f. follows by comparison of coefficients.
namespace OMAa193661

open OMA.S_oeis_a193661 Polynomial Finset

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

theorem two_T (n k : ℕ) :
    2 * T n k = (n.choose k : ℤ) * 3 ^ (n - k) + n.choose k := by
  have e : ((X + 3 : ℤ[X]) ^ n + (X + 1) ^ n).coeff k =
      (3 : ℤ) ^ (n - k) * (n.choose k : ℤ) + (n.choose k : ℤ) := by
    rw [coeff_add, show (X + 3 : ℤ[X]) = X + C 3 by simp, coeff_X_add_C_pow, coeff_X_add_one_pow]
  have hd : (2 : ℤ) ∣ ((X + 3 : ℤ[X]) ^ n + (X + 1) ^ n).coeff k := by
    rw [e]
    have ho : Odd ((3 : ℤ) ^ (n - k)) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := ho
    exact ⟨(n.choose k : ℤ) * (m + 1), by rw [hm]; ring⟩
  rw [T, Int.mul_ediv_cancel' hd, e]
  ring

theorem P_eval_two (n : ℕ) : 2 * (P n).eval 2 = 7 ^ n + 3 ^ n := by
  rw [P, eval_finsetSum, mul_sum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have e : ∀ k ∈ range (n + 1), 2 * (T n k * 2 ^ (n - k)) =
      1 ^ k * 6 ^ (n - k) * (n.choose k : ℤ) + 1 ^ k * 2 ^ (n - k) * (n.choose k : ℤ) := by
    intro k hk
    rw [mem_range] at hk
    rw [← mul_assoc, two_T n k, show (6 : ℤ) = 3 * 2 by norm_num, mul_pow]
    ring
  rw [sum_congr rfl e, sum_add_distrib, ← add_pow, ← add_pow]
  norm_num

theorem P_eval_zero (n : ℕ) : (P n).eval 0 = 1 := by
  rw [P, eval_finsetSum, sum_eq_single n]
  · have h := two_T n n
    simp only [Nat.choose_self, Nat.sub_self, pow_zero] at h
    simp only [eval_C, Nat.sub_self, pow_zero, mul_one]
    norm_num at h
    linarith
  · intro k hk hkn
    rw [mem_range] at hk
    rw [eval_mul, eval_pow, eval_X, zero_pow (by omega), mul_zero]
  · intro h
    simp at h

theorem four_a (n : ℕ) : 4 * a n = 7 ^ n + 3 ^ n + 2 := by
  have h := two_residue (P n)
  have h2 := P_eval_two n
  rw [P_eval_zero] at h
  rw [a]
  linarith

theorem gf :
    PowerSeries.mk a * ((PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (7 * PowerSeries.X - 1)) =
      -1 + 8 * PowerSeries.X - 13 * PowerSeries.X ^ 2 := by
  have e : PowerSeries.mk a * ((PowerSeries.X - 1) * (3 * PowerSeries.X - 1) *
        (7 * PowerSeries.X - 1)) =
      PowerSeries.C (21 : ℤ) * (PowerSeries.X ^ 3 * PowerSeries.mk a) -
        PowerSeries.C (31 : ℤ) * (PowerSeries.X ^ 2 * PowerSeries.mk a) +
        PowerSeries.C (11 : ℤ) * (PowerSeries.X ^ 1 * PowerSeries.mk a) - PowerSeries.mk a := by
    rw [show PowerSeries.C (21 : ℤ) = 21 by simp, show PowerSeries.C (31 : ℤ) = 31 by simp,
      show PowerSeries.C (11 : ℤ) = 11 by simp]
    ring
  have e2 : (-1 : PowerSeries ℤ) + 8 * PowerSeries.X - 13 * PowerSeries.X ^ 2 =
      PowerSeries.C (8 : ℤ) * PowerSeries.X ^ 1 - PowerSeries.C (13 : ℤ) * PowerSeries.X ^ 2 -
        PowerSeries.C (1 : ℤ) := by
    rw [show PowerSeries.C (8 : ℤ) = 8 by simp, show PowerSeries.C (13 : ℤ) = 13 by simp]
    simp
    ring
  rw [e, e2]
  ext n
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  have h0 := four_a 0
  have h1 := four_a 1
  have h2 := four_a 2
  norm_num at h0 h1 h2
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
    have k0 := four_a n
    have k1 := four_a (n + 1)
    have k2 := four_a (n + 2)
    have k3 := four_a (n + 3)
    rw [pow_succ, pow_succ (3 : ℤ)] at k1
    rw [pow_succ, pow_succ, pow_succ (3 : ℤ), pow_succ (3 : ℤ)] at k2
    rw [pow_succ, pow_succ, pow_succ, pow_succ (3 : ℤ), pow_succ (3 : ℤ), pow_succ (3 : ℤ)] at k3
    have : 4 * (21 * a n - 31 * a (n + 1) + 11 * a (n + 2) - a (n + 3)) = 0 := by
      linear_combination 21 * k0 - 31 * k1 + 11 * k2 - k3
    linarith

end OMAa193661

theorem OMA.solution : type_of% @OMA.S_oeis_a193661.main :=
  OMAa193661.gf
