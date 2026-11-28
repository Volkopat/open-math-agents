import OMAStatements.S_oeis_a193662
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A193662 (statement by @ivillar).
-- Idea: r(0) = 1 and r(k) = 2^(k-1) for k ≥ 1, so 2*a(n) = 2^n * L(n, 1/2) + [x^n]L(n,x) for n ≥ 1
-- (the k = n term carries r(0) = 1 instead of 1/2). The Lucas recurrence gives
-- w(n) = 2^n * L(n,1/2) with w(n) = w(n-1) + 4*w(n-2), and the leading coefficient [x^n]L(n,x) is the
-- same for all n ≥ 1. As (t^2 - t - 4)*(t - 1) = t^3 - 2t^2 - 3t + 4, the recurrence follows for n > 3.

namespace OMAA193662Helpers

open Polynomial OMA.S_oeis_a193662

theorem r_one : r 1 = 1 := by
  rw [r.eq_2]
  simp [r.eq_1]

theorem r_succ_succ (k : ℕ) : r (k + 2) = 2 * r (k + 1) := by
  rw [r.eq_2 (k + 1), Fin.sum_univ_succ]
  have h : ∑ i : Fin (k + 1), r (k + 1 - ((Fin.succ i : Fin (k + 2)) : ℕ)) = r (k + 1) := by
    rw [r.eq_2 k]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_succ]
    congr 1
    omega
  rw [h]
  simp only [Fin.val_zero, Nat.sub_zero]
  ring

theorem r_pow (m : ℕ) : r (m + 1) = 2 ^ m := by
  induction m with
  | zero => simpa using r_one
  | succ m ih => rw [r_succ_succ, ih]; ring

theorem L_deg : ∀ n : ℕ, (L n).natDegree ≤ n ∧ (L (n + 1)).natDegree ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [L]
    · simp only [L]; exact natDegree_X_le
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show (X * L (n + 1) + L n).natDegree ≤ n + 2
    have hX : (X : ℤ[X]).natDegree ≤ 1 := natDegree_X_le
    calc (X * L (n + 1) + L n).natDegree ≤ max (X * L (n + 1)).natDegree (L n).natDegree :=
          natDegree_add_le _ _
      _ ≤ n + 2 := max_le (le_trans natDegree_mul_le (by omega)) (by omega)

theorem L_coeff_hi (n : ℕ) : (L n).coeff (n + 2) = 0 :=
  coeff_eq_zero_of_natDegree_lt (by have := (L_deg n).1; omega)

theorem L_top (n : ℕ) : (L (n + 2)).coeff (n + 2) = (L (n + 1)).coeff (n + 1) := by
  show (X * L (n + 1) + L n).coeff (n + 2) = _
  rw [coeff_add, coeff_X_mul, L_coeff_hi, add_zero]

/-- ev(n) = L(n, 1/2). -/
noncomputable def ev (n : ℕ) : ℚ := eval₂ (Int.castRingHom ℚ) (1 / 2) (L n)

theorem ev_rec (n : ℕ) : ev (n + 2) = 1 / 2 * ev (n + 1) + ev n := by
  simp only [ev, L, eval₂_add, eval₂_mul, eval₂_X]

theorem key (m : ℕ) :
    2 * (a (m + 1) : ℚ) = 2 ^ (m + 1) * ev (m + 1) + ((L (m + 1)).coeff (m + 1) : ℚ) := by
  have hd : (L (m + 1)).natDegree < m + 2 := by have := (L_deg m).2; omega
  unfold a ev
  rw [eval₂_eq_sum_range' _ hd]
  simp only [eq_intCast]
  push_cast
  conv_lhs => rw [Finset.sum_range_succ]
  conv_rhs => rw [Finset.sum_range_succ]
  have hsum : 2 * ∑ x ∈ Finset.range (m + 1), ((L (m + 1)).coeff x : ℚ) * (r (m + 1 - x) : ℚ) =
      2 ^ (m + 1) * ∑ x ∈ Finset.range (m + 1), ((L (m + 1)).coeff x : ℚ) * (1 / 2) ^ x := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨t, rfl⟩ : ∃ t, m = k + t := ⟨m - k, by omega⟩
    rw [show k + t + 1 - k = t + 1 by omega, r_pow]
    push_cast
    have e : (2 : ℚ) ^ (k + t + 1) * (1 / 2) ^ k = 2 ^ (t + 1) := by
      rw [show k + t + 1 = (t + 1) + k by ring, pow_add, mul_assoc, ← mul_pow]
      norm_num
    linear_combination (-((L (k + t + 1)).coeff k : ℚ)) * e
  rw [Nat.sub_self, r.eq_1]
  have e2 : (2 : ℚ) ^ (m + 1) * (1 / 2) ^ (m + 1) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  linear_combination hsum - ((L (m + 1)).coeff (m + 1) : ℚ) * e2

end OMAA193662Helpers

open Polynomial OMA.S_oeis_a193662 OMAA193662Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a193662.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = (k + 2) + 1 by omega, show k + 4 - 2 = (k + 1) + 1 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 = (k + 3) + 1 by omega]
  have h4 := key (k + 3)
  have h3 := key (k + 2)
  have h2 := key (k + 1)
  have h1 := key k
  have t4 : (L (k + 3 + 1)).coeff (k + 3 + 1) = (L (k + 2 + 1)).coeff (k + 2 + 1) := L_top (k + 2)
  have t3 : (L (k + 2 + 1)).coeff (k + 2 + 1) = (L (k + 1 + 1)).coeff (k + 1 + 1) := L_top (k + 1)
  have t2 : (L (k + 1 + 1)).coeff (k + 1 + 1) = (L (k + 1)).coeff (k + 1) := L_top k
  have r4 : ev (k + 3 + 1) = 1 / 2 * ev (k + 2 + 1) + ev (k + 1 + 1) := ev_rec (k + 2)
  have r3 : ev (k + 2 + 1) = 1 / 2 * ev (k + 1 + 1) + ev (k + 1) := ev_rec (k + 1)
  have q : (2 : ℚ) * ((a (k + 3 + 1) : ℚ) - (2 * a (k + 2 + 1) + 3 * a (k + 1 + 1) - 4 * a (k + 1))) = 0 := by
    rw [mul_sub, mul_sub, mul_add, h4]
    have t4' : ((L (k + 3 + 1)).coeff (k + 3 + 1) : ℚ) = (L (k + 1)).coeff (k + 1) := by
      rw [t4, t3, t2]
    have t3' : ((L (k + 2 + 1)).coeff (k + 2 + 1) : ℚ) = (L (k + 1)).coeff (k + 1) := by
      rw [t3, t2]
    have t2' : ((L (k + 1 + 1)).coeff (k + 1 + 1) : ℚ) = (L (k + 1)).coeff (k + 1) := by
      rw [t2]
    linear_combination t4' - 2 * h3 - 3 * h2 + 4 * h1 + 2 ^ (k + 4) * r4 - 2 ^ (k + 3) * r3 -
      2 * t3' - 3 * t2'
  have q' : ((a (k + 3 + 1) : ℚ) - (2 * a (k + 2 + 1) + 3 * a (k + 1 + 1) - 4 * a (k + 1))) = 0 := by
    linarith
  have : ((a (k + 3 + 1) - (2 * a (k + 2 + 1) + 3 * a (k + 1 + 1) - 4 * a (k + 1)) : ℤ) : ℚ) = 0 := by
    push_cast; linarith
  have := Int.cast_eq_zero.mp this
  linarith
