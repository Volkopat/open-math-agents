import OMAStatements.S_oeis_a081923
import Mathlib.Tactic

namespace OMA.S_oeis_a081923_proof

open OMA.S_oeis_a081923

private lemma add_one_mul_choose (n k : ℕ) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  by_cases hk : k ≤ n
  · have hpos : 0 < k.factorial * (n - k).factorial :=
      Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (n - k))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have hL : (n + 1).choose (k + 1) * (k + 1).factorial * (n - k).factorial = (n + 1).factorial := by
      rw [show n - k = (n + 1) - (k + 1) by omega]
      exact Nat.choose_mul_factorial_mul_factorial (by omega)
    have hR : n.choose k * k.factorial * (n - k).factorial = n.factorial :=
      Nat.choose_mul_factorial_mul_factorial hk
    calc
      (k + 1) * (n + 1).choose (k + 1) * (k.factorial * (n - k).factorial)
        = (n + 1).choose (k + 1) * ((k + 1) * k.factorial) * (n - k).factorial := by ring
      _ = (n + 1).choose (k + 1) * (k + 1).factorial * (n - k).factorial := by
          rw [Nat.factorial_succ k]
      _ = (n + 1).factorial := hL
      _ = (n + 1) * n.factorial := Nat.factorial_succ n
      _ = (n + 1) * (n.choose k * k.factorial * (n - k).factorial) := by rw [hR]
      _ = (n + 1) * n.choose k * (k.factorial * (n - k).factorial) := by ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < k + 1),
        Nat.choose_eq_zero_of_lt (by omega : n < k)]
    simp

private lemma choose_mul_sub_eq (m j : ℕ) (hj : j ≤ m) :
    (m + 1).choose j * (m + 1 - j) = (m + 1) * m.choose j := by
  have h1 : (m + 1).choose j = (m + 1).choose (m + 1 - j) :=
    (Nat.choose_symm (by omega)).symm
  have h2 : m.choose j = m.choose (m - j) := (Nat.choose_symm hj).symm
  have hsub : m + 1 - j = (m - j) + 1 := by omega
  rw [h1, h2, hsub, mul_comm _ (m - j + 1), add_one_mul_choose m (m - j)]

private lemma a_succ_split (m : ℕ) :
    a (m + 2) =
      2 * a (m + 1) +
        ∑ j ∈ Finset.range (m + 2), (m + 1).choose j * 2 ^ (m + 1 - j) * (j + 2).factorial := by
  let F : ℕ → ℕ := fun k => (m + 1).choose k * 2 ^ (m + 2 - k) * (k + 1).factorial
  have ha_expand :
      a (m + 2) =
        (∑ j ∈ Finset.range (m + 2), F (j + 1)) + F 0 +
          ∑ j ∈ Finset.range (m + 2), (m + 1).choose j * 2 ^ (m + 1 - j) * (j + 2).factorial := by
    rw [a, Finset.sum_range_succ']
    have h0 : (m + 2).choose 0 * 2 ^ (m + 2 - 0) * (0 + 1).factorial = F 0 := by simp [F]
    have hsum :
        (∑ j ∈ Finset.range (m + 2), (m + 2).choose (j + 1) * 2 ^ (m + 2 - (j + 1)) * (j + 1 + 1).factorial) =
          (∑ j ∈ Finset.range (m + 2), F (j + 1)) +
            ∑ j ∈ Finset.range (m + 2), (m + 1).choose j * 2 ^ (m + 1 - j) * (j + 2).factorial := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [F]
      rw [show m + 2 - (j + 1) = m + 1 - j by omega, show j + 1 + 1 = j + 2 by omega,
        Nat.choose_succ_succ]
      ring
    rw [hsum, h0]
    ring
  have hF_sum : (∑ j ∈ Finset.range (m + 2), F (j + 1)) + F 0 = 2 * a (m + 1) := by
    have hshift :
        (∑ j ∈ Finset.range (m + 2), F (j + 1)) + F 0 = ∑ k ∈ Finset.range (m + 3), F k :=
      (Finset.sum_range_succ' F (m + 2)).symm
    rw [hshift, Finset.sum_range_succ]
    have hlast : F (m + 2) = 0 := by
      simp [F]
    rw [hlast, add_zero, a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [F]
    rw [show m + 2 - k = (m + 1 - k) + 1 by omega, pow_succ']
    ring
  rw [ha_expand, hF_sum]

private lemma two_mul_pred_a (m : ℕ) :
    2 * (m + 1) * a m =
      ∑ j ∈ Finset.range (m + 2),
        (m + 1).choose j * 2 ^ (m + 1 - j) * (m + 1 - j) * (j + 1).factorial := by
  rw [Finset.sum_range_succ]
  have hlast : (m + 1).choose (m + 1) * 2 ^ (m + 1 - (m + 1)) * (m + 1 - (m + 1)) *
      (m + 1 + 1).factorial = 0 := by
    simp
  rw [hlast, add_zero, a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : 2 ^ (m + 1 - j) = 2 * 2 ^ (m - j) := by
    rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ']
  have hch := choose_mul_sub_eq m j hj_le
  calc
    2 * (m + 1) * (m.choose j * 2 ^ (m - j) * (j + 1).factorial)
      = ((m + 1) * m.choose j) * (2 * 2 ^ (m - j)) * (j + 1).factorial := by ring
    _ = ((m + 1).choose j * (m + 1 - j)) * 2 ^ (m + 1 - j) * (j + 1).factorial := by
        rw [← hch, ← hpow]
    _ = (m + 1).choose j * 2 ^ (m + 1 - j) * (m + 1 - j) * (j + 1).factorial := by ring

end OMA.S_oeis_a081923_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a081923.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, show m + 2 + 3 = m + 5 by omega]
  rw [OMA.S_oeis_a081923_proof.a_succ_split m, OMA.S_oeis_a081923_proof.two_mul_pred_a m, add_assoc]
  have hcomb :
      (∑ j ∈ Finset.range (m + 2),
          (m + 1).choose j * 2 ^ (m + 1 - j) * (j + 2).factorial) +
        ∑ j ∈ Finset.range (m + 2),
          (m + 1).choose j * 2 ^ (m + 1 - j) * (m + 1 - j) * (j + 1).factorial =
        (m + 3) * OMA.S_oeis_a081923.a (m + 1) := by
    rw [← Finset.sum_add_distrib, OMA.S_oeis_a081923.a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.factorial_succ (j + 1)]
    have hcoeff : (j + 2) + (m + 1 - j) = m + 3 := by omega
    calc
      (m + 1).choose j * 2 ^ (m + 1 - j) * ((j + 2) * (j + 1).factorial) +
          (m + 1).choose j * 2 ^ (m + 1 - j) * (m + 1 - j) * (j + 1).factorial
        = ((j + 2) + (m + 1 - j)) * ((m + 1).choose j * 2 ^ (m + 1 - j) * (j + 1).factorial) := by
          ring
      _ = (m + 3) * ((m + 1).choose j * 2 ^ (m + 1 - j) * (j + 1).factorial) := by rw [hcoeff]
  rw [hcomb]
  ring
