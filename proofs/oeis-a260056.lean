import OMAStatements.S_oeis_a260056
import Mathlib

open Polynomial OMA.S_oeis_a260056

lemma OMA.pasg (q : ℤ[X]) (k : ℕ) : (q * (1 + X + X ^ 2)).coeff k =
    q.coeff k + (if 1 ≤ k then q.coeff (k - 1) else 0) + (if 2 ≤ k then q.coeff (k - 2) else 0) := by
  rw [show q * (1 + X + X ^ 2) = q + q * X ^ 1 + q * X ^ 2 by ring, coeff_add, coeff_add,
    coeff_mul_X_pow', coeff_mul_X_pow']

lemma OMA.pasp (n k : ℕ) : ((1 + X + X ^ 2 : ℤ[X]) ^ (n + 1)).coeff k =
    ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k +
      (if 1 ≤ k then ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (k - 1) else 0) +
      (if 2 ≤ k then ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (k - 2) else 0) := by
  rw [pow_succ (1 + X + X ^ 2 : ℤ[X]) n]
  exact OMA.pasg _ k

lemma OMA.core1 (t : ℕ → ℕ → ℤ)
    (pas : ∀ n k, t (n + 1) k = t n k + (if 1 ≤ k then t n (k - 1) else 0) +
      (if 2 ≤ k then t n (k - 2) else 0))
    (t0 : ∀ k, t 0 k = if k = 0 then 1 else 0) :
    ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ∑ j ∈ Finset.range (n - k + 1), t j k) =
      (((n + 3) / 4 + (n + 4) / 4 : ℕ) : ℤ) := by
  have z : ∀ s, t 0 (s + 1) = 0 := fun s => by
    rw [t0]
    simp
  have hrec : ∀ s, (∑ k ∈ Finset.range (s + 4), (-1 : ℤ) ^ k * t (s + 3 - k) k) =
      (∑ k ∈ Finset.range (s + 3), (-1 : ℤ) ^ k * t (s + 2 - k) k) -
      (∑ k ∈ Finset.range (s + 2), (-1 : ℤ) ^ k * t (s + 1 - k) k) +
      ∑ k ∈ Finset.range (s + 1), (-1 : ℤ) ^ k * t (s - k) k := by
    intro s
    have hA : ∑ k ∈ Finset.range (s + 3), (-1 : ℤ) ^ k * t (s + 3 - k) k =
        ∑ k ∈ Finset.range (s + 3), ((-1 : ℤ) ^ k * t (s + 2 - k) k +
          (-1 : ℤ) ^ k * (if 1 ≤ k then t (s + 2 - k) (k - 1) else 0) +
          (-1 : ℤ) ^ k * (if 2 ≤ k then t (s + 2 - k) (k - 2) else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < s + 3 := Finset.mem_range.1 hk
      rw [show s + 3 - k = s + 2 - k + 1 by omega, pas]
      ring
    have hB : ∑ k ∈ Finset.range (s + 3),
        (-1 : ℤ) ^ k * (if 1 ≤ k then t (s + 2 - k) (k - 1) else 0) =
        -∑ k ∈ Finset.range (s + 2), (-1 : ℤ) ^ k * t (s + 1 - k) k := by
      rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib]
      simp only [show ¬ (1 ≤ 0) by omega, if_false, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_pos (show 1 ≤ j + 1 by omega), show s + 2 - (j + 1) = s + 1 - j by omega,
        show j + 1 - 1 = j by omega, pow_succ]
      ring
    have hC : ∑ k ∈ Finset.range (s + 3),
        (-1 : ℤ) ^ k * (if 2 ≤ k then t (s + 2 - k) (k - 2) else 0) =
        ∑ k ∈ Finset.range (s + 1), (-1 : ℤ) ^ k * t (s - k) k := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [show ¬ (2 ≤ 0) by omega, show ¬ (2 ≤ 0 + 1) by omega, if_false, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_pos (show 2 ≤ j + 1 + 1 by omega), show s + 2 - (j + 1 + 1) = s - j by omega,
        show j + 1 + 1 - 2 = j by omega, pow_succ, pow_succ]
      ring
    rw [Finset.sum_range_succ, show s + 3 - (s + 3) = 0 by omega, z (s + 2), mul_zero, add_zero, hA,
      Finset.sum_add_distrib, Finset.sum_add_distrib, hB, hC]
    ring
  have aux : ∀ s,
      ((∑ k ∈ Finset.range (s + 1), (-1 : ℤ) ^ k * t (s - k) k) = if s % 4 < 2 then 1 else 0) ∧
      ((∑ k ∈ Finset.range (s + 2), (-1 : ℤ) ^ k * t (s + 1 - k) k) =
        if (s + 1) % 4 < 2 then 1 else 0) ∧
      ((∑ k ∈ Finset.range (s + 3), (-1 : ℤ) ^ k * t (s + 2 - k) k) =
        if (s + 2) % 4 < 2 then 1 else 0) := by
    intro s
    induction s with
    | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [Finset.sum_range_succ, pas, t0]
    | succ s ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have h := hrec s
      rw [h0, h1, h2] at h
      show (∑ k ∈ Finset.range (s + 4), (-1 : ℤ) ^ k * t (s + 3 - k) k) =
        if (s + 3) % 4 < 2 then 1 else 0
      rw [h]
      split_ifs <;> omega
  have hD : ∀ n, (∑ k ∈ Finset.range (n + 2),
        (-1 : ℤ) ^ k * ∑ j ∈ Finset.range (n + 1 - k + 1), t j k) =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ∑ j ∈ Finset.range (n - k + 1), t j k) +
      ∑ k ∈ Finset.range (n + 2), (-1 : ℤ) ^ k * t (n + 1 - k) k := by
    intro n
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => (-1 : ℤ) ^ k * t (n + 1 - k) k)]
    rw [show n + 1 - (n + 1) = 0 by omega]
    simp only [zero_add, Finset.sum_range_one, z n, mul_zero, add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.1 hk
    rw [show n + 1 - k + 1 = (n - k + 1) + 1 by omega, Finset.sum_range_succ,
      show n - k + 1 = n + 1 - k by omega]
    ring
  intro n
  induction n with
  | zero => simp [t0]
  | succ n ih =>
    have h := hD n
    have e : (∑ k ∈ Finset.range (n + 2), (-1 : ℤ) ^ k * t (n + 1 - k) k) =
        if (n + 1) % 4 < 2 then 1 else 0 := (aux (n + 1)).1
    show (∑ k ∈ Finset.range (n + 2), (-1 : ℤ) ^ k * ∑ j ∈ Finset.range (n + 1 - k + 1), t j k) = _
    rw [h, ih, e]
    split_ifs <;> omega

lemma OMA.coeff_fsum (s : Finset ℕ) (f : ℕ → ℤ[X]) (k : ℕ) :
    (∑ m ∈ s, f m).coeff k = ∑ m ∈ s, (f m).coeff k := by
  simpa only [lcoeff_apply] using map_sum (lcoeff ℤ k) f s

lemma OMA.altsum {R : Type} [CommRing R] (x : R) (K : ℕ) :
    ∑ m ∈ Finset.range (K + 1), ((-1 : R) ^ m * (K.choose m : R)) * x ^ m = (1 - x) ^ K := by
  rw [show (1 - x) = -x + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro m _
  rw [one_pow, mul_one, neg_pow]
  ring

lemma OMA.part2 (n k : ℕ) :
    (∑ m ∈ Finset.range (k + 3), (-1 : ℤ) ^ m *
      (∑ j ∈ Finset.range (n + m + 1), (1 + X + X ^ 2 : ℤ[X]) ^ j).coeff k *
        ((k + 2).choose m : ℤ)) = 0 := by
  have hne : (1 + X + X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun q : ℤ[X] => q.coeff 1) h
    simp at this
  have e : ∀ m : ℕ, (1 + X + X ^ 2 - 1 : ℤ[X]) *
      (((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) *
        ∑ j ∈ Finset.range (n + m + 1), (1 + X + X ^ 2 : ℤ[X]) ^ j) =
      (1 + X + X ^ 2) ^ (n + 1) *
          (((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) * (1 + X + X ^ 2) ^ m) -
        ((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) * 1 ^ m := by
    intro m
    have g := mul_geom_sum (1 + X + X ^ 2 : ℤ[X]) (n + m + 1)
    linear_combination ((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) * g
  have hS : (1 + X + X ^ 2 - 1 : ℤ[X]) *
      (∑ m ∈ Finset.range (k + 2 + 1), ((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) *
        ∑ j ∈ Finset.range (n + m + 1), (1 + X + X ^ 2 : ℤ[X]) ^ j) =
      (1 + X + X ^ 2 - 1) *
        (-((1 + X + X ^ 2) ^ (n + 1) * (1 - (1 + X + X ^ 2)) ^ (k + 1))) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib,
      ← Finset.mul_sum, OMA.altsum, OMA.altsum]
    ring
  have hS' := mul_left_cancel₀ hne hS
  have hc : (∑ m ∈ Finset.range (k + 2 + 1), ((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) *
        ∑ j ∈ Finset.range (n + m + 1), (1 + X + X ^ 2 : ℤ[X]) ^ j).coeff k = 0 := by
    rw [hS', show (1 - (1 + X + X ^ 2) : ℤ[X]) = (-(1 + X)) * X by ring, mul_pow,
      show -((1 + X + X ^ 2 : ℤ[X]) ^ (n + 1) * ((-(1 + X)) ^ (k + 1) * X ^ (k + 1))) =
        (-((1 + X + X ^ 2) ^ (n + 1) * (-(1 + X)) ^ (k + 1))) * X ^ (k + 1) by ring,
      coeff_mul_X_pow', if_neg (show ¬ (k + 1 ≤ k) by omega)]
  rw [OMA.coeff_fsum] at hc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro m _
  rw [show ((-1 : ℤ[X]) ^ m * ((k + 2).choose m : ℤ[X])) =
      C ((-1 : ℤ) ^ m * ((k + 2).choose m : ℤ)) by simp, coeff_C_mul]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a260056.main := by
  refine ⟨fun n => ?_, fun n k => ?_⟩
  · have h := OMA.core1 (fun j k => ((1 + X + X ^ 2 : ℤ[X]) ^ j).coeff k) OMA.pasp
      (fun k => by simp [coeff_one]) n
    simp only [T, row, OMA.coeff_fsum]
    exact h
  · simp only [T, row]
    exact OMA.part2 n k
