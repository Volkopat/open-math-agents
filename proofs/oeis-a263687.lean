import OMAStatements.S_oeis_a263687
import Mathlib

open OMA.S_oeis_a263687


def EE (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (2 * k) : ℤ) * 2 ^ k
def OO (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (2 * k + 1) : ℤ) * 2 ^ k

theorem s0 (n : ℕ) : (Nat.stirlingFirst n 0 : ℤ) * n = 0 := by
  cases n with
  | zero => simp
  | succ n => simp

theorem OO_succ (n : ℕ) : OO (n + 1) = EE n + n * OO n := by
  unfold OO EE
  rw [Finset.sum_range_succ]
  have z1 : Nat.stirlingFirst n (2 * (n + 1) + 1) = 0 := Nat.stirlingFirst_eq_zero_of_lt (by omega)
  have z2 : Nat.stirlingFirst n (2 * (n + 1)) = 0 := Nat.stirlingFirst_eq_zero_of_lt (by omega)
  have : ∀ k, (Nat.stirlingFirst (n + 1) (2 * k + 1) : ℤ) * 2 ^ k =
      (Nat.stirlingFirst n (2 * k) : ℤ) * 2 ^ k + n * ((Nat.stirlingFirst n (2 * k + 1) : ℤ) * 2 ^ k) := by
    intro k
    rw [Nat.stirlingFirst_succ_succ]; push_cast; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, z1, z2]
  push_cast; ring

theorem EE_succ (n : ℕ) : EE (n + 1) = n * EE n + 2 * OO n := by
  unfold OO EE
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (Nat.stirlingFirst n (2 * k) : ℤ) * 2 ^ k)]
  have z2 : Nat.stirlingFirst n (2 * (n + 1)) = 0 := Nat.stirlingFirst_eq_zero_of_lt (by omega)
  have : ∀ k, (Nat.stirlingFirst (n + 1) (2 * (k + 1)) : ℤ) * 2 ^ (k + 1) =
      n * ((Nat.stirlingFirst n (2 * (k + 1)) : ℤ) * 2 ^ (k + 1)) +
        2 * ((Nat.stirlingFirst n (2 * k + 1) : ℤ) * 2 ^ k) := by
    intro k
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.stirlingFirst_succ_succ]; push_cast; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ (fun k => (Nat.stirlingFirst n (2 * (k + 1)) : ℤ) * 2 ^ (k + 1)), z2]
  have h0 := s0 n
  simp only [Nat.mul_zero, pow_zero, mul_one, Nat.stirlingFirst_succ_zero, Nat.cast_zero, Nat.cast_ofNat]
  push_cast
  linear_combination (-1 : ℤ) * h0

theorem poch_eq (n : ℕ) : poch n = ⟨EE n, OO n⟩ := by
  induction n with
  | zero => simp [poch, EE, OO]; rfl
  | succ n ih =>
    rw [poch, Finset.prod_range_succ, ← poch, ih]
    ext
    · simp [EE_succ]; ring
    · simp [OO_succ]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a263687.main := by
  intro n
  rw [a, poch_eq]
  show EE n = _
  unfold EE Stirling1
  rw [Finset.mul_sum]
  have hc : ∀ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℤ) ^ n * ((-1) ^ (n - 2 * k) * (Nat.stirlingFirst n (2 * k) : ℤ) * 2 ^ k) =
        (Nat.stirlingFirst n (2 * k) : ℤ) * 2 ^ k := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have : (-1 : ℤ) ^ n * (-1) ^ (n - 2 * k) = 1 := by
      rw [← pow_add, show n + (n - 2 * k) = 2 * (n - k) by omega, pow_mul]; norm_num
    linear_combination ((Nat.stirlingFirst n (2 * k) : ℤ) * 2 ^ k) * this
  rw [Finset.sum_congr rfl hc]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]
    simp
