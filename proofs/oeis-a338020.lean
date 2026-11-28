import OMAStatements.S_oeis_a338020
import Mathlib

namespace OMA.A338020Proof

open OMA.S_oeis_a338020

/-- For `n ≥ 1` the counted set is the integer interval `(⌊π (n - 1) ^ 2⌋₊, ⌈π n ^ 2⌉₊)`. -/
theorem set_eq (n : ℕ) (hn : 1 ≤ n) :
    {A : ℕ | 0 < A ∧ ((n : ℝ) - 1) < Real.sqrt ((A : ℝ) / Real.pi) ∧
      Real.sqrt ((A : ℝ) / Real.pi) < n} =
      ↑(Finset.Ioo ⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ ⌈(n : ℝ) ^ 2 * Real.pi⌉₊) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hv : (0 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 * Real.pi := by positivity
  ext A
  simp only [Set.mem_ofPred_eq, Finset.coe_Ioo, Set.mem_Ioo]
  rw [Real.lt_sqrt hn1, Real.sqrt_lt' hn0, lt_div_iff₀ hpi, div_lt_iff₀ hpi, Nat.floor_lt hv,
    Nat.lt_ceil]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    have h0 : (0 : ℝ) < A := lt_of_le_of_lt hv h1
    exact_mod_cast h0

theorem a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = (Finset.Ioo ⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ ⌈(n : ℝ) ^ 2 * Real.pi⌉₊).card := by
  unfold OMA.S_oeis_a338020.a
  rw [set_eq n hn, Set.ncard_coe_finset]

theorem a_add (n : ℕ) (hn : 1 ≤ n) :
    a n + ⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ + 1 = ⌈(n : ℝ) ^ 2 * Real.pi⌉₊ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv : (0 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 * Real.pi := by positivity
  have h1 : (⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ : ℝ) ≤ ((n : ℝ) - 1) ^ 2 * Real.pi := Nat.floor_le hv
  have h3 : (n : ℝ) ^ 2 * Real.pi ≤ ⌈(n : ℝ) ^ 2 * Real.pi⌉₊ := Nat.le_ceil _
  have hm : 0 < Real.pi * (2 * (n : ℝ) - 1) := mul_pos hpi (by linarith)
  have hlt : ((n : ℝ) - 1) ^ 2 * Real.pi < (n : ℝ) ^ 2 * Real.pi := by linarith
  have hfc : ⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ < ⌈(n : ℝ) ^ 2 * Real.pi⌉₊ := by
    have h : (⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ : ℝ) < ⌈(n : ℝ) ^ 2 * Real.pi⌉₊ := by linarith
    exact Nat.cast_lt.mp h
  rw [a_eq n hn, Nat.card_Ioo]
  omega

/-- `π (2 n - 1) - 1 ≤ a n < π (2 n - 1) + 1` for `n ≥ 1`. -/
theorem a_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * (2 * (n : ℝ) - 1) - 1 ≤ (a n : ℝ) ∧ (a n : ℝ) < Real.pi * (2 * (n : ℝ) - 1) + 1 := by
  have hv : (0 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 * Real.pi := by positivity
  have hu : (0 : ℝ) ≤ (n : ℝ) ^ 2 * Real.pi := by positivity
  have h1 : (⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ : ℝ) ≤ ((n : ℝ) - 1) ^ 2 * Real.pi := Nat.floor_le hv
  have h2 : ((n : ℝ) - 1) ^ 2 * Real.pi < ⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ + 1 :=
    Nat.lt_floor_add_one _
  have h3 : (n : ℝ) ^ 2 * Real.pi ≤ ⌈(n : ℝ) ^ 2 * Real.pi⌉₊ := Nat.le_ceil _
  have h4 : (⌈(n : ℝ) ^ 2 * Real.pi⌉₊ : ℝ) < (n : ℝ) ^ 2 * Real.pi + 1 := Nat.ceil_lt_add_one hu
  have h5 : ((a n + ⌊((n : ℝ) - 1) ^ 2 * Real.pi⌋₊ + 1 : ℕ) : ℝ) = (⌈(n : ℝ) ^ 2 * Real.pi⌉₊ : ℝ) := by
    rw [a_add n hn]
  simp only [Nat.cast_add, Nat.cast_one] at h5
  constructor <;> linarith

end OMA.A338020Proof

open OMA.S_oeis_a338020

theorem OMA.solution : type_of% @OMA.S_oeis_a338020.main := by
  intro k hk
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpk : Real.pi * 2 ≤ Real.pi * k := mul_le_mul_of_nonneg_left hk' Real.pi_pos.le
  obtain ⟨l0, u0⟩ := OMA.A338020Proof.a_bounds k (by omega)
  obtain ⟨l1, u1⟩ := OMA.A338020Proof.a_bounds (k + 1) (by omega)
  obtain ⟨l2, u2⟩ := OMA.A338020Proof.a_bounds (k + 2) (by omega)
  push_cast at l1 u1 l2 u2
  have r0 : (0 : ℝ) < a k := by linarith
  have r01 : (a k : ℝ) < a (k + 1) := by linarith
  have r12 : (a (k + 1) : ℝ) < a (k + 2) := by linarith
  have rt : (a (k + 2) : ℝ) < a k + a (k + 1) := by linarith
  have n0 : 0 < a k := by exact_mod_cast r0
  have n01 : a k < a (k + 1) := by exact_mod_cast r01
  have n12 : a (k + 1) < a (k + 2) := by exact_mod_cast r12
  have nt : a (k + 2) < a k + a (k + 1) := by exact_mod_cast rt
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega, by omega, by ring⟩
