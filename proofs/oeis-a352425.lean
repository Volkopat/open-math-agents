import OMAStatements.S_oeis_a352425
import Mathlib

open OMA.S_oeis_a352425

namespace P352425

theorem rs (l m : ℕ) : runSum l (2 * m + 1) = (2 * m + 1) * (l + m) := by
  unfold runSum
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h := Finset.sum_range_id_mul_two (2 * m + 1)
  rw [show 2 * m + 1 - 1 = 2 * m by omega] at h
  have : ∑ i ∈ Finset.range (2 * m + 1), i = (2 * m + 1) * m := by nlinarith
  rw [this]; ring

theorem tr_iff (n d : ℕ) : d ≤ triangularRoot n ↔ d * (d + 1) ≤ 2 * n := by
  unfold triangularRoot
  constructor
  · intro h
    have hs := Nat.findGreatest_spec (P := fun d => d * (d + 1) ≤ 2 * n) (m := 0) (Nat.zero_le n) (by simp)
    have : d * (d + 1) ≤ Nat.findGreatest (fun d => d * (d + 1) ≤ 2 * n) n *
        (Nat.findGreatest (fun d => d * (d + 1) ≤ 2 * n) n + 1) := Nat.mul_le_mul h (by omega)
    exact le_trans this hs
  · intro h
    exact Nat.le_findGreatest (P := fun d => d * (d + 1) ≤ 2 * n) (by nlinarith) h

end P352425

theorem OMA.solution : type_of% @OMA.S_oeis_a352425.main := by
  intro n hn
  apply Finset.sum_nbij' (fun z => z.2) (fun d => (n / d - (d - 1) / 2, d))
  · rintro ⟨l, d⟩ hz
    simp only [runs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hz
    obtain ⟨⟨⟨hl1, hln⟩, hd1, hdn⟩, ⟨m, rfl⟩, hs⟩ := hz
    rw [P352425.rs] at hs
    simp only [lengths, Finset.mem_filter, Nat.mem_divisors, P352425.tr_iff]
    refine ⟨⟨⟨l + m, hs.symm⟩, by omega⟩, ⟨m, rfl⟩, ?_⟩
    rw [← hs]; nlinarith
  · intro d hd
    simp only [lengths, Finset.mem_filter, Nat.mem_divisors, P352425.tr_iff] at hd
    obtain ⟨⟨⟨q, hq⟩, -⟩, ⟨m, rfl⟩, hle⟩ := hd
    have hdpos : 0 < 2 * m + 1 := by omega
    have hqd : n / (2 * m + 1) = q := by rw [hq]; exact Nat.mul_div_cancel_left q hdpos
    have hmq : m + 1 ≤ q := by
      rw [hq] at hle
      have : (2 * m + 1) * (2 * m + 2) ≤ (2 * m + 1) * (2 * q) := by nlinarith
      have := Nat.le_of_mul_le_mul_left this hdpos
      omega
    simp only [runs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_coe]
    rw [hqd, show (2 * m + 1 - 1) / 2 = m by omega]
    refine ⟨⟨⟨by omega, ?_⟩, by omega, ?_⟩, ⟨m, rfl⟩, ?_⟩
    · have : q ≤ (2 * m + 1) * q := Nat.le_mul_of_pos_left q hdpos
      omega
    · rw [hq]; nlinarith
    · rw [P352425.rs, show q - m + m = q by omega, hq]
  · rintro ⟨l, d⟩ hz
    simp only [runs, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hz
    obtain ⟨-, ⟨m, rfl⟩, hs⟩ := hz
    rw [P352425.rs] at hs
    simp only [Prod.mk.injEq, and_true]
    rw [← hs, Nat.mul_div_cancel_left _ (by omega), show (2 * m + 1 - 1) / 2 = m by omega]
    omega
  · intro d _; rfl
  · intro z _; rfl
