import OMAStatements.S_oeis_a208138
import Mathlib

namespace A208138Aux

def R : List ℕ := [0, 4, 5, 8, 10, 12, 13, 14, 15]

open OMA.S_oeis_a208138 in
lemma rows_eq : rows 4 1 3 = R := by decide +kernel

open OMA.S_oeis_a208138 in
lemma b0 : below R 0 = [0] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b4 : below R 4 = [0, 4] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b5 : below R 5 = [0, 4, 5] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b8 : below R 8 = [0, 8] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b10 : below R 10 = [0, 8, 10] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b12 : below R 12 = [0, 4, 8, 12] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b13 : below R 13 = [0, 4, 5, 8, 12, 13] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b14 : below R 14 = [0, 4, 8, 10, 12, 14] := by decide +kernel
open OMA.S_oeis_a208138 in
lemma b15 : below R 15 = [0, 4, 5, 8, 10, 12, 13, 14, 15] := by decide +kernel

lemma flat_len (f : ℕ → List (List ℕ)) (L : List ℕ) :
    (L.flatMap fun s => (f s).map (s :: ·)).length = (L.map fun s => (f s).length).sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, List.map_cons, List.sum_cons, ih]

open OMA.S_oeis_a208138 in
lemma tails_len (rs : List ℕ) (h r : ℕ) :
    (tails rs (h + 1) r).length = ((below rs r).map fun s => (tails rs h s).length).sum :=
  flat_len (tails rs h) (below rs r)

open OMA.S_oeis_a208138 in
lemma tails_zero (rs : List ℕ) (r : ℕ) : (tails rs 0 r).length = 1 := rfl

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a208138 in
lemma key (h : ℕ) :
    ((tails R h 0).length : ℤ) = 1 ∧
    ((tails R h 4).length : ℤ) = (h : ℤ) + 1 ∧
    ((tails R h 8).length : ℤ) = (h : ℤ) + 1 ∧
    2 * ((tails R h 5).length : ℤ) = ((h : ℤ) + 1) * ((h : ℤ) + 2) ∧
    2 * ((tails R h 10).length : ℤ) = ((h : ℤ) + 1) * ((h : ℤ) + 2) ∧
    ((tails R h 12).length : ℤ) = ((h : ℤ) + 1) ^ 2 ∧
    2 * ((tails R h 13).length : ℤ) = ((h : ℤ) + 1) ^ 2 * ((h : ℤ) + 2) ∧
    2 * ((tails R h 14).length : ℤ) = ((h : ℤ) + 1) ^ 2 * ((h : ℤ) + 2) ∧
    4 * ((tails R h 15).length : ℤ) = ((h : ℤ) + 1) ^ 2 * ((h : ℤ) + 2) ^ 2 := by
  induction h with
  | zero =>
    simp only [tails_zero]
    norm_num
  | succ h ih =>
    obtain ⟨h0, h4, h8, h5, h10, h12, h13, h14, h15⟩ := ih
    have e0 : (tails R (h + 1) 0).length = (tails R h 0).length + 0 := by
      have t := tails_len R h 0
      rw [b0] at t
      exact t
    have e4 : (tails R (h + 1) 4).length = (tails R h 0).length + ((tails R h 4).length + 0) := by
      have t := tails_len R h 4
      rw [b4] at t
      exact t
    have e5 : (tails R (h + 1) 5).length = (tails R h 0).length + ((tails R h 4).length + ((tails R h 5).length + 0)) := by
      have t := tails_len R h 5
      rw [b5] at t
      exact t
    have e8 : (tails R (h + 1) 8).length = (tails R h 0).length + ((tails R h 8).length + 0) := by
      have t := tails_len R h 8
      rw [b8] at t
      exact t
    have e10 : (tails R (h + 1) 10).length = (tails R h 0).length + ((tails R h 8).length + ((tails R h 10).length + 0)) := by
      have t := tails_len R h 10
      rw [b10] at t
      exact t
    have e12 : (tails R (h + 1) 12).length = (tails R h 0).length + ((tails R h 4).length + ((tails R h 8).length + ((tails R h 12).length + 0))) := by
      have t := tails_len R h 12
      rw [b12] at t
      exact t
    have e13 : (tails R (h + 1) 13).length = (tails R h 0).length + ((tails R h 4).length + ((tails R h 5).length + ((tails R h 8).length + ((tails R h 12).length + ((tails R h 13).length + 0))))) := by
      have t := tails_len R h 13
      rw [b13] at t
      exact t
    have e14 : (tails R (h + 1) 14).length = (tails R h 0).length + ((tails R h 4).length + ((tails R h 8).length + ((tails R h 10).length + ((tails R h 12).length + ((tails R h 14).length + 0))))) := by
      have t := tails_len R h 14
      rw [b14] at t
      exact t
    have e15 : (tails R (h + 1) 15).length = (tails R h 0).length + ((tails R h 4).length + ((tails R h 5).length + ((tails R h 8).length + ((tails R h 10).length + ((tails R h 12).length + ((tails R h 13).length + ((tails R h 14).length + ((tails R h 15).length + 0)))))))) := by
      have t := tails_len R h 15
      rw [b15] at t
      exact t
    rw [e0, e4, e5, e8, e10, e12, e13, e14, e15]
    push_cast
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩

lemma const_flat (L : List ℕ) (T : List (List ℕ)) :
    (L.flatMap fun r => T.map (r :: ·)).length = L.length * T.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    ring

open OMA.S_oeis_a208138 in
lemma a_succ (h : ℕ) : 4 * a (h + 1) = 9 * ((h : ℤ) + 1) ^ 2 * ((h : ℤ) + 2) ^ 2 := by
  have hk := (key h).2.2.2.2.2.2.2.2
  have e : a (h + 1)
      = (((rows 4 1 3).flatMap fun r => (tails (rows 4 1 3) h 15).map (r :: ·)).length : ℤ) := rfl
  have hR : R.length = 9 := rfl
  rw [e, rows_eq, const_flat, hR]
  push_cast
  linarith

open OMA.S_oeis_a208138 in
lemma a_formula (n : ℕ) : 4 * a n = 9 * (n : ℤ) ^ 2 * (1 + (n : ℤ)) ^ 2 := by
  cases n with
  | zero =>
    have e : a 0 = 0 := rfl
    rw [e]; norm_num
  | succ h =>
    have := a_succ h
    push_cast
    linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A208138Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a208138 A208138Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a208138.main := by
  refine ⟨?_, a_formula⟩
  have hD : ((1 - PowerSeries.X) ^ 5 : PowerSeries ℤ) =
      PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-5) * PowerSeries.X ^ 1 +
      PowerSeries.C 10 * PowerSeries.X ^ 2 + PowerSeries.C (-10) * PowerSeries.X ^ 3 +
      PowerSeries.C 5 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
    simp only [map_one, map_ofNat, map_neg]; ring
  have hN : (9 * PowerSeries.X * (1 + 4 * PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℤ) =
      PowerSeries.C 9 * PowerSeries.X ^ 1 + PowerSeries.C 36 * PowerSeries.X ^ 2 +
      PowerSeries.C 9 * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
  by_cases h5 : 5 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have f0 := a_formula m
    have f1 := a_formula (m + 1)
    have f2 := a_formula (m + 2)
    have f3 := a_formula (m + 3)
    have f4 := a_formula (m + 4)
    have f5 := a_formula (m + 5)
    push_cast at f0 f1 f2 f3 f4 f5
    have c0 : (0 : ℕ) ≤ m + 5 := by omega
    have c1 : (1 : ℕ) ≤ m + 5 := by omega
    have c2 : (2 : ℕ) ≤ m + 5 := by omega
    have c3 : (3 : ℕ) ≤ m + 5 := by omega
    have c4 : (4 : ℕ) ≤ m + 5 := by omega
    have c5 : (5 : ℕ) ≤ m + 5 := by omega
    have n1 : ¬ (m + 5 = 1) := by omega
    have n2 : ¬ (m + 5 = 2) := by omega
    have n3 : ¬ (m + 5 = 3) := by omega
    have d0 : m + 5 - 0 = m + 5 := by omega
    have d1 : m + 5 - 1 = m + 4 := by omega
    have d2 : m + 5 - 2 = m + 3 := by omega
    have d3 : m + 5 - 3 = m + 2 := by omega
    have d4 : m + 5 - 4 = m + 1 := by omega
    have d5 : m + 5 - 5 = m := by omega
    rw [if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_neg n1, if_neg n2,
      if_neg n3, d0, d1, d2, d3, d4, d5]
    linarith
  · have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    have f0 := a_formula 0
    have f1 := a_formula 1
    have f2 := a_formula 2
    have f3 := a_formula 3
    have f4 := a_formula 4
    norm_num at f0 f1 f2 f3 f4
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · norm_num; linarith
    · norm_num; linarith
    · norm_num; linarith
    · norm_num; linarith
    · norm_num; linarith
