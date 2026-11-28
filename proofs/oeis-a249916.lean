import OMAStatements.S_oeis_a249916
import Mathlib

-- Problem: A249916: a(n) = 4*(n - 1) - a(n-3), n >= 3, a(0) = a(1) = 1, a(2) = 5.
-- Upstream: formal-conjectures statements/oeis-a249916.lean:0 (declaration OMA.S_oeis_a249916.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The order-five recurrence follows by using the defining recurrence at n, n - 1 and n - 2.
The generating function identity is the same recurrence together with the first five terms. For
the pattern of repeats, the closed form a(6 q + r) = 12 q + c(r) with c = 1, 1, 5, 7, 11, 11 holds
by induction on q, and the set of indices with a given value is read off from it. -/

namespace A249916Aux

open PowerSeries OMA.S_oeis_a249916

theorem a_rec (n : ℕ) : a (n + 3) = 4 * ((n : ℤ) + 2) - a n := by
  rw [a]

theorem rec5 (m : ℕ) :
    a (m + 5) = 2 * a (m + 4) - a (m + 3) - a (m + 2) + 2 * a (m + 1) - a m := by
  have h5 := a_rec (m + 2)
  have h4 := a_rec (m + 1)
  have h3 := a_rec m
  push_cast at h5 h4
  have e5 : m + 2 + 3 = m + 5 := by ring
  have e4 : m + 1 + 3 = m + 4 := by ring
  rw [e5] at h5
  rw [e4] at h4
  linarith

/-- The closed form on residues modulo 6. -/
def cf (n : ℕ) : ℤ :=
  12 * ((n / 6 : ℕ) : ℤ) +
    (if n % 6 = 0 then 1 else if n % 6 = 1 then 1 else if n % 6 = 2 then 5
      else if n % 6 = 3 then 7 else 11)

theorem blocks (q : ℕ) :
    a (6 * q) = 12 * q + 1 ∧ a (6 * q + 1) = 12 * q + 1 ∧ a (6 * q + 2) = 12 * q + 5 ∧
    a (6 * q + 3) = 12 * q + 7 ∧ a (6 * q + 4) = 12 * q + 11 ∧ a (6 * q + 5) = 12 * q + 11 := by
  induction q with
  | zero =>
    refine ⟨by simp [a], by simp [a], by simp [a], ?_, ?_, ?_⟩
    · simp [a]
    · simp [a]
    · simp [a]
  | succ q ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ih
    have e0 : 6 * (q + 1) = 6 * q + 3 + 3 := by ring
    have e1 : 6 * (q + 1) + 1 = 6 * q + 4 + 3 := by ring
    have e2 : 6 * (q + 1) + 2 = 6 * q + 5 + 3 := by ring
    have e3 : 6 * (q + 1) + 3 = 6 * (q + 1) + 3 := rfl
    have g0 : a (6 * (q + 1)) = 12 * ((q + 1 : ℕ) : ℤ) + 1 := by
      rw [e0, a_rec, h3]
      push_cast
      ring
    have g1 : a (6 * (q + 1) + 1) = 12 * ((q + 1 : ℕ) : ℤ) + 1 := by
      rw [e1, a_rec, h4]
      push_cast
      ring
    have g2 : a (6 * (q + 1) + 2) = 12 * ((q + 1 : ℕ) : ℤ) + 5 := by
      rw [e2, a_rec, h5]
      push_cast
      ring
    have g3 : a (6 * (q + 1) + 3) = 12 * ((q + 1 : ℕ) : ℤ) + 7 := by
      rw [a_rec, g0]
      push_cast
      ring
    have g4 : a (6 * (q + 1) + 4) = 12 * ((q + 1 : ℕ) : ℤ) + 11 := by
      have e : 6 * (q + 1) + 4 = 6 * (q + 1) + 1 + 3 := by ring
      rw [e, a_rec, g1]
      push_cast
      ring
    have g5 : a (6 * (q + 1) + 5) = 12 * ((q + 1 : ℕ) : ℤ) + 11 := by
      have e : 6 * (q + 1) + 5 = 6 * (q + 1) + 2 + 3 := by ring
      rw [e, a_rec, g2]
      push_cast
      ring
    exact ⟨g0, g1, g2, g3, g4, g5⟩

theorem a_eq_cf (n : ℕ) : a n = cf n := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := blocks (n / 6)
  have hn : n = 6 * (n / 6) + n % 6 := (Nat.div_add_mod n 6).symm
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  unfold cf
  rcases (by omega : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5)
    with h | h | h | h | h | h
  · rw [hn, h, add_zero, h0]
    simp
  · rw [hn, h, h1]
    simp [Nat.add_div, Nat.add_mod]
  · rw [hn, h, h2]
    simp [Nat.add_div, Nat.add_mod]
  · rw [hn, h, h3]
    simp [Nat.add_div, Nat.add_mod]
  · rw [hn, h, h4]
    simp [Nat.add_div, Nat.add_mod]
  · rw [hn, h, h5]
    simp [Nat.add_div, Nat.add_mod]

theorem fiber (m n : ℕ) : a n = (m : ℤ) ↔
    (m % 12 = 1 ∧ (n = 6 * (m / 12) ∨ n = 6 * (m / 12) + 1)) ∨
    (m % 12 = 5 ∧ n = 6 * (m / 12) + 2) ∨ (m % 12 = 7 ∧ n = 6 * (m / 12) + 3) ∨
    (m % 12 = 11 ∧ (n = 6 * (m / 12) + 4 ∨ n = 6 * (m / 12) + 5)) := by
  rw [a_eq_cf]
  unfold cf
  split_ifs <;> omega

theorem count (m : ℕ) : {n : ℕ | a n = (m : ℤ)}.ncard =
    if m % 12 = 1 ∨ m % 12 = 11 then 2 else if m % 12 = 5 ∨ m % 12 = 7 then 1 else 0 := by
  by_cases h1 : m % 12 = 1
  · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12), 6 * (m / 12) + 1} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, fiber]
      omega
    rw [hs, Set.ncard_pair (by omega), if_pos (Or.inl h1)]
  · by_cases h11 : m % 12 = 11
    · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12) + 4, 6 * (m / 12) + 5} := by
        ext n
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, fiber]
        omega
      rw [hs, Set.ncard_pair (by omega), if_pos (Or.inr h11)]
    · rw [if_neg (by omega)]
      by_cases h5 : m % 12 = 5
      · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12) + 2} := by
          ext n
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, fiber]
          omega
        rw [hs, Set.ncard_singleton, if_pos (Or.inl h5)]
      · by_cases h7 : m % 12 = 7
        · have hs : {n : ℕ | a n = (m : ℤ)} = {6 * (m / 12) + 3} := by
            ext n
            simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, fiber]
            omega
          rw [hs, Set.ncard_singleton, if_pos (Or.inr h7)]
        · have hs : {n : ℕ | a n = (m : ℤ)} = ∅ := by
            ext n
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, fiber, iff_false]
            omega
          rw [hs, Set.ncard_empty, if_neg (by omega)]

theorem c_succ (f : ℤ⟦X⟧) (c : ℤ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℤ⟦X⟧) (c : ℤ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem c_cube (f : ℤ⟦X⟧) (m : ℕ) :
    coeff m (f * (1 + X ^ 3)) = coeff m f + if 3 ≤ m then coeff (m - 3) f else 0 := by
  rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow']

theorem coeff_quartic (u0 u1 u2 u3 u4 : ℤ) (m : ℕ) :
    coeff m (C u0 + C u1 * X + C u2 * X * X + C u3 * X * X * X + C u4 * X * X * X * X : ℤ⟦X⟧) =
      if m = 0 then u0 else if m = 1 then u1 else if m = 2 then u2 else if m = 3 then u3
        else if m = 4 then u4 else 0 := by
  rcases m with _ | _ | _ | _ | _ | m
  · simp only [map_add, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_C, add_zero, if_true]
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp

theorem gf : PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X ^ 3)) = 1 - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have h4 : (C 4 : ℤ⟦X⟧) = 4 := map_ofNat C 4
  have hm1 : (C (-1) : ℤ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have hl : PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X ^ 3)) =
      PowerSeries.mk a * (1 - C 1 * X) * (1 - C 1 * X) * (1 + X ^ 3) := by
    rw [h1]
    ring
  have hr : (1 - X + 4 * X ^ 2 - X ^ 3 + X ^ 4 : ℤ⟦X⟧) =
      C 1 + C (-1) * X + C 4 * X * X + C (-1) * X * X * X + C 1 * X * X * X * X := by
    rw [h1, h4, hm1]
    ring
  rw [hl, hr]
  ext m
  rw [coeff_quartic, c_cube]
  have v0 : a 0 = 1 := by simp [a]
  have v1 : a 1 = 1 := by simp [a]
  have v2 : a 2 = 5 := by simp [a]
  have v3 : a 3 = 7 := by
    simp [a]
  have v4 : a 4 = 11 := by
    simp [a]
  rcases m with _ | _ | _ | _ | _ | m
  · simp only [c_zero, PowerSeries.coeff_mk, v0]
    simp
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk, v0, v1]
    simp
  · simp only [c_succ, PowerSeries.coeff_mk, v0, v1, v2]
    simp
  · simp only [c_succ, PowerSeries.coeff_mk, v1, v2, v3]
    simp [v0]
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk, v0, v1, v2, v3, v4]
    simp
  · have hr5 := rec5 m
    have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := by omega
    simp only [c_succ, PowerSeries.coeff_mk, e3]
    have e5 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by ring
    have e4 : m + 1 + 1 + 1 + 1 = m + 4 := by ring
    have e3' : m + 1 + 1 + 1 = m + 3 := by ring
    have e2 : m + 1 + 1 = m + 2 := by ring
    rw [e5, e4, e3', e2]
    simp
    linarith

end A249916Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a249916.main := by
  refine ⟨?_, A249916Aux.gf, A249916Aux.count⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 4 := by omega
  have e2 : m + 5 - 2 = m + 3 := by omega
  have e3 : m + 5 - 3 = m + 2 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  rw [e1, e2, e3, e4, Nat.add_sub_cancel]
  exact A249916Aux.rec5 m
