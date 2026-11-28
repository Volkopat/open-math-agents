import OMAStatements.S_oeis_a263245

-- Problem: A263245: Decimal representation of the n-th iteration of the Rule 155 elementary cellular automaton starting with a single ON (black) cell
-- Upstream: formal-conjectures statements/oeis-a263245.lean:0 (declaration OMA.S_oeis_a263245.main)
-- Shorter version of the merged proof (the first solve keeps its credit).
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a263245

open OMA.S_oeis_a263245
open PowerSeries

lemma r (l c r : Bool) : ruleOut 155 l c r = ((!c || r) && (!l || c || !r)) := by
  cases l <;> cases c <;> cases r <;> rfl

-- after t + 1 steps the only OFF cells are -t and, for odd t, 1 - t
lemma cf (t : ℕ) : cell 155 (t + 1) = fun i : ℤ => decide (i ≠ -t ∧ (i ≠ 1 - t ∨ t % 2 = 0)) := by
  induction t with
  | zero => ext i; rw [Bool.eq_iff_iff]; simp [cell, r]; omega
  | succ t ih => rw [cell, ih]; ext i; rw [Bool.eq_iff_iff]; simp [r]; omega

lemma gs (k : ℕ) : ∑ j ∈ Finset.range (k + 1), (2 : ℤ) ^ (k - j) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ']; simp [ih, pow_succ]; ring

lemma av (m : ℕ) :
    a (m + 1) = 2 ^ (2 * m + 3) - 1 - 2 ^ (2 * m + 1) - if m % 2 = 1 then 2 ^ (2 * m) else 0 := by
  rw [a, Finset.sum_congr rfl fun j _ => show _ = (2 : ℤ) ^ (2 * (m + 1) - j) -
    (if j = 1 then 2 ^ (2 * (m + 1) - j) else 0) - if j = 2 ∧ m % 2 = 1 then 2 ^ (2 * (m + 1) - j) else 0 by
      simp only [cf]; split_ifs <;> simp_all <;> omega]
  simp [Finset.sum_sub_distrib, gs, ite_and, mul_add]

lemma st (k : ℕ) : a (k + 3) = 16 * a (k + 1) + 15 := by
  rw [av, av, show (k + 2) % 2 = k % 2 by omega]; split_ifs <;> ring

private lemma a_rec : ∀ n > 3, a n = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have := st k
  have := st (k + 1)
  simp at *
  linarith

private lemma a_zero : a 0 = 1 := by
  simp [a, cell]

private lemma a_one : a 1 = 5 := by
  rw [av]; norm_num

private lemma a_two : a 2 = 19 := by
  rw [av]; norm_num

private lemma a_three : a 3 = 95 := by
  rw [av]; norm_num

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X)) =
      1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 := by
  have hfactor : ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) =
      1 - X - C (16 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 := by
    have h16 : C (16 : ℚ) = (16 : PowerSeries ℚ) := map_ofNat C 16
    rw [h16]
    ring
  have hrhs_eq : (1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 : PowerSeries ℚ) =
      C (1 : ℚ) + C (4 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 := by
    have h1 : C (1 : ℚ) = (1 : PowerSeries ℚ) := map_one C
    have h4 : C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat C 4
    have h2 : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
    have h12 : C (12 : ℚ) = (12 : PowerSeries ℚ) := map_ofNat C 12
    rw [h1, h4, h2, h12, pow_one]
  rw [hfactor, hrhs_eq]
  ext n
  have hcoeff_mul :
      PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) *
          (1 - X - C (16 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3)) =
        (a n : ℚ)
        - (if 1 ≤ n then (a (n - 1) : ℚ) else 0)
        - 16 * (if 2 ≤ n then (a (n - 2) : ℚ) else 0)
        + 16 * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) := by
    have hdistrib :
        PowerSeries.mk (fun k => (a k : ℚ)) *
            (1 - X - C (16 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3) =
          PowerSeries.mk (fun k => (a k : ℚ))
          - PowerSeries.mk (fun k => (a k : ℚ)) * X
          - C (16 : ℚ) * (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 2)
          + C (16 : ℚ) * (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 3) := by
      ring
    rw [hdistrib]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    have h1 : PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) * X) =
        if 1 ≤ n then (a (n - 1) : ℚ) else 0 := by
      cases n with
      | zero => simp
      | succ m => simp [PowerSeries.coeff_succ_mul_X]
    have h2 : PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 2) =
        if 2 ≤ n then (a (n - 2) : ℚ) else 0 := by
      rw [PowerSeries.coeff_mul_X_pow']
      simp
    have h3 : PowerSeries.coeff n (PowerSeries.mk (fun k => (a k : ℚ)) * X ^ 3) =
        if 3 ≤ n then (a (n - 3) : ℚ) else 0 := by
      rw [PowerSeries.coeff_mul_X_pow']
      simp
    rw [h1, h2, h3]
  have hcoeff_rhs :
      PowerSeries.coeff n (C (1 : ℚ) + C (4 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3) =
        (if n = 0 then (1 : ℚ) else 0)
        + (if n = 1 then (4 : ℚ) else 0)
        - (if n = 2 then (2 : ℚ) else 0)
        + (if n = 3 then (12 : ℚ) else 0) := by
    simp only [map_add, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul_X_pow]
  rw [hcoeff_mul, hcoeff_rhs]
  rcases n with _ | _ | _ | _ | n
  · simp [a_zero]
  · simp [a_one, a_zero]; norm_num
  · simp [a_two, a_one, a_zero]; norm_num
  · simp [a_three, a_two, a_one, a_zero]; norm_num
  · have hr := a_rec (n + 4) (by omega)
    have hrq : (a (n + 4) : ℚ) =
        (a (n + 3) : ℚ) + 16 * (a (n + 2) : ℚ) - 16 * (a (n + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega,
      ite_true, show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
      show n + 4 - 3 = n + 1 by omega, show n + 4 ≠ 0 by omega, show n + 4 ≠ 1 by omega,
      show n + 4 ≠ 2 by omega, show n + 4 ≠ 3 by omega, ite_false]
    linarith

private lemma a_odd_rat (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = (3 * (4 : ℚ) ^ (((n : ℤ) - 1) / 2) * (2 : ℚ) ^ (n : ℤ) - 1 : ℚ) := by
  obtain ⟨k, rfl⟩ := hn
  rw [av, show (((2 * k + 1 : ℕ) : ℤ) - 1) / 2 = k by omega, zpow_natCast, zpow_natCast,
    show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  simp
  ring

private lemma a_even_rat (n : ℕ) (h0 : 0 < n) (hn : Even n) :
    (a n : ℚ) = (5 * (4 : ℚ) ^ ((n : ℤ) / 2 - 1) * (2 : ℚ) ^ (n : ℤ) - 1 : ℚ) := by
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, av,
    show ((2 * m + 1 + 1 : ℕ) : ℤ) / 2 - 1 = m by omega, zpow_natCast, zpow_natCast,
    show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  simp
  ring

end OMA.Proof_oeis_a263245

theorem OMA.solution : type_of% @OMA.S_oeis_a263245.main := by
  exact ⟨OMA.Proof_oeis_a263245.a_rec,
    OMA.Proof_oeis_a263245.gf_eq,
    OMA.Proof_oeis_a263245.a_odd_rat,
    OMA.Proof_oeis_a263245.a_even_rat⟩
