import OMAStatements.S_oeis_a262779
import Mathlib

-- Problem: A262779: Binary representation of the n-th iteration of the "Rule 175" elementary cellular automaton starting with a single ON (black) cell
-- Upstream: formal-conjectures statements/oeis-a262779.lean:0 (declaration OMA.S_oeis_a262779.main)
-- Credit: @vincentkoc (the owner of the agent is credited as the solver)
-- Shortened by Left to Solve (Grok Bot)
-- Proof: Rule 175 sends (l, c, r) to (!l || r). From a single ON cell, after t + 1 steps every
-- cell is ON except the one at position 1 - t. So a(m+1) and a(m+2) share every digit except the
-- last two, giving a(m+2) = 100 * a(m+1) + 11. The recurrence and the generating function follow.

namespace OMA.A262779Proof

open OMA.S_oeis_a262779 PowerSeries

lemma cell_175 (t : ℕ) (i : ℤ) : cell 175 (t + 1) i = decide (i ≠ 1 - t) := by
  have h : ∀ l c r, ruleOut 175 l c r = (!l || r) := by decide
  induction t generalizing i with
  | zero => simp only [cell, h]; rw [Bool.eq_iff_iff]; simp; omega
  | succ t ih => rw [cell]; simp only [ih, h]; rw [Bool.eq_iff_iff]; simp; omega

lemma s (m : ℕ) : a (m + 2) = 100 * a (m + 1) + 11 := by
  rw [a, a, show 2 * (m + 2) + 1 = 2 * (m + 1) + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.mul_sum, add_assoc]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp only [cell_175, Finset.mem_range] at *
    split_ifs <;> simp_all <;> first | omega | rw [show 2 * (m + 2) - j = 2 * (m + 1) - j + 2 by omega]; ring
  · simp [cell_175]
    rw [show 2 * (m + 2) - (2 * (m + 1) + 1) = 1 by omega, show 2 * (m + 2) - (2 * (m + 1) + 2) = 0 by omega]
    split_ifs <;> omega

end OMA.A262779Proof

open OMA.S_oeis_a262779 OMA.A262779Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a262779.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp [s]
    ring
  · have h : ∀ k, coeff (k + 1) (9 : ℚ⟦X⟧) = 0 := fun k => by rw [← map_ofNat C]; exact coeff_C ..
    rw [show (1 - X) * (1 - 100 * X) = 1 - C (101 : ℚ) * X + C 100 * X ^ 2 by simp only [map_ofNat]; ring]
    ext k
    rcases k with _ | _ | _ | k <;> simp [mul_sub, mul_add, ← mul_assoc, coeff_mul_X_pow', coeff_X_pow,
      coeff_one, s, h, map_ofNat constantCoeff 9, show a 0 = 1 by decide, show a 1 = 110 by decide] <;> ring
