import OMAStatements.S_oeis_a246460
import Mathlib

/-!
# Integrality of OEIS A246460

Source: https://oeis.org/A246460 (OEIS Foundation, CC BY-SA 4.0).
The OEIS entry credits Zhi-Wei Sun with the proof in
https://arxiv.org/html/1408.5381.
Formalization: @grp06.
-/

open scoped BigOperators

private theorem a246460_sum_by_parts (a : ℕ → ℤ) (m : ℕ) :
    (∑ j ∈ Finset.range m, ((j : ℤ) + 1) ^ 2 * (a j ^ 2 - a (j + 1) ^ 2)) =
      (∑ j ∈ Finset.range m, (2 * (j : ℤ) + 1) * a j ^ 2) -
        (m : ℤ) ^ 2 * a m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Finset.sum_range_succ, Nat.cast_succ, ih]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a246460.main := by
  intro n hn
  let a (j : ℕ) : ℤ :=
    ((n - 1).choose j : ℤ) * ((n + j).choose j : ℤ)
  have adjacent (j : ℕ) (hj : j < n) :
      ((j : ℤ) + 1) ^ 2 * (a j + a (j + 1)) = (n : ℤ) ^ 2 * a j := by
    have hsub : n - 1 - j = n - (j + 1) := by omega
    have hle : j + 1 ≤ n := by omega
    have hfirst :
        ((n - 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) =
          ((n - 1).choose j : ℤ) * ((n : ℤ) - ((j : ℤ) + 1)) := by
      have h := congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_succ_right_eq (n - 1) j)
      simpa only [Nat.cast_mul, hsub, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one] using h
    have hsecond :
        ((n + (j + 1)).choose (j + 1) : ℤ) * ((j : ℤ) + 1) =
          ((n : ℤ) + ((j : ℤ) + 1)) * ((n + j).choose j : ℤ) := by
      have h := congrArg (fun x : ℕ => (x : ℤ)) (Nat.add_one_mul_choose_eq (n + j) j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.add_assoc] using h.symm
    have hprod :
        ((j : ℤ) + 1) ^ 2 * a (j + 1) =
          ((n : ℤ) ^ 2 - ((j : ℤ) + 1) ^ 2) * a j := by
      calc
        ((j : ℤ) + 1) ^ 2 * a (j + 1) =
            (((n - 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1)) *
              (((n + (j + 1)).choose (j + 1) : ℤ) * ((j : ℤ) + 1)) := by
                dsimp only [a]
                ring
        _ = ((n : ℤ) ^ 2 - ((j : ℤ) + 1) ^ 2) * a j := by
          rw [hfirst, hsecond]
          dsimp only [a]
          ring
    rw [mul_add, hprod]
    ring
  have azero : a n = 0 := by
    have hlt : n - 1 < n := by omega
    simp [a, Nat.choose_eq_zero_of_lt hlt]
  have hsum :
      (∑ j ∈ Finset.range n, (2 * (j : ℤ) + 1) * a j ^ 2) =
        (n : ℤ) ^ 2 * ∑ j ∈ Finset.range n, a j * (a j - a (j + 1)) := by
    calc
      (∑ j ∈ Finset.range n, (2 * (j : ℤ) + 1) * a j ^ 2) =
          ∑ j ∈ Finset.range n, ((j : ℤ) + 1) ^ 2 * (a j ^ 2 - a (j + 1) ^ 2) := by
            simpa [azero] using (a246460_sum_by_parts a n).symm
      _ = (n : ℤ) ^ 2 * ∑ j ∈ Finset.range n, a j * (a j - a (j + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        calc
          ((j : ℤ) + 1) ^ 2 * (a j ^ 2 - a (j + 1) ^ 2) =
              (((j : ℤ) + 1) ^ 2 * (a j + a (j + 1))) * (a j - a (j + 1)) := by
                ring
          _ = (n : ℤ) ^ 2 * (a j * (a j - a (j + 1))) := by
            rw [adjacent j (Finset.mem_range.mp hj), mul_assoc]
  refine Int.natCast_dvd_natCast.mp ?_
  refine ⟨∑ j ∈ Finset.range n, a j * (a j - a (j + 1)), ?_⟩
  push_cast
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro j _
  dsimp only [a]
  ring
