import OMAStatements.S_oeis_a266665
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 47 is (not l) or (l and not c and r). By induction, stage 2k+2 is ON exactly at
-- cells 2k+1, 2k+2 and stage 2k+3 is OFF exactly at cells 2k+2, 2k+3 (stage 1: OFF only at 1).
-- Hence white(2k+2) = 4k+3, white(2k+3) = 2, giving a(2m+1) = 2m^2+3m+1 and a(2m+2) = 2m^2+7m+4,
-- i.e. Barker's closed form; the recurrence and the generating function follow by comparing
-- coefficients. No computer search.

namespace OMA.A266665Proof
open PowerSeries OMA.S_oeis_a266665
lemma eca47 (l c r : Bool) : eca 47 l c r = (!l || (l && !c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma st1 (i : ℤ) : state 1 i = decide (i ≠ 1) := by
  show eca 47 _ _ _ = _
  simp only [state, eca47]
  by_cases h0 : i = 0
  · subst h0; decide
  by_cases h1 : i = 1
  · subst h1; decide
  by_cases h2 : i = -1
  · subst h2; decide
  have : i - 1 ≠ 0 := by omega
  have : i + 1 ≠ 0 := by omega
  simp_all

lemma stE (k : ℕ) : (∀ i : ℤ, state (2 * k + 2) i = decide (i = 2 * k + 1 ∨ i = 2 * k + 2)) ∧
    (∀ i : ℤ, state (2 * k + 3) i = decide (i ≠ 2 * k + 2 ∧ i ≠ 2 * k + 3)) := by
  have step2 : ∀ k : ℕ, (∀ i : ℤ, state (2 * k + 1) i = decide (i ≠ 2 * k ∧ i ≠ 2 * k + 1) ∨ k = 0) →
      True := fun _ _ => trivial
  induction k with
  | zero =>
    have e2 : ∀ i : ℤ, state 2 i = decide (i = 1 ∨ i = 2) := by
      intro i
      show eca 47 _ _ _ = _
      rw [st1, st1, st1, eca47]
      rw [Bool.eq_iff_iff]; simp; omega
    refine ⟨fun i => by simpa using e2 i, fun i => ?_⟩
    show eca 47 _ _ _ = _
    rw [e2, e2, e2, eca47]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    rw [Bool.eq_iff_iff]; simp; omega
  | succ k ih =>
    have eA : ∀ i : ℤ, state (2 * (k + 1) + 2) i = decide (i = 2 * ((k + 1 : ℕ) : ℤ) + 1 ∨ i = 2 * ((k + 1 : ℕ) : ℤ) + 2) := by
      intro i
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by ring]
      show eca 47 _ _ _ = _
      rw [ih.2, ih.2, ih.2, eca47]
      push_cast
      rw [Bool.eq_iff_iff]; simp; omega
    refine ⟨eA, fun i => ?_⟩
    rw [show 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 by ring]
    show eca 47 _ _ _ = _
    rw [eA, eA, eA, eca47]
    push_cast
    rw [Bool.eq_iff_iff]; simp; omega

lemma white0 : white 0 = 0 := by decide

lemma white1 : white 1 = 1 := by
  unfold white
  rw [show (Finset.range (2 * 1 + 1)).filter (fun i : ℕ => state 1 ((i : ℤ) - (1 : ℕ)) = false) = {2} by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, st1, Finset.mem_singleton]
    rw [decide_eq_false_iff_not]; push_cast; omega]
  rfl

lemma whiteE (k : ℕ) : white (2 * k + 2) = 4 * k + 3 := by
  unfold white
  rw [show (Finset.range (2 * (2 * k + 2) + 1)).filter
      (fun i : ℕ => state (2 * k + 2) ((i : ℤ) - ((2 * k + 2 : ℕ) : ℤ)) = false) = Finset.range (4 * k + 3) by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, (stE k).1]
    rw [decide_eq_false_iff_not]; push_cast; omega]
  simp

lemma whiteO (k : ℕ) : white (2 * k + 3) = 2 := by
  unfold white
  rw [show (Finset.range (2 * (2 * k + 3) + 1)).filter
      (fun i : ℕ => state (2 * k + 3) ((i : ℤ) - ((2 * k + 3 : ℕ) : ℤ)) = false) = Finset.Ico (4 * k + 5) (4 * k + 7) by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, (stE k).2, Finset.mem_Ico]
    rw [decide_eq_false_iff_not]; push_cast; omega]
  simp

lemma aS (n : ℕ) : a (n + 1) = a n + white (n + 1) := by
  unfold a; rw [Finset.sum_range_succ]

lemma aOdd (m : ℕ) : (a (2 * m + 1) : ℤ) = 2 * m ^ 2 + 3 * m + 1 ∧
    (a (2 * m + 2) : ℤ) = 2 * m ^ 2 + 7 * m + 4 := by
  induction m with
  | zero => refine ⟨?_, ?_⟩ <;> decide
  | succ m ih =>
    have h1 : (a (2 * (m + 1) + 1) : ℤ) = a (2 * m + 2) + 2 := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, aS, show 2 * m + 2 + 1 = 2 * m + 3 by ring, whiteO]
      push_cast; ring
    have h2 : (a (2 * (m + 1) + 2) : ℤ) = a (2 * (m + 1) + 1) + 4 * (m + 1) + 3 := by
      rw [aS, show 2 * (m + 1) + 1 + 1 = 2 * (m + 1) + 2 by ring, whiteE]
      push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [h1, ih.2]; push_cast; ring
    · rw [h2, h1, ih.2]; push_cast; ring

lemma closed (n : ℕ) (hn : 0 < n) : 2 * (a n : ℤ) = n ^ 2 + 2 * n + (-1) ^ n * (n - 1) - 1 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 1 ∨ n = 2 * m + 2 := ⟨(n - 1) / 2, by omega⟩
  · have e : ((-1 : ℤ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [(aOdd m).1]; push_cast; rw [e]; ring
  · have e : ((-1 : ℤ)) ^ (2 * m + 2) = 1 := by rw [pow_succ, pow_succ, pow_mul]; norm_num
    rw [(aOdd m).2]; push_cast; rw [e]; ring

theorem main_proof :
    (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = n ^ 2 + 2 * n + (-1) ^ n * (n - 1) - 1) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (X * (1 + 3 * X + X ^ 3 - X ^ 4) : PowerSeries ℤ) := by
  have hrec : ∀ m : ℕ, (a (m + 6) : ℤ) = a (m + 5) + 2 * a (m + 4) - 2 * a (m + 3) - a (m + 2) + a (m + 1) := by
    intro m
    have c0 := closed (m + 6) (by omega)
    have c1 := closed (m + 5) (by omega)
    have c2 := closed (m + 4) (by omega)
    have c3 := closed (m + 3) (by omega)
    have c4 := closed (m + 2) (by omega)
    have c5 := closed (m + 1) (by omega)
    push_cast at c0 c1 c2 c3 c4 c5
    simp only [pow_succ] at c0 c1 c2 c3 c4 c5
    have h2 : 2 * (a (m + 6) : ℤ) = 2 * (a (m + 5) + 2 * a (m + 4) - 2 * a (m + 3) - a (m + 2) + a (m + 1)) := by
      linear_combination c0 - c1 - 2 * c2 + 2 * c3 + c4 - c5
    linarith
  refine ⟨closed, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
    exact hrec m
  · have hP : ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
        X ^ 0 - X ^ 1 - X ^ 2 - X ^ 2 + X ^ 3 + X ^ 3 + X ^ 4 - X ^ 5 := by ring
    have hQ : (X * (1 + 3 * X + X ^ 3 - X ^ 4) : PowerSeries ℤ) =
        X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 4 - X ^ 5 := by ring
    rw [hP, hQ]
    ext n
    simp only [mul_sub, mul_add, map_sub, map_add, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      simp only [show 0 ≤ m + 6 by omega, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega,
        show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, if_true,
        show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega, show m + 6 ≠ 4 by omega, show m + 6 ≠ 5 by omega,
        if_false, show m + 6 - 0 = m + 6 by omega, show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
        show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
      linear_combination hrec m
end OMA.A266665Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266665.main := OMA.A266665Proof.main_proof
