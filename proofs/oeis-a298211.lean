import OMAStatements.S_oeis_a298211
import Mathlib

namespace OMA.A298211Proof

open OMA.S_oeis_a298211

/-! ### The first values of `U` (A001353): 0, 1, 4, 15, 56, 209 -/

theorem U_1 : U 1 = 1 := rfl

theorem U_2 : U 2 = 4 := rfl

theorem U_3 : U 3 = 15 := rfl

theorem U_4 : U 4 = 56 := rfl

theorem U_5 : U 5 = 209 := rfl

/-! ### Bounds on `a` from membership and from a lower bound on the set -/

theorem a_le {n i : ℕ} (hi : 1 ≤ i) (h : (n : ℤ) ∣ U i) : a n ≤ i := by
  unfold a
  apply Nat.sInf_le
  exact ⟨hi, h⟩

theorem le_a {n m : ℕ} (hne : ∃ i, 1 ≤ i ∧ (n : ℤ) ∣ U i)
    (h : ∀ i, 1 ≤ i → (n : ℤ) ∣ U i → m ≤ i) : m ≤ a n := by
  unfold a
  obtain ⟨j, hj1, hj2⟩ := hne
  apply le_csInf
  · exact ⟨j, hj1, hj2⟩
  · rintro i ⟨hi1, hi2⟩
    exact h i hi1 hi2

/-- `209 = 11 * 19` divides `U 5`. -/
theorem dvd19 : ((19 : ℕ) : ℤ) ∣ U 5 := by
  rw [U_5]
  norm_num

theorem dvd209 : ((209 : ℕ) : ℤ) ∣ U 5 := by
  rw [U_5]
  norm_num

/-- `a 19 = 5`: `19` divides none of `U 1, ..., U 4 = 1, 4, 15, 56` and divides `U 5 = 209`. -/
theorem a_19 : a 19 = 5 := by
  apply le_antisymm (a_le (by norm_num) dvd19)
  apply le_a ⟨5, by norm_num, dvd19⟩
  intro i hi h
  by_contra hlt
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl
  · rw [U_1] at h
    norm_num at h
  · rw [U_2] at h
    norm_num at h
  · rw [U_3] at h
    norm_num at h
  · rw [U_4] at h
    norm_num at h

/-- `a 209 ≤ 5`, since `209 ∣ U 5`. -/
theorem a_209_le : a 209 ≤ 5 :=
  a_le (by norm_num) dvd209

/-! ### `safe 3 = 11` and `sophie 3 = 5` -/

theorem count_safe_11 :
    Nat.count (fun p : ℕ => p.Prime ∧ ((p - 1) / 2).Prime) 11 = 2 := by
  norm_num [Nat.count_succ]

theorem safe_3 : safe 3 = 11 := by
  have h11 : Nat.Prime 11 ∧ Nat.Prime ((11 - 1) / 2) := ⟨by norm_num, by norm_num⟩
  have h := Nat.nth_count (p := fun p : ℕ => p.Prime ∧ ((p - 1) / 2).Prime) (n := 11) h11
  rw [count_safe_11] at h
  exact h

theorem count_sophie_5 :
    Nat.count (fun p : ℕ => p.Prime ∧ (2 * p + 1).Prime) 5 = 2 := by
  norm_num [Nat.count_succ]

theorem sophie_3 : sophie 3 = 5 := by
  have h5 : Nat.Prime 5 ∧ Nat.Prime (2 * 5 + 1) := ⟨by norm_num, by norm_num⟩
  have h := Nat.nth_count (p := fun p : ℕ => p.Prime ∧ (2 * p + 1).Prime) (n := 5) h5
  rw [count_sophie_5] at h
  exact h

end OMA.A298211Proof

/-- The conjecture fails at `n = 3` (`A005385(3) = 11`, `A005384(3) = 5`) and `k = 19`: it would give
`a(209) = a(19) * 5 = 25`, but `209 ∣ U 5`, so `a(209) ≤ 5`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298211.main) := by
  intro h
  have h1 := h 3 (by norm_num) 19 (by norm_num)
  rw [OMA.A298211Proof.safe_3, OMA.A298211Proof.sophie_3, OMA.A298211Proof.a_19,
    show (19 : ℕ) * 11 = 209 from rfl] at h1
  have h2 := OMA.A298211Proof.a_209_le
  omega
