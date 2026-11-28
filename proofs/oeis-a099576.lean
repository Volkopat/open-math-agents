import OMAStatements.S_oeis_a099576
import Mathlib

/-!
The inner sum is a hockey stick: the sum over j < M of C(n+j, n) is C(n+M, n+1). Pairing the
outer indices k = 2i and k = 2i+1 and applying the hockey stick again gives
a(2m) = 2 C(3m+1, 2m+2) + C(3m+1, 2m+1) and a(2m+1) = 2 C(3m+3, 2m+3). Every binomial is then
a rational multiple of Y(m) = C(3m+1, 2m+1), and the recurrence for n = 2m+2 and n = 2m+3 is a
rational identity in m.
-/

namespace R099576

open OMA.S_oeis_a099576 Finset

theorem hs (n M : ℕ) : ∑ j ∈ range M, (n + j).choose n = (n + M).choose (n + 1) := by
  induction M with
  | zero => rw [sum_range_zero, Nat.add_zero, Nat.choose_eq_zero_of_lt (by omega : n < n + 1)]
  | succ M ih =>
    rw [sum_range_succ, ih, show n + (M + 1) = n + M + 1 by omega, Nat.choose_succ_succ' (n + M) n]
    ring

theorem ha (n : ℕ) : a n = ∑ k ∈ range (n + 1), (n + 1 + k / 2).choose (n + 1) := by
  unfold a
  refine sum_congr rfl fun k _ => ?_
  rw [show n + 1 + k / 2 = n + (k / 2 + 1) by omega, ← hs n (k / 2 + 1)]
  refine sum_congr rfl fun j _ => ?_
  exact Nat.choose_symm_add.symm

theorem pair (f : ℕ → ℕ) (m : ℕ) : ∑ k ∈ range (2 * m), f (k / 2) = 2 * ∑ i ∈ range m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [sum_range_succ]
    rw [ih, show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega]
    ring

theorem a_even (m : ℕ) :
    a (2 * m) = 2 * (3 * m + 1).choose (2 * m + 2) + (3 * m + 1).choose (2 * m + 1) := by
  have hp : ∑ k ∈ range (2 * m), (2 * m + 1 + k / 2).choose (2 * m + 1) =
      2 * ∑ i ∈ range m, (2 * m + 1 + i).choose (2 * m + 1) :=
    pair (fun i => (2 * m + 1 + i).choose (2 * m + 1)) m
  rw [ha, sum_range_succ, hp, hs (2 * m + 1) m, show 2 * m / 2 = m by omega,
    show 2 * m + 1 + 1 = 2 * m + 2 by ring, show 2 * m + 1 + m = 3 * m + 1 by ring]

theorem a_odd (m : ℕ) : a (2 * m + 1) = 2 * (3 * m + 3).choose (2 * m + 3) := by
  have hp : ∑ k ∈ range (2 * (m + 1)), (2 * (m + 1) + k / 2).choose (2 * (m + 1)) =
      2 * ∑ i ∈ range (m + 1), (2 * (m + 1) + i).choose (2 * (m + 1)) :=
    pair (fun i => (2 * (m + 1) + i).choose (2 * (m + 1))) (m + 1)
  rw [ha, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, hp, hs (2 * (m + 1)) (m + 1),
    show 2 * (m + 1) + (m + 1) = 3 * m + 3 by ring, show 2 * (m + 1) + 1 = 2 * m + 3 by ring]

theorem g1 (m : ℕ) : ((3 * m + 2 : ℚ)) * ((3 * m + 1).choose (2 * m + 1) : ℚ) =
    ((3 * m + 2).choose (2 * m + 2) : ℚ) * (2 * m + 2) := by
  have f : (3 * m + 2) * (3 * m + 1).choose (2 * m + 1) =
      (3 * m + 2).choose (2 * m + 2) * (2 * m + 2) :=
    Nat.add_one_mul_choose_eq (3 * m + 1) (2 * m + 1)
  exact_mod_cast f

theorem g2 (m : ℕ) : ((3 * m + 3 : ℚ)) * ((3 * m + 2).choose (2 * m + 2) : ℚ) =
    ((3 * m + 3).choose (2 * m + 3) : ℚ) * (2 * m + 3) := by
  have f : (3 * m + 3) * (3 * m + 2).choose (2 * m + 2) =
      (3 * m + 3).choose (2 * m + 3) * (2 * m + 3) :=
    Nat.add_one_mul_choose_eq (3 * m + 2) (2 * m + 2)
  exact_mod_cast f

theorem g3 (m : ℕ) : ((3 * m + 3).choose (2 * m + 3) : ℚ) * (3 * m + 4) =
    ((3 * m + 4).choose (2 * m + 3) : ℚ) * (m + 1) := by
  have f : (3 * m + 3).choose (2 * m + 3) * (3 * m + 4) =
      (3 * m + 4).choose (2 * m + 3) * (m + 1) := by
    have h := Nat.choose_mul_succ_eq (3 * m + 3) (2 * m + 3)
    rwa [show 3 * m + 3 + 1 - (2 * m + 3) = m + 1 by omega] at h
  exact_mod_cast f

theorem qe (m : ℕ) :
    (a (2 * m) : ℚ) = (2 * m + 1) * ((3 * m + 1).choose (2 * m + 1) : ℚ) / (m + 1) := by
  have e : (3 * m + 1).choose (2 * m + 2) * (2 * m + 2) = (3 * m + 1).choose (2 * m + 1) * m := by
    have h := Nat.choose_succ_right_eq (3 * m + 1) (2 * m + 1)
    rwa [show 3 * m + 1 - (2 * m + 1) = m by omega] at h
  have g : ((3 * m + 1).choose (2 * m + 2) : ℚ) * (2 * m + 2) =
      ((3 * m + 1).choose (2 * m + 1) : ℚ) * m := by
    exact_mod_cast e
  rw [eq_div_iff (by positivity), a_even]
  push_cast
  linear_combination g

theorem qo (m : ℕ) :
    (a (2 * m + 1) : ℚ) = 3 * (3 * m + 2) * ((3 * m + 1).choose (2 * m + 1) : ℚ) / (2 * m + 3) := by
  rw [eq_div_iff (by positivity), a_odd]
  push_cast
  linear_combination (-2) * g2 m - 3 * g1 m

theorem qs (m : ℕ) : ((3 * (m + 1) + 1).choose (2 * (m + 1) + 1) : ℚ) =
    ((3 * m + 1).choose (2 * m + 1) : ℚ) * ((3 * m + 2) * (3 * m + 3) * (3 * m + 4)) /
      ((m + 1) * (2 * m + 2) * (2 * m + 3)) := by
  rw [show 3 * (m + 1) + 1 = 3 * m + 4 by ring, show 2 * (m + 1) + 1 = 2 * m + 3 by ring,
    eq_div_iff (by positivity)]
  linear_combination -(2 * (m : ℚ) + 2) * (2 * m + 3) * g3 m - (3 * (m : ℚ) + 4) * (2 * m + 2) * g2 m -
    (3 * (m : ℚ) + 3) * (3 * m + 4) * g1 m

theorem key (n : ℕ) (hn : 2 ≤ n) :
    4 * (n : ℚ) * ((n : ℚ) - 1) * (3 * (n : ℚ) + 2) * ((n : ℚ) + 2) * (a n : ℚ) -
      36 * ((n : ℚ) - 1) * ((n : ℚ) + 1) * (a (n - 1) : ℚ) -
      3 * (n : ℚ) * (3 * (n : ℚ) + 5) * (3 * (n : ℚ) - 1) *
        (3 * (n : ℚ) - 2) * (a (n - 2) : ℚ) = 0 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 2 ∨ n = 2 * m + 3 := ⟨(n - 2) / 2, by omega⟩
  · have h0 := qe (m + 1)
    rw [qs m, show 2 * (m + 1) = 2 * m + 2 by ring] at h0
    rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega, show 2 * m + 2 - 2 = 2 * m by omega, h0, qo m,
      qe m]
    push_cast
    field_simp
    ring
  · have h0 := qe (m + 1)
    have h1 := qo (m + 1)
    rw [qs m, show 2 * (m + 1) = 2 * m + 2 by ring] at h0
    rw [qs m, show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at h1
    rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega, h1, h0,
      qo m]
    push_cast
    field_simp
    ring

end R099576

theorem OMA.solution : type_of% @OMA.S_oeis_a099576.main := by
  intro n hn
  have k := R099576.key n hn
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  linear_combination k
