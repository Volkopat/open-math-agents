import OMAStatements.S_oeis_a325689
import Mathlib

namespace R325689
open OMA.S_oeis_a325689

/-- Counting the points of `Icc 1 n` that satisfy a predicate cutting out an interval. -/
theorem cnt (n a b : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ y, (1 ≤ y ∧ y ≤ n ∧ p y) ↔ (a ≤ y ∧ y ≤ b)) :
    (∑ y ∈ Finset.Icc 1 n, if p y then 1 else 0) = b + 1 - a := by
  first
    | rw [← Finset.card_filter]
    | rw [Finset.sum_boole, Nat.cast_id]
  have h : (Finset.Icc 1 n).filter p = Finset.Icc a b := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact (hp y).1 ⟨h1, h2, h3⟩
    · intro h
      obtain ⟨h1, h2, h3⟩ := (hp y).2 h
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [h, Nat.card_Icc]

/-- The third part is determined by the first two. -/
theorem sum_z (n x y : ℕ) :
    (∑ z ∈ Finset.Icc 1 n,
      if x + y + z = n ∧ x ≠ y + z ∧ y ≠ x + z ∧ z ≠ x + y then 1 else 0) =
    if x + y < n ∧ 2 * x ≠ n ∧ 2 * y ≠ n ∧ 2 * (x + y) ≠ n then 1 else 0 := by
  by_cases h : x + y < n
  · rw [Finset.sum_eq_single_of_mem (n - x - y)
      (show n - x - y ∈ Finset.Icc 1 n from Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    all_goals first
      | (intro b _ hb; split_ifs <;> omega)
      | (split_ifs <;> omega)
  · rw [if_neg (show ¬(x + y < n ∧ 2 * x ≠ n ∧ 2 * y ≠ n ∧ 2 * (x + y) ≠ n) by omega)]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_Icc] at hb
    split_ifs <;> omega

theorem a_eq (n : ℕ) : a n = ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n,
    if x + y < n ∧ 2 * x ≠ n ∧ 2 * y ≠ n ∧ 2 * (x + y) ≠ n then 1 else 0 := by
  have h1 : a n = ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n, ∑ z ∈ Finset.Icc 1 n,
      (if x + y + z = n ∧ x ≠ y + z ∧ y ≠ x + z ∧ z ≠ x + y then 1 else 0) := by
    first
      | (rw [a, Finset.card_filter, Finset.sum_product]
         refine Finset.sum_congr rfl fun x _ => ?_
         rw [Finset.sum_product] <;> rfl)
      | (simp only [a, Finset.card_filter, Finset.sum_product])
      | (unfold a
         simp only [Finset.card_filter, Finset.sum_product])
  rw [h1]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => sum_z n x y

theorem inner_lt (n x : ℕ) :
    (∑ y ∈ Finset.Icc 1 n, if x + y < n then 1 else 0) = n - 1 - x :=
  (cnt n 1 (n - 1 - x) (fun y => x + y < n) (fun y => by omega)).trans (by omega)

theorem gauss (k : ℕ) : 2 * (∑ x ∈ Finset.Icc 1 k, (k - x)) + k = k * k := by
  induction k with
  | zero => first | simp | rfl | decide
  | succ k ih =>
    have h3 : ∑ x ∈ Finset.Icc 1 k, (k + 1 - x) = ∑ x ∈ Finset.Icc 1 k, ((k - x) + 1) :=
      Finset.sum_congr rfl fun x hx => by rw [Finset.mem_Icc] at hx; omega
    have h1 : ∑ x ∈ Finset.Icc 1 (k + 1), (k + 1 - x) = ∑ x ∈ Finset.Icc 1 k, (k - x) + k := by
      rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), show k + 1 - (k + 1) = 0 by omega,
        add_zero, h3, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul] <;> omega
    have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    rw [h1]
    omega

theorem P_eq (n : ℕ) (hn : 1 ≤ n) :
    2 * (∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n, if x + y < n then 1 else 0) + 3 * n =
      n * n + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (∑ x ∈ Finset.Icc 1 (k + 1), ∑ y ∈ Finset.Icc 1 (k + 1),
      if x + y < k + 1 then 1 else 0) = ∑ x ∈ Finset.Icc 1 (k + 1), (k - x) :=
    Finset.sum_congr rfl fun x _ => (inner_lt (k + 1) x).trans (by omega)
  have h2 : ∑ x ∈ Finset.Icc 1 (k + 1), (k - x) = ∑ x ∈ Finset.Icc 1 k, (k - x) := by
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), show k - (k + 1) = 0 by omega,
      add_zero]
  have hg := gauss k
  have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  rw [h1, h2]
  omega

theorem a_odd (m : ℕ) : a (2 * m + 1) + m = 2 * (m * m) := by
  have hP := P_eq (2 * m + 1) (by omega)
  have hD : a (2 * m + 1) = ∑ x ∈ Finset.Icc 1 (2 * m + 1), ∑ y ∈ Finset.Icc 1 (2 * m + 1),
      if x + y < 2 * m + 1 then 1 else 0 := by
    rw [a_eq]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by split_ifs <;> omega
  have e : (2 * m + 1) * (2 * m + 1) = 4 * (m * m) + 4 * m + 1 := by ring
  omega

theorem inner_C1 (m x : ℕ) :
    (∑ y ∈ Finset.Icc 1 (2 * m), if x = m ∧ y < m then 1 else 0) = if x = m then m - 1 else 0 := by
  by_cases h : x = m
  · rw [if_pos h]
    exact (cnt (2 * m) 1 (m - 1) (fun y => x = m ∧ y < m) (fun y => by omega)).trans (by omega)
  · rw [if_neg h]
    exact (cnt (2 * m) 1 0 (fun y => x = m ∧ y < m) (fun y => by omega)).trans (by omega)

theorem inner_C2 (m x : ℕ) :
    (∑ y ∈ Finset.Icc 1 (2 * m), if y = m ∧ x < m then 1 else 0) = if x < m then 1 else 0 := by
  by_cases h : x < m
  · rw [if_pos h]
    exact (cnt (2 * m) m m (fun y => y = m ∧ x < m) (fun y => by omega)).trans (by omega)
  · rw [if_neg h]
    exact (cnt (2 * m) 1 0 (fun y => y = m ∧ x < m) (fun y => by omega)).trans (by omega)

theorem inner_C3 (m x : ℕ) :
    (∑ y ∈ Finset.Icc 1 (2 * m), if x + y = m then 1 else 0) = if x < m then 1 else 0 := by
  by_cases h : x < m
  · rw [if_pos h]
    exact (cnt (2 * m) (m - x) (m - x) (fun y => x + y = m) (fun y => by omega)).trans
      (by omega)
  · rw [if_neg h]
    exact (cnt (2 * m) 1 0 (fun y => x + y = m) (fun y => by omega)).trans (by omega)

theorem sumA (m : ℕ) (hm : 1 ≤ m) :
    (∑ x ∈ Finset.Icc 1 (2 * m), if x = m then m - 1 else 0) = m - 1 := by
  refine (Finset.sum_eq_single_of_mem m ?_ ?_).trans ?_
  all_goals first
    | exact Finset.mem_Icc.mpr ⟨hm, by omega⟩
    | (intro b _ hb; exact if_neg hb)
    | exact if_pos rfl

theorem sumB (m : ℕ) : (∑ x ∈ Finset.Icc 1 (2 * m), if x < m then 1 else 0) = m - 1 :=
  (cnt (2 * m) 1 (m - 1) (fun x => x < m) (fun y => by omega)).trans (by omega)

theorem a_even (m : ℕ) (hm : 1 ≤ m) : a (2 * m) + 6 * m = 2 * (m * m) + 4 := by
  have key : ∀ x ∈ Finset.Icc 1 (2 * m), ∀ y ∈ Finset.Icc 1 (2 * m),
      ((if x + y < 2 * m ∧ 2 * x ≠ 2 * m ∧ 2 * y ≠ 2 * m ∧ 2 * (x + y) ≠ 2 * m then 1 else 0) +
        ((if x = m ∧ y < m then 1 else 0) + (if y = m ∧ x < m then 1 else 0) +
          (if x + y = m then 1 else 0)) : ℕ) = if x + y < 2 * m then 1 else 0 := by
    intro x hx y hy
    rw [Finset.mem_Icc] at hx hy
    split_ifs <;> omega
  have e1 : ∀ x ∈ Finset.Icc 1 (2 * m),
      (∑ y ∈ Finset.Icc 1 (2 * m),
          (if x + y < 2 * m ∧ 2 * x ≠ 2 * m ∧ 2 * y ≠ 2 * m ∧ 2 * (x + y) ≠ 2 * m then 1 else 0)) +
        ((if x = m then m - 1 else 0) + (if x < m then 1 else 0) + (if x < m then 1 else 0)) =
      ∑ y ∈ Finset.Icc 1 (2 * m), if x + y < 2 * m then 1 else 0 := by
    intro x hx
    have h := Finset.sum_congr rfl (key x hx)
    first
      | (rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          inner_C1, inner_C2, inner_C3] at h
         exact h)
      | (simp only [Finset.sum_add_distrib, inner_C1, inner_C2, inner_C3] at h
         first | exact h | omega)
  have e2 : (∑ x ∈ Finset.Icc 1 (2 * m), ∑ y ∈ Finset.Icc 1 (2 * m),
      (if x + y < 2 * m ∧ 2 * x ≠ 2 * m ∧ 2 * y ≠ 2 * m ∧ 2 * (x + y) ≠ 2 * m then 1 else 0)) +
        3 * (m - 1) =
      ∑ x ∈ Finset.Icc 1 (2 * m), ∑ y ∈ Finset.Icc 1 (2 * m), if x + y < 2 * m then 1 else 0 := by
    have h := Finset.sum_congr rfl e1
    first
      | (rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          sumA m hm, sumB m] at h
         omega)
      | (simp only [Finset.sum_add_distrib] at h
         rw [sumA m hm, sumB m] at h
         omega)
  have hP := P_eq (2 * m) (by omega)
  have e : 2 * m * (2 * m) = 4 * (m * m) := by ring
  rw [a_eq]
  omega

theorem closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = -(5 + 3 * (-1) ^ n - 2 * (n : ℤ)) * ((n : ℤ) - 2) / 4 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h' : (a (2 * m) : ℤ) + 6 * (m : ℤ) = 2 * ((m : ℤ) * (m : ℤ)) + 4 := by
      exact_mod_cast a_even m (by omega)
    rw [show ((-1 : ℤ)) ^ (2 * m) = 1 by
      first
        | exact Even.neg_one_pow ⟨m, two_mul m⟩
        | exact (even_two_mul m).neg_one_pow
        | simp [pow_mul]]
    refine Int.eq_ediv_of_mul_eq_left (by norm_num) ?_
    push_cast
    first | linear_combination 4 * h' | linarith | nlinarith [h']
  · have h' : (a (2 * m + 1) : ℤ) + (m : ℤ) = 2 * ((m : ℤ) * (m : ℤ)) := by
      exact_mod_cast a_odd m
    rw [show ((-1 : ℤ)) ^ (2 * m + 1) = -1 by
      first
        | exact Odd.neg_one_pow ⟨m, rfl⟩
        | exact (odd_two_mul_add_one m).neg_one_pow
        | simp [pow_succ, pow_mul]]
    refine Int.eq_ediv_of_mul_eq_left (by norm_num) ?_
    push_cast
    first | linear_combination 4 * h' | linarith | nlinarith [h']

end R325689

theorem OMA.solution : type_of% @OMA.S_oeis_a325689.main := by
  intro n hn
  exact R325689.closed_form n hn
