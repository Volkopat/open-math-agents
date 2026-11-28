import OMAStatements.S_oeis_a273724
import Mathlib

/-!
Credit: @ivillar
Proof: chords from i and from j = 3i mod n coincide (for i /= j) exactly when 9i == i and 9j == j
(mod n); keeping the smaller point of each such pair gives a set R of representatives on which
the chord map is injective. R is all of 0..n-1 minus an explicit set of 1, 2, 3 or 5 points
(depending on n mod 8), found by writing 3i = qn + u, 9i = q9 n + v with q < 3, q9 < 9.
-/

namespace OMAA273724Helpers

open OMA.S_oeis_a273724 Finset

/-- One representative for each chord: drop `i` when `i = 3j mod n` for a smaller `j` with the
same chord. -/
def R (n : ℕ) : Finset ℕ :=
  (range n).filter fun i => 3 * i % n ≠ i ∧ ¬ (9 * i % n = i ∧ 3 * i % n < i)

theorem mod9 (n i : ℕ) : 3 * (3 * i % n) % n = 9 * i % n := by
  rw [show 9 * i = 3 * (3 * i) by ring, Nat.mul_mod 3 (3 * i % n), Nat.mod_mod, ← Nat.mul_mod]

theorem card_eq (n : ℕ) : a n = #(R n) := by
  unfold a chords
  have himg : ((range n).filter fun i => 3 * i % n ≠ i).image (fun i => s(i, 3 * i % n)) =
      (R n).image (fun i => s(i, 3 * i % n)) := by
    apply subset_antisymm
    · intro c hc
      rw [mem_image] at hc ⊢
      obtain ⟨i, hi, rfl⟩ := hc
      rw [mem_filter, mem_range] at hi
      have hn : 0 < n := by omega
      have hl := Nat.mod_lt (3 * i) hn
      by_cases h : 9 * i % n = i ∧ 3 * i % n < i
      · refine ⟨3 * i % n, ?_, ?_⟩
        · rw [R, mem_filter, mem_range, mod9]
          refine ⟨hl, by omega, by omega⟩
        · rw [mod9, h.1, Sym2.eq_swap]
      · exact ⟨i, by rw [R, mem_filter, mem_range]; exact ⟨hi.1, hi.2, h⟩, rfl⟩
    · apply image_subset_image
      intro i hi
      rw [R, mem_filter] at hi
      rw [mem_filter]
      exact ⟨hi.1, hi.2.1⟩
  rw [himg, card_image_of_injOn]
  intro i hi j hj hij
  rw [mem_coe, R, mem_filter] at hi hj
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have e1 : 9 * i % n = i := by rw [← mod9, h2, ← h1]
    have e2 : 9 * j % n = j := by rw [← mod9, ← h1, h2]
    have := hi.2.2
    have := hj.2.2
    rw [e1, h2] at hi
    rw [e2, ← h1] at hj
    omega

theorem count (n : ℕ) (X : Finset ℕ) (hX : X ⊆ range n)
    (h : ∀ i < n, (3 * i % n ≠ i ∧ ¬ (9 * i % n = i ∧ 3 * i % n < i)) ↔ i ∉ X) :
    #(R n) = n - #X := by
  have e : R n = range n \ X := by
    ext i
    rw [R, mem_filter, mem_sdiff, mem_range]
    constructor
    · rintro ⟨hi, hP⟩
      exact ⟨hi, (h i hi).mp hP⟩
    · rintro ⟨hi, hX⟩
      exact ⟨hi, (h i hi).mpr hX⟩
  rw [e, card_sdiff_of_subset hX, card_range]

theorem div_facts (n i : ℕ) (hi : i < n) :
    n * (3 * i / n) + 3 * i % n = 3 * i ∧ n * (9 * i / n) + 9 * i % n = 9 * i ∧
      3 * i % n < n ∧ 9 * i % n < n ∧ 3 * i / n < 3 ∧ 9 * i / n < 9 :=
  ⟨Nat.div_add_mod _ _, Nat.div_add_mod _ _, Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega),
    Nat.div_lt_of_lt_mul (by omega), Nat.div_lt_of_lt_mul (by omega)⟩

theorem cOdd (m : ℕ) : #(R (2 * m + 1)) = 2 * m := by
  rw [count (2 * m + 1) ({0} : Finset ℕ)]
  · rw [card_singleton]
    omega
  · intro x hx
    simp only [mem_singleton] at hx
    rw [mem_range]
    omega
  · intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := div_facts _ i hi
    generalize 3 * i / (2 * m + 1) = x at *
    generalize 9 * i / (2 * m + 1) = y at *
    generalize 3 * i % (2 * m + 1) = u at *
    generalize 9 * i % (2 * m + 1) = v at *
    simp only [mem_singleton]
    interval_cases x <;> interval_cases y <;> omega

theorem c2 (m : ℕ) : #(R (8 * m + 2)) = 8 * m := by
  rw [count (8 * m + 2) ({0, 4 * m + 1} : Finset ℕ)]
  · rw [card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
    omega
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    omega
  · intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := div_facts _ i hi
    generalize 3 * i / (8 * m + 2) = x at *
    generalize 9 * i / (8 * m + 2) = y at *
    generalize 3 * i % (8 * m + 2) = u at *
    generalize 9 * i % (8 * m + 2) = v at *
    simp only [mem_insert, mem_singleton]
    interval_cases x <;> interval_cases y <;> omega

theorem c6 (m : ℕ) : #(R (8 * m + 6)) = 8 * m + 4 := by
  rw [count (8 * m + 6) ({0, 4 * m + 3} : Finset ℕ)]
  · rw [card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
    omega
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    omega
  · intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := div_facts _ i hi
    generalize 3 * i / (8 * m + 6) = x at *
    generalize 9 * i / (8 * m + 6) = y at *
    generalize 3 * i % (8 * m + 6) = u at *
    generalize 9 * i % (8 * m + 6) = v at *
    simp only [mem_insert, mem_singleton]
    interval_cases x <;> interval_cases y <;> omega

theorem c4 (m : ℕ) : #(R (8 * m + 4)) = 8 * m + 1 := by
  rw [count (8 * m + 4) ({0, 4 * m + 2, 6 * m + 3} : Finset ℕ)]
  · rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega), card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
    omega
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    omega
  · intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := div_facts _ i hi
    generalize 3 * i / (8 * m + 4) = x at *
    generalize 9 * i / (8 * m + 4) = y at *
    generalize 3 * i % (8 * m + 4) = u at *
    generalize 9 * i % (8 * m + 4) = v at *
    simp only [mem_insert, mem_singleton]
    interval_cases x <;> interval_cases y <;> omega

theorem c0 (m : ℕ) : #(R (8 * m + 8)) = 8 * m + 3 := by
  rw [count (8 * m + 8) ({0, 4 * m + 4, 3 * m + 3, 6 * m + 6, 7 * m + 7} : Finset ℕ)]
  · rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega), card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega), card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega), card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
    omega
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    omega
  · intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := div_facts _ i hi
    generalize 3 * i / (8 * m + 8) = x at *
    generalize 9 * i / (8 * m + 8) = y at *
    generalize 3 * i % (8 * m + 8) = u at *
    generalize 9 * i % (8 * m + 8) = v at *
    simp only [mem_insert, mem_singleton]
    interval_cases x <;> interval_cases y <;> omega

theorem closed (n : ℕ) (hn : 0 < n) : (a n : ℤ) = n - (if n % 2 = 1 then 1
    else if n % 8 = 2 ∨ n % 8 = 6 then 2 else if n % 8 = 4 then 3 else 5) := by
  rw [card_eq]
  have hd := Nat.div_add_mod n 8
  have hlt := Nat.mod_lt n (show 8 > 0 by norm_num)
  generalize n / 8 = m at hd
  generalize n % 8 = r at hd hlt
  subst hd
  interval_cases r
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 8 * (k + 1) + 0 = 8 * k + 8 by ring, c0, if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    push_cast
    ring
  · rw [show 8 * m + 1 = 2 * (4 * m) + 1 by ring, cOdd, if_pos (by omega)]
    push_cast
    ring
  · rw [c2, if_neg (by omega), if_pos (by omega)]
    push_cast
    ring
  · rw [show 8 * m + 3 = 2 * (4 * m + 1) + 1 by ring, cOdd, if_pos (by omega)]
    push_cast
    ring
  · rw [c4, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    push_cast
    ring
  · rw [show 8 * m + 5 = 2 * (4 * m + 2) + 1 by ring, cOdd, if_pos (by omega)]
    push_cast
    ring
  · rw [c6, if_neg (by omega), if_pos (by omega)]
    push_cast
    ring
  · rw [show 8 * m + 7 = 2 * (4 * m + 3) + 1 by ring, cOdd, if_pos (by omega)]
    push_cast
    ring

end OMAA273724Helpers

open OMAA273724Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a273724.main := by
  refine ⟨closed, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 8 = m + 2 by omega,
    show m + 10 - 9 = m + 1 by omega, closed (m + 10) (by omega), closed (m + 9) (by omega),
    closed (m + 2) (by omega), closed (m + 1) (by omega),
    show (m + 10) % 2 = (m + 2) % 2 by omega, show (m + 10) % 8 = (m + 2) % 8 by omega,
    show (m + 9) % 2 = (m + 1) % 2 by omega, show (m + 9) % 8 = (m + 1) % 8 by omega]
  push_cast
  ring
