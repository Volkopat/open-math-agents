import OMAStatements.S_oeis_a245024
import Mathlib

/-!
Proof sketch. Even n >= 10 with n = 4 mod 6 are always terms, n = 0 mod 6 never; so the
successor of a term t is t + 2 (t = 2 mod 6), t + 4 (t = 4 mod 6, t + 4 a term) or t + 6.
Five consecutive candidates t + 4 + 6 j cover all residues mod 5: the one with 5 | n - 1 is a
term and the one with 5 | n - 3 is not. Run witnesses are checked locally with norm_num.
-/

namespace R245024
open OMA.S_oeis_a245024

theorem mf_ge {n k : ℕ} (hn : n ≠ 1) (h : ∀ q, 2 ≤ q → q ≤ k → ¬ q ∣ n) : k < n.minFac := by
  by_contra hc
  exact h _ (Nat.minFac_prime hn).two_le (not_lt.mp hc) (Nat.minFac_dvd n)

theorem term_mod {n : ℕ} (h : isTerm n) : 10 ≤ n ∧ (n % 6 = 2 ∨ n % 6 = 4) := by
  obtain ⟨h4, he, hlt⟩ := h
  rw [Nat.even_iff] at he
  have h0 : n % 6 ≠ 0 := by
    intro h6
    have a1 : (n - 3).minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) (by omega)
    have a2 : 2 < (n - 1).minFac :=
      mf_ge (by omega) (fun q hq1 hq2 hd => by interval_cases q; omega)
    omega
  refine ⟨?_, by omega⟩
  by_contra hc
  have : n = 4 ∨ n = 8 := by omega
  rcases this with rfl | rfl <;> norm_num at hlt

theorem term_of4 {n : ℕ} (h6 : n % 6 = 4) (h10 : 10 ≤ n) : isTerm n := by
  refine ⟨by omega, Nat.even_iff.2 (by omega), ?_⟩
  have a1 : (n - 1).minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) (by omega)
  have a2 : 3 < (n - 3).minFac :=
    mf_ge (by omega) (fun q hq1 hq2 hd => by interval_cases q <;> omega)
  omega

theorem term51 {n : ℕ} (h6 : n % 6 = 2) (h5 : n % 5 = 1) : isTerm n := by
  refine ⟨by omega, Nat.even_iff.2 (by omega), ?_⟩
  have a1 : (n - 1).minFac ≤ 5 := Nat.minFac_le_of_dvd (by norm_num) (by omega)
  have a2 : 5 < (n - 3).minFac :=
    mf_ge (by omega) (fun q hq1 hq2 hd => by interval_cases q <;> omega)
  omega

theorem nt53 {n : ℕ} (h6 : n % 6 = 2) (h5 : n % 5 = 3) : ¬ isTerm n := by
  rintro ⟨h4, -, hlt⟩
  have a1 : (n - 3).minFac ≤ 5 := Nat.minFac_le_of_dvd (by norm_num) (by omega)
  have a2 : 5 < (n - 1).minFac :=
    mf_ge (by omega) (fun q hq1 hq2 hd => by interval_cases q <;> omega)
  omega

theorem yes {n : ℕ} (h6 : n % 2 = 0) (h4 : 4 ≤ n) (hm : (n - 1).minFac < (n - 3).minFac) :
    isTerm n := ⟨h4, Nat.even_iff.2 h6, hm⟩

theorem no {n : ℕ} (hm : ¬ (n - 1).minFac < (n - 3).minFac) : ¬ isTerm n :=
  fun h => hm h.2.2

theorem hinf : (Set.ofPred isTerm).Infinite :=
  Set.infinite_of_forall_exists_gt fun x =>
    ⟨6 * x + 10, show isTerm (6 * x + 10) from term_of4 (by omega) (by omega), by omega⟩

theorem tm (i : ℕ) : isTerm (a i) := Nat.nth_mem_of_infinite hinf i

theorem exists_idx {t : ℕ} (h : isTerm t) : ∃ c, a c = t := by
  classical
  exact ⟨_, Nat.nth_count h⟩

theorem next_eq {i m : ℕ} (hm : a i < m) (ht : isTerm m)
    (hno : ∀ x, a i < x → x < m → ¬ isTerm x) : a (i + 1) = m := by
  have h1 : a i < a (i + 1) := (Nat.nth_lt_nth hinf).2 (Nat.lt_succ_self i)
  have h2 : isTerm (a (i + 1)) := Nat.nth_mem_of_infinite hinf _
  rcases lt_trichotomy (a (i + 1)) m with h | h | h
  · exact absurd h2 (hno _ h1 h)
  · exact h
  · have h3 : m ≤ a i := Nat.le_nth_of_lt_nth_succ (p := isTerm) h ht
    omega

theorem s2 {i t u : ℕ} (h : a i = t) (h6 : t % 6 = 2) (hu : t + 2 = u) : a (i + 1) = u := by
  have h10 := (term_mod (tm i)).1
  refine next_eq (by omega) (term_of4 (by omega) (by omega)) ?_
  intro x h1 h2 hx
  have := (term_mod hx).2
  omega

theorem s4y {i t u : ℕ} (h : a i = t) (h6 : t % 6 = 4) (ht : isTerm (t + 4)) (hu : t + 4 = u) :
    a (i + 1) = u := by
  subst hu
  refine next_eq (by omega) ht ?_
  intro x h1 h2 hx
  have := (term_mod hx).2
  omega

theorem s4n {i t u : ℕ} (h : a i = t) (h6 : t % 6 = 4) (hn : ¬ isTerm (t + 4)) (hu : t + 6 = u) :
    a (i + 1) = u := by
  have h10 := (term_mod (tm i)).1
  subst hu
  refine next_eq (by omega) (term_of4 (by omega) (by omega)) ?_
  intro x h1 h2 hx
  by_cases e : x = t + 4
  · subst e
    exact hn hx
  · have := (term_mod hx).2
    omega

theorem ad (i : ℕ) : a (i + 1) = a i + d i := by
  have : a i < a (i + 1) := (Nat.nth_lt_nth hinf).2 (Nat.lt_succ_self i)
  unfold d
  omega

theorem step (i : ℕ) : (a i % 6 = 2 ∧ d i = 2) ∨ (a i % 6 = 4 ∧ isTerm (a i + 4) ∧ d i = 4) ∨
    (a i % 6 = 4 ∧ ¬ isTerm (a i + 4) ∧ d i = 6) := by
  have e := ad i
  rcases (term_mod (tm i)).2 with h | h
  · have := s2 (i := i) rfl h rfl
    left
    exact ⟨h, by omega⟩
  · by_cases ht : isTerm (a i + 4)
    · have := s4y (i := i) rfl h ht rfl
      right; left
      exact ⟨h, ht, by omega⟩
    · have := s4n (i := i) rfl h ht rfl
      right; right
      exact ⟨h, ht, by omega⟩

theorem six {m : ℕ} (h : d m = 6) :
    (a m + 4) % 6 = 2 ∧ ¬ isTerm (a m + 4) ∧ a (m + 1) = a m + 6 := by
  have e := ad m
  rcases step m with ⟨a1, b1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩
  · omega
  · omega
  · exact ⟨by omega, b1, by omega⟩

theorem ft {m : ℕ} (h4 : d m = 4) (h2 : d (m + 1) = 2) :
    (a m + 4) % 6 = 2 ∧ isTerm (a m + 4) ∧ a (m + 2) = a m + 6 := by
  have e1 := ad m
  have e2 : a (m + 2) = a (m + 1) + d (m + 1) := ad (m + 1)
  rcases step m with ⟨a1, b1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩
  · omega
  · exact ⟨by omega, b1, by omega⟩
  · omega

theorem c1 (i : ℕ) : d i = 2 ∨ d i = 4 ∨ d i = 6 := by
  rcases step i with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega

theorem c2 (i : ℕ) : ¬ (d i = 2 ∧ d (i + 1) = 2) := by
  rintro ⟨h1, h2⟩
  have e := ad i
  rcases step i with ⟨a1, b1⟩ | ⟨a1, -, b1⟩ | ⟨a1, -, b1⟩ <;>
  rcases step (i + 1) with ⟨a2, b2⟩ | ⟨a2, -, b2⟩ | ⟨a2, -, b2⟩ <;> omega

theorem c3 (i : ℕ) : ¬ (d i = 4 ∧ d (i + 1) = 4) := by
  rintro ⟨h1, h2⟩
  have e := ad i
  rcases step i with ⟨a1, b1⟩ | ⟨a1, -, b1⟩ | ⟨a1, -, b1⟩ <;>
  rcases step (i + 1) with ⟨a2, b2⟩ | ⟨a2, -, b2⟩ | ⟨a2, -, b2⟩ <;> omega

theorem c4 (i : ℕ) : ¬ (∀ j < 5, d (i + j) = 6) := by
  intro h
  have d0 : d i = 6 := h 0 (by norm_num)
  have d1 : d (i + 1) = 6 := h 1 (by norm_num)
  have d2 : d (i + 2) = 6 := h 2 (by norm_num)
  have d3 : d (i + 3) = 6 := h 3 (by norm_num)
  have d4 : d (i + 4) = 6 := h 4 (by norm_num)
  obtain ⟨p0, q0, -⟩ := six d0
  obtain ⟨p1, q1, -⟩ := six d1
  obtain ⟨p2, q2, -⟩ := six d2
  obtain ⟨p3, q3, -⟩ := six d3
  obtain ⟨p4, q4, -⟩ := six d4
  have e0 : a (i + 1) = a i + 6 := (six d0).2.2
  have e1 : a (i + 2) = a (i + 1) + 6 := (six d1).2.2
  have e2 : a (i + 3) = a (i + 2) + 6 := (six d2).2.2
  have e3 : a (i + 4) = a (i + 3) + 6 := (six d3).2.2
  rcases (by omega : a i % 5 = 0 ∨ a i % 5 = 1 ∨ a i % 5 = 2 ∨ a i % 5 = 3 ∨ a i % 5 = 4)
    with h' | h' | h' | h' | h'
  · exact q2 (term51 p2 (by omega))
  · exact q1 (term51 p1 (by omega))
  · exact q0 (term51 p0 (by omega))
  · exact q4 (term51 p4 (by omega))
  · exact q3 (term51 p3 (by omega))

theorem c6 (i : ℕ) : ¬ (∀ j < 5, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) := by
  intro h
  have h0 : d i = 4 ∧ d (i + 1) = 2 := h 0 (by norm_num)
  have h1 : d (i + 2) = 4 ∧ d (i + 3) = 2 := h 1 (by norm_num)
  have h2 : d (i + 4) = 4 ∧ d (i + 5) = 2 := h 2 (by norm_num)
  have h3 : d (i + 6) = 4 ∧ d (i + 7) = 2 := h 3 (by norm_num)
  have h4 : d (i + 8) = 4 ∧ d (i + 9) = 2 := h 4 (by norm_num)
  obtain ⟨p0, q0, -⟩ := ft h0.1 h0.2
  obtain ⟨p1, q1, -⟩ := ft h1.1 h1.2
  obtain ⟨p2, q2, -⟩ := ft h2.1 h2.2
  obtain ⟨p3, q3, -⟩ := ft h3.1 h3.2
  obtain ⟨p4, q4, -⟩ := ft h4.1 h4.2
  have e0 : a (i + 2) = a i + 6 := (ft h0.1 h0.2).2.2
  have e1 : a (i + 4) = a (i + 2) + 6 := (ft h1.1 h1.2).2.2
  have e2 : a (i + 6) = a (i + 4) + 6 := (ft h2.1 h2.2).2.2
  have e3 : a (i + 8) = a (i + 6) + 6 := (ft h3.1 h3.2).2.2
  rcases (by omega : a i % 5 = 0 ∨ a i % 5 = 1 ∨ a i % 5 = 2 ∨ a i % 5 = 3 ∨ a i % 5 = 4)
    with h' | h' | h' | h' | h'
  · exact nt53 p4 (by omega) q4
  · exact nt53 p3 (by omega) q3
  · exact nt53 p2 (by omega) q2
  · exact nt53 p1 (by omega) q1
  · exact nt53 p0 (by omega) q0

theorem w6_1 : ∃ i, (i = 0 ∨ d (i - 1) ≠ 6) ∧ (∀ j < 1, d (i + j) = 6) ∧ d (i + 1) ≠ 6 := by
  obtain ⟨c, h0⟩ := exists_idx (t := 134) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 136 := s2 h0 (by norm_num) (by norm_num)
  have h2 : a (c + 2) = 142 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 146 := s4y h2 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  refine ⟨c + 1, Or.inr ?_, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]; simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w6_2 : ∃ i, (i = 0 ∨ d (i - 1) ≠ 6) ∧ (∀ j < 2, d (i + j) = 6) ∧ d (i + 2) ≠ 6 := by
  obtain ⟨c, h0⟩ := exists_idx (t := 116) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 118 := s2 h0 (by norm_num) (by norm_num)
  have h2 : a (c + 2) = 124 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 130 := s4n h2 (by norm_num) (no (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 134 := s4y h3 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  refine ⟨c + 1, Or.inr ?_, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]; simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w6_3 : ∃ i, (i = 0 ∨ d (i - 1) ≠ 6) ∧ (∀ j < 3, d (i + j) = 6) ∧ d (i + 3) ≠ 6 := by
  obtain ⟨c, h0⟩ := exists_idx (t := 26) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 28 := s2 h0 (by norm_num) (by norm_num)
  have h2 : a (c + 2) = 34 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 40 := s4n h2 (by norm_num) (no (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 46 := s4n h3 (by norm_num) (no (by norm_num)) (by norm_num)
  have h5 : a (c + 5) = 50 := s4y h4 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  refine ⟨c + 1, Or.inr ?_, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]; simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w6_4 : ∃ i, (i = 0 ∨ d (i - 1) ≠ 6) ∧ (∀ j < 4, d (i + j) = 6) ∧ d (i + 4) ≠ 6 := by
  obtain ⟨c, h0⟩ := exists_idx (t := 56) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 58 := s2 h0 (by norm_num) (by norm_num)
  have h2 : a (c + 2) = 64 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 70 := s4n h2 (by norm_num) (no (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 76 := s4n h3 (by norm_num) (no (by norm_num)) (by norm_num)
  have h5 : a (c + 5) = 82 := s4n h4 (by norm_num) (no (by norm_num)) (by norm_num)
  have h6 : a (c + 6) = 86 := s4y h5 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  refine ⟨c + 1, Or.inr ?_, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]; simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w42_1 : ∃ i, (i < 2 ∨ ¬ (d (i - 2) = 4 ∧ d (i - 1) = 2)) ∧
    (∀ j < 1, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) ∧
    ¬ (d (i + 2 * 1) = 4 ∧ d (i + 2 * 1 + 1) = 2) := by
  obtain ⟨c, h0⟩ := exists_idx (t := 10) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 16 := s4n h0 (by norm_num) (no (by norm_num)) (by norm_num)
  have h2 : a (c + 2) = 22 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 26 := s4y h2 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 28 := s2 h3 (by norm_num) (by norm_num)
  have h5 : a (c + 5) = 34 := s4n h4 (by norm_num) (no (by norm_num)) (by norm_num)
  have h6 : a (c + 6) = 40 := s4n h5 (by norm_num) (no (by norm_num)) (by norm_num)
  refine ⟨c + 2, Or.inr ?_, ?_, ?_⟩
  · rw [show c + 2 - 2 = c by omega, show c + 2 - 1 = c + 1 by omega]
    simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w42_2 : ∃ i, (i < 2 ∨ ¬ (d (i - 2) = 4 ∧ d (i - 1) = 2)) ∧
    (∀ j < 2, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) ∧
    ¬ (d (i + 2 * 2) = 4 ∧ d (i + 2 * 2 + 1) = 2) := by
  obtain ⟨c, h0⟩ := exists_idx (t := 34) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 40 := s4n h0 (by norm_num) (no (by norm_num)) (by norm_num)
  have h2 : a (c + 2) = 46 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 50 := s4y h2 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 52 := s2 h3 (by norm_num) (by norm_num)
  have h5 : a (c + 5) = 56 := s4y h4 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h6 : a (c + 6) = 58 := s2 h5 (by norm_num) (by norm_num)
  have h7 : a (c + 7) = 64 := s4n h6 (by norm_num) (no (by norm_num)) (by norm_num)
  have h8 : a (c + 8) = 70 := s4n h7 (by norm_num) (no (by norm_num)) (by norm_num)
  refine ⟨c + 2, Or.inr ?_, ?_, ?_⟩
  · rw [show c + 2 - 2 = c by omega, show c + 2 - 1 = c + 1 by omega]
    simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w42_3 : ∃ i, (i < 2 ∨ ¬ (d (i - 2) = 4 ∧ d (i - 1) = 2)) ∧
    (∀ j < 3, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) ∧
    ¬ (d (i + 2 * 3) = 4 ∧ d (i + 2 * 3 + 1) = 2) := by
  obtain ⟨c, h0⟩ := exists_idx (t := 238) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 244 := s4n h0 (by norm_num) (no (by norm_num)) (by norm_num)
  have h2 : a (c + 2) = 250 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 254 := s4y h2 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 256 := s2 h3 (by norm_num) (by norm_num)
  have h5 : a (c + 5) = 260 := s4y h4 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h6 : a (c + 6) = 262 := s2 h5 (by norm_num) (by norm_num)
  have h7 : a (c + 7) = 266 := s4y h6 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h8 : a (c + 8) = 268 := s2 h7 (by norm_num) (by norm_num)
  have h9 : a (c + 9) = 274 := s4n h8 (by norm_num) (no (by norm_num)) (by norm_num)
  have h10 : a (c + 10) = 280 := s4n h9 (by norm_num) (no (by norm_num)) (by norm_num)
  refine ⟨c + 2, Or.inr ?_, ?_, ?_⟩
  · rw [show c + 2 - 2 = c by omega, show c + 2 - 1 = c + 1 by omega]
    simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]

theorem w42_4 : ∃ i, (i < 2 ∨ ¬ (d (i - 2) = 4 ∧ d (i - 1) = 2)) ∧
    (∀ j < 4, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) ∧
    ¬ (d (i + 2 * 4) = 4 ∧ d (i + 2 * 4 + 1) = 2) := by
  obtain ⟨c, h0⟩ := exists_idx (t := 1892) (yes (by norm_num) (by norm_num) (by norm_num))
  have h1 : a (c + 1) = 1894 := s2 h0 (by norm_num) (by norm_num)
  have h2 : a (c + 2) = 1900 := s4n h1 (by norm_num) (no (by norm_num)) (by norm_num)
  have h3 : a (c + 3) = 1904 := s4y h2 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h4 : a (c + 4) = 1906 := s2 h3 (by norm_num) (by norm_num)
  have h5 : a (c + 5) = 1910 := s4y h4 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h6 : a (c + 6) = 1912 := s2 h5 (by norm_num) (by norm_num)
  have h7 : a (c + 7) = 1916 := s4y h6 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h8 : a (c + 8) = 1918 := s2 h7 (by norm_num) (by norm_num)
  have h9 : a (c + 9) = 1922 := s4y h8 (by norm_num) (yes (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have h10 : a (c + 10) = 1924 := s2 h9 (by norm_num) (by norm_num)
  have h11 : a (c + 11) = 1930 := s4n h10 (by norm_num) (no (by norm_num)) (by norm_num)
  have h12 : a (c + 12) = 1936 := s4n h11 (by norm_num) (no (by norm_num)) (by norm_num)
  refine ⟨c + 2, Or.inr ?_, ?_, ?_⟩
  · rw [show c + 2 - 2 = c by omega, show c + 2 - 1 = c + 1 by omega]
    simp [d, Nat.add_assoc, *]
  · intro j hj; interval_cases j <;> simp [d, Nat.add_assoc, *]
  · simp [d, Nat.add_assoc, *]
end R245024

theorem OMA.solution : type_of% @OMA.S_oeis_a245024.main := by
  refine ⟨R245024.c1, R245024.c2, R245024.c3, R245024.c4, ?_, R245024.c6, ?_⟩
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact R245024.w6_1
    · exact R245024.w6_2
    · exact R245024.w6_3
    · exact R245024.w6_4
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact R245024.w42_1
    · exact R245024.w42_2
    · exact R245024.w42_3
    · exact R245024.w42_4
