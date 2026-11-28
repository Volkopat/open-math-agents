import OMAStatements.S_oeis_a337500

-- Problem: A337500: a(n) is the number of ballot sequences of length n tied or won by at most 3 votes.
-- Upstream: formal-conjectures statements/oeis-a337500.lean:0 (declaration OMA.S_oeis_a337500.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: only three (n even) or four (n odd) binomials survive, which gives the closed forms
-- (m+1) a(2m) = (3m+1) C(2m,m) and (m+2) a(2m+1) = 4(2m+1) C(2m,m); with
-- (m+1) C(2m+2,m+1) = 2(2m+1) C(2m,m) the recurrence becomes a polynomial identity in each parity.

open OMA.S_oeis_a337500 in
theorem even337500 (m : ℕ) :
    ((m : ℤ) + 1) * (a (2 * m) : ℤ) = (3 * (m : ℤ) + 1) * (Nat.centralBinom m : ℤ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : a (2 * 0) = 1 := by decide
    rw [h0, Nat.centralBinom_zero]
    norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have ha : a (2 * (p + 1)) = ∑ k ∈ ({p, p + 1, p + 2} : Finset ℕ), (2 * (p + 1)).choose k := by
      unfold a
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor <;> intro h <;> omega
    have n1 : p ∉ ({p + 1, p + 2} : Finset ℕ) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    have n2 : p + 1 ∉ ({p + 2} : Finset ℕ) := by
      rw [Finset.mem_singleton]
      omega
    rw [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_singleton] at ha
    have hsym : (2 * (p + 1)).choose (p + 2) = (2 * (p + 1)).choose p :=
      Nat.choose_symm_of_eq_add (by ring)
    have hr : (2 * (p + 1)).choose (p + 1) * (p + 1) = (2 * (p + 1)).choose p * (2 * (p + 1) - p) :=
      Nat.choose_succ_right_eq _ _
    rw [show 2 * (p + 1) - p = p + 2 by omega] at hr
    have hrz : (((2 * (p + 1)).choose (p + 1) : ℕ) : ℤ) * ((p : ℤ) + 1) =
        (((2 * (p + 1)).choose p : ℕ) : ℤ) * ((p : ℤ) + 2) := by
      exact_mod_cast hr
    rw [ha, hsym, Nat.centralBinom_eq_two_mul_choose]
    push_cast
    linear_combination (-2) * hrz

open OMA.S_oeis_a337500 in
theorem odd337500 (m : ℕ) :
    ((m : ℤ) + 2) * (a (2 * m + 1) : ℤ) = 4 * (2 * (m : ℤ) + 1) * (Nat.centralBinom m : ℤ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : a (2 * 0 + 1) = 2 := by decide
    rw [h1, Nat.centralBinom_zero]
    norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have ha : a (2 * (p + 1) + 1) =
        ∑ k ∈ ({p, p + 1, p + 2, p + 3} : Finset ℕ), (2 * (p + 1) + 1).choose k := by
      unfold a
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor <;> intro h <;> omega
    have n1 : p ∉ ({p + 1, p + 2, p + 3} : Finset ℕ) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      omega
    have n2 : p + 1 ∉ ({p + 2, p + 3} : Finset ℕ) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    have n3 : p + 2 ∉ ({p + 3} : Finset ℕ) := by
      rw [Finset.mem_singleton]
      omega
    rw [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_singleton] at ha
    have hsym1 : (2 * (p + 1) + 1).choose (p + 3) = (2 * (p + 1) + 1).choose p :=
      Nat.choose_symm_of_eq_add (by ring)
    have hsym2 : (2 * (p + 1) + 1).choose (p + 2) = (2 * (p + 1) + 1).choose (p + 1) :=
      Nat.choose_symm_of_eq_add (by ring)
    have hr : (2 * (p + 1) + 1).choose (p + 1) * (p + 1) =
        (2 * (p + 1) + 1).choose p * (2 * (p + 1) + 1 - p) := Nat.choose_succ_right_eq _ _
    rw [show 2 * (p + 1) + 1 - p = p + 3 by omega] at hr
    have hc : (2 * (p + 1)).choose (p + 1) * (2 * (p + 1) + 1) =
        (2 * (p + 1) + 1).choose (p + 1) * (2 * (p + 1) + 1 - (p + 1)) := Nat.choose_mul_succ_eq _ _
    rw [show 2 * (p + 1) + 1 - (p + 1) = p + 2 by omega] at hc
    have hrz : (((2 * (p + 1) + 1).choose (p + 1) : ℕ) : ℤ) * ((p : ℤ) + 1) =
        (((2 * (p + 1) + 1).choose p : ℕ) : ℤ) * ((p : ℤ) + 3) := by
      exact_mod_cast hr
    have hcz : (((2 * (p + 1)).choose (p + 1) : ℕ) : ℤ) * (2 * ((p : ℤ) + 1) + 1) =
        (((2 * (p + 1) + 1).choose (p + 1) : ℕ) : ℤ) * ((p : ℤ) + 2) := by
      exact_mod_cast hc
    rw [ha, hsym1, hsym2, Nat.centralBinom_eq_two_mul_choose]
    push_cast
    linear_combination (-2) * hrz - 4 * hcz

open OMA.S_oeis_a337500 in
theorem OMA.solution : type_of% @OMA.S_oeis_a337500.main := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 3 ∨ n = 2 * m + 4 := ⟨(n - 3) / 2, by omega⟩
  · rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega,
      show 2 * m + 3 - 3 = 2 * m by omega]
    have e0 := even337500 m
    have o0 := odd337500 m
    have e1 := even337500 (m + 1)
    rw [show 2 * (m + 1) = 2 * m + 2 by ring] at e1
    push_cast at e1
    have o1 := odd337500 (m + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at o1
    push_cast at o1
    have hb0 : ((m : ℤ) + 1) * (Nat.centralBinom (m + 1) : ℤ) =
        2 * (2 * (m : ℤ) + 1) * (Nat.centralBinom m : ℤ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hK : ((m : ℤ) + 1) * ((m : ℤ) + 2) * ((m : ℤ) + 3) ≠ 0 := by positivity
    push_cast
    refine (mul_eq_zero.mp ?_).resolve_left hK
    linear_combination
      (-((2 * (m : ℤ) + 3) + 3) * ((2 * (m : ℤ) + 3) - 4)) * ((m : ℤ) + 1) * ((m : ℤ) + 2) * o1
      + (2 * ((2 * (m : ℤ) + 3) ^ 2 - 2 * (2 * (m : ℤ) + 3) - 11)) * ((m : ℤ) + 1) * ((m : ℤ) + 3) * e1
      + (4 * ((2 * (m : ℤ) + 3) - 1) ^ 2) * ((m : ℤ) + 1) * ((m : ℤ) + 3) * o0
      + (-8 * ((2 * (m : ℤ) + 3) - 1) * ((2 * (m : ℤ) + 3) - 2)) * ((m : ℤ) + 2) * ((m : ℤ) + 3) * e0
      + (4 * (-((2 * (m : ℤ) + 3) + 3) * ((2 * (m : ℤ) + 3) - 4)) * ((m : ℤ) + 2) * (2 * (m : ℤ) + 3)
        + (2 * ((2 * (m : ℤ) + 3) ^ 2 - 2 * (2 * (m : ℤ) + 3) - 11)) * ((m : ℤ) + 3) * (3 * (m : ℤ) + 4))
        * hb0
  · rw [show 2 * m + 4 - 1 = 2 * m + 3 by omega, show 2 * m + 4 - 2 = 2 * m + 2 by omega,
      show 2 * m + 4 - 3 = 2 * m + 1 by omega]
    have o0 := odd337500 m
    have e1 := even337500 (m + 1)
    rw [show 2 * (m + 1) = 2 * m + 2 by ring] at e1
    push_cast at e1
    have o1 := odd337500 (m + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring] at o1
    push_cast at o1
    have e2 := even337500 (m + 2)
    rw [show 2 * (m + 2) = 2 * m + 4 by ring] at e2
    push_cast at e2
    have hb0 : ((m : ℤ) + 1) * (Nat.centralBinom (m + 1) : ℤ) =
        2 * (2 * (m : ℤ) + 1) * (Nat.centralBinom m : ℤ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have h1 : (m + 2) * Nat.centralBinom (m + 2) = 2 * (2 * (m + 1) + 1) * Nat.centralBinom (m + 1) :=
      Nat.succ_mul_centralBinom_succ (m + 1)
    have hb1 : ((m : ℤ) + 2) * (Nat.centralBinom (m + 2) : ℤ) =
        2 * (2 * ((m : ℤ) + 1) + 1) * (Nat.centralBinom (m + 1) : ℤ) := by
      exact_mod_cast h1
    have hK : ((m : ℤ) + 1) * ((m : ℤ) + 2) * ((m : ℤ) + 3) ≠ 0 := by positivity
    push_cast
    refine (mul_eq_zero.mp ?_).resolve_left hK
    linear_combination
      (-((2 * (m : ℤ) + 4) + 3) * ((2 * (m : ℤ) + 4) - 4)) * ((m : ℤ) + 1) * ((m : ℤ) + 2) * e2
      + (2 * ((2 * (m : ℤ) + 4) ^ 2 - 2 * (2 * (m : ℤ) + 4) - 11)) * ((m : ℤ) + 1) * ((m : ℤ) + 2) * o1
      + (4 * ((2 * (m : ℤ) + 4) - 1) ^ 2) * ((m : ℤ) + 1) * ((m : ℤ) + 3) * e1
      + (-8 * ((2 * (m : ℤ) + 4) - 1) * ((2 * (m : ℤ) + 4) - 2)) * ((m : ℤ) + 1) * ((m : ℤ) + 3) * o0
      + ((m : ℤ) + 1) * (-((2 * (m : ℤ) + 4) + 3) * ((2 * (m : ℤ) + 4) - 4)) * (3 * (m : ℤ) + 7) * hb1
      + (2 * (-((2 * (m : ℤ) + 4) + 3) * ((2 * (m : ℤ) + 4) - 4)) * (3 * (m : ℤ) + 7) * (2 * (m : ℤ) + 3)
        + 4 * (2 * ((2 * (m : ℤ) + 4) ^ 2 - 2 * (2 * (m : ℤ) + 4) - 11)) * ((m : ℤ) + 2) * (2 * (m : ℤ) + 3)
        + (4 * ((2 * (m : ℤ) + 4) - 1) ^ 2) * ((m : ℤ) + 3) * (3 * (m : ℤ) + 4)) * hb0
