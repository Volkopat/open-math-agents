import OMAStatements.S_oeis_a282415

-- Problem: A282415: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 469, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a282415 PowerSeries

namespace OMA.Proof_oeis_a282415

-- ============================================================================
-- Section 1: Exact 2-step outer-diamond + x-axis characterization of Rule 469
-- ============================================================================

private abbrev c4 (t : ℕ) (x y : ℤ) : Bool := cell 469 t x y

private def rule469 (cur : Bool) (s : ℕ) : Bool :=
  (469 : ℕ).testBit (cur.toNat + 2 * s)

private lemma c4_succ (t : ℕ) (x y : ℤ) :
    c4 (t + 1) x y =
      rule469 (c4 t x y)
        ((c4 t (x + 1) y).toNat + (c4 t (x - 1) y).toNat +
         (c4 t x (y + 1)).toNat + (c4 t x (y - 1)).toNat) :=
  rfl

private lemma rule469_false (s : ℕ) (hs : s ≤ 4) : rule469 false s = true := by
  interval_cases s <;> decide

private lemma rule469_true (s : ℕ) (hs : s ≤ 4) : rule469 true s = decide (s = 3) := by
  interval_cases s <;> decide

private lemma c4_neg_x (t : ℕ) (x y : ℤ) : c4 t (-x) y = c4 t x y := by
  induction t generalizing x y with
  | zero => simp [c4, cell]
  | succ t ih =>
    rw [c4_succ, c4_succ, show -x + 1 = -(x - 1) by ring, show -x - 1 = -(x + 1) by ring,
        ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

private lemma c4_neg_y (t : ℕ) (x y : ℤ) : c4 t x (-y) = c4 t x y := by
  induction t generalizing x y with
  | zero => simp [c4, cell]
  | succ t ih =>
    rw [c4_succ, c4_succ, show -y + 1 = -(y - 1) by ring, show -y - 1 = -(y + 1) by ring,
        ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 1; omega

private lemma c4_even_and_odd (m : ℕ) :
    (∀ x y : ℤ, (m : ℤ) < |x| + |y| → c4 (2 * m) x y = false) ∧
    (∀ x : ℤ, c4 (2 * m) x 0 = decide (|x| ≤ (m : ℤ))) ∧
    (∀ x y : ℤ, (m : ℤ) < |x| + |y| → c4 (2 * m + 1) x y = true) ∧
    (∀ x : ℤ, c4 (2 * m + 1) x 0 = decide ((m : ℤ) < |x|)) := by
  have step_even_to_odd : ∀ k : ℕ,
      (∀ x y : ℤ, (k : ℤ) < |x| + |y| → c4 (2 * k) x y = false) →
      (∀ x : ℤ, c4 (2 * k) x 0 = decide (|x| ≤ (k : ℤ))) →
      (∀ x y : ℤ, (k : ℤ) < |x| + |y| → c4 (2 * k + 1) x y = true) ∧
      (∀ x : ℤ, c4 (2 * k + 1) x 0 = decide ((k : ℤ) < |x|)) := by
    intro k hout hax
    refine ⟨?_, ?_⟩
    · intro x y h
      rw [c4_succ, hout x y h]
      apply rule469_false
      have a1 := Bool.toNat_le (c4 (2 * k) (x + 1) y)
      have a2 := Bool.toNat_le (c4 (2 * k) (x - 1) y)
      have a3 := Bool.toNat_le (c4 (2 * k) x (y + 1))
      have a4 := Bool.toNat_le (c4 (2 * k) x (y - 1))
      omega
    · intro x
      rw [c4_succ, hax x, hax (x + 1), hax (x - 1)]
      simp only [zero_add, zero_sub]
      rw [c4_neg_y (2 * k) x 1]
      by_cases hgt : (k : ℤ) < |x|
      · have hle : ¬ |x| ≤ (k : ℤ) := by omega
        rw [decide_eq_false hle, decide_eq_true hgt]
        apply rule469_false
        have a1 := Bool.toNat_le (decide (|x + 1| ≤ (k : ℤ)))
        have a2 := Bool.toNat_le (decide (|x - 1| ≤ (k : ℤ)))
        have a3 := Bool.toNat_le (c4 (2 * k) x 1)
        omega
      · have hle : |x| ≤ (k : ℤ) := by omega
        rw [decide_eq_true hle, decide_eq_false hgt]
        have hs4 : (decide (|x + 1| ≤ (k : ℤ))).toNat + (decide (|x - 1| ≤ (k : ℤ))).toNat +
            (c4 (2 * k) x 1).toNat + (c4 (2 * k) x 1).toNat ≤ 4 := by
          have a1 := Bool.toNat_le (decide (|x + 1| ≤ (k : ℤ)))
          have a2 := Bool.toNat_le (decide (|x - 1| ≤ (k : ℤ)))
          have a3 := Bool.toNat_le (c4 (2 * k) x 1)
          omega
        rw [rule469_true _ hs4, decide_eq_false_iff_not]
        by_cases heq : |x| = (k : ℤ)
        · have hy1 : c4 (2 * k) x 1 = false := hout x 1 (by simp; omega)
          rw [hy1, Bool.toNat_false]
          have a1 := Bool.toNat_le (decide (|x + 1| ≤ (k : ℤ)))
          have a2 := Bool.toNat_le (decide (|x - 1| ≤ (k : ℤ)))
          omega
        · have hp : |x + 1| ≤ (k : ℤ) := by simp only [abs_eq_max_neg] at heq hle ⊢; omega
          have hm : |x - 1| ≤ (k : ℤ) := by simp only [abs_eq_max_neg] at heq hle ⊢; omega
          rw [decide_eq_true hp, decide_eq_true hm, Bool.toNat_true]
          omega
  induction m with
  | zero =>
    have hout0 : ∀ x y : ℤ, ((0 : ℕ) : ℤ) < |x| + |y| → c4 (2 * 0) x y = false := by
      intro x y h
      simp only [c4, cell, decide_eq_false_iff_not]
      rintro ⟨rfl, rfl⟩; simp at h
    have hax0 : ∀ x : ℤ, c4 (2 * 0) x 0 = decide (|x| ≤ ((0 : ℕ) : ℤ)) := by
      intro x
      simp only [c4, cell, Nat.cast_zero]
      apply decide_eq_decide.mpr
      simp only [and_true, abs_eq_max_neg]; omega
    exact ⟨hout0, hax0, step_even_to_odd 0 hout0 hax0⟩
  | succ m ih =>
    obtain ⟨_, _, hout1, hax1⟩ := ih
    have hout2 : ∀ x y : ℤ, ((m + 1 : ℕ) : ℤ) < |x| + |y| → c4 (2 * (m + 1)) x y = false := by
      intro x y h
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, c4_succ]
      have hC : c4 (2 * m + 1) x y = true := hout1 x y (by push_cast at h; omega)
      have hE : c4 (2 * m + 1) (x + 1) y = true :=
        hout1 (x + 1) y (by simp only [abs_eq_max_neg] at h ⊢; push_cast at h; omega)
      have hW : c4 (2 * m + 1) (x - 1) y = true :=
        hout1 (x - 1) y (by simp only [abs_eq_max_neg] at h ⊢; push_cast at h; omega)
      have hN : c4 (2 * m + 1) x (y + 1) = true :=
        hout1 x (y + 1) (by simp only [abs_eq_max_neg] at h ⊢; push_cast at h; omega)
      have hS : c4 (2 * m + 1) x (y - 1) = true :=
        hout1 x (y - 1) (by simp only [abs_eq_max_neg] at h ⊢; push_cast at h; omega)
      rw [hC, hE, hW, hN, hS]; decide
    have hax2 : ∀ x : ℤ, c4 (2 * (m + 1)) x 0 = decide (|x| ≤ ((m + 1 : ℕ) : ℤ)) := by
      intro x
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, c4_succ, hax1 x, hax1 (x + 1), hax1 (x - 1)]
      simp only [zero_add, zero_sub]
      by_cases hle : |x| ≤ (m : ℤ)
      · have h1 : ¬ ((m : ℤ) < |x|) := by omega
        have h2 : |x| ≤ ((m + 1 : ℕ) : ℤ) := by push_cast; omega
        rw [decide_eq_false h1, decide_eq_true h2]
        apply rule469_false
        have a1 := Bool.toNat_le (decide ((m : ℤ) < |x + 1|))
        have a2 := Bool.toNat_le (decide ((m : ℤ) < |x - 1|))
        have a3 := Bool.toNat_le (c4 (2 * m + 1) x 1)
        have a4 := Bool.toNat_le (c4 (2 * m + 1) x (-1))
        omega
      · by_cases heq : |x| = ((m + 1 : ℕ) : ℤ)
        · have hC : (m : ℤ) < |x| := by push_cast at heq; omega
          have hN : c4 (2 * m + 1) x 1 = true := hout1 x 1 (by simp; push_cast at heq; omega)
          have hS : c4 (2 * m + 1) x (-1) = true := hout1 x (-1) (by simp; push_cast at heq; omega)
          rw [decide_eq_true hC, hN, hS, decide_eq_true (by omega : |x| ≤ ((m + 1 : ℕ) : ℤ))]
          rcases le_or_gt 0 x with hx | hx
          · have hxp : (m : ℤ) < |x + 1| := by
              rw [abs_of_nonneg hx] at heq; rw [abs_of_nonneg (by omega)]; push_cast at heq; omega
            have hxm : ¬ ((m : ℤ) < |x - 1|) := by
              rw [abs_of_nonneg hx] at heq; rw [abs_of_nonneg (by push_cast at heq; omega)]; push_cast at heq; omega
            rw [decide_eq_true hxp, decide_eq_false hxm]; decide
          · have hxp : ¬ ((m : ℤ) < |x + 1|) := by
              rw [abs_of_neg hx] at heq; rw [abs_of_nonpos (by push_cast at heq; omega)]; push_cast at heq; omega
            have hxm : (m : ℤ) < |x - 1| := by
              rw [abs_of_neg hx] at heq; rw [abs_of_neg (by omega)]; push_cast at heq; omega
            rw [decide_eq_false hxp, decide_eq_true hxm]; decide
        · have hgt : ((m + 1 : ℕ) : ℤ) < |x| := by push_cast; omega
          have hC : (m : ℤ) < |x| := by push_cast at hgt; omega
          have hxp : (m : ℤ) < |x + 1| := by simp only [abs_eq_max_neg] at hgt ⊢; push_cast at hgt; omega
          have hxm : (m : ℤ) < |x - 1| := by simp only [abs_eq_max_neg] at hgt ⊢; push_cast at hgt; omega
          have hN : c4 (2 * m + 1) x 1 = true := hout1 x 1 (by simp; push_cast at hgt; omega)
          have hS : c4 (2 * m + 1) x (-1) = true := hout1 x (-1) (by simp; push_cast at hgt; omega)
          rw [decide_eq_true hC, decide_eq_true hxp, decide_eq_true hxm, hN, hS,
              decide_eq_false (by omega : ¬ |x| ≤ ((m + 1 : ℕ) : ℤ))]
          decide
    exact ⟨hout2, hax2, step_even_to_odd (m + 1) hout2 hax2⟩

-- ============================================================================
-- Section 2: Closed form for a(n), recurrence, and generating function
-- ============================================================================

private lemma geom10 (k : ℕ) : 9 * ∑ j ∈ Finset.range k, (10 : ℤ) ^ j = 10 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring

private lemma a_eq_sum_pos (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), if c4 n (j : ℤ) 0 then (10 : ℤ) ^ j else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect (fun j => if c4 n (j : ℤ) 0 then (10 : ℤ) ^ j else 0) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hsub : n + 1 - 1 - k = n - k := by omega
  rw [hsub, ← c4_neg_x n ((n - k : ℕ) : ℤ) 0,
      show -((n - k : ℕ) : ℤ) = (k : ℤ) - (n : ℤ) by omega]

private lemma a_even_mul9 (m : ℕ) : 9 * a (2 * m) = 10 ^ (m + 1) - 1 := by
  rw [a_eq_sum_pos]
  have hax := (c4_even_and_odd m).2.1
  have hsum : (∑ j ∈ Finset.range (2 * m + 1), if c4 (2 * m) (j : ℤ) 0 then (10 : ℤ) ^ j else 0) =
      ∑ j ∈ Finset.range (m + 1), (10 : ℤ) ^ j := by
    rw [show 2 * m + 1 = (m + 1) + m by omega, Finset.sum_range_add]
    have h1 : (∑ j ∈ Finset.range (m + 1), if c4 (2 * m) (j : ℤ) 0 then (10 : ℤ) ^ j else 0) =
        ∑ j ∈ Finset.range (m + 1), (10 : ℤ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hax (j : ℤ), abs_of_nonneg (Int.natCast_nonneg j), decide_eq_true (by omega), if_pos rfl]
    have h2 : (∑ x ∈ Finset.range m, if c4 (2 * m) ((m + 1 + x : ℕ) : ℤ) 0 then (10 : ℤ) ^ (m + 1 + x) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [hax, abs_of_nonneg (Int.natCast_nonneg _), decide_eq_false (by omega), if_neg Bool.false_ne_true]
    rw [h1, h2, add_zero]
  rw [hsum, geom10]

private lemma a_odd_mul9 (m : ℕ) : 9 * a (2 * m + 1) = 10 ^ (2 * m + 2) - 10 ^ (m + 1) := by
  rw [a_eq_sum_pos]
  have hax := (c4_even_and_odd m).2.2.2
  have hsum : (∑ j ∈ Finset.range (2 * m + 2), if c4 (2 * m + 1) (j : ℤ) 0 then (10 : ℤ) ^ j else 0) +
      (∑ j ∈ Finset.range (m + 1), (10 : ℤ) ^ j) =
      ∑ j ∈ Finset.range (2 * m + 2), (10 : ℤ) ^ j := by
    conv_rhs => rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, Finset.sum_range_add]
    conv_lhs => arg 1; rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, Finset.sum_range_add]
    have h1 : (∑ j ∈ Finset.range (m + 1), if c4 (2 * m + 1) (j : ℤ) 0 then (10 : ℤ) ^ j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hax (j : ℤ), abs_of_nonneg (Int.natCast_nonneg j), decide_eq_false (by omega), if_neg Bool.false_ne_true]
    have h2 : (∑ x ∈ Finset.range (m + 1), if c4 (2 * m + 1) ((m + 1 + x : ℕ) : ℤ) 0 then (10 : ℤ) ^ (m + 1 + x) else 0) =
        ∑ x ∈ Finset.range (m + 1), (10 : ℤ) ^ (m + 1 + x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hax, abs_of_nonneg (Int.natCast_nonneg _), decide_eq_true (by omega), if_pos rfl]
    rw [h1, h2, zero_add, add_comm]
  have h9 := congrArg (9 * ·) hsum
  rw [mul_add, geom10 (m + 1), geom10 (2 * m + 2)] at h9
  linarith

private lemma a_rec_int (n : ℕ) (hn : 6 ≤ n) :
    a n = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6) := by
  by_cases hp : n % 2 = 0
  · set m := n / 2 - 3
    have hn_eq : n = 2 * (m + 3) := by omega
    rw [hn_eq, show 2 * (m + 3) - 2 = 2 * (m + 2) by omega,
        show 2 * (m + 3) - 4 = 2 * (m + 1) by omega,
        show 2 * (m + 3) - 6 = 2 * m by omega]
    have h3 := a_even_mul9 (m + 3)
    have h2 := a_even_mul9 (m + 2)
    have h1 := a_even_mul9 (m + 1)
    have h0 := a_even_mul9 m
    have p3 : (10 : ℤ) ^ (m + 3 + 1) = 1000 * (10 : ℤ) ^ (m + 1) := by
      rw [show m + 3 + 1 = (m + 1) + 3 by omega, pow_add]; ring
    have p2 : (10 : ℤ) ^ (m + 2 + 1) = 100 * (10 : ℤ) ^ (m + 1) := by
      rw [show m + 2 + 1 = (m + 1) + 2 by omega, pow_add]; ring
    have p1 : (10 : ℤ) ^ (m + 1 + 1) = 10 * (10 : ℤ) ^ (m + 1) := by
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_add]; ring
    linarith
  · set m := n / 2 - 3
    have hn_eq : n = 2 * (m + 3) + 1 := by omega
    rw [hn_eq, show 2 * (m + 3) + 1 - 2 = 2 * (m + 2) + 1 by omega,
        show 2 * (m + 3) + 1 - 4 = 2 * (m + 1) + 1 by omega,
        show 2 * (m + 3) + 1 - 6 = 2 * m + 1 by omega]
    have h3 := a_odd_mul9 (m + 3)
    have h2 := a_odd_mul9 (m + 2)
    have h1 := a_odd_mul9 (m + 1)
    have h0 := a_odd_mul9 m
    have p3 : (10 : ℤ) ^ (m + 3 + 1) = 1000 * (10 : ℤ) ^ (m + 1) := by
      rw [show m + 3 + 1 = (m + 1) + 3 by omega, pow_add]; ring
    have p2 : (10 : ℤ) ^ (m + 2 + 1) = 100 * (10 : ℤ) ^ (m + 1) := by
      rw [show m + 2 + 1 = (m + 1) + 2 by omega, pow_add]; ring
    have p1 : (10 : ℤ) ^ (m + 1 + 1) = 10 * (10 : ℤ) ^ (m + 1) := by
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_add]; ring
    have q3 : (10 : ℤ) ^ (2 * (m + 3) + 2) = 1000000 * (10 : ℤ) ^ (2 * m + 2) := by
      rw [show 2 * (m + 3) + 2 = (2 * m + 2) + 6 by omega, pow_add]; ring
    have q2 : (10 : ℤ) ^ (2 * (m + 2) + 2) = 10000 * (10 : ℤ) ^ (2 * m + 2) := by
      rw [show 2 * (m + 2) + 2 = (2 * m + 2) + 4 by omega, pow_add]; ring
    have q1 : (10 : ℤ) ^ (2 * (m + 1) + 2) = 100 * (10 : ℤ) ^ (2 * m + 2) := by
      rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega, pow_add]; ring
    linarith

private lemma a_rec (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6) := by
  exact_mod_cast a_rec_int n hn

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2) : PowerSeries ℚ) =
      1 + 10 * X - 100 * X ^ 2 - 10 * X ^ 3 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : A * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2) : PowerSeries ℚ) =
      A - PowerSeries.C (111 : ℚ) * (A * X ^ 2) + PowerSeries.C (1110 : ℚ) * (A * X ^ 4) -
        PowerSeries.C (1000 : ℚ) * (A * X ^ 6) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + 10 * X - 100 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) + PowerSeries.C (10 : ℚ) * X -
        PowerSeries.C (100 : ℚ) * X ^ 2 - PowerSeries.C (10 : ℚ) * X ^ 3 := by
    simp only [map_one, map_ofNat]
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 6 ≤ n
  · have hrec := a_rec n hn
    simp only [show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      ite_true, ite_false]
    linarith
  · have h0 : (a 0 : ℚ) = 1 := by
      have := a_even_mul9 0; norm_num at this; exact_mod_cast (by omega : a 0 = 1)
    have h1 : (a 1 : ℚ) = 10 := by
      have := a_odd_mul9 0; norm_num at this; exact_mod_cast (by omega : a 1 = 10)
    have h2 : (a 2 : ℚ) = 11 := by
      have := a_even_mul9 1; norm_num at this; exact_mod_cast (by omega : a 2 = 11)
    have h3 : (a 3 : ℚ) = 1100 := by
      have := a_odd_mul9 1; norm_num at this; exact_mod_cast (by omega : a 3 = 1100)
    have h4 : (a 4 : ℚ) = 111 := by
      have := a_even_mul9 2; norm_num at this; exact_mod_cast (by omega : a 4 = 111)
    have h5 : (a 5 : ℚ) = 111000 := by
      have := a_odd_mul9 2; norm_num at this; exact_mod_cast (by omega : a 5 = 111000)
    have hs3 : (3 - 2 : ℕ) = 1 := rfl
    have hs4 : (4 - 2 : ℕ) = 2 := rfl
    have hs5 : (5 - 2 : ℕ) = 3 := rfl
    interval_cases n <;>
      simp only [Nat.sub_self, hs3, hs4, hs5, h0, h1, h2, h3, h4, h5] <;>
      norm_num

end OMA.Proof_oeis_a282415

theorem OMA.solution : type_of% @OMA.S_oeis_a282415.main :=
  ⟨OMA.Proof_oeis_a282415.a_rec, OMA.Proof_oeis_a282415.gf_eq⟩
