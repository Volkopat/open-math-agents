import OMAStatements.S_oeis_a282142

-- Problem: A282142: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 553
-- Upstream: formal-conjectures statements/oeis-a282142.lean:0 (declaration OMA.S_oeis_a282142.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.OeisA282142

open OMA.S_oeis_a282142 PowerSeries

private def step553 (c n1 n2 n3 n4 : Bool) : Bool :=
  (553 : ℕ).testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat))

private def uwStep (c n1 n2 n3 n4 : Bool) : Bool :=
  c && decide (n1.toNat + n2.toNat + n3.toNat + n4.toNat ≠ 3)

private lemma cell_succ (t : ℕ) (i j : ℤ) :
    cell 553 (t + 1) i j =
      step553 (cell 553 t i j) (cell 553 t (i + 1) j) (cell 553 t (i - 1) j)
        (cell 553 t i (j + 1)) (cell 553 t i (j - 1)) :=
  rfl

private lemma step553_01_step1 (x y : Bool) :
    step553 (x && y) true true x y = (x && y) := by
  cases x <;> cases y <;> rfl

private lemma step553_10_step1 (x y : Bool) :
    step553 (x && y) x y true true = (x && y) := by
  cases x <;> cases y <;> rfl

private lemma step553_11_two_steps (u v w z : Bool) :
    step553 (step553 true (v && w) (u && z) (z && w) (u && v))
      (v && w) (u && z) (z && w) (u && v) = true := by
  cases u <;> cases v <;> cases w <;> cases z <;> rfl

private lemma step553_11_step1_of_edge (u v w z : Bool)
    (h : (v && w) = true ∨ (u && z) = true ∨ (z && w) = true ∨ (u && v) = true) :
    step553 true (v && w) (u && z) (z && w) (u && v) = true := by
  cases u <;> cases v <;> cases w <;> cases z <;> simp_all [step553] <;> rfl

private lemma step553_00_two_steps (c n1 n2 n3 n4 : Bool) :
    step553 (step553 c (c && n1) (c && n2) (c && n3) (c && n4))
      (c && n1) (c && n2) (c && n3) (c && n4) =
      uwStep c n1 n2 n3 n4 := by
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> rfl

private lemma step553_00_true_step1 (n1 n2 n3 n4 : Bool)
    (h : n1 = true ∨ n2 = true ∨ n3 = true ∨ n4 = true) :
    step553 true (true && n1) (true && n2) (true && n3) (true && n4) =
      uwStep true n1 n2 n3 n4 := by
  cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> simp_all [step553, uwStep] <;> rfl

private lemma step553_false_of_neighbor (n1 n2 n3 n4 : Bool)
    (h : n1 = true ∨ n2 = true ∨ n3 = true ∨ n4 = true) :
    step553 false n1 n2 n3 n4 = false := by
  cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> simp_all [step553] <;> rfl

private lemma step553_edge_true_step2 (x' y' : Bool) (h : x' = true ∨ y' = true) :
    step553 true true true x' y' = (x' && y') := by
  cases x' <;> cases y' <;> simp_all [step553] <;> rfl

private lemma step553_edge_true_step2' (x' y' : Bool) (h : x' = true ∨ y' = true) :
    step553 true x' y' true true = (x' && y') := by
  cases x' <;> cases y' <;> simp_all [step553] <;> rfl

private lemma cell_zero_eq (i j : ℤ) : cell 553 0 i j = decide (i = 0 ∧ j = 0) :=
  rfl

private lemma cell_one_eq (i j : ℤ) : cell 553 1 i j = decide (1 < |i| + |j|) := by
  rw [cell_succ]
  have habs_i : |i| = i ∨ |i| = -i := abs_choice i
  have habs_j : |j| = j ∨ |j| = -j := abs_choice j
  have hi_nn : 0 ≤ |i| := abs_nonneg i
  have hj_nn : 0 ≤ |j| := abs_nonneg j
  by_cases h : 1 < |i| + |j|
  · have h0 : cell 553 0 i j = false := by
      simp only [cell_zero_eq, decide_eq_false_iff_not]; omega
    have h1 : cell 553 0 (i + 1) j = false := by
      simp only [cell_zero_eq, decide_eq_false_iff_not]; omega
    have h2 : cell 553 0 (i - 1) j = false := by
      simp only [cell_zero_eq, decide_eq_false_iff_not]; omega
    have h3 : cell 553 0 i (j + 1) = false := by
      simp only [cell_zero_eq, decide_eq_false_iff_not]; omega
    have h4 : cell 553 0 i (j - 1) = false := by
      simp only [cell_zero_eq, decide_eq_false_iff_not]; omega
    rw [h0, h1, h2, h3, h4, decide_eq_true h]
    rfl
  · have hle : |i| + |j| ≤ 1 := by omega
    rw [decide_eq_false h]
    have hcases : (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨
        (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

private lemma cell_outside : ∀ t : ℕ, 1 ≤ t → ∀ i j : ℤ, (t : ℤ) < |i| + |j| →
    cell 553 t i j = true
  | 0, ht => by omega
  | 1, _ => fun i j h => by
    rw [cell_one_eq, decide_eq_true_iff]
    exact h
  | t + 2, _ => fun i j h => by
    have ih := cell_outside (t + 1) (by omega)
    have htriP : ∀ x : ℤ, |x| ≤ |x + 1| + 1 := fun x => by
      have := abs_add_le (x + 1) (-1)
      simpa [show x + 1 + (-1) = x by ring] using this
    have htriM : ∀ x : ℤ, |x| ≤ |x - 1| + 1 := fun x => by
      have := abs_add_le (x - 1) 1
      simpa [show x - 1 + 1 = x by ring] using this
    rw [cell_succ]
    rw [ih i j (by push_cast at h ⊢; linarith),
      ih (i + 1) j (by push_cast at h ⊢; linarith [htriP i]),
      ih (i - 1) j (by push_cast at h ⊢; linarith [htriM i]),
      ih i (j + 1) (by push_cast at h ⊢; linarith [htriP j]),
      ih i (j - 1) (by push_cast at h ⊢; linarith [htriM j])]
    rfl

private def f (m : ℕ) (a b : ℤ) : Bool :=
  cell 553 (2 * m + 1) (2 * a) (2 * b)

private structure Inv (m : ℕ) : Prop where
  h11 : ∀ a b : ℤ, cell 553 (2 * m + 1) (2 * a + 1) (2 * b + 1) = true
  h01 : ∀ a b : ℤ, cell 553 (2 * m + 1) (2 * a) (2 * b + 1) = (f m a b && f m a (b + 1))
  h10 : ∀ a b : ℤ, cell 553 (2 * m + 1) (2 * a + 1) (2 * b) = (f m a b && f m (a + 1) b)
  hpar : ∀ a b : ℤ, f m a b = true → (a + b) % 2 = (m : ℤ) % 2 →
    (f m (a + 1) b).toNat + (f m (a - 1) b).toNat +
      (f m a (b + 1)).toNat + (f m a (b - 1)).toNat ≠ 3

private lemma inv_zero : Inv 0 where
  h11 a b := by
    change cell 553 1 (2 * a + 1) (2 * b + 1) = true
    rw [cell_one_eq, decide_eq_true_iff]
    have h1 : 1 ≤ |2 * a + 1| := Int.one_le_abs (by omega)
    have h2 : 1 ≤ |2 * b + 1| := Int.one_le_abs (by omega)
    linarith
  h01 a b := by
    change cell 553 1 (2 * a) (2 * b + 1) = (cell 553 1 (2 * a) (2 * b) && cell 553 1 (2 * a) (2 * (b + 1)))
    simp only [cell_one_eq]
    by_cases ha : a = 0
    · subst ha
      by_cases hb0 : b = 0
      · subst hb0; rfl
      · by_cases hb1 : b = -1
        · subst hb1; rfl
        · have h2b : 2 ≤ |2 * b| := by
            have := Int.one_le_abs hb0; rw [abs_mul]; norm_num; linarith
          have h2b1 : 2 ≤ |2 * (b + 1)| := by
            have := Int.one_le_abs (by omega : b + 1 ≠ 0); rw [abs_mul]; norm_num; linarith
          have hodd : 2 ≤ |2 * b + 1| := by
            by_cases hpos : 0 < b
            · rw [abs_of_nonneg (by omega)]; omega
            · rw [abs_of_nonpos (by omega)]; omega
          have e1 : 1 < |2 * (0 : ℤ)| + |2 * b + 1| := by linarith [abs_nonneg (2 * (0 : ℤ))]
          have e2 : 1 < |2 * (0 : ℤ)| + |2 * b| := by linarith [abs_nonneg (2 * (0 : ℤ))]
          have e3 : 1 < |2 * (0 : ℤ)| + |2 * (b + 1)| := by linarith [abs_nonneg (2 * (0 : ℤ))]
          rw [decide_eq_true e1, decide_eq_true e2, decide_eq_true e3]; rfl
    · have h2a : 2 ≤ |2 * a| := by
        have := Int.one_le_abs ha; rw [abs_mul]; norm_num; linarith
      have e1 : 1 < |2 * a| + |2 * b + 1| := by linarith [abs_nonneg (2 * b + 1)]
      have e2 : 1 < |2 * a| + |2 * b| := by linarith [abs_nonneg (2 * b)]
      have e3 : 1 < |2 * a| + |2 * (b + 1)| := by linarith [abs_nonneg (2 * (b + 1))]
      rw [decide_eq_true e1, decide_eq_true e2, decide_eq_true e3]; rfl
  h10 a b := by
    change cell 553 1 (2 * a + 1) (2 * b) = (cell 553 1 (2 * a) (2 * b) && cell 553 1 (2 * (a + 1)) (2 * b))
    simp only [cell_one_eq]
    by_cases hb : b = 0
    · subst hb
      by_cases ha0 : a = 0
      · subst ha0; rfl
      · by_cases ha1 : a = -1
        · subst ha1; rfl
        · have h2a : 2 ≤ |2 * a| := by
            have := Int.one_le_abs ha0; rw [abs_mul]; norm_num; linarith
          have h2a1 : 2 ≤ |2 * (a + 1)| := by
            have := Int.one_le_abs (by omega : a + 1 ≠ 0); rw [abs_mul]; norm_num; linarith
          have hodd : 2 ≤ |2 * a + 1| := by
            by_cases hpos : 0 < a
            · rw [abs_of_nonneg (by omega)]; omega
            · rw [abs_of_nonpos (by omega)]; omega
          have e1 : 1 < |2 * a + 1| + |2 * (0 : ℤ)| := by linarith [abs_nonneg (2 * (0 : ℤ))]
          have e2 : 1 < |2 * a| + |2 * (0 : ℤ)| := by linarith [abs_nonneg (2 * (0 : ℤ))]
          have e3 : 1 < |2 * (a + 1)| + |2 * (0 : ℤ)| := by linarith [abs_nonneg (2 * (0 : ℤ))]
          rw [decide_eq_true e1, decide_eq_true e2, decide_eq_true e3]; rfl
    · have h2b : 2 ≤ |2 * b| := by
        have := Int.one_le_abs hb; rw [abs_mul]; norm_num; linarith
      have e1 : 1 < |2 * a + 1| + |2 * b| := by linarith [abs_nonneg (2 * a + 1)]
      have e2 : 1 < |2 * a| + |2 * b| := by linarith [abs_nonneg (2 * a)]
      have e3 : 1 < |2 * (a + 1)| + |2 * b| := by linarith [abs_nonneg (2 * (a + 1))]
      rw [decide_eq_true e1, decide_eq_true e2, decide_eq_true e3]; rfl
  hpar a b _ hmod := by
    have haux : ∀ x y : ℤ, (x + y) % 2 ≠ 0 → 1 < |2 * x| + |2 * y| := by
      intro x y hne
      have hxy : x ≠ 0 ∨ y ≠ 0 := by omega
      rcases hxy with hx | hy
      · have : 1 ≤ |x| := Int.one_le_abs hx
        have h2x : |2 * x| = 2 * |x| := by rw [abs_mul]; norm_num
        linarith [abs_nonneg (2 * y)]
      · have : 1 ≤ |y| := Int.one_le_abs hy
        have h2y : |2 * y| = 2 * |y| := by rw [abs_mul]; norm_num
        linarith [abs_nonneg (2 * x)]
    have h1 : f 0 (a + 1) b = true := by
      change cell 553 1 (2 * (a + 1)) (2 * b) = true
      rw [cell_one_eq, decide_eq_true_iff]; exact haux _ _ (by omega)
    have h2 : f 0 (a - 1) b = true := by
      change cell 553 1 (2 * (a - 1)) (2 * b) = true
      rw [cell_one_eq, decide_eq_true_iff]; exact haux _ _ (by omega)
    have h3 : f 0 a (b + 1) = true := by
      change cell 553 1 (2 * a) (2 * (b + 1)) = true
      rw [cell_one_eq, decide_eq_true_iff]; exact haux _ _ (by omega)
    have h4 : f 0 a (b - 1) = true := by
      change cell 553 1 (2 * a) (2 * (b - 1)) = true
      rw [cell_one_eq, decide_eq_true_iff]; exact haux _ _ (by omega)
    rw [h1, h2, h3, h4]
    decide

private lemma even_01 {m : ℕ} (hm : Inv m) (a b : ℤ) :
    cell 553 (2 * m + 2) (2 * a) (2 * b + 1) = (f m a b && f m a (b + 1)) := by
  have ht : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [ht, cell_succ]
  have hn1 : 2 * a + 1 = 2 * a + 1 := rfl
  have hn2 : 2 * a - 1 = 2 * (a - 1) + 1 := by omega
  have hn3 : 2 * b + 1 + 1 = 2 * (b + 1) := by omega
  have hn4 : 2 * b + 1 - 1 = 2 * b := by omega
  rw [hm.h01 a b, hm.h11 a b, hn2, hm.h11 (a - 1) b, hn3, hn4]
  simpa [f, Bool.and_comm] using step553_01_step1 (f m a (b + 1)) (f m a b)

private lemma even_10 {m : ℕ} (hm : Inv m) (a b : ℤ) :
    cell 553 (2 * m + 2) (2 * a + 1) (2 * b) = (f m a b && f m (a + 1) b) := by
  have ht : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [ht, cell_succ]
  have hn1 : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
  have hn2 : 2 * a + 1 - 1 = 2 * a := by omega
  have hn3 : 2 * b + 1 = 2 * b + 1 := rfl
  have hn4 : 2 * b - 1 = 2 * (b - 1) + 1 := by omega
  rw [hm.h10 a b, hn1, hn2, hm.h11 a b, hn4, hm.h11 a (b - 1)]
  simpa [f, Bool.and_comm] using step553_10_step1 (f m (a + 1) b) (f m a b)

private lemma even_11_expr {m : ℕ} (hm : Inv m) (a b : ℤ) :
    cell 553 (2 * m + 2) (2 * a + 1) (2 * b + 1) =
      step553 true
        (f m (a + 1) b && f m (a + 1) (b + 1))
        (f m a b && f m a (b + 1))
        (f m a (b + 1) && f m (a + 1) (b + 1))
        (f m a b && f m (a + 1) b) := by
  have ht : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [ht, cell_succ]
  have hn1 : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
  have hn2 : 2 * a + 1 - 1 = 2 * a := by omega
  have hn3 : 2 * b + 1 + 1 = 2 * (b + 1) := by omega
  have hn4 : 2 * b + 1 - 1 = 2 * b := by omega
  rw [hm.h11 a b, hn1, hm.h01 (a + 1) b, hn2, hm.h01 a b, hn3, hm.h10 a (b + 1), hn4, hm.h10 a b]

private lemma even_00_expr {m : ℕ} (hm : Inv m) (a b : ℤ) :
    cell 553 (2 * m + 2) (2 * a) (2 * b) =
      step553 (f m a b)
        (f m a b && f m (a + 1) b)
        (f m a b && f m (a - 1) b)
        (f m a b && f m a (b + 1))
        (f m a b && f m a (b - 1)) := by
  have ht : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [ht, cell_succ]
  have hn1 : 2 * a - 1 = 2 * (a - 1) + 1 := by omega
  have hn2 : 2 * b - 1 = 2 * (b - 1) + 1 := by omega
  have ha1 : a - 1 + 1 = a := by omega
  have hb1 : b - 1 + 1 = b := by omega
  rw [hm.h10 a b, hn1, hm.h10 (a - 1) b, ha1, hm.h01 a b, hn2, hm.h01 a (b - 1), hb1]
  simp only [f, Bool.and_comm]

private lemma f_succ_of_inv {m : ℕ} (hm : Inv m) (a b : ℤ) :
    f (m + 1) a b =
      uwStep (f m a b) (f m (a + 1) b) (f m (a - 1) b) (f m a (b + 1)) (f m a (b - 1)) := by
  change cell 553 (2 * (m + 1) + 1) (2 * a) (2 * b) = _
  have ht : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
  rw [ht, cell_succ, even_00_expr hm a b]
  have hn1 : 2 * a - 1 = 2 * (a - 1) + 1 := by omega
  have hn2 : 2 * b - 1 = 2 * (b - 1) + 1 := by omega
  have ha1 : a - 1 + 1 = a := by omega
  have hb1 : b - 1 + 1 = b := by omega
  rw [even_10 hm a b, hn1, even_10 hm (a - 1) b, ha1, even_01 hm a b, hn2, even_01 hm a (b - 1), hb1]
  have hc1 : (f m (a - 1) b && f m a b) = (f m a b && f m (a - 1) b) := Bool.and_comm _ _
  have hc2 : (f m a (b - 1) && f m a b) = (f m a b && f m a (b - 1)) := Bool.and_comm _ _
  rw [hc1, hc2]
  exact step553_00_two_steps (f m a b) (f m (a + 1) b) (f m (a - 1) b) (f m a (b + 1)) (f m a (b - 1))

private lemma f_succ_eq_true_of_par {m : ℕ} (hm : Inv m) {a b : ℤ}
    (h1 : f m a b = true) (hmod : (a + b) % 2 = (m : ℤ) % 2) :
    f (m + 1) a b = true := by
  rw [f_succ_of_inv hm, uwStep, h1]
  simp [hm.hpar a b h1 hmod]

private lemma inv_succ {m : ℕ} (hm : Inv m) : Inv (m + 1) where
  h11 a b := by
    have ht : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
    rw [ht, cell_succ, even_11_expr hm a b]
    have hn1 : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
    have hn2 : 2 * a + 1 - 1 = 2 * a := by omega
    have hn3 : 2 * b + 1 + 1 = 2 * (b + 1) := by omega
    have hn4 : 2 * b + 1 - 1 = 2 * b := by omega
    rw [hn1, even_01 hm (a + 1) b, hn2, even_01 hm a b, hn3, even_10 hm a (b + 1), hn4, even_10 hm a b]
    exact step553_11_two_steps (f m a b) (f m (a + 1) b) (f m (a + 1) (b + 1)) (f m a (b + 1))
  h01 a b := by
    have ht : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
    rw [ht, cell_succ, even_01 hm a b]
    have hn2 : 2 * a - 1 = 2 * (a - 1) + 1 := by omega
    have hn3 : 2 * b + 1 + 1 = 2 * (b + 1) := by omega
    have hn4 : 2 * b + 1 - 1 = 2 * b := by omega
    rw [hn2, hn3, hn4]
    cases hfa : f m a b <;> cases hfb : f m a (b + 1)
    · have hfe : cell 553 (2 * m + 2) (2 * a) (2 * b) = true := by
        rw [even_00_expr hm a b, hfa]; simp only [Bool.false_and]; rfl
      have hf1 : f (m + 1) a b = false := by
        rw [f_succ_of_inv hm, uwStep, hfa]; rfl
      rw [hf1]; simp only [Bool.false_and]
      exact step553_false_of_neighbor _ _ _ _ (Or.inr (Or.inr (Or.inr hfe)))
    · have hfe : cell 553 (2 * m + 2) (2 * a) (2 * b) = true := by
        rw [even_00_expr hm a b, hfa]; simp only [Bool.false_and]; rfl
      have hf1 : f (m + 1) a b = false := by
        rw [f_succ_of_inv hm, uwStep, hfa]; rfl
      rw [hf1]; simp only [Bool.false_and]
      exact step553_false_of_neighbor _ _ _ _ (Or.inr (Or.inr (Or.inr hfe)))
    · have hfe : cell 553 (2 * m + 2) (2 * a) (2 * (b + 1)) = true := by
        rw [even_00_expr hm a (b + 1), hfb]; simp only [Bool.false_and]; rfl
      have hf2 : f (m + 1) a (b + 1) = false := by
        rw [f_succ_of_inv hm, uwStep, hfb]; rfl
      rw [hf2]; simp only [Bool.and_false]
      exact step553_false_of_neighbor _ _ _ _ (Or.inr (Or.inr (Or.inl hfe)))
    · simp only [Bool.true_and]
      have h11R : cell 553 (2 * m + 2) (2 * a + 1) (2 * b + 1) = true := by
        rw [even_11_expr hm a b]
        apply step553_11_step1_of_edge
        right; left; simp [hfa, hfb]
      have h11L : cell 553 (2 * m + 2) (2 * (a - 1) + 1) (2 * b + 1) = true := by
        rw [even_11_expr hm (a - 1) b]
        apply step553_11_step1_of_edge
        left
        have ha1 : a - 1 + 1 = a := by omega
        rw [ha1, hfa, hfb]
        rfl
      have h00B : cell 553 (2 * m + 2) (2 * a) (2 * b) = f (m + 1) a b := by
        rw [even_00_expr hm a b, f_succ_of_inv hm a b, hfa]
        exact step553_00_true_step1 _ _ _ _ (Or.inr (Or.inr (Or.inl hfb)))
      have h00T : cell 553 (2 * m + 2) (2 * a) (2 * (b + 1)) = f (m + 1) a (b + 1) := by
        rw [even_00_expr hm a (b + 1), f_succ_of_inv hm a (b + 1), hfb]
        have hb1 : b + 1 - 1 = b := by omega
        rw [hb1]
        exact step553_00_true_step1 _ _ _ _ (Or.inr (Or.inr (Or.inr hfa)))
      rw [h11R, h11L, h00T, h00B]
      have hor : f (m + 1) a (b + 1) = true ∨ f (m + 1) a b = true := by
        by_cases hmod : (a + b) % 2 = (m : ℤ) % 2
        · exact Or.inr (f_succ_eq_true_of_par hm hfa hmod)
        · have hmod' : (a + (b + 1)) % 2 = (m : ℤ) % 2 := by omega
          exact Or.inl (f_succ_eq_true_of_par hm hfb hmod')
      rw [step553_edge_true_step2 _ _ hor, Bool.and_comm]
  h10 a b := by
    have ht : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
    rw [ht, cell_succ, even_10 hm a b]
    have hn1 : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
    have hn2 : 2 * a + 1 - 1 = 2 * a := by omega
    have hn4 : 2 * b - 1 = 2 * (b - 1) + 1 := by omega
    rw [hn1, hn2, hn4]
    cases hfa : f m a b <;> cases hfb : f m (a + 1) b
    · have hfe : cell 553 (2 * m + 2) (2 * a) (2 * b) = true := by
        rw [even_00_expr hm a b, hfa]; simp only [Bool.false_and]; rfl
      have hf1 : f (m + 1) a b = false := by
        rw [f_succ_of_inv hm, uwStep, hfa]; rfl
      rw [hf1]; simp only [Bool.false_and]
      exact step553_false_of_neighbor _ _ _ _ (Or.inr (Or.inl hfe))
    · have hfe : cell 553 (2 * m + 2) (2 * a) (2 * b) = true := by
        rw [even_00_expr hm a b, hfa]; simp only [Bool.false_and]; rfl
      have hf1 : f (m + 1) a b = false := by
        rw [f_succ_of_inv hm, uwStep, hfa]; rfl
      rw [hf1]; simp only [Bool.false_and]
      exact step553_false_of_neighbor _ _ _ _ (Or.inr (Or.inl hfe))
    · have hfe : cell 553 (2 * m + 2) (2 * (a + 1)) (2 * b) = true := by
        rw [even_00_expr hm (a + 1) b, hfb]; simp only [Bool.false_and]; rfl
      have hf2 : f (m + 1) (a + 1) b = false := by
        rw [f_succ_of_inv hm, uwStep, hfb]; rfl
      rw [hf2]; simp only [Bool.and_false]
      exact step553_false_of_neighbor _ _ _ _ (Or.inl hfe)
    · simp only [Bool.true_and]
      have h11T : cell 553 (2 * m + 2) (2 * a + 1) (2 * b + 1) = true := by
        rw [even_11_expr hm a b]
        apply step553_11_step1_of_edge
        right; right; right; simp [hfa, hfb]
      have h11B : cell 553 (2 * m + 2) (2 * a + 1) (2 * (b - 1) + 1) = true := by
        rw [even_11_expr hm a (b - 1)]
        apply step553_11_step1_of_edge
        right; right; left
        have hb1 : b - 1 + 1 = b := by omega
        rw [hb1, hfa, hfb]
        rfl
      have h00L : cell 553 (2 * m + 2) (2 * a) (2 * b) = f (m + 1) a b := by
        rw [even_00_expr hm a b, f_succ_of_inv hm a b, hfa]
        exact step553_00_true_step1 _ _ _ _ (Or.inl hfb)
      have h00R : cell 553 (2 * m + 2) (2 * (a + 1)) (2 * b) = f (m + 1) (a + 1) b := by
        rw [even_00_expr hm (a + 1) b, f_succ_of_inv hm (a + 1) b, hfb]
        have ha1 : a + 1 - 1 = a := by omega
        rw [ha1]
        exact step553_00_true_step1 _ _ _ _ (Or.inr (Or.inl hfa))
      rw [h00R, h00L, h11T, h11B]
      have hor : f (m + 1) (a + 1) b = true ∨ f (m + 1) a b = true := by
        by_cases hmod : (a + b) % 2 = (m : ℤ) % 2
        · exact Or.inr (f_succ_eq_true_of_par hm hfa hmod)
        · have hmod' : (a + 1 + b) % 2 = (m : ℤ) % 2 := by omega
          exact Or.inl (f_succ_eq_true_of_par hm hfb hmod')
      rw [step553_edge_true_step2' _ _ hor, Bool.and_comm]
  hpar a b hf1 hmod := by
    have hsucc : f (m + 1) a b =
        uwStep (f m a b) (f m (a + 1) b) (f m (a - 1) b) (f m a (b + 1)) (f m a (b - 1)) :=
      f_succ_of_inv hm a b
    have hfm : f m a b = true ∧
        (f m (a + 1) b).toNat + (f m (a - 1) b).toNat +
          (f m a (b + 1)).toNat + (f m a (b - 1)).toNat ≠ 3 := by
      rw [hsucc, uwStep] at hf1
      simpa using hf1
    have hsame : ∀ a' b' : ℤ, (a' + b') % 2 = (m : ℤ) % 2 → f (m + 1) a' b' = f m a' b' := by
      intro a' b' hmod'
      cases h : f m a' b'
      · rw [f_succ_of_inv hm, uwStep, h]; rfl
      · exact f_succ_eq_true_of_par hm h hmod'
    rw [hsame (a + 1) b (by omega), hsame (a - 1) b (by omega),
      hsame a (b + 1) (by omega), hsame a (b - 1) (by omega)]
    exact hfm.2

private lemma inv_all (m : ℕ) : Inv m := by
  induction m with
  | zero => exact inv_zero
  | succ m ih => exact inv_succ ih

private lemma f_axis : ∀ (m : ℕ) (a : ℤ), f m a 0 = decide ((m : ℤ) < |a|)
  | 0, a => by
    change cell 553 1 (2 * a) 0 = decide (0 < |a|)
    rw [cell_one_eq]
    have h2a : |2 * a| = 2 * |a| := by rw [abs_mul]; norm_num
    by_cases h : 0 < |a|
    · rw [decide_eq_true h, decide_eq_true (by rw [h2a, abs_zero]; omega)]
    · rw [decide_eq_false h, decide_eq_false (by rw [h2a, abs_zero]; omega)]
  | m + 1, a => by
    have h2a : |2 * a| = 2 * |a| := by rw [abs_mul]; norm_num
    by_cases hgt : ((m + 1 : ℕ) : ℤ) < |a|
    · rw [decide_eq_true hgt]
      exact cell_outside (2 * (m + 1) + 1) (by omega) (2 * a) 0 (by rw [h2a, abs_zero]; omega)
    · rw [decide_eq_false hgt, f_succ_of_inv (inv_all m) a 0]
      by_cases hle : |a| ≤ (m : ℤ)
      · have h0 : f m a 0 = false := by rw [f_axis m a, decide_eq_false (by omega)]
        rw [h0]; rfl
      · have heq : |a| = (m : ℤ) + 1 := by omega
        have hself : f m a 0 = true := by rw [f_axis m a, decide_eq_true (by omega)]
        have hup : f m a 1 = true := by
          simpa [f] using cell_outside (2 * m + 1) (by omega) (2 * a) 2
            (by rw [h2a, show |(2 : ℤ)| = 2 by norm_num]; omega)
        have hdn : f m a (-1) = true := by
          simpa [f] using cell_outside (2 * m + 1) (by omega) (2 * a) (-2)
            (by rw [h2a, show |(-2 : ℤ)| = 2 by norm_num]; omega)
        rcases eq_or_eq_neg_of_abs_eq heq with rfl | rfl
        · have hR : f m ((m : ℤ) + 1 + 1) 0 = true := by
            rw [f_axis m, abs_of_nonneg (by omega), decide_eq_true (by omega)]
          have hL : f m ((m : ℤ) + 1 - 1) 0 = false := by
            rw [f_axis m, abs_of_nonneg (by omega), decide_eq_false (by omega)]
          simp only [zero_add, zero_sub]
          rw [hself, hR, hL, hup, hdn]; rfl
        · have hR : f m (-((m : ℤ) + 1) + 1) 0 = false := by
            rw [f_axis m, abs_of_nonpos (by omega), decide_eq_false (by omega)]
          have hL : f m (-((m : ℤ) + 1) - 1) 0 = true := by
            rw [f_axis m, abs_of_nonpos (by omega), decide_eq_true (by omega)]
          simp only [zero_add, zero_sub]
          rw [hself, hR, hL, hup, hdn]; rfl

private lemma cell_odd_axis (m : ℕ) (k : ℕ) (hk : k ≤ 2 * m + 1) :
    cell 553 (2 * m + 1) k 0 = false := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hcast : ((j + j : ℕ) : ℤ) = 2 * (j : ℤ) := by omega
    rw [hcast]
    change f m j 0 = false
    rw [f_axis m j, abs_of_nonneg (Int.natCast_nonneg j), decide_eq_false (by omega)]
  · have hcast : ((2 * j + 1 : ℕ) : ℤ) = 2 * (j : ℤ) + 1 := by omega
    rw [hcast, show (0 : ℤ) = 2 * 0 by ring, (inv_all m).h10 j 0, f_axis m j,
      abs_of_nonneg (Int.natCast_nonneg j), decide_eq_false (by omega)]
    rfl

private lemma cell_even_axis (m : ℕ) (k : ℕ) (hk : k ≤ 2 * m + 2) :
    cell 553 (2 * m + 2) k 0 = decide (Even k ∧ k ≤ 2 * m) := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hcast : ((j + j : ℕ) : ℤ) = 2 * (j : ℤ) := by omega
    rw [hcast, show (0 : ℤ) = 2 * 0 by ring, even_00_expr (inv_all m) j 0]
    by_cases hj : j ≤ m
    · have h0 : f m j 0 = false := by
        rw [f_axis m j, abs_of_nonneg (Int.natCast_nonneg j), decide_eq_false (by omega)]
      rw [h0, decide_eq_true ⟨⟨j, rfl⟩, by omega⟩]
      simp only [Bool.false_and]
      rfl
    · have hjeq : j = m + 1 := by omega
      subst hjeq
      have hself : f m (m + 1 : ℕ) 0 = true := by
        rw [f_axis m, abs_of_nonneg (Int.natCast_nonneg _), decide_eq_true (by omega)]
      have hR : f m ((m + 1 : ℕ) + 1) 0 = true := by
        rw [f_axis m, abs_of_nonneg (by omega), decide_eq_true (by omega)]
      have hL : f m ((m + 1 : ℕ) - 1) 0 = false := by
        rw [f_axis m, abs_of_nonneg (by omega), decide_eq_false (by omega)]
      have hup : f m (m + 1 : ℕ) 1 = true := by
        simpa [f] using cell_outside (2 * m + 1) (by omega) (2 * (m + 1 : ℕ)) 2 (by
          rw [abs_of_nonneg (by omega), show |(2 : ℤ)| = 2 by norm_num]; omega)
      have hdn : f m (m + 1 : ℕ) (-1) = true := by
        simpa [f] using cell_outside (2 * m + 1) (by omega) (2 * (m + 1 : ℕ)) (-2) (by
          rw [abs_of_nonneg (by omega), show |(-2 : ℤ)| = 2 by norm_num]; omega)
      simp only [zero_add, zero_sub]
      rw [hself, hR, hL, hup, hdn, decide_eq_false (by omega)]
      rfl
  · have hcast : ((2 * j + 1 : ℕ) : ℤ) = 2 * (j : ℤ) + 1 := by omega
    rw [hcast, show (0 : ℤ) = 2 * 0 by ring, even_10 (inv_all m) j 0, f_axis m j,
      abs_of_nonneg (Int.natCast_nonneg j), decide_eq_false (by omega)]
    have hodd : ¬ Even (2 * j + 1) := by
      rintro ⟨r, hr⟩; omega
    rw [decide_eq_false (fun h => hodd h.1)]
    rfl

private lemma a_odd_int (m : ℕ) : a (2 * m + 1) = 0 := by
  unfold a
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  rw [cell_odd_axis m k (by omega)]
  rfl

private lemma a_odd (n : ℕ) (hn : Odd n) : (a n : ℚ) = 0 := by
  rcases hn with ⟨m, rfl⟩
  rw [a_odd_int m]
  simp

private lemma a_zero_int : a 0 = 1 := by
  unfold a
  simp [cell_zero_eq]

private lemma a_two_int : a 2 = 100 := by
  unfold a
  have h0 : cell 553 2 0 0 = true := by
    simpa using cell_even_axis 0 0 (by omega)
  have h1 : cell 553 2 1 0 = false := by
    simpa using cell_even_axis 0 1 (by omega)
  have h2 : cell 553 2 2 0 = false := by
    simpa using cell_even_axis 0 2 (by omega)
  simp [Finset.sum_range_succ, h0, h1, h2]

private lemma a_even_step_int (m : ℕ) : a (2 * m + 4) = 100 * a (2 * m + 2) + 100 := by
  unfold a
  have h2m4 : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
  have hsplit : 2 * m + 4 + 1 = (2 * m + 2 + 1) + 2 := by omega
  rw [hsplit, Finset.sum_range_succ _ (2 * m + 2 + 1 + 1), Finset.sum_range_succ _ (2 * m + 2 + 1)]
  have hlast1 : cell 553 (2 * m + 4) (↑(2 * m + 2 + 1 + 1) : ℤ) 0 = false := by
    have h := cell_even_axis (m + 1) (2 * m + 2 + 1 + 1) (by omega)
    rw [h2m4] at h
    rw [h, decide_eq_false (by omega)]
  have hlast2 : cell 553 (2 * m + 4) (↑(2 * m + 2 + 1) : ℤ) 0 = false := by
    have h := cell_even_axis (m + 1) (2 * m + 2 + 1) (by omega)
    rw [h2m4] at h
    rw [h, decide_eq_false (by omega)]
  rw [hlast1, hlast2]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [Finset.sum_range_succ _ (2 * m + 2), Finset.sum_range_succ _ (2 * m + 2)]
  have hpen1 : cell 553 (2 * m + 4) (↑(2 * m + 2) : ℤ) 0 = true := by
    have h := cell_even_axis (m + 1) (2 * m + 2) (by omega)
    rw [h2m4] at h
    rw [h, decide_eq_true ⟨⟨m + 1, by omega⟩, by omega⟩]
  have hpen2 : cell 553 (2 * m + 2) (↑(2 * m + 2) : ℤ) 0 = false := by
    rw [cell_even_axis m (2 * m + 2) (by omega), decide_eq_false (by omega)]
  rw [hpen1, hpen2]
  simp only [↓reduceIte, Bool.false_eq_true, add_zero]
  have hpow2 : (10 : ℤ) ^ (2 * m + 4 - (2 * m + 2)) = 100 := by
    have : 2 * m + 4 - (2 * m + 2) = 2 := by omega
    rw [this]; norm_num
  rw [hpow2]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hc1 : cell 553 (2 * m + 4) k 0 = decide (Even k ∧ k ≤ 2 * m + 2) := by
    have h := cell_even_axis (m + 1) k (by omega)
    rw [h2m4] at h
    simpa [show 2 * (m + 1) = 2 * m + 2 by ring] using h
  have hc2 : cell 553 (2 * m + 2) k 0 = decide (Even k ∧ k ≤ 2 * m) :=
    cell_even_axis m k (by omega)
  have hceq : cell 553 (2 * m + 4) k 0 = cell 553 (2 * m + 2) k 0 := by
    rw [hc1, hc2]
    by_cases he : Even k
    · by_cases hle : k ≤ 2 * m
      · simp [he, hle, (by omega : k ≤ 2 * m + 2)]
      · have : k = 2 * m + 1 := by omega
        subst this
        exfalso; rcases he with ⟨r, hr⟩; omega
    · simp [he]
  rw [hceq]
  cases cell 553 (2 * m + 2) k 0
  · simp
  · simp only [↓reduceIte]
    have hexp : 2 * m + 4 - k = (2 * m + 2 - k) + 2 := by omega
    rw [hexp, pow_add]
    ring

private lemma a_even_closed_aux (m : ℕ) :
    (a (2 * m + 2) : ℚ) = 100 * ((10 : ℚ) ^ (2 * m + 2) - 1) / 99 := by
  induction m with
  | zero =>
    rw [show 2 * 0 + 2 = 2 by rfl, a_two_int]
    norm_num
  | succ m ih =>
    have hstep : (a (2 * m + 4) : ℚ) = 100 * (a (2 * m + 2) : ℚ) + 100 := by
      exact_mod_cast a_even_step_int m
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 by omega, hstep, ih]
    rw [show 2 * m + 4 = (2 * m + 2) + 2 by omega, pow_add]
    ring

private lemma a_even (n : ℕ) (hn1 : 1 ≤ n) (he : Even n) :
    (a n : ℚ) = 100 * ((10 : ℚ) ^ n - 1) / 99 := by
  rcases he with ⟨k, rfl⟩
  cases k with
  | zero => omega
  | succ m =>
    rw [show (m + 1) + (m + 1) = 2 * m + 2 by omega]
    exact a_even_closed_aux m

private lemma a_rec (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 3 ≤ k := by omega
    have h1 : k + k - 2 = 2 * (k - 1) := by omega
    have h2 : k + k - 4 = 2 * (k - 2) := by omega
    rw [a_even (k + k) (by omega) ⟨k, rfl⟩,
      a_even (k + k - 2) (by omega) ⟨k - 1, by omega⟩,
      a_even (k + k - 4) (by omega) ⟨k - 2, by omega⟩]
    set r : ℕ := k + k - 4 with hr
    have he2 : k + k - 2 = r + 2 := by omega
    have he1 : k + k = r + 4 := by omega
    rw [he2, he1, pow_add (10 : ℚ) r 4, pow_add (10 : ℚ) r 2]
    ring
  · have h1 : Odd (2 * k + 1) := ⟨k, rfl⟩
    have h2 : Odd (2 * k + 1 - 2) := ⟨k - 1, by omega⟩
    have h3 : Odd (2 * k + 1 - 4) := ⟨k - 2, by omega⟩
    rw [a_odd _ h1, a_odd _ h2, a_odd _ h3]
    ring

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      1 - X ^ 2 + 100 * X ^ 4 := by
  set P : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hfac : ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      1 - 101 * X ^ 2 + 100 * X ^ 4 := by ring
  rw [hfac]
  have hexp : P * (1 - 101 * X ^ 2 + 100 * X ^ 4) =
      P - C (101 : ℚ) * (P * X ^ 2) + C (100 : ℚ) * (P * X ^ 4) := by
    have h101 : C (101 : ℚ) = (101 : PowerSeries ℚ) := map_ofNat C 101
    have h100 : C (100 : ℚ) = (100 : PowerSeries ℚ) := map_ofNat C 100
    rw [h101, h100]; ring
  rw [hexp]
  have hrhs : (1 - X ^ 2 + 100 * X ^ 4 : PowerSeries ℚ) =
      1 - X ^ 2 + C (100 : ℚ) * X ^ 4 := by
    have h100 : C (100 : ℚ) = (100 : PowerSeries ℚ) := map_ofNat C 100
    rw [h100]
  rw [hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow, PowerSeries.coeff_C, PowerSeries.coeff_mk, P]
  have ha0 : (a 0 : ℚ) = 1 := by exact_mod_cast a_zero_int
  have ha1 : (a 1 : ℚ) = 0 := a_odd 1 ⟨0, rfl⟩
  have ha2 : (a 2 : ℚ) = 100 := by exact_mod_cast a_two_int
  have ha3 : (a 3 : ℚ) = 0 := a_odd 3 ⟨1, rfl⟩
  have ha4 : (a 4 : ℚ) = 10100 := by
    have := a_even 4 (by omega) ⟨2, rfl⟩
    norm_num at this
    exact this
  match n with
  | 0 => simp [ha0]
  | 1 => simp [ha1]
  | 2 => simp [ha2, ha0]; norm_num
  | 3 => simp [ha3, ha1]
  | 4 => simp [ha4, ha2, ha0]; norm_num
  | n + 5 =>
    have hge5 : 5 ≤ n + 5 := by omega
    have hge4 : 4 ≤ n + 5 := by omega
    have hge2 : 2 ≤ n + 5 := by omega
    have hne0 : n + 5 ≠ 0 := by omega
    have hne2 : n + 5 ≠ 2 := by omega
    have hne4' : n + 5 - 4 ≠ 0 := by omega
    simp only [hge4, hge2, hne0, hne2, hne4', ↓reduceIte, sub_zero, add_zero]
    linarith [a_rec (n + 5) hge5]

end OMA.OeisA282142

theorem OMA.solution : type_of% @OMA.S_oeis_a282142.main :=
  ⟨OMA.OeisA282142.a_rec, OMA.OeisA282142.a_even, OMA.OeisA282142.a_odd, OMA.OeisA282142.gf_eq⟩
