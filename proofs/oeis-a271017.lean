import OMAStatements.S_oeis_a271017

namespace OeisA271017

open Finset OMA.S_oeis_a271017

-- ============================================================================
-- Section 1: 45-Degree Rotated 2x2 Operators and Exact Rule 251 Correspondence
-- ============================================================================

private def cntEO (P : ℤ → ℤ → Bool) (u v : ℤ) : ℕ :=
  (P u v).toNat + (P (u + 1) v).toNat + (P u (v + 1)).toNat + (P (u + 1) (v + 1)).toNat

private def stepEO (P : ℤ → ℤ → Bool) (u v : ℤ) : Bool :=
  (cntEO P u v == 1) || (cntEO P u v == 4)

private def stepOE (P : ℤ → ℤ → Bool) (u v : ℤ) : Bool :=
  P (u - 1) (v - 1) || P u (v - 1) || P (u - 1) v || P u v

private lemma stepEO_congr {P Q : ℤ → ℤ → Bool} {u v : ℤ}
    (h00 : P u v = Q u v) (h10 : P (u + 1) v = Q (u + 1) v)
    (h01 : P u (v + 1) = Q u (v + 1)) (h11 : P (u + 1) (v + 1) = Q (u + 1) (v + 1)) :
    stepEO P u v = stepEO Q u v := by
  simp only [stepEO, cntEO, h00, h10, h01, h11]

private lemma stepEO_of_cnt_eq {P Q : ℤ → ℤ → Bool} {u₁ v₁ u₂ v₂ : ℤ}
    (h : cntEO P u₁ v₁ = cntEO Q u₂ v₂) : stepEO P u₁ v₁ = stepEO Q u₂ v₂ := by
  simp only [stepEO, h]

private lemma bool_or4_swap_mid (a b c d : Bool) :
    (a || b || c || d) = (a || c || b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma bool_or4_swap_x (a b c d : Bool) :
    (b || a || d || c) = (a || b || c || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma bool_or4_swap_y (a b c d : Bool) :
    (c || d || a || b) = (a || b || c || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma bool_or5_swap_x (s a b c d : Bool) :
    (s || c || d || a || b) = (s || a || b || c || d) := by
  cases s <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma bool_or5_swap_y (s a b c d : Bool) :
    (s || b || a || d || c) = (s || a || b || c || d) := by
  cases s <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma bool_or5_swap_t (s a b c d : Bool) :
    (s || a || c || b || d) = (s || a || b || c || d) := by
  cases s <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma stepOE_or (P Q : ℤ → ℤ → Bool) (u v : ℤ) :
    stepOE (fun x y => P x y || Q x y) u v = (stepOE P u v || stepOE Q u v) := by
  simp only [stepOE]
  cases P (u - 1) (v - 1) <;> cases P u (v - 1) <;> cases P (u - 1) v <;> cases P u v <;>
    cases Q (u - 1) (v - 1) <;> cases Q u (v - 1) <;> cases Q (u - 1) v <;> cases Q u v <;> rfl

private lemma stepOE_shift (P : ℤ → ℤ → Bool) (c1 c2 u v : ℤ) :
    stepOE (fun x y => P (x - c1) (y - c2)) u v = stepOE P (u - c1) (v - c2) := by
  simp only [stepOE]
  have h1 : u - 1 - c1 = u - c1 - 1 := by ring
  have h2 : v - 1 - c2 = v - c2 - 1 := by ring
  rw [h1, h2]

private lemma stepEO_shift (P : ℤ → ℤ → Bool) (c1 c2 u v : ℤ) :
    stepEO (fun x y => P (x - c1) (y - c2)) u v = stepEO P (u - c1) (v - c2) := by
  apply stepEO_of_cnt_eq
  simp only [cntEO]
  have h1 : u + 1 - c1 = u - c1 + 1 := by ring
  have h2 : v + 1 - c2 = v - c2 + 1 := by ring
  rw [h1, h2]

private lemma bit251_even_zero (c : Bool) :
    Nat.testBit 251 (c.toNat + 2 * (0 + 0 + 0 + 0)) = true := by
  cases c <;> decide

private lemma bit251_even_step (b00 b10 b01 b11 : Bool) :
    Nat.testBit 251 (0 + 2 * (b11.toNat + b00.toNat + b10.toNat + b01.toNat)) =
      !((b00.toNat + b10.toNat + b01.toNat + b11.toNat == 1) ||
        (b00.toNat + b10.toNat + b01.toNat + b11.toNat == 4)) := by
  cases b00 <;> cases b10 <;> cases b01 <;> cases b11 <;> decide

private lemma bit251_odd_zero (c : Bool) :
    Nat.testBit 251 (c.toNat + 2 * (1 + 1 + 1 + 1)) = false := by
  cases c <;> decide

private lemma bit251_odd_step (b00 b10 b01 b11 : Bool) :
    Nat.testBit 251 (1 + 2 * ((!b11).toNat + (!b00).toNat + (!b10).toNat + (!b01).toNat)) =
      (b00 || b10 || b01 || b11) := by
  cases b00 <;> cases b10 <;> cases b01 <;> cases b11 <;> decide

private def Se : ℕ → ℤ → ℤ → Bool
  | 0 => fun u v => decide (u = 0 ∧ v = 0)
  | k + 1 => stepOE (stepEO (Se k))

private def So (k : ℕ) : ℤ → ℤ → Bool := stepEO (Se k)

private lemma cell_even_and_odd :
    ∀ k : ℕ,
      (∀ i j : ℤ, cell 251 (2 * k) i j =
        (decide ((i + j) % 2 = 0) && Se k ((i + j) / 2) ((i - j) / 2))) ∧
      (∀ i j : ℤ, cell 251 (2 * k + 1) i j =
        !(decide ((i + j) % 2 ≠ 0) && So k ((i + j - 1) / 2) ((i - j - 1) / 2))) := by
  have heven_to_odd : ∀ k : ℕ,
      (∀ i j : ℤ, cell 251 (2 * k) i j =
        (decide ((i + j) % 2 = 0) && Se k ((i + j) / 2) ((i - j) / 2))) →
      (∀ i j : ℤ, cell 251 (2 * k + 1) i j =
        !(decide ((i + j) % 2 ≠ 0) && So k ((i + j - 1) / 2) ((i - j - 1) / 2))) := by
    intro k hev i j
    unfold cell
    rw [hev i j, hev (i + 1) j, hev (i - 1) j, hev i (j + 1), hev i (j - 1)]
    by_cases hpar : (i + j) % 2 = 0
    · have h1 : (i + 1 + j) % 2 ≠ 0 := by omega
      have h2 : (i - 1 + j) % 2 ≠ 0 := by omega
      have h3 : (i + (j + 1)) % 2 ≠ 0 := by omega
      have h4 : (i + (j - 1)) % 2 ≠ 0 := by omega
      simp only [hpar, h1, h2, h3, h4, decide_true, decide_false, Bool.false_and,
        Bool.toNat_false, Bool.not_false, ne_eq, not_true_eq_false]
      exact bit251_even_zero _
    · have h1 : (i + 1 + j) % 2 = 0 := by omega
      have h2 : (i - 1 + j) % 2 = 0 := by omega
      have h3 : (i + (j + 1)) % 2 = 0 := by omega
      have h4 : (i + (j - 1)) % 2 = 0 := by omega
      set u : ℤ := (i + j - 1) / 2
      set v : ℤ := (i - j - 1) / 2
      have ha1 : (i + 1 + j) / 2 = u + 1 := by omega
      have ha2 : (i + 1 - j) / 2 = v + 1 := by omega
      have hb1 : (i - 1 + j) / 2 = u := by omega
      have hb2 : (i - 1 - j) / 2 = v := by omega
      have hc1 : (i + (j + 1)) / 2 = u + 1 := by omega
      have hc2 : (i - (j + 1)) / 2 = v := by omega
      have hd1 : (i + (j - 1)) / 2 = u := by omega
      have hd2 : (i - (j - 1)) / 2 = v + 1 := by omega
      simp only [hpar, h1, h2, h3, h4, ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2,
        decide_true, decide_false, Bool.false_and, Bool.true_and, Bool.toNat_false,
        ne_eq, not_false_eq_true, So, stepEO, cntEO]
      exact bit251_even_step (Se k u v) (Se k (u + 1) v) (Se k u (v + 1)) (Se k (u + 1) (v + 1))
  intro k
  induction k with
  | zero =>
    have h0 : ∀ i j : ℤ, cell 251 0 i j =
        (decide ((i + j) % 2 = 0) && Se 0 ((i + j) / 2) ((i - j) / 2)) := by
      intro i j
      simp only [cell, Se]
      by_cases hij : i = 0 ∧ j = 0
      · rcases hij with ⟨rfl, rfl⟩; decide
      · have hnot : ¬ ((i + j) % 2 = 0 ∧ (i + j) / 2 = 0 ∧ (i - j) / 2 = 0) := by omega
        by_cases hpar : (i + j) % 2 = 0
        · have hnot2 : ¬ ((i + j) / 2 = 0 ∧ (i - j) / 2 = 0) := by omega
          simp [hij, hpar, hnot2]
        · simp [hij, hpar]
    exact ⟨h0, heven_to_odd 0 h0⟩
  | succ k ih =>
    have hev_succ : ∀ i j : ℤ, cell 251 (2 * (k + 1)) i j =
        (decide ((i + j) % 2 = 0) && Se (k + 1) ((i + j) / 2) ((i - j) / 2)) := by
      intro i j
      have h2k : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h2k]
      unfold cell
      have hodd := ih.2
      rw [hodd i j, hodd (i + 1) j, hodd (i - 1) j, hodd i (j + 1), hodd i (j - 1)]
      by_cases hpar : (i + j) % 2 = 0
      · have h1 : (i + 1 + j) % 2 ≠ 0 := by omega
        have h2 : (i - 1 + j) % 2 ≠ 0 := by omega
        have h3 : (i + (j + 1)) % 2 ≠ 0 := by omega
        have h4 : (i + (j - 1)) % 2 ≠ 0 := by omega
        set u : ℤ := (i + j) / 2
        set v : ℤ := (i - j) / 2
        have ha1 : (i + 1 + j - 1) / 2 = u := by omega
        have ha2 : (i + 1 - j - 1) / 2 = v := by omega
        have hb1 : (i - 1 + j - 1) / 2 = u - 1 := by omega
        have hb2 : (i - 1 - j - 1) / 2 = v - 1 := by omega
        have hc1 : (i + (j + 1) - 1) / 2 = u := by omega
        have hc2 : (i - (j + 1) - 1) / 2 = v - 1 := by omega
        have hd1 : (i + (j - 1) - 1) / 2 = u - 1 := by omega
        have hd2 : (i - (j - 1) - 1) / 2 = v := by omega
        simp only [hpar, h1, h2, h3, h4, ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2,
          decide_true, decide_false, Bool.false_and, Bool.true_and, Bool.not_false,
          Bool.toNat_true, ne_eq, not_true_eq_false, not_false_eq_true, Se, stepOE, So]
        exact bit251_odd_step (stepEO (Se k) (u - 1) (v - 1)) (stepEO (Se k) u (v - 1))
          (stepEO (Se k) (u - 1) v) (stepEO (Se k) u v)
      · have h1 : (i + 1 + j) % 2 = 0 := by omega
        have h2 : (i - 1 + j) % 2 = 0 := by omega
        have h3 : (i + (j + 1)) % 2 = 0 := by omega
        have h4 : (i + (j - 1)) % 2 = 0 := by omega
        simp only [hpar, h1, h2, h3, h4, decide_false, Bool.false_and,
          Bool.not_false, Bool.toNat_true, ne_eq, not_true_eq_false]
        exact bit251_odd_zero _
    exact ⟨hev_succ, heven_to_odd (k + 1) hev_succ⟩

-- ============================================================================
-- Section 2: Corner Seed Evolution (To, Te) and Its Three Invariants
-- ============================================================================

private def To : ℕ → ℤ → ℤ → Bool
  | 0 => fun u v => decide (u = 0 ∧ v = 0)
  | r + 1 => stepEO (stepOE (To r))

private def Te (r : ℕ) : ℤ → ℤ → Bool := stepOE (To r)

private lemma To_Te_invariants :
    ∀ r : ℕ,
      (∀ u v, To r u v = true → -(r : ℤ) ≤ u ∧ u ≤ r ∧ -(r : ℤ) ≤ v ∧ v ≤ r) ∧
      (To r 0 0 = true) ∧
      (∀ u v, To r (-u) v = To r u v) ∧
      (∀ u v, To r u (-v) = To r u v) ∧
      (∀ u v, To r v u = To r u v) ∧
      (∀ u v, Te r u v = true → -(r : ℤ) ≤ u ∧ u ≤ r + 1 ∧ -(r : ℤ) ≤ v ∧ v ≤ r + 1) ∧
      (∀ u v, (u = 0 ∨ u = 1) → (v = 0 ∨ v = 1) → Te r u v = true) ∧
      (∀ u v, Te r (1 - u) v = Te r u v) ∧
      (∀ u v, Te r u (1 - v) = Te r u v) ∧
      (∀ u v, Te r v u = Te r u v) := by
  have hTo_to_Te : ∀ r : ℕ,
      ((∀ u v, To r u v = true → -(r : ℤ) ≤ u ∧ u ≤ r ∧ -(r : ℤ) ≤ v ∧ v ≤ r) ∧
       (To r 0 0 = true) ∧
       (∀ u v, To r (-u) v = To r u v) ∧
       (∀ u v, To r u (-v) = To r u v) ∧
       (∀ u v, To r v u = To r u v)) →
      ((∀ u v, Te r u v = true → -(r : ℤ) ≤ u ∧ u ≤ r + 1 ∧ -(r : ℤ) ≤ v ∧ v ≤ r + 1) ∧
       (∀ u v, (u = 0 ∨ u = 1) → (v = 0 ∨ v = 1) → Te r u v = true) ∧
       (∀ u v, Te r (1 - u) v = Te r u v) ∧
       (∀ u v, Te r u (1 - v) = Te r u v) ∧
       (∀ u v, Te r v u = Te r u v)) := by
    rintro r ⟨hcone, hcore, hsx, hsy, hst⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u v h
      simp only [Te, stepOE, Bool.or_eq_true] at h
      rcases h with ((h | h) | h) | h
      · have := hcone (u - 1) (v - 1) h; omega
      · have := hcone u (v - 1) h; omega
      · have := hcone (u - 1) v h; omega
      · have := hcone u v h; omega
    · intro u v hu hv
      simp only [Te, stepOE, Bool.or_eq_true]
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · right; exact hcore
      · left; left; right; simpa using hcore
      · left; right; simpa using hcore
      · left; left; left; simpa using hcore
    · intro u v
      simp only [Te, stepOE]
      have e1 : 1 - u - 1 = -u := by ring
      have e2 : -(1 - u) = u - 1 := by ring
      rw [e1, hsx u (v - 1), hsx u v, ← hsx (1 - u) (v - 1), ← hsx (1 - u) v, e2]
      exact bool_or4_swap_x _ _ _ _
    · intro u v
      simp only [Te, stepOE]
      have e1 : 1 - v - 1 = -v := by ring
      have e2 : -(1 - v) = v - 1 := by ring
      rw [e1, hsy (u - 1) v, hsy u v, ← hsy (u - 1) (1 - v), ← hsy u (1 - v), e2]
      exact bool_or4_swap_y _ _ _ _
    · intro u v
      simp only [Te, stepOE]
      rw [hst (v - 1) (u - 1), hst v (u - 1), hst (v - 1) u, hst v u]
      exact bool_or4_swap_mid _ _ _ _
  intro r
  induction r with
  | zero =>
    have hbase : (∀ u v, To 0 u v = true → -(0 : ℤ) ≤ u ∧ u ≤ 0 ∧ -(0 : ℤ) ≤ v ∧ v ≤ 0) ∧
        (To 0 0 0 = true) ∧
        (∀ u v, To 0 (-u) v = To 0 u v) ∧
        (∀ u v, To 0 u (-v) = To 0 u v) ∧
        (∀ u v, To 0 v u = To 0 u v) := by
      refine ⟨?_, by decide, ?_, ?_, ?_⟩
      · intro u v h; simp [To] at h; omega
      · intro u v; simp only [To]; by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [hu, hv]
      · intro u v; simp only [To]; by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [hu, hv]
      · intro u v; simp only [To]; by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [hu, hv]
    exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hbase.2.2.2.2, hTo_to_Te 0 hbase⟩
  | succ r ih =>
    obtain ⟨_, _, _, _, _, hte_cone, hte_core, hte_sx, hte_sy, hte_st⟩ := ih
    have hnext : (∀ u v, To (r + 1) u v = true →
          -((r + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (r + 1 : ℕ) ∧ -((r + 1 : ℕ) : ℤ) ≤ v ∧ v ≤ (r + 1 : ℕ)) ∧
        (To (r + 1) 0 0 = true) ∧
        (∀ u v, To (r + 1) (-u) v = To (r + 1) u v) ∧
        (∀ u v, To (r + 1) u (-v) = To (r + 1) u v) ∧
        (∀ u v, To (r + 1) v u = To (r + 1) u v) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro u v h
        change stepEO (Te r) u v = true at h
        have hex : Te r u v = true ∨ Te r (u + 1) v = true ∨
            Te r u (v + 1) = true ∨ Te r (u + 1) (v + 1) = true := by
          by_contra hnone
          push Not at hnone
          simp only [Bool.not_eq_true] at hnone
          rcases hnone with ⟨h1, h2, h3, h4⟩
          simp [stepEO, cntEO, h1, h2, h3, h4] at h
        rcases hex with h1 | h2 | h3 | h4
        · have := hte_cone u v h1; omega
        · have := hte_cone (u + 1) v h2; omega
        · have := hte_cone u (v + 1) h3; omega
        · have := hte_cone (u + 1) (v + 1) h4; omega
      · change stepEO (Te r) 0 0 = true
        simp only [stepEO, cntEO, zero_add, hte_core 0 0 (Or.inl rfl) (Or.inl rfl),
          hte_core 1 0 (Or.inr rfl) (Or.inl rfl),
          hte_core 0 1 (Or.inl rfl) (Or.inr rfl),
          hte_core 1 1 (Or.inr rfl) (Or.inr rfl)]
        rfl
      · intro u v
        change stepEO (Te r) (-u) v = stepEO (Te r) u v
        apply stepEO_of_cnt_eq
        simp only [cntEO]
        have e1 : 1 - (-u) = u + 1 := by ring
        have e2 : 1 - (-u + 1) = u := by ring
        have h1 : Te r (-u) v = Te r (u + 1) v := by rw [← hte_sx (-u) v, e1]
        have h2 : Te r (-u + 1) v = Te r u v := by rw [← hte_sx (-u + 1) v, e2]
        have h3 : Te r (-u) (v + 1) = Te r (u + 1) (v + 1) := by rw [← hte_sx (-u) (v + 1), e1]
        have h4 : Te r (-u + 1) (v + 1) = Te r u (v + 1) := by rw [← hte_sx (-u + 1) (v + 1), e2]
        rw [h1, h2, h3, h4]; omega
      · intro u v
        change stepEO (Te r) u (-v) = stepEO (Te r) u v
        apply stepEO_of_cnt_eq
        simp only [cntEO]
        have e1 : 1 - (-v) = v + 1 := by ring
        have e2 : 1 - (-v + 1) = v := by ring
        have h1 : Te r u (-v) = Te r u (v + 1) := by rw [← hte_sy u (-v), e1]
        have h2 : Te r (u + 1) (-v) = Te r (u + 1) (v + 1) := by rw [← hte_sy (u + 1) (-v), e1]
        have h3 : Te r u (-v + 1) = Te r u v := by rw [← hte_sy u (-v + 1), e2]
        have h4 : Te r (u + 1) (-v + 1) = Te r (u + 1) v := by rw [← hte_sy (u + 1) (-v + 1), e2]
        rw [h1, h2, h3, h4]; omega
      · intro u v
        change stepEO (Te r) v u = stepEO (Te r) u v
        apply stepEO_of_cnt_eq
        simp only [cntEO]
        rw [hte_st v u, hte_st (v + 1) u, hte_st v (u + 1), hte_st (v + 1) (u + 1)]; omega
    exact ⟨hnext.1, hnext.2.1, hnext.2.2.1, hnext.2.2.2.1, hnext.2.2.2.2, hTo_to_Te (r + 1) hnext⟩

-- ============================================================================
-- Section 3: Unified Square-Corner Decomposition Lemma
-- ============================================================================

private def sqBox (a b u v : ℤ) : Bool :=
  decide (a ≤ u ∧ u ≤ b ∧ a ≤ v ∧ v ≤ b)

private def Uo (a b : ℤ) (r : ℕ) (u v : ℤ) : Bool :=
  sqBox a (b - 1) u v ||
  To r (u - (a - 1)) (v - (a - 1)) ||
  To r (u - (a - 1)) (v - b) ||
  To r (u - b) (v - (a - 1)) ||
  To r (u - b) (v - b)

private def Ue (a b : ℤ) (r : ℕ) (u v : ℤ) : Bool :=
  sqBox a b u v ||
  Te r (u - (a - 1)) (v - (a - 1)) ||
  Te r (u - (a - 1)) (v - b) ||
  Te r (u - b) (v - (a - 1)) ||
  Te r (u - b) (v - b)

private lemma stepEO_sqBox {a b : ℤ} (hab : a < b) (u v : ℤ) :
    stepEO (sqBox a b) u v = Uo a b 0 u v := by
  have hmul : ∀ b1 b2 : Bool, (b1 && b2).toNat = b1.toNat * b2.toNat := by decide
  have hsq_split : ∀ x y : ℤ,
      sqBox a b x y = (decide (a ≤ x ∧ x ≤ b) && decide (a ≤ y ∧ y ≤ b)) := by
    intro x y
    simp only [sqBox, Bool.decide_and, Bool.and_assoc]
  have hcnt : cntEO (sqBox a b) u v =
      ((decide (a ≤ u ∧ u ≤ b)).toNat + (decide (a ≤ u + 1 ∧ u + 1 ≤ b)).toNat) *
      ((decide (a ≤ v ∧ v ≤ b)).toNat + (decide (a ≤ v + 1 ∧ v + 1 ≤ b)).toNat) := by
    simp only [cntEO, hsq_split, hmul]
    ring
  have hc : ∀ z : ℤ,
      ((decide (a ≤ z ∧ z ≤ b)).toNat + (decide (a ≤ z + 1 ∧ z + 1 ≤ b)).toNat = 2 ↔
        a ≤ z ∧ z ≤ b - 1) ∧
      ((decide (a ≤ z ∧ z ≤ b)).toNat + (decide (a ≤ z + 1 ∧ z + 1 ≤ b)).toNat = 1 ↔
        z = a - 1 ∨ z = b) ∧
      (decide (a ≤ z ∧ z ≤ b)).toNat + (decide (a ≤ z + 1 ∧ z + 1 ≤ b)).toNat ≤ 2 := by
    intro z
    by_cases h1 : a ≤ z ∧ z ≤ b <;> by_cases h2 : a ≤ z + 1 ∧ z + 1 ≤ b
    · rw [decide_eq_true h1, decide_eq_true h2]
      refine ⟨by simp; omega, by simp; omega, by decide⟩
    · rw [decide_eq_true h1, decide_eq_false h2]
      refine ⟨by simp; omega, by simp; omega, by decide⟩
    · rw [decide_eq_false h1, decide_eq_true h2]
      refine ⟨by simp; omega, by simp; omega, by decide⟩
    · rw [decide_eq_false h1, decide_eq_false h2]
      refine ⟨by simp; omega, by simp; omega, by decide⟩
  have hprod : ∀ x y : ℕ, x ≤ 2 → y ≤ 2 →
      (x * y = 1 ∨ x * y = 4 ↔ (x = 2 ∧ y = 2) ∨ (x = 1 ∧ y = 1)) := by
    intro x y hx hy
    interval_cases x <;> interval_cases y <;> decide
  apply Bool.eq_iff_iff.mpr
  simp only [stepEO, hcnt, Bool.or_eq_true, beq_iff_eq]
  rw [hprod _ _ (hc u).2.2 (hc v).2.2, (hc u).1, (hc u).2.1, (hc v).1, (hc v).2.1]
  simp only [Uo, sqBox, To, Bool.or_eq_true, decide_eq_true_eq]
  omega

private lemma stepOE_sqBox {a b : ℤ} (hab : a < b) (u v : ℤ) :
    stepOE (sqBox a (b - 1)) u v = sqBox a b u v := by
  simp only [stepOE, sqBox]
  by_cases h : a ≤ u ∧ u ≤ b ∧ a ≤ v ∧ v ≤ b
  · rw [decide_eq_true h, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
    simp only [decide_eq_true_eq]
    by_cases hu : u = a <;> by_cases hv : v = a
    · right; omega
    · left; left; right; omega
    · left; right; omega
    · left; left; left; omega
  · rw [decide_eq_false h, Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff]
    simp only [decide_eq_false_iff_not]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩

private lemma stepOE_Uo {a b : ℤ} (hab : a < b) (r : ℕ) (u v : ℤ) :
    stepOE (Uo a b r) u v = Ue a b r u v := by
  change stepOE (fun x y =>
    (((sqBox a (b - 1) x y || To r (x - (a - 1)) (y - (a - 1))) ||
      To r (x - (a - 1)) (y - b)) ||
      To r (x - b) (y - (a - 1))) ||
      To r (x - b) (y - b)) u v = Ue a b r u v
  rw [stepOE_or, stepOE_or, stepOE_or, stepOE_or,
    stepOE_sqBox hab, stepOE_shift, stepOE_shift, stepOE_shift, stepOE_shift]
  rfl

private lemma Ue_sym_x (a b : ℤ) (r : ℕ) (x y : ℤ) :
    Ue a b r (a + b - x) y = Ue a b r x y := by
  have hsx := (To_Te_invariants r).2.2.2.2.2.2.2.1
  simp only [Ue, sqBox]
  have hb : (a ≤ a + b - x ∧ a + b - x ≤ b ∧ a ≤ y ∧ y ≤ b) ↔
      (a ≤ x ∧ x ≤ b ∧ a ≤ y ∧ y ≤ b) := by omega
  have e1 : a + b - x - (a - 1) = 1 - (x - b) := by ring
  have e2 : a + b - x - b = 1 - (x - (a - 1)) := by ring
  rw [e1, e2, hsx (x - b), hsx (x - b), hsx (x - (a - 1)), hsx (x - (a - 1))]
  simp only [hb]
  exact bool_or5_swap_x _ _ _ _ _

private lemma Ue_sym_y (a b : ℤ) (r : ℕ) (x y : ℤ) :
    Ue a b r x (a + b - y) = Ue a b r x y := by
  have hsy := (To_Te_invariants r).2.2.2.2.2.2.2.2.1
  simp only [Ue, sqBox]
  have hb : (a ≤ x ∧ x ≤ b ∧ a ≤ a + b - y ∧ a + b - y ≤ b) ↔
      (a ≤ x ∧ x ≤ b ∧ a ≤ y ∧ y ≤ b) := by omega
  have e1 : a + b - y - (a - 1) = 1 - (y - b) := by ring
  have e2 : a + b - y - b = 1 - (y - (a - 1)) := by ring
  rw [e1, e2, hsy _ (y - b), hsy _ (y - b), hsy _ (y - (a - 1)), hsy _ (y - (a - 1))]
  simp only [hb]
  exact bool_or5_swap_y _ _ _ _ _

private lemma Ue_sym_t (a b : ℤ) (r : ℕ) (x y : ℤ) :
    Ue a b r y x = Ue a b r x y := by
  have hst := (To_Te_invariants r).2.2.2.2.2.2.2.2.2
  simp only [Ue, sqBox]
  have hb : (a ≤ y ∧ y ≤ b ∧ a ≤ x ∧ x ≤ b) ↔ (a ≤ x ∧ x ≤ b ∧ a ≤ y ∧ y ≤ b) := by omega
  rw [hst (y - (a - 1)) (x - (a - 1)), hst (y - (a - 1)) (x - b),
    hst (y - b) (x - (a - 1)), hst (y - b) (x - b)]
  simp only [hb]
  exact bool_or5_swap_t _ _ _ _ _

private lemma Uo_sym_x (a b : ℤ) (r : ℕ) (u v : ℤ) :
    Uo a b r (a + b - 1 - u) v = Uo a b r u v := by
  have hsx := (To_Te_invariants r).2.2.1
  simp only [Uo, sqBox]
  have hb : (a ≤ a + b - 1 - u ∧ a + b - 1 - u ≤ b - 1 ∧ a ≤ v ∧ v ≤ b - 1) ↔
      (a ≤ u ∧ u ≤ b - 1 ∧ a ≤ v ∧ v ≤ b - 1) := by omega
  have e1 : a + b - 1 - u - (a - 1) = -(u - b) := by ring
  have e2 : a + b - 1 - u - b = -(u - (a - 1)) := by ring
  rw [e1, e2, hsx (u - b), hsx (u - b), hsx (u - (a - 1)), hsx (u - (a - 1))]
  simp only [hb]
  exact bool_or5_swap_x _ _ _ _ _

private lemma Uo_sym_y (a b : ℤ) (r : ℕ) (u v : ℤ) :
    Uo a b r u (a + b - 1 - v) = Uo a b r u v := by
  have hsy := (To_Te_invariants r).2.2.2.1
  simp only [Uo, sqBox]
  have hb : (a ≤ u ∧ u ≤ b - 1 ∧ a ≤ a + b - 1 - v ∧ a + b - 1 - v ≤ b - 1) ↔
      (a ≤ u ∧ u ≤ b - 1 ∧ a ≤ v ∧ v ≤ b - 1) := by omega
  have e1 : a + b - 1 - v - (a - 1) = -(v - b) := by ring
  have e2 : a + b - 1 - v - b = -(v - (a - 1)) := by ring
  rw [e1, e2, hsy _ (v - b), hsy _ (v - b), hsy _ (v - (a - 1)), hsy _ (v - (a - 1))]
  simp only [hb]
  exact bool_or5_swap_y _ _ _ _ _

private lemma Uo_sym_t (a b : ℤ) (r : ℕ) (u v : ℤ) :
    Uo a b r v u = Uo a b r u v := by
  have hst := (To_Te_invariants r).2.2.2.2.1
  simp only [Uo, sqBox]
  have hb : (a ≤ v ∧ v ≤ b - 1 ∧ a ≤ u ∧ u ≤ b - 1) ↔
      (a ≤ u ∧ u ≤ b - 1 ∧ a ≤ v ∧ v ≤ b - 1) := by omega
  rw [hst (v - (a - 1)) (u - (a - 1)), hst (v - (a - 1)) (u - b),
    hst (v - b) (u - (a - 1)), hst (v - b) (u - b)]
  simp only [hb]
  exact bool_or5_swap_t _ _ _ _ _

private lemma stepEO_Ue_sym_x (a b : ℤ) (r : ℕ) (u v : ℤ) :
    stepEO (Ue a b r) (a + b - 1 - u) v = stepEO (Ue a b r) u v := by
  apply stepEO_of_cnt_eq
  simp only [cntEO]
  have e1 : a + b - (a + b - 1 - u) = u + 1 := by ring
  have e2 : a + b - (a + b - 1 - u + 1) = u := by ring
  have h1 : Ue a b r (a + b - 1 - u) v = Ue a b r (u + 1) v := by rw [← Ue_sym_x a b r, e1]
  have h2 : Ue a b r (a + b - 1 - u + 1) v = Ue a b r u v := by rw [← Ue_sym_x a b r, e2]
  have h3 : Ue a b r (a + b - 1 - u) (v + 1) = Ue a b r (u + 1) (v + 1) := by rw [← Ue_sym_x a b r, e1]
  have h4 : Ue a b r (a + b - 1 - u + 1) (v + 1) = Ue a b r u (v + 1) := by rw [← Ue_sym_x a b r, e2]
  rw [h1, h2, h3, h4]; omega

private lemma stepEO_Ue_sym_y (a b : ℤ) (r : ℕ) (u v : ℤ) :
    stepEO (Ue a b r) u (a + b - 1 - v) = stepEO (Ue a b r) u v := by
  apply stepEO_of_cnt_eq
  simp only [cntEO]
  have e1 : a + b - (a + b - 1 - v) = v + 1 := by ring
  have e2 : a + b - (a + b - 1 - v + 1) = v := by ring
  have h1 : Ue a b r u (a + b - 1 - v) = Ue a b r u (v + 1) := by rw [← Ue_sym_y a b r, e1]
  have h2 : Ue a b r (u + 1) (a + b - 1 - v) = Ue a b r (u + 1) (v + 1) := by rw [← Ue_sym_y a b r, e1]
  have h3 : Ue a b r u (a + b - 1 - v + 1) = Ue a b r u v := by rw [← Ue_sym_y a b r, e2]
  have h4 : Ue a b r (u + 1) (a + b - 1 - v + 1) = Ue a b r (u + 1) v := by rw [← Ue_sym_y a b r, e2]
  rw [h1, h2, h3, h4]; omega

private lemma stepEO_Ue_sym_t (a b : ℤ) (r : ℕ) (u v : ℤ) :
    stepEO (Ue a b r) v u = stepEO (Ue a b r) u v := by
  apply stepEO_of_cnt_eq
  simp only [cntEO]
  rw [Ue_sym_t a b r v u, Ue_sym_t a b r (v + 1) u,
    Ue_sym_t a b r v (u + 1), Ue_sym_t a b r (v + 1) (u + 1)]; omega

private lemma stepEO_Ue_canonical {a b : ℤ} {r : ℕ} (hab : a < b)
    (hr : 2 * (r : ℤ) + 2 ≤ b - a) {u v : ℤ} (hu : b ≤ u) (hv : a + b - 1 ≤ 2 * v) :
    stepEO (Ue a b r) u v = Uo a b (r + 1) u v := by
  have hTe_cone := (To_Te_invariants r).2.2.2.2.2.1
  have hTe_core := (To_Te_invariants r).2.2.2.2.2.2.1
  have hTe_sx := (To_Te_invariants r).2.2.2.2.2.2.2.1
  have hTo_cone := (To_Te_invariants (r + 1)).1
  have hUe_eq : ∀ x y : ℤ, b ≤ x → a + b - 1 ≤ 2 * y →
      Ue a b r x y = (sqBox a b x y || Te r (x - b) (y - b)) := by
    intro x y hx hy
    have hz1 : Te r (x - (a - 1)) (y - (a - 1)) = false := by
      cases h : Te r (x - (a - 1)) (y - (a - 1)) with
      | false => rfl
      | true => have := hTe_cone _ _ h; omega
    have hz2 : Te r (x - (a - 1)) (y - b) = false := by
      cases h : Te r (x - (a - 1)) (y - b) with
      | false => rfl
      | true => have := hTe_cone _ _ h; omega
    have hz3 : Te r (x - b) (y - (a - 1)) = false := by
      cases h : Te r (x - b) (y - (a - 1)) with
      | false => rfl
      | true => have := hTe_cone _ _ h; omega
    simp only [Ue, hz1, hz2, hz3, Bool.or_false]
  have hUo_eq : Uo a b (r + 1) u v = stepEO (fun x y => Te r (x - b) (y - b)) u v := by
    have hsq : sqBox a (b - 1) u v = false := by simp only [sqBox]; rw [decide_eq_false_iff_not]; omega
    have hz1 : To (r + 1) (u - (a - 1)) (v - (a - 1)) = false := by
      cases h : To (r + 1) (u - (a - 1)) (v - (a - 1)) with
      | false => rfl
      | true => have := hTo_cone _ _ h; omega
    have hz2 : To (r + 1) (u - (a - 1)) (v - b) = false := by
      cases h : To (r + 1) (u - (a - 1)) (v - b) with
      | false => rfl
      | true => have := hTo_cone _ _ h; omega
    have hz3 : To (r + 1) (u - b) (v - (a - 1)) = false := by
      cases h : To (r + 1) (u - b) (v - (a - 1)) with
      | false => rfl
      | true => have := hTo_cone _ _ h; omega
    simp only [Uo, hsq, hz1, hz2, hz3, Bool.false_or]
    rw [stepEO_shift]
    rfl
  rw [hUo_eq]
  rw [stepEO_congr (Q := fun x y => sqBox a b x y || Te r (x - b) (y - b))
    (hUe_eq u v hu hv) (hUe_eq (u + 1) v (by omega) hv)
    (hUe_eq u (v + 1) hu (by omega)) (hUe_eq (u + 1) (v + 1) (by omega) (by omega))]
  by_cases hout : b + 1 ≤ u ∨ b + 1 ≤ v
  · apply stepEO_congr
    · have : sqBox a b u v = false := by simp only [sqBox]; rw [decide_eq_false_iff_not]; omega
      simp [this]
    · have : sqBox a b (u + 1) v = false := by simp only [sqBox]; rw [decide_eq_false_iff_not]; omega
      simp [this]
    · have : sqBox a b u (v + 1) = false := by simp only [sqBox]; rw [decide_eq_false_iff_not]; omega
      simp [this]
    · have : sqBox a b (u + 1) (v + 1) = false := by simp only [sqBox]; rw [decide_eq_false_iff_not]; omega
      simp [this]
  · have hu_eq : u = b := by omega
    subst u
    by_cases hvb : v = b
    · subst v
      have ht00 : Te r (b - b) (b - b) = true := by simpa using hTe_core 0 0 (Or.inl rfl) (Or.inl rfl)
      have ht10 : Te r (b + 1 - b) (b - b) = true := by
        rw [show b + 1 - b = 1 by ring, show b - b = 0 by ring]
        exact hTe_core 1 0 (Or.inr rfl) (Or.inl rfl)
      have ht01 : Te r (b - b) (b + 1 - b) = true := by
        rw [show b - b = 0 by ring, show b + 1 - b = 1 by ring]
        exact hTe_core 0 1 (Or.inl rfl) (Or.inr rfl)
      have ht11 : Te r (b + 1 - b) (b + 1 - b) = true := by
        rw [show b + 1 - b = 1 by ring]
        exact hTe_core 1 1 (Or.inr rfl) (Or.inr rfl)
      simp only [stepEO, cntEO, ht00, ht10, ht01, ht11, Bool.or_true]
    · have hva : a ≤ v := by omega
      have hvb' : v ≤ b - 1 := by omega
      have hs00 : sqBox a b b v = true := by simp only [sqBox, decide_eq_true_eq]; omega
      have hs01 : sqBox a b b (v + 1) = true := by simp only [sqBox, decide_eq_true_eq]; omega
      have hs10 : sqBox a b (b + 1) v = false := by simp only [sqBox, decide_eq_false_iff_not]; omega
      have hs11 : sqBox a b (b + 1) (v + 1) = false := by simp only [sqBox, decide_eq_false_iff_not]; omega
      have htx0 : Te r (b + 1 - b) (v - b) = Te r (b - b) (v - b) := by
        rw [show b + 1 - b = 1 - 0 by ring, show b - b = 0 by ring]
        exact hTe_sx 0 (v - b)
      have htx1 : Te r (b + 1 - b) (v + 1 - b) = Te r (b - b) (v + 1 - b) := by
        rw [show b + 1 - b = 1 - 0 by ring, show b - b = 0 by ring]
        exact hTe_sx 0 (v + 1 - b)
      simp only [stepEO, cntEO, hs00, hs01, hs10, hs11, htx0, htx1, Bool.true_or, Bool.false_or]
      cases Te r (b - b) (v - b) <;> cases Te r (b - b) (v + 1 - b) <;> decide

private lemma stepEO_Ue {a b : ℤ} {r : ℕ} (hab : a < b) (hr : 2 * (r : ℤ) + 2 ≤ b - a) (u v : ℤ) :
    stepEO (Ue a b r) u v = Uo a b (r + 1) u v := by
  by_cases hin : a ≤ u ∧ u ≤ b - 1 ∧ a ≤ v ∧ v ≤ b - 1
  · have hs00 : sqBox a b u v = true := by simp only [sqBox, decide_eq_true_eq]; omega
    have hs10 : sqBox a b (u + 1) v = true := by simp only [sqBox, decide_eq_true_eq]; omega
    have hs01 : sqBox a b u (v + 1) = true := by simp only [sqBox, decide_eq_true_eq]; omega
    have hs11 : sqBox a b (u + 1) (v + 1) = true := by simp only [sqBox, decide_eq_true_eq]; omega
    have hsq_in : sqBox a (b - 1) u v = true := by simp only [sqBox, decide_eq_true_eq]; omega
    simp only [stepEO, cntEO, Ue, Uo, hs00, hs10, hs01, hs11, hsq_in, Bool.true_or]
    decide
  · by_cases hu_hi : b ≤ u
    · by_cases hv_hi : a + b - 1 ≤ 2 * v
      · exact stepEO_Ue_canonical hab hr hu_hi hv_hi
      · rw [← stepEO_Ue_sym_y a b r u v, ← Uo_sym_y a b (r + 1) u v]
        exact stepEO_Ue_canonical hab hr hu_hi (by omega)
    · by_cases hu_lo : u ≤ a - 1
      · rw [← stepEO_Ue_sym_x a b r u v, ← Uo_sym_x a b (r + 1) u v]
        by_cases hv_hi : a + b - 1 ≤ 2 * v
        · exact stepEO_Ue_canonical hab hr (by omega) hv_hi
        · rw [← stepEO_Ue_sym_y a b r (a + b - 1 - u) v, ← Uo_sym_y a b (r + 1) (a + b - 1 - u) v]
          exact stepEO_Ue_canonical hab hr (by omega) (by omega)
      · rw [← stepEO_Ue_sym_t a b r u v, ← Uo_sym_t a b (r + 1) u v]
        by_cases hv_hi : b ≤ v
        · by_cases hu_half : a + b - 1 ≤ 2 * u
          · exact stepEO_Ue_canonical hab hr hv_hi hu_half
          · rw [← stepEO_Ue_sym_y a b r v u, ← Uo_sym_y a b (r + 1) v u]
            exact stepEO_Ue_canonical hab hr hv_hi (by omega)
        · have hv_lo : v ≤ a - 1 := by omega
          rw [← stepEO_Ue_sym_x a b r v u, ← Uo_sym_x a b (r + 1) v u]
          by_cases hu_half : a + b - 1 ≤ 2 * u
          · exact stepEO_Ue_canonical hab hr (by omega) hu_half
          · rw [← stepEO_Ue_sym_y a b r (a + b - 1 - v) u, ← Uo_sym_y a b (r + 1) (a + b - 1 - v) u]
            exact stepEO_Ue_canonical hab hr (by omega) (by omega)

-- ============================================================================
-- Section 4: Simultaneous Power-of-Two Solid Square Theorem
-- ============================================================================

private lemma iter_Ue {a b : ℤ} (hab : a < b) (F : ℕ → ℤ → ℤ → Bool) (k0 : ℕ)
    (hinit : F k0 = sqBox a b) (hstep : ∀ k, F (k + 1) = stepOE (stepEO (F k))) :
    ∀ r : ℕ, 2 * (r : ℤ) ≤ b - a → F (k0 + r + 1) = Ue a b r := by
  intro r
  induction r with
  | zero =>
    intro _
    funext u v
    rw [show k0 + 0 + 1 = k0 + 1 by omega, hstep k0, hinit]
    have h1 : stepEO (sqBox a b) = Uo a b 0 := by funext x y; exact stepEO_sqBox hab x y
    rw [h1]
    exact stepOE_Uo hab 0 u v
  | succ r ih =>
    intro hr
    funext u v
    rw [show k0 + (r + 1) + 1 = (k0 + r + 1) + 1 by omega, hstep (k0 + r + 1), ih (by omega)]
    have h1 : stepEO (Ue a b r) = Uo a b (r + 1) := by
      funext x y; exact stepEO_Ue hab (by omega) x y
    rw [h1]
    exact stepOE_Uo hab (r + 1) u v

private lemma solid_squares :
    ∀ m : ℕ,
      Te (2 ^ m - 1) = sqBox (-(2 ^ m - 1 : ℤ)) (2 ^ m : ℤ) ∧
      Se (2 ^ m - 1) = sqBox (-(2 ^ m - 1 : ℤ)) (2 ^ m - 1 : ℤ) := by
  intro m
  induction m with
  | zero =>
    constructor
    · funext u v
      simp only [pow_zero, Nat.sub_self, Te, stepOE, To, sqBox]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (((h | h) | h) | h) <;> omega
      · intro h
        rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;>
        rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> simp
    · funext u v
      simp only [pow_zero, Nat.sub_self, Se, sqBox]
      have heq : (u = 0 ∧ v = 0) ↔ (-(1 - 1 : ℤ) ≤ u ∧ u ≤ 1 - 1 ∧ -(1 - 1 : ℤ) ≤ v ∧ v ≤ 1 - 1) := by omega
      simp [heq]
  | succ m ih =>
    obtain ⟨ihT, ihS⟩ := ih
    set M : ℕ := 2 ^ m
    have hM_pos : 1 ≤ M := Nat.one_le_pow m 2 (by omega)
    have hM_int : (2 : ℤ) ^ m = (M : ℤ) := by exact_mod_cast (rfl : 2 ^ m = M)
    have h2M : 2 ^ (m + 1) = 2 * M := by rw [pow_succ]; ring
    have h2M_int : (2 : ℤ) ^ (m + 1) = 2 * (M : ℤ) := by exact_mod_cast h2M
    have hTe_step : ∀ k : ℕ, Te (k + 1) = stepOE (stepEO (Te k)) := fun _ => rfl
    have hSe_step : ∀ k : ℕ, Se (k + 1) = stepOE (stepEO (Se k)) := fun _ => rfl
    have hTe_next : Te (2 ^ (m + 1) - 1) = sqBox (-(2 ^ (m + 1) - 1 : ℤ)) (2 ^ (m + 1) : ℤ) := by
      have ha_lt_b : (-(M - 1 : ℤ)) < (M : ℤ) := by omega
      have hiter := iter_Ue ha_lt_b Te (M - 1) ihT hTe_step (M - 1) (by omega)
      have hidx : M - 1 + (M - 1) + 1 = 2 ^ (m + 1) - 1 := by omega
      rw [hidx] at hiter
      rw [hiter]
      funext u v
      simp only [Ue, ihT, sqBox, hM_int, h2M_int]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((((h | h) | h) | h) | h) <;> omega
      · intro h
        by_cases hu : u ≤ 0 <;> by_cases hv : v ≤ 0
        · left; left; left; right; omega
        · left; left; right; omega
        · left; right; omega
        · right; omega
    have hSe_next : Se (2 ^ (m + 1) - 1) = sqBox (-(2 ^ (m + 1) - 1 : ℤ)) (2 ^ (m + 1) - 1 : ℤ) := by
      cases m with
      | zero =>
        funext u v
        rw [show 2 ^ (0 + 1) - 1 = 1 by rfl,
            show -(2 ^ (0 + 1) - 1 : ℤ) = -1 by norm_num,
            show (2 ^ (0 + 1) - 1 : ℤ) = 1 by norm_num]
        simp only [Se, stepOE, stepEO, cntEO, sqBox]
        by_cases h : (-1 : ℤ) ≤ u ∧ u ≤ 1 ∧ (-1 : ℤ) ≤ v ∧ v ≤ 1
        · rw [decide_eq_true h]
          rcases (by omega : u = -1 ∨ u = 0 ∨ u = 1) with rfl | rfl | rfl <;>
          rcases (by omega : v = -1 ∨ v = 0 ∨ v = 1) with rfl | rfl | rfl <;> decide
        · rw [decide_eq_false h]
          have hsub : ∀ x y : ℤ, (x = u - 1 ∨ x = u) → (y = v - 1 ∨ y = v) →
              (((decide (x = 0 ∧ y = 0)).toNat + (decide (x + 1 = 0 ∧ y = 0)).toNat +
                (decide (x = 0 ∧ y + 1 = 0)).toNat + (decide (x + 1 = 0 ∧ y + 1 = 0)).toNat == 1) ||
               ((decide (x = 0 ∧ y = 0)).toNat + (decide (x + 1 = 0 ∧ y = 0)).toNat +
                (decide (x = 0 ∧ y + 1 = 0)).toNat + (decide (x + 1 = 0 ∧ y + 1 = 0)).toNat == 4)) = false := by
            intro x y hx hy
            have ha : ¬ (x = 0 ∧ y = 0) := by omega
            have hb : ¬ (x + 1 = 0 ∧ y = 0) := by omega
            have hc : ¬ (x = 0 ∧ y + 1 = 0) := by omega
            have hd : ¬ (x + 1 = 0 ∧ y + 1 = 0) := by omega
            rw [decide_eq_false ha, decide_eq_false hb, decide_eq_false hc, decide_eq_false hd]
            rfl
          rw [hsub (u - 1) (v - 1) (Or.inl rfl) (Or.inl rfl),
              hsub u (v - 1) (Or.inr rfl) (Or.inl rfl),
              hsub (u - 1) v (Or.inl rfl) (Or.inr rfl),
              hsub u v (Or.inr rfl) (Or.inr rfl)]
          rfl
      | succ m' =>
        have hM2 : 2 ≤ M := by
          have : 1 ≤ 2 ^ m' := Nat.one_le_pow m' 2 (by omega)
          show 2 ≤ 2 ^ (m' + 1)
          rw [pow_succ]; omega
        have ha_lt_b : (-(M - 1 : ℤ)) < (M - 1 : ℤ) := by omega
        have hiter := iter_Ue ha_lt_b Se (M - 1) ihS hSe_step (M - 1) (by omega)
        have hidx : M - 1 + (M - 1) + 1 = 2 ^ (m' + 1 + 1) - 1 := by omega
        rw [hidx] at hiter
        rw [hiter]
        funext u v
        simp only [Ue, ihT, sqBox, hM_int, h2M_int]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((((h | h) | h) | h) | h) <;> omega
        · intro h
          by_cases hu : u ≤ 0 <;> by_cases hv : v ≤ 0
          · left; left; left; right; omega
          · left; left; right; omega
          · left; right; omega
          · right; omega
    exact ⟨hTe_next, hSe_next⟩

-- ============================================================================
-- Section 5: Exact Cell Count, Closed Form, Recurrence, and Generating Function
-- ============================================================================

private lemma a_zero : a 0 = 1 := by decide
private lemma a_one : a 1 = 5 := by decide
private lemma a_two : a 2 = 41 := by decide

private lemma a_closed_int {n : ℕ} (hn : 1 ≤ n) : a n = 3 * (4 : ℤ) ^ n - 7 := by
  by_cases hn1 : n = 1
  · subst hn1; rw [a_one]; norm_num
  · have hn2 : 2 ≤ n := by omega
    set M : ℕ := 2 ^ (n - 1)
    have hM2 : 2 ≤ M := by
      have : 1 ≤ n - 1 := by omega
      have hpow : 2 ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) this
      simpa using hpow
    have h2n : 2 ^ n = 2 * M := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have h4n : (4 : ℤ) ^ n = 4 * (M : ℤ) ^ 2 := by
      have : (4 : ℤ) ^ n = ((2 : ℤ) ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this, show (2 : ℤ) ^ n = 2 * (M : ℤ) by exact_mod_cast h2n]
      ring
    set t : ℕ := 2 ^ n - 1
    have ht_eq : t = 2 * (M - 1) + 1 := by omega
    have hSo_eq : So (M - 1) = Uo (-(M - 1 : ℤ)) (M - 1 : ℤ) 0 := by
      unfold So
      rw [(solid_squares (n - 1)).2]
      funext u v
      exact stepEO_sqBox (by omega : (-(M - 1 : ℤ)) < (M - 1 : ℤ)) u v
    set grid : Finset (ℕ × ℕ) := Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)
    set offSet : Finset (ℕ × ℕ) :=
      grid.filter (fun p => cell 251 t ((p.1 : ℤ) - (t : ℤ)) ((p.2 : ℤ) - (t : ℤ)) = false)
    have hon_plus_off : onCount 251 t + offSet.card = (2 * t + 1) ^ 2 := by
      have htot : (∑ p ∈ grid, (if cell 251 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) then 1 else 0)) +
          (∑ p ∈ grid, (if cell 251 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = false then 1 else 0)) =
          ∑ _p ∈ grid, (1 : ℕ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        cases cell 251 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) <;> simp
      have hon_eq : onCount 251 t =
          ∑ p ∈ grid, (if cell 251 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) then 1 else 0) := by
        unfold onCount
        rw [Finset.sum_product]
      have hoff_eq : offSet.card =
          ∑ p ∈ grid, (if cell 251 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = false then 1 else 0) := by
        dsimp only [offSet]
        rw [Finset.card_filter]
      rw [hon_eq, hoff_eq, htot, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_product, Finset.card_range, sq]
    set box : Finset (ℤ × ℤ) :=
      Finset.Icc (-(M - 1 : ℤ)) (M - 2 : ℤ) ×ˢ Finset.Icc (-(M - 1 : ℤ)) (M - 2 : ℤ)
    set corners : Finset (ℤ × ℤ) :=
      {(-(M : ℤ), -(M : ℤ)), (-(M : ℤ), (M - 1 : ℤ)), ((M - 1 : ℤ), -(M : ℤ)), ((M - 1 : ℤ), (M - 1 : ℤ))}
    set src : Finset (ℤ × ℤ) := box ∪ corners
    have hdisj : Disjoint box corners := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [box, Finset.mem_product, Finset.mem_Icc] at hp1
      simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hp2
      rcases hp2 with rfl | rfl | rfl | rfl <;> omega
    have hbox_card : box.card = (2 * M - 2) ^ 2 := by
      rw [Finset.card_product, Int.card_Icc, sq]
      have : ((M - 2 : ℤ) + 1 - -(M - 1 : ℤ)).toNat = 2 * M - 2 := by omega
      rw [this]
    have hcorn_card : corners.card = 4 := by
      simp only [corners]
      rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_pair (by intro h; simp at h; omega)]
    have hsrc_card : src.card = (2 * M - 2) ^ 2 + 4 := by
      rw [Finset.card_union_of_disjoint hdisj, hbox_card, hcorn_card]
    have hmem_src_iff : ∀ u v : ℤ, (u, v) ∈ src ↔ Uo (-(M - 1 : ℤ)) (M - 1 : ℤ) 0 u v = true := by
      intro u v
      simp only [src, box, corners, Uo, sqBox, To, Finset.mem_union, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true,
        decide_eq_true_eq, Prod.mk.injEq]
      omega
    have hoff_card : offSet.card = src.card := by
      symm
      refine Finset.card_bij
        (fun q _ => ((q.1 + q.2 + 1 + (t : ℤ)).toNat, (q.1 - q.2 + (t : ℤ)).toNat)) ?_ ?_ ?_
      · intro q hq
        have hUo : Uo (-(M - 1 : ℤ)) (M - 1 : ℤ) 0 q.1 q.2 = true := (hmem_src_iff q.1 q.2).mp hq
        have hbd : -(t : ℤ) ≤ q.1 + q.2 + 1 ∧ q.1 + q.2 + 1 ≤ t ∧
                   -(t : ℤ) ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ t := by
          simp only [src, box, corners, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
            Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with ⟨h1, h2⟩ | (h | h | h | h)
          · omega
          · rw [h]; omega
          · rw [h]; omega
          · rw [h]; omega
          · rw [h]; omega
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
        rw [ht_eq, (cell_even_and_odd (M - 1)).2]
        have hx : (((q.1 + q.2 + 1 + (t : ℤ)).toNat : ℤ) - (t : ℤ)) = q.1 + q.2 + 1 := by omega
        have hy : (((q.1 - q.2 + (t : ℤ)).toNat : ℤ) - (t : ℤ)) = q.1 - q.2 := by omega
        rw [show (2 * (M - 1) + 1 : ℕ) = t from ht_eq.symm, hx, hy]
        have hpar : (q.1 + q.2 + 1 + (q.1 - q.2)) % 2 ≠ 0 := by omega
        have hu' : (q.1 + q.2 + 1 + (q.1 - q.2) - 1) / 2 = q.1 := by omega
        have hv' : (q.1 + q.2 + 1 - (q.1 - q.2) - 1) / 2 = q.2 := by omega
        rw [hu', hv', hSo_eq, hUo]
        simp [hpar]
      · intro q₁ hq₁ q₂ hq₂ heq
        have hbd1 : -(t : ℤ) ≤ q₁.1 + q₁.2 + 1 ∧ -(t : ℤ) ≤ q₁.1 - q₁.2 := by
          simp only [src, box, corners, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
            Finset.mem_insert, Finset.mem_singleton] at hq₁
          rcases hq₁ with ⟨_, _⟩ | (h | h | h | h) <;> [omega; (rw [h]; omega); (rw [h]; omega); (rw [h]; omega); (rw [h]; omega)]
        have hbd2 : -(t : ℤ) ≤ q₂.1 + q₂.2 + 1 ∧ -(t : ℤ) ≤ q₂.1 - q₂.2 := by
          simp only [src, box, corners, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
            Finset.mem_insert, Finset.mem_singleton] at hq₂
          rcases hq₂ with ⟨_, _⟩ | (h | h | h | h) <;> [omega; (rw [h]; omega); (rw [h]; omega); (rw [h]; omega); (rw [h]; omega)]
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        ext <;> omega
      · intro p hp
        rw [Finset.mem_filter] at hp
        rcases hp with ⟨hp_grid, hp_off⟩
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp_grid
        set i : ℤ := (p.1 : ℤ) - (t : ℤ)
        set j : ℤ := (p.2 : ℤ) - (t : ℤ)
        have hp_off' : cell 251 (2 * (M - 1) + 1) i j = false := by
          rw [← ht_eq]; exact hp_off
        rw [(cell_even_and_odd (M - 1)).2, Bool.not_eq_false', Bool.and_eq_true,
          decide_eq_true_eq, hSo_eq] at hp_off'
        refine ⟨((i + j - 1) / 2, (i - j - 1) / 2), (hmem_src_iff _ _).mpr hp_off'.2, ?_⟩
        ext <;> dsimp only <;> omega
    have hon_int : (onCount 251 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - ((2 * (M : ℤ) - 2) ^ 2 + 4) := by
      have h1 : (onCount 251 t : ℤ) + (offSet.card : ℤ) = (2 * (t : ℤ) + 1) ^ 2 := by
        exact_mod_cast hon_plus_off
      have h2 : (offSet.card : ℤ) = (2 * (M : ℤ) - 2) ^ 2 + 4 := by
        rw [hoff_card, hsrc_card]
        have hM_sub : ((2 * M - 2 : ℕ) : ℤ) = 2 * (M : ℤ) - 2 := by omega
        push_cast
        rw [hM_sub]
      omega
    unfold a
    rw [show 2 ^ n - 1 = t from rfl, hon_int, h4n, show (t : ℤ) = 2 * (M : ℤ) - 1 by omega]
    ring

private lemma a_closed_rat (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 3 * (4 : ℚ) ^ n - 7 := by
  exact_mod_cast a_closed_int hn

private lemma a_rec_rat (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = 5 * (a (n - 1) : ℚ) - 4 * (a (n - 2) : ℚ) := by
  rw [a_closed_rat n (by omega), a_closed_rat (n - 1) (by omega), a_closed_rat (n - 2) (by omega)]
  have h1 : (4 : ℚ) ^ (n - 1) = 4 * (4 : ℚ) ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
  have h2 : (4 : ℚ) ^ n = 16 * (4 : ℚ) ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]; ring
  rw [h1, h2]
  ring

private lemma a_gf :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X) : PowerSeries ℚ) =
      1 + 20 * PowerSeries.X ^ 2 := by
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hstep : F * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X) : PowerSeries ℚ) =
      F - PowerSeries.C 5 * (PowerSeries.X * F) +
        PowerSeries.C 4 * (PowerSeries.X * (PowerSeries.X * F)) := by
    rw [show PowerSeries.C (5 : ℚ) = (5 : PowerSeries ℚ) from rfl,
        show PowerSeries.C (4 : ℚ) = (4 : PowerSeries ℚ) from rfl]
    ring
  rw [hstep, show (20 : PowerSeries ℚ) = PowerSeries.C 20 from rfl]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow]
  cases k with
  | zero =>
    simp only [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mk, F, a_zero]
    norm_num
  | succ k =>
    cases k with
    | zero =>
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_mk, F, a_zero]
      norm_num [a_one]
    | succ k =>
      cases k with
      | zero =>
        simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, F, a_zero, a_one]
        norm_num [a_two]
      | succ k =>
        have hne0 : k + 3 ≠ 0 := by omega
        have hne2 : k + 3 ≠ 2 := by omega
        simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, F, hne0, hne2, ↓reduceIte]
        have hrec := a_rec_rat (k + 3) (by omega)
        simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hrec
        linarith

theorem main_proof :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (4 : ℚ) ^ n - 7) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X) : PowerSeries ℚ) =
      1 + 20 * PowerSeries.X ^ 2) :=
  ⟨a_closed_rat, a_rec_rat, a_gf⟩

end OeisA271017

theorem OMA.solution : type_of% @OMA.S_oeis_a271017.main :=
  OeisA271017.main_proof
