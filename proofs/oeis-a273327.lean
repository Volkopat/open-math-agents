import OMAStatements.S_oeis_a273327

namespace OeisA273327

open OMA.S_oeis_a273327

-- ============================================================================
-- Section 1: Rule 646 Time-Halving to Rule 526 on 2Z x 2Z
-- ============================================================================

private def cnt526 (P : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (P (x + 1) y).toNat + (P (x - 1) y).toNat + (P x (y + 1)).toNat + (P x (y - 1)).toNat

private def step526 (P : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  if P x y then
    (cnt526 P x y == 0) || (cnt526 P x y == 1) || (cnt526 P x y == 4)
  else
    cnt526 P x y == 1

private lemma step526_congr {P Q : ℤ → ℤ → Bool} {x y : ℤ}
    (hc : P x y = Q x y)
    (h1 : P (x + 1) y = Q (x + 1) y)
    (h2 : P (x - 1) y = Q (x - 1) y)
    (h3 : P x (y + 1) = Q x (y + 1))
    (h4 : P x (y - 1) = Q x (y - 1)) :
    step526 P x y = step526 Q x y := by
  simp only [step526, cnt526, hc, h1, h2, h3, h4]

private lemma step526_of_eq {P Q : ℤ → ℤ → Bool} {x y x' y' : ℤ}
    (hc : P x y = Q x' y')
    (hcnt : cnt526 P x y = cnt526 Q x' y') :
    step526 P x y = step526 Q x' y' := by
  simp only [step526, hc, hcnt]

private lemma step526_shift (P : ℤ → ℤ → Bool) (dx dy x y : ℤ) :
    step526 (fun u v => P (u - dx) (v - dy)) x y = step526 P (x - dx) (y - dy) := by
  simp only [step526, cnt526, show x + 1 - dx = x - dx + 1 by ring,
    show x - 1 - dx = x - dx - 1 by ring, show y + 1 - dy = y - dy + 1 by ring,
    show y - 1 - dy = y - dy - 1 by ring]

private lemma step526_shift_x (P : ℤ → ℤ → Bool) (dx x y : ℤ) :
    step526 (fun u v => P (u - dx) v) x y = step526 P (x - dx) y := by
  simpa using step526_shift P dx 0 x y

private lemma cell_succ (code t : ℕ) (i j : ℤ) :
    cell code (t + 1) i j =
      code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
        (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat + (cell code t i (j - 1)).toNat)) :=
  rfl

private def A : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | k + 1 => step526 (A k)

private lemma bit646_zero (c : Bool) :
    (646 : ℕ).testBit (c.toNat + 2 * (0 + 0 + 0 + 0)) = c := by
  cases c <;> decide

private lemma bit646_xor_h (a b : Bool) :
    (646 : ℕ).testBit (0 + 2 * (b.toNat + a.toNat + 0 + 0)) = xor a b := by
  cases a <;> cases b <;> decide

private lemma bit646_xor_v (a b : Bool) :
    (646 : ℕ).testBit (0 + 2 * (0 + 0 + b.toNat + a.toNat)) = xor a b := by
  cases a <;> cases b <;> decide

private lemma bit646_oo (a b c d : Bool) :
    (646 : ℕ).testBit (0 + 2 * ((xor b d).toNat + (xor a c).toNat +
      (xor c d).toNat + (xor a b).toNat)) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma bit646_oe (a b : Bool) :
    (646 : ℕ).testBit ((xor a b).toNat + 2 * (b.toNat + a.toNat + 0 + 0)) = false := by
  cases a <;> cases b <;> decide

private lemma bit646_eo (a b : Bool) :
    (646 : ℕ).testBit ((xor a b).toNat + 2 * (0 + 0 + b.toNat + a.toNat)) = false := by
  cases a <;> cases b <;> decide

private lemma bit646_ee (c n1 n2 n3 n4 : Bool) :
    (646 : ℕ).testBit (c.toNat + 2 * ((xor c n1).toNat + (xor n2 c).toNat +
      (xor c n3).toNat + (xor n4 c).toNat)) =
      (if c then
        (n1.toNat + n2.toNat + n3.toNat + n4.toNat == 0) ||
        (n1.toNat + n2.toNat + n3.toNat + n4.toNat == 1) ||
        (n1.toNat + n2.toNat + n3.toNat + n4.toNat == 4)
      else
        n1.toNat + n2.toNat + n3.toNat + n4.toNat == 1) := by
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> decide

private lemma cell_even_and_odd :
    ∀ k : ℕ,
      (∀ i j : ℤ, cell 646 (2 * k) i j =
        (decide (i % 2 = 0 ∧ j % 2 = 0) && A k (i / 2) (j / 2))) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x) (2 * y) = A k x y) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x + 1) (2 * y) = xor (A k x y) (A k (x + 1) y)) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x) (2 * y + 1) = xor (A k x y) (A k x (y + 1))) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x + 1) (2 * y + 1) = false) := by
  have heven_to_odd : ∀ k : ℕ,
      (∀ i j : ℤ, cell 646 (2 * k) i j =
        (decide (i % 2 = 0 ∧ j % 2 = 0) && A k (i / 2) (j / 2))) →
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x) (2 * y) = A k x y) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x + 1) (2 * y) = xor (A k x y) (A k (x + 1) y)) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x) (2 * y + 1) = xor (A k x y) (A k x (y + 1))) ∧
      (∀ x y : ℤ, cell 646 (2 * k + 1) (2 * x + 1) (2 * y + 1) = false) := by
    intro k hev
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y
      simp only [cell, hev]
      have h0 : (2 * x) % 2 = 0 ∧ (2 * y) % 2 = 0 := by omega
      have h1 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y) % 2 = 0) := by omega
      have h2 : ¬ ((2 * x - 1) % 2 = 0 ∧ (2 * y) % 2 = 0) := by omega
      have h3 : ¬ ((2 * x) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h4 : ¬ ((2 * x) % 2 = 0 ∧ (2 * y - 1) % 2 = 0) := by omega
      rw [decide_eq_true h0, decide_eq_false h1, decide_eq_false h2,
        decide_eq_false h3, decide_eq_false h4]
      simp only [Bool.true_and, Bool.false_and, Bool.toNat_false,
        show (2 * x) / 2 = x by omega, show (2 * y) / 2 = y by omega]
      exact bit646_zero (A k x y)
    · intro x y
      simp only [cell, hev]
      have h0 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y) % 2 = 0) := by omega
      have h1 : (2 * x + 1 + 1) % 2 = 0 ∧ (2 * y) % 2 = 0 := by omega
      have h2 : (2 * x + 1 - 1) % 2 = 0 ∧ (2 * y) % 2 = 0 := by omega
      have h3 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h4 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y - 1) % 2 = 0) := by omega
      rw [decide_eq_false h0, decide_eq_true h1, decide_eq_true h2,
        decide_eq_false h3, decide_eq_false h4]
      simp only [Bool.true_and, Bool.false_and, Bool.toNat_false,
        show (2 * x + 1 + 1) / 2 = x + 1 by omega, show (2 * x + 1 - 1) / 2 = x by omega,
        show (2 * y) / 2 = y by omega]
      exact bit646_xor_h (A k x y) (A k (x + 1) y)
    · intro x y
      simp only [cell, hev]
      have h0 : ¬ ((2 * x) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h1 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h2 : ¬ ((2 * x - 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h3 : (2 * x) % 2 = 0 ∧ (2 * y + 1 + 1) % 2 = 0 := by omega
      have h4 : (2 * x) % 2 = 0 ∧ (2 * y + 1 - 1) % 2 = 0 := by omega
      rw [decide_eq_false h0, decide_eq_false h1, decide_eq_false h2,
        decide_eq_true h3, decide_eq_true h4]
      simp only [Bool.true_and, Bool.false_and, Bool.toNat_false,
        show (2 * x) / 2 = x by omega, show (2 * y + 1 + 1) / 2 = y + 1 by omega,
        show (2 * y + 1 - 1) / 2 = y by omega]
      exact bit646_xor_v (A k x y) (A k x (y + 1))
    · intro x y
      simp only [cell, hev]
      have h0 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h1 : ¬ ((2 * x + 1 + 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h2 : ¬ ((2 * x + 1 - 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
      have h3 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y + 1 + 1) % 2 = 0) := by omega
      have h4 : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y + 1 - 1) % 2 = 0) := by omega
      rw [decide_eq_false h0, decide_eq_false h1, decide_eq_false h2,
        decide_eq_false h3, decide_eq_false h4]
      simp only [Bool.false_and, Bool.toNat_false]
      rfl
  intro k
  induction k with
  | zero =>
    have hev0 : ∀ i j : ℤ, cell 646 (2 * 0) i j =
        (decide (i % 2 = 0 ∧ j % 2 = 0) && A 0 (i / 2) (j / 2)) := by
      intro i j
      simp only [cell, A]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    exact ⟨hev0, heven_to_odd 0 hev0⟩
  | succ k ih =>
    obtain ⟨_, h_ee, h_oe, h_eo, h_oo⟩ := ih
    have hev_succ : ∀ i j : ℤ, cell 646 (2 * (k + 1)) i j =
        (decide (i % 2 = 0 ∧ j % 2 = 0) && A (k + 1) (i / 2) (j / 2)) := by
      intro i j
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      set x : ℤ := i / 2
      set y : ℤ := j / 2
      have hi : i = 2 * x ∨ i = 2 * x + 1 := by omega
      have hj : j = 2 * y ∨ j = 2 * y + 1 := by omega
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · rw [hi, hj, cell_succ]
        rw [show 2 * x - 1 = 2 * (x - 1) + 1 by ring,
            show 2 * y - 1 = 2 * (y - 1) + 1 by ring,
            h_ee x y, h_oe x y, h_oe (x - 1) y, h_eo x y, h_eo x (y - 1),
            show x - 1 + 1 = x by ring, show y - 1 + 1 = y by ring]
        have hpar : (2 * x) % 2 = 0 ∧ (2 * y) % 2 = 0 := by omega
        rw [decide_eq_true hpar, Bool.true_and]
        exact bit646_ee (A k x y) (A k (x + 1) y) (A k (x - 1) y) (A k x (y + 1)) (A k x (y - 1))
      · rw [hi, hj, cell_succ]
        rw [show 2 * x - 1 = 2 * (x - 1) + 1 by ring,
            show 2 * y + 1 + 1 = 2 * (y + 1) by ring,
            show 2 * y + 1 - 1 = 2 * y by ring,
            h_eo x y, h_oo x y, h_oo (x - 1) y, h_ee x (y + 1), h_ee x y]
        have hpar : ¬ ((2 * x) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
        rw [decide_eq_false hpar, Bool.false_and]
        simp only [Bool.toNat_false]
        exact bit646_eo (A k x y) (A k x (y + 1))
      · rw [hi, hj, cell_succ]
        rw [show 2 * x + 1 + 1 = 2 * (x + 1) by ring,
            show 2 * x + 1 - 1 = 2 * x by ring,
            show 2 * y - 1 = 2 * (y - 1) + 1 by ring,
            h_oe x y, h_ee (x + 1) y, h_ee x y, h_oo x y, h_oo x (y - 1)]
        have hpar : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y) % 2 = 0) := by omega
        rw [decide_eq_false hpar, Bool.false_and]
        simp only [Bool.toNat_false]
        exact bit646_oe (A k x y) (A k (x + 1) y)
      · rw [hi, hj, cell_succ]
        rw [show 2 * x + 1 + 1 = 2 * (x + 1) by ring,
            show 2 * x + 1 - 1 = 2 * x by ring,
            show 2 * y + 1 + 1 = 2 * (y + 1) by ring,
            show 2 * y + 1 - 1 = 2 * y by ring,
            h_oo x y, h_eo (x + 1) y, h_eo x y, h_oe x (y + 1), h_oe x y]
        have hpar : ¬ ((2 * x + 1) % 2 = 0 ∧ (2 * y + 1) % 2 = 0) := by omega
        rw [decide_eq_false hpar, Bool.false_and]
        simp only [Bool.toNat_false]
        exact bit646_oo (A k x y) (A k (x + 1) y) (A k x (y + 1)) (A k (x + 1) (y + 1))
    exact ⟨hev_succ, heven_to_odd (k + 1) hev_succ⟩

-- ============================================================================
-- Section 2: Global Invariants of A and the 2-Adic Still Life F
-- ============================================================================

private lemma A_invariants :
    ∀ k : ℕ,
      (∀ x y : ℤ, A k x y = true → (x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ k) ∧
      (∀ x y : ℤ, A k (-x) y = A k x y) ∧
      (∀ x y : ℤ, A k x (-y) = A k x y) ∧
      (∀ x y : ℤ, A k y x = A k x y) ∧
      (A k 0 0 = true) ∧
      (∀ x : ℤ, x ≠ 0 → A k x x = false) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, by decide, ?_⟩
    · intro x y h; simp only [A, decide_eq_true_eq] at h; omega
    · intro x y; simp only [A]; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · intro x y; simp only [A]; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · intro x y; simp only [A]; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · intro x hx; simp only [A, decide_eq_false_iff_not]; omega
  | succ k ih =>
    obtain ⟨hcone, hsx, hsy, hst, horig, hdiag⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      by_contra hgt
      have hfar : ∀ u v : ℤ, (k : ℤ) < (u.natAbs : ℤ) + (v.natAbs : ℤ) → A k u v = false := by
        intro u v huv
        rw [Bool.eq_false_iff]
        intro ht
        have := hcone u v ht
        omega
      have hc : A k x y = false := hfar x y (by omega)
      have h1 : A k (x + 1) y = false := hfar (x + 1) y (by omega)
      have h2 : A k (x - 1) y = false := hfar (x - 1) y (by omega)
      have h3 : A k x (y + 1) = false := hfar x (y + 1) (by omega)
      have h4 : A k x (y - 1) = false := hfar x (y - 1) (by omega)
      simp only [A, step526, cnt526, hc, h1, h2, h3, h4] at h
      exact Bool.false_ne_true h
    · intro x y
      apply step526_of_eq (hsx x y)
      simp only [cnt526]
      have e1 : -x + 1 = -(x - 1) := by ring
      have e2 : -x - 1 = -(x + 1) := by ring
      rw [e1, e2, hsx (x - 1) y, hsx (x + 1) y, hsx x (y + 1), hsx x (y - 1)]
      omega
    · intro x y
      apply step526_of_eq (hsy x y)
      simp only [cnt526]
      have e1 : -y + 1 = -(y - 1) := by ring
      have e2 : -y - 1 = -(y + 1) := by ring
      rw [e1, e2, hsy (x + 1) y, hsy (x - 1) y, hsy x (y - 1), hsy x (y + 1)]
      omega
    · intro x y
      apply step526_of_eq (hst x y)
      simp only [cnt526]
      rw [hst x (y + 1), hst x (y - 1), hst (x + 1) y, hst (x - 1) y]
      omega
    · simp only [A, step526, cnt526, horig]
      have h1 : A k (0 - 1) 0 = A k 1 0 := by rw [show (0 - 1 : ℤ) = -1 by ring, hsx 1 0]
      have h2 : A k 0 1 = A k 1 0 := hst 1 0
      have h3 : A k 0 (0 - 1) = A k 1 0 := by rw [show (0 - 1 : ℤ) = -1 by ring, hsy 0 1, hst 1 0]
      rw [zero_add, h1, h2, h3]
      cases A k 1 0 <;> rfl
    · intro x hx
      simp only [A, step526, cnt526, hdiag x hx]
      rw [hst (x + 1) x, hst (x - 1) x]
      cases A k (x + 1) x <;> cases A k (x - 1) x <;> rfl

private lemma A_cone {k : ℕ} {x y : ℤ} (h : A k x y = true) : (x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ k :=
  (A_invariants k).1 x y h

private lemma A_cone_false {k : ℕ} {x y : ℤ} (h : (k : ℤ) < (x.natAbs : ℤ) + (y.natAbs : ℤ)) : A k x y = false := by
  rw [Bool.eq_false_iff]
  intro ht
  have := A_cone ht
  omega

private lemma A_sym_x (k : ℕ) (x y : ℤ) : A k (-x) y = A k x y := (A_invariants k).2.1 x y
private lemma A_sym_y (k : ℕ) (x y : ℤ) : A k x (-y) = A k x y := (A_invariants k).2.2.1 x y
private lemma A_sym_t (k : ℕ) (x y : ℤ) : A k y x = A k x y := (A_invariants k).2.2.2.1 x y
private lemma A_origin (k : ℕ) : A k 0 0 = true := (A_invariants k).2.2.2.2.1

private lemma A_diag (k : ℕ) {x y : ℤ} (hxy : (x.natAbs : ℤ) = (y.natAbs : ℤ)) (hx : x ≠ 0) : A k x y = false := by
  have hcases : y = x ∨ y = -x := by omega
  rcases hcases with hy | hy
  · rw [hy]; exact (A_invariants k).2.2.2.2.2 x hx
  · rw [hy, A_sym_y]
    exact (A_invariants k).2.2.2.2.2 x hx

-- Computable 2-adic valuation on N (so base cases reduce in kernel by decide)
private def v2Nat : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + v2Nat ((n + 1) / 2) else 0
termination_by n => n
decreasing_by omega

private lemma v2Nat_dvd_and_not_dvd :
    ∀ n : ℕ, n ≠ 0 → 2 ^ v2Nat n ∣ n ∧ ¬ 2 ^ (v2Nat n + 1) ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact absurd rfl hn
    | succ m =>
      rw [v2Nat]
      by_cases hev : (m + 1) % 2 = 0
      · rw [if_pos hev]
        set q : ℕ := (m + 1) / 2
        have hq_lt : q < m + 1 := by omega
        have hq_ne : q ≠ 0 := by omega
        have hq_mul : 2 * q = m + 1 := by omega
        obtain ⟨hd1, hd2⟩ := ih q hq_lt hq_ne
        constructor
        · rw [show 1 + v2Nat q = v2Nat q + 1 by omega, pow_succ', ← hq_mul]
          exact Nat.mul_dvd_mul_left 2 hd1
        · rw [show 1 + v2Nat q + 1 = (v2Nat q + 1) + 1 by omega, pow_succ', ← hq_mul]
          intro hbad
          exact hd2 ((Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp hbad)
      · rw [if_neg hev]
        constructor
        · simp
        · intro hbad
          obtain ⟨q, hq⟩ := hbad
          omega

private lemma v2Nat_eq_of_dvd {n e : ℕ} (hn : n ≠ 0)
    (h1 : 2 ^ e ∣ n) (h2 : ¬ 2 ^ (e + 1) ∣ n) : v2Nat n = e := by
  obtain ⟨hk1, hk2⟩ := v2Nat_dvd_and_not_dvd n hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hk2 (dvd_trans (Nat.pow_dvd_pow 2 (by omega : v2Nat n + 1 ≤ e)) h1)
  · exact h2 (dvd_trans (Nat.pow_dvd_pow 2 (by omega : e + 1 ≤ v2Nat n)) hk1)

private lemma v2Nat_pow_two (m : ℕ) : v2Nat (2 ^ m) = m := by
  apply v2Nat_eq_of_dvd (Nat.ne_of_gt (Nat.two_pow_pos m)) (dvd_refl _)
  intro hbad
  have hle := Nat.le_of_dvd (Nat.two_pow_pos m) hbad
  rw [pow_succ] at hle
  have := Nat.two_pow_pos m
  omega

private lemma v2Nat_lt_of_lt_pow_two {a m : ℕ} (ha0 : 0 < a) (ham : a < 2 ^ m) :
    v2Nat a < m := by
  by_contra hge
  have hd : 2 ^ m ∣ a :=
    dvd_trans (Nat.pow_dvd_pow 2 (by omega : m ≤ v2Nat a))
      (v2Nat_dvd_and_not_dvd a (by omega)).1
  have hle := Nat.le_of_dvd ha0 hd
  omega

private lemma v2Nat_sub_pow_two {a m : ℕ} (ha0 : 0 < a) (ha_lt : a < 2 ^ (m + 1))
    (ha_ne : a ≠ 2 ^ m) :
    v2Nat a < m ∧ v2Nat ((a : ℤ) - ((2 ^ m : ℕ) : ℤ)).natAbs = v2Nat a := by
  have he_lt : v2Nat a < m := by
    by_contra hge
    have hd : 2 ^ m ∣ a :=
      dvd_trans (Nat.pow_dvd_pow 2 (by omega : m ≤ v2Nat a))
        (v2Nat_dvd_and_not_dvd a (by omega)).1
    rcases hd with ⟨q, hq⟩
    have hpow_pos := Nat.two_pow_pos m
    rw [pow_succ] at ha_lt
    have hq1 : q = 1 := by nlinarith
    rw [hq1, mul_one] at hq
    exact ha_ne hq
  refine ⟨he_lt, ?_⟩
  set e : ℕ := v2Nat a
  obtain ⟨ha_d1, ha_d2⟩ := v2Nat_dvd_and_not_dvd a (by omega)
  have hp_d1 : 2 ^ e ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
  have hp_d2 : 2 ^ (e + 1) ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
  set b : ℕ := ((a : ℤ) - ((2 ^ m : ℕ) : ℤ)).natAbs
  have hb_ne : b ≠ 0 := by
    intro h0
    have : (a : ℤ) - ((2 ^ m : ℕ) : ℤ) = 0 := Int.natAbs_eq_zero.mp h0
    exact ha_ne (by omega)
  apply v2Nat_eq_of_dvd hb_ne
  · rcases lt_or_gt_of_ne ha_ne with hlt | hgt
    · have hb_eq : b = 2 ^ m - a := by omega
      rw [hb_eq]
      exact Nat.dvd_sub hp_d1 ha_d1
    · have hb_eq : b = a - 2 ^ m := by omega
      rw [hb_eq]
      exact Nat.dvd_sub ha_d1 hp_d1
  · intro hbad
    rcases lt_or_gt_of_ne ha_ne with hlt | hgt
    · have hb_eq : b = 2 ^ m - a := by omega
      rw [hb_eq] at hbad
      have hbad' : 2 ^ (e + 1) ∣ a := by
        rw [show a = 2 ^ m - (2 ^ m - a) by omega]
        exact Nat.dvd_sub hp_d2 hbad
      exact ha_d2 hbad'
    · have hb_eq : b = a - 2 ^ m := by omega
      rw [hb_eq] at hbad
      have hbad' : 2 ^ (e + 1) ∣ a := by
        rw [show a = 2 ^ m + (a - 2 ^ m) by omega]
        exact Nat.dvd_add hp_d2 hbad
      exact ha_d2 hbad'

private def F (x y : ℤ) : Bool :=
  decide ((x + y) % 2 ≠ 0) ||
  (decide (x % 4 = 0 ∧ y % 4 = 0) &&
    decide (x = 0 ∨ y = 0 ∨ v2Nat x.natAbs ≠ v2Nat y.natAbs))

private lemma F_sym_x (x y : ℤ) : F (-x) y = F x y := by
  simp only [F, Int.natAbs_neg]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro (h | ⟨⟨h1, h2⟩, h3⟩)
  · left; omega
  · right; refine ⟨⟨by omega, h2⟩, ?_⟩; rcases h3 with h3 | h3 | h3 <;> [left; right; right] <;> [omega; exact Or.inl h3; exact Or.inr h3]
  · left; omega
  · right; refine ⟨⟨by omega, h2⟩, ?_⟩; rcases h3 with h3 | h3 | h3 <;> [left; right; right] <;> [omega; exact Or.inl h3; exact Or.inr h3]

private lemma F_sym_y (x y : ℤ) : F x (-y) = F x y := by
  simp only [F, Int.natAbs_neg]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro (h | ⟨⟨h1, h2⟩, h3⟩)
  · left; omega
  · right; refine ⟨⟨h1, by omega⟩, ?_⟩; rcases h3 with h3 | h3 | h3 <;> [left; right; right] <;> [exact h3; exact Or.inl (by omega); exact Or.inr h3]
  · left; omega
  · right; refine ⟨⟨h1, by omega⟩, ?_⟩; rcases h3 with h3 | h3 | h3 <;> [left; right; right] <;> [exact h3; exact Or.inl (by omega); exact Or.inr h3]

private lemma F_sym_t (x y : ℤ) : F y x = F x y := by
  simp only [F]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro (h | ⟨⟨h1, h2⟩, h3⟩)
  · left; omega
  · right; refine ⟨⟨h2, h1⟩, ?_⟩; rcases h3 with h3 | h3 | h3 <;> [right; left; right] <;> [exact Or.inl h3; exact h3; exact Or.inr (Ne.symm h3)]
  · left; omega
  · right; refine ⟨⟨h2, h1⟩, ?_⟩; rcases h3 with h3 | h3 | h3 <;> [right; left; right] <;> [exact Or.inl h3; exact h3; exact Or.inr (Ne.symm h3)]

private lemma F_odd {x y : ℤ} (h : (x + y) % 2 ≠ 0) : F x y = true := by
  simp only [F, decide_eq_true h, Bool.true_or]

private lemma F_diag {x y : ℤ} (hxy : (x.natAbs : ℤ) = (y.natAbs : ℤ)) (hx : x ≠ 0) : F x y = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have habs : x.natAbs = y.natAbs := by omega
  rcases h with hodd | ⟨_, h3⟩
  · omega
  · rcases h3 with h3 | h3 | h3
    · exact hx h3
    · omega
    · exact h3 (congrArg v2Nat habs)

private lemma F_still_life (x y : ℤ) : step526 F x y = F x y := by
  by_cases hpar : (x + y) % 2 = 0
  · have h1 : F (x + 1) y = true := F_odd (by omega)
    have h2 : F (x - 1) y = true := F_odd (by omega)
    have h3 : F x (y + 1) = true := F_odd (by omega)
    have h4 : F x (y - 1) = true := F_odd (by omega)
    simp only [step526, cnt526, h1, h2, h3, h4]
    cases F x y <;> rfl
  · have hc : F x y = true := F_odd hpar
    have hmul4 : ∀ u v : ℤ, (u + v) % 2 = 0 → F u v = true → u % 4 = 0 ∧ v % 4 = 0 := by
      intro u v huv hf
      simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
      rcases hf with hodd | ⟨h4, _⟩
      · omega
      · exact h4
    have hcnt_le : cnt526 F x y ≤ 1 := by
      simp only [cnt526]
      by_cases h1 : F (x + 1) y = true <;>
      by_cases h2 : F (x - 1) y = true <;>
      by_cases h3 : F x (y + 1) = true <;>
      by_cases h4 : F x (y - 1) = true
      all_goals
        simp only [h1, h2, h3, h4]
      all_goals
        try (have := hmul4 (x + 1) y (by omega) h1)
        try (have := hmul4 (x - 1) y (by omega) h2)
        try (have := hmul4 x (y + 1) (by omega) h3)
        try (have := hmul4 x (y - 1) (by omega) h4)
        try omega
        try decide
    simp only [step526, hc, ite_true]
    have h01 : cnt526 F x y = 0 ∨ cnt526 F x y = 1 := by omega
    rcases h01 with h | h <;> simp [h]

private lemma F_pow2_bd {m : ℕ} (hm : 2 ≤ m) {x y : ℤ} (hxy : (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ m : ℕ)) :
    F x y = decide (x = 0 ∨ y = 0) := by
  have hd4 : (4 : ℤ) ∣ (2 ^ m : ℕ) := by
    have : 2 ^ 2 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm
    exact_mod_cast this
  rcases hd4 with ⟨qd, hqd⟩
  have hev : (x + y) % 2 = 0 := by omega
  by_cases h0 : x = 0 ∨ y = 0
  · rw [decide_eq_true h0]
    simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rcases h0 with rfl | rfl
    · left; rfl
    · right; left; rfl
  · rw [decide_eq_false h0, Bool.eq_false_iff]
    intro hf
    simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
    rcases hf with hodd | ⟨_, h3⟩
    · omega
    · rcases h3 with hx | hy | hv
      · exact h0 (Or.inl hx)
      · exact h0 (Or.inr hy)
      · have hxpos : 0 < x.natAbs := Int.natAbs_pos.mpr (fun hx => h0 (Or.inl hx))
        have hypos : 0 < y.natAbs := Int.natAbs_pos.mpr (fun hy => h0 (Or.inr hy))
        have hsum : x.natAbs + y.natAbs = 2 ^ m := by omega
        have hxlt : x.natAbs < 2 ^ m := by omega
        have hsub := (v2Nat_sub_pow_two (m := m) hxpos (by rw [pow_succ]; omega) (by omega)).2
        have habs_eq : ((x.natAbs : ℤ) - ((2 ^ m : ℕ) : ℤ)).natAbs = y.natAbs := by omega
        rw [habs_eq] at hsub
        exact hv hsub.symm

private lemma F_shift {m : ℕ} (hm : 2 ≤ m) {x y : ℤ}
    (hcone : (y.natAbs : ℤ) < x) (hlo : (2 ^ m : ℕ) < x + (y.natAbs : ℤ)) (hhi : x + (y.natAbs : ℤ) ≤ 2 * (2 ^ m : ℕ)) :
    F x y = F (x - (2 ^ m : ℕ)) y := by
  set d : ℕ := 2 ^ m
  have hd4 : (4 : ℤ) ∣ (d : ℤ) := by
    have : 2 ^ 2 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm
    exact_mod_cast this
  rcases hd4 with ⟨qd, hqd⟩
  by_cases hpar : (x + y) % 2 ≠ 0
  · rw [F_odd hpar, F_odd (by omega)]
  · push Not at hpar
    by_cases h4 : x % 4 = 0 ∧ y % 4 = 0
    · have h4' : (x - (d : ℤ)) % 4 = 0 ∧ y % 4 = 0 := ⟨by omega, h4.2⟩
      have hpar' : (x - (d : ℤ) + y) % 2 = 0 := by omega
      simp only [F, decide_eq_false (show ¬ ((x + y) % 2 ≠ 0) by omega),
        decide_eq_false (show ¬ ((x - (d : ℤ) + y) % 2 ≠ 0) by omega),
        decide_eq_true h4, decide_eq_true h4', Bool.false_or, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      by_cases hy0 : y = 0
      · simp [hy0]
      · by_cases hxd : x = (d : ℤ)
        · subst hxd
          have hylt : y.natAbs < 2 ^ m := by omega
          have hypos : 0 < y.natAbs := Int.natAbs_pos.mpr hy0
          have hv_lt : v2Nat y.natAbs < m := v2Nat_lt_of_lt_pow_two hypos hylt
          have hv_d : v2Nat ((d : ℤ)).natAbs = m := by
            rw [Int.natAbs_natCast]; exact v2Nat_pow_two m
          simp only [sub_self, true_or, iff_true]
          right; right; rw [hv_d]; omega
        · by_cases hx2d : x = 2 * (d : ℤ)
          · omega
          · have hx_pos : 0 < x.natAbs := by omega
            have hx_lt : x.natAbs < 2 ^ (m + 1) := by rw [pow_succ]; omega
            have hx_ne : x.natAbs ≠ 2 ^ m := by omega
            have hv := (v2Nat_sub_pow_two (m := m) hx_pos hx_lt hx_ne).2
            have heq_abs : ((x.natAbs : ℤ) - ((2 ^ m : ℕ) : ℤ)).natAbs = (x - (d : ℤ)).natAbs := by
              have hxnn : (x.natAbs : ℤ) = x := by omega
              rw [hxnn]
            rw [heq_abs] at hv
            have hne1 : x ≠ 0 := by omega
            have hne2 : x - (d : ℤ) ≠ 0 := by omega
            simp only [hne1, hne2, hy0, false_or, hv]
    · have h4' : ¬ ((x - (d : ℤ)) % 4 = 0 ∧ y % 4 = 0) := by omega
      simp only [F, decide_eq_false (show ¬ ((x + y) % 2 ≠ 0) by omega),
        decide_eq_false (show ¬ ((x - (d : ℤ) + y) % 2 ≠ 0) by omega),
        decide_eq_false h4, decide_eq_false h4', Bool.false_or, Bool.false_and]

-- ============================================================================
-- Section 3: Unified Configuration UG and Simultaneous Doubling Induction
-- ============================================================================

private def UG (d : ℤ) (P : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  if (x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ d then F x y
  else if (y.natAbs : ℤ) < x then P (x - d) y
  else if (y.natAbs : ℤ) < -x then P (x + d) y
  else if (x.natAbs : ℤ) < y then P x (y - d)
  else if (x.natAbs : ℤ) < -y then P x (y + d)
  else false

private lemma UG_sym_x (d : ℤ) {P : ℤ → ℤ → Bool}
    (hsx : ∀ u v, P (-u) v = P u v) (x y : ℤ) :
    UG d P (-x) y = UG d P x y := by
  simp only [UG, Int.natAbs_neg, neg_neg]
  split_ifs
  all_goals first
    | omega
    | exact F_sym_x x y
    | (rw [show -x - d = -(x + d) by ring, hsx])
    | (rw [show -x + d = -(x - d) by ring, hsx])
    | exact hsx x (y - d)
    | exact hsx x (y + d)
    | rfl

private lemma UG_sym_y (d : ℤ) {P : ℤ → ℤ → Bool}
    (hsy : ∀ u v, P u (-v) = P u v) (x y : ℤ) :
    UG d P x (-y) = UG d P x y := by
  simp only [UG, Int.natAbs_neg, neg_neg]
  split_ifs
  all_goals first
    | omega
    | exact F_sym_y x y
    | exact hsy (x - d) y
    | exact hsy (x + d) y
    | (rw [show -y - d = -(y + d) by ring, hsy])
    | (rw [show -y + d = -(y - d) by ring, hsy])
    | rfl

private lemma UG_sym_t (d : ℤ) {P : ℤ → ℤ → Bool}
    (hst : ∀ u v, P v u = P u v) (x y : ℤ) :
    UG d P y x = UG d P x y := by
  simp only [UG]
  split_ifs
  all_goals first
    | exact F_sym_t x y
    | exact hst x (y - d)
    | exact hst x (y + d)
    | exact hst (x - d) y
    | exact hst (x + d) y
    | rfl
    | omega

private lemma step526_sym_x {P : ℤ → ℤ → Bool} (hsx : ∀ u v, P (-u) v = P u v) (x y : ℤ) :
    step526 P (-x) y = step526 P x y := by
  apply step526_of_eq (hsx x y)
  simp only [cnt526]
  rw [show -x + 1 = -(x - 1) by ring, show -x - 1 = -(x + 1) by ring,
    hsx (x - 1) y, hsx (x + 1) y, hsx x (y + 1), hsx x (y - 1)]
  omega

private lemma step526_sym_y {P : ℤ → ℤ → Bool} (hsy : ∀ u v, P u (-v) = P u v) (x y : ℤ) :
    step526 P x (-y) = step526 P x y := by
  apply step526_of_eq (hsy x y)
  simp only [cnt526]
  rw [show -y + 1 = -(y - 1) by ring, show -y - 1 = -(y + 1) by ring,
    hsy (x + 1) y, hsy (x - 1) y, hsy x (y - 1), hsy x (y + 1)]
  omega

private lemma step526_sym_t {P : ℤ → ℤ → Bool} (hst : ∀ u v, P v u = P u v) (x y : ℤ) :
    step526 P y x = step526 P x y := by
  apply step526_of_eq (hst x y)
  simp only [cnt526]
  rw [hst x (y + 1), hst x (y - 1), hst (x + 1) y, hst (x - 1) y]
  omega

private lemma eq_of_D4_wedge {P Q : ℤ → ℤ → Bool}
    (hPx : ∀ u v, P (-u) v = P u v) (hPy : ∀ u v, P u (-v) = P u v) (hPt : ∀ u v, P v u = P u v)
    (hQx : ∀ u v, Q (-u) v = Q u v) (hQy : ∀ u v, Q u (-v) = Q u v) (hQt : ∀ u v, Q v u = Q u v)
    (hwedge : ∀ x y : ℤ, 0 ≤ y → y ≤ x → P x y = Q x y) :
    ∀ x y : ℤ, P x y = Q x y := by
  have h1 : ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → P x y = Q x y := by
    intro x y hx hy
    by_cases hle : y ≤ x
    · exact hwedge x y hy hle
    · rw [← hPt x y, ← hQt x y]
      exact hwedge y x hx (by omega)
  have h2 : ∀ x y : ℤ, 0 ≤ x → P x y = Q x y := by
    intro x y hx
    by_cases hy : 0 ≤ y
    · exact h1 x y hx hy
    · rw [← hPy x y, ← hQy x y]
      exact h1 x (-y) hx (by omega)
  intro x y
  by_cases hx : 0 ≤ x
  · exact h2 x y hx
  · rw [← hPx x y, ← hQx x y]
    exact h2 (-x) y (by omega)

-- Sublemma <2>1: step526 (UG d (A r)) = UG d (A (r + 1)) for 1 <= r <= d - 1
private lemma step526_UG_step {m : ℕ} (hm : 2 ≤ m) {r : ℕ} (_hr1 : 1 ≤ r) (hr2 : r ≤ 2 ^ m - 1) :
    step526 (UG (2 ^ m : ℕ) (A r)) = UG (2 ^ m : ℕ) (A (r + 1)) := by
  set d : ℕ := 2 ^ m
  have hd4 : 4 ≤ d := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    simpa [d] using this
  have hd_even : ∃ q : ℕ, d = 2 * q := by
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    exact this
  rcases hd_even with ⟨qd, hqd⟩
  have hUGx : ∀ u v, UG (d : ℤ) (A r) (-u) v = UG (d : ℤ) (A r) u v :=
    UG_sym_x d (A_sym_x r)
  have hUGy : ∀ u v, UG (d : ℤ) (A r) u (-v) = UG (d : ℤ) (A r) u v :=
    UG_sym_y d (A_sym_y r)
  have hUGt : ∀ u v, UG (d : ℤ) (A r) v u = UG (d : ℤ) (A r) u v :=
    UG_sym_t d (A_sym_t r)
  funext x y
  refine eq_of_D4_wedge
    (step526_sym_x hUGx) (step526_sym_y hUGy) (step526_sym_t hUGt)
    (UG_sym_x d (A_sym_x (r + 1))) (UG_sym_y d (A_sym_y (r + 1))) (UG_sym_t d (A_sym_t (r + 1)))
    ?_ x y
  intro x y hy hyx
  by_cases hlt : x + y ≤ (d : ℤ) - 1
  · have hagree : ∀ u v : ℤ, (u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ (d : ℤ) → UG (d : ℤ) (A r) u v = F u v := by
      intro u v huv; simp only [UG, if_pos huv]
    rw [step526_congr (hagree x y (by omega)) (hagree (x + 1) y (by omega))
      (hagree (x - 1) y (by omega)) (hagree x (y + 1) (by omega)) (hagree x (y - 1) (by omega)),
      F_still_life, UG, if_pos (by omega)]
  · by_cases heq : x + y = (d : ℤ)
    · by_cases hy0 : y = 0
      · subst hy0
        have hx : x = (d : ℤ) := by omega
        subst hx
        have hc : UG (d : ℤ) (A r) d 0 = true := by
          rw [UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_true (Or.inr rfl)]
        have hL : UG (d : ℤ) (A r) ((d : ℤ) - 1) 0 = true := by
          rw [UG, if_pos (by omega)]; exact F_odd (by omega)
        have hR : UG (d : ℤ) (A r) ((d : ℤ) + 1) 0 = A r 1 0 := by
          simp only [UG, if_neg (show ¬ ((((d : ℤ) + 1).natAbs : ℤ) + ((0 : ℤ).natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_pos (show ((0 : ℤ).natAbs : ℤ) < (d : ℤ) + 1 by omega), add_sub_cancel_left]
        have hU : UG (d : ℤ) (A r) (d : ℤ) 1 = A r 1 0 := by
          simp only [UG, if_neg (show ¬ ((((d : ℤ)).natAbs : ℤ) + ((1 : ℤ).natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_pos (show ((1 : ℤ).natAbs : ℤ) < (d : ℤ) by omega), sub_self]
          exact A_sym_t r 1 0
        have hD : UG (d : ℤ) (A r) (d : ℤ) (-1) = A r 1 0 := by
          simp only [UG, if_neg (show ¬ ((((d : ℤ)).natAbs : ℤ) + ((-1 : ℤ).natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_pos (show ((-1 : ℤ).natAbs : ℤ) < (d : ℤ) by omega), sub_self]
          rw [A_sym_y, A_sym_t]
        have hRHS : UG (d : ℤ) (A (r + 1)) d 0 = true := by
          rw [UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_true (Or.inr rfl)]
        rw [hRHS]
        simp only [step526, cnt526, hc, hL, hR, zero_add, zero_sub, hU, hD]
        cases A r 1 0 <;> rfl
      · have hc : UG (d : ℤ) (A r) x y = false := by
          rw [UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_false (by omega)]
        have hL : UG (d : ℤ) (A r) (x - 1) y = true := by
          rw [UG, if_pos (by omega)]; exact F_odd (by omega)
        have hD : UG (d : ℤ) (A r) x (y - 1) = true := by
          rw [UG, if_pos (by omega)]; exact F_odd (by omega)
        have hRHS : UG (d : ℤ) (A (r + 1)) x y = false := by
          rw [UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_false (by omega)]
        rw [hRHS]
        simp only [step526, cnt526, hc, hL, hD, Bool.false_eq_true, ↓reduceIte,
          Bool.toNat_true, beq_eq_false_iff_ne]
        omega
    · by_cases hdiag_xy : x = y
      · subst hdiag_xy
        have hxpos : 0 < x := by omega
        have hc : UG (d : ℤ) (A r) x x = false := by
          simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (x.natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_neg (show ¬ ((x.natAbs : ℤ) < x) by omega), if_neg (show ¬ ((x.natAbs : ℤ) < -x) by omega)]
        have hRHS : UG (d : ℤ) (A (r + 1)) x x = false := by
          simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (x.natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_neg (show ¬ ((x.natAbs : ℤ) < x) by omega), if_neg (show ¬ ((x.natAbs : ℤ) < -x) by omega)]
        rw [hRHS]
        simp only [step526, cnt526, hc, Bool.false_eq_true, ↓reduceIte]
        rw [hUGt (x + 1) x, hUGt (x - 1) x]
        cases UG (d : ℤ) (A r) (x + 1) x <;> cases UG (d : ℤ) (A r) (x - 1) x <;> rfl
      · -- Strict outer cone: x > y >= 0, x + y >= d + 1
        have hq : ∀ u v : ℤ, (v.natAbs : ℤ) ≤ u → (d : ℤ) ≤ (u.natAbs : ℤ) + (v.natAbs : ℤ) →
            UG (d : ℤ) (A r) u v = A r (u - d) v := by
          intro u v hvu hdu
          by_cases hdeq : (u.natAbs : ℤ) + (v.natAbs : ℤ) = (d : ℤ)
          · rw [UG, if_pos (by omega), F_pow2_bd hm hdeq]
            by_cases hv0 : v = 0
            · subst hv0
              have hu : u = (d : ℤ) := by omega
              subst hu
              simp [A_origin]
            · rw [decide_eq_false (by omega)]
              symm
              exact A_diag r (by omega) (by omega)
          · by_cases hdiag_uv : (v.natAbs : ℤ) = u
            · have hu_pos : 0 < u := by omega
              simp only [UG, if_neg (show ¬ ((u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ (d : ℤ)) by omega),
                if_neg (show ¬ ((v.natAbs : ℤ) < u) by omega), if_neg (show ¬ ((v.natAbs : ℤ) < -u) by omega),
                if_neg (show ¬ ((u.natAbs : ℤ) < v) by omega), if_neg (show ¬ ((u.natAbs : ℤ) < -v) by omega)]
              symm
              exact A_cone_false (by omega)
            · simp only [UG, if_neg (show ¬ ((u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ (d : ℤ)) by omega),
                if_pos (show (v.natAbs : ℤ) < u by omega)]
        have hstep := @step526_congr (UG (d : ℤ) (A r)) (fun u v => A r (u - d) v) x y
          (hq x y (by omega) (by omega))
          (hq (x + 1) y (by omega) (by omega))
          (hq (x - 1) y (by omega) (by omega))
          (hq x (y + 1) (by omega) (by omega))
          (hq x (y - 1) (by omega) (by omega))
        rw [hstep, step526_shift_x (A r) d x y]
        change A (r + 1) (x - d) y = UG (d : ℤ) (A (r + 1)) x y
        simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
          if_pos (show (y.natAbs : ℤ) < x by omega)]

private lemma iter_UG_step {m : ℕ} (hm : 2 ≤ m) (hbase : A (2 ^ m + 1) = UG (2 ^ m : ℕ) (A 1)) :
    ∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ m → A (2 ^ m + r) = UG (2 ^ m : ℕ) (A r) := by
  intro r
  induction r with
  | zero => intro hr1; omega
  | succ r ih =>
    intro _ hr2
    cases r with
    | zero => exact hbase
    | succ r' =>
      have hprev := ih (by omega) (by omega)
      rw [show 2 ^ m + (r' + 1 + 1) = (2 ^ m + (r' + 1)) + 1 by omega]
      change step526 (A (2 ^ m + (r' + 1))) = UG (2 ^ m : ℕ) (A (r' + 1 + 1))
      rw [hprev]
      exact step526_UG_step hm (by omega) (by omega)

-- Sublemma <2>2: Doubling step d -> 2d
private lemma doubling_step {m : ℕ} (hm : 2 ≤ m)
    (h1 : ∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ m : ℕ) → A (2 ^ m) x y = decide (x = 0 ∨ y = 0))
    (h2a : ∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ m : ℕ) - 2 → A (2 ^ m) x y = false)
    (h2b : A (2 ^ m) 0 ((2 ^ m : ℕ) - 1) = true)
    (h3 : A (2 ^ m + 1) = UG (2 ^ m : ℕ) (A 1)) :
    (∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ (m + 1) : ℕ) → A (2 ^ (m + 1)) x y = decide (x = 0 ∨ y = 0)) ∧
    (∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ (m + 1) : ℕ) - 2 → A (2 ^ (m + 1)) x y = false) ∧
    (A (2 ^ (m + 1)) 0 ((2 ^ (m + 1) : ℕ) - 1) = true) ∧
    (A (2 ^ (m + 1) + 1) = UG (2 ^ (m + 1) : ℕ) (A 1)) := by
  set d : ℕ := 2 ^ m
  have hd4 : 4 ≤ d := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    simpa [d] using this
  have hd_even : ∃ q : ℕ, d = 2 * q := by
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    exact this
  rcases hd_even with ⟨qd, hqd⟩
  have h2d_nat : 2 ^ (m + 1) = 2 * d := by rw [pow_succ]; ring
  have h2d_int : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 * (d : ℤ) := by exact_mod_cast h2d_nat
  have hG : A (2 * d) = UG (d : ℤ) (A d) := by
    rw [show 2 * d = d + d by omega]
    exact iter_UG_step hm h3 d (by omega) (le_refl d)
  have h1' : ∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = 2 * (d : ℤ) → A (2 * d) x y = decide (x = 0 ∨ y = 0) := by
    intro x y hxy
    rw [hG]
    by_cases hdx : (y.natAbs : ℤ) < x
    · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega), if_pos hdx]
      by_cases hxd : (d : ℤ) ≤ x
      · rw [h1 (x - d) y (by omega)]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      · rw [A_cone_false (by omega), decide_eq_false (by omega)]
    · by_cases hdxn : (y.natAbs : ℤ) < -x
      · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
          if_neg hdx, if_pos hdxn]
        by_cases hxd : (d : ℤ) ≤ -x
        · rw [h1 (x + d) y (by omega)]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega
        · rw [A_cone_false (by omega), decide_eq_false (by omega)]
      · by_cases hdy : (x.natAbs : ℤ) < y
        · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_neg hdx, if_neg hdxn, if_pos hdy]
          by_cases hyd : (d : ℤ) ≤ y
          · rw [h1 x (y - d) (by omega)]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq]
            omega
          · rw [A_cone_false (by omega), decide_eq_false (by omega)]
        · by_cases hdyn : (x.natAbs : ℤ) < -y
          · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_neg hdx, if_neg hdxn, if_neg hdy, if_pos hdyn]
            by_cases hyd : (d : ℤ) ≤ -y
            · rw [h1 x (y + d) (by omega)]
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              omega
            · rw [A_cone_false (by omega), decide_eq_false (by omega)]
          · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_neg hdx, if_neg hdxn, if_neg hdy, if_neg hdyn]
            rw [decide_eq_false (by omega)]
  have h2a' : ∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = 2 * (d : ℤ) - 2 → A (2 * d) x y = false := by
    intro x y hxy
    rw [hG]
    by_cases hdx : (y.natAbs : ℤ) < x
    · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega), if_pos hdx]
      exact h2a (x - d) y (by omega)
    · by_cases hdxn : (y.natAbs : ℤ) < -x
      · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
          if_neg hdx, if_pos hdxn]
        exact h2a (x + d) y (by omega)
      · by_cases hdy : (x.natAbs : ℤ) < y
        · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
            if_neg hdx, if_neg hdxn, if_pos hdy]
          exact h2a x (y - d) (by omega)
        · by_cases hdyn : (x.natAbs : ℤ) < -y
          · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_neg hdx, if_neg hdxn, if_neg hdy, if_pos hdyn]
            exact h2a x (y + d) (by omega)
          · simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_neg hdx, if_neg hdxn, if_neg hdy, if_neg hdyn]
  have h2b' : A (2 * d) 0 (2 * (d : ℤ) - 1) = true := by
    rw [hG]
    simp only [UG,
      if_neg (show ¬ (((0 : ℤ).natAbs : ℤ) + ((2 * (d : ℤ) - 1).natAbs : ℤ) ≤ (d : ℤ)) by omega),
      if_neg (show ¬ (((2 * (d : ℤ) - 1).natAbs : ℤ) < 0) by omega),
      if_neg (show ¬ (((2 * (d : ℤ) - 1).natAbs : ℤ) < -(0 : ℤ)) by omega),
      if_pos (show ((0 : ℤ).natAbs : ℤ) < 2 * (d : ℤ) - 1 by omega)]
    rw [show 2 * (d : ℤ) - 1 - (d : ℤ) = (d : ℤ) - 1 by ring]
    exact h2b
  have h3' : A (2 * d + 1) = UG (2 * (d : ℤ)) (A 1) := by
    funext x y
    refine eq_of_D4_wedge
      (A_sym_x (2 * d + 1)) (A_sym_y (2 * d + 1)) (A_sym_t (2 * d + 1))
      (UG_sym_x (2 * d) (A_sym_x 1)) (UG_sym_y (2 * d) (A_sym_y 1)) (UG_sym_t (2 * d) (A_sym_t 1))
      ?_ x y
    intro x y hy hyx
    change step526 (A (2 * d)) x y = UG (2 * (d : ℤ)) (A 1) x y
    by_cases hlt : x + y ≤ (d : ℤ) - 1
    · have hagree : ∀ u v : ℤ, (u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ (d : ℤ) → A (2 * d) u v = F u v := by
        intro u v huv; rw [hG, UG, if_pos huv]
      rw [step526_congr (hagree x y (by omega)) (hagree (x + 1) y (by omega))
        (hagree (x - 1) y (by omega)) (hagree x (y + 1) (by omega)) (hagree x (y - 1) (by omega)),
        F_still_life, UG, if_pos (by omega)]
    · by_cases heq : x + y = (d : ℤ)
      · by_cases hy0 : y = 0
        · subst hy0
          have hx : x = (d : ℤ) := by omega
          subst hx
          have hc : A (2 * d) d 0 = true := by
            rw [hG, UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_true (Or.inr rfl)]
          have hL : A (2 * d) ((d : ℤ) - 1) 0 = true := by
            rw [hG, UG, if_pos (by omega)]; exact F_odd (by omega)
          have hR : A (2 * d) ((d : ℤ) + 1) 0 = A d 1 0 := by
            rw [hG]; simp only [UG, if_neg (show ¬ ((((d : ℤ) + 1).natAbs : ℤ) + ((0 : ℤ).natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_pos (show ((0 : ℤ).natAbs : ℤ) < (d : ℤ) + 1 by omega), add_sub_cancel_left]
          have hU : A (2 * d) (d : ℤ) 1 = A d 1 0 := by
            rw [hG]; simp only [UG, if_neg (show ¬ ((((d : ℤ)).natAbs : ℤ) + ((1 : ℤ).natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_pos (show ((1 : ℤ).natAbs : ℤ) < (d : ℤ) by omega), sub_self]
            exact A_sym_t d 1 0
          have hD : A (2 * d) (d : ℤ) (-1) = A d 1 0 := by
            rw [hG]; simp only [UG, if_neg (show ¬ ((((d : ℤ)).natAbs : ℤ) + ((-1 : ℤ).natAbs : ℤ) ≤ (d : ℤ)) by omega),
              if_pos (show ((-1 : ℤ).natAbs : ℤ) < (d : ℤ) by omega), sub_self]
            rw [A_sym_y, A_sym_t]
          have hRHS : UG (2 * (d : ℤ)) (A 1) d 0 = true := by
            rw [UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_true (Or.inr rfl)]
          rw [hRHS]
          simp only [step526, cnt526, hc, hL, hR, zero_add, zero_sub, hU, hD]
          cases A d 1 0 <;> rfl
        · have hc : A (2 * d) x y = false := by
            rw [hG, UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_false (by omega)]
          have hL : A (2 * d) (x - 1) y = true := by
            rw [hG, UG, if_pos (by omega)]; exact F_odd (by omega)
          have hD : A (2 * d) x (y - 1) = true := by
            rw [hG, UG, if_pos (by omega)]; exact F_odd (by omega)
          have hRHS : UG (2 * (d : ℤ)) (A 1) x y = false := by
            rw [UG, if_pos (by omega), F_pow2_bd hm (by omega), decide_eq_false (by omega)]
          rw [hRHS]
          simp only [step526, cnt526, hc, hL, hD, Bool.false_eq_true, ↓reduceIte,
            Bool.toNat_true, beq_eq_false_iff_ne]
          omega
      · by_cases hdiag_xy : x = y
        · subst hdiag_xy
          have hL : A (2 * d + 1) x x = false := A_diag (2 * d + 1) rfl (by omega)
          change A (2 * d + 1) x x = UG (2 * (d : ℤ)) (A 1) x x
          rw [hL]
          by_cases hle2d : (x.natAbs : ℤ) + (x.natAbs : ℤ) ≤ 2 * (d : ℤ)
          · rw [UG, if_pos hle2d, F_diag rfl (by omega)]
          · simp only [UG, if_neg hle2d, if_neg (show ¬ ((x.natAbs : ℤ) < x) by omega),
              if_neg (show ¬ ((x.natAbs : ℤ) < -x) by omega)]
        · -- Strict outer cone: x > y >= 0, x + y >= d + 1
          by_cases hspec1 : x = (d : ℤ) ∧ y = (d : ℤ) - 1
          · rcases hspec1 with ⟨rfl, rfl⟩
            have hc : A (2 * d) d ((d : ℤ) - 1) = true := by
              rw [hG]
              simp only [UG, if_neg (show ¬ ((((d : ℤ)).natAbs : ℤ) + (((d : ℤ) - 1).natAbs : ℤ) ≤ (d : ℤ)) by omega),
                if_pos (show (((d : ℤ) - 1).natAbs : ℤ) < (d : ℤ) by omega), sub_self]
              exact h2b
            have hR : A (2 * d) ((d : ℤ) + 1) ((d : ℤ) - 1) = false := by
              rw [h1' ((d : ℤ) + 1) ((d : ℤ) - 1) (by omega), decide_eq_false (by omega)]
            have hL : A (2 * d) ((d : ℤ) - 1) ((d : ℤ) - 1) = false :=
              A_diag (2 * d) rfl (by omega)
            have hU : A (2 * d) (d : ℤ) (((d : ℤ) - 1) + 1) = false := by
              rw [sub_add_cancel]; exact A_diag (2 * d) rfl (by omega)
            have hD : A (2 * d) (d : ℤ) (((d : ℤ) - 1) - 1) = false :=
              h2a' d (((d : ℤ) - 1) - 1) (by omega)
            have hRHS : UG (2 * (d : ℤ)) (A 1) d ((d : ℤ) - 1) = true := by
              rw [UG, if_pos (by omega)]; exact F_odd (by omega)
            rw [hRHS]
            simp only [step526, cnt526, hc, hR, hL, hU, hD]
            rfl
          · by_cases hspec2 : x = (d : ℤ) + 1 ∧ y = (d : ℤ)
            · rcases hspec2 with ⟨rfl, rfl⟩
              have hc : A (2 * d) ((d : ℤ) + 1) d = false := A_cone_false (by omega)
              have hR : A (2 * d) ((d : ℤ) + 1 + 1) d = false := A_cone_false (by omega)
              have hL : A (2 * d) ((d : ℤ) + 1 - 1) d = false := by
                rw [add_sub_cancel_right]; exact A_diag (2 * d) rfl (by omega)
              have hU : A (2 * d) ((d : ℤ) + 1) ((d : ℤ) + 1) = false :=
                A_diag (2 * d) rfl (by omega)
              have hD : A (2 * d) ((d : ℤ) + 1) ((d : ℤ) - 1) = false := by
                rw [h1' ((d : ℤ) + 1) ((d : ℤ) - 1) (by omega), decide_eq_false (by omega)]
              have hRHS : UG (2 * (d : ℤ)) (A 1) ((d : ℤ) + 1) d = false := by
                simp only [UG, if_neg (show ¬ ((((d : ℤ) + 1).natAbs : ℤ) + (((d : ℤ)).natAbs : ℤ) ≤ 2 * (d : ℤ)) by omega),
                  if_pos (show (((d : ℤ)).natAbs : ℤ) < (d : ℤ) + 1 by omega)]
                exact A_cone_false (by omega)
              rw [hRHS]
              simp only [step526, cnt526, hc, hR, hL, hU, hD]
              rfl
            · -- Generic point in strict cone x > y >= 0, x + y >= d + 1, excluding (d, d-1) and (d+1, d)
              have hq : ∀ u v : ℤ, (v.natAbs : ℤ) ≤ u → (d : ℤ) ≤ (u.natAbs : ℤ) + (v.natAbs : ℤ) →
                  ((v.natAbs : ℤ) = u → (v.natAbs : ℤ) ≠ (d : ℤ)) →
                  A (2 * d) u v = A d (u - d) v := by
                intro u v hvu hdu hne_d
                rw [hG]
                by_cases hdeq : (u.natAbs : ℤ) + (v.natAbs : ℤ) = (d : ℤ)
                · rw [UG, if_pos (by omega), F_pow2_bd hm hdeq]
                  by_cases hv0 : v = 0
                  · subst hv0
                    have hu : u = (d : ℤ) := by omega
                    subst hu
                    simp [A_origin]
                  · rw [decide_eq_false (by omega)]
                    symm
                    exact A_diag d (by omega) (by omega)
                · by_cases hdiag_uv : (v.natAbs : ℤ) = u
                  · have hvn : (v.natAbs : ℤ) ≠ (d : ℤ) := hne_d hdiag_uv
                    simp only [UG, if_neg (show ¬ ((u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ (d : ℤ)) by omega),
                      if_neg (show ¬ ((v.natAbs : ℤ) < u) by omega), if_neg (show ¬ ((v.natAbs : ℤ) < -u) by omega),
                      if_neg (show ¬ ((u.natAbs : ℤ) < v) by omega), if_neg (show ¬ ((u.natAbs : ℤ) < -v) by omega)]
                    symm
                    by_cases hvlt : (v.natAbs : ℤ) < (d : ℤ)
                    · rw [h1 (u - d) v (by omega), decide_eq_false (by omega)]
                    · exact A_cone_false (by omega)
                  · simp only [UG, if_neg (show ¬ ((u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ (d : ℤ)) by omega),
                      if_pos (show (v.natAbs : ℤ) < u by omega)]
              have hstep := @step526_congr (A (2 * d)) (fun u v => A d (u - d) v) x y
                (hq x y (by omega) (by omega) (by omega))
                (hq (x + 1) y (by omega) (by omega) (by omega))
                (hq (x - 1) y (by omega) (by omega) (by omega))
                (hq x (y + 1) (by omega) (by omega) (by omega))
                (hq x (y - 1) (by omega) (by omega) (by omega))
              rw [hstep, step526_shift_x (A d) d x y]
              change A (d + 1) (x - d) y = UG (2 * (d : ℤ)) (A 1) x y
              rw [h3]
              by_cases hle2d : x + y ≤ 2 * (d : ℤ)
              · rw [UG, if_pos (by omega), UG, if_pos (by omega)]
                exact (F_shift hm (by omega) (by omega) (by omega)).symm
              · rw [UG, if_neg (show ¬ (((x - (d : ℤ)).natAbs : ℤ) + (y.natAbs : ℤ) ≤ (d : ℤ)) by omega),
                    UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ 2 * (d : ℤ)) by omega),
                    if_pos (show (y.natAbs : ℤ) < x by omega)]
                by_cases hcone' : (y.natAbs : ℤ) < x - (d : ℤ)
                · rw [if_pos hcone', show x - (d : ℤ) - (d : ℤ) = x - 2 * (d : ℤ) by ring]
                · rw [if_neg hcone']
                  have hRHS_f : A 1 (x - 2 * (d : ℤ)) y = false := A_cone_false (by omega)
                  rw [hRHS_f]
                  split_ifs
                  · exact A_cone_false (by omega)
                  · exact A_cone_false (by omega)
                  · exact A_cone_false (by omega)
                  · rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy; rw [h2d_nat]; exact h1' x y (by omega)
  · intro x y hxy; rw [h2d_nat]; exact h2a' x y (by omega)
  · rw [h2d_nat, show ((2 * d : ℕ) : ℤ) = 2 * (d : ℤ) by push_cast; ring]; exact h2b'
  · rw [h2d_nat, show ((2 * d : ℕ) : ℤ) = 2 * (d : ℤ) by push_cast; ring]; exact h3'

private lemma base_m2 :
    (∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ 2 : ℕ) → A (2 ^ 2) x y = decide (x = 0 ∨ y = 0)) ∧
    (∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ 2 : ℕ) - 2 → A (2 ^ 2) x y = false) ∧
    (A (2 ^ 2) 0 ((2 ^ 2 : ℕ) - 1) = true) ∧
    (A (2 ^ 2 + 1) = UG (2 ^ 2 : ℕ) (A 1)) := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro x y hxy
    have hx1 : -4 ≤ x := by omega
    have hx2 : x ≤ 4 := by omega
    have hy1 : -4 ≤ y := by omega
    have hy2 : y ≤ 4 := by omega
    interval_cases x <;> interval_cases y <;> try omega
    all_goals decide
  · intro x y hxy
    have hx1 : -2 ≤ x := by omega
    have hx2 : x ≤ 2 := by omega
    have hy1 : -2 ≤ y := by omega
    have hy2 : y ≤ 2 := by omega
    interval_cases x <;> interval_cases y <;> try omega
    all_goals decide
  · funext x y
    refine eq_of_D4_wedge
      (A_sym_x 5) (A_sym_y 5) (A_sym_t 5)
      (UG_sym_x 4 (A_sym_x 1)) (UG_sym_y 4 (A_sym_y 1)) (UG_sym_t 4 (A_sym_t 1))
      ?_ x y
    intro x y hy hyx
    by_cases hle : x + y ≤ 5
    · have hx1 : 0 ≤ x := by omega
      have hx2 : x ≤ 5 := by omega
      have hy1 : 0 ≤ y := by omega
      have hy2 : y ≤ 5 := by omega
      interval_cases x <;> interval_cases y <;> try omega
      all_goals decide
    · rw [A_cone_false (by omega)]
      simp only [UG, if_neg (show ¬ ((x.natAbs : ℤ) + (y.natAbs : ℤ) ≤ 4) by omega)]
      split_ifs
      · symm; exact A_cone_false (by omega)
      · symm; exact A_cone_false (by omega)
      · symm; exact A_cone_false (by omega)
      · symm; exact A_cone_false (by omega)
      · rfl

private lemma doubling_theorem :
    ∀ m : ℕ, 2 ≤ m →
      (∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ m : ℕ) → A (2 ^ m) x y = decide (x = 0 ∨ y = 0)) ∧
      (∀ x y : ℤ, (x.natAbs : ℤ) + (y.natAbs : ℤ) = (2 ^ m : ℕ) - 2 → A (2 ^ m) x y = false) ∧
      (A (2 ^ m) 0 ((2 ^ m : ℕ) - 1) = true) ∧
      (A (2 ^ m + 1) = UG (2 ^ m : ℕ) (A 1)) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm2 : m + 1 = 2
    · rw [hm2]; exact base_m2
    · obtain ⟨h1, h2a, h2b, h3⟩ := ih (by omega)
      exact doubling_step (by omega) h1 h2a h2b h3

private lemma A_pow2_sub_one {m : ℕ} (hm : 3 ≤ m) :
    A (2 ^ m - 1) = UG (2 ^ (m - 1) : ℕ) (A (2 ^ (m - 1) - 1)) := by
  have hm1 : 2 ≤ m - 1 := by omega
  have hpow_pos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
  have h4 : 4 ≤ 2 ^ (m - 1) := by
    have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) hm1
    simpa using this
  have hbase := (doubling_theorem (m - 1) hm1).2.2.2
  have hiter := iter_UG_step hm1 hbase (2 ^ (m - 1) - 1) (by omega) (by omega)
  have hidx : 2 ^ (m - 1) + (2 ^ (m - 1) - 1) = 2 ^ m - 1 := by
    have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    omega
  rwa [hidx] at hiter

-- ============================================================================
-- Section 4: Exact Cell-Edge Identity and 3-Cone Counts
-- ============================================================================

private def zIcc (a b : ℤ) : Finset ℤ :=
  (Finset.range (b - a + 1).toNat).image (fun n : ℕ => a + (n : ℤ))

private lemma mem_zIcc {a b x : ℤ} : x ∈ zIcc a b ↔ a ≤ x ∧ x ≤ b := by
  simp only [zIcc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩; omega
  · intro ⟨h1, h2⟩; exact ⟨(x - a).toNat, by omega, by omega⟩

private lemma card_filter_split {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_filter] at h1 h2; exact h2.2 h1.2
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx; by_cases hp : p x; exact Or.inl ⟨hx, hp⟩; exact Or.inr ⟨hx, hp⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private lemma v2Nat_mul_four {n : ℕ} (hn : n ≠ 0) : v2Nat (4 * n) = v2Nat n + 2 := by
  obtain ⟨hd1, hd2⟩ := v2Nat_dvd_and_not_dvd n hn
  apply v2Nat_eq_of_dvd (by omega)
  · rw [pow_add, mul_comm]; exact Nat.mul_dvd_mul_left 4 hd1
  · rw [show v2Nat n + 2 + 1 = (v2Nat n + 1) + 2 by omega, pow_add, mul_comm]
    intro hbad; exact hd2 ((Nat.mul_dvd_mul_iff_left (by omega : 0 < 4)).mp hbad)

private def boxB (R : ℤ) : Finset (ℤ × ℤ) :=
  zIcc (-R) R ×ˢ zIcc (-R) R

private def Aset (k : ℕ) : Finset (ℤ × ℤ) :=
  (boxB k).filter (fun p => A k p.1 p.2 = true)

private lemma mem_Aset {k : ℕ} {p : ℤ × ℤ} : p ∈ Aset k ↔ A k p.1 p.2 = true := by
  simp only [Aset, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc, and_iff_right_iff_imp]
  intro h
  have := A_cone h
  omega

private def edgesOf (S : Finset (ℤ × ℤ)) : ℕ :=
  (S.filter (fun p => (p.1 + 1, p.2) ∈ S)).card +
  (S.filter (fun p => (p.1, p.2 + 1) ∈ S)).card

private lemma onCount_odd_eq (k : ℕ) :
    onCount 646 (2 * k + 1) + 2 * edgesOf (Aset k) = 5 * (Aset k).card := by
  set t : ℕ := 2 * k + 1
  set onSet : Finset (ℤ × ℤ) := (boxB t).filter (fun p => cell 646 t p.1 p.2 = true)
  have hon_card : onCount 646 t = onSet.card := by
    have h1 : onCount 646 t =
        ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter
          (fun p => cell 646 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true)).card := by
      unfold onCount
      rw [Finset.card_filter, Finset.sum_product]
    rw [h1]
    refine Finset.card_bij (fun p _ => ((p.1 : ℤ) - (t : ℤ), (p.2 : ℤ) - (t : ℤ))) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc]
      exact ⟨⟨by omega, by omega⟩, hp.2⟩
    · intro p₁ _ p₂ _ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      ext <;> omega
    · intro q hq
      simp only [onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc] at hq
      refine ⟨((q.1 + (t : ℤ)).toNat, (q.2 + (t : ℤ)).toNat), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [show (((q.1 + (t : ℤ)).toNat : ℤ) - (t : ℤ)) = q.1 by omega,
            show (((q.2 + (t : ℤ)).toNat : ℤ) - (t : ℤ)) = q.2 by omega]
        exact hq.2
      · ext <;> dsimp only <;> omega
  obtain ⟨_, h_ee, h_oe, h_eo, h_oo⟩ := cell_even_and_odd k
  set eeSet : Finset (ℤ × ℤ) := onSet.filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0)
  set oeSet : Finset (ℤ × ℤ) := onSet.filter (fun p => p.1 % 2 ≠ 0 ∧ p.2 % 2 = 0)
  set eoSet : Finset (ℤ × ℤ) := onSet.filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 ≠ 0)
  have hon_part : onSet = eeSet ∪ (oeSet ∪ eoSet) := by
    ext p
    simp only [eeSet, oeSet, eoSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      by_cases h1 : p.1 % 2 = 0 <;> by_cases h2 : p.2 % 2 = 0
      · exact Or.inl ⟨hp, h1, h2⟩
      · exact Or.inr (Or.inr ⟨hp, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨hp, h1, h2⟩)
      · exfalso
        have hp_c : cell 646 (2 * k + 1) p.1 p.2 = true := (Finset.mem_filter.mp hp).2
        rw [show p.1 = 2 * (p.1 / 2) + 1 by omega, show p.2 = 2 * (p.2 / 2) + 1 by omega,
          h_oo] at hp_c
        exact Bool.false_ne_true hp_c
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hd_ee : Disjoint eeSet (oeSet ∪ eoSet) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [eeSet, oeSet, eoSet, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp2 with ⟨_, h1, _⟩ | ⟨_, _, h2⟩
    · exact h1 hp1.2.1
    · exact h2 hp1.2.2
  have hd_oe : Disjoint oeSet eoSet := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [oeSet, eoSet, Finset.mem_filter] at hp1 hp2
    exact hp1.2.1 hp2.2.1
  have hon_sum : onSet.card = eeSet.card + oeSet.card + eoSet.card := by
    rw [hon_part, Finset.card_union_of_disjoint hd_ee, Finset.card_union_of_disjoint hd_oe]
    omega
  have hee_card : eeSet.card = (Aset k).card := by
    symm
    refine Finset.card_bij (fun p _ => (2 * p.1, 2 * p.2)) ?_ ?_ ?_
    · intro p hp
      rw [mem_Aset] at hp
      have hcone := A_cone hp
      simp only [eeSet, onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc]
      exact ⟨⟨⟨by omega, by omega⟩, by rw [h_ee]; exact hp⟩, by omega, by omega⟩
    · intro p₁ _ p₂ _ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      ext <;> omega
    · intro q hq
      simp only [eeSet, onSet, Finset.mem_filter] at hq
      refine ⟨(q.1 / 2, q.2 / 2), ?_, ?_⟩
      · rw [mem_Aset]
        have hc := hq.1.2
        rw [show q.1 = 2 * (q.1 / 2) by omega, show q.2 = 2 * (q.2 / 2) by omega, h_ee] at hc
        exact hc
      · ext <;> dsimp only <;> omega
  set hBdyR : Finset (ℤ × ℤ) := (Aset k).filter (fun p => (p.1 + 1, p.2) ∉ Aset k)
  set hBdyL : Finset (ℤ × ℤ) := (Aset k).filter (fun p => (p.1 - 1, p.2) ∉ Aset k)
  set vBdyU : Finset (ℤ × ℤ) := (Aset k).filter (fun p => (p.1, p.2 + 1) ∉ Aset k)
  set vBdyD : Finset (ℤ × ℤ) := (Aset k).filter (fun p => (p.1, p.2 - 1) ∉ Aset k)
  have hoe_card : oeSet.card = hBdyR.card + hBdyL.card := by
    set oe1 : Finset (ℤ × ℤ) := oeSet.filter (fun q => A k ((q.1 - 1) / 2) (q.2 / 2) = true)
    set oe2 : Finset (ℤ × ℤ) := oeSet.filter (fun q => A k ((q.1 - 1) / 2) (q.2 / 2) ≠ true)
    have hsplit : oeSet.card = oe1.card + oe2.card :=
      (card_filter_split (s := oeSet)
        (p := fun q => A k ((q.1 - 1) / 2) (q.2 / 2) = true)).symm
    rw [hsplit]
    congr 1
    · symm
      refine Finset.card_bij (fun p _ => (2 * p.1 + 1, 2 * p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [hBdyR, Finset.mem_filter, mem_Aset] at hp
        have hcone := A_cone hp.1
        have hp2f : A k (p.1 + 1) p.2 = false := Bool.eq_false_iff.mpr hp.2
        simp only [oe1, oeSet, onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc]
        refine ⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩, ?_⟩
        · rw [h_oe, hp.1, hp2f]; rfl
        · rw [show (2 * p.1 + 1 - 1) / 2 = p.1 by omega, show (2 * p.2) / 2 = p.2 by omega]; exact hp.1
      · intro p₁ _ p₂ _ heq
        have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
      · intro q hq
        simp only [oe1, oeSet, onSet, Finset.mem_filter] at hq
        refine ⟨((q.1 - 1) / 2, q.2 / 2), ?_, ?_⟩
        · simp only [hBdyR, Finset.mem_filter, mem_Aset]
          refine ⟨hq.2, ?_⟩
          intro hbad
          have hc := hq.1.1.2
          rw [show q.1 = 2 * ((q.1 - 1) / 2) + 1 by omega, show q.2 = 2 * (q.2 / 2) by omega,
            h_oe, hq.2, hbad] at hc
          exact Bool.false_ne_true hc
        · ext <;> dsimp only <;> omega
    · symm
      refine Finset.card_bij (fun p _ => (2 * p.1 - 1, 2 * p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [hBdyL, Finset.mem_filter, mem_Aset] at hp
        have hcone := A_cone hp.1
        have hp2f : A k (p.1 - 1) p.2 = false := Bool.eq_false_iff.mpr hp.2
        simp only [oe2, oeSet, onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc]
        refine ⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩, ?_⟩
        · rw [show 2 * p.1 - 1 = 2 * (p.1 - 1) + 1 by ring, h_oe, hp2f,
            show p.1 - 1 + 1 = p.1 by ring, hp.1]; rfl
        · rw [show (2 * p.1 - 1 - 1) / 2 = p.1 - 1 by omega, show (2 * p.2) / 2 = p.2 by omega]
          exact hp.2
      · intro p₁ _ p₂ _ heq
        have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
      · intro q hq
        simp only [oe2, oeSet, onSet, Finset.mem_filter] at hq
        refine ⟨((q.1 - 1) / 2 + 1, q.2 / 2), ?_, ?_⟩
        · simp only [hBdyL, Finset.mem_filter, mem_Aset]
          have hqf : A k ((q.1 - 1) / 2) (q.2 / 2) = false := Bool.eq_false_iff.mpr hq.2
          have hc := hq.1.1.2
          rw [show q.1 = 2 * ((q.1 - 1) / 2) + 1 by omega, show q.2 = 2 * (q.2 / 2) by omega,
            h_oe, hqf, Bool.false_xor] at hc
          refine ⟨hc, ?_⟩
          rw [add_sub_cancel_right]
          exact hq.2
        · ext <;> dsimp only <;> omega
  have heo_card : eoSet.card = vBdyU.card + vBdyD.card := by
    set eo1 : Finset (ℤ × ℤ) := eoSet.filter (fun q => A k (q.1 / 2) ((q.2 - 1) / 2) = true)
    set eo2 : Finset (ℤ × ℤ) := eoSet.filter (fun q => A k (q.1 / 2) ((q.2 - 1) / 2) ≠ true)
    have hsplit : eoSet.card = eo1.card + eo2.card :=
      (card_filter_split (s := eoSet)
        (p := fun q => A k (q.1 / 2) ((q.2 - 1) / 2) = true)).symm
    rw [hsplit]
    congr 1
    · symm
      refine Finset.card_bij (fun p _ => (2 * p.1, 2 * p.2 + 1)) ?_ ?_ ?_
      · intro p hp
        simp only [vBdyU, Finset.mem_filter, mem_Aset] at hp
        have hcone := A_cone hp.1
        have hp2f : A k p.1 (p.2 + 1) = false := Bool.eq_false_iff.mpr hp.2
        simp only [eo1, eoSet, onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc]
        refine ⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩, ?_⟩
        · rw [h_eo, hp.1, hp2f]; rfl
        · rw [show (2 * p.1) / 2 = p.1 by omega, show (2 * p.2 + 1 - 1) / 2 = p.2 by omega]; exact hp.1
      · intro p₁ _ p₂ _ heq
        have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
      · intro q hq
        simp only [eo1, eoSet, onSet, Finset.mem_filter] at hq
        refine ⟨(q.1 / 2, (q.2 - 1) / 2), ?_, ?_⟩
        · simp only [vBdyU, Finset.mem_filter, mem_Aset]
          refine ⟨hq.2, ?_⟩
          intro hbad
          have hc := hq.1.1.2
          rw [show q.1 = 2 * (q.1 / 2) by omega, show q.2 = 2 * ((q.2 - 1) / 2) + 1 by omega,
            h_eo, hq.2, hbad] at hc
          exact Bool.false_ne_true hc
        · ext <;> dsimp only <;> omega
    · symm
      refine Finset.card_bij (fun p _ => (2 * p.1, 2 * p.2 - 1)) ?_ ?_ ?_
      · intro p hp
        simp only [vBdyD, Finset.mem_filter, mem_Aset] at hp
        have hcone := A_cone hp.1
        have hp2f : A k p.1 (p.2 - 1) = false := Bool.eq_false_iff.mpr hp.2
        simp only [eo2, eoSet, onSet, boxB, Finset.mem_filter, Finset.mem_product, mem_zIcc]
        refine ⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩, ?_⟩
        · rw [show 2 * p.2 - 1 = 2 * (p.2 - 1) + 1 by ring, h_eo, hp2f,
            show p.2 - 1 + 1 = p.2 by ring, hp.1]; rfl
        · rw [show (2 * p.1) / 2 = p.1 by omega, show (2 * p.2 - 1 - 1) / 2 = p.2 - 1 by omega]
          exact hp.2
      · intro p₁ _ p₂ _ heq
        have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
      · intro q hq
        simp only [eo2, eoSet, onSet, Finset.mem_filter] at hq
        refine ⟨(q.1 / 2, (q.2 - 1) / 2 + 1), ?_, ?_⟩
        · simp only [vBdyD, Finset.mem_filter, mem_Aset]
          have hqf : A k (q.1 / 2) ((q.2 - 1) / 2) = false := Bool.eq_false_iff.mpr hq.2
          have hc := hq.1.1.2
          rw [show q.1 = 2 * (q.1 / 2) by omega, show q.2 = 2 * ((q.2 - 1) / 2) + 1 by omega,
            h_eo, hqf, Bool.false_xor] at hc
          refine ⟨hc, ?_⟩
          rw [add_sub_cancel_right]
          exact hq.2
        · ext <;> dsimp only <;> omega
  have hhR : ((Aset k).filter (fun p => (p.1 + 1, p.2) ∈ Aset k)).card + hBdyR.card = (Aset k).card :=
    card_filter_split (s := Aset k) (p := fun p => (p.1 + 1, p.2) ∈ Aset k)
  have hhL : ((Aset k).filter (fun p => (p.1 - 1, p.2) ∈ Aset k)).card + hBdyL.card = (Aset k).card :=
    card_filter_split (s := Aset k) (p := fun p => (p.1 - 1, p.2) ∈ Aset k)
  have hvU : ((Aset k).filter (fun p => (p.1, p.2 + 1) ∈ Aset k)).card + vBdyU.card = (Aset k).card :=
    card_filter_split (s := Aset k) (p := fun p => (p.1, p.2 + 1) ∈ Aset k)
  have hvD : ((Aset k).filter (fun p => (p.1, p.2 - 1) ∈ Aset k)).card + vBdyD.card = (Aset k).card :=
    card_filter_split (s := Aset k) (p := fun p => (p.1, p.2 - 1) ∈ Aset k)
  have hh_eq : ((Aset k).filter (fun p => (p.1 - 1, p.2) ∈ Aset k)).card =
      ((Aset k).filter (fun p => (p.1 + 1, p.2) ∈ Aset k)).card := by
    refine Finset.card_bij (fun p _ => (p.1 - 1, p.2)) ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.2, by simpa using hp.1⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [Finset.mem_filter] at hq
      exact ⟨(q.1 + 1, q.2), Finset.mem_filter.mpr ⟨hq.2, by simpa using hq.1⟩, by ext <;> simp⟩
  have hv_eq : ((Aset k).filter (fun p => (p.1, p.2 - 1) ∈ Aset k)).card =
      ((Aset k).filter (fun p => (p.1, p.2 + 1) ∈ Aset k)).card := by
    refine Finset.card_bij (fun p _ => (p.1, p.2 - 1)) ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.2, by simpa using hp.1⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [Finset.mem_filter] at hq
      exact ⟨(q.1, q.2 + 1), Finset.mem_filter.mpr ⟨hq.2, by simpa using hq.1⟩, by ext <;> simp⟩
  rw [hon_card, hon_sum, hee_card, hoe_card, heo_card, edgesOf]
  omega

-- Helper lemmas for edgesOf under translation, rotation, and disjoint union
private lemma edgesOf_image_shift (S : Finset (ℤ × ℤ)) (dx dy : ℤ) :
    edgesOf (S.image (fun p => (p.1 + dx, p.2 + dy))) = edgesOf S := by
  set T := S.image (fun p => (p.1 + dx, p.2 + dy))
  have hmem : ∀ a b : ℤ, (a + dx, b + dy) ∈ T ↔ (a, b) ∈ S := by
    intro a b
    simp only [T, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨u, v⟩, huv, h1, h2⟩
      have : u = a := by omega
      have : v = b := by omega
      subst this; simpa [‹u = a›] using huv
    · intro h; exact ⟨(a, b), h, rfl, rfl⟩
  simp only [edgesOf]
  congr 1
  · symm
    refine Finset.card_bij (fun p _ => (p.1 + dx, p.2 + dy)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨(hmem p.1 p.2).mpr hp.1, ?_⟩
      rw [show p.1 + dx + 1 = (p.1 + 1) + dx by ring]
      exact (hmem (p.1 + 1) p.2).mpr hp.2
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq
      simp only [Finset.mem_filter] at hq
      rcases Finset.mem_image.mp hq.1 with ⟨p, hp, rfl⟩
      refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
      have hq2 := hq.2
      dsimp only at hq2
      rw [show p.1 + dx + 1 = (p.1 + 1) + dx by ring] at hq2
      exact (hmem (p.1 + 1) p.2).mp hq2
  · symm
    refine Finset.card_bij (fun p _ => (p.1 + dx, p.2 + dy)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨(hmem p.1 p.2).mpr hp.1, ?_⟩
      rw [show p.2 + dy + 1 = (p.2 + 1) + dy by ring]
      exact (hmem p.1 (p.2 + 1)).mpr hp.2
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq
      simp only [Finset.mem_filter] at hq
      rcases Finset.mem_image.mp hq.1 with ⟨p, hp, rfl⟩
      refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
      have hq2 := hq.2
      dsimp only at hq2
      rw [show p.2 + dy + 1 = (p.2 + 1) + dy by ring] at hq2
      exact (hmem p.1 (p.2 + 1)).mp hq2

private lemma edgesOf_sym_x {S T : Finset (ℤ × ℤ)}
    (h : ∀ x y : ℤ, (x, y) ∈ T ↔ (-x, y) ∈ S) : edgesOf T = edgesOf S := by
  simp only [edgesOf]
  congr 1
  · refine Finset.card_bij (fun p _ => (-p.1 - 1, p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨?_, ?_⟩
      · have h2 := (h (p.1 + 1) p.2).mp hp.2
        rwa [show -(p.1 + 1) = -p.1 - 1 by ring] at h2
      · rw [show -p.1 - 1 + 1 = -p.1 by ring]; exact (h p.1 p.2).mp hp.1
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq
      simp only [Finset.mem_filter] at hq
      refine ⟨(-q.1 - 1, q.2), ?_, by ext; (dsimp only; ring); rfl⟩
      simp only [Finset.mem_filter]
      refine ⟨(h (-q.1 - 1) q.2).mpr (by rw [show -(-q.1 - 1) = q.1 + 1 by ring]; exact hq.2), ?_⟩
      rw [show -q.1 - 1 + 1 = -q.1 by ring]
      exact (h (-q.1) q.2).mpr (by rw [neg_neg]; exact hq.1)
  · refine Finset.card_bij (fun p _ => (-p.1, p.2)) ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter] at hp ⊢
      exact ⟨(h p.1 p.2).mp hp.1, (h p.1 (p.2 + 1)).mp hp.2⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [Finset.mem_filter] at hq
      refine ⟨(-q.1, q.2), Finset.mem_filter.mpr ⟨(h (-q.1) q.2).mpr (by simpa using hq.1),
        (h (-q.1) (q.2 + 1)).mpr (by simpa using hq.2)⟩, by ext <;> simp⟩

private lemma edgesOf_sym_t {S T : Finset (ℤ × ℤ)}
    (h : ∀ x y : ℤ, (x, y) ∈ T ↔ (y, x) ∈ S) : edgesOf T = edgesOf S := by
  simp only [edgesOf]
  rw [add_comm]
  congr 1
  · refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter] at hp ⊢
      exact ⟨(h p.1 p.2).mp hp.1, (h p.1 (p.2 + 1)).mp hp.2⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [Finset.mem_filter] at hq
      exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨(h q.2 q.1).mpr hq.1, (h q.2 (q.1 + 1)).mpr hq.2⟩, by ext <;> simp⟩
  · refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter] at hp ⊢
      exact ⟨(h p.1 p.2).mp hp.1, (h (p.1 + 1) p.2).mp hp.2⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [Finset.mem_filter] at hq
      exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨(h q.2 q.1).mpr hq.1, (h (q.2 + 1) q.1).mpr hq.2⟩, by ext <;> simp⟩

private lemma edgesOf_union_no_cross {S T : Finset (ℤ × ℤ)}
    (hdisj : Disjoint S T)
    (hnc : ∀ p ∈ S, ∀ q ∈ T, ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1) :
    edgesOf (S ∪ T) = edgesOf S + edgesOf T := by
  simp only [edgesOf]
  have hh : ((S ∪ T).filter (fun p => (p.1 + 1, p.2) ∈ S ∪ T)) =
      (S.filter (fun p => (p.1 + 1, p.2) ∈ S)) ∪ (T.filter (fun p => (p.1 + 1, p.2) ∈ T)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpS | hpT, hqS | hqT⟩
      · exact Or.inl ⟨hpS, hqS⟩
      · exfalso; exact hnc p hpS (p.1 + 1, p.2) hqT (by simp)
      · exfalso; exact hnc (p.1 + 1, p.2) hqS p hpT (by simp)
      · exact Or.inr ⟨hpT, hqT⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, Or.inl h2⟩
      · exact ⟨Or.inr h1, Or.inr h2⟩
  have hv : ((S ∪ T).filter (fun p => (p.1, p.2 + 1) ∈ S ∪ T)) =
      (S.filter (fun p => (p.1, p.2 + 1) ∈ S)) ∪ (T.filter (fun p => (p.1, p.2 + 1) ∈ T)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpS | hpT, hqS | hqT⟩
      · exact Or.inl ⟨hpS, hqS⟩
      · exfalso; exact hnc p hpS (p.1, p.2 + 1) hqT (by simp)
      · exfalso; exact hnc (p.1, p.2 + 1) hqS p hpT (by simp)
      · exact Or.inr ⟨hpT, hqT⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, Or.inl h2⟩
      · exact ⟨Or.inr h1, Or.inr h2⟩
  have hd1 : Disjoint (S.filter (fun p => (p.1 + 1, p.2) ∈ S))
      (T.filter (fun p => (p.1 + 1, p.2) ∈ T)) :=
    Finset.disjoint_filter_filter hdisj
  have hd2 : Disjoint (S.filter (fun p => (p.1, p.2 + 1) ∈ S))
      (T.filter (fun p => (p.1, p.2 + 1) ∈ T)) :=
    Finset.disjoint_filter_filter hdisj
  rw [hh, hv, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
  omega

-- Step <1>4(1): N(K) = (4^K - 1) / 3
private def Nset (K : ℕ) : Finset (ℤ × ℤ) :=
  (zIcc 1 ((2 ^ K : ℕ) : ℤ) ×ˢ zIcc (-((2 ^ K : ℕ) : ℤ)) ((2 ^ K : ℕ) : ℤ)).filter
    (fun p => (p.2.natAbs : ℤ) < p.1 ∧ p.1 + (p.2.natAbs : ℤ) < (2 ^ K : ℕ) ∧
      (p.2 = 0 ∨ v2Nat p.1.natAbs ≠ v2Nat p.2.natAbs))

private lemma mem_Nset {K : ℕ} {p : ℤ × ℤ} :
    p ∈ Nset K ↔
      (p.2.natAbs : ℤ) < p.1 ∧ p.1 + (p.2.natAbs : ℤ) < (2 ^ K : ℕ) ∧
      (p.2 = 0 ∨ v2Nat p.1.natAbs ≠ v2Nat p.2.natAbs) := by
  simp only [Nset, Finset.mem_filter, Finset.mem_product, mem_zIcc, and_iff_right_iff_imp]
  intro h
  omega

private lemma Nset_card : ∀ K : ℕ, 3 * (Nset K).card + 1 = 4 ^ K := by
  intro K
  induction K with
  | zero =>
    have h0 : Nset 0 = ∅ := by
      ext p; simp only [mem_Nset, pow_zero, Nat.cast_one, Finset.notMem_empty, iff_false]; omega
    rw [h0]; simp
  | succ K ih =>
    set R : ℕ := 2 ^ K
    have hR_pos : 1 ≤ R := Nat.one_le_pow K 2 (by omega)
    have h2R : ((2 ^ (K + 1) : ℕ) : ℤ) = 2 * (R : ℤ) := by
      have : 2 ^ (K + 1) = 2 * R := by rw [pow_succ]; ring
      exact_mod_cast this
    have hstep : (Nset (K + 1)).card = 4 * (Nset K).card + 1 := by
      set P1 := (Nset (K + 1)).filter (fun p => p.1 + (p.2.natAbs : ℤ) < (R : ℤ))
      set P2 := (Nset (K + 1)).filter (fun p => p.1 + (p.2.natAbs : ℤ) = (R : ℤ))
      set P3a := (Nset (K + 1)).filter (fun p => (R : ℤ) < p.1 + (p.2.natAbs : ℤ) ∧ (p.2.natAbs : ℤ) < p.1 - (R : ℤ))
      set P3b := (Nset (K + 1)).filter (fun p => (R : ℤ) < p.1 + (p.2.natAbs : ℤ) ∧ ((p.1 - (R : ℤ)).natAbs : ℤ) < p.2)
      set P3c := (Nset (K + 1)).filter (fun p => (R : ℤ) < p.1 + (p.2.natAbs : ℤ) ∧ ((p.1 - (R : ℤ)).natAbs : ℤ) < -p.2)
      have hP1 : P1 = Nset K := by
        ext p; simp only [P1, Finset.mem_filter, mem_Nset, h2R]; constructor <;> intro h <;>
          [exact ⟨h.1.1, h.2, h.1.2.2⟩; exact ⟨⟨h.1, by omega, h.2.2⟩, h.2.1⟩]
      have hP2 : P2 = {((R : ℤ), 0)} := by
        ext p
        simp only [P2, Finset.mem_filter, mem_Nset, Finset.mem_singleton, h2R]
        constructor
        · rintro ⟨⟨h1, _, h3⟩, heq⟩
          by_cases hy0 : p.2 = 0
          · ext <;> dsimp only <;> omega
          · exfalso
            rcases h3 with hy | hv
            · exact hy0 hy
            · have ha0 : 0 < p.1.natAbs := by omega
              have halt : p.1.natAbs < 2 ^ K := by omega
              have hsub := (v2Nat_sub_pow_two (m := K) ha0 (by rw [pow_succ]; omega) (by omega)).2
              have habs : ((p.1.natAbs : ℤ) - ((2 ^ K : ℕ) : ℤ)).natAbs = p.2.natAbs := by omega
              rw [habs] at hsub
              exact hv hsub.symm
        · rintro rfl
          refine ⟨⟨by omega, by omega, Or.inl rfl⟩, by omega⟩
      have hshift_ok : ∀ p : ℤ × ℤ, (p.2.natAbs : ℤ) < p.1 → (R : ℤ) < p.1 + (p.2.natAbs : ℤ) →
          p.1 + (p.2.natAbs : ℤ) < 2 * (R : ℤ) →
          ((p.2 = 0 ∨ v2Nat p.1.natAbs ≠ v2Nat p.2.natAbs) ↔
           ((p.1 - (R : ℤ) = 0 ∧ p.2 ≠ 0) ∨ p.2 = 0 ∨
             (p.1 - (R : ℤ) ≠ 0 ∧ v2Nat (p.1 - (R : ℤ)).natAbs ≠ v2Nat p.2.natAbs))) := by
        intro p h1 h2 h3
        by_cases hy0 : p.2 = 0
        · simp [hy0]
        · by_cases hxR : p.1 = (R : ℤ)
          · have hylt : p.2.natAbs < 2 ^ K := by omega
            have hypos : 0 < p.2.natAbs := Int.natAbs_pos.mpr hy0
            have hvlt : v2Nat p.2.natAbs < K := v2Nat_lt_of_lt_pow_two hypos hylt
            have hvp : v2Nat (R : ℤ).natAbs = K := by
              rw [Int.natAbs_natCast]; exact v2Nat_pow_two K
            simp only [hxR, sub_self, hy0, ne_eq, not_false_eq_true, and_self, true_or,
              iff_true, false_or]
            rw [hvp]; omega
          · have ha0 : 0 < p.1.natAbs := by omega
            have halt : p.1.natAbs < 2 ^ (K + 1) := by rw [pow_succ]; omega
            have hane : p.1.natAbs ≠ 2 ^ K := by omega
            have hv := (v2Nat_sub_pow_two (m := K) ha0 halt hane).2
            have habs : ((p.1.natAbs : ℤ) - ((2 ^ K : ℕ) : ℤ)).natAbs = (p.1 - (R : ℤ)).natAbs := by
              rw [show (p.1.natAbs : ℤ) = p.1 by omega]
            rw [habs] at hv
            have hne : p.1 - (R : ℤ) ≠ 0 := by omega
            simp only [hy0, eq_false hne, eq_true hne, false_and, false_or, true_and, hv]
      have hP3a : P3a.card = (Nset K).card := by
        refine Finset.card_bij (fun p _ => (p.1 - (R : ℤ), p.2)) ?_ ?_ ?_
        · intro p hp
          simp only [P3a, Finset.mem_filter, mem_Nset, h2R] at hp ⊢
          have hs := (hshift_ok p hp.1.1 hp.2.1 hp.1.2.1).mp hp.1.2.2
          refine ⟨hp.2.2, by omega, ?_⟩
          rcases hs with ⟨h0, _⟩ | hy | ⟨_, hv⟩
          · omega
          · exact Or.inl hy
          · exact Or.inr hv
        · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
        · intro q hq
          rw [mem_Nset] at hq
          refine ⟨(q.1 + (R : ℤ), q.2), ?_, by ext <;> simp⟩
          simp only [P3a, Finset.mem_filter, mem_Nset, h2R]
          have hs := (hshift_ok (q.1 + (R : ℤ), q.2) (by omega) (by omega) (by omega)).mpr
            (by
              rw [add_sub_cancel_right]
              rcases hq.2.2 with hy | hv
              · exact Or.inr (Or.inl hy)
              · exact Or.inr (Or.inr ⟨by omega, hv⟩))
          exact ⟨⟨by omega, by omega, hs⟩, by omega, by simp only [add_sub_cancel_right]; omega⟩
      have hP3b : P3b.card = (Nset K).card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1 - (R : ℤ))) ?_ ?_ ?_
        · intro p hp
          simp only [P3b, Finset.mem_filter, mem_Nset, h2R] at hp ⊢
          have hs := (hshift_ok p hp.1.1 hp.2.1 hp.1.2.1).mp hp.1.2.2
          refine ⟨hp.2.2, by omega, ?_⟩
          rcases hs with ⟨h0, _⟩ | hy | ⟨_, hv⟩
          · exact Or.inl h0
          · omega
          · exact Or.inr (Ne.symm hv)
        · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
        · intro q hq
          rw [mem_Nset] at hq
          refine ⟨(q.2 + (R : ℤ), q.1), ?_, by ext <;> simp⟩
          simp only [P3b, Finset.mem_filter, mem_Nset, h2R]
          have hs := (hshift_ok (q.2 + (R : ℤ), q.1) (by omega) (by omega) (by omega)).mpr
            (by
              rw [add_sub_cancel_right]
              by_cases hq2 : q.2 = 0
              · exact Or.inl ⟨hq2, by omega⟩
              · rcases hq.2.2 with h0 | hv
                · exact Or.inl ⟨h0, by omega⟩
                · exact Or.inr (Or.inr ⟨hq2, Ne.symm hv⟩))
          exact ⟨⟨by omega, by omega, hs⟩, by omega, by simp only [add_sub_cancel_right]; omega⟩
      have hP3c : P3c.card = (Nset K).card := by
        refine Finset.card_bij (fun p _ => (-p.2, p.1 - (R : ℤ))) ?_ ?_ ?_
        · intro p hp
          simp only [P3c, Finset.mem_filter, mem_Nset, h2R] at hp ⊢
          have hs := (hshift_ok p hp.1.1 hp.2.1 hp.1.2.1).mp hp.1.2.2
          refine ⟨hp.2.2, by omega, ?_⟩
          rw [Int.natAbs_neg]
          rcases hs with ⟨h0, _⟩ | hy | ⟨_, hv⟩
          · exact Or.inl h0
          · omega
          · exact Or.inr (Ne.symm hv)
        · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
        · intro q hq
          rw [mem_Nset] at hq
          refine ⟨(q.2 + (R : ℤ), -q.1), ?_, by ext <;> simp⟩
          simp only [P3c, Finset.mem_filter, mem_Nset, h2R]
          have hs := (hshift_ok (q.2 + (R : ℤ), -q.1) (by omega) (by omega) (by omega)).mpr
            (by
              rw [add_sub_cancel_right, Int.natAbs_neg]
              by_cases hq2 : q.2 = 0
              · exact Or.inl ⟨hq2, by omega⟩
              · rcases hq.2.2 with h0 | hv
                · exact Or.inl ⟨h0, by omega⟩
                · exact Or.inr (Or.inr ⟨hq2, Ne.symm hv⟩))
          exact ⟨⟨by omega, by omega, hs⟩, by omega, by simp only [add_sub_cancel_right]; omega⟩
      have hunion : Nset (K + 1) = P1 ∪ (P2 ∪ (P3a ∪ (P3b ∪ P3c))) := by
        ext p
        simp only [P1, P2, P3a, P3b, P3c, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hp
          have hm := mem_Nset.mp hp
          rw [h2R] at hm
          by_cases hlt : p.1 + (p.2.natAbs : ℤ) < (R : ℤ)
          · exact Or.inl ⟨hp, hlt⟩
          · by_cases heq : p.1 + (p.2.natAbs : ℤ) = (R : ℤ)
            · exact Or.inr (Or.inl ⟨hp, heq⟩)
            · have hgt : (R : ℤ) < p.1 + (p.2.natAbs : ℤ) := by omega
              by_cases ha : (p.2.natAbs : ℤ) < p.1 - (R : ℤ)
              · exact Or.inr (Or.inr (Or.inl ⟨hp, hgt, ha⟩))
              · by_cases hb : ((p.1 - (R : ℤ)).natAbs : ℤ) < p.2
                · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hgt, hb⟩)))
                · by_cases hc : ((p.1 - (R : ℤ)).natAbs : ℤ) < -p.2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hgt, hc⟩)))
                  · exfalso
                    have heq_abs : ((p.1 - (R : ℤ)).natAbs : ℤ) = (p.2.natAbs : ℤ) := by omega
                    have hs := (hshift_ok p hm.1 hgt hm.2.1).mp hm.2.2
                    rcases hs with ⟨h0, hne⟩ | hy0 | ⟨hne, hv⟩
                    · omega
                    · omega
                    · have : (p.1 - (R : ℤ)).natAbs = p.2.natAbs := by omega
                      exact hv (congrArg v2Nat this)
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      have hd1 : Disjoint P1 (P2 ∪ (P3a ∪ (P3b ∪ P3c))) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P1, P2, P3a, P3b, P3c, Finset.mem_union, Finset.mem_filter] at h1 h2
        rcases h2 with ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
      have hd2 : Disjoint P2 (P3a ∪ (P3b ∪ P3c)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P2, P3a, P3b, P3c, Finset.mem_union, Finset.mem_filter] at h1 h2
        rcases h2 with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
      have hd3 : Disjoint P3a (P3b ∪ P3c) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P3a, P3b, P3c, Finset.mem_union, Finset.mem_filter] at h1 h2
        rcases h2 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
      have hd4 : Disjoint P3b P3c := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P3b, P3c, Finset.mem_filter] at h1 h2; omega
      rw [hunion, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
        Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd4,
        hP1, hP2, Finset.card_singleton, hP3a, hP3b, hP3c]
      omega
    rw [hstep, pow_succ]
    omega

-- Step <1>4(2): F_{C, d} cell and edge counts
private def coneBox (d : ℕ) : Finset (ℤ × ℤ) :=
  (zIcc 1 (d : ℤ) ×ˢ zIcc (-(d : ℤ)) (d : ℤ)).filter
    (fun p => (p.2.natAbs : ℤ) < p.1 ∧ p.1 + (p.2.natAbs : ℤ) ≤ (d : ℤ))

private lemma mem_coneBox {d : ℕ} {p : ℤ × ℤ} :
    p ∈ coneBox d ↔ (p.2.natAbs : ℤ) < p.1 ∧ p.1 + (p.2.natAbs : ℤ) ≤ (d : ℤ) := by
  simp only [coneBox, Finset.mem_filter, Finset.mem_product, mem_zIcc, and_iff_right_iff_imp]
  intro h; omega

private def Fodd (d : ℕ) : Finset (ℤ × ℤ) :=
  (coneBox d).filter (fun p => (p.1 + p.2) % 2 ≠ 0)

private lemma Fodd_even_card : ∀ h : ℕ, (Fodd (2 * h)).card = h ^ 2 := by
  intro h
  induction h with
  | zero =>
    have h0 : Fodd 0 = ∅ := by
      ext p; simp only [Fodd, Finset.mem_filter, mem_coneBox, Finset.notMem_empty, iff_false]; omega
    rw [h0]; simp
  | succ h ih =>
    set ringSet := (Fodd (2 * (h + 1))).filter (fun p => p.1 + (p.2.natAbs : ℤ) = 2 * (h : ℤ) + 1)
    have hpart : Fodd (2 * (h + 1)) = Fodd (2 * h) ∪ ringSet := by
      ext p
      simp only [Fodd, ringSet, Finset.mem_union, Finset.mem_filter, mem_coneBox]
      constructor
      · rintro ⟨⟨h1, h2⟩, hodd⟩
        by_cases hle : p.1 + (p.2.natAbs : ℤ) ≤ (2 * h : ℕ)
        · exact Or.inl ⟨⟨h1, hle⟩, hodd⟩
        · exact Or.inr ⟨⟨⟨h1, h2⟩, hodd⟩, by omega⟩
      · rintro (⟨⟨h1, h2⟩, hodd⟩ | ⟨hp, _⟩)
        · exact ⟨⟨h1, by omega⟩, hodd⟩
        · exact hp
    have hdisj : Disjoint (Fodd (2 * h)) ringSet := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [Fodd, ringSet, Finset.mem_filter, mem_coneBox] at h1 h2; omega
    have hring_card : ringSet.card = 2 * h + 1 := by
      have hIcc : (Finset.Icc (-(h : ℤ)) (h : ℤ)).card = 2 * h + 1 := by
        rw [Int.card_Icc]; omega
      rw [← hIcc]
      symm
      refine Finset.card_bij (fun y _ => (2 * (h : ℤ) + 1 - (y.natAbs : ℤ), y)) ?_ ?_ ?_
      · intro y hy
        rw [Finset.mem_Icc] at hy
        simp only [ringSet, Fodd, Finset.mem_filter, mem_coneBox]
        exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
      · intro y₁ _ y₂ _ heq; exact congrArg Prod.snd heq
      · intro p hp
        simp only [ringSet, Fodd, Finset.mem_filter, mem_coneBox] at hp
        refine ⟨p.2, Finset.mem_Icc.mpr (by omega), ?_⟩
        ext
        · dsimp only; omega
        · rfl
    rw [hpart, Finset.card_union_of_disjoint hdisj, ih, hring_card]
    ring

private def FCset (m : ℕ) : Finset (ℤ × ℤ) :=
  (coneBox (2 ^ (m - 1))).filter (fun p => F p.1 p.2 = true)

private lemma FCset_counts {m : ℕ} (hm : 3 ≤ m) :
    3 * (FCset m).card = 13 * 4 ^ (m - 3) + 2 ∧
    3 * edgesOf (FCset m) + 1 = 4 ^ (m - 2) := by
  set d : ℕ := 2 ^ (m - 1)
  have hm1 : 2 ≤ m - 1 := by omega
  have hpow3_pos : 1 ≤ 2 ^ (m - 3) := Nat.one_le_pow (m - 3) 2 (by omega)
  have hd_eq : d = 4 * 2 ^ (m - 3) := by
    have : m - 1 = (m - 3) + 2 := by omega
    show 2 ^ (m - 1) = 4 * 2 ^ (m - 3)
    rw [this, pow_add]; ring
  have hd_int : (d : ℤ) = 4 * ((2 ^ (m - 3) : ℕ) : ℤ) := by exact_mod_cast hd_eq
  have hd_even : d = 2 * 2 ^ (m - 2) := by
    have : m - 1 = (m - 2) + 1 := by omega
    show 2 ^ (m - 1) = 2 * 2 ^ (m - 2)
    rw [this, pow_succ]; ring
  set Feven := (FCset m).filter (fun p => (p.1 + p.2) % 2 = 0)
  set Fodd' := (FCset m).filter (fun p => (p.1 + p.2) % 2 ≠ 0)
  have hFodd'_eq : Fodd' = Fodd d := by
    ext p
    simp only [Fodd', FCset, Fodd, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hc, _⟩, hodd⟩; exact ⟨hc, hodd⟩
    · rintro ⟨hc, hodd⟩; exact ⟨⟨hc, F_odd hodd⟩, hodd⟩
  have hFodd_card : Fodd'.card = 4 ^ (m - 2) := by
    rw [hFodd'_eq, hd_even, Fodd_even_card]
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set Fint := Feven.filter (fun p => p.1 + (p.2.natAbs : ℤ) < (d : ℤ))
  set Ftip := Feven.filter (fun p => p.1 + (p.2.natAbs : ℤ) = (d : ℤ))
  have hFeven_part : Feven = Fint ∪ Ftip := by
    ext p
    simp only [Fint, Ftip, Feven, FCset, Finset.mem_union, Finset.mem_filter, mem_coneBox]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hF⟩, hev⟩
      by_cases hlt : p.1 + (p.2.natAbs : ℤ) < (d : ℤ)
      · exact Or.inl ⟨⟨⟨⟨h1, h2⟩, hF⟩, hev⟩, hlt⟩
      · exact Or.inr ⟨⟨⟨⟨h1, h2⟩, hF⟩, hev⟩, by omega⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hFeven_disj : Disjoint Fint Ftip := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Fint, Ftip, Finset.mem_filter] at h1 h2; omega
  have hFtip_eq : Ftip = {((d : ℤ), 0)} := by
    ext p
    simp only [Ftip, Feven, FCset, Finset.mem_filter, mem_coneBox, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨⟨h1, _⟩, hF⟩, _⟩, heq⟩
      rw [F_pow2_bd hm1 (by omega), decide_eq_true_eq] at hF
      ext <;> dsimp only <;> omega
    · rintro rfl
      refine ⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩, by omega⟩
      rw [F_pow2_bd hm1 (by omega), decide_eq_true (Or.inr rfl)]
  have hFint_card : Fint.card = (Nset (m - 3)).card := by
    symm
    refine Finset.card_bij (fun q _ => (4 * q.1, 4 * q.2)) ?_ ?_ ?_
    · intro q hq
      rw [mem_Nset] at hq
      simp only [Fint, Feven, FCset, Finset.mem_filter, mem_coneBox]
      have h4q1 : (4 * q.1).natAbs = 4 * q.1.natAbs := by omega
      have h4q2 : (4 * q.2).natAbs = 4 * q.2.natAbs := by omega
      refine ⟨⟨⟨⟨by omega, by change 4 * q.1 + ((4 * q.2).natAbs : ℤ) ≤ (d : ℤ); omega⟩, ?_⟩, by omega⟩,
        by omega⟩
      simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      right
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      by_cases hq2 : q.2 = 0
      · right; left; omega
      · rcases hq.2.2 with h0 | hv
        · right; left; omega
        · right; right
          rw [h4q1, h4q2, v2Nat_mul_four (by omega), v2Nat_mul_four (Nat.ne_of_gt (Int.natAbs_pos.mpr hq2))]
          omega
    · intro q₁ _ q₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro p hp
      simp only [Fint, Feven, FCset, Finset.mem_filter, mem_coneBox] at hp
      have h4 : p.1 % 4 = 0 ∧ p.2 % 4 = 0 ∧ (p.1 = 0 ∨ p.2 = 0 ∨ v2Nat p.1.natAbs ≠ v2Nat p.2.natAbs) := by
        have hF := hp.1.1.2
        simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hF
        rcases hF with hodd | ⟨⟨h1, h2⟩, h3⟩
        · omega
        · exact ⟨h1, h2, h3⟩
      refine ⟨(p.1 / 4, p.2 / 4), ?_, by ext <;> dsimp only <;> omega⟩
      rw [mem_Nset]
      refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
      dsimp only
      by_cases hy0 : p.2 = 0
      · left; omega
      · rcases h4.2.2 with h0 | h0 | hv
        · omega
        · left; omega
        · right
          have hp1 : p.1.natAbs = 4 * (p.1 / 4).natAbs := by omega
          have hp2 : p.2.natAbs = 4 * (p.2 / 4).natAbs := by omega
          rw [hp1, hp2, v2Nat_mul_four (by omega), v2Nat_mul_four (by omega)] at hv
          omega
  have hFC_split : (FCset m).card = Feven.card + Fodd'.card :=
    (card_filter_split (FCset m) (fun p => (p.1 + p.2) % 2 = 0)).symm
  have hN := Nset_card (m - 3)
  have h4pow : 4 ^ (m - 2) = 4 * 4 ^ (m - 3) := by
    rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]; ring
  have hcell : 3 * (FCset m).card = 13 * 4 ^ (m - 3) + 2 := by
    rw [hFC_split, hFeven_part, Finset.card_union_of_disjoint hFeven_disj,
      hFtip_eq, Finset.card_singleton, hFint_card, hFodd_card]
    omega
  -- Edges inside FCset m: bipartite between Feven and Fodd'
  have hedge : 3 * edgesOf (FCset m) + 1 = 4 ^ (m - 2) := by
    -- Partition horizontal and vertical edges by parity of left/bottom endpoint
    have hpar_split : ∀ (dir : ℤ × ℤ), (dir.1 + dir.2) % 2 ≠ 0 →
        ((FCset m).filter (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ FCset m)).card =
        (Feven.filter (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ Fodd')).card +
        (Feven.filter (fun p => (p.1 - dir.1, p.2 - dir.2) ∈ Fodd')).card := by
      intro dir hdir
      set S := (FCset m).filter (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ FCset m)
      have hsp := (card_filter_split (s := S)
        (p := fun p => (p.1 + p.2) % 2 = 0)).symm
      have hpart1 : (S.filter (fun p => (p.1 + p.2) % 2 = 0)).card =
          (Feven.filter (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ Fodd')).card := by
        congr 1
        ext p
        simp only [S, Feven, Fodd', Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, hq⟩, hev⟩; exact ⟨⟨hp, hev⟩, ⟨hq, by omega⟩⟩
        · rintro ⟨⟨hp, hev⟩, ⟨hq, _⟩⟩; exact ⟨⟨hp, hq⟩, hev⟩
      have hpart2 : (S.filter (fun p => ¬ (p.1 + p.2) % 2 = 0)).card =
          (Feven.filter (fun p => (p.1 - dir.1, p.2 - dir.2) ∈ Fodd')).card := by
        refine Finset.card_bij (fun p _ => (p.1 + dir.1, p.2 + dir.2)) ?_ ?_ ?_
        · intro p hp
          simp only [S, Feven, Fodd', Finset.mem_filter] at hp ⊢
          exact ⟨⟨hp.1.2, by omega⟩, ⟨by simpa using hp.1.1, by omega⟩⟩
        · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
        · intro q hq
          simp only [Feven, Fodd', Finset.mem_filter] at hq
          refine ⟨(q.1 - dir.1, q.2 - dir.2), ?_, by ext <;> simp⟩
          simp only [S, Finset.mem_filter]
          exact ⟨⟨hq.2.1, by simpa using hq.1.1⟩, hq.2.2⟩
      rw [hsp, hpart1, hpart2]
    have hdir_count : ∀ dir : ℤ × ℤ, (dir.1.natAbs : ℤ) + (dir.2.natAbs : ℤ) = 1 →
        (Feven.filter (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ Fodd')).card =
        Fint.card + (if dir = (-1, 0) then 1 else 0) := by
      intro dir hdir
      have hsub_int : ∀ p ∈ Fint, (p.1 + dir.1, p.2 + dir.2) ∈ Fodd' := by
        intro p hp
        simp only [Fint, Feven, FCset, Finset.mem_filter, mem_coneBox] at hp
        have h4 : p.1 % 4 = 0 ∧ p.2 % 4 = 0 := by
          have hF := hp.1.1.2
          simp only [F, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hF
          rcases hF with hodd | ⟨h4, _⟩
          · omega
          · exact h4
        have hgap1 : (p.2.natAbs : ℤ) + 4 ≤ p.1 := by omega
        have hgap2 : p.1 + (p.2.natAbs : ℤ) + 4 ≤ (d : ℤ) := by
          have hd4 : (4 : ℤ) ∣ (d : ℤ) := by rw [hd_eq]; push_cast; exact dvd_mul_right 4 _
          omega
        rw [hFodd'_eq]
        simp only [Fodd, Finset.mem_filter, mem_coneBox]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      have htip_check : ((d : ℤ) + dir.1, 0 + dir.2) ∈ Fodd' ↔ dir = (-1, 0) := by
        rw [hFodd'_eq]
        simp only [Fodd, Finset.mem_filter, mem_coneBox]
        constructor
        · rintro ⟨⟨h1, h2⟩, _⟩
          ext <;> dsimp only <;> omega
        · rintro rfl
          exact ⟨⟨by omega, by omega⟩, by omega⟩
      rw [hFeven_part, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hFeven_disj)]
      have h1 : Fint.filter (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ Fodd') = Fint :=
        Finset.filter_true_of_mem hsub_int
      rw [h1, hFtip_eq]
      by_cases hdir_eq : dir = (-1, 0)
      · rw [if_pos hdir_eq]
        have : ({((d : ℤ), 0)} : Finset (ℤ × ℤ)).filter
            (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ Fodd') = {((d : ℤ), 0)} := by
          ext p; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · exact fun h => h.1
          · rintro rfl; exact ⟨rfl, htip_check.mpr hdir_eq⟩
        rw [this, Finset.card_singleton]
      · rw [if_neg hdir_eq]
        have : ({((d : ℤ), 0)} : Finset (ℤ × ℤ)).filter
            (fun p => (p.1 + dir.1, p.2 + dir.2) ∈ Fodd') = ∅ := by
          ext p; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨rfl, hmem⟩
          exact hdir_eq (htip_check.mp hmem)
        rw [this, Finset.card_empty]
    have hh := hpar_split (1, 0) (by decide)
    have hv := hpar_split (0, 1) (by decide)
    have h1 := hdir_count (1, 0) (by decide)
    have h2 := hdir_count (-1, 0) (by decide)
    have h3 := hdir_count (0, 1) (by decide)
    have h4 := hdir_count (0, -1) (by decide)
    have he_eq : edgesOf (FCset m) = 4 * Fint.card + 1 := by
      simp only [edgesOf]
      have hh' : ((FCset m).filter (fun p => (p.1 + 1, p.2) ∈ FCset m)).card =
          (Feven.filter (fun p => (p.1 + 1, p.2) ∈ Fodd')).card +
          (Feven.filter (fun p => (p.1 - 1, p.2) ∈ Fodd')).card := by
        simpa using hh
      have hv' : ((FCset m).filter (fun p => (p.1, p.2 + 1) ∈ FCset m)).card =
          (Feven.filter (fun p => (p.1, p.2 + 1) ∈ Fodd')).card +
          (Feven.filter (fun p => (p.1, p.2 - 1) ∈ Fodd')).card := by
        simpa using hv
      have h1' : (Feven.filter (fun p => (p.1 + 1, p.2) ∈ Fodd')).card = Fint.card := by
        simpa using h1
      have h2' : (Feven.filter (fun p => (p.1 - 1, p.2) ∈ Fodd')).card = Fint.card + 1 := by
        simpa [sub_eq_add_neg] using h2
      have h3' : (Feven.filter (fun p => (p.1, p.2 + 1) ∈ Fodd')).card = Fint.card := by
        simpa using h3
      have h4' : (Feven.filter (fun p => (p.1, p.2 - 1) ∈ Fodd')).card = Fint.card := by
        simpa [sub_eq_add_neg] using h4
      rw [hh', hv', h1', h2', h3', h4']
      omega
    rw [he_eq, hFint_card]
    omega
  exact ⟨hcell, hedge⟩

-- Step <1>4(3): S_C(m) and E_C(m) recurrences
private def SCset (m : ℕ) : Finset (ℤ × ℤ) :=
  (Aset (2 ^ m - 1)).filter (fun p => (p.2.natAbs : ℤ) < p.1)

private lemma mem_SCset {m : ℕ} {p : ℤ × ℤ} :
    p ∈ SCset m ↔ A (2 ^ m - 1) p.1 p.2 = true ∧ (p.2.natAbs : ℤ) < p.1 := by
  simp only [SCset, Finset.mem_filter, mem_Aset]

private lemma SC_and_EC_step {m : ℕ} (hm : 3 ≤ m) :
    (SCset m).card = 3 * (SCset (m - 1)).card + (FCset m).card ∧
    (m = 3 → edgesOf (SCset 3) = 3 * edgesOf (SCset 2) + edgesOf (FCset 3)) ∧
    (4 ≤ m → edgesOf (SCset m) = 3 * edgesOf (SCset (m - 1)) + edgesOf (FCset m) + 3) := by
  set d : ℕ := 2 ^ (m - 1)
  have hm1 : 2 ≤ m - 1 := by omega
  have hd4 : 4 ≤ d := by
    have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) hm1
    simpa [d] using this
  have hAeq : A (2 ^ m - 1) = UG (d : ℤ) (A (d - 1)) := A_pow2_sub_one hm
  set inner := (SCset m).filter (fun p => p.1 + (p.2.natAbs : ℤ) ≤ (d : ℤ))
  set outer := (SCset m).filter (fun p => (d : ℤ) < p.1 + (p.2.natAbs : ℤ))
  have hpart : SCset m = inner ∪ outer := by
    ext p
    simp only [inner, outer, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp; by_cases h : p.1 + (p.2.natAbs : ℤ) ≤ (d : ℤ); exact Or.inl ⟨hp, h⟩; exact Or.inr ⟨hp, by omega⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint inner outer := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [inner, outer, Finset.mem_filter] at h1 h2; omega
  have hinner_eq : inner = FCset m := by
    ext p
    simp only [inner, FCset, Finset.mem_filter, mem_SCset, mem_coneBox, hAeq]
    constructor
    · rintro ⟨⟨hUG, hcone⟩, hle⟩
      rw [UG, if_pos (by omega)] at hUG
      exact ⟨⟨hcone, hle⟩, hUG⟩
    · rintro ⟨⟨hcone, hle⟩, hF⟩
      refine ⟨⟨?_, hcone⟩, hle⟩
      rw [UG, if_pos (by omega)]; exact hF
  -- Decompose outer into 3 disjoint translated cones of A(d - 1)
  set C1 := (Aset (d - 1)).filter (fun q => (q.2.natAbs : ℤ) < q.1)
  set C2 := (Aset (d - 1)).filter (fun q => (q.1.natAbs : ℤ) < q.2)
  set C3 := (Aset (d - 1)).filter (fun q => (q.1.natAbs : ℤ) < -q.2)
  have hC1_eq : C1 = SCset (m - 1) := rfl
  have hC2_card : C2.card = (SCset (m - 1)).card := by
    rw [← hC1_eq]
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq; simp only [C1, C2, Finset.mem_filter, mem_Aset] at hq ⊢
      exact ⟨by rw [A_sym_t]; exact hq.1, hq.2⟩
    · intro q₁ _ q₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [C1, Finset.mem_filter, mem_Aset] at hq
      exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨mem_Aset.mpr (by rw [A_sym_t]; exact hq.1), hq.2⟩, by ext <;> simp⟩
  have hC3_card : C3.card = (SCset (m - 1)).card := by
    rw [← hC1_eq]
    refine Finset.card_bij (fun q _ => (-q.2, q.1)) ?_ ?_ ?_
    · intro q hq; simp only [C1, C3, Finset.mem_filter, mem_Aset] at hq ⊢
      exact ⟨by rw [A_sym_x, A_sym_t]; exact hq.1, hq.2⟩
    · intro q₁ _ q₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [C1, Finset.mem_filter, mem_Aset] at hq
      exact ⟨(q.2, -q.1), Finset.mem_filter.mpr ⟨mem_Aset.mpr (by rw [A_sym_y, A_sym_t]; exact hq.1), by simpa using hq.2⟩, by ext <;> simp⟩
  have hC12 : Disjoint C1 C2 := by
    rw [Finset.disjoint_left]; intro q h1 h2; simp only [C1, C2, Finset.mem_filter] at h1 h2; omega
  have hC13 : Disjoint C1 C3 := by
    rw [Finset.disjoint_left]; intro q h1 h2; simp only [C1, C3, Finset.mem_filter] at h1 h2; omega
  have hC23 : Disjoint C2 C3 := by
    rw [Finset.disjoint_left]; intro q h1 h2; simp only [C2, C3, Finset.mem_filter] at h1 h2; omega
  set C123 := C1 ∪ (C2 ∪ C3)
  have houter_eq : outer = C123.image (fun q => (q.1 + (d : ℤ), q.2)) := by
    ext p
    simp only [outer, C123, C1, C2, C3, Finset.mem_filter, mem_SCset, Finset.mem_image,
      Finset.mem_union, mem_Aset, hAeq]
    constructor
    · rintro ⟨⟨hUG, hcone⟩, hgt⟩
      rw [UG, if_neg (by omega), if_pos hcone] at hUG
      refine ⟨(p.1 - (d : ℤ), p.2), ?_, by ext <;> simp⟩
      by_cases h1 : (p.2.natAbs : ℤ) < p.1 - (d : ℤ)
      · exact Or.inl ⟨hUG, h1⟩
      · by_cases h2 : ((p.1 - (d : ℤ)).natAbs : ℤ) < p.2
        · exact Or.inr (Or.inl ⟨hUG, h2⟩)
        · by_cases h3 : ((p.1 - (d : ℤ)).natAbs : ℤ) < -p.2
          · exact Or.inr (Or.inr ⟨hUG, h3⟩)
          · exfalso
            have habs : ((p.1 - (d : ℤ)).natAbs : ℤ) = (p.2.natAbs : ℤ) := by omega
            have hne : p.1 - (d : ℤ) ≠ 0 := by omega
            have hf := A_diag (d - 1) habs hne
            rw [hUG] at hf
            exact Bool.false_ne_true hf.symm
    · rintro ⟨q, (⟨hq, h1⟩ | ⟨hq, h2⟩ | ⟨hq, h3⟩), rfl⟩
      all_goals
        have hq_cone := A_cone hq
        refine ⟨⟨?_, by omega⟩, by omega⟩
        rw [UG, if_neg (by omega), if_pos (by omega)]
        simpa using hq
  have hC123_card : C123.card = 3 * (SCset (m - 1)).card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hC12, hC13⟩),
      Finset.card_union_of_disjoint hC23, hC1_eq, hC2_card, hC3_card]
    omega
  have houter_card : outer.card = 3 * (SCset (m - 1)).card := by
    rw [houter_eq, Finset.card_image_of_injective _ (fun q₁ q₂ h => by
      have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; ext <;> omega), hC123_card]
  have hcell : (SCset m).card = 3 * (SCset (m - 1)).card + (FCset m).card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj, hinner_eq, houter_card]
    omega
  have hC2_edges : edgesOf C2 = edgesOf (SCset (m - 1)) := by
    rw [← hC1_eq]
    apply edgesOf_sym_t
    intro x y
    simp only [C1, C2, Finset.mem_filter, mem_Aset]
    rw [A_sym_t]
  have hC3_edges : edgesOf C3 = edgesOf (SCset (m - 1)) := by
    rw [← hC1_eq]
    have h1 := edgesOf_sym_t (S := C1) (T := C3.image (fun p => (p.1, -p.2))) (by
      intro x y
      simp only [C1, C3, Finset.mem_image, Finset.mem_filter, mem_Aset, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨hA, hb⟩, rfl, rfl⟩
        exact ⟨by rw [A_sym_x, A_sym_t]; exact hA, by omega⟩
      · rintro ⟨hA, hxy⟩
        exact ⟨(x, -y), ⟨by rw [A_sym_y, A_sym_t]; exact hA, by omega⟩, rfl, by ring⟩)
    rw [← h1]
    symm
    have h2 : edgesOf (C3.image (fun p => (-p.2, p.1))) = edgesOf C3 := by
      have ha := edgesOf_sym_x (S := C3.image (fun p => (p.2, p.1)))
        (T := C3.image (fun p => (-p.2, p.1))) (by
          intro x y
          simp only [Finset.mem_image, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact ⟨(a, b), h, by ring, rfl⟩
          · rintro ⟨⟨a, b⟩, h, h1, rfl⟩; exact ⟨(a, b), h, by omega, rfl⟩)
      have hb := edgesOf_sym_t (S := C3) (T := C3.image (fun p => (p.2, p.1))) (by
        intro x y
        simp only [Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact h
        · intro h; exact ⟨(y, x), h, rfl, rfl⟩)
      rw [ha, hb]
    rw [← h2]
    apply edgesOf_sym_t
    intro x y
    simp only [Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact ⟨(a, b), h, rfl, rfl⟩
    · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact ⟨(a, b), h, rfl, rfl⟩
  have houter_edges : edgesOf outer = 3 * edgesOf (SCset (m - 1)) := by
    have hsh : outer = C123.image (fun q => (q.1 + (d : ℤ), q.2 + 0)) := by
      rw [houter_eq]; congr 1; funext q; simp
    rw [hsh, edgesOf_image_shift]
    have hnc1 : ∀ p ∈ C1, ∀ q ∈ C2 ∪ C3, ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1 := by
      intro p hp q hq
      simp only [C1, C2, C3, Finset.mem_union, Finset.mem_filter] at hp hq
      rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> omega
    have hnc2 : ∀ p ∈ C2, ∀ q ∈ C3, ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1 := by
      intro p hp q hq
      simp only [C2, C3, Finset.mem_filter] at hp hq; omega
    rw [edgesOf_union_no_cross (Finset.disjoint_union_right.mpr ⟨hC12, hC13⟩) hnc1,
      edgesOf_union_no_cross hC23 hnc2, hC1_eq, hC2_edges, hC3_edges]
    omega
  have hbd_tip : ∀ p ∈ inner, p.1 + (p.2.natAbs : ℤ) = (d : ℤ) → p = ((d : ℤ), 0) := by
    intro p hp heq
    rw [hinner_eq] at hp
    simp only [FCset, Finset.mem_filter, mem_coneBox] at hp
    have hF := hp.2
    rw [F_pow2_bd hm1 (by omega), decide_eq_true_eq] at hF
    ext <;> dsimp only <;> omega
  refine ⟨hcell, ?_, ?_⟩
  · intro hm3
    subst hm3
    have hA3_10 : A 3 1 0 = false := by decide
    have hA3_01 : A 3 0 1 = false := by rw [A_sym_t]; exact hA3_10
    have hA3_0n1 : A 3 0 (-1) = false := by rw [A_sym_y]; exact hA3_01
    have hnc : ∀ p ∈ inner, ∀ q ∈ outer,
        ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1 := by
      intro p hp q hq h1
      have hp1 := (Finset.mem_filter.mp hp).2
      have hq1 := (Finset.mem_filter.mp hq).2
      have htip := hbd_tip p hp (by omega)
      subst htip
      have hqUG := (mem_SCset.mp (Finset.mem_filter.mp hq).1).1
      rw [hAeq, UG, if_neg (by omega), if_pos (by omega)] at hqUG
      have hq_cases : (q.1 - (d : ℤ) = 1 ∧ q.2 = 0) ∨ (q.1 - (d : ℤ) = 0 ∧ q.2 = 1) ∨
          (q.1 - (d : ℤ) = 0 ∧ q.2 = -1) := by omega
      rcases hq_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hqUG; exact Bool.false_ne_true (hA3_10.symm.trans hqUG)
      · rw [h1, h2] at hqUG; exact Bool.false_ne_true (hA3_01.symm.trans hqUG)
      · rw [h1, h2] at hqUG; exact Bool.false_ne_true (hA3_0n1.symm.trans hqUG)
    rw [hpart, edgesOf_union_no_cross hdisj hnc, hinner_eq, houter_edges]
    simp only [show 3 - 1 = 2 by rfl]
    omega
  intro hm4
  -- For m >= 4, d / 2 = 2^(m-2) >= 4, so A(d - 1) agrees with F on (x.natAbs : ℤ) + (y.natAbs : ℤ) <= d/2,
  -- giving (1, 0), (0, 1), (0, -1) in A(d - 1), hence (d+1, 0), (d, 1), (d, -1) in outer!
  have hA_d1_10 : A (d - 1) 1 0 = true := by
    have hprev := A_pow2_sub_one (show 3 ≤ m - 1 by omega)
    rw [show 2 ^ (m - 1) = d from rfl] at hprev
    have hd2 : 4 ≤ 2 ^ (m - 1 - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (m - 1 - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    rw [hprev, UG, if_pos (by omega)]
    exact F_odd (by decide)
  have hA_d1_01 : A (d - 1) 0 1 = true := by rw [A_sym_t]; exact hA_d1_10
  have hA_d1_0n1 : A (d - 1) 0 (-1) = true := by rw [A_sym_y]; exact hA_d1_01
  have htip_in : ((d : ℤ), 0) ∈ inner := by
    rw [hinner_eq]
    simp only [FCset, Finset.mem_filter, mem_coneBox]
    exact ⟨⟨by omega, by omega⟩, by rw [F_pow2_bd hm1 (by omega), decide_eq_true (Or.inr rfl)]⟩
  have hR_out : ((d : ℤ) + 1, 0) ∈ outer := by
    simp only [outer, Finset.mem_filter, mem_SCset, hAeq]
    refine ⟨⟨?_, by omega⟩, by omega⟩
    rw [UG, if_neg (by omega), if_pos (by omega), add_sub_cancel_left]
    exact hA_d1_10
  have hU_out : ((d : ℤ), 1) ∈ outer := by
    simp only [outer, Finset.mem_filter, mem_SCset, hAeq]
    refine ⟨⟨?_, by omega⟩, by omega⟩
    rw [UG, if_neg (by omega), if_pos (by omega), sub_self]
    exact hA_d1_01
  have hD_out : ((d : ℤ), -1) ∈ outer := by
    simp only [outer, Finset.mem_filter, mem_SCset, hAeq]
    refine ⟨⟨?_, by omega⟩, by omega⟩
    rw [UG, if_neg (by omega), if_pos (by omega), sub_self]
    exact hA_d1_0n1
  -- Crossing edges between inner and outer:
  -- Horizontal: ONLY ((d, 0), (d + 1, 0)) (count 1)
  -- Vertical: ONLY ((d, 0), (d, 1)) and ((d, -1), (d, 0)) (count 2)
  have hh_part : ((inner ∪ outer).filter (fun p => (p.1 + 1, p.2) ∈ inner ∪ outer)) =
      (inner.filter (fun p => (p.1 + 1, p.2) ∈ inner)) ∪
      (outer.filter (fun p => (p.1 + 1, p.2) ∈ outer)) ∪ {((d : ℤ), 0)} := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hpI | hpO, hqI | hqO⟩
      · exact Or.inl (Or.inl ⟨hpI, hqI⟩)
      · have hp1 := (Finset.mem_filter.mp hpI).2
        have hq1 := (Finset.mem_filter.mp hqO).2
        exact Or.inr (hbd_tip p hpI (by omega))
      · exfalso
        have hp1 := (Finset.mem_filter.mp hpO).2
        have hq1 := (Finset.mem_filter.mp hqI).2
        omega
      · exact Or.inl (Or.inr ⟨hpO, hqO⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | rfl)
      · exact ⟨Or.inl h1, Or.inl h2⟩
      · exact ⟨Or.inr h1, Or.inr h2⟩
      · exact ⟨Or.inl htip_in, Or.inr hR_out⟩
  have hv_part : ((inner ∪ outer).filter (fun p => (p.1, p.2 + 1) ∈ inner ∪ outer)) =
      (inner.filter (fun p => (p.1, p.2 + 1) ∈ inner)) ∪
      (outer.filter (fun p => (p.1, p.2 + 1) ∈ outer)) ∪ {((d : ℤ), 0), ((d : ℤ), -1)} := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hpI | hpO, hqI | hqO⟩
      · exact Or.inl (Or.inl ⟨hpI, hqI⟩)
      · have hp1 := (Finset.mem_filter.mp hpI).2
        have hq1 := (Finset.mem_filter.mp hqO).2
        exact Or.inr (Or.inl (hbd_tip p hpI (by omega)))
      · have hp1 := (Finset.mem_filter.mp hpO).2
        have hq1 := (Finset.mem_filter.mp hqI).2
        have hqt := hbd_tip (p.1, p.2 + 1) hqI (by omega)
        have h1 := congrArg Prod.fst hqt
        have h2 := congrArg Prod.snd hqt
        exact Or.inr (Or.inr (by ext <;> dsimp only <;> omega))
      · exact Or.inl (Or.inr ⟨hpO, hqO⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (rfl | rfl))
      · exact ⟨Or.inl h1, Or.inl h2⟩
      · exact ⟨Or.inr h1, Or.inr h2⟩
      · exact ⟨Or.inl htip_in, Or.inr hU_out⟩
      · exact ⟨Or.inr hD_out, Or.inl (by simpa using htip_in)⟩
  have hhd1 : Disjoint (inner.filter (fun p => (p.1 + 1, p.2) ∈ inner))
      (outer.filter (fun p => (p.1 + 1, p.2) ∈ outer)) :=
    Finset.disjoint_filter_filter hdisj
  have hhd2 : Disjoint
      (inner.filter (fun p => (p.1 + 1, p.2) ∈ inner) ∪ outer.filter (fun p => (p.1 + 1, p.2) ∈ outer))
      {((d : ℤ), 0)} := by
    rw [Finset.disjoint_right]; intro p hp
    rw [Finset.mem_singleton] at hp; subst hp
    simp only [Finset.mem_union, Finset.mem_filter]
    rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · have := (Finset.mem_filter.mp h2).2; omega
    · have := (Finset.mem_filter.mp h1).2; omega
  have hvd1 : Disjoint (inner.filter (fun p => (p.1, p.2 + 1) ∈ inner))
      (outer.filter (fun p => (p.1, p.2 + 1) ∈ outer)) :=
    Finset.disjoint_filter_filter hdisj
  have hvd2 : Disjoint
      (inner.filter (fun p => (p.1, p.2 + 1) ∈ inner) ∪ outer.filter (fun p => (p.1, p.2 + 1) ∈ outer))
      {((d : ℤ), 0), ((d : ℤ), -1)} := by
    rw [Finset.disjoint_right]; intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hp with rfl | rfl
    · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · have := (Finset.mem_filter.mp h2).2; omega
      · have := (Finset.mem_filter.mp h1).2; omega
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · have := (Finset.mem_filter.mp h1).2; omega
      · have := (Finset.mem_filter.mp h2).2; omega
  have hpair_card : ({((d : ℤ), 0), ((d : ℤ), -1)} : Finset (ℤ × ℤ)).card = 2 :=
    Finset.card_pair (by intro h; have := congrArg Prod.snd h; omega)
  rw [hpart]
  simp only [edgesOf]
  rw [hh_part, hv_part, Finset.card_union_of_disjoint hhd2, Finset.card_union_of_disjoint hhd1,
    Finset.card_union_of_disjoint hvd2, Finset.card_union_of_disjoint hvd1,
    Finset.card_singleton, hpair_card]
  have hinner_e : edgesOf inner = edgesOf (FCset m) := by rw [hinner_eq]
  simp only [edgesOf] at hinner_e houter_edges
  omega

private lemma SC_base : (SCset 2).card = 4 := by decide
private lemma EC_base : edgesOf (SCset 3) = 10 := by
  have hstep := (SC_and_EC_step (m := 3) (by omega)).2.1 rfl
  have hFC := (FCset_counts (m := 3) (by omega)).2
  have hSC2 : edgesOf (SCset 2) = 3 := by decide
  omega

private lemma SC_card_closed :
    ∀ m : ℕ, 2 ≤ m → 3 * (SCset m).card + 1 = 13 * 4 ^ (m - 2) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm2 : m + 1 = 2
    · rw [hm2, SC_base]; norm_num
    · have hm3 : 3 ≤ m + 1 := by omega
      have hrec := (SC_and_EC_step hm3).1
      have hFC := (FCset_counts hm3).1
      have hih := ih (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      have h4pow : 4 ^ (m + 1 - 2) = 4 * 4 ^ (m - 2) := by
        rw [show m + 1 - 2 = (m - 2) + 1 by omega, pow_succ]; ring
      have h4pow' : m + 1 - 3 = m - 2 := by omega
      rw [h4pow'] at hFC
      omega

private lemma EC_card_closed :
    ∀ m : ℕ, 3 ≤ m → 3 * edgesOf (SCset m) + 4 = 4 ^ (m - 1) + 6 * 3 ^ (m - 2) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm3 : m + 1 = 3
    · rw [hm3, EC_base]; norm_num
    · have hm4 : 4 ≤ m + 1 := by omega
      have hrec := (SC_and_EC_step (by omega : 3 ≤ m + 1)).2.2 hm4
      have hFC := (FCset_counts (by omega : 3 ≤ m + 1)).2
      have hih := ih (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      have h4pow : 4 ^ (m + 1 - 1) = 4 * 4 ^ (m - 1) := by
        rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ]; ring
      have h3pow : 3 ^ (m + 1 - 2) = 3 * 3 ^ (m - 2) := by
        rw [show m + 1 - 2 = (m - 2) + 1 by omega, pow_succ]; ring
      have heq4 : m + 1 - 2 = m - 1 := by omega
      rw [heq4] at hFC
      omega

-- ============================================================================
-- Section 5: Total Counts for A(2^m - 1) and Blomberg's Closed Form
-- ============================================================================

private lemma Aset_total_counts {m : ℕ} (hm : 3 ≤ m) :
    (Aset (2 ^ m - 1)).card = 1 + 4 * (SCset m).card ∧
    edgesOf (Aset (2 ^ m - 1)) = 4 + 4 * edgesOf (SCset m) := by
  set k : ℕ := 2 ^ m - 1
  set C1 := (Aset k).filter (fun p => (p.2.natAbs : ℤ) < p.1)
  set C2 := (Aset k).filter (fun p => (p.2.natAbs : ℤ) < -p.1)
  set C3 := (Aset k).filter (fun p => (p.1.natAbs : ℤ) < p.2)
  set C4 := (Aset k).filter (fun p => (p.1.natAbs : ℤ) < -p.2)
  have hC1_eq : C1 = SCset m := rfl
  have hC2_card : C2.card = C1.card := by
    refine Finset.card_bij (fun p _ => (-p.1, p.2)) ?_ ?_ ?_
    · intro p hp; simp only [C1, C2, Finset.mem_filter, mem_Aset] at hp ⊢
      exact ⟨by rw [A_sym_x]; exact hp.1, hp.2⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [C1, Finset.mem_filter, mem_Aset] at hq
      exact ⟨(-q.1, q.2), Finset.mem_filter.mpr ⟨mem_Aset.mpr (by rw [A_sym_x]; exact hq.1), by simpa using hq.2⟩, by ext <;> simp⟩
  have hC3_card : C3.card = C1.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [C1, C3, Finset.mem_filter, mem_Aset] at hp ⊢
      exact ⟨by rw [A_sym_t]; exact hp.1, hp.2⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [C1, Finset.mem_filter, mem_Aset] at hq
      exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨mem_Aset.mpr (by rw [A_sym_t]; exact hq.1), hq.2⟩, by ext <;> simp⟩
  have hC4_card : C4.card = C1.card := by
    refine Finset.card_bij (fun p _ => (-p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [C1, C4, Finset.mem_filter, mem_Aset] at hp ⊢
      exact ⟨by rw [A_sym_x, A_sym_t]; exact hp.1, hp.2⟩
    · intro p₁ _ p₂ _ heq; have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq; ext <;> omega
    · intro q hq; simp only [C1, Finset.mem_filter, mem_Aset] at hq
      exact ⟨(q.2, -q.1), Finset.mem_filter.mpr ⟨mem_Aset.mpr (by rw [A_sym_y, A_sym_t]; exact hq.1), by simpa using hq.2⟩, by ext <;> simp⟩
  set U4 := C1 ∪ (C2 ∪ (C3 ∪ C4))
  have hpart : Aset k = {(0, 0)} ∪ U4 := by
    ext p
    simp only [U4, C1, C2, C3, C4, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hp
      by_cases h0 : p = (0, 0)
      · exact Or.inl h0
      · by_cases h1 : (p.2.natAbs : ℤ) < p.1
        · exact Or.inr (Or.inl ⟨hp, h1⟩)
        · by_cases h2 : (p.2.natAbs : ℤ) < -p.1
          · exact Or.inr (Or.inr (Or.inl ⟨hp, h2⟩))
          · by_cases h3 : (p.1.natAbs : ℤ) < p.2
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, h3⟩)))
            · by_cases h4 : (p.1.natAbs : ℤ) < -p.2
              · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, h4⟩)))
              · exfalso
                have habs : (p.1.natAbs : ℤ) = (p.2.natAbs : ℤ) := by omega
                have hne : p.1 ≠ 0 := by intro hx; exact h0 (by ext <;> omega)
                have ht := mem_Aset.mp hp
                rw [A_diag k habs hne] at ht
                exact Bool.false_ne_true ht
    · rintro (rfl | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩)
      · exact mem_Aset.mpr (A_origin k)
      all_goals exact hp
  have hd0 : Disjoint ({(0, 0)} : Finset (ℤ × ℤ)) U4 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    rw [Finset.mem_singleton] at h1; subst h1
    simp only [U4, C1, C2, C3, C4, Finset.mem_union, Finset.mem_filter] at h2
    rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hd1 : Disjoint C1 (C2 ∪ (C3 ∪ C4)) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [C1, C2, C3, C4, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hd2 : Disjoint C2 (C3 ∪ C4) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [C2, C3, C4, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hd3 : Disjoint C3 C4 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [C3, C4, Finset.mem_filter] at h1 h2; omega
  have hcard : (Aset k).card = 1 + 4 * (SCset m).card := by
    rw [hpart, Finset.card_union_of_disjoint hd0, Finset.card_singleton,
      Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd3, hC2_card, hC3_card, hC4_card, hC1_eq]
    omega
  -- Edges of U4 = 4 * edgesOf (SCset m)
  have hC2_edges : edgesOf C2 = edgesOf C1 := by
    apply edgesOf_sym_x; intro x y
    simp only [C1, C2, Finset.mem_filter, mem_Aset]; rw [A_sym_x]
  have hC3_edges : edgesOf C3 = edgesOf C1 := by
    apply edgesOf_sym_t; intro x y
    simp only [C1, C3, Finset.mem_filter, mem_Aset]; rw [A_sym_t]
  have hC4_edges : edgesOf C4 = edgesOf C1 := by
    have h1 : edgesOf C4 = edgesOf C2 := by
      apply edgesOf_sym_t; intro x y
      simp only [C2, C4, Finset.mem_filter, mem_Aset]; rw [A_sym_t]
    rw [h1, hC2_edges]
  have hU4_edges : edgesOf U4 = 4 * edgesOf (SCset m) := by
    have hnc1 : ∀ p ∈ C1, ∀ q ∈ C2 ∪ (C3 ∪ C4), ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1 := by
      intro p hp q hq
      simp only [C1, C2, C3, C4, Finset.mem_union, Finset.mem_filter] at hp hq
      rcases hq with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hnc2 : ∀ p ∈ C2, ∀ q ∈ C3 ∪ C4, ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1 := by
      intro p hp q hq
      simp only [C2, C3, C4, Finset.mem_union, Finset.mem_filter] at hp hq
      rcases hq with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hnc3 : ∀ p ∈ C3, ∀ q ∈ C4, ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ) ≠ 1 := by
      intro p hp q hq
      simp only [C3, C4, Finset.mem_filter] at hp hq; omega
    rw [edgesOf_union_no_cross hd1 hnc1, edgesOf_union_no_cross hd2 hnc2,
      edgesOf_union_no_cross hd3 hnc3, hC2_edges, hC3_edges, hC4_edges, hC1_eq]
    omega
  -- Four edges incident to (0, 0) since (±1, 0), (0, ±1) are in A(2^m - 1) for m >= 3
  have h10_in : (1, 0) ∈ U4 := by
    have hA10 : A k 1 0 = true := by
      have hAeq := A_pow2_sub_one hm
      have hd4 : 4 ≤ 2 ^ (m - 1) := by
        have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using this
      show A (2 ^ m - 1) 1 0 = true
      rw [hAeq, UG, if_pos (by omega)]
      exact F_odd (by decide)
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨mem_Aset.mpr hA10, by decide⟩)
  have hn10_in : (-1, 0) ∈ U4 := by
    have hA10 : A k (-1) 0 = true := by
      rw [A_sym_x]
      have hAeq := A_pow2_sub_one hm
      have hd4 : 4 ≤ 2 ^ (m - 1) := by
        have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using this
      show A (2 ^ m - 1) 1 0 = true
      rw [hAeq, UG, if_pos (by omega)]; exact F_odd (by decide)
    exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨mem_Aset.mpr hA10, by decide⟩))
  have h01_in : (0, 1) ∈ U4 := by
    have hA01 : A k 0 1 = true := by
      rw [A_sym_t]
      have hAeq := A_pow2_sub_one hm
      have hd4 : 4 ≤ 2 ^ (m - 1) := by
        have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using this
      show A (2 ^ m - 1) 1 0 = true
      rw [hAeq, UG, if_pos (by omega)]; exact F_odd (by decide)
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨mem_Aset.mpr hA01, by decide⟩)))
  have h0n1_in : (0, -1) ∈ U4 := by
    have hA0n1 : A k 0 (-1) = true := by
      rw [A_sym_y, A_sym_t]
      have hAeq := A_pow2_sub_one hm
      have hd4 : 4 ≤ 2 ^ (m - 1) := by
        have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using this
      show A (2 ^ m - 1) 1 0 = true
      rw [hAeq, UG, if_pos (by omega)]; exact F_odd (by decide)
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨mem_Aset.mpr hA0n1, by decide⟩)))
  have h0_not_U4 : (0, 0) ∉ U4 :=
    Finset.disjoint_left.mp hd0 (Finset.mem_singleton_self (0, 0))
  have hh_tot : (({(0, 0)} ∪ U4).filter (fun p => (p.1 + 1, p.2) ∈ {(0, 0)} ∪ U4)) =
      (U4.filter (fun p => (p.1 + 1, p.2) ∈ U4)) ∪ {(0, 0), (-1, 0)} := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hpU, hq0 | hqU⟩
      · exfalso; have := congrArg Prod.fst hq0; omega
      · exact Or.inr (Or.inl rfl)
      · have h1 := congrArg Prod.fst hq0; have h2 := congrArg Prod.snd hq0
        exact Or.inr (Or.inr (by ext <;> dsimp only <;> omega))
      · exact Or.inl ⟨hpU, hqU⟩
    · rintro (⟨h1, h2⟩ | rfl | rfl)
      · exact ⟨Or.inr h1, Or.inr h2⟩
      · exact ⟨Or.inl rfl, Or.inr h10_in⟩
      · exact ⟨Or.inr hn10_in, Or.inl (by simp)⟩
  have hv_tot : (({(0, 0)} ∪ U4).filter (fun p => (p.1, p.2 + 1) ∈ {(0, 0)} ∪ U4)) =
      (U4.filter (fun p => (p.1, p.2 + 1) ∈ U4)) ∪ {(0, 0), (0, -1)} := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hpU, hq0 | hqU⟩
      · exfalso; have := congrArg Prod.snd hq0; omega
      · exact Or.inr (Or.inl rfl)
      · have h1 := congrArg Prod.fst hq0; have h2 := congrArg Prod.snd hq0
        exact Or.inr (Or.inr (by ext <;> dsimp only <;> omega))
      · exact Or.inl ⟨hpU, hqU⟩
    · rintro (⟨h1, h2⟩ | rfl | rfl)
      · exact ⟨Or.inr h1, Or.inr h2⟩
      · exact ⟨Or.inl rfl, Or.inr h01_in⟩
      · exact ⟨Or.inr h0n1_in, Or.inl (by simp)⟩
  have hhd : Disjoint (U4.filter (fun p => (p.1 + 1, p.2) ∈ U4)) {(0, 0), (-1, 0)} := by
    rw [Finset.disjoint_right]; intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    simp only [Finset.mem_filter]
    rcases hp with rfl | rfl
    · exact fun h => h0_not_U4 h.1
    · exact fun h => h0_not_U4 (by simpa using h.2)
  have hvd : Disjoint (U4.filter (fun p => (p.1, p.2 + 1) ∈ U4)) {(0, 0), (0, -1)} := by
    rw [Finset.disjoint_right]; intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    simp only [Finset.mem_filter]
    rcases hp with rfl | rfl
    · exact fun h => h0_not_U4 h.1
    · exact fun h => h0_not_U4 (by simpa using h.2)
  have hedges : edgesOf (Aset k) = 4 + 4 * edgesOf (SCset m) := by
    rw [hpart]
    simp only [edgesOf]
    rw [hh_tot, hv_tot, Finset.card_union_of_disjoint hhd, Finset.card_union_of_disjoint hvd,
      Finset.card_pair (by decide : ((0 : ℤ), (0 : ℤ)) ≠ (-1, 0)),
      Finset.card_pair (by decide : ((0 : ℤ), (0 : ℤ)) ≠ (0, -1))]
    simp only [edgesOf] at hU4_edges
    omega
  exact ⟨hcard, hedges⟩

private lemma a_three : a 3 = 61 := by
  have h := onCount_odd_eq 3
  have hc : (Aset 3).card = 17 := by decide
  have he : edgesOf (Aset 3) = 12 := by decide
  unfold a
  rw [show 2 ^ 3 - 1 = 2 * 3 + 1 by rfl]
  omega

theorem main_proof :
    ∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 19 * (4 : ℚ) ^ (n - 2) - 16 * (3 : ℚ) ^ (n - 3) + 1 := by
  intro n hn
  by_cases hn3 : n = 3
  · subst hn3; rw [a_three]; norm_num
  · set m : ℕ := n - 1
    have hm : 3 ≤ m := by omega
    have hpow : 2 ^ n - 1 = 2 * (2 ^ m - 1) + 1 := by
      have h2n : 2 ^ n = 2 * 2 ^ m := by
        conv_lhs => rw [show n = m + 1 by omega, pow_succ]
        ring
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      omega
    have hon := onCount_odd_eq (2 ^ m - 1)
    obtain ⟨hA_card, hA_edge⟩ := Aset_total_counts hm
    have hSC := SC_card_closed m (by omega)
    have hEC := EC_card_closed m hm
    have h4eq : 4 ^ (m - 1) = 4 * 4 ^ (m - 2) := by
      rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]; ring
    have hnat : 3 * onCount 646 (2 * (2 ^ m - 1) + 1) + 48 * 3 ^ (m - 2) =
        57 * 4 ^ (m - 1) + 3 := by
      omega
    have hint : (a n : ℤ) = 19 * (4 : ℤ) ^ (n - 2) - 16 * (3 : ℤ) ^ (n - 3) + 1 := by
      unfold a
      rw [hpow]
      have hnat_z : 3 * (onCount 646 (2 * (2 ^ m - 1) + 1) : ℤ) + 48 * (3 : ℤ) ^ (m - 2) =
          57 * (4 : ℤ) ^ (m - 1) + 3 := by
        exact_mod_cast hnat
      rw [show n - 2 = m - 1 by omega, show n - 3 = m - 2 by omega]
      omega
    exact_mod_cast hint

end OeisA273327

theorem OMA.solution : type_of% @OMA.S_oeis_a273327.main :=
  OeisA273327.main_proof
