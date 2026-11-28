import OMAStatements.S_oeis_a273747

namespace Adapt273747

def applyRule (r : ℕ) (c n s w e : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (n.toNat + s.toNat + w.toNat + e.toNat))


def stepR (r : ℕ) (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  applyRule r (g x y) (g x (y - 1)) (g x (y + 1)) (g (x - 1) y) (g (x + 1) y)

def stateR (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => stepR r (stateR r t) x y

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma stateR_out (r : ℕ) (hr0 : applyRule r false false false false false = false) (t : ℕ) :
    ∀ x y : ℤ, (t : ℤ) < |x| + |y| → stateR r t x y = false := by
  induction t with
  | zero =>
    intro x y h
    have hne : ¬(x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [stateR, hne]
  | succ t ih =>
    intro x y h
    change stepR r (stateR r t) x y = false
    unfold stepR
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    rw [ih x y (by omega), ih x (y - 1) (by omega), ih x (y + 1) (by omega),
        ih (x - 1) y (by omega), ih (x + 1) y (by omega)]
    exact hr0

lemma cone_nbr_count_one_or_two (t : ℕ) (x y : ℤ) (heq : |x| + |y| = ((t + 1 : ℕ) : ℤ)) :
    (decide (|x| + |y - 1| ≤ (t : ℤ))).toNat +
    (decide (|x| + |y + 1| ≤ (t : ℤ))).toNat +
    (decide (|x - 1| + |y| ≤ (t : ℤ))).toNat +
    (decide (|x + 1| + |y| ≤ (t : ℤ))).toNat = 1 ∨
    (decide (|x| + |y - 1| ≤ (t : ℤ))).toNat +
    (decide (|x| + |y + 1| ≤ (t : ℤ))).toNat +
    (decide (|x - 1| + |y| ≤ (t : ℤ))).toNat +
    (decide (|x + 1| + |y| ≤ (t : ℤ))).toNat = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hx1 : |x - 1| = |x| + 1 := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
    have hx2 : |x + 1| = |x| - 1 := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hy1 : |y - 1| = |y| + 1 := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have hy2 : |y + 1| = |y| - 1 := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      right
      simp [hx1, hx2, hy1, hy2, show ¬(|x| + 1 + |y| ≤ (t : ℤ)) by omega,
        show |x| - 1 + |y| ≤ (t : ℤ) by omega,
        show ¬(|x| + (|y| + 1) ≤ (t : ℤ)) by omega,
        show |x| + (|y| - 1) ≤ (t : ℤ) by omega]
    · left
      simp [hx1, hx2, show ¬(|x| + 1 ≤ (t : ℤ)) by simp at heq; omega,
        show |x| - 1 ≤ (t : ℤ) by simp at heq; omega]
    · have hy1 : |y - 1| = |y| - 1 := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have hy2 : |y + 1| = |y| + 1 := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      right
      simp [hx1, hx2, hy1, hy2, show ¬(|x| + 1 + |y| ≤ (t : ℤ)) by omega,
        show |x| - 1 + |y| ≤ (t : ℤ) by omega,
        show |x| + (|y| - 1) ≤ (t : ℤ) by omega,
        show ¬(|x| + (|y| + 1) ≤ (t : ℤ)) by omega]
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hy1 : |y - 1| = |y| + 1 := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have hy2 : |y + 1| = |y| - 1 := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      left
      simp [hy1, hy2, show ¬(1 + |y| ≤ (t : ℤ)) by simp at heq; omega,
        show ¬(|y| + 1 ≤ (t : ℤ)) by simp at heq; omega,
        show |y| - 1 ≤ (t : ℤ) by simp at heq; omega]
    · simp at heq; omega
    · have hy1 : |y - 1| = |y| - 1 := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have hy2 : |y + 1| = |y| + 1 := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      left
      simp [hy1, hy2, show ¬(1 + |y| ≤ (t : ℤ)) by simp at heq; omega,
        show |y| - 1 ≤ (t : ℤ) by simp at heq; omega,
        show ¬(|y| + 1 ≤ (t : ℤ)) by simp at heq; omega]
  · have hx1 : |x - 1| = |x| - 1 := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
    have hx2 : |x + 1| = |x| + 1 := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hy1 : |y - 1| = |y| + 1 := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have hy2 : |y + 1| = |y| - 1 := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      right
      simp [hx1, hx2, hy1, hy2, show |x| - 1 + |y| ≤ (t : ℤ) by omega,
        show ¬(|x| + 1 + |y| ≤ (t : ℤ)) by omega,
        show ¬(|x| + (|y| + 1) ≤ (t : ℤ)) by omega,
        show |x| + (|y| - 1) ≤ (t : ℤ) by omega]
    · left
      simp [hx1, hx2, show |x| - 1 ≤ (t : ℤ) by simp at heq; omega,
        show ¬(|x| + 1 ≤ (t : ℤ)) by simp at heq; omega]
    · have hy1 : |y - 1| = |y| - 1 := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have hy2 : |y + 1| = |y| + 1 := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      right
      simp [hx1, hx2, hy1, hy2, show |x| - 1 + |y| ≤ (t : ℤ) by omega,
        show ¬(|x| + 1 + |y| ≤ (t : ℤ)) by omega,
        show |x| + (|y| - 1) ≤ (t : ℤ) by omega,
        show ¬(|x| + (|y| + 1) ≤ (t : ℤ)) by omega]

lemma stateR_918_even_true (t : ℕ) :
    ∀ x y : ℤ, |x| + |y| ≤ (t : ℤ) → (x + y + (t : ℤ)) % 2 = 0 → stateR 918 t x y = true := by
  induction t with
  | zero =>
    intro x y hle _
    obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := by cases abs_cases x <;> cases abs_cases y <;> omega
    decide
  | succ t ih =>
    intro x y hle hp
    change stepR 918 (stateR 918 t) x y = true
    unfold stepR
    have habs_par : (|x| + |y| + ((t + 1 : ℕ) : ℤ)) % 2 = 0 := by
      cases abs_cases x <;> cases abs_cases y <;> omega
    by_cases hlt : |x| + |y| ≤ (t : ℤ) - 1
    · rw [ih x (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega) (by omega),
          ih x (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega) (by omega),
          ih (x - 1) y (by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega) (by omega),
          ih (x + 1) y (by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega) (by omega)]
      cases stateR 918 t x y <;> decide
    · have heq : |x| + |y| = ((t + 1 : ℕ) : ℤ) := by omega
      have hc : stateR 918 t x y = false := stateR_out 918 (by decide) t x y (by omega)
      have hn_eq : stateR 918 t x (y - 1) = decide (|x| + |y - 1| ≤ (t : ℤ)) := by
        by_cases h : |x| + |y - 1| ≤ (t : ℤ)
        · rw [ih x (y - 1) h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t x (y - 1) (by omega), decide_eq_false h]
      have hs_eq : stateR 918 t x (y + 1) = decide (|x| + |y + 1| ≤ (t : ℤ)) := by
        by_cases h : |x| + |y + 1| ≤ (t : ℤ)
        · rw [ih x (y + 1) h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t x (y + 1) (by omega), decide_eq_false h]
      have hw_eq : stateR 918 t (x - 1) y = decide (|x - 1| + |y| ≤ (t : ℤ)) := by
        by_cases h : |x - 1| + |y| ≤ (t : ℤ)
        · rw [ih (x - 1) y h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t (x - 1) y (by omega), decide_eq_false h]
      have he_eq : stateR 918 t (x + 1) y = decide (|x + 1| + |y| ≤ (t : ℤ)) := by
        by_cases h : |x + 1| + |y| ≤ (t : ℤ)
        · rw [ih (x + 1) y h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t (x + 1) y (by omega), decide_eq_false h]
      rw [hc, hn_eq, hs_eq, hw_eq, he_eq]
      unfold applyRule
      rcases cone_nbr_count_one_or_two t x y heq with h1 | h1 <;>
        simp only [Bool.toNat_false, zero_add, h1] <;> decide

set_option maxHeartbeats 2000000 in
lemma stepR_982_eq_918 (t : ℕ) (x y : ℤ) :
    stepR 982 (stateR 918 t) x y = stepR 918 (stateR 918 t) x y := by
  unfold stepR
  by_cases hc : stateR 918 t x y = true
  · rw [hc]
    cases stateR 918 t x (y - 1) <;> cases stateR 918 t x (y + 1) <;>
      cases stateR 918 t (x - 1) y <;> cases stateR 918 t (x + 1) y <;> decide
  · have hcf : stateR 918 t x y = false := Bool.eq_false_iff.mpr hc
    rw [hcf]
    by_cases hp : (x + y + (t : ℤ)) % 2 = 0
    · have hout : (t : ℤ) < |x| + |y| := by
        by_contra hle
        push_neg at hle
        have ht := stateR_918_even_true t x y hle hp
        rw [hcf] at ht; cases ht
      have habs_par : (|x| + |y| + (t : ℤ)) % 2 = 0 := by
        cases abs_cases x <;> cases abs_cases y <;> omega
      have hge : (t : ℤ) + 2 ≤ |x| + |y| := by omega
      have hx := abs_step_lb x
      have hy := abs_step_lb y
      rw [stateR_out 918 (by decide) t x (y - 1) (by omega),
          stateR_out 918 (by decide) t x (y + 1) (by omega),
          stateR_out 918 (by decide) t (x - 1) y (by omega),
          stateR_out 918 (by decide) t (x + 1) y (by omega)]
      decide
    · have hn_eq : stateR 918 t x (y - 1) = decide (|x| + |y - 1| ≤ (t : ℤ)) := by
        by_cases h : |x| + |y - 1| ≤ (t : ℤ)
        · rw [stateR_918_even_true t x (y - 1) h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t x (y - 1) (by omega), decide_eq_false h]
      have hs_eq : stateR 918 t x (y + 1) = decide (|x| + |y + 1| ≤ (t : ℤ)) := by
        by_cases h : |x| + |y + 1| ≤ (t : ℤ)
        · rw [stateR_918_even_true t x (y + 1) h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t x (y + 1) (by omega), decide_eq_false h]
      have hw_eq : stateR 918 t (x - 1) y = decide (|x - 1| + |y| ≤ (t : ℤ)) := by
        by_cases h : |x - 1| + |y| ≤ (t : ℤ)
        · rw [stateR_918_even_true t (x - 1) y h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t (x - 1) y (by omega), decide_eq_false h]
      have he_eq : stateR 918 t (x + 1) y = decide (|x + 1| + |y| ≤ (t : ℤ)) := by
        by_cases h : |x + 1| + |y| ≤ (t : ℤ)
        · rw [stateR_918_even_true t (x + 1) y h (by omega), decide_eq_true h]
        · rw [stateR_out 918 (by decide) t (x + 1) y (by omega), decide_eq_false h]
      rw [hn_eq, hs_eq, hw_eq, he_eq]
      have habs_odd : (|x| + |y| + (t : ℤ)) % 2 ≠ 0 := by
        cases abs_cases x <;> cases abs_cases y <;> omega
      rcases (by omega : |x| + |y| ≤ (t : ℤ) - 1 ∨ |x| + |y| = ((t + 1 : ℕ) : ℤ) ∨
          (t : ℤ) + 2 ≤ |x| + |y|) with hle | heq | hgt
      · have h1 : |x| + |y - 1| ≤ (t : ℤ) := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
        have h2 : |x| + |y + 1| ≤ (t : ℤ) := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
        have h3 : |x - 1| + |y| ≤ (t : ℤ) := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
        have h4 : |x + 1| + |y| ≤ (t : ℤ) := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
        simp only [h1, h2, h3, h4, decide_true]; decide
      · unfold applyRule
        rcases cone_nbr_count_one_or_two t x y heq with h1 | h1 <;>
          simp only [Bool.toNat_false, zero_add, h1] <;> decide
      · have hx := abs_step_lb x
        have hy := abs_step_lb y
        have h1 : ¬(|x| + |y - 1| ≤ (t : ℤ)) := by omega
        have h2 : ¬(|x| + |y + 1| ≤ (t : ℤ)) := by omega
        have h3 : ¬(|x - 1| + |y| ≤ (t : ℤ)) := by omega
        have h4 : ¬(|x + 1| + |y| ≤ (t : ℤ)) := by omega
        simp only [h1, h2, h3, h4, decide_false]; decide

lemma stateR_982_eq_918 (t : ℕ) : stateR 982 t = stateR 918 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    change stepR 982 (stateR 982 t) x y = stepR 918 (stateR 918 t) x y
    rw [ih]
    exact stepR_982_eq_918 t x y


lemma state_bridge (r t : ℕ) (x y : ℤ) : OMA.S_oeis_a273747.state r t x y = stateR r t x y := by
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
    simp only [OMA.S_oeis_a273747.state, stateR, stepR, applyRule, ih]
    congr 1
    omega

end Adapt273747

theorem OMA.solution : type_of% @OMA.S_oeis_a273747.main := by
  intro n
  unfold OMA.S_oeis_a273747.a OMA.S_oeis_a273747.count
  simp only [Adapt273747.state_bridge, Adapt273747.stateR_982_eq_918]
