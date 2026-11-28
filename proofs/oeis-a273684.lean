import OMAStatements.S_oeis_a273684

namespace Adapt273684

def applyRule (r : ℕ) (c n s w e : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (n.toNat + s.toNat + w.toNat + e.toNat))


def stepR (r : ℕ) (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  applyRule r (g x y) (g x (y - 1)) (g x (y + 1)) (g (x - 1) y) (g (x + 1) y)

def stateR (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => stepR r (stateR r t) x y

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma stateR_out (r : ℕ) (hr0 : applyRule r false false false false false = true)
    (hr1 : applyRule r true true true true true = true) (t : ℕ) :
    ∀ x y : ℤ, (t : ℤ) < |x| + |y| → stateR r t x y = decide (1 ≤ t) := by
  induction t with
  | zero =>
    intro x y h
    have hne : ¬(x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [stateR, hne]
  | succ t ih =>
    intro x y h
    change stepR r (stateR r t) x y = true
    unfold stepR
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    rw [ih x y (by omega), ih x (y - 1) (by omega), ih x (y + 1) (by omega),
        ih (x - 1) y (by omega), ih (x + 1) y (by omega)]
    by_cases ht : 1 ≤ t
    · simp [ht, hr1]
    · simp [ht, hr0]

set_option maxHeartbeats 2000000 in
lemma stateR_two_odd : ∀ x y : ℤ, (x + y + 2) % 2 ≠ 0 → stateR 841 2 x y = true := by
  intro x y hp
  by_cases h : |x| ≤ 2 ∧ |y| ≤ 2
  · rcases h with ⟨hx, hy⟩
    rcases abs_le.mp hx with ⟨hx1, hx2⟩
    rcases abs_le.mp hy with ⟨hy1, hy2⟩
    interval_cases x <;> interval_cases y <;> first | omega | decide
  · have hout : (2 : ℤ) < |x| + |y| := by cases abs_cases x <;> cases abs_cases y <;> omega
    simpa using stateR_out 841 (by decide) (by decide) 2 x y hout

lemma stateR_checker_841 (k : ℕ) :
    ∀ x y : ℤ, (x + y + ((k + 2 : ℕ) : ℤ)) % 2 ≠ 0 → stateR 841 (k + 2) x y = true := by
  induction k with
  | zero => exact stateR_two_odd
  | succ k ih =>
    intro x y hp
    change stepR 841 (stateR 841 (k + 2)) x y = true
    unfold stepR
    rw [ih x (y - 1) (by omega), ih x (y + 1) (by omega),
        ih (x - 1) y (by omega), ih (x + 1) y (by omega)]
    cases stateR 841 (k + 2) x y <;> decide

lemma stepR_857_eq_841_ge2 (k : ℕ) (x y : ℤ) :
    stepR 857 (stateR 841 (k + 2)) x y = stepR 841 (stateR 841 (k + 2)) x y := by
  unfold stepR
  by_cases hc : stateR 841 (k + 2) x y = true
  · rw [hc]
    cases stateR 841 (k + 2) x (y - 1) <;> cases stateR 841 (k + 2) x (y + 1) <;>
      cases stateR 841 (k + 2) (x - 1) y <;> cases stateR 841 (k + 2) (x + 1) y <;> decide
  · have hcf : stateR 841 (k + 2) x y = false := Bool.eq_false_iff.mpr hc
    have hp : (x + y + ((k + 2 : ℕ) : ℤ)) % 2 = 0 := by
      by_contra hne
      have ht := stateR_checker_841 k x y hne
      rw [hcf] at ht; cases ht
    rw [hcf,
        stateR_checker_841 k x (y - 1) (by omega),
        stateR_checker_841 k x (y + 1) (by omega),
        stateR_checker_841 k (x - 1) y (by omega),
        stateR_checker_841 k (x + 1) y (by omega)]
    decide

set_option maxHeartbeats 2000000 in
lemma stateR_857_eq_841 (t : ℕ) : stateR 857 t = stateR 841 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    change stepR 857 (stateR 857 t) x y = stepR 841 (stateR 841 t) x y
    rw [ih]
    rcases t with _ | _ | k
    · by_cases h : x = 0 ∧ y = 0
      · rcases h with ⟨rfl, rfl⟩; decide
      · unfold stepR
        by_cases h1 : |x| + |y| ≤ 1
        · have hx : -1 ≤ x ∧ x ≤ 1 := by cases abs_cases x <;> cases abs_cases y <;> omega
          have hy : -1 ≤ y ∧ y ≤ 1 := by cases abs_cases x <;> cases abs_cases y <;> omega
          rcases hx with ⟨hx1, hx2⟩; rcases hy with ⟨hy1, hy2⟩
          interval_cases x <;> interval_cases y <;> first | tauto | decide
        · have z0 : ∀ u v : ℤ, ¬(u = 0 ∧ v = 0) → stateR 841 0 u v = false := by
            intro u v huv; simp [stateR, huv]
          rw [z0 x y h,
              z0 x (y - 1) (by cases abs_cases x <;> cases abs_cases y <;> omega),
              z0 x (y + 1) (by cases abs_cases x <;> cases abs_cases y <;> omega),
              z0 (x - 1) y (by cases abs_cases x <;> cases abs_cases y <;> omega),
              z0 (x + 1) y (by cases abs_cases x <;> cases abs_cases y <;> omega)]
          decide
    · by_cases h2 : |x| ≤ 2 ∧ |y| ≤ 2
      · rcases h2 with ⟨hx, hy⟩
        rcases abs_le.mp hx with ⟨hx1, hx2⟩
        rcases abs_le.mp hy with ⟨hy1, hy2⟩
        interval_cases x <;> interval_cases y <;> decide
      · unfold stepR
        have o1 := stateR_out 841 (by decide) (by decide) 1
        have hgt : 2 < |x| ∨ 2 < |y| := by omega
        rw [o1 x y (by cases abs_cases x <;> cases abs_cases y <;> omega),
            o1 x (y - 1) (by cases abs_cases x <;> cases abs_cases y <;> cases abs_cases (y - 1) <;> omega),
            o1 x (y + 1) (by cases abs_cases x <;> cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
            o1 (x - 1) y (by cases abs_cases x <;> cases abs_cases y <;> cases abs_cases (x - 1) <;> omega),
            o1 (x + 1) y (by cases abs_cases x <;> cases abs_cases y <;> cases abs_cases (x + 1) <;> omega)]
        decide
    · exact stepR_857_eq_841_ge2 k x y


lemma state_bridge (r t : ℕ) (x y : ℤ) : OMA.S_oeis_a273684.state r t x y = stateR r t x y := by
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
    simp only [OMA.S_oeis_a273684.state, stateR, stepR, applyRule, ih]
    congr 1
    omega

end Adapt273684

theorem OMA.solution : type_of% @OMA.S_oeis_a273684.main := by
  intro n
  unfold OMA.S_oeis_a273684.a OMA.S_oeis_a273684.count
  simp only [Adapt273684.state_bridge, Adapt273684.stateR_857_eq_841]
