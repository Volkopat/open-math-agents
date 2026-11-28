import OMAStatements.S_oeis_a269712

namespace OMA.S_oeis_a269712

open PowerSeries





/-! ### Binomial coefficients mod 2 -/

/-- Whether C(n, k) is odd. -/
def od (n k : ℕ) : Bool := n.choose k % 2 == 1

theorem od_succ_succ (n k : ℕ) : od (n + 1) (k + 1) = xor (od n k) (od n (k + 1)) := by
  unfold od
  rw [Nat.choose_succ_succ']
  rcases Nat.mod_two_eq_zero_or_one (n.choose k) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (n.choose (k + 1)) with h2 | h2 <;>
    simp [Nat.add_mod, h1, h2]

theorem od_zero (n : ℕ) : od n 0 = true := by simp [od]

theorem od_two (n j : ℕ) : od (n + 2) (j + 2) = xor (od n j) (od n (j + 2)) := by
  have h1 := od_succ_succ (n + 1) (j + 1)
  have h2 := od_succ_succ n j
  have h3 := od_succ_succ n (j + 1)
  simp only [show n + 1 + 1 = n + 2 from rfl, show j + 1 + 1 = j + 2 from rfl] at h1 h3
  rw [h1, h2, h3]
  cases od n j <;> cases od n (j + 1) <;> cases od n (j + 2) <;> rfl

theorem od_even_odd (u i : ℕ) : od (2 * u) (2 * i + 1) = false := by
  induction u generalizing i with
  | zero =>
    show (Nat.choose (2 * 0) (2 * i + 1) % 2 == 1) = false
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl
  | succ u ih =>
    rcases i with _ | i
    · show (Nat.choose (2 * (u + 1)) (2 * 0 + 1) % 2 == 1) = false
      rw [show 2 * 0 + 1 = 1 by ring, Nat.choose_one_right,
        show 2 * (u + 1) % 2 = 0 by omega]
      rfl
    · have e1 := ih i
      have e2 := ih (i + 1)
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring] at e2
      rw [show 2 * (u + 1) = 2 * u + 2 by ring, show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring,
        od_two, e1, e2]
      rfl

theorem od_central (v : ℕ) (hv : 0 < v) : od (2 * v) v = false := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have h := Nat.choose_succ_succ' (2 * w + 1) w
  have hs : Nat.choose (2 * w + 1) (w + 1) = Nat.choose (2 * w + 1) w := by
    have := Nat.choose_symm (n := 2 * w + 1) (k := w) (by omega)
    rwa [show 2 * w + 1 - w = w + 1 by omega] at this
  unfold od
  rw [show 2 * (w + 1) = 2 * w + 1 + 1 by ring, h, hs,
    show (Nat.choose (2 * w + 1) w + Nat.choose (2 * w + 1) w) % 2 = 0 by omega]
  rfl

theorem od_pow (n j : ℕ) (h1 : 0 < j) (h2 : j < 2 ^ n) : od (2 ^ n) j = false := by
  have hd : 2 ∣ (2 ^ n).choose j := Nat.Prime.dvd_choose_pow Nat.prime_two (by omega) (by omega)
  unfold od
  rw [Nat.mod_eq_zero_of_dvd hd]
  rfl

theorem pas (t k : ℕ) : od (t + 2) (k + 1) = xor (od (t + 1) k) (od (t + 1) (k + 1)) :=
  od_succ_succ (t + 1) k

/-! ### The pattern -/

/-- Off-axis cells at e = t - d: ON iff e is even and C(t+1, e/2) is odd. -/
def offOn (t e : ℕ) : Bool := e % 2 == 0 && od (t + 1) (e / 2)

/-- Axis cells: ON iff e is divisible by 4 and C(t+1, e/2) is odd. -/
def axOn (t e : ℕ) : Bool := e % 4 == 0 && od (t + 1) (e / 2)

def offP (t d : ℕ) : Bool := decide (d ≤ t) && offOn t (t - d)

def axP (t d : ℕ) : Bool := decide (d ≤ t) && axOn t (t - d)

theorem off_out {t d : ℕ} (h : t < d) : offP t d = false := by
  simp only [offP, decide_eq_false (by omega : ¬d ≤ t), Bool.false_and]

theorem ax_out {t d : ℕ} (h : t < d) : axP t d = false := by
  simp only [axP, decide_eq_false (by omega : ¬d ≤ t), Bool.false_and]

theorem off_at (t d e : ℕ) (h : t = d + e) : offP t d = offOn t e := by
  simp only [offP, decide_eq_true (by omega : d ≤ t), Bool.true_and, show t - d = e by omega]

theorem ax_at (t d e : ℕ) (h : t = d + e) : axP t d = axOn t e := by
  simp only [axP, decide_eq_true (by omega : d ≤ t), Bool.true_and, show t - d = e by omega]

theorem offOn_odd (t k : ℕ) : offOn t (2 * k + 1) = false := by
  simp only [offOn, show (2 * k + 1) % 2 = 1 by omega]; rfl

theorem offOn_even (t k : ℕ) : offOn t (2 * k) = od (t + 1) k := by
  simp only [offOn, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega]; rfl

theorem axOn_odd (t k : ℕ) : axOn t (2 * k + 1) = false := by
  simp only [axOn, show ((2 * k + 1) % 4 == 0) = false by rw [beq_eq_false_iff_ne]; omega,
    Bool.false_and]

theorem axOn_4 (t j : ℕ) : axOn t (4 * j) = od (t + 1) (2 * j) := by
  simp only [axOn, show 4 * j % 4 = 0 by omega, show 4 * j / 2 = 2 * j by omega]; rfl

theorem axOn_42 (t j : ℕ) : axOn t (4 * j + 2) = false := by
  simp only [axOn, show (4 * j + 2) % 4 = 2 by omega]; rfl

/-! ### One step, for the five kinds of cells -/

theorem stepO2 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 20 ((offP t d).toNat + 2 * ((offP t (d - 1)).toNat + (offP t (d - 1)).toNat +
      (offP t (d + 1)).toNat + (offP t (d + 1)).toNat)) = offP (t + 1) d := by
  rcases (by omega : t + 2 ≤ d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [off_out (by omega : t < d), off_out (by omega : t < d - 1), off_out (by omega : t < d + 1),
      off_out (by omega : t + 1 < d)]
    rfl
  · rw [off_out (by omega : t < d), off_at t (d - 1) (2 * 0) (by omega), offOn_even, od_zero,
      off_out (by omega : t < d + 1), off_at (t + 1) d (2 * 0) (by omega), offOn_even, od_zero]
    rfl
  · obtain ⟨e, he⟩ : ∃ e, t = d + e := ⟨t - d, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [off_at t (d - 1) (2 * k + 1) (by omega), offOn_odd, off_at (t + 1) d (2 * k + 1) (by omega),
        offOn_odd]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [off_out (by omega : t < d + 1)]
        cases offP t d <;> rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [off_at t (d + 1) (2 * k' + 1) (by omega), offOn_odd]
        cases offP t d <;> rfl
    · rw [off_at t d (2 * k + 1) he, offOn_odd, off_at t (d - 1) (2 * (k + 1)) (by omega),
        offOn_even, off_at t (d + 1) (2 * k) (by omega), offOn_even,
        off_at (t + 1) d (2 * (k + 1)) (by omega), offOn_even, od_succ_succ (t + 1) k]
      cases od (t + 1) k <;> cases od (t + 1) (k + 1) <;> rfl

theorem stepO1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 20 ((offP t d).toNat + 2 * ((axP t (d - 1)).toNat + (offP t (d - 1)).toNat +
      (offP t (d + 1)).toNat + (offP t (d + 1)).toNat)) = offP (t + 1) d := by
  rcases (by omega : t + 2 ≤ d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [off_out (by omega : t < d), ax_out (by omega : t < d - 1), off_out (by omega : t < d - 1),
      off_out (by omega : t < d + 1), off_out (by omega : t + 1 < d)]
    rfl
  · rw [off_out (by omega : t < d), ax_at t (d - 1) (4 * 0) (by omega), axOn_4,
      off_at t (d - 1) (2 * 0) (by omega), offOn_even, show 2 * 0 = 0 from rfl, od_zero,
      off_out (by omega : t < d + 1), off_at (t + 1) d (2 * 0) (by omega), offOn_even, od_zero]
    rfl
  · obtain ⟨e, he⟩ : ∃ e, t = d + e := ⟨t - d, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [ax_at t (d - 1) (2 * k + 1) (by omega), axOn_odd, off_at t (d - 1) (2 * k + 1) (by omega),
        offOn_odd, off_at (t + 1) d (2 * k + 1) (by omega), offOn_odd]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [off_out (by omega : t < d + 1)]
        cases offP t d <;> rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [off_at t (d + 1) (2 * k' + 1) (by omega), offOn_odd]
        cases offP t d <;> rfl
    · rw [off_at t d (2 * k + 1) he, offOn_odd, off_at t (d - 1) (2 * (k + 1)) (by omega),
        offOn_even, off_at t (d + 1) (2 * k) (by omega), offOn_even,
        off_at (t + 1) d (2 * (k + 1)) (by omega), offOn_even, od_succ_succ (t + 1) k]
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · rw [ax_at t (d - 1) (4 * j + 2) (by omega), axOn_42]
        cases od (t + 1) (2 * j) <;> cases od (t + 1) (2 * j + 1) <;> rfl
      · rw [ax_at t (d - 1) (4 * (j + 1)) (by omega), axOn_4,
          show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
        cases od (t + 1) (2 * j + 1) <;> cases od (t + 1) (2 * j + 1 + 1) <;> rfl

theorem step11 (t : ℕ) :
    Nat.testBit 20 ((offP t 2).toNat + 2 * ((axP t 1).toNat + (axP t 1).toNat +
      (offP t 3).toNat + (offP t 3).toNat)) = offP (t + 1) 2 := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ 2 ≤ t) with rfl | rfl | ht
  · rfl
  · rfl
  · obtain ⟨e, he⟩ : ∃ e, t = 2 + e := ⟨t - 2, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [ax_at t 1 (2 * k + 1) (by omega), axOn_odd, off_at (t + 1) 2 (2 * k + 1) (by omega),
        offOn_odd]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [off_out (by omega : t < 3)]
        cases offP t 2 <;> rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [off_at t 3 (2 * k' + 1) (by omega), offOn_odd]
        cases offP t 2 <;> rfl
    · rw [off_at t 2 (2 * k + 1) he, offOn_odd, off_at t 3 (2 * k) (by omega), offOn_even,
        off_at (t + 1) 2 (2 * (k + 1)) (by omega), offOn_even, od_succ_succ (t + 1) k]
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · -- k = 2j: the axis cells at e + 1 = 4j + 2 are OFF, and C(t+1, k+1) is even
        rw [ax_at t 1 (4 * j + 2) (by omega), axOn_42,
          show od (t + 1) (2 * j + 1) = false by
            rw [show t + 1 = 2 * (2 * j + 2) by omega, od_even_odd]]
        cases od (t + 1) (2 * j) <;> rfl
      · rw [ax_at t 1 (4 * (j + 1)) (by omega), axOn_4, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
        cases od (t + 1) (2 * j + 1) <;> cases od (t + 1) (2 * j + 1 + 1) <;> rfl

theorem stepA (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 20 ((axP t d).toNat + 2 * ((axP t (d - 1)).toNat + (axP t (d + 1)).toNat +
      (offP t (d + 1)).toNat + (offP t (d + 1)).toNat)) = axP (t + 1) d := by
  rcases (by omega : t + 2 ≤ d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [ax_out (by omega : t < d), ax_out (by omega : t < d - 1), ax_out (by omega : t < d + 1),
      off_out (by omega : t < d + 1), ax_out (by omega : t + 1 < d)]
    rfl
  · rw [ax_out (by omega : t < d), ax_at t (d - 1) (4 * 0) (by omega), axOn_4,
      show 2 * 0 = 0 from rfl, od_zero, ax_out (by omega : t < d + 1),
      off_out (by omega : t < d + 1), ax_at (t + 1) d (4 * 0) (by omega), axOn_4, od_zero]
    rfl
  · obtain ⟨e, he⟩ : ∃ e, t = d + e := ⟨t - d, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [ax_at t (d - 1) (2 * k + 1) (by omega), axOn_odd, ax_at (t + 1) d (2 * k + 1) (by omega),
        axOn_odd]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [ax_out (by omega : t < d + 1), off_out (by omega : t < d + 1)]
        cases axP t d <;> rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [ax_at t (d + 1) (2 * k' + 1) (by omega), axOn_odd,
          off_at t (d + 1) (2 * k' + 1) (by omega), offOn_odd]
        cases axP t d <;> rfl
    · rw [ax_at t d (2 * k + 1) he, axOn_odd, off_at t (d + 1) (2 * k) (by omega), offOn_even]
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · -- k = 2j: inner axis cell at 4j + 2 OFF, outer axis cell at 4j
        rw [ax_at t (d - 1) (4 * j + 2) (by omega), axOn_42, ax_at t (d + 1) (4 * j) (by omega),
          axOn_4, ax_at (t + 1) d (4 * j + 2) (by omega), axOn_42]
        cases od (t + 1) (2 * j) <;> rfl
      · rw [ax_at t (d - 1) (4 * (j + 1)) (by omega), axOn_4, ax_at t (d + 1) (4 * j + 2) (by omega),
          axOn_42, ax_at (t + 1) d (4 * (j + 1)) (by omega), axOn_4,
          show 2 * (j + 1) = 2 * j + 1 + 1 by ring, od_succ_succ (t + 1) (2 * j + 1)]
        cases od (t + 1) (2 * j + 1) <;> cases od (t + 1) (2 * j + 1 + 1) <;> rfl

theorem step0 (t : ℕ) :
    Nat.testBit 20 ((axP t 0).toNat + 2 * ((axP t 1).toNat + (axP t 1).toNat +
      (axP t 1).toNat + (axP t 1).toNat)) = axP (t + 1) 0 := by
  have e : axP (t + 1) 0 = false := by
    rw [ax_at (t + 1) 0 (t + 1) (by omega)]
    by_cases h : (t + 1) % 4 = 0
    · obtain ⟨w, hw⟩ : ∃ w, t + 1 = 4 * (w + 1) := ⟨(t + 1) / 4 - 1, by omega⟩
      rw [hw, axOn_4, show 2 * (w + 1) = 2 * w + 1 + 1 by ring, od_succ_succ,
        show od (4 * (w + 1)) (2 * w + 1) = false by
          rw [show 4 * (w + 1) = 2 * (2 * (w + 1)) by ring]; exact od_even_odd _ w,
        show od (4 * (w + 1)) (2 * w + 1 + 1) = false by
          rw [show 4 * (w + 1) = 2 * (2 * (w + 1)) by ring,
            show 2 * w + 1 + 1 = 2 * (w + 1) by ring]
          exact od_central _ (by omega)]
      rfl
    · simp only [axOn, show ((t + 1) % 4 == 0) = false by simpa using h, Bool.false_and]
  rw [e]
  cases axP t 0 <;> cases axP t 1 <;> rfl

/-! ### The plane -/

/-- The pattern: axis cells by `axP`, the others by `offP`, of the distance |x| + |y|. -/
def P (t : ℕ) (x y : ℤ) : Bool :=
  if x = 0 ∨ y = 0 then axP t (x.natAbs + y.natAbs) else offP t (x.natAbs + y.natAbs)

theorem P_ax (t : ℕ) (x y : ℤ) (h : x = 0 ∨ y = 0) : P t x y = axP t (x.natAbs + y.natAbs) :=
  if_pos h

theorem P_off (t : ℕ) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    P t x y = offP t (x.natAbs + y.natAbs) :=
  if_neg (by tauto)

theorem state_pattern (t : ℕ) : ∀ x y, state 20 t x y = P t x y := by
  induction t with
  | zero =>
    intro x y
    show decide (x = 0 ∧ y = 0) = P 0 x y
    by_cases h : x = 0 ∧ y = 0
    · rw [decide_eq_true h, P_ax 0 x y (Or.inl h.1), show x.natAbs + y.natAbs = 0 by omega]
      rfl
    · rw [decide_eq_false h]
      by_cases h' : x = 0 ∨ y = 0
      · rw [P_ax 0 x y h', ax_out (by omega)]
      · rw [P_off 0 x y (by tauto) (by tauto), off_out (by omega)]
  | succ t ih =>
    intro x y
    show Nat.testBit 20 _ = _
    rw [ih, ih, ih, ih, ih]
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    -- x < 0, y < 0
    · rcases (by omega : (x = -1 ∨ x ≤ -2)) with ex | ex <;>
        rcases (by omega : (y = -1 ∨ y ≤ -2)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 3 by omega,
          show (x + 1).natAbs + y.natAbs = 1 by omega, show x.natAbs + (y - 1).natAbs = 3 by omega,
          show x.natAbs + (y + 1).natAbs = 1 by omega, ← step11 t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO2 t _ (by omega)]
        congr 1; ring
    -- x < 0, y = 0
    · rw [P_ax t x y (by omega), P_ax t (x - 1) y (by omega), P_ax t (x + 1) y (by omega),
        P_off t x (y - 1) (by omega) (by omega), P_off t x (y + 1) (by omega) (by omega),
        P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← stepA t _ (by omega)]
      congr 1; ring
    -- x < 0, y > 0
    · rcases (by omega : (x = -1 ∨ x ≤ -2)) with ex | ex <;>
        rcases (by omega : (y = 1 ∨ 2 ≤ y)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 3 by omega,
          show (x + 1).natAbs + y.natAbs = 1 by omega, show x.natAbs + (y - 1).natAbs = 1 by omega,
          show x.natAbs + (y + 1).natAbs = 3 by omega, ← step11 t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO2 t _ (by omega)]
        congr 1; ring
    -- x = 0, y < 0
    · rw [P_ax t x y (by omega), P_off t (x - 1) y (by omega) (by omega),
        P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
        P_ax t x (y + 1) (by omega), P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← stepA t _ (by omega)]
      congr 1; ring
    -- origin
    · rw [P_ax t x y (by omega), P_ax t (x - 1) y (by omega), P_ax t (x + 1) y (by omega),
        P_ax t x (y - 1) (by omega), P_ax t x (y + 1) (by omega), P_ax (t + 1) x y (by omega),
        show x.natAbs + y.natAbs = 0 by omega, show (x - 1).natAbs + y.natAbs = 1 by omega,
        show (x + 1).natAbs + y.natAbs = 1 by omega, show x.natAbs + (y - 1).natAbs = 1 by omega,
        show x.natAbs + (y + 1).natAbs = 1 by omega, ← step0 t]
    -- x = 0, y > 0
    · rw [P_ax t x y (by omega), P_off t (x - 1) y (by omega) (by omega),
        P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
        P_ax t x (y + 1) (by omega), P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← stepA t _ (by omega)]
      congr 1; ring
    -- x > 0, y < 0
    · rcases (by omega : (x = 1 ∨ 2 ≤ x)) with ex | ex <;>
        rcases (by omega : (y = -1 ∨ y ≤ -2)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 1 by omega,
          show (x + 1).natAbs + y.natAbs = 3 by omega, show x.natAbs + (y - 1).natAbs = 3 by omega,
          show x.natAbs + (y + 1).natAbs = 1 by omega, ← step11 t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO2 t _ (by omega)]
        congr 1; ring
    -- x > 0, y = 0
    · rw [P_ax t x y (by omega), P_ax t (x - 1) y (by omega), P_ax t (x + 1) y (by omega),
        P_off t x (y - 1) (by omega) (by omega), P_off t x (y + 1) (by omega) (by omega),
        P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← stepA t _ (by omega)]
    -- x > 0, y > 0
    · rcases (by omega : (x = 1 ∨ 2 ≤ x)) with ex | ex <;>
        rcases (by omega : (y = 1 ∨ 2 ≤ y)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 1 by omega,
          show (x + 1).natAbs + y.natAbs = 3 by omega, show x.natAbs + (y - 1).natAbs = 1 by omega,
          show x.natAbs + (y + 1).natAbs = 3 by omega, ← step11 t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO2 t _ (by omega)]
        congr 1; ring

/-! ### Counting -/

/-- The number of integers with absolute value i. -/
def w (i : ℕ) : ℕ := if i = 0 then 1 else 2

/-- The number of cells at distance d = |x| + |y| from the origin. -/
def c (d : ℕ) : ℕ := if d = 0 then 1 else 4 * d

theorem sum_Icc_natAbs (n : ℕ) (h : ℕ → ℕ) :
    ∑ x ∈ Finset.Icc (-(n : ℤ)) n, h x.natAbs = ∑ i ∈ Finset.range (n + 1), w i * h i := by
  induction n with
  | zero => simp [w]
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      Finset.sum_range_succ _ (n + 1), Int.natAbs_neg, Int.natAbs_natCast,
      show w (n + 1) = 2 by simp [w]]
    ring

theorem sum_ww (m : ℕ) (hm : 1 ≤ m) : ∑ i ∈ Finset.range (m + 1), w i * w (m - i) = 4 * m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have e : ∀ i ∈ Finset.range k, w (i + 1) * w (k + 1 - (i + 1)) = 4 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [w, if_neg (show i + 1 ≠ 0 by omega), if_neg (show k + 1 - (i + 1) ≠ 0 by omega)]
  rw [Finset.sum_congr rfl e, show k + 1 - (k + 1) = 0 by omega, show k + 1 - 0 = k + 1 by omega,
    show w 0 = 1 from rfl, show w (k + 1) = 2 by simp [w]]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- Grouping the pairs (i, j) with i + j <= n by d = i + j. -/
theorem shell (n : ℕ) (h : ℕ → ℕ) :
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      w i * w j * (if i + j ≤ n then h (i + j) else 0) =
    ∑ d ∈ Finset.range (n + 1), c d * h d := by
  induction n with
  | zero => simp [w, c]
  | succ n ih =>
    have split : ∀ i j, (if i + j ≤ n + 1 then h (i + j) else 0) =
        (if i + j ≤ n then h (i + j) else 0) + (if i + j = n + 1 then h (n + 1) else 0) := by
      intro i j
      by_cases h1 : i + j ≤ n
      · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
      · by_cases h2 : i + j = n + 1
        · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add, h2]
        · rw [if_neg (by omega), if_neg h1, if_neg h2]
    simp only [split, mul_add, Finset.sum_add_distrib]
    have hA : ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
        w i * w j * (if i + j ≤ n then h (i + j) else 0) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          w i * w j * (if i + j ≤ n then h (i + j) else 0) := by
      rw [Finset.sum_range_succ]
      have z : ∑ j ∈ Finset.range (n + 1 + 1),
          w (n + 1) * w j * (if n + 1 + j ≤ n then h (n + 1 + j) else 0) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [if_neg (by omega), mul_zero])
      rw [z, add_zero]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      rw [Finset.sum_range_succ, if_neg (by omega), mul_zero, add_zero]
    have hB : ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
        w i * w j * (if i + j = n + 1 then h (n + 1) else 0) = c (n + 1) * h (n + 1) := by
      have inner : ∀ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
          w i * w j * (if i + j = n + 1 then h (n + 1) else 0) =
            w i * w (n + 1 - i) * h (n + 1) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [Finset.sum_eq_single (n + 1 - i)]
        · rw [if_pos (by omega)]
        · intro j _ hj
          rw [if_neg (by omega), mul_zero]
        · intro hj
          simp only [Finset.mem_range] at hj
          omega
      rw [Finset.sum_congr rfl inner, ← Finset.sum_mul, sum_ww (n + 1) (by omega)]
      simp only [c, if_neg (show n + 1 ≠ 0 by omega)]
    rw [hA, hB, ih, Finset.sum_range_succ _ (n + 1)]

/-- The pattern in terms of |x| and |y|. -/
def Pn (t i j : ℕ) : Bool := if i = 0 ∨ j = 0 then axP t (i + j) else offP t (i + j)

theorem P_eq (t : ℕ) (x y : ℤ) : P t x y = Pn t x.natAbs y.natAbs := by
  unfold P Pn
  by_cases h : x = 0 ∨ y = 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem count_eq (t : ℕ) : count 20 t =
    ∑ i ∈ Finset.range (t + 1), ∑ j ∈ Finset.range (t + 1),
      w i * w j * (if Pn t i j then 1 else 0) := by
  unfold count
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ x ∈ Finset.Icc (-(t : ℤ)) t,
      (∑ y ∈ Finset.Icc (-(t : ℤ)) t, if state 20 t x y = true then 1 else 0) =
        ∑ j ∈ Finset.range (t + 1), w j * (if Pn t x.natAbs j then 1 else 0) := by
    intro x _
    simp only [state_pattern, P_eq]
    exact sum_Icc_natAbs t (fun j => if Pn t x.natAbs j then 1 else 0)
  rw [Finset.sum_congr rfl inner,
    sum_Icc_natAbs t (fun i => ∑ j ∈ Finset.range (t + 1), w j * (if Pn t i j then 1 else 0))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- At t = 2^n - 1 only the edge d = t is ON. -/
theorem offOn_top (n e : ℕ) (hn : 1 ≤ n) (he : e ≤ 2 ^ n - 1) :
    offOn (2 ^ n - 1) e = decide (e = 0) := by
  have hp : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rw [offOn_even, show 2 ^ n - 1 + 1 = 2 ^ n by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [od_zero]; rfl
    · rw [od_pow n k hk (by omega), decide_eq_false (by omega)]
  · rw [offOn_odd, decide_eq_false (by omega)]

theorem axOn_top (n e : ℕ) (hn : 1 ≤ n) (he : e ≤ 2 ^ n - 1) :
    axOn (2 ^ n - 1) e = decide (e = 0) := by
  have hp : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rw [show 2 * (2 * j) = 4 * j by ring, axOn_4, show 2 ^ n - 1 + 1 = 2 ^ n by omega]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [show 2 * 0 = 0 from rfl, od_zero]; rfl
      · rw [od_pow n (2 * j) (by omega) (by omega), decide_eq_false (by omega)]
    · rw [show 2 * (2 * j + 1) = 4 * j + 2 by ring, axOn_42, decide_eq_false (by omega)]
  · rw [axOn_odd, decide_eq_false (by omega)]

theorem point_top (n i j : ℕ) (hn : 1 ≤ n) :
    (if Pn (2 ^ n - 1) i j then 1 else 0) =
      (if i + j ≤ 2 ^ n - 1 then (if i + j = 2 ^ n - 1 then 1 else 0) else 0) := by
  unfold Pn
  by_cases hd : i + j ≤ 2 ^ n - 1
  · rw [if_pos hd]
    by_cases h0 : i = 0 ∨ j = 0
    · rw [if_pos h0, ax_at (2 ^ n - 1) (i + j) (2 ^ n - 1 - (i + j)) (by omega),
        axOn_top n _ hn (by omega)]
      by_cases h1 : i + j = 2 ^ n - 1
      · rw [decide_eq_true (by omega), if_pos h1]; rfl
      · rw [decide_eq_false (by omega), if_neg h1]; rfl
    · rw [if_neg h0, off_at (2 ^ n - 1) (i + j) (2 ^ n - 1 - (i + j)) (by omega),
        offOn_top n _ hn (by omega)]
      by_cases h1 : i + j = 2 ^ n - 1
      · rw [decide_eq_true (by omega), if_pos h1]; rfl
      · rw [decide_eq_false (by omega), if_neg h1]; rfl
  · rw [if_neg hd]
    by_cases h0 : i = 0 ∨ j = 0
    · rw [if_pos h0, ax_out (by omega : 2 ^ n - 1 < i + j)]; rfl
    · rw [if_neg h0, off_out (by omega : 2 ^ n - 1 < i + j)]; rfl

/-- At t = 2^n - 1 (n >= 1) exactly the 4t cells at distance t are ON. -/
theorem count_top (n : ℕ) (hn : 1 ≤ n) : count 20 (2 ^ n - 1) = 4 * (2 ^ n - 1) := by
  have hp : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [count_eq]
  have e : ∀ i ∈ Finset.range (2 ^ n - 1 + 1), ∀ j ∈ Finset.range (2 ^ n - 1 + 1),
      w i * w j * (if Pn (2 ^ n - 1) i j then 1 else 0) =
        w i * w j * (if i + j ≤ 2 ^ n - 1 then (fun d => if d = 2 ^ n - 1 then 1 else 0) (i + j)
          else 0) := by
    intro i _ j _
    rw [point_top n i j hn]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => e i hi j hj)),
    shell (2 ^ n - 1) (fun d => if d = 2 ^ n - 1 then 1 else 0),
    Finset.sum_eq_single (2 ^ n - 1)]
  · simp only [c, if_neg (show 2 ^ n - 1 ≠ 0 by omega), ite_true, mul_one]
  · intro d _ hd
    simp only [if_neg hd, mul_zero]
  · intro h
    simp only [Finset.mem_range] at h
    omega

/-- Barker's closed forms, for n > 0. -/
theorem closed (n : ℕ) (hn : 0 < n) : (a n : ℤ) = 4 * (2 ^ n - 1) := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  unfold a
  rw [count_top n hn]
  push_cast [Nat.cast_sub hp]
  ring

theorem closed' (n : ℕ) (hn : 0 < n) : (a n : ℤ) = A028399 (n + 2) := by
  rw [closed n hn, A028399, pow_add]
  ring

theorem a_zero : a 0 = 1 := by
  show count 20 0 = 1
  rw [count_eq]
  decide

theorem val (n N : ℕ) (hn : 0 < n) (hN : (N : ℤ) = 4 * (2 ^ n - 1)) : a n = N := by
  have h := (closed n hn).trans hN.symm
  exact_mod_cast h

/-- Controls: the entry's terms a(0..15). -/
theorem controls : a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 12 ∧ a 3 = 28 ∧ a 4 = 60 ∧ a 5 = 124 ∧
    a 6 = 252 ∧ a 7 = 508 ∧ a 8 = 1020 ∧ a 9 = 2044 ∧ a 10 = 4092 ∧ a 11 = 8188 ∧
    a 12 = 16380 ∧ a 13 = 32764 ∧ a 14 = 65532 ∧ a 15 = 131068 :=
  ⟨a_zero, val 1 4 (by norm_num) (by norm_num), val 2 12 (by norm_num) (by norm_num),
    val 3 28 (by norm_num) (by norm_num), val 4 60 (by norm_num) (by norm_num),
    val 5 124 (by norm_num) (by norm_num), val 6 252 (by norm_num) (by norm_num),
    val 7 508 (by norm_num) (by norm_num), val 8 1020 (by norm_num) (by norm_num),
    val 9 2044 (by norm_num) (by norm_num), val 10 4092 (by norm_num) (by norm_num),
    val 11 8188 (by norm_num) (by norm_num), val 12 16380 (by norm_num) (by norm_num),
    val 13 32764 (by norm_num) (by norm_num), val 14 65532 (by norm_num) (by norm_num),
    val 15 131068 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 2. -/
theorem recurrence (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    closed (m + 3) (by omega), closed (m + 2) (by omega), closed (m + 1) (by omega)]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X)) = 1 + X + 2 * X ^ 2 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have hD : A * ((1 - X) * (1 - 2 * X)) = A - C 3 * (A * X ^ 1) + C 2 * (A * X ^ 2) := by
    rw [c2, c3]; ring
  have hN : (1 + X + 2 * X ^ 2 : PowerSeries ℤ) = 1 + X ^ 1 + X ^ 2 * C 2 := by
    rw [c2]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  obtain ⟨v0, v1, v2, -⟩ := controls
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp [v0, v1, v2]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, if_false]
    linear_combination r

/-- Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 0 < n → (a n : ℤ) = 4 * (2 ^ n - 1) ∧ (a n : ℤ) = A028399 (n + 2)) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X)) = 1 + X + 2 * X ^ 2 :=
  ⟨fun n hn => ⟨closed n hn, closed' n hn⟩, recurrence, gf⟩

end OMA.S_oeis_a269712

theorem OMA.solution : type_of% @OMA.S_oeis_a269712.main :=
  OMA.S_oeis_a269712.conjecture
