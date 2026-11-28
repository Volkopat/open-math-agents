import OMAStatements.S_oeis_a284028

namespace OMA.S_oeis_a284028




/-- The Rule 790 state at stage t of a cell at distance d = |x| + |y| from the origin. -/
def g : ℕ → ℕ → Bool
  | 0, d => d == 0
  | t + 1, d => if d = 0 then true else if t + 1 < d then false else if d = t + 1 then true
      else if g t d then (g t (d - 1) == g t (d + 1)) else true

theorem g_succ (t d : ℕ) : g (t + 1) d = if d = 0 then true else if t + 1 < d then false
    else if d = t + 1 then true else if g t d then (g t (d - 1) == g t (d + 1)) else true := rfl

theorem g_origin (t : ℕ) : g t 0 = true := by
  cases t with
  | zero => rfl
  | succ t => rw [g_succ, if_pos rfl]

theorem g_out (t d : ℕ) (h : t < d) : g t d = false := by
  cases t with
  | zero => simp only [g, beq_eq_false_iff_ne]; omega
  | succ t => rw [g_succ, if_neg (by omega), if_pos h]

theorem g_edge (t : ℕ) : g t t = true := by
  cases t with
  | zero => rfl
  | succ t => rw [g_succ, if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- Every OFF cell inside the cone has d + t odd. -/
theorem g_parity (t : ℕ) : ∀ d, d ≤ t → g t d = false → (d + t) % 2 = 1 := by
  induction t with
  | zero =>
    intro d hd h
    obtain rfl : d = 0 := by omega
    exact absurd h (by decide)
  | succ t ih =>
    intro d hd h
    by_cases h0 : d = 0
    · rw [g_succ, if_pos h0] at h; exact absurd h (by decide)
    by_cases h2 : d = t + 1
    · rw [g_succ, if_neg h0, if_neg (by omega), if_pos h2] at h; exact absurd h (by decide)
    rw [g_succ, if_neg h0, if_neg (by omega), if_neg h2] at h
    cases hc : g t d
    · rw [hc, if_neg (by decide)] at h; exact absurd h (by decide)
    · rw [hc, if_pos rfl] at h
      cases ha : g t (d - 1) <;> cases hb : g t (d + 1) <;> rw [ha, hb] at h
      · exact absurd h (by decide)
      · have := ih (d - 1) (by omega) ha
        omega
      · by_cases hd1 : d + 1 ≤ t
        · have := ih (d + 1) hd1 hb
          omega
        · omega
      · exact absurd h (by decide)

/-- The neighbors of an OFF cell inside the cone are ON. -/
theorem g_nbrs (t d : ℕ) (hd1 : 1 ≤ d) (hdt : d ≤ t) (h : g t d = false) :
    g t (d - 1) = true ∧ g t (d + 1) = true := by
  have hp := g_parity t d hdt h
  constructor
  · by_contra hc
    have := g_parity t (d - 1) (by omega) (by simpa using hc)
    omega
  · by_cases hd : d + 1 ≤ t
    · by_contra hc
      have := g_parity t (d + 1) hd (by simpa using hc)
      omega
    · obtain rfl : d = t := by omega
      rw [g_edge] at h
      exact absurd h (by decide)

/-- Rule 790 at the origin: four neighbors at distance 1. -/
theorem step0 (t : ℕ) : Nat.testBit 790 ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rw [g_origin, g_origin]
  cases g t 1 <;> rfl

/-- Rule 790 on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 790 ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  rcases (by omega : t + 1 < d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [g_out t d (by omega), g_out t (d - 1) (by omega), g_out t (d + 1) (by omega),
      g_out (t + 1) d c]
    rfl
  · subst c
    rw [g_out t (t + 1) (by omega), show t + 1 - 1 = t by omega, g_edge t,
      g_out t (t + 1 + 1) (by omega), g_edge (t + 1)]
    rfl
  · rw [g_succ t d, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    cases hc : g t d
    · obtain ⟨ha, hb⟩ := g_nbrs t d hd c hc
      rw [ha, hb]
      rfl
    · cases ha : g t (d - 1) <;> cases hb : g t (d + 1) <;> rfl

/-- Rule 790 off the axes: two neighbors at distance d - 1, two at d + 1. -/
theorem step2 (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit 790 ((g t d).toNat + 2 * (2 * (g t (d - 1)).toNat + 2 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  rcases (by omega : t + 1 < d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [g_out t d (by omega), g_out t (d - 1) (by omega), g_out t (d + 1) (by omega),
      g_out (t + 1) d c]
    rfl
  · subst c
    rw [g_out t (t + 1) (by omega), show t + 1 - 1 = t by omega, g_edge t,
      g_out t (t + 1 + 1) (by omega), g_edge (t + 1)]
    rfl
  · rw [g_succ t d, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    cases hc : g t d
    · obtain ⟨ha, hb⟩ := g_nbrs t d (by omega) c hc
      rw [ha, hb]
      rfl
    · cases ha : g t (d - 1) <;> cases hb : g t (d + 1) <;> rfl

/-- Stage t of Rule 790 is the profile `g` of the distance |x| + |y|. -/
theorem state790_pattern (t : ℕ) : ∀ x y, state 790 t x y = g t (x.natAbs + y.natAbs) := by
  induction t with
  | zero =>
    intro x y
    by_cases h : x = 0 ∧ y = 0
    · rw [show state 790 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_true h,
        show x.natAbs + y.natAbs = 0 by omega]
      rfl
    · rw [show state 790 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_false h,
        g_out 0 _ (by omega)]
  | succ t ih =>
    intro x y
    show Nat.testBit 790 _ = _
    rw [ih, ih, ih, ih, ih]
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = 1 by omega,
        show (x + 1).natAbs + y.natAbs = 1 by omega,
        show x.natAbs + (y - 1).natAbs = 1 by omega,
        show x.natAbs + (y + 1).natAbs = 1 by omega,
        show x.natAbs + y.natAbs = 0 by omega, ← step0 t]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring

/-- The Rule 771 state at stage t of a cell at distance d: stage t + 1 is g t inside the cone of
stage t, OFF at distance t + 1 and ON beyond. -/
def f : ℕ → ℕ → Bool
  | 0, d => d == 0
  | t + 1, d => if d ≤ t then g t d else decide (t + 1 < d)

theorem f_zero_pos {d : ℕ} (h : 0 < d) : f 0 d = false := by
  simp only [f, beq_eq_false_iff_ne]; omega

theorem f_in (s e : ℕ) (h : e ≤ s + 1) : f (s + 1) e = g s e := by
  show (if e ≤ s then g s e else decide (s + 1 < e)) = g s e
  by_cases h' : e ≤ s
  · rw [if_pos h']
  · rw [if_neg h', g_out s e (by omega)]
    simp only [decide_eq_false_iff_not]; omega

theorem f_out (s e : ℕ) (h : s + 1 < e) : f (s + 1) e = true := by
  show (if e ≤ s then g s e else decide (s + 1 < e)) = true
  rw [if_neg (by omega)]
  simp only [decide_eq_true_eq]; omega

theorem f_edge (s : ℕ) : f (s + 1) (s + 1) = false := by
  rw [f_in s (s + 1) le_rfl, g_out s (s + 1) (by omega)]

/-- Rule 771 at the origin. -/
theorem step0' (t : ℕ) :
    Nat.testBit 771 ((f t 0).toNat + 2 * (4 * (f t 1).toNat)) = f (t + 1) 0 := by
  cases t with
  | zero => rfl
  | succ s =>
    rw [f_in s 0 (by omega), f_in (s + 1) 0 (by omega), g_origin, g_origin]
    cases f (s + 1) 1 <;> rfl

/-- Rule 771 on an axis. -/
theorem step1' (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 771 ((f t d).toNat + 2 * ((f t (d - 1)).toNat + 3 * (f t (d + 1)).toNat)) =
      f (t + 1) d := by
  cases t with
  | zero =>
    rcases (by omega : d = 1 ∨ 2 ≤ d) with c | c
    · subst c; rfl
    · rw [f_zero_pos (by omega : 0 < d), f_zero_pos (by omega : 0 < d - 1),
        f_zero_pos (by omega : 0 < d + 1), f_out 0 d (by omega)]
      rfl
  | succ s =>
    rcases (by omega : d ≤ s ∨ d = s + 1 ∨ d = s + 2 ∨ s + 3 ≤ d) with c | c | c | c
    · rw [f_in s d (by omega), f_in s (d - 1) (by omega), f_in s (d + 1) (by omega),
        f_in (s + 1) d (by omega), g_succ s d, if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      cases hc : g s d
      · obtain ⟨ha, hb⟩ := g_nbrs s d hd c hc
        rw [ha, hb]
        rfl
      · cases ha : g s (d - 1) <;> cases hb : g s (d + 1) <;> rfl
    · subst c
      rw [f_edge s, show s + 1 - 1 = s by omega, f_in s s (by omega), g_edge s,
        f_out s (s + 1 + 1) (by omega), f_in (s + 1) (s + 1) (by omega), g_edge (s + 1)]
      rfl
    · subst c
      rw [f_out s (s + 2) (by omega), show s + 2 - 1 = s + 1 by omega, f_edge s,
        f_out s (s + 2 + 1) (by omega)]
      show _ = (if s + 2 ≤ s + 1 then g (s + 1) (s + 2) else decide (s + 1 + 1 < s + 2))
      rw [if_neg (by omega), decide_eq_false (by omega : ¬(s + 1 + 1 < s + 2))]
      rfl
    · rw [f_out s d (by omega), f_out s (d - 1) (by omega), f_out s (d + 1) (by omega),
        f_out (s + 1) d (by omega)]
      rfl

/-- Rule 771 off the axes. -/
theorem step2' (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit 771 ((f t d).toNat + 2 * (2 * (f t (d - 1)).toNat + 2 * (f t (d + 1)).toNat)) =
      f (t + 1) d := by
  cases t with
  | zero =>
    rw [f_zero_pos (by omega : 0 < d), f_zero_pos (by omega : 0 < d - 1),
      f_zero_pos (by omega : 0 < d + 1), f_out 0 d (by omega)]
    rfl
  | succ s =>
    rcases (by omega : d ≤ s ∨ d = s + 1 ∨ d = s + 2 ∨ s + 3 ≤ d) with c | c | c | c
    · rw [f_in s d (by omega), f_in s (d - 1) (by omega), f_in s (d + 1) (by omega),
        f_in (s + 1) d (by omega), g_succ s d, if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      cases hc : g s d
      · obtain ⟨ha, hb⟩ := g_nbrs s d (by omega) c hc
        rw [ha, hb]
        rfl
      · cases ha : g s (d - 1) <;> cases hb : g s (d + 1) <;> rfl
    · subst c
      rw [f_edge s, show s + 1 - 1 = s by omega, f_in s s (by omega), g_edge s,
        f_out s (s + 1 + 1) (by omega), f_in (s + 1) (s + 1) (by omega), g_edge (s + 1)]
      rfl
    · subst c
      rw [f_out s (s + 2) (by omega), show s + 2 - 1 = s + 1 by omega, f_edge s,
        f_out s (s + 2 + 1) (by omega)]
      show _ = (if s + 2 ≤ s + 1 then g (s + 1) (s + 2) else decide (s + 1 + 1 < s + 2))
      rw [if_neg (by omega), decide_eq_false (by omega : ¬(s + 1 + 1 < s + 2))]
      rfl
    · rw [f_out s d (by omega), f_out s (d - 1) (by omega), f_out s (d + 1) (by omega),
        f_out (s + 1) d (by omega)]
      rfl

/-- Stage t of Rule 771 is the profile `f` of the distance |x| + |y|. -/
theorem state771_pattern (t : ℕ) : ∀ x y, state 771 t x y = f t (x.natAbs + y.natAbs) := by
  induction t with
  | zero =>
    intro x y
    by_cases h : x = 0 ∧ y = 0
    · rw [show state 771 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_true h,
        show x.natAbs + y.natAbs = 0 by omega]
      rfl
    · rw [show state 771 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_false h,
        f_zero_pos (by omega)]
  | succ t ih =>
    intro x y
    show Nat.testBit 771 _ = _
    rw [ih, ih, ih, ih, ih]
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step1' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = 1 by omega,
        show (x + 1).natAbs + y.natAbs = 1 by omega,
        show x.natAbs + (y - 1).natAbs = 1 by omega,
        show x.natAbs + (y + 1).natAbs = 1 by omega,
        show x.natAbs + y.natAbs = 0 by omega, ← step0' t]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1' t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2' t _ (by omega)]
      congr 1; ring

theorem a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), if g n k then 10 ^ k else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state790_pattern, show (-(k : ℤ)).natAbs + (0 : ℤ).natAbs = k by simp]

theorem A283906_eq (n : ℕ) :
    A283906 n = ∑ k ∈ Finset.range (n + 1), if f n k then 10 ^ k else 0 := by
  unfold A283906
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state771_pattern, show (-(k : ℤ)).natAbs + (0 : ℤ).natAbs = k by simp]

/-- Controls: the entries' terms a(0..9) and A283906(0..10). -/
theorem controls : (List.range 10).map a =
      [1, 11, 101, 1111, 10111, 111011, 1010101, 11111111, 101111111, 1110111111] ∧
    (List.range 11).map A283906 =
      [1, 1, 11, 101, 1111, 10111, 111011, 1010101, 11111111, 101111111, 1110111111] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n k then 10 ^ k else 0 from funext a_eq,
    show A283906 = fun n => ∑ k ∈ Finset.range (n + 1), if f n k then 10 ^ k else 0 from
      funext A283906_eq]
  decide

/-- Mathar's conjecture. -/
theorem conjecture : ∀ n : ℕ, a n = A283906 (n + 1) := by
  intro n
  rw [a_eq, A283906_eq, Finset.sum_range_succ (fun k : ℕ => if f (n + 1) k then 10 ^ k else 0)
    (n + 1), f_edge n, if_neg (by decide), add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [f_in n k (by omega)]

end OMA.S_oeis_a284028

theorem OMA.solution : type_of% @OMA.S_oeis_a284028.main :=
  OMA.S_oeis_a284028.conjecture
