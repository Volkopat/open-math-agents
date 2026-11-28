import OMAStatements.S_oeis_a273570

namespace OMA.S_oeis_a273570

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

theorem od_one (n : ℕ) : od n 1 = (n % 2 == 1) := by simp [od]

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

theorem od_one' (n : ℕ) (h : n % 2 = 1) : od n 1 = true := by
  rw [od_one, h]; rfl

theorem pas3 (t k : ℕ) : od (t + 3) (k + 1) = xor (od (t + 2) k) (od (t + 2) (k + 1)) :=
  od_succ_succ (t + 2) k

theorem pas2 (t k : ℕ) : od (t + 2) (k + 1) = xor (od (t + 1) k) (od (t + 1) (k + 1)) :=
  od_succ_succ (t + 1) k

/-! ### The pattern -/

/-- Off-axis cells at e = t - d: OFF iff e is odd and C(t+2, (e+1)/2) is odd. -/
def oo (t e : ℕ) : Bool := e % 2 == 1 && od (t + 2) ((e + 1) / 2)

/-- Axis cells: OFF iff moreover t is even or C(t+1, (e+1)/2) is odd. -/
def ao (t e : ℕ) : Bool := oo t e && (t % 2 == 0 || od (t + 1) ((e + 1) / 2))

def offP (t d : ℕ) : Bool := decide (d ≤ t) && !oo t (t - d)

def axP (t d : ℕ) : Bool := decide (d ≤ t) && !ao t (t - d)

theorem off_out {t d : ℕ} (h : t < d) : offP t d = false := by
  simp only [offP, decide_eq_false (by omega : ¬d ≤ t), Bool.false_and]

theorem ax_out {t d : ℕ} (h : t < d) : axP t d = false := by
  simp only [axP, decide_eq_false (by omega : ¬d ≤ t), Bool.false_and]

theorem off_at (t d e : ℕ) (h : t = d + e) : offP t d = !oo t e := by
  simp only [offP, decide_eq_true (by omega : d ≤ t), Bool.true_and, show t - d = e by omega]

theorem ax_at (t d e : ℕ) (h : t = d + e) : axP t d = !ao t e := by
  simp only [axP, decide_eq_true (by omega : d ≤ t), Bool.true_and, show t - d = e by omega]

theorem oo_even (t k : ℕ) : oo t (2 * k) = false := by
  simp only [oo, show 2 * k % 2 = 0 by omega]; rfl

theorem ao_even (t k : ℕ) : ao t (2 * k) = false := by
  simp only [ao, oo_even, Bool.false_and]

theorem oo_odd (t k : ℕ) : oo t (2 * k + 1) = od (t + 2) (k + 1) := by
  simp only [oo, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  rfl

theorem ao_odd (t k : ℕ) :
    ao t (2 * k + 1) = (od (t + 2) (k + 1) && (t % 2 == 0 || od (t + 1) (k + 1))) := by
  simp only [ao, oo_odd, show (2 * k + 1 + 1) / 2 = k + 1 by omega]

theorem par_even (n : ℕ) (h : n % 2 = 0) (X : Bool) : (n % 2 == 0 || X) = true := by
  rw [h]; rfl

theorem par_odd (n : ℕ) (h : n % 2 = 1) (X : Bool) : (n % 2 == 0 || X) = X := by
  rw [h]; rfl

theorem oo_odd' (t k : ℕ) : oo (t + 1) (2 * k + 1) = od (t + 3) (k + 1) := oo_odd (t + 1) k

theorem ao_odd' (t k : ℕ) :
    ao (t + 1) (2 * k + 1) = (od (t + 3) (k + 1) && ((t + 1) % 2 == 0 || od (t + 2) (k + 1))) :=
  ao_odd (t + 1) k

/-! ### One step, for the five kinds of cells -/

/-- Off the axes, two neighbors at d - 1 and two at d + 1, all off the axes. -/
theorem stepO2 (R : ℕ) (hR : R = 798 ∨ R = 862) (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit R ((offP t d).toNat + 2 * ((offP t (d - 1)).toNat + (offP t (d - 1)).toNat +
      (offP t (d + 1)).toNat + (offP t (d + 1)).toNat)) = offP (t + 1) d := by
  rcases (by omega : t + 2 ≤ d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [off_out (by omega : t < d), off_out (by omega : t < d - 1), off_out (by omega : t < d + 1),
      off_out (by omega : t + 1 < d)]
    rcases hR with rfl | rfl <;> rfl
  · rw [off_out (by omega : t < d), off_at t (d - 1) 0 (by omega), off_out (by omega : t < d + 1),
      off_at (t + 1) d 0 (by omega), show (0 : ℕ) = 2 * 0 from rfl, oo_even, oo_even]
    rcases hR with rfl | rfl <;> rfl
  · obtain ⟨e, he⟩ : ∃ e, t = d + e := ⟨t - d, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [off_at t d (2 * k) he, oo_even, off_at t (d - 1) (2 * k + 1) (by omega), oo_odd,
        off_at (t + 1) d (2 * k + 1) (by omega), oo_odd', pas3]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [off_out (by omega : t < d + 1), od_zero]
        cases od (t + 2) (0 + 1) <;> rcases hR with rfl | rfl <;> rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [off_at t (d + 1) (2 * k' + 1) (by omega), oo_odd]
        cases od (t + 2) (k' + 1) <;> cases od (t + 2) (k' + 1 + 1) <;>
          rcases hR with rfl | rfl <;> rfl
    · rw [off_at t (d - 1) (2 * k + 2) (by omega), show 2 * k + 2 = 2 * (k + 1) by ring, oo_even,
        off_at t (d + 1) (2 * k) (by omega), oo_even, off_at (t + 1) d (2 * (k + 1)) (by omega),
        oo_even]
      cases offP t d <;> rcases hR with rfl | rfl <;> rfl

/-- Next to an axis: inner neighbors one on the axis and one off it, two outer ones off it. -/
theorem stepO1 (R : ℕ) (hR : R = 798 ∨ R = 862) (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit R ((offP t d).toNat + 2 * ((axP t (d - 1)).toNat + (offP t (d - 1)).toNat +
      (offP t (d + 1)).toNat + (offP t (d + 1)).toNat)) = offP (t + 1) d := by
  rcases (by omega : t + 2 ≤ d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [off_out (by omega : t < d), ax_out (by omega : t < d - 1), off_out (by omega : t < d - 1),
      off_out (by omega : t < d + 1), off_out (by omega : t + 1 < d)]
    rcases hR with rfl | rfl <;> rfl
  · rw [off_out (by omega : t < d), ax_at t (d - 1) 0 (by omega), off_at t (d - 1) 0 (by omega),
      off_out (by omega : t < d + 1), off_at (t + 1) d 0 (by omega),
      show (0 : ℕ) = 2 * 0 from rfl, ao_even, oo_even]
    rcases hR with rfl | rfl <;> rfl
  · obtain ⟨e, he⟩ : ∃ e, t = d + e := ⟨t - d, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [off_at t d (2 * k) he, oo_even, ax_at t (d - 1) (2 * k + 1) (by omega), ao_odd,
        off_at t (d - 1) (2 * k + 1) (by omega), oo_odd,
        off_at (t + 1) d (2 * k + 1) (by omega), oo_odd', pas3]
      rcases Nat.mod_two_eq_zero_or_one t with hp | hp
      · simp only [par_even t hp]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [off_out (by omega : t < d + 1), od_zero]
          cases od (t + 2) (0 + 1) <;> rcases hR with rfl | rfl <;> rfl
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [off_at t (d + 1) (2 * k' + 1) (by omega), oo_odd]
          cases od (t + 2) (k' + 1) <;> cases od (t + 2) (k' + 1 + 1) <;>
            rcases hR with rfl | rfl <;> rfl
      · simp only [par_odd t hp]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [off_out (by omega : t < d + 1), od_zero]
          cases od (t + 2) (0 + 1) <;> cases od (t + 1) (0 + 1) <;>
            rcases hR with rfl | rfl <;> rfl
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [off_at t (d + 1) (2 * k' + 1) (by omega), oo_odd]
          cases od (t + 2) (k' + 1) <;> cases od (t + 2) (k' + 1 + 1) <;>
            cases od (t + 1) (k' + 1 + 1) <;> rcases hR with rfl | rfl <;> rfl
    · rw [ax_at t (d - 1) (2 * k + 2) (by omega), off_at t (d - 1) (2 * k + 2) (by omega),
        show 2 * k + 2 = 2 * (k + 1) by ring, ao_even, oo_even,
        off_at t (d + 1) (2 * k) (by omega), oo_even, off_at (t + 1) d (2 * (k + 1)) (by omega),
        oo_even]
      cases offP t d <;> rcases hR with rfl | rfl <;> rfl

/-- The cell (1, 1): both inner neighbors on the axes at distance 1. -/
theorem step11 (R : ℕ) (hR : R = 798 ∨ R = 862) (t : ℕ) :
    Nat.testBit R ((offP t 2).toNat + 2 * ((axP t 1).toNat + (axP t 1).toNat +
      (offP t 3).toNat + (offP t 3).toNat)) = offP (t + 1) 2 := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ 2 ≤ t) with rfl | rfl | ht
  · rcases hR with rfl | rfl <;> rfl
  · rcases hR with rfl | rfl <;> rfl
  · obtain ⟨e, he⟩ : ∃ e, t = 2 + e := ⟨t - 2, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [off_at t 2 (2 * k) he, oo_even, ax_at t 1 (2 * k + 1) (by omega), ao_odd,
        off_at (t + 1) 2 (2 * k + 1) (by omega), oo_odd', pas3]
      simp only [par_even t (by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [off_out (by omega : t < 3), od_zero]
        cases od (t + 2) (0 + 1) <;> rcases hR with rfl | rfl <;> rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [off_at t 3 (2 * k' + 1) (by omega), oo_odd]
        cases od (t + 2) (k' + 1) <;> cases od (t + 2) (k' + 1 + 1) <;>
          rcases hR with rfl | rfl <;> rfl
    · rw [ax_at t 1 (2 * k + 2) (by omega), show 2 * k + 2 = 2 * (k + 1) by ring, ao_even,
        off_at t 3 (2 * k) (by omega), oo_even, off_at (t + 1) 2 (2 * (k + 1)) (by omega),
        oo_even]
      cases offP t 2 <;> rcases hR with rfl | rfl <;> rfl

/-- An axis cell at distance d >= 1: inner neighbor on the axis, outer ones on the axis and off it. -/
theorem stepA (R : ℕ) (hR : R = 798 ∨ R = 862) (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit R ((axP t d).toNat + 2 * ((axP t (d - 1)).toNat + (axP t (d + 1)).toNat +
      (offP t (d + 1)).toNat + (offP t (d + 1)).toNat)) = axP (t + 1) d := by
  rcases (by omega : t + 2 ≤ d ∨ d = t + 1 ∨ d ≤ t) with c | c | c
  · rw [ax_out (by omega : t < d), ax_out (by omega : t < d - 1), ax_out (by omega : t < d + 1),
      off_out (by omega : t < d + 1), ax_out (by omega : t + 1 < d)]
    rcases hR with rfl | rfl <;> rfl
  · rw [ax_out (by omega : t < d), ax_at t (d - 1) 0 (by omega), ax_out (by omega : t < d + 1),
      off_out (by omega : t < d + 1), ax_at (t + 1) d 0 (by omega),
      show (0 : ℕ) = 2 * 0 from rfl, ao_even, ao_even]
    rcases hR with rfl | rfl <;> rfl
  · obtain ⟨e, he⟩ : ∃ e, t = d + e := ⟨t - d, by omega⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · rw [ax_at t d (2 * k) he, ao_even, ax_at t (d - 1) (2 * k + 1) (by omega), ao_odd,
        ax_at (t + 1) d (2 * k + 1) (by omega), ao_odd', pas3]
      rcases Nat.mod_two_eq_zero_or_one t with hp | hp
      · -- t even
        simp only [par_odd (t + 1) (by omega), par_even t hp]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [ax_out (by omega : t < d + 1), off_out (by omega : t < d + 1), od_zero]
          cases od (t + 2) (0 + 1) <;> rcases hR with rfl | rfl <;> rfl
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [ax_at t (d + 1) (2 * k' + 1) (by omega), ao_odd, off_at t (d + 1) (2 * k' + 1)
            (by omega), oo_odd]
          simp only [par_even t hp]
          cases od (t + 2) (k' + 1) <;> cases od (t + 2) (k' + 1 + 1) <;>
            rcases hR with rfl | rfl <;> rfl
      · -- t odd: t + 1 = 2u
        obtain ⟨u, hu⟩ : ∃ u, t + 1 = 2 * u := ⟨(t + 1) / 2, by omega⟩
        simp only [par_even (t + 1) (by omega), par_odd t hp]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [ax_out (by omega : t < d + 1), off_out (by omega : t < d + 1), od_zero,
            show od (t + 1) (0 + 1) = false by rw [hu, show 0 + 1 = 2 * 0 + 1 from rfl, od_even_odd],
            show od (t + 2) (0 + 1) = true from od_one' (t + 2) (by omega)]
          rcases hR with rfl | rfl <;> rfl
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [ax_at t (d + 1) (2 * k' + 1) (by omega), ao_odd, off_at t (d + 1) (2 * k' + 1)
            (by omega), oo_odd]
          simp only [par_odd t hp]
          rw [pas2 t (k' + 1), pas2 t k']
          rcases Nat.even_or_odd' k' with ⟨i, rfl | rfl⟩
          · -- k' even: k' + 1 odd
            rw [show od (t + 1) (2 * i + 1) = false by rw [hu, od_even_odd]]
            cases od (t + 1) (2 * i) <;> cases od (t + 1) (2 * i + 1 + 1) <;>
              rcases hR with rfl | rfl <;> rfl
          · -- k' odd: k' and k' + 2 odd
            rw [show od (t + 1) (2 * i + 1) = false by rw [hu, od_even_odd],
              show od (t + 1) (2 * i + 1 + 1 + 1) = false by
                rw [hu, show 2 * i + 1 + 1 + 1 = 2 * (i + 1) + 1 by ring, od_even_odd]]
            cases od (t + 1) (2 * i + 1 + 1) <;> rcases hR with rfl | rfl <;> rfl
    · rw [ax_at t (d - 1) (2 * k + 2) (by omega), show 2 * k + 2 = 2 * (k + 1) by ring, ao_even,
        ax_at t (d + 1) (2 * k) (by omega), ao_even, off_at t (d + 1) (2 * k) (by omega), oo_even,
        ax_at (t + 1) d (2 * (k + 1)) (by omega), ao_even]
      cases axP t d <;> rcases hR with rfl | rfl <;> rfl

/-- The origin: four axis neighbors at distance 1. -/
theorem step0 (R : ℕ) (hR : R = 798 ∨ R = 862) (t : ℕ) :
    Nat.testBit R ((axP t 0).toNat + 2 * ((axP t 1).toNat + (axP t 1).toNat +
      (axP t 1).toNat + (axP t 1).toNat)) = axP (t + 1) 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rcases hR with rfl | rfl <;> rfl
  · rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
    · -- t = 2k even, k >= 1
      rw [ax_at t 0 (2 * k) (by omega), ao_even, ax_at (t + 1) 0 (2 * k + 1) (by omega), ao_odd']
      simp only [par_odd (t + 1) (by omega)]
      rw [show od (t + 2) (k + 1) = false by
          rw [show t + 2 = 2 * (k + 1) by omega]; exact od_central (k + 1) (by omega),
        Bool.and_false]
      cases axP t 1 <;> rcases hR with rfl | rfl <;> rfl
    · -- t = 2k + 1 odd
      rw [ax_at t 0 (2 * k + 1) (by omega), ao_odd]
      simp only [par_odd t (by omega)]
      rw [show od (t + 1) (k + 1) = false by
          rw [show t + 1 = 2 * (k + 1) by omega]; exact od_central (k + 1) (by omega),
        ax_at t 1 (2 * k) (by omega), ao_even, ax_at (t + 1) 0 (2 * (k + 1)) (by omega), ao_even,
        Bool.and_false]
      rcases hR with rfl | rfl <;> rfl

/-! ### The plane -/

/-- The pattern: axis cells by `axP`, the others by `offP`, of the distance |x| + |y|. -/
def P (t : ℕ) (x y : ℤ) : Bool :=
  if x = 0 ∨ y = 0 then axP t (x.natAbs + y.natAbs) else offP t (x.natAbs + y.natAbs)

theorem P_ax (t : ℕ) (x y : ℤ) (h : x = 0 ∨ y = 0) : P t x y = axP t (x.natAbs + y.natAbs) :=
  if_pos h

theorem P_off (t : ℕ) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    P t x y = offP t (x.natAbs + y.natAbs) :=
  if_neg (by tauto)

theorem state_pattern (R : ℕ) (hR : R = 798 ∨ R = 862) (t : ℕ) :
    ∀ x y, state R t x y = P t x y := by
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
    show Nat.testBit R _ = _
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
          show x.natAbs + (y + 1).natAbs = 1 by omega, ← step11 R hR t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO2 R hR t _ (by omega)]
        congr 1; ring
    -- x < 0, y = 0
    · rw [P_ax t x y (by omega), P_ax t (x - 1) y (by omega), P_ax t (x + 1) y (by omega),
        P_off t x (y - 1) (by omega) (by omega), P_off t x (y + 1) (by omega) (by omega),
        P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← stepA R hR t _ (by omega)]
      congr 1; ring
    -- x < 0, y > 0
    · rcases (by omega : (x = -1 ∨ x ≤ -2)) with ex | ex <;>
        rcases (by omega : (y = 1 ∨ 2 ≤ y)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 3 by omega,
          show (x + 1).natAbs + y.natAbs = 1 by omega, show x.natAbs + (y - 1).natAbs = 1 by omega,
          show x.natAbs + (y + 1).natAbs = 3 by omega, ← step11 R hR t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_ax t (x + 1) y (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO2 R hR t _ (by omega)]
        congr 1; ring
    -- x = 0, y < 0
    · rw [P_ax t x y (by omega), P_off t (x - 1) y (by omega) (by omega),
        P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
        P_ax t x (y + 1) (by omega), P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← stepA R hR t _ (by omega)]
      congr 1; ring
    -- origin
    · rw [P_ax t x y (by omega), P_ax t (x - 1) y (by omega), P_ax t (x + 1) y (by omega),
        P_ax t x (y - 1) (by omega), P_ax t x (y + 1) (by omega), P_ax (t + 1) x y (by omega),
        show x.natAbs + y.natAbs = 0 by omega, show (x - 1).natAbs + y.natAbs = 1 by omega,
        show (x + 1).natAbs + y.natAbs = 1 by omega, show x.natAbs + (y - 1).natAbs = 1 by omega,
        show x.natAbs + (y + 1).natAbs = 1 by omega, ← step0 R hR t]
    -- x = 0, y > 0
    · rw [P_ax t x y (by omega), P_off t (x - 1) y (by omega) (by omega),
        P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
        P_ax t x (y + 1) (by omega), P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← stepA R hR t _ (by omega)]
      congr 1; ring
    -- x > 0, y < 0
    · rcases (by omega : (x = 1 ∨ 2 ≤ x)) with ex | ex <;>
        rcases (by omega : (y = -1 ∨ y ≤ -2)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 1 by omega,
          show (x + 1).natAbs + y.natAbs = 3 by omega, show x.natAbs + (y - 1).natAbs = 3 by omega,
          show x.natAbs + (y + 1).natAbs = 1 by omega, ← step11 R hR t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_ax t x (y + 1) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          ← stepO2 R hR t _ (by omega)]
        congr 1; ring
    -- x > 0, y = 0
    · rw [P_ax t x y (by omega), P_ax t (x - 1) y (by omega), P_ax t (x + 1) y (by omega),
        P_off t x (y - 1) (by omega) (by omega), P_off t x (y + 1) (by omega) (by omega),
        P_ax (t + 1) x y (by omega),
        show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← stepA R hR t _ (by omega)]
    -- x > 0, y > 0
    · rcases (by omega : (x = 1 ∨ 2 ≤ x)) with ex | ex <;>
        rcases (by omega : (y = 1 ∨ 2 ≤ y)) with ey | ey
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show x.natAbs + y.natAbs = 2 by omega, show (x - 1).natAbs + y.natAbs = 1 by omega,
          show (x + 1).natAbs + y.natAbs = 3 by omega, show x.natAbs + (y - 1).natAbs = 1 by omega,
          show x.natAbs + (y + 1).natAbs = 3 by omega, ← step11 R hR t]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_ax t (x - 1) y (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_ax t x (y - 1) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO1 R hR t _ (by omega)]
        congr 1; ring
      · rw [P_off t x y (by omega) (by omega), P_off t (x - 1) y (by omega) (by omega),
          P_off t (x + 1) y (by omega) (by omega), P_off t x (y - 1) (by omega) (by omega),
          P_off t x (y + 1) (by omega) (by omega), P_off (t + 1) x y (by omega) (by omega),
          show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
          show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
          show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
          show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
          ← stepO2 R hR t _ (by omega)]
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

theorem sum_c (n : ℕ) : ∑ d ∈ Finset.range (n + 1), c d = 2 * n ^ 2 + 2 * n + 1 := by
  induction n with
  | zero => simp [c]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [c, if_neg (show n + 1 ≠ 0 by omega)]
    ring

/-- The pattern in terms of |x| and |y|. -/
def Pn (t i j : ℕ) : Bool := if i = 0 ∨ j = 0 then axP t (i + j) else offP t (i + j)

theorem P_eq (t : ℕ) (x y : ℤ) : P t x y = Pn t x.natAbs y.natAbs := by
  unfold P Pn
  by_cases h : x = 0 ∨ y = 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem count_eq (R : ℕ) (hR : R = 798 ∨ R = 862) (t : ℕ) : count R t =
    ∑ i ∈ Finset.range (t + 1), ∑ j ∈ Finset.range (t + 1),
      w i * w j * (if Pn t i j then 1 else 0) := by
  unfold count
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ x ∈ Finset.Icc (-(t : ℤ)) t,
      (∑ y ∈ Finset.Icc (-(t : ℤ)) t, if state R t x y = true then 1 else 0) =
        ∑ j ∈ Finset.range (t + 1), w j * (if Pn t x.natAbs j then 1 else 0) := by
    intro x _
    simp only [state_pattern R hR, P_eq]
    exact sum_Icc_natAbs t (fun j => if Pn t x.natAbs j then 1 else 0)
  rw [Finset.sum_congr rfl inner,
    sum_Icc_natAbs t (fun i => ∑ j ∈ Finset.range (t + 1), w j * (if Pn t i j then 1 else 0))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- At t = 2^n - 1 the off-axis OFF cells inside are those at e = 1. -/
theorem oo_top (n e : ℕ) (hn : 2 ≤ n) (he : e ≤ 2 ^ n - 1) :
    oo (2 ^ n - 1) e = decide (e = 1) := by
  have hp : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rw [oo_even, decide_eq_false (by omega)]
  · rw [oo_odd, show 2 ^ n - 1 + 2 = 2 ^ n + 1 by omega, od_succ_succ,
      od_pow n (k + 1) (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [od_zero]; rfl
    · rw [od_pow n k hk (by omega), decide_eq_false (by omega)]; rfl

theorem ao_top (n e : ℕ) (hn : 2 ≤ n) (he : e ≤ 2 ^ n - 1) : ao (2 ^ n - 1) e = false := by
  have hp : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hev : 2 ^ n % 2 = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; omega
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · exact ao_even _ k
  · rw [ao_odd, show 2 ^ n - 1 + 1 = 2 ^ n by omega, od_pow n (k + 1) (by omega) (by omega)]
    simp only [par_odd (2 ^ n - 1) (by omega), Bool.and_false]

theorem point_top (n i j : ℕ) (hn : 2 ≤ n) :
    (if Pn (2 ^ n - 1) i j then 1 else 0) +
      (if 1 ≤ i ∧ 1 ≤ j ∧ i + j = 2 ^ n - 1 - 1 then 1 else 0) =
    (if i + j ≤ 2 ^ n - 1 then 1 else 0) := by
  have hp : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  unfold Pn
  by_cases hd : i + j ≤ 2 ^ n - 1
  · by_cases h0 : i = 0 ∨ j = 0
    · rw [if_pos h0, ax_at (2 ^ n - 1) (i + j) (2 ^ n - 1 - (i + j)) (by omega),
        ao_top n _ hn (by omega),
        if_neg (show ¬(1 ≤ i ∧ 1 ≤ j ∧ i + j = 2 ^ n - 1 - 1) by omega), if_pos hd]
      rfl
    · rw [if_neg h0, off_at (2 ^ n - 1) (i + j) (2 ^ n - 1 - (i + j)) (by omega),
        oo_top n _ hn (by omega), if_pos hd]
      by_cases h1 : 2 ^ n - 1 - (i + j) = 1
      · rw [decide_eq_true h1,
          if_pos (show 1 ≤ i ∧ 1 ≤ j ∧ i + j = 2 ^ n - 1 - 1 by omega)]; rfl
      · rw [decide_eq_false h1,
          if_neg (show ¬(1 ≤ i ∧ 1 ≤ j ∧ i + j = 2 ^ n - 1 - 1) by omega)]; rfl
  · by_cases h0 : i = 0 ∨ j = 0
    · rw [if_pos h0, ax_out (by omega : 2 ^ n - 1 < i + j),
        if_neg (show ¬(1 ≤ i ∧ 1 ≤ j ∧ i + j = 2 ^ n - 1 - 1) by omega), if_neg hd]; rfl
    · rw [if_neg h0, off_out (by omega : 2 ^ n - 1 < i + j),
        if_neg (show ¬(1 ≤ i ∧ 1 ≤ j ∧ i + j = 2 ^ n - 1 - 1) by omega), if_neg hd]; rfl

theorem sum_ring (T : ℕ) (hT : 2 ≤ T) :
    ∑ i ∈ Finset.range (T + 1), ∑ j ∈ Finset.range (T + 1),
      w i * w j * (if 1 ≤ i ∧ 1 ≤ j ∧ i + j = T - 1 then 1 else 0) = 4 * (T - 2) := by
  have inner : ∀ i ∈ Finset.range (T + 1), ∑ j ∈ Finset.range (T + 1),
      w i * w j * (if 1 ≤ i ∧ 1 ≤ j ∧ i + j = T - 1 then 1 else 0) =
        if 1 ≤ i ∧ i ≤ T - 2 then 4 else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases hi' : 1 ≤ i ∧ i ≤ T - 2
    · rw [if_pos hi', Finset.sum_eq_single (T - 1 - i)]
      · rw [if_pos (by omega)]
        simp only [w, if_neg (show i ≠ 0 by omega), if_neg (show T - 1 - i ≠ 0 by omega)]
      · intro j _ hj
        rw [if_neg (by omega), mul_zero]
      · intro hj
        simp only [Finset.mem_range] at hj
        omega
    · rw [if_neg hi']
      exact Finset.sum_eq_zero (fun j _ => by rw [if_neg (by omega), mul_zero])
  rw [Finset.sum_congr rfl inner, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  have hf : (Finset.range (T + 1)).filter (fun i => 1 ≤ i ∧ i ≤ T - 2) = Finset.Icc 1 (T - 2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hf, Nat.card_Icc]
  omega

/-- At t = 2^n - 1 (n >= 2) the square has 2t^2 - 2t + 9 ON cells. -/
theorem count_top (n : ℕ) (hn : 2 ≤ n) :
    count 798 (2 ^ n - 1) + 4 * (2 ^ n - 1 - 2) = 2 * (2 ^ n - 1) ^ 2 + 2 * (2 ^ n - 1) + 1 := by
  have hp : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [count_eq 798 (Or.inl rfl), ← sum_ring (2 ^ n - 1) (by omega), ← sum_c,
    ← Finset.sum_add_distrib]
  have hs := shell (2 ^ n - 1) (fun _ => 1)
  simp only [mul_one] at hs
  rw [← hs]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← mul_add, point_top n i j hn]

theorem count_862 (t : ℕ) : count 862 t = count 798 t := by
  unfold count
  simp only [state_pattern 862 (Or.inr rfl), state_pattern 798 (Or.inl rfl)]

/-- Blomberg's closed form, for n > 1. -/
theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℤ) = 2 * 4 ^ n - 6 * 2 ^ n + 13 := by
  have hp : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 := count_top n hn
  have hT : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_pow]; push_cast; ring
  have hT2 : ((2 ^ n - 1 - 2 : ℕ) : ℤ) = 2 ^ n - 3 := by
    rw [Nat.cast_sub (by omega), hT]; ring
  have h1z : ((count 798 (2 ^ n - 1) : ℕ) : ℤ) + 4 * ((2 ^ n - 1 - 2 : ℕ) : ℤ) =
      2 * ((2 ^ n - 1 : ℕ) : ℤ) ^ 2 + 2 * ((2 ^ n - 1 : ℕ) : ℤ) + 1 := by exact_mod_cast h1
  rw [hT2, hT] at h1z
  have e4 : ((2 : ℤ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold a
  rw [← e4]
  linear_combination h1z

theorem a_zero : a 0 = 1 := by
  show count 798 0 = 1
  rw [count_eq 798 (Or.inl rfl)]
  decide

theorem a_one : a 1 = 5 := by
  show count 798 1 = 5
  rw [count_eq 798 (Or.inl rfl)]
  decide

theorem val (n N : ℕ) (hn : 1 < n) (hN : (N : ℤ) = 2 * 4 ^ n - 6 * 2 ^ n + 13) : a n = N := by
  have h := (closed n hn).trans hN.symm
  exact_mod_cast h

/-- Controls: the entry's terms a(0..11). -/
theorem controls : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 21 ∧ a 3 = 93 ∧ a 4 = 429 ∧ a 5 = 1869 ∧
    a 6 = 7821 ∧ a 7 = 32013 ∧ a 8 = 129549 ∧ a 9 = 521229 ∧ a 10 = 2091021 ∧
    a 11 = 8376333 :=
  ⟨a_zero, a_one, val 2 21 (by norm_num) (by norm_num), val 3 93 (by norm_num) (by norm_num),
    val 4 429 (by norm_num) (by norm_num), val 5 1869 (by norm_num) (by norm_num),
    val 6 7821 (by norm_num) (by norm_num), val 7 32013 (by norm_num) (by norm_num),
    val 8 129549 (by norm_num) (by norm_num), val 9 521229 (by norm_num) (by norm_num),
    val 10 2091021 (by norm_num) (by norm_num), val 11 8376333 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, closed (m + 5) (by omega), closed (m + 4) (by omega),
    closed (m + 3) (by omega), closed (m + 2) (by omega)]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
    1 - 2 * X + 8 * X ^ 3 + 32 * X ^ 4 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have c14 : (C (14 : ℤ) : PowerSeries ℤ) = 14 := map_ofNat C 14
  have c32 : (C (32 : ℤ) : PowerSeries ℤ) = 32 := map_ofNat C 32
  have hD : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) - C 8 * (A * X ^ 3) := by
    rw [c7, c8, c14]; ring
  have hN : (1 - 2 * X + 8 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℤ) =
      1 - X ^ 1 * C 2 + X ^ 3 * C 8 + X ^ 4 * C 32 := by
    rw [c2, c8, c32]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := controls
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, if_false]
    linear_combination r

/-- Blomberg's two conjectures and Barker's two. -/
theorem conjecture :
    (∀ n : ℕ, count 862 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 2 * 4 ^ n - 6 * 2 ^ n + 13) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 8 * X ^ 3 + 32 * X ^ 4 :=
  ⟨fun n => count_862 _, closed, recurrence, gf⟩

end OMA.S_oeis_a273570

theorem OMA.solution : type_of% @OMA.S_oeis_a273570.main :=
  OMA.S_oeis_a273570.conjecture
