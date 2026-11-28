import OMAStatements.S_oeis_a269696

-- Problem: A269696: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 6, based on the 5-celled von Neumann neighborhood.
-- Upstream: statements/oeis-a269696.lean (declaration OMA.S_oeis_a269696.main)
-- Credit: @rgoldman73-dev (the owner of the agent is credited as the solver)
--
-- Proof of Colin Barker's conjectures a(n) = 5*4^(n-1), a(n) = 4*a(n-1), g.f. (1+x)/(1-4x).
-- Rule 6 turns a cell ON exactly when one cell of its closed von Neumann neighbourhood is ON.
-- Writing T = 2^n (n >= 1) and f t for the configuration after t steps:
--   * f T consists of the four cells at L1-distance T on the axes (theorem Qf_pow),
--   * for s < T, f (T + s) is the disjoint union of four translates of f s (theorem K):
--     the copies sit in L1-balls of radius s around centres 2T apart, so they do not interact
--     while s + 1 < T (theorem stp_quad), and one more step collapses them again (theorem collapse).
-- Hence the count at time 2T - 1 is four times the count at time T - 1 (theorem count_pow).

namespace A269696H

open OMA.S_oeis_a269696

/-- Number of ON cells in the closed von Neumann neighbourhood. -/
def nb (g : ℤ → ℤ → Bool) (i j : ℤ) : ℕ :=
  (g i j).toNat + (g (i + 1) j).toNat + (g (i + -1) j).toNat + (g i (j + 1)).toNat +
    (g i (j + -1)).toNat

/-- One step of Rule 6: ON exactly when one cell of the closed neighbourhood is ON. -/
def stp (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j => decide (nb g i j = 1)

/-- Translate of a configuration. -/
def sh (g : ℤ → ℤ → Bool) (a b : ℤ) : ℤ → ℤ → Bool := fun x y => g (x + a) (y + b)

/-- Superposition of four translates. -/
def quad (g : ℤ → ℤ → Bool) (T : ℤ) : ℤ → ℤ → Bool := fun x y =>
  sh g (-T) 0 x y || sh g T 0 x y || sh g 0 (-T) x y || sh g 0 T x y

/-- The closed L1 ball of radius `r`. -/
def inB (r x y : ℤ) : Prop := x + y ≤ r ∧ x - y ≤ r ∧ -x + y ≤ r ∧ -x - y ≤ r

theorem rule6 : ∀ a b c d e : Bool,
    Nat.testBit 6 (a.toNat + 2 * (b.toNat + c.toNat + d.toNat + e.toNat)) =
      decide (a.toNat + b.toNat + c.toNat + d.toNat + e.toNat = 1) := by
  decide

theorem cell_succ (t : ℕ) : cell 6 (t + 1) = stp (cell 6 t) := by
  funext i j
  simp only [cell, stp, nb, sub_eq_add_neg]
  exact rule6 _ _ _ _ _

theorem nb_ne_zero {g : ℤ → ℤ → Bool} {i j : ℤ} (h : nb g i j ≠ 0) :
    g i j = true ∨ g (i + 1) j = true ∨ g (i + -1) j = true ∨ g i (j + 1) = true ∨
      g i (j + -1) = true := by
  by_contra hc
  simp only [not_or, Bool.not_eq_true] at hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  apply h
  simp [nb, h1, h2, h3, h4, h5]

theorem near {g : ℤ → ℤ → Bool} {r : ℤ} (hg : ∀ x y, g x y = true → inB r x y) {i j : ℤ}
    (h : nb g i j ≠ 0) : inB (r + 1) i j := by
  rcases nb_ne_zero h with h | h | h | h | h <;> have h' := hg _ _ h <;>
    simp only [inB] at h' ⊢ <;> omega

theorem nb_sh (g : ℤ → ℤ → Bool) (a b i j : ℤ) : nb (sh g a b) i j = nb g (i + a) (j + b) := by
  simp only [nb, sh]
  have e1 : i + 1 + a = i + a + 1 := by ring
  have e2 : i + -1 + a = i + a + -1 := by ring
  have e3 : j + 1 + b = j + b + 1 := by ring
  have e4 : j + -1 + b = j + b + -1 := by ring
  rw [e1, e2, e3, e4]

theorem or4_toNat (a b c d : Bool) (hab : ¬(a = true ∧ b = true)) (hac : ¬(a = true ∧ c = true))
    (had : ¬(a = true ∧ d = true)) (hbc : ¬(b = true ∧ c = true)) (hbd : ¬(b = true ∧ d = true))
    (hcd : ¬(c = true ∧ d = true)) :
    (a || b || c || d).toNat = a.toNat + b.toNat + c.toNat + d.toNat := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem quad_toNat (g : ℤ → ℤ → Bool) (T s : ℤ) (hg : ∀ x y, g x y = true → inB s x y)
    (hsT : s < T) (x y : ℤ) :
    (quad g T x y).toNat = (sh g (-T) 0 x y).toNat + (sh g T 0 x y).toNat +
      (sh g 0 (-T) x y).toNat + (sh g 0 T x y).toNat := by
  unfold quad
  apply or4_toNat <;>
    (rintro ⟨h1, h2⟩
     have h1' := hg _ _ h1
     have h2' := hg _ _ h2
     simp only [inB] at h1' h2'
     omega)

theorem nb_quad (g : ℤ → ℤ → Bool) (T s : ℤ) (hg : ∀ x y, g x y = true → inB s x y)
    (hsT : s < T) (i j : ℤ) :
    nb (quad g T) i j = nb g (i + -T) (j + 0) + nb g (i + T) (j + 0) + nb g (i + 0) (j + -T) +
      nb g (i + 0) (j + T) := by
  rw [← nb_sh, ← nb_sh, ← nb_sh, ← nb_sh]
  simp only [nb, quad_toNat g T s hg hsT]
  ring

theorem stp_quad (g : ℤ → ℤ → Bool) (T s : ℤ) (hg : ∀ x y, g x y = true → inB s x y)
    (hsT : s + 1 < T) (i j : ℤ) : stp (quad g T) i j = quad (stp g) T i j := by
  have hn := nb_quad g T s hg (by omega) i j
  have b1 : nb g (i + -T) (j + 0) ≠ 0 → inB (s + 1) (i + -T) (j + 0) := near hg
  have b2 : nb g (i + T) (j + 0) ≠ 0 → inB (s + 1) (i + T) (j + 0) := near hg
  have b3 : nb g (i + 0) (j + -T) ≠ 0 → inB (s + 1) (i + 0) (j + -T) := near hg
  have b4 : nb g (i + 0) (j + T) ≠ 0 → inB (s + 1) (i + 0) (j + T) := near hg
  simp only [stp, quad, sh, hn]
  generalize nb g (i + -T) (j + 0) = n1 at *
  generalize nb g (i + T) (j + 0) = n2 at *
  generalize nb g (i + 0) (j + -T) = n3 at *
  generalize nb g (i + 0) (j + T) = n4 at *
  simp only [inB] at b1 b2 b3 b4
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem supp : ∀ (t : ℕ) (i j : ℤ), cell 6 t i j = true → inB t i j := by
  intro t
  induction t with
  | zero =>
    intro i j h
    simp only [cell, decide_eq_true_eq] at h
    simp only [inB]
    omega
  | succ t ih =>
    intro i j h
    rw [cell_succ] at h
    simp only [stp, decide_eq_true_eq] at h
    have h2 := near ih (i := i) (j := j) (by omega)
    simp only [inB] at h2 ⊢
    omega

theorem quad_zero (T x y : ℤ) : quad (cell 6 0) T x y = true ↔
    ((x = T ∧ y = 0) ∨ (x = -T ∧ y = 0) ∨ (x = 0 ∧ y = T) ∨ (x = 0 ∧ y = -T)) := by
  simp only [quad, sh, cell, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem K (T : ℕ) (hQ : ∀ i j, cell 6 T i j = quad (cell 6 0) T i j) :
    ∀ s : ℕ, s < T → ∀ i j, cell 6 (T + s) i j = quad (cell 6 s) T i j := by
  intro s
  induction s with
  | zero => intro _ i j; exact hQ i j
  | succ s ih =>
    intro hs i j
    have ih' : cell 6 (T + s) = quad (cell 6 s) T := by
      funext x y
      exact ih (by omega) x y
    rw [← Nat.add_assoc, cell_succ, ih', stp_quad (cell 6 s) T s (supp s) (by omega), cell_succ]

theorem base2 (i j : ℤ) : cell 6 2 i j = quad (cell 6 0) 2 i j := by
  rw [Bool.eq_iff_iff, quad_zero]
  by_cases hB : inB 2 i j
  · simp only [inB] at hB
    obtain ⟨h1, h2, h3, h4⟩ := hB
    have hi1 : -2 ≤ i := by omega
    have hi2 : i ≤ 2 := by omega
    have hj1 : -2 ≤ j := by omega
    have hj2 : j ≤ 2 := by omega
    clear h1 h2 h3 h4
    interval_cases i <;> interval_cases j <;> decide
  · constructor
    · intro h
      exact absurd (supp 2 i j h) hB
    · intro h
      exfalso
      apply hB
      simp only [inB]
      omega

theorem collapse_arith (T i j : ℤ) (hT : 0 < T) (n1 n2 n3 n4 : ℕ)
    (e1 : n1 = 1 ↔ ((i + -T = T ∧ j + 0 = 0) ∨ (i + -T = -T ∧ j + 0 = 0) ∨
      (i + -T = 0 ∧ j + 0 = T) ∨ (i + -T = 0 ∧ j + 0 = -T)))
    (e2 : n2 = 1 ↔ ((i + T = T ∧ j + 0 = 0) ∨ (i + T = -T ∧ j + 0 = 0) ∨
      (i + T = 0 ∧ j + 0 = T) ∨ (i + T = 0 ∧ j + 0 = -T)))
    (e3 : n3 = 1 ↔ ((i + 0 = T ∧ j + -T = 0) ∨ (i + 0 = -T ∧ j + -T = 0) ∨
      (i + 0 = 0 ∧ j + -T = T) ∨ (i + 0 = 0 ∧ j + -T = -T)))
    (e4 : n4 = 1 ↔ ((i + 0 = T ∧ j + T = 0) ∨ (i + 0 = -T ∧ j + T = 0) ∨
      (i + 0 = 0 ∧ j + T = T) ∨ (i + 0 = 0 ∧ j + T = -T)))
    (b1 : n1 = 0 ∨ inB T (i + -T) (j + 0)) (b2 : n2 = 0 ∨ inB T (i + T) (j + 0))
    (b3 : n3 = 0 ∨ inB T (i + 0) (j + -T)) (b4 : n4 = 0 ∨ inB T (i + 0) (j + T)) :
    n1 + n2 + n3 + n4 = 1 ↔
      ((i = 2 * T ∧ j = 0) ∨ (i = -(2 * T) ∧ j = 0) ∨ (i = 0 ∧ j = 2 * T) ∨
        (i = 0 ∧ j = -(2 * T))) := by
  simp only [inB] at b1 b2 b3 b4
  constructor
  · intro hs
    have hc : n1 = 1 ∨ n2 = 1 ∨ n3 = 1 ∨ n4 = 1 := by omega
    rcases hc with h | h | h | h
    · rcases e1.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · have := e2.mpr (Or.inl ⟨by omega, by omega⟩); omega
      · have := e3.mpr (Or.inl ⟨by omega, by omega⟩); omega
      · have := e4.mpr (Or.inl ⟨by omega, by omega⟩); omega
    · rcases e2.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have := e1.mpr (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · have := e3.mpr (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
      · have := e4.mpr (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
    · rcases e3.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have := e1.mpr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))); omega
      · have := e2.mpr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))); omega
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      · have := e4.mpr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))); omega
    · rcases e4.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have := e1.mpr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))); omega
      · have := e2.mpr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))); omega
      · have := e3.mpr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))); omega
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · have := e1.mpr (Or.inl ⟨by omega, by omega⟩); omega
    · have := e2.mpr (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
    · have := e3.mpr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))); omega
    · have := e4.mpr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))); omega

theorem collapse (T : ℕ) (hT : 1 ≤ T) (hQ : ∀ i j, cell 6 T i j = quad (cell 6 0) T i j) :
    ∀ i j, cell 6 (2 * T) i j = quad (cell 6 0) ((2 * T : ℕ) : ℤ) i j := by
  intro i j
  obtain ⟨r, rfl⟩ : ∃ r, T = r + 1 := ⟨T - 1, by omega⟩
  have hK : cell 6 (r + 1 + r) = quad (cell 6 r) ((r + 1 : ℕ) : ℤ) := by
    funext x y
    exact K (r + 1) hQ r (by omega) x y
  have h2 : 2 * (r + 1) = (r + 1 + r) + 1 := by omega
  have hn := nb_quad (cell 6 r) ((r + 1 : ℕ) : ℤ) r (supp r) (by push_cast; omega) i j
  have key : ∀ x y : ℤ, nb (cell 6 r) x y = 1 ↔
      ((x = ((r + 1 : ℕ) : ℤ) ∧ y = 0) ∨ (x = -((r + 1 : ℕ) : ℤ) ∧ y = 0) ∨
        (x = 0 ∧ y = ((r + 1 : ℕ) : ℤ)) ∨ (x = 0 ∧ y = -((r + 1 : ℕ) : ℤ))) := by
    intro x y
    rw [← quad_zero, ← hQ x y, cell_succ]
    simp only [stp, decide_eq_true_eq]
  have nr : ∀ x y : ℤ, nb (cell 6 r) x y = 0 ∨ inB ((r + 1 : ℕ) : ℤ) x y := by
    intro x y
    by_cases h : nb (cell 6 r) x y = 0
    · exact Or.inl h
    · right
      have := near (supp r) h
      simpa using this
  rw [Bool.eq_iff_iff, quad_zero, h2, cell_succ, hK]
  simp only [stp, decide_eq_true_eq, hn]
  have := collapse_arith ((r + 1 : ℕ) : ℤ) i j (by positivity) _ _ _ _
    (key _ _) (key _ _) (key _ _) (key _ _) (nr _ _) (nr _ _) (nr _ _) (nr _ _)
  rw [this]
  push_cast
  constructor <;> (intro h; omega)

theorem Qf_pow (n : ℕ) :
    ∀ i j, cell 6 (2 ^ (n + 1)) i j = quad (cell 6 0) ((2 ^ (n + 1) : ℕ) : ℤ) i j := by
  induction n with
  | zero =>
    intro i j
    simpa using base2 i j
  | succ n ih =>
    intro i j
    have := collapse (2 ^ (n + 1)) Nat.one_le_two_pow ih i j
    rwa [← pow_succ'] at this

theorem ite_toNat (b : Bool) : (if b = true then (1 : ℕ) else 0) = b.toNat := by
  cases b <;> rfl

theorem sum_win (F : ℤ → ℕ) (r A C : ℕ)
    (hF : ∀ x : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x) → F x = 0) :
    ∑ i ∈ Finset.range (A + (2 * r + 1) + C), F ((i : ℤ) - ((A : ℤ) + r)) =
      ∑ i ∈ Finset.range (2 * r + 1), F ((i : ℤ) - r) := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have z1 : ∑ x ∈ Finset.range A, F ((x : ℤ) - ((A : ℤ) + r)) = 0 :=
    Finset.sum_eq_zero (fun x hx => hF _ (Or.inl (by
      have := Finset.mem_range.mp hx
      omega)))
  have z3 : ∑ x ∈ Finset.range C, F (((A + (2 * r + 1) + x : ℕ) : ℤ) - ((A : ℤ) + r)) = 0 :=
    Finset.sum_eq_zero (fun x _ => hF _ (Or.inr (by
      push_cast
      omega)))
  rw [z1, z3, zero_add, add_zero]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  push_cast
  ring

theorem sum_win2 (G : ℤ → ℤ → ℕ) (r A C A' C' : ℕ)
    (hG : ∀ x y : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x ∨ y < -(r : ℤ) ∨ (r : ℤ) < y) → G x y = 0) :
    ∑ i ∈ Finset.range (A + (2 * r + 1) + C), ∑ j ∈ Finset.range (A' + (2 * r + 1) + C'),
        G ((i : ℤ) - ((A : ℤ) + r)) ((j : ℤ) - ((A' : ℤ) + r)) =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        G ((i : ℤ) - r) ((j : ℤ) - r) := by
  refine (sum_win (fun x => ∑ j ∈ Finset.range (A' + (2 * r + 1) + C'),
    G x ((j : ℤ) - ((A' : ℤ) + r))) r A C
    (fun x hx => Finset.sum_eq_zero (fun j _ => hG _ _ (by tauto)))).trans ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact sum_win (fun y => G ((i : ℤ) - r) y) r A' C' (fun y hy => hG _ _ (by tauto))

theorem cnt_quad (g : ℤ → ℤ → Bool) (r : ℕ) (hg : ∀ x y, g x y = true → inB r x y) :
    ∑ i ∈ Finset.range (2 * (r + 1 + r) + 1), ∑ j ∈ Finset.range (2 * (r + 1 + r) + 1),
        (quad g ((r + 1 : ℕ) : ℤ) ((i : ℤ) - ((r + 1 + r : ℕ) : ℤ))
          ((j : ℤ) - ((r + 1 + r : ℕ) : ℤ))).toNat =
      4 * ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        (g ((i : ℤ) - r) ((j : ℤ) - r)).toNat := by
  have hG : ∀ x y : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x ∨ y < -(r : ℤ) ∨ (r : ℤ) < y) →
      (g x y).toNat = 0 := by
    intro x y h
    cases hgx : g x y
    · rfl
    · have := hg x y hgx
      simp only [inB] at this
      omega
  have w1 := sum_win2 (fun x y => (g x y).toNat) r (2 * r + 2) 0 (r + 1) (r + 1) hG
  have w2 := sum_win2 (fun x y => (g x y).toNat) r 0 (2 * r + 2) (r + 1) (r + 1) hG
  have w3 := sum_win2 (fun x y => (g x y).toNat) r (r + 1) (r + 1) (2 * r + 2) 0 hG
  have w4 := sum_win2 (fun x y => (g x y).toNat) r (r + 1) (r + 1) 0 (2 * r + 2) hG
  simp only [quad_toNat g ((r + 1 : ℕ) : ℤ) r hg (by push_cast; omega), Finset.sum_add_distrib]
  have e1 : ∑ i ∈ Finset.range (2 * (r + 1 + r) + 1), ∑ j ∈ Finset.range (2 * (r + 1 + r) + 1),
      (sh g (-((r + 1 : ℕ) : ℤ)) 0 ((i : ℤ) - ((r + 1 + r : ℕ) : ℤ))
        ((j : ℤ) - ((r + 1 + r : ℕ) : ℤ))).toNat =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        (g ((i : ℤ) - r) ((j : ℤ) - r)).toNat := by
    rw [← w1]
    refine Finset.sum_congr (by congr 1; omega) (fun i _ => ?_)
    refine Finset.sum_congr (by congr 1; omega) (fun j _ => ?_)
    simp only [sh]
    congr 2 <;> push_cast <;> ring
  have e2 : ∑ i ∈ Finset.range (2 * (r + 1 + r) + 1), ∑ j ∈ Finset.range (2 * (r + 1 + r) + 1),
      (sh g ((r + 1 : ℕ) : ℤ) 0 ((i : ℤ) - ((r + 1 + r : ℕ) : ℤ))
        ((j : ℤ) - ((r + 1 + r : ℕ) : ℤ))).toNat =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        (g ((i : ℤ) - r) ((j : ℤ) - r)).toNat := by
    rw [← w2]
    refine Finset.sum_congr (by congr 1; omega) (fun i _ => ?_)
    refine Finset.sum_congr (by congr 1; omega) (fun j _ => ?_)
    simp only [sh]
    congr 2 <;> push_cast <;> ring
  have e3 : ∑ i ∈ Finset.range (2 * (r + 1 + r) + 1), ∑ j ∈ Finset.range (2 * (r + 1 + r) + 1),
      (sh g 0 (-((r + 1 : ℕ) : ℤ)) ((i : ℤ) - ((r + 1 + r : ℕ) : ℤ))
        ((j : ℤ) - ((r + 1 + r : ℕ) : ℤ))).toNat =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        (g ((i : ℤ) - r) ((j : ℤ) - r)).toNat := by
    rw [← w3]
    refine Finset.sum_congr (by congr 1; omega) (fun i _ => ?_)
    refine Finset.sum_congr (by congr 1; omega) (fun j _ => ?_)
    simp only [sh]
    congr 2 <;> push_cast <;> ring
  have e4 : ∑ i ∈ Finset.range (2 * (r + 1 + r) + 1), ∑ j ∈ Finset.range (2 * (r + 1 + r) + 1),
      (sh g 0 ((r + 1 : ℕ) : ℤ) ((i : ℤ) - ((r + 1 + r : ℕ) : ℤ))
        ((j : ℤ) - ((r + 1 + r : ℕ) : ℤ))).toNat =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        (g ((i : ℤ) - r) ((j : ℤ) - r)).toNat := by
    rw [← w4]
    refine Finset.sum_congr (by congr 1; omega) (fun i _ => ?_)
    refine Finset.sum_congr (by congr 1; omega) (fun j _ => ?_)
    simp only [sh]
    congr 2 <;> push_cast <;> ring
  rw [e1, e2, e3, e4]
  ring

theorem count_rec (r : ℕ) (hK : cell 6 (r + 1 + r) = quad (cell 6 r) ((r + 1 : ℕ) : ℤ)) :
    onCount 6 (r + 1 + r) = 4 * onCount 6 r := by
  simp only [onCount, ite_toNat, hK]
  exact cnt_quad (cell 6 r) r (supp r)

theorem count_pow (n : ℕ) : onCount 6 (2 ^ (n + 2) - 1) = 4 * onCount 6 (2 ^ (n + 1) - 1) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ (n + 1) = r + 1 :=
    ⟨2 ^ (n + 1) - 1, by have := Nat.one_le_two_pow (n := n + 1); omega⟩
  have hK : cell 6 (r + 1 + r) = quad (cell 6 r) ((r + 1 : ℕ) : ℤ) := by
    funext x y
    have hQ := Qf_pow n
    rw [hr] at hQ
    exact K (r + 1) hQ r (by omega) x y
  have e1 : 2 ^ (n + 2) - 1 = r + 1 + r := by
    rw [pow_succ, hr]
    omega
  have e2 : 2 ^ (n + 1) - 1 = r := by omega
  rw [e1, e2]
  exact count_rec r hK

theorem count_zero : onCount 6 0 = 1 := by decide

theorem count_one : onCount 6 1 = 5 := by decide

theorem a_zero : a 0 = 1 := by
  simp [a, count_zero]

theorem a_one : a 1 = 5 := by
  simp [a, count_one]

theorem a_succ (n : ℕ) : a (n + 2) = 4 * a (n + 1) := by
  simp only [a]
  rw [count_pow]
  push_cast
  ring

theorem a_formula (n : ℕ) : a (n + 1) = 5 * 4 ^ n := by
  induction n with
  | zero => simpa using a_one
  | succ n ih =>
    rw [a_succ, ih]
    ring

end A269696H

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a269696.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [A269696H.a_formula]
    simp
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [A269696H.a_succ]
    simp
  · have key : PowerSeries.mk (fun n => (OMA.S_oeis_a269696.a n : ℚ)) * (1 - 4 * X) =
        PowerSeries.mk (fun n => (OMA.S_oeis_a269696.a n : ℚ)) -
          PowerSeries.C (4 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a269696.a n : ℚ)) * X) := by
      simp only [map_ofNat]
      ring
    rw [key]
    ext n
    rcases n with _ | _ | n
    · simp [A269696H.a_zero]
    · simp [A269696H.a_zero, A269696H.a_one]
      norm_num
    · simp [A269696H.a_succ, PowerSeries.coeff_X, PowerSeries.coeff_one]
