import FormalConjectures.Other.Rule30

-- Reduction Rule30.centerColumn_not_eventually_periodic.R2 of Rule 30 Prize, Problem 1 (non-periodicity).
-- Credit: @Hee-San
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
A one-sided reduction: the right half of the pattern is dropped.
When a center cell is black, the cell on its left equals the negation of the next
center cell. Past the threshold the left half is an autonomous one-sided system,
forced by the repeating center word and started from a finite word. H1 and H2 say that
no finitely supported left half can obey this black-time law forever, for repeating
words with two consecutive black cells (H1) and with isolated black cells (H2).
The all-white tail is excluded directly (lemmas tick .. noConstant are taken from
reduction R1 of this problem, by @desenyon).
In H1 and H2, w is the forcing word and X t j is the cell at position -(j+1) at time t.
-/
open Rule30
namespace OMA.R_Rule30_centerColumn_not_eventually_periodic_R2

private theorem tick (t : ℕ) (i : ℤ) :
    state (t+1) i = xor (state t (i-1)) (state t i || state t (i+1)) := rfl

private theorem outsideLeft (t : ℕ) (i : ℤ) (h : i < -(t : ℤ)) : state t i = false := by
  induction t generalizing i with
  | zero => simp [show i ≠ 0 by omega]
  | succ t ih =>
    rw [tick, ih (i-1) (by omega), ih i (by omega), ih (i+1) (by omega)]
    rfl

private theorem leftEdge (t : ℕ) : state t (-(t : ℤ)) = true := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [tick, outsideLeft t _ (by omega), outsideLeft t _ (by omega)]
    rw [show -(↑(t+1) : ℤ) + 1 = -(t : ℤ) by omega, ih]
    rfl

private theorem outsideRight (t : ℕ) (i : ℤ) (h : (t : ℤ) < i) : state t i = false := by
  induction t generalizing i with
  | zero => simp [show i ≠ 0 by omega]
  | succ t ih =>
    rw [tick, ih (i-1) (by omega), ih i (by omega), ih (i+1) (by omega)]
    rfl

private theorem rightEdge (t : ℕ) : state t (t : ℤ) = true := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [tick, outsideRight t (↑(t+1)) (by omega), outsideRight t (↑(t+1)+1) (by omega)]
    rw [show (↑(t+1) : ℤ) - 1 = (t : ℤ) by omega, ih]
    rfl

private theorem sideways (t : ℕ) (i : ℤ) :
    state t (i-1) = xor (state (t+1) i) (state t i || state t (i+1)) := by
  rw [tick]
  generalize state t (i-1) = a
  generalize (state t i || state t (i+1)) = b
  cases a <;> cases b <;> rfl

/-- A temporal window on two adjacent columns determines the left tip of its triangle. -/
private theorem twoColumnTip (d a b : ℕ) (i : ℤ)
    (h : ∀ j ≤ d, state (a+j) i = state (b+j) i ∧
        state (a+j) (i+1) = state (b+j) (i+1)) :
    state a (i-(d : ℤ)) = state b (i-(d : ℤ)) := by
  induction d generalizing i with
  | zero => simpa using (h 0 (by omega)).1
  | succ d ih =>
    rw [show i - (↑(d+1) : ℤ) = (i-1) - (d : ℤ) by omega]
    apply ih (i-1)
    intro j hj
    obtain ⟨h0,h1⟩ := h j (by omega)
    have hn := (h (j+1) (by omega)).1
    constructor
    · rw [sideways (a+j) i, sideways (b+j) i, h0, h1]
      simpa [Nat.add_assoc] using congrArg (fun x => xor x (state (b+j) i || state (b+j) (i+1))) hn
    · simpa using h0

/-- The observation at the right is needed only when the center is white.
The edge of row b witnesses distinct initial left tips. -/
private theorem maskedDefect (a b : ℕ) (hab : a < b)
    (hc : ∀ j ≤ b, centerColumn (a+j) = centerColumn (b+j)) :
    ∃ j < b, centerColumn (a+j) = false ∧ state (a+j) 1 ≠ state (b+j) 1 := by
  by_contra! hg
  have eqL (j : ℕ) (hj : j < b) : state (a+j) (-1) = state (b+j) (-1) := by
    have hn := hc (j+1) (by omega)
    have hh := hc j (by omega)
    change state (a+(j+1)) 0 = state (b+(j+1)) 0 at hn
    change state (a+j) 0 = state (b+j) 0 at hh
    rw [← show (0:ℤ)-1 = -1 from rfl, sideways (a+j) 0, sideways (b+j) 0]
    simp only [zero_add, Nat.add_assoc, hn]
    cases he : state (a+j) 0 with
    | false =>
      have e := hg j hj (show centerColumn (a+j) = false from he)
      simp [←hh, he, e]
    | true => simp [←hh, he]
  have key := twoColumnTip (b-1) a b (-1) (by
    intro j hj
    exact ⟨eqL j (by omega), hc j (by omega)⟩)
  rw [show (-1 : ℤ) - ↑(b-1) = -(b:ℤ) by omega,
    outsideLeft a _ (by omega), leftEdge] at key
  contradiction

/-- One step of erosion of a white interval attached to a white wall. -/
private theorem whiteStrip (t n : ℕ) (wall : state t 0 = false) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n+1 → state (t+1) i = false) ↔
    (∀ i : ℕ, 1 ≤ i → i ≤ n+2 → state t i = false) := by
  constructor
  · intro h
    have grow (j : ℕ) (hj : j ≤ n+1) : state t j = false ∧ state t (↑j+1) = false := by
      induction j with
      | zero =>
        have e := h 1 (by omega) (by omega)
        rw [tick] at e
        simp [wall] at e
        exact ⟨wall, by simpa using e.1⟩
      | succ j ih =>
        have prev := ih (by omega)
        have e := h (j+1) (by omega) hj
        rw [tick] at e
        simp [prev.1, prev.2] at e
        exact ⟨by simpa using prev.2, by simpa using e⟩
    intro i hi hn
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simpa using (grow j (by omega)).2
  · intro h i hi hn
    rw [tick]
    have hl : state t (↑i-1) = false := by
      by_cases hi1 : i = 1
      · subst i; simpa using wall
      · rw [show (↑i : ℤ)-1 = ↑(i-1) by omega]
        exact h _ (by omega) (by omega)
    rw [hl, h i hi (by omega), show (↑i : ℤ)+1 = ↑(i+1) from rfl, h (i+1) (by omega) (by omega)]
    rfl

/-- The gated neighbor remains white exactly until the nearest black pixel
on the right arrives at the wall. -/
private theorem whiteArrival (a k : ℕ) (h : ∀ j < k, centerColumn (a+j) = false) :
    state (a+k) 1 = false ↔ ∀ i : ℕ, 1 ≤ i → i ≤ k+1 → state a i = false := by
  have aux (d w t : ℕ) (hc : ∀ j < d, centerColumn (t+j) = false) :
      (∀ i : ℕ, 1 ≤ i → i ≤ w+1 → state (t+d) i = false) ↔
      (∀ i : ℕ, 1 ≤ i → i ≤ w+d+1 → state t i = false) := by
    induction d generalizing t w with
    | zero => simp
    | succ d ih =>
      have wall := hc 0 (by omega)
      have hh (j : ℕ) (hj : j < d) : centerColumn (t+1+j) = false := by
        rw [show t+1+j = t+(j+1) by omega]
        exact hc _ (by omega)
      rw [show t+(d+1) = t+1+d by omega, ih w (t+1) hh,
        whiteStrip t (w+d) (by simpa only [centerColumn, Nat.add_zero] using wall)]
      simp only [Nat.add_assoc]
  have e := aux k 0 a h
  simp only [Nat.zero_add] at e
  constructor
  · intro hw
    apply e.mp
    intro i hl hu
    have hi : i = 1 := by omega
    simpa only [hi, Nat.cast_one] using hw
  · intro hw
    exact (e.mpr hw) 1 (by omega) (by omega)

/-- No constant tail. For a white wall, the advancing right edge supplies
a black neighbor in finite time, and it stays black thereafter. -/
private theorem noConstant (N : ℕ) (v : Bool) (hc : ∀ t ≥ N, centerColumn t = v) : False := by
  cases v with
  | true =>
    obtain ⟨j, _, hj, _⟩ := maskedDefect N (N+1) (by omega)
      (fun j _ => (hc _ (by omega)).trans (hc _ (by omega)).symm)
    rw [hc _ (by omega)] at hj
    contradiction
  | false =>
    let a := N+1
    have hr (s : ℕ) (hs : 2*a ≤ s) : state s 1 = true := by
      by_contra! h
      have hh : state (a+(s-a)) 1 = false := by
        rw [show a+(s-a) = s by omega]
        cases e : state s 1 <;> simp_all
      have hw (j : ℕ) (_ : j < s-a) : centerColumn (a+j) = false := hc _ (by dsimp [a]; omega)
      have bad := (whiteArrival a (s-a) hw).mp hh a (by dsimp [a]; omega) (by omega)
      rw [rightEdge] at bad
      contradiction
    obtain ⟨j, _, _, hj⟩ := maskedDefect (2*a) (2*a+1) (by omega)
      (fun j _ => (hc _ (by dsimp [a]; omega)).trans (hc _ (by dsimp [a]; omega)).symm)
    exact hj ((hr _ (by omega)).trans (hr _ (by omega)).symm)

/-- Repeating words containing two consecutive black cells: a finitely supported
forced left half breaks the black-time law. -/
def H1 : Prop := ∀ (w : ℕ → Bool) (X : ℕ → ℕ → Bool) (p : ℕ), 0 < p →
  (∀ t, w (t+p) = w t) → (∃ t, w t = true ∧ w (t+1) = true) →
  (∃ K, ∀ j, K ≤ j → X 0 j = false) →
  (∀ t, X (t+1) 0 = xor (X t 1) (X t 0 || w t)) →
  (∀ t j, X (t+1) (j+1) = xor (X t (j+2)) (X t (j+1) || X t j)) →
  ∃ t, w t = true ∧ X t 0 = w (t+1)

/-- Repeating words whose black cells are isolated (and which have one): a finitely
supported forced left half breaks the black-time law. -/
def H2 : Prop := ∀ (w : ℕ → Bool) (X : ℕ → ℕ → Bool) (p : ℕ), 0 < p →
  (∀ t, w (t+p) = w t) → (∃ t, w t = true) → (∀ t, w t = true → w (t+1) = false) →
  (∃ K, ∀ j, K ≤ j → X 0 j = false) →
  (∀ t, X (t+1) 0 = xor (X t 1) (X t 0 || w t)) →
  (∀ t j, X (t+1) (j+1) = xor (X t (j+2)) (X t (j+1) || X t j)) →
  ∃ t, w t = true ∧ X t 0 = w (t+1)

theorem main : H1 → H2 → type_of% @Rule30.centerColumn_not_eventually_periodic := by
  intro h1 h2
  rintro ⟨p, hp, N, hper⟩
  have per : ∀ t, centerColumn (N+(t+p)) = centerColumn (N+t) := fun t => by
    rw [← Nat.add_assoc]; exact hper _ (by omega)
  have fin : ∃ K : ℕ, ∀ j : ℕ, K ≤ j → state (N+0) (-((j:ℤ)+1)) = false :=
    ⟨N, fun j hj => outsideLeft _ _ (by push_cast; omega)⟩
  have r0 : ∀ t, state (N+(t+1)) (-(((0:ℕ):ℤ)+1)) =
      xor (state (N+t) (-(((1:ℕ):ℤ)+1))) (state (N+t) (-(((0:ℕ):ℤ)+1)) || centerColumn (N+t)) := by
    intro t
    rw [← Nat.add_assoc, tick]
    simp only [centerColumn]
    norm_num
  have r1 : ∀ t j, state (N+(t+1)) (-(((j+1:ℕ):ℤ)+1)) =
      xor (state (N+t) (-(((j+2:ℕ):ℤ)+1)))
        (state (N+t) (-(((j+1:ℕ):ℤ)+1)) || state (N+t) (-((j:ℤ)+1))) := by
    intro t j
    rw [← Nat.add_assoc, tick]
    congr 2
  have law : ∀ t, centerColumn (N+t) = true →
      state (N+t) (-(((0:ℕ):ℤ)+1)) = centerColumn (N+(t+1)) → False := by
    intro t hb he
    have e : centerColumn (N+(t+1)) =
        xor (state (N+t) (-1)) (state (N+t) 0 || state (N+t) 1) := by
      rw [← Nat.add_assoc]; exact tick _ _
    have hb' : state (N+t) 0 = true := hb
    rw [hb'] at e
    rw [e] at he
    norm_num at he
  by_cases c1 : ∃ t, centerColumn (N+t) = true ∧ centerColumn (N+(t+1)) = true
  · obtain ⟨t, hb, he⟩ := h1 (fun t => centerColumn (N+t))
      (fun t j => state (N+t) (-((j:ℤ)+1))) p hp per c1 fin r0 r1
    exact law t hb he
  · by_cases c2 : ∃ t, centerColumn (N+t) = true
    · obtain ⟨t, hb, he⟩ := h2 (fun t => centerColumn (N+t))
        (fun t j => state (N+t) (-((j:ℤ)+1))) p hp per c2
        (fun t ht => by
          cases h : centerColumn (N+(t+1))
          · rfl
          · exact absurd ⟨t, ht, h⟩ c1) fin r0 r1
      exact law t hb he
    · refine noConstant N false (fun t ht => ?_)
      cases h : centerColumn t
      · rfl
      · exact absurd ⟨t-N, by rw [show N+(t-N) = t by omega]; exact h⟩ c2

end OMA.R_Rule30_centerColumn_not_eventually_periodic_R2
