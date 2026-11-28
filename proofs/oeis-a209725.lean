import OMAStatements.S_oeis_a209725

-- Problem: A209725: 1/4 the number of (n+1) x 5 0..2 arrays with every 2x2 subblock having distinct clockwise edge diffs.
-- Credit: @ceejcake
-- Proof: Parametric characterization for all M, W >= 2: valid(M, W) = HStar(M, W) ∪ VStar(M, W)
-- with |HStar(M, W) ∩ VStar(M, W)| = 8.

namespace ClockDiff

open OMA.S_oeis_a209725

-- Local 2x2 predicate and decidable structural lemmas
private def ok2 (a b d c : Fin 3) : Prop := distinctClockwise a b d c

private lemma ok2_transpose : ∀ a b d c : Fin 3, ok2 a b d c → ok2 a d b c := by
  unfold ok2 distinctClockwise; decide

private lemma ok2_xor_row02 : ∀ a b d c : Fin 3, ok2 a b d c →
    (((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) ∧ ¬ ((d = 0 ∧ c = 2) ∨ (d = 2 ∧ c = 0))) ∨
    (¬ ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) ∧ ((d = 0 ∧ c = 2) ∨ (d = 2 ∧ c = 0))) := by
  unfold ok2 distinctClockwise; decide

private lemma ok2_top02 : ∀ a b d c : Fin 3, ok2 a b d c →
    ((a = 0 ∧ b = 2) → (d = 1 ∧ c = 0) ∨ (d = 2 ∧ c = 1)) ∧
    ((a = 2 ∧ b = 0) → (d = 0 ∧ c = 1) ∨ (d = 1 ∧ c = 2)) := by
  unfold ok2 distinctClockwise; decide

private lemma ok2_bot02 : ∀ a b d c : Fin 3, ok2 a b d c →
    ((d = 0 ∧ c = 2) → (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1)) ∧
    ((d = 2 ∧ c = 0) → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) := by
  unfold ok2 distinctClockwise; decide

private lemma ok2_top_non02 : ∀ a b d c : Fin 3, ok2 a b d c →
    ((a = 1 ∧ b = 0) → d = 0 ∧ c = 2) ∧
    ((a = 0 ∧ b = 1) → d = 2 ∧ c = 0) ∧
    ((a = 2 ∧ b = 1) → d = 0 ∧ c = 2) ∧
    ((a = 1 ∧ b = 2) → d = 2 ∧ c = 0) := by
  unfold ok2 distinctClockwise; decide

private lemma ok2_bot_non02 : ∀ a b d c : Fin 3, ok2 a b d c →
    ((d = 1 ∧ c = 0) → a = 0 ∧ b = 2) ∧
    ((d = 0 ∧ c = 1) → a = 2 ∧ b = 0) ∧
    ((d = 2 ∧ c = 1) → a = 0 ∧ b = 2) ∧
    ((d = 1 ∧ c = 2) → a = 2 ∧ b = 0) := by
  unfold ok2 distinctClockwise; decide

private def isPair02 (x y : Fin 3) : Prop := (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0)

-- At a 2x3 switch (one 2x2 has top {0,2}, adjacent 2x2 has bottom {0,2}), the shared middle column is {0,2}!
private lemma ok2_switch_mid (a b e d c f : Fin 3) (h1 : ok2 a b d c) (h2 : ok2 b e c f)
    (hsw : (isPair02 a b ∧ isPair02 c f) ∨ (isPair02 d c ∧ isPair02 b e)) :
    isPair02 b c := by
  unfold isPair02 at hsw ⊢
  rcases hsw with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hc⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hb⟩
  · rcases (ok2_top02 _ _ _ _ h1).1 ⟨rfl, rfl⟩ with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · rcases (ok2_top02 _ _ _ _ h1).2 ⟨rfl, rfl⟩ with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases (ok2_bot02 _ _ _ _ h1).1 ⟨rfl, rfl⟩ with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · rcases hb with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · rcases (ok2_bot02 _ _ _ _ h1).2 ⟨rfl, rfl⟩ with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rcases hb with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
    · exact Or.inr ⟨rfl, rfl⟩

-- A 2x3 switch propagates downward: middle column alternates {0,2} and the next 2x3 is also a switch!
private lemma ok2_switch_down (a b e d c f g h k : Fin 3)
    (h1 : ok2 a b d c) (h2 : ok2 b e c f) (h3 : ok2 d c g h) (h4 : ok2 c f h k)
    (hsw : (isPair02 a b ∧ isPair02 c f) ∨ (isPair02 d c ∧ isPair02 b e)) :
    h = b ∧ ((isPair02 d c ∧ isPair02 h k) ∨ (isPair02 g h ∧ isPair02 c f)) := by
  have hmid : isPair02 b c := ok2_switch_mid a b e d c f h1 h2 hsw
  have hxor3 := ok2_xor_row02 d c g h h3
  have hxor4 := ok2_xor_row02 c f h k h4
  have hxor1 := ok2_xor_row02 a b d c h1
  have hxor2 := ok2_xor_row02 b e c f h2
  have hsw_next : (isPair02 d c ∧ isPair02 h k) ∨ (isPair02 g h ∧ isPair02 c f) := by
    unfold isPair02 at hsw ⊢
    rcases hsw with ⟨hab, hcf⟩ | ⟨hdc, hbe⟩
    · right
      have hndc : ¬ ((d = 0 ∧ c = 2) ∨ (d = 2 ∧ c = 0)) := by
        rcases hxor1 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd hab h
      have hgh : (g = 0 ∧ h = 2) ∨ (g = 2 ∧ h = 0) := by
        rcases hxor3 with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hndc
        · exact h
      exact ⟨hgh, hcf⟩
    · left
      have hncf : ¬ ((c = 0 ∧ f = 2) ∨ (c = 2 ∧ f = 0)) := by
        rcases hxor2 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd hbe h
      have hhk : (h = 0 ∧ k = 2) ∨ (h = 2 ∧ k = 0) := by
        rcases hxor4 with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hncf
        · exact h
      exact ⟨hdc, hhk⟩
  have hmid2 : isPair02 c h := ok2_switch_mid d c f g h k h3 h4 hsw_next
  refine ⟨?_, hsw_next⟩
  rcases hmid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hmid2 with ⟨h1', rfl⟩ | ⟨h1', rfl⟩
  · exact absurd h1' (by decide)
  · rfl
  · rfl
  · exact absurd h1' (by decide)

private lemma mkConst_transpose_exists :
    ∀ p q ch : Fin 2, ∃ p' q' ch' : Fin 2, ∀ im jm : Fin 2,
      (if im.1 = p.1 then (if (jm.1 + q.1) % 2 = 0 then (0 : Fin 3) else 2)
       else if ch = 0 then (if (jm.1 + q.1) % 2 = 0 then 1 else 0)
       else (if (jm.1 + q.1) % 2 = 0 then 2 else 1)) =
      (if jm.1 = p'.1 then (if (im.1 + q'.1) % 2 = 0 then (0 : Fin 3) else 2)
       else if ch' = 0 then (if (im.1 + q'.1) % 2 = 0 then 1 else 0)
       else (if (im.1 + q'.1) % 2 = 0 then 2 else 1)) := by
  decide

section General
open scoped Classical
noncomputable section

def validGrid {M W : ℕ} (A : Fin M → Fin W → Fin 3) : Prop :=
  ∀ (i : Fin M) (hi : i.1 + 1 < M) (j : Fin W) (hj : j.1 + 1 < W),
    ok2 (A i j) (A i ⟨j.1 + 1, hj⟩) (A ⟨i.1 + 1, hi⟩ j) (A ⟨i.1 + 1, hi⟩ ⟨j.1 + 1, hj⟩)

private lemma validGrid_transpose {M W : ℕ} {A : Fin M → Fin W → Fin 3} (hA : validGrid A) :
    validGrid (fun j i => A i j) := by
  intro j hj i hi
  exact ok2_transpose _ _ _ _ (hA i hi j hj)

def alt02 {L : ℕ} (q : Fin 2) (r : Fin L → Fin 3) : Prop :=
  ∀ j : Fin L, r j = if (j.1 + q.1) % 2 = 0 then 0 else 2

def alt10 {L : ℕ} (q : Fin 2) (r : Fin L → Fin 3) : Prop :=
  ∀ j : Fin L, r j = if (j.1 + q.1) % 2 = 0 then 1 else 0

def alt21 {L : ℕ} (q : Fin 2) (r : Fin L → Fin 3) : Prop :=
  ∀ j : Fin L, r j = if (j.1 + q.1) % 2 = 0 then 2 else 1

def hPat {M W : ℕ} (p q : Fin 2) (A : Fin M → Fin W → Fin 3) : Prop :=
  (∀ i : Fin M, i.1 % 2 = p.1 → alt02 q (A i)) ∧
  (∀ i : Fin M, i.1 % 2 ≠ p.1 → alt10 q (A i) ∨ alt21 q (A i))

def isHStar {M W : ℕ} (A : Fin M → Fin W → Fin 3) : Prop :=
  ∃ p q : Fin 2, hPat p q A

def isVStar {M W : ℕ} (A : Fin M → Fin W → Fin 3) : Prop :=
  isHStar (fun j i => A i j)

-- Row-to-row propagation: if r1 = alt02 q and (r1, r2) is a valid 2xW strip (W >= 2), then r2 = alt10 q ∨ alt21 q
private lemma row_from_alt02 {W : ℕ} (hW : 2 ≤ W) {q : Fin 2} {r1 r2 : Fin W → Fin 3}
    (h1 : alt02 q r1)
    (hstrip : ∀ (j : Fin W) (hj : j.1 + 1 < W), ok2 (r1 j) (r1 ⟨j.1 + 1, hj⟩) (r2 j) (r2 ⟨j.1 + 1, hj⟩)) :
    alt10 q r2 ∨ alt21 q r2 := by
  have h01 := hstrip ⟨0, by omega⟩ (by dsimp only; omega)
  have hr10 := h1 ⟨0, by omega⟩
  have hr11 := h1 ⟨1, by omega⟩
  -- Determine branch from j = 0
  have hbranch : (r2 ⟨0, by omega⟩ = if (0 + q.1) % 2 = 0 then 1 else 0) ∨
                 (r2 ⟨0, by omega⟩ = if (0 + q.1) % 2 = 0 then 2 else 1) := by
    have hq := q.2
    by_cases hq0 : q.1 = 0
    · simp only [hq0, Nat.add_zero, Nat.zero_mod, ↓reduceIte] at hr10 ⊢
      simp only [hq0, Nat.add_zero, show (1 : ℕ) % 2 ≠ 0 by omega, ↓reduceIte] at hr11
      rcases (ok2_top02 _ _ _ _ h01).1 ⟨hr10, hr11⟩ with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · have hq1 : q.1 = 1 := by omega
      simp only [hq1, Nat.zero_add, show (1 : ℕ) % 2 ≠ 0 by omega, ↓reduceIte] at hr10 ⊢
      simp only [hq1, show (1 + 1) % 2 = 0 by omega, ↓reduceIte] at hr11
      rcases (ok2_top02 _ _ _ _ h01).2 ⟨hr10, hr11⟩ with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
  rcases hbranch with hb10 | hb21
  · left
    intro j; rcases j with ⟨k, hk⟩
    induction k with
    | zero => exact hb10
    | succ k ih =>
      have hprev := ih (by omega)
      have hst := hstrip ⟨k, by omega⟩ (by dsimp only; omega)
      have hrk := h1 ⟨k, by omega⟩
      have hrk1 := h1 ⟨k + 1, hk⟩
      by_cases hp : (k + q.1) % 2 = 0
      · have hp1 : ¬ (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_top02 _ _ _ _ hst).1 ⟨hrk, hrk1⟩ with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · rw [hprev] at h; exact absurd h (by decide)
      · have hp1 : (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_top02 _ _ _ _ hst).2 ⟨hrk, hrk1⟩ with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · rw [hprev] at h; exact absurd h (by decide)
  · right
    intro j; rcases j with ⟨k, hk⟩
    induction k with
    | zero => exact hb21
    | succ k ih =>
      have hprev := ih (by omega)
      have hst := hstrip ⟨k, by omega⟩ (by dsimp only; omega)
      have hrk := h1 ⟨k, by omega⟩
      have hrk1 := h1 ⟨k + 1, hk⟩
      by_cases hp : (k + q.1) % 2 = 0
      · have hp1 : ¬ (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_top02 _ _ _ _ hst).1 ⟨hrk, hrk1⟩ with ⟨h, _⟩ | ⟨_, h⟩
        · rw [hprev] at h; exact absurd h (by decide)
        · exact h
      · have hp1 : (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_top02 _ _ _ _ hst).2 ⟨hrk, hrk1⟩ with ⟨h, _⟩ | ⟨_, h⟩
        · rw [hprev] at h; exact absurd h (by decide)
        · exact h

-- Symmetric: row above an alt02 row
private lemma row_above_alt02 {W : ℕ} (hW : 2 ≤ W) {q : Fin 2} {r1 r2 : Fin W → Fin 3}
    (h2 : alt02 q r2)
    (hstrip : ∀ (j : Fin W) (hj : j.1 + 1 < W), ok2 (r1 j) (r1 ⟨j.1 + 1, hj⟩) (r2 j) (r2 ⟨j.1 + 1, hj⟩)) :
    alt10 q r1 ∨ alt21 q r1 := by
  have h01 := hstrip ⟨0, by omega⟩ (by dsimp only; omega)
  have hr20 := h2 ⟨0, by omega⟩
  have hr21 := h2 ⟨1, by omega⟩
  have hbranch : (r1 ⟨0, by omega⟩ = if (0 + q.1) % 2 = 0 then 1 else 0) ∨
                 (r1 ⟨0, by omega⟩ = if (0 + q.1) % 2 = 0 then 2 else 1) := by
    have hq := q.2
    by_cases hq0 : q.1 = 0
    · simp only [hq0, Nat.add_zero, Nat.zero_mod, ↓reduceIte] at hr20 ⊢
      simp only [hq0, Nat.add_zero, show (1 : ℕ) % 2 ≠ 0 by omega, ↓reduceIte] at hr21
      rcases (ok2_bot02 _ _ _ _ h01).1 ⟨hr20, hr21⟩ with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · have hq1 : q.1 = 1 := by omega
      simp only [hq1, Nat.zero_add, show (1 : ℕ) % 2 ≠ 0 by omega, ↓reduceIte] at hr20 ⊢
      simp only [hq1, show (1 + 1) % 2 = 0 by omega, ↓reduceIte] at hr21
      rcases (ok2_bot02 _ _ _ _ h01).2 ⟨hr20, hr21⟩ with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
  rcases hbranch with hb10 | hb21
  · left
    intro j; rcases j with ⟨k, hk⟩
    induction k with
    | zero => exact hb10
    | succ k ih =>
      have hprev := ih (by omega)
      have hst := hstrip ⟨k, by omega⟩ (by dsimp only; omega)
      have hrk := h2 ⟨k, by omega⟩
      have hrk1 := h2 ⟨k + 1, hk⟩
      by_cases hp : (k + q.1) % 2 = 0
      · have hp1 : ¬ (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_bot02 _ _ _ _ hst).1 ⟨hrk, hrk1⟩ with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · rw [hprev] at h; exact absurd h (by decide)
      · have hp1 : (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_bot02 _ _ _ _ hst).2 ⟨hrk, hrk1⟩ with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · rw [hprev] at h; exact absurd h (by decide)
  · right
    intro j; rcases j with ⟨k, hk⟩
    induction k with
    | zero => exact hb21
    | succ k ih =>
      have hprev := ih (by omega)
      have hst := hstrip ⟨k, by omega⟩ (by dsimp only; omega)
      have hrk := h2 ⟨k, by omega⟩
      have hrk1 := h2 ⟨k + 1, hk⟩
      by_cases hp : (k + q.1) % 2 = 0
      · have hp1 : ¬ (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_bot02 _ _ _ _ hst).1 ⟨hrk, hrk1⟩ with ⟨h, _⟩ | ⟨_, h⟩
        · rw [hprev] at h; exact absurd h (by decide)
        · exact h
      · have hp1 : (k + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at hrk hprev
        simp only [hp1, ↓reduceIte] at hrk1 ⊢
        rcases (ok2_bot02 _ _ _ _ hst).2 ⟨hrk, hrk1⟩ with ⟨h, _⟩ | ⟨_, h⟩
        · rw [hprev] at h; exact absurd h (by decide)
        · exact h

-- Row below/above an alt10 or alt21 row is forced to be alt02
private lemma row_from_non02 {W : ℕ} (hW : 2 ≤ W) {q : Fin 2} {r1 r2 : Fin W → Fin 3}
    (h1 : alt10 q r1 ∨ alt21 q r1)
    (hstrip : ∀ (j : Fin W) (hj : j.1 + 1 < W), ok2 (r1 j) (r1 ⟨j.1 + 1, hj⟩) (r2 j) (r2 ⟨j.1 + 1, hj⟩)) :
    alt02 q r2 := by
  intro j
  by_cases hj : j.1 + 1 < W
  · have hst := hstrip j hj
    rcases h1 with h10 | h21
    · have a1 := h10 j; have a2 := h10 ⟨j.1 + 1, hj⟩
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_top_non02 _ _ _ _ hst).1 ⟨a1, a2⟩).1
      · have hp1 : (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_top_non02 _ _ _ _ hst).2.1 ⟨a1, a2⟩).1
    · have a1 := h21 j; have a2 := h21 ⟨j.1 + 1, hj⟩
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_top_non02 _ _ _ _ hst).2.2.1 ⟨a1, a2⟩).1
      · have hp1 : (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_top_non02 _ _ _ _ hst).2.2.2 ⟨a1, a2⟩).1
  · have hjm : j.1 - 1 + 1 < W := by omega
    have hst := hstrip ⟨j.1 - 1, by omega⟩ hjm
    have heq : (⟨(⟨j.1 - 1, by omega⟩ : Fin W).1 + 1, hjm⟩ : Fin W) = j := Fin.ext (by dsimp only; omega)
    rw [heq] at hst
    rcases h1 with h10 | h21
    · have a1 := h10 ⟨j.1 - 1, by omega⟩; have a2 := h10 j
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_top_non02 _ _ _ _ hst).2.1 ⟨a1, a2⟩).2
      · have hp1 : (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_top_non02 _ _ _ _ hst).1 ⟨a1, a2⟩).2
    · have a1 := h21 ⟨j.1 - 1, by omega⟩; have a2 := h21 j
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_top_non02 _ _ _ _ hst).2.2.2 ⟨a1, a2⟩).2
      · have hp1 : (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_top_non02 _ _ _ _ hst).2.2.1 ⟨a1, a2⟩).2

private lemma row_above_non02 {W : ℕ} (hW : 2 ≤ W) {q : Fin 2} {r1 r2 : Fin W → Fin 3}
    (h2 : alt10 q r2 ∨ alt21 q r2)
    (hstrip : ∀ (j : Fin W) (hj : j.1 + 1 < W), ok2 (r1 j) (r1 ⟨j.1 + 1, hj⟩) (r2 j) (r2 ⟨j.1 + 1, hj⟩)) :
    alt02 q r1 := by
  intro j
  by_cases hj : j.1 + 1 < W
  · have hst := hstrip j hj
    rcases h2 with h10 | h21
    · have a1 := h10 j; have a2 := h10 ⟨j.1 + 1, hj⟩
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_bot_non02 _ _ _ _ hst).1 ⟨a1, a2⟩).1
      · have hp1 : (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_bot_non02 _ _ _ _ hst).2.1 ⟨a1, a2⟩).1
    · have a1 := h21 j; have a2 := h21 ⟨j.1 + 1, hj⟩
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_bot_non02 _ _ _ _ hst).2.2.1 ⟨a1, a2⟩).1
      · have hp1 : (j.1 + 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a1 ⊢; simp only [hp1, ↓reduceIte] at a2
        exact ((ok2_bot_non02 _ _ _ _ hst).2.2.2 ⟨a1, a2⟩).1
  · have hjm : j.1 - 1 + 1 < W := by omega
    have hst := hstrip ⟨j.1 - 1, by omega⟩ hjm
    have heq : (⟨(⟨j.1 - 1, by omega⟩ : Fin W).1 + 1, hjm⟩ : Fin W) = j := Fin.ext (by dsimp only; omega)
    rw [heq] at hst
    rcases h2 with h10 | h21
    · have a1 := h10 ⟨j.1 - 1, by omega⟩; have a2 := h10 j
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_bot_non02 _ _ _ _ hst).2.1 ⟨a1, a2⟩).2
      · have hp1 : (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_bot_non02 _ _ _ _ hst).1 ⟨a1, a2⟩).2
    · have a1 := h21 ⟨j.1 - 1, by omega⟩; have a2 := h21 j
      by_cases hp : (j.1 + q.1) % 2 = 0
      · have hp1 : ¬ (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_bot_non02 _ _ _ _ hst).2.2.2 ⟨a1, a2⟩).2
      · have hp1 : (j.1 - 1 + q.1) % 2 = 0 := by omega
        simp only [hp, ↓reduceIte] at a2 ⊢; simp only [hp1, ↓reduceIte] at a1
        exact ((ok2_bot_non02 _ _ _ _ hst).2.2.1 ⟨a1, a2⟩).2

-- If ANY row of a valid grid (W >= 2) is alt02, then the entire grid is HStar!
private lemma isHStar_of_alt02_row {M W : ℕ} (hW : 2 ≤ W) {A : Fin M → Fin W → Fin 3}
    (hA : validGrid A) (i0 : Fin M) (q : Fin 2) (h0 : alt02 q (A i0)) :
    isHStar A := by
  let p : Fin 2 := ⟨i0.1 % 2, by omega⟩
  refine ⟨p, q, ?_⟩
  -- Prove both conditions simultaneously for all i by distance |i - i0|
  suffices hall : ∀ i : Fin M, (i.1 % 2 = p.1 → alt02 q (A i)) ∧ (i.1 % 2 ≠ p.1 → alt10 q (A i) ∨ alt21 q (A i)) by
    exact ⟨fun i hi => (hall i).1 hi, fun i hi => (hall i).2 hi⟩
  have hdown : ∀ d : ℕ, ∀ hd : i0.1 + d < M,
      ((i0.1 + d) % 2 = p.1 → alt02 q (A ⟨i0.1 + d, hd⟩)) ∧
      ((i0.1 + d) % 2 ≠ p.1 → alt10 q (A ⟨i0.1 + d, hd⟩) ∨ alt21 q (A ⟨i0.1 + d, hd⟩)) := by
    intro d; induction d with
    | zero =>
      intro hd
      have heq : (⟨i0.1 + 0, hd⟩ : Fin M) = i0 := Fin.ext (by simp)
      rw [heq]; refine ⟨fun _ => h0, fun h => absurd (by dsimp only [p]; omega) h⟩
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hst : ∀ (j : Fin W) (hj : j.1 + 1 < W),
          ok2 (A ⟨i0.1 + d, by omega⟩ j) (A ⟨i0.1 + d, by omega⟩ ⟨j.1 + 1, hj⟩)
              (A ⟨i0.1 + (d + 1), hd⟩ j) (A ⟨i0.1 + (d + 1), hd⟩ ⟨j.1 + 1, hj⟩) := by
        intro j hj
        have h := hA ⟨i0.1 + d, by omega⟩ (by dsimp only; omega) j hj
        have heq : (⟨(⟨i0.1 + d, by omega⟩ : Fin M).1 + 1, by dsimp only; omega⟩ : Fin M) = ⟨i0.1 + (d + 1), hd⟩ :=
          Fin.ext (by dsimp only; omega)
        rwa [heq] at h
      refine ⟨fun he => row_from_non02 hW (hprev.2 (by dsimp [p] at he ⊢; omega)) hst,
              fun hne => row_from_alt02 hW (hprev.1 (by dsimp [p] at hne ⊢; omega)) hst⟩
  have hup : ∀ d : ℕ, ∀ hd : d ≤ i0.1,
      ((i0.1 - d) % 2 = p.1 → alt02 q (A ⟨i0.1 - d, by omega⟩)) ∧
      ((i0.1 - d) % 2 ≠ p.1 → alt10 q (A ⟨i0.1 - d, by omega⟩) ∨ alt21 q (A ⟨i0.1 - d, by omega⟩)) := by
    intro d; induction d with
    | zero =>
      intro _
      have heq : (⟨i0.1 - 0, by omega⟩ : Fin M) = i0 := Fin.ext (by simp)
      rw [heq]; refine ⟨fun _ => h0, fun h => absurd (by dsimp only [p]; omega) h⟩
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hst : ∀ (j : Fin W) (hj : j.1 + 1 < W),
          ok2 (A ⟨i0.1 - (d + 1), by omega⟩ j) (A ⟨i0.1 - (d + 1), by omega⟩ ⟨j.1 + 1, hj⟩)
              (A ⟨i0.1 - d, by omega⟩ j) (A ⟨i0.1 - d, by omega⟩ ⟨j.1 + 1, hj⟩) := by
        intro j hj
        have h := hA ⟨i0.1 - (d + 1), by omega⟩ (by dsimp only; omega) j hj
        have heq : (⟨(⟨i0.1 - (d + 1), by omega⟩ : Fin M).1 + 1, by dsimp only; omega⟩ : Fin M) = ⟨i0.1 - d, by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        rwa [heq] at h
      refine ⟨fun he => row_above_non02 hW (hprev.2 (by dsimp [p] at he ⊢; omega)) hst,
              fun hne => row_above_alt02 hW (hprev.1 (by dsimp [p] at hne ⊢; omega)) hst⟩
  intro i
  by_cases hi : i0.1 ≤ i.1
  · have h := hdown (i.1 - i0.1) (by omega)
    have heq : (⟨i0.1 + (i.1 - i0.1), by omega⟩ : Fin M) = i := Fin.ext (by dsimp only; omega)
    have heq' : i0.1 + (i.1 - i0.1) = i.1 := by omega
    rw [heq, heq'] at h; exact h
  · have h := hup (i0.1 - i.1) (by omega)
    have heq : (⟨i0.1 - (i0.1 - i.1), by omega⟩ : Fin M) = i := Fin.ext (by dsimp only; omega)
    have heq' : i0.1 - (i0.1 - i.1) = i.1 := by omega
    rw [heq, heq'] at h; exact h

-- Main characterization theorem: for M, W >= 2, validGrid A ↔ isHStar A ∨ isVStar A!
theorem validGrid_iff {M W : ℕ} (hM : 2 ≤ M) (hW : 2 ≤ W) (A : Fin M → Fin W → Fin 3) :
    validGrid A ↔ isHStar A ∨ isVStar A := by
  constructor
  · intro hA
    -- Check if row 0 or row 1 is alt02
    by_cases hr0 : ∃ q : Fin 2, alt02 q (A ⟨0, by omega⟩)
    · rcases hr0 with ⟨q, hq⟩; exact Or.inl (isHStar_of_alt02_row hW hA ⟨0, by omega⟩ q hq)
    by_cases hr1 : ∃ q : Fin 2, alt02 q (A ⟨1, by omega⟩)
    · rcases hr1 with ⟨q, hq⟩; exact Or.inl (isHStar_of_alt02_row hW hA ⟨1, by omega⟩ q hq)
    -- Otherwise, in rows 0..1, each column pair (j, j+1) has top {0,2} XOR bottom {0,2}.
    -- Since neither row 0 nor row 1 is all {0,2}, there must be a switch at some j (with j + 2 < W)!
    right
    let top02 (j : ℕ) (hj : j + 1 < W) : Prop :=
      (A ⟨0, by omega⟩ ⟨j, by omega⟩ = 0 ∧ A ⟨0, by omega⟩ ⟨j + 1, hj⟩ = 2) ∨
      (A ⟨0, by omega⟩ ⟨j, by omega⟩ = 2 ∧ A ⟨0, by omega⟩ ⟨j + 1, hj⟩ = 0)
    let bot02 (j : ℕ) (hj : j + 1 < W) : Prop :=
      (A ⟨1, by omega⟩ ⟨j, by omega⟩ = 0 ∧ A ⟨1, by omega⟩ ⟨j + 1, hj⟩ = 2) ∨
      (A ⟨1, by omega⟩ ⟨j, by omega⟩ = 2 ∧ A ⟨1, by omega⟩ ⟨j + 1, hj⟩ = 0)
    have hxor : ∀ (j : ℕ) (hj : j + 1 < W), (top02 j hj ∧ ¬ bot02 j hj) ∨ (¬ top02 j hj ∧ bot02 j hj) := by
      intro j hj
      exact ok2_xor_row02 _ _ _ _ (hA ⟨0, by omega⟩ (by dsimp only; omega) ⟨j, by omega⟩ hj)
    -- If all j had top02, then row 0 would be alt02; if all j had bot02, row 1 would be alt02!
    have hex_switch : ∃ (j : ℕ) (hj : j + 2 < W),
        (top02 j (by omega) ∧ bot02 (j + 1) hj) ∨ (bot02 j (by omega) ∧ top02 (j + 1) hj) := by
      by_contra hno
      -- Then top02 j has the same truth value for all j < W - 1!
      have hsame : ∀ (j : ℕ) (hj : j + 1 < W), top02 j hj ↔ top02 0 (by omega) := by
        intro j; induction j with
        | zero => intro _; exact Iff.rfl
        | succ j ih =>
          intro hj
          have h1 := hxor j (by omega)
          have h2 := hxor (j + 1) hj
          have hno' : ¬ ((top02 j (by omega) ∧ bot02 (j + 1) hj) ∨ (bot02 j (by omega) ∧ top02 (j + 1) hj)) :=
            fun h => hno ⟨j, hj, h⟩
          have hstep : top02 (j + 1) hj ↔ top02 j (by omega) := by
            constructor
            · intro ht1
              rcases h1 with ⟨ht0, _⟩ | ⟨_, hb0⟩
              · exact ht0
              · exact absurd (Or.inr ⟨hb0, ht1⟩) hno'
            · intro ht0
              rcases h2 with ⟨ht1, _⟩ | ⟨_, hb1⟩
              · exact ht1
              · exact absurd (Or.inl ⟨ht0, hb1⟩) hno'
          exact hstep.trans (ih (by omega))
      -- Helper: if all pairs (j, j+1) of a row r are (0,2) or (2,0), then r is alt02!
      have hall_alt02 : ∀ r : Fin W → Fin 3,
          (∀ (j : ℕ) (hj : j + 1 < W), (r ⟨j, by omega⟩ = 0 ∧ r ⟨j + 1, hj⟩ = 2) ∨ (r ⟨j, by omega⟩ = 2 ∧ r ⟨j + 1, hj⟩ = 0)) →
          ∃ q : Fin 2, alt02 q r := by
        intro r hr
        rcases hr 0 (by omega) with ⟨h0, _⟩ | ⟨h0, _⟩
        · refine ⟨0, fun j => ?_⟩; rcases j with ⟨k, hk⟩
          induction k with
          | zero => simpa using h0
          | succ k ih =>
            have hp := ih (by omega)
            rcases hr k hk with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · by_cases he : k % 2 = 0
              · have he1 : ¬ (k + 1 + (0 : Fin 2).1) % 2 = 0 := by simp; omega
                rw [if_neg he1]; exact hb
              · simp [he] at hp; rw [hp] at ha; exact absurd ha (by decide)
            · by_cases he : k % 2 = 0
              · simp [he] at hp; rw [hp] at ha; exact absurd ha (by decide)
              · have he1 : (k + 1 + (0 : Fin 2).1) % 2 = 0 := by simp; omega
                rw [if_pos he1]; exact hb
        · refine ⟨1, fun j => ?_⟩; rcases j with ⟨k, hk⟩
          induction k with
          | zero => simpa using h0
          | succ k ih =>
            have hp := ih (by omega)
            rcases hr k hk with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · by_cases he : (k + 1) % 2 = 0
              · have he1 : ¬ (k + 1 + (1 : Fin 2).1) % 2 = 0 := by simp; omega
                rw [if_neg he1]; exact hb
              · simp [he] at hp; rw [hp] at ha; exact absurd ha (by decide)
            · by_cases he : (k + 1) % 2 = 0
              · simp [he] at hp; rw [hp] at ha; exact absurd ha (by decide)
              · have he1 : (k + 1 + (1 : Fin 2).1) % 2 = 0 := by simp; omega
                rw [if_pos he1]; exact hb
      rcases hxor 0 (by omega) with ⟨ht0, _⟩ | ⟨hnt0, _⟩
      · exact hr0 (hall_alt02 (A ⟨0, by omega⟩) (fun j hj => (hsame j hj).mpr ht0))
      · exact hr1 (hall_alt02 (A ⟨1, by omega⟩) (fun j hj => by
          rcases hxor j hj with ⟨htj, _⟩ | ⟨_, hbj⟩
          · exact absurd ((hsame j hj).mp htj) hnt0
          · exact hbj))
    rcases hex_switch with ⟨j0, hj0, hsw⟩
    -- At column j0 + 1, the 2x3 switch propagates all the way down, making column j0 + 1 alt02!
    let isSw (r : ℕ) (hr : r + 1 < M) : Prop :=
      (isPair02 (A ⟨r, by omega⟩ ⟨j0, by omega⟩) (A ⟨r, by omega⟩ ⟨j0 + 1, by omega⟩) ∧
       isPair02 (A ⟨r + 1, hr⟩ ⟨j0 + 1, by omega⟩) (A ⟨r + 1, hr⟩ ⟨j0 + 2, hj0⟩)) ∨
      (isPair02 (A ⟨r + 1, hr⟩ ⟨j0, by omega⟩) (A ⟨r + 1, hr⟩ ⟨j0 + 1, by omega⟩) ∧
       isPair02 (A ⟨r, by omega⟩ ⟨j0 + 1, by omega⟩) (A ⟨r, by omega⟩ ⟨j0 + 2, hj0⟩))
    have hsw_all : ∀ (r : ℕ) (hr : r + 1 < M), isSw r hr := by
      intro r; induction r with
      | zero => intro _; exact hsw
      | succ r ih =>
        intro hr
        have hprev := ih (by omega)
        exact (ok2_switch_down _ _ _ _ _ _ _ _ _
          (hA ⟨r, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
          (hA ⟨r, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
          (hA ⟨r + 1, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
          (hA ⟨r + 1, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
          hprev).2
    have hmid01 : isPair02 (A ⟨0, by omega⟩ ⟨j0 + 1, by omega⟩) (A ⟨1, by omega⟩ ⟨j0 + 1, by omega⟩) :=
      ok2_switch_mid _ _ _ _ _ _
        (hA ⟨0, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
        (hA ⟨0, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
        hsw
    have hcol_alt : ∃ q : Fin 2, alt02 q (fun i => A i ⟨j0 + 1, by omega⟩) := by
      rcases hmid01 with ⟨hm0, hm1⟩ | ⟨hm0, hm1⟩
      · refine ⟨0, fun i => ?_⟩; rcases i with ⟨k, hk⟩
        induction k using Nat.strong_induction_on with
        | h k ih =>
          match k with
          | 0 => simpa using hm0
          | 1 => simpa using hm1
          | r + 2 =>
            have hr0' := ih r (by omega) (by omega)
            have hstep := (ok2_switch_down _ _ _ _ _ _ _ _ _
              (hA ⟨r, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
              (hA ⟨r, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
              (hA ⟨r + 1, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
              (hA ⟨r + 1, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
              (hsw_all r (by omega))).1
            dsimp only at hstep hr0' ⊢
            rw [hstep, hr0']
            have : (r + 2 + (0 : Fin 2).1) % 2 = (r + (0 : Fin 2).1) % 2 := by omega
            simp only [this]
      · refine ⟨1, fun i => ?_⟩; rcases i with ⟨k, hk⟩
        induction k using Nat.strong_induction_on with
        | h k ih =>
          match k with
          | 0 => simpa using hm0
          | 1 => simpa using hm1
          | r + 2 =>
            have hr0' := ih r (by omega) (by omega)
            have hstep := (ok2_switch_down _ _ _ _ _ _ _ _ _
              (hA ⟨r, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
              (hA ⟨r, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
              (hA ⟨r + 1, by omega⟩ (by dsimp only; omega) ⟨j0, by omega⟩ (by dsimp only; omega))
              (hA ⟨r + 1, by omega⟩ (by dsimp only; omega) ⟨j0 + 1, by omega⟩ (by dsimp only; omega))
              (hsw_all r (by omega))).1
            dsimp only at hstep hr0' ⊢
            rw [hstep, hr0']
            have : (r + 2 + (1 : Fin 2).1) % 2 = (r + (1 : Fin 2).1) % 2 := by omega
            simp only [this]
    rcases hcol_alt with ⟨q, hq⟩
    exact isHStar_of_alt02_row hM (validGrid_transpose hA) ⟨j0 + 1, by omega⟩ q hq
  · -- Converse: isHStar ∨ isVStar → validGrid
    have hH : ∀ {M' W' : ℕ} {B : Fin M' → Fin W' → Fin 3}, isHStar B → validGrid B := by
      intro M' W' B ⟨p, q, hp0, hp1⟩ i hi j hj
      by_cases hip : i.1 % 2 = p.1
      · have h0 := hp0 i hip
        have h1 := hp1 ⟨i.1 + 1, hi⟩ (by dsimp only; omega)
        have a := h0 j; have b := h0 ⟨j.1 + 1, hj⟩
        rcases h1 with h10 | h21
        · have d := h10 j; have c := h10 ⟨j.1 + 1, hj⟩
          rw [a, b, d, c]; by_cases hp : (j.1 + q.1) % 2 = 0
          · have hp' : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
          · have hp' : (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
        · have d := h21 j; have c := h21 ⟨j.1 + 1, hj⟩
          rw [a, b, d, c]; by_cases hp : (j.1 + q.1) % 2 = 0
          · have hp' : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
          · have hp' : (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
      · have h0 := hp1 i hip
        have h1 := hp0 ⟨i.1 + 1, hi⟩ (by dsimp only; omega)
        have d := h1 j; have c := h1 ⟨j.1 + 1, hj⟩
        rcases h0 with h10 | h21
        · have a := h10 j; have b := h10 ⟨j.1 + 1, hj⟩
          rw [a, b, d, c]; by_cases hp : (j.1 + q.1) % 2 = 0
          · have hp' : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
          · have hp' : (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
        · have a := h21 j; have b := h21 ⟨j.1 + 1, hj⟩
          rw [a, b, d, c]; by_cases hp : (j.1 + q.1) % 2 = 0
          · have hp' : ¬ (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
          · have hp' : (j.1 + 1 + q.1) % 2 = 0 := by omega
            simp only [hp, hp', ↓reduceIte]; unfold ok2 distinctClockwise; decide
    rintro (h | h)
    · exact hH h
    · exact validGrid_transpose (hH h)

-- Exact cardinality of HStar(M, W) for M >= 2, W >= 2
def hStarCount (M : ℕ) : ℕ :=
  if M % 2 = 0 then 4 * 2 ^ (M / 2) else 6 * 2 ^ (M / 2)

private lemma card_hStar {M W : ℕ} (hM : 2 ≤ M) (hW : 2 ≤ W) :
    (Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => isHStar A)).card = hStarCount M := by
  let S (p q : Fin 2) : Finset (Fin M → Fin W → Fin 3) := Finset.univ.filter (hPat p q)
  have hunion : Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => isHStar A) =
      S 0 0 ∪ S 0 1 ∪ S 1 0 ∪ S 1 1 := by
    ext A
    simp only [Finset.mem_union, S]
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, isHStar]
    constructor
    · rintro ⟨p, q, hpq⟩
      match p, q with
      | 0, 0 => exact Or.inl (Or.inl (Or.inl hpq))
      | 0, 1 => exact Or.inl (Or.inl (Or.inr hpq))
      | 1, 0 => exact Or.inl (Or.inr hpq)
      | 1, 1 => exact Or.inr hpq
    · rintro (((h | h) | h) | h)
      · exact ⟨0, 0, h⟩
      · exact ⟨0, 1, h⟩
      · exact ⟨1, 0, h⟩
      · exact ⟨1, 1, h⟩
  have hdisj : ∀ p1 q1 p2 q2 : Fin 2, (p1, q1) ≠ (p2, q2) → Disjoint (S p1 q1) (S p2 q2) := by
    intro p1 q1 p2 q2 hne
    rw [Finset.disjoint_left]; intro A h1 h2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have h02_ne_1021 : ∀ q1' q2' : Fin 2, ∀ r : Fin W → Fin 3,
        alt02 q1' r → (alt10 q2' r ∨ alt21 q2' r) → False := by
      intro q1' q2' r ha hb
      have a0 := ha ⟨0, by omega⟩; have a1 := ha ⟨1, by omega⟩
      rcases hb with h10 | h21
      · have b0 := h10 ⟨0, by omega⟩; have b1 := h10 ⟨1, by omega⟩
        rcases q1' with ⟨v1, hv1⟩; rcases q2' with ⟨v2, hv2⟩
        interval_cases v1 <;> interval_cases v2 <;> simp at a0 a1 b0 b1
        · rw [a0] at b0; cases b0
        · rw [a1] at b1; cases b1
        · rw [a0] at b0; cases b0
        · rw [a0] at b0; cases b0
      · have b0 := h21 ⟨0, by omega⟩; have b1 := h21 ⟨1, by omega⟩
        rcases q1' with ⟨v1, hv1⟩; rcases q2' with ⟨v2, hv2⟩
        interval_cases v1 <;> interval_cases v2 <;> simp at a0 a1 b0 b1
        · rw [a0] at b0; cases b0
        · rw [a0] at b0; cases b0
        · rw [a1] at b1; cases b1
        · rw [a0] at b0; cases b0
    have hp_eq : p1 = p2 := by
      by_contra hpn
      have h0 : p1.1 = 0 ∨ p1.1 = 1 := by omega
      rcases h0 with hp10 | hp11
      · have hp21 : p2.1 = 1 := by have := p2.2; omega
        exact h02_ne_1021 q1 q2 (A ⟨0, by omega⟩) (h1.1 ⟨0, by omega⟩ (by simp [hp10])) (h2.2 ⟨0, by omega⟩ (by simp [hp21]))
      · have hp20 : p2.1 = 0 := by have := p2.2; omega
        exact h02_ne_1021 q2 q1 (A ⟨0, by omega⟩) (h2.1 ⟨0, by omega⟩ (by simp [hp20])) (h1.2 ⟨0, by omega⟩ (by simp [hp11]))
    subst hp_eq
    have hq_ne : q1 ≠ q2 := fun h => hne (by rw [h])
    have r0a := h1.1 ⟨p1.1, by omega⟩ (by dsimp only; omega) ⟨0, by omega⟩
    have r0b := h2.1 ⟨p1.1, by omega⟩ (by dsimp only; omega) ⟨0, by omega⟩
    rcases q1 with ⟨q1v, hq1v⟩; rcases q2 with ⟨q2v, hq2v⟩
    interval_cases q1v <;> interval_cases q2v
    · exact hq_ne rfl
    · simp at r0a r0b; rw [r0a] at r0b; cases r0b
    · simp at r0a r0b; rw [r0a] at r0b; cases r0b
    · exact hq_ne rfl
  -- Card of each S p q = 2 ^ |{i : Fin M | i % 2 ≠ p}|
  have hcS : ∀ p q : Fin 2, (S p q).card = 2 ^ (Finset.univ.filter (fun i : Fin M => i.1 % 2 ≠ p.1)).card := by
    intro p q
    let idx := Finset.univ.filter (fun i : Fin M => i.1 % 2 ≠ p.1)
    have hpow : 2 ^ idx.card = Fintype.card ({i : Fin M // i ∈ idx} → Bool) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    rw [hpow, ← Finset.card_univ]
    refine Finset.card_bij
      (fun A _ i => decide (A i.1 ⟨0, by omega⟩ = if (0 + q.1) % 2 = 0 then 1 else 0)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro A1 hA1 A2 hA2 h
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
      funext i j
      by_cases hi : i.1 % 2 = p.1
      · rw [hA1.1 i hi j, hA2.1 i hi j]
      · have hmem : i ∈ idx := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hb := congr_fun h ⟨i, hmem⟩
        dsimp only at hb
        rcases hA1.2 i hi with h11 | h12 <;> rcases hA2.2 i hi with h21 | h22
        · rw [h11 j, h21 j]
        · have a1 := h11 ⟨0, by omega⟩; have a2 := h22 ⟨0, by omega⟩
          rw [a1, a2] at hb
          rcases q with ⟨qv, hqv⟩; interval_cases qv <;> simp at hb
        · have a1 := h12 ⟨0, by omega⟩; have a2 := h21 ⟨0, by omega⟩
          rw [a1, a2] at hb
          rcases q with ⟨qv, hqv⟩; interval_cases qv <;> simp at hb
        · rw [h12 j, h22 j]
    · intro f _
      let A : Fin M → Fin W → Fin 3 := fun i j =>
        if hi : i.1 % 2 = p.1 then
          (if (j.1 + q.1) % 2 = 0 then 0 else 2)
        else if f ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩ then
          (if (j.1 + q.1) % 2 = 0 then 1 else 0)
        else
          (if (j.1 + q.1) % 2 = 0 then 2 else 1)
      refine ⟨A, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun i hi j => by simp only [A, hi, ↓reduceDIte], fun i hi => ?_⟩
        by_cases hfi : f ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩ = true
        · left; intro j; simp only [A, hi, ↓reduceDIte, hfi, ↓reduceIte]
        · right; intro j; simp only [A, hi, ↓reduceDIte, hfi, Bool.false_eq_true, ↓reduceIte]
      · funext ⟨i, hmem⟩
        have hi : i.1 % 2 ≠ p.1 := (Finset.mem_filter.mp hmem).2
        simp only [A, hi, ↓reduceDIte]
        cases hf : f ⟨i, hmem⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          match q with | 0 => simp | 1 => simp
        · simp only [↓reduceIte, decide_true]
  rw [hunion]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
        exact ⟨⟨hdisj 0 0 1 1 (by decide), hdisj 0 1 1 1 (by decide)⟩, hdisj 1 0 1 1 (by decide)⟩)]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left]
        exact ⟨hdisj 0 0 1 0 (by decide), hdisj 0 1 1 0 (by decide)⟩)]
  rw [Finset.card_union_of_disjoint (hdisj 0 0 0 1 (by decide))]
  rw [hcS 0 0, hcS 0 1, hcS 1 0, hcS 1 1]
  have hodd : (Finset.univ.filter (fun i : Fin M => i.1 % 2 ≠ (0 : Fin 2).1)).card = M / 2 := by
    have : (Finset.univ.filter (fun i : Fin M => i.1 % 2 ≠ (0 : Fin 2).1)).card =
        ((Finset.range M).filter (fun k => k % 2 ≠ 0)).card := by
      refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero] at hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.2, hi⟩
      · intro i1 _ i2 _ h; exact Fin.ext h
      · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk
        exact ⟨⟨k, hk.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]; exact hk.2, rfl⟩
    rw [this]; clear this hunion hdisj hcS hM
    induction M with
    | zero => simp
    | succ k ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hk
      · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
      · rw [ih]; omega
  have heven : (Finset.univ.filter (fun i : Fin M => i.1 % 2 ≠ (1 : Fin 2).1)).card = (M + 1) / 2 := by
    have : (Finset.univ.filter (fun i : Fin M => i.1 % 2 ≠ (1 : Fin 2).1)).card =
        ((Finset.range M).filter (fun k => k % 2 = 0)).card := by
      refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_one] at hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.2, by omega⟩
      · intro i1 _ i2 _ h; exact Fin.ext h
      · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk
        exact ⟨⟨k, hk.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_one]; omega, rfl⟩
    rw [this]; clear this hodd hunion hdisj hcS hM
    induction M with
    | zero => simp
    | succ k ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hk
      · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
      · rw [ih]; omega
  rw [hodd, heven]
  unfold hStarCount
  by_cases hm : M % 2 = 0
  · rw [if_pos hm]
    have hdiv : (M + 1) / 2 = M / 2 := by omega
    rw [hdiv]; ring
  · rw [if_neg hm]
    have hdiv : (M + 1) / 2 = M / 2 + 1 := by omega
    rw [hdiv]; ring

-- Exact cardinality of HStar(M, W) ∩ VStar(M, W) is 8!
private lemma card_inter_hStar_vStar {M W : ℕ} (hM : 2 ≤ M) (hW : 2 ≤ W) :
    (Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => isHStar A ∧ isVStar A)).card = 8 := by
  let mkConst (p q ch : Fin 2) : Fin M → Fin W → Fin 3 := fun i j =>
    if i.1 % 2 = p.1 then (if (j.1 + q.1) % 2 = 0 then 0 else 2)
    else if ch = 0 then (if (j.1 + q.1) % 2 = 0 then 1 else 0)
    else (if (j.1 + q.1) % 2 = 0 then 2 else 1)
  have h8 : (8 : ℕ) = Fintype.card (Fin 2 × Fin 2 × Fin 2) := by decide
  rw [h8, ← Finset.card_univ]
  refine Finset.card_bij (fun A _ =>
    let p : Fin 2 := if A ⟨0, by omega⟩ ⟨0, by omega⟩ + A ⟨0, by omega⟩ ⟨1, by omega⟩ = 2 ∧
        A ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ A ⟨0, by omega⟩ ⟨1, by omega⟩ then 0 else 1
    let q : Fin 2 := if A ⟨p.1, by omega⟩ ⟨0, by omega⟩ = 0 then 0 else 1
    let ch : Fin 2 := if A ⟨1 - p.1, by omega⟩ ⟨0, by omega⟩ = (if (0 + q.1) % 2 = 0 then 1 else 0) then 0 else 1
    (p, q, ch)) ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro A1 hA1 A2 hA2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
    -- Any A ∈ HStar ∩ VStar is determined by its 2x2 top-left corner (since every row has period 2 and every col has period 2!)
    have hper : ∀ A : Fin M → Fin W → Fin 3, isHStar A → isVStar A →
        ∀ i : Fin M, ∀ j : Fin W, A i j = A ⟨i.1 % 2, by omega⟩ ⟨j.1 % 2, by omega⟩ := by
      intro A ⟨p, q, hp0, hp1⟩ ⟨p', q', hv0, hv1⟩ i j
      -- Every row has period 2 in j (from HStar) and every col has period 2 in i (from VStar)!
      have hcol_per : ∀ (i1 i2 : Fin M), i1.1 % 2 = i2.1 % 2 → ∀ j' : Fin W, A i1 j' = A i2 j' := by
        intro i1 i2 hi j'
        by_cases hj' : j'.1 % 2 = p'.1
        · have h1 := hv0 j' hj' i1; have h2 := hv0 j' hj' i2
          dsimp only at h1 h2; rw [h1, h2]
          have : (i1.1 + q'.1) % 2 = (i2.1 + q'.1) % 2 := by omega
          rw [this]
        · rcases hv1 j' hj' with h10 | h21
          · have h1 := h10 i1; have h2 := h10 i2; dsimp only at h1 h2; rw [h1, h2]
            have : (i1.1 + q'.1) % 2 = (i2.1 + q'.1) % 2 := by omega
            rw [this]
          · have h1 := h21 i1; have h2 := h21 i2; dsimp only at h1 h2; rw [h1, h2]
            have : (i1.1 + q'.1) % 2 = (i2.1 + q'.1) % 2 := by omega
            rw [this]
      have hrow_per : ∀ (j1 j2 : Fin W), j1.1 % 2 = j2.1 % 2 → ∀ i' : Fin M, A i' j1 = A i' j2 := by
        intro j1 j2 hj i'
        by_cases hi' : i'.1 % 2 = p.1
        · have h1 := hp0 i' hi' j1; have h2 := hp0 i' hi' j2; rw [h1, h2]
          have : (j1.1 + q.1) % 2 = (j2.1 + q.1) % 2 := by omega
          rw [this]
        · rcases hp1 i' hi' with h10 | h21
          · have h1 := h10 j1; have h2 := h10 j2; rw [h1, h2]
            have : (j1.1 + q.1) % 2 = (j2.1 + q.1) % 2 := by omega
            rw [this]
          · have h1 := h21 j1; have h2 := h21 j2; rw [h1, h2]
            have : (j1.1 + q.1) % 2 = (j2.1 + q.1) % 2 := by omega
            rw [this]
      rw [hcol_per i ⟨i.1 % 2, by omega⟩ (by dsimp only; omega) j,
          hrow_per j ⟨j.1 % 2, by omega⟩ (by dsimp only; omega)]
    -- Show that the extracted (p, q, ch) reconstructs the 2x2 top-left corner uniquely
    have hrec : ∀ A : Fin M → Fin W → Fin 3, isHStar A →
        let p : Fin 2 := if A ⟨0, by omega⟩ ⟨0, by omega⟩ + A ⟨0, by omega⟩ ⟨1, by omega⟩ = 2 ∧
            A ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ A ⟨0, by omega⟩ ⟨1, by omega⟩ then 0 else 1
        let q : Fin 2 := if A ⟨p.1, by omega⟩ ⟨0, by omega⟩ = 0 then 0 else 1
        let ch : Fin 2 := if A ⟨1 - p.1, by omega⟩ ⟨0, by omega⟩ = (if (0 + q.1) % 2 = 0 then 1 else 0) then 0 else 1
        ∀ i : Fin 2, ∀ j : Fin 2, A ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ = mkConst p q ch ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ := by
      intro A ⟨p0, q0, hp0, hp1⟩ p q ch i j
      have hp_eq : p = p0 := by
        dsimp only [p]
        rcases p0 with ⟨p0v, hp0v⟩; rcases q0 with ⟨q0v, hq0v⟩
        interval_cases p0v
        · have r0 := hp0 ⟨0, by omega⟩ (by simp)
          have a0 := r0 ⟨0, by omega⟩; have a1 := r0 ⟨1, by omega⟩
          interval_cases q0v <;> (simp at a0 a1; rw [a0, a1]; simp)
        · have r0 := hp1 ⟨0, by omega⟩ (by simp)
          rcases r0 with h10 | h21
          · have a0 := h10 ⟨0, by omega⟩; have a1 := h10 ⟨1, by omega⟩
            interval_cases q0v <;> (simp at a0 a1; rw [a0, a1]; simp)
          · have a0 := h21 ⟨0, by omega⟩; have a1 := h21 ⟨1, by omega⟩
            interval_cases q0v <;> (simp at a0 a1; rw [a0, a1]; simp)
      have hq_eq : q = q0 := by
        dsimp only [q]
        have hpf : (⟨p.1, by omega⟩ : Fin M) = ⟨p0.1, by omega⟩ := Fin.ext (by dsimp only; exact congr_arg Fin.val hp_eq)
        rw [hpf]
        have rp := hp0 ⟨p0.1, by omega⟩ (by dsimp only; omega) ⟨0, by omega⟩
        rcases q0 with ⟨q0v, hq0v⟩
        interval_cases q0v <;> (simp at rp; rw [rp]; simp)
      have hpf : (⟨1 - p.1, by omega⟩ : Fin M) = ⟨1 - p0.1, by omega⟩ := Fin.ext (by dsimp only; rw [hp_eq])
      have hch_eq : ch = if A ⟨1 - p0.1, by omega⟩ ⟨0, by omega⟩ = (if (0 + q0.1) % 2 = 0 then 1 else 0) then 0 else 1 := by
        dsimp only [ch]; rw [hpf, hq_eq]
      rw [hp_eq, hq_eq]
      dsimp only [mkConst]
      by_cases hi : i.1 % 2 = p0.1
      · simp only [hi, ↓reduceIte]; exact hp0 ⟨i.1, by omega⟩ hi ⟨j.1, by omega⟩
      · simp only [hi, ↓reduceIte]
        have hi' : (⟨i.1, by omega⟩ : Fin M) = ⟨1 - p0.1, by omega⟩ := Fin.ext (by dsimp only; have := i.2; have := p0.2; omega)
        rcases hp1 ⟨i.1, by omega⟩ hi with h10 | h21
        · have h0 := h10 ⟨0, by omega⟩
          rw [hi'] at h0
          have hc0 : ch = 0 := by rw [hch_eq, if_pos h0]
          rw [hc0, if_pos rfl]; exact h10 ⟨j.1, by omega⟩
        · have h0 := h21 ⟨0, by omega⟩
          rw [hi'] at h0
          have hc1 : ch = 1 := by
            rw [hch_eq, if_neg]
            rw [h0]; rcases q0 with ⟨q0v, hq0v⟩; interval_cases q0v <;> simp
          rw [hc1, if_neg (by simp)]; exact h21 ⟨j.1, by omega⟩
    funext i j
    rw [hper A1 hA1.1 hA1.2 i j, hper A2 hA2.1 hA2.2 i j]
    have e1 := hrec A1 hA1.1 ⟨i.1 % 2, by omega⟩ ⟨j.1 % 2, by omega⟩
    have e2 := hrec A2 hA2.1 ⟨i.1 % 2, by omega⟩ ⟨j.1 % 2, by omega⟩
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨hp, hq, hch⟩
    dsimp only at e1 e2
    rw [e1, e2]
    have hmk_eq : ∀ {a1 a2 b1 b2 c1 c2 : Fin 2}, a1 = a2 → b1 = b2 → c1 = c2 →
        ∀ i' j', mkConst a1 b1 c1 i' j' = mkConst a2 b2 c2 i' j' := by
      rintro a _ b _ c _ rfl rfl rfl i' j'; rfl
    exact hmk_eq hp hq hch _ _
  · intro ⟨p, q, ch⟩ _
    refine ⟨mkConst p q ch, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hH : isHStar (mkConst p q ch) := by
        refine ⟨p, q, fun i hi j => by simp [mkConst, hi], fun i hi => ?_⟩
        by_cases hc : ch = 0
        · left; intro j; simp [mkConst, hi, hc]
        · right; intro j; simp [mkConst, hi, hc]
      have hV : isVStar (mkConst p q ch) := by
        obtain ⟨p', q', ch', htr⟩ := mkConst_transpose_exists p q ch
        have htr' : ∀ j : Fin W, ∀ i : Fin M, mkConst p q ch i j =
            (if j.1 % 2 = p'.1 then (if (i.1 + q'.1) % 2 = 0 then 0 else 2)
             else if ch' = 0 then (if (i.1 + q'.1) % 2 = 0 then 1 else 0)
             else (if (i.1 + q'.1) % 2 = 0 then 2 else 1)) := by
          intro j i
          have h := htr ⟨i.1 % 2, by omega⟩ ⟨j.1 % 2, by omega⟩
          have hj : (j.1 % 2 + q.1) % 2 = (j.1 + q.1) % 2 := by omega
          have hi : (i.1 % 2 + q'.1) % 2 = (i.1 + q'.1) % 2 := by omega
          simpa only [mkConst, hj, hi] using h
        refine ⟨p', q', fun j hj i => by simp only [htr' j i, hj, ↓reduceIte], fun j hj => ?_⟩
        by_cases hc : ch' = 0
        · left; intro i; simp only [htr' j i, hj, hc, ↓reduceIte]
        · right; intro i; simp only [htr' j i, hj, hc, ↓reduceIte]
      exact ⟨hH, hV⟩
    · rcases p with ⟨pv, hpv⟩; rcases q with ⟨qv, hqv⟩; rcases ch with ⟨cv, hcv⟩
      interval_cases pv <;> interval_cases qv <;> interval_cases cv <;> simp [mkConst]

-- Master cardinality theorem for all M >= 2, W >= 2!
theorem card_validGrid {M W : ℕ} (hM : 2 ≤ M) (hW : 2 ≤ W) :
    (Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => validGrid A)).card =
      hStarCount M + hStarCount W - 8 := by
  let H := Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => isHStar A)
  let V := Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => isVStar A)
  have heq : Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => validGrid A) = H ∪ V := by
    ext A; simp only [H, V, Finset.mem_union]
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact validGrid_iff hM hW A
  have hV_card : V.card = hStarCount W := by
    rw [← card_hStar hW hM]
    refine Finset.card_bij (fun A _ j i => A i j) ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_filter] at hA ⊢
      exact ⟨Finset.mem_univ _, hA.2⟩
    · intro A1 _ A2 _ h; funext i j; exact congr_fun (congr_fun h j) i
    · intro B hB
      rw [Finset.mem_filter] at hB
      refine ⟨fun i j => B j i, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hB.2⟩
  have hI_card : (H ∩ V).card = 8 := by
    have : H ∩ V = Finset.univ.filter (fun A : Fin M → Fin W → Fin 3 => isHStar A ∧ isVStar A) := by
      ext A; simp only [H, V, Finset.mem_inter]
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
    rw [this]; exact card_inter_hStar_vStar hM hW
  have hH_card : H.card = hStarCount M := card_hStar hM hW
  have hu := Finset.card_union_add_card_inter H V
  rw [heq]
  omega

end
end General
end ClockDiff

namespace ProofA209725

open OMA.S_oeis_a209725 ClockDiff
open scoped Classical

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → a n = 3 * 2 ^ (n / 2 - 1) + 10) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → a n = 2 ^ ((n + 1) / 2) + 10) := by
  have ha : ∀ n : ℕ, 1 ≤ n → a n = (ClockDiff.hStarCount (n + 1) + ClockDiff.hStarCount 7 - 8) / 4 := by
    intro n hn
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have heq : Finset.univ.filter (isValid n) =
        Finset.univ.filter (fun A : Fin (n + 1) → Fin 7 → Fin 3 => ClockDiff.validGrid A) := by
      ext A; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h i hi j hj
        exact h ⟨i.1, by omega⟩ ⟨j.1, by omega⟩
      · intro h i j
        exact h i.castSucc (by simp) j.castSucc (by simp only [Fin.val_castSucc]; omega)
    rw [heq, ClockDiff.card_validGrid (by omega) (by omega)]
  have h7 : ClockDiff.hStarCount 7 = 48 := by decide
  constructor
  · rintro n hn ⟨m, rfl⟩
    rw [ha (m + m) hn, h7]
    unfold ClockDiff.hStarCount
    have hmod : ¬ (m + m + 1) % 2 = 0 := by omega
    rw [if_neg hmod]
    have hdiv1 : (m + m + 1) / 2 = m := by omega
    have hdiv2 : (m + m) / 2 = m := by omega
    rw [hdiv1, hdiv2]
    have hm : 1 ≤ m := by omega
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have hm1 : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm1]
      rw [pow_succ']
    rw [hpow]; omega
  · rintro n hn ⟨m, rfl⟩
    rw [ha (2 * m + 1) hn, h7]
    unfold ClockDiff.hStarCount
    have hmod : (2 * m + 1 + 1) % 2 = 0 := by omega
    rw [if_pos hmod]
    have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [hdiv1]; omega

end ProofA209725

theorem OMA.solution : type_of% @OMA.S_oeis_a209725.main :=
  ProofA209725.main
