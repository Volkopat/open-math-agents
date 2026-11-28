import OMAStatements.S_oeis_a122226

namespace OeisA122226

open Finset

private abbrev Site := OMA.S_oeis_a122226.Site
private abbrev Center := OMA.S_oeis_a122226.Center
private abbrev unitStep := OMA.S_oeis_a122226.unitStep

/- Section 1: Axial quadratic form Q, unit steps on ZMod 6, and D6 symmetries -/

private def Q (x y : ℝ) : ℝ := x ^ 2 + x * y + y ^ 2

private def Qp (u : Center) : ℝ := Q u.1 u.2

private def toR (p : Site) : Center := ((p.1 : ℝ), (p.2 : ℝ))

private def subR (p : Site) (o : Center) : Center := ((p.1 : ℝ) - o.1, (p.2 : ℝ) - o.2)

private lemma Q_nonneg (x y : ℝ) : 0 ≤ Q x y := by
  have h : 4 * Q x y = (2 * x + y) ^ 2 + 3 * y ^ 2 := by unfold Q; ring
  nlinarith

private lemma Qp_nonneg (u : Center) : 0 ≤ Qp u := Q_nonneg u.1 u.2

private lemma Q_convex2 {x1 y1 x2 y2 w1 w2 R : ℝ}
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hsum : w1 + w2 = 1)
    (h1 : Q x1 y1 ≤ R) (h2 : Q x2 y2 ≤ R) :
    Q (w1 * x1 + w2 * x2) (w1 * y1 + w2 * y2) ≤ R := by
  have hq : 0 ≤ w1 * w2 * Q (x1 - x2) (y1 - y2) :=
    mul_nonneg (mul_nonneg hw1 hw2) (Q_nonneg _ _)
  have h1' : w1 * Q x1 y1 ≤ w1 * R := mul_le_mul_of_nonneg_left h1 hw1
  have h2' : w2 * Q x2 y2 ≤ w2 * R := mul_le_mul_of_nonneg_left h2 hw2
  have hid : w1 * Q x1 y1 + w2 * Q x2 y2 -
      Q (w1 * x1 + w2 * x2) (w1 * y1 + w2 * y2) =
      w1 * w2 * Q (x1 - x2) (y1 - y2) := by
    have hw2' : w2 = 1 - w1 := by linarith
    subst hw2'
    unfold Q
    ring
  have hR : w1 * R + w2 * R = R := by linear_combination R * hsum
  linarith

private lemma Q_convex3 {x1 y1 x2 y2 x3 y3 w1 w2 w3 R : ℝ}
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hsum : w1 + w2 + w3 = 1)
    (h1 : Q x1 y1 ≤ R) (h2 : Q x2 y2 ≤ R) (h3 : Q x3 y3 ≤ R) :
    Q (w1 * x1 + w2 * x2 + w3 * x3) (w1 * y1 + w2 * y2 + w3 * y3) ≤ R := by
  have h12 : 0 ≤ w1 * w2 * Q (x1 - x2) (y1 - y2) :=
    mul_nonneg (mul_nonneg hw1 hw2) (Q_nonneg _ _)
  have h13 : 0 ≤ w1 * w3 * Q (x1 - x3) (y1 - y3) :=
    mul_nonneg (mul_nonneg hw1 hw3) (Q_nonneg _ _)
  have h23 : 0 ≤ w2 * w3 * Q (x2 - x3) (y2 - y3) :=
    mul_nonneg (mul_nonneg hw2 hw3) (Q_nonneg _ _)
  have h1' : w1 * Q x1 y1 ≤ w1 * R := mul_le_mul_of_nonneg_left h1 hw1
  have h2' : w2 * Q x2 y2 ≤ w2 * R := mul_le_mul_of_nonneg_left h2 hw2
  have h3' : w3 * Q x3 y3 ≤ w3 * R := mul_le_mul_of_nonneg_left h3 hw3
  have hid : w1 * Q x1 y1 + w2 * Q x2 y2 + w3 * Q x3 y3 -
      Q (w1 * x1 + w2 * x2 + w3 * x3) (w1 * y1 + w2 * y2 + w3 * y3) =
      w1 * w2 * Q (x1 - x2) (y1 - y2) +
      w1 * w3 * Q (x1 - x3) (y1 - y3) +
      w2 * w3 * Q (x2 - x3) (y2 - y3) := by
    have hw3' : w3 = 1 - w1 - w2 := by linarith
    subst hw3'
    unfold Q
    ring
  have hR : w1 * R + w2 * R + w3 * R = R := by linear_combination R * hsum
  linarith

private def dir : ZMod 6 → Site
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (-1, 1)
  | ⟨3, _⟩ => (-1, 0)
  | ⟨4, _⟩ => (0, -1)
  | ⟨5, _⟩ => (1, -1)

private lemma dir_ne_zero (d : ZMod 6) : dir d ≠ (0, 0) := by
  fin_cases d <;> decide

private lemma dir_inj {a b : ZMod 6} (h : dir a = dir b) : a = b := by
  revert a b h; decide

private lemma dir_add_three (d : ZMod 6) : dir (d + 3) = -dir d := by
  fin_cases d <;> decide

private lemma dir_sub_one_sub (d : ZMod 6) : dir (d - 1) - dir d = dir (d + 4) := by
  fin_cases d <;> decide

private lemma dir_add_two_eq (d : ZMod 6) : dir (d + 2) = dir (d + 1) - dir d := by
  fin_cases d <;> decide

private lemma dir_add_four_eq (d : ZMod 6) : dir (d + 4) = dir (d + 5) - dir d := by
  fin_cases d <;> decide

private lemma dir_add_three_add_five (d : ZMod 6) : dir (d + 3) + dir (d + 5) = dir (d + 4) := by
  fin_cases d <;> decide

private lemma unitStep_symm {p q : Site} (h : unitStep p q) : unitStep q p := by
  unfold unitStep OMA.S_oeis_a122226.unitStep at h ⊢
  dsimp only at h ⊢
  nlinarith

private lemma unitStep_add_dir (p : Site) (d : ZMod 6) : unitStep p (p + dir d) := by
  unfold unitStep OMA.S_oeis_a122226.unitStep
  dsimp only [Prod.fst_add, Prod.snd_add]
  fin_cases d <;> dsimp [dir] <;> ring

private lemma zmod6_cases (c : ZMod 6) :
    c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
  revert c; decide

private lemma unitStep_iff_exists_dir (p q : Site) :
    unitStep p q ↔ ∃ d : ZMod 6, q = p + dir d := by
  constructor
  · intro h
    unfold unitStep OMA.S_oeis_a122226.unitStep at h
    dsimp only at h
    set x := p.1 - q.1
    set y := p.2 - q.2
    have hx_def : x = p.1 - q.1 := rfl
    have hy_def : y = p.2 - q.2 := rfl
    have h4 : (2 * x + y) ^ 2 + 3 * y ^ 2 = 4 := by nlinarith
    have hy1 : -1 ≤ y := by nlinarith
    have hy2 : y ≤ 1 := by nlinarith
    have hx1 : -1 ≤ x := by nlinarith
    have hx2 : x ≤ 1 := by nlinarith
    interval_cases y <;> interval_cases x <;> try (norm_num at h4; done)
    · refine ⟨1, Prod.ext (by dsimp [dir]; omega) (by dsimp [dir]; omega)⟩
    · refine ⟨2, Prod.ext (by dsimp [dir]; omega) (by dsimp [dir]; omega)⟩
    · refine ⟨0, Prod.ext (by dsimp [dir]; omega) (by dsimp [dir]; omega)⟩
    · refine ⟨3, Prod.ext (by dsimp [dir]; omega) (by dsimp [dir]; omega)⟩
    · refine ⟨5, Prod.ext (by dsimp [dir]; omega) (by dsimp [dir]; omega)⟩
    · refine ⟨4, Prod.ext (by dsimp [dir]; omega) (by dsimp [dir]; omega)⟩
  · rintro ⟨d, rfl⟩
    exact unitStep_add_dir p d

private lemma unitStep_dir_iff (a b : ZMod 6) :
    unitStep (dir a) (dir b) ↔ b = a + 1 ∨ b = a - 1 := by
  unfold unitStep OMA.S_oeis_a122226.unitStep
  revert a b; decide

private lemma not_unitStep_triangle_dir (a b c : ZMod 6) :
    ¬ (unitStep (dir a) (dir b) ∧ unitStep (dir b) (dir c) ∧ unitStep (dir c) (dir a)) := by
  rw [unitStep_dir_iff, unitStep_dir_iff, unitStep_dir_iff]
  revert a b c; decide

private def rotR (u : Center) : Center := (-u.2, u.1 + u.2)
private def refR (u : Center) : Center := (u.2, u.1)
private def rotS (p : Site) : Site := (-p.2, p.1 + p.2)
private def refS (p : Site) : Site := (p.2, p.1)

private lemma Qp_rotR (u : Center) : Qp (rotR u) = Qp u := by
  unfold Qp Q rotR; ring

private lemma Qp_refR (u : Center) : Qp (refR u) = Qp u := by
  unfold Qp Q refR; ring

private lemma rotS_dir (d : ZMod 6) : rotS (dir d) = dir (d + 1) := by
  fin_cases d <;> decide

private lemma refS_dir (d : ZMod 6) : refS (dir d) = dir (1 - d) := by
  fin_cases d <;> decide

private lemma rotR_add (a1 a2 b1 b2 : ℝ) : rotR (a1 + b1, a2 + b2) =
    ((rotR (a1, a2)).1 + (rotR (b1, b2)).1, (rotR (a1, a2)).2 + (rotR (b1, b2)).2) := by
  ext <;> simp [rotR] <;> ring

private lemma refR_add (a1 a2 b1 b2 : ℝ) : refR (a1 + b1, a2 + b2) =
    ((refR (a1, a2)).1 + (refR (b1, b2)).1, (refR (a1, a2)).2 + (refR (b1, b2)).2) := by
  ext <;> simp [refR]

private lemma rotR_dir (d : ZMod 6) :
    rotR (((dir d).1 : ℝ), ((dir d).2 : ℝ)) = (((dir (d + 1)).1 : ℝ), ((dir (d + 1)).2 : ℝ)) := by
  have h := rotS_dir d
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  ext
  · simp only [rotR, rotS] at h1 ⊢; exact_mod_cast h1
  · simp only [rotR, rotS] at h2 ⊢; exact_mod_cast h2

private lemma refR_dir (d : ZMod 6) :
    refR (((dir d).1 : ℝ), ((dir d).2 : ℝ)) = (((dir (1 - d)).1 : ℝ), ((dir (1 - d)).2 : ℝ)) := by
  have h := refS_dir d
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  ext
  · simp only [refR, refS] at h1 ⊢; exact_mod_cast h1
  · simp only [refR, refS] at h2 ⊢; exact_mod_cast h2

private def rotPowR : ℕ → Center → Center
  | 0, u => u
  | m + 1, u => rotR (rotPowR m u)

private lemma Qp_rotPowR (m : ℕ) (u : Center) : Qp (rotPowR m u) = Qp u := by
  induction m with
  | zero => rfl
  | succ m ih => simp [rotPowR, Qp_rotR, ih]

private lemma rotPowR_add (m : ℕ) (a1 a2 b1 b2 : ℝ) :
    rotPowR m (a1 + b1, a2 + b2) =
      ((rotPowR m (a1, a2)).1 + (rotPowR m (b1, b2)).1,
       (rotPowR m (a1, a2)).2 + (rotPowR m (b1, b2)).2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rotPowR, ih]
    exact rotR_add _ _ _ _

private lemma rotPowR_smul (m : ℕ) (c : ℝ) (u : Center) :
    rotPowR m (c * u.1, c * u.2) = (c * (rotPowR m u).1, c * (rotPowR m u).2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rotPowR, ih, rotR]
    ext <;> ring

private lemma rotPowR_dir (m : ℕ) (d : ZMod 6) :
    rotPowR m (((dir d).1 : ℝ), ((dir d).2 : ℝ)) =
      (((dir (d + (m : ZMod 6))).1 : ℝ), ((dir (d + (m : ZMod 6))).2 : ℝ)) := by
  induction m with
  | zero => simp [rotPowR]
  | succ m ih =>
    simp only [rotPowR, ih, rotR_dir, Nat.cast_succ]
    have : d + (m : ZMod 6) + 1 = d + ((m : ZMod 6) + 1) := by ring
    rw [this]

private lemma refR_smul (c : ℝ) (u : Center) :
    refR (c * u.1, c * u.2) = (c * (refR u).1, c * (refR u).2) := by
  ext <;> simp [refR]

/- Section 2: Fundamental sector and unit-disk triangle coverage -/

private lemma exists_rotPow_first_quad (u : Center) :
    ∃ m : ℕ, 0 ≤ (rotPowR m u).1 ∧ 0 ≤ (rotPowR m u).2 := by
  rcases u with ⟨a, b⟩
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · exact ⟨0, ha, hb⟩
    · by_cases hab : 0 ≤ a + b
      · refine ⟨1, ?_, ?_⟩ <;> simp [rotPowR, rotR] <;> linarith
      · refine ⟨2, ?_, ?_⟩ <;> simp [rotPowR, rotR] <;> linarith
  · by_cases hb : b ≤ 0
    · refine ⟨3, ?_, ?_⟩ <;> simp [rotPowR, rotR] <;> linarith
    · by_cases hab : 0 ≤ a + b
      · refine ⟨5, ?_, ?_⟩ <;> simp [rotPowR, rotR] <;> linarith
      · refine ⟨4, ?_, ?_⟩ <;> simp [rotPowR, rotR] <;> linarith

private lemma exists_d6_sector (u : Center) :
    ∃ (b : Bool) (m : ℕ),
      let v := if b then refR (rotPowR m u) else rotPowR m u
      0 ≤ v.2 ∧ v.2 ≤ v.1 := by
  rcases exists_rotPow_first_quad u with ⟨m, h1, h2⟩
  by_cases hle : (rotPowR m u).2 ≤ (rotPowR m u).1
  · exact ⟨false, m, h2, hle⟩
  · refine ⟨true, m, ?_, ?_⟩ <;> simp [refR] <;> linarith

private lemma D1_exists_three (o : Center) :
    ∃ T : Finset Site, 3 ≤ T.card ∧ ∀ p ∈ T, Qp (subR p o) ≤ 1 := by
  set a : ℤ := ⌊o.1⌋
  set b : ℤ := ⌊o.2⌋
  set s : ℝ := o.1 - (a : ℝ)
  set t : ℝ := o.2 - (b : ℝ)
  have hs0 : 0 ≤ s := sub_nonneg.mpr (Int.floor_le o.1)
  have hs1 : s < 1 := by
    have := Int.lt_floor_add_one o.1
    linarith
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le o.2)
  have ht1 : t < 1 := by
    have := Int.lt_floor_add_one o.2
    linarith
  by_cases hst : s + t ≤ 1
  · refine ⟨{(a, b), (a + 1, b), (a, b + 1)}, ?_, ?_⟩
    · have h12 : ((a, b) : Site) ≠ (a + 1, b) := by intro h; simp at h
      have h13 : ((a, b) : Site) ≠ (a, b + 1) := by intro h; simp at h
      have h23 : ((a + 1, b) : Site) ≠ (a, b + 1) := by intro h; simp at h
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp only [Qp, Q, subR, Int.cast_add, Int.cast_one] <;> nlinarith
  · refine ⟨{(a + 1, b + 1), (a, b + 1), (a + 1, b)}, ?_, ?_⟩
    · have h12 : ((a + 1, b + 1) : Site) ≠ (a, b + 1) := by intro h; simp at h
      have h13 : ((a + 1, b + 1) : Site) ≠ (a + 1, b) := by intro h; simp at h
      have h23 : ((a, b + 1) : Site) ≠ (a + 1, b) := by intro h; simp at h
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp only [Qp, Q, subR, Int.cast_add, Int.cast_one] <;> nlinarith

/- Section 3: Onion layers K_k(o, r), S_k, and iterated interior identity -/

private def inK0 (k : ℕ) (r : ℝ) (u : Center) : Prop :=
  ∀ d : ZMod 6, Q (u.1 + (k : ℝ) * (dir d).1) (u.2 + (k : ℝ) * (dir d).2) ≤ r ^ 2

private lemma inK0_rotR {k : ℕ} {r : ℝ} {u : Center} (h : inK0 k r u) :
    inK0 k r (rotR u) := by
  intro d
  have hd := h (d - 1)
  have hrot : Qp (rotR (u.1 + (k : ℝ) * (dir (d - 1)).1,
      u.2 + (k : ℝ) * (dir (d - 1)).2)) =
      Q (u.1 + (k : ℝ) * (dir (d - 1)).1) (u.2 + (k : ℝ) * (dir (d - 1)).2) := Qp_rotR _
  have hlin : rotR (u.1 + (k : ℝ) * (dir (d - 1)).1, u.2 + (k : ℝ) * (dir (d - 1)).2) =
      ((rotR u).1 + (k : ℝ) * (dir d).1, (rotR u).2 + (k : ℝ) * (dir d).2) := by
    have hr := rotR_dir (d - 1)
    have hdm : d - 1 + 1 = d := by ring
    rw [hdm] at hr
    have h1 := congrArg Prod.fst hr
    have h2 := congrArg Prod.snd hr
    simp only [rotR] at h1 h2 ⊢
    ext
    · dsimp only; linear_combination (k : ℝ) * h1
    · dsimp only; linear_combination (k : ℝ) * h2
  have hq : Q ((rotR u).1 + (k : ℝ) * (dir d).1) ((rotR u).2 + (k : ℝ) * (dir d).2) =
      Qp ((rotR u).1 + (k : ℝ) * (dir d).1, (rotR u).2 + (k : ℝ) * (dir d).2) := rfl
  rw [hq, ← hlin, hrot]
  exact hd

private lemma inK0_rotPowR (m : ℕ) {k : ℕ} {r : ℝ} {u : Center} (h : inK0 k r u) :
    inK0 k r (rotPowR m u) := by
  induction m with
  | zero => exact h
  | succ m ih => exact inK0_rotR ih

private lemma inK0_refR {k : ℕ} {r : ℝ} {u : Center} (h : inK0 k r u) :
    inK0 k r (refR u) := by
  intro d
  have hd := h (1 - d)
  have href : Qp (refR (u.1 + (k : ℝ) * (dir (1 - d)).1,
      u.2 + (k : ℝ) * (dir (1 - d)).2)) =
      Q (u.1 + (k : ℝ) * (dir (1 - d)).1) (u.2 + (k : ℝ) * (dir (1 - d)).2) := Qp_refR _
  have hlin : refR (u.1 + (k : ℝ) * (dir (1 - d)).1, u.2 + (k : ℝ) * (dir (1 - d)).2) =
      ((refR u).1 + (k : ℝ) * (dir d).1, (refR u).2 + (k : ℝ) * (dir d).2) := by
    have hr := refR_dir (1 - d)
    have hdm : 1 - (1 - d) = d := by ring
    rw [hdm] at hr
    have h1 := congrArg Prod.fst hr
    have h2 := congrArg Prod.snd hr
    simp only [refR] at h1 h2 ⊢
    ext
    · dsimp only; linear_combination (k : ℝ) * h1
    · dsimp only; linear_combination (k : ℝ) * h2
  have hq : Q ((refR u).1 + (k : ℝ) * (dir d).1) ((refR u).2 + (k : ℝ) * (dir d).2) =
      Qp ((refR u).1 + (k : ℝ) * (dir d).1, (refR u).2 + (k : ℝ) * (dir d).2) := rfl
  rw [hq, ← hlin, href]
  exact hd

private lemma inK0_iff_rotPowR (m : ℕ) {k : ℕ} {r : ℝ} {u : Center} :
    inK0 k r (rotPowR m u) ↔ inK0 k r u := by
  constructor
  · intro h
    have h6 : ∀ v : Center, rotPowR 6 v = v := by
      intro ⟨a, b⟩; ext <;> (simp only [rotPowR, rotR]; ring)
    have hcomp : ∀ a b v, rotPowR a (rotPowR b v) = rotPowR (a + b) v := by
      intro a b v
      induction a with
      | zero => simp [rotPowR]
      | succ a ih =>
        have : a + 1 + b = (a + b) + 1 := by omega
        rw [this]; simp [rotPowR, ih]
    have hm : rotPowR (6 - m % 6) (rotPowR m u) = u := by
      have hmod : ∀ q v, rotPowR (6 * q) v = v := by
        intro q v
        induction q with
        | zero => rfl
        | succ q ih =>
          have : 6 * (q + 1) = 6 + 6 * q := by omega
          rw [this, ← hcomp, ih, h6]
      rw [hcomp]
      have hdiv : 6 - m % 6 + m = 6 * (m / 6 + 1) := by omega
      rw [hdiv, hmod]
    rw [← hm]
    exact inK0_rotPowR (6 - m % 6) h
  · exact inK0_rotPowR m

private lemma inK0_iff_refR {k : ℕ} {r : ℝ} {u : Center} :
    inK0 k r (refR u) ↔ inK0 k r u := by
  constructor
  · intro h
    have : refR (refR u) = u := by ext <;> simp [refR]
    rw [← this]
    exact inK0_refR h
  · exact inK0_refR

private lemma inK0_Q_le {k : ℕ} {r : ℝ} {u : Center} (h : inK0 k r u) :
    Qp u ≤ r ^ 2 := by
  have h0 := h 0
  have h3 := h 3
  simp only [dir, Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero] at h0
  have h3' : Q (u.1 - (k : ℝ)) u.2 ≤ r ^ 2 := by
    have : dir (3 : ZMod 6) = (-1, 0) := by decide
    rw [this] at h3
    simpa [sub_eq_add_neg] using h3
  have havg := Q_convex2 (w1 := 1 / 2) (w2 := 1 / 2) (by norm_num) (by norm_num) (by norm_num) h0 h3'
  have hx : 1 / 2 * (u.1 + (k : ℝ)) + 1 / 2 * (u.1 - (k : ℝ)) = u.1 := by ring
  have hy : 1 / 2 * u.2 + 1 / 2 * u.2 = u.2 := by ring
  rw [hx, hy] at havg
  exact havg

private lemma inK0_of_Q_le {k : ℕ} {ρ r : ℝ} {u : Center}
    (hρ : 0 ≤ ρ) (hr : (k : ℝ) + ρ ≤ r) (hu : Qp u ≤ ρ ^ 2) :
    inK0 k r u := by
  rcases u with ⟨x, y⟩
  unfold Qp Q at hu
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hB1 : 2 * x + y ≤ 2 * ρ := by nlinarith [sq_nonneg y]
  have hB2 : -(2 * x + y) ≤ 2 * ρ := by nlinarith [sq_nonneg y]
  have hB3 : x + 2 * y ≤ 2 * ρ := by nlinarith [sq_nonneg x]
  have hB4 : -(x + 2 * y) ≤ 2 * ρ := by nlinarith [sq_nonneg x]
  have hB5 : y - x ≤ 2 * ρ := by nlinarith [sq_nonneg (x + y)]
  have hB6 : x - y ≤ 2 * ρ := by nlinarith [sq_nonneg (x + y)]
  intro d
  fin_cases d <;> dsimp only [dir] <;> unfold Q <;> norm_num <;> nlinarith

private lemma inK0_zero_iff (r : ℝ) (u : Center) : inK0 0 r u ↔ Qp u ≤ r ^ 2 := by
  simp [inK0, Qp]

private lemma inK0_succ_iff (k : ℕ) (r : ℝ) (u : Center) :
    inK0 (k + 1) r u ↔ ∀ j : ZMod 6, inK0 k r (u.1 + (dir j).1, u.2 + (dir j).2) := by
  constructor
  · intro h j d
    dsimp only
    by_cases hk0 : k = 0
    · subst hk0
      simpa using h j
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0)
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      obtain ⟨c, hc⟩ : ∃ c : ZMod 6, j = d + c := ⟨j - d, by ring⟩
      subst hc
      have hstep : ∀ (a : ZMod 6),
          Q (u.1 + ((k : ℝ) + 1) * (dir a).1) (u.2 + ((k : ℝ) + 1) * (dir a).2) ≤ r ^ 2 := by
        intro a; simpa [Nat.cast_add, Nat.cast_one] using h a
      rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl
      · have heq1 : u.1 + (dir (d + 0)).1 + (k : ℝ) * (dir d).1 =
            u.1 + ((k : ℝ) + 1) * (dir d).1 := by simp; ring
        have heq2 : u.2 + (dir (d + 0)).2 + (k : ℝ) * (dir d).2 =
            u.2 + ((k : ℝ) + 1) * (dir d).2 := by simp; ring
        rw [heq1, heq2]; exact hstep d
      · have hcv := Q_convex2 (w1 := 1 / ((k : ℝ) + 1)) (w2 := (k : ℝ) / ((k : ℝ) + 1))
          (by positivity) (by positivity) (by field_simp; ring) (hstep (d + 1)) (hstep d)
        have heq1 : 1 / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir (d + 1)).1) +
            (k : ℝ) / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir d).1) =
            u.1 + (dir (d + 1)).1 + (k : ℝ) * (dir d).1 := by field_simp; ring
        have heq2 : 1 / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir (d + 1)).2) +
            (k : ℝ) / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir d).2) =
            u.2 + (dir (d + 1)).2 + (k : ℝ) * (dir d).2 := by field_simp; ring
        rw [heq1, heq2] at hcv; exact hcv
      · have hcv := Q_convex3
          (w1 := 1 / ((k : ℝ) + 1))
          (w2 := (2 * (k : ℝ) - 1) / (2 * ((k : ℝ) + 1)))
          (w3 := 1 / (2 * ((k : ℝ) + 1)))
          (by positivity)
          (div_nonneg (by linarith) (by positivity))
          (by positivity)
          (by field_simp; ring)
          (hstep (d + 1)) (hstep d) (hstep (d + 3))
        have hd2 := dir_add_two_eq d
        have hd3 := dir_add_three d
        have h21 : ((dir (d + 2)).1 : ℝ) = ((dir (d + 1)).1 : ℝ) - ((dir d).1 : ℝ) := by
          have := congrArg Prod.fst hd2; exact_mod_cast this
        have h22 : ((dir (d + 2)).2 : ℝ) = ((dir (d + 1)).2 : ℝ) - ((dir d).2 : ℝ) := by
          have := congrArg Prod.snd hd2; exact_mod_cast this
        have h31 : ((dir (d + 3)).1 : ℝ) = -((dir d).1 : ℝ) := by
          have := congrArg Prod.fst hd3; exact_mod_cast this
        have h32 : ((dir (d + 3)).2 : ℝ) = -((dir d).2 : ℝ) := by
          have := congrArg Prod.snd hd3; exact_mod_cast this
        have heq1 : 1 / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir (d + 1)).1) +
            (2 * (k : ℝ) - 1) / (2 * ((k : ℝ) + 1)) * (u.1 + ((k : ℝ) + 1) * (dir d).1) +
            1 / (2 * ((k : ℝ) + 1)) * (u.1 + ((k : ℝ) + 1) * (dir (d + 3)).1) =
            u.1 + (dir (d + 2)).1 + (k : ℝ) * (dir d).1 := by
          rw [h21, h31]; field_simp; ring
        have heq2 : 1 / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir (d + 1)).2) +
            (2 * (k : ℝ) - 1) / (2 * ((k : ℝ) + 1)) * (u.2 + ((k : ℝ) + 1) * (dir d).2) +
            1 / (2 * ((k : ℝ) + 1)) * (u.2 + ((k : ℝ) + 1) * (dir (d + 3)).2) =
            u.2 + (dir (d + 2)).2 + (k : ℝ) * (dir d).2 := by
          rw [h22, h32]; field_simp; ring
        rw [heq1, heq2] at hcv; exact hcv
      · have hcv := Q_convex2 (w1 := (k : ℝ) / ((k : ℝ) + 1)) (w2 := 1 / ((k : ℝ) + 1))
          (by positivity) (by positivity) (by field_simp) (hstep d) (hstep (d + 3))
        have hd3 := dir_add_three d
        have h31 : ((dir (d + 3)).1 : ℝ) = -((dir d).1 : ℝ) := by
          have := congrArg Prod.fst hd3; exact_mod_cast this
        have h32 : ((dir (d + 3)).2 : ℝ) = -((dir d).2 : ℝ) := by
          have := congrArg Prod.snd hd3; exact_mod_cast this
        have heq1 : (k : ℝ) / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir d).1) +
            1 / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir (d + 3)).1) =
            u.1 + (dir (d + 3)).1 + (k : ℝ) * (dir d).1 := by
          rw [h31]; field_simp; ring
        have heq2 : (k : ℝ) / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir d).2) +
            1 / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir (d + 3)).2) =
            u.2 + (dir (d + 3)).2 + (k : ℝ) * (dir d).2 := by
          rw [h32]; field_simp; ring
        rw [heq1, heq2] at hcv; exact hcv
      · have hcv := Q_convex3
          (w1 := 1 / ((k : ℝ) + 1))
          (w2 := (2 * (k : ℝ) - 1) / (2 * ((k : ℝ) + 1)))
          (w3 := 1 / (2 * ((k : ℝ) + 1)))
          (by positivity)
          (div_nonneg (by linarith) (by positivity))
          (by positivity)
          (by field_simp; ring)
          (hstep (d + 5)) (hstep d) (hstep (d + 3))
        have hd4 := dir_add_four_eq d
        have hd3 := dir_add_three d
        have h41 : ((dir (d + 4)).1 : ℝ) = ((dir (d + 5)).1 : ℝ) - ((dir d).1 : ℝ) := by
          have := congrArg Prod.fst hd4; exact_mod_cast this
        have h42 : ((dir (d + 4)).2 : ℝ) = ((dir (d + 5)).2 : ℝ) - ((dir d).2 : ℝ) := by
          have := congrArg Prod.snd hd4; exact_mod_cast this
        have h31 : ((dir (d + 3)).1 : ℝ) = -((dir d).1 : ℝ) := by
          have := congrArg Prod.fst hd3; exact_mod_cast this
        have h32 : ((dir (d + 3)).2 : ℝ) = -((dir d).2 : ℝ) := by
          have := congrArg Prod.snd hd3; exact_mod_cast this
        have heq1 : 1 / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir (d + 5)).1) +
            (2 * (k : ℝ) - 1) / (2 * ((k : ℝ) + 1)) * (u.1 + ((k : ℝ) + 1) * (dir d).1) +
            1 / (2 * ((k : ℝ) + 1)) * (u.1 + ((k : ℝ) + 1) * (dir (d + 3)).1) =
            u.1 + (dir (d + 4)).1 + (k : ℝ) * (dir d).1 := by
          rw [h41, h31]; field_simp; ring
        have heq2 : 1 / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir (d + 5)).2) +
            (2 * (k : ℝ) - 1) / (2 * ((k : ℝ) + 1)) * (u.2 + ((k : ℝ) + 1) * (dir d).2) +
            1 / (2 * ((k : ℝ) + 1)) * (u.2 + ((k : ℝ) + 1) * (dir (d + 3)).2) =
            u.2 + (dir (d + 4)).2 + (k : ℝ) * (dir d).2 := by
          rw [h42, h32]; field_simp; ring
        rw [heq1, heq2] at hcv; exact hcv
      · have hcv := Q_convex2 (w1 := 1 / ((k : ℝ) + 1)) (w2 := (k : ℝ) / ((k : ℝ) + 1))
          (by positivity) (by positivity) (by field_simp; ring) (hstep (d + 5)) (hstep d)
        have heq1 : 1 / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir (d + 5)).1) +
            (k : ℝ) / ((k : ℝ) + 1) * (u.1 + ((k : ℝ) + 1) * (dir d).1) =
            u.1 + (dir (d + 5)).1 + (k : ℝ) * (dir d).1 := by field_simp; ring
        have heq2 : 1 / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir (d + 5)).2) +
            (k : ℝ) / ((k : ℝ) + 1) * (u.2 + ((k : ℝ) + 1) * (dir d).2) =
            u.2 + (dir (d + 5)).2 + (k : ℝ) * (dir d).2 := by field_simp; ring
        rw [heq1, heq2] at hcv; exact hcv
  · intro h d
    have hdd := h d d
    have heq1 : u.1 + ((k + 1 : ℕ) : ℝ) * (dir d).1 = u.1 + (dir d).1 + (k : ℝ) * (dir d).1 := by
      push_cast; ring
    have heq2 : u.2 + ((k + 1 : ℕ) : ℝ) * (dir d).2 = u.2 + (dir d).2 + (k : ℝ) * (dir d).2 := by
      push_cast; ring
    rw [heq1, heq2]
    exact hdd

private lemma inK0_mono {k : ℕ} {r : ℝ} {u : Center} (h : inK0 (k + 1) r u) :
    inK0 k r u := by
  have hall := (inK0_succ_iff k r u).mp h
  intro d
  have h0 := hall 0 d
  have h3 := hall 3 d
  have hd0 : dir (0 : ZMod 6) = (1, 0) := by decide
  have hd3 : dir (3 : ZMod 6) = (-1, 0) := by decide
  rw [hd0] at h0
  rw [hd3] at h3
  have hcv := Q_convex2 (w1 := 1 / 2) (w2 := 1 / 2) (by norm_num) (by norm_num) (by norm_num) h0 h3
  have hx : 1 / 2 * (u.1 + (1 : ℤ) + (k : ℝ) * (dir d).1) +
      1 / 2 * (u.1 + (-1 : ℤ) + (k : ℝ) * (dir d).1) = u.1 + (k : ℝ) * (dir d).1 := by
    push_cast; ring
  have hy : 1 / 2 * (u.2 + (0 : ℤ) + (k : ℝ) * (dir d).2) +
      1 / 2 * (u.2 + (0 : ℤ) + (k : ℝ) * (dir d).2) = u.2 + (k : ℝ) * (dir d).2 := by
    push_cast; ring
  rw [hx, hy] at hcv
  exact hcv

private noncomputable def layerFinset (k : ℕ) (o : Center) (r : ℝ) : Finset Site := by
  classical
  exact (Finset.Icc ⌊o.1 - 2 * r⌋ ⌈o.1 + 2 * r⌉ ×ˢ
         Finset.Icc ⌊o.2 - 2 * r⌋ ⌈o.2 + 2 * r⌉).filter fun p => inK0 k r (subR p o)

private lemma mem_layerFinset {k : ℕ} {o : Center} {r : ℝ} (hr : 0 ≤ r) (p : Site) :
    p ∈ layerFinset k o r ↔ inK0 k r (subR p o) := by
  classical
  unfold layerFinset
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro hp
    refine ⟨?_, hp⟩
    have hq := inK0_Q_le hp
    unfold Qp Q subR at hq
    have hx4 : 3 * ((p.1 : ℝ) - o.1) ^ 2 ≤ 4 * r ^ 2 := by
      nlinarith [sq_nonneg ((p.1 : ℝ) - o.1 + 2 * ((p.2 : ℝ) - o.2))]
    have hy4 : 3 * ((p.2 : ℝ) - o.2) ^ 2 ≤ 4 * r ^ 2 := by
      nlinarith [sq_nonneg (2 * ((p.1 : ℝ) - o.1) + ((p.2 : ℝ) - o.2))]
    have hx_lo : o.1 - 2 * r ≤ (p.1 : ℝ) := by nlinarith
    have hx_hi : (p.1 : ℝ) ≤ o.1 + 2 * r := by nlinarith
    have hy_lo : o.2 - 2 * r ≤ (p.2 : ℝ) := by nlinarith
    have hy_hi : (p.2 : ℝ) ≤ o.2 + 2 * r := by nlinarith
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨Int.floor_le_iff.mpr (by linarith [Int.floor_le (o.1 - 2 * r)]),
            Int.le_ceil_iff.mpr (by linarith)⟩,
           ⟨Int.floor_le_iff.mpr (by linarith [Int.floor_le (o.2 - 2 * r)]),
            Int.le_ceil_iff.mpr (by linarith)⟩⟩

private noncomputable def combInt (S : Finset Site) : Finset Site := by
  classical
  exact S.filter fun p => ∀ d : ZMod 6, p + dir d ∈ S

private noncomputable def combBdry (S : Finset Site) : Finset Site := by
  classical
  exact S \ combInt S

private lemma mem_combInt {S : Finset Site} {p : Site} :
    p ∈ combInt S ↔ p ∈ S ∧ ∀ d : ZMod 6, p + dir d ∈ S := by
  classical
  simp [combInt]

private lemma mem_combBdry {S : Finset Site} {p : Site} :
    p ∈ combBdry S ↔ p ∈ S ∧ ∃ d : ZMod 6, p + dir d ∉ S := by
  classical
  simp only [combBdry, combInt, Finset.mem_sdiff, Finset.mem_filter, not_and, not_forall]
  tauto

private lemma layer_combInt (k : ℕ) (o : Center) {r : ℝ} (hr : 0 ≤ r) :
    combInt (layerFinset k o r) = layerFinset (k + 1) o r := by
  ext p
  rw [mem_combInt, mem_layerFinset hr, mem_layerFinset hr, inK0_succ_iff]
  constructor
  · rintro ⟨_, hall⟩ j
    have hj := (mem_layerFinset hr (p + dir j)).mp (hall j)
    have hsub : subR (p + dir j) o = ((subR p o).1 + (dir j).1, (subR p o).2 + (dir j).2) := by
      ext <;> simp [subR] <;> ring
    rwa [hsub] at hj
  · intro hall
    refine ⟨inK0_mono ((inK0_succ_iff k r (subR p o)).mpr hall), fun j => ?_⟩
    rw [mem_layerFinset hr]
    have hsub : subR (p + dir j) o = ((subR p o).1 + (dir j).1, (subR p o).2 + (dir j).2) := by
      ext <;> simp [subR] <;> ring
    rw [hsub]
    exact hall j

/- Section 4 & 5: Horizontal convexity, sector inward-triangle, and local connectivity -/

private def HorizConvex (S : Finset Site) : Prop :=
  ∀ x1 x x2 y : ℤ, (x1, y) ∈ S → (x2, y) ∈ S → x1 ≤ x → x ≤ x2 → (x, y) ∈ S

private lemma layer_horizConvex (k : ℕ) (o : Center) {r : ℝ} (hr : 0 ≤ r) :
    HorizConvex (layerFinset k o r) := by
  intro x1 x x2 y h1 h2 hle1 hle2
  rw [mem_layerFinset hr] at h1 h2 ⊢
  by_cases heq : x1 = x2
  · have : x = x1 := by omega
    subst this; exact h1
  · have hpos : (0 : ℝ) < (x2 : ℝ) - (x1 : ℝ) := by
      have : x1 < x2 := by omega
      exact_mod_cast (sub_pos.mpr this)
    set t : ℝ := ((x : ℝ) - (x1 : ℝ)) / ((x2 : ℝ) - (x1 : ℝ))
    have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast sub_nonneg.mpr hle1) hpos.le
    have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast sub_le_sub_right hle2 x1)
    intro d
    have hcv := Q_convex2 (w1 := 1 - t) (w2 := t) (by linarith) ht0 (by ring) (h1 d) (h2 d)
    have hx : (1 - t) * ((x1 : ℝ) - o.1 + (k : ℝ) * (dir d).1) +
        t * ((x2 : ℝ) - o.1 + (k : ℝ) * (dir d).1) =
        (x : ℝ) - o.1 + (k : ℝ) * (dir d).1 := by
      dsimp only [t]; field_simp; ring
    have hy : (1 - t) * ((y : ℝ) - o.2 + (k : ℝ) * (dir d).2) +
        t * ((y : ℝ) - o.2 + (k : ℝ) * (dir d).2) =
        (y : ℝ) - o.2 + (k : ℝ) * (dir d).2 := by ring
    simpa [subR, hx, hy] using hcv

private lemma step5_inward_e3 {k : ℕ} {r : ℝ} {u : Center}
    (hr : (k : ℝ) + 1 ≤ r) (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) (hin : inK0 k r u) :
    inK0 k r (u.1 - 1, u.2) := by
  rcases u with ⟨a, b⟩
  dsimp only at hu1 hu2 ⊢
  have hE : 2 * a + b ≤ 1 → a ^ 2 + a * b + b ^ 2 - 2 * a - b ≤ 0 := by
    intro hle; nlinarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hrk : ((k : ℝ) + 1) ^ 2 ≤ r ^ 2 := by nlinarith
  have hd0 := hin 0
  have hd1 := hin 1
  have hd3 := hin 3
  have hd5 := hin 5
  simp only [dir, Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero] at hd0
  have hd1' : Q a (b + (k : ℝ)) ≤ r ^ 2 := by
    have : dir (1 : ZMod 6) = (0, 1) := by decide
    rw [this] at hd1; simpa using hd1
  have hd3' : Q (a - (k : ℝ)) b ≤ r ^ 2 := by
    have : dir (3 : ZMod 6) = (-1, 0) := by decide
    rw [this] at hd3; simpa [sub_eq_add_neg] using hd3
  have hd5' : Q (a + (k : ℝ)) (b - (k : ℝ)) ≤ r ^ 2 := by
    have : dir (5 : ZMod 6) = (1, -1) := by decide
    rw [this] at hd5; simpa [sub_eq_add_neg] using hd5
  intro d
  fin_cases d <;> dsimp only [dir]
  · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero]
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.cast_zero, add_zero] at hd0 hrk ⊢
      by_cases h2 : 1 ≤ 2 * a + b
      · unfold Q at hd0 ⊢; nlinarith
      · have hle := hE (by linarith)
        unfold Q; nlinarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      have hcv := Q_convex2 (w1 := (2 * (k : ℝ) - 1) / (2 * (k : ℝ))) (w2 := 1 / (2 * (k : ℝ)))
        (div_nonneg (by linarith) (by positivity)) (by positivity) (by field_simp; ring) hd0 hd3'
      have hx : (2 * (k : ℝ) - 1) / (2 * (k : ℝ)) * (a + (k : ℝ)) +
          1 / (2 * (k : ℝ)) * (a - (k : ℝ)) = a - 1 + (k : ℝ) := by field_simp; ring
      have hy : (2 * (k : ℝ) - 1) / (2 * (k : ℝ)) * b + 1 / (2 * (k : ℝ)) * b = b := by
        field_simp; ring
      rw [hx, hy] at hcv; exact hcv
  · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero]
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.cast_zero, add_zero] at hd1' hrk ⊢
      by_cases h2 : 1 ≤ 2 * a + b
      · unfold Q at hd1' ⊢; nlinarith
      · have hle := hE (by linarith); unfold Q; nlinarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      unfold Q at hd1' ⊢; nlinarith
  · simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
    by_cases h2 : 1 ≤ 2 * a + b
    · unfold Q at hd1' ⊢; nlinarith
    · have hle := hE (by linarith)
      unfold Q; nlinarith
  · simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, mul_neg, mul_one, mul_zero, add_zero]
    by_cases h2 : 1 ≤ 2 * a + b
    · unfold Q at hd0 ⊢; nlinarith
    · have hle := hE (by linarith)
      unfold Q; nlinarith
  · simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, mul_neg, mul_one, mul_zero, add_zero]
    by_cases h2 : 1 ≤ 2 * a + b
    · unfold Q at hd1' ⊢; nlinarith
    · have hle := hE (by linarith)
      unfold Q; nlinarith
  · simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.cast_zero, add_zero] at hd0 hrk ⊢
      by_cases h2 : 1 ≤ 2 * a + b
      · unfold Q at hd0 ⊢; nlinarith
      · have hle := hE (by linarith); unfold Q; nlinarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      unfold Q at hd5' ⊢; nlinarith

private lemma step5_lateral_e5 {k : ℕ} {r : ℝ} {u : Center}
    (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) (hin : inK0 k r u) (hin0 : inK0 k r (u.1 + 1, u.2)) :
    inK0 k r (u.1 + 1, u.2 - 1) := by
  rcases u with ⟨a, b⟩
  dsimp only at hu1 hu2 ⊢
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  by_cases hk : k = 0
  · subst hk
    rw [inK0_zero_iff] at hin0 ⊢
    unfold Qp Q at hin0 ⊢
    nlinarith
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have h00 : Q (a + 1 + (k : ℝ)) b ≤ r ^ 2 := by
      have h := hin0 0; have : dir (0 : ZMod 6) = (1, 0) := by decide
      rw [this] at h; simpa using h
    have h01 : Q (a + 1) (b + (k : ℝ)) ≤ r ^ 2 := by
      have h := hin0 1; have : dir (1 : ZMod 6) = (0, 1) := by decide
      rw [this] at h; simpa using h
    have h04 : Q (a + 1) (b - (k : ℝ)) ≤ r ^ 2 := by
      have h := hin0 4; have : dir (4 : ZMod 6) = (0, -1) := by decide
      rw [this] at h; simpa [sub_eq_add_neg] using h
    have h2 : Q (a - (k : ℝ)) (b + (k : ℝ)) ≤ r ^ 2 := by
      have h := hin 2; have : dir (2 : ZMod 6) = (-1, 1) := by decide
      rw [this] at h; simpa [sub_eq_add_neg] using h
    have h3 : Q (a - (k : ℝ)) b ≤ r ^ 2 := by
      have h := hin 3; have : dir (3 : ZMod 6) = (-1, 0) := by decide
      rw [this] at h; simpa [sub_eq_add_neg] using h
    have h4 : Q a (b - (k : ℝ)) ≤ r ^ 2 := by
      have h := hin 4; have : dir (4 : ZMod 6) = (0, -1) := by decide
      rw [this] at h; simpa [sub_eq_add_neg] using h
    have h5 : Q (a + (k : ℝ)) (b - (k : ℝ)) ≤ r ^ 2 := by
      have h := hin 5; have : dir (5 : ZMod 6) = (1, -1) := by decide
      rw [this] at h; simpa [sub_eq_add_neg] using h
    intro d
    fin_cases d <;> dsimp only [dir]
    · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero]
      unfold Q at h00 ⊢; nlinarith
    · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero]
      have hcv := Q_convex2 (w1 := (2 * (k : ℝ) - 1) / (2 * (k : ℝ))) (w2 := 1 / (2 * (k : ℝ)))
        (div_nonneg (by linarith) (by positivity)) (by positivity) (by field_simp; ring) h01 h04
      have hx : (2 * (k : ℝ) - 1) / (2 * (k : ℝ)) * (a + 1) + 1 / (2 * (k : ℝ)) * (a + 1) = a + 1 := by
        field_simp; ring
      have hy : (2 * (k : ℝ) - 1) / (2 * (k : ℝ)) * (b + (k : ℝ)) +
          1 / (2 * (k : ℝ)) * (b - (k : ℝ)) = b - 1 + (k : ℝ) := by field_simp; ring
      rw [hx, hy] at hcv; exact hcv
    · simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
      have hcv := Q_convex2 (w1 := (2 * (k : ℝ) - 1) / (2 * (k : ℝ))) (w2 := 1 / (2 * (k : ℝ)))
        (div_nonneg (by linarith) (by positivity)) (by positivity) (by field_simp; ring) h2 h5
      have hx : (2 * (k : ℝ) - 1) / (2 * (k : ℝ)) * (a - (k : ℝ)) +
          1 / (2 * (k : ℝ)) * (a + (k : ℝ)) = a + 1 + -(k : ℝ) := by field_simp; ring
      have hy : (2 * (k : ℝ) - 1) / (2 * (k : ℝ)) * (b + (k : ℝ)) +
          1 / (2 * (k : ℝ)) * (b - (k : ℝ)) = b - 1 + (k : ℝ) := by field_simp; ring
      rw [hx, hy] at hcv; exact hcv
    · simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, mul_neg, mul_one, mul_zero, add_zero]
      have hcv := Q_convex2 (w1 := ((k : ℝ) - 1) / (k : ℝ)) (w2 := 1 / (k : ℝ))
        (div_nonneg (by linarith) (by positivity)) (by positivity) (by field_simp; ring) h3 h4
      have hx : ((k : ℝ) - 1) / (k : ℝ) * (a - (k : ℝ)) + 1 / (k : ℝ) * a = a + 1 + -(k : ℝ) := by
        field_simp; ring
      have hy : ((k : ℝ) - 1) / (k : ℝ) * b + 1 / (k : ℝ) * (b - (k : ℝ)) = b - 1 := by
        field_simp; ring
      rw [hx, hy] at hcv; exact hcv
    · simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, mul_neg, mul_one, mul_zero, add_zero]
      unfold Q at h01 ⊢; nlinarith
    · simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
      unfold Q at h00 ⊢; nlinarith

private def IsArc (A : ZMod 6 → Prop) : Prop :=
  (∃ d1 d2 : ZMod 6, d1 ≠ d2 ∧ A d1 ∧ A d2) ∧
  (∀ d1 d2 : ZMod 6, A d1 → ¬ A (d1 - 1) → A d2 → ¬ A (d2 - 1) → d1 = d2)

private def eval6 (f0 f1 f2 f3 f4 f5 : Bool) : ZMod 6 → Bool
  | ⟨0, _⟩ => f0
  | ⟨1, _⟩ => f1
  | ⟨2, _⟩ => f2
  | ⟨3, _⟩ => f3
  | ⟨4, _⟩ => f4
  | ⟨5, _⟩ => f5

private lemma eval6_decide (A : ZMod 6 → Prop) [DecidablePred A] (d : ZMod 6) :
    eval6 (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5)) d =
      decide (A d) := by
  fin_cases d <;> rfl

private lemma isArc_of_step5 {A : ZMod 6 → Prop}
    (h3 : A 3) (h4 : A 4) (h05 : A 0 → A 5) (h12 : A 1 → A 2) : IsArc A := by
  refine ⟨⟨3, 4, by decide, h3, h4⟩, fun d1 d2 ha1 hb1 ha2 hb2 => ?_⟩
  have h01 : (0 : ZMod 6) - 1 = 5 := by decide
  have h11 : (1 : ZMod 6) - 1 = 0 := by decide
  have h21 : (2 : ZMod 6) - 1 = 1 := by decide
  have h31 : (3 : ZMod 6) - 1 = 2 := by decide
  have h41 : (4 : ZMod 6) - 1 = 3 := by decide
  have h51 : (5 : ZMod 6) - 1 = 4 := by decide
  rcases zmod6_cases d1 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h01] at hb1; exact absurd (h05 ha1) hb1
  · rw [h11] at hb1
    rcases zmod6_cases d2 with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h01] at hb2; exact absurd (h05 ha2) hb2
    · rfl
    · rw [h21] at hb2; exact absurd ha1 hb2
    · rw [h31] at hb2; exact absurd (h12 ha1) hb2
    · rw [h41] at hb2; exact absurd h3 hb2
    · rw [h51] at hb2; exact absurd h4 hb2
  · rw [h21] at hb1
    rcases zmod6_cases d2 with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h01] at hb2; exact absurd (h05 ha2) hb2
    · exact absurd ha2 hb1
    · rfl
    · rw [h31] at hb2; exact absurd ha1 hb2
    · rw [h41] at hb2; exact absurd h3 hb2
    · rw [h51] at hb2; exact absurd h4 hb2
  · rw [h31] at hb1
    rcases zmod6_cases d2 with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h01] at hb2; exact absurd (h05 ha2) hb2
    · exact absurd (h12 ha2) hb1
    · exact absurd ha2 hb1
    · rfl
    · rw [h41] at hb2; exact absurd h3 hb2
    · rw [h51] at hb2; exact absurd h4 hb2
  · rw [h41] at hb1; exact absurd h3 hb1
  · rw [h51] at hb1; exact absurd h4 hb1

private lemma isArc_shift {A : ZMod 6 → Prop} (m : ZMod 6) (h : IsArc (fun d => A (d + m))) :
    IsArc A := by
  rcases h with ⟨⟨d1, d2, hne, h1, h2⟩, huniq⟩
  refine ⟨⟨d1 + m, d2 + m, fun heq => hne (by linear_combination heq), h1, h2⟩, ?_⟩
  intro a1 a2 ha1 hb1 ha2 hb2
  have heq := huniq (a1 - m) (a2 - m)
    (by simpa using ha1) (by simpa [sub_add_eq_add_sub, add_sub_assoc] using hb1)
    (by simpa using ha2) (by simpa [sub_add_eq_add_sub, add_sub_assoc] using hb2)
  linear_combination heq

private lemma isArc_end_unique {A : ZMod 6 → Prop} (h : IsArc A)
    {a1 a2 : ZMod 6} (ha1 : A a1) (hb1 : ¬ A (a1 + 1)) (ha2 : A a2) (hb2 : ¬ A (a2 + 1)) :
    a1 = a2 := by
  classical
  have key : ∀ (f0 f1 f2 f3 f4 f5 : Bool),
      (∀ d1 d2 : ZMod 6, eval6 f0 f1 f2 f3 f4 f5 d1 = true → eval6 f0 f1 f2 f3 f4 f5 (d1 - 1) = false →
        eval6 f0 f1 f2 f3 f4 f5 d2 = true → eval6 f0 f1 f2 f3 f4 f5 (d2 - 1) = false → d1 = d2) →
      (∀ e1 e2 : ZMod 6, eval6 f0 f1 f2 f3 f4 f5 e1 = true → eval6 f0 f1 f2 f3 f4 f5 (e1 + 1) = false →
        eval6 f0 f1 f2 f3 f4 f5 e2 = true → eval6 f0 f1 f2 f3 f4 f5 (e2 + 1) = false → e1 = e2) := by
    decide
  have hstart : ∀ d1 d2 : ZMod 6,
      eval6 (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5)) d1 = true →
      eval6 (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5)) (d1 - 1) = false →
      eval6 (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5)) d2 = true →
      eval6 (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5)) (d2 - 1) = false →
      d1 = d2 := by
    intro d1 d2 s1 s2 s3 s4
    rw [eval6_decide] at s1 s2 s3 s4
    exact h.2 d1 d2 (of_decide_eq_true s1) (of_decide_eq_false s2)
      (of_decide_eq_true s3) (of_decide_eq_false s4)
  have hend := key (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5)) hstart a1 a2
  rw [eval6_decide, eval6_decide, eval6_decide, eval6_decide] at hend
  exact hend (decide_eq_true ha1) (decide_eq_false hb1)
    (decide_eq_true ha2) (decide_eq_false hb2)

private lemma isArc_exists_start {A : ZMod 6 → Prop} (h : IsArc A) (hnot : ∃ d : ZMod 6, ¬ A d) :
    ∃ d : ZMod 6, A d ∧ ¬ A (d - 1) := by
  classical
  have key : ∀ (f0 f1 f2 f3 f4 f5 : Bool),
      (∃ d : ZMod 6, eval6 f0 f1 f2 f3 f4 f5 d = true) →
      (∃ d : ZMod 6, eval6 f0 f1 f2 f3 f4 f5 d = false) →
      (∃ d : ZMod 6, eval6 f0 f1 f2 f3 f4 f5 d = true ∧ eval6 f0 f1 f2 f3 f4 f5 (d - 1) = false) := by
    decide
  rcases h.1 with ⟨d1, _, _, hd1, _⟩
  rcases hnot with ⟨d0, hd0⟩
  have hex := key (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5))
    ⟨d1, by rw [eval6_decide]; exact decide_eq_true hd1⟩
    ⟨d0, by rw [eval6_decide]; exact decide_eq_false hd0⟩
  rcases hex with ⟨d, h1, h2⟩
  rw [eval6_decide] at h1 h2
  exact ⟨d, of_decide_eq_true h1, of_decide_eq_false h2⟩

private lemma isArc_no_isolated {A : ZMod 6 → Prop} (h : IsArc A) {d : ZMod 6}
    (hd : A d) (hm : ¬ A (d - 1)) (hp : ¬ A (d + 1)) : False := by
  classical
  have key : ∀ (f0 f1 f2 f3 f4 f5 : Bool),
      (∃ d1 d2 : ZMod 6, d1 ≠ d2 ∧ eval6 f0 f1 f2 f3 f4 f5 d1 = true ∧ eval6 f0 f1 f2 f3 f4 f5 d2 = true) →
      (∀ d1 d2 : ZMod 6, eval6 f0 f1 f2 f3 f4 f5 d1 = true → eval6 f0 f1 f2 f3 f4 f5 (d1 - 1) = false →
        eval6 f0 f1 f2 f3 f4 f5 d2 = true → eval6 f0 f1 f2 f3 f4 f5 (d2 - 1) = false → d1 = d2) →
      ∀ d : ZMod 6, ¬ (eval6 f0 f1 f2 f3 f4 f5 d = true ∧
        eval6 f0 f1 f2 f3 f4 f5 (d - 1) = false ∧ eval6 f0 f1 f2 f3 f4 f5 (d + 1) = false) := by
    decide
  rcases h.1 with ⟨d1, d2, hne, h1, h2⟩
  have hno := key (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3)) (decide (A 4)) (decide (A 5))
    ⟨d1, d2, hne, by rw [eval6_decide]; exact decide_eq_true h1,
                  by rw [eval6_decide]; exact decide_eq_true h2⟩
    (fun a b s1 s2 s3 s4 => by
      rw [eval6_decide] at s1 s2 s3 s4
      exact h.2 a b (of_decide_eq_true s1) (of_decide_eq_false s2)
        (of_decide_eq_true s3) (of_decide_eq_false s4))
    d
  rw [eval6_decide, eval6_decide, eval6_decide] at hno
  exact hno ⟨decide_eq_true hd, decide_eq_false hm, decide_eq_false hp⟩

private lemma isArc_gap_forces {A : ZMod 6 → Prop} (h : IsArc A) {a b c d : ZMod 6}
    (ha : A a) (hb : ¬ A b) (hc : ¬ A c) :
    (a = 1 ∧ b = 0 ∧ c = 3 ∧ (d = 4 ∨ d = 5) → ¬ A d) ∧
    (a = 0 ∧ b = 5 ∧ c = 2 ∧ (d = 3 ∨ d = 4) → ¬ A d) ∧
    (a = 0 ∧ b = 5 ∧ c = 3 ∧ d = 4 → ¬ A d) ∧
    (a = 3 ∧ b = 2 ∧ c = 5 ∧ (d = 0 ∨ d = 1) → ¬ A d) := by
  have h01 : (0 : ZMod 6) - 1 = 5 := by decide
  have h11 : (1 : ZMod 6) - 1 = 0 := by decide
  have h31 : (3 : ZMod 6) - 1 = 2 := by decide
  have h41 : (4 : ZMod 6) - 1 = 3 := by decide
  have h51 : (5 : ZMod 6) - 1 = 4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl, rfl, rfl | rfl⟩
    · intro h4; exact absurd (h.2 1 4 ha (h11.symm ▸ hb) h4 (h41.symm ▸ hc)) (by decide)
    · have h4 : ¬ A 4 := fun h4 => absurd (h.2 1 4 ha (h11.symm ▸ hb) h4 (h41.symm ▸ hc)) (by decide)
      intro h5; exact absurd (h.2 1 5 ha (h11.symm ▸ hb) h5 (h51.symm ▸ h4)) (by decide)
  · rintro ⟨rfl, rfl, rfl, rfl | rfl⟩
    · intro h3; exact absurd (h.2 0 3 ha (h01.symm ▸ hb) h3 (h31.symm ▸ hc)) (by decide)
    · have h3 : ¬ A 3 := fun h3 => absurd (h.2 0 3 ha (h01.symm ▸ hb) h3 (h31.symm ▸ hc)) (by decide)
      intro h4; exact absurd (h.2 0 4 ha (h01.symm ▸ hb) h4 (h41.symm ▸ h3)) (by decide)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    intro h4; exact absurd (h.2 0 4 ha (h01.symm ▸ hb) h4 (h41.symm ▸ hc)) (by decide)
  · rintro ⟨rfl, rfl, rfl, rfl | rfl⟩
    · intro h0; exact absurd (h.2 3 0 ha (h31.symm ▸ hb) h0 (h01.symm ▸ hc)) (by decide)
    · have h0 : ¬ A 0 := fun h0 => absurd (h.2 3 0 ha (h31.symm ▸ hb) h0 (h01.symm ▸ hc)) (by decide)
      intro h1; exact absurd (h.2 3 1 ha (h31.symm ▸ hb) h1 (h11.symm ▸ h0)) (by decide)

private lemma layer_locallyConn (k : ℕ) (o : Center) {r : ℝ} (hr : (k : ℝ) + 1 ≤ r) :
    ∀ p ∈ layerFinset k o r, IsArc (fun d => p + dir d ∈ layerFinset k o r) := by
  have hr0 : 0 ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) k]
  intro p hp
  rw [mem_layerFinset hr0] at hp
  rcases exists_rotPow_first_quad (subR p o) with ⟨m, h1, h2⟩
  set v := rotPowR m (subR p o)
  have hv : inK0 k r v := inK0_rotPowR m hp
  have htrans : ∀ d : ZMod 6,
      p + dir (d - (m : ZMod 6)) ∈ layerFinset k o r ↔
      inK0 k r (v.1 + (dir d).1, v.2 + (dir d).2) := by
    intro d
    rw [mem_layerFinset hr0, ← inK0_iff_rotPowR m]
    have hsub : subR (p + dir (d - (m : ZMod 6))) o =
        ((subR p o).1 + (dir (d - (m : ZMod 6))).1,
         (subR p o).2 + (dir (d - (m : ZMod 6))).2) := by
      ext <;> simp [subR] <;> ring
    rw [hsub, rotPowR_add, rotPowR_dir]
    have hd : d - (m : ZMod 6) + (m : ZMod 6) = d := by ring
    rw [hd]
  have hA3 : inK0 k r (v.1 + (dir 3).1, v.2 + (dir 3).2) := by
    have : dir (3 : ZMod 6) = (-1, 0) := by decide
    rw [this]; simpa [sub_eq_add_neg] using step5_inward_e3 hr h1 h2 hv
  have hA4 : inK0 k r (v.1 + (dir 4).1, v.2 + (dir 4).2) := by
    have href_in : inK0 k r (refR v) := inK0_refR hv
    have h3ref := step5_inward_e3 hr h2 h1 href_in
    have hback := inK0_refR h3ref
    have : dir (4 : ZMod 6) = (0, -1) := by decide
    rw [this]
    simpa [refR, sub_eq_add_neg] using hback
  have hA05 : inK0 k r (v.1 + (dir 0).1, v.2 + (dir 0).2) →
      inK0 k r (v.1 + (dir 5).1, v.2 + (dir 5).2) := by
    intro h0
    have hd0 : dir (0 : ZMod 6) = (1, 0) := by decide
    have hd5 : dir (5 : ZMod 6) = (1, -1) := by decide
    rw [hd0] at h0; rw [hd5]
    simpa [sub_eq_add_neg] using step5_lateral_e5 h1 h2 hv (by simpa using h0)
  have hA12 : inK0 k r (v.1 + (dir 1).1, v.2 + (dir 1).2) →
      inK0 k r (v.1 + (dir 2).1, v.2 + (dir 2).2) := by
    intro h1in
    have hd1 : dir (1 : ZMod 6) = (0, 1) := by decide
    have hd2 : dir (2 : ZMod 6) = (-1, 1) := by decide
    rw [hd1] at h1in; rw [hd2]
    have href_in : inK0 k r (refR v) := inK0_refR hv
    have href1 : inK0 k r ((refR v).1 + 1, (refR v).2) := by
      have := inK0_refR h1in; simpa [refR] using this
    have hlat := step5_lateral_e5 h2 h1 href_in href1
    have hback := inK0_refR hlat
    simpa [refR, sub_eq_add_neg] using hback
  have harc_shift : IsArc (fun d => p + dir (d + (-(m : ZMod 6))) ∈ layerFinset k o r) := by
    have heq : (fun d => p + dir (d + (-(m : ZMod 6))) ∈ layerFinset k o r) =
        (fun d => inK0 k r (v.1 + (dir d).1, v.2 + (dir d).2)) := by
      funext d
      rw [← sub_eq_add_neg]
      exact propext (htrans d)
    rw [heq]
    exact isArc_of_step5 hA3 hA4 hA05 hA12
  exact isArc_shift (-(m : ZMod 6)) harc_shift

/- Section 6: Connectedness of S_k for r - k >= 1 -/

private def Reach (S : Finset Site) : Site → Site → Prop :=
  Relation.ReflTransGen fun u v => u ∈ S ∧ v ∈ S ∧ unitStep u v

private lemma reach_symm {S : Finset Site} {p q : Site} (h : Reach S p q) : Reach S q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, unitStep_symm hstep.2.2⟩ ih

private lemma reach_trans {S : Finset Site} {a b c : Site}
    (h1 : Reach S a b) (h2 : Reach S b c) : Reach S a c :=
  Relation.ReflTransGen.trans h1 h2

private def IsConn (S : Finset Site) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Reach S p q

private lemma layer_descent_D1 (k : ℕ) (o : Center) {r : ℝ} (hr : (k : ℝ) + 1 ≤ r) :
    ∀ p ∈ layerFinset k o r, ∃ w ∈ layerFinset k o r, Qp (subR w o) ≤ 1 ∧ Reach (layerFinset k o r) p w := by
  classical
  have hr0 : 0 ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) k]
  suffices h : ∀ N : ℕ, ∀ p ∈ layerFinset k o r,
      ((layerFinset k o r).filter fun z => Qp (subR z o) < Qp (subR p o)).card ≤ N →
      ∃ w ∈ layerFinset k o r, Qp (subR w o) ≤ 1 ∧ Reach (layerFinset k o r) p w by
    intro p hp
    exact h _ p hp le_rfl
  intro N
  induction N with
  | zero =>
    intro p hp hcard
    by_cases hq : Qp (subR p o) ≤ 1
    · exact ⟨p, hp, hq, Relation.ReflTransGen.refl⟩
    · push Not at hq
      rcases exists_d6_sector (subR p o) with ⟨b, m, h2, hle⟩
      set v := if b then refR (rotPowR m (subR p o)) else rotPowR m (subR p o)
      have hv_in : inK0 k r v := by
        have hp' := (mem_layerFinset hr0 p).mp hp
        cases b
        · exact inK0_rotPowR m hp'
        · exact inK0_refR (inK0_rotPowR m hp')
      have hv_step : inK0 k r (v.1 - 1, v.2) := step5_inward_e3 hr (by linarith) h2 hv_in
      set d_step : ZMod 6 := if b then (4 : ZMod 6) - (m : ZMod 6) else (3 : ZMod 6) - (m : ZMod 6)
      set p' : Site := p + dir d_step
      have hp'_transform : (if b then refR (rotPowR m (subR p' o)) else rotPowR m (subR p' o)) =
          (v.1 - 1, v.2) := by
        have hsub : subR p' o = ((subR p o).1 + (dir d_step).1, (subR p o).2 + (dir d_step).2) := by
          ext <;> simp [p', subR] <;> ring
        rw [hsub, rotPowR_add, rotPowR_dir]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, d_step, v]
          have hd : (3 : ZMod 6) - (m : ZMod 6) + (m : ZMod 6) = 3 := by ring
          rw [hd]
          have : dir (3 : ZMod 6) = (-1, 0) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        · simp only [↓reduceIte, d_step, v]
          have hd : (4 : ZMod 6) - (m : ZMod 6) + (m : ZMod 6) = 4 := by ring
          rw [hd, refR_add, refR_dir]
          have h14 : (1 : ZMod 6) - 4 = 3 := by decide
          rw [h14]
          have : dir (3 : ZMod 6) = (-1, 0) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
      have hp'_mem : p' ∈ layerFinset k o r := by
        rw [mem_layerFinset hr0]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at hp'_transform
          rw [← inK0_iff_rotPowR m, hp'_transform]; exact hv_step
        · simp only [↓reduceIte] at hp'_transform
          rw [← inK0_iff_rotPowR m, ← inK0_iff_refR, hp'_transform]; exact hv_step
      have hQp_eq : Qp v = Qp (subR p o) := by
        cases b <;> simp [v, Qp_refR, Qp_rotPowR]
      have hQp'_eq : Qp (subR p' o) = Qp (v.1 - 1, v.2) := by
        have h1 : Qp (if b then refR (rotPowR m (subR p' o)) else rotPowR m (subR p' o)) =
            Qp (subR p' o) := by
          cases b <;> simp [Qp_refR, Qp_rotPowR]
        rw [← h1, hp'_transform]
      have hstrict : Qp (subR p' o) < Qp (subR p o) := by
        rw [hQp'_eq, ← hQp_eq]
        unfold Qp Q at hQp_eq hq ⊢
        have h3q : (2 * v.1 + v.2) ^ 2 ≥ 3 * (v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2) := by nlinarith
        have h2v : 1 < 2 * v.1 + v.2 := by nlinarith
        nlinarith
      have hmem_filt : p' ∈ (layerFinset k o r).filter fun z => Qp (subR z o) < Qp (subR p o) :=
        Finset.mem_filter.mpr ⟨hp'_mem, hstrict⟩
      have hpos : 0 < ((layerFinset k o r).filter fun z => Qp (subR z o) < Qp (subR p o)).card :=
        Finset.card_pos.mpr ⟨p', hmem_filt⟩
      omega
  | succ N ih =>
    intro p hp hcard
    by_cases hq : Qp (subR p o) ≤ 1
    · exact ⟨p, hp, hq, Relation.ReflTransGen.refl⟩
    · push Not at hq
      rcases exists_d6_sector (subR p o) with ⟨b, m, h2, hle⟩
      set v := if b then refR (rotPowR m (subR p o)) else rotPowR m (subR p o)
      have hv_in : inK0 k r v := by
        have hp' := (mem_layerFinset hr0 p).mp hp
        cases b
        · exact inK0_rotPowR m hp'
        · exact inK0_refR (inK0_rotPowR m hp')
      have hv_step : inK0 k r (v.1 - 1, v.2) := step5_inward_e3 hr (by linarith) h2 hv_in
      set d_step : ZMod 6 := if b then (4 : ZMod 6) - (m : ZMod 6) else (3 : ZMod 6) - (m : ZMod 6)
      set p' : Site := p + dir d_step
      have hp'_transform : (if b then refR (rotPowR m (subR p' o)) else rotPowR m (subR p' o)) =
          (v.1 - 1, v.2) := by
        have hsub : subR p' o = ((subR p o).1 + (dir d_step).1, (subR p o).2 + (dir d_step).2) := by
          ext <;> simp [p', subR] <;> ring
        rw [hsub, rotPowR_add, rotPowR_dir]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, d_step, v]
          have hd : (3 : ZMod 6) - (m : ZMod 6) + (m : ZMod 6) = 3 := by ring
          rw [hd]
          have : dir (3 : ZMod 6) = (-1, 0) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        · simp only [↓reduceIte, d_step, v]
          have hd : (4 : ZMod 6) - (m : ZMod 6) + (m : ZMod 6) = 4 := by ring
          rw [hd, refR_add, refR_dir]
          have h14 : (1 : ZMod 6) - 4 = 3 := by decide
          rw [h14]
          have : dir (3 : ZMod 6) = (-1, 0) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
      have hp'_mem : p' ∈ layerFinset k o r := by
        rw [mem_layerFinset hr0]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at hp'_transform
          rw [← inK0_iff_rotPowR m, hp'_transform]; exact hv_step
        · simp only [↓reduceIte] at hp'_transform
          rw [← inK0_iff_rotPowR m, ← inK0_iff_refR, hp'_transform]; exact hv_step
      have hQp_eq : Qp v = Qp (subR p o) := by
        cases b <;> simp [v, Qp_refR, Qp_rotPowR]
      have hQp'_eq : Qp (subR p' o) = Qp (v.1 - 1, v.2) := by
        have h1 : Qp (if b then refR (rotPowR m (subR p' o)) else rotPowR m (subR p' o)) =
            Qp (subR p' o) := by
          cases b <;> simp [Qp_refR, Qp_rotPowR]
        rw [← h1, hp'_transform]
      have hstrict : Qp (subR p' o) < Qp (subR p o) := by
        rw [hQp'_eq, ← hQp_eq]
        unfold Qp Q at hQp_eq hq ⊢
        have h3q : (2 * v.1 + v.2) ^ 2 ≥ 3 * (v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2) := by nlinarith
        have h2v : 1 < 2 * v.1 + v.2 := by nlinarith
        nlinarith
      have hssub : ((layerFinset k o r).filter fun z => Qp (subR z o) < Qp (subR p' o)) ⊂
          ((layerFinset k o r).filter fun z => Qp (subR z o) < Qp (subR p o)) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨p', Finset.mem_filter.mpr ⟨hp'_mem, hstrict⟩, by simp⟩
        · intro z hz
          simp only [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, lt_trans hz.2 hstrict⟩
      have hcard' : ((layerFinset k o r).filter fun z => Qp (subR z o) < Qp (subR p' o)).card ≤ N := by
        have hlt := Finset.card_lt_card hssub
        omega
      rcases ih p' hp'_mem hcard' with ⟨w, hw_mem, hw_q, hreach⟩
      exact ⟨w, hw_mem, hw_q, Relation.ReflTransGen.head ⟨hp, hp'_mem, unitStep_add_dir p d_step⟩ hreach⟩

private lemma int_Q_le_four_cases (x y : ℤ) (h : x ^ 2 + x * y + y ^ 2 ≤ 4) :
    (x = 0 ∧ y = 0) ∨
    (∃ d : ZMod 6, (x, y) = dir d) ∨
    (∃ d : ZMod 6, (x, y) = (2 * (dir d).1, 2 * (dir d).2)) ∨
    (∃ d : ZMod 6, (x, y) = dir d + dir (d + 1)) := by
  have h4 : (2 * x + y) ^ 2 + 3 * y ^ 2 ≤ 16 := by nlinarith
  have hy1 : -2 ≤ y := by nlinarith
  have hy2 : y ≤ 2 := by nlinarith
  have hx1 : -2 ≤ x := by nlinarith
  have hx2 : x ≤ 2 := by nlinarith
  interval_cases y <;> interval_cases x <;> try (norm_num at h; done)
  · exact Or.inr (Or.inr (Or.inl ⟨4, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨4, by decide⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨3, by decide⟩))
  · exact Or.inr (Or.inl ⟨4, by decide⟩)
  · exact Or.inr (Or.inl ⟨5, by decide⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨5, by decide⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, by decide⟩))
  · exact Or.inr (Or.inl ⟨3, by decide⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨0, by decide⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨0, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨2, by decide⟩))
  · exact Or.inr (Or.inl ⟨2, by decide⟩)
  · exact Or.inr (Or.inl ⟨1, by decide⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨0, by decide⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨2, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨1, by decide⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨1, by decide⟩))

private lemma layer_conn (k : ℕ) (o : Center) {r : ℝ} (hr : (k : ℝ) + 1 ≤ r) :
    IsConn (layerFinset k o r) := by
  have hr0 : 0 ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hD1_mem : ∀ z : Site, Qp (subR z o) ≤ 1 → z ∈ layerFinset k o r := by
    intro z hz
    rw [mem_layerFinset hr0]
    exact inK0_of_Q_le (ρ := 1) (by norm_num) hr (by simpa using hz)
  have hD1_reach : ∀ p1 p2 : Site, Qp (subR p1 o) ≤ 1 → Qp (subR p2 o) ≤ 1 →
      Reach (layerFinset k o r) p1 p2 := by
    intro p1 p2 h1 h2
    have hm1 := hD1_mem p1 h1
    have hm2 := hD1_mem p2 h2
    have hq4_r : Q ((p2.1 - p1.1 : ℤ) : ℝ) ((p2.2 - p1.2 : ℤ) : ℝ) ≤ 4 := by
      unfold Qp Q subR at h1 h2
      unfold Q
      push_cast
      have hpar : ((p2.1 : ℝ) - p1.1) ^ 2 + ((p2.1 : ℝ) - p1.1) * ((p2.2 : ℝ) - p1.2) +
          ((p2.2 : ℝ) - p1.2) ^ 2 +
          (((p1.1 : ℝ) - o.1 + ((p2.1 : ℝ) - o.1)) ^ 2 +
           ((p1.1 : ℝ) - o.1 + ((p2.1 : ℝ) - o.1)) * ((p1.2 : ℝ) - o.2 + ((p2.2 : ℝ) - o.2)) +
           ((p1.2 : ℝ) - o.2 + ((p2.2 : ℝ) - o.2)) ^ 2) =
          2 * (((p1.1 : ℝ) - o.1) ^ 2 + ((p1.1 : ℝ) - o.1) * ((p1.2 : ℝ) - o.2) + ((p1.2 : ℝ) - o.2) ^ 2) +
          2 * (((p2.1 : ℝ) - o.1) ^ 2 + ((p2.1 : ℝ) - o.1) * ((p2.2 : ℝ) - o.2) + ((p2.2 : ℝ) - o.2) ^ 2) := by
        ring
      have hnn := Q_nonneg ((p1.1 : ℝ) - o.1 + ((p2.1 : ℝ) - o.1)) ((p1.2 : ℝ) - o.2 + ((p2.2 : ℝ) - o.2))
      unfold Q at hnn
      linarith
    have hq4 : (p2.1 - p1.1) ^ 2 + (p2.1 - p1.1) * (p2.2 - p1.2) + (p2.2 - p1.2) ^ 2 ≤ 4 := by
      have : (((p2.1 - p1.1) ^ 2 + (p2.1 - p1.1) * (p2.2 - p1.2) + (p2.2 - p1.2) ^ 2 : ℤ) : ℝ) ≤ (4 : ℤ) := by
        unfold Q at hq4_r; push_cast at hq4_r ⊢; exact hq4_r
      exact_mod_cast this
    rcases int_Q_le_four_cases (p2.1 - p1.1) (p2.2 - p1.2) hq4 with
      ⟨hx, hy⟩ | ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
    · have : p1 = p2 := Prod.ext (by omega) (by omega)
      subst this; exact Relation.ReflTransGen.refl
    · have hp2 : p2 = p1 + dir d := by
        have h1' := congrArg Prod.fst hd
        have h2' := congrArg Prod.snd hd
        exact Prod.ext (by dsimp at h1' ⊢; omega) (by dsimp at h2' ⊢; omega)
      exact Relation.ReflTransGen.single ⟨hm1, hm2, hp2 ▸ unitStep_add_dir p1 d⟩
    · set w : Site := p1 + dir d
      have hp2 : p2 = w + dir d := by
        have h1' := congrArg Prod.fst hd
        have h2' := congrArg Prod.snd hd
        exact Prod.ext (by dsimp [w] at h1' ⊢; omega) (by dsimp [w] at h2' ⊢; omega)
      have hw_q : Qp (subR w o) ≤ 1 := by
        have hcv := Q_convex2 (w1 := 1 / 2) (w2 := 1 / 2) (by norm_num) (by norm_num) (by norm_num) h1 h2
        have hx : 1 / 2 * (subR p1 o).1 + 1 / 2 * (subR p2 o).1 = (subR w o).1 := by
          have hp2x : p2.1 = p1.1 + 2 * (dir d).1 := by
            have := congrArg Prod.fst hp2
            simp only [Prod.fst_add, w] at this; omega
          have hp2x_r : (p2.1 : ℝ) = (p1.1 : ℝ) + 2 * ((dir d).1 : ℝ) := by exact_mod_cast hp2x
          simp only [subR, Prod.fst_add, Int.cast_add, w]
          linarith
        have hy : 1 / 2 * (subR p1 o).2 + 1 / 2 * (subR p2 o).2 = (subR w o).2 := by
          have hp2y : p2.2 = p1.2 + 2 * (dir d).2 := by
            have := congrArg Prod.snd hp2
            simp only [Prod.snd_add, w] at this; omega
          have hp2y_r : (p2.2 : ℝ) = (p1.2 : ℝ) + 2 * ((dir d).2 : ℝ) := by exact_mod_cast hp2y
          simp only [subR, Prod.snd_add, Int.cast_add, w]
          linarith
        unfold Qp at h1 h2 ⊢; rw [← hx, ← hy]; exact hcv
      have hmw := hD1_mem w hw_q
      exact Relation.ReflTransGen.head ⟨hm1, hmw, unitStep_add_dir p1 d⟩
        (Relation.ReflTransGen.single ⟨hmw, hm2, hp2 ▸ unitStep_add_dir w d⟩)
    · set w1 : Site := p1 + dir d
      set w2 : Site := p1 + dir (d + 1)
      have hp2_1 : p2 = w1 + dir (d + 1) := by
        have h1' := congrArg Prod.fst hd
        have h2' := congrArg Prod.snd hd
        exact Prod.ext (by dsimp [w1] at h1' ⊢; omega) (by dsimp [w1] at h2' ⊢; omega)
      have hp2_2 : p2 = w2 + dir d := by
        have h1' := congrArg Prod.fst hd
        have h2' := congrArg Prod.snd hd
        exact Prod.ext (by dsimp [w2] at h1' ⊢; omega) (by dsimp [w2] at h2' ⊢; omega)
      have hsum_q : 2 * Qp (subR w1 o) + 2 * Qp (subR w2 o) ≤ 2 := by
        have hdir_id : ∀ c : ZMod 6,
            (((dir c).1 : ℝ) + (dir (c + 1)).1) ^ 2 +
            (((dir c).1 : ℝ) + (dir (c + 1)).1) * (((dir c).2 : ℝ) + (dir (c + 1)).2) +
            (((dir c).2 : ℝ) + (dir (c + 1)).2) ^ 2 = 3 ∧
            (((dir c).1 : ℝ) - (dir (c + 1)).1) ^ 2 +
            (((dir c).1 : ℝ) - (dir (c + 1)).1) * (((dir c).2 : ℝ) - (dir (c + 1)).2) +
            (((dir c).2 : ℝ) - (dir (c + 1)).2) ^ 2 = 1 := by
          intro c
          have hc : ((dir c).1 + (dir (c + 1)).1) ^ 2 +
              ((dir c).1 + (dir (c + 1)).1) * ((dir c).2 + (dir (c + 1)).2) +
              ((dir c).2 + (dir (c + 1)).2) ^ 2 = 3 ∧
              ((dir c).1 - (dir (c + 1)).1) ^ 2 +
              ((dir c).1 - (dir (c + 1)).1) * ((dir c).2 - (dir (c + 1)).2) +
              ((dir c).2 - (dir (c + 1)).2) ^ 2 = 1 := by
            revert c; decide
          exact ⟨by exact_mod_cast hc.1, by exact_mod_cast hc.2⟩
        rcases hdir_id d with ⟨h3, h1'⟩
        have hx2 : (p2.1 : ℝ) = (p1.1 : ℝ) + (dir d).1 + (dir (d + 1)).1 := by
          have := congrArg Prod.fst hp2_1
          simp only [Prod.fst_add, w1] at this
          exact_mod_cast this
        have hy2 : (p2.2 : ℝ) = (p1.2 : ℝ) + (dir d).2 + (dir (d + 1)).2 := by
          have := congrArg Prod.snd hp2_1
          simp only [Prod.snd_add, w1] at this
          exact_mod_cast this
        have hident : 2 * Qp (subR w1 o) + 2 * Qp (subR w2 o) =
            2 * Qp (subR p1 o) + 2 * Qp (subR p2 o) -
            ((((dir d).1 : ℝ) + (dir (d + 1)).1) ^ 2 +
             (((dir d).1 : ℝ) + (dir (d + 1)).1) * (((dir d).2 : ℝ) + (dir (d + 1)).2) +
             (((dir d).2 : ℝ) + (dir (d + 1)).2) ^ 2) +
            ((((dir d).1 : ℝ) - (dir (d + 1)).1) ^ 2 +
             (((dir d).1 : ℝ) - (dir (d + 1)).1) * (((dir d).2 : ℝ) - (dir (d + 1)).2) +
             (((dir d).2 : ℝ) - (dir (d + 1)).2) ^ 2) := by
          simp only [Qp, Q, subR, w1, w2, Prod.fst_add, Prod.snd_add, Int.cast_add, hx2, hy2]
          ring
        linarith
      by_cases hw1 : Qp (subR w1 o) ≤ 1
      · have hmw1 := hD1_mem w1 hw1
        exact Relation.ReflTransGen.head ⟨hm1, hmw1, unitStep_add_dir p1 d⟩
          (Relation.ReflTransGen.single ⟨hmw1, hm2, hp2_1 ▸ unitStep_add_dir w1 (d + 1)⟩)
      · have hw2 : Qp (subR w2 o) ≤ 1 := by linarith
        have hmw2 := hD1_mem w2 hw2
        exact Relation.ReflTransGen.head ⟨hm1, hmw2, unitStep_add_dir p1 (d + 1)⟩
          (Relation.ReflTransGen.single ⟨hmw2, hm2, hp2_2 ▸ unitStep_add_dir w2 d⟩)
  intro p hp q hq
  rcases layer_descent_D1 k o hr p hp with ⟨w1, _, hw1, hr1⟩
  rcases layer_descent_D1 k o hr q hq with ⟨w2, _, hw2, hr2⟩
  exact reach_trans hr1 (reach_trans (hD1_reach w1 w2 hw1 hw2) (reach_symm hr2))

/- Section 7: Zero-Topology Single-Orbit Boundary Cycle Theorem (modular for reuse!) -/

private structure GoodRegion (S : Finset Site) : Prop where
  nonempty : S.Nonempty
  conn : IsConn S
  hconv : HorizConvex S
  loc : ∀ p ∈ S, IsArc (fun d => p + dir d ∈ S)

private lemma layer_goodRegion (k : ℕ) (o : Center) {r : ℝ} (hr : (k : ℝ) + 1 ≤ r) :
    GoodRegion (layerFinset k o r) := by
  have hr0 : 0 ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) k]
  refine ⟨?_, layer_conn k o hr, layer_horizConvex k o hr0, layer_locallyConn k o hr⟩
  rcases D1_exists_three o with ⟨T, hcard, hT⟩
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  rcases hTne with ⟨p, hp⟩
  exact ⟨p, (mem_layerFinset hr0 p).mpr (inK0_of_Q_le (ρ := 1) (by norm_num) hr (by simpa using hT p hp))⟩

private def lexLe (p q : Site) : Prop :=
  p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 ≤ q.1)

private lemma exists_lexMin (T : Finset Site) (hT : T.Nonempty) :
    ∃ u ∈ T, ∀ v ∈ T, lexLe u v := by
  classical
  induction T using Finset.induction_on with
  | empty => exact absurd hT Finset.not_nonempty_empty
  | @insert a s ha ih =>
    by_cases hs : s.Nonempty
    · rcases ih hs with ⟨u, hu, hmin⟩
      by_cases hle : lexLe a u
      · refine ⟨a, Finset.mem_insert_self a s, fun v hv => ?_⟩
        rcases Finset.mem_insert.mp hv with rfl | hvs
        · exact Or.inr ⟨rfl, le_rfl⟩
        · have hv' := hmin v hvs
          unfold lexLe at hle hv' ⊢
          omega
      · refine ⟨u, Finset.mem_insert_of_mem hu, fun v hv => ?_⟩
        rcases Finset.mem_insert.mp hv with rfl | hvs
        · unfold lexLe at hle ⊢; omega
        · exact hmin v hvs
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, Finset.mem_singleton_self a, fun v hv => ?_⟩
      rw [Finset.mem_singleton.mp hv]
      exact Or.inr ⟨rfl, le_rfl⟩

private lemma lexMin_mem_bdry {S : Finset Site} {u : Site}
    (hu : u ∈ S) (hmin : ∀ v ∈ S, lexLe u v) : u ∈ combBdry S := by
  rw [mem_combBdry]
  refine ⟨hu, 4, fun h4 => ?_⟩
  have hle := hmin (u + dir 4) h4
  have : dir (4 : ZMod 6) = (0, -1) := by decide
  rw [this] at hle
  unfold lexLe at hle
  simp at hle

private noncomputable def bdryDir (S : Finset Site) (u : Site) : ZMod 6 := by
  classical
  exact if h : ∃ d : ZMod 6, u + dir d ∈ S ∧ u + dir (d - 1) ∉ S then Classical.choose h else 0

private noncomputable def phi (S : Finset Site) (u : Site) : Site :=
  u + dir (bdryDir S u)

private lemma bdryDir_spec {S : Finset Site} (h : GoodRegion S) {u : Site} (hu : u ∈ combBdry S) :
    u + dir (bdryDir S u) ∈ S ∧ u + dir (bdryDir S u - 1) ∉ S := by
  classical
  rcases mem_combBdry.mp hu with ⟨huS, hnot⟩
  have hex := isArc_exists_start (h.loc u huS) hnot
  unfold bdryDir
  rw [dif_pos hex]
  exact Classical.choose_spec hex

private lemma bdryDir_unique {S : Finset Site} (h : GoodRegion S) {u : Site} (hu : u ∈ combBdry S)
    {d : ZMod 6} (h1 : u + dir d ∈ S) (h2 : u + dir (d - 1) ∉ S) :
    bdryDir S u = d := by
  have hs := bdryDir_spec h hu
  exact (h.loc u (mem_combBdry.mp hu).1).2 _ _ hs.1 hs.2 h1 h2

private lemma phi_mem_bdry {S : Finset Site} (h : GoodRegion S) {u : Site} (hu : u ∈ combBdry S) :
    phi S u ∈ combBdry S := by
  have hs := bdryDir_spec h hu
  rw [mem_combBdry]
  refine ⟨hs.1, bdryDir S u + 4, ?_⟩
  have heq : phi S u + dir (bdryDir S u + 4) = u + dir (bdryDir S u - 1) := by
    unfold phi
    have hsub := dir_sub_one_sub (bdryDir S u)
    ext <;> simp [← hsub]
  rw [heq]
  exact hs.2

private lemma phi_unitStep {S : Finset Site} (u : Site) : unitStep u (phi S u) :=
  unitStep_add_dir u (bdryDir S u)

private lemma phi_ne {S : Finset Site} (u : Site) : phi S u ≠ u := by
  intro heq
  unfold phi at heq
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  exact dir_ne_zero (bdryDir S u) (Prod.ext (by simp at h1; omega) (by simp at h2; omega))

private lemma phi_phi_ne {S : Finset Site} (h : GoodRegion S) {u : Site} (hu : u ∈ combBdry S) :
    phi S (phi S u) ≠ u := by
  intro heq
  set d := bdryDir S u
  set v := phi S u
  have hv := phi_mem_bdry h hu
  have hdv : bdryDir S v = d + 3 := by
    have h1 : v + dir (bdryDir S v) = v + dir (d + 3) := by
      change phi S v = v + dir (d + 3)
      rw [heq]
      unfold v phi
      have h3 := dir_add_three d
      dsimp only [d] at h3 ⊢
      ext <;> simp [h3]
    have h2 : dir (bdryDir S v) = dir (d + 3) := by
      have ha := congrArg Prod.fst h1
      have hb := congrArg Prod.snd h1
      exact Prod.ext (by simp at ha; omega) (by simp at hb; omega)
    exact dir_inj h2
  have hsv := bdryDir_spec h hv
  rw [hdv] at hsv
  have hm : v + dir (d + 3 - 1) ∉ S := hsv.2
  have hp : v + dir (d + 3 + 1) ∉ S := by
    have h4 : d + 3 + 1 = d + 4 := by ring
    rw [h4]
    have heq2 : v + dir (d + 4) = u + dir (d - 1) := by
      unfold v phi
      have hsub := dir_sub_one_sub d
      ext <;> simp [← hsub] <;> ring
    rw [heq2]
    exact (bdryDir_spec h hu).2
  exact isArc_no_isolated (h.loc v (mem_combBdry.mp hv).1) hsv.1 hm hp

private lemma phi_injOn {S : Finset Site} (h : GoodRegion S) :
    Set.InjOn (phi S) (combBdry S : Set Site) := by
  intro u1 hu1 u2 hu2 heq
  have hu1' : u1 ∈ combBdry S := hu1
  have hu2' : u2 ∈ combBdry S := hu2
  set v := phi S u1
  have hv : v ∈ combBdry S := phi_mem_bdry h hu1'
  set a1 := bdryDir S u1 + 3
  set a2 := bdryDir S u2 + 3
  have hu1_eq : v + dir a1 = u1 := by
    unfold v phi a1
    have h3 := dir_add_three (bdryDir S u1)
    ext <;> simp [h3]
  have hu2_eq : v + dir a2 = u2 := by
    have hv2 : v = phi S u2 := heq
    rw [hv2]; unfold phi a2
    have h3 := dir_add_three (bdryDir S u2)
    ext <;> simp [h3]
  have ha1_in : v + dir a1 ∈ S := hu1_eq ▸ (mem_combBdry.mp hu1').1
  have ha2_in : v + dir a2 ∈ S := hu2_eq ▸ (mem_combBdry.mp hu2').1
  have ha1_out : v + dir (a1 + 1) ∉ S := by
    have : v + dir (a1 + 1) = u1 + dir (bdryDir S u1 - 1) := by
      unfold v phi a1
      have hsub := dir_sub_one_sub (bdryDir S u1)
      have h4 : bdryDir S u1 + 3 + 1 = bdryDir S u1 + 4 := by ring
      rw [h4]; ext <;> simp [← hsub]
    rw [this]; exact (bdryDir_spec h hu1').2
  have ha2_out : v + dir (a2 + 1) ∉ S := by
    have : v + dir (a2 + 1) = u2 + dir (bdryDir S u2 - 1) := by
      have hv2 : v = phi S u2 := heq
      rw [hv2]; unfold phi a2
      have hsub := dir_sub_one_sub (bdryDir S u2)
      have h4 : bdryDir S u2 + 3 + 1 = bdryDir S u2 + 4 := by ring
      rw [h4]; ext <;> simp [← hsub]
    rw [this]; exact (bdryDir_spec h hu2').2
  have ha_eq : a1 = a2 := isArc_end_unique (h.loc v (mem_combBdry.mp hv).1) ha1_in ha1_out ha2_in ha2_out
  rw [← hu1_eq, ← hu2_eq, ha_eq]

private lemma phi_preimage_spec {S : Finset Site} (h : GoodRegion S)
    {u v : Site} (hu : u ∈ combBdry S) (huv : phi S u = v) :
    ∃ a : ZMod 6, u = v + dir a ∧ v + dir a ∈ S ∧ v + dir (a + 1) ∉ S ∧ bdryDir S u = a + 3 := by
  set d := bdryDir S u
  have h33 : d = d + 3 + 3 := by
    have : (3 : ZMod 6) + 3 = 0 := by decide
    rw [add_assoc, this, add_zero]
  have hv_back : v + dir (d + 3) = u := by
    rw [← huv]; unfold phi
    have h3 := dir_add_three d
    dsimp only [d] at h3 ⊢
    ext <;> simp [h3]
  refine ⟨d + 3, hv_back.symm, hv_back ▸ (mem_combBdry.mp hu).1, ?_, h33⟩
  have : v + dir (d + 3 + 1) = u + dir (d - 1) := by
    rw [← huv]; unfold phi
    have hsub := dir_sub_one_sub d
    have h4 : d + 3 + 1 = d + 4 := by ring
    rw [h4]; dsimp only [d] at hsub ⊢; ext <;> simp [← hsub]
  rw [this]; exact (bdryDir_spec h hu).2

private lemma no_below_of_row_barrier {S : Finset Site} (h : GoodRegion S)
    {x0 y0 : ℤ} {t : ℕ}
    (hrow : ∀ p ∈ S, p.2 = y0 → x0 ≤ p.1 ∧ p.1 ≤ x0 + t)
    (hbelow : ∀ j : ℕ, j ≤ t + 1 → (x0 + j, y0 - 1) ∉ S)
    (hmem : (x0, y0) ∈ S) :
    ∀ p ∈ S, y0 ≤ p.2 := by
  intro p hp
  have hreach := h.conn (x0, y0) hmem p hp
  by_contra hlt
  push Not at hlt
  have hstep : ∀ a b : Site, Reach S a b → y0 ≤ a.2 → b.2 < y0 → False := by
    intro a b hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => intro ha hb; omega
    | @head a c hstep_ac _ ih =>
      intro ha hb
      by_cases hc : y0 ≤ c.2
      · exact ih hc hb
      · push Not at hc
        rcases (unitStep_iff_exists_dir a c).mp hstep_ac.2.2 with ⟨d, rfl⟩
        have hay : a.2 = y0 := by
          fin_cases d <;> dsimp only [dir] at hc ⊢ <;> simp only [Prod.snd_add] at hc <;> omega
        have hax := hrow a hstep_ac.1 hay
        have hd_cases : d = 4 ∨ d = 5 := by
          fin_cases d <;> dsimp only [dir] at hc ⊢ <;>
            (try (simp only [Prod.snd_add] at hc; omega)) <;>
            first | exact Or.inl rfl | exact Or.inr rfl
        rcases hd_cases with rfl | rfl
        · have hd4 : dir (4 : ZMod 6) = (0, -1) := by decide
          rw [hd4] at hstep_ac
          set j : ℕ := Int.toNat (a.1 - x0)
          have hj_le : j ≤ t + 1 := by omega
          have heq : (a + (0, -1) : Site) = (x0 + j, y0 - 1) := by
            ext <;> simp [j] <;> omega
          rw [heq] at hstep_ac
          exact hbelow j hj_le hstep_ac.2.1
        · have hd5 : dir (5 : ZMod 6) = (1, -1) := by decide
          rw [hd5] at hstep_ac
          set j : ℕ := Int.toNat (a.1 + 1 - x0)
          have hj_le : j ≤ t + 1 := by omega
          have heq : (a + (1, -1) : Site) = (x0 + j, y0 - 1) := by
            ext <;> simp [j] <;> omega
          rw [heq] at hstep_ac
          exact hbelow j hj_le hstep_ac.2.1
  exact hstep (x0, y0) p hreach le_rfl hlt

private lemma phi_orbit_contains_lexMin {S : Finset Site} (h : GoodRegion S)
    {O : Finset Site} (hOne : O.Nonempty) (hOsub : O ⊆ combBdry S)
    (hOfwd : ∀ u ∈ O, phi S u ∈ O) (hObwd : ∀ v ∈ O, ∃ u ∈ O, phi S u = v) :
    ∃ u ∈ O, ∀ p ∈ S, lexLe u p := by
  classical
  rcases exists_lexMin O hOne with ⟨u, huO, huMin⟩
  have huB : u ∈ combBdry S := hOsub huO
  have huS : u ∈ S := (mem_combBdry.mp huB).1
  set uout := phi S u
  have huoutO : uout ∈ O := hOfwd u huO
  rcases hObwd u huO with ⟨uin, huinO, hphi_in⟩
  have huinB : uin ∈ combBdry S := hOsub huinO
  have hne_io : uin ≠ uout := by
    intro heq
    have : phi S uout = u := by rw [← heq]; exact hphi_in
    exact phi_phi_ne h huB this
  set d := bdryDir S u
  have hd_spec := bdryDir_spec h huB
  have hd_012 : d = 0 ∨ d = 1 ∨ d = 2 := by
    have hle := huMin uout huoutO
    unfold uout phi lexLe at hle
    rcases zmod6_cases d with hd | hd | hd | hd | hd | hd
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr hd)
    · exfalso; change (u.2 < (u + dir d).2 ∨ u.2 = (u + dir d).2 ∧ u.1 ≤ (u + dir d).1) at hle
      rw [hd] at hle; simp [dir] at hle
    · exfalso; change (u.2 < (u + dir d).2 ∨ u.2 = (u + dir d).2 ∧ u.1 ≤ (u + dir d).1) at hle
      rw [hd] at hle; simp [dir] at hle
    · exfalso; change (u.2 < (u + dir d).2 ∨ u.2 = (u + dir d).2 ∧ u.1 ≤ (u + dir d).1) at hle
      rw [hd] at hle; simp [dir] at hle
  rcases phi_preimage_spec h huinB hphi_in with ⟨a, huin_eq, ha_in, ha_out, hdin_eq⟩
  have ha_012 : a = 0 ∨ a = 1 ∨ a = 2 := by
    have hle := huMin uin huinO
    rw [huin_eq] at hle
    unfold lexLe at hle
    fin_cases a <;> dsimp only [dir] at hle ⊢ <;>
      (try (simp only [Prod.fst_add, Prod.snd_add] at hle; omega)) <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  have had_ne : a ≠ d := by
    intro heq
    apply hne_io
    rw [huin_eq, heq]; rfl
  rcases hd_012 with hd0 | hd1 | hd2
  · -- Case d = 0
    have h5out : u + dir 5 ∉ S := by
      have : d - 1 = 5 := by rw [hd0]; decide
      rw [← this]; exact hd_spec.2
    have h0in : u + dir 0 ∈ S := hd0 ▸ hd_spec.1
    have h34out : u + dir 3 ∉ S ∧ u + dir 4 ∉ S := by
      rcases ha_012 with rfl | rfl | rfl
      · exact absurd hd0.symm had_ne
      · have h2out : u + dir 2 ∉ S := by
          have : (1 : ZMod 6) + 1 = 2 := by decide
          rwa [this] at ha_out
        have hg3 := (isArc_gap_forces (h.loc u huS) (a := 0) (b := 5) (c := 2) (d := 3)
          h0in h5out h2out).2.1 ⟨rfl, rfl, rfl, Or.inl rfl⟩
        have hg4 := (isArc_gap_forces (h.loc u huS) (a := 0) (b := 5) (c := 2) (d := 4)
          h0in h5out h2out).2.1 ⟨rfl, rfl, rfl, Or.inr rfl⟩
        exact ⟨hg3, hg4⟩
      · have h3out : u + dir 3 ∉ S := by
          have : (2 : ZMod 6) + 1 = 3 := by decide
          rwa [this] at ha_out
        have hg4 := (isArc_gap_forces (h.loc u huS) (a := 0) (b := 5) (c := 3) (d := 4)
          h0in h5out h3out).2.2.1 ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨h3out, hg4⟩
    let P : ℕ → Prop := fun j =>
      ∀ i : ℕ, i ≤ j → (u.1 + i, u.2) ∈ O ∧ (i < j → bdryDir S (u.1 + i, u.2) = 0)
    have hP0 : P 0 := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact ⟨by simpa using huO, fun hlt => by omega⟩
    have hP1 : P 1 := by
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        exact ⟨by simpa using huO, fun _ => by simpa using hd0⟩
      · have hi1 : i = 1 := by omega
        subst hi1
        refine ⟨?_, fun hlt => by omega⟩
        have : (u.1 + (1 : ℕ), u.2) = uout := by
          unfold uout phi
          have hd0' : bdryDir S u = 0 := hd0
          rw [hd0']; have : dir (0 : ZMod 6) = (1, 0) := by decide
          rw [this]; ext <;> simp
        rw [this]; exact huoutO
    have hnot_big : ¬ P S.card := by
      intro hbig
      let f : ℕ → Site := fun i => (u.1 + i, u.2)
      have hsub : (Finset.range (S.card + 1)).image f ⊆ S := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
        exact (mem_combBdry.mp (hOsub (hbig i (by simp at hi; omega)).1)).1
      have hinj : Set.InjOn f (Finset.range (S.card + 1) : Set ℕ) := by
        intro i _ j _ hij
        have := congrArg Prod.fst hij
        dsimp [f] at this; omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
      omega
    let T := (Finset.range (S.card + 1)).filter P
    have hTne : T.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := h.nonempty.card_pos; omega), hP1⟩⟩
    set t := T.max' hTne
    have ht_mem : t ∈ T := Finset.max'_mem T hTne
    have htP : P t := (Finset.mem_filter.mp ht_mem).2
    have ht_ge1 : 1 ≤ t := Finset.le_max' T 1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := h.nonempty.card_pos; omega), hP1⟩)
    have ht_lt : t < S.card := by
      have hle : t ≤ S.card := by
        have := (Finset.mem_filter.mp ht_mem).1; simp at this; omega
      by_contra hge
      have heq : t = S.card := by omega
      exact hnot_big (heq ▸ htP)
    set wt : Site := (u.1 + t, u.2)
    have hwtO : wt ∈ O := (htP t le_rfl).1
    have hwtB : wt ∈ combBdry S := hOsub hwtO
    have hwt_prev_dir : bdryDir S (u.1 + ((t - 1 : ℕ) : ℤ), u.2) = 0 :=
      (htP (t - 1) (by omega)).2 (by omega)
    have hwt_prev_B : (u.1 + ((t - 1 : ℕ) : ℤ), u.2) ∈ combBdry S :=
      hOsub (htP (t - 1) (by omega)).1
    have hwt_4out : wt + dir 4 ∉ S := by
      have h5 := (bdryDir_spec h hwt_prev_B).2
      rw [hwt_prev_dir] at h5
      have heq : wt + dir 4 = (u.1 + ((t - 1 : ℕ) : ℤ), u.2) + dir (0 - 1) := by
        have h4 : dir (4 : ZMod 6) = (0, -1) := by decide
        have h5' : dir ((0 : ZMod 6) - 1) = (1, -1) := by decide
        rw [h4, h5']; ext <;> simp [wt]; omega
      rw [heq]; exact h5
    have hwt_5out : wt + dir 5 ∉ S := by
      intro h5in
      have hdwt : bdryDir S wt = 5 := bdryDir_unique h hwtB h5in (by
        have : (5 : ZMod 6) - 1 = 4 := by decide
        rw [this]; exact hwt_4out)
      have hnextO : wt + dir 5 ∈ O := by
        have : phi S wt = wt + dir 5 := by unfold phi; rw [hdwt]
        rw [← this]; exact hOfwd wt hwtO
      have hle := huMin _ hnextO
      have : dir (5 : ZMod 6) = (1, -1) := by decide
      rw [this] at hle; unfold lexLe at hle; simp [wt] at hle
    have hwt_0out : wt + dir 0 ∉ S := by
      intro h0in
      have hdwt : bdryDir S wt = 0 := bdryDir_unique h hwtB h0in (by
        have : (0 : ZMod 6) - 1 = 5 := by decide
        rw [this]; exact hwt_5out)
      have hnextO : (u.1 + ((t + 1 : ℕ) : ℤ), u.2) ∈ O := by
        have : phi S wt = (u.1 + ((t + 1 : ℕ) : ℤ), u.2) := by
          unfold phi; rw [hdwt]; have : dir (0 : ZMod 6) = (1, 0) := by decide
          rw [this]; ext <;> simp [wt]; omega
        rw [← this]; exact hOfwd wt hwtO
      have hPt1 : P (t + 1) := by
        intro i hi
        by_cases hit : i ≤ t
        · refine ⟨(htP i hit).1, fun hlt => ?_⟩
          by_cases hieq : i = t
          · subst hieq; exact hdwt
          · exact (htP i hit).2 (by omega)
        · have hieq : i = t + 1 := by omega
          subst hieq
          exact ⟨hnextO, fun hlt => by omega⟩
      have hmem1 : t + 1 ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hPt1⟩
      have hle1 := Finset.le_max' T (t + 1) hmem1
      omega
    have hrow : ∀ p ∈ S, p.2 = u.2 → u.1 ≤ p.1 ∧ p.1 ≤ u.1 + t := by
      intro p hp hy
      constructor
      · by_contra hlt
        push Not at hlt
        have h3in : (u.1 - 1, u.2) ∈ S :=
          h.hconv p.1 (u.1 - 1) u.1 u.2 (by rwa [← hy]) huS (by omega) (by omega)
        have : u + dir 3 = (u.1 - 1, u.2) := by
          have : dir (3 : ZMod 6) = (-1, 0) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        exact h34out.1 (this ▸ h3in)
      · by_contra hgt
        push Not at hgt
        have h0in : (u.1 + t + 1, u.2) ∈ S :=
          h.hconv (u.1 + t) (u.1 + t + 1) p.1 u.2 (mem_combBdry.mp hwtB).1 (by rwa [← hy])
            (by omega) (by omega)
        have : wt + dir 0 = (u.1 + t + 1, u.2) := by
          have : dir (0 : ZMod 6) = (1, 0) := by decide
          rw [this]; ext <;> simp [wt]
        exact hwt_0out (this ▸ h0in)
    have hbelow : ∀ j : ℕ, j ≤ t + 1 → (u.1 + j, u.2 - 1) ∉ S := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have : u + dir 4 = (u.1 + (0 : ℕ), u.2 - 1) := by
          have : dir (4 : ZMod 6) = (0, -1) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        exact this ▸ h34out.2
      · by_cases hjt : j ≤ t
        · have hj1B : (u.1 + ((j - 1 : ℕ) : ℤ), u.2) ∈ combBdry S :=
            hOsub (htP (j - 1) (by omega)).1
          have hj1d : bdryDir S (u.1 + ((j - 1 : ℕ) : ℤ), u.2) = 0 :=
            (htP (j - 1) (by omega)).2 (by omega)
          have h5 := (bdryDir_spec h hj1B).2
          rw [hj1d] at h5
          have : (u.1 + ((j - 1 : ℕ) : ℤ), u.2) + dir (0 - 1) = (u.1 + j, u.2 - 1) := by
            have : dir ((0 : ZMod 6) - 1) = (1, -1) := by decide
            rw [this]; ext <;> simp <;> omega
          exact this ▸ h5
        · have hjeq : j = t + 1 := by omega
          subst hjeq
          have : wt + dir 5 = (u.1 + ((t + 1 : ℕ) : ℤ), u.2 - 1) := by
            have : dir (5 : ZMod 6) = (1, -1) := by decide
            rw [this]; ext <;> (simp [wt]; omega)
          exact this ▸ hwt_5out
    have hge := no_below_of_row_barrier h hrow hbelow huS
    refine ⟨u, huO, fun p hp => ?_⟩
    have hp2 := hge p hp
    by_cases heq : u.2 = p.2
    · exact Or.inr ⟨heq, (hrow p hp heq.symm).1⟩
    · exact Or.inl (by omega)
  · -- Case d = 1
    have h0out : u + dir 0 ∉ S := by
      have : d - 1 = 0 := by rw [hd1]; decide
      rw [← this]; exact hd_spec.2
    have h1in : u + dir 1 ∈ S := hd1 ▸ hd_spec.1
    have ha2 : a = 2 := by
      rcases ha_012 with rfl | rfl | rfl
      · exact absurd ha_in h0out
      · exact absurd hd1.symm had_ne
      · rfl
    have h3out : u + dir 3 ∉ S := by
      rw [ha2] at ha_out
      have : (2 : ZMod 6) + 1 = 3 := by decide
      rwa [this] at ha_out
    have h4out : u + dir 4 ∉ S :=
      (isArc_gap_forces (h.loc u huS) (a := 1) (b := 0) (c := 3) (d := 4)
        h1in h0out h3out).1 ⟨rfl, rfl, rfl, Or.inl rfl⟩
    have h5out : u + dir 5 ∉ S :=
      (isArc_gap_forces (h.loc u huS) (a := 1) (b := 0) (c := 3) (d := 5)
        h1in h0out h3out).1 ⟨rfl, rfl, rfl, Or.inr rfl⟩
    have hrow : ∀ p ∈ S, p.2 = u.2 → u.1 ≤ p.1 ∧ p.1 ≤ u.1 + (0 : ℕ) := by
      intro p hp hy
      constructor
      · by_contra hlt; push Not at hlt
        have h3in : (u.1 - 1, u.2) ∈ S :=
          h.hconv p.1 (u.1 - 1) u.1 u.2 (by rwa [← hy]) huS (by omega) (by omega)
        have : u + dir 3 = (u.1 - 1, u.2) := by
          have : dir (3 : ZMod 6) = (-1, 0) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        exact h3out (this ▸ h3in)
      · by_contra hgt; push Not at hgt
        have h0in : (u.1 + 1, u.2) ∈ S :=
          h.hconv u.1 (u.1 + 1) p.1 u.2 huS (by rwa [← hy]) (by omega) (by omega)
        have : u + dir 0 = (u.1 + 1, u.2) := by
          have : dir (0 : ZMod 6) = (1, 0) := by decide
          rw [this]; ext <;> simp
        exact h0out (this ▸ h0in)
    have hbelow : ∀ j : ℕ, j ≤ 0 + 1 → (u.1 + j, u.2 - 1) ∉ S := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have : u + dir 4 = (u.1 + (0 : ℕ), u.2 - 1) := by
          have : dir (4 : ZMod 6) = (0, -1) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        exact this ▸ h4out
      · have hj1 : j = 1 := by omega
        subst hj1
        have : u + dir 5 = (u.1 + (1 : ℕ), u.2 - 1) := by
          have : dir (5 : ZMod 6) = (1, -1) := by decide
          rw [this]; ext <;> simp [sub_eq_add_neg]
        exact this ▸ h5out
    have hge := no_below_of_row_barrier h hrow hbelow huS
    refine ⟨u, huO, fun p hp => ?_⟩
    have hp2 := hge p hp
    by_cases heq : u.2 = p.2
    · exact Or.inr ⟨heq, (hrow p hp heq.symm).1⟩
    · exact Or.inl (by omega)
  · -- Case d = 2 (impossible!)
    exfalso
    have h1out : u + dir 1 ∉ S := by
      have : d - 1 = 1 := by rw [hd2]; decide
      rw [← this]; exact hd_spec.2
    have h2in : u + dir 2 ∈ S := hd2 ▸ hd_spec.1
    have ha0 : a = 0 := by
      rcases ha_012 with rfl | rfl | rfl
      · rfl
      · exact absurd ha_in h1out
      · exact absurd hd2.symm had_ne
    have hrow_above : ∀ t : ℕ, (u.1 + t, u.2 + 1) ∉ S := by
      intro t ht
      have h1in : (u.1, u.2 + 1) ∈ S := by
        have hleft : (u.1 - 1, u.2 + 1) ∈ S := by
          have : u + dir 2 = (u.1 - 1, u.2 + 1) := by
            have : dir (2 : ZMod 6) = (-1, 1) := by decide
            rw [this]; ext <;> simp [sub_eq_add_neg]
          exact this ▸ h2in
        exact h.hconv (u.1 - 1) u.1 (u.1 + t) (u.2 + 1) hleft ht (by omega) (by omega)
      have : u + dir 1 = (u.1, u.2 + 1) := by
        have : dir (1 : ZMod 6) = (0, 1) := by decide
        rw [this]; ext <;> simp
      exact h1out (this ▸ h1in)
    have hray : ∀ t : ℕ, (u.1 + (t + 1 : ℕ), u.2) ∈ O ∧ bdryDir S (u.1 + (t + 1 : ℕ), u.2) = 3 := by
      intro t
      induction t with
      | zero =>
        have heq : (u.1 + (1 : ℕ), u.2) = uin := by
          rw [huin_eq, ha0]; have : dir (0 : ZMod 6) = (1, 0) := by decide
          rw [this]; ext <;> simp
        rw [heq]
        refine ⟨huinO, ?_⟩
        rw [hdin_eq, ha0]; decide
      | succ t ih =>
        set vt : Site := (u.1 + (t + 1 : ℕ), u.2)
        have hvtO : vt ∈ O := ih.1
        have hvtB : vt ∈ combBdry S := hOsub hvtO
        have hvt_d : bdryDir S vt = 3 := ih.2
        rcases hObwd vt hvtO with ⟨w, hwO, hphi_w⟩
        have hwB : w ∈ combBdry S := hOsub hwO
        rcases phi_preimage_spec h hwB hphi_w with ⟨aw, hw_eq, haw_in, _, hdw_eq⟩
        have haw0 : aw = 0 := by
          have hne3 : aw ≠ 3 := by
            intro h3
            have hww : w = phi S vt := by
              rw [hw_eq, h3]; unfold phi; rw [hvt_d]
            have : phi S (phi S vt) = vt := by rw [← hww]; exact hphi_w
            exact phi_phi_ne h hvtB this
          have hne45 : aw ≠ 4 ∧ aw ≠ 5 := by
            have hle := huMin w hwO
            rw [hw_eq] at hle; unfold lexLe at hle
            constructor <;> (intro heq; rw [heq] at hle; simp [vt, dir] at hle)
          have hne1 : aw ≠ 1 := by
            intro h1
            rw [h1] at haw_in
            have : vt + dir 1 = (u.1 + (t + 1 : ℕ), u.2 + 1) := by
              have : dir (1 : ZMod 6) = (0, 1) := by decide
              rw [this]; ext <;> simp [vt]
            exact hrow_above (t + 1) (this ▸ haw_in)
          have hne2 : aw ≠ 2 := by
            intro h2
            rw [h2] at haw_in
            have : vt + dir 2 = (u.1 + (t : ℕ), u.2 + 1) := by
              have : dir (2 : ZMod 6) = (-1, 1) := by decide
              rw [this]; ext <;> simp [vt]; omega
            exact hrow_above t (this ▸ haw_in)
          rcases zmod6_cases aw with rfl | rfl | rfl | rfl | rfl | rfl
          · rfl
          · exact absurd rfl hne1
          · exact absurd rfl hne2
          · exact absurd rfl hne3
          · exact absurd rfl hne45.1
          · exact absurd rfl hne45.2
        have heq : (u.1 + (t + 1 + 1 : ℕ), u.2) = w := by
          rw [hw_eq, haw0]; have : dir (0 : ZMod 6) = (1, 0) := by decide
          rw [this]; ext <;> simp [vt]; omega
        rw [heq]
        refine ⟨hwO, ?_⟩
        rw [hdw_eq, haw0]; decide
    let f : ℕ → Site := fun t => (u.1 + (t + 1 : ℕ), u.2)
    have hsub : (Finset.range (S.card + 1)).image f ⊆ S := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨t, _, rfl⟩
      exact (mem_combBdry.mp (hOsub (hray t).1)).1
    have hinj : Set.InjOn f (Finset.range (S.card + 1) : Set ℕ) := by
      intro i _ j _ hij
      have := congrArg Prod.fst hij; dsimp [f] at this; omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
    omega

private lemma finite_perm_orbit {α : Type*} [DecidableEq α] (B : Finset α) (f : α → α)
    (hmaps : ∀ x ∈ B, f x ∈ B) (hinj : Set.InjOn f (B : Set α)) (x0 : α) (hx0 : x0 ∈ B) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ B.card ∧ f^[L] x0 = x0 ∧
      (∀ i j : ℕ, i < L → j < L → f^[i] x0 = f^[j] x0 → i = j) := by
  have hiter_mem : ∀ k : ℕ, f^[k] x0 ∈ B := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  have hex_rep : ∃ L : ℕ, 1 ≤ L ∧ L ≤ B.card ∧ f^[L] x0 = x0 := by
    by_contra hnone
    have hnodup : Set.InjOn (fun k => f^[k] x0) (Finset.range (B.card + 1) : Set ℕ) := by
      intro i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      have hshift : ∀ a b : ℕ, a ≤ b → f^[a] x0 = f^[b] x0 → f^[b - a] x0 = x0 := by
        intro a b hab
        induction a generalizing b with
        | zero => intro h; simpa using h.symm
        | succ a iha =>
          intro h
          have hb1 : 1 ≤ b := by omega
          have hba : b = (b - 1) + 1 := by omega
          rw [hba, Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
          have hprev := hinj (hiter_mem a) (hiter_mem (b - 1)) h
          have hsub : b - (a + 1) = (b - 1) - a := by omega
          rw [hsub]
          exact iha (b - 1) (by omega) hprev
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hnone ⟨j - i, by omega, by omega, hshift i j (by omega) heq⟩
      · exact hnone ⟨i - j, by omega, by omega, hshift j i (by omega) heq.symm⟩
    have hsub : (Finset.range (B.card + 1)).image (fun k => f^[k] x0) ⊆ B := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩
      exact hiter_mem k
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hnodup, Finset.card_range] at hcard
    omega
  let P : ℕ → Prop := fun L => 1 ≤ L ∧ f^[L] x0 = x0
  classical
  have hexP : ∃ L, P L := by rcases hex_rep with ⟨L, h1, _, h2⟩; exact ⟨L, h1, h2⟩
  set L := Nat.find hexP
  have hL : P L := Nat.find_spec hexP
  have hL_le : L ≤ B.card := by
    rcases hex_rep with ⟨L', h1', hle', h2'⟩
    exact le_trans (Nat.find_min' hexP ⟨h1', h2'⟩) hle'
  refine ⟨L, hL.1, hL_le, hL.2, ?_⟩
  intro i j hi hj heq
  by_contra hne
  have hshift : ∀ a b : ℕ, a ≤ b → f^[a] x0 = f^[b] x0 → f^[b - a] x0 = x0 := by
    intro a b hab
    induction a generalizing b with
    | zero => intro h; simpa using h.symm
    | succ a iha =>
      intro h
      have hba : b = (b - 1) + 1 := by omega
      rw [hba, Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
      have hprev := hinj (hiter_mem a) (hiter_mem (b - 1)) h
      have hsub : b - (a + 1) = (b - 1) - a := by omega
      rw [hsub]
      exact iha (b - 1) (by omega) hprev
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact Nat.find_min hexP (m := j - i) (by omega) ⟨by omega, hshift i j (by omega) heq⟩
  · exact Nat.find_min hexP (m := i - j) (by omega) ⟨by omega, hshift j i (by omega) heq.symm⟩

private structure HamCycle (S : Finset Site) (L : List Site) : Prop where
  len_ge3 : 3 ≤ L.length
  nodup : L.Nodup
  mem_iff : ∀ p : Site, p ∈ L ↔ p ∈ S
  adj : ∀ i : ℕ, (hi : i < L.length) →
    unitStep (L[i]'hi) (L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)))

private lemma goodRegion_bdry_cycle {S : Finset Site} (h : GoodRegion S) :
    ∃ C : List Site, HamCycle (combBdry S) C ∧
      ∀ i : ℕ, (hi : i < C.length) →
        C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega)) = phi S (C[i]'hi) := by
  classical
  rcases exists_lexMin S h.nonempty with ⟨umin, huminS, huminMin⟩
  have huminB : umin ∈ combBdry S := lexMin_mem_bdry huminS huminMin
  have hmaps : ∀ u ∈ combBdry S, phi S u ∈ combBdry S := fun u hu => phi_mem_bdry h hu
  have hinj : Set.InjOn (phi S) (combBdry S : Set Site) := phi_injOn h
  rcases finite_perm_orbit (combBdry S) (phi S) hmaps hinj umin huminB with
    ⟨L, hL1, hLle, hLper, hLinj⟩
  have hiter_mem : ∀ k : ℕ, (phi S)^[k] umin ∈ combBdry S := by
    intro k
    induction k with
    | zero => exact huminB
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  -- Every x in combBdry S lies in the orbit of umin
  have hsurj : ∀ x ∈ combBdry S, ∃ k < L, (phi S)^[k] umin = x := by
    intro x hx
    rcases finite_perm_orbit (combBdry S) (phi S) hmaps hinj x hx with
      ⟨Lx, hLx1, _, hLxper, _⟩
    have hiter_x : ∀ k : ℕ, (phi S)^[k] x ∈ combBdry S := by
      intro k
      induction k with
      | zero => exact hx
      | succ k ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
    let Ox := (Finset.range Lx).image fun k => (phi S)^[k] x
    have hOx_ne : Ox.Nonempty := ⟨x, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
    have hOx_sub : Ox ⊆ combBdry S := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩
      exact hiter_x k
    have hOx_fwd : ∀ u ∈ Ox, phi S u ∈ Ox := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      by_cases hlast : k + 1 < Lx
      · exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr hlast,
          Function.iterate_succ_apply' (phi S) k x⟩
      · have hkeq : k + 1 = Lx := by omega
        refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        rw [← Function.iterate_succ_apply' (phi S) k x, Nat.succ_eq_add_one, hkeq, hLxper]; rfl
    have hOx_bwd : ∀ v ∈ Ox, ∃ u ∈ Ox, phi S u = v := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨(phi S)^[Lx - 1] x, Finset.mem_image.mpr ⟨Lx - 1, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
        rw [← Function.iterate_succ_apply' (phi S) (Lx - 1) x, Nat.succ_eq_add_one]
        have : Lx - 1 + 1 = Lx := by omega
        rw [this, hLxper]; rfl
      · refine ⟨(phi S)^[k - 1] x, Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
        rw [← Function.iterate_succ_apply' (phi S) (k - 1) x, Nat.succ_eq_add_one]
        have : k - 1 + 1 = k := by omega
        rw [this]
    rcases phi_orbit_contains_lexMin h hOx_ne hOx_sub hOx_fwd hOx_bwd with ⟨u0, hu0Ox, hu0Min⟩
    have hu0_eq : u0 = umin := by
      have h1 := huminMin u0 (mem_combBdry.mp (hOx_sub hu0Ox)).1
      have h2 := hu0Min umin huminS
      unfold lexLe at h1 h2
      exact Prod.ext (by omega) (by omega)
    rw [hu0_eq] at hu0Ox
    rcases Finset.mem_image.mp hu0Ox with ⟨r0, hr0, hr0_eq⟩
    rw [Finset.mem_range] at hr0
    have hiter_mod : ∀ t : ℕ, (phi S)^[t] umin = (phi S)^[t % L] umin := by
      intro t
      have hdiv := Nat.div_add_mod t L
      have hmul : ∀ q : ℕ, (phi S)^[L * q] umin = umin := by
        intro q
        induction q with
        | zero => rfl
        | succ q ih =>
          rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hLper]
      conv_lhs => rw [← hdiv, add_comm, Function.iterate_add_apply]
      rw [hmul]
    have hback : (phi S)^[Lx - r0] umin = x := by
      rw [← hr0_eq, ← Function.iterate_add_apply]
      have : Lx - r0 + r0 = Lx := by omega
      rw [this, hLxper]
    refine ⟨(Lx - r0) % L, Nat.mod_lt _ (by omega), ?_⟩
    rw [← hiter_mod, hback]
  have hLge3 : 3 ≤ L := by
    by_contra hlt
    have hcases : L = 1 ∨ L = 2 := by omega
    rcases hcases with h1 | h2
    · rw [h1] at hLper; exact phi_ne umin hLper
    · rw [h2] at hLper; exact phi_phi_ne h huminB hLper
  let C : List Site := List.ofFn fun i : Fin L => (phi S)^[i.val] umin
  refine ⟨C, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [C, hLge3]
  · rw [List.nodup_ofFn]
    intro i j hij
    exact Fin.ext (hLinj i.val j.val i.isLt j.isLt hij)
  · intro p
    simp only [C, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩; exact hiter_mem i.val
    · intro hp
      rcases hsurj p hp with ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  · intro i hi
    have hiL : i < L := by simpa [C] using hi
    have hnext : C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega)) = phi S (C[i]'hi) := by
      simp only [C, List.length_ofFn, List.getElem_ofFn]
      by_cases hlast : i + 1 < L
      · rw [Nat.mod_eq_of_lt hlast, Function.iterate_succ_apply' (phi S) i umin]
      · have heq : i + 1 = L := by omega
        rw [heq, Nat.mod_self, ← Function.iterate_succ_apply' (phi S) i umin, Nat.succ_eq_add_one, heq, hLper]; rfl
    rw [hnext]
    exact phi_unitStep _
  · intro i hi
    have hiL : i < L := by simpa [C] using hi
    simp only [C, List.length_ofFn, List.getElem_ofFn]
    by_cases hlast : i + 1 < L
    · rw [Nat.mod_eq_of_lt hlast, Function.iterate_succ_apply' (phi S) i umin]
    · have heq : i + 1 = L := by omega
      rw [heq, Nat.mod_self, ← Function.iterate_succ_apply' (phi S) i umin, Nat.succ_eq_add_one, heq, hLper]; rfl

/- Section 8: Universal Path-Splice and Layer-Merge Lemma -/

private lemma hamCycle_splice_path {B I : Finset Site} {C P : List Site}
    (hC : HamCycle B C) (hdisj : ∀ x, x ∈ B → x ∉ I)
    (hPne : 1 ≤ P.length) (hPnd : P.Nodup) (hPmem : ∀ x, x ∈ P ↔ x ∈ I)
    (hPadj : ∀ j : ℕ, (hj : j + 1 < P.length) →
      unitStep (P[j]'(by omega)) (P[j + 1]'hj))
    {idx : ℕ} (hidx : idx < C.length)
    (hseam1 : unitStep (C[idx]'hidx) (P[0]'(by omega)))
    (hseam2 : unitStep (P[P.length - 1]'(by omega))
      (C[(idx + 1) % C.length]'(Nat.mod_lt _ (by omega)))) :
    ∃ C' : List Site, HamCycle (B ∪ I) C' := by
  set m := C.length
  have hm3 : 3 ≤ m := hC.len_ge3
  set k := P.length
  let Crot : List Site := List.ofFn fun i : Fin m =>
    C[(i.val + idx + 1) % m]'(Nat.mod_lt _ (by omega))
  have hCrot_len : Crot.length = m := by simp [Crot]
  have hCrot_nd : Crot.Nodup := by
    rw [List.nodup_ofFn]
    intro a b hab
    dsimp only at hab
    have hmod : (a.val + idx + 1) % m = (b.val + idx + 1) % m :=
      (hC.nodup.getElem_inj_iff).mp hab
    apply Fin.ext
    have ha := a.isLt; have hb := b.isLt
    have h1 : (a.val + idx + 1) = m * ((a.val + idx + 1) / m) + (a.val + idx + 1) % m :=
      (Nat.div_add_mod _ _).symm
    have h2 : (b.val + idx + 1) = m * ((b.val + idx + 1) / m) + (b.val + idx + 1) % m :=
      (Nat.div_add_mod _ _).symm
    have hq1 : (a.val + idx + 1) / m ≤ 1 := by
      have : a.val + idx + 1 < 2 * m := by omega
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    have hq2 : (b.val + idx + 1) / m ≤ 1 := by
      have : b.val + idx + 1 < 2 * m := by omega
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    have hq1_c : (a.val + idx + 1) / m = 0 ∨ (a.val + idx + 1) / m = 1 := by
      generalize (a.val + idx + 1) / m = q at hq1 ⊢; omega
    have hq2_c : (b.val + idx + 1) / m = 0 ∨ (b.val + idx + 1) / m = 1 := by
      generalize (b.val + idx + 1) / m = q at hq2 ⊢; omega
    rcases hq1_c with hq1' | hq1' <;> rcases hq2_c with hq2' | hq2' <;>
      (rw [hq1'] at h1; rw [hq2'] at h2; omega)
  have hCrot_mem : ∀ x, x ∈ Crot ↔ x ∈ B := by
    intro x
    rw [← hC.mem_iff]
    simp only [Crot, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩; exact List.getElem_mem _
    · intro hx
      rcases List.mem_iff_getElem.mp hx with ⟨j, hj, rfl⟩
      set i0 := (j + m - (idx + 1) % m) % m
      refine ⟨⟨i0, Nat.mod_lt _ (by omega)⟩, ?_⟩
      congr 1
      have : (i0 + idx + 1) % m = j := by
        dsimp only [i0]
        rw [Nat.add_assoc, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h1 : j + m - (idx + 1) % m + (idx + 1) =
            j + m + (m * ((idx + 1) / m)) := by
          have := Nat.div_add_mod (idx + 1) m
          have : (idx + 1) % m < m := Nat.mod_lt _ (by omega)
          omega
        rw [h1]
        have h2 : j + m + m * ((idx + 1) / m) = j + m * ((idx + 1) / m + 1) := by ring
        rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      exact this
  let C' := Crot ++ P
  refine ⟨C', ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [C', hCrot_len]; omega
  · rw [List.nodup_append]
    refine ⟨hCrot_nd, hPnd, fun x hx y hy hxy => ?_⟩
    subst hxy
    exact hdisj x ((hCrot_mem x).mp hx) ((hPmem x).mp hy)
  · intro x
    simp only [C', List.mem_append, Finset.mem_union, hCrot_mem, hPmem]
  · intro i hi
    have hlen : C'.length = m + k := by simp [C', hCrot_len, k]
    by_cases h1 : i + 1 < m
    · have hi_m : i < m := by omega
      have hget1 : C'[i]'hi = C[(i + idx + 1) % m]'(Nat.mod_lt _ (by omega)) := by
        simp [C', List.getElem_append_left (hCrot_len ▸ hi_m), Crot]
      have hget2 : C'[(i + 1) % C'.length]'(Nat.mod_lt _ (by omega)) =
          C[((i + idx + 1) % m + 1) % m]'(Nat.mod_lt _ (by omega)) := by
        have hmod : (i + 1) % C'.length = i + 1 := Nat.mod_eq_of_lt (by omega)
        simp only [hmod, C', List.getElem_append_left (hCrot_len ▸ h1), Crot, List.getElem_ofFn]
        congr 1
        rw [Nat.add_mod ((i + idx + 1) % m), Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      rw [hget1, hget2]
      exact hC.adj _ _
    · by_cases h2 : i + 1 = m
      · have hi_m : i < m := by omega
        have hget1 : C'[i]'hi = C[idx]'hidx := by
          simp only [C', List.getElem_append_left (hCrot_len ▸ hi_m), Crot, List.getElem_ofFn]
          congr 1
          have : i + idx + 1 = idx + m := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
        have hget2 : C'[(i + 1) % C'.length]'(Nat.mod_lt _ (by omega)) = P[0]'(by omega) := by
          have hmod : (i + 1) % C'.length = m := by rw [Nat.mod_eq_of_lt (by omega), h2]
          simp only [hmod, C']
          rw [List.getElem_append_right (by omega)]
          simp only [hCrot_len, Nat.sub_self]
        rw [hget1, hget2]
        exact hseam1
      · by_cases h3 : i + 1 < m + k
        · have hi_ge : Crot.length ≤ i := by omega
          have hget1 : C'[i]'hi = P[i - m]'(by omega) := by
            simp only [C', List.getElem_append_right hi_ge, hCrot_len]
          have hget2 : C'[(i + 1) % C'.length]'(Nat.mod_lt _ (by omega)) =
              P[(i - m) + 1]'(by omega) := by
            have hmod : (i + 1) % C'.length = i + 1 := Nat.mod_eq_of_lt (by omega)
            have hi1_ge : Crot.length ≤ i + 1 := by omega
            simp only [hmod, C', List.getElem_append_right hi1_ge, hCrot_len]
            congr 1; omega
          rw [hget1, hget2]
          exact hPadj (i - m) (by omega)
        · have hlast : i + 1 = m + k := by omega
          have hi_ge : Crot.length ≤ i := by omega
          have hget1 : C'[i]'hi = P[P.length - 1]'(by omega) := by
            simp only [C', List.getElem_append_right hi_ge, hCrot_len]
            congr 1; omega
          have hget2 : C'[(i + 1) % C'.length]'(Nat.mod_lt _ (by omega)) =
              C[(idx + 1) % m]'(Nat.mod_lt _ (by omega)) := by
            have hmod0 : (i + 1) % C'.length = 0 := by rw [hlen, hlast, Nat.mod_self]
            simp only [hmod0, C', List.getElem_append_left (by omega : 0 < Crot.length),
              Crot, List.getElem_ofFn, zero_add]
          rw [hget1, hget2]
          exact hseam2

private lemma hamCycle_to_path_fwd {I : Finset Site} {C : List Site} (hC : HamCycle I C)
    {j : ℕ} (hj : j < C.length) :
    ∃ P : List Site, 1 ≤ P.length ∧ P.Nodup ∧ (∀ x, x ∈ P ↔ x ∈ I) ∧
      (∀ t : ℕ, (ht : t + 1 < P.length) → unitStep (P[t]'(by omega)) (P[t + 1]'ht)) ∧
      (∀ h0 : 0 < P.length, P[0]'h0 = C[(j + 1) % C.length]'(Nat.mod_lt _ (by omega))) ∧
      (∀ hl : P.length - 1 < P.length, P[P.length - 1]'hl = C[j]'hj) := by
  set m := C.length
  have hm3 : 3 ≤ m := hC.len_ge3
  let P : List Site := List.ofFn fun i : Fin m =>
    C[(i.val + j + 1) % m]'(Nat.mod_lt _ (by omega))
  refine ⟨P, by simp [P]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro a b hab
    dsimp only at hab
    have hmod : (a.val + j + 1) % m = (b.val + j + 1) % m :=
      (hC.nodup.getElem_inj_iff).mp hab
    apply Fin.ext
    have ha := a.isLt; have hb := b.isLt
    have h1 := (Nat.div_add_mod (a.val + j + 1) m).symm
    have h2 := (Nat.div_add_mod (b.val + j + 1) m).symm
    have hq1 : (a.val + j + 1) / m ≤ 1 :=
      Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    have hq2 : (b.val + j + 1) / m ≤ 1 :=
      Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    have hq1_c : (a.val + j + 1) / m = 0 ∨ (a.val + j + 1) / m = 1 := by
      generalize (a.val + j + 1) / m = q at hq1 ⊢; omega
    have hq2_c : (b.val + j + 1) / m = 0 ∨ (b.val + j + 1) / m = 1 := by
      generalize (b.val + j + 1) / m = q at hq2 ⊢; omega
    rcases hq1_c with hq1' | hq1' <;> rcases hq2_c with hq2' | hq2' <;>
      (rw [hq1'] at h1; rw [hq2'] at h2; omega)
  · intro x
    rw [← hC.mem_iff]
    simp only [P, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩; exact List.getElem_mem _
    · intro hx
      rcases List.mem_iff_getElem.mp hx with ⟨a, ha, rfl⟩
      set i0 := (a + m - (j + 1) % m) % m
      refine ⟨⟨i0, Nat.mod_lt _ (by omega)⟩, ?_⟩
      congr 1
      dsimp only [i0]
      rw [Nat.add_assoc, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h1 : a + m - (j + 1) % m + (j + 1) = a + m + m * ((j + 1) / m) := by
        have := Nat.div_add_mod (j + 1) m
        have : (j + 1) % m < m := Nat.mod_lt _ (by omega)
        omega
      rw [h1]
      have h2 : a + m + m * ((j + 1) / m) = a + m * ((j + 1) / m + 1) := by ring
      rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · intro t ht
    simp only [P, List.getElem_ofFn]
    have heq : (t + 1 + j + 1) % m = ((t + j + 1) % m + 1) % m := by
      rw [Nat.add_mod ((t + j + 1) % m), Nat.mod_mod, ← Nat.add_mod]; congr 1; omega
    simp only [heq]
    exact hC.adj _ _
  · intro _; simp only [P, List.getElem_ofFn, zero_add]; rfl
  · intro _
    simp only [P, List.length_ofFn, List.getElem_ofFn]
    congr 1
    have : m - 1 + j + 1 = j + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

private lemma hamCycle_to_path_bwd {I : Finset Site} {C : List Site} (hC : HamCycle I C)
    {j : ℕ} (hj : j < C.length) :
    ∃ P : List Site, 1 ≤ P.length ∧ P.Nodup ∧ (∀ x, x ∈ P ↔ x ∈ I) ∧
      (∀ t : ℕ, (ht : t + 1 < P.length) → unitStep (P[t]'(by omega)) (P[t + 1]'ht)) ∧
      (∀ h0 : 0 < P.length, P[0]'h0 = C[j]'hj) ∧
      (∀ hl : P.length - 1 < P.length, P[P.length - 1]'hl = C[(j + 1) % C.length]'(Nat.mod_lt _ (by omega))) := by
  rcases hamCycle_to_path_fwd hC hj with ⟨P, hlen, hnd, hmem, hadj, h0, hlast⟩
  refine ⟨P.reverse, by simp [hlen], List.nodup_reverse.mpr hnd, by simpa using hmem, ?_, ?_, ?_⟩
  · intro t ht
    have hlt : t + 1 < P.length := by simpa using ht
    rw [List.getElem_reverse, List.getElem_reverse]
    have heq : P.length - 1 - t = (P.length - 1 - (t + 1)) + 1 := by omega
    simp only [heq]
    exact unitStep_symm (hadj (P.length - 1 - (t + 1)) (by omega))
  · intro _; rw [List.getElem_reverse]; simpa using hlast (by omega)
  · intro _; rw [List.getElem_reverse]
    have : P.length - 1 - (P.reverse.length - 1) = 0 := by simp
    simpa [this] using h0 (by omega)

private def star13 (v : Site) : Finset Site :=
  {v} ∪ (Finset.univ.image fun d : ZMod 6 => v + dir d) ∪
    (Finset.univ.image fun d : ZMod 6 => v + dir d + dir (d + 1))

private lemma goodRegion_merge_singleton {S : Finset Site} (h : GoodRegion S) {v : Site}
    (hint : combInt S = {v}) (hne_star : S ≠ star13 v) :
    ∃ C : List Site, HamCycle S C := by
  classical
  rcases goodRegion_bdry_cycle h with ⟨C, hC, hCphi⟩
  have hvI : v ∈ combInt S := by rw [hint]; exact Finset.mem_singleton_self v
  have hvS : v ∈ S := (mem_combInt.mp hvI).1
  have hring : ∀ d : ZMod 6, v + dir d ∈ S := (mem_combInt.mp hvI).2
  have hring_bdry : ∀ d : ZMod 6, v + dir d ∈ combBdry S := by
    intro d
    rw [combBdry, Finset.mem_sdiff, hint, Finset.mem_singleton]
    refine ⟨hring d, fun heq => dir_ne_zero d ?_⟩
    have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq
    exact Prod.ext (by simp at h1; omega) (by simp at h2; omega)
  have hex_edge : ∃ u ∈ combBdry S, unitStep u v ∧ unitStep (phi S u) v := by
    by_contra hnone
    push Not at hnone
    have ha_in : ∀ d : ZMod 6, v + dir d + dir (d + 1) ∈ S := by
      intro d
      by_contra ha_out
      set ud := v + dir d
      have hudB := hring_bdry d
      have h2in : ud + dir (d + 2) ∈ S := by
        have : ud + dir (d + 2) = v + dir (d + 1) := by
          unfold ud; have h2 := dir_add_two_eq d
          ext <;> simp [h2]
        rw [this]; exact hring (d + 1)
      have h1out : ud + dir (d + 2 - 1) ∉ S := by
        have h1 : d + 2 - 1 = d + 1 := by ring
        rw [h1]; exact ha_out
      have hd_eq : bdryDir S ud = d + 2 := bdryDir_unique h hudB h2in h1out
      have hphi_eq : phi S ud = v + dir (d + 1) := by
        unfold phi; rw [hd_eq]; unfold ud
        have h2 := dir_add_two_eq d
        ext <;> simp [h2]
      have hbad := hnone ud hudB (unitStep_symm (unitStep_add_dir v d))
      rw [hphi_eq] at hbad
      exact hbad (unitStep_symm (unitStep_add_dir v (d + 1)))
    have h2e_out : ∀ d : ZMod 6, v + dir d + dir d ∉ S := by
      intro d h2in
      set ud := v + dir d
      have hud_all : ∀ c : ZMod 6, ud + dir c ∈ S := by
        intro c
        obtain ⟨diff, hc⟩ : ∃ diff : ZMod 6, c = d + diff := ⟨c - d, by ring⟩
        rw [hc]
        rcases zmod6_cases diff with rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [ud] using h2in
        · simpa [ud] using ha_in d
        · have : ud + dir (d + 2) = v + dir (d + 1) := by
            unfold ud; have h2 := dir_add_two_eq d; ext <;> simp [h2]
          rw [this]; exact hring (d + 1)
        · have : ud + dir (d + 3) = v := by
            unfold ud; have h3 := dir_add_three d; ext <;> simp [h3]
          rw [this]; exact hvS
        · have : ud + dir (d + 4) = v + dir (d - 1) := by
            unfold ud; have h4 := dir_sub_one_sub d; ext <;> simp [← h4]
          rw [this]; exact hring (d - 1)
        · have : ud + dir (d + 5) = v + dir (d - 1) + dir ((d - 1) + 1) := by
            unfold ud
            have : ∀ x : ZMod 6, dir x + dir (x + 5) = dir (x - 1) + dir (x - 1 + 1) := by
              decide
            have hx := this d
            have h1 := congrArg Prod.fst hx; have h2 := congrArg Prod.snd hx
            ext <;> simp at h1 h2 ⊢ <;> omega
          rw [this]; exact ha_in (d - 1)
      have hudI : ud ∈ combInt S := mem_combInt.mpr ⟨hring d, hud_all⟩
      exact (Finset.mem_sdiff.mp (hring_bdry d)).2 hudI
    have hstar_sub : star13 v ⊆ S := by
      intro z hz
      simp only [star13, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and] at hz
      rcases hz with (rfl | ⟨d, rfl⟩) | ⟨d, rfl⟩
      · exact hvS
      · exact hring d
      · exact ha_in d
    have hclosed : ∀ x ∈ star13 v, ∀ y ∈ S, unitStep x y → y ∈ star13 v := by
      intro x hx y hy hxy
      rcases (unitStep_iff_exists_dir x y).mp hxy with ⟨c, rfl⟩
      simp only [star13, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and] at hx ⊢
      rcases hx with (rfl | ⟨d, rfl⟩) | ⟨d, rfl⟩
      · exact Or.inl (Or.inr ⟨c, rfl⟩)
      · obtain ⟨diff, hc⟩ : ∃ diff : ZMod 6, c = d + diff := ⟨c - d, by ring⟩
        rw [hc] at hy ⊢
        rcases zmod6_cases diff with rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; exact h2e_out d (by simpa using hy)
        · exact Or.inr ⟨d, rfl⟩
        · refine Or.inl (Or.inr ⟨d + 1, ?_⟩)
          have h2 := dir_add_two_eq d; ext <;> simp [h2]
        · refine Or.inl (Or.inl ?_)
          have h3 := dir_add_three d; ext <;> simp [h3]
        · refine Or.inl (Or.inr ⟨d - 1, ?_⟩)
          have h4 := dir_sub_one_sub d; ext <;> simp [← h4]
        · refine Or.inr ⟨d - 1, ?_⟩
          have : ∀ t : ZMod 6, dir t + dir (t + 5) = dir (t - 1) + dir (t - 1 + 1) := by decide
          have ht := this d
          have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
          ext <;> simp at h1 h2 ⊢ <;> omega
      · set ad := v + dir d + dir (d + 1)
        have ha_arc := h.loc ad (ha_in d)
        have ha_shift : IsArc (fun t => ad + dir (t + d) ∈ S) := by
          exact isArc_shift (-d) (by simpa [add_assoc] using ha_arc)
        have h3in : ad + dir (3 + d) ∈ S := by
          have : ∀ t : ZMod 6, dir t + dir (t + 1) + dir (3 + t) = dir (t + 1) := by decide
          have ht := this d
          have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
          have heq : ad + dir (3 + d) = v + dir (d + 1) := by
            unfold ad; ext <;> simp at h1 h2 ⊢ <;> omega
          rw [heq]; exact hring (d + 1)
        have h2out : ad + dir (2 + d) ∉ S := by
          have : ∀ t : ZMod 6, dir t + dir (t + 1) + dir (2 + t) = dir (t + 1) + dir (t + 1) := by decide
          have ht := this d
          have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
          have heq : ad + dir (2 + d) = v + dir (d + 1) + dir (d + 1) := by
            unfold ad; ext <;> simp at h1 h2 ⊢ <;> omega
          rw [heq]; exact h2e_out (d + 1)
        have h5out : ad + dir (5 + d) ∉ S := by
          have : ∀ t : ZMod 6, dir t + dir (t + 1) + dir (5 + t) = dir t + dir t := by decide
          have ht := this d
          have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
          have heq : ad + dir (5 + d) = v + dir d + dir d := by
            unfold ad; ext <;> simp at h1 h2 ⊢ <;> omega
          rw [heq]; exact h2e_out d
        have h0out : ad + dir (0 + d) ∉ S :=
          (isArc_gap_forces ha_shift (a := 3) (b := 2) (c := 5) (d := 0)
            h3in h2out h5out).2.2.2 ⟨rfl, rfl, rfl, Or.inl rfl⟩
        have h1out : ad + dir (1 + d) ∉ S :=
          (isArc_gap_forces ha_shift (a := 3) (b := 2) (c := 5) (d := 1)
            h3in h2out h5out).2.2.2 ⟨rfl, rfl, rfl, Or.inr rfl⟩
        obtain ⟨diff, hc⟩ : ∃ diff : ZMod 6, c = diff + d := ⟨c - d, by ring⟩
        rw [hc] at hy ⊢
        rcases zmod6_cases diff with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hy h0out
        · exact absurd hy h1out
        · exact absurd hy h2out
        · refine Or.inl (Or.inr ⟨d + 1, ?_⟩)
          have : ∀ t : ZMod 6, dir t + dir (t + 1) + dir (3 + t) = dir (t + 1) := by decide
          have ht := this d
          have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
          unfold ad; ext <;> simp at h1 h2 ⊢ <;> omega
        · refine Or.inl (Or.inr ⟨d, ?_⟩)
          have : ∀ t : ZMod 6, dir t + dir (t + 1) + dir (4 + t) = dir t := by decide
          have ht := this d
          have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
          unfold ad; ext <;> simp at h1 h2 ⊢ <;> omega
        · exact absurd hy h5out
    have hS_eq : S = star13 v := by
      apply Finset.Subset.antisymm _ hstar_sub
      intro z hz
      have hr := h.conn v hvS z hz
      have hreach_closed : ∀ a b, Reach S a b → a ∈ star13 v → b ∈ star13 v := by
        intro a b hreach
        induction hreach using Relation.ReflTransGen.head_induction_on with
        | refl => exact id
        | @head a c hstep _ ih =>
          intro ha
          exact ih (hclosed a ha c hstep.2.1 hstep.2.2)
      exact hreach_closed v z hr (by simp [star13])
    exact hne_star hS_eq
  rcases hex_edge with ⟨u, huB, huv, hphiv⟩
  rcases List.mem_iff_getElem.mp ((hC.mem_iff u).mpr huB) with ⟨idx, hidx, huidx⟩
  have hnext : C[(idx + 1) % C.length]'(Nat.mod_lt _ (by omega)) = phi S u := by
    rw [hCphi idx hidx, huidx]
  have hdisj : ∀ x, x ∈ combBdry S → x ∉ ({v} : Finset Site) := by
    intro x hx hxv
    rw [Finset.mem_singleton.mp hxv] at hx
    exact (Finset.mem_sdiff.mp hx).2 hvI
  have hunion : combBdry S ∪ ({v} : Finset Site) = S := by
    rw [← hint, combBdry, Finset.sdiff_union_of_subset]
    intro x hx; exact (mem_combInt.mp hx).1
  rw [← hunion]
  refine hamCycle_splice_path hC hdisj (P := [v]) (by simp) (by simp) (by simp)
    (fun j hj => by simp at hj) hidx ?_ ?_
  · simpa [huidx] using huv
  · simpa [hnext] using unitStep_symm hphiv

private lemma universal_rhombus_bridge {S : Finset Site} (h : GoodRegion S)
    {v0 v1 : Site} {d : ZMod 6}
    (hv0 : v0 ∈ combInt S) (hv1 : v1 ∈ combInt S)
    (hv1_eq : v1 = v0 + dir d) (hu2_out : v0 + dir (d - 1) ∉ combInt S) :
    ∃ u ∈ combBdry S, unitStep u v0 ∧ unitStep (phi S u) v1 := by
  set u1 := v0 + dir (d - 2)
  set u2 := v0 + dir (d - 1)
  set u3 := v1 + dir (d - 1)
  have hu1S : u1 ∈ S := (mem_combInt.mp hv0).2 (d - 2)
  have hu2S : u2 ∈ S := (mem_combInt.mp hv0).2 (d - 1)
  have hu3S : u3 ∈ S := (mem_combInt.mp hv1).2 (d - 1)
  have hu2B : u2 ∈ combBdry S := Finset.mem_sdiff.mpr ⟨hu2S, hu2_out⟩
  have hu2_d : u2 + dir d = u3 := by
    unfold u2 u3; rw [hv1_eq]; ext <;> simp <;> ring
  have hu2_d1 : u2 + dir (d + 1) = v1 := by
    unfold u2; rw [hv1_eq]
    have : ∀ t : ZMod 6, dir (t - 1) + dir (t + 1) = dir t := by
      intro t; fin_cases t <;> decide
    have ht := this d
    have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
    ext <;> simp at h1 h2 ⊢ <;> omega
  have hu2_d2 : u2 + dir (d + 2) = v0 := by
    unfold u2
    have : ∀ t : ZMod 6, dir (t - 1) + dir (t + 2) = (0, 0) := by
      intro t; fin_cases t <;> decide
    have ht := this d
    have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
    ext <;> simp at h1 h2 ⊢ <;> omega
  have hu2_d3 : u2 + dir (d + 3) = u1 := by
    unfold u2 u1
    have : ∀ t : ZMod 6, dir (t - 1) + dir (t + 3) = dir (t - 2) := by
      intro t; fin_cases t <;> decide
    have ht := this d
    have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
    ext <;> simp at h1 h2 ⊢ <;> omega
  by_cases h5 : u2 + dir (d + 5) ∉ S
  · have hd_u2 : bdryDir S u2 = d := by
      refine bdryDir_unique h hu2B (hu2_d ▸ hu3S) ?_
      have : d - 1 = d + 5 := (by decide : ∀ x : ZMod 6, x - 1 = x + 5) d
      rw [this]; exact h5
    refine ⟨u2, hu2B, unitStep_symm (unitStep_add_dir v0 (d - 1)), ?_⟩
    have hphi : phi S u2 = u3 := by unfold phi; rw [hd_u2]; exact hu2_d
    rw [hphi]
    exact unitStep_symm (unitStep_add_dir v1 (d - 1))
  · push Not at h5
    have h4 : u2 + dir (d + 4) ∉ S := by
      intro h4in
      have hall : ∀ c : ZMod 6, u2 + dir c ∈ S := by
        intro c
        obtain ⟨diff, hc⟩ : ∃ diff : ZMod 6, c = d + diff := ⟨c - d, by ring⟩
        rw [hc]
        rcases zmod6_cases diff with rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [hu2_d] using hu3S
        · simpa [hu2_d1] using (mem_combInt.mp hv1).1
        · simpa [hu2_d2] using (mem_combInt.mp hv0).1
        · simpa [hu2_d3] using hu1S
        · exact h4in
        · exact h5
      exact hu2_out (mem_combInt.mpr ⟨hu2S, hall⟩)
    have hu1_d : u1 + dir d = u2 := by
      unfold u1 u2
      have : ∀ t : ZMod 6, dir (t - 2) + dir t = dir (t - 1) := by decide
      have ht := this d
      have h1 := congrArg Prod.fst ht; have h2 := congrArg Prod.snd ht
      ext <;> simp at h1 h2 ⊢ <;> omega
    have hu1_d5 : u1 + dir (d - 1) = u2 + dir (d + 4) := by
      rw [← hu2_d3]
      have h35 := dir_add_three_add_five d
      have h1 : d - 1 = d + 5 := (by decide : ∀ x : ZMod 6, x - 1 = x + 5) d
      rw [h1]
      have ha := congrArg Prod.fst h35; have hb := congrArg Prod.snd h35
      ext <;> simp at ha hb ⊢ <;> omega
    have hu1B : u1 ∈ combBdry S := mem_combBdry.mpr ⟨hu1S, d - 1, hu1_d5 ▸ h4⟩
    have hd_u1 : bdryDir S u1 = d := bdryDir_unique h hu1B (hu1_d ▸ hu2S) (hu1_d5 ▸ h4)
    refine ⟨u1, hu1B, unitStep_symm (unitStep_add_dir v0 (d - 2)), ?_⟩
    have hphi : phi S u1 = u2 := by unfold phi; rw [hd_u1]; exact hu1_d
    rw [hphi, ← hu2_d1]
    exact unitStep_add_dir u2 (d + 1)

private lemma goodRegion_merge_pair {S : Finset Site} (h : GoodRegion S) {v0 v1 : Site}
    (hint : combInt S = {v0, v1}) (hstep : unitStep v0 v1) :
    ∃ C : List Site, HamCycle S C := by
  classical
  rcases goodRegion_bdry_cycle h with ⟨C, hC, hCphi⟩
  rcases (unitStep_iff_exists_dir v0 v1).mp hstep with ⟨d, hv1_eq⟩
  have hv0I : v0 ∈ combInt S := by rw [hint]; simp
  have hv1I : v1 ∈ combInt S := by rw [hint]; simp
  have hne : v0 ≠ v1 := by
    intro heq
    rw [hv1_eq] at heq
    have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq
    exact dir_ne_zero d (Prod.ext (by simp at h1; omega) (by simp at h2; omega))
  have hu2_out : v0 + dir (d - 1) ∉ combInt S := by
    rw [hint, Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq)
    · have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq
      exact dir_ne_zero (d - 1) (Prod.ext (by simp at h1; omega) (by simp at h2; omega))
    · rw [hv1_eq] at heq
      have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq
      have hd_eq : d - 1 = d := dir_inj (Prod.ext (by simp at h1; omega) (by simp at h2; omega))
      have : (-1 : ZMod 6) = 0 := by linear_combination hd_eq
      revert this; decide
  rcases universal_rhombus_bridge h hv0I hv1I hv1_eq hu2_out with ⟨u, huB, huv0, hphiv1⟩
  rcases List.mem_iff_getElem.mp ((hC.mem_iff u).mpr huB) with ⟨idx, hidx, huidx⟩
  have hnext : C[(idx + 1) % C.length]'(Nat.mod_lt _ (by omega)) = phi S u := by
    rw [hCphi idx hidx, huidx]
  have hdisj : ∀ x, x ∈ combBdry S → x ∉ ({v0, v1} : Finset Site) := by
    intro x hx hxI
    rw [← hint] at hxI
    exact (Finset.mem_sdiff.mp hx).2 hxI
  have hunion : combBdry S ∪ ({v0, v1} : Finset Site) = S := by
    rw [← hint, combBdry, Finset.sdiff_union_of_subset]
    intro x hx; exact (mem_combInt.mp hx).1
  rw [← hunion]
  refine hamCycle_splice_path hC hdisj (P := [v0, v1]) (by simp)
    (by simp [hne]) (by intro x; simp) (fun j hj => by
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0; simpa using hstep) hidx ?_ ?_
  · simpa [huidx] using huv0
  · simpa [hnext] using unitStep_symm hphiv1

private lemma goodRegion_merge_cycle {S : Finset Site} (h : GoodRegion S) {Cin : List Site}
    (hCin : HamCycle (combInt S) Cin) :
    ∃ C : List Site, HamCycle S C := by
  classical
  rcases goodRegion_bdry_cycle h with ⟨Cout, hCout, hCout_phi⟩
  set I := combInt S
  have hIne : I.Nonempty := by
    have h0 : 0 < Cin.length := by have := hCin.len_ge3; omega
    exact ⟨Cin[0]'h0, (hCin.mem_iff _).mp (List.getElem_mem h0)⟩
  rcases exists_lexMin I hIne with ⟨v0, hv0I, hv0Min⟩
  rcases List.mem_iff_getElem.mp ((hCin.mem_iff v0).mpr hv0I) with ⟨j, hj, hv0_eq⟩
  set m := Cin.length
  have hm3 : 3 ≤ m := hCin.len_ge3
  set j_next := (j + 1) % m
  set j_prev := (j + m - 1) % m
  have hj_next : j_next < m := Nat.mod_lt _ (by omega)
  have hj_prev : j_prev < m := Nat.mod_lt _ (by omega)
  have hj_prev_succ : (j_prev + 1) % Cin.length = j := by
    dsimp only [j_prev, m]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : j + Cin.length - 1 + 1 = j + Cin.length := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  set vn := Cin[j_next]'hj_next
  set vp := Cin[j_prev]'hj_prev
  have hvnI : vn ∈ I := (hCin.mem_iff _).mp (List.getElem_mem hj_next)
  have hvpI : vp ∈ I := (hCin.mem_iff _).mp (List.getElem_mem hj_prev)
  have hstep_n : unitStep v0 vn := by rw [← hv0_eq]; exact hCin.adj j hj
  have hstep_p : unitStep v0 vp := by
    have h1 := hCin.adj j_prev hj_prev
    simp only [hj_prev_succ, hv0_eq] at h1
    exact unitStep_symm h1
  have hne_np : vn ≠ vp := by
    intro heq
    have hmod : j_next = j_prev := (hCin.nodup.getElem_inj_iff).mp heq
    dsimp only [j_next, j_prev] at hmod
    by_cases hjm : j + 1 < m
    · rw [Nat.mod_eq_of_lt hjm] at hmod
      by_cases hj0 : j = 0
      · subst hj0; rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · have : j + m - 1 = (j - 1) + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmod; omega
    · have hjeq : j = m - 1 := by omega
      subst hjeq
      have h1 : (m - 1 + 1) % m = 0 := by
        have : m - 1 + 1 = m := by omega
        rw [this, Nat.mod_self]
      have h2 : (m - 1 + m - 1) % m = m - 2 := by
        have : m - 1 + m - 1 = (m - 2) + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  rcases (unitStep_iff_exists_dir v0 vn).mp hstep_n with ⟨dn, hvn_eq⟩
  rcases (unitStep_iff_exists_dir v0 vp).mp hstep_p with ⟨dp, hvp_eq⟩
  have hdn_012 : dn = 0 ∨ dn = 1 ∨ dn = 2 := by
    have hle := hv0Min vn hvnI; rw [hvn_eq] at hle; unfold lexLe at hle
    rcases zmod6_cases dn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exfalso; simp [dir] at hle
    · exfalso; simp [dir] at hle
    · exfalso; simp [dir] at hle
  have hdp_012 : dp = 0 ∨ dp = 1 ∨ dp = 2 := by
    have hle := hv0Min vp hvpI; rw [hvp_eq] at hle; unfold lexLe at hle
    rcases zmod6_cases dp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exfalso; simp [dir] at hle
    · exfalso; simp [dir] at hle
    · exfalso; simp [dir] at hle
  have hd_ne : dn ≠ dp := by
    intro heq; apply hne_np; rw [hvn_eq, hvp_eq, heq]
  have hdisj : ∀ x, x ∈ combBdry S → x ∉ I := fun x hx => (Finset.mem_sdiff.mp hx).2
  have hunion : combBdry S ∪ I = S := by
    unfold I combBdry; rw [Finset.sdiff_union_of_subset]
    intro x hx; exact (mem_combInt.mp hx).1
  have h5_out : v0 + dir 5 ∉ I := by
    intro h5
    have hle := hv0Min _ h5; have : dir (5 : ZMod 6) = (1, -1) := by decide
    rw [this] at hle; unfold lexLe at hle; simp at hle
  have h3_out : v0 + dir 3 ∉ I := by
    intro h3
    have hle := hv0Min _ h3; have : dir (3 : ZMod 6) = (-1, 0) := by decide
    rw [this] at hle; unfold lexLe at hle; simp at hle
  have h0_sub1 : (0 : ZMod 6) - 1 = 5 := by decide
  have hor : dn = 0 ∨ dn = 2 ∨ dp = 0 ∨ dp = 2 := by
    rcases hdn_012 with rfl | rfl | rfl <;> rcases hdp_012 with rfl | rfl | rfl <;> simp_all
  rw [← hunion]
  rcases hor with rfl | rfl | rfl | rfl
  · -- dn = 0: bridge (v0, vn, d = 0), splice backward path P from v0 to vn
    rcases universal_rhombus_bridge h hv0I hvnI hvn_eq (h0_sub1.symm ▸ h5_out) with
      ⟨u, huB, huv0, hphivn⟩
    rcases List.mem_iff_getElem.mp ((hCout.mem_iff u).mpr huB) with ⟨idx, hidx, huidx⟩
    have hnext : Cout[(idx + 1) % Cout.length]'(Nat.mod_lt _ (by omega)) = phi S u := by
      rw [hCout_phi idx hidx, huidx]
    rcases hamCycle_to_path_bwd hCin hj with ⟨P, hPlen, hPnd, hPmem, hPadj, hP0, hPlast⟩
    refine hamCycle_splice_path hCout hdisj hPlen hPnd hPmem hPadj hidx ?_ ?_
    · rw [huidx, hP0 (by omega), hv0_eq]; exact huv0
    · rw [hPlast (by omega), hnext]; exact unitStep_symm hphivn
  · -- dn = 2: swap (vn, v0, d = 5), splice forward path P from vn to v0
    have hv0_from_vn : v0 = vn + dir 5 := by
      rw [hvn_eq]; have : dir (2 : ZMod 6) + dir (5 : ZMod 6) = (0, 0) := by decide
      have h1 := congrArg Prod.fst this; have h2 := congrArg Prod.snd this
      ext <;> simp at h1 h2 ⊢ <;> omega
    have hu2_out : vn + dir (5 - 1) ∉ I := by
      have heq : vn + dir (5 - 1) = v0 + dir 3 := by
        rw [hvn_eq]; have : dir (2 : ZMod 6) + dir ((5 : ZMod 6) - 1) = dir (3 : ZMod 6) := by decide
        have h1 := congrArg Prod.fst this; have h2 := congrArg Prod.snd this
        ext <;> simp at h1 h2 ⊢ <;> omega
      rw [heq]; exact h3_out
    rcases universal_rhombus_bridge h hvnI hv0I hv0_from_vn hu2_out with ⟨u, huB, huvn, hphiv0⟩
    rcases List.mem_iff_getElem.mp ((hCout.mem_iff u).mpr huB) with ⟨idx, hidx, huidx⟩
    have hnext : Cout[(idx + 1) % Cout.length]'(Nat.mod_lt _ (by omega)) = phi S u := by
      rw [hCout_phi idx hidx, huidx]
    rcases hamCycle_to_path_fwd hCin hj with ⟨P, hPlen, hPnd, hPmem, hPadj, hP0, hPlast⟩
    refine hamCycle_splice_path hCout hdisj hPlen hPnd hPmem hPadj hidx ?_ ?_
    · rw [huidx, hP0 (by omega)]; exact huvn
    · rw [hPlast (by omega), hv0_eq, hnext]; exact unitStep_symm hphiv0
  · -- dp = 0: bridge (v0, vp, d = 0), splice forward path P from v0 = Cin[(j_prev+1)%m] to vp = Cin[j_prev]
    rcases universal_rhombus_bridge h hv0I hvpI hvp_eq (h0_sub1.symm ▸ h5_out) with
      ⟨u, huB, huv0, hphivp⟩
    rcases List.mem_iff_getElem.mp ((hCout.mem_iff u).mpr huB) with ⟨idx, hidx, huidx⟩
    have hnext : Cout[(idx + 1) % Cout.length]'(Nat.mod_lt _ (by omega)) = phi S u := by
      rw [hCout_phi idx hidx, huidx]
    rcases hamCycle_to_path_fwd hCin hj_prev with ⟨P, hPlen, hPnd, hPmem, hPadj, hP0, hPlast⟩
    refine hamCycle_splice_path hCout hdisj hPlen hPnd hPmem hPadj hidx ?_ ?_
    · rw [huidx, hP0 (by omega)]; simp only [hj_prev_succ, hv0_eq]; exact huv0
    · rw [hPlast (by omega), hnext]; exact unitStep_symm hphivp
  · -- dp = 2: swap (vp, v0, d = 5), splice backward path P from vp = Cin[j_prev] to v0 = Cin[(j_prev+1)%m]
    have hv0_from_vp : v0 = vp + dir 5 := by
      rw [hvp_eq]; have : dir (2 : ZMod 6) + dir (5 : ZMod 6) = (0, 0) := by decide
      have h1 := congrArg Prod.fst this; have h2 := congrArg Prod.snd this
      ext <;> simp at h1 h2 ⊢ <;> omega
    have hu2_out : vp + dir (5 - 1) ∉ I := by
      have heq : vp + dir (5 - 1) = v0 + dir 3 := by
        rw [hvp_eq]; have : dir (2 : ZMod 6) + dir ((5 : ZMod 6) - 1) = dir (3 : ZMod 6) := by decide
        have h1 := congrArg Prod.fst this; have h2 := congrArg Prod.snd this
        ext <;> simp at h1 h2 ⊢ <;> omega
      rw [heq]; exact h3_out
    rcases universal_rhombus_bridge h hvpI hv0I hv0_from_vp hu2_out with ⟨u, huB, huvp, hphiv0⟩
    rcases List.mem_iff_getElem.mp ((hCout.mem_iff u).mpr huB) with ⟨idx, hidx, huidx⟩
    have hnext : Cout[(idx + 1) % Cout.length]'(Nat.mod_lt _ (by omega)) = phi S u := by
      rw [hCout_phi idx hidx, huidx]
    rcases hamCycle_to_path_bwd hCin hj_prev with ⟨P, hPlen, hPnd, hPmem, hPadj, hP0, hPlast⟩
    refine hamCycle_splice_path hCout hdisj hPlen hPnd hPmem hPadj hidx ?_ ?_
    · rw [huidx, hP0 (by omega)]; exact huvp
    · rw [hPlast (by omega), hnext]; simp only [hj_prev_succ, hv0_eq]; exact unitStep_symm hphiv0

/- Section 9 & 10: Half-Integer Polynomial Bounds & Backward Onion Induction -/

private lemma core_clique {k : ℕ} {o : Center} {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ (k : ℝ) + 1 / 2) :
    (layerFinset k o r).card ≤ 1 ∨
    (∃ v0 v1 : Site, layerFinset k o r = {v0, v1} ∧ unitStep v0 v1) ∨
    (∃ C : List Site, HamCycle (layerFinset k o r) C) := by
  classical
  have hQ_small : ∀ p ∈ layerFinset k o r, 3 * Qp (subR p o) < 1 := by
    intro p hp
    rw [mem_layerFinset hr0] at hp
    rcases exists_d6_sector (subR p o) with ⟨b, m, h2, hle⟩
    set v := if b then refR (rotPowR m (subR p o)) else rotPowR m (subR p o)
    have hv_in : inK0 k r v := by
      cases b
      · exact inK0_rotPowR m hp
      · exact inK0_refR (inK0_rotPowR m hp)
    have hQv : Qp v = Qp (subR p o) := by
      cases b <;> simp [v, Qp_refR, Qp_rotPowR]
    rw [← hQv]
    by_contra hge
    push Not at hge
    have h3 : (2 * v.1 + v.2) ^ 2 ≥ 3 * Qp v := by
      unfold Qp Q; nlinarith
    have h2v : 1 ≤ 2 * v.1 + v.2 := by nlinarith
    have h0 := hv_in 0
    have hd0 : dir (0 : ZMod 6) = (1, 0) := by decide
    rw [hd0] at h0
    simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero] at h0
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    unfold Qp Q at hge
    unfold Q at h0
    nlinarith
  have hpair : ∀ p1 ∈ layerFinset k o r, ∀ p2 ∈ layerFinset k o r, p1 ≠ p2 → unitStep p1 p2 := by
    intro p1 h1 p2 h2 hne
    have hq1 := hQ_small p1 h1
    have hq2 := hQ_small p2 h2
    have hdiff_r : Q ((p1.1 - p2.1 : ℤ) : ℝ) ((p1.2 - p2.2 : ℤ) : ℝ) < 2 := by
      unfold Qp Q subR at hq1 hq2
      unfold Q
      push_cast
      have hpar : ((p1.1 : ℝ) - p2.1) ^ 2 + ((p1.1 : ℝ) - p2.1) * ((p1.2 : ℝ) - p2.2) +
          ((p1.2 : ℝ) - p2.2) ^ 2 +
          (((p1.1 : ℝ) - o.1 + ((p2.1 : ℝ) - o.1)) ^ 2 +
           ((p1.1 : ℝ) - o.1 + ((p2.1 : ℝ) - o.1)) * ((p1.2 : ℝ) - o.2 + ((p2.2 : ℝ) - o.2)) +
           ((p1.2 : ℝ) - o.2 + ((p2.2 : ℝ) - o.2)) ^ 2) =
          2 * (((p1.1 : ℝ) - o.1) ^ 2 + ((p1.1 : ℝ) - o.1) * ((p1.2 : ℝ) - o.2) + ((p1.2 : ℝ) - o.2) ^ 2) +
          2 * (((p2.1 : ℝ) - o.1) ^ 2 + ((p2.1 : ℝ) - o.1) * ((p2.2 : ℝ) - o.2) + ((p2.2 : ℝ) - o.2) ^ 2) := by
        ring
      have hnn := Q_nonneg ((p1.1 : ℝ) - o.1 + ((p2.1 : ℝ) - o.1)) ((p1.2 : ℝ) - o.2 + ((p2.2 : ℝ) - o.2))
      unfold Q at hnn
      linarith
    have hdiff_z : (p1.1 - p2.1) ^ 2 + (p1.1 - p2.1) * (p1.2 - p2.2) + (p1.2 - p2.2) ^ 2 < 2 := by
      have : (((p1.1 - p2.1) ^ 2 + (p1.1 - p2.1) * (p1.2 - p2.2) + (p1.2 - p2.2) ^ 2 : ℤ) : ℝ) < (2 : ℤ) := by
        unfold Q at hdiff_r; push_cast at hdiff_r ⊢; exact hdiff_r
      exact_mod_cast this
    have hpos_z : 1 ≤ (p1.1 - p2.1) ^ 2 + (p1.1 - p2.1) * (p1.2 - p2.2) + (p1.2 - p2.2) ^ 2 := by
      by_contra hle0
      push Not at hle0
      have h4 : (2 * (p1.1 - p2.1) + (p1.2 - p2.2)) ^ 2 + 3 * (p1.2 - p2.2) ^ 2 ≤ 0 := by nlinarith
      have h1' : p1.2 = p2.2 := by nlinarith
      have h2' : p1.1 = p2.1 := by nlinarith
      exact hne (Prod.ext h2' h1')
    unfold unitStep OMA.S_oeis_a122226.unitStep
    dsimp only
    omega
  set S := layerFinset k o r
  have hcard_le3 : S.card ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have h4 : 4 ≤ S.toList.length := by rw [Finset.length_toList]; omega
    set p0 := S.toList[0]'(by omega)
    set p1 := S.toList[1]'(by omega)
    set p2 := S.toList[2]'(by omega)
    set p3 := S.toList[3]'(by omega)
    have hnd := S.nodup_toList
    have hmem : ∀ i (hi : i < S.toList.length), S.toList[i]'hi ∈ S := fun i hi =>
      Finset.mem_toList.mp (List.getElem_mem hi)
    have hne : ∀ i j (hi : i < S.toList.length) (hj : j < S.toList.length), i ≠ j →
        S.toList[i]'hi ≠ S.toList[j]'hj := by
      intro i j hi hj hij heq
      exact hij ((hnd.getElem_inj_iff).mp heq)
    rcases (unitStep_iff_exists_dir p0 p1).mp (hpair _ (hmem 0 _) _ (hmem 1 _) (hne 0 1 _ _ (by omega))) with ⟨d1, hd1⟩
    rcases (unitStep_iff_exists_dir p0 p2).mp (hpair _ (hmem 0 _) _ (hmem 2 _) (hne 0 2 _ _ (by omega))) with ⟨d2, hd2⟩
    rcases (unitStep_iff_exists_dir p0 p3).mp (hpair _ (hmem 0 _) _ (hmem 3 _) (hne 0 3 _ _ (by omega))) with ⟨d3, hd3⟩
    have hstep_sub : ∀ a b : ZMod 6, unitStep (p0 + dir a) (p0 + dir b) → unitStep (dir a) (dir b) := by
      intro a b hab
      unfold unitStep OMA.S_oeis_a122226.unitStep at hab ⊢
      dsimp only [Prod.fst_add, Prod.snd_add] at hab ⊢
      have h1 : p0.1 + (dir a).1 - (p0.1 + (dir b).1) = (dir a).1 - (dir b).1 := by ring
      have h2 : p0.2 + (dir a).2 - (p0.2 + (dir b).2) = (dir a).2 - (dir b).2 := by ring
      rw [h1, h2] at hab; exact hab
    have h12 := hstep_sub d1 d2 (hd1 ▸ hd2 ▸ hpair _ (hmem 1 _) _ (hmem 2 _) (hne 1 2 _ _ (by omega)))
    have h23 := hstep_sub d2 d3 (hd2 ▸ hd3 ▸ hpair _ (hmem 2 _) _ (hmem 3 _) (hne 2 3 _ _ (by omega)))
    have h31 := hstep_sub d3 d1 (hd3 ▸ hd1 ▸ hpair _ (hmem 3 _) _ (hmem 1 _) (hne 3 1 _ _ (by omega)))
    exact not_unitStep_triangle_dir d1 d2 d3 ⟨h12, h23, h31⟩
  by_cases h1 : S.card ≤ 1
  · exact Or.inl h1
  · by_cases h2 : S.card = 2
    · right; left
      rcases Finset.card_eq_two.mp h2 with ⟨v0, v1, hne, heq⟩
      refine ⟨v0, v1, heq, hpair v0 (heq ▸ by simp) v1 (heq ▸ by simp) hne⟩
    · right; right
      have h3 : S.card = 3 := by omega
      refine ⟨S.toList, ⟨?_, S.nodup_toList, fun p => Finset.mem_toList, ?_⟩⟩
      · rw [Finset.length_toList]; omega
      · intro i hi
        have hlen : S.toList.length = 3 := by rw [Finset.length_toList]; omega
        have hne_idx : i ≠ (i + 1) % S.toList.length := by rw [hlen]; omega
        have hne_val : S.toList[i]'hi ≠ S.toList[(i + 1) % S.toList.length]'(Nat.mod_lt _ (by omega)) := by
          intro heq
          exact hne_idx ((S.nodup_toList.getElem_inj_iff).mp heq)
        exact hpair _ (Finset.mem_toList.mp (List.getElem_mem hi))
          _ (Finset.mem_toList.mp (List.getElem_mem (Nat.mod_lt _ (by omega)))) hne_val

private lemma no_star13_of_le_three_halves {k : ℕ} {o : Center} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (k : ℝ) + 3 / 2) (v : Site) :
    layerFinset k o r ≠ star13 v := by
  intro heq
  have h1 : v + dir 0 + dir 1 ∈ layerFinset k o r := by
    rw [heq]; simp only [star13, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨0, rfl⟩
  have h2 : v + dir 3 + dir 4 ∈ layerFinset k o r := by
    rw [heq]; simp only [star13, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨3, rfl⟩
  have h1k := (mem_layerFinset hr0 _).mp h1 0
  have h2k := (mem_layerFinset hr0 _).mp h2 3
  have hd0 : dir (0 : ZMod 6) = (1, 0) := by decide
  have hd1 : dir (1 : ZMod 6) = (0, 1) := by decide
  have hd3 : dir (3 : ZMod 6) = (-1, 0) := by decide
  have hd4 : dir (4 : ZMod 6) = (0, -1) := by decide
  rw [hd0, hd1] at h1k
  rw [hd3, hd4] at h2k
  simp only [subR, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_neg, Int.cast_one,
    Int.cast_zero, add_zero, mul_one, mul_neg, mul_zero] at h1k h2k
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hq_nn := Q_nonneg ((v.1 : ℝ) - o.1) ((v.2 : ℝ) - o.2)
  unfold Q at h1k h2k hq_nn
  nlinarith

private lemma no_star13_int_diam {n k : ℕ} {o : Center} {v : Site}
    (hcard : (layerFinset (k + 1) o ((n : ℝ) / 2)).card = 1) :
    layerFinset k o ((n : ℝ) / 2) ≠ star13 v := by
  have hr0 : 0 ≤ (n : ℝ) / 2 := by positivity
  have hn_le : n ≤ 2 * k + 3 := by
    by_contra hgt
    push Not at hgt
    have hr : ((k + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) / 2 := by
      have : (2 * k + 4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 * k + 4 ≤ n)
      push_cast; linarith
    rcases D1_exists_three o with ⟨T, hT3, hT⟩
    have hsub : T ⊆ layerFinset (k + 1) o ((n : ℝ) / 2) := by
      intro p hp
      rw [mem_layerFinset hr0]
      exact inK0_of_Q_le (ρ := 1) (by norm_num) hr (by simpa using hT p hp)
    have := Finset.card_le_card hsub
    omega
  have hr_le : (n : ℝ) / 2 ≤ (k : ℝ) + 3 / 2 := by
    have : (n : ℝ) ≤ (2 * k + 3 : ℝ) := by exact_mod_cast hn_le
    linarith
  exact no_star13_of_le_three_halves hr0 hr_le v

private lemma disk_has_hamCycle {n : ℕ} (hn : 1 < n) (o : Center) :
    ∃ C : List Site, HamCycle (layerFinset 0 o ((n : ℝ) / 2)) C := by
  classical
  set r : ℝ := (n : ℝ) / 2
  have hr0 : 0 ≤ r := by positivity
  set q : ℕ := n / 2
  have hq_le : r ≤ (q : ℝ) + 1 / 2 := by
    have : n ≤ 2 * q + 1 := by omega
    have : (n : ℝ) ≤ 2 * (q : ℝ) + 1 := by exact_mod_cast this
    dsimp only [r]; linarith
  let Inv : ℕ → Prop := fun k =>
    (layerFinset k o r).card ≤ 1 ∨
    (∃ v0 v1 : Site, layerFinset k o r = {v0, v1} ∧ unitStep v0 v1) ∨
    (∃ C : List Site, HamCycle (layerFinset k o r) C)
  have hind : ∀ d : ℕ, d ≤ q → Inv (q - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa [Inv] using core_clique (o := o) hr0 hq_le
    | succ d ih =>
      intro hd_le
      set k := q - (d + 1)
      have hk_succ : k + 1 = q - d := by omega
      have hprev : Inv (k + 1) := hk_succ ▸ ih (by omega)
      have hrk : (k : ℝ) + 1 ≤ r := by
        have : 2 * k + 2 ≤ n := by omega
        have : 2 * (k : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast this
        dsimp only [r]; linarith
      have hgood : GoodRegion (layerFinset k o r) := layer_goodRegion k o hrk
      have hint : combInt (layerFinset k o r) = layerFinset (k + 1) o r := layer_combInt k o hr0
      right; right
      rcases hprev with hcard1 | ⟨v0, v1, hpair, hstep⟩ | ⟨Cin, hCin⟩
      · by_cases h0 : (layerFinset (k + 1) o r).card = 0
        · have hempty : combInt (layerFinset k o r) = ∅ := by
            rw [hint]; exact Finset.card_eq_zero.mp h0
          rcases goodRegion_bdry_cycle hgood with ⟨Cout, hCout, _⟩
          have hbdry_eq : combBdry (layerFinset k o r) = layerFinset k o r := by
            unfold combBdry; rw [hempty, Finset.sdiff_empty]
          exact ⟨Cout, hbdry_eq ▸ hCout⟩
        · have h1 : (layerFinset (k + 1) o r).card = 1 := by omega
          rcases Finset.card_eq_one.mp h1 with ⟨v, hv⟩
          have hne_star : layerFinset k o r ≠ star13 v := no_star13_int_diam h1
          exact goodRegion_merge_singleton hgood (hint.trans hv) hne_star
      · exact goodRegion_merge_pair hgood (hint.trans hpair) hstep
      · exact goodRegion_merge_cycle hgood (hint ▸ hCin)
  have h0 : Inv 0 := by simpa using hind q le_rfl
  have hcard0 : 3 ≤ (layerFinset 0 o r).card := by
    rcases D1_exists_three o with ⟨T, hT3, hT⟩
    have hr1 : ((0 : ℕ) : ℝ) + 1 ≤ r := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      dsimp only [r]; push_cast; linarith
    have hsub : T ⊆ layerFinset 0 o r := by
      intro p hp
      rw [mem_layerFinset hr0]
      exact inK0_of_Q_le (ρ := 1) (by norm_num) hr1 (by simpa using hT p hp)
    exact le_trans hT3 (Finset.card_le_card hsub)
  rcases h0 with hle1 | ⟨v0, v1, hpair, _⟩ | ⟨C, hC⟩
  · omega
  · have : (layerFinset 0 o r).card ≤ 2 := by rw [hpair]; exact Finset.card_le_two
    omega
  · exact ⟨C, hC⟩

/- Section 11: Main Theorem OMA.S_oeis_a122226.main -/

private lemma inDisk_iff_mem_layer0 (n : ℕ) (o : Center) (p : Site) :
    OMA.S_oeis_a122226.inDisk n o p ↔ p ∈ layerFinset 0 o ((n : ℝ) / 2) := by
  have hr0 : 0 ≤ (n : ℝ) / 2 := by positivity
  rw [mem_layerFinset hr0, inK0_zero_iff]
  unfold OMA.S_oeis_a122226.inDisk Qp Q subR
  dsimp only
  constructor <;> intro h <;> nlinarith

private lemma siteCounts_bdd (n : ℕ) :
    ∀ m ∈ OMA.S_oeis_a122226.siteCounts n, m ≤ (4 * n + 1) ^ 2 := by
  classical
  rintro m ⟨s, o, rfl, hs⟩
  by_cases hne : s.Nonempty
  · rcases hne with ⟨p0, hp0⟩
    let box := Finset.Icc (-2 * (n : ℤ)) (2 * (n : ℤ)) ×ˢ Finset.Icc (-2 * (n : ℤ)) (2 * (n : ℤ))
    have hcard_box : box.card = (4 * n + 1) ^ 2 := by
      simp only [box, Finset.card_product, Int.card_Icc]
      have : Int.toNat (2 * (n : ℤ) + 1 - -2 * (n : ℤ)) = 4 * n + 1 := by omega
      rw [this]; ring
    let f : Site → Site := fun p => (p.1 - p0.1, p.2 - p0.2)
    have hinj : Set.InjOn f (s : Set Site) := by
      intro a _ b _ hab
      have h1 := congrArg Prod.fst hab; have h2 := congrArg Prod.snd hab
      dsimp [f] at h1 h2
      exact Prod.ext (by omega) (by omega)
    have hsub : s.image f ⊆ box := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have h1 := hs p hp
      have h2 := hs p0 hp0
      unfold OMA.S_oeis_a122226.inDisk at h1 h2
      dsimp only at h1 h2
      have hpar : 4 * (((p.1 : ℝ) - p0.1) ^ 2 + ((p.1 : ℝ) - p0.1) * ((p.2 : ℝ) - p0.2) +
          ((p.2 : ℝ) - p0.2) ^ 2) +
          4 * (((p.1 : ℝ) - o.1 + ((p0.1 : ℝ) - o.1)) ^ 2 +
               ((p.1 : ℝ) - o.1 + ((p0.1 : ℝ) - o.1)) * ((p.2 : ℝ) - o.2 + ((p0.2 : ℝ) - o.2)) +
               ((p.2 : ℝ) - o.2 + ((p0.2 : ℝ) - o.2)) ^ 2) =
          8 * (((p.1 : ℝ) - o.1) ^ 2 + ((p.1 : ℝ) - o.1) * ((p.2 : ℝ) - o.2) + ((p.2 : ℝ) - o.2) ^ 2) +
          8 * (((p0.1 : ℝ) - o.1) ^ 2 + ((p0.1 : ℝ) - o.1) * ((p0.2 : ℝ) - o.2) + ((p0.2 : ℝ) - o.2) ^ 2) := by
        ring
      have hnn := Q_nonneg ((p.1 : ℝ) - o.1 + ((p0.1 : ℝ) - o.1)) ((p.2 : ℝ) - o.2 + ((p0.2 : ℝ) - o.2))
      unfold Q at hnn
      have hq : ((p.1 : ℝ) - p0.1) ^ 2 + ((p.1 : ℝ) - p0.1) * ((p.2 : ℝ) - p0.2) +
          ((p.2 : ℝ) - p0.2) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      have hx2 : 3 * ((p.1 : ℝ) - p0.1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((p.1 : ℝ) - p0.1) + 2 * ((p.2 : ℝ) - p0.2))]
      have hy2 : 3 * ((p.2 : ℝ) - p0.2) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (2 * ((p.1 : ℝ) - p0.1) + ((p.2 : ℝ) - p0.2))]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxb1 : -(2 * (n : ℝ)) ≤ (p.1 : ℝ) - p0.1 := by nlinarith
      have hxb2 : (p.1 : ℝ) - p0.1 ≤ 2 * (n : ℝ) := by nlinarith
      have hyb1 : -(2 * (n : ℝ)) ≤ (p.2 : ℝ) - p0.2 := by nlinarith
      have hyb2 : (p.2 : ℝ) - p0.2 ≤ 2 * (n : ℝ) := by nlinarith
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp [f]
      · have hle : ((-2 * (n : ℤ) : ℤ) : ℝ) ≤ ((p.1 - p0.1 : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast hle
      · have hle : ((p.1 - p0.1 : ℤ) : ℝ) ≤ ((2 * (n : ℤ) : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast hle
      · have hle : ((-2 * (n : ℤ) : ℤ) : ℝ) ≤ ((p.2 - p0.2 : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast hle
      · have hle : ((p.2 - p0.2 : ℤ) : ℝ) ≤ ((2 * (n : ℤ) : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast hle
    calc s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ box.card := Finset.card_le_card hsub
      _ = (4 * n + 1) ^ 2 := hcard_box
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne; simp

private lemma main_proof : ∀ n : ℕ, 1 < n →
    ∃ m : ℕ, IsGreatest (OMA.S_oeis_a122226.walkLengths n) m ∧
             IsGreatest (OMA.S_oeis_a122226.siteCounts n) m := by
  classical
  intro n hn
  set B := (4 * n + 1) ^ 2
  set M := Nat.findGreatest (fun m => m ∈ OMA.S_oeis_a122226.siteCounts n) B
  have h0_mem : 0 ∈ OMA.S_oeis_a122226.siteCounts n := ⟨∅, (0, 0), rfl, fun _ h => by simp at h⟩
  have hM_mem : M ∈ OMA.S_oeis_a122226.siteCounts n :=
    Nat.findGreatest_spec (m := 0) (Nat.zero_le B) h0_mem
  have hM_ub : ∀ m ∈ OMA.S_oeis_a122226.siteCounts n, m ≤ M := fun m hm =>
    Nat.le_findGreatest (siteCounts_bdd n m hm) hm
  have hM_great_site : IsGreatest (OMA.S_oeis_a122226.siteCounts n) M := ⟨hM_mem, hM_ub⟩
  rcases hM_mem with ⟨s0, o0, hs0_card, hs0_in⟩
  set S0 := layerFinset 0 o0 ((n : ℝ) / 2)
  have hS0_mem : S0.card ∈ OMA.S_oeis_a122226.siteCounts n :=
    ⟨S0, o0, rfl, fun p hp => (inDisk_iff_mem_layer0 n o0 p).mpr hp⟩
  have hs0_sub : s0 ⊆ S0 := fun p hp => (inDisk_iff_mem_layer0 n o0 p).mp (hs0_in p hp)
  have hS0_card : S0.card = M :=
    le_antisymm (hM_ub S0.card hS0_mem) (hs0_card ▸ Finset.card_le_card hs0_sub)
  rcases disk_has_hamCycle hn o0 with ⟨C, hC⟩
  have hClen : C.length = M := by
    have h1 : C.toFinset = S0 := by
      ext p; rw [List.mem_toFinset]; exact hC.mem_iff p
    have h2 : C.toFinset.card = C.length := List.toFinset_card_of_nodup hC.nodup
    rw [← h2, h1, hS0_card]
  have hM3 : 3 ≤ M := hClen ▸ hC.len_ge3
  have hM_walk : M ∈ OMA.S_oeis_a122226.walkLengths n := by
    let p : ℕ → Site := fun i => C[i % C.length]'(Nat.mod_lt _ (by omega))
    refine ⟨p, o0, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      have hiC : i < C.length := hClen.symm ▸ hi
      dsimp only [p]
      have h1 : i % C.length = i := Nat.mod_eq_of_lt hiC
      simp only [h1]
      exact hC.adj i hiC
    · intro i j hij hjM heq
      have hjC : j ≤ C.length := hClen.symm ▸ hjM
      dsimp only [p] at heq
      have hmod : i % C.length = j % C.length := (hC.nodup.getElem_inj_iff).mp heq
      have hiC : i < C.length := by omega
      rw [Nat.mod_eq_of_lt hiC] at hmod
      by_cases hlt : j < C.length
      · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
      · have hjeq : j = C.length := by omega
        rw [hjeq, Nat.mod_self] at hmod
        exact ⟨hmod, hjeq.trans hClen⟩
    · intro _; exact hM3
    · intro i _
      exact (inDisk_iff_mem_layer0 n o0 _).mpr ((hC.mem_iff _).mp (List.getElem_mem _))
  have hwalk_ub : ∀ m ∈ OMA.S_oeis_a122226.walkLengths n, m ≤ M := by
    rintro m ⟨p, o, ⟨_, hinj_p, _⟩, hin_p⟩
    have hinj : Set.InjOn p (Finset.range m : Set ℕ) := by
      intro i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := (hinj_p i j hlt (by omega) heq).2; omega
      · have := (hinj_p j i hgt (by omega) heq.symm).2; omega
    have hm_site : m ∈ OMA.S_oeis_a122226.siteCounts n := by
      refine ⟨(Finset.range m).image p, o, ?_, ?_⟩
      · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      · intro q hq
        rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
        exact hin_p i (by simp at hi; omega)
    exact hM_ub m hm_site
  exact ⟨M, ⟨hM_walk, hwalk_ub⟩, hM_great_site⟩

end OeisA122226

theorem OMA.solution : type_of% @OMA.S_oeis_a122226.main :=
  OeisA122226.main_proof
