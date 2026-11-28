import OMAStatements.S_oeis_a346126

namespace OeisA346126

open OMA.S_oeis_a346126

/-! ### Section 1: Axial norm, unit steps, D_6 symmetries, and convexity -/

private def Q (u : ℝ × ℝ) : ℝ :=
  u.1 ^ 2 + u.1 * u.2 + u.2 ^ 2

private def QZ (u : Site) : ℤ :=
  u.1 ^ 2 + u.1 * u.2 + u.2 ^ 2

private def toR (p : Site) : ℝ × ℝ :=
  ((p.1 : ℝ), (p.2 : ℝ))

private def addS (p q : Site) : Site :=
  (p.1 + q.1, p.2 + q.2)

private def subS (p q : Site) : Site :=
  (p.1 - q.1, p.2 - q.2)

private def smulS (k : ℤ) (p : Site) : Site :=
  (k * p.1, k * p.2)

private def addR (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 + v.1, u.2 + v.2)

private def subR (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 - v.1, u.2 - v.2)

private def smulR (c : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (c * u.1, c * u.2)

private lemma Q_nonneg (u : ℝ × ℝ) : 0 ≤ Q u := by
  unfold Q
  nlinarith [sq_nonneg (2 * u.1 + u.2), sq_nonneg u.2]

private lemma Q_eq_zero_iff (u : ℝ × ℝ) : Q u = 0 ↔ u.1 = 0 ∧ u.2 = 0 := by
  unfold Q
  constructor
  · intro h
    have h1 : (2 * u.1 + u.2) ^ 2 + 3 * u.2 ^ 2 = 0 := by linarith
    have h2 : u.2 = 0 := by nlinarith [sq_nonneg (2 * u.1 + u.2)]
    have h3 : u.1 = 0 := by nlinarith [sq_nonneg u.2]
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    ring

private lemma Q_neg (u : ℝ × ℝ) : Q (-u.1, -u.2) = Q u := by
  unfold Q; ring

private lemma Q_toR (p : Site) : Q (toR p) = (QZ p : ℝ) := by
  unfold Q QZ toR
  push_cast
  ring

private lemma Q_convex {u v : ℝ × ℝ} {t R : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : Q u ≤ R) (hv : Q v ≤ R) :
    Q (addR (smulR (1 - t) u) (smulR t v)) ≤ R := by
  have hid :
      Q (addR (smulR (1 - t) u) (smulR t v)) =
        (1 - t) * Q u + t * Q v - t * (1 - t) * Q (subR u v) := by
    unfold Q addR smulR subR; ring
  have hq : 0 ≤ Q (subR u v) := Q_nonneg _
  have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  nlinarith

private lemma Q_parallelogram (u v : ℝ × ℝ) :
    Q (addR u v) + Q (subR u v) = 2 * Q u + 2 * Q v := by
  unfold Q addR subR; ring

private lemma Q_sub_le (u v : ℝ × ℝ) :
    Q (subR u v) ≤ 2 * Q u + 2 * Q v := by
  have h := Q_parallelogram u v
  have h0 := Q_nonneg (addR u v)
  linarith

private lemma Q_cauchy (u v : ℝ × ℝ) :
    (2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2) ^ 2 ≤ 4 * Q u * Q v := by
  unfold Q
  nlinarith [sq_nonneg (u.1 * v.2 - u.2 * v.1)]

/-- Six cyclic unit directions on the triangular lattice. -/
private def e : ZMod 6 → Site
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (-1, 1)
  | ⟨3, _⟩ => (-1, 0)
  | ⟨4, _⟩ => (0, -1)
  | ⟨5, _⟩ => (1, -1)

private lemma QZ_e (d : ZMod 6) : QZ (e d) = 1 := by
  fin_cases d <;> rfl

private lemma Q_e (d : ZMod 6) : Q (toR (e d)) = 1 := by
  rw [Q_toR, QZ_e]
  norm_num

private lemma e_add_three (d : ZMod 6) : e (d + 3) = (-(e d).1, -(e d).2) := by
  fin_cases d <;> rfl

private lemma e_add_two_eq (d : ZMod 6) : addS (e d) (e (d + 2)) = e (d + 1) := by
  fin_cases d <;> rfl

private lemma e_sub_next (d : ZMod 6) : subS (e (d - 1)) (e d) = e (d + 4) := by
  fin_cases d <;> rfl

private lemma e_add_three_five (d : ZMod 6) : addS (e (d + 3)) (e (d + 5)) = e (d + 4) := by
  fin_cases d <;> rfl

private lemma e_injective : Function.Injective e := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [e] <;> rfl

private lemma QZ_eq_one_iff (v : Site) : QZ v = 1 ↔ ∃ d : ZMod 6, v = e d := by
  constructor
  · intro h
    have h4 : (2 * v.1 + v.2) ^ 2 + 3 * v.2 ^ 2 = 4 := by
      unfold QZ at h; linarith
    have hy1 : -1 ≤ v.2 := by nlinarith [sq_nonneg (2 * v.1 + v.2)]
    have hy2 : v.2 ≤ 1 := by nlinarith [sq_nonneg (2 * v.1 + v.2)]
    have h4' : (v.1 + 2 * v.2) ^ 2 + 3 * v.1 ^ 2 = 4 := by
      unfold QZ at h; linarith
    have hx1 : -1 ≤ v.1 := by nlinarith [sq_nonneg (v.1 + 2 * v.2)]
    have hx2 : v.1 ≤ 1 := by nlinarith [sq_nonneg (v.1 + 2 * v.2)]
    rcases v with ⟨x, y⟩
    dsimp only at h hx1 hx2 hy1 hy2
    have hcases : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = -1 ∧ y = 1) ∨
        (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = -1) := by
      unfold QZ at h
      interval_cases y <;> interval_cases x <;> norm_num at h <;> norm_num
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  · rintro ⟨d, rfl⟩
    exact QZ_e d

private lemma unitStep_symm {p q : Site} (h : unitStep p q) : unitStep q p := by
  unfold unitStep at h ⊢
  linarith

private lemma unitStep_iff_exists_dir (p q : Site) :
    unitStep p q ↔ ∃ d : ZMod 6, q = addS p (e d) := by
  constructor
  · intro h
    have hq : QZ (subS q p) = 1 := by
      unfold QZ subS; unfold unitStep at h; linarith
    obtain ⟨d, hd⟩ := (QZ_eq_one_iff _).mp hq
    refine ⟨d, ?_⟩
    rcases p with ⟨px, py⟩
    rcases q with ⟨qx, qy⟩
    unfold subS at hd
    unfold addS
    have h1 := congrArg Prod.fst hd
    have h2 := congrArg Prod.snd hd
    dsimp only at h1 h2
    ext <;> dsimp only <;> linarith
  · rintro ⟨d, rfl⟩
    unfold unitStep addS
    have h := QZ_e d
    unfold QZ at h
    linarith

private lemma unitStep_addS_e (p : Site) (d : ZMod 6) : unitStep p (addS p (e d)) :=
  (unitStep_iff_exists_dir p _).mpr ⟨d, rfl⟩

private lemma unitStep_e_iff (a b : ZMod 6) :
    unitStep (e a) (e b) ↔ b = a + 1 ∨ b = a - 1 := by
  fin_cases a <;> fin_cases b <;> unfold unitStep e <;>
    first
    | exact iff_of_true (by norm_num) (by first | exact Or.inl rfl | exact Or.inr rfl)
    | exact iff_of_false (by norm_num) (by rintro (h | h) <;> exact absurd (congrArg (@ZMod.val 6) h) (by decide))

private lemma not_unitStep_self (p : Site) : ¬ unitStep p p := by
  unfold unitStep; norm_num

/-- D_6 linear isometries on ℝ × ℝ and Site. -/
private def rotR (u : ℝ × ℝ) : ℝ × ℝ := (-u.2, u.1 + u.2)
private def tauR (u : ℝ × ℝ) : ℝ × ℝ := (u.2, u.1)
private def rotS (p : Site) : Site := (-p.2, p.1 + p.2)
private def tauS (p : Site) : Site := (p.2, p.1)

private lemma Q_rotR (u : ℝ × ℝ) : Q (rotR u) = Q u := by
  unfold Q rotR; ring

private lemma Q_tauR (u : ℝ × ℝ) : Q (tauR u) = Q u := by
  unfold Q tauR; ring

private lemma rotR_add (u v : ℝ × ℝ) : rotR (addR u v) = addR (rotR u) (rotR v) := by
  unfold rotR addR; ext <;> dsimp only <;> ring

private lemma rotR_sub (u v : ℝ × ℝ) : rotR (subR u v) = subR (rotR u) (rotR v) := by
  unfold rotR subR; ext <;> dsimp only <;> ring

private lemma rotR_smul (c : ℝ) (u : ℝ × ℝ) : rotR (smulR c u) = smulR c (rotR u) := by
  unfold rotR smulR; ext <;> dsimp only <;> ring

private lemma tauR_add (u v : ℝ × ℝ) : tauR (addR u v) = addR (tauR u) (tauR v) := by
  unfold tauR addR; rfl

private lemma tauR_sub (u v : ℝ × ℝ) : tauR (subR u v) = subR (tauR u) (tauR v) := by
  unfold tauR subR; rfl

private lemma tauR_smul (c : ℝ) (u : ℝ × ℝ) : tauR (smulR c u) = smulR c (tauR u) := by
  unfold tauR smulR; rfl

private lemma rotS_e (d : ZMod 6) : rotS (e d) = e (d + 1) := by
  fin_cases d <;> rfl

private def tauDir : ZMod 6 → ZMod 6
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 2

private lemma tauS_e (d : ZMod 6) : tauS (e d) = e (tauDir d) := by
  fin_cases d <;> rfl

private lemma tauDir_invol (d : ZMod 6) : tauDir (tauDir d) = d := by
  fin_cases d <;> rfl

private lemma rotR_toR (p : Site) : rotR (toR p) = toR (rotS p) := by
  unfold rotR rotS toR; ext <;> dsimp only <;> push_cast <;> ring

private lemma tauR_toR (p : Site) : tauR (toR p) = toR (tauS p) := by
  unfold tauR tauS toR; rfl

private lemma rotR_pow6 (u : ℝ × ℝ) : rotR^[6] u = u := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  unfold rotR; ext <;> dsimp only <;> ring

private lemma rotS_pow6 (p : Site) : rotS^[6] p = p := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  unfold rotS; ext <;> dsimp only <;> ring

private lemma rotR_iter_Q (n : ℕ) (u : ℝ × ℝ) : Q (rotR^[n] u) = Q u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Q_rotR, ih]

private lemma rotR_iter_add (n : ℕ) (u v : ℝ × ℝ) :
    rotR^[n] (addR u v) = addR (rotR^[n] u) (rotR^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, rotR_add]

private lemma rotR_iter_sub (n : ℕ) (u v : ℝ × ℝ) :
    rotR^[n] (subR u v) = subR (rotR^[n] u) (rotR^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, rotR_sub]

private lemma rotR_iter_smul (n : ℕ) (c : ℝ) (u : ℝ × ℝ) :
    rotR^[n] (smulR c u) = smulR c (rotR^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, rotR_smul]

private lemma rotR_iter_toR (n : ℕ) (p : Site) :
    rotR^[n] (toR p) = toR (rotS^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, rotR_toR]

private lemma rotS_iter_e (n : ℕ) (d : ZMod 6) :
    rotS^[n] (e d) = e (d + (n : ZMod 6)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, rotS_e]
    push_cast
    ring_nf

/-! ### Section 2: Fundamental sector and unit-disk triangle coverage -/

private lemma exists_rot_first_quadrant (u : ℝ × ℝ) :
    ∃ n : Fin 6, 0 ≤ (rotR^[n.val] u).1 ∧ 0 ≤ (rotR^[n.val] u).2 := by
  rcases u with ⟨a, b⟩
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · exact ⟨⟨0, by omega⟩, ha, hb⟩
    · by_cases hab : 0 ≤ a + b
      · refine ⟨⟨1, by omega⟩, ?_⟩
        simp only [Function.iterate_one, rotR]
        exact ⟨by linarith, hab⟩
      · refine ⟨⟨2, by omega⟩, ?_⟩
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, rotR]
        exact ⟨by linarith, by linarith⟩
  · by_cases hb : b ≤ 0
    · refine ⟨⟨3, by omega⟩, ?_⟩
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, rotR]
      exact ⟨by linarith, by linarith⟩
    · by_cases hab : 0 ≤ a + b
      · refine ⟨⟨5, by omega⟩, ?_⟩
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, rotR]
        exact ⟨by linarith, by linarith⟩
      · refine ⟨⟨4, by omega⟩, ?_⟩
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, rotR]
        exact ⟨by linarith, by linarith⟩

private lemma exists_d6_fundamental (u : ℝ × ℝ) :
    ∃ (n : Fin 6) (flip : Bool),
      let v := if flip then tauR (rotR^[n.val] u) else rotR^[n.val] u
      0 ≤ v.2 ∧ v.2 ≤ v.1 := by
  obtain ⟨n, h1, h2⟩ := exists_rot_first_quadrant u
  by_cases h : (rotR^[n.val] u).2 ≤ (rotR^[n.val] u).1
  · exact ⟨n, false, h2, h⟩
  · refine ⟨n, true, ?_⟩
    simp only [ite_true, tauR]
    exact ⟨h1, by linarith⟩

private lemma unitDisk_three_sites (o : Center) :
    ∃ p₁ p₂ p₃ : Site, p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      Q (subR (toR p₁) o) ≤ 1 ∧ Q (subR (toR p₂) o) ≤ 1 ∧ Q (subR (toR p₃) o) ≤ 1 := by
  let a : ℤ := ⌊o.1⌋
  let b : ℤ := ⌊o.2⌋
  have ha1 : (a : ℝ) ≤ o.1 := Int.floor_le o.1
  have ha2 : o.1 < (a : ℝ) + 1 := Int.lt_floor_add_one o.1
  have hb1 : (b : ℝ) ≤ o.2 := Int.floor_le o.2
  have hb2 : o.2 < (b : ℝ) + 1 := Int.lt_floor_add_one o.2
  set s : ℝ := o.1 - a
  set t : ℝ := o.2 - b
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s < 1 := by linarith
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  by_cases hst : s + t ≤ 1
  · refine ⟨(a, b), (a + 1, b), (a, b + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; omega
    · intro h; have := congrArg Prod.snd h; omega
    · intro h; have := congrArg Prod.fst h; omega
    · unfold Q subR toR; push_cast; nlinarith
    · unfold Q subR toR; push_cast; nlinarith
    · unfold Q subR toR; push_cast; nlinarith
  · refine ⟨(a + 1, b + 1), (a + 1, b), (a, b + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; have := congrArg Prod.snd h; omega
    · intro h; have := congrArg Prod.fst h; omega
    · intro h; have := congrArg Prod.fst h; omega
    · unfold Q subR toR; push_cast; nlinarith
    · unfold Q subR toR; push_cast; nlinarith
    · unfold Q subR toR; push_cast; nlinarith

/-! ### Section 3: Onion layers S_k = K_k(o, r) ∩ ℤ² and iterated interior identity -/

private def inKR (o : Center) (r : ℝ) (k : ℕ) (x : ℝ × ℝ) : Prop :=
  ∀ d : ZMod 6, Q (addR (subR x o) (smulR (k : ℝ) (toR (e d)))) ≤ r ^ 2

private def inKS (o : Center) (r : ℝ) (k : ℕ) (p : Site) : Prop :=
  inKR o r k (toR p)

private lemma inKR_convex {o : Center} {r : ℝ} {k : ℕ} {x y : ℝ × ℝ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : inKR o r k x) (hy : inKR o r k y) :
    inKR o r k (addR (smulR (1 - t) x) (smulR t y)) := by
  intro d
  have hrew :
      addR (subR (addR (smulR (1 - t) x) (smulR t y)) o) (smulR (k : ℝ) (toR (e d))) =
        addR (smulR (1 - t) (addR (subR x o) (smulR (k : ℝ) (toR (e d)))))
             (smulR t (addR (subR y o) (smulR (k : ℝ) (toR (e d))))) := by
    unfold addR subR smulR; ext <;> dsimp only <;> ring
  rw [hrew]
  exact Q_convex ht0 ht1 (hx d) (hy d)

private lemma inKR_Q_le {o : Center} {r : ℝ} {k : ℕ} {x : ℝ × ℝ} (hx : inKR o r k x) :
    Q (subR x o) ≤ r ^ 2 := by
  have h0 := hx 0
  have h3 := hx 3
  have hsum :
      Q (addR (subR x o) (smulR (k : ℝ) (toR (e 0)))) +
        Q (addR (subR x o) (smulR (k : ℝ) (toR (e 3)))) =
      2 * Q (subR x o) + 2 * (k : ℝ) ^ 2 := by
    unfold Q addR subR smulR toR e; norm_num; ring
  nlinarith [sq_nonneg (k : ℝ)]

private lemma inKR_rot_iff (r : ℝ) (k : ℕ) (u : ℝ × ℝ) :
    inKR (0, 0) r k (rotR u) ↔ inKR (0, 0) r k u := by
  constructor
  · intro h d
    have hd := h (d + 1)
    have he : toR (e (d + 1)) = rotR (toR (e d)) := by
      rw [← rotS_e, rotR_toR]
    have hsub : ∀ z : ℝ × ℝ, subR z (0, 0) = z := fun z => by unfold subR; ext <;> simp
    rw [hsub] at hd ⊢
    rw [he, ← rotR_smul, ← rotR_add, Q_rotR] at hd
    exact hd
  · intro h d
    have hd := h (d - 1)
    have he : toR (e d) = rotR (toR (e (d - 1))) := by
      rw [rotR_toR, rotS_e, sub_add_cancel]
    have hsub : ∀ z : ℝ × ℝ, subR z (0, 0) = z := fun z => by unfold subR; ext <;> simp
    rw [hsub] at hd ⊢
    rw [he, ← rotR_smul, ← rotR_add, Q_rotR]
    exact hd

private lemma inKR_rot_iter_iff (r : ℝ) (k n : ℕ) (u : ℝ × ℝ) :
    inKR (0, 0) r k (rotR^[n] u) ↔ inKR (0, 0) r k u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', inKR_rot_iff, ih]

private lemma inKR_tau_iff (r : ℝ) (k : ℕ) (u : ℝ × ℝ) :
    inKR (0, 0) r k (tauR u) ↔ inKR (0, 0) r k u := by
  have hsub : ∀ z : ℝ × ℝ, subR z (0, 0) = z := fun z => by unfold subR; ext <;> simp
  constructor
  · intro h d
    have hd := h (tauDir d)
    rw [hsub] at hd ⊢
    have he : toR (e (tauDir d)) = tauR (toR (e d)) := by
      rw [← tauS_e, tauR_toR]
    rw [he, ← tauR_smul, ← tauR_add, Q_tauR] at hd
    exact hd
  · intro h d
    have hd := h (tauDir d)
    rw [hsub] at hd ⊢
    have he : toR (e d) = tauR (toR (e (tauDir d))) := by
      rw [tauR_toR, tauS_e, tauDir_invol]
    rw [he, ← tauR_smul, ← tauR_add, Q_tauR]
    exact hd

private lemma inKR_shift_zero (o : Center) (r : ℝ) (k : ℕ) (x : ℝ × ℝ) :
    inKR o r k x ↔ inKR (0, 0) r k (subR x o) := by
  unfold inKR subR addR; simp

private lemma inKS_zero_iff (o : Center) (r : ℝ) (p : Site) :
    inKS o r 0 p ↔ Q (subR (toR p) o) ≤ r ^ 2 := by
  unfold inKS inKR smulR addR
  simp

private lemma inKS_of_Q_le_one {o : Center} {r : ℝ} {k : ℕ} {p : Site}
    (hr : (k : ℝ) + 1 ≤ r) (hp : Q (subR (toR p) o) ≤ 1) : inKS o r k p := by
  intro d
  set u := subR (toR p) o
  set v := toR (e d)
  have hv : Q v = 1 := Q_e d
  have hcs := Q_cauchy u v
  have hB : 2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2 ≤ 2 := by
    have : (2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2) ^ 2 ≤ 4 := by
      nlinarith [Q_nonneg u]
    nlinarith
  have hexp :
      Q (addR u (smulR (k : ℝ) v)) =
        Q u + (k : ℝ) * (2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2) +
          (k : ℝ) ^ 2 * Q v := by
    unfold Q addR smulR; ring
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Finiteness of S_k via an explicit bounding box around o. -/
private noncomputable def layerFinset (o : Center) (r : ℝ) (k : ℕ) : Finset Site := by
  classical
  let M : ℤ := ⌈2 * |r| + |o.1| + |o.2| + 2⌉
  exact (Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M).filter (fun p => inKS o r k p)

private lemma mem_layerFinset (o : Center) (r : ℝ) (k : ℕ) (p : Site) :
    p ∈ layerFinset o r k ↔ inKS o r k p := by
  classical
  unfold layerFinset
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hp
  have hq : Q (subR (toR p) o) ≤ r ^ 2 := inKR_Q_le hp
  have hq' : (2 * ((p.1 : ℝ) - o.1) + ((p.2 : ℝ) - o.2)) ^ 2 + 3 * ((p.2 : ℝ) - o.2) ^ 2 ≤ 4 * r ^ 2 := by
    unfold Q subR toR at hq; linarith
  have hq'' : (((p.1 : ℝ) - o.1) + 2 * ((p.2 : ℝ) - o.2)) ^ 2 + 3 * ((p.1 : ℝ) - o.1) ^ 2 ≤ 4 * r ^ 2 := by
    unfold Q subR toR at hq; linarith
  have h1 : |((p.1 : ℝ) - o.1)| ≤ 2 * |r| := by
    rw [abs_le]
    have hr : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    constructor <;> nlinarith [sq_nonneg (((p.1 : ℝ) - o.1) + 2 * ((p.2 : ℝ) - o.2)), abs_nonneg r]
  have h2 : |((p.2 : ℝ) - o.2)| ≤ 2 * |r| := by
    rw [abs_le]
    have hr : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    constructor <;> nlinarith [sq_nonneg (2 * ((p.1 : ℝ) - o.1) + ((p.2 : ℝ) - o.2)), abs_nonneg r]
  set M : ℤ := ⌈2 * |r| + |o.1| + |o.2| + 2⌉
  have hM : 2 * |r| + |o.1| + |o.2| + 2 ≤ (M : ℝ) := Int.le_ceil _
  have h1' : -(M : ℝ) ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ (M : ℝ) := by
    rw [abs_le] at h1
    have ho1 := neg_abs_le o.1
    have ho1' := le_abs_self o.1
    have ho2 := abs_nonneg o.2
    constructor <;> linarith
  have h2' : -(M : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ (M : ℝ) := by
    rw [abs_le] at h2
    have ho2 := neg_abs_le o.2
    have ho2' := le_abs_self o.2
    have ho1 := abs_nonneg o.1
    constructor <;> linarith
  exact ⟨⟨by exact_mod_cast h1'.1, by exact_mod_cast h1'.2⟩,
         ⟨by exact_mod_cast h2'.1, by exact_mod_cast h2'.2⟩⟩

/-- Combinatorial interior and boundary of any finite set of lattice sites. -/
private def intS (S : Finset Site) : Finset Site :=
  S.filter (fun p => ∀ d : ZMod 6, addS p (e d) ∈ S)

private def bdyS (S : Finset Site) : Finset Site :=
  S \ intS S

private lemma mem_intS {S : Finset Site} {p : Site} :
    p ∈ intS S ↔ p ∈ S ∧ ∀ d : ZMod 6, addS p (e d) ∈ S := by
  simp [intS]

private lemma mem_bdyS {S : Finset Site} {p : Site} :
    p ∈ bdyS S ↔ p ∈ S ∧ ∃ d : ZMod 6, addS p (e d) ∉ S := by
  simp only [bdyS, Finset.mem_sdiff, mem_intS, not_and, not_forall]
  tauto

/-- Step 3.2: Iterated interior identity S_{k+1} = Int(S_k). -/
private lemma layer_succ_eq_int (o : Center) (r : ℝ) (k : ℕ) :
    layerFinset o r (k + 1) = intS (layerFinset o r k) := by
  ext p
  rw [mem_layerFinset, mem_intS, mem_layerFinset]
  constructor
  · intro hp
    have hp_k : inKS o r k p := by
      intro d
      have h1 := hp d
      have h2 := hp (d + 3)
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have ht0 : (0 : ℝ) ≤ 1 / (2 * ((k : ℝ) + 1)) := by positivity
      have ht1 : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have he3 : toR (e (d + 3)) = (- (toR (e d)).1, -(toR (e d)).2) := by
        rw [e_add_three]; unfold toR; ext <;> simp
      have hcomb :
          addR (subR (toR p) o) (smulR (k : ℝ) (toR (e d))) =
            addR (smulR (1 - 1 / (2 * ((k : ℝ) + 1)))
                    (addR (subR (toR p) o) (smulR ((k + 1 : ℕ) : ℝ) (toR (e d)))))
                 (smulR (1 / (2 * ((k : ℝ) + 1)))
                    (addR (subR (toR p) o) (smulR ((k + 1 : ℕ) : ℝ) (toR (e (d + 3)))))) := by
        rw [he3]
        unfold addR subR smulR
        push_cast
        ext <;> dsimp only <;> field_simp <;> ring
      rw [hcomb]
      exact Q_convex ht0 ht1 h1 h2
    refine ⟨hp_k, ?_⟩
    intro j
    rw [mem_layerFinset]
    intro d
    -- Universal 1-line convex combination: e_j + k * e_d = (1/(k+1))((k+1)*e_j) + (k/(k+1))((k+1)*e_d)!
    have h1 := hp j
    have h2 := hp d
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have ht0 : (0 : ℝ) ≤ (k : ℝ) / ((k : ℝ) + 1) := by positivity
    have ht1 : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hk1]; linarith
    have hcomb :
        addR (subR (toR (addS p (e j))) o) (smulR (k : ℝ) (toR (e d))) =
          addR (smulR (1 - (k : ℝ) / ((k : ℝ) + 1))
                  (addR (subR (toR p) o) (smulR ((k + 1 : ℕ) : ℝ) (toR (e j)))))
               (smulR ((k : ℝ) / ((k : ℝ) + 1))
                  (addR (subR (toR p) o) (smulR ((k + 1 : ℕ) : ℝ) (toR (e d))))) := by
      unfold addR subR smulR toR addS
      push_cast
      ext <;> dsimp only <;> field_simp <;> ring
    rw [hcomb]
    exact Q_convex ht0 ht1 h1 h2
  · rintro ⟨_, hnb⟩ d
    have hd := (mem_layerFinset o r k (addS p (e d))).mp (hnb d) d
    have hcomb :
        addR (subR (toR p) o) (smulR ((k + 1 : ℕ) : ℝ) (toR (e d))) =
          addR (subR (toR (addS p (e d))) o) (smulR (k : ℝ) (toR (e d))) := by
      unfold addR subR smulR toR addS
      push_cast
      ext <;> dsimp only <;> ring
    rw [hcomb]
    exact hd

/-! ### Section 4: Horizontal convexity of S_k -/

private def HorizConvex (S : Finset Site) : Prop :=
  ∀ x₁ x₂ x y : ℤ, (x₁, y) ∈ S → (x₂, y) ∈ S → x₁ ≤ x → x ≤ x₂ → (x, y) ∈ S

private lemma layer_horizConvex (o : Center) (r : ℝ) (k : ℕ) :
    HorizConvex (layerFinset o r k) := by
  intro x₁ x₂ x y h₁ h₂ hx₁ hx₂
  rw [mem_layerFinset] at h₁ h₂ ⊢
  by_cases heq : x₁ = x₂
  · have : x = x₁ := by omega
    subst this; exact h₁
  · have hlt : (x₁ : ℝ) < (x₂ : ℝ) := by exact_mod_cast (show x₁ < x₂ by omega)
    have hne : (x₂ : ℝ) - (x₁ : ℝ) ≠ 0 := by linarith
    have hx1R : (x₁ : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx₁
    have hx2R : (x : ℝ) ≤ (x₂ : ℝ) := by exact_mod_cast hx₂
    set t : ℝ := ((x : ℝ) - (x₁ : ℝ)) / ((x₂ : ℝ) - (x₁ : ℝ))
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hcomb : toR (x, y) = addR (smulR (1 - t) (toR (x₁, y))) (smulR t (toR (x₂, y))) := by
      unfold toR addR smulR
      ext <;> dsimp only
      · simp only [t]; field_simp [hne]; ring
      · simp only [t]; field_simp [hne]; ring
    unfold inKS
    rw [hcomb]
    exact inKR_convex ht0 ht1 h₁ h₂

/-! ### Section 5: Sector Inward-Triangle & Local Connectivity of S_k (r ≥ k + 1) -/

private lemma sector_inward_e3 {r : ℝ} {k : ℕ} {q : ℝ × ℝ}
    (hr : (k : ℝ) + 1 ≤ r) (h1 : 0 ≤ q.1) (h2 : 0 ≤ q.2)
    (hq : inKR (0, 0) r k q) :
    inKR (0, 0) r k (addR q (toR (e 3))) := by
  have hsub : ∀ z : ℝ × ℝ, subR z (0, 0) = z := fun z => by unfold subR; ext <;> simp
  have hE : 2 * q.1 + q.2 ≤ 1 → q.1 ^ 2 + q.1 * q.2 + q.2 ^ 2 - 2 * q.1 - q.2 ≤ 0 := by
    intro hle
    nlinarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hr2 : ((k : ℝ) + 1) ^ 2 ≤ r ^ 2 := by nlinarith
  intro d
  rw [hsub]
  fin_cases d
  · -- d = 0
    by_cases hk : k = 0
    · subst hk
      have hq0 := hq 0; rw [hsub] at hq0
      unfold Q addR smulR toR e at hq0 ⊢; norm_num at hq0 ⊢
      by_cases hle : 2 * q.1 + q.2 ≤ 1
      · have := hE hle; nlinarith
      · nlinarith
    · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      have h0 := hq 0; have h3 := hq 3
      rw [hsub] at h0 h3
      have ht0 : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
      have ht1 : 1 / (2 * (k : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk
        linarith
      have hcomb :
          addR (addR q (toR (e 3))) (smulR (k : ℝ) (toR (e 0))) =
            addR (smulR (1 - 1 / (2 * (k : ℝ))) (addR q (smulR (k : ℝ) (toR (e 0)))))
                 (smulR (1 / (2 * (k : ℝ))) (addR q (smulR (k : ℝ) (toR (e 3))))) := by
        unfold addR smulR toR e; ext <;> dsimp only <;> norm_num <;> field_simp <;> ring
      change Q (addR (addR q (toR (e 3))) (smulR (k : ℝ) (toR (e 0)))) ≤ r ^ 2
      rw [hcomb]
      exact Q_convex ht0 ht1 h0 h3
  · -- d = 1
    by_cases hk : k = 0
    · subst hk
      have hq0 := hq 0; rw [hsub] at hq0
      unfold Q addR smulR toR e at hq0 ⊢; norm_num at hq0 ⊢
      by_cases hle : 2 * q.1 + q.2 ≤ 1
      · have := hE hle; nlinarith
      · nlinarith
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hq1 := hq 1; rw [hsub] at hq1
      unfold Q addR smulR toR e at hq1 ⊢; norm_num at hq1 ⊢
      nlinarith
  · -- d = 2
    have hq1 := hq 1; rw [hsub] at hq1
    unfold Q addR smulR toR e at hq1 ⊢; norm_num at hq1 ⊢
    by_cases hle : 2 * q.1 + q.2 ≤ 1
    · have := hE hle; nlinarith
    · nlinarith
  · -- d = 3
    have hq0 := hq 0; rw [hsub] at hq0
    unfold Q addR smulR toR e at hq0 ⊢; norm_num at hq0 ⊢
    by_cases hle : 2 * q.1 + q.2 ≤ 1
    · have := hE hle; nlinarith
    · nlinarith
  · -- d = 4
    have hq1 := hq 1; rw [hsub] at hq1
    unfold Q addR smulR toR e at hq1 ⊢; norm_num at hq1 ⊢
    by_cases hle : 2 * q.1 + q.2 ≤ 1
    · have := hE hle; nlinarith
    · nlinarith
  · -- d = 5
    by_cases hk : k = 0
    · subst hk
      have hq0 := hq 0; rw [hsub] at hq0
      unfold Q addR smulR toR e at hq0 ⊢; norm_num at hq0 ⊢
      by_cases hle : 2 * q.1 + q.2 ≤ 1
      · have := hE hle; nlinarith
      · nlinarith
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hq5 := hq 5; rw [hsub] at hq5
      unfold Q addR smulR toR e at hq5 ⊢; norm_num at hq5 ⊢
      nlinarith

private lemma sector_lateral_e0_to_e5 {r : ℝ} {k : ℕ} {q : ℝ × ℝ}
    (h1 : 0 ≤ q.1) (h2 : 0 ≤ q.2)
    (hq : inKR (0, 0) r k q) (hq0 : inKR (0, 0) r k (addR q (toR (e 0)))) :
    inKR (0, 0) r k (addR q (toR (e 5))) := by
  have hsub : ∀ z : ℝ × ℝ, subR z (0, 0) = z := fun z => by unfold subR; ext <;> simp
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  intro d
  rw [hsub]
  by_cases hk : k = 0
  · subst hk
    have ha := hq0 0; rw [hsub] at ha
    unfold Q addR smulR toR e at ha ⊢; norm_num at ha ⊢
    fin_cases d <;> nlinarith
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk
    fin_cases d
    · -- d = 0
      have ha := hq0 0; rw [hsub] at ha
      unfold Q addR smulR toR e at ha ⊢; norm_num at ha ⊢; nlinarith
    · -- d = 1
      have ha := hq0 1; have hb := hq0 4; rw [hsub] at ha hb
      have ht0 : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
      have ht1 : 1 / (2 * (k : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hcomb :
          addR (addR q (toR (e 5))) (smulR (k : ℝ) (toR (e 1))) =
            addR (smulR (1 - 1 / (2 * (k : ℝ))) (addR (addR q (toR (e 0))) (smulR (k : ℝ) (toR (e 1)))))
                 (smulR (1 / (2 * (k : ℝ))) (addR (addR q (toR (e 0))) (smulR (k : ℝ) (toR (e 4))))) := by
        unfold addR smulR toR e; ext <;> dsimp only <;> norm_num <;> field_simp <;> ring
      change Q (addR (addR q (toR (e 5))) (smulR (k : ℝ) (toR (e 1)))) ≤ r ^ 2
      rw [hcomb]; exact Q_convex ht0 ht1 ha hb
    · -- d = 2
      have ha := hq 2; have hb := hq 5; rw [hsub] at ha hb
      have ht0 : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
      have ht1 : 1 / (2 * (k : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hcomb :
          addR (addR q (toR (e 5))) (smulR (k : ℝ) (toR (e 2))) =
            addR (smulR (1 - 1 / (2 * (k : ℝ))) (addR q (smulR (k : ℝ) (toR (e 2)))))
                 (smulR (1 / (2 * (k : ℝ))) (addR q (smulR (k : ℝ) (toR (e 5))))) := by
        unfold addR smulR toR e; ext <;> dsimp only <;> norm_num <;> field_simp <;> ring
      change Q (addR (addR q (toR (e 5))) (smulR (k : ℝ) (toR (e 2)))) ≤ r ^ 2
      rw [hcomb]; exact Q_convex ht0 ht1 ha hb
    · -- d = 3
      have ha := hq 3; have hb := hq 4; rw [hsub] at ha hb
      have ht0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      have ht1 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; linarith
      have hcomb :
          addR (addR q (toR (e 5))) (smulR (k : ℝ) (toR (e 3))) =
            addR (smulR (1 - 1 / (k : ℝ)) (addR q (smulR (k : ℝ) (toR (e 3)))))
                 (smulR (1 / (k : ℝ)) (addR q (smulR (k : ℝ) (toR (e 4))))) := by
        unfold addR smulR toR e; ext <;> dsimp only <;> norm_num <;> field_simp <;> ring
      change Q (addR (addR q (toR (e 5))) (smulR (k : ℝ) (toR (e 3)))) ≤ r ^ 2
      rw [hcomb]; exact Q_convex ht0 ht1 ha hb
    · -- d = 4
      have ha := hq0 1; rw [hsub] at ha
      unfold Q addR smulR toR e at ha ⊢; norm_num at ha ⊢; nlinarith
    · -- d = 5
      have ha := hq0 0; rw [hsub] at ha
      unfold Q addR smulR toR e at ha ⊢; norm_num at ha ⊢; nlinarith

/-- Contiguous arc on ZMod 6 of size ≥ 2: at most one entry transition (d ∈ A ∧ d-1 ∉ A),
    and at least two elements. -/
private def IsArcGeTwo (A : ZMod 6 → Prop) : Prop :=
  (∃ d₁ d₂ : ZMod 6, d₁ ≠ d₂ ∧ A d₁ ∧ A d₂) ∧
  (∀ d₁ d₂ : ZMod 6, A d₁ → ¬ A (d₁ - 1) → A d₂ → ¬ A (d₂ - 1) → d₁ = d₂)

private lemma isArcGeTwo_of_sector (A : ZMod 6 → Prop)
    (h3 : A 3) (h4 : A 4) (h05 : A 0 → A 5) (h12 : A 1 → A 2) :
    IsArcGeTwo A := by
  refine ⟨⟨3, 4, by decide, h3, h4⟩, ?_⟩
  have hstep : ∀ d : ZMod 6, A d → ¬ A (d - 1) →
      (d = 0 ∧ A 0 ∧ ¬ A 5) ∨ (d = 1 ∧ A 1 ∧ ¬ A 0) ∨ (d = 2 ∧ A 2 ∧ ¬ A 1) ∨
      (d = 3 ∧ A 3 ∧ ¬ A 2) ∨ (d = 5 ∧ A 5 ∧ ¬ A 4) := by
    intro d ha hb
    fin_cases d
    · exact Or.inl ⟨rfl, ha, hb⟩
    · exact Or.inr (Or.inl ⟨rfl, ha, hb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, ha, hb⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ha, hb⟩)))
    · exact absurd h3 hb
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ha, hb⟩)))
  intro d₁ d₂ ha₁ hb₁ ha₂ hb₂
  rcases hstep d₁ ha₁ hb₁ with ⟨rfl, a0, n5⟩ | ⟨rfl, a1, n0⟩ | ⟨rfl, a2, n1⟩ | ⟨rfl, _, n2⟩ | ⟨rfl, _, n4⟩
  · exact absurd (h05 a0) n5
  · rcases hstep d₂ ha₂ hb₂ with ⟨rfl, a0', _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, n1'⟩ | ⟨rfl, _, n2'⟩ | ⟨rfl, _, n4'⟩
    · exact absurd a0' n0
    · rfl
    · exact absurd a1 n1'
    · exact absurd (h12 a1) n2'
    · exact absurd h4 n4'
  · rcases hstep d₂ ha₂ hb₂ with ⟨rfl, a0', n5'⟩ | ⟨rfl, a1', _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, n2'⟩ | ⟨rfl, _, n4'⟩
    · exact absurd (h05 a0') n5'
    · exact absurd a1' n1
    · rfl
    · exact absurd a2 n2'
    · exact absurd h4 n4'
  · rcases hstep d₂ ha₂ hb₂ with ⟨rfl, a0', n5'⟩ | ⟨rfl, a1', _⟩ | ⟨rfl, a2', _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, n4'⟩
    · exact absurd (h05 a0') n5'
    · exact absurd (h12 a1') n2
    · exact absurd a2' n2
    · rfl
    · exact absurd h4 n4'
  · exact absurd h4 n4

private def LocallyConn (S : Finset Site) : Prop :=
  ∀ p ∈ S, IsArcGeTwo (fun d => addS p (e d) ∈ S)

private lemma layer_locallyConn {o : Center} {r : ℝ} {k : ℕ} (hr : (k : ℝ) + 1 ≤ r) :
    LocallyConn (layerFinset o r k) := by
  intro p hp
  rw [mem_layerFinset] at hp
  set u := subR (toR p) o
  have hu : inKR (0, 0) r k u := (inKR_shift_zero o r k (toR p)).mp hp
  obtain ⟨n, h1, h2⟩ := exists_rot_first_quadrant u
  set q := rotR^[n.val] u
  have hq : inKR (0, 0) r k q := (inKR_rot_iter_iff r k n.val u).mpr hu
  have hq3 : inKR (0, 0) r k (addR q (toR (e 3))) := sector_inward_e3 hr h1 h2 hq
  have hq4 : inKR (0, 0) r k (addR q (toR (e 4))) := by
    have hqt : inKR (0, 0) r k (tauR q) := (inKR_tau_iff r k q).mpr hq
    have hqt3 := sector_inward_e3 hr h2 h1 hqt
    rw [← inKR_tau_iff r k]
    have hrew : tauR (addR q (toR (e 4))) = addR (tauR q) (toR (e 3)) := by
      rw [tauR_add, tauR_toR, tauS_e]; rfl
    rw [hrew]; exact hqt3
  have h05 : inKR (0, 0) r k (addR q (toR (e 0))) → inKR (0, 0) r k (addR q (toR (e 5))) :=
    sector_lateral_e0_to_e5 h1 h2 hq
  have h12 : inKR (0, 0) r k (addR q (toR (e 1))) → inKR (0, 0) r k (addR q (toR (e 2))) := by
    intro hq1
    have hqt : inKR (0, 0) r k (tauR q) := (inKR_tau_iff r k q).mpr hq
    have hqt0 : inKR (0, 0) r k (addR (tauR q) (toR (e 0))) := by
      have hrew : addR (tauR q) (toR (e 0)) = tauR (addR q (toR (e 1))) := by
        rw [tauR_add, tauR_toR, tauS_e]; rfl
      rw [hrew]; exact (inKR_tau_iff r k _).mpr hq1
    have hqt5 := sector_lateral_e0_to_e5 h2 h1 hqt hqt0
    rw [← inKR_tau_iff r k]
    have hrew : tauR (addR q (toR (e 2))) = addR (tauR q) (toR (e 5)) := by
      rw [tauR_add, tauR_toR, tauS_e]; rfl
    rw [hrew]; exact hqt5
  -- Transfer IsArcGeTwo back from q = rotR^[n] u to u by rotating directions by -(n : ZMod 6)!
  have harc_q := isArcGeTwo_of_sector (fun d => inKR (0, 0) r k (addR q (toR (e d)))) hq3 hq4 h05 h12
  have hiff : ∀ d : ZMod 6, addS p (e d) ∈ layerFinset o r k ↔
      inKR (0, 0) r k (addR q (toR (e (d + (n.val : ZMod 6))))) := by
    intro d
    rw [mem_layerFinset]
    unfold inKS
    rw [inKR_shift_zero, ← inKR_rot_iter_iff r k n.val]
    have hrew : rotR^[n.val] (subR (toR (addS p (e d))) o) =
        addR q (toR (e (d + (n.val : ZMod 6)))) := by
      have hsub_add : subR (toR (addS p (e d))) o = addR u (toR (e d)) := by
        dsimp only [u]; unfold subR toR addS addR; push_cast; ext <;> dsimp only <;> ring
      rw [hsub_add, rotR_iter_add, rotR_iter_toR, rotS_iter_e]
    rw [hrew]
  refine ⟨?_, ?_⟩
  · obtain ⟨d₁, d₂, hne, ha, hb⟩ := harc_q.1
    refine ⟨d₁ - (n.val : ZMod 6), d₂ - (n.val : ZMod 6), ?_, ?_, ?_⟩
    · intro h; apply hne; exact sub_left_inj.mp h
    · dsimp only; rw [hiff, sub_add_cancel]; exact ha
    · dsimp only; rw [hiff, sub_add_cancel]; exact hb
  · intro d₁ d₂ ha₁ hb₁ ha₂ hb₂
    dsimp only at ha₁ hb₁ ha₂ hb₂
    rw [hiff] at ha₁ hb₁ ha₂ hb₂
    have heq := harc_q.2 (d₁ + (n.val : ZMod 6)) (d₂ + (n.val : ZMod 6))
      ha₁ (by rwa [add_sub_right_comm]) ha₂ (by rwa [add_sub_right_comm])
    exact add_right_cancel heq

/-! ### Section 6: Connectedness of S_k (r ≥ k + 1) -/

private def ReachIn (S : Finset Site) : Site → Site → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ unitStep a b)

private def ConnS (S : Finset Site) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ReachIn S a b

private lemma reachIn_symm {S : Finset Site} {a b : Site} (h : ReachIn S a b) :
    ReachIn S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.head ⟨hab.2.1, hab.1, unitStep_symm hab.2.2⟩ ih

private lemma reachIn_unitDisk {o : Center} {r : ℝ} {k : ℕ} (hr : (k : ℝ) + 1 ≤ r)
    {p₁ p₂ : Site} (h₁ : Q (subR (toR p₁) o) ≤ 1) (h₂ : Q (subR (toR p₂) o) ≤ 1) :
    ReachIn (layerFinset o r k) p₁ p₂ := by
  have hp₁ : p₁ ∈ layerFinset o r k := (mem_layerFinset _ _ _ _).mpr (inKS_of_Q_le_one hr h₁)
  have hp₂ : p₂ ∈ layerFinset o r k := (mem_layerFinset _ _ _ _).mpr (inKS_of_Q_le_one hr h₂)
  set v := subS p₂ p₁
  have hv_le : QZ v ≤ 4 := by
    have hR : (QZ v : ℝ) ≤ 4 := by
      rw [← Q_toR]
      have hsub : toR v = subR (subR (toR p₂) o) (subR (toR p₁) o) := by
        unfold toR v subS subR; push_cast; ext <;> dsimp only <;> ring
      rw [hsub]
      linarith [Q_sub_le (subR (toR p₂) o) (subR (toR p₁) o)]
    exact_mod_cast hR
  have h4 : (2 * v.1 + v.2) ^ 2 + 3 * v.2 ^ 2 ≤ 16 := by
    unfold QZ at hv_le; linarith
  have h4' : (v.1 + 2 * v.2) ^ 2 + 3 * v.1 ^ 2 ≤ 16 := by
    unfold QZ at hv_le; linarith
  have hy1 : -2 ≤ v.2 := by nlinarith [sq_nonneg (2 * v.1 + v.2)]
  have hy2 : v.2 ≤ 2 := by nlinarith [sq_nonneg (2 * v.1 + v.2)]
  have hx1 : -2 ≤ v.1 := by nlinarith [sq_nonneg (v.1 + 2 * v.2)]
  have hx2 : v.1 ≤ 2 := by nlinarith [sq_nonneg (v.1 + 2 * v.2)]
  have hv0 : 0 ≤ QZ v := by
    unfold QZ; nlinarith [sq_nonneg (2 * v.1 + v.2), sq_nonneg v.2]
  have hv_cases : QZ v = 0 ∨ QZ v = 1 ∨ QZ v = 3 ∨ QZ v = 4 := by
    rcases hv_eq : v with ⟨vx, vy⟩
    rw [hv_eq] at hx1 hx2 hy1 hy2 hv_le hv0
    dsimp only [QZ] at hx1 hx2 hy1 hy2 hv_le hv0 ⊢
    interval_cases vy <;> interval_cases vx <;> omega
  rcases hv_cases with h0 | h1 | h3 | h4eq
  · have : p₁ = p₂ := by
      have h0R : Q (toR v) = 0 := by rw [Q_toR, h0]; norm_num
      obtain ⟨hx0, hy0⟩ := (Q_eq_zero_iff _).mp h0R
      dsimp only [v] at hx0 hy0
      unfold toR subS at hx0 hy0
      rcases p₁ with ⟨a, b⟩; rcases p₂ with ⟨c, d⟩
      dsimp only at hx0 hy0
      have hc : (c : ℝ) - a = 0 := by exact_mod_cast hx0
      have hd : (d : ℝ) - b = 0 := by exact_mod_cast hy0
      ext <;> dsimp only <;> [exact_mod_cast (show (a : ℝ) = c by linarith); exact_mod_cast (show (b : ℝ) = d by linarith)]
    subst this; exact Relation.ReflTransGen.refl
  · obtain ⟨d, hd⟩ := (QZ_eq_one_iff v).mp h1
    have hstep : unitStep p₁ p₂ := by
      unfold unitStep; dsimp only [v] at h1; unfold QZ subS at h1; linarith
    exact Relation.ReflTransGen.single ⟨hp₁, hp₂, hstep⟩
  · -- QZ v = 3: v = e d + e (d+1) for one of 6 diagonals; one of p₁ + e d, p₁ + e (d+1) is in D_1(o)!
    have hdiag : ∃ d : ZMod 6, v = addS (e d) (e (d + 1)) := by
      rcases hv_eq : v with ⟨vx, vy⟩
      rw [hv_eq] at hx1 hx2 hy1 hy2 h3
      dsimp only at hx1 hx2 hy1 hy2 h3
      unfold QZ at h3
      have hlist : (vx = 1 ∧ vy = 1) ∨ (vx = -1 ∧ vy = 2) ∨ (vx = -2 ∧ vy = 1) ∨
          (vx = -1 ∧ vy = -1) ∨ (vx = 1 ∧ vy = -2) ∨ (vx = 2 ∧ vy = -1) := by
        interval_cases vy <;> interval_cases vx <;> norm_num at h3 <;> norm_num
      rcases hlist with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    obtain ⟨d, hd⟩ := hdiag
    have hp2 : p₂ = addS p₁ (addS (e d) (e (d + 1))) := by
      dsimp only [v] at hd
      rcases p₁ with ⟨a, b⟩; rcases p₂ with ⟨c, f⟩
      unfold subS addS at hd; unfold addS
      have hf1 := congrArg Prod.fst hd; have hf2 := congrArg Prod.snd hd
      dsimp only at hf1 hf2
      ext <;> dsimp only <;> linarith
    let w₁ := addS p₁ (e d)
    let w₂ := addS p₁ (e (d + 1))
    have hsum : 2 * Q (subR (toR w₁) o) + 2 * Q (subR (toR w₂) o) =
        2 * Q (subR (toR p₁) o) + 2 * Q (subR (toR p₂) o) - 2 := by
      rw [hp2]
      dsimp only [w₁, w₂]
      rw [← rotS_e]
      unfold Q subR toR addS rotS
      fin_cases d <;> unfold e <;> push_cast <;> ring
    have hw1_step1 : unitStep p₁ w₁ := unitStep_addS_e p₁ d
    have hw1_step2 : unitStep w₁ p₂ := by
      rw [unitStep_iff_exists_dir]
      refine ⟨d + 1, ?_⟩
      rw [hp2]; unfold w₁ addS; ext <;> dsimp only <;> ring
    have hw2_step1 : unitStep p₁ w₂ := unitStep_addS_e p₁ (d + 1)
    have hw2_step2 : unitStep w₂ p₂ := by
      rw [unitStep_iff_exists_dir]
      refine ⟨d, ?_⟩
      rw [hp2]; unfold w₂ addS; ext <;> dsimp only <;> ring
    by_cases hqw : Q (subR (toR w₁) o) ≤ 1
    · have hw1_mem : w₁ ∈ layerFinset o r k := (mem_layerFinset _ _ _ _).mpr (inKS_of_Q_le_one hr hqw)
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨hp₁, hw1_mem, hw1_step1⟩)
        (Relation.ReflTransGen.single ⟨hw1_mem, hp₂, hw1_step2⟩)
    · have hqw2 : Q (subR (toR w₂) o) ≤ 1 := by linarith
      have hw2_mem : w₂ ∈ layerFinset o r k := (mem_layerFinset _ _ _ _).mpr (inKS_of_Q_le_one hr hqw2)
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨hp₁, hw2_mem, hw2_step1⟩)
        (Relation.ReflTransGen.single ⟨hw2_mem, hp₂, hw2_step2⟩)
  · -- QZ v = 4: v = 2 * e d, midpoint p₁ + e d is in D_1(o) by convexity!
    have hdbl : ∃ d : ZMod 6, v = smulS 2 (e d) := by
      rcases hv_eq : v with ⟨vx, vy⟩
      rw [hv_eq] at hx1 hx2 hy1 hy2 h4eq
      dsimp only at hx1 hx2 hy1 hy2 h4eq
      unfold QZ at h4eq
      have hlist : (vx = 2 ∧ vy = 0) ∨ (vx = 0 ∧ vy = 2) ∨ (vx = -2 ∧ vy = 2) ∨
          (vx = -2 ∧ vy = 0) ∨ (vx = 0 ∧ vy = -2) ∨ (vx = 2 ∧ vy = -2) := by
        interval_cases vy <;> interval_cases vx <;> norm_num at h4eq <;> norm_num
      rcases hlist with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    obtain ⟨d, hd⟩ := hdbl
    have hp2 : p₂ = addS p₁ (smulS 2 (e d)) := by
      dsimp only [v] at hd
      rcases p₁ with ⟨a, b⟩; rcases p₂ with ⟨c, f⟩
      unfold subS smulS at hd
      have hf1 := congrArg Prod.fst hd; have hf2 := congrArg Prod.snd hd
      dsimp only at hf1 hf2
      unfold addS smulS; ext <;> dsimp only <;> linarith
    let w := addS p₁ (e d)
    have hmid : subR (toR w) o = addR (smulR (1 - (1 / 2 : ℝ)) (subR (toR p₁) o))
        (smulR (1 / 2 : ℝ) (subR (toR p₂) o)) := by
      rw [hp2]
      unfold w addS smulS subR toR addR smulR
      push_cast
      ext <;> dsimp only <;> ring
    have hqw : Q (subR (toR w) o) ≤ 1 := by
      rw [hmid]; exact Q_convex (by norm_num) (by norm_num) h₁ h₂
    have hw_mem : w ∈ layerFinset o r k := (mem_layerFinset _ _ _ _).mpr (inKS_of_Q_le_one hr hqw)
    have hs1 : unitStep p₁ w := unitStep_addS_e p₁ d
    have hs2 : unitStep w p₂ := by
      rw [unitStep_iff_exists_dir]
      refine ⟨d, ?_⟩
      rw [hp2]; unfold w addS smulS; ext <;> dsimp only <;> ring
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single ⟨hp₁, hw_mem, hs1⟩)
      (Relation.ReflTransGen.single ⟨hw_mem, hp₂, hs2⟩)

private lemma layer_step_closer {o : Center} {r : ℝ} {k : ℕ} (hr : (k : ℝ) + 1 ≤ r)
    {p : Site} (hp : p ∈ layerFinset o r k) (hgt : 1 < Q (subR (toR p) o)) :
    ∃ p' ∈ layerFinset o r k, unitStep p p' ∧ Q (subR (toR p') o) < Q (subR (toR p) o) := by
  set u := subR (toR p) o with hu_def
  have hu : inKR (0, 0) r k u := (inKR_shift_zero o r k (toR p)).mp ((mem_layerFinset _ _ _ _).mp hp)
  obtain ⟨n, flip, h2, h1⟩ := exists_d6_fundamental u
  set v := if flip then tauR (rotR^[n.val] u) else rotR^[n.val] u with hv_def
  have hQuv : Q v = Q u := by
    rw [hv_def]
    cases flip
    · simp only [Bool.false_eq_true, ite_false]; exact rotR_iter_Q n.val u
    · simp only [ite_true]; rw [Q_tauR, rotR_iter_Q]
  have hv : inKR (0, 0) r k v := by
    rw [hv_def]
    cases flip
    · simp only [Bool.false_eq_true, ite_false]; exact (inKR_rot_iter_iff r k n.val u).mpr hu
    · simp only [ite_true]; exact (inKR_tau_iff r k _).mpr ((inKR_rot_iter_iff r k n.val u).mpr hu)
  have hQv : 1 < Q v := by linarith
  have hv3 : inKR (0, 0) r k (addR v (toR (e 3))) := sector_inward_e3 hr (by linarith) h2 hv
  have hdec : Q (addR v (toR (e 3))) < Q v := by
    have h3q : (2 * v.1 + v.2) ^ 2 ≥ 3 * Q v := by unfold Q; nlinarith
    have hpos : 2 * v.1 + v.2 > 1 := by nlinarith
    unfold Q at hQv; unfold Q addR toR e; norm_num; nlinarith
  let d₀ : ZMod 6 := (if flip then tauDir 3 else 3) - (n.val : ZMod 6)
  let p' := addS p (e d₀)
  have hsub_add : subR (toR p') o = addR u (toR (e d₀)) := by
    rw [hu_def]; unfold p' addS subR toR addR; push_cast; ext <;> dsimp only <;> ring
  cases flip
  · have hrel : rotR^[n.val] (subR (toR p') o) = addR v (toR (e 3)) := by
      rw [hsub_add, rotR_iter_add, rotR_iter_toR, rotS_iter_e, hv_def]
      simp only [d₀, Bool.false_eq_true, ite_false, sub_add_cancel]
    have hp'_mem : p' ∈ layerFinset o r k := by
      rw [mem_layerFinset]; unfold inKS; rw [inKR_shift_zero, ← inKR_rot_iter_iff r k n.val, hrel]
      exact hv3
    have hQp' : Q (subR (toR p') o) < Q (subR (toR p) o) := by
      have hQ1 : Q (subR (toR p') o) = Q (addR v (toR (e 3))) := by
        rw [← rotR_iter_Q n.val, hrel]
      linarith
    exact ⟨p', hp'_mem, unitStep_addS_e p d₀, hQp'⟩
  · have hrel : tauR (rotR^[n.val] (subR (toR p') o)) = addR v (toR (e 3)) := by
      rw [hsub_add, rotR_iter_add, rotR_iter_toR, rotS_iter_e, hv_def]
      simp only [d₀, ite_true, sub_add_cancel, tauR_add, tauR_toR, tauS_e, tauDir_invol]
    have hp'_mem : p' ∈ layerFinset o r k := by
      rw [mem_layerFinset]; unfold inKS; rw [inKR_shift_zero, ← inKR_rot_iter_iff r k n.val, ← inKR_tau_iff r k, hrel]
      exact hv3
    have hQp' : Q (subR (toR p') o) < Q (subR (toR p) o) := by
      have hQ1 : Q (subR (toR p') o) = Q (addR v (toR (e 3))) := by
        rw [← rotR_iter_Q n.val, ← Q_tauR, hrel]
      linarith
    exact ⟨p', hp'_mem, unitStep_addS_e p d₀, hQp'⟩

private lemma layer_reach_unitDisk {o : Center} {r : ℝ} {k : ℕ} (hr : (k : ℝ) + 1 ≤ r) :
    ∀ p ∈ layerFinset o r k, ∃ p₀ : Site, Q (subR (toR p₀) o) ≤ 1 ∧ ReachIn (layerFinset o r k) p p₀ := by
  classical
  let flt (p : Site) : Finset Site :=
    (layerFinset o r k).filter (fun w => Q (subR (toR w) o) < Q (subR (toR p) o))
  have hmain : ∀ N : ℕ, ∀ p ∈ layerFinset o r k, (flt p).card ≤ N →
      ∃ p₀ : Site, Q (subR (toR p₀) o) ≤ 1 ∧ ReachIn (layerFinset o r k) p p₀ := by
    intro N
    induction N with
    | zero =>
      intro p hp hcard
      by_cases hle : Q (subR (toR p) o) ≤ 1
      · exact ⟨p, hle, Relation.ReflTransGen.refl⟩
      · obtain ⟨p', hp'_mem, _, hQp'⟩ := layer_step_closer hr hp (lt_of_not_ge hle)
        have hmem_filt : p' ∈ flt p := by simp [flt, hp'_mem, hQp']
        have hpos : 0 < (flt p).card := Finset.card_pos.mpr ⟨p', hmem_filt⟩
        omega
    | succ N ih =>
      intro p hp hcard
      by_cases hle : Q (subR (toR p) o) ≤ 1
      · exact ⟨p, hle, Relation.ReflTransGen.refl⟩
      · obtain ⟨p', hp'_mem, hstep, hQp'⟩ := layer_step_closer hr hp (lt_of_not_ge hle)
        have hss : flt p' ⊂ flt p := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨p', by simp [flt, hp'_mem, hQp'], by simp [flt]⟩
          · intro w hw
            simp only [flt, Finset.mem_filter] at hw ⊢
            exact ⟨hw.1, lt_trans hw.2 hQp'⟩
        have hcard' : (flt p').card ≤ N := by
          have hlt := Finset.card_lt_card hss
          omega
        obtain ⟨p₀, hq₀, hreach⟩ := ih p' hp'_mem hcard'
        exact ⟨p₀, hq₀, Relation.ReflTransGen.head ⟨hp, hp'_mem, hstep⟩ hreach⟩
  intro p hp
  exact hmain _ p hp le_rfl

private lemma layer_connS {o : Center} {r : ℝ} {k : ℕ} (hr : (k : ℝ) + 1 ≤ r) :
    ConnS (layerFinset o r k) := by
  intro a ha b hb
  obtain ⟨a₀, ha₀, hra⟩ := layer_reach_unitDisk hr a ha
  obtain ⟨b₀, hb₀, hrb⟩ := layer_reach_unitDisk hr b hb
  exact Relation.ReflTransGen.trans hra
    (Relation.ReflTransGen.trans (reachIn_unitDisk hr ha₀ hb₀) (reachIn_symm hrb))

/-! ### Section 9: Real-radius core classification (0 ≤ r < q + 1) -/

private lemma core_linear_bounds {o : Center} {r : ℝ} {q : ℕ} {p : Site}
    (hr0 : 0 ≤ r) (hr : r < (q : ℝ) + 1) (hp : p ∈ layerFinset o r q) :
    |2 * ((p.1 : ℝ) - o.1) + ((p.2 : ℝ) - o.2)| < 2 ∧
    |((p.1 : ℝ) - o.1) + 2 * ((p.2 : ℝ) - o.2)| < 2 ∧
    |((p.1 : ℝ) - o.1) - ((p.2 : ℝ) - o.2)| < 2 := by
  rw [mem_layerFinset] at hp
  set u := subR (toR p) o
  have hgen : ∀ d : ZMod 6,
      2 * u.1 * (toR (e d)).1 + u.1 * (toR (e d)).2 + u.2 * (toR (e d)).1 + 2 * u.2 * (toR (e d)).2 < 2 := by
    intro d
    have hd := hp d
    set v := toR (e d)
    have hv : Q v = 1 := Q_e d
    set L := 2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2
    have hcs : L ^ 2 ≤ 4 * Q u := by
      have := Q_cauchy u v; rw [hv, mul_one] at this; exact this
    have hexp : 4 * Q (addR u (smulR (q : ℝ) v)) =
        4 * Q u + 4 * (q : ℝ) * L + 4 * (q : ℝ) ^ 2 * Q v := by
      unfold Q addR smulR L; ring
    have hsq : (L + 2 * (q : ℝ)) ^ 2 < (2 * (q : ℝ) + 2) ^ 2 := by
      have h1 : (L + 2 * (q : ℝ)) ^ 2 ≤ 4 * r ^ 2 := by
        rw [hv, mul_one] at hexp
        nlinarith
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      nlinarith
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith
  have h0 := hgen 0; have h3 := hgen 3
  have h1 := hgen 1; have h4 := hgen 4
  have h5 := hgen 5; have h2 := hgen 2
  unfold u subR toR e at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩,
          abs_lt.mpr ⟨by linarith, by linarith⟩,
          abs_lt.mpr ⟨by linarith, by linarith⟩⟩

private lemma core_pair_QZ {o : Center} {r : ℝ} {q : ℕ} {p₁ p₂ : Site}
    (hr0 : 0 ≤ r) (hr : r < (q : ℝ) + 1)
    (h₁ : p₁ ∈ layerFinset o r q) (h₂ : p₂ ∈ layerFinset o r q) :
    let v := subS p₂ p₁
    |2 * v.1 + v.2| ≤ 3 ∧ |v.1 + 2 * v.2| ≤ 3 ∧ |v.1 - v.2| ≤ 3 ∧
      (QZ v = 0 ∨ QZ v = 1 ∨ QZ v = 3) := by
  obtain ⟨a1, a2, a3⟩ := core_linear_bounds hr0 hr h₁
  obtain ⟨b1, b2, b3⟩ := core_linear_bounds hr0 hr h₂
  rw [abs_lt] at a1 a2 a3 b1 b2 b3
  set v := subS p₂ p₁
  have h1R : |(2 * v.1 + v.2 : ℝ)| < 4 := by
    rw [abs_lt]; unfold v subS; push_cast; constructor <;> linarith
  have h2R : |(v.1 + 2 * v.2 : ℝ)| < 4 := by
    rw [abs_lt]; unfold v subS; push_cast; constructor <;> linarith
  have h3R : |(v.1 - v.2 : ℝ)| < 4 := by
    rw [abs_lt]; unfold v subS; push_cast; constructor <;> linarith
  have h1 : |2 * v.1 + v.2| ≤ 3 := by
    rw [abs_lt] at h1R; rw [abs_le]
    have ha : -4 < 2 * v.1 + v.2 := by exact_mod_cast h1R.1
    have hb : 2 * v.1 + v.2 < 4 := by exact_mod_cast h1R.2
    omega
  have h2 : |v.1 + 2 * v.2| ≤ 3 := by
    rw [abs_lt] at h2R; rw [abs_le]
    have ha : -4 < v.1 + 2 * v.2 := by exact_mod_cast h2R.1
    have hb : v.1 + 2 * v.2 < 4 := by exact_mod_cast h2R.2
    omega
  have h3 : |v.1 - v.2| ≤ 3 := by
    rw [abs_lt] at h3R; rw [abs_le]
    have ha : -4 < v.1 - v.2 := by exact_mod_cast h3R.1
    have hb : v.1 - v.2 < 4 := by exact_mod_cast h3R.2
    omega
  refine ⟨h1, h2, h3, ?_⟩
  rcases hv_eq : v with ⟨vx, vy⟩
  rw [hv_eq] at h1 h2 h3
  dsimp only at h1 h2 h3 ⊢
  rw [abs_le] at h1 h2 h3
  have hx1 : -2 ≤ vx := by omega
  have hx2 : vx ≤ 2 := by omega
  have hy1 : -2 ≤ vy := by omega
  have hy2 : vy ≤ 2 := by omega
  dsimp only [QZ]
  interval_cases vy <;> interval_cases vx <;> omega

private lemma core_no_sqrt3_tri {o : Center} {r : ℝ} {q : ℕ} {a : Site}
    (hr0 : 0 ≤ r) (hr : r < (q : ℝ) + 1)
    (ha : a ∈ layerFinset o r q) (hb : addS a (1, 1) ∈ layerFinset o r q) :
    addS a (-1, 2) ∉ layerFinset o r q ∧ addS a (2, -1) ∉ layerFinset o r q := by
  rw [mem_layerFinset] at ha hb
  constructor
  · intro hc
    rw [mem_layerFinset] at hc
    have h1 := ha 4; have h2 := hb 0; have h3 := hc 2
    have hsum :
        Q (addR (subR (toR a) o) (smulR (q : ℝ) (toR (e 4)))) +
        Q (addR (subR (toR (addS a (1, 1))) o) (smulR (q : ℝ) (toR (e 0)))) +
        Q (addR (subR (toR (addS a (-1, 2))) o) (smulR (q : ℝ) (toR (e 2)))) =
        3 * Q (subR (toR (addS a (0, 1))) o) + 3 * ((q : ℝ) + 1) ^ 2 := by
      unfold Q addR subR smulR toR addS e; push_cast; ring
    have hq0 := Q_nonneg (subR (toR (addS a (0, 1))) o)
    have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith
  · intro hc
    rw [mem_layerFinset] at hc
    have h1 := ha 3; have h2 := hb 1; have h3 := hc 5
    have hsum :
        Q (addR (subR (toR a) o) (smulR (q : ℝ) (toR (e 3)))) +
        Q (addR (subR (toR (addS a (1, 1))) o) (smulR (q : ℝ) (toR (e 1)))) +
        Q (addR (subR (toR (addS a (2, -1))) o) (smulR (q : ℝ) (toR (e 5)))) =
        3 * Q (subR (toR (addS a (1, 0))) o) + 3 * ((q : ℝ) + 1) ^ 2 := by
      unfold Q addR subR smulR toR addS e; push_cast; ring
    have hq0 := Q_nonneg (subR (toR (addS a (1, 0))) o)
    have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith

private lemma core_rhombus_complete {o : Center} {r : ℝ} {q : ℕ} {a : Site}
    (hr0 : 0 ≤ r) (hr : r < (q : ℝ) + 1)
    (ha : a ∈ layerFinset o r q) (hb : addS a (1, 1) ∈ layerFinset o r q) :
    addS a (1, 0) ∈ layerFinset o r q ∧ addS a (0, 1) ∈ layerFinset o r q := by
  obtain ⟨ha1, ha2, _⟩ := core_linear_bounds hr0 hr ha
  obtain ⟨hb1, hb2, _⟩ := core_linear_bounds hr0 hr hb
  rw [abs_lt] at ha1 ha2 hb1 hb2
  unfold addS at hb1 hb2
  push_cast at hb1 hb2
  set u₁ : ℝ := o.1 - (a.1 : ℝ) - 1 / 2 with hu1_def
  set u₂ : ℝ := o.2 - (a.2 : ℝ) - 1 / 2 with hu2_def
  have hu1 : -(1 / 2 : ℝ) < 2 * u₁ + u₂ ∧ 2 * u₁ + u₂ < 1 / 2 := by
    rw [hu1_def, hu2_def]; constructor <;> linarith
  have hu2 : -(1 / 2 : ℝ) < u₁ + 2 * u₂ ∧ u₁ + 2 * u₂ < 1 / 2 := by
    rw [hu1_def, hu2_def]; constructor <;> linarith
  have hu12 : -1 < u₁ - u₂ ∧ u₁ - u₂ < 1 := by
    constructor <;> linarith
  rw [mem_layerFinset] at ha hb
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  constructor
  · rw [mem_layerFinset]
    intro d
    fin_cases d
    · have h := hb 0; unfold Q addR subR smulR toR addS e at h ⊢; push_cast at h ⊢
      have hid : ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) ^ 2 -
          (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 0) ^ 2) = (q : ℝ) + 1 / 2 - (u₁ + 2 * u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := hb 1; unfold Q addR subR smulR toR addS e at h ⊢; push_cast at h ⊢
      have hid : ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) ^ 2 -
          (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 1) ^ 2) = 2 * (q : ℝ) + 1 / 2 - (u₁ + 2 * u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := hb 2; unfold Q addR subR smulR toR addS e at h ⊢; push_cast at h ⊢
      have hid : ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) ^ 2 -
          (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 1) ^ 2) = (q : ℝ) + 1 / 2 - (u₁ + 2 * u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := ha 3; unfold Q addR subR smulR toR e at h; unfold Q addR subR smulR toR addS e; push_cast at h ⊢
      have hid : ((a.1 : ℝ) - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) - o.2 + (q : ℝ) * 0) ^ 2 -
          (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * 0) ^ 2) = 2 * (q : ℝ) + 1 / 2 + (2 * u₁ + u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := ha 4; unfold Q addR subR smulR toR e at h; unfold Q addR subR smulR toR addS e; push_cast at h ⊢
      have hid : ((a.1 : ℝ) - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) - o.2 + (q : ℝ) * -1) ^ 2 -
          (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * -1) ^ 2) = (q : ℝ) + 1 / 2 + (2 * u₁ + u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h1 := hb 0; have h2 := ha 4
      unfold Q addR subR smulR toR addS e at h1 ⊢; unfold Q addR subR smulR toR e at h2; push_cast at h1 h2 ⊢
      have hid : (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) ^ 2) +
          (((a.1 : ℝ) - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) - o.2 + (q : ℝ) * -1) ^ 2) -
          2 * (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) + 0 - o.2 + (q : ℝ) * -1) ^ 2) = ((q : ℝ) + 1) * (1 + (u₁ - u₂)) := by
        rw [hu1_def, hu2_def]; ring
      have hpos : (0 : ℝ) ≤ ((q : ℝ) + 1) * (1 + (u₁ - u₂)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
  · rw [mem_layerFinset]
    intro d
    fin_cases d
    · have h := hb 0; unfold Q addR subR smulR toR addS e at h ⊢; push_cast at h ⊢
      have hid : ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) ^ 2 -
          (((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) ^ 2) = 2 * (q : ℝ) + 1 / 2 - (2 * u₁ + u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := hb 1; unfold Q addR subR smulR toR addS e at h ⊢; push_cast at h ⊢
      have hid : ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) ^ 2 -
          (((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) ^ 2) = (q : ℝ) + 1 / 2 - (2 * u₁ + u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h1 := hb 1; have h2 := ha 3
      unfold Q addR subR smulR toR addS e at h1 ⊢; unfold Q addR subR smulR toR e at h2; push_cast at h1 h2 ⊢
      have hid : (((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) ^ 2) +
          (((a.1 : ℝ) - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) - o.2 + (q : ℝ) * 0) ^ 2) -
          2 * (((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 1) ^ 2) = ((q : ℝ) + 1) * (1 - (u₁ - u₂)) := by
        rw [hu1_def, hu2_def]; ring
      have hpos : (0 : ℝ) ≤ ((q : ℝ) + 1) * (1 - (u₁ - u₂)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · have h := ha 3; unfold Q addR subR smulR toR e at h; unfold Q addR subR smulR toR addS e; push_cast at h ⊢
      have hid : ((a.1 : ℝ) - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) - o.2 + (q : ℝ) * 0) ^ 2 -
          (((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * -1) ^ 2 +
          ((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * -1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * 0) ^ 2) = (q : ℝ) + 1 / 2 + (u₁ + 2 * u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := ha 4; unfold Q addR subR smulR toR e at h; unfold Q addR subR smulR toR addS e; push_cast at h ⊢
      have hid : ((a.1 : ℝ) - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) - o.2 + (q : ℝ) * -1) ^ 2 -
          (((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 0) ^ 2 +
          ((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 0) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * -1) ^ 2) = 2 * (q : ℝ) + 1 / 2 + (u₁ + 2 * u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith
    · have h := hb 5; unfold Q addR subR smulR toR addS e at h ⊢; push_cast at h ⊢
      have hid : ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 1 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * -1) ^ 2 -
          (((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 1) ^ 2 +
          ((a.1 : ℝ) + 0 - o.1 + (q : ℝ) * 1) * ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * -1) +
          ((a.2 : ℝ) + 1 - o.2 + (q : ℝ) * -1) ^ 2) = (q : ℝ) + 1 / 2 - (2 * u₁ + u₂) := by
        rw [hu1_def, hu2_def]; ring
      linarith

/-! ### Section 7: Cycle splicing API and Zero-Topology Boundary Cycle Theorem -/

private lemma zmod6_cases (z : ZMod 6) :
    z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private lemma zmod6_shift_cases (c d : ZMod 6) :
    c = d ∨ c = d + 1 ∨ c = d + 2 ∨ c = d + 3 ∨ c = d + 4 ∨ c = d + 5 := by
  rcases zmod6_cases (c - d) with h | h | h | h | h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (Or.inl (eq_add_of_sub_eq' h))
  · exact Or.inr (Or.inr (Or.inl (eq_add_of_sub_eq' h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_add_of_sub_eq' h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_add_of_sub_eq' h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_add_of_sub_eq' h)))))

private def IsHamCycle (S : Finset Site) (L : List Site) : Prop :=
  3 ≤ L.length ∧
  L.Nodup ∧
  (∀ x, x ∈ L ↔ x ∈ S) ∧
  (∀ (i : ℕ) (hi : i < L.length),
    unitStep L[i] (L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega))))

private def HasHamCycle (S : Finset Site) : Prop :=
  ∃ L : List Site, IsHamCycle S L

private lemma isHamCycle_card_eq {S : Finset Site} {L : List Site} (h : IsHamCycle S L) :
    L.length = S.card := by
  have hfin : L.toFinset = S := by
    ext x; simp [h.2.2.1 x]
  rw [← hfin, List.toFinset_card_of_nodup h.2.1]

private lemma mod_add_cancel {n i j k : ℕ} (hi : i < n) (hj : j < n)
    (h : (i + k) % n = (j + k) % n) : i = j := by
  have h1 : (i + k + (n - k % n)) % n = (j + k + (n - k % n)) % n := by
    rw [Nat.add_mod (i + k), h, ← Nat.add_mod (j + k)]
  have hk : (k + (n - k % n)) % n = 0 := by
    have hlt : k % n < n := Nat.mod_lt k (by omega)
    have hdiv : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
    have hmul : n * (k / n + 1) = n * (k / n) + n := by ring
    rw [show k + (n - k % n) = n * (k / n + 1) by omega]
    exact Nat.mul_mod_right n _
  have hsimp : ∀ x < n, (x + k + (n - k % n)) % n = x := by
    intro x hx
    rw [add_assoc, Nat.add_mod, hk, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hx]
  rw [hsimp i hi, hsimp j hj] at h1
  exact h1

private def rotCycle (C : List Site) (hC : 0 < C.length) (k : ℕ) : List Site :=
  List.ofFn (fun i : Fin C.length => C[(i.val + k) % C.length]'(Nat.mod_lt _ hC))

private lemma rotCycle_length (C : List Site) (hC : 0 < C.length) (k : ℕ) :
    (rotCycle C hC k).length = C.length := by
  simp [rotCycle]

private lemma rotCycle_getElem (C : List Site) (hC : 0 < C.length) (k i : ℕ)
    (hi : i < (rotCycle C hC k).length) :
    (rotCycle C hC k)[i] = C[(i + k) % C.length]'(Nat.mod_lt _ hC) := by
  simp [rotCycle]

private lemma isHamCycle_rotCycle {S : Finset Site} {C : List Site}
    (hC : IsHamCycle S C) (k : ℕ) :
    IsHamCycle S (rotCycle C (by have := hC.1; omega) k) := by
  have hpos : 0 < C.length := by have := hC.1; omega
  have hlen : (rotCycle C hpos k).length = C.length := rotCycle_length C hpos k
  refine ⟨by rw [hlen]; exact hC.1, ?_, ?_, ?_⟩
  · unfold rotCycle
    rw [List.nodup_ofFn]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    have hmod : (i + k) % C.length = (j + k) % C.length :=
      (hC.2.1.getElem_inj_iff).mp heq
    exact Fin.ext (mod_add_cancel hi hj hmod)
  · intro x
    rw [← hC.2.2.1 x]
    unfold rotCycle
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact List.getElem_mem _
    · intro hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      let i : ℕ := (j + (C.length - k % C.length)) % C.length
      have hi : i < C.length := Nat.mod_lt _ hpos
      refine ⟨⟨i, hi⟩, ?_⟩
      dsimp only
      congr 1
      have hlt : k % C.length < C.length := Nat.mod_lt k hpos
      have hdiv : k = C.length * (k / C.length) + k % C.length := (Nat.div_add_mod k C.length).symm
      have hmul : C.length * (k / C.length + 1) = C.length * (k / C.length) + C.length := by ring
      have hk : (C.length - k % C.length + k) % C.length = 0 := by
        rw [show C.length - k % C.length + k = C.length * (k / C.length + 1) by omega]
        exact Nat.mul_mod_right C.length _
      have hcalc : (i + k) % C.length = j := by
        dsimp only [i]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc, Nat.add_mod j, hk, add_zero,
            Nat.mod_mod, Nat.mod_eq_of_lt hj]
      exact hcalc
  · intro i hi
    have hi' : i < C.length := by omega
    rw [rotCycle_getElem C hpos k i hi, rotCycle_getElem C hpos k ((i + 1) % (rotCycle C hpos k).length)]
    have hstep := hC.2.2.2 ((i + k) % C.length) (Nat.mod_lt _ hpos)
    have hidx : ((i + 1) % (rotCycle C hpos k).length + k) % C.length =
        ((i + k) % C.length + 1) % C.length := by
      rw [hlen]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [Nat.add_mod ((i + k) % C.length), Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    convert hstep using 2

/-- Universal path-into-cycle splice lemma: handles Steps 8.1, 8.3 (K_2 and HamCycle), and 8.4 (D_13). -/
private lemma splice_path_into_cycle {B I : Finset Site} {C P : List Site}
    (hdisj : Disjoint B I)
    (hC : IsHamCycle B C)
    (idx : ℕ) (hidx : idx < C.length)
    (hP_pos : 0 < P.length)
    (hP_nodup : P.Nodup)
    (hP_mem : ∀ x, x ∈ P ↔ x ∈ I)
    (hP_step : ∀ (j : ℕ) (hj : j + 1 < P.length), unitStep P[j] P[j + 1])
    (h_in : unitStep C[idx] (P[0]'hP_pos))
    (h_out : unitStep (P[P.length - 1]'(by omega)) (C[(idx + 1) % C.length]'(Nat.mod_lt _ (by have := hC.1; omega)))) :
    HasHamCycle (B ∪ I) := by
  have hCpos : 0 < C.length := by have := hC.1; omega
  let k : ℕ := (idx + 1) % C.length
  let C' : List Site := rotCycle C hCpos k
  have hC' : IsHamCycle B C' := isHamCycle_rotCycle hC k
  have hC'len : C'.length = C.length := rotCycle_length C hCpos k
  have hC'0 : C'[0]'(by omega) = C[(idx + 1) % C.length]'(Nat.mod_lt _ hCpos) := by
    rw [rotCycle_getElem]
    congr 1
    simp [k]
  have hC'last : C'[C'.length - 1]'(by omega) = C[idx] := by
    rw [rotCycle_getElem]
    congr 1
    have hcalc : (C'.length - 1 + k) % C.length = idx := by
      rw [hC'len]
      dsimp only [k]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [show C.length - 1 + (idx + 1) = idx + C.length by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
    exact hcalc
  refine ⟨C' ++ P, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]; have := hC'.1; omega
  · rw [List.nodup_append]
    refine ⟨hC'.2.1, hP_nodup, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have hxB : x ∈ B := (hC'.2.2.1 x).mp hx
    have hxI : x ∈ I := (hP_mem x).mp hy
    exact Finset.disjoint_left.mp hdisj hxB hxI
  · intro x
    rw [List.mem_append, Finset.mem_union, hC'.2.2.1 x, hP_mem x]
  · intro i hi
    rw [List.length_append] at hi
    by_cases h1 : i + 1 < C'.length
    · have hmod : (i + 1) % (C' ++ P).length = i + 1 := by
        rw [List.length_append]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hmod]
      rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
      have hs := hC'.2.2.2 i (by omega)
      simpa only [Nat.mod_eq_of_lt h1] using hs
    · by_cases h2 : i = C'.length - 1
      · have hmod : (i + 1) % (C' ++ P).length = C'.length := by
          rw [List.length_append, h2, show C'.length - 1 + 1 = C'.length by omega]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [hmod]
        rw [List.getElem_append_left (by omega), List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, h2, hC'last]
        exact h_in
      · by_cases h3 : i + 1 < C'.length + P.length
        · have hge : C'.length ≤ i := by omega
          have hmod : (i + 1) % (C' ++ P).length = i + 1 := by
            rw [List.length_append]; exact Nat.mod_eq_of_lt h3
          simp only [hmod]
          rw [List.getElem_append_right hge, List.getElem_append_right (by omega)]
          have hs := hP_step (i - C'.length) (by omega)
          have heq : i + 1 - C'.length = i - C'.length + 1 := by omega
          simpa only [heq] using hs
        · have hi_last : i = C'.length + P.length - 1 := by omega
          have hmod : (i + 1) % (C' ++ P).length = 0 := by
            rw [List.length_append, hi_last, show C'.length + P.length - 1 + 1 = C'.length + P.length by omega]
            exact Nat.mod_self _
          simp only [hmod]
          rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
          have heq : i - C'.length = P.length - 1 := by omega
          simpa only [heq, hC'0] using h_out

/-- Extract a Hamiltonian path from a to b by deleting a cyclic edge {a, b} of a cycle C. -/
private lemma path_of_cycle_edge {I : Finset Site} {C : List Site}
    (hC : IsHamCycle I C) (j : ℕ) (hj : j < C.length) :
    ∃ (P : List Site) (hP : 0 < P.length),
      P.Nodup ∧ (∀ x, x ∈ P ↔ x ∈ I) ∧
      (∀ (t : ℕ) (ht : t + 1 < P.length), unitStep P[t] P[t + 1]) ∧
      P[0]'hP = C[(j + 1) % C.length]'(Nat.mod_lt _ (by have := hC.1; omega)) ∧
      P[P.length - 1]'(by omega) = C[j] := by
  have hpos : 0 < C.length := by have := hC.1; omega
  let P := rotCycle C hpos ((j + 1) % C.length)
  have hP := isHamCycle_rotCycle hC ((j + 1) % C.length)
  have hlen : P.length = C.length := rotCycle_length C hpos _
  refine ⟨P, by omega, hP.2.1, hP.2.2.1, ?_, ?_, ?_⟩
  · intro t ht
    dsimp only [P] at ht ⊢
    have ht' : t < (rotCycle C hpos ((j + 1) % C.length)).length := by omega
    have hs := hP.2.2.2 t ht'
    simpa only [Nat.mod_eq_of_lt ht] using hs
  · rw [rotCycle_getElem]
    congr 1; simp
  · rw [rotCycle_getElem]
    congr 1
    rw [hlen, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [show C.length - 1 + (j + 1) = j + C.length by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]

private lemma path_reverse {I : Finset Site} {P : List Site}
    (hpos : 0 < P.length) (hnd : P.Nodup) (hmem : ∀ x, x ∈ P ↔ x ∈ I)
    (hstep : ∀ (t : ℕ) (ht : t + 1 < P.length), unitStep P[t] P[t + 1]) :
    0 < P.reverse.length ∧ P.reverse.Nodup ∧ (∀ x, x ∈ P.reverse ↔ x ∈ I) ∧
    (∀ (t : ℕ) (ht : t + 1 < P.reverse.length), unitStep P.reverse[t] P.reverse[t + 1]) ∧
    P.reverse[0]'(by rw [List.length_reverse]; exact hpos) = P[P.length - 1]'(by omega) ∧
    P.reverse[P.reverse.length - 1]'(by rw [List.length_reverse]; omega) = P[0]'hpos := by
  refine ⟨by simpa, List.nodup_reverse.mpr hnd, fun x => by rw [List.mem_reverse, hmem x], ?_, ?_, ?_⟩
  · intro t ht
    rw [List.length_reverse] at ht
    rw [List.getElem_reverse, List.getElem_reverse]
    have hs := hstep (P.length - 1 - (t + 1)) (by omega)
    have heq : P.length - 1 - (t + 1) + 1 = P.length - 1 - t := by omega
    exact unitStep_symm (by simpa only [heq] using hs)
  · rw [List.getElem_reverse]; simp
  · rw [List.getElem_reverse]; congr 1; rw [List.length_reverse]; omega

/-- Lexicographic order on Site: smaller y first, then smaller x. -/
private def lexLt (a b : Site) : Prop :=
  a.2 < b.2 ∨ (a.2 = b.2 ∧ a.1 < b.1)

private lemma lexLt_irrefl (a : Site) : ¬ lexLt a a := by
  unfold lexLt; omega

private lemma lexLt_antisymm {a b : Site} (h1 : lexLt a b) (h2 : lexLt b a) : False := by
  unfold lexLt at h1 h2; omega

private lemma lexLt_e_iff (u : Site) (d : ZMod 6) :
    lexLt u (addS u (e d)) ↔ d = 0 ∨ d = 1 ∨ d = 2 := by
  fin_cases d <;> unfold lexLt addS e <;> dsimp only
  · exact iff_of_true (Or.inr ⟨by omega, by omega⟩) (Or.inl rfl)
  · exact iff_of_true (Or.inl (by omega)) (Or.inr (Or.inl rfl))
  · exact iff_of_true (Or.inl (by omega)) (Or.inr (Or.inr rfl))
  · exact iff_of_false (by omega) (by rintro (h | h | h) <;> exact absurd (congrArg (@ZMod.val 6) h) (by decide))
  · exact iff_of_false (by omega) (by rintro (h | h | h) <;> exact absurd (congrArg (@ZMod.val 6) h) (by decide))
  · exact iff_of_false (by omega) (by rintro (h | h | h) <;> exact absurd (congrArg (@ZMod.val 6) h) (by decide))

private lemma exists_lexMin {T : Finset Site} (hT : T.Nonempty) :
    ∃ u ∈ T, ∀ v ∈ T, v ≠ u → lexLt u v := by
  obtain ⟨p, hpT, hpmin⟩ := Finset.exists_min_image T Prod.snd hT
  let row := T.filter (fun q => q.2 = p.2)
  have hrow_ne : row.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hpT, rfl⟩⟩
  obtain ⟨u, hurow, humin⟩ := Finset.exists_min_image row Prod.fst hrow_ne
  have huT : u ∈ T := (Finset.mem_filter.mp hurow).1
  have huy : u.2 = p.2 := (Finset.mem_filter.mp hurow).2
  refine ⟨u, huT, ?_⟩
  intro v hvT hvne
  have hvy : u.2 ≤ v.2 := by rw [huy]; exact hpmin v hvT
  by_cases heq : u.2 = v.2
  · right
    refine ⟨heq, ?_⟩
    have hvrow : v ∈ row := Finset.mem_filter.mpr ⟨hvT, by rw [← heq, huy]⟩
    have hvx : u.1 ≤ v.1 := humin v hvrow
    by_contra hge
    apply hvne
    ext <;> omega
  · left; omega

/-- Basic ZMod 6 arc consequences of IsArcGeTwo. -/
private lemma isArcGeTwo_step_false {A : ZMod 6 → Prop} (hA : IsArcGeTwo A)
    {x : ZMod 6} (hx : A x) (hxm : ¬ A (x - 1))
    {c : ZMod 6} (hne : c ≠ x) (hcm : ¬ A (c - 1)) : ¬ A c := by
  intro hc
  exact hne (hA.2 c x hc hcm hx hxm)

private lemma isArcGeTwo_exists_entry {A : ZMod 6 → Prop} (hA : IsArcGeTwo A)
    (hmiss : ∃ d : ZMod 6, ¬ A d) : ∃ d : ZMod 6, A d ∧ ¬ A (d - 1) := by
  obtain ⟨d₀, hd₀⟩ := hmiss
  obtain ⟨d₁, _, _, hd₁, _⟩ := hA.1
  by_cases h1 : A (d₀ + 1)
  · exact ⟨d₀ + 1, h1, by rwa [add_sub_cancel_right]⟩
  · by_cases h2 : A (d₀ + 2)
    · exact ⟨d₀ + 2, h2, by convert h1 using 2; ring⟩
    · by_cases h3 : A (d₀ + 3)
      · exact ⟨d₀ + 3, h3, by convert h2 using 2; ring⟩
      · by_cases h4 : A (d₀ + 4)
        · exact ⟨d₀ + 4, h4, by convert h3 using 2; ring⟩
        · by_cases h5 : A (d₀ + 5)
          · exact ⟨d₀ + 5, h5, by convert h4 using 2; ring⟩
          · exfalso
            rcases zmod6_shift_cases d₁ d₀ with rfl | rfl | rfl | rfl | rfl | rfl
            · exact hd₀ hd₁
            · exact h1 hd₁
            · exact h2 hd₁
            · exact h3 hd₁
            · exact h4 hd₁
            · exact h5 hd₁

private lemma isArcGeTwo_shift {A : ZMod 6 → Prop} (hA : IsArcGeTwo A) (s : ZMod 6) :
    IsArcGeTwo (fun d => A (d + s)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨d₁, d₂, hne, h1, h2⟩ := hA.1
    refine ⟨d₁ - s, d₂ - s, ?_, by dsimp only; rwa [sub_add_cancel], by dsimp only; rwa [sub_add_cancel]⟩
    intro h; exact hne (sub_left_inj.mp h)
  · intro d₁ d₂ h1 m1 h2 m2
    dsimp only at h1 m1 h2 m2
    have heq := hA.2 (d₁ + s) (d₂ + s) h1 (by rwa [add_sub_right_comm]) h2 (by rwa [add_sub_right_comm])
    exact add_right_cancel heq

private lemma isArcGeTwo_entry_ne_exit {A : ZMod 6 → Prop} (hA : IsArcGeTwo A)
    {d a : ZMod 6} (hd : A d) (hdm : ¬ A (d - 1)) (ha : A a) (hap : ¬ A (a + 1)) : d ≠ a := by
  intro heq
  subst heq
  have h1 : ¬ A (d + 1) := hap
  have h2 : ¬ A (d + 2) := isArcGeTwo_step_false hA hd hdm (by intro h; have := sub_eq_zero.mpr h; rw [add_sub_cancel_left] at this; exact absurd (congrArg (@ZMod.val 6) this) (by decide)) (by convert h1 using 2; ring)
  have h3 : ¬ A (d + 3) := isArcGeTwo_step_false hA hd hdm (by intro h; have := sub_eq_zero.mpr h; rw [add_sub_cancel_left] at this; exact absurd (congrArg (@ZMod.val 6) this) (by decide)) (by convert h2 using 2; ring)
  have h4 : ¬ A (d + 4) := isArcGeTwo_step_false hA hd hdm (by intro h; have := sub_eq_zero.mpr h; rw [add_sub_cancel_left] at this; exact absurd (congrArg (@ZMod.val 6) this) (by decide)) (by convert h3 using 2; ring)
  have h5 : ¬ A (d + 5) := isArcGeTwo_step_false hA hd hdm (by intro h; have := sub_eq_zero.mpr h; rw [add_sub_cancel_left] at this; exact absurd (congrArg (@ZMod.val 6) this) (by decide)) (by convert h4 using 2; ring)
  have hall : ∀ c : ZMod 6, A c → c = d := by
    intro c hc
    rcases zmod6_shift_cases c d with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hc h1
    · exact absurd hc h2
    · exact absurd hc h3
    · exact absurd hc h4
    · exact absurd hc h5
  obtain ⟨d₁, d₂, hne, ha₁, ha₂⟩ := hA.1
  exact hne (by rw [hall d₁ ha₁, hall d₂ ha₂])

private lemma isArcGeTwo_unique_exit {A : ZMod 6 → Prop} (hA : IsArcGeTwo A)
    {a₁ a₂ : ZMod 6} (h1 : A a₁) (m1 : ¬ A (a₁ + 1)) (h2 : A a₂) (m2 : ¬ A (a₂ + 1)) :
    a₁ = a₂ := by
  let B : ZMod 6 → Prop := fun i => A (i + a₁)
  have hB : IsArcGeTwo B := isArcGeTwo_shift hA a₁
  have hB0 : B 0 := by simpa [B] using h1
  have hB1 : ¬ B 1 := by simpa [B, add_comm] using m1
  have hBd : B (a₂ - a₁) := by dsimp only [B]; rwa [sub_add_cancel]
  have hBdp : ¬ B ((a₂ - a₁) + 1) := by
    dsimp only [B]
    have : a₂ - a₁ + 1 + a₁ = a₂ + 1 := by ring
    rwa [this]
  have hd0 : a₂ - a₁ = 0 := by
    rcases zmod6_cases (a₂ - a₁) with h | h | h | h | h | h
    · exact h
    · exfalso; rw [h] at hBd; exact hB1 hBd
    · exfalso
      rw [h] at hBd hBdp
      have hx2 : B 2 ∧ ¬ B (2 - 1) := ⟨hBd, by rwa [show (2 : ZMod 6) - 1 = 1 from rfl]⟩
      have h3 : ¬ B 3 := by rwa [show (2 : ZMod 6) + 1 = 3 from rfl] at hBdp
      have h4 : ¬ B 4 := isArcGeTwo_step_false hB hx2.1 hx2.2 (by decide) (by rwa [show (4 : ZMod 6) - 1 = 3 from rfl])
      have h5 : ¬ B 5 := isArcGeTwo_step_false hB hx2.1 hx2.2 (by decide) (by rwa [show (5 : ZMod 6) - 1 = 4 from rfl])
      have h0 : ¬ B 0 := isArcGeTwo_step_false hB hx2.1 hx2.2 (by decide) (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
      exact h0 hB0
    · exfalso
      rw [h] at hBd hBdp
      have h4 : ¬ B 4 := by rwa [show (3 : ZMod 6) + 1 = 4 from rfl] at hBdp
      by_cases h2b : B 2
      · have hx2 : B 2 ∧ ¬ B (2 - 1) := ⟨h2b, by rwa [show (2 : ZMod 6) - 1 = 1 from rfl]⟩
        have h5 : ¬ B 5 := isArcGeTwo_step_false hB hx2.1 hx2.2 (by decide) (by rwa [show (5 : ZMod 6) - 1 = 4 from rfl])
        have h0 : ¬ B 0 := isArcGeTwo_step_false hB hx2.1 hx2.2 (by decide) (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
        exact h0 hB0
      · have hx3 : B 3 ∧ ¬ B (3 - 1) := ⟨hBd, by rwa [show (3 : ZMod 6) - 1 = 2 from rfl]⟩
        have h5 : ¬ B 5 := isArcGeTwo_step_false hB hx3.1 hx3.2 (by decide) (by rwa [show (5 : ZMod 6) - 1 = 4 from rfl])
        have h0 : ¬ B 0 := isArcGeTwo_step_false hB hx3.1 hx3.2 (by decide) (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
        exact h0 hB0
    · exfalso
      rw [h] at hBd hBdp
      have h5 : ¬ B 5 := by rwa [show (4 : ZMod 6) + 1 = 5 from rfl] at hBdp
      by_cases h2b : B 2
      · have hx2 : B 2 ∧ ¬ B (2 - 1) := ⟨h2b, by rwa [show (2 : ZMod 6) - 1 = 1 from rfl]⟩
        have h0 : ¬ B 0 := isArcGeTwo_step_false hB hx2.1 hx2.2 (by decide) (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
        exact h0 hB0
      · by_cases h3b : B 3
        · have hx3 : B 3 ∧ ¬ B (3 - 1) := ⟨h3b, by rwa [show (3 : ZMod 6) - 1 = 2 from rfl]⟩
          have h0 : ¬ B 0 := isArcGeTwo_step_false hB hx3.1 hx3.2 (by decide) (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
          exact h0 hB0
        · have hx4 : B 4 ∧ ¬ B (4 - 1) := ⟨hBd, by rwa [show (4 : ZMod 6) - 1 = 3 from rfl]⟩
          have h0 : ¬ B 0 := isArcGeTwo_step_false hB hx4.1 hx4.2 (by decide) (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
          exact h0 hB0
    · exfalso
      rw [h] at hBdp
      exact hBdp (by rwa [show (5 : ZMod 6) + 1 = 0 from rfl])
  exact (sub_eq_zero.mp hd0).symm

/-- Right-hand boundary direction and boundary dart bijection φ : ∂S → ∂S. -/
private noncomputable def bdyDir (S : Finset Site) (u : Site) : ZMod 6 :=
  if h : ∃ d : ZMod 6, addS u (e d) ∈ S ∧ addS u (e (d - 1)) ∉ S
  then Classical.choose h else 0

private noncomputable def phi (S : Finset Site) (u : Site) : Site :=
  addS u (e (bdyDir S u))

private lemma bdyDir_spec {S : Finset Site} (hloc : LocallyConn S)
    {u : Site} (hu : u ∈ bdyS S) :
    addS u (e (bdyDir S u)) ∈ S ∧ addS u (e (bdyDir S u - 1)) ∉ S := by
  obtain ⟨huS, hmiss⟩ := mem_bdyS.mp hu
  have hex : ∃ d : ZMod 6, addS u (e d) ∈ S ∧ addS u (e (d - 1)) ∉ S :=
    isArcGeTwo_exists_entry (hloc u huS) hmiss
  unfold bdyDir
  rw [dif_pos hex]
  exact Classical.choose_spec hex

private lemma bdyDir_eq_of {S : Finset Site} (hloc : LocallyConn S)
    {u : Site} (huS : u ∈ S) {d : ZMod 6}
    (hin : addS u (e d) ∈ S) (hout : addS u (e (d - 1)) ∉ S) :
    bdyDir S u = d := by
  have hu : u ∈ bdyS S := mem_bdyS.mpr ⟨huS, d - 1, hout⟩
  have hsp := bdyDir_spec hloc hu
  exact (hloc u huS).2 (bdyDir S u) d hsp.1 hsp.2 hin hout

private lemma addS_addS_e (u : Site) (a b : ZMod 6) :
    addS (addS u (e a)) (e b) = addS u (addS (e a) (e b)) := by
  unfold addS; ext <;> dsimp only <;> ring

private lemma e_add_four_eq_sub_one (d : ZMod 6) :
    addS (e d) (e (d + 4)) = e (d - 1) := by
  fin_cases d <;> rfl

private lemma e_add_three_cancel (u : Site) (d : ZMod 6) :
    addS (addS u (e d)) (e (d + 3)) = u := by
  rw [addS_addS_e]
  have h0 : addS (e d) (e (d + 3)) = (0, 0) := by fin_cases d <;> rfl
  rw [h0]; unfold addS; ext <;> simp

private lemma phi_mem_bdyS {S : Finset Site} (hloc : LocallyConn S)
    {u : Site} (hu : u ∈ bdyS S) : phi S u ∈ bdyS S := by
  have hsp := bdyDir_spec hloc hu
  rw [mem_bdyS]
  refine ⟨hsp.1, bdyDir S u + 4, ?_⟩
  unfold phi
  rw [addS_addS_e, e_add_four_eq_sub_one]
  exact hsp.2

private lemma phi_in_exit {S : Finset Site} (hloc : LocallyConn S)
    {u : Site} (hu : u ∈ bdyS S) :
    u = addS (phi S u) (e (bdyDir S u + 3)) ∧
    addS (phi S u) (e (bdyDir S u + 3)) ∈ S ∧
    addS (phi S u) (e (bdyDir S u + 3 + 1)) ∉ S := by
  have huS : u ∈ S := (mem_bdyS.mp hu).1
  have hsp := bdyDir_spec hloc hu
  have h1 : addS (phi S u) (e (bdyDir S u + 3)) = u := e_add_three_cancel u (bdyDir S u)
  refine ⟨h1.symm, by rw [h1]; exact huS, ?_⟩
  unfold phi
  rw [show bdyDir S u + 3 + 1 = bdyDir S u + 4 by ring, addS_addS_e, e_add_four_eq_sub_one]
  exact hsp.2

private lemma phi_injOn {S : Finset Site} (hloc : LocallyConn S) :
    Set.InjOn (phi S) (bdyS S : Set Site) := by
  intro u₁ hu₁ u₂ hu₂ heq
  have hu₁' : u₁ ∈ bdyS S := hu₁
  have hu₂' : u₂ ∈ bdyS S := hu₂
  have hvS : phi S u₁ ∈ S := (mem_bdyS.mp (phi_mem_bdyS hloc hu₁')).1
  obtain ⟨h1eq, h1in, h1out⟩ := phi_in_exit hloc hu₁'
  obtain ⟨h2eq, h2in, h2out⟩ := phi_in_exit hloc hu₂'
  rw [← heq] at h2eq h2in h2out
  have hd : bdyDir S u₁ + 3 = bdyDir S u₂ + 3 :=
    isArcGeTwo_unique_exit (hloc (phi S u₁) hvS) h1in h1out h2in h2out
  rw [h1eq, h2eq, hd]

private lemma phi_ne_self {S : Finset Site} (u : Site) : phi S u ≠ u := by
  intro h
  unfold phi at h
  have h0 : e (bdyDir S u) = (0, 0) := by
    have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    unfold addS at h1 h2
    ext <;> omega
  have hq := QZ_e (bdyDir S u)
  rw [h0] at hq
  unfold QZ at hq; norm_num at hq

private lemma phi_phi_ne_self {S : Finset Site} (hloc : LocallyConn S)
    {u : Site} (hu : u ∈ bdyS S) : phi S (phi S u) ≠ u := by
  intro h
  have hv : phi S u ∈ bdyS S := phi_mem_bdyS hloc hu
  have hvS : phi S u ∈ S := (mem_bdyS.mp hv).1
  have hsp := bdyDir_spec hloc hv
  obtain ⟨heq, hin, hout⟩ := phi_in_exit hloc hu
  have hdir : bdyDir S (phi S u) = bdyDir S u + 3 := by
    apply e_injective
    have hadd : addS (phi S u) (e (bdyDir S (phi S u))) = addS (phi S u) (e (bdyDir S u + 3)) := by
      calc addS (phi S u) (e (bdyDir S (phi S u))) = phi S (phi S u) := rfl
      _ = u := h
      _ = addS (phi S u) (e (bdyDir S u + 3)) := heq
    have h1 := congrArg Prod.fst hadd; have h2 := congrArg Prod.snd hadd
    unfold addS at h1 h2; dsimp only at h1 h2
    ext <;> omega
  exact isArcGeTwo_entry_ne_exit (hloc (phi S u) hvS) hsp.1 hsp.2 hin hout hdir

/-- Generic finite-bijection orbit existence and single-orbit cycle builder. -/
private lemma iter_mem_of_maps {T : Finset Site} {f : Site → Site}
    (hmap : ∀ x ∈ T, f x ∈ T) : ∀ (k : ℕ) {x : Site}, x ∈ T → f^[k] x ∈ T := by
  intro k
  induction k with
  | zero => intro x hx; exact hx
  | succ k ih => intro x hx; rw [Function.iterate_succ_apply']; exact hmap _ (ih hx)

private lemma iter_cancel_inj {T : Finset Site} {f : Site → Site}
    (hmap : ∀ x ∈ T, f x ∈ T) (hinj : Set.InjOn f (T : Set Site)) :
    ∀ (k : ℕ) {x y : Site}, x ∈ T → y ∈ T → f^[k] x = f^[k] y → x = y := by
  intro k
  induction k with
  | zero => intro x y _ _ h; exact h
  | succ k ih =>
    intro x y hx hy h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
    exact ih hx hy (hinj (iter_mem_of_maps hmap k hx) (iter_mem_of_maps hmap k hy) h)

private lemma exists_min_period {T : Finset Site} {f : Site → Site}
    (hmap : ∀ x ∈ T, f x ∈ T) (hinj : Set.InjOn f (T : Set Site))
    {x : Site} (hx : x ∈ T) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ T.card ∧ f^[p] x = x ∧
      ∀ a b : ℕ, a < p → b < p → f^[a] x = f^[b] x → a = b := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 T.card).filter (fun p => f^[p] x = x)
  have hP_ne : P.Nonempty := by
    have hlt : T.card < (Finset.range (T.card + 1)).card := by simp
    have hmaps : ∀ k ∈ Finset.range (T.card + 1), f^[k] x ∈ T := fun k _ => iter_mem_of_maps hmap k hx
    obtain ⟨i, hi, j, hj, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    rw [Finset.mem_range] at hi hj
    have hsub : ∀ a b : ℕ, a < b → b ≤ T.card → f^[a] x = f^[b] x → b - a ∈ P := by
      intro a b hab hb heq'
      have hba : f^[b - a] x = x := by
        apply iter_cancel_inj hmap hinj a (iter_mem_of_maps hmap (b - a) hx) hx
        rw [← Function.iterate_add_apply, show a + (b - a) = b by omega]
        exact heq'.symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hba⟩
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · exact ⟨j - i, hsub i j hlt' (by omega) heq⟩
    · exact ⟨i - j, hsub j i hgt' (by omega) heq.symm⟩
  let p := P.min' hP_ne
  have hp_mem : p ∈ P := Finset.min'_mem P hP_ne
  have hp_icc := (Finset.mem_filter.mp hp_mem).1
  have hp_fix : f^[p] x = x := (Finset.mem_filter.mp hp_mem).2
  refine ⟨p, (Finset.mem_Icc.mp hp_icc).1, (Finset.mem_Icc.mp hp_icc).2, hp_fix, ?_⟩
  intro a b ha hb heq
  by_contra hne
  have hbad : ∀ u v : ℕ, u < v → v < p → f^[u] x = f^[v] x → False := by
    intro u v huv hv heq'
    have hvu : f^[v - u] x = x := by
      apply iter_cancel_inj hmap hinj u (iter_mem_of_maps hmap (v - u) hx) hx
      rw [← Function.iterate_add_apply, show u + (v - u) = v by omega]
      exact heq'.symm
    have hmem' : v - u ∈ P :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by have := (Finset.mem_Icc.mp hp_icc).2; omega⟩, hvu⟩
    have hle : p ≤ v - u := Finset.min'_le P (v - u) hmem'
    omega
  rcases lt_or_gt_of_ne hne with hlt' | hgt'
  · exact hbad a b hlt' hb heq
  · exact hbad b a hgt' ha heq.symm

private lemma iter_mod_period {f : Site → Site} {x : Site} {p : ℕ}
    (_hp : 0 < p) (hfix : f^[p] x = x) : ∀ m : ℕ, f^[m] x = f^[m % p] x := by
  intro m
  have hmul : ∀ q : ℕ, f^[q * p] x = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show (q + 1) * p = q * p + p by ring, Function.iterate_add_apply, hfix, ih]
  have hdiv : m = m % p + (m / p) * p := by
    have := Nat.div_add_mod m p; linarith [mul_comm p (m / p)]
  conv_lhs => rw [hdiv]
  rw [Function.iterate_add_apply, hmul (m / p)]

/-- Row barrier lemma shared by cases d* = 1 and d* = 0 of Step 7.2. -/
private lemma no_vertex_below_of_row_barrier {S : Finset Site}
    (hconn : ConnS S) (hconv : HorizConvex S)
    {xL xR yS : ℤ} (hle : xL ≤ xR)
    (hstart : (xL, yS) ∈ S)
    (hleft : (xL - 1, yS) ∉ S)
    (hright : (xR + 1, yS) ∉ S)
    (hbelow : ∀ x : ℤ, xL ≤ x → x ≤ xR → (x, yS - 1) ∉ S ∧ (x + 1, yS - 1) ∉ S) :
    (∀ p ∈ S, yS ≤ p.2) ∧ (∀ p ∈ S, p.2 = yS → xL ≤ p.1) := by
  have hrow : ∀ x : ℤ, (x, yS) ∈ S → xL ≤ x ∧ x ≤ xR := by
    intro x hx
    constructor
    · by_contra hlt
      exact hleft (hconv x xL (xL - 1) yS hx hstart (by omega) (by omega))
    · by_contra hgt
      exact hright (hconv xL x (xR + 1) yS hstart hx (by omega) (by omega))
  have hge : ∀ a b : Site, ReachIn S a b → yS ≤ a.2 → yS ≤ b.2 := by
    intro a b hr
    induction hr with
    | refl => intro h; exact h
    | @tail b' c' _ hstep ih =>
      intro ha
      have hb_ge := ih ha
      obtain ⟨hbS, hcS, hunit⟩ := hstep
      obtain ⟨d, hd⟩ := (unitStep_iff_exists_dir b' c').mp hunit
      by_contra hlt
      have hdy : (e d).2 = -1 ∨ (e d).2 = 0 ∨ (e d).2 = 1 := by fin_cases d <;> simp [e]
      have hby : b'.2 = yS := by
        rw [hd] at hlt
        unfold addS at hlt; dsimp only at hlt
        omega
      have hbx : xL ≤ b'.1 ∧ b'.1 ≤ xR := by
        apply hrow
        have hbeq : (b'.1, yS) = b' := by ext <;> [rfl; exact hby.symm]
        rwa [hbeq]
      fin_cases d <;> rw [hd] at hcS hlt <;> unfold addS e at hcS hlt <;> dsimp only at hcS hlt
      · omega
      · omega
      · omega
      · omega
      · have hceq : (b'.1, yS - 1) = (b'.1 + 0, b'.2 + -1) := Prod.ext (by omega) (by omega)
        exact (hbelow b'.1 hbx.1 hbx.2).1 (by rwa [hceq])
      · have hceq : (b'.1 + 1, yS - 1) = (b'.1 + 1, b'.2 + -1) := Prod.ext rfl (by omega)
        exact (hbelow b'.1 hbx.1 hbx.2).2 (by rwa [hceq])
  refine ⟨fun p hp => hge (xL, yS) p (hconn _ hstart p hp) le_rfl, ?_⟩
  intro p hp hpy
  have hpeq : (p.1, yS) = p := Prod.ext rfl hpy.symm
  exact (hrow p.1 (by rwa [hpeq])).1

/-- Step 7.2: Every closed orbit O of φ on ∂S contains the global lex-min of S. -/
private lemma orbit_contains_global_lexMin {S : Finset Site}
    (hconn : ConnS S) (hconv : HorizConvex S) (hloc : LocallyConn S)
    {O : Finset Site} (hO_ne : O.Nonempty) (hO_sub : O ⊆ bdyS S)
    (hO_fwd : ∀ u ∈ O, phi S u ∈ O)
    (hO_bwd : ∀ u ∈ O, ∃ w ∈ O, phi S w = u)
    {uMin : Site} (huMin : uMin ∈ S) (huMin_min : ∀ v ∈ S, v ≠ uMin → lexLt uMin v) :
    uMin ∈ O := by
  classical
  obtain ⟨u, huO, humin⟩ := exists_lexMin hO_ne
  have huB : u ∈ bdyS S := hO_sub huO
  have huS : u ∈ S := (mem_bdyS.mp huB).1
  have hu_ge : ∀ w ∈ O, u.2 ≤ w.2 := by
    intro w hw
    by_cases heq : w = u
    · rw [heq]
    · rcases humin w hw heq with hlt | ⟨heq', _⟩ <;> omega
  have hu_outO : phi S u ∈ O := hO_fwd u huO
  have hu_out_lt : lexLt u (phi S u) := humin (phi S u) hu_outO (phi_ne_self u)
  have hd012 : bdyDir S u = 0 ∨ bdyDir S u = 1 ∨ bdyDir S u = 2 := (lexLt_e_iff u (bdyDir S u)).mp hu_out_lt
  obtain ⟨wIn, hwInO, hwIn_phi⟩ := hO_bwd u huO
  have hwInB : wIn ∈ bdyS S := hO_sub hwInO
  obtain ⟨hwIn_eq, hwIn_in, hwIn_out⟩ := phi_in_exit hloc hwInB
  rw [hwIn_phi] at hwIn_eq hwIn_in hwIn_out
  have hwIn_ne : wIn ≠ u := by
    intro h; subst h; exact phi_ne_self _ hwIn_phi
  have ha012 : bdyDir S wIn + 3 = 0 ∨ bdyDir S wIn + 3 = 1 ∨ bdyDir S wIn + 3 = 2 := by
    have hlt : lexLt u wIn := humin wIn hwInO hwIn_ne
    rw [hwIn_eq] at hlt
    exact (lexLt_e_iff u (bdyDir S wIn + 3)).mp hlt
  have hsp_u := bdyDir_spec hloc huB
  have hda : bdyDir S u ≠ bdyDir S wIn + 3 :=
    isArcGeTwo_entry_ne_exit (hloc u huS) hsp_u.1 hsp_u.2 hwIn_in hwIn_out
  have hu_eq_uMin : u = uMin := by
    rcases hd012 with hd0 | hd1 | hd2
    · -- Case d = 0: walk right along row u.2 to maximal t, apply row barrier.
      have h5out : addS u (e 5) ∉ S := by
        have := hsp_u.2; rw [hd0, show (0 : ZMod 6) - 1 = 5 from rfl] at this; exact this
      have h0in : addS u (e 0) ∈ S := by
        have := hsp_u.1; rw [hd0] at this; exact this
      have h34out : addS u (e 3) ∉ S ∧ addS u (e 4) ∉ S := by
        have ha12 : bdyDir S wIn + 3 = 1 ∨ bdyDir S wIn + 3 = 2 := by
          rcases ha012 with h | h | h
          · exact absurd (by rw [hd0, h]) hda
          · exact Or.inl h
          · exact Or.inr h
        have hsp0 : addS u (e 0) ∈ S ∧ addS u (e (0 - 1)) ∉ S :=
          ⟨h0in, by rwa [show (0 : ZMod 6) - 1 = 5 from rfl]⟩
        rcases ha12 with ha1 | ha2
        · have h2out : addS u (e 2) ∉ S := by
            rw [ha1, show (1 : ZMod 6) + 1 = 2 from rfl] at hwIn_out; exact hwIn_out
          have h3out : addS u (e 3) ∉ S :=
            isArcGeTwo_step_false (hloc u huS) hsp0.1 hsp0.2 (by decide) (by rwa [show (3 : ZMod 6) - 1 = 2 from rfl])
          have h4out : addS u (e 4) ∉ S :=
            isArcGeTwo_step_false (hloc u huS) hsp0.1 hsp0.2 (by decide) (by rwa [show (4 : ZMod 6) - 1 = 3 from rfl])
          exact ⟨h3out, h4out⟩
        · have h3out : addS u (e 3) ∉ S := by
            rw [ha2, show (2 : ZMod 6) + 1 = 3 from rfl] at hwIn_out; exact hwIn_out
          have h4out : addS u (e 4) ∉ S :=
            isArcGeTwo_step_false (hloc u huS) hsp0.1 hsp0.2 (by decide) (by rwa [show (4 : ZMod 6) - 1 = 3 from rfl])
          exact ⟨h3out, h4out⟩
      -- Maximal right run t on row u.2 starting at u
      let good (j : ℕ) : Prop :=
        (∀ i ≤ j, (u.1 + (i : ℤ), u.2) ∈ O) ∧
        (∀ i < j, bdyDir S (u.1 + (i : ℤ), u.2) = 0)
      let G : Finset ℕ := (Finset.range (S.card + 1)).filter (fun j => good j)
      have h1_good : good 1 := by
        refine ⟨?_, ?_⟩
        · intro i hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · simpa using huO
          · have hphi0 : phi S u = (u.1 + 1, u.2) := by
              unfold phi; rw [hd0]; unfold addS e; ext <;> simp
            simpa [← hphi0] using hu_outO
        · intro i hi
          have : i = 0 := by omega
          subst this; simpa using hd0
      have hG_ne : G.Nonempty := by
        refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, h1_good⟩⟩
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u, huS⟩
        omega
      let t := G.max' hG_ne
      have ht_mem : t ∈ G := Finset.max'_mem G hG_ne
      have ht_good : good t := (Finset.mem_filter.mp ht_mem).2
      have ht_ge1 : 1 ≤ t := Finset.le_max' G 1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.card_pos.mpr ⟨u, huS⟩; omega), h1_good⟩)
      have ht_lt : t < S.card := by
        let pts := (Finset.range (t + 1)).image (fun i : ℕ => (u.1 + (i : ℤ), u.2))
        have hsub : pts ⊆ S := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
          exact (mem_bdyS.mp (hO_sub (ht_good.1 i (by rw [Finset.mem_range] at hi; omega)))).1
        have hcard : pts.card = t + 1 := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro a b h; have := congrArg Prod.fst h; dsimp only at this; omega
        have := Finset.card_le_card hsub
        omega
      let wt : Site := (u.1 + (t : ℤ), u.2)
      have hwtO : wt ∈ O := ht_good.1 t le_rfl
      have hwtB : wt ∈ bdyS S := hO_sub hwtO
      have hwtS : wt ∈ S := (mem_bdyS.mp hwtB).1
      have hwt4 : addS wt (e 4) ∉ S := by
        have hprevO := ht_good.1 (t - 1) (by omega)
        have hprevDir := ht_good.2 (t - 1) (by omega)
        have hsp := bdyDir_spec hloc (hO_sub hprevO)
        rw [hprevDir, show (0 : ZMod 6) - 1 = 5 from rfl] at hsp
        have heq : addS (u.1 + ((t - 1 : ℕ) : ℤ), u.2) (e 5) = addS wt (e 4) := by
          unfold wt addS e; dsimp only; exact Prod.ext (by omega) (by omega)
        rw [← heq]; exact hsp.2
      have hwt5 : addS wt (e 5) ∉ S := by
        intro h5in
        have hdir5 : bdyDir S wt = 5 :=
          bdyDir_eq_of hloc hwtS h5in (by rwa [show (5 : ZMod 6) - 1 = 4 from rfl])
        have hphi5 : phi S wt ∈ O := hO_fwd wt hwtO
        have hge := hu_ge (phi S wt) hphi5
        unfold phi at hge; rw [hdir5] at hge; unfold wt addS e at hge; dsimp only at hge; omega
      have hwt0 : addS wt (e 0) ∉ S := by
        intro h0in
        have hdir0 : bdyDir S wt = 0 :=
          bdyDir_eq_of hloc hwtS h0in (by rwa [show (0 : ZMod 6) - 1 = 5 from rfl])
        have hphi0 : phi S wt ∈ O := hO_fwd wt hwtO
        have ht1_good : good (t + 1) := by
          refine ⟨?_, ?_⟩
          · intro i hi
            by_cases hle' : i ≤ t
            · exact ht_good.1 i hle'
            · have hi_eq : i = t + 1 := by omega
              subst hi_eq
              have heq : phi S wt = (u.1 + ((t + 1 : ℕ) : ℤ), u.2) := by
                unfold phi; rw [hdir0]; unfold wt addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              rw [← heq]; exact hphi0
          · intro i hi
            by_cases hlt' : i < t
            · exact ht_good.2 i hlt'
            · have hi_eq : i = t := by omega
              subst hi_eq; exact hdir0
        have ht1_mem : t + 1 ∈ G :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht1_good⟩
        have := Finset.le_max' G (t + 1) ht1_mem
        omega
      have hbar := no_vertex_below_of_row_barrier hconn hconv (xL := u.1) (xR := u.1 + (t : ℤ)) (yS := u.2)
        (by omega) (by simpa using huS)
        (by have : (u.1 - 1, u.2) = addS u (e 3) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
            rw [this]; exact h34out.1)
        (by have : (u.1 + (t : ℤ) + 1, u.2) = addS wt (e 0) := by unfold wt addS e; dsimp only; exact Prod.ext (by omega) (by omega)
            rw [this]; exact hwt0)
        (by
          intro x hx1 hx2
          let j : ℕ := (x - u.1).toNat
          have hjx : u.1 + (j : ℤ) = x := by omega
          have hjt : j ≤ t := by omega
          constructor
          · by_cases hj0 : j = 0
            · have : (x, u.2 - 1) = addS u (e 4) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              rw [this]; exact h34out.2
            · have hprevO := ht_good.1 (j - 1) (by omega)
              have hprevDir := ht_good.2 (j - 1) (by omega)
              have hsp := bdyDir_spec hloc (hO_sub hprevO)
              rw [hprevDir, show (0 : ZMod 6) - 1 = 5 from rfl] at hsp
              have : (x, u.2 - 1) = addS (u.1 + ((j - 1 : ℕ) : ℤ), u.2) (e 5) := by
                unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              rw [this]; exact hsp.2
          · by_cases hjeq : j = t
            · have : (x + 1, u.2 - 1) = addS wt (e 5) := by unfold wt addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              rw [this]; exact hwt5
            · have hjO := ht_good.1 j (by omega)
              have hjDir := ht_good.2 j (by omega)
              have hsp := bdyDir_spec hloc (hO_sub hjO)
              rw [hjDir, show (0 : ZMod 6) - 1 = 5 from rfl] at hsp
              have : (x + 1, u.2 - 1) = addS (u.1 + (j : ℤ), u.2) (e 5) := by
                unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              rw [this]; exact hsp.2)
      by_contra hne
      rcases huMin_min u huS hne with hlt | ⟨heq, hlt⟩
      · have := hbar.1 uMin huMin; omega
      · have := hbar.2 uMin huMin heq; omega
    · -- Case d = 1: single-vertex row barrier at u!
      have h0out : addS u (e 0) ∉ S := by
        have := hsp_u.2; rw [hd1, show (1 : ZMod 6) - 1 = 0 from rfl] at this; exact this
      have h1in : addS u (e 1) ∈ S := by
        have := hsp_u.1; rw [hd1] at this; exact this
      have ha2 : bdyDir S wIn + 3 = 2 := by
        rcases ha012 with h | h | h
        · exfalso; rw [h] at hwIn_in; exact h0out hwIn_in
        · exact absurd (by rw [hd1, h]) hda
        · exact h
      have h3out : addS u (e 3) ∉ S := by
        rw [ha2, show (2 : ZMod 6) + 1 = 3 from rfl] at hwIn_out; exact hwIn_out
      have hsp1 : addS u (e 1) ∈ S ∧ addS u (e (1 - 1)) ∉ S :=
        ⟨h1in, by rwa [show (1 : ZMod 6) - 1 = 0 from rfl]⟩
      have h4out : addS u (e 4) ∉ S :=
        isArcGeTwo_step_false (hloc u huS) hsp1.1 hsp1.2 (by decide) (by rwa [show (4 : ZMod 6) - 1 = 3 from rfl])
      have h5out : addS u (e 5) ∉ S :=
        isArcGeTwo_step_false (hloc u huS) hsp1.1 hsp1.2 (by decide) (by rwa [show (5 : ZMod 6) - 1 = 4 from rfl])
      have hbar := no_vertex_below_of_row_barrier hconn hconv (xL := u.1) (xR := u.1) (yS := u.2)
        le_rfl (by simpa using huS)
        (by have : (u.1 - 1, u.2) = addS u (e 3) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
            rw [this]; exact h3out)
        (by have : (u.1 + 1, u.2) = addS u (e 0) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
            rw [this]; exact h0out)
        (by
          intro x hx1 hx2
          exact ⟨by have : (x, u.2 - 1) = addS u (e 4) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
                    rw [this]; exact h4out,
                 by have : (x + 1, u.2 - 1) = addS u (e 5) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
                    rw [this]; exact h5out⟩)
      by_contra hne
      rcases huMin_min u huS hne with hlt | ⟨heq, hlt⟩
      · have := hbar.1 uMin huMin; omega
      · have := hbar.2 uMin huMin heq; omega
    · -- Case d = 2: impossible (infinite rightward ray on row u.2 contradicts finiteness of S)!
      exfalso
      have h1out : addS u (e 1) ∉ S := by
        have := hsp_u.2; rw [hd2, show (2 : ZMod 6) - 1 = 1 from rfl] at this; exact this
      have h2in : addS u (e 2) ∈ S := by
        have := hsp_u.1; rw [hd2] at this; exact this
      have ha0 : bdyDir S wIn + 3 = 0 := by
        rcases ha012 with h | h | h
        · exact h
        · exfalso; rw [h] at hwIn_in; exact h1out hwIn_in
        · exact absurd (by rw [hd2, h]) hda
      have hrow_above : ∀ t : ℕ, (u.1 + (t : ℤ), u.2 + 1) ∉ S := by
        intro t ht
        have hleft : (u.1 - 1, u.2 + 1) ∈ S := by
          have : (u.1 - 1, u.2 + 1) = addS u (e 2) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
          rw [this]; exact h2in
        have hmid : (u.1, u.2 + 1) ∈ S :=
          hconv (u.1 - 1) (u.1 + (t : ℤ)) u.1 (u.2 + 1) hleft ht (by omega) (by omega)
        have : addS u (e 1) = (u.1, u.2 + 1) := by unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
        exact h1out (by rwa [this])
      have hray : ∀ t : ℕ, (u.1 + ((t + 1 : ℕ) : ℤ), u.2) ∈ O ∧
          bdyDir S (u.1 + ((t + 1 : ℕ) : ℤ), u.2) = 3 := by
        intro t
        induction t with
        | zero =>
          have hw1 : wIn = (u.1 + 1, u.2) := by
            rw [hwIn_eq, ha0]; unfold addS e; dsimp only; exact Prod.ext (by omega) (by omega)
          have hdir3 : bdyDir S wIn = 3 := by
            calc bdyDir S wIn = (bdyDir S wIn + 3) + 3 := by ring_nf; rw [show (6 : ZMod 6) = 0 from rfl]; simp
            _ = 0 + 3 := by rw [ha0]
            _ = 3 := by simp
          rw [show u.1 + ((0 + 1 : ℕ) : ℤ) = u.1 + 1 by omega, ← hw1]
          exact ⟨hwInO, hdir3⟩
        | succ t ih =>
          set vt : Site := (u.1 + ((t + 1 : ℕ) : ℤ), u.2)
          obtain ⟨hvtO, hvtDir⟩ := ih
          obtain ⟨w, hwO, hw_phi⟩ := hO_bwd vt hvtO
          have hwB : w ∈ bdyS S := hO_sub hwO
          obtain ⟨hw_eq, hw_in, hw_out⟩ := phi_in_exit hloc hwB
          rw [hw_phi] at hw_eq hw_in hw_out
          have hvtB : vt ∈ bdyS S := hO_sub hvtO
          have hvtS : vt ∈ S := (mem_bdyS.mp hvtB).1
          have hvt_sp := bdyDir_spec hloc hvtB
          have hb_ne3 : bdyDir S w + 3 ≠ 3 := by
            have hne := (isArcGeTwo_entry_ne_exit (hloc vt hvtS) hvt_sp.1 hvt_sp.2 hw_in hw_out).symm
            rwa [hvtDir] at hne
          have hb0 : bdyDir S w + 3 = 0 := by
            have hw_ge : u.2 ≤ w.2 := hu_ge w hwO
            rcases zmod6_cases (bdyDir S w + 3) with hb | hb | hb | hb | hb | hb
            · exact hb
            · exfalso
              rw [hb] at hw_in
              have : (u.1 + ((t + 1 : ℕ) : ℤ), u.2 + 1) = addS vt (e 1) := by unfold vt addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              exact hrow_above (t + 1) (by rwa [this])
            · exfalso
              rw [hb] at hw_in
              have : (u.1 + (t : ℤ), u.2 + 1) = addS vt (e 2) := by unfold vt addS e; dsimp only; exact Prod.ext (by omega) (by omega)
              exact hrow_above t (by rwa [this])
            · exact absurd hb hb_ne3
            · exfalso
              rw [hw_eq, hb] at hw_ge; unfold vt addS e at hw_ge; dsimp only at hw_ge; omega
            · exfalso
              rw [hw_eq, hb] at hw_ge; unfold vt addS e at hw_ge; dsimp only at hw_ge; omega
          have hw_val : w = (u.1 + ((t + 1 + 1 : ℕ) : ℤ), u.2) := by
            rw [hw_eq, hb0]; unfold vt addS e; ext <;> dsimp only <;> omega
          have hdir3 : bdyDir S w = 3 := by
            calc bdyDir S w = (bdyDir S w + 3) + 3 := by ring_nf; rw [show (6 : ZMod 6) = 0 from rfl]; simp
            _ = 0 + 3 := by rw [hb0]
            _ = 3 := by simp
          rw [← hw_val]; exact ⟨hwO, hdir3⟩
      let pts := (Finset.range (S.card + 1)).image (fun t : ℕ => (u.1 + ((t + 1 : ℕ) : ℤ), u.2))
      have hsub : pts ⊆ S := by
        intro p hp
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
        exact (mem_bdyS.mp (hO_sub (hray t).1)).1
      have hcard : pts.card = S.card + 1 := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b h; have := congrArg Prod.fst h; dsimp only at this; omega
      have := Finset.card_le_card hsub
      omega
  rw [← hu_eq_uMin]; exact huO

/-- Step 7.3: Single-Orbit Boundary Cycle Theorem. -/
private lemma boundary_hasHamCycle {S : Finset Site}
    (hS_ne : S.Nonempty) (hconn : ConnS S) (hconv : HorizConvex S) (hloc : LocallyConn S) :
    ∃ C : List Site, IsHamCycle (bdyS S) C ∧
      ∀ u ∈ bdyS S, ∃ (i : ℕ) (hi : i < C.length),
        C[i] = u ∧ (C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega))) = phi S u := by
  classical
  obtain ⟨uMin, huMinS, huMin_min⟩ := exists_lexMin hS_ne
  have huMinB : uMin ∈ bdyS S := by
    rw [mem_bdyS]
    refine ⟨huMinS, 4, ?_⟩
    intro h4
    have hne : addS uMin (e 4) ≠ uMin := by
      intro h; have := congrArg Prod.snd h; unfold addS e at this; dsimp only at this; omega
    rcases huMin_min _ h4 hne with hlt | ⟨heq, _⟩ <;> unfold addS e at * <;> dsimp only at * <;> omega
  have hmap : ∀ u ∈ bdyS S, phi S u ∈ bdyS S := fun _ hu => phi_mem_bdyS hloc hu
  have hinj : Set.InjOn (phi S) (bdyS S : Set Site) := phi_injOn hloc
  obtain ⟨p₀, hp₀_ge1, hp₀_le, hp₀_fix, hp₀_inj⟩ := exists_min_period hmap hinj huMinB
  let O₀ : Finset Site := (Finset.range p₀).image (fun k => (phi S)^[k] uMin)
  have hO₀_eq : O₀ = bdyS S := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact iter_mem_of_maps hmap k huMinB
    · intro y hy
      obtain ⟨py, hpy_ge1, _, hpy_fix, _⟩ := exists_min_period hmap hinj hy
      let Oy : Finset Site := (Finset.range py).image (fun k => (phi S)^[k] y)
      have hOy_ne : Oy.Nonempty := ⟨y, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
      have hOy_sub : Oy ⊆ bdyS S := by
        intro z hz
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
        exact iter_mem_of_maps hmap k hy
      have hOy_fwd : ∀ z ∈ Oy, phi S z ∈ Oy := by
        intro z hz
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_range] at hk
        by_cases hlt : k + 1 < py
        · exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr hlt, Function.iterate_succ_apply' (phi S) k y⟩
        · have heq : k + 1 = py := by omega
          refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
          rw [← Function.iterate_succ_apply' (phi S), Nat.succ_eq_add_one, heq, hpy_fix]; rfl
      have hOy_bwd : ∀ z ∈ Oy, ∃ w ∈ Oy, phi S w = z := by
        intro z hz
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_range] at hk
        by_cases hk0 : k = 0
        · subst hk0
          refine ⟨(phi S)^[py - 1] y, Finset.mem_image.mpr ⟨py - 1, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
          rw [← Function.iterate_succ_apply' (phi S), Nat.succ_eq_add_one, show py - 1 + 1 = py by omega, hpy_fix]; rfl
        · refine ⟨(phi S)^[k - 1] y, Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
          rw [← Function.iterate_succ_apply' (phi S), Nat.succ_eq_add_one, show k - 1 + 1 = k by omega]
      have huMin_in : uMin ∈ Oy :=
        orbit_contains_global_lexMin hconn hconv hloc hOy_ne hOy_sub hOy_fwd hOy_bwd huMinS huMin_min
      obtain ⟨k, hk, hk_eq⟩ := Finset.mem_image.mp huMin_in
      rw [Finset.mem_range] at hk
      have hy_eq : (phi S)^[py - k] uMin = y := by
        rw [← hk_eq, ← Function.iterate_add_apply, show py - k + k = py by omega, hpy_fix]
      rw [← hy_eq, iter_mod_period (by omega) hp₀_fix]
      exact Finset.mem_image.mpr ⟨(py - k) % p₀, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩
  have hp₀_ge3 : 3 ≤ p₀ := by
    by_contra hlt
    have h12 : p₀ = 1 ∨ p₀ = 2 := by omega
    rcases h12 with h1 | h2
    · rw [h1, Function.iterate_one] at hp₀_fix
      exact phi_ne_self uMin hp₀_fix
    · rw [h2, Function.iterate_succ_apply', Function.iterate_one] at hp₀_fix
      exact phi_phi_ne_self hloc huMinB hp₀_fix
  let C : List Site := List.ofFn (fun i : Fin p₀ => (phi S)^[i.val] uMin)
  have hClen : C.length = p₀ := List.length_ofFn
  have hC_step : ∀ (i : ℕ) (hi : i < C.length),
      (C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega))) = phi S C[i] := by
    intro i hi
    simp only [C, List.getElem_ofFn, hClen]
    rw [← Function.iterate_succ_apply' (phi S), iter_mod_period (by omega) hp₀_fix (i + 1)]
  refine ⟨C, ⟨by omega, ?_, ?_, ?_⟩, ?_⟩
  · unfold C
    rw [List.nodup_ofFn]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    exact Fin.ext (hp₀_inj i j hi hj heq)
  · intro x
    rw [← hO₀_eq]
    unfold C O₀
    rw [List.mem_ofFn, Finset.mem_image]
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩; exact ⟨k, Finset.mem_range.mpr hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, Finset.mem_range.mp hk⟩, rfl⟩
  · intro i hi
    rw [hC_step i hi]
    exact unitStep_addS_e C[i] (bdyDir S C[i])
  · intro u hu
    rw [← hO₀_eq] at hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_range] at hk
    refine ⟨k, by omega, by simp [C], ?_⟩
    rw [hC_step k (by omega)]
    simp [C]

/-! ### Section 8: Universal Layer-Merge Lemmas (including Inner D_13 Splice) -/

private def D13Offsets : List Site :=
  [(0, 0),
   (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1),
   (1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]

private def D13 (v : Site) : Finset Site :=
  (D13Offsets.map (addS v)).toFinset

private lemma addS_inj (v : Site) : Function.Injective (addS v) := by
  intro a b h
  have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
  unfold addS at h1 h2; dsimp only at h1 h2
  ext <;> omega

private lemma D13_card (v : Site) : (D13 v).card = 13 := by
  unfold D13
  rw [List.toFinset_card_of_nodup]
  · simp [D13Offsets]
  · exact List.Nodup.map (addS_inj v) (by decide)

private lemma mem_D13_iff (v p : Site) :
    p ∈ D13 v ↔ p = v ∨ (∃ d : ZMod 6, p = addS v (e d)) ∨
      (∃ d : ZMod 6, p = addS v (addS (e d) (e (d + 1)))) := by
  unfold D13
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp only [D13Offsets, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; unfold addS; ext <;> simp
    · right; left; exact ⟨0, rfl⟩
    · right; left; exact ⟨1, rfl⟩
    · right; left; exact ⟨2, rfl⟩
    · right; left; exact ⟨3, rfl⟩
    · right; left; exact ⟨4, rfl⟩
    · right; left; exact ⟨5, rfl⟩
    · right; right; exact ⟨0, rfl⟩
    · right; right; exact ⟨1, rfl⟩
    · right; right; exact ⟨2, rfl⟩
    · right; right; exact ⟨3, rfl⟩
    · right; right; exact ⟨4, rfl⟩
    · right; right; exact ⟨5, rfl⟩
  · rintro (rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩)
    · exact ⟨(0, 0), by simp [D13Offsets], by unfold addS; ext <;> simp⟩
    · fin_cases d <;> exact ⟨_, by simp [D13Offsets, e], rfl⟩
    · rw [← rotS_e]; fin_cases d <;> exact ⟨_, by simp [D13Offsets, addS, rotS, e], rfl⟩

private lemma addS_assoc (a b c : Site) : addS (addS a b) c = addS a (addS b c) := by
  unfold addS; ext <;> dsimp only <;> ring

private lemma zmod6_sub_one_eq_add_five (d : ZMod 6) : d - 1 = d + 5 := by
  fin_cases d <;> rfl

private lemma tip_add_e3 (v : Site) (d : ZMod 6) :
    addS (addS v (addS (e d) (e (d + 1)))) (e (d + 3)) = addS v (e (d + 1)) := by
  rw [addS_assoc]; congr 1; fin_cases d <;> rfl

private lemma tip_add_e4 (v : Site) (d : ZMod 6) :
    addS (addS v (addS (e d) (e (d + 1)))) (e (d + 4)) = addS v (e d) := by
  rw [addS_assoc]; congr 1; fin_cases d <;> rfl

private lemma tip_add_e2 (v : Site) (d : ZMod 6) :
    addS (addS v (addS (e d) (e (d + 1)))) (e (d + 2)) = addS v (addS (e (d + 1)) (e (d + 1))) := by
  rw [addS_assoc]; congr 1; fin_cases d <;> rfl

private lemma tip_add_e5 (v : Site) (d : ZMod 6) :
    addS (addS v (addS (e d) (e (d + 1)))) (e (d + 5)) = addS v (addS (e d) (e d)) := by
  rw [addS_assoc]; congr 1; fin_cases d <;> rfl

/-- Step 8.1: |Int(S)| = 1 and S ≠ D_13(v) ⇒ triangle-splice v into C_out. -/
private lemma splice_K1 {S : Finset Site} {v : Site}
    (hconn : ConnS S) (hconv : HorizConvex S) (hloc : LocallyConn S)
    (hint : intS S = {v}) (hneD : S ≠ D13 v) : HasHamCycle S := by
  have hvI : v ∈ intS S := by rw [hint]; simp
  have hvS : v ∈ S := (mem_intS.mp hvI).1
  have hv_nb : ∀ d : ZMod 6, addS v (e d) ∈ S := (mem_intS.mp hvI).2
  have hS_ne : S.Nonempty := ⟨v, hvS⟩
  obtain ⟨C, hC, hC_edge⟩ := boundary_hasHamCycle hS_ne hconn hconv hloc
  have hunion : bdyS S ∪ {v} = S := by
    rw [← hint]; unfold bdyS
    exact Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hdisj : Disjoint (bdyS S) {v} := by
    rw [← hint]; exact disjoint_sdiff_self_left
  by_cases hmiss : ∃ d : ZMod 6, addS v (addS (e d) (e (d + 1))) ∉ S
  · obtain ⟨d, hd_out⟩ := hmiss
    let u := addS v (e d)
    have huS : u ∈ S := hv_nb d
    have hu_ne : u ≠ v := by
      intro h; have := congrArg Prod.fst h; have := congrArg Prod.snd h
      fin_cases d <;> unfold u addS e at * <;> dsimp only at * <;> omega
    have huB : u ∈ bdyS S := by
      rw [bdyS, Finset.mem_sdiff, hint, Finset.mem_singleton]
      exact ⟨huS, hu_ne⟩
    have hu_in : addS u (e (d + 2)) ∈ S := by
      have heq : addS u (e (d + 2)) = addS v (e (d + 1)) := by
        unfold u; rw [addS_addS_e, e_add_two_eq]
      rw [heq]; exact hv_nb (d + 1)
    have hu_out : addS u (e (d + 2 - 1)) ∉ S := by
      have heq : addS u (e (d + 2 - 1)) = addS v (addS (e d) (e (d + 1))) := by
        unfold u; rw [show d + 2 - 1 = d + 1 by ring, addS_addS_e]
      rw [heq]; exact hd_out
    have hdir : bdyDir S u = d + 2 := bdyDir_eq_of hloc huS hu_in hu_out
    have hphi_u : phi S u = addS v (e (d + 1)) := by
      unfold phi; rw [hdir]; unfold u; rw [addS_addS_e, e_add_two_eq]
    obtain ⟨idx, hidx, hCidx, hCnext⟩ := hC_edge u huB
    rw [← hunion]
    apply splice_path_into_cycle hdisj hC idx hidx (P := [v])
      (by simp) (by simp) (by intro x; simp) (by intro j hj; simp at hj)
    · rw [hCidx]; exact unitStep_symm (unitStep_addS_e v d)
    · rw [hCnext, hphi_u]; exact unitStep_addS_e v (d + 1)
  · -- All 6 tips a_d lie in S ⇒ S = D13 v, contradiction!
    exfalso
    apply hneD
    have hall_tips : ∀ d : ZMod 6, addS v (addS (e d) (e (d + 1))) ∈ S := by
      intro d; by_contra h; exact hmiss ⟨d, h⟩
    have hD_sub : D13 v ⊆ S := by
      intro p hp
      rcases (mem_D13_iff v p).mp hp with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact hvS
      · exact hv_nb d
      · exact hall_tips d
    have hno_2e : ∀ d : ZMod 6, addS v (addS (e d) (e d)) ∉ S := by
      intro d h2in
      let ud := addS v (e d)
      have hud_ne : ud ≠ v := by
        intro h; fin_cases d <;> unfold ud addS e at h <;>
          [have := congrArg Prod.fst h; have := congrArg Prod.snd h; have := congrArg Prod.fst h;
           have := congrArg Prod.fst h; have := congrArg Prod.snd h; have := congrArg Prod.fst h] <;>
          dsimp only at this <;> omega
      have hud_notI : ud ∉ intS S := by rw [hint, Finset.mem_singleton]; exact hud_ne
      apply hud_notI
      rw [mem_intS]
      refine ⟨hv_nb d, fun c => ?_⟩
      rcases zmod6_shift_cases c d with hc | hc | hc | hc | hc | hc
      · rw [hc, show addS ud (e d) = addS v (addS (e d) (e d)) from addS_addS_e v d d]; exact h2in
      · rw [hc, show addS ud (e (d + 1)) = addS v (addS (e d) (e (d + 1))) from addS_addS_e v d (d + 1)]
        exact hall_tips d
      · rw [hc]
        have : addS ud (e (d + 2)) = addS v (e (d + 1)) := by unfold ud; rw [addS_addS_e, e_add_two_eq]
        rw [this]; exact hv_nb (d + 1)
      · rw [hc]
        have : addS ud (e (d + 3)) = v := e_add_three_cancel v d
        rw [this]; exact hvS
      · rw [hc]
        have : addS ud (e (d + 4)) = addS v (e (d - 1)) := by unfold ud; rw [addS_addS_e, e_add_four_eq_sub_one]
        rw [this]; exact hv_nb (d - 1)
      · rw [hc]
        have : addS ud (e (d + 5)) = addS v (addS (e (d - 1)) (e (d - 1 + 1))) := by
          unfold ud; rw [addS_addS_e, sub_add_cancel]
          congr 1; fin_cases d <;> rfl
        rw [this]; exact hall_tips (d - 1)
    have hclosed : ∀ x ∈ D13 v, ∀ y ∈ S, unitStep x y → y ∈ D13 v := by
      intro x hx y hy hstep
      obtain ⟨c, rfl⟩ := (unitStep_iff_exists_dir x y).mp hstep
      rcases (mem_D13_iff v x).mp hx with hx0 | ⟨d, hxd⟩ | ⟨d, hxd⟩
      · rw [hx0]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inl ⟨c, rfl⟩))
      · rw [hxd] at hy ⊢
        rcases zmod6_shift_cases c d with hc | hc | hc | hc | hc | hc
        · exfalso; rw [hc, addS_addS_e] at hy; exact hno_2e d hy
        · rw [hc, addS_addS_e]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inr ⟨d, rfl⟩))
        · rw [hc, addS_addS_e, e_add_two_eq]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inl ⟨d + 1, rfl⟩))
        · rw [hc, e_add_three_cancel]; exact (mem_D13_iff v _).mpr (Or.inl rfl)
        · rw [hc, addS_addS_e, e_add_four_eq_sub_one]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inl ⟨d - 1, rfl⟩))
        · rw [hc]
          have : addS (addS v (e d)) (e (d + 5)) = addS v (addS (e (d - 1)) (e (d - 1 + 1))) := by
            rw [addS_addS_e, sub_add_cancel]; congr 1; fin_cases d <;> rfl
          rw [this]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inr ⟨d - 1, rfl⟩))
      · rw [hxd] at hy ⊢
        let ad := addS v (addS (e d) (e (d + 1)))
        have hadS : ad ∈ S := hall_tips d
        have h3in : addS ad (e (d + 3)) ∈ S := by rw [tip_add_e3]; exact hv_nb (d + 1)
        have h2out : addS ad (e (d + 2)) ∉ S := by rw [tip_add_e2]; exact hno_2e (d + 1)
        have h5out : addS ad (e (d + 5)) ∉ S := by rw [tip_add_e5]; exact hno_2e d
        have hsp : addS ad (e (d + 3)) ∈ S ∧ addS ad (e (d + 3 - 1)) ∉ S :=
          ⟨h3in, by rwa [show d + 3 - 1 = d + 2 by ring]⟩
        have h0out : addS ad (e d) ∉ S :=
          isArcGeTwo_step_false (hloc ad hadS) hsp.1 hsp.2
            (by intro h
                have h30 : (3 : ZMod 6) = 0 := by linear_combination -h
                exact absurd (congrArg (@ZMod.val 6) h30) (by decide))
            (by rwa [zmod6_sub_one_eq_add_five])
        have h1out : addS ad (e (d + 1)) ∉ S :=
          isArcGeTwo_step_false (hloc ad hadS) hsp.1 hsp.2
            (by intro h
                have h20 : (2 : ZMod 6) = 0 := by linear_combination -h
                exact absurd (congrArg (@ZMod.val 6) h20) (by decide))
            (by rwa [add_sub_cancel_right])
        rcases zmod6_shift_cases c d with hc | hc | hc | hc | hc | hc
        · rw [hc] at hy; exact absurd hy h0out
        · rw [hc] at hy; exact absurd hy h1out
        · rw [hc] at hy; exact absurd hy h2out
        · rw [hc, tip_add_e3]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inl ⟨d + 1, rfl⟩))
        · rw [hc, tip_add_e4]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inl ⟨d, rfl⟩))
        · rw [hc] at hy; exact absurd hy h5out
    apply Finset.Subset.antisymm _ hD_sub
    intro y hy
    have hreach := hconn v hvS y hy
    have hvD : v ∈ D13 v := (mem_D13_iff v v).mpr (Or.inl rfl)
    induction hreach with
    | refl => exact hvD
    | tail _ hstep ih => exact hclosed _ (ih hstep.1) _ hstep.2.1 hstep.2.2

/-- Step 8.2: Universal Rhombus-Bridge Lemma. -/
private lemma rhombus_bridge {S : Finset Site} (hloc : LocallyConn S)
    {v₀ v₁ : Site} {d : ZMod 6}
    (hv₀ : v₀ ∈ intS S) (hv₁ : v₁ ∈ intS S)
    (heq : v₁ = addS v₀ (e d))
    (hu₂_out : addS v₀ (e (d - 1)) ∉ intS S) :
    ∃ u ∈ bdyS S, unitStep u v₀ ∧ unitStep v₁ (phi S u) := by
  let u₁ := addS v₀ (e (d - 2))
  let u₂ := addS v₀ (e (d - 1))
  let u₃ := addS v₁ (e (d - 1))
  have hv₀_nb := (mem_intS.mp hv₀).2
  have hv₁_nb := (mem_intS.mp hv₁).2
  have hu₁S : u₁ ∈ S := hv₀_nb (d - 2)
  have hu₂S : u₂ ∈ S := hv₀_nb (d - 1)
  have hu₃S : u₃ ∈ S := hv₁_nb (d - 1)
  have hu₂B : u₂ ∈ bdyS S := by rw [bdyS, Finset.mem_sdiff]; exact ⟨hu₂S, hu₂_out⟩
  have hu₂_d : addS u₂ (e d) = u₃ := by
    unfold u₂ u₃; rw [heq]; unfold addS; ext <;> dsimp only <;> ring
  have hu₂_d1 : addS u₂ (e (d + 1)) = v₁ := by
    unfold u₂; rw [heq, addS_addS_e]; congr 1; fin_cases d <;> rfl
  have hu₂_d2 : addS u₂ (e (d + 2)) = v₀ := by
    unfold u₂; rw [addS_addS_e]; have : addS (e (d - 1)) (e (d + 2)) = (0, 0) := by fin_cases d <;> rfl
    rw [this]; unfold addS; ext <;> simp
  have hu₂_d3 : addS u₂ (e (d + 3)) = u₁ := by
    unfold u₂ u₁; rw [addS_addS_e]; congr 1; fin_cases d <;> rfl
  by_cases h5 : addS u₂ (e (d + 5)) ∉ S
  · have hdir : bdyDir S u₂ = d :=
      bdyDir_eq_of hloc hu₂S (by rw [hu₂_d]; exact hu₃S) (by rwa [zmod6_sub_one_eq_add_five])
    refine ⟨u₂, hu₂B, unitStep_symm (unitStep_addS_e v₀ (d - 1)), ?_⟩
    unfold phi; rw [hdir, hu₂_d]
    exact unitStep_addS_e v₁ (d - 1)
  · have h5in : addS u₂ (e (d + 5)) ∈ S := by by_contra h; exact h5 h
    have h4out : addS u₂ (e (d + 4)) ∉ S := by
      intro h4in
      apply hu₂_out
      rw [mem_intS]
      refine ⟨hu₂S, fun c => ?_⟩
      rcases zmod6_shift_cases c d with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hu₂_d]; exact hu₃S
      · rw [hu₂_d1]; exact (mem_intS.mp hv₁).1
      · rw [hu₂_d2]; exact (mem_intS.mp hv₀).1
      · rw [hu₂_d3]; exact hu₁S
      · exact h4in
      · exact h5in
    have hu₁_5 : addS u₁ (e (d + 5)) = addS u₂ (e (d + 4)) := by
      unfold u₁ u₂; rw [addS_addS_e, addS_addS_e]; congr 1; fin_cases d <;> rfl
    have hu₁_d : addS u₁ (e d) = u₂ := by
      unfold u₁ u₂; rw [addS_addS_e]; congr 1; fin_cases d <;> rfl
    have hu₁_out : addS u₁ (e (d - 1)) ∉ S := by
      rw [zmod6_sub_one_eq_add_five, hu₁_5]; exact h4out
    have hu₁B : u₁ ∈ bdyS S := mem_bdyS.mpr ⟨hu₁S, d - 1, hu₁_out⟩
    have hdir : bdyDir S u₁ = d := bdyDir_eq_of hloc hu₁S (by rw [hu₁_d]; exact hu₂S) hu₁_out
    refine ⟨u₁, hu₁B, unitStep_symm (unitStep_addS_e v₀ (d - 2)), ?_⟩
    unfold phi; rw [hdir, hu₁_d]
    have : unitStep u₂ v₁ := by rw [← hu₂_d1]; exact unitStep_addS_e u₂ (d + 1)
    exact unitStep_symm this

/-- Step 8.3a: Merge adjacent K_2 interior into C_out. -/
private def IsAdjPair (S : Finset Site) : Prop :=
  ∃ a b : Site, a ≠ b ∧ unitStep a b ∧ S = {a, b}

private lemma merge_K2 {S : Finset Site}
    (hconn : ConnS S) (hconv : HorizConvex S) (hloc : LocallyConn S)
    (hI : IsAdjPair (intS S)) : HasHamCycle S := by
  obtain ⟨a, b, hne, hstep, hint⟩ := hI
  have haI : a ∈ intS S := by rw [hint]; simp
  have hbI : b ∈ intS S := by rw [hint]; simp
  have hS_ne : S.Nonempty := ⟨a, (mem_intS.mp haI).1⟩
  obtain ⟨C, hC, hC_edge⟩ := boundary_hasHamCycle hS_ne hconn hconv hloc
  obtain ⟨d, hd⟩ := (unitStep_iff_exists_dir a b).mp hstep
  have hu₂_out : addS a (e (d - 1)) ∉ intS S := by
    rw [hint, Finset.mem_insert, Finset.mem_singleton]
    rintro (h1 | h2)
    · have h0 : e (d - 1) = (0, 0) := by
        have h1' := congrArg Prod.fst h1; have h2' := congrArg Prod.snd h1
        unfold addS at h1' h2'; dsimp only at h1' h2'; ext <;> omega
      have hq := QZ_e (d - 1); rw [h0] at hq; unfold QZ at hq; norm_num at hq
    · rw [hd] at h2
      have : e (d - 1) = e d := by
        have h1 := congrArg Prod.fst h2; have h2' := congrArg Prod.snd h2
        unfold addS at h1 h2'; dsimp only at h1 h2'; ext <;> omega
      have := e_injective this
      have : (-1 : ZMod 6) = 0 := by linear_combination this
      exact absurd (congrArg (@ZMod.val 6) this) (by decide)
  obtain ⟨u, huB, hu_a, hb_phi⟩ := rhombus_bridge hloc haI hbI hd hu₂_out
  obtain ⟨idx, hidx, hCidx, hCnext⟩ := hC_edge u huB
  have hunion : bdyS S ∪ intS S = S := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hdisj : Disjoint (bdyS S) (intS S) := disjoint_sdiff_self_left
  rw [← hunion]
  apply splice_path_into_cycle hdisj hC idx hidx (P := [a, b])
    (by simp) (by simp [hne]) (by intro x; rw [hint]; simp)
    (by intro j hj
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; exact hstep)
  · rw [hCidx]; simpa using hu_a
  · rw [hCnext]; simpa using hb_phi

/-- Step 8.3b: Merge Hamiltonian interior C_in into C_out via lexMin(I) edge with d ∈ {0, 2}. -/
private lemma merge_HamCycle {S : Finset Site}
    (hconn : ConnS S) (hconv : HorizConvex S) (hloc : LocallyConn S)
    (hI : HasHamCycle (intS S)) : HasHamCycle S := by
  obtain ⟨Cin, hCin⟩ := hI
  have hCin_pos : 0 < Cin.length := by have := hCin.1; omega
  have hI_ne : (intS S).Nonempty := ⟨Cin[0], (hCin.2.2.1 _).mp (List.getElem_mem _)⟩
  obtain ⟨v₀, hv₀I, hv₀_min⟩ := exists_lexMin hI_ne
  have hS_ne : S.Nonempty := ⟨v₀, (mem_intS.mp hv₀I).1⟩
  obtain ⟨C, hC, hC_edge⟩ := boundary_hasHamCycle hS_ne hconn hconv hloc
  have hv₀_mem : v₀ ∈ Cin := (hCin.2.2.1 v₀).mpr hv₀I
  rw [List.mem_iff_getElem] at hv₀_mem
  obtain ⟨j, hj, hj_eq⟩ := hv₀_mem
  let jPrev : ℕ := (j + Cin.length - 1) % Cin.length
  let jNext : ℕ := (j + 1) % Cin.length
  have hjPrev_lt : jPrev < Cin.length := Nat.mod_lt _ hCin_pos
  have hjNext_lt : jNext < Cin.length := Nat.mod_lt _ hCin_pos
  have hjPrev_succ : (jPrev + 1) % Cin.length = j := by
    dsimp only [jPrev]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show j + Cin.length - 1 + 1 = j + Cin.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  let wPrev := Cin[jPrev]
  let wNext := Cin[jNext]
  have hwPrev_step : unitStep v₀ wPrev := by
    have hs := hCin.2.2.2 jPrev hjPrev_lt
    simp only [hjPrev_succ, hj_eq] at hs
    exact unitStep_symm hs
  have hwNext_step : unitStep v₀ wNext := by
    have hs := hCin.2.2.2 j hj
    rwa [hj_eq] at hs
  obtain ⟨d1, hd1⟩ := (unitStep_iff_exists_dir v₀ wPrev).mp hwPrev_step
  obtain ⟨d2, hd2⟩ := (unitStep_iff_exists_dir v₀ wNext).mp hwNext_step
  have hwPrevI : wPrev ∈ intS S := (hCin.2.2.1 _).mp (List.getElem_mem _)
  have hwNextI : wNext ∈ intS S := (hCin.2.2.1 _).mp (List.getElem_mem _)
  have hwPrev_ne : wPrev ≠ v₀ := fun h => not_unitStep_self v₀ (h ▸ hwPrev_step)
  have hwNext_ne : wNext ≠ v₀ := fun h => not_unitStep_self v₀ (h ▸ hwNext_step)
  have hd1_012 : d1 = 0 ∨ d1 = 1 ∨ d1 = 2 := (lexLt_e_iff v₀ d1).mp (hd1 ▸ hv₀_min wPrev hwPrevI hwPrev_ne)
  have hd2_012 : d2 = 0 ∨ d2 = 1 ∨ d2 = 2 := (lexLt_e_iff v₀ d2).mp (hd2 ▸ hv₀_min wNext hwNextI hwNext_ne)
  have hd12_ne : d1 ≠ d2 := by
    intro heq
    have hw_eq : wPrev = wNext := by rw [hd1, hd2, heq]
    have hidx_eq : jPrev = jNext := (hCin.2.1.getElem_inj_iff).mp hw_eq
    have hmod_eq : (j + Cin.length - 1) % Cin.length = (j + 1) % Cin.length := hidx_eq
    have h2 : (Cin.length - 1 + j) % Cin.length = (1 + j) % Cin.length := by
      convert hmod_eq using 2 <;> omega
    have h1eq : Cin.length - 1 = 1 := mod_add_cancel (by omega) (by have := hCin.1; omega) h2
    have := hCin.1; omega
  have hunion : bdyS S ∪ intS S = S := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hdisj : Disjoint (bdyS S) (intS S) := disjoint_sdiff_self_left
  -- Helper: given a cycle edge jE of Cin connecting a = Cin[jE] and b = Cin[(jE+1)%m],
  -- bridge either (a, b) or (b, a) into C_out!
  have hbridge_ab : ∀ (jE : ℕ) (hjE : jE < Cin.length) (a b : Site),
      ((Cin[jE] = a ∧ Cin[(jE + 1) % Cin.length]'(Nat.mod_lt _ hCin_pos) = b) ∨
       (Cin[jE] = b ∧ Cin[(jE + 1) % Cin.length]'(Nat.mod_lt _ hCin_pos) = a)) →
      (∃ u ∈ bdyS S, unitStep u a ∧ unitStep b (phi S u)) → HasHamCycle S := by
    intro jE hjE a b hedge ⟨u, huB, hua, hbu⟩
    obtain ⟨idx, hidx, hCidx, hCnext⟩ := hC_edge u huB
    obtain ⟨P, hPpos, hPnd, hPmem, hPstep, hP0, hPlast⟩ := path_of_cycle_edge hCin jE hjE
    rw [← hunion]
    rcases hedge with ⟨haE, hbE⟩ | ⟨hbE, haE⟩
    · -- P runs from b to a; reverse P runs from a to b!
      obtain ⟨hRpos, hRnd, hRmem, hRstep, hR0, hRlast⟩ := path_reverse hPpos hPnd hPmem hPstep
      apply splice_path_into_cycle hdisj hC idx hidx hRpos hRnd hRmem hRstep
      · rw [hCidx, hR0, hPlast, haE]; exact hua
      · rw [hCnext, hRlast, hP0, hbE]; exact hbu
    · -- P already runs from a to b!
      apply splice_path_into_cycle hdisj hC idx hidx hPpos hPnd hPmem hPstep
      · rw [hCidx, hP0, haE]; exact hua
      · rw [hCnext, hPlast, hbE]; exact hbu
  -- At least one of d1, d2 is 0 or 2!
  have hcase : (d1 = 0 ∨ d1 = 2) ∨ (d2 = 0 ∨ d2 = 2) := by
    rcases hd1_012 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases hd2_012 with h' | h' | h'
      · exact Or.inr (Or.inl h')
      · exact absurd (h.trans h'.symm) hd12_ne
      · exact Or.inr (Or.inr h')
    · exact Or.inl (Or.inr h)
  -- Helper for an incident edge (v₀, w) with direction d ∈ {0, 2}:
  have hdo : ∀ (jE : ℕ) (hjE : jE < Cin.length) (w : Site) (d : ZMod 6),
      w ∈ intS S → w = addS v₀ (e d) → (d = 0 ∨ d = 2) →
      ((Cin[jE] = v₀ ∧ Cin[(jE + 1) % Cin.length]'(Nat.mod_lt _ hCin_pos) = w) ∨
       (Cin[jE] = w ∧ Cin[(jE + 1) % Cin.length]'(Nat.mod_lt _ hCin_pos) = v₀)) →
      HasHamCycle S := by
    intro jE hjE w d hwI hwd hd02 hedge
    rcases hd02 with rfl | rfl
    · -- d = 0: u₂ = v₀ + e 5 has y = v₀.2 - 1 < v₀.2 ⇒ u₂ ∉ intS S!
      have hu₂_out : addS v₀ (e (0 - 1)) ∉ intS S := by
        rw [show (0 : ZMod 6) - 1 = 5 from rfl]
        intro hmem
        have hne : addS v₀ (e 5) ≠ v₀ := by
          intro h; have := congrArg Prod.snd h; unfold addS e at this; dsimp only at this; omega
        rcases hv₀_min _ hmem hne with hlt | ⟨heq, _⟩ <;> unfold addS e at * <;> dsimp only at * <;> omega
      exact hbridge_ab jE hjE v₀ w hedge (rhombus_bridge hloc hv₀I hwI hwd hu₂_out)
    · -- d = 2: reverse edge (w, v₀) has direction 5, u₂ = w + e 4 = v₀ + e 3 has x = v₀.1 - 1 < v₀.1 ⇒ u₂ ∉ intS S!
      have hv₀_eq : v₀ = addS w (e 5) := by
        rw [hwd, addS_addS_e]; have : addS (e 2) (e 5) = (0, 0) := rfl; rw [this]; unfold addS; ext <;> simp
      have hu₂_out : addS w (e (5 - 1)) ∉ intS S := by
        have heq : addS w (e (5 - 1)) = addS v₀ (e 3) := by
          rw [hwd, addS_addS_e]; congr 1
        rw [heq]
        intro hmem
        have hne : addS v₀ (e 3) ≠ v₀ := by
          intro h; have := congrArg Prod.fst h; unfold addS e at this; dsimp only at this; omega
        rcases hv₀_min _ hmem hne with hlt | ⟨heq', hlt⟩ <;> unfold addS e at * <;> dsimp only at * <;> omega
      have hedge' :
          (Cin[jE] = w ∧ Cin[(jE + 1) % Cin.length]'(Nat.mod_lt _ hCin_pos) = v₀) ∨
          (Cin[jE] = v₀ ∧ Cin[(jE + 1) % Cin.length]'(Nat.mod_lt _ hCin_pos) = w) := hedge.symm
      exact hbridge_ab jE hjE w v₀ hedge' (rhombus_bridge hloc hwI hv₀I hv₀_eq hu₂_out)
  rcases hcase with h1 | h2
  · exact hdo jPrev hjPrev_lt wPrev d1 hwPrevI hd1 h1 (Or.inr ⟨rfl, by simp only [hjPrev_succ, hj_eq]⟩)
  · exact hdo j hj wNext d2 hwNextI hd2 h2 (Or.inl ⟨hj_eq, rfl⟩)

/-- Step 8.4: Inner Star-of-David Splice (Int(S) = D_13(v)). -/
private def P13Offsets : List Site :=
  [(2, -1), (1, 0), (0, 0), (1, -1), (1, -2), (0, -1),
   (-1, -1), (-1, 0), (-2, 1), (-1, 1), (-1, 2), (0, 1), (1, 1)]

private lemma merge_D13 {S : Finset Site} {v : Site}
    (hconn : ConnS S) (hconv : HorizConvex S) (hloc : LocallyConn S)
    (hint : intS S = D13 v) : HasHamCycle S := by
  have hvI : v ∈ intS S := by rw [hint]; exact (mem_D13_iff v v).mpr (Or.inl rfl)
  have hS_ne : S.Nonempty := ⟨v, (mem_intS.mp hvI).1⟩
  obtain ⟨C, hC, hC_edge⟩ := boundary_hasHamCycle hS_ne hconn hconv hloc
  let t₀ := addS v (1, 1)
  let h₀ := addS v (1, 0)
  let t₅ := addS v (2, -1)
  have ht₀I : t₀ ∈ intS S := by rw [hint]; exact (mem_D13_iff v t₀).mpr (Or.inr (Or.inr ⟨0, rfl⟩))
  have hh₀I : h₀ ∈ intS S := by rw [hint]; exact (mem_D13_iff v h₀).mpr (Or.inr (Or.inl ⟨0, rfl⟩))
  have ht₅I : t₅ ∈ intS S := by rw [hint]; exact (mem_D13_iff v t₅).mpr (Or.inr (Or.inr ⟨5, rfl⟩))
  let u₁ := addS v (2, 0)
  have hu₁S : u₁ ∈ S := by
    have : u₁ = addS t₀ (e 5) := by unfold u₁ t₀ addS e; ext <;> dsimp only <;> omega
    rw [this]; exact (mem_intS.mp ht₀I).2 5
  have hu₁_notI : u₁ ∉ intS S := by
    rw [hint]; unfold D13
    rw [List.mem_toFinset, List.mem_map]
    rintro ⟨q, hq, heq⟩
    have hqeq : q = (2, 0) := addS_inj v heq
    subst hqeq
    exact absurd hq (by decide)
  have hu₁B : u₁ ∈ bdyS S := by rw [bdyS, Finset.mem_sdiff]; exact ⟨hu₁S, hu₁_notI⟩
  have hnb1 : addS u₁ (e 1) ∈ S := by
    have : addS u₁ (e 1) = addS t₀ (e 0) := by unfold u₁ t₀ addS e; ext <;> dsimp only <;> omega
    rw [this]; exact (mem_intS.mp ht₀I).2 0
  have hnb2 : addS u₁ (e 2) ∈ S := by
    have : addS u₁ (e 2) = t₀ := by unfold u₁ t₀ addS e; ext <;> dsimp only <;> omega
    rw [this]; exact (mem_intS.mp ht₀I).1
  have hnb3 : addS u₁ (e 3) ∈ S := by
    have : addS u₁ (e 3) = h₀ := by unfold u₁ h₀ addS e; ext <;> dsimp only <;> omega
    rw [this]; exact (mem_intS.mp hh₀I).1
  have hnb4 : addS u₁ (e 4) ∈ S := by
    have : addS u₁ (e 4) = t₅ := by unfold u₁ t₅ addS e; ext <;> dsimp only <;> omega
    rw [this]; exact (mem_intS.mp ht₅I).1
  have hnb5 : addS u₁ (e 5) ∈ S := by
    have : addS u₁ (e 5) = addS t₅ (e 0) := by unfold u₁ t₅ addS e; dsimp only; exact Prod.ext (by omega) (by omega)
    rw [this]; exact (mem_intS.mp ht₅I).2 0
  have hnb0_out : addS u₁ (e 0) ∉ S := by
    intro h0in
    apply hu₁_notI
    rw [mem_intS]
    refine ⟨hu₁S, fun d => ?_⟩
    fin_cases d
    · exact h0in
    · exact hnb1
    · exact hnb2
    · exact hnb3
    · exact hnb4
    · exact hnb5
  have hdir : bdyDir S u₁ = 1 := bdyDir_eq_of hloc hu₁S hnb1 (by simpa using hnb0_out)
  have hphi_u₁ : phi S u₁ = addS v (2, 1) := by
    unfold phi; rw [hdir]; unfold u₁ addS e; ext <;> dsimp only <;> omega
  obtain ⟨idx, hidx, hCidx, hCnext⟩ := hC_edge u₁ hu₁B
  let P : List Site := P13Offsets.map (addS v)
  have hP_pos : 0 < P.length := by simp [P, P13Offsets]
  have hP_nodup : P.Nodup := List.Nodup.map (addS_inj v) (by decide)
  have hP_mem : ∀ x, x ∈ P ↔ x ∈ intS S := by
    intro x
    rw [hint]; unfold P D13
    rw [List.mem_toFinset, List.mem_map, List.mem_map]
    have hiff : ∀ q : Site, q ∈ P13Offsets ↔ q ∈ D13Offsets := by
      intro q
      constructor
      · intro h
        simp only [P13Offsets, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [D13Offsets]
      · intro h
        simp only [D13Offsets, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [P13Offsets]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, (hiff q).mp hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, (hiff q).mpr hq, rfl⟩
  have hP_step : ∀ (j : ℕ) (hj : j + 1 < P.length), unitStep P[j] P[j + 1] := by
    intro j hj
    have hj12 : j < 12 := by simp [P, P13Offsets] at hj; omega
    have hsh : ∀ a b : Site, unitStep a b → unitStep (addS v a) (addS v b) := by
      intro a b h; unfold unitStep at h; unfold unitStep addS; linarith
    simp only [P, List.getElem_map]
    apply hsh
    interval_cases j <;> rfl
  have h_in : unitStep C[idx] P[0] := by
    rw [hCidx]; simp only [P, P13Offsets, List.map_cons, List.getElem_cons_zero]
    unfold u₁ unitStep addS; ring
  have h_out : unitStep (P[P.length - 1]'(by omega)) (C[(idx + 1) % C.length]'(Nat.mod_lt _ (by have := hC.1; omega))) := by
    rw [hCnext, hphi_u₁]
    have hlast : P[P.length - 1] = addS v (1, 1) := rfl
    rw [hlast]
    unfold unitStep addS; ring
  have hunion : bdyS S ∪ intS S = S := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hdisj : Disjoint (bdyS S) (intS S) := disjoint_sdiff_self_left
  rw [← hunion]
  exact splice_path_into_cycle hdisj hC idx hidx hP_pos hP_nodup hP_mem hP_step h_in h_out

/-! ### Section 9 (completion): Core classification for 0 ≤ r < q + 1 -/

private def OnionProp (S : Finset Site) : Prop :=
  S.card ≤ 1 ∨ IsAdjPair S ∨ HasHamCycle S ∨ ∃ v : Site, S = D13 v

private lemma unitStep_rotS (p q : Site) : unitStep (rotS p) (rotS q) ↔ unitStep p q := by
  unfold unitStep rotS; dsimp only
  have h : (-p.2 - -q.2) ^ 2 + (-p.2 - -q.2) * (p.1 + p.2 - (q.1 + q.2)) +
      (p.1 + p.2 - (q.1 + q.2)) ^ 2 = (p.1 - q.1) ^ 2 + (p.1 - q.1) * (p.2 - q.2) + (p.2 - q.2) ^ 2 := by
    ring
  rw [h]

private lemma unitStep_rotS_iter (n : ℕ) (p q : Site) :
    unitStep (rotS^[n] p) (rotS^[n] q) ↔ unitStep p q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', unitStep_rotS, ih]

private lemma rotS_iter_inj (n : ℕ) : Function.Injective (rotS^[n]) := by
  intro a b h
  have h6 : rotS^[6 - n % 6] (rotS^[n] a) = rotS^[6 - n % 6] (rotS^[n] b) := congrArg _ h
  have hmod : ∀ x : Site, rotS^[6 - n % 6] (rotS^[n] x) = x := by
    intro x
    rw [← Function.iterate_add_apply]
    have hmul : ∀ m : ℕ, rotS^[m * 6] x = x := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [show (m + 1) * 6 = m * 6 + 6 by ring, Function.iterate_add_apply, rotS_pow6, ih]
    have hdiv : 6 - n % 6 + n = (n / 6 + 1) * 6 := by
      have := Nat.div_add_mod n 6; have := Nat.mod_lt n (by decide : 0 < 6); omega
    rw [hdiv, hmul]
  rw [hmod a, hmod b] at h6
  exact h6

private lemma mem_layerFinset_rot (o : Center) (r : ℝ) (q n : ℕ) (p : Site) :
    rotS^[n] p ∈ layerFinset (rotR^[n] o) r q ↔ p ∈ layerFinset o r q := by
  rw [mem_layerFinset, mem_layerFinset]
  unfold inKS
  rw [inKR_shift_zero (rotR^[n] o), inKR_shift_zero o, ← rotR_iter_toR, ← rotR_iter_sub, inKR_rot_iter_iff]

private lemma core_classify {o : Center} {r : ℝ} {q : ℕ}
    (hr0 : 0 ≤ r) (hr : r < (q : ℝ) + 1) :
    OnionProp (layerFinset o r q) := by
  classical
  set S := layerFinset o r q
  by_cases h3 : ∃ a ∈ S, ∃ b ∈ S, QZ (subS b a) = 3
  · -- Rhombus case: rotate b - a to (1, 1) and apply core_no_sqrt3_tri + core_rhombus_complete!
    obtain ⟨a, haS, b, hbS, hQZ3⟩ := h3
    obtain ⟨h1, h2, h3', _⟩ := core_pair_QZ hr0 hr haS hbS
    have hdiag : ∃ d : ZMod 6, subS b a = addS (e d) (e (d + 1)) := by
      rcases hv_eq : subS b a with ⟨vx, vy⟩
      rw [hv_eq] at h1 h2 h3' hQZ3
      dsimp only [QZ] at h1 h2 h3' hQZ3
      rw [abs_le] at h1 h2 h3'
      have hx1 : -2 ≤ vx := by omega
      have hx2 : vx ≤ 2 := by omega
      have hy1 : -2 ≤ vy := by omega
      have hy2 : vy ≤ 2 := by omega
      have hlist : (vx = 1 ∧ vy = 1) ∨ (vx = -1 ∧ vy = 2) ∨ (vx = -2 ∧ vy = 1) ∨
          (vx = -1 ∧ vy = -1) ∨ (vx = 1 ∧ vy = -2) ∨ (vx = 2 ∧ vy = -1) := by
        interval_cases vy <;> interval_cases vx <;> norm_num at hQZ3 <;> norm_num
      rcases hlist with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    obtain ⟨d, hd⟩ := hdiag
    let m : ℕ := (6 - d.val) % 6
    let o' := rotR^[m] o
    let S' := layerFinset o' r q
    let a' := rotS^[m] a
    let b' := rotS^[m] b
    have ha' : a' ∈ S' := (mem_layerFinset_rot o r q m a).mpr haS
    have hb' : b' ∈ S' := (mem_layerFinset_rot o r q m b).mpr hbS
    have hrot_add : ∀ (n : ℕ) (x y : Site), rotS^[n] (addS x y) = addS (rotS^[n] x) (rotS^[n] y) := by
      intro n x y; induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        unfold rotS addS; ext <;> dsimp only <;> ring
    have hb'_eq : b' = addS a' (1, 1) := by
      have hb_eq : b = addS a (addS (e d) (e (d + 1))) := by
        rcases a with ⟨ax, ay⟩; rcases b with ⟨bx, by'⟩
        unfold subS addS at hd; unfold addS
        have hf1 := congrArg Prod.fst hd; have hf2 := congrArg Prod.snd hd
        dsimp only at hf1 hf2; ext <;> dsimp only <;> omega
      dsimp only [b', a']
      rw [hb_eq, hrot_add, hrot_add, rotS_iter_e, rotS_iter_e]
      congr 1
      have hdm : d + (m : ZMod 6) = 0 := by
        fin_cases d <;> decide
      have hdm1 : d + 1 + (m : ZMod 6) = 1 := by
        rw [add_right_comm, hdm, zero_add]
      rw [hdm, hdm1]; rfl
    rw [hb'_eq] at hb'
    obtain ⟨hw1, hw2⟩ := core_rhombus_complete hr0 hr ha' hb'
    obtain ⟨hno1, hno2⟩ := core_no_sqrt3_tri hr0 hr ha' hb'
    have hS'_eq : ∀ c : Site, c ∈ S' ↔
        c = a' ∨ c = addS a' (1, 0) ∨ c = addS a' (1, 1) ∨ c = addS a' (0, 1) := by
      intro c
      constructor
      · intro hc
        obtain ⟨ca1, ca2, ca3, _⟩ := core_pair_QZ hr0 hr ha' hc
        obtain ⟨cb1, cb2, cb3, _⟩ := core_pair_QZ hr0 hr hb' hc
        rcases hv_eq : subS c a' with ⟨vx, vy⟩
        have hc_eq : c = addS a' (vx, vy) := by
          rcases c with ⟨cx, cy⟩; rcases a' with ⟨ax, ay⟩
          unfold subS at hv_eq; unfold addS
          have h1 := congrArg Prod.fst hv_eq; have h2 := congrArg Prod.snd hv_eq
          dsimp only at h1 h2; ext <;> dsimp only <;> omega
        have hcb_eq : subS c (addS a' (1, 1)) = (vx - 1, vy - 1) := by
          rw [hc_eq]; unfold subS addS; ext <;> dsimp only <;> omega
        rw [hv_eq] at ca1 ca2 ca3
        rw [hcb_eq] at cb1 cb2 cb3
        dsimp only at ca1 ca2 ca3 cb1 cb2 cb3
        rw [abs_le] at ca1 ca2 ca3 cb1 cb2 cb3
        have hx1 : -2 ≤ vx := by omega
        have hx2 : vx ≤ 2 := by omega
        have hy1 : -2 ≤ vy := by omega
        have hy2 : vy ≤ 2 := by omega
        have h6 : (vx = 0 ∧ vy = 0) ∨ (vx = 1 ∧ vy = 0) ∨ (vx = 0 ∧ vy = 1) ∨
            (vx = 1 ∧ vy = 1) ∨ (vx = -1 ∧ vy = 2) ∨ (vx = 2 ∧ vy = -1) := by
          interval_cases vy <;> interval_cases vx <;> omega
        rcases h6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left; rw [hc_eq]; unfold addS; ext <;> simp
        · right; left; exact hc_eq
        · right; right; right; exact hc_eq
        · right; right; left; exact hc_eq
        · exfalso; rw [hc_eq] at hc; exact hno1 hc
        · exfalso; rw [hc_eq] at hc; exact hno2 hc
      · rintro (rfl | rfl | rfl | rfl)
        · exact ha'
        · exact hw1
        · exact hb'
        · exact hw2
    -- Build Hamiltonian 4-cycle on S' and pull back to S via rotS^[6 - m]!
    let L' : List Site := [a', addS a' (1, 0), addS a' (1, 1), addS a' (0, 1)]
    let kback : ℕ := (6 - m) % 6
    let L : List Site := L'.map (rotS^[kback])
    have hback_id : ∀ x : Site, rotS^[kback] (rotS^[m] x) = x := by
      intro x
      rw [← Function.iterate_add_apply]
      have hsum : kback + m = 0 ∨ kback + m = 6 := by
        dsimp only [kback, m]; omega
      rcases hsum with h0 | h6
      · rw [h0]; rfl
      · rw [h6]; exact rotS_pow6 x
    have hL'_nd : L'.Nodup := by
      simp only [L', List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_false_eq_true, List.nodup_nil, and_true]
      refine ⟨?_, ?_, ?_⟩
      · rintro (h | h | h) <;> unfold addS at h <;>
          [have := congrArg Prod.fst h; have := congrArg Prod.fst h; have := congrArg Prod.snd h] <;>
          dsimp only at this <;> omega
      · rintro (h | h) <;> unfold addS at h <;>
          [have := congrArg Prod.snd h; have := congrArg Prod.fst h] <;>
          dsimp only at this <;> omega
      · intro h; have := congrArg Prod.fst h; unfold addS at this; dsimp only at this; omega
    right; right; left
    refine ⟨L, by simp [L, L'], List.Nodup.map (rotS_iter_inj kback) hL'_nd, ?_, ?_⟩
    · intro x
      rw [← mem_layerFinset_rot o r q m x]
      show x ∈ L ↔ rotS^[m] x ∈ S'
      rw [hS'_eq]
      simp only [L, L', List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;>
          have hfwd : ∀ y : Site, rotS^[m] (rotS^[kback] y) = y := by
            intro y; rw [← Function.iterate_add_apply]
            have : m + kback = 0 ∨ m + kback = 6 := by dsimp only [kback, m]; omega
            rcases this with h0 | h6
            · rw [h0]; rfl
            · rw [h6]; exact rotS_pow6 y
        · left; exact hfwd a'
        · right; left; exact hfwd _
        · right; right; left; exact hfwd _
        · right; right; right; exact hfwd _
      · rintro (h | h | h | h)
        · left; rw [← h, hback_id]
        · right; left; rw [← h, hback_id]
        · right; right; left; rw [← h, hback_id]
        · right; right; right; rw [← h, hback_id]
    · intro i hi
      have hi4 : i < 4 := by simp [L, L'] at hi; omega
      have hL'len : L'.length = 4 := rfl
      simp only [L, List.getElem_map, List.length_map, hL'len, unitStep_rotS_iter]
      interval_cases i
      · change unitStep a' (addS a' (1, 0)); unfold unitStep addS; ring
      · change unitStep (addS a' (1, 0)) (addS a' (1, 1)); unfold unitStep addS; ring
      · change unitStep (addS a' (1, 1)) (addS a' (0, 1)); unfold unitStep addS; ring
      · change unitStep (addS a' (0, 1)) a'; unfold unitStep addS; ring
  · -- Clique case: every pair of distinct vertices in S is adjacent ⇒ |S| ≤ 3!
    have hadj : ∀ p₁ ∈ S, ∀ p₂ ∈ S, p₁ ≠ p₂ → unitStep p₁ p₂ := by
      intro p₁ h1 p₂ h2 hne
      obtain ⟨_, _, _, hq⟩ := core_pair_QZ hr0 hr h1 h2
      rcases hq with h0 | h1' | h3'
      · exfalso
        have h0R : Q (toR (subS p₂ p₁)) = 0 := by rw [Q_toR, h0]; norm_num
        obtain ⟨hx, hy⟩ := (Q_eq_zero_iff _).mp h0R
        unfold toR subS at hx hy
        rcases p₁ with ⟨a, b⟩; rcases p₂ with ⟨c, d⟩; dsimp only at hx hy
        have hx' : c - a = 0 := by exact_mod_cast hx
        have hy' : d - b = 0 := by exact_mod_cast hy
        exact hne (by ext <;> dsimp only <;> omega)
      · unfold unitStep; unfold QZ subS at h1'; linarith
      · exact absurd ⟨p₁, h1, p₂, h2, h3'⟩ h3
    by_cases hc1 : S.card ≤ 1
    · exact Or.inl hc1
    · by_cases hc2 : S.card = 2
      · obtain ⟨a, b, hne, hEq⟩ := Finset.card_eq_two.mp hc2
        right; left
        have haS : a ∈ S := by rw [hEq]; simp
        have hbS : b ∈ S := by rw [hEq]; simp
        exact ⟨a, b, hne, hadj a haS b hbS hne, hEq⟩
      · by_cases hc3 : S.card = 3
        · obtain ⟨a, b, c, hab, hac, hbc, hEq⟩ := Finset.card_eq_three.mp hc3
          right; right; left
          have haS : a ∈ S := by rw [hEq]; simp
          have hbS : b ∈ S := by rw [hEq]; simp
          have hcS : c ∈ S := by rw [hEq]; simp
          refine ⟨[a, b, c], by simp, by simp [hab, hac, hbc], by intro x; rw [hEq]; simp, ?_⟩
          intro i hi
          have hi3 : i < 3 := by simpa using hi
          have hlen3 : ([a, b, c] : List Site).length = 3 := rfl
          simp only [hlen3]
          interval_cases i
          · exact hadj a haS b hbS hab
          · exact hadj b hbS c hcS hbc
          · exact hadj c hcS a haS hac.symm
        · -- |S| ≥ 4: impossible since C_6 is triangle-free!
          exfalso
          have hc4 : 4 ≤ S.card := by omega
          have hne0 : S.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨p₀, hp₀⟩ := hne0
          let S1 := S.erase p₀
          have hne1 : S1.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hp₀]; omega)
          obtain ⟨p₁, hp₁⟩ := hne1
          let S2 := S1.erase p₁
          have hne2 : S2.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hp₁, Finset.card_erase_of_mem hp₀]; omega)
          obtain ⟨p₂, hp₂⟩ := hne2
          let S3 := S2.erase p₂
          have hne3 : S3.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hp₂, Finset.card_erase_of_mem hp₁, Finset.card_erase_of_mem hp₀]; omega)
          obtain ⟨p₃, hp₃⟩ := hne3
          have hp₁S : p₁ ∈ S := (Finset.mem_erase.mp hp₁).2
          have hp₁0 : p₁ ≠ p₀ := (Finset.mem_erase.mp hp₁).1
          have hp₂S : p₂ ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hp₂).2).2
          have hp₂1 : p₂ ≠ p₁ := (Finset.mem_erase.mp hp₂).1
          have hp₂0 : p₂ ≠ p₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hp₂).2).1
          have hp₃S : p₃ ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hp₃).2).2).2
          have hp₃2 : p₃ ≠ p₂ := (Finset.mem_erase.mp hp₃).1
          have hp₃1 : p₃ ≠ p₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hp₃).2).1
          have hp₃0 : p₃ ≠ p₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hp₃).2).2).1
          obtain ⟨d₁, hd₁⟩ := (unitStep_iff_exists_dir p₀ p₁).mp (hadj p₀ hp₀ p₁ hp₁S hp₁0.symm)
          obtain ⟨d₂, hd₂⟩ := (unitStep_iff_exists_dir p₀ p₂).mp (hadj p₀ hp₀ p₂ hp₂S hp₂0.symm)
          obtain ⟨d₃, hd₃⟩ := (unitStep_iff_exists_dir p₀ p₃).mp (hadj p₀ hp₀ p₃ hp₃S hp₃0.symm)
          have hstep_e : ∀ (a b : ZMod 6), unitStep (addS p₀ (e a)) (addS p₀ (e b)) →
              b = a + 1 ∨ b = a - 1 := by
            intro a b h
            rw [← unitStep_e_iff]
            unfold unitStep addS at h; unfold unitStep; linarith
          have h12 := hstep_e d₁ d₂ (by rw [← hd₁, ← hd₂]; exact hadj p₁ hp₁S p₂ hp₂S hp₂1.symm)
          have h23 := hstep_e d₂ d₃ (by rw [← hd₂, ← hd₃]; exact hadj p₂ hp₂S p₃ hp₃S hp₃2.symm)
          have h31 := hstep_e d₃ d₁ (by rw [← hd₃, ← hd₁]; exact hadj p₃ hp₃S p₁ hp₁S hp₃1)
          rcases h12 with rfl | rfl <;> rcases h23 with rfl | rfl <;> rcases h31 with h | h
          · have : (3 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (1 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (1 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (-1 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (1 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (-1 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (-1 : ZMod 6) = 0 := by linear_combination -h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)
          · have : (3 : ZMod 6) = 0 := by linear_combination h
            exact absurd (congrArg (@ZMod.val 6) this) (by decide)

/-! ### Section 10: Backward Onion Induction (k = ⌊r⌋ down to 0) -/

private lemma onion_induction (o : Center) {r : ℝ} (hr0 : 0 ≤ r) :
    OnionProp (layerFinset o r 0) := by
  let q : ℕ := ⌊r⌋₊
  have hq_le : (q : ℝ) ≤ r := Nat.floor_le hr0
  have hq_lt : r < (q : ℝ) + 1 := Nat.lt_floor_add_one r
  have hind : ∀ t : ℕ, t ≤ q → OnionProp (layerFinset o r (q - t)) := by
    intro t
    induction t with
    | zero =>
      intro _; simpa using core_classify hr0 hq_lt
    | succ t ih =>
      intro ht
      let k : ℕ := q - (t + 1)
      have hk1 : k + 1 = q - t := by omega
      have hrk : (k : ℝ) + 1 ≤ r := by
        have hk_le : (k + 1 : ℕ) ≤ q := by omega
        have hkR : ((k + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hk_le
        push_cast at hkR; linarith
      set S := layerFinset o r k
      have hS_ne : S.Nonempty := by
        obtain ⟨p₁, _, _, _, _, _, hp₁, _, _⟩ := unitDisk_three_sites o
        exact ⟨p₁, (mem_layerFinset o r k p₁).mpr (inKS_of_Q_le_one hrk hp₁)⟩
      have hconn : ConnS S := layer_connS hrk
      have hconv : HorizConvex S := layer_horizConvex o r k
      have hloc : LocallyConn S := layer_locallyConn hrk
      have hint_eq : intS S = layerFinset o r (q - t) := by
        rw [← hk1, ← layer_succ_eq_int]
      have hI : OnionProp (intS S) := by rw [hint_eq]; exact ih (by omega)
      rcases hI with hcard1 | hK2 | hHam | ⟨v, hD13⟩
      · by_cases hc0 : (intS S).card = 0
        · have hemp : intS S = ∅ := Finset.card_eq_zero.mp hc0
          have hbdy_eq : bdyS S = S := by unfold bdyS; rw [hemp]; simp
          obtain ⟨C, hC, _⟩ := boundary_hasHamCycle hS_ne hconn hconv hloc
          rw [hbdy_eq] at hC
          exact Or.inr (Or.inr (Or.inl ⟨C, hC⟩))
        · have hc1 : (intS S).card = 1 := by omega
          obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
          by_cases hD : S = D13 v
          · exact Or.inr (Or.inr (Or.inr ⟨v, hD⟩))
          · exact Or.inr (Or.inr (Or.inl (splice_K1 hconn hconv hloc hv hD)))
      · exact Or.inr (Or.inr (Or.inl (merge_K2 hconn hconv hloc hK2)))
      · exact Or.inr (Or.inr (Or.inl (merge_HamCycle hconn hconv hloc hHam)))
      · exact Or.inr (Or.inr (Or.inl (merge_D13 hconn hconv hloc hD13)))
  simpa using hind q le_rfl

private lemma disk_ham_or_D13 (o : Center) {r : ℝ} (hr0 : 0 ≤ r)
    (hcard : 3 ≤ (layerFinset o r 0).card) :
    HasHamCycle (layerFinset o r 0) ∨ ∃ v : Site, layerFinset o r 0 = D13 v := by
  rcases onion_induction o hr0 with h1 | hK2 | hHam | hD13
  · omega
  · obtain ⟨a, b, hne, _, hEq⟩ := hK2
    have : (layerFinset o r 0).card = 2 := by rw [hEq, Finset.card_pair hne]
    omega
  · exact Or.inl hHam
  · exact Or.inr hD13

/-! ### Section 11: Final Assembly (`OMA.S_oeis_a346126.main`) -/

private lemma attainable_of_cycle {L : List Site} {o : Center} {s : ℝ} {k : ℕ}
    (hL3 : 3 ≤ L.length) (hnd : L.Nodup)
    (hstep : ∀ (i : ℕ) (hi : i < L.length),
      unitStep L[i] (L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega))))
    (hfit : ∀ x ∈ L, Q (subR (toR x) o) ≤ s)
    (hk2 : 2 ≤ k) (hkle : k ≤ L.length) : attainable k s := by
  have hpos : 0 < L.length := by omega
  let q : ℕ → Site := fun i => L[i % L.length]'(Nat.mod_lt _ hpos)
  refine ⟨q, o, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hiL : i < L.length := by omega
    dsimp only [q]
    have hmod : i % L.length = i := Nat.mod_eq_of_lt hiL
    simpa only [hmod] using hstep i hiL
  · intro i j hij hjk heq
    have hmod : i % L.length = j % L.length := (hnd.getElem_inj_iff).mp heq
    have hiL : i < L.length := by omega
    rw [Nat.mod_eq_of_lt hiL] at hmod
    by_cases hjL : j < L.length
    · rw [Nat.mod_eq_of_lt hjL] at hmod; omega
    · have hj_eq : j = L.length := by omega
      rw [hj_eq, Nat.mod_self] at hmod
      exact ⟨hmod, by omega⟩
  · intro heq
    have hmod : 0 % L.length = k % L.length := (hnd.getElem_inj_iff).mp heq
    rw [Nat.zero_mod] at hmod
    by_cases hkL : k < L.length
    · rw [Nat.mod_eq_of_lt hkL] at hmod; omega
    · omega
  · intro i _
    exact hfit (q i) (List.getElem_mem _)

private def C12 : List Site :=
  [(-1, 0), (0, 0), (1, 0), (0, 1), (-1, 1), (-1, 2),
   (0, 2), (1, 1), (2, 0), (2, -1), (1, -1), (0, -1)]

private lemma c12_attainable {m : ℕ} (hm2 : 2 ≤ m) (hm12 : m ≤ 12) :
    attainable m ((7 : ℝ) / 3) := by
  refine attainable_of_cycle (L := C12) (o := ((1 : ℝ) / 3, (1 : ℝ) / 3))
    (by decide) (by decide) ?_ ?_ hm2 (by simpa [C12] using hm12)
  · intro i hi
    have hi12 : i < 12 := by simpa [C12] using hi
    have hlen12 : C12.length = 12 := rfl
    simp only [hlen12]
    interval_cases i <;> rfl
  · intro x hx
    simp only [C12, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      unfold Q subR toR <;> norm_num

private lemma d13_radius_ge_three {o : Center} {r s : ℝ} {v : Site}
    (hrs : r ^ 2 = s) (hD : layerFinset o r 0 = D13 v) : (3 : ℝ) ≤ s := by
  have hp1 : addS v (1, 1) ∈ layerFinset o r 0 := by
    rw [hD]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inr ⟨0, rfl⟩))
  have hp2 : addS v (-1, -1) ∈ layerFinset o r 0 := by
    rw [hD]; exact (mem_D13_iff v _).mpr (Or.inr (Or.inr ⟨3, rfl⟩))
  rw [mem_layerFinset, inKS_zero_iff, hrs] at hp1 hp2
  have hpar : Q (subR (toR (addS v (1, 1))) o) + Q (subR (toR (addS v (-1, -1))) o) =
      2 * Q (subR (toR v) o) + 6 := by
    unfold Q subR toR addS; push_cast; ring
  have hq0 := Q_nonneg (subR (toR v) o)
  linarith

private theorem main_proof : ∀ (m : ℕ) (s : ℝ) (p : ℕ → Site) (o : Center),
    2 ≤ m → valid m p → fits m p o s →
    (∀ t : ℝ, attainable m t → s ≤ t) →
    ¬ attainable (m + 1) s → p 0 = p m := by
  intro m s p o hm hval hfit hmin hmax
  by_contra hopen
  have hs0 : 0 ≤ s := by
    have hf0 := hfit 0 (Nat.zero_le m)
    have hq0 := Q_nonneg (subR (toR (p 0)) o)
    unfold Q subR toR at hq0
    linarith
  set r : ℝ := Real.sqrt s
  have hr0 : 0 ≤ r := Real.sqrt_nonneg s
  have hrs : r ^ 2 = s := Real.sq_sqrt hs0
  set S₀ := layerFinset o r 0 with hS₀_def
  have hp_mem : ∀ i ≤ m, p i ∈ S₀ := by
    intro i hi
    rw [hS₀_def, mem_layerFinset, inKS_zero_iff, hrs]
    exact hfit i hi
  have hp_inj : Set.InjOn p (Finset.range (m + 1) : Set ℕ) := by
    intro i hi j hj heq
    have hi' : i ≤ m := by rw [Finset.mem_coe, Finset.mem_range] at hi; omega
    have hj' : j ≤ m := by rw [Finset.mem_coe, Finset.mem_range] at hj; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨h0, hm'⟩ := hval.2.1 i j hlt hj' heq
      rw [h0, hm'] at heq; exact hopen heq
    · obtain ⟨h0, hm'⟩ := hval.2.1 j i hgt hi' heq.symm
      rw [h0, hm'] at heq; exact hopen heq.symm
  have hsub : (Finset.range (m + 1)).image p ⊆ S₀ := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hp_mem i (by rw [Finset.mem_range] at hi; omega)
  have hcard : m + 1 ≤ S₀.card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hp_inj, Finset.card_range] at this
  have hcard3 : 3 ≤ (layerFinset o r 0).card := by rw [← hS₀_def]; omega
  rcases disk_ham_or_D13 o hr0 hcard3 with ⟨C, hC⟩ | ⟨v, hD13⟩
  · apply hmax
    have hClen : C.length = S₀.card := by rw [hS₀_def]; exact isHamCycle_card_eq hC
    refine attainable_of_cycle (o := o) hC.1 hC.2.1 hC.2.2.2 ?_ (by omega) (by omega)
    intro x hx
    have hxS : x ∈ layerFinset o r 0 := (hC.2.2.1 x).mp hx
    rwa [mem_layerFinset, inKS_zero_iff, hrs] at hxS
  · have hm12 : m ≤ 12 := by
      have h13 : S₀.card = 13 := by rw [hS₀_def, hD13, D13_card]
      omega
    have hs_ge : (3 : ℝ) ≤ s := d13_radius_ge_three hrs hD13
    have hs_le : s ≤ (7 : ℝ) / 3 := hmin ((7 : ℝ) / 3) (c12_attainable hm hm12)
    linarith

end OeisA346126

theorem OMA.solution : type_of% @OMA.S_oeis_a346126.main :=
  OeisA346126.main_proof
