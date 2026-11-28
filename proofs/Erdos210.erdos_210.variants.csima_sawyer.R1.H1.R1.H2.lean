import OMAReductions.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1
import Mathlib

-- Step Erdos210.erdos_210.variants.csima_sawyer.R1.H1.R1.H2: hypothesis H2 of reduction Erdos210.erdos_210.variants.csima_sawyer.R1.H1.R1
-- Credit: @Uynet
--
-- Idea. Move p to the origin. A connecting line L that misses p is {x : <alpha, x> = 1}.
-- For a direction e, take the connecting line maximising <alpha_L, e> (`val`).
-- * If the maximiser is ordinary, maximality alone gives the attachment sign pattern.
-- * If it has a third point, one of its points c is in the middle, and then the line pc
--   is ordinary. Since p lies on exactly one ordinary line (through r), c = r.
-- * Taking e = r - p (or a generic e when all lines lie on one side of r) keeps the
--   maximiser and the minimiser away from that bad case, and they are distinct lines.

open EuclideanGeometry Finset
open scoped Classical

namespace OMA.KM

/-- Signed area of the triangle `x y z`; zero iff the three points are collinear. -/
def C (x y z : ℝ²) : ℝ := (y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)

/-- Cross product of `x - p` with the direction `e`. -/
def K (p x : ℝ²) (e : ℝ × ℝ) : ℝ := (x 0 - p 0) * e.2 - (x 1 - p 1) * e.1

/-- The direction from `p` to `r`. -/
def dir (p r : ℝ²) : ℝ × ℝ := (r 0 - p 0, r 1 - p 1)

/-- Height of the line `a b` in direction `e`, seen from `p`. -/
noncomputable def val (p : ℝ²) (e : ℝ × ℝ) (a b : ℝ²) : ℝ := (K p a e - K p b e) / C p a b

theorem ext2 {x y : ℝ²} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem C_cycle (x y z : ℝ²) : C y z x = C x y z := by unfold C; ring
theorem C_swap (x y z : ℝ²) : C x z y = -C x y z := by unfold C; ring
theorem C_flip (x y z : ℝ²) : C y x z = -C x y z := by unfold C; ring
theorem C_rev (x y z : ℝ²) : C z y x = -C x y z := by unfold C; ring
theorem C_left (x y : ℝ²) : C x x y = 0 := by unfold C; ring
theorem C_mid (x y : ℝ²) : C x y x = 0 := by unfold C; ring
theorem C_right (x y : ℝ²) : C x y y = 0 := by unfold C; ring

theorem K_dir (p r x : ℝ²) : K p x (dir p r) = C p x r := by
  show (x 0 - p 0) * (r 1 - p 1) - (x 1 - p 1) * (r 0 - p 0) = _
  unfold C; ring

theorem K_neg (p x : ℝ²) (e : ℝ × ℝ) : K p x (-e) = -K p x e := by
  show (x 0 - p 0) * (-e.2) - (x 1 - p 1) * (-e.1) = -((x 0 - p 0) * e.2 - (x 1 - p 1) * e.1)
  ring

theorem val_fst (p a b z : ℝ²) (e : ℝ × ℝ) (hD : C p a b ≠ 0) (hz : C p z b ≠ 0) :
    val p e z b - val p e a b = C a b z / C p a b * (K p b e / C p b z) := by
  have hz' : C p b z ≠ 0 := by rw [C_swap]; exact neg_ne_zero.mpr hz
  unfold val
  rw [div_sub_div _ _ hz hD, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero hz hD) (mul_ne_zero hD hz')]
  unfold C K
  ring

theorem val_snd (p a b z : ℝ²) (e : ℝ × ℝ) (hD : C p a b ≠ 0) (hz : C p a z ≠ 0) :
    val p e a z - val p e a b = C a b z / C p a b * (K p a e / C p a z) := by
  unfold val
  rw [div_sub_div _ _ hz hD, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero hz hD) (mul_ne_zero hD hz)]
  unfold C K
  ring

theorem val_symm (p a b : ℝ²) (e : ℝ × ℝ) : val p e b a = val p e a b := by
  unfold val
  rw [C_swap p a b, div_neg, ← neg_div, neg_sub]

theorem val_neg (p a b : ℝ²) (e : ℝ × ℝ) : val p (-e) a b = -val p e a b := by
  unfold val
  rw [K_neg, K_neg]
  ring

theorem val_dir (p r a b : ℝ²) (hD : C p a b ≠ 0) :
    val p (dir p r) a b - 1 = -C a b r / C p a b := by
  unfold val
  rw [K_dir, K_dir, div_sub_one hD]
  congr 1
  unfold C; ring

theorem mul_form {x d k g : ℝ} (hd : d ≠ 0) (hg : g ≠ 0) (h : x / d * (k / g) ≤ 0) :
    x * d * (k * g) ≤ 0 := by
  have h2 : x * d * (k * g) = x / d * (k / g) * (d ^ 2 * g ^ 2) := by field_simp
  have h3 := mul_nonneg (neg_nonneg.mpr h) (show (0 : ℝ) ≤ d ^ 2 * g ^ 2 by positivity)
  rw [h2]
  linarith

theorem hpp {k l : ℝ} (hk : 0 < k) (h : 0 ≤ k * l) : 0 ≤ l := by
  by_contra hc; push Not at hc; linarith [mul_neg_of_pos_of_neg hk hc]
theorem hpn {k l : ℝ} (hk : 0 < k) (h : k * l ≤ 0) : l ≤ 0 := by
  by_contra hc; push Not at hc; linarith [mul_pos hk hc]
theorem hnp {k l : ℝ} (hk : k < 0) (h : 0 ≤ k * l) : l ≤ 0 := by
  by_contra hc; push Not at hc; linarith [mul_neg_of_neg_of_pos hk hc]
theorem hnn {k l : ℝ} (hk : k < 0) (h : k * l ≤ 0) : 0 ≤ l := by
  by_contra hc; push Not at hc; linarith [mul_pos_of_neg_of_neg hk hc]

/-- Two lines through `a` that both contain `c` force `c = a`. -/
theorem eq_of_C {p a b c : ℝ²} (hD : C p a b ≠ 0) (h1 : C a b c = 0) (h2 : C p a c = 0) :
    c = a := by
  have e0 : (c 0 - a 0) * C p a b = 0 := by
    unfold C at h1 h2 ⊢
    linear_combination (-(a 0 - p 0)) * h1 + (b 0 - a 0) * h2
  have e1 : (c 1 - a 1) * C p a b = 0 := by
    unfold C at h1 h2 ⊢
    linear_combination (-(a 1 - p 1)) * h1 + (b 1 - a 1) * h2
  have f0 := (mul_eq_zero.mp e0).resolve_right hD
  have f1 := (mul_eq_zero.mp e1).resolve_right hD
  exact ext2 (by linarith) (by linarith)

theorem C_ne_of_line {p a b c : ℝ²} (hD : C p a b ≠ 0) (hl : C a b c = 0) (hca : c ≠ a) :
    C p a c ≠ 0 :=
  fun h2 => hca (eq_of_C hD hl h2)

theorem exists_mu {p x z : ℝ²} (hxp : x ≠ p) (h : C p x z = 0) :
    ∃ μ : ℝ, z 0 - p 0 = μ * (x 0 - p 0) ∧ z 1 - p 1 = μ * (x 1 - p 1) := by
  have hne : x 0 ≠ p 0 ∨ x 1 ≠ p 1 := by
    by_contra hc
    push Not at hc
    exact hxp (ext2 hc.1 hc.2)
  unfold C at h
  rcases hne with h0 | h1
  · have h0' : x 0 - p 0 ≠ 0 := sub_ne_zero.mpr h0
    refine ⟨(z 0 - p 0) / (x 0 - p 0), by field_simp, ?_⟩
    field_simp
    linarith
  · have h1' : x 1 - p 1 ≠ 0 := sub_ne_zero.mpr h1
    refine ⟨(z 1 - p 1) / (x 1 - p 1), ?_, by field_simp⟩
    field_simp
    linarith

/-- Membership in a line through two distinct points, in coordinates. -/
theorem mem_line_iff {x y z : ℝ²} (hxy : x ≠ y) : z ∈ line[ℝ, x, y] ↔ C x y z = 0 := by
  have hz : z = (z -ᵥ x) +ᵥ x := (vsub_vadd z x).symm
  rw [hz, vadd_left_mem_affineSpan_pair, ← hz]
  constructor
  · rintro ⟨t, ht⟩
    have h0 : t * (y 0 - x 0) = z 0 - x 0 := by
      have h := congrArg (fun v : ℝ² => v 0) ht
      simpa using h
    have h1 : t * (y 1 - x 1) = z 1 - x 1 := by
      have h := congrArg (fun v : ℝ² => v 1) ht
      simpa using h
    unfold C
    linear_combination (-(y 0 - x 0)) * h1 + (y 1 - x 1) * h0
  · intro h
    have hyx : y ≠ x := fun h' => hxy h'.symm
    obtain ⟨μ, h0, h1⟩ := exists_mu hyx h
    refine ⟨μ, ?_⟩
    apply ext2
    · simp; linarith
    · simp; linarith

theorem ordinary_of {s : Finset ℝ²} {a b : ℝ²} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (h : ∀ z ∈ s, C a b z = 0 → z = a ∨ z = b) : line[ℝ, a, b] ∈ ordinaryLines s := by
  rw [mem_ordinaryLines]
  refine ⟨⟨a, ha, b, hb, hab, rfl⟩, ?_⟩
  rw [Finset.card_eq_two]
  refine ⟨a, b, hab, ?_⟩
  ext z
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hzl⟩
    exact h z hz ((mem_line_iff hab).mp hzl)
  · rintro (h1 | h1)
    · rw [h1]; exact ⟨ha, left_mem_affineSpan_pair ℝ _ _⟩
    · rw [h1]; exact ⟨hb, right_mem_affineSpan_pair ℝ _ _⟩

/-- `a b` is a pair of points of `s`, not collinear with `p`, maximising `val`. -/
def IsMax (s : Finset ℝ²) (p : ℝ²) (e : ℝ × ℝ) (a b : ℝ²) : Prop :=
  a ∈ s ∧ b ∈ s ∧ C p a b ≠ 0 ∧
    ∀ a' ∈ s, ∀ b' ∈ s, C p a' b' ≠ 0 → val p e a' b' ≤ val p e a b

theorem exists_isMax (s : Finset ℝ²) (p : ℝ²) (e : ℝ × ℝ)
    (h : ∃ a ∈ s, ∃ b ∈ s, C p a b ≠ 0) : ∃ a b, IsMax s p e a b := by
  obtain ⟨a0, ha0, b0, hb0, h0⟩ := h
  have hne : ((s ×ˢ s).filter (fun q : ℝ² × ℝ² => C p q.1 q.2 ≠ 0)).Nonempty :=
    ⟨(a0, b0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha0, hb0⟩, h0⟩⟩
  obtain ⟨q, hq, hmax⟩ :=
    Finset.exists_max_image _ (fun q : ℝ² × ℝ² => val p e q.1 q.2) hne
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqa, hqb⟩ := Finset.mem_product.mp hq1
  exact ⟨q.1, q.2, hqa, hqb, hq2, fun a' ha' b' hb' h' =>
    hmax (a', b') (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha', hb'⟩, h'⟩)⟩

theorem IsMax.ineq_snd {s : Finset ℝ²} {p : ℝ²} {e : ℝ × ℝ} {a b : ℝ²} (h : IsMax s p e a b)
    {z : ℝ²} (hz : z ∈ s) : C a b z * C p a b * (K p b e * C p b z) ≤ 0 := by
  by_cases hzb : C p z b = 0
  · have h0 : C p b z = 0 := by rw [C_swap, hzb, neg_zero]
    rw [h0]; simp
  · have hz' : C p b z ≠ 0 := by rw [C_swap]; exact neg_ne_zero.mpr hzb
    have h1 := h.2.2.2 z hz b h.2.1 hzb
    have h2 := val_fst p a b z e h.2.2.1 hzb
    exact mul_form h.2.2.1 hz' (by rw [← h2]; linarith)

theorem IsMax.ineq_fst {s : Finset ℝ²} {p : ℝ²} {e : ℝ × ℝ} {a b : ℝ²} (h : IsMax s p e a b)
    {z : ℝ²} (hz : z ∈ s) : C a b z * C p a b * (K p a e * C p a z) ≤ 0 := by
  by_cases hza : C p a z = 0
  · rw [hza]; simp
  · have h1 := h.2.2.2 a h.1 z hz hza
    have h2 := val_snd p a b z e h.2.2.1 hza
    exact mul_form h.2.2.1 hza (by rw [← h2]; linarith)

theorem IsMax.replace_fst {s : Finset ℝ²} {p : ℝ²} {e : ℝ × ℝ} {a b : ℝ²} (h : IsMax s p e a b)
    {c : ℝ²} (hc : c ∈ s) (hl : C a b c = 0) (hcb : C p c b ≠ 0) : IsMax s p e c b := by
  have h2 := val_fst p a b c e h.2.2.1 hcb
  rw [hl, zero_div, zero_mul] at h2
  have h3 : val p e c b = val p e a b := by linarith
  exact ⟨hc, h.2.1, hcb, fun a' ha' b' hb' h' => by rw [h3]; exact h.2.2.2 a' ha' b' hb' h'⟩

theorem IsMax.replace_snd {s : Finset ℝ²} {p : ℝ²} {e : ℝ × ℝ} {a b : ℝ²} (h : IsMax s p e a b)
    {c : ℝ²} (hc : c ∈ s) (hl : C a b c = 0) (hac : C p a c ≠ 0) : IsMax s p e a c := by
  have h2 := val_snd p a b c e h.2.2.1 hac
  rw [hl, zero_div, zero_mul] at h2
  have h3 : val p e a c = val p e a b := by linarith
  exact ⟨h.1, hc, hac, fun a' ha' b' hb' h' => by rw [h3]; exact h.2.2.2 a' ha' b' hb' h'⟩

/-- A point `x` in the middle of a maximising pair has an empty line through `p`. -/
theorem IsMax.middle {s : Finset ℝ²} {p : ℝ²} {e : ℝ × ℝ} {y w : ℝ²} (h : IsMax s p e y w)
    {x : ℝ²} (hl : C y w x = 0) (hm : C p y x * K p y e * (C p w x * K p w e) < 0)
    (hxp : x ≠ p) : ∀ z ∈ s, C p x z = 0 → z = p ∨ z = x := by
  intro z hz hzx
  by_contra hne
  push Not at hne
  obtain ⟨μ, hμ0, hμ1⟩ := exists_mu hxp hzx
  have i1 := h.ineq_fst hz
  have i2 := h.ineq_snd hz
  have e1 : C p y z = μ * C p y x := by
    unfold C; linear_combination (y 0 - p 0) * hμ1 - (y 1 - p 1) * hμ0
  have e2 : C p w z = μ * C p w x := by
    unfold C; linear_combination (w 0 - p 0) * hμ1 - (w 1 - p 1) * hμ0
  have e3 : C y w z = (1 - μ) * C p y w := by
    unfold C at hl ⊢
    linear_combination (w 0 - y 0) * hμ1 - (w 1 - y 1) * hμ0 + μ * hl
  have hμz : μ ≠ 0 := by
    intro h0
    rw [h0] at hμ0 hμ1
    exact hne.1 (ext2 (by linarith) (by linarith))
  have hμo : μ ≠ 1 := by
    intro h0
    rw [h0] at hμ0 hμ1
    exact hne.2 (ext2 (by linarith) (by linarith))
  rw [e1, e3] at i1
  rw [e2, e3] at i2
  have hD := h.2.2.1
  have hne0 : (1 - μ) * μ * C p y w ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hμo)) hμz) (pow_ne_zero 2 hD)
  have tpos : 0 < ((1 - μ) * μ * C p y w ^ 2) ^ 2 :=
    (sq_nonneg _).lt_of_ne' (pow_ne_zero 2 hne0)
  have k1 := mul_nonneg_of_nonpos_of_nonpos i1 i2
  have k2 := mul_neg_of_pos_of_neg tpos hm
  linarith

theorem tri (p a b c : ℝ²) (e : ℝ × ℝ) (hab : C p a b ≠ 0) (hac : C p a c ≠ 0)
    (hbc : C p b c ≠ 0) (ka : K p a e ≠ 0) (kb : K p b e ≠ 0) (kc : K p c e ≠ 0) :
    C p a c * K p a e * (C p b c * K p b e) < 0 ∨
    C p c a * K p c e * (C p b a * K p b e) < 0 ∨
    C p a b * K p a e * (C p c b * K p c e) < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hprod := mul_nonneg (mul_nonneg h1 h2) h3
  rw [C_swap p a c, C_swap p a b, C_swap p b c] at hprod
  have hne : C p a b * C p a c * C p b c * K p a e * K p b e * K p c e ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hab hac) hbc) ka) kb) kc
  have hpos : 0 < (C p a b * C p a c * C p b c * K p a e * K p b e * K p c e) ^ 2 :=
    (sq_nonneg _).lt_of_ne' (pow_ne_zero 2 hne)
  linarith

/-- If `r` is in the middle of a maximising pair, lines on both sides of `r` exist. -/
theorem IsMax.bad {s : Finset ℝ²} {p : ℝ²} {e : ℝ × ℝ} {y w : ℝ²} (h : IsMax s p e y w)
    {r y' w' : ℝ²} (hl : C y w r = 0)
    (hm : C p y r * K p y e * (C p w r * K p w e) < 0)
    (hy' : y' ∈ s) (hy'p : y' ≠ p) (hy'y : y' ≠ y) (hyl : C p y y' = 0)
    (hw' : w' ∈ s) (hw'p : w' ≠ p) (hw'w : w' ≠ w) (hwl : C p w w' = 0) :
    C p y' w ≠ 0 ∧ C p y w' ≠ 0 ∧
    ((1 < val p (dir p r) y' w ∧ val p (dir p r) y w' < 1) ∨
     (val p (dir p r) y' w < 1 ∧ 1 < val p (dir p r) y w')) := by
  have hD := h.2.2.1
  have hyp : y ≠ p := by
    intro h0; rw [h0] at hD; exact hD (C_left _ _)
  have hwp : w ≠ p := by
    intro h0; rw [h0] at hD; exact hD (C_mid _ _)
  obtain ⟨μ, hμ0, hμ1⟩ := exists_mu hyp hyl
  obtain ⟨ν, hν0, hν1⟩ := exists_mu hwp hwl
  have hμz : μ ≠ 0 := by
    intro h0; rw [h0] at hμ0 hμ1
    exact hy'p (ext2 (by linarith) (by linarith))
  have hμo : μ ≠ 1 := by
    intro h0; rw [h0] at hμ0 hμ1
    exact hy'y (ext2 (by linarith) (by linarith))
  have hνz : ν ≠ 0 := by
    intro h0; rw [h0] at hν0 hν1
    exact hw'p (ext2 (by linarith) (by linarith))
  have hνo : ν ≠ 1 := by
    intro h0; rw [h0] at hν0 hν1
    exact hw'w (ext2 (by linarith) (by linarith))
  have c1 : C p y' w = μ * C p y w := by
    unfold C; linear_combination (w 1 - p 1) * hμ0 - (w 0 - p 0) * hμ1
  have c2 : C p w y' = -(μ * C p y w) := by rw [C_swap, c1]
  have c3 : C y w y' = (1 - μ) * C p y w := by
    unfold C; linear_combination (w 0 - y 0) * hμ1 - (w 1 - y 1) * hμ0
  have d1 : C p y w' = ν * C p y w := by
    unfold C; linear_combination (y 0 - p 0) * hν1 - (y 1 - p 1) * hν0
  have d3 : C y w w' = (1 - ν) * C p y w := by
    unfold C; linear_combination (w 0 - y 0) * hν1 - (w 1 - y 1) * hν0
  have hc1 : C p y' w ≠ 0 := by rw [c1]; exact mul_ne_zero hμz hD
  have hd1 : C p y w' ≠ 0 := by rw [d1]; exact mul_ne_zero hνz hD
  refine ⟨hc1, hd1, ?_⟩
  have m1 := h.2.2.2 y' hy' w h.2.1 hc1
  have v1 := val_fst p y w y' e hD hc1
  have m2 := h.2.2.2 y h.1 w' hw' hd1
  have v2 := val_snd p y w w' e hD hd1
  have r1 := val_fst p y w y' (dir p r) hD hc1
  have r2 := val_snd p y w w' (dir p r) hD hd1
  have r0 := val_dir p r y w hD
  rw [hl, neg_zero, zero_div] at r0
  rw [c3, c2] at v1 r1
  rw [d3, d1] at v2 r2
  rw [K_dir] at r1 r2
  set q1 : ℝ := (1 - μ) / (-(μ * C p y w)) with hq1
  set q2 : ℝ := (1 - ν) / (ν * C p y w) with hq2
  have hq1n : q1 ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hμo)) (neg_ne_zero.mpr (mul_ne_zero hμz hD))
  have hq2n : q2 ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hνo)) (mul_ne_zero hνz hD)
  have a1 : (1 - μ) * C p y w / C p y w * (K p w e / -(μ * C p y w)) = q1 * K p w e := by
    rw [hq1]; field_simp
  have a2 : (1 - ν) * C p y w / C p y w * (K p y e / (ν * C p y w)) = q2 * K p y e := by
    rw [hq2]; field_simp
  have b1 : (1 - μ) * C p y w / C p y w * (C p w r / -(μ * C p y w)) = q1 * C p w r := by
    rw [hq1]; field_simp
  have b2 : (1 - ν) * C p y w / C p y w * (C p y r / (ν * C p y w)) = q2 * C p y r := by
    rw [hq2]; field_simp
  rw [a1] at v1
  rw [a2] at v2
  rw [b1] at r1
  rw [b2] at r2
  have he1 : q1 * K p w e ≤ 0 := by linarith
  have he2 : q2 * K p y e ≤ 0 := by linarith
  have key := mul_nonneg_of_nonpos_of_nonpos he1 he2
  have hq12 : 0 < (q1 * q2) ^ 2 :=
    (sq_nonneg _).lt_of_ne' (pow_ne_zero 2 (mul_ne_zero hq1n hq2n))
  have hprod := mul_neg_of_pos_of_neg hq12 hm
  have hpos : 0 < q1 * K p w e * (q2 * K p y e) := by
    rcases key.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have : (q1 * q2) ^ 2 * (C p y r * K p y e * (C p w r * K p w e)) =
          q1 * C p w r * (q2 * C p y r) * (q1 * K p w e * (q2 * K p y e)) := by ring
      rw [this, ← h1, mul_zero] at hprod
      exact lt_irrefl _ hprod
  have huv : q1 * C p w r * (q2 * C p y r) < 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_nonneg hcon hpos.le
    linarith
  rcases mul_neg_iff.mp huv with ⟨u1, u2⟩ | ⟨u1, u2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- Both a line of height above 1 and one of height below 1, relative to `r`. -/
def Case1 (s : Finset ℝ²) (p r : ℝ²) : Prop :=
  (∃ a ∈ s, ∃ b ∈ s, C p a b ≠ 0 ∧ 1 < val p (dir p r) a b) ∧
  (∃ a ∈ s, ∃ b ∈ s, C p a b ≠ 0 ∧ val p (dir p r) a b < 1)

/-- A maximising line is ordinary. -/
theorem good_of_max {s : Finset ℝ²} {p r : ℝ²} {e : ℝ × ℝ} {a b : ℝ²}
    (hU : ∀ x ∈ s, x ≠ p → x ≠ r → ∃ x' ∈ s, x' ≠ p ∧ x' ≠ x ∧ C p x x' = 0)
    (h : IsMax s p e a b)
    (hg : ∀ x ∈ s, C a b x = 0 → K p x e ≠ 0)
    (hn : C a b r ≠ 0 ∨ ¬ Case1 s p r) :
    ∀ z ∈ s, C a b z = 0 → z = a ∨ z = b := by
  have hD := h.2.2.1
  have hnm : ∀ y w x : ℝ², IsMax s p e y w → x ∈ s → C a b x = 0 → C y w x = 0 →
      C p y x * K p y e * (C p w x * K p w e) < 0 → False := by
    intro y w x hyw hx hxl hl hm
    have hD' := hyw.2.2.1
    have hpyx : C p y x ≠ 0 := by
      intro h0; rw [h0] at hm; simp at hm
    have hpwx : C p w x ≠ 0 := by
      intro h0; rw [h0] at hm; simp at hm
    have hxp : x ≠ p := by
      intro h0; rw [h0] at hpyx; exact hpyx (C_mid _ _)
    have hfree := hyw.middle hl hm hxp
    by_cases hxr : x = r
    · rcases hn with hn | hn
      · rw [hxr] at hxl; exact hn hxl
      · apply hn
        have hyp : y ≠ p := by
          intro h0; rw [h0] at hD'; exact hD' (C_left _ _)
        have hwp : w ≠ p := by
          intro h0; rw [h0] at hD'; exact hD' (C_mid _ _)
        have hyr : y ≠ r := by
          intro h0; rw [h0, hxr] at hpyx; exact hpyx (C_right _ _)
        have hwr : w ≠ r := by
          intro h0; rw [h0, hxr] at hpwx; exact hpwx (C_right _ _)
        obtain ⟨y', hy', hy'p, hy'y, hyl⟩ := hU y hyw.1 hyp hyr
        obtain ⟨w', hw', hw'p, hw'w, hwl⟩ := hU w hyw.2.1 hwp hwr
        rw [hxr] at hl hm
        obtain ⟨n1, n2, hcase⟩ := hyw.bad hl hm hy' hy'p hy'y hyl hw' hw'p hw'w hwl
        rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2⟩
        · exact ⟨⟨y', hy', w, hyw.2.1, n1, c1⟩, ⟨y, hyw.1, w', hw', n2, c2⟩⟩
        · exact ⟨⟨y, hyw.1, w', hw', n2, c2⟩, ⟨y', hy', w, hyw.2.1, n1, c1⟩⟩
    · obtain ⟨x', hx', hx'p, hx'x, hxl'⟩ := hU x hx hxp hxr
      rcases hfree x' hx' hxl' with h1 | h1
      · exact hx'p h1
      · exact hx'x h1
  intro c hc hl
  by_contra hne
  push Not at hne
  obtain ⟨hca, hcb⟩ := hne
  have hac : C p a c ≠ 0 := C_ne_of_line hD hl hca
  have hbc : C p b c ≠ 0 := by
    have hD2 : C p b a ≠ 0 := by rw [C_swap]; exact neg_ne_zero.mpr hD
    have hl2 : C b a c = 0 := by rw [C_flip, hl, neg_zero]
    exact C_ne_of_line hD2 hl2 hcb
  have hcb' : C p c b ≠ 0 := by rw [C_swap]; exact neg_ne_zero.mpr hbc
  have hmax_cb := h.replace_fst hc hl hcb'
  have hmax_ac := h.replace_snd hc hl hac
  have ka := hg a h.1 (C_mid a b)
  have kb := hg b h.2.1 (C_right a b)
  have kc := hg c hc hl
  rcases tri p a b c e hD hac hbc ka kb kc with t | t | t
  · exact hnm a b c h hc hl hl t
  · have h0 : C c b a = 0 := by rw [C_rev, hl, neg_zero]
    exact hnm c b a hmax_cb h.1 (C_mid a b) h0 t
  · have h0 : C a c b = 0 := by rw [C_swap, hl, neg_zero]
    exact hnm a c b hmax_ac h.2.1 (C_right a b) h0 t

/-- The attachment relation of the reduction, written out. -/
def Att (s : Finset ℝ²) (w : ℝ²) (L : AffineSubspace ℝ ℝ²) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
    ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
      ∀ z ∈ s, ∃ a b c : ℝ,
        (![z 0, z 1, 1] : Fin 3 → ℝ) =
          a • (![p 0, p 1, 1] : Fin 3 → ℝ) + b • (ε • (![q 0, q 1, 1] : Fin 3 → ℝ)) +
            c • (δ • (![w 0, w 1, 1] : Fin 3 → ℝ)) ∧
        ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))

/-- An ordinary maximising line is attached to `p`. -/
theorem attached_of {s : Finset ℝ²} {p a b : ℝ²} {e : ℝ × ℝ} (h : IsMax s p e a b)
    (hord : ∀ z ∈ s, C a b z = 0 → z = a ∨ z = b) (ka : K p a e ≠ 0) (kb : K p b e ≠ 0) :
    Att s p (line[ℝ, a, b]) := by
  have hD := h.2.2.1
  have hab : a ≠ b := by
    intro h0; rw [h0] at hD; exact hD (C_right _ _)
  have hpl : p ∉ line[ℝ, a, b] := by
    rw [mem_line_iff hab, C_cycle p a b]; exact hD
  have hsign : ∀ z ∈ s,
      (0 ≤ -(C a b z * C p a b) ∧ 0 ≤ C p a z * K p a e ∧ 0 ≤ C p b z * K p b e) ∨
      (-(C a b z * C p a b) ≤ 0 ∧ C p a z * K p a e ≤ 0 ∧ C p b z * K p b e ≤ 0) := by
    intro z hz
    have i1 := h.ineq_fst hz
    have i2 := h.ineq_snd hz
    rcases lt_trichotomy (-(C a b z * C p a b)) 0 with hN | hN | hN
    · right
      exact ⟨hN.le, hnp hN (by linarith), hnp hN (by linarith)⟩
    · have hz0 : C a b z = 0 := by
        have h0 : C a b z * C p a b = 0 := by linarith
        exact (mul_eq_zero.mp h0).resolve_right hD
      rcases hord z hz hz0 with hza | hzb
      · have hY : C p a z * K p a e = 0 := by rw [hza, C_right, zero_mul]
        rcases le_total 0 (C p b z * K p b e) with hZ | hZ
        · left; exact ⟨hN.ge, hY.ge, hZ⟩
        · right; exact ⟨hN.le, hY.le, hZ⟩
      · have hZ : C p b z * K p b e = 0 := by rw [hzb, C_right, zero_mul]
        rcases le_total 0 (C p a z * K p a e) with hY | hY
        · left; exact ⟨hN.ge, hY, hZ.ge⟩
        · right; exact ⟨hN.le, hY, hZ.le⟩
    · left
      exact ⟨hN.le, hpp hN (by linarith), hpp hN (by linarith)⟩
  have hD2 : -(C p a b ^ 2) < 0 := neg_lt_zero.mpr ((sq_nonneg _).lt_of_ne' (pow_ne_zero 2 hD))
  have r1 : ∀ z : ℝ², -(C a b z * C p a b) = -(C p a b ^ 2) * (C a b z / C p a b) := by
    intro z; field_simp
  have r2 : ∀ z : ℝ², C p a z * K p a e = C p a b * K p a e * (C p a z / C p a b) := by
    intro z; field_simp
  have r3 : ∀ z : ℝ², C p b z * K p b e = -(C p a b * K p b e) * (-(C p b z) / C p a b) := by
    intro z; field_simp
  have hvec : ∀ z : ℝ², (![z 0, z 1, 1] : Fin 3 → ℝ) =
      (-(C p b z) / C p a b) • (![a 0, a 1, 1] : Fin 3 → ℝ) +
        (C p a z / C p a b) • (![b 0, b 1, 1] : Fin 3 → ℝ) +
          (C a b z / C p a b) • (![p 0, p 1, 1] : Fin 3 → ℝ) := by
    intro z
    ext i
    fin_cases i
    · simp; field_simp; unfold C; ring
    · simp; field_simp; unfold C; ring
    · simp; field_simp; unfold C; ring
  have hκa : C p a b * K p a e ≠ 0 := mul_ne_zero hD ka
  have hκb : -(C p a b * K p b e) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hD kb)
  refine ⟨a, h.1, b, h.2.1, hab, left_mem_affineSpan_pair ℝ a b,
    right_mem_affineSpan_pair ℝ a b, hpl, ?_⟩
  rcases lt_or_gt_of_ne hκb with hb | hb <;> rcases lt_or_gt_of_ne hκa with ha | ha
  · refine ⟨1, 1, by norm_num, by norm_num, fun z hz =>
      ⟨-(C p b z) / C p a b, C p a z / C p a b, C a b z / C p a b, ?_, ?_⟩⟩
    · rw [one_smul, one_smul]; exact hvec z
    · rcases hsign z hz with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
      · right
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hnp hb s3, hnp ha s2, hnp hD2 s1⟩
      · left
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hnn hb s3, hnn ha s2, hnn hD2 s1⟩
  · refine ⟨-1, 1, by norm_num, by norm_num, fun z hz =>
      ⟨-(C p b z) / C p a b, -(C p a z / C p a b), C a b z / C p a b, ?_, ?_⟩⟩
    · simp only [neg_smul, smul_neg, one_smul, neg_neg]; exact hvec z
    · rcases hsign z hz with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
      · right
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hnp hb s3, neg_nonpos.mpr (hpp ha s2), hnp hD2 s1⟩
      · left
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hnn hb s3, neg_nonneg.mpr (hpn ha s2), hnn hD2 s1⟩
  · refine ⟨-1, -1, by norm_num, by norm_num, fun z hz =>
      ⟨-(C p b z) / C p a b, -(C p a z / C p a b), -(C a b z / C p a b), ?_, ?_⟩⟩
    · simp only [neg_smul, smul_neg, one_smul, neg_neg]; exact hvec z
    · rcases hsign z hz with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
      · left
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hpp hb s3, neg_nonneg.mpr (hnp ha s2), neg_nonneg.mpr (hnp hD2 s1)⟩
      · right
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hpn hb s3, neg_nonpos.mpr (hnn ha s2), neg_nonpos.mpr (hnn hD2 s1)⟩
  · refine ⟨1, -1, by norm_num, by norm_num, fun z hz =>
      ⟨-(C p b z) / C p a b, C p a z / C p a b, -(C a b z / C p a b), ?_, ?_⟩⟩
    · simp only [neg_smul, smul_neg, one_smul, neg_neg]; exact hvec z
    · rcases hsign z hz with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
      · left
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hpp hb s3, hpp ha s2, neg_nonneg.mpr (hnp hD2 s1)⟩
      · right
        rw [r1 z] at s1; rw [r2 z] at s2; rw [r3 z] at s3
        exact ⟨hpn hb s3, hpn ha s2, neg_nonpos.mpr (hnn hD2 s1)⟩

theorem exists_generic (s : Finset ℝ²) (p : ℝ²) :
    ∃ e : ℝ × ℝ, ∀ x ∈ s, x ≠ p → K p x e ≠ 0 := by
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    (s.image (fun x : ℝ² => (x 1 - p 1) / (x 0 - p 0)))
  refine ⟨(1, t), fun x hx hxp h0 => ?_⟩
  have h0' : (x 0 - p 0) * t - (x 1 - p 1) * 1 = 0 := h0
  by_cases hx0 : x 0 = p 0
  · apply hxp
    apply ext2 hx0
    rw [hx0] at h0'
    linarith
  · apply ht
    rw [Finset.mem_image]
    refine ⟨x, hx, ?_⟩
    have hne : x 0 - p 0 ≠ 0 := sub_ne_zero.mpr hx0
    field_simp
    linarith

theorem main (s : Finset ℝ²) (hc : ¬ Collinear ℝ (s : Set ℝ²)) (p : ℝ²) (hp : p ∈ s)
    (hd : ((ordinaryLines s).filter (fun L => p ∈ L)).card = 1) :
    ∃ L1 ∈ ordinaryLines s, ∃ L2 ∈ ordinaryLines s, L1 ≠ L2 ∧ Att s p L1 ∧ Att s p L2 := by
  -- the unique ordinary line through p, and its other point r
  obtain ⟨L0, hL0⟩ := Finset.card_eq_one.mp hd
  have hL0m : L0 ∈ (ordinaryLines s).filter (fun L => p ∈ L) := by
    rw [hL0]; exact Finset.mem_singleton_self _
  obtain ⟨hL0O, hpL0⟩ := Finset.mem_filter.mp hL0m
  obtain ⟨-, hcard⟩ := mem_ordinaryLines.mp hL0O
  obtain ⟨x, y, hxy, hfil⟩ := Finset.card_eq_two.mp hcard
  have hall : ∀ z ∈ s, z ∈ L0 → z = x ∨ z = y := by
    intro z hz hzL
    have h0 : z ∈ s.filter (fun q => q ∈ L0) := Finset.mem_filter.mpr ⟨hz, hzL⟩
    rw [hfil] at h0
    simpa using h0
  have hxm : x ∈ s ∧ x ∈ L0 := by
    have h0 : x ∈ s.filter (fun q => q ∈ L0) := by rw [hfil]; simp
    exact Finset.mem_filter.mp h0
  have hym : y ∈ s ∧ y ∈ L0 := by
    have h0 : y ∈ s.filter (fun q => q ∈ L0) := by rw [hfil]; simp
    exact Finset.mem_filter.mp h0
  obtain ⟨r, hrs, hrL0, hrp, honly⟩ :
      ∃ r, r ∈ s ∧ r ∈ L0 ∧ r ≠ p ∧ ∀ z ∈ s, z ∈ L0 → z = p ∨ z = r := by
    rcases hall p hp hpL0 with h0 | h0
    · refine ⟨y, hym.1, hym.2, ?_, ?_⟩
      · rw [h0]; exact fun h1 => hxy h1.symm
      · intro z hz hzL; rw [h0]; exact hall z hz hzL
    · refine ⟨x, hxm.1, hxm.2, ?_, ?_⟩
      · rw [h0]; exact hxy
      · intro z hz hzL; rw [h0]; exact (hall z hz hzL).symm
  have hpr : p ≠ r := fun h0 => hrp h0.symm
  have hR : ∀ z ∈ s, C p r z = 0 → z = p ∨ z = r := by
    intro z hz hz0
    have h1 : z ∈ line[ℝ, p, r] := (mem_line_iff hpr).mpr hz0
    exact honly z hz (affineSpan_pair_le_of_mem_of_mem hpL0 hrL0 h1)
  have hU : ∀ x ∈ s, x ≠ p → x ≠ r → ∃ x' ∈ s, x' ≠ p ∧ x' ≠ x ∧ C p x x' = 0 := by
    intro x hx hxp hxr
    by_contra hno
    push Not at hno
    have hord : line[ℝ, p, x] ∈ ordinaryLines s :=
      ordinary_of hp hx (fun h0 => hxp h0.symm) (fun z hz hzl => by
        by_contra hh
        push Not at hh
        exact hno z hz hh.1 hh.2 hzl)
    have h1 : line[ℝ, p, x] ∈ (ordinaryLines s).filter (fun L => p ∈ L) :=
      Finset.mem_filter.mpr ⟨hord, left_mem_affineSpan_pair ℝ p x⟩
    rw [hL0, Finset.mem_singleton] at h1
    have hxL0 : x ∈ L0 := by rw [← h1]; exact right_mem_affineSpan_pair ℝ p x
    rcases honly x hx hxL0 with h2 | h2
    · exact hxp h2
    · exact hxr h2
  have hnc : ∃ x ∈ s, C p r x ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hc
    have hsub : (s : Set ℝ²) ⊆ {p, r} := by
      intro z hz
      rcases hR z hz (hno z hz) with h0 | h0
      · rw [h0]; simp
      · rw [h0]; simp
    exact Collinear.subset hsub (collinear_pair ℝ p r)
  obtain ⟨x0, hx0, hx0r⟩ := hnc
  have hpair : ∃ a ∈ s, ∃ b ∈ s, C p a b ≠ 0 := ⟨r, hrs, x0, hx0, hx0r⟩
  -- two maximisers (for e and -e) give two attached ordinary lines
  have fin : ∀ (e : ℝ × ℝ) (a b a' b' : ℝ²), IsMax s p e a b → IsMax s p (-e) a' b' →
      val p e a' b' < val p e a b →
      (∀ x ∈ s, C a b x = 0 → K p x e ≠ 0) → (∀ x ∈ s, C a' b' x = 0 → K p x e ≠ 0) →
      (C a b r ≠ 0 ∨ ¬ Case1 s p r) → (C a' b' r ≠ 0 ∨ ¬ Case1 s p r) →
      ∃ L1 ∈ ordinaryLines s, ∃ L2 ∈ ordinaryLines s, L1 ≠ L2 ∧ Att s p L1 ∧ Att s p L2 := by
    intro e a b a' b' h1 h2 hlt hg1 hg2 hn1 hn2
    have hg2' : ∀ x ∈ s, C a' b' x = 0 → K p x (-e) ≠ 0 := fun x hx hl => by
      rw [K_neg]; exact neg_ne_zero.mpr (hg2 x hx hl)
    have o1 := good_of_max hU h1 hg1 hn1
    have o2 := good_of_max hU h2 hg2' hn2
    have hab : a ≠ b := by
      intro h0; have hD := h1.2.2.1; rw [h0] at hD; exact hD (C_right _ _)
    have hab' : a' ≠ b' := by
      intro h0; have hD := h2.2.2.1; rw [h0] at hD; exact hD (C_right _ _)
    refine ⟨line[ℝ, a, b], ordinary_of h1.1 h1.2.1 hab o1, line[ℝ, a', b'],
      ordinary_of h2.1 h2.2.1 hab' o2, ?_,
      attached_of h1 o1 (hg1 a h1.1 (C_mid _ _)) (hg1 b h1.2.1 (C_right _ _)),
      attached_of h2 o2 (hg2' a' h2.1 (C_mid _ _)) (hg2' b' h2.2.1 (C_right _ _))⟩
    intro heq
    have ha' : a' ∈ line[ℝ, a, b] := by rw [heq]; exact left_mem_affineSpan_pair ℝ a' b'
    have hb' : b' ∈ line[ℝ, a, b] := by rw [heq]; exact right_mem_affineSpan_pair ℝ a' b'
    rw [mem_line_iff hab] at ha' hb'
    have e1 := o1 a' h2.1 ha'
    have e2 := o1 b' h2.2.1 hb'
    have hv : val p e a' b' = val p e a b := by
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact absurd (e1.trans e2.symm) hab'
      · rw [e1, e2]
      · rw [e1, e2]; exact val_symm p a b e
      · exact absurd (e1.trans e2.symm) hab'
    linarith
  by_cases hC1 : Case1 s p r
  · obtain ⟨⟨a1, ha1, b1, hb1, hD1, hgt⟩, ⟨a2, ha2, b2, hb2, hD2, hlt⟩⟩ := hC1
    obtain ⟨a, b, hmax⟩ := exists_isMax s p (dir p r) hpair
    obtain ⟨a', b', hmax'⟩ := exists_isMax s p (-(dir p r)) hpair
    have hv1 : 1 < val p (dir p r) a b := lt_of_lt_of_le hgt (hmax.2.2.2 a1 ha1 b1 hb1 hD1)
    have hv2 : val p (dir p r) a' b' < 1 := by
      have h0 := hmax'.2.2.2 a2 ha2 b2 hb2 hD2
      rw [val_neg, val_neg] at h0
      linarith
    have hr1 : C a b r ≠ 0 := by
      intro h0
      have h1 := val_dir p r a b hmax.2.2.1
      rw [h0, neg_zero, zero_div] at h1
      linarith
    have hr2 : C a' b' r ≠ 0 := by
      intro h0
      have h1 := val_dir p r a' b' hmax'.2.2.1
      rw [h0, neg_zero, zero_div] at h1
      linarith
    have gen : ∀ a b : ℝ², C p a b ≠ 0 → C a b r ≠ 0 →
        ∀ x ∈ s, C a b x = 0 → K p x (dir p r) ≠ 0 := by
      intro a b hD hr x hx hl
      rw [K_dir]
      intro h0
      have h0' : C p r x = 0 := by rw [C_swap, h0, neg_zero]
      rcases hR x hx h0' with h1 | h1
      · rw [h1] at hl
        exact hD (by rw [← C_cycle p a b]; exact hl)
      · rw [h1] at hl
        exact hr hl
    exact fin (dir p r) a b a' b' hmax hmax' (by linarith) (gen a b hmax.2.2.1 hr1)
      (gen a' b' hmax'.2.2.1 hr2) (Or.inl hr1) (Or.inl hr2)
  · obtain ⟨e, he⟩ := exists_generic s p
    obtain ⟨a, b, hmax⟩ := exists_isMax s p e hpair
    obtain ⟨a', b', hmax'⟩ := exists_isMax s p (-e) hpair
    have gen : ∀ a b : ℝ², C p a b ≠ 0 → ∀ x ∈ s, C a b x = 0 → K p x e ≠ 0 := by
      intro a b hD x hx hl
      apply he x hx
      intro hxp
      rw [hxp] at hl
      exact hD (by rw [← C_cycle p a b]; exact hl)
    have hx0p : x0 ≠ p := by
      intro h0; rw [h0] at hx0r; exact hx0r (C_mid _ _)
    have hx0r' : x0 ≠ r := by
      intro h0; rw [h0] at hx0r; exact hx0r (C_right _ _)
    obtain ⟨x1, hx1, hx1p, hx1x, hx1l⟩ := hU x0 hx0 hx0p hx0r'
    have hD0 : C p x0 r ≠ 0 := by rw [C_swap]; exact neg_ne_zero.mpr hx0r
    have hD1 : C p x1 r ≠ 0 := by
      intro h0
      have e0 : (x1 0 - p 0) * C p x0 r = 0 := by
        unfold C at h0 hx1l ⊢
        linear_combination (x0 0 - p 0) * h0 + (r 0 - p 0) * hx1l
      have e1 : (x1 1 - p 1) * C p x0 r = 0 := by
        unfold C at h0 hx1l ⊢
        linear_combination (x0 1 - p 1) * h0 + (r 1 - p 1) * hx1l
      have f0 := (mul_eq_zero.mp e0).resolve_right hD0
      have f1 := (mul_eq_zero.mp e1).resolve_right hD0
      exact hx1p (ext2 (by linarith) (by linarith))
    have hne : val p e x1 r ≠ val p e x0 r := by
      have hv := val_fst p x0 r x1 e hD0 hD1
      have hc3 : C x0 r x1 ≠ 0 := fun h0 => hx1x (eq_of_C hD0 h0 hx1l)
      have hkr : K p r e ≠ 0 := he r hrs hrp
      have hc4 : C p r x1 ≠ 0 := by rw [C_swap]; exact neg_ne_zero.mpr hD1
      intro heq
      rw [heq, sub_self] at hv
      exact mul_ne_zero (div_ne_zero hc3 hD0) (div_ne_zero hkr hc4) hv.symm
    have hlt : val p e a' b' < val p e a b := by
      have u1 := hmax.2.2.2 x1 hx1 r hrs hD1
      have u0 := hmax.2.2.2 x0 hx0 r hrs hD0
      have l1 := hmax'.2.2.2 x1 hx1 r hrs hD1
      have l0 := hmax'.2.2.2 x0 hx0 r hrs hD0
      rw [val_neg, val_neg] at l1 l0
      rcases lt_or_gt_of_ne hne with h0 | h0 <;> linarith
    exact fin e a b a' b' hmax hmax' hlt (gen a b hmax.2.2.1) (gen a' b' hmax'.2.2.1)
      (Or.inr hC1) (Or.inr hC1)

end OMA.KM

theorem OMA.solution : OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1.H2 := by
  intro s _ hc _ O d v attached A p hp hd
  obtain ⟨L1, h1, L2, h2, hne, a1, a2⟩ := OMA.KM.main s hc p hp hd
  exact Finset.one_lt_card.mpr
    ⟨L1, Finset.mem_filter.mpr ⟨h1, a1⟩, L2, Finset.mem_filter.mpr ⟨h2, a2⟩, hne⟩
