import OMAReductions.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1
import Mathlib

-- Extracted from @iskan-ai's merged proof of Erdős 210's Csima–Sawyer bound (PR #5154).
-- This part proves the Kelly–Moser attachment bound at a point of ordinary-line degree zero.

namespace Erdos210KM

open EuclideanGeometry Finset
open scoped BigOperators Classical

private noncomputable def det2 (u v : ℝ²) : ℝ :=
  u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0

private noncomputable def dot2 (u v : ℝ²) : ℝ :=
  u.ofLp 0 * v.ofLp 0 + u.ofLp 1 * v.ofLp 1

private noncomputable def perp (u : ℝ²) : ℝ² :=
  !₂[-u.ofLp 1, u.ofLp 0]

private lemma dot2_comm (u v : ℝ²) : dot2 u v = dot2 v u := by
  dsimp [dot2]; ring

private lemma dot2_add_left (u v w : ℝ²) : dot2 (u + v) w = dot2 u w + dot2 v w := by
  simp only [dot2, PiLp.add_apply]; ring

private lemma dot2_add_right (u v w : ℝ²) : dot2 u (v + w) = dot2 u v + dot2 u w := by
  simp only [dot2, PiLp.add_apply]; ring

private lemma dot2_sub_left (u v w : ℝ²) : dot2 (u - v) w = dot2 u w - dot2 v w := by
  simp only [dot2, PiLp.sub_apply]; ring

private lemma dot2_sub_right (u v w : ℝ²) : dot2 u (v - w) = dot2 u v - dot2 u w := by
  simp only [dot2, PiLp.sub_apply]; ring

private lemma dot2_smul_left (c : ℝ) (u v : ℝ²) : dot2 (c • u) v = c * dot2 u v := by
  simp only [dot2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma dot2_smul_right (c : ℝ) (u v : ℝ²) : dot2 u (c • v) = c * dot2 u v := by
  simp only [dot2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma dot2_self_pos {u : ℝ²} (hu : u ≠ 0) : 0 < dot2 u u := by
  have hnn : 0 ≤ dot2 u u := by dsimp [dot2]; nlinarith
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · exfalso; apply hu; ext i
    dsimp [dot2] at h0
    match i with
    | 0 => change u.ofLp 0 = 0; nlinarith
    | 1 => change u.ofLp 1 = 0; nlinarith
  · exact hpos

private lemma det2_anticomm (u v : ℝ²) : det2 u v = -det2 v u := by
  dsimp [det2]; ring

private lemma det2_self (u : ℝ²) : det2 u u = 0 := by
  dsimp [det2]; ring

private lemma det2_add_left (u v w : ℝ²) : det2 (u + v) w = det2 u w + det2 v w := by
  simp only [det2, PiLp.add_apply]; ring

private lemma det2_smul_left (c : ℝ) (u v : ℝ²) : det2 (c • u) v = c * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det2_smul_right (c : ℝ) (u v : ℝ²) : det2 u (c • v) = c * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma dot2_perp_left (u v : ℝ²) : dot2 (perp u) v = det2 u v := by
  simp only [dot2, perp, det2, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

private lemma dot2_perp_right (u v : ℝ²) : dot2 u (perp v) = -det2 u v := by
  simp only [dot2, perp, det2, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

private lemma dot2_self_perp (u : ℝ²) : dot2 u (perp u) = 0 := by
  rw [dot2_perp_right, det2_self, neg_zero]

private lemma perp_ne_zero {u : ℝ²} (hu : u ≠ 0) : perp u ≠ 0 := by
  intro h; apply hu; ext i
  have h0 := congrArg (fun x : ℝ² => x.ofLp 0) h
  have h1 := congrArg (fun x : ℝ² => x.ofLp 1) h
  simp only [perp, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  change -u.ofLp 1 = 0 at h0
  change u.ofLp 0 = 0 at h1
  match i with
  | 0 => exact h1
  | 1 => change u.ofLp 1 = 0; linarith

private lemma eq_of_det2_eq_zero {u v : ℝ²} (hu : u ≠ 0) (hdet : det2 u v = 0) :
    ∃ t : ℝ, v = t • u := by
  by_cases h0 : u.ofLp 0 ≠ 0
  · refine ⟨v.ofLp 0 / u.ofLp 0, ?_⟩
    ext i; match i with
    | 0 => change v.ofLp 0 = (v.ofLp 0 / u.ofLp 0) * u.ofLp 0; field_simp [h0]
    | 1 =>
      change v.ofLp 1 = (v.ofLp 0 / u.ofLp 0) * u.ofLp 1
      dsimp [det2] at hdet; field_simp [h0]; linarith
  · push Not at h0
    have h1 : u.ofLp 1 ≠ 0 := by
      intro h1; apply hu; ext i; match i with | 0 => exact h0 | 1 => exact h1
    refine ⟨v.ofLp 1 / u.ofLp 1, ?_⟩
    ext i; match i with
    | 0 =>
      change v.ofLp 0 = (v.ofLp 1 / u.ofLp 1) * u.ofLp 0
      dsimp [det2] at hdet; rw [h0] at hdet ⊢
      have hv0 : v.ofLp 0 = 0 := (mul_eq_zero.mp (show u.ofLp 1 * v.ofLp 0 = 0 by linarith)).resolve_left h1
      rw [hv0, mul_zero]
    | 1 => change v.ofLp 1 = (v.ofLp 1 / u.ofLp 1) * u.ofLp 1; field_simp [h1]

private lemma mem_line_iff_det2 {a b c : ℝ²} (hab : a ≠ b) :
    c ∈ line[ℝ, a, b] ↔ det2 (b - a) (c - a) = 0 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    have : AffineMap.lineMap a b t - a = t • (b - a) := by
      rw [AffineMap.lineMap_apply_module']; abel
    rw [this, det2_smul_right, det2_self, mul_zero]
  · intro hdet
    obtain ⟨t, ht⟩ := eq_of_det2_eq_zero (sub_ne_zero.mpr hab.symm) hdet
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    have : c = t • (b - a) + a := eq_add_of_sub_eq ht
    exact this.symm

private lemma basis_decomp {u v : ℝ²} (hdet : det2 u v ≠ 0) (z : ℝ²) :
    ∃ a b : ℝ, z = a • u + b • v := by
  set D := det2 u v
  refine ⟨det2 z v / D, det2 u z / D, ?_⟩
  ext i; match i with
  | 0 =>
    change z.ofLp 0 = (det2 z v / D) * u.ofLp 0 + (det2 u z / D) * v.ofLp 0
    field_simp [hdet]; dsimp [D, det2]; ring
  | 1 =>
    change z.ofLp 1 = (det2 z v / D) * u.ofLp 1 + (det2 u z / D) * v.ofLp 1
    field_simp [hdet]; dsimp [D, det2]; ring

private lemma decomp_orth {h : ℝ²} (hh : h ≠ 0) (r : ℝ²) (hr : dot2 h r = 1) :
    r = (1 / dot2 h h) • h + (dot2 (perp h) r / dot2 h h) • perp h := by
  set D := dot2 h h
  have hpos : 0 < D := dot2_self_pos hh
  have hne : D ≠ 0 := hpos.ne'
  ext i; match i with
  | 0 =>
    change r.ofLp 0 = (1 / D) * h.ofLp 0 + (dot2 (perp h) r / D) * (perp h).ofLp 0
    field_simp [hne]
    simp only [D, dot2, perp, Matrix.cons_val_zero, Matrix.cons_val_one] at hr ⊢
    linear_combination h.ofLp 0 * hr
  | 1 =>
    change r.ofLp 1 = (1 / D) * h.ofLp 1 + (dot2 (perp h) r / D) * (perp h).ofLp 1
    field_simp [hne]
    simp only [D, dot2, perp, Matrix.cons_val_zero, Matrix.cons_val_one] at hr ⊢
    linear_combination h.ofLp 1 * hr

/- ### Polar duality centered at `w` -/

private noncomputable def evalDual (w z u : ℝ²) : ℝ :=
  dot2 (z - w) u + 1

private noncomputable def dualInter (w p q : ℝ²) : ℝ² :=
  let dp := p - w
  let dq := q - w
  let D := det2 dp dq
  !₂[(dp.ofLp 1 - dq.ofLp 1) / D, (dq.ofLp 0 - dp.ofLp 0) / D]

private lemma evalDual_dualInter_left {w p q : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    evalDual w p (dualInter w p q) = 0 := by
  set D := det2 (p - w) (q - w)
  change (p - w).ofLp 0 * (((p - w).ofLp 1 - (q - w).ofLp 1) / D) +
    (p - w).ofLp 1 * (((q - w).ofLp 0 - (p - w).ofLp 0) / D) + 1 = 0
  field_simp [hdet]; dsimp [D, det2]; ring

private lemma evalDual_dualInter_right {w p q : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    evalDual w q (dualInter w p q) = 0 := by
  set D := det2 (p - w) (q - w)
  change (q - w).ofLp 0 * (((p - w).ofLp 1 - (q - w).ofLp 1) / D) +
    (q - w).ofLp 1 * (((q - w).ofLp 0 - (p - w).ofLp 0) / D) + 1 = 0
  field_simp [hdet]; dsimp [D, det2]; ring

private lemma dualInter_unique {w p q u : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0)
    (hp : evalDual w p u = 0) (hq : evalDual w q u = 0) :
    u = dualInter w p q := by
  set d := u - dualInter w p q
  have hp' : dot2 (p - w) d = 0 := by
    dsimp [d]; rw [dot2_sub_right]
    have h1 : dot2 (p - w) u = -1 := by dsimp [evalDual] at hp; linarith
    have h2 : dot2 (p - w) (dualInter w p q) = -1 := by
      have := evalDual_dualInter_left hdet; dsimp [evalDual] at this; linarith
    linarith
  have hq' : dot2 (q - w) d = 0 := by
    dsimp [d]; rw [dot2_sub_right]
    have h1 : dot2 (q - w) u = -1 := by dsimp [evalDual] at hq; linarith
    have h2 : dot2 (q - w) (dualInter w p q) = -1 := by
      have := evalDual_dualInter_right hdet; dsimp [evalDual] at this; linarith
    linarith
  have h0 : d = 0 := by
    dsimp [dot2] at hp' hq'
    dsimp [det2] at hdet
    ext i; match i with
    | 0 =>
      change d.ofLp 0 = 0
      have : ((p.ofLp 0 - w.ofLp 0) * (q.ofLp 1 - w.ofLp 1) - (p.ofLp 1 - w.ofLp 1) * (q.ofLp 0 - w.ofLp 0)) * d.ofLp 0 = 0 := by
        linear_combination (q.ofLp 1 - w.ofLp 1) * hp' - (p.ofLp 1 - w.ofLp 1) * hq'
      exact (mul_eq_zero.mp this).resolve_left hdet
    | 1 =>
      change d.ofLp 1 = 0
      have : ((p.ofLp 0 - w.ofLp 0) * (q.ofLp 1 - w.ofLp 1) - (p.ofLp 1 - w.ofLp 1) * (q.ofLp 0 - w.ofLp 0)) * d.ofLp 1 = 0 := by
        linear_combination (p.ofLp 0 - w.ofLp 0) * hq' - (q.ofLp 0 - w.ofLp 0) * hp'
      exact (mul_eq_zero.mp this).resolve_left hdet
  exact sub_eq_zero.mp h0

private lemma mem_line_iff_evalDual_zero {w p q z : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    z ∈ line[ℝ, p, q] ↔ evalDual w z (dualInter w p q) = 0 := by
  have hpq : p ≠ q := by
    intro h; subst h; exact hdet (det2_self _)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    have hsub : AffineMap.lineMap p q t - w = (1 - t) • (p - w) + t • (q - w) := by
      rw [AffineMap.lineMap_apply_module']; module
    dsimp [evalDual]
    rw [hsub, dot2_add_left, dot2_smul_left, dot2_smul_left]
    have h1 := evalDual_dualInter_left hdet
    have h2 := evalDual_dualInter_right hdet
    dsimp [evalDual] at h1 h2
    have h1' : dot2 (p - w) (dualInter w p q) = -1 := by linarith
    have h2' : dot2 (q - w) (dualInter w p q) = -1 := by linarith
    rw [h1', h2']; ring
  · intro hz
    obtain ⟨a, b, hab⟩ := basis_decomp hdet (z - w)
    have hsum : a + b = 1 := by
      dsimp [evalDual] at hz
      rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left] at hz
      have h1 := evalDual_dualInter_left hdet
      have h2 := evalDual_dualInter_right hdet
      dsimp [evalDual] at h1 h2
      have h1' : dot2 (p - w) (dualInter w p q) = -1 := by linarith
      have h2' : dot2 (q - w) (dualInter w p q) = -1 := by linarith
      rw [h1', h2'] at hz; linarith
    refine ⟨b, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    have ha : a = 1 - b := by linarith
    rw [ha] at hab
    have : z = b • (q - p) + p := by
      calc z = (z - w) + w := (sub_add_cancel z w).symm
        _ = (1 - b) • (p - w) + b • (q - w) + w := by rw [hab]
        _ = b • (q - p) + p := by module
    exact this.symm

private lemma not_mem_line_of_det2_ne_zero {w p q : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    w ∉ line[ℝ, p, q] := by
  rw [mem_line_iff_evalDual_zero hdet]
  simp [evalDual, dot2]

/- ### Perturbed maximization produces strictly exposed vertices -/

private lemma exists_strictly_exposed (s V : Finset ℝ²) (w : ℝ²)
    (hV : V.Nonempty) (h₀ : ℝ²) (hh₀ : h₀ ≠ 0) :
    ∃ X ∈ V, ∃ h : ℝ², h ≠ 0 ∧
      (∀ Y ∈ V, Y ≠ X → dot2 h Y < dot2 h X) ∧
      (∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0) ∧
      (∀ Y ∈ V, dot2 h₀ Y ≤ dot2 h₀ X) := by
  obtain ⟨X₀, hX₀V, hmax₀⟩ := V.exists_max_image (fun Y => dot2 h₀ Y) hV
  let V₀ := V.filter (fun Y => dot2 h₀ Y = dot2 h₀ X₀)
  have hV₀_ne : V₀.Nonempty := ⟨X₀, Finset.mem_filter.mpr ⟨hX₀V, rfl⟩⟩
  let h₁ := perp h₀
  obtain ⟨X, hXV₀, hmax₁⟩ := V₀.exists_max_image (fun Y => dot2 h₁ Y) hV₀_ne
  obtain ⟨hXV, hX_eq⟩ := Finset.mem_filter.mp hXV₀
  have hmax₀X : ∀ Y ∈ V, dot2 h₀ Y ≤ dot2 h₀ X := fun Y hY => hX_eq ▸ hmax₀ Y hY
  -- Compute gap threshold for ε > 0 so h = h₀ + ε • h₁ exposes X strictly
  let V_out := V.filter (fun Y => dot2 h₀ Y < dot2 h₀ X)
  have hε_bound : ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ∀ Y ∈ V_out, dot2 (h₀ + ε • h₁) Y < dot2 (h₀ + ε • h₁) X := by
    by_cases hout : V_out.Nonempty
    · have hexY : ∀ Y ∈ V_out, ∃ δY : ℝ, 0 < δY ∧
          ∀ ε : ℝ, 0 < ε → ε < δY → dot2 (h₀ + ε • h₁) Y < dot2 (h₀ + ε • h₁) X := by
        intro Y hY
        have hlt : dot2 h₀ Y < dot2 h₀ X := (Finset.mem_filter.mp hY).2
        let gap := dot2 h₀ X - dot2 h₀ Y
        have hgap : 0 < gap := sub_pos.mpr hlt
        let diff := dot2 h₁ Y - dot2 h₁ X
        refine ⟨gap / (|diff| + 1), by positivity, fun ε hε0 hεδ => ?_⟩
        rw [dot2_add_left, dot2_add_left, dot2_smul_left, dot2_smul_left]
        have h1 : ε * (|diff| + 1) < gap := (lt_div_iff₀ (by positivity : (0 : ℝ) < |diff| + 1)).mp hεδ
        have h2 : diff ≤ |diff| := le_abs_self _
        have h3 : ε * diff < gap := by nlinarith
        dsimp [gap, diff] at h3
        linarith
      choose δY hδY_pos hδY_ok using hexY
      let δs := V_out.attach.image (fun y => δY y.1 y.2)
      have hδs_ne : δs.Nonempty := by
        obtain ⟨y, hy⟩ := hout
        exact ⟨δY y hy, Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩⟩
      let δ := δs.min' hδs_ne
      have hδ_pos : 0 < δ := by
        obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (δs.min'_mem hδs_ne)
        change 0 < δs.min' hδs_ne; rw [← hy]; exact hδY_pos y.1 y.2
      refine ⟨δ, hδ_pos, fun ε hε0 hεδ Y hY => hδY_ok Y hY ε hε0 (lt_of_lt_of_le hεδ ?_)⟩
      exact δs.min'_le _ (Finset.mem_image.mpr ⟨⟨Y, hY⟩, Finset.mem_attach _ _, rfl⟩)
    · refine ⟨1, zero_lt_one, fun _ _ _ Y hY => absurd ⟨Y, hY⟩ hout⟩
  obtain ⟨δ, hδ_pos, hδ_ok⟩ := hε_bound
  -- Avoid the finitely many ε where det2 (h₀ + ε • h₁) (z - w) = 0
  let bad : Finset ℝ :=
    (s.filter (fun z => z ≠ w)).image (fun z => -det2 h₀ (z - w) / det2 h₁ (z - w))
  have hex_ε : ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε ∉ bad := by
    have hinf : (Set.Ioo (0 : ℝ) δ).Infinite := Set.Ioo_infinite hδ_pos
    obtain ⟨ε, hεI, hεB⟩ := (hinf.sdiff (bad.finite_toSet)).nonempty
    exact ⟨ε, hεI.1, hεI.2, hεB⟩
  obtain ⟨ε, hε0, hεδ, hε_not_bad⟩ := hex_ε
  let h := h₀ + ε • h₁
  have hh_ne : h ≠ 0 := by
    intro hzero
    have hdot := congrArg (fun v => dot2 h₀ v) hzero
    rw [dot2_add_right, dot2_smul_right, dot2_self_perp, mul_zero, add_zero] at hdot
    have hpos := dot2_self_pos hh₀
    have hz0 : dot2 h₀ 0 = 0 := by simp [dot2]
    linarith
  refine ⟨X, hXV, h, hh_ne, ?_, ?_, hmax₀X⟩
  · intro Y hYV hYX
    rcases lt_or_eq_of_le (hmax₀X Y hYV) with hlt | heq
    · exact hδ_ok ε hε0 hεδ Y (Finset.mem_filter.mpr ⟨hYV, hlt⟩)
    · have hYV₀ : Y ∈ V₀ := Finset.mem_filter.mpr ⟨hYV, heq.trans hX_eq⟩
      have hle₁ := hmax₁ Y hYV₀
      have hne₁ : dot2 h₁ Y ≠ dot2 h₁ X := by
        intro heq₁
        apply hYX
        have hdot0 : dot2 h₀ (Y - X) = 0 := by rw [dot2_sub_right]; linarith
        have hdot1 : dot2 (perp h₀) (Y - X) = 0 := by rw [dot2_sub_right]; linarith
        have hdet : det2 h₀ (Y - X) = 0 := by rw [← dot2_perp_left]; exact hdot1
        obtain ⟨t, ht⟩ := eq_of_det2_eq_zero hh₀ hdet
        rw [ht, dot2_smul_right] at hdot0
        have ht0 : t = 0 := (mul_eq_zero.mp hdot0).resolve_right (dot2_self_pos hh₀).ne'
        rw [ht0, zero_smul] at ht
        exact sub_eq_zero.mp ht
      have hlt₁ : dot2 h₁ Y < dot2 h₁ X := lt_of_le_of_ne hle₁ hne₁
      dsimp [h]
      rw [dot2_add_left, dot2_add_left, dot2_smul_left, dot2_smul_left]
      nlinarith
  · intro z hzs hzw hdet0
    dsimp [h] at hdet0
    rw [det2_add_left, det2_smul_left] at hdet0
    by_cases hd1 : det2 h₁ (z - w) = 0
    · rw [hd1, mul_zero, add_zero] at hdet0
      have hdot : dot2 h₀ (z - w) = 0 := by
        have : det2 (perp h₀) (z - w) = -dot2 h₀ (z - w) := by
          simp only [det2, perp, dot2, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
        linarith
      obtain ⟨t, ht⟩ := eq_of_det2_eq_zero hh₀ hdet0
      rw [ht, dot2_smul_right] at hdot
      have ht0 : t = 0 := (mul_eq_zero.mp hdot).resolve_right (dot2_self_pos hh₀).ne'
      rw [ht0, zero_smul] at ht
      exact hzw (sub_eq_zero.mp ht)
    · have hε_eq : ε = -det2 h₀ (z - w) / det2 h₁ (z - w) := by
        field_simp [hd1]; linarith
      apply hε_not_bad
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzs, hzw⟩, hε_eq.symm⟩

/- ### Main Kelly–Moser local attachment theorem -/

private lemma exists_three_directions {s : Finset ℝ²} (hcol : ¬ Collinear ℝ (s : Set ℝ²))
    (hno2 : ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M))
    {w : ℝ²} (hw : w ∈ s) :
    ∃ p₁ ∈ s, ∃ p₂ ∈ s, ∃ p₃ ∈ s,
      det2 (p₁ - w) (p₂ - w) ≠ 0 ∧ det2 (p₁ - w) (p₃ - w) ≠ 0 ∧ det2 (p₂ - w) (p₃ - w) ≠ 0 := by
  have hex1 : ∃ p₁ ∈ s, p₁ ≠ w := by
    by_contra! hall
    apply hcol
    refine (collinear_singleton ℝ w).subset fun z hz => ?_
    simp [hall z hz]
  obtain ⟨p₁, hp₁s, hp₁ne⟩ := hex1
  have hL1 : Module.finrank ℝ (line[ℝ, w, p₁]).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₁ne.symm)]
  have hex2 : ∃ p₂ ∈ s, p₂ ∉ line[ℝ, w, p₁] := by
    by_contra! hall
    apply hcol
    rw [collinear_iff_finrank_le_one]
    have hle : vectorSpan ℝ (s : Set ℝ²) ≤ (line[ℝ, w, p₁]).direction := by
      rw [← direction_affineSpan]
      exact AffineSubspace.direction_le (affineSpan_le.mpr fun z hz => hall z hz)
    exact (Submodule.finrank_mono hle).trans hL1.le
  obtain ⟨p₂, hp₂s, hp₂not⟩ := hex2
  have hp₂ne : p₂ ≠ w := fun h => hp₂not (h ▸ left_mem_affineSpan_pair ℝ w p₁)
  have hL2 : Module.finrank ℝ (line[ℝ, w, p₂]).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₂ne.symm)]
  have hex3 : ∃ p₃ ∈ s, p₃ ∉ line[ℝ, w, p₁] ∧ p₃ ∉ line[ℝ, w, p₂] := by
    by_contra! hall
    apply hno2
    refine ⟨line[ℝ, w, p₁], line[ℝ, w, p₂], hL1, hL2, fun z hz => ?_⟩
    by_cases h1 : z ∈ line[ℝ, w, p₁]
    · exact Or.inl h1
    · exact Or.inr (hall z hz h1)
  obtain ⟨p₃, hp₃s, hp₃not1, hp₃not2⟩ := hex3
  refine ⟨p₁, hp₁s, p₂, hp₂s, p₃, hp₃s, ?_, ?_, ?_⟩
  · exact (mem_line_iff_det2 hp₁ne.symm).not.mp hp₂not
  · exact (mem_line_iff_det2 hp₁ne.symm).not.mp hp₃not1
  · exact (mem_line_iff_det2 hp₂ne.symm).not.mp hp₃not2

/-- The dual vertex set `V` of all pairwise intersections of dual lines `ℓ_p, ℓ_q` (`p, q ∈ s \ {w}`). -/
private noncomputable def dualVerts (s : Finset ℝ²) (w : ℝ²) : Finset ℝ² :=
  ((s ×ˢ s).filter (fun pq => det2 (pq.1 - w) (pq.2 - w) ≠ 0)).image (fun pq => dualInter w pq.1 pq.2)

private lemma dualVerts_not_collinear {s : Finset ℝ²} (hcol : ¬ Collinear ℝ (s : Set ℝ²))
    (hno2 : ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M))
    {w : ℝ²} (hw : w ∈ s) :
    ¬ Collinear ℝ (dualVerts s w : Set ℝ²) := by
  obtain ⟨p₁, hp₁s, p₂, hp₂s, p₃, hp₃s, h12, h13, h23⟩ :=
    exists_three_directions hcol hno2 hw
  have hmemV : ∀ {a b : ℝ²}, a ∈ s → b ∈ s → det2 (a - w) (b - w) ≠ 0 →
      dualInter w a b ∈ dualVerts s w := fun {a b} ha hb hd =>
    Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hd⟩, rfl⟩
  let X12 := dualInter w p₁ p₂
  let X13 := dualInter w p₁ p₃
  let X23 := dualInter w p₂ p₃
  have hX12 : X12 ∈ dualVerts s w := hmemV hp₁s hp₂s h12
  have hX13 : X13 ∈ dualVerts s w := hmemV hp₁s hp₃s h13
  have hX23 : X23 ∈ dualVerts s w := hmemV hp₂s hp₃s h23
  intro hVcol
  -- Case 1: all points of dualVerts equal X12
  by_cases hall_eq : ∀ X ∈ dualVerts s w, X = X12
  · -- Then every z ∈ s \ {w} lies on line[p₁, p₂]
    have hp₁p₂ : p₁ ≠ p₂ := fun h => h12 (h ▸ det2_self _)
    have hp₁w : p₁ ≠ w := fun h => h12 (by rw [h, sub_self]; simp [det2])
    have hL12 : Module.finrank ℝ (line[ℝ, p₁, p₂]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₁p₂)]
    have hLw1 : Module.finrank ℝ (line[ℝ, w, p₁]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₁w.symm)]
    apply hno2
    refine ⟨line[ℝ, p₁, p₂], line[ℝ, w, p₁], hL12, hLw1, fun z hz => ?_⟩
    by_cases hzw : z = w
    · exact Or.inr (hzw ▸ left_mem_affineSpan_pair ℝ w p₁)
    · by_cases hdz1 : det2 (p₁ - w) (z - w) = 0
      · exact Or.inr ((mem_line_iff_det2 hp₁w.symm).mpr hdz1)
      · left
        rw [mem_line_iff_evalDual_zero h12]
        have hXz : dualInter w p₁ z = dualInter w p₁ p₂ := hall_eq _ (hmemV hp₁s hz hdz1)
        rw [← hXz]
        exact evalDual_dualInter_right hdz1
  · -- There exists X' ∈ dualVerts with X' ≠ X12
    push Not at hall_eq
    obtain ⟨X', hX'V, hX'ne⟩ := hall_eq
    -- Every X ∈ dualVerts lies on line[X12, X']
    have honM : ∀ X ∈ dualVerts s w, X ∈ line[ℝ, X12, X'] := fun X hXV =>
      hVcol.mem_affineSpan_of_mem_of_ne hX12 hX'V hXV hX'ne.symm
    -- Show X12 = X13 = X23
    have hX13_eq : X13 = X12 := by
      by_contra hne
      -- Both X12, X13 lie on line[X12, X'] and satisfy evalDual w p₁ _ = 0
      -- Hence every point of line[X12, X'] satisfies evalDual w p₁ _ = 0
      have hp1_on_M : ∀ Y ∈ line[ℝ, X12, X'], evalDual w p₁ Y = 0 := by
        intro Y hY
        have hM_eq : line[ℝ, X12, X'] = line[ℝ, X12, X13] :=
          (affineSpan_pair_eq_of_mem_of_mem_of_ne
            (left_mem_affineSpan_pair ℝ X12 X') (honM X13 hX13) (Ne.symm hne)).symm
        rw [hM_eq, mem_affineSpan_pair_iff_exists_lineMap_eq] at hY
        obtain ⟨t, rfl⟩ := hY
        have hsub : AffineMap.lineMap X12 X13 t = (1 - t) • X12 + t • X13 := by
          rw [AffineMap.lineMap_apply_module']; module
        dsimp [evalDual]
        rw [hsub, dot2_add_right, dot2_smul_right, dot2_smul_right]
        have e1 : dot2 (p₁ - w) X12 + 1 = 0 := evalDual_dualInter_left h12
        have e2 : dot2 (p₁ - w) X13 + 1 = 0 := evalDual_dualInter_left h13
        linear_combination (1 - t) * e1 + t * e2
      -- Since X23 ∈ line[X12, X'], evalDual w p₁ X23 = 0, so X23 = X12 = X13!
      have he1 : evalDual w p₁ X23 = 0 := hp1_on_M X23 (honM X23 hX23)
      have h23_12 : X23 = X12 := dualInter_unique h12 he1 (evalDual_dualInter_left h23)
      have h23_13 : X23 = X13 := dualInter_unique h13 he1 (evalDual_dualInter_right h23)
      exact hne (h23_13.symm.trans h23_12)
    have hX23_eq : X23 = X12 := by
      have hp2 : evalDual w p₂ X12 = 0 := evalDual_dualInter_right h12
      have hp3 : evalDual w p₃ X12 = 0 := by rw [← hX13_eq]; exact evalDual_dualInter_right h13
      exact (dualInter_unique h23 hp2 hp3).symm
    -- Now X12 lies on ℓ_{p₁}, ℓ_{p₂}, ℓ_{p₃} and X' ≠ X12 lies on M = line[X12, X'].
    -- At most one of ℓ_{p₁}, ℓ_{p₂}, ℓ_{p₃} contains X'!
    have hnot_two : ∀ {a b : ℝ²}, det2 (a - w) (b - w) ≠ 0 →
        evalDual w a X12 = 0 → evalDual w b X12 = 0 →
        ¬ (evalDual w a X' = 0 ∧ evalDual w b X' = 0) := by
      rintro a b hab ha12 hb12 ⟨ha', hb'⟩
      have h1 : X12 = dualInter w a b := dualInter_unique hab ha12 hb12
      have h2 : X' = dualInter w a b := dualInter_unique hab ha' hb'
      exact hX'ne (h2.trans h1.symm)
    -- Therefore we can pick two of {p₁, p₂, p₃}, say q₁, q₂, with evalDual w q₁ X' ≠ 0 and evalDual w q₂ X' ≠ 0
    have hex_pair : ∃ q₁ ∈ s, ∃ q₂ ∈ s, det2 (q₁ - w) (q₂ - w) ≠ 0 ∧
        evalDual w q₁ X12 = 0 ∧ evalDual w q₂ X12 = 0 ∧
        evalDual w q₁ X' ≠ 0 ∧ evalDual w q₂ X' ≠ 0 := by
      have e1 : evalDual w p₁ X12 = 0 := evalDual_dualInter_left h12
      have e2 : evalDual w p₂ X12 = 0 := evalDual_dualInter_right h12
      have e3 : evalDual w p₃ X12 = 0 := hX13_eq ▸ evalDual_dualInter_right h13
      by_cases h1' : evalDual w p₁ X' = 0
      · have h2' : evalDual w p₂ X' ≠ 0 := fun h => hnot_two h12 e1 e2 ⟨h1', h⟩
        have h3' : evalDual w p₃ X' ≠ 0 := fun h => hnot_two h13 e1 e3 ⟨h1', h⟩
        exact ⟨p₂, hp₂s, p₃, hp₃s, h23, e2, e3, h2', h3'⟩
      · by_cases h2' : evalDual w p₂ X' = 0
        · have h3' : evalDual w p₃ X' ≠ 0 := fun h => hnot_two h23 e2 e3 ⟨h2', h⟩
          exact ⟨p₁, hp₁s, p₃, hp₃s, h13, e1, e3, h1', h3'⟩
        · exact ⟨p₁, hp₁s, p₂, hp₂s, h12, e1, e2, h1', h2'⟩
    obtain ⟨q₁, hq₁s, q₂, hq₂s, hq12, eq1, eq2, hq1', hq2'⟩ := hex_pair
    -- Any Y ∈ line[X12, X'] with evalDual w qᵢ Y = 0 must equal X12!
    have huniq_on_M : ∀ {q Y : ℝ²}, evalDual w q X12 = 0 → evalDual w q X' ≠ 0 →
        Y ∈ line[ℝ, X12, X'] → evalDual w q Y = 0 → Y = X12 := by
      intro q Y hq0 hqne hYM hqY
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hYM
      obtain ⟨t, rfl⟩ := hYM
      have hsub : AffineMap.lineMap X12 X' t = (1 - t) • X12 + t • X' := by
        rw [AffineMap.lineMap_apply_module']; module
      dsimp [evalDual] at hq0 hqne hqY
      rw [hsub, dot2_add_right, dot2_smul_right, dot2_smul_right] at hqY
      have ht0 : t = 0 := by
        have : t * (dot2 (q - w) X' + 1) = 0 := by linear_combination hqY - (1 - t) * hq0
        exact (mul_eq_zero.mp this).resolve_right hqne
      simp [ht0]
    -- Hence EVERY z ∈ s \ {w} satisfies evalDual w z X12 = 0!
    have hall_zero : ∀ z ∈ s, z ≠ w → evalDual w z X12 = 0 := by
      intro z hzs hzw
      by_cases hd1 : det2 (q₁ - w) (z - w) = 0
      · have hd2 : det2 (q₂ - w) (z - w) ≠ 0 := by
          have hq1w : q₁ - w ≠ 0 := fun h => hq12 (by rw [h]; simp [det2])
          obtain ⟨t, ht⟩ := eq_of_det2_eq_zero hq1w hd1
          have ht0 : t ≠ 0 := fun h => hzw (sub_eq_zero.mp (by rw [ht, h, zero_smul]))
          rw [ht, det2_smul_right, det2_anticomm]
          exact mul_ne_zero ht0 (neg_ne_zero.mpr hq12)
        have hY : dualInter w q₂ z = X12 :=
          huniq_on_M eq2 hq2' (honM _ (hmemV hq₂s hzs hd2)) (evalDual_dualInter_left hd2)
        rw [← hY]; exact evalDual_dualInter_right hd2
      · have hY : dualInter w q₁ z = X12 :=
          huniq_on_M eq1 hq1' (honM _ (hmemV hq₁s hzs hd1)) (evalDual_dualInter_left hd1)
        rw [← hY]; exact evalDual_dualInter_right hd1
    -- Contradiction: X' ∈ dualVerts must equal X12!
    obtain ⟨⟨a, b⟩, habf, rfl⟩ := Finset.mem_image.mp hX'V
    obtain ⟨habp, hdet_ab⟩ := Finset.mem_filter.mp habf
    obtain ⟨has, hbs⟩ := Finset.mem_product.mp habp
    have haw : a ≠ w := fun h => hdet_ab (by rw [h, sub_self]; simp [det2])
    have hbw : b ≠ w := fun h => hdet_ab (by rw [h, sub_self]; simp [det2])
    exact hX'ne (dualInter_unique hdet_ab (hall_zero a has haw) (hall_zero b hbs hbw)).symm

/-- Given a strictly exposed vertex `X ∈ dualVerts s w` with supporting normal `h`,
the normalized ray direction `r_z` along `ℓ_z` has `dot2 (z - w) r_z = 0` and `dot2 h r_z = 1`. -/
private noncomputable def rayDir (w h z : ℝ²) : ℝ² :=
  (1 / (-det2 h (z - w))) • perp (z - w)

private lemma dot2_rayDir_self {w h z : ℝ²} :
    dot2 (z - w) (rayDir w h z) = 0 := by
  rw [rayDir, dot2_smul_right, dot2_self_perp, mul_zero]

private lemma dot2_h_rayDir {w h z : ℝ²} (hdet : det2 h (z - w) ≠ 0) :
    dot2 h (rayDir w h z) = 1 := by
  rw [rayDir, dot2_smul_right, dot2_perp_right]
  field_simp [hdet]

/-- Slope coordinate of `rayDir w h z` along `perp h`. -/
private noncomputable def raySlope (w h z : ℝ²) : ℝ :=
  dot2 (perp h) (rayDir w h z) / dot2 h h

private lemma rayDir_sub_eq {w h a b : ℝ²} (hh : h ≠ 0)
    (ha : det2 h (a - w) ≠ 0) (hb : det2 h (b - w) ≠ 0) :
    rayDir w h a - rayDir w h b = (raySlope w h a - raySlope w h b) • perp h := by
  have ha' := decomp_orth hh (rayDir w h a) (dot2_h_rayDir ha)
  have hb' := decomp_orth hh (rayDir w h b) (dot2_h_rayDir hb)
  dsimp [raySlope]
  conv_lhs => rw [ha', hb']
  module

private lemma dot2_rayDir_eq {w h a b : ℝ²} (hh : h ≠ 0)
    (ha : det2 h (a - w) ≠ 0) (hb : det2 h (b - w) ≠ 0) :
    dot2 (b - w) (rayDir w h a) = (raySlope w h a - raySlope w h b) * dot2 (b - w) (perp h) := by
  have hsub := rayDir_sub_eq hh ha hb
  have : rayDir w h a = (raySlope w h a - raySlope w h b) • perp h + rayDir w h b :=
    eq_add_of_sub_eq hsub
  rw [this, dot2_add_right, dot2_rayDir_self, add_zero, dot2_smul_right]

private lemma raySlope_ne_of_ne_through_X {w h X a b : ℝ²} (hh : h ≠ 0)
    (ha : det2 h (a - w) ≠ 0) (hb : det2 h (b - w) ≠ 0)
    (haX : evalDual w a X = 0) (hbX : evalDual w b X = 0) (hab : a ≠ b) :
    raySlope w h a ≠ raySlope w h b := by
  intro heq
  have hreq : rayDir w h a = rayDir w h b := by
    have := rayDir_sub_eq hh ha hb
    rw [heq, sub_self, zero_smul] at this
    exact sub_eq_zero.mp this
  have hdot : dot2 (a - w) (rayDir w h b) = 0 := hreq ▸ dot2_rayDir_self
  rw [rayDir, dot2_smul_right, dot2_perp_right] at hdot
  have hdet0 : det2 (a - w) (b - w) = 0 := by
    have := (mul_eq_zero.mp hdot).resolve_left (by simp [hb])
    linarith
  have haw : a - w ≠ 0 := fun h0 => ha (by rw [h0]; simp [det2])
  obtain ⟨t, ht⟩ := eq_of_det2_eq_zero haw hdet0
  dsimp [evalDual] at haX hbX
  rw [ht, dot2_smul_left] at hbX
  have haX' : dot2 (a - w) X = -1 := by linarith
  rw [haX'] at hbX
  have ht1 : t = 1 := by linarith
  rw [ht1, one_smul] at ht
  exact hab (sub_left_inj.mp ht.symm)

/-- Claim A: At a strictly exposed vertex `X` with supporting normal `h`, if three distinct points
`p₁, p₂, p₃ ∈ s \ {w}` pass through `X` with `raySlope p₁ < raySlope p₂ < raySlope p₃`, then
`p₂` has NO parallel partner in `s \ {w}` (i.e., `line[w, p₂]` is an ordinary line of `s`). -/
private lemma no_parallel_of_middle_at_exposed {s : Finset ℝ²} {w X h p₁ p₂ p₃ : ℝ²}
    (hh : h ≠ 0)
    (hmax : ∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X)
    (hdet : ∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0)
    (hp₁ : p₁ ∈ s) (hp₁w : p₁ ≠ w) (hp₂ : p₂ ∈ s) (hp₂w : p₂ ≠ w) (hp₃ : p₃ ∈ s) (hp₃w : p₃ ≠ w)
    (hX₁ : evalDual w p₁ X = 0) (hX₂ : evalDual w p₂ X = 0) (hX₃ : evalDual w p₃ X = 0)
    (hs12 : raySlope w h p₁ < raySlope w h p₂) (hs23 : raySlope w h p₂ < raySlope w h p₃) :
    ∀ z ∈ s, z ≠ w → z ≠ p₂ → det2 (p₂ - w) (z - w) ≠ 0 := by
  intro z hzs hzw hzp2 hpar
  obtain ⟨lam, hlam⟩ := eq_of_det2_eq_zero (sub_ne_zero.mpr hp₂w) hpar
  have hlam0 : lam ≠ 0 := fun h0 => hzw (sub_eq_zero.mp (by rw [hlam, h0, zero_smul]))
  have hlam1 : lam ≠ 1 := fun h1 => hzp2 (sub_left_inj.mp (by rw [hlam, h1, one_smul]))
  have hd1 := hdet p₁ hp₁ hp₁w
  have hd2 := hdet p₂ hp₂ hp₂w
  have hd3 := hdet p₃ hp₃ hp₃w
  have hdp2_perp : dot2 (p₂ - w) (perp h) ≠ 0 := by
    rw [dot2_perp_right, det2_anticomm, neg_neg]; exact hd2
  have hg1 : dot2 (p₂ - w) (rayDir w h p₁) = (raySlope w h p₁ - raySlope w h p₂) * dot2 (p₂ - w) (perp h) :=
    dot2_rayDir_eq hh hd1 hd2
  have hg3 : dot2 (p₂ - w) (rayDir w h p₃) = (raySlope w h p₃ - raySlope w h p₂) * dot2 (p₂ - w) (perp h) :=
    dot2_rayDir_eq hh hd3 hd2
  have hprod_neg : dot2 (p₂ - w) (rayDir w h p₁) * dot2 (p₂ - w) (rayDir w h p₃) < 0 := by
    rw [hg1, hg3]
    have hsq : 0 < dot2 (p₂ - w) (perp h) ^ 2 := sq_pos_of_ne_zero hdp2_perp
    have hss : (raySlope w h p₁ - raySlope w h p₂) * (raySlope w h p₃ - raySlope w h p₂) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have heq : (raySlope w h p₁ - raySlope w h p₂) * dot2 (p₂ - w) (perp h) *
        ((raySlope w h p₃ - raySlope w h p₂) * dot2 (p₂ - w) (perp h)) =
        ((raySlope w h p₁ - raySlope w h p₂) * (raySlope w h p₃ - raySlope w h p₂)) *
        dot2 (p₂ - w) (perp h) ^ 2 := by ring
    rw [heq]
    exact mul_neg_of_neg_of_pos hss hsq
  have h1m : 1 - 1 / lam ≠ 0 := by
    intro h0; apply hlam1; field_simp [hlam0] at h0; linarith
  -- Helper: if t > 0 solves evalDual w z (X + t • rayDir w h p) = 0, contradiction with hmax
  have kill : ∀ p : ℝ², p ∈ s → p ≠ w → evalDual w p X = 0 →
      det2 (p₂ - w) (p - w) ≠ 0 →
      0 < (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p) → False := by
    intro p hps hpw hXp hdet_p2p htpos
    set t := (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p)
    have hdp_ne : dot2 (p₂ - w) (rayDir w h p) ≠ 0 := by
      intro h0; simp [t, h0] at htpos
    have hdet_zp : det2 (z - w) (p - w) ≠ 0 := by
      rw [hlam, det2_smul_left]; exact mul_ne_zero hlam0 hdet_p2p
    let Y := X + t • rayDir w h p
    have hYp : evalDual w p Y = 0 := by
      dsimp [evalDual, Y]; rw [dot2_add_right, dot2_smul_right, dot2_rayDir_self, mul_zero, add_zero]
      exact hXp
    have hYz : evalDual w z Y = 0 := by
      dsimp [evalDual, Y]
      rw [hlam, dot2_smul_left, dot2_add_right, dot2_smul_right]
      have hX2' : dot2 (p₂ - w) X = -1 := by dsimp [evalDual] at hX₂; linarith
      rw [hX2']
      dsimp [t]
      field_simp [hlam0, hdp_ne]; ring
    have hY_eq : Y = dualInter w z p := dualInter_unique hdet_zp hYz hYp
    have hYV : Y ∈ dualVerts s w := by
      rw [hY_eq]
      exact Finset.mem_image.mpr ⟨(z, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzs, hps⟩, hdet_zp⟩, rfl⟩
    have hdotY : dot2 h Y = dot2 h X + t := by
      dsimp [Y]; rw [dot2_add_right, dot2_smul_right, dot2_h_rayDir (hdet p hps hpw), mul_one]
    have hYne : Y ≠ X := fun h => by rw [h] at hdotY; linarith
    have hlt := hmax Y hYV hYne
    linarith
  have hdet_p2p1 : det2 (p₂ - w) (p₁ - w) ≠ 0 := by
    intro h0
    have hdot : dot2 (p₂ - w) (rayDir w h p₁) = 0 := by
      rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero]
    rw [hdot] at hprod_neg; linarith
  have hdet_p2p3 : det2 (p₂ - w) (p₃ - w) ≠ 0 := by
    intro h0
    have hdot : dot2 (p₂ - w) (rayDir w h p₃) = 0 := by
      rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero]
    rw [hdot] at hprod_neg; linarith
  by_cases ht1 : 0 < (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁)
  · exact kill p₁ hp₁ hp₁w hX₁ hdet_p2p1 ht1
  · have ht3 : 0 < (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₃) := by
      have h1ne : dot2 (p₂ - w) (rayDir w h p₁) ≠ 0 := by intro h0; rw [h0, zero_mul] at hprod_neg; linarith
      have h3ne : dot2 (p₂ - w) (rayDir w h p₃) ≠ 0 := by intro h0; rw [h0, mul_zero] at hprod_neg; linarith
      have hdiv_prod : ((1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁)) *
          ((1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₃)) < 0 := by
        rw [div_mul_div_comm]
        exact div_neg_of_pos_of_neg (mul_self_pos.mpr h1m) hprod_neg
      have hne0 : (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁) ≠ 0 := div_ne_zero h1m h1ne
      have hlt0 : (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁) < 0 := lt_of_le_of_ne (not_lt.mp ht1) hne0
      nlinarith
    exact kill p₃ hp₃ hp₃w hX₃ hdet_p2p3 ht3

/-- An ordinary strictly exposed vertex `X ∈ dualVerts s w` yields an ordinary line of `s`
attached to `w`. -/
private lemma ordinary_exposed_gives_attached {s : Finset ℝ²} {w X h : ℝ²}
    (hh : h ≠ 0)
    (hXV : X ∈ dualVerts s w)
    (hmax : ∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X)
    (hdet : ∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0)
    (hord : (s.filter (fun z => evalDual w z X = 0)).card ≤ 2) :
    ∃ L ∈ ordinaryLines s,
      (∀ z ∈ s, z ∈ L ↔ evalDual w z X = 0) ∧
      (∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            (![z 0, z 1, 1] : Fin 3 → ℝ) =
              a • (![p 0, p 1, 1] : Fin 3 → ℝ) +
              b • (ε • (![q 0, q 1, 1] : Fin 3 → ℝ)) +
              c • (δ • (![w 0, w 1, 1] : Fin 3 → ℝ)) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) := by
  obtain ⟨⟨p, q⟩, hpqf, rfl⟩ := Finset.mem_image.mp hXV
  obtain ⟨hpqp, hdet_pq⟩ := Finset.mem_filter.mp hpqf
  obtain ⟨hps, hqs⟩ := Finset.mem_product.mp hpqp
  have hpw : p ≠ w := fun h0 => hdet_pq (by rw [h0, sub_self]; simp [det2])
  have hqw : q ≠ w := fun h0 => hdet_pq (by rw [h0, sub_self]; simp [det2])
  have hpq : p ≠ q := fun h0 => hdet_pq (h0 ▸ det2_self _)
  set X := dualInter w p q
  let L := line[ℝ, p, q]
  have hmemL : ∀ z ∈ s, z ∈ L ↔ evalDual w z X = 0 := fun z _ => mem_line_iff_evalDual_zero hdet_pq
  have hL_ord : L ∈ ordinaryLines s := by
    rw [mem_ordinaryLines]
    refine ⟨⟨p, hps, q, hqs, hpq, rfl⟩, ?_⟩
    have hfilt : s.filter (fun z => z ∈ L) = s.filter (fun z => evalDual w z X = 0) :=
      Finset.filter_congr fun z hz => hmemL z hz
    rw [hfilt]
    have hsub : ({p, q} : Finset ℝ²) ⊆ s.filter (fun z => evalDual w z X = 0) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hps, evalDual_dualInter_left hdet_pq⟩
      · exact Finset.mem_filter.mpr ⟨hqs, evalDual_dualInter_right hdet_pq⟩
    have hge : 2 ≤ (s.filter (fun z => evalDual w z X = 0)).card := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hpq] at hle
      exact hle
    omega
  -- Now construct ε, δ ∈ {±1} for the attachment certificate!
  have hdp := hdet p hps hpw
  have hdq := hdet q hqs hqw
  have hα_ne : dot2 (p - w) (rayDir w h q) ≠ 0 := by
    rw [rayDir, dot2_smul_right, dot2_perp_right]
    exact mul_ne_zero (by simp [hdq]) (neg_ne_zero.mpr hdet_pq)
  have hβ_ne : dot2 (q - w) (rayDir w h p) ≠ 0 := by
    rw [rayDir, dot2_smul_right, dot2_perp_right]
    refine mul_ne_zero (by simp [hdp]) (neg_ne_zero.mpr ?_)
    rw [det2_anticomm]; exact neg_ne_zero.mpr hdet_pq
  let εp : ℝ := if 0 < dot2 (p - w) (rayDir w h q) then 1 else -1
  let εq : ℝ := if 0 < dot2 (q - w) (rayDir w h p) then 1 else -1
  have hεp_sq : εp ^ 2 = 1 := by dsimp [εp]; split_ifs <;> norm_num
  have hεq_sq : εq ^ 2 = 1 := by dsimp [εq]; split_ifs <;> norm_num
  have hα_pos : 0 < εp * dot2 (p - w) (rayDir w h q) := by
    dsimp [εp]; split_ifs with h1
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp h1) hα_ne; linarith
  have hβ_pos : 0 < εq * dot2 (q - w) (rayDir w h p) := by
    dsimp [εq]; split_ifs with h1
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp h1) hβ_ne; linarith
  refine ⟨L, hL_ord, hmemL, p, hps, q, hqs, hpq, left_mem_affineSpan_pair ℝ p q,
    right_mem_affineSpan_pair ℝ p q, not_mem_line_of_det2_ne_zero hdet_pq,
    εp * εq, εp, by rw [mul_pow, hεp_sq, hεq_sq, one_mul], hεp_sq, fun z hzs => ?_⟩
  by_cases hzw : z = w
  · subst hzw
    refine ⟨0, 0, εp, ?_, ?_⟩
    · have hsq : εp * εp = 1 := by nlinarith [hεp_sq]
      ext i; fin_cases i <;> simp [← mul_assoc, hsq]
    · dsimp [εp]; split_ifs <;> [exact Or.inl (by norm_num); exact Or.inr (by norm_num)]
  by_cases hzp : z = p
  · subst hzp
    exact ⟨1, 0, 0, by ext i; fin_cases i <;> simp, Or.inl (by norm_num)⟩
  by_cases hzq : z = q
  · subst hzq
    refine ⟨0, εp * εq, 0, ?_, ?_⟩
    · ext i
      have hsq : (εp * εq) * (εp * εq) = 1 := by nlinarith [hεp_sq, hεq_sq]
      fin_cases i <;> simp [← mul_assoc, hsq]
    · dsimp [εp, εq]; split_ifs <;> [exact Or.inl (by norm_num); exact Or.inr (by norm_num);
        exact Or.inr (by norm_num); exact Or.inl (by norm_num)]
  -- General z ∉ {w, p, q}: evalDual w z X ≠ 0!
  have hzX_ne : evalDual w z X ≠ 0 := by
    intro h0
    have hsub : ({p, q, z} : Finset ℝ²) ⊆ s.filter (fun u => evalDual w u X = 0) := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hps, evalDual_dualInter_left hdet_pq⟩
      · exact Finset.mem_filter.mpr ⟨hqs, evalDual_dualInter_right hdet_pq⟩
      · exact Finset.mem_filter.mpr ⟨hzs, h0⟩
    have h3 : ({p, q, z} : Finset ℝ²).card = 3 :=
      Finset.card_eq_three.mpr ⟨p, q, z, hpq, Ne.symm hzp, Ne.symm hzq, rfl⟩
    have := Finset.card_le_card hsub
    omega
  -- Key sign lemma: evalDual w z X and dot2 (z - w) (rayDir w h r) cannot have opposite strict signs!
  have same_sign_ray : ∀ r : ℝ², r ∈ s → r ≠ w → evalDual w r X = 0 →
      0 ≤ evalDual w z X * dot2 (z - w) (rayDir w h r) := by
    intro r hrs hrw hXr
    by_contra hneg
    push Not at hneg
    have hg_ne : dot2 (z - w) (rayDir w h r) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hneg; linarith
    have hdet_zr : det2 (z - w) (r - w) ≠ 0 := by
      intro h0
      rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero] at hg_ne
      exact hg_ne rfl
    set t := -evalDual w z X / dot2 (z - w) (rayDir w h r)
    have ht_pos : 0 < t := by
      dsimp [t]
      rw [div_pos_iff]
      rcases lt_or_gt_of_ne hzX_ne with h1 | h1
      · left; exact ⟨by linarith, by nlinarith⟩
      · right; exact ⟨by linarith, by nlinarith⟩
    let Y := X + t • rayDir w h r
    have hYr : evalDual w r Y = 0 := by
      dsimp [evalDual, Y]; rw [dot2_add_right, dot2_smul_right, dot2_rayDir_self, mul_zero, add_zero]
      exact hXr
    have hYz : evalDual w z Y = 0 := by
      dsimp [evalDual, Y]; rw [dot2_add_right, dot2_smul_right]
      dsimp [t, evalDual]; field_simp [hg_ne]; ring
    have hY_eq : Y = dualInter w z r := dualInter_unique hdet_zr hYz hYr
    have hYV : Y ∈ dualVerts s w := by
      rw [hY_eq]
      exact Finset.mem_image.mpr ⟨(z, r), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzs, hrs⟩, hdet_zr⟩, rfl⟩
    have hdotY : dot2 h Y = dot2 h X + t := by
      dsimp [Y]; rw [dot2_add_right, dot2_smul_right, dot2_h_rayDir (hdet r hrs hrw), mul_one]
    have hYne : Y ≠ X := fun h => by rw [h] at hdotY; linarith
    linarith [hmax Y hYV hYne]
  have hsp : 0 ≤ evalDual w z X * dot2 (z - w) (rayDir w h p) :=
    same_sign_ray p hps hpw (evalDual_dualInter_left hdet_pq)
  have hsq : 0 ≤ evalDual w z X * dot2 (z - w) (rayDir w h q) :=
    same_sign_ray q hqs hqw (evalDual_dualInter_right hdet_pq)
  -- Express z - w = a • (p - w) + (b * (εp * εq)) • (q - w)
  obtain ⟨a₀, b₀, hab⟩ := basis_decomp hdet_pq (z - w)
  let a := a₀
  let b := b₀ * (εp * εq)
  let c := εp * evalDual w z X
  have hb_eq : b * (εp * εq) = b₀ := by
    dsimp [b]
    calc b₀ * (εp * εq) * (εp * εq) = b₀ * (εp ^ 2 * εq ^ 2) := by ring
      _ = b₀ := by rw [hεp_sq, hεq_sq]; ring
  have hce : c * εp = evalDual w z X := by
    dsimp [c]
    calc εp * evalDual w z X * εp = εp ^ 2 * evalDual w z X := by ring
      _ = evalDual w z X := by rw [hεp_sq, one_mul]
  have ha_dot : dot2 (z - w) (rayDir w h q) = a * dot2 (p - w) (rayDir w h q) := by
    rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left, dot2_rayDir_self, mul_zero, add_zero]
  have hb_dot : dot2 (z - w) (rayDir w h p) = b₀ * dot2 (q - w) (rayDir w h p) := by
    rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left, dot2_rayDir_self, mul_zero, zero_add]
  have hsum1 : a + b * (εp * εq) + c * εp = 1 := by
    rw [hb_eq, hce]
    dsimp [evalDual]
    rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left]
    have ep : dot2 (p - w) X = -1 := by
      have h := evalDual_dualInter_left hdet_pq; dsimp [evalDual] at h; linarith
    have eq : dot2 (q - w) X = -1 := by
      have h := evalDual_dualInter_right hdet_pq; dsimp [evalDual] at h; linarith
    change a₀ + b₀ + (a₀ * dot2 (p - w) X + b₀ * dot2 (q - w) X + 1) = 1
    rw [ep, eq]; ring
  have hs0 : a₀ + b₀ + c * εp = 1 := by rw [← hb_eq]; exact hsum1
  refine ⟨a, b, c, ?_, ?_⟩
  · ext i
    have h0 := congrArg (fun v : ℝ² => v.ofLp 0) hab
    have h1 := congrArg (fun v : ℝ² => v.ofLp 1) hab
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
    fin_cases i
    · change z.ofLp 0 = a₀ * p.ofLp 0 + b * (εp * εq * q.ofLp 0) + c * (εp * w.ofLp 0)
      have hb0 : b * (εp * εq * q.ofLp 0) = b₀ * q.ofLp 0 := by rw [← mul_assoc, hb_eq]
      rw [hb0]
      linear_combination h0 - w.ofLp 0 * hs0
    · change z.ofLp 1 = a₀ * p.ofLp 1 + b * (εp * εq * q.ofLp 1) + c * (εp * w.ofLp 1)
      have hb1 : b * (εp * εq * q.ofLp 1) = b₀ * q.ofLp 1 := by rw [← mul_assoc, hb_eq]
      rw [hb1]
      linear_combination h1 - w.ofLp 1 * hs0
    · change (1 : ℝ) = a * 1 + b * (εp * εq * 1) + c * (εp * 1)
      linarith [hsum1]
  · -- Check all three of a, b, c have the same sign as c = εp * evalDual w z X!
    have hca : 0 ≤ c * a := by
      have h1 : (c * a) * (εp * dot2 (p - w) (rayDir w h q)) =
          evalDual w z X * dot2 (z - w) (rayDir w h q) := by
        rw [ha_dot]; dsimp [c]
        calc εp * evalDual w z X * a * (εp * dot2 (p - w) (rayDir w h q))
            = εp ^ 2 * (evalDual w z X * (a * dot2 (p - w) (rayDir w h q))) := by ring
          _ = evalDual w z X * (a * dot2 (p - w) (rayDir w h q)) := by rw [hεp_sq, one_mul]
      nlinarith
    have hcb : 0 ≤ c * b := by
      have h1 : (c * b) * (εq * dot2 (q - w) (rayDir w h p)) =
          evalDual w z X * dot2 (z - w) (rayDir w h p) := by
        rw [hb_dot]; dsimp [c, b]
        calc εp * evalDual w z X * (b₀ * (εp * εq)) * (εq * dot2 (q - w) (rayDir w h p))
            = (εp ^ 2) * (εq ^ 2) * (evalDual w z X * (b₀ * dot2 (q - w) (rayDir w h p))) := by ring
          _ = evalDual w z X * (b₀ * dot2 (q - w) (rayDir w h p)) := by rw [hεp_sq, hεq_sq]; ring
      nlinarith
    have hc_ne : c ≠ 0 := by
      dsimp [c]; exact mul_ne_zero (by dsimp [εp]; split_ifs <;> norm_num) hzX_ne
    rcases lt_or_gt_of_ne hc_ne with hcneg | hcpos
    · right; exact ⟨by nlinarith, by nlinarith, hcneg.le⟩
    · left; exact ⟨by nlinarith, by nlinarith, hcpos.le⟩

/-- Distinct dual vertices give distinct ordinary lines (when each characterizes its line). -/
private lemma line_ne_of_vert_ne {s : Finset ℝ²} {w X₁ X₂ : ℝ²}
    {L₁ L₂ : AffineSubspace ℝ ℝ²}
    (hX₁ : X₁ ∈ dualVerts s w) (hX₂ : X₂ ∈ dualVerts s w) (hne : X₁ ≠ X₂)
    (h1 : ∀ z ∈ s, z ∈ L₁ ↔ evalDual w z X₁ = 0)
    (h2 : ∀ z ∈ s, z ∈ L₂ ↔ evalDual w z X₂ = 0) : L₁ ≠ L₂ := by
  intro heq
  obtain ⟨⟨p, q⟩, hpqf, rfl⟩ := Finset.mem_image.mp hX₁
  obtain ⟨hpqp, hdet⟩ := Finset.mem_filter.mp hpqf
  obtain ⟨hps, hqs⟩ := Finset.mem_product.mp hpqp
  have hp2 : evalDual w p X₂ = 0 := (h2 p hps).mp (heq ▸ (h1 p hps).mpr (evalDual_dualInter_left hdet))
  have hq2 : evalDual w q X₂ = 0 := (h2 q hqs).mp (heq ▸ (h1 q hqs).mpr (evalDual_dualInter_right hdet))
  exact hne (dualInter_unique hdet hp2 hq2).symm

/-- If a strictly exposed vertex `X` has ≥ 3 incident dual lines, there are 3 with strictly ordered slopes. -/
private lemma three_sorted_of_card_gt_two {s : Finset ℝ²} {w X h : ℝ²}
    (hh : h ≠ 0)
    (hdet : ∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0)
    (hgt : 2 < (s.filter (fun z => evalDual w z X = 0)).card) :
    ∃ p₁ ∈ s, ∃ p₂ ∈ s, ∃ p₃ ∈ s,
      p₁ ≠ w ∧ p₂ ≠ w ∧ p₃ ≠ w ∧
      evalDual w p₁ X = 0 ∧ evalDual w p₂ X = 0 ∧ evalDual w p₃ X = 0 ∧
      raySlope w h p₁ < raySlope w h p₂ ∧ raySlope w h p₂ < raySlope w h p₃ := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hgt
  obtain ⟨has, haX⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbs, hbX⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcs, hcX⟩ := Finset.mem_filter.mp hc
  have haw : a ≠ w := fun h0 => by rw [h0] at haX; simp [evalDual, dot2] at haX
  have hbw : b ≠ w := fun h0 => by rw [h0] at hbX; simp [evalDual, dot2] at hbX
  have hcw : c ≠ w := fun h0 => by rw [h0] at hcX; simp [evalDual, dot2] at hcX
  have sab : raySlope w h a ≠ raySlope w h b :=
    raySlope_ne_of_ne_through_X hh (hdet a has haw) (hdet b hbs hbw) haX hbX hab
  have sac : raySlope w h a ≠ raySlope w h c :=
    raySlope_ne_of_ne_through_X hh (hdet a has haw) (hdet c hcs hcw) haX hcX hac
  have sbc : raySlope w h b ≠ raySlope w h c :=
    raySlope_ne_of_ne_through_X hh (hdet b hbs hbw) (hdet c hcs hcw) hbX hcX hbc
  rcases lt_or_gt_of_ne sab with h1 | h1 <;>
  rcases lt_or_gt_of_ne sac with h2 | h2 <;>
  rcases lt_or_gt_of_ne sbc with h3 | h3
  · exact ⟨a, has, b, hbs, c, hcs, haw, hbw, hcw, haX, hbX, hcX, h1, h3⟩
  · exact ⟨a, has, c, hcs, b, hbs, haw, hcw, hbw, haX, hcX, hbX, h2, h3⟩
  · linarith
  · exact ⟨c, hcs, a, has, b, hbs, hcw, haw, hbw, hcX, haX, hbX, h2, h1⟩
  · exact ⟨b, hbs, a, has, c, hcs, hbw, haw, hcw, hbX, haX, hcX, h1, h2⟩
  · linarith
  · exact ⟨b, hbs, c, hcs, a, has, hbw, hcw, haw, hbX, hcX, haX, h3, h2⟩
  · exact ⟨c, hcs, b, hbs, a, has, hcw, hbw, haw, hcX, hbX, haX, h3, h1⟩

/-- If `z ∈ s \ {w}` has NO parallel partner in `s \ {w}`, then `line[w, z]` is an ordinary line through `w`. -/
private lemma ordinary_through_w_of_no_parallel {s : Finset ℝ²} {w z : ℝ²}
    (hw : w ∈ s) (hz : z ∈ s) (hzw : z ≠ w)
    (hno : ∀ u ∈ s, u ≠ w → u ≠ z → det2 (z - w) (u - w) ≠ 0) :
    line[ℝ, w, z] ∈ ordinaryLines s ∧ w ∈ line[ℝ, w, z] := by
  refine ⟨?_, left_mem_affineSpan_pair ℝ w z⟩
  rw [mem_ordinaryLines]
  refine ⟨⟨w, hw, z, hz, hzw.symm, rfl⟩, ?_⟩
  have heq : s.filter (fun u => u ∈ line[ℝ, w, z]) = {w, z} := by
    ext u; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hus, huL⟩
      by_cases huw : u = w
      · exact Or.inl huw
      · by_cases huz : u = z
        · exact Or.inr huz
        · exfalso; exact hno u hus huw huz ((mem_line_iff_det2 hzw.symm).mp huL)
    · rintro (hu | hu)
      · rw [hu]; exact ⟨hw, left_mem_affineSpan_pair ℝ w z⟩
      · rw [hu]; exact ⟨hz, right_mem_affineSpan_pair ℝ w z⟩
  rw [heq, Finset.card_pair hzw.symm]

/-- Existence of three distinct strictly exposed vertices of any non-collinear finite set `V`. -/
private lemma exists_three_exposed (s V : Finset ℝ²) (w : ℝ²)
    (hVcol : ¬ Collinear ℝ (V : Set ℝ²)) :
    ∃ (X₁ X₂ X₃ : ℝ²), X₁ ∈ V ∧ X₂ ∈ V ∧ X₃ ∈ V ∧ X₁ ≠ X₂ ∧ X₁ ≠ X₃ ∧ X₂ ≠ X₃ ∧
      (∃ h₁ : ℝ², h₁ ≠ 0 ∧ (∀ Y ∈ V, Y ≠ X₁ → dot2 h₁ Y < dot2 h₁ X₁) ∧
        (∀ z ∈ s, z ≠ w → det2 h₁ (z - w) ≠ 0)) ∧
      (∃ h₂ : ℝ², h₂ ≠ 0 ∧ (∀ Y ∈ V, Y ≠ X₂ → dot2 h₂ Y < dot2 h₂ X₂) ∧
        (∀ z ∈ s, z ≠ w → det2 h₂ (z - w) ≠ 0)) ∧
      (∃ h₃ : ℝ², h₃ ≠ 0 ∧ (∀ Y ∈ V, Y ≠ X₃ → dot2 h₃ Y < dot2 h₃ X₃) ∧
        (∀ z ∈ s, z ≠ w → det2 h₃ (z - w) ≠ 0)) := by
  have hVne : V.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hVcol (by simp [h, collinear_empty])
  let e₀ : ℝ² := !₂[1, 0]
  have he₀ : e₀ ≠ 0 := by intro h; have := congrArg (fun x : ℝ² => x.ofLp 0) h; norm_num [e₀] at this
  obtain ⟨X₁, hX₁V, h₁, hh₁, hmax₁, hdet₁, hle₁⟩ := exists_strictly_exposed s V w hVne e₀ he₀
  obtain ⟨X₂, hX₂V, h₂, hh₂, hmax₂, hdet₂, hle₂⟩ :=
    exists_strictly_exposed s V w hVne (-e₀) (neg_ne_zero.mpr he₀)
  have hX₁₂ : X₁ ≠ X₂ := by
    intro heq; subst heq
    -- Every Y ∈ V has dot2 e₀ Y = dot2 e₀ X₁, so V lies on a vertical line (collinear!)
    apply hVcol
    have hall : ∀ Y ∈ V, Y.ofLp 0 = X₁.ofLp 0 := fun Y hY => by
      have h1 := hle₁ Y hY
      have h2 := hle₂ Y hY
      simp only [dot2, e₀, PiLp.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
      linarith
    have hsub : (V : Set ℝ²) ⊆ line[ℝ, X₁, X₁ + !₂[0, 1]] := by
      intro Y hY
      change Y ∈ line[ℝ, X₁, X₁ + !₂[0, 1]]
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨Y.ofLp 1 - X₁.ofLp 1, ?_⟩
      ext i; rw [AffineMap.lineMap_apply_module']
      match i with
      | 0 => simp [hall Y hY]
      | 1 => simp
    rw [collinear_iff_finrank_le_one]
    have hdir : Module.finrank ℝ (line[ℝ, X₁, X₁ + !₂[(0 : ℝ), 1]]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton]
      intro h0
      have := congrArg (fun x : ℝ² => x.ofLp 1) h0
      simp at this
    exact (Submodule.finrank_mono (by rw [← direction_affineSpan]; exact AffineSubspace.direction_le (affineSpan_le.mpr hsub))).trans hdir.le
  let n₁₂ := perp (X₂ - X₁)
  have hn₁₂ : n₁₂ ≠ 0 := perp_ne_zero (sub_ne_zero.mpr hX₁₂.symm)
  have h12_eq : dot2 n₁₂ X₁ = dot2 n₁₂ X₂ := by
    have : dot2 n₁₂ (X₂ - X₁) = 0 := by rw [dot2_comm, dot2_self_perp]
    rw [dot2_sub_right] at this; linarith
  have hex_off : ∃ Y ∈ V, dot2 n₁₂ Y ≠ dot2 n₁₂ X₁ := by
    by_contra! hall
    apply hVcol
    have hsub : (V : Set ℝ²) ⊆ line[ℝ, X₁, X₂] := by
      intro Y hY
      change Y ∈ line[ℝ, X₁, X₂]
      rw [mem_line_iff_det2 hX₁₂]
      have h0 : dot2 n₁₂ (Y - X₁) = 0 := by rw [dot2_sub_right, hall Y hY, sub_self]
      rw [← dot2_perp_left]; exact h0
    rw [collinear_iff_finrank_le_one]
    have hdir : Module.finrank ℝ (line[ℝ, X₁, X₂]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hX₁₂)]
    exact (Submodule.finrank_mono (by rw [← direction_affineSpan]; exact AffineSubspace.direction_le (affineSpan_le.mpr hsub))).trans hdir.le
  obtain ⟨Y₀, hY₀V, hY₀ne⟩ := hex_off
  rcases lt_or_gt_of_ne hY₀ne with hlt | hgt
  · obtain ⟨X₃, hX₃V, h₃, hh₃, hmax₃, hdet₃, hle₃⟩ :=
      exists_strictly_exposed s V w hVne (-n₁₂) (neg_ne_zero.mpr hn₁₂)
    have hlt3 : dot2 n₁₂ X₃ < dot2 n₁₂ X₁ := by
      have := hle₃ Y₀ hY₀V
      simp only [dot2, PiLp.neg_apply] at this hlt ⊢; linarith
    exact ⟨X₁, X₂, X₃, hX₁V, hX₂V, hX₃V, hX₁₂,
      fun h => by rw [h] at hlt3; linarith,
      fun h => by rw [← h, ← h12_eq] at hlt3; linarith,
      ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩
  · obtain ⟨X₃, hX₃V, h₃, hh₃, hmax₃, hdet₃, hle₃⟩ :=
      exists_strictly_exposed s V w hVne n₁₂ hn₁₂
    have hgt3 : dot2 n₁₂ X₁ < dot2 n₁₂ X₃ := lt_of_lt_of_le hgt (hle₃ Y₀ hY₀V)
    exact ⟨X₁, X₂, X₃, hX₁V, hX₂V, hX₃V, hX₁₂,
      fun h => by rw [h] at hgt3; linarith,
      fun h => by rw [← h, ← h12_eq] at hgt3; linarith,
      ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩

theorem kelly_moser_zero :
    ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
    ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
    let O := ordinaryLines s
    let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
    let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
    let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
    let A := fun p => (O.filter (attached p)).card
    ∀ w ∈ s, d w = 0 → 3 ≤ A w := by
  intro s _ hcol hno2 O d v attached A w hw hdw
  have hVcol := dualVerts_not_collinear hcol hno2 hw
  obtain ⟨X₁, X₂, X₃, hX₁, hX₂, hX₃, h12, h13, h23,
    ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩ :=
    exists_three_exposed s (dualVerts s w) w hVcol
  have ord_of_exposed : ∀ {X h : ℝ²}, h ≠ 0 →
      (∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X) →
      (∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0) →
      (s.filter (fun z => evalDual w z X = 0)).card ≤ 2 := by
    intro X h hh hmax hdet
    by_contra! hgt
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, hp₁w, hp₂w, hp₃w, hX₁', hX₂', hX₃', hs12, hs23⟩ :=
      three_sorted_of_card_gt_two hh hdet hgt
    have hno_par := no_parallel_of_middle_at_exposed hh hmax hdet hp₁ hp₁w hp₂ hp₂w hp₃ hp₃w hX₁' hX₂' hX₃' hs12 hs23
    obtain ⟨hord, hmem⟩ := ordinary_through_w_of_no_parallel hw hp₂ hp₂w hno_par
    have hpos : 0 < d w := Finset.card_pos.mpr ⟨line[ℝ, w, p₂], Finset.mem_filter.mpr ⟨hord, hmem⟩⟩
    omega
  obtain ⟨L₁, hL₁O, hL₁m, hL₁a⟩ := ordinary_exposed_gives_attached hh₁ hX₁ hmax₁ hdet₁ (ord_of_exposed hh₁ hmax₁ hdet₁)
  obtain ⟨L₂, hL₂O, hL₂m, hL₂a⟩ := ordinary_exposed_gives_attached hh₂ hX₂ hmax₂ hdet₂ (ord_of_exposed hh₂ hmax₂ hdet₂)
  obtain ⟨L₃, hL₃O, hL₃m, hL₃a⟩ := ordinary_exposed_gives_attached hh₃ hX₃ hmax₃ hdet₃ (ord_of_exposed hh₃ hmax₃ hdet₃)
  have hL12 : L₁ ≠ L₂ := line_ne_of_vert_ne hX₁ hX₂ h12 hL₁m hL₂m
  have hL13 : L₁ ≠ L₃ := line_ne_of_vert_ne hX₁ hX₃ h13 hL₁m hL₃m
  have hL23 : L₂ ≠ L₃ := line_ne_of_vert_ne hX₂ hX₃ h23 hL₂m hL₃m
  have hsub : ({L₁, L₂, L₃} : Finset (AffineSubspace ℝ ℝ²)) ⊆ O.filter (attached w) := by
    intro L hL; simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hL₁O, hL₁a⟩
    · exact Finset.mem_filter.mpr ⟨hL₂O, hL₂a⟩
    · exact Finset.mem_filter.mpr ⟨hL₃O, hL₃a⟩
  have h3 : ({L₁, L₂, L₃} : Finset (AffineSubspace ℝ ℝ²)).card = 3 :=
    Finset.card_eq_three.mpr ⟨L₁, L₂, L₃, hL12, hL13, hL23, rfl⟩
  exact h3 ▸ Finset.card_le_card hsub

end Erdos210KM

theorem OMA.solution : OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1.H1 := by
  exact Erdos210KM.kelly_moser_zero
