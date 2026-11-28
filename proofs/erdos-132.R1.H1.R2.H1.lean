import OMAReductions.R_erdos_132_R1_H1_R2

-- Step erdos-132.R1.H1.R2.H1: hypothesis H1 of reduction erdos-132.R1.H1.R2
-- Credit: @yhay81

open Finset
open scoped Classical
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

namespace Erdos132R1H1R2H1

private abbrev Pt := EuclideanSpace ℝ (Fin 2)

private lemma dist_sq_eq (p q : Pt) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

private lemma eq_of_coord_eq {p q : Pt} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  have hsq : dist p q ^ 2 = 0 := by rw [dist_sq_eq, h0, h1]; ring
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hsq)

private def ptLt (p q : Pt) : Prop :=
  p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 < q 1)

private lemma ptLt_asymm {p q : Pt} (h : ptLt p q) : ¬ ptLt q p := by
  rcases h with h | ⟨h0, h1⟩ <;> rintro (h' | ⟨h0', h1'⟩) <;> linarith

private lemma ptLt_or_of_ne {p q : Pt} (hne : p ≠ q) : ptLt p q ∨ ptLt q p := by
  rcases lt_trichotomy (p 0) (q 0) with h | h0 | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (p 1) (q 1) with h1 | h1 | h1
    · exact Or.inl (Or.inr ⟨h0, h1⟩)
    · exact False.elim (hne (eq_of_coord_eq h0 h1))
    · exact Or.inr (Or.inr ⟨h0.symm, h1⟩)
  · exact Or.inr (Or.inl h)

private lemma two_mul_pairMultiplicity (A : Finset Pt) (d : ℝ) :
    2 * pairMultiplicity A d = (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card := by
  set S := A.offDiag.filter (fun p => dist p.1 p.2 = d)
  set S1 := S.filter (fun p => ptLt p.1 p.2)
  set S2 := S.filter (fun p => ptLt p.2 p.1)
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact ptLt_asymm (Finset.mem_filter.mp hp1).2 (Finset.mem_filter.mp hp2).2
  have hunion : S1 ∪ S2 = S := by
    ext p
    simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hp
      have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2
      rcases ptLt_or_of_ne hne with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  have hcard : S1.card = S2.card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hlt⟩
      rcases Finset.mem_filter.mp hpS with ⟨hpo, hdist⟩
      rcases Finset.mem_offDiag.mp hpo with ⟨hp1, hp2, hne⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨hp2, hp1, hne.symm⟩, ?_⟩, hlt⟩
      change dist p.2 p.1 = d
      rw [dist_comm]; exact hdist
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hlt⟩
      rcases Finset.mem_filter.mp hpS with ⟨hpo, hdist⟩
      rcases Finset.mem_offDiag.mp hpo with ⟨hp1, hp2, hne⟩
      refine ⟨p.swap, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨hp2, hp1, hne.symm⟩, ?_⟩, hlt⟩, Prod.swap_swap p⟩
      change dist p.2 p.1 = d
      rw [dist_comm]; exact hdist
  have hS : S.card = 2 * S1.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hcard, two_mul]
  change 2 * (S.card / 2) = S.card
  omega

private lemma pairMultiplicity_pos_of_mem_image {A : Finset Pt} {d : ℝ}
    (hd : d ∈ A.offDiag.image (fun p => dist p.1 p.2)) :
    1 ≤ pairMultiplicity A d := by
  rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
  have hmem : p ∈ A.offDiag.filter (fun q => dist q.1 q.2 = dist p.1 p.2) :=
    Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hpos : 0 < (A.offDiag.filter (fun q => dist q.1 q.2 = dist p.1 p.2)).card :=
    Finset.card_pos.mpr ⟨p, hmem⟩
  have h2 := two_mul_pairMultiplicity A (dist p.1 p.2)
  omega

private lemma mem_rareDistances_iff (A : Finset Pt) (d : ℝ) :
    d ∈ rareDistances A ↔
      d ∈ A.offDiag.image (fun p => dist p.1 p.2) ∧ pairMultiplicity A d ≤ A.card := by
  simp only [rareDistances, Finset.mem_filter]
  constructor
  · rintro ⟨hd, _, hle⟩; exact ⟨hd, hle⟩
  · rintro ⟨hd, hle⟩; exact ⟨hd, pairMultiplicity_pos_of_mem_image hd, hle⟩

private lemma two_mul_sum_pairMultiplicity (A : Finset Pt) :
    2 * ∑ d ∈ A.offDiag.image (fun p => dist p.1 p.2), pairMultiplicity A d =
      A.card * (A.card - 1) := by
  rw [Finset.mul_sum]
  have h1 :
      ∑ d ∈ A.offDiag.image (fun p => dist p.1 p.2), 2 * pairMultiplicity A d =
        ∑ d ∈ A.offDiag.image (fun p => dist p.1 p.2),
          (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card :=
    Finset.sum_congr rfl fun d _ => two_mul_pairMultiplicity A d
  rw [h1, ← Finset.card_eq_sum_card_image (fun p => dist p.1 p.2) A.offDiag,
    Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

private lemma two_mul_pairMultiplicity_eq_sum_deg (A : Finset Pt) (d : ℝ) :
    2 * pairMultiplicity A d =
      ∑ v ∈ A, ((A.erase v).filter (fun u => dist v u = d)).card := by
  rw [two_mul_pairMultiplicity]
  set S := A.offDiag.filter (fun p => dist p.1 p.2 = d)
  have hmaps : ∀ p ∈ S, p.1 ∈ A := fun p hp =>
    (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun v hv => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hp1⟩
    rcases Finset.mem_filter.mp hpS with ⟨hpo, hdist⟩
    rcases Finset.mem_offDiag.mp hpo with ⟨_, hp2, hne⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hp2⟩, ?_⟩
    · intro heq; exact hne (hp1.trans heq.symm)
    · simpa only [hp1] using hdist
  · intro p hp q hq h2
    have hp1 : p.1 = v := (Finset.mem_filter.mp hp).2
    have hq1 : q.1 = v := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hp1.trans hq1.symm) h2
  · intro u hu
    rcases Finset.mem_filter.mp hu with ⟨hue, hdist⟩
    rcases Finset.mem_erase.mp hue with ⟨hne, huA⟩
    exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨hv, huA, hne.symm⟩, hdist⟩, rfl⟩, rfl⟩

private lemma equilateral_fourth_point_cases {x y R da db dc : ℝ}
    (h1 : 3 * x ^ 2 + y ^ 2 = 3 * da)
    (h2 : 3 * (x - 1) ^ 2 + y ^ 2 = 3 * db)
    (h3 : 3 * (x - 1 / 2) ^ 2 + (y - 3 / 2) ^ 2 = 3 * dc)
    (ha : da = 1 ∨ da = R) (hb : db = 1 ∨ db = R) (hc : dc = 1 ∨ dc = R)
    (hda : 0 < da) (hdb : 0 < db) (hdc : 0 < dc) :
    (R = 1 / 3 ∧ x = 1 / 2 ∧ y = 1 / 2) ∨
    (R = 3 ∧ ((x = 1 / 2 ∧ y = -3 / 2) ∨ (x = -1 / 2 ∧ y = 3 / 2) ∨ (x = 3 / 2 ∧ y = 3 / 2))) ∨
    (R ^ 2 - 4 * R + 1 = 0 ∧
      ((x = 1 / 2 ∧ y = (2 * R - 1) / 2) ∨
       (x = R / 2 ∧ y = (2 - R) / 2) ∨
       (x = (2 - R) / 2 ∧ y = (2 - R) / 2))) := by
  have hx : x = (1 + da - db) / 2 := by linarith
  have hy : y = (1 + da + db - 2 * dc) / 2 := by linarith
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rw [ha] at h1 hx hy hda <;> rw [hb] at h2 hx hy hdb <;> rw [hc] at h3 hy hdc
  · exfalso; nlinarith only [h1, hx, hy]
  · right; left
    have hR : R = 3 := by nlinarith only [h1, hx, hy, hdc]
    exact ⟨hR, Or.inl ⟨by linarith only [hx], by linarith only [hy, hR]⟩⟩
  · right; left
    have hR : R = 3 := by nlinarith only [h1, hx, hy, hdb]
    exact ⟨hR, Or.inr (Or.inl ⟨by linarith only [hx, hR], by linarith only [hy, hR]⟩)⟩
  · right; right
    refine ⟨by nlinarith only [h1, hx, hy],
      Or.inr (Or.inr ⟨by linarith only [hx], by linarith only [hy]⟩)⟩
  · right; left
    have hR : R = 3 := by nlinarith only [h1, hx, hy, hda]
    exact ⟨hR, Or.inr (Or.inr ⟨by linarith only [hx, hR], by linarith only [hy, hR]⟩)⟩
  · right; right
    refine ⟨by nlinarith only [h1, hx, hy],
      Or.inr (Or.inl ⟨by linarith only [hx], by linarith only [hy]⟩)⟩
  · right; right
    refine ⟨by nlinarith only [h1, hx, hy],
      Or.inl ⟨by linarith only [hx], by linarith only [hy]⟩⟩
  · left
    exact ⟨by nlinarith only [h1, hx, hy], by linarith only [hx], by linarith only [hy]⟩

private lemma no_two_fourth_points {xp yp xq yq R dpq : ℝ}
    (hpq_eq : 3 * (xp - xq) ^ 2 + (yp - yq) ^ 2 = 3 * dpq)
    (hpq_pos : 0 < dpq) (hpq_or : dpq = 1 ∨ dpq = R)
    (hp_cases :
      (R = 1 / 3 ∧ xp = 1 / 2 ∧ yp = 1 / 2) ∨
      (R = 3 ∧ ((xp = 1 / 2 ∧ yp = -3 / 2) ∨ (xp = -1 / 2 ∧ yp = 3 / 2) ∨
        (xp = 3 / 2 ∧ yp = 3 / 2))) ∨
      (R ^ 2 - 4 * R + 1 = 0 ∧
        ((xp = 1 / 2 ∧ yp = (2 * R - 1) / 2) ∨
         (xp = R / 2 ∧ yp = (2 - R) / 2) ∨
         (xp = (2 - R) / 2 ∧ yp = (2 - R) / 2))))
    (hq_cases :
      (R = 1 / 3 ∧ xq = 1 / 2 ∧ yq = 1 / 2) ∨
      (R = 3 ∧ ((xq = 1 / 2 ∧ yq = -3 / 2) ∨ (xq = -1 / 2 ∧ yq = 3 / 2) ∨
        (xq = 3 / 2 ∧ yq = 3 / 2))) ∨
      (R ^ 2 - 4 * R + 1 = 0 ∧
        ((xq = 1 / 2 ∧ yq = (2 * R - 1) / 2) ∨
         (xq = R / 2 ∧ yq = (2 - R) / 2) ∨
         (xq = (2 - R) / 2 ∧ yq = (2 - R) / 2)))) : False := by
  rcases hp_cases with ⟨hR, hxp, hyp⟩ | ⟨hR, hp3⟩ | ⟨hR, hp3⟩ <;>
    rcases hq_cases with ⟨hR', hxq, hyq⟩ | ⟨hR', hq3⟩ | ⟨hR', hq3⟩
  · nlinarith only [hpq_eq, hpq_pos, hxp, hyp, hxq, hyq]
  · linarith only [hR, hR']
  · rw [hR] at hR'; norm_num at hR'
  · linarith only [hR, hR']
  · rcases hp3 with ⟨hxp, hyp⟩ | ⟨hxp, hyp⟩ | ⟨hxp, hyp⟩ <;>
      rcases hq3 with ⟨hxq, hyq⟩ | ⟨hxq, hyq⟩ | ⟨hxq, hyq⟩ <;>
      rcases hpq_or with hd | hd <;>
      nlinarith only [hpq_eq, hpq_pos, hR, hxp, hyp, hxq, hyq, hd]
  · rw [hR] at hR'; norm_num at hR'
  · rw [hR'] at hR; norm_num at hR
  · rw [hR'] at hR; norm_num at hR
  · have h_not_2R : dpq ≠ 2 * R := by
      intro h2R
      rcases hpq_or with hd | hd
      · have hval : R = 1 / 2 := by linarith only [h2R, hd]
        rw [hval] at hR; norm_num at hR
      · have hval : R = 0 := by linarith only [h2R, hd]
        rw [hval] at hR; norm_num at hR
    rcases hp3 with ⟨hxp, hyp⟩ | ⟨hxp, hyp⟩ | ⟨hxp, hyp⟩ <;>
      rcases hq3 with ⟨hxq, hyq⟩ | ⟨hxq, hyq⟩ | ⟨hxq, hyq⟩
    · rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hpq_pos]
    · exact h_not_2R (by rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hR])
    · exact h_not_2R (by rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hR])
    · exact h_not_2R (by rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hR])
    · rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hpq_pos]
    · exact h_not_2R (by rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hR])
    · exact h_not_2R (by rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hR])
    · exact h_not_2R (by rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hR])
    · rw [hxp, hyp, hxq, hyq] at hpq_eq; linarith only [hpq_eq, hpq_pos]

private lemma no_equilateral_in_five_two_dist {a b c p q : Pt} {s t : ℝ}
    (hab_ne : a ≠ b) (hap : a ≠ p) (hbp : b ≠ p) (hcp : c ≠ p)
    (haq : a ≠ q) (hbq : b ≠ q) (hcq : c ≠ q) (hpq : p ≠ q)
    (hab : dist a b = s) (hbc : dist b c = s) (hca : dist c a = s)
    (hpa : dist p a = s ∨ dist p a = t) (hpb : dist p b = s ∨ dist p b = t)
    (hpc : dist p c = s ∨ dist p c = t)
    (hqa : dist q a = s ∨ dist q a = t) (hqb : dist q b = s ∨ dist q b = t)
    (hqc : dist q c = s ∨ dist q c = t)
    (hpq_d : dist p q = s ∨ dist p q = t) : False := by
  have hs : 0 < s := hab ▸ dist_pos.mpr hab_ne
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  set u0 := b 0 - a 0
  set u1 := b 1 - a 1
  set v0 := 2 * (c 0 - a 0) - u0
  set v1 := 2 * (c 1 - a 1) - u1
  have hu : u0 ^ 2 + u1 ^ 2 = s ^ 2 := by
    have h := dist_sq_eq a b; rw [hab] at h; linarith
  have hca_sq : (c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2 = s ^ 2 := by
    have h := dist_sq_eq c a; rw [hca] at h; linarith
  have hbc_sq : (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 = s ^ 2 := by
    have h := dist_sq_eq b c; rw [hbc] at h; linarith
  have hcb_diff : (c 0 - a 0 - u0) ^ 2 + (c 1 - a 1 - u1) ^ 2 = s ^ 2 := by
    have h0 : c 0 - a 0 - u0 = -(b 0 - c 0) := by dsimp only [u0]; ring
    have h1 : c 1 - a 1 - u1 = -(b 1 - c 1) := by dsimp only [u1]; ring
    rw [h0, h1]; nlinarith
  have huv : u0 * v0 + u1 * v1 = 0 := by
    dsimp only [v0, v1]; linarith
  have hv : v0 ^ 2 + v1 ^ 2 = 3 * s ^ 2 := by
    dsimp only [v0, v1]; linarith
  let X : Pt → ℝ := fun z => ((z 0 - a 0) * u0 + (z 1 - a 1) * u1) / s ^ 2
  let Y : Pt → ℝ := fun z => ((z 0 - a 0) * v0 + (z 1 - a 1) * v1) / s ^ 2
  have hdist_xy : ∀ z w : Pt,
      3 * (X z - X w) ^ 2 + (Y z - Y w) ^ 2 = 3 * (dist z w ^ 2 / s ^ 2) := by
    intro z w
    set dx := z 0 - w 0
    set dy := z 1 - w 1
    have hX : X z - X w = (dx * u0 + dy * u1) / s ^ 2 := by
      dsimp only [X, dx, dy]; ring
    have hY : Y z - Y w = (dx * v0 + dy * v1) / s ^ 2 := by
      dsimp only [Y, dx, dy]; ring
    rw [hX, hY, dist_sq_eq z w]
    have hdet : (u0 * v1 - u1 * v0) ^ 2 = 3 * s ^ 4 := by
      have hid0 : (u0 * v1 - u1 * v0) ^ 2 =
          (u0 ^ 2 + u1 ^ 2) * (v0 ^ 2 + v1 ^ 2) - (u0 * v0 + u1 * v1) ^ 2 := by ring
      rw [hid0, hu, hv, huv]; ring
    have hid :
        (v0 ^ 2 + v1 ^ 2) * (dx * u0 + dy * u1) ^ 2 +
          (u0 ^ 2 + u1 ^ 2) * (dx * v0 + dy * v1) ^ 2 -
          2 * (u0 * v0 + u1 * v1) * (dx * u0 + dy * u1) * (dx * v0 + dy * v1) =
          (u0 * v1 - u1 * v0) ^ 2 * (dx ^ 2 + dy ^ 2) := by ring
    have hnum :
        3 * s ^ 2 * (dx * u0 + dy * u1) ^ 2 + s ^ 2 * (dx * v0 + dy * v1) ^ 2 =
          3 * s ^ 4 * (dx ^ 2 + dy ^ 2) := by
      rw [hu, hv, huv, hdet] at hid; linarith only [hid]
    have hs2_ne : s ^ 2 ≠ 0 := ne_of_gt hs2
    have hnum' :
        3 * (dx * u0 + dy * u1) ^ 2 + (dx * v0 + dy * v1) ^ 2 =
          3 * s ^ 2 * (dx ^ 2 + dy ^ 2) := by
      apply mul_left_cancel₀ hs2_ne
      linarith only [hnum]
    have hgoal :
        3 * ((dx * u0 + dy * u1) / s ^ 2) ^ 2 + ((dx * v0 + dy * v1) / s ^ 2) ^ 2 =
          (3 * (dx * u0 + dy * u1) ^ 2 + (dx * v0 + dy * v1) ^ 2) / s ^ 4 := by ring
    rw [hgoal, hnum']
    have hs4 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
    rw [hs4]
    field_simp [hs2_ne]
    rfl
  have hXa : X a = 0 := by dsimp only [X]; ring
  have hYa : Y a = 0 := by dsimp only [Y]; ring
  have hXb : X b = 1 := by
    dsimp only [X]
    have hnum : (b 0 - a 0) * u0 + (b 1 - a 1) * u1 = s ^ 2 := by
      dsimp only [u0, u1] at hu ⊢; linarith
    rw [hnum, div_self (ne_of_gt hs2)]
  have hYb : Y b = 0 := by
    dsimp only [Y]
    have hnum : (b 0 - a 0) * v0 + (b 1 - a 1) * v1 = 0 := by
      dsimp only [u0, u1] at huv; linarith
    rw [hnum, zero_div]
  have hXc : X c = 1 / 2 := by
    dsimp only [X]
    have hnum : (c 0 - a 0) * u0 + (c 1 - a 1) * u1 = s ^ 2 / 2 := by linarith
    rw [hnum]; field_simp [ne_of_gt hs2]
  have hYc : Y c = 3 / 2 := by
    dsimp only [Y]
    have hnum : (c 0 - a 0) * v0 + (c 1 - a 1) * v1 = 3 * s ^ 2 / 2 := by
      dsimp only [v0, v1]; linarith
    rw [hnum]; field_simp [ne_of_gt hs2]
  set R := t ^ 2 / s ^ 2
  have hD_or : ∀ z w : Pt, dist z w = s ∨ dist z w = t →
      dist z w ^ 2 / s ^ 2 = 1 ∨ dist z w ^ 2 / s ^ 2 = R := by
    intro z w h
    rcases h with h | h
    · left; rw [h, div_self (ne_of_gt hs2)]
    · right; rw [h]
  have hD_pos : ∀ z w : Pt, z ≠ w → 0 < dist z w ^ 2 / s ^ 2 := fun z w hne =>
    div_pos (sq_pos_of_pos (dist_pos.mpr hne)) hs2
  have h_pt := fun (z : Pt) (hza : a ≠ z) (hzb : b ≠ z) (hzc : c ≠ z)
      (h1 : dist z a = s ∨ dist z a = t) (h2 : dist z b = s ∨ dist z b = t)
      (h3 : dist z c = s ∨ dist z c = t) => by
    have e1 := hdist_xy z a; rw [hXa, hYa, sub_zero, sub_zero] at e1
    have e2 := hdist_xy z b; rw [hXb, hYb, sub_zero] at e2
    have e3 := hdist_xy z c; rw [hXc, hYc] at e3
    exact equilateral_fourth_point_cases e1 e2 e3
      (hD_or z a h1) (hD_or z b h2) (hD_or z c h3)
      (hD_pos z a hza.symm) (hD_pos z b hzb.symm) (hD_pos z c hzc.symm)
  exact no_two_fourth_points (hdist_xy p q) (hD_pos p q hpq) (hD_or p q hpq_d)
    (h_pt p hap hbp hcp hpa hpb hpc) (h_pt q haq hbq hcq hqa hqb hqc)

private lemma exists_two_of_two_le_card {α : Type*} {S : Finset α} (h : 2 ≤ S.card) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have h1 : 0 < (S.erase p).card := by rw [Finset.card_erase_of_mem hp]; omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp h1
  rcases Finset.mem_erase.mp hq with ⟨hqp, hqS⟩
  exact ⟨p, hp, q, hqS, hqp.symm⟩

private lemma exists_three_of_three_le_card {α : Type*} {S : Finset α} (h : 3 ≤ S.card) :
    ∃ u1 ∈ S, ∃ u2 ∈ S, ∃ u3 ∈ S, u1 ≠ u2 ∧ u2 ≠ u3 ∧ u1 ≠ u3 := by
  obtain ⟨u1, hu1⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have h1 : 2 ≤ (S.erase u1).card := by rw [Finset.card_erase_of_mem hu1]; omega
  obtain ⟨u2, hu2, u3, hu3, h23⟩ := exists_two_of_two_le_card h1
  rcases Finset.mem_erase.mp hu2 with ⟨h21, hu2S⟩
  rcases Finset.mem_erase.mp hu3 with ⟨h31, hu3S⟩
  exact ⟨u1, hu1, u2, hu2S, u3, hu3S, h21.symm, h23, h31.symm⟩

private lemma no_triangle_of_two_dist_card_ge_five {S : Finset Pt} {s t : ℝ}
    (hcard : 5 ≤ S.card)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = s ∨ dist x y = t)
    {a b c : Pt} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab_ne : a ≠ b) (hbc_ne : b ≠ c) (hca_ne : c ≠ a)
    (hab : dist a b = s) (hbc : dist b c = s) (hca : dist c a = s) : False := by
  set T := ((S.erase a).erase b).erase c
  have hT : 2 ≤ T.card := by
    have hb1 : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab_ne.symm, hb⟩
    have hc2 : c ∈ (S.erase a).erase b :=
      Finset.mem_erase.mpr ⟨hbc_ne.symm, Finset.mem_erase.mpr ⟨hca_ne, hc⟩⟩
    rw [Finset.card_erase_of_mem hc2, Finset.card_erase_of_mem hb1, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨p, hpT, q, hqT, hpq⟩ := exists_two_of_two_le_card hT
  have hmem : ∀ z ∈ T, z ∈ S ∧ a ≠ z ∧ b ≠ z ∧ c ≠ z := by
    intro z hz
    rcases Finset.mem_erase.mp hz with ⟨hzc, hz1⟩
    rcases Finset.mem_erase.mp hz1 with ⟨hzb, hz2⟩
    rcases Finset.mem_erase.mp hz2 with ⟨hza, hzS⟩
    exact ⟨hzS, hza.symm, hzb.symm, hzc.symm⟩
  obtain ⟨hpS, hap, hbp, hcp⟩ := hmem p hpT
  obtain ⟨hqS, haq, hbq, hcq⟩ := hmem q hqT
  exact no_equilateral_in_five_two_dist hab_ne hap hbp hcp haq hbq hcq hpq hab hbc hca
    (h2 p hpS a ha hap.symm) (h2 p hpS b hb hbp.symm) (h2 p hpS c hc hcp.symm)
    (h2 q hqS a ha haq.symm) (h2 q hqS b hb hbq.symm) (h2 q hqS c hc hcq.symm)
    (h2 p hpS q hqS hpq)

private lemma deg_le_two_of_two_dist_card_ge_five {S : Finset Pt} {s t : ℝ}
    (hcard : 5 ≤ S.card)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = s ∨ dist x y = t)
    {v : Pt} (hv : v ∈ S) :
    ((S.erase v).filter (fun u => dist v u = s)).card ≤ 2 := by
  by_contra hgt
  have h3 : 3 ≤ ((S.erase v).filter (fun u => dist v u = s)).card := by omega
  obtain ⟨u1, hu1, u2, hu2, u3, hu3, h12, h23, h13⟩ := exists_three_of_three_le_card h3
  rcases Finset.mem_filter.mp hu1 with ⟨hu1e, hd1⟩
  rcases Finset.mem_filter.mp hu2 with ⟨hu2e, hd2⟩
  rcases Finset.mem_filter.mp hu3 with ⟨hu3e, hd3⟩
  rcases Finset.mem_erase.mp hu1e with ⟨hv1, hu1S⟩
  rcases Finset.mem_erase.mp hu2e with ⟨hv2, hu2S⟩
  rcases Finset.mem_erase.mp hu3e with ⟨hv3, hu3S⟩
  rcases h2 u1 hu1S u2 hu2S h12 with h12s | h12t
  · exact no_triangle_of_two_dist_card_ge_five hcard h2 hv hu1S hu2S
      hv1.symm h12 hv2 hd1 h12s (dist_comm v u2 ▸ hd2)
  · rcases h2 u2 hu2S u3 hu3S h23 with h23s | h23t
    · exact no_triangle_of_two_dist_card_ge_five hcard h2 hv hu2S hu3S
        hv2.symm h23 hv3 hd2 h23s (dist_comm v u3 ▸ hd3)
    · rcases h2 u1 hu1S u3 hu3S h13 with h13s | h13t
      · exact no_triangle_of_two_dist_card_ge_five hcard h2 hv hu1S hu3S
          hv1.symm h13 hv3 hd1 h13s (dist_comm v u3 ▸ hd3)
      · have h2' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = t ∨ dist x y = s :=
          fun x hx y hy hne => (h2 x hx y hy hne).symm
        exact no_triangle_of_two_dist_card_ge_five hcard h2' hu1S hu2S hu3S
          h12 h23 h13.symm h12t h23t (dist_comm u1 u3 ▸ h13t)

private lemma card_eq_five_and_deg_eq_two {S : Finset Pt} {s t : ℝ}
    (hcard : 5 ≤ S.card)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = s ∨ dist x y = t) :
    S.card = 5 ∧ s ≠ t ∧
      ∀ v ∈ S, ((S.erase v).filter (fun u => dist v u = s)).card = 2 ∧
               ((S.erase v).filter (fun u => dist v u = t)).card = 2 := by
  have h2' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = t ∨ dist x y = s :=
    fun x hx y hy hne => (h2 x hx y hy hne).symm
  have hsub : ∀ v ∈ S,
      S.erase v ⊆ (S.erase v).filter (fun u => dist v u = s) ∪
                  (S.erase v).filter (fun u => dist v u = t) := by
    intro v hv u hu
    rcases Finset.mem_erase.mp hu with ⟨huv, huS⟩
    rcases h2 v hv u huS huv.symm with hs | ht
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, ht⟩)
  have hcard5 : S.card = 5 := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hle1 := deg_le_two_of_two_dist_card_ge_five hcard h2 hv
    have hle2 := deg_le_two_of_two_dist_card_ge_five hcard h2' hv
    have hle : (S.erase v).card ≤ 4 :=
      (Finset.card_le_card (hsub v hv)).trans
        ((Finset.card_union_le _ _).trans (by omega))
    rw [Finset.card_erase_of_mem hv] at hle
    omega
  have hdeg : ∀ v ∈ S,
      ((S.erase v).filter (fun u => dist v u = s)).card = 2 ∧
      ((S.erase v).filter (fun u => dist v u = t)).card = 2 := by
    intro v hv
    have hle1 := deg_le_two_of_two_dist_card_ge_five hcard h2 hv
    have hle2 := deg_le_two_of_two_dist_card_ge_five hcard h2' hv
    have hge : 4 ≤ ((S.erase v).filter (fun u => dist v u = s)).card +
                   ((S.erase v).filter (fun u => dist v u = t)).card := by
      have h4 : (S.erase v).card = 4 := by rw [Finset.card_erase_of_mem hv]; omega
      calc 4 = (S.erase v).card := h4.symm
        _ ≤ _ := (Finset.card_le_card (hsub v hv)).trans (Finset.card_union_le _ _)
    omega
  have hst : s ≠ t := by
    rintro rfl
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hfilt : (S.erase v).filter (fun u => dist v u = s) = S.erase v := by
      ext u
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro hu
      rcases Finset.mem_erase.mp hu with ⟨huv, huS⟩
      rcases h2 v hv u huS huv.symm with h | h <;> exact h
    have h4 : (S.erase v).card = 4 := by rw [Finset.card_erase_of_mem hv]; omega
    have h2v := (hdeg v hv).1
    rw [hfilt, h4] at h2v
    omega
  exact ⟨hcard5, hst, hdeg⟩

private lemma exists_two_dists_of_card_le_two {A : Finset Pt}
    (hle : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 2) :
    ∃ s t : ℝ, ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = s ∨ dist x y = t := by
  set D := A.offDiag.image (fun p => dist p.1 p.2)
  by_cases h0 : D.card = 0
  · refine ⟨0, 0, fun x hx y hy hne => ?_⟩
    have hmem : dist x y ∈ D :=
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩
    exact False.elim (Finset.notMem_empty _ (Finset.card_eq_zero.mp h0 ▸ hmem))
  · obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
    by_cases h1 : (D.erase s).card = 0
    · refine ⟨s, s, fun x hx y hy hne => ?_⟩
      have hmem : dist x y ∈ D :=
        Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩
      by_cases heq : dist x y = s
      · exact Or.inl heq
      · exact False.elim (Finset.notMem_empty _
          (Finset.card_eq_zero.mp h1 ▸ Finset.mem_erase.mpr ⟨heq, hmem⟩))
    · obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < (D.erase s).card)
      have hcard_erase : ((D.erase s).erase t).card = 0 := by
        rw [Finset.card_erase_of_mem ht, Finset.card_erase_of_mem hs]
        omega
      refine ⟨s, t, fun x hx y hy hne => ?_⟩
      have hmem : dist x y ∈ D :=
        Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩
      by_cases heqs : dist x y = s
      · exact Or.inl heqs
      · by_cases heqt : dist x y = t
        · exact Or.inr heqt
        · exact False.elim (Finset.notMem_empty _
            (Finset.card_eq_zero.mp hcard_erase ▸
              Finset.mem_erase.mpr ⟨heqt, Finset.mem_erase.mpr ⟨heqs, hmem⟩⟩))

private lemma part1 (A : Finset Pt) (hcard : 5 ≤ A.card)
    (hle : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 2) :
    A.card = 5 ∧ (rareDistances A).card = 2 := by
  obtain ⟨s, t, h2⟩ := exists_two_dists_of_card_le_two hle
  obtain ⟨hcard5, hst, hdeg⟩ := card_eq_five_and_deg_eq_two hcard h2
  have hms : pairMultiplicity A s = 5 := by
    have h := two_mul_pairMultiplicity_eq_sum_deg A s
    have hsum : ∑ v ∈ A, ((A.erase v).filter (fun u => dist v u = s)).card = ∑ _v ∈ A, 2 :=
      Finset.sum_congr rfl fun v hv => (hdeg v hv).1
    rw [hsum, Finset.sum_const, smul_eq_mul, hcard5] at h
    omega
  have hmt : pairMultiplicity A t = 5 := by
    have h := two_mul_pairMultiplicity_eq_sum_deg A t
    have hsum : ∑ v ∈ A, ((A.erase v).filter (fun u => dist v u = t)).card = ∑ _v ∈ A, 2 :=
      Finset.sum_congr rfl fun v hv => (hdeg v hv).2
    rw [hsum, Finset.sum_const, smul_eq_mul, hcard5] at h
    omega
  have himg_eq : A.offDiag.image (fun p => dist p.1 p.2) = {s, t} := by
    ext d
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, hne⟩
      exact h2 p.1 hp1 p.2 hp2 hne
    · rintro (hd | hd)
      · rw [hd]
        have hpos : 0 < (A.offDiag.filter (fun p => dist p.1 p.2 = s)).card := by
          have := two_mul_pairMultiplicity A s; omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        rcases Finset.mem_filter.mp hp with ⟨hpo, hp_d⟩
        exact ⟨p, hpo, hp_d⟩
      · rw [hd]
        have hpos : 0 < (A.offDiag.filter (fun p => dist p.1 p.2 = t)).card := by
          have := two_mul_pairMultiplicity A t; omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        rcases Finset.mem_filter.mp hp with ⟨hpo, hp_d⟩
        exact ⟨p, hpo, hp_d⟩
  have hrare_eq : rareDistances A = {s, t} := by
    ext d
    rw [mem_rareDistances_iff, himg_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, by omega⟩
      · exact ⟨Or.inr rfl, by omega⟩
  rw [hrare_eq, Finset.card_pair hst]
  exact ⟨hcard5, rfl⟩

private lemma not_four_equidistant_two_dist {B : Finset Pt} {u v : Pt} {d1 d2 : ℝ}
    (hB : B.card = 4) (huv : u ≠ v)
    (heq : ∀ x ∈ B, dist x u = dist x v)
    (h2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → dist x y = d1 ∨ dist x y = d2) : False := by
  set wx := v 0 - u 0
  set wy := v 1 - u 1
  let f : Pt → ℝ := fun x => (-wy) * x 0 + wx * x 1
  have hduv_pos : 0 < dist u v := dist_pos.mpr huv
  have hduv_sq : wx ^ 2 + wy ^ 2 = dist u v ^ 2 := by
    have h := dist_sq_eq u v; dsimp only [wx, wy]; linarith
  have hdist_f : ∀ x ∈ B, ∀ y ∈ B, dist u v * dist x y = |f x - f y| := by
    intro x hx y hy
    have hxu : (x 0 - u 0) ^ 2 + (x 1 - u 1) ^ 2 = (x 0 - v 0) ^ 2 + (x 1 - v 1) ^ 2 := by
      have h1 := dist_sq_eq x u; have h2 := dist_sq_eq x v; rw [heq x hx] at h1; linarith
    have hyu : (y 0 - u 0) ^ 2 + (y 1 - u 1) ^ 2 = (y 0 - v 0) ^ 2 + (y 1 - v 1) ^ 2 := by
      have h1 := dist_sq_eq y u; have h2 := dist_sq_eq y v; rw [heq y hy] at h1; linarith
    have horth : wx * (x 0 - y 0) + wy * (x 1 - y 1) = 0 := by
      dsimp only [wx, wy]; linarith
    have hpar : (-wy) * (x 0 - y 0) + wx * (x 1 - y 1) = f x - f y := by
      dsimp only [f]; ring
    have hsq : (dist u v * dist x y) ^ 2 = |f x - f y| ^ 2 := by
      rw [sq_abs, mul_pow, ← hduv_sq, dist_sq_eq x y]
      have hid : (wx ^ 2 + wy ^ 2) * ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) =
          (wx * (x 0 - y 0) + wy * (x 1 - y 1)) ^ 2 +
            ((-wy) * (x 0 - y 0) + wx * (x 1 - y 1)) ^ 2 := by ring
      rw [hid, horth, hpar]; ring
    have hnn1 : 0 ≤ dist u v * dist x y := mul_nonneg dist_nonneg dist_nonneg
    have hnn2 : 0 ≤ |f x - f y| := abs_nonneg _
    nlinarith
  have hinj : Set.InjOn f B := by
    intro x hx y hy hxy
    have h0 : dist u v * dist x y = 0 := by
      rw [hdist_f x hx y hy, hxy, sub_self, abs_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact dist_eq_zero.mp h
  set T := B.image f
  have hT4 : T.card = 4 := by rw [Finset.card_image_of_injOn hinj, hB]
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  set t0 := T.min' hTne
  have ht0 : t0 ∈ T := Finset.min'_mem T hTne
  set T1 := T.erase t0
  have hT1 : T1.card = 3 := by rw [Finset.card_erase_of_mem ht0, hT4]
  have hT1ne : T1.Nonempty := Finset.card_pos.mp (by omega)
  set t1 := T1.min' hT1ne
  have ht1_1 : t1 ∈ T1 := Finset.min'_mem T1 hT1ne
  have ht1 : t1 ∈ T := (Finset.mem_erase.mp ht1_1).2
  set T2 := T1.erase t1
  have hT2 : T2.card = 2 := by rw [Finset.card_erase_of_mem ht1_1, hT1]
  have hT2ne : T2.Nonempty := Finset.card_pos.mp (by omega)
  set t2 := T2.min' hT2ne
  have ht2_2 : t2 ∈ T2 := Finset.min'_mem T2 hT2ne
  have ht2_1 : t2 ∈ T1 := (Finset.mem_erase.mp ht2_2).2
  have ht2 : t2 ∈ T := (Finset.mem_erase.mp ht2_1).2
  set T3 := T2.erase t2
  have hT3 : T3.card = 1 := by rw [Finset.card_erase_of_mem ht2_2, hT2]
  obtain ⟨t3, ht3_3⟩ := Finset.card_pos.mp (by omega : 0 < T3.card)
  have ht3_2 : t3 ∈ T2 := (Finset.mem_erase.mp ht3_3).2
  have ht3_1 : t3 ∈ T1 := (Finset.mem_erase.mp ht3_2).2
  have ht3 : t3 ∈ T := (Finset.mem_erase.mp ht3_1).2
  have hlt01 : t0 < t1 := lt_of_le_of_ne (Finset.min'_le T t1 ht1)
    (Finset.mem_erase.mp ht1_1).1.symm
  have hlt12 : t1 < t2 := lt_of_le_of_ne (Finset.min'_le T1 t2 ht2_1)
    (Finset.mem_erase.mp ht2_2).1.symm
  have hlt23 : t2 < t3 := lt_of_le_of_ne (Finset.min'_le T2 t3 ht3_2)
    (Finset.mem_erase.mp ht3_3).1.symm
  rcases Finset.mem_image.mp ht0 with ⟨x0, hx0, hfx0⟩
  rcases Finset.mem_image.mp ht1 with ⟨x1, hx1, hfx1⟩
  rcases Finset.mem_image.mp ht2 with ⟨x2, hx2, hfx2⟩
  rcases Finset.mem_image.mp ht3 with ⟨x3, hx3, hfx3⟩
  have hne01 : x0 ≠ x1 := fun h => by rw [h] at hfx0; linarith
  have hne02 : x0 ≠ x2 := fun h => by rw [h] at hfx0; linarith
  have hne03 : x0 ≠ x3 := fun h => by rw [h] at hfx0; linarith
  have hd01 : dist u v * dist x0 x1 = t1 - t0 := by
    rw [hdist_f x0 hx0 x1 hx1, hfx0, hfx1, abs_of_neg (by linarith)]; ring
  have hd02 : dist u v * dist x0 x2 = t2 - t0 := by
    rw [hdist_f x0 hx0 x2 hx2, hfx0, hfx2, abs_of_neg (by linarith)]; ring
  have hd03 : dist u v * dist x0 x3 = t3 - t0 := by
    rw [hdist_f x0 hx0 x3 hx3, hfx0, hfx3, abs_of_neg (by linarith)]; ring
  have hlt_d12 : dist x0 x1 < dist x0 x2 := by nlinarith
  have hlt_d23 : dist x0 x2 < dist x0 x3 := by nlinarith
  rcases h2 x0 hx0 x1 hx1 hne01 with h1 | h1 <;>
    rcases h2 x0 hx0 x2 hx2 hne02 with h2' | h2' <;>
    rcases h2 x0 hx0 x3 hx3 hne03 with h3 | h3 <;> linarith

private lemma part2 (A : Finset Pt) (hcard : A.card = 6) :
    2 ≤ (rareDistances A).card := by
  by_contra hlt
  have hR_le : (rareDistances A).card ≤ 1 := by omega
  set D := A.offDiag.image (fun p => dist p.1 p.2)
  set R := rareDistances A
  set N := D \ R
  have hR_sub : R ⊆ D := Finset.filter_subset _ _
  have hD_card : D.card = R.card + N.card := by
    have h := Finset.card_sdiff_add_card_eq_card hR_sub
    change N.card + R.card = D.card at h
    omega
  have hsum_D : ∑ d ∈ D, pairMultiplicity A d = 15 := by
    have h := two_mul_sum_pairMultiplicity A
    change 2 * ∑ d ∈ D, pairMultiplicity A d = A.card * (A.card - 1) at h
    rw [hcard] at h
    omega
  have hN_ge7 : ∀ d ∈ N, 7 ≤ pairMultiplicity A d := by
    intro d hd
    rcases Finset.mem_sdiff.mp hd with ⟨hdD, hdR⟩
    rw [mem_rareDistances_iff] at hdR
    have hnot : ¬ pairMultiplicity A d ≤ A.card := fun hle => hdR ⟨hdD, hle⟩
    omega
  have hsum_N_le : ∑ d ∈ N, pairMultiplicity A d ≤ 15 := by
    rw [← hsum_D]
    exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hN_le : N.card ≤ 2 := by
    have h7 : 7 * N.card ≤ ∑ d ∈ N, pairMultiplicity A d := by
      calc 7 * N.card = ∑ _d ∈ N, 7 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ d ∈ N, pairMultiplicity A d := Finset.sum_le_sum hN_ge7
    omega
  have hD_ge3 : 3 ≤ D.card := by
    by_contra hle2
    have h5 := (part1 A (by omega) (by change D.card ≤ 2; omega)).1
    omega
  have hR1 : R.card = 1 := by omega
  have hN2 : N.card = 2 := by omega
  obtain ⟨d3, hd3_eq⟩ := Finset.card_eq_one.mp hR1
  obtain ⟨d1, d2, hd12, hN_eq⟩ := Finset.card_eq_two.mp hN2
  have hd3R : d3 ∈ R := by rw [hd3_eq]; exact Finset.mem_singleton_self d3
  have hd3D : d3 ∈ D := hR_sub hd3R
  have hd1N : d1 ∈ N := by rw [hN_eq]; exact Finset.mem_insert_self d1 {d2}
  have hd2N : d2 ∈ N := by rw [hN_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self d2)
  have hD_eq : D = insert d3 {d1, d2} := by
    have hu : R ∪ N = D := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hR_sub
    rw [← hu, hd3_eq, hN_eq]
    ext x; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  have hd3_not_N : d3 ∉ ({d1, d2} : Finset ℝ) := by
    rw [← hN_eq]; intro h; exact (Finset.mem_sdiff.mp h).2 hd3R
  have hsum_3 : pairMultiplicity A d3 + pairMultiplicity A d1 + pairMultiplicity A d2 = 15 := by
    rw [hD_eq, Finset.sum_insert hd3_not_N, Finset.sum_pair hd12] at hsum_D
    omega
  have hm1 : 7 ≤ pairMultiplicity A d1 := hN_ge7 d1 hd1N
  have hm2 : 7 ≤ pairMultiplicity A d2 := hN_ge7 d2 hd2N
  have hm3_ge : 1 ≤ pairMultiplicity A d3 := pairMultiplicity_pos_of_mem_image hd3D
  have hm3 : pairMultiplicity A d3 = 1 := by omega
  set S3 := A.offDiag.filter (fun p => dist p.1 p.2 = d3)
  have hS3_card : S3.card = 2 := by
    have h := two_mul_pairMultiplicity A d3
    change 2 * pairMultiplicity A d3 = S3.card at h
    omega
  obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < S3.card)
  rcases Finset.mem_filter.mp hp0 with ⟨hp0o, hp0d⟩
  rcases Finset.mem_offDiag.mp hp0o with ⟨huA, hvA, huv⟩
  set u := p0.1
  set v := p0.2
  have huv_mem : (u, v) ∈ S3 := hp0
  have hvu_mem : (v, u) ∈ S3 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hvA, huA, huv.symm⟩, ?_⟩
    simpa only [dist_comm] using hp0d
  have huv_ne_vu : (u, v) ≠ (v, u) := fun h => huv (congrArg Prod.fst h)
  have hS3_eq : S3 = {(u, v), (v, u)} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact huv_mem
      · rw [Finset.mem_singleton.mp hq]; exact hvu_mem
    · rw [hS3_card, Finset.card_pair huv_ne_vu]
  have hdist_other : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
      dist x y = d1 ∨ dist x y = d2 := by
    intro x hx y hy hne hnot
    have hmemD : dist x y ∈ D :=
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩
    rw [hD_eq] at hmemD
    rcases Finset.mem_insert.mp hmemD with hd | hd
    · exfalso
      have hmemS3 : (x, y) ∈ S3 :=
        Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, hd⟩
      rw [hS3_eq] at hmemS3
      rcases Finset.mem_insert.mp hmemS3 with h | h
      · exact hnot (Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
      · have h' := Finset.mem_singleton.mp h
        exact hnot (Or.inr ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩)
    · rcases Finset.mem_insert.mp hd with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
  set Au := A.erase v
  set Av := A.erase u
  have hAu_card : Au.card = 5 := by rw [Finset.card_erase_of_mem hvA, hcard]
  have hAv_card : Av.card = 5 := by rw [Finset.card_erase_of_mem huA, hcard]
  have hAu_2 : ∀ x ∈ Au, ∀ y ∈ Au, x ≠ y → dist x y = d1 ∨ dist x y = d2 := by
    intro x hx y hy hne
    rcases Finset.mem_erase.mp hx with ⟨hxv, hxA⟩
    rcases Finset.mem_erase.mp hy with ⟨hyv, hyA⟩
    exact hdist_other x hxA y hyA hne (by rintro (⟨_, rfl⟩ | ⟨rfl, _⟩) <;> contradiction)
  have hAv_2 : ∀ x ∈ Av, ∀ y ∈ Av, x ≠ y → dist x y = d1 ∨ dist x y = d2 := by
    intro x hx y hy hne
    rcases Finset.mem_erase.mp hx with ⟨hxu, hxA⟩
    rcases Finset.mem_erase.mp hy with ⟨hyu, hyA⟩
    exact hdist_other x hxA y hyA hne (by rintro (⟨rfl, _⟩ | ⟨_, rfl⟩) <;> contradiction)
  have hdeg_Au := (card_eq_five_and_deg_eq_two (by omega) hAu_2).2.2
  have hdeg_Av := (card_eq_five_and_deg_eq_two (by omega) hAv_2).2.2
  set B := (A.erase u).erase v
  have hv_Au : v ∈ A.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvA⟩
  have hB_card : B.card = 4 := by
    rw [Finset.card_erase_of_mem hv_Au, Finset.card_erase_of_mem huA, hcard]
  have hB_sub_Au : B ⊆ Au := by
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxv, hxu⟩
    exact Finset.mem_erase.mpr ⟨hxv, (Finset.mem_erase.mp hxu).2⟩
  have hB_sub_Av : B ⊆ Av := Finset.erase_subset v Av
  have heq_B : ∀ x ∈ B, dist x u = dist x v := by
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxv, hxu⟩
    rcases Finset.mem_erase.mp hxu with ⟨hxu_ne, hxA⟩
    have hAu_erase : Au.erase x = insert u (B.erase x) := by
      ext y
      simp only [Au, B, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hyx, hyv, hyA⟩
        by_cases hyu : y = u
        · exact Or.inl hyu
        · exact Or.inr ⟨hyx, hyv, hyu, hyA⟩
      · rintro (rfl | ⟨hyx, hyv, _, hyA⟩)
        · exact ⟨hxu_ne.symm, huv, huA⟩
        · exact ⟨hyx, hyv, hyA⟩
    have hAv_erase : Av.erase x = insert v (B.erase x) := by
      ext y
      simp only [Av, B, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hyx, hyu, hyA⟩
        by_cases hyv : y = v
        · exact Or.inl hyv
        · exact Or.inr ⟨hyx, hyv, hyu, hyA⟩
      · rintro (rfl | ⟨hyx, _, hyu, hyA⟩)
        · exact ⟨hxv.symm, huv.symm, hvA⟩
        · exact ⟨hyx, hyu, hyA⟩
    have hu_not_B : u ∉ B.erase x := fun h =>
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2).1 rfl
    have hv_not_B : v ∉ B.erase x := fun h =>
      (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
    have hcu := (hdeg_Au x (hB_sub_Au hx)).1
    have hcv := (hdeg_Av x (hB_sub_Av hx)).1
    rw [hAu_erase, Finset.filter_insert] at hcu
    rw [hAv_erase, Finset.filter_insert] at hcv
    have hiff : dist x u = d1 ↔ dist x v = d1 := by
      by_cases h1 : dist x u = d1 <;> by_cases h2 : dist x v = d1
      · simp [h1, h2]
      · simp only [h1, h2, ite_true, ite_false] at hcu hcv
        rw [Finset.card_insert_of_notMem (fun h => hu_not_B (Finset.mem_filter.mp h).1)] at hcu
        omega
      · simp only [h1, h2, ite_true, ite_false] at hcu hcv
        rw [Finset.card_insert_of_notMem (fun h => hv_not_B (Finset.mem_filter.mp h).1)] at hcv
        omega
      · simp [h1, h2]
    have hxu_or : dist x u = d1 ∨ dist x u = d2 :=
      hAu_2 x (hB_sub_Au hx) u (Finset.mem_erase.mpr ⟨huv, huA⟩) hxu_ne
    have hxv_or : dist x v = d1 ∨ dist x v = d2 :=
      hAv_2 x (hB_sub_Av hx) v (Finset.mem_erase.mpr ⟨huv.symm, hvA⟩) hxv
    rcases hxu_or with h1 | h1 <;> rcases hxv_or with h2 | h2
    · rw [h1, h2]
    · have := hiff.mp h1; rw [h1, this]
    · have := hiff.mpr h2; rw [this, h2]
    · rw [h1, h2]
  have hB_2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → dist x y = d1 ∨ dist x y = d2 :=
    fun x hx y hy hne => hAu_2 x (hB_sub_Au hx) y (hB_sub_Au hy) hne
  exact not_four_equidistant_two_dist hB_card huv heq_B hB_2

end Erdos132R1H1R2H1

theorem OMA.solution : OMA.R_erdos_132_R1_H1_R2.H1 :=
  ⟨Erdos132R1H1R2H1.part1, Erdos132R1H1R2H1.part2⟩
