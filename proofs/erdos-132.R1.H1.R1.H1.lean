import OMAReductions.R_erdos_132_R1_H1_R1

namespace OMA.AltmanProof

open scoped Classical

private abbrev Pt := EuclideanSpace ℝ (Fin 2)

private def mkPt (x y : ℝ) : Pt :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then x else y)

@[simp]
private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl

@[simp]
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

private lemma pt_ext {p q : Pt} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

private def cross2 (u v : Pt) : ℝ :=
  u 0 * v 1 - u 1 * v 0

private lemma dist_sq_eq (p q : Pt) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

private lemma dist_eq_sqrt (p q : Pt) :
    dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by
  rw [← dist_sq_eq, Real.sqrt_sq dist_nonneg]

private lemma cross2_cyclic (a b c : Pt) :
    cross2 (b - a) (c - a) = cross2 (c - b) (a - b) := by
  simp only [cross2, PiLp.sub_apply]
  ring

private lemma cross2_swap_neg (a b c : Pt) :
    cross2 (b - c) (a - c) = -cross2 (b - a) (c - a) := by
  simp only [cross2, PiLp.sub_apply]
  ring

private lemma cross2_sub_origin (o a b c : Pt) :
    cross2 (b - a) (c - a) =
      cross2 (a - o) (b - o) + cross2 (b - o) (c - o) + cross2 (c - o) (a - o) := by
  simp only [cross2, PiLp.sub_apply]
  ring

private lemma cramer2 (u v w : Pt) (h : cross2 u w ≠ 0) :
    v = (cross2 v w / cross2 u w) • u + (cross2 u v / cross2 u w) • w := by
  have hd : u 0 * w 1 - u 1 * w 0 ≠ 0 := h
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cross2]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hd]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cross2]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hd]
    ring

private lemma strict_triangle_of_cross2_ne_zero (a b c : Pt)
    (h : cross2 (b - a) (c - a) ≠ 0) :
    dist a c < dist a b + dist b c := by
  have hsq : dist a c ^ 2 < (dist a b + dist b c) ^ 2 := by
    have hac := dist_sq_eq a c
    have hab := dist_sq_eq a b
    have hbc := dist_sq_eq b c
    have hdot_lt : (b 0 - a 0) * (c 0 - b 0) + (b 1 - a 1) * (c 1 - b 1) <
        dist a b * dist b c := by
      have hcr : (b 0 - a 0) * (c 1 - b 1) - (b 1 - a 1) * (c 0 - b 0) ≠ 0 := by
        intro heq
        apply h
        simp only [cross2, PiLp.sub_apply]
        linarith
      have hlag :
          ((b 0 - a 0) * (c 0 - b 0) + (b 1 - a 1) * (c 1 - b 1)) ^ 2 <
            (dist a b * dist b c) ^ 2 := by
        have hpos : 0 < ((b 0 - a 0) * (c 1 - b 1) - (b 1 - a 1) * (c 0 - b 0)) ^ 2 :=
          sq_pos_of_ne_zero hcr
        have hprod : (dist a b * dist b c) ^ 2 = dist a b ^ 2 * dist b c ^ 2 := mul_pow _ _ 2
        rw [hprod, hab, hbc]
        nlinarith
      have hnn : 0 ≤ dist a b * dist b c := mul_nonneg dist_nonneg dist_nonneg
      nlinarith
    have hident :
        (a 0 - c 0) ^ 2 + (a 1 - c 1) ^ 2 =
          ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2) + ((b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2) +
            2 * ((b 0 - a 0) * (c 0 - b 0) + (b 1 - a 1) * (c 1 - b 1)) := by ring
    nlinarith
  have hnn : 0 ≤ dist a b + dist b c := add_nonneg dist_nonneg dist_nonneg
  nlinarith [dist_nonneg (x := a) (y := c)]

private lemma dist_add_of_segment (a b : Pt) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist a ((1 - t) • a + t • b) + dist ((1 - t) • a + t • b) b = dist a b := by
  have h1 : dist a ((1 - t) • a + t • b) = t * dist a b := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : a - ((1 - t) • a + t • b) = t • (a - b) := by
      apply pt_ext <;> simp <;> ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have h2 : dist ((1 - t) • a + t • b) b = (1 - t) * dist a b := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : ((1 - t) • a + t • b) - b = (1 - t) • (a - b) := by
      apply pt_ext <;> simp <;> ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [h1, h2]
  ring

private lemma dist_homothety (o p q : Pt) {lam : ℝ} (hlam : 0 ≤ lam) :
    dist (o + lam • (p - o)) (o + lam • (q - o)) = lam * dist p q := by
  rw [dist_eq_norm, dist_eq_norm]
  have heq : (o + lam • (p - o)) - (o + lam • (q - o)) = lam • (p - q) := by
    apply pt_ext <;> simp <;> ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]

private lemma dist_homothety_center (o p : Pt) {lam : ℝ} (hlam : 0 ≤ lam) :
    dist (o + lam • (p - o)) o = lam * dist p o := by
  simpa using dist_homothety o p o hlam

-- Centroid elimination and cyclic CCW ordering

private noncomputable def centroid (C : Finset Pt) : Pt :=
  ((C.card : ℝ)⁻¹) • ∑ x ∈ C, x

private lemma centroid_combo_ne {C : Finset Pt}
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt))
    (hcard : 2 ≤ C.card) {b a c : Pt} (hb : b ∈ C)
    (ha : a ∈ C.erase b) (hc : c ∈ C.erase b)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    b ≠ (1 - s - t) • centroid C + s • a + t • c := by
  intro hbeq
  set n : ℝ := (C.card : ℝ)
  have hn2 : (2 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hcard
  have hn0 : 0 < n := by linarith
  set r : ℝ := 1 - s - t
  have hr0 : 0 ≤ r := by linarith
  have hr1 : r ≤ 1 := by linarith
  set denom : ℝ := 1 - r / n
  have hdenom_pos : 0 < denom := by
    have : r / n ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  let w : Pt → ℝ := fun x =>
    (r / n + (if x = a then s else 0) + (if x = c then t else 0)) / denom
  have hw0 : ∀ x ∈ C.erase b, 0 ≤ w x := by
    intro x _
    dsimp [w]
    have h1 : 0 ≤ r / n := div_nonneg hr0 hn0.le
    have h2 : 0 ≤ if x = a then s else 0 := by split_ifs <;> linarith
    have h3 : 0 ≤ if x = c then t else 0 := by split_ifs <;> linarith
    exact div_nonneg (by linarith) hdenom_pos.le
  have hsum_w : ∑ x ∈ C.erase b, w x = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq', ha, hc, ↓reduceIte]
    have hcard_erase : ((C.erase b).card : ℝ) = n - 1 := by
      rw [Finset.card_erase_of_mem hb, Nat.cast_sub (by omega : 1 ≤ C.card)]
      simp [n]
    rw [hcard_erase]
    have hnum : (n - 1) * (r / n) + s + t = denom := by
      dsimp [denom, r]
      field_simp [hn0.ne']
      ring
    rw [hnum, div_self hdenom_pos.ne']
  have hsum_pt : ∑ x ∈ C.erase b, w x • x = b := by
    have hsplit_sum : ∑ x ∈ C, x = b + ∑ x ∈ C.erase b, x :=
      (Finset.add_sum_erase C (fun x => x) hb).symm
    have hcent : r • centroid C = (r / n) • b + (r / n) • ∑ x ∈ C.erase b, x := by
      unfold centroid
      rw [hsplit_sum, smul_add, smul_add, smul_smul, smul_smul]
      have hmul : r * (C.card : ℝ)⁻¹ = r / n := (div_eq_mul_inv r n).symm
      rw [hmul]
    have hnum_sum : ∑ x ∈ C.erase b,
        (r / n + (if x = a then s else 0) + (if x = c then t else 0)) • x = denom • b := by
      have hexp : ∑ x ∈ C.erase b,
          (r / n + (if x = a then s else 0) + (if x = c then t else 0)) • x =
          (∑ x ∈ C.erase b, (r / n) • x) +
          (∑ x ∈ C.erase b, (if x = a then s else 0) • x) +
          (∑ x ∈ C.erase b, (if x = c then t else 0) • x) := by
        simp only [add_smul, Finset.sum_add_distrib]
      rw [hexp, ← Finset.smul_sum]
      have hia : ∑ x ∈ C.erase b, (if x = a then s else 0) • x = s • a := by
        have : ∀ x ∈ C.erase b, (if x = a then s else 0) • x = if x = a then s • x else 0 := by
          intro x _
          split_ifs <;> simp
        rw [Finset.sum_congr rfl this]
        simp [ha]
      have hic : ∑ x ∈ C.erase b, (if x = c then t else 0) • x = t • c := by
        have : ∀ x ∈ C.erase b, (if x = c then t else 0) • x = if x = c then t • x else 0 := by
          intro x _
          split_ifs <;> simp
        rw [Finset.sum_congr rfl this]
        simp [hc]
      rw [hia, hic]
      apply pt_ext
      · have h0 := congrArg (fun p : Pt => p 0) hbeq
        have hc0 := congrArg (fun p : Pt => p 0) hcent
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 hc0 ⊢
        dsimp [denom, r] at h0 hc0 ⊢
        linarith
      · have h1 := congrArg (fun p : Pt => p 1) hbeq
        have hc1 := congrArg (fun p : Pt => p 1) hcent
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h1 hc1 ⊢
        dsimp [denom, r] at h1 hc1 ⊢
        linarith
    have hdiv_sum : ∑ x ∈ C.erase b, w x • x =
        denom⁻¹ • ∑ x ∈ C.erase b,
          (r / n + (if x = a then s else 0) + (if x = c then t else 0)) • x := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp [w]
      rw [div_eq_inv_mul, mul_smul]
    rw [hdiv_sum, hnum_sum, inv_smul_smul₀ hdenom_pos.ne']
  have hmem : b ∈ convexHull ℝ (↑(C.erase b) : Set Pt) := by
    have hcm := Finset.centerMass_mem_convexHull (t := C.erase b) (s := (↑(C.erase b) : Set Pt))
      hw0 (by linarith) (fun x hx => Finset.mem_coe.mpr hx)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum_w, hsum_pt] at hcm
    exact hcm
  exact hconv b hb hmem

private lemma centroid_not_mem {C : Finset Pt}
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt))
    (hcard : 2 ≤ C.card) :
    centroid C ∉ C := by
  intro hmem
  have hne : (C.erase (centroid C)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hmem]
    omega
  obtain ⟨a, ha⟩ := hne
  have := centroid_combo_ne hconv hcard hmem ha ha (s := 0) (t := 0) le_rfl le_rfl (by norm_num)
  simp at this

private def toComplex (u : Pt) : ℂ := ⟨u 0, u 1⟩

private noncomputable def polarAngle (o p : Pt) : ℝ := (toComplex (p - o)).arg

private lemma toComplex_ne_zero {u : Pt} (hu : u ≠ 0) : toComplex u ≠ 0 := by
  intro h
  apply hu
  apply pt_ext
  · simpa [toComplex] using congrArg Complex.re h
  · simpa [toComplex] using congrArg Complex.im h

private lemma pt_coord_polar {u : Pt} (hu : u ≠ 0) :
    u 0 = ‖toComplex u‖ * Real.cos (toComplex u).arg ∧
    u 1 = ‖toComplex u‖ * Real.sin (toComplex u).arg := by
  have hz : toComplex u ≠ 0 := toComplex_ne_zero hu
  have hnorm : ‖toComplex u‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · have hcos := Complex.cos_arg hz
    change Real.cos (toComplex u).arg = u 0 / ‖toComplex u‖ at hcos
    rw [hcos, mul_div_cancel₀ _ hnorm]
  · have hsin := Complex.sin_arg (toComplex u)
    change Real.sin (toComplex u).arg = u 1 / ‖toComplex u‖ at hsin
    rw [hsin, mul_div_cancel₀ _ hnorm]

private lemma cross2_polar {u v : Pt} (hu : u ≠ 0) (hv : v ≠ 0) :
    cross2 u v = ‖toComplex u‖ * ‖toComplex v‖ *
      Real.sin ((toComplex v).arg - (toComplex u).arg) := by
  obtain ⟨hu0, hu1⟩ := pt_coord_polar hu
  obtain ⟨hv0, hv1⟩ := pt_coord_polar hv
  rw [cross2, hu0, hu1, hv0, hv1, Real.sin_sub]
  ring

private lemma polarAngle_injOn {C : Finset Pt}
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt))
    (hcard : 2 ≤ C.card) :
    Set.InjOn (polarAngle (centroid C)) (↑C : Set Pt) := by
  intro a ha b hb harg
  by_contra hab
  have haC : a ∈ C := Finset.mem_coe.mp ha
  have hbC : b ∈ C := Finset.mem_coe.mp hb
  have ho : centroid C ∉ C := centroid_not_mem hconv hcard
  have hua : a - centroid C ≠ 0 := sub_ne_zero.mpr (fun h => ho (h ▸ haC))
  have hub : b - centroid C ≠ 0 := sub_ne_zero.mpr (fun h => ho (h ▸ hbC))
  obtain ⟨ha0, ha1⟩ := pt_coord_polar hua
  obtain ⟨hb0, hb1⟩ := pt_coord_polar hub
  set ra := ‖toComplex (a - centroid C)‖
  set rb := ‖toComplex (b - centroid C)‖
  have hra : 0 < ra := norm_pos_iff.mpr (toComplex_ne_zero hua)
  have hrb : 0 < rb := norm_pos_iff.mpr (toComplex_ne_zero hub)
  unfold polarAngle at harg
  rw [← harg] at hb0 hb1
  have hrel0 : rb * (a 0 - centroid C 0) = ra * (b 0 - centroid C 0) := by
    have ha0' : a 0 - centroid C 0 = ra * Real.cos (toComplex (a - centroid C)).arg := ha0
    have hb0' : b 0 - centroid C 0 = rb * Real.cos (toComplex (a - centroid C)).arg := hb0
    rw [ha0', hb0']; ring
  have hrel1 : rb * (a 1 - centroid C 1) = ra * (b 1 - centroid C 1) := by
    have ha1' : a 1 - centroid C 1 = ra * Real.sin (toComplex (a - centroid C)).arg := ha1
    have hb1' : b 1 - centroid C 1 = rb * Real.sin (toComplex (a - centroid C)).arg := hb1
    rw [ha1', hb1']; ring
  rcases le_total rb ra with hle | hle
  · have ha_erase : a ∈ C.erase b := Finset.mem_erase.mpr ⟨hab, haC⟩
    have hne := centroid_combo_ne hconv hcard hbC ha_erase ha_erase
      (s := rb / ra) (t := 0) (div_nonneg hrb.le hra.le) le_rfl
      (by rw [add_zero]; exact (div_le_one hra).mpr hle)
    apply hne
    apply pt_ext
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, zero_mul, add_zero]
      field_simp [hra.ne']
      linarith
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, zero_mul, add_zero]
      field_simp [hra.ne']
      linarith
  · have hb_erase : b ∈ C.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hbC⟩
    have hne := centroid_combo_ne hconv hcard haC hb_erase hb_erase
      (s := ra / rb) (t := 0) (div_nonneg hra.le hrb.le) le_rfl
      (by rw [add_zero]; exact (div_le_one hrb).mpr hle)
    apply hne
    apply pt_ext
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, zero_mul, add_zero]
      field_simp [hrb.ne']
      linarith
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, zero_mul, add_zero]
      field_simp [hrb.ne']
      linarith

private lemma ccw_of_pos_sector {C : Finset Pt}
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt))
    (hcard : 2 ≤ C.card) {x y z : Pt}
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hzy : z ≠ y)
    (h1 : 0 < cross2 (x - centroid C) (y - centroid C))
    (h2 : 0 < cross2 (y - centroid C) (z - centroid C))
    (h3 : 0 < cross2 (x - centroid C) (z - centroid C)) :
    0 < cross2 (y - x) (z - x) := by
  by_contra hle
  push Not at hle
  set o := centroid C
  have hcr := cramer2 (x - o) (y - o) (z - o) h3.ne'
  set s := cross2 (y - o) (z - o) / cross2 (x - o) (z - o)
  set t := cross2 (x - o) (y - o) / cross2 (x - o) (z - o)
  have hs : 0 ≤ s := div_nonneg h2.le h3.le
  have ht : 0 ≤ t := div_nonneg h1.le h3.le
  have hst : s + t ≤ 1 := by
    have hsub := cross2_sub_origin o x y z
    have hneg : cross2 (z - o) (x - o) = -cross2 (x - o) (z - o) := by
      simp only [cross2]; ring
    dsimp [s, t]
    rw [← add_div, div_le_one h3]
    linarith
  have hyeq : y = (1 - s - t) • o + s • x + t • z := by
    apply pt_ext
    · have h0 := congrArg (fun p : Pt => p 0) hcr
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 ⊢
      linarith
    · have h1' := congrArg (fun p : Pt => p 1) hcr
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h1' ⊢
      linarith
  exact centroid_combo_ne hconv hcard hy
    (Finset.mem_erase.mpr ⟨hxy, hx⟩) (Finset.mem_erase.mpr ⟨hzy, hz⟩) hs ht hst hyeq

private lemma ccw_of_polarAngle_lt {C : Finset Pt}
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt))
    (hcard : 2 ≤ C.card) {a b c : Pt}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (hab_ang : polarAngle (centroid C) a < polarAngle (centroid C) b)
    (hbc_ang : polarAngle (centroid C) b < polarAngle (centroid C) c) :
    0 < cross2 (b - a) (c - a) := by
  set o := centroid C
  have ho : o ∉ C := centroid_not_mem hconv hcard
  have hab : a ≠ b := fun h => by rw [h] at hab_ang; exact lt_irrefl _ hab_ang
  have hbc : b ≠ c := fun h => by rw [h] at hbc_ang; exact lt_irrefl _ hbc_ang
  have hac : a ≠ c := fun h => by rw [h] at hab_ang; linarith
  have hua : a - o ≠ 0 := sub_ne_zero.mpr (fun h => ho (h ▸ ha))
  have hub : b - o ≠ 0 := sub_ne_zero.mpr (fun h => ho (h ▸ hb))
  have huc : c - o ≠ 0 := sub_ne_zero.mpr (fun h => ho (h ▸ hc))
  set ra := ‖toComplex (a - o)‖
  set rb := ‖toComplex (b - o)‖
  set rc := ‖toComplex (c - o)‖
  have hra : 0 < ra := norm_pos_iff.mpr (toComplex_ne_zero hua)
  have hrb : 0 < rb := norm_pos_iff.mpr (toComplex_ne_zero hub)
  have hrc : 0 < rc := norm_pos_iff.mpr (toComplex_ne_zero huc)
  set θa := (toComplex (a - o)).arg
  set θb := (toComplex (b - o)).arg
  set θc := (toComplex (c - o)).arg
  have hθa_gt : -Real.pi < θa := Complex.neg_pi_lt_arg _
  have hθc_le : θc ≤ Real.pi := Complex.arg_le_pi _
  set α := θb - θa
  set β := θc - θb
  set γ := 2 * Real.pi - (θc - θa)
  have hα0 : 0 < α := sub_pos.mpr hab_ang
  have hβ0 : 0 < β := sub_pos.mpr hbc_ang
  have hγ0 : 0 < γ := by dsimp [γ]; linarith
  have hsum : α + β + γ = 2 * Real.pi := by dsimp [α, β, γ]; ring
  have hcab : cross2 (a - o) (b - o) = ra * rb * Real.sin α := cross2_polar hua hub
  have hcbc : cross2 (b - o) (c - o) = rb * rc * Real.sin β := cross2_polar hub huc
  have hcca : cross2 (c - o) (a - o) = rc * ra * Real.sin γ := by
    rw [cross2_polar huc hua]
    have : θa - θc = γ - 2 * Real.pi := by dsimp [γ]; ring
    rw [this, Real.sin_sub_two_pi]
  have hcac : cross2 (a - o) (c - o) = ra * rc * Real.sin (α + β) := by
    rw [cross2_polar hua huc]
    have : θc - θa = α + β := by dsimp [α, β]; ring
    rw [this]
  have hcba : cross2 (b - o) (a - o) = rb * ra * Real.sin (β + γ) := by
    rw [cross2_polar hub hua]
    have : θa - θb = (β + γ) - 2 * Real.pi := by dsimp [α, β, γ]; ring
    rw [this, Real.sin_sub_two_pi]
  have hccb : cross2 (c - o) (b - o) = rc * rb * Real.sin (γ + α) := by
    rw [cross2_polar huc hub]
    have : θb - θc = (γ + α) - 2 * Real.pi := by dsimp [α, β, γ]; ring
    rw [this, Real.sin_sub_two_pi]
  by_cases hγ : Real.pi < γ
  · have hαβ : α + β < Real.pi := by linarith
    exact ccw_of_pos_sector hconv hcard ha hb hc hab (Ne.symm hbc)
      (by rw [hcab]; exact mul_pos (mul_pos hra hrb) (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith)))
      (by rw [hcbc]; exact mul_pos (mul_pos hrb hrc) (Real.sin_pos_of_pos_of_lt_pi hβ0 (by linarith)))
      (by rw [hcac]; exact mul_pos (mul_pos hra hrc) (Real.sin_pos_of_pos_of_lt_pi (by linarith) hαβ))
  · by_cases hα : Real.pi < α
    · have hβγ : β + γ < Real.pi := by linarith
      rw [cross2_cyclic]
      exact ccw_of_pos_sector hconv hcard hb hc ha hbc hac
        (by rw [hcbc]; exact mul_pos (mul_pos hrb hrc) (Real.sin_pos_of_pos_of_lt_pi hβ0 (by linarith)))
        (by rw [hcca]; exact mul_pos (mul_pos hrc hra) (Real.sin_pos_of_pos_of_lt_pi hγ0 (by linarith)))
        (by rw [hcba]; exact mul_pos (mul_pos hrb hra) (Real.sin_pos_of_pos_of_lt_pi (by linarith) hβγ))
    · by_cases hβ : Real.pi < β
      · have hγα : γ + α < Real.pi := by linarith
        rw [cross2_cyclic, cross2_cyclic]
        exact ccw_of_pos_sector hconv hcard hc ha hb (Ne.symm hac) (Ne.symm hab)
          (by rw [hcca]; exact mul_pos (mul_pos hrc hra) (Real.sin_pos_of_pos_of_lt_pi hγ0 (by linarith)))
          (by rw [hcab]; exact mul_pos (mul_pos hra hrb) (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith)))
          (by rw [hccb]; exact mul_pos (mul_pos hrc hrb) (Real.sin_pos_of_pos_of_lt_pi (by linarith) hγα))
      · push Not at hγ hα hβ
        rw [cross2_sub_origin o, hcab, hcbc, hcca]
        have hsα : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0.le hα
        have hsβ : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ0.le hβ
        have hsγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0.le hγ
        have hlt_one : α < Real.pi ∨ β < Real.pi ∨ γ < Real.pi := by
          by_contra hall
          push Not at hall
          have hpi : 0 < Real.pi := Real.pi_pos
          linarith
        rcases hlt_one with hlt | hlt | hlt
        · have hp := Real.sin_pos_of_pos_of_lt_pi hα0 hlt
          nlinarith [mul_pos hra hrb, mul_nonneg (mul_pos hrb hrc).le hsβ,
            mul_nonneg (mul_pos hrc hra).le hsγ]
        · have hp := Real.sin_pos_of_pos_of_lt_pi hβ0 hlt
          nlinarith [mul_pos hrb hrc, mul_nonneg (mul_pos hra hrb).le hsα,
            mul_nonneg (mul_pos hrc hra).le hsγ]
        · have hp := Real.sin_pos_of_pos_of_lt_pi hγ0 hlt
          nlinarith [mul_pos hrc hra, mul_nonneg (mul_pos hra hrb).le hsα,
            mul_nonneg (mul_pos hrb hrc).le hsβ]

private lemma exists_ccw_enum {C : Finset Pt}
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt))
    (hcard : 2 ≤ C.card) :
    ∃ v : Fin C.card → Pt,
      (∀ i, v i ∈ C) ∧
      Function.Injective v ∧
      (∀ i j k : Fin C.card, i < j → j < k → 0 < cross2 (v j - v i) (v k - v i)) := by
  let S := C.image (polarAngle (centroid C))
  have hScard : S.card = C.card := Finset.card_image_of_injOn (polarAngle_injOn hconv hcard)
  let emb : Fin C.card ↪o ℝ := S.orderEmbOfFin hScard
  have hmem : ∀ i : Fin C.card, ∃ p ∈ C, polarAngle (centroid C) p = emb i := by
    intro i
    have hi : emb i ∈ S := Finset.orderEmbOfFin_mem S hScard i
    exact Finset.mem_image.mp hi
  let v : Fin C.card → Pt := fun i => Classical.choose (hmem i)
  have hv_mem : ∀ i, v i ∈ C := fun i => (Classical.choose_spec (hmem i)).1
  have hv_ang : ∀ i, polarAngle (centroid C) (v i) = emb i :=
    fun i => (Classical.choose_spec (hmem i)).2
  refine ⟨v, hv_mem, ?_, ?_⟩
  · intro i j hij
    apply emb.injective
    rw [← hv_ang i, ← hv_ang j, hij]
  · intro i j k hij hjk
    apply ccw_of_polarAngle_lt hconv hcard (hv_mem i) (hv_mem j) (hv_mem k)
    · rw [hv_ang i, hv_ang j]
      exact emb.strictMono hij
    · rw [hv_ang j, hv_ang k]
      exact emb.strictMono hjk

private lemma cyclic_shift_ccw {n : ℕ} (v : Fin n → Pt)
    (hccw : ∀ i j k : Fin n, i < j → j < k → 0 < cross2 (v j - v i) (v k - v i))
    (shift : Fin n) :
    ∀ i j k : Fin n, i < j → j < k →
      let w : Fin n → Pt := fun r =>
        v ⟨(r.val + shift.val) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) shift.isLt)⟩
      0 < cross2 (w j - w i) (w k - w i) := by
  intro i j k hij hjk
  dsimp only
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) shift.isLt
  let pi : Fin n := ⟨(i.val + shift.val) % n, Nat.mod_lt _ hn⟩
  let pj : Fin n := ⟨(j.val + shift.val) % n, Nat.mod_lt _ hn⟩
  let pk : Fin n := ⟨(k.val + shift.val) % n, Nat.mod_lt _ hn⟩
  show 0 < cross2 (v pj - v pi) (v pk - v pi)
  have hi_lt : i.val < j.val := hij
  have hj_lt : j.val < k.val := hjk
  have hk_lt : k.val < n := k.isLt
  have hs_lt : shift.val < n := shift.isLt
  by_cases h1 : k.val + shift.val < n
  · have hpi : pi.val = i.val + shift.val := Nat.mod_eq_of_lt (by omega)
    have hpj : pj.val = j.val + shift.val := Nat.mod_eq_of_lt (by omega)
    have hpk : pk.val = k.val + shift.val := Nat.mod_eq_of_lt h1
    exact hccw pi pj pk (by change pi.val < pj.val; omega) (by change pj.val < pk.val; omega)
  · by_cases h2 : j.val + shift.val < n
    · have hpi : pi.val = i.val + shift.val := Nat.mod_eq_of_lt (by omega)
      have hpj : pj.val = j.val + shift.val := Nat.mod_eq_of_lt h2
      have hpk : pk.val = k.val + shift.val - n := by
        show (k.val + shift.val) % n = _
        rw [Nat.mod_eq_sub_mod (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [cross2_cyclic, cross2_cyclic]
      exact hccw pk pi pj (by change pk.val < pi.val; omega) (by change pi.val < pj.val; omega)
    · by_cases h3 : i.val + shift.val < n
      · have hpi : pi.val = i.val + shift.val := Nat.mod_eq_of_lt h3
        have hpj : pj.val = j.val + shift.val - n := by
          show (j.val + shift.val) % n = _
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hpk : pk.val = k.val + shift.val - n := by
          show (k.val + shift.val) % n = _
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        rw [cross2_cyclic]
        exact hccw pj pk pi (by change pj.val < pk.val; omega) (by change pk.val < pi.val; omega)
      · have hpi : pi.val = i.val + shift.val - n := by
          show (i.val + shift.val) % n = _
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hpj : pj.val = j.val + shift.val - n := by
          show (j.val + shift.val) % n = _
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hpk : pk.val = k.val + shift.val - n := by
          show (k.val + shift.val) % n = _
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        exact hccw pi pj pk (by change pi.val < pj.val; omega) (by change pj.val < pk.val; omega)

-- Referee's 5-point lemma and Altman's Lemma 1

private lemma referee_five_point_coord {L0 : ℝ} (hL0 : 0 < L0)
    {A1 At An : Pt}
    (hyt : 0 < At 1) (hy1 : A1 1 < 0) (hy1n : A1 1 ≤ An 1) (hyn0 : An 1 ≤ 0)
    (hv1t : 0 < cross2 (A1 - mkPt 0 0) (At - mkPt 0 0))
    (h1st : 0 < cross2 (mkPt L0 0 - A1) (At - A1))
    (htvn : 0 ≤ cross2 (mkPt 0 0 - At) (An - At))
    (hn1t : 0 ≤ cross2 (A1 - An) (At - An))
    (hdiam : dist A1 At ≤ dist A1 An) :
    dist (mkPt L0 0) At < dist (mkPt L0 0) (mkPt 0 0) := by
  set Av := mkPt 0 0
  set As := mkPt L0 0
  have hden : 0 < At 1 - A1 1 := by linarith
  set α := (-A1 1) / (At 1 - A1 1)
  have hα0 : 0 < α := div_pos (by linarith) hden
  have hα1 : α < 1 := (div_lt_one hden).mpr (by linarith)
  set Q := (1 - α) • A1 + α • At
  have hQ1 : Q 1 = 0 := by
    simp only [Q, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, α]
    field_simp [hden.ne']
    ring
  have hQ0_pos : 0 < Q 0 := by
    simp only [cross2, PiLp.sub_apply, Av, mkPt_zero, mkPt_one, sub_zero] at hv1t
    simp only [Q, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, α]
    have : (1 - -A1 1 / (At 1 - A1 1)) * A1 0 + -A1 1 / (At 1 - A1 1) * At 0 =
        (A1 0 * At 1 - A1 1 * At 0) / (At 1 - A1 1) := by
      field_simp [hden.ne']; ring
    rw [this]
    exact div_pos hv1t hden
  have hQ0_lt : Q 0 < L0 := by
    simp only [cross2, PiLp.sub_apply, As, mkPt_zero, mkPt_one, zero_sub] at h1st
    simp only [Q, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, α]
    have : L0 - ((1 - -A1 1 / (At 1 - A1 1)) * A1 0 + -A1 1 / (At 1 - A1 1) * At 0) =
        ((L0 - A1 0) * (At 1 - A1 1) - -A1 1 * (At 0 - A1 0)) / (At 1 - A1 1) := by
      field_simp [hden.ne']; ring
    have hpos : 0 < L0 - ((1 - -A1 1 / (At 1 - A1 1)) * A1 0 + -A1 1 / (At 1 - A1 1) * At 0) := by
      rw [this]; exact div_pos h1st hden
    linarith
  set β := (An 1 - A1 1) / (At 1 - A1 1)
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) hden.le
  have hβ1 : β ≤ 1 := (div_le_one hden).mpr (by linarith)
  set P := (1 - β) • A1 + β • At
  have hP1 : P 1 = An 1 := by
    simp only [P, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, β]
    field_simp [hden.ne']
    ring
  have hA1At : dist A1 P + dist P At = dist A1 At := dist_add_of_segment A1 At hβ0 hβ1
  set lam := (At 1 - An 1) / At 1
  have hlam1 : 1 ≤ lam := (one_le_div hyt).mpr (by linarith)
  have hlam0 : 0 < lam := by linarith
  have hP_hom : P = At + lam • (Q - At) := by
    apply pt_ext
    · simp only [P, Q, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, α, β, lam]
      field_simp [hden.ne', hyt.ne']
      ring
    · simp only [P, Q, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, α, β, lam]
      field_simp [hden.ne', hyt.ne']
      ring
  set W := At + lam • (Av - At)
  have hW1 : W 1 = An 1 := by
    simp only [W, Av, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      mkPt_one, lam]
    field_simp [hyt.ne']
    ring
  have hW0_le_An0 : W 0 ≤ An 0 := by
    simp only [cross2, PiLp.sub_apply, Av, mkPt_zero, mkPt_one, zero_sub] at htvn
    have : An 0 - W 0 = ((-At 0) * (An 1 - At 1) - (-At 1) * (An 0 - At 0)) / At 1 := by
      simp only [W, Av, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        mkPt_zero, lam]
      field_simp [hyt.ne']
      ring
    have hnn : 0 ≤ An 0 - W 0 := by rw [this]; exact div_nonneg htvn hyt.le
    linarith
  have hAn0_le_P0 : An 0 ≤ P 0 := by
    simp only [cross2, PiLp.sub_apply] at hn1t
    have : P 0 - An 0 =
        ((A1 0 - An 0) * (At 1 - An 1) - (A1 1 - An 1) * (At 0 - An 0)) / (At 1 - A1 1) := by
      simp only [P, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, β]
      field_simp [hden.ne']
      ring
    have hnn : 0 ≤ P 0 - An 0 := by rw [this]; exact div_nonneg hn1t hden.le
    linarith
  have hdist_PAn : dist P An = P 0 - An 0 := by
    rw [dist_eq_sqrt, hP1, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (by linarith)]
  have hdist_PW : dist P W = P 0 - W 0 := by
    rw [dist_eq_sqrt, hP1, hW1, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (by linarith)]
  have hPAn_le_PW : dist P An ≤ dist P W := by linarith
  have hPW_eq : dist P W = lam * dist Q Av := by
    rw [hP_hom]
    exact dist_homothety At Q Av hlam0.le
  have hPAt_eq : dist P At = lam * dist Q At := by
    rw [hP_hom]
    exact dist_homothety_center At Q hlam0.le
  have hQAt_le_QAv : dist Q At ≤ dist Q Av := by
    have htri : dist A1 An ≤ dist A1 P + dist P An := dist_triangle A1 P An
    have hchain : lam * dist Q At ≤ lam * dist Q Av := by linarith
    exact le_of_mul_le_mul_left hchain hlam0
  have hdist_AsQ : dist As Q = L0 - Q 0 := by
    rw [dist_eq_sqrt, hQ1]
    simp only [As, mkPt_zero, mkPt_one, sub_zero, sq, mul_zero, add_zero]
    rw [← sq, Real.sqrt_sq (by linarith)]
  have hdist_QAv : dist Q Av = Q 0 := by
    rw [dist_eq_sqrt, hQ1]
    simp only [Av, mkPt_zero, mkPt_one, sub_zero, sq, mul_zero, add_zero]
    rw [← sq, Real.sqrt_sq hQ0_pos.le]
  have hdist_AsAv : dist As Av = L0 := by
    rw [dist_eq_sqrt]
    simp only [As, Av, mkPt_zero, mkPt_one, sub_zero, sq, mul_zero, add_zero]
    rw [← sq, Real.sqrt_sq hL0.le]
  have hcr_ne : cross2 (Q - As) (At - As) ≠ 0 := by
    simp only [cross2, PiLp.sub_apply, hQ1, As, mkPt_zero, mkPt_one, sub_zero]
    nlinarith
  have hstrict : dist As At < dist As Q + dist Q At :=
    strict_triangle_of_cross2_ne_zero As Q At hcr_ne
  linarith

private lemma referee_five_point {A1 As At Av An : Pt}
    (hsv : As ≠ Av)
    (hyt : 0 < cross2 (As - Av) (At - Av))
    (hy1 : cross2 (As - Av) (A1 - Av) < 0)
    (hy1n : cross2 (As - Av) (A1 - Av) ≤ cross2 (As - Av) (An - Av))
    (hyn0 : cross2 (As - Av) (An - Av) ≤ 0)
    (hv1t : 0 < cross2 (A1 - Av) (At - Av))
    (h1st : 0 < cross2 (As - A1) (At - A1))
    (htvn : 0 ≤ cross2 (Av - At) (An - At))
    (hn1t : 0 ≤ cross2 (A1 - An) (At - An))
    (hdiam : dist A1 At ≤ dist A1 An) :
    dist As At < dist As Av := by
  set L0 := dist As Av
  have hL0 : 0 < L0 := dist_pos.mpr hsv
  set c := (As 0 - Av 0) / L0
  set s := (As 1 - Av 1) / L0
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    rw [div_pow, div_pow, ← add_div, ← dist_sq_eq]
    exact div_self (pow_ne_zero 2 hL0.ne')
  let T : Pt → Pt := fun p =>
    mkPt (c * (p 0 - Av 0) + s * (p 1 - Av 1)) (-s * (p 0 - Av 0) + c * (p 1 - Av 1))
  have hTAv : T Av = mkPt 0 0 := by
    apply pt_ext <;> simp [T]
  have hTAs : T As = mkPt L0 0 := by
    apply pt_ext
    · simp only [T, mkPt_zero]
      dsimp [c, s]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← sq, ← sq, ← dist_sq_eq, sq]
      exact mul_div_cancel_right₀ L0 hL0.ne'
    · simp only [T, mkPt_one]
      dsimp [c, s]
      field_simp [hL0.ne']
      ring
  have hTdist : ∀ p q, dist (T p) (T q) = dist p q := by
    intro p q
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [T, mkPt_zero, mkPt_one]
    have hident :
        ((c * (p 0 - Av 0) + s * (p 1 - Av 1)) - (c * (q 0 - Av 0) + s * (q 1 - Av 1))) ^ 2 +
        ((-s * (p 0 - Av 0) + c * (p 1 - Av 1)) - (-s * (q 0 - Av 0) + c * (q 1 - Av 1))) ^ 2 =
        (c ^ 2 + s ^ 2) * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by ring
    rw [hident, hcs, one_mul]
  have hTcross : ∀ p q r, cross2 (T p - T r) (T q - T r) = cross2 (p - r) (q - r) := by
    intro p q r
    simp only [cross2, PiLp.sub_apply, T, mkPt_zero, mkPt_one]
    have hident :
        ((c * (p 0 - Av 0) + s * (p 1 - Av 1)) - (c * (r 0 - Av 0) + s * (r 1 - Av 1))) *
        ((-s * (q 0 - Av 0) + c * (q 1 - Av 1)) - (-s * (r 0 - Av 0) + c * (r 1 - Av 1))) -
        ((-s * (p 0 - Av 0) + c * (p 1 - Av 1)) - (-s * (r 0 - Av 0) + c * (r 1 - Av 1))) *
        ((c * (q 0 - Av 0) + s * (q 1 - Av 1)) - (c * (r 0 - Av 0) + s * (r 1 - Av 1))) =
        (c ^ 2 + s ^ 2) * ((p 0 - r 0) * (q 1 - r 1) - (p 1 - r 1) * (q 0 - r 0)) := by ring
    rw [hident, hcs, one_mul]
  have hTy : ∀ p, T p 1 = cross2 (As - Av) (p - Av) / L0 := by
    intro p
    simp only [T, mkPt_one, cross2, PiLp.sub_apply]
    dsimp [c, s]
    field_simp [hL0.ne']
    ring
  change dist As At < dist As Av
  rw [← hTdist As At, ← hTdist As Av, hTAs, hTAv]
  refine referee_five_point_coord hL0 (A1 := T A1) (An := T An) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hTy]; exact div_pos hyt hL0
  · rw [hTy]; exact div_neg_of_neg_of_pos hy1 hL0
  · rw [hTy, hTy]; exact div_le_div_of_nonneg_right hy1n hL0.le
  · rw [hTy]; exact div_nonpos_of_nonpos_of_nonneg hyn0 hL0.le
  · rw [← hTAv, hTcross]; exact hv1t
  · rw [← hTAs, hTcross]; exact h1st
  · rw [← hTAv, hTcross]; exact htvn
  · rw [hTcross]; exact hn1t
  · rw [hTdist, hTdist]; exact hdiam

private lemma altman_lemma1_left {L : ℕ} (A : Fin (L + 1) → Pt)
    (hccw : ∀ i j k : Fin (L + 1), i < j → j < k → 0 < cross2 (A j - A i) (A k - A i))
    {s t v : Fin (L + 1)}
    (hst : s < t) (htv : t < v) (h0s : (0 : Fin (L + 1)) < s)
    (hy : cross2 (A s - A v) (A 0 - A v) ≤ cross2 (A s - A v) (A (Fin.last L) - A v))
    (hdiam : dist (A 0) (A t) ≤ dist (A 0) (A (Fin.last L))) :
    dist (A s) (A t) < dist (A s) (A v) := by
  have hsv : A s ≠ A v := by
    intro h
    have := hccw s t v hst htv
    rw [h] at this
    simp [cross2] at this
  have hyt : 0 < cross2 (A s - A v) (A t - A v) := by
    have := hccw s t v hst htv
    have heq : cross2 (A s - A v) (A t - A v) = cross2 (A t - A s) (A v - A s) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith
  have hy1 : cross2 (A s - A v) (A 0 - A v) < 0 := by
    have := hccw 0 s v h0s (lt_trans hst htv)
    have heq : cross2 (A s - A v) (A 0 - A v) = -cross2 (A s - A 0) (A v - A 0) :=
      cross2_swap_neg (A 0) (A s) (A v)
    linarith
  have hyn0 : cross2 (A s - A v) (A (Fin.last L) - A v) ≤ 0 := by
    rcases eq_or_lt_of_le (Fin.le_last v) with hvL | hvL
    · rw [hvL]; simp [cross2]
    · have := hccw s v (Fin.last L) (lt_trans hst htv) hvL
      have heq : cross2 (A s - A v) (A (Fin.last L) - A v) =
          -cross2 (A v - A s) (A (Fin.last L) - A s) := by
        simp only [cross2, PiLp.sub_apply]; ring
      linarith
  have hv1t : 0 < cross2 (A 0 - A v) (A t - A v) := by
    have := hccw 0 t v (lt_trans h0s hst) htv
    rw [cross2_cyclic, cross2_cyclic] at this
    exact this
  have h1st : 0 < cross2 (A s - A 0) (A t - A 0) := hccw 0 s t h0s hst
  have htvn : 0 ≤ cross2 (A v - A t) (A (Fin.last L) - A t) := by
    rcases eq_or_lt_of_le (Fin.le_last v) with hvL | hvL
    · rw [hvL]; simp only [cross2]; rw [mul_comm, sub_self]
    · exact (hccw t v (Fin.last L) htv hvL).le
  have hn1t : 0 ≤ cross2 (A 0 - A (Fin.last L)) (A t - A (Fin.last L)) := by
    have h0t : (0 : Fin (L + 1)) < t := lt_trans h0s hst
    have htL : t < Fin.last L := lt_of_lt_of_le htv (Fin.le_last v)
    have := hccw 0 t (Fin.last L) h0t htL
    rw [cross2_cyclic, cross2_cyclic] at this
    exact this.le
  exact referee_five_point hsv hyt hy1 hy hyn0 hv1t h1st htvn hn1t hdiam

private lemma altman_lemma1 {L : ℕ} (A : Fin (L + 1) → Pt)
    (hccw : ∀ i j k : Fin (L + 1), i < j → j < k → 0 < cross2 (A j - A i) (A k - A i))
    {s t u v : Fin (L + 1)}
    (hst : s < t) (htv : t < v) (hsu : s < u) (huv : u < v)
    (hne : ¬(s = 0 ∧ v = Fin.last L))
    (hdiam_t : dist (A 0) (A t) ≤ dist (A 0) (A (Fin.last L)))
    (hdiam_u : dist (A u) (A (Fin.last L)) ≤ dist (A 0) (A (Fin.last L))) :
    min (dist (A s) (A t)) (dist (A u) (A v)) < dist (A s) (A v) := by
  rcases le_total (cross2 (A s - A v) (A 0 - A v))
      (cross2 (A s - A v) (A (Fin.last L) - A v)) with hle | hle
  · have h0s : (0 : Fin (L + 1)) < s := by
      rcases eq_or_lt_of_le (Fin.zero_le s) with hs0 | hs0
      · exfalso
        have hvL : v < Fin.last L := by
          rcases eq_or_lt_of_le (Fin.le_last v) with hvL | hvL
          · exact False.elim (hne ⟨hs0.symm, hvL⟩)
          · exact hvL
        have hpos := hccw 0 v (Fin.last L) (lt_of_le_of_lt (Fin.zero_le s) (lt_trans hst htv)) hvL
        rw [← hs0] at hle
        have hzero : cross2 (A 0 - A v) (A 0 - A v) = 0 := by simp only [cross2]; ring
        have hneg : cross2 (A 0 - A v) (A (Fin.last L) - A v) =
            -cross2 (A v - A 0) (A (Fin.last L) - A 0) := by
          simp only [cross2, PiLp.sub_apply]; ring
        linarith
      · exact hs0
    exact lt_of_le_of_lt (min_le_left _ _)
      (altman_lemma1_left A hccw hst htv h0s hle hdiam_t)
  · let R : Pt → Pt := fun p => mkPt (-p 0) (p 1)
    let B : Fin (L + 1) → Pt := fun i => R (A ⟨L - i.val, by omega⟩)
    have hRdist : ∀ p q, dist (R p) (R q) = dist p q := by
      intro p q
      rw [dist_eq_sqrt, dist_eq_sqrt]
      congr 1
      simp only [R, mkPt_zero, mkPt_one]
      ring
    have hRcross : ∀ p q r, cross2 (R p - R r) (R q - R r) = -cross2 (p - r) (q - r) := by
      intro p q r
      simp only [cross2, PiLp.sub_apply, R, mkPt_zero, mkPt_one]
      ring
    have hBccw : ∀ i j k : Fin (L + 1), i < j → j < k → 0 < cross2 (B j - B i) (B k - B i) := by
      intro i j k hij hjk
      let ai : Fin (L + 1) := ⟨L - k.val, by omega⟩
      let aj : Fin (L + 1) := ⟨L - j.val, by omega⟩
      let ak : Fin (L + 1) := ⟨L - i.val, by omega⟩
      have h1 : ai < aj := by change L - k.val < L - j.val; omega
      have h2 : aj < ak := by change L - j.val < L - i.val; omega
      change 0 < cross2 (R (A aj) - R (A ak)) (R (A ai) - R (A ak))
      rw [hRcross, cross2_swap_neg, neg_neg]
      exact hccw ai aj ak h1 h2
    let s' : Fin (L + 1) := ⟨L - v.val, by omega⟩
    let t' : Fin (L + 1) := ⟨L - u.val, by omega⟩
    let v' : Fin (L + 1) := ⟨L - s.val, by omega⟩
    have hs't' : s' < t' := by change L - v.val < L - u.val; omega
    have ht'v' : t' < v' := by change L - u.val < L - s.val; omega
    have hBs' : B s' = R (A v) := by
      dsimp [B, s']
      congr 2; apply Fin.ext; dsimp; omega
    have hBt' : B t' = R (A u) := by
      dsimp [B, t']
      congr 2; apply Fin.ext; dsimp; omega
    have hBv' : B v' = R (A s) := by
      dsimp [B, v']
      congr 2; apply Fin.ext; dsimp; omega
    have hB0 : B 0 = R (A (Fin.last L)) := by
      dsimp [B]
      rfl
    have hBL : B (Fin.last L) = R (A 0) := by
      dsimp [B]
      congr 2; apply Fin.ext; dsimp [Fin.last]; omega
    have hy' : cross2 (B s' - B v') (B 0 - B v') ≤
        cross2 (B s' - B v') (B (Fin.last L) - B v') := by
      rw [hBs', hBv', hB0, hBL, hRcross, hRcross]
      have he1 : -cross2 (A v - A s) (A (Fin.last L) - A s) =
          cross2 (A s - A v) (A (Fin.last L) - A v) := by
        simp only [cross2, PiLp.sub_apply]; ring
      have he2 : -cross2 (A v - A s) (A 0 - A s) =
          cross2 (A s - A v) (A 0 - A v) := by
        simp only [cross2, PiLp.sub_apply]; ring
      linarith
    have h0s' : (0 : Fin (L + 1)) < s' := by
      rcases eq_or_lt_of_le (Fin.zero_le s') with hs0' | hs0'
      · exfalso
        have hvL : v = Fin.last L := by
          apply Fin.ext
          have : s'.val = 0 := by rw [← hs0']; rfl
          dsimp [s', Fin.last] at this ⊢
          omega
        have hs0 : (0 : Fin (L + 1)) < s := by
          rcases eq_or_lt_of_le (Fin.zero_le s) with hs0 | hs0
          · exact False.elim (hne ⟨hs0.symm, hvL⟩)
          · exact hs0
        have hpos := hccw 0 s (Fin.last L) hs0 (lt_of_lt_of_le (lt_trans hst htv) (Fin.le_last v))
        rw [hvL] at hle
        have hzero : cross2 (A s - A (Fin.last L)) (A (Fin.last L) - A (Fin.last L)) = 0 := by
          simp [cross2]
        have hneg : cross2 (A s - A (Fin.last L)) (A 0 - A (Fin.last L)) =
            -cross2 (A s - A 0) (A (Fin.last L) - A 0) :=
          cross2_swap_neg (A 0) (A s) (A (Fin.last L))
        linarith
      · exact hs0'
    have hdiam' : dist (B 0) (B t') ≤ dist (B 0) (B (Fin.last L)) := by
      rw [hB0, hBt', hBL, hRdist, hRdist, dist_comm (A (Fin.last L)), dist_comm (A (Fin.last L))]
      exact hdiam_u
    have hres := altman_lemma1_left B hBccw hs't' ht'v' h0s' hy' hdiam'
    rw [hBs', hBt', hBv', hRdist, hRdist, dist_comm (A v) (A u), dist_comm (A v) (A s)] at hres
    exact lt_of_le_of_lt (min_le_right _ _) hres

-- Main proof of Altman's Theorem

private lemma altman_main (C : Finset Pt)
    (hconv : ∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set Pt)) :
    C.card / 2 ≤ (C.offDiag.image (fun p => dist p.1 p.2)).card := by
  set D := C.offDiag.image (fun p => dist p.1 p.2)
  by_cases hsmall : C.card < 4
  · by_cases h2 : C.card < 2
    · omega
    · have hcard2 : 1 < C.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard2
      have hmem : dist a b ∈ D :=
        Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩
      have hpos : 1 ≤ D.card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
  · push Not at hsmall
    set n := C.card
    have hn4 : 4 ≤ n := hsmall
    have hn0 : 0 < n := by omega
    obtain ⟨v, hv_mem, hv_inj, hv_ccw⟩ := exists_ccw_enum hconv (by omega)
    have hDne : D.Nonempty := by
      have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by intro h; simp at h
      refine ⟨dist (v ⟨0, by omega⟩) (v ⟨1, by omega⟩), Finset.mem_image.mpr ?_⟩
      exact ⟨(v ⟨0, by omega⟩, v ⟨1, by omega⟩),
        Finset.mem_offDiag.mpr ⟨hv_mem _, hv_mem _, fun h => h01 (hv_inj h)⟩, rfl⟩
    set Δ := D.max' hDne
    have hΔmem : Δ ∈ D := Finset.max'_mem D hDne
    have hΔmax : ∀ d ∈ D, d ≤ Δ := fun d hd => Finset.le_max' D d hd
    have hdist_le_Δ : ∀ i j : Fin n, dist (v i) (v j) ≤ Δ := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [dist_self]
        obtain ⟨⟨x, y⟩, hxy, hxyΔ⟩ := Finset.mem_image.mp hΔmem
        rw [← hxyΔ]
        exact dist_nonneg
      · exact hΔmax _ (Finset.mem_image.mpr ⟨(v i, v j),
          Finset.mem_offDiag.mpr ⟨hv_mem i, hv_mem j, fun h => hij (hv_inj h)⟩, rfl⟩)
    let arcLen : Fin n × Fin n → ℕ := fun p => (p.2.val + n - p.1.val) % n
    let diamPairs : Finset (Fin n × Fin n) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ dist (v p.1) (v p.2) = Δ)
    have hdiam_ne : diamPairs.Nonempty := by
      obtain ⟨⟨x, y⟩, hxy, hdist⟩ := Finset.mem_image.mp hΔmem
      obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
      have hsurj : ∀ c ∈ C, ∃ i : Fin n, v i = c := by
        have himg : Finset.univ.image v = C := by
          refine Finset.eq_of_subset_of_card_le ?_ ?_
          · intro c hc
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
            exact hv_mem i
          · rw [Finset.card_image_of_injective _ hv_inj, Finset.card_fin]
        intro c hc
        rw [← himg] at hc
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
        exact ⟨i, rfl⟩
      obtain ⟨i, rfl⟩ := hsurj x hx
      obtain ⟨j, rfl⟩ := hsurj y hy
      exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne (congrArg v h), hdist⟩⟩
    obtain ⟨⟨i0, j0⟩, hp0_mem, hp0_max⟩ := Finset.exists_max_image diamPairs arcLen hdiam_ne
    obtain ⟨_, hi0j0, hdist0⟩ := Finset.mem_filter.mp hp0_mem
    dsimp only at hi0j0 hdist0
    have hi0lt : i0.val < n := i0.isLt
    have hj0lt : j0.val < n := j0.isLt
    set L := arcLen (i0, j0)
    have hL_pos : 0 < L := by
      dsimp [L, arcLen]
      by_contra h0
      have hmod0 : (j0.val + n - i0.val) % n = 0 := by omega
      have hdiv : n ∣ j0.val + n - i0.val := Nat.dvd_of_mod_eq_zero hmod0
      obtain ⟨q, hq⟩ := hdiv
      have hlt : j0.val + n - i0.val < 2 * n := by omega
      have hgt : 0 < j0.val + n - i0.val := by omega
      have hq1 : q = 1 := by nlinarith
      rw [hq1, mul_one] at hq
      apply hi0j0
      apply Fin.ext
      omega
    have hL_lt : L < n := Nat.mod_lt _ hn0
    have hrev_mem : (j0, i0) ∈ diamPairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0j0.symm, (dist_comm _ _).trans hdist0⟩
    have hrev_le : arcLen (j0, i0) ≤ L := hp0_max (j0, i0) hrev_mem
    have harc_add : L + arcLen (j0, i0) = n := by
      dsimp [L, arcLen]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi0j0) with hlt | hgt
      · have h1 : (j0.val + n - i0.val) % n = j0.val - i0.val := by
          have : j0.val + n - i0.val = (j0.val - i0.val) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (i0.val + n - j0.val) % n = i0.val + n - j0.val :=
          Nat.mod_eq_of_lt (by omega)
        omega
      · have h1 : (j0.val + n - i0.val) % n = j0.val + n - i0.val :=
          Nat.mod_eq_of_lt (by omega)
        have h2 : (i0.val + n - j0.val) % n = i0.val - j0.val := by
          have : i0.val + n - j0.val = (i0.val - j0.val) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have h2L : n ≤ 2 * L := by omega
    have hL2 : 2 ≤ L := by omega
    let w : Fin n → Pt := fun r => v ⟨(r.val + i0.val) % n, Nat.mod_lt _ hn0⟩
    have hw_ccw : ∀ i j k : Fin n, i < j → j < k → 0 < cross2 (w j - w i) (w k - w i) :=
      cyclic_shift_ccw v hv_ccw i0
    let A : Fin (L + 1) → Pt := fun r => w ⟨r.val, by omega⟩
    have hA_ccw : ∀ i j k : Fin (L + 1), i < j → j < k → 0 < cross2 (A j - A i) (A k - A i) := by
      intro i j k hij hjk
      exact hw_ccw ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ ⟨k.val, by omega⟩ hij hjk
    have hA0 : A 0 = v i0 := by
      dsimp [A, w]
      congr 1; apply Fin.ext; dsimp
      rw [zero_add, Nat.mod_eq_of_lt i0.isLt]
    have hAL : A (Fin.last L) = v j0 := by
      dsimp [A, w]
      congr 1; apply Fin.ext; dsimp [Fin.last, L, arcLen]
      have : ((j0.val + n - i0.val) % n + i0.val) % n = j0.val := by
        rw [Nat.mod_add_mod]
        have hadd : j0.val + n - i0.val + i0.val = j0.val + n := by omega
        rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt j0.isLt]
      exact this
    have hA_diam : ∀ r : Fin (L + 1), dist (A 0) (A r) ≤ dist (A 0) (A (Fin.last L)) ∧
        dist (A r) (A (Fin.last L)) ≤ dist (A 0) (A (Fin.last L)) := by
      intro r
      rw [hA0, hAL, hdist0]
      exact ⟨hdist_le_Δ _ _, hdist_le_Δ _ _⟩
    have hA_mem_D : ∀ r s : Fin (L + 1), r ≠ s → dist (A r) (A s) ∈ D := by
      intro r s hrs
      have hne_idx : (⟨(r.val + i0.val) % n, Nat.mod_lt _ hn0⟩ : Fin n) ≠
          ⟨(s.val + i0.val) % n, Nat.mod_lt _ hn0⟩ := by
        intro heq
        have hval : (r.val + i0.val) % n = (s.val + i0.val) % n := congrArg Fin.val heq
        apply hrs
        apply Fin.ext
        by_cases hr1 : r.val + i0.val < n <;> by_cases hs1 : s.val + i0.val < n
        · rw [Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hs1] at hval; omega
        · rw [Nat.mod_eq_of_lt hr1, Nat.mod_eq_sub_mod (by omega),
              Nat.mod_eq_of_lt (by omega)] at hval; omega
        · rw [Nat.mod_eq_of_lt hs1, Nat.mod_eq_sub_mod (by omega),
              Nat.mod_eq_of_lt (by omega)] at hval; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
      exact Finset.mem_image.mpr ⟨(A r, A s),
        Finset.mem_offDiag.mpr ⟨hv_mem _, hv_mem _, fun h => hne_idx (hv_inj h)⟩, rfl⟩
    let spanSet : (k : ℕ) → Finset ℝ := fun k =>
      (Finset.Icc 0 (L - k)).image (fun r =>
        if h : r + k ≤ L then dist (A ⟨r, by omega⟩) (A ⟨r + k, by omega⟩) else 0)
    have hspan_ne : ∀ k, k ≤ L → (spanSet k).Nonempty := by
      intro k hk
      exact Finset.image_nonempty.mpr ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
    let μ : ℕ → ℝ := fun k =>
      if hk : k ≤ L then (spanSet k).min' (hspan_ne k hk) else 0
    have hμ_mem_D : ∀ k, 1 ≤ k → k ≤ L → μ k ∈ D := by
      intro k hk1 hkL
      have hmin : μ k ∈ spanSet k := by
        dsimp [μ]; rw [dif_pos hkL]; exact Finset.min'_mem _ _
      obtain ⟨r, hr, hreq⟩ := Finset.mem_image.mp hmin
      have hrle : r ≤ L - k := (Finset.mem_Icc.mp hr).2
      have hrk : r + k ≤ L := by omega
      rw [dif_pos hrk] at hreq
      rw [← hreq]
      apply hA_mem_D
      intro h
      have : r = r + k := congrArg Fin.val h
      omega
    have hμ_le : ∀ (k r : ℕ), k ≤ L → (hrk : r + k ≤ L) →
        μ k ≤ dist (A ⟨r, by omega⟩) (A ⟨r + k, by omega⟩) := by
      intro k r hkL hrk
      dsimp [μ]
      rw [dif_pos hkL]
      apply Finset.min'_le
      refine Finset.mem_image.mpr ⟨r, Finset.mem_Icc.mpr ⟨Nat.zero_le r, by omega⟩, ?_⟩
      rw [dif_pos hrk]
    have hμ_step : ∀ k, 2 ≤ k → k ≤ L - 1 → μ (k - 1) < μ k := by
      intro k hk2 hkL1
      have hkL : k ≤ L := by omega
      dsimp [μ]
      rw [dif_pos (by omega : k - 1 ≤ L), dif_pos hkL]
      rw [Finset.lt_min'_iff]
      intro d hd
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hd
      have hrle : r ≤ L - k := (Finset.mem_Icc.mp hr).2
      have hrk : r + k ≤ L := by omega
      rw [dif_pos hrk]
      let s : Fin (L + 1) := ⟨r, by omega⟩
      let t : Fin (L + 1) := ⟨r + k - 1, by omega⟩
      let u : Fin (L + 1) := ⟨r + 1, by omega⟩
      let vv : Fin (L + 1) := ⟨r + k, by omega⟩
      have hlem := altman_lemma1 A hA_ccw
        (s := s) (t := t) (u := u) (v := vv)
        (by change r < r + k - 1; omega)
        (by change r + k - 1 < r + k; omega)
        (by change r < r + 1; omega)
        (by change r + 1 < r + k; omega)
        (by
          rintro ⟨hs0, hvL⟩
          have h1 : r = 0 := congrArg Fin.val hs0
          have h2 : r + k = L := congrArg Fin.val hvL
          omega)
        (hA_diam t).1
        (hA_diam u).2
      have hleft : (spanSet (k - 1)).min' (hspan_ne (k - 1) (by omega)) ≤ dist (A s) (A t) := by
        have := hμ_le (k - 1) r (by omega) (by omega)
        dsimp [μ] at this
        rw [dif_pos (by omega : k - 1 ≤ L)] at this
        have ht_eq : (⟨r + (k - 1), by omega⟩ : Fin (L + 1)) = t := by
          apply Fin.ext; dsimp [t]; omega
        rw [ht_eq] at this
        exact this
      have hright : (spanSet (k - 1)).min' (hspan_ne (k - 1) (by omega)) ≤ dist (A u) (A vv) := by
        have := hμ_le (k - 1) (r + 1) (by omega) (by omega)
        dsimp [μ] at this
        rw [dif_pos (by omega : k - 1 ≤ L)] at this
        have hv_eq : (⟨r + 1 + (k - 1), by omega⟩ : Fin (L + 1)) = vv := by
          apply Fin.ext; dsimp [vv]; omega
        rw [hv_eq] at this
        exact this
      exact lt_of_le_of_lt (le_min hleft hright) hlem
    have hμ_strict : ∀ a b, 1 ≤ a → a < b → b ≤ L - 1 → μ a < μ b := by
      intro a b ha hab hb
      induction b with
      | zero => omega
      | succ b ih =>
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
        · exact hμ_step (a + 1) (by omega) hb
        · exact lt_trans (ih hlt (by omega)) (hμ_step (b + 1) (by omega) hb)
    let Mset := (Finset.Icc 1 (L - 1)).image μ
    have hMsub : Mset ⊆ D := by
      intro d hd
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact hμ_mem_D k hk1 (by omega)
    have hMcard : Mset.card = L - 1 := by
      rw [Finset.card_image_of_injOn]
      · rw [Nat.card_Icc]; omega
      · intro a ha b hb heq
        obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp ha)
        obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp (Finset.mem_coe.mp hb)
        rcases lt_trichotomy a b with hlt | rfl | hgt
        · exact absurd heq (ne_of_lt (hμ_strict a b ha1 hlt hb2))
        · rfl
        · exact absurd heq.symm (ne_of_lt (hμ_strict b a hb1 hgt ha2))
    by_cases hbig : n / 2 + 1 ≤ L
    · have hle : Mset.card ≤ D.card := Finset.card_le_card hMsub
      have h1 : n / 2 ≤ L - 1 := Nat.le_sub_of_add_le hbig
      rw [← hMcard] at h1
      exact h1.trans hle
    · have hLeq : L = n / 2 := by omega
      have hn2L : n = 2 * L := by omega
      have hμ_lt_Δ : μ (L - 1) < Δ := by
        have hle1 : μ (L - 1) ≤ dist (A 0) (A ⟨L - 1, by omega⟩) := by
          have h0 := hμ_le (L - 1) 0 (by omega) (by omega)
          have hA0' : (⟨0, by omega⟩ : Fin (L + 1)) = 0 := rfl
          have hAL1' : (⟨0 + (L - 1), by omega⟩ : Fin (L + 1)) = ⟨L - 1, by omega⟩ := by
            apply Fin.ext; simp
          rwa [hA0', hAL1'] at h0
        have hle2 : dist (A 0) (A ⟨L - 1, by omega⟩) ≤ Δ := by
          rw [hA0]; exact hdist_le_Δ _ _
        have hne_Δ : dist (A 0) (A ⟨L - 1, by omega⟩) ≠ Δ := by
          intro heq
          let p1 : Fin n := ⟨(L - 1 + i0.val) % n, Nat.mod_lt _ hn0⟩
          have hp1_ne : p1 ≠ i0 := by
            intro h
            have hval : (L - 1 + i0.val) % n = i0.val := congrArg Fin.val h
            by_cases hc : L - 1 + i0.val < n
            · rw [Nat.mod_eq_of_lt hc] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          have hp1_mem : (p1, i0) ∈ diamPairs := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1_ne, ?_⟩
            have hAL1 : A ⟨L - 1, by omega⟩ = v p1 := rfl
            rw [hA0, hAL1] at heq
            rw [dist_comm]
            exact heq
          have harc_gt : L < arcLen (p1, i0) := by
            dsimp [arcLen, p1]
            have hval : (i0.val + n - (L - 1 + i0.val) % n) % n = L + 1 := by
              by_cases hc : L - 1 + i0.val < n
              · rw [Nat.mod_eq_of_lt hc]
                have : i0.val + n - (L - 1 + i0.val) = L + 1 := by omega
                rw [this, Nat.mod_eq_of_lt (by omega)]
              · have hinner : (L - 1 + i0.val) % n = L - 1 + i0.val - n := by
                  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
                rw [hinner]
                have : i0.val + n - (L - 1 + i0.val - n) = (L + 1) + n := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
          exact not_le_of_gt harc_gt (hp0_max (p1, i0) hp1_mem)
        exact lt_of_le_of_lt hle1 (lt_of_le_of_ne hle2 hne_Δ)
      have hΔ_not_mem : Δ ∉ Mset := by
        intro hmem
        obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp hmem
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        rcases eq_or_lt_of_le hk2 with rfl | hlt
        · linarith
        · have := hμ_strict k (L - 1) hk1 hlt le_rfl
          linarith
      have hins_sub : insert Δ Mset ⊆ D := Finset.insert_subset hΔmem hMsub
      have hcard_ins : (insert Δ Mset).card = L := by
        rw [Finset.card_insert_of_notMem hΔ_not_mem, hMcard]
        exact Nat.sub_add_cancel (by omega : 1 ≤ L)
      have hle : (insert Δ Mset).card ≤ D.card := Finset.card_le_card hins_sub
      rw [hcard_ins, hLeq] at hle
      exact hle

end OMA.AltmanProof

theorem OMA.solution : OMA.R_erdos_132_R1_H1_R1.H1 :=
  OMA.AltmanProof.altman_main
