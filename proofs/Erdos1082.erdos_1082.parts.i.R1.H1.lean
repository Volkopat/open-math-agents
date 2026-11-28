import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1

/-!
# Proof of H1 for Erdos Problem 1082 (R1)

We prove that any finite non-trilinear planar set determining at most three
distinct distances satisfies `A.card / 2 ≤ distinctDistances A`.
-/

open EuclideanGeometry
open scoped Classical

namespace OMA.Erdos1082_H1_Proof

open OMA.R_Erdos1082_erdos_1082_parts_i_R1

private lemma r2_ext {u v : ℝ²} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

private def dot2 (u v : ℝ²) : ℝ := u 0 * v 0 + u 1 * v 1

private def det2 (u v : ℝ²) : ℝ := u 0 * v 1 - u 1 * v 0

private lemma norm_sq_r2 (x : ℝ²) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

private lemma dist_sq_r2 (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_r2]
  rfl

private lemma dot2_self (u : ℝ²) : dot2 u u = ‖u‖ ^ 2 := by
  rw [norm_sq_r2, dot2]
  ring

private lemma dot2_sub_norm_sq (x y : ℝ²) : dot2 (x - y) (x - y) = dist x y ^ 2 := by
  rw [dot2_self, dist_eq_norm]

private lemma lagrange_r2 (u v : ℝ²) :
    dot2 u v ^ 2 + det2 u v ^ 2 = dot2 u u * dot2 v v := by
  simp only [dot2, det2]
  ring

private lemma eq_zero_of_dot2_det2 {u v : ℝ} {e w : ℝ²}
    (he : 0 < dot2 e e) (hd : dot2 w e = u) (hx : det2 e w = v) (hu : u = 0) (hv : v = 0) :
    w = 0 := by
  subst hu hv
  have hsq : dot2 w w * dot2 e e = 0 := by
    have h1 := lagrange_r2 e w
    have h2 : dot2 e w = 0 := by
      simp only [dot2] at hd ⊢
      linarith
    rw [h2, hx] at h1
    nlinarith
  have hww : dot2 w w = 0 := (mul_eq_zero.mp hsq).resolve_right he.ne'
  rw [dot2_self] at hww
  have hn : ‖w‖ = 0 := sq_eq_zero_iff.mp hww
  exact norm_eq_zero.mp hn

private lemma collinear_of_det2_eq_zero (x y z : ℝ²) (h : det2 (y - x) (z - x) = 0) :
    Collinear ℝ ({x, y, z} : Set ℝ²) := by
  by_cases hxy : y = x
  · rw [hxy]
    have hset : ({x, x, z} : Set ℝ²) = {x, z} := by
      ext w
      simp
    rw [hset]
    exact collinear_pair ℝ x z
  · apply (collinear_iff_of_mem (k := ℝ) (Set.mem_insert x ({y, z} : Set ℝ²))).mpr
    refine ⟨y - x, ?_⟩
    intro w hw
    rcases hw with hwx | hwy | hwz
    · subst hwx; exact ⟨0, by simp⟩
    · subst hwy; exact ⟨1, by simp⟩
    · subst hwz
      have hne : y 0 - x 0 ≠ 0 ∨ y 1 - x 1 ≠ 0 := by
        by_contra h0
        push Not at h0
        exact hxy (r2_ext (by linarith [h0.1]) (by linarith [h0.2]))
      simp only [det2, PiLp.sub_apply] at h
      rcases hne with h0 | h1
      · refine ⟨(w 0 - x 0) / (y 0 - x 0), ?_⟩
        rw [vadd_eq_add]
        apply r2_ext
        · change w 0 = ((w 0 - x 0) / (y 0 - x 0)) * (y 0 - x 0) + x 0
          field_simp [h0]
          ring
        · change w 1 = ((w 0 - x 0) / (y 0 - x 0)) * (y 1 - x 1) + x 1
          field_simp [h0]
          linarith
      · refine ⟨(w 1 - x 1) / (y 1 - x 1), ?_⟩
        rw [vadd_eq_add]
        apply r2_ext
        · change w 0 = ((w 1 - x 1) / (y 1 - x 1)) * (y 0 - x 0) + x 0
          field_simp [h1]
          linarith
        · change w 1 = ((w 1 - x 1) / (y 1 - x 1)) * (y 1 - x 1) + x 1
          field_simp [h1]
          ring

private lemma card_dist_eq_pair_le_two (A : Finset ℝ²) (p q : ℝ²) (r s : ℝ) (hpq : p ≠ q) :
    (A.filter fun z => dist z p = r ∧ dist z q = s).card ≤ 2 := by
  by_contra! h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp h
  obtain ⟨_, hxp, hxq⟩ := Finset.mem_filter.mp hx
  obtain ⟨_, hyp, hyq⟩ := Finset.mem_filter.mp hy
  obtain ⟨_, hzp, hzq⟩ := Finset.mem_filter.mp hz
  rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (finrank_euclideanSpace_fin (n := 2)) hpq hxy
      hxp hyp hzp hxq hyq hzq with he | he
  · exact hxz he.symm
  · exact hyz he.symm

private lemma card_equidistant_le_two {A : Finset ℝ²} (hA : NonTrilinear (A : Set ℝ²))
    {p q : ℝ²} (hpq : p ≠ q) :
    (A.filter fun z => dist z p = dist z q).card ≤ 2 := by
  by_contra! h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp h
  obtain ⟨hxA, hxd⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyA, hyd⟩ := Finset.mem_filter.mp hy
  obtain ⟨hzA, hzd⟩ := Finset.mem_filter.mp hz
  have hsq : ∀ w : ℝ², dist w p = dist w q →
      2 * ((w 0 - x 0) * (q 0 - p 0) + (w 1 - x 1) * (q 1 - p 1)) = 0 := by
    intro w hw
    have hw2 : dist w p ^ 2 = dist w q ^ 2 := by rw [hw]
    have hx2 : dist x p ^ 2 = dist x q ^ 2 := by rw [hxd]
    rw [dist_sq_r2, dist_sq_r2] at hw2 hx2
    linarith
  have hy0 := hsq y hyd
  have hz0 := hsq z hzd
  have hne : q 0 - p 0 ≠ 0 ∨ q 1 - p 1 ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hpq (r2_ext (by linarith [h0.1]) (by linarith [h0.2]))
  have hdet : det2 (y - x) (z - x) = 0 := by
    simp only [det2, PiLp.sub_apply]
    rcases hne with h0 | h1
    · have : (q 0 - p 0) * ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) = 0 := by
        linear_combination ((z 1 - x 1) / 2) * hy0 - ((y 1 - x 1) / 2) * hz0
      exact (mul_eq_zero.mp this).resolve_left h0
    · have : (q 1 - p 1) * ((y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0)) = 0 := by
        linear_combination -((z 0 - x 0) / 2) * hy0 + ((y 0 - x 0) / 2) * hz0
      exact (mul_eq_zero.mp this).resolve_left h1
  exact hA hxA hyA hzA hxy hyz hxz (collinear_of_det2_eq_zero x y z hdet)

/- ## Case d = 0 and d = 1 -/

private lemma card_le_one_of_dist_eq_zero (A : Finset ℝ²) (h : distinctDistances A = 0) :
    A.card ≤ 1 := by
  by_contra! hgt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hgt
  have hm := dist_mem hx hy hxy
  have hpos : 0 < distinctDistances A := Finset.card_pos.mpr ⟨_, hm⟩
  omega

private lemma card_le_three_of_dist_le_one (A : Finset ℝ²) (h : distinctDistances A ≤ 1) :
    A.card ≤ 3 := by
  by_contra! hgt
  obtain ⟨B, hBA, hB4⟩ := Finset.exists_subset_card_eq (show 4 ≤ A.card by omega)
  have hBd : distinctDistances B ≤ 1 := (Finset.card_le_card (distanceSet_mono hBA)).trans h
  have hBne : distinctDistances B ≠ 0 := by
    intro h0
    have := card_le_one_of_dist_eq_zero B h0
    omega
  have hB1 : (distanceSet B).card = 1 := by
    change distinctDistances B = 1
    omega
  obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hB1
  obtain ⟨p0, B1, hp0B1, hB_eq, hB1_3⟩ := Finset.card_eq_succ.mp hB4
  obtain ⟨p1, B2, hp1B2, hB1_eq, hB2_2⟩ := Finset.card_eq_succ.mp hB1_3
  obtain ⟨p2, B3, hp2B3, hB2_eq, hB3_1⟩ := Finset.card_eq_succ.mp hB2_2
  obtain ⟨p3, hB3_eq⟩ := Finset.card_eq_one.mp hB3_1
  have hm0 : p0 ∈ B := hB_eq ▸ Finset.mem_insert_self _ _
  have hm1 : p1 ∈ B := hB_eq ▸ Finset.mem_insert_of_mem (hB1_eq ▸ Finset.mem_insert_self _ _)
  have hm2 : p2 ∈ B := hB_eq ▸ Finset.mem_insert_of_mem
    (hB1_eq ▸ Finset.mem_insert_of_mem (hB2_eq ▸ Finset.mem_insert_self _ _))
  have hm3 : p3 ∈ B := hB_eq ▸ Finset.mem_insert_of_mem
    (hB1_eq ▸ Finset.mem_insert_of_mem (hB2_eq ▸ Finset.mem_insert_of_mem (hB3_eq ▸ Finset.mem_singleton_self _)))
  have h01 : p0 ≠ p1 := fun he => hp0B1 (he ▸ hB1_eq ▸ Finset.mem_insert_self _ _)
  have h02 : p0 ≠ p2 := fun he => hp0B1 (he ▸ hB1_eq ▸ Finset.mem_insert_of_mem (hB2_eq ▸ Finset.mem_insert_self _ _))
  have h03 : p0 ≠ p3 := fun he => hp0B1 (he ▸ hB1_eq ▸ Finset.mem_insert_of_mem (hB2_eq ▸ Finset.mem_insert_of_mem (hB3_eq ▸ Finset.mem_singleton_self _)))
  have h12 : p1 ≠ p2 := fun he => hp1B2 (he ▸ hB2_eq ▸ Finset.mem_insert_self _ _)
  have h13 : p1 ≠ p3 := fun he => hp1B2 (he ▸ hB2_eq ▸ Finset.mem_insert_of_mem (hB3_eq ▸ Finset.mem_singleton_self _))
  have h23 : p2 ≠ p3 := fun he => hp2B3 (he ▸ hB3_eq ▸ Finset.mem_singleton_self _)
  have hdist : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → dist x y = r := fun x hx y hy hxy =>
    Finset.mem_singleton.mp (hr_eq ▸ dist_mem hx hy hxy)
  have hrpos : 0 < r := (dist_pos.mpr h01).trans_eq (hdist p0 hm0 p1 hm1 h01)
  have hd01 : dist p1 p0 ^ 2 = r ^ 2 := by rw [dist_comm, hdist p0 hm0 p1 hm1 h01]
  have hd02 : dist p2 p0 ^ 2 = r ^ 2 := by rw [dist_comm, hdist p0 hm0 p2 hm2 h02]
  have hd03 : dist p3 p0 ^ 2 = r ^ 2 := by rw [dist_comm, hdist p0 hm0 p3 hm3 h03]
  have hd12 : dist p1 p2 ^ 2 = r ^ 2 := by rw [hdist p1 hm1 p2 hm2 h12]
  have hd13 : dist p1 p3 ^ 2 = r ^ 2 := by rw [hdist p1 hm1 p3 hm3 h13]
  have hd23 : dist p2 p3 ^ 2 = r ^ 2 := by rw [hdist p2 hm2 p3 hm3 h23]
  let u := p1 - p0
  let v := p2 - p0
  let w := p3 - p0
  have hu : u 0 ^ 2 + u 1 ^ 2 = r ^ 2 := by
    simpa [u, dist_sq_r2] using hd01
  have hv : v 0 ^ 2 + v 1 ^ 2 = r ^ 2 := by
    simpa [v, dist_sq_r2] using hd02
  have hw : w 0 ^ 2 + w 1 ^ 2 = r ^ 2 := by
    simpa [w, dist_sq_r2] using hd03
  have huv : 2 * (u 0 * v 0 + u 1 * v 1) = r ^ 2 := by
    have h' : (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = r ^ 2 := by
      have : (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = (p1 0 - p2 0) ^ 2 + (p1 1 - p2 1) ^ 2 := by
        simp [u, v]
      rw [this, ← dist_sq_r2]
      exact hd12
    linarith
  have huw : 2 * (u 0 * w 0 + u 1 * w 1) = r ^ 2 := by
    have h' : (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 = r ^ 2 := by
      have : (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 = (p1 0 - p3 0) ^ 2 + (p1 1 - p3 1) ^ 2 := by
        simp [u, w]
      rw [this, ← dist_sq_r2]
      exact hd13
    linarith
  have hvw : 2 * (v 0 * w 0 + v 1 * w 1) = r ^ 2 := by
    have h' : (v 0 - w 0) ^ 2 + (v 1 - w 1) ^ 2 = r ^ 2 := by
      have : (v 0 - w 0) ^ 2 + (v 1 - w 1) ^ 2 = (p2 0 - p3 0) ^ 2 + (p2 1 - p3 1) ^ 2 := by
        simp [v, w]
      rw [this, ← dist_sq_r2]
      exact hd23
    linarith
  let α := v 0 * w 1 - v 1 * w 0
  let β := w 0 * u 1 - w 1 * u 0
  let γ := u 0 * v 1 - u 1 * v 0
  have hlin0 : α * u 0 + β * v 0 + γ * w 0 = 0 := by dsimp [α, β, γ]; ring
  have hlin1 : α * u 1 + β * v 1 + γ * w 1 = 0 := by dsimp [α, β, γ]; ring
  have hzero : r ^ 2 * ((α + β) ^ 2 + (β + γ) ^ 2 + (γ + α) ^ 2) = 0 := by
    have hsq : (α * u 0 + β * v 0 + γ * w 0) ^ 2 + (α * u 1 + β * v 1 + γ * w 1) ^ 2 = 0 := by
      rw [hlin0, hlin1]; norm_num
    have hexp :
        2 * ((α * u 0 + β * v 0 + γ * w 0) ^ 2 + (α * u 1 + β * v 1 + γ * w 1) ^ 2) =
        2 * α ^ 2 * (u 0 ^ 2 + u 1 ^ 2) + 2 * β ^ 2 * (v 0 ^ 2 + v 1 ^ 2) +
        2 * γ ^ 2 * (w 0 ^ 2 + w 1 ^ 2) +
        2 * α * β * (2 * (u 0 * v 0 + u 1 * v 1)) +
        2 * α * γ * (2 * (u 0 * w 0 + u 1 * w 1)) +
        2 * β * γ * (2 * (v 0 * w 0 + v 1 * w 1)) := by ring
    rw [hsq, hu, hv, hw, huv, huw, hvw] at hexp
    linarith
  have hsum0 : (α + β) ^ 2 + (β + γ) ^ 2 + (γ + α) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (by positivity)
  have hγ : γ = 0 := by
    have h1 : (α + β) ^ 2 = 0 := by nlinarith only [hsum0, sq_nonneg (α + β), sq_nonneg (β + γ), sq_nonneg (γ + α)]
    have h2 : (β + γ) ^ 2 = 0 := by nlinarith only [hsum0, sq_nonneg (α + β), sq_nonneg (β + γ), sq_nonneg (γ + α)]
    have h3 : (γ + α) ^ 2 = 0 := by nlinarith only [hsum0, sq_nonneg (α + β), sq_nonneg (β + γ), sq_nonneg (γ + α)]
    have hab0 : α + β = 0 := sq_eq_zero_iff.mp h1
    have hbc0 : β + γ = 0 := sq_eq_zero_iff.mp h2
    have hca0 : γ + α = 0 := sq_eq_zero_iff.mp h3
    linarith only [hab0, hbc0, hca0]
  have hlag : (u 0 * v 0 + u 1 * v 1) ^ 2 + γ ^ 2 = (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
    dsimp [γ]; ring
  rw [hu, hv, hγ] at hlag
  have hsq_uv : 4 * (u 0 * v 0 + u 1 * v 1) ^ 2 = r ^ 4 := by
    have : (2 * (u 0 * v 0 + u 1 * v 1)) ^ 2 = (r ^ 2) ^ 2 := by rw [huv]
    linarith
  have hr4 : 0 < r ^ 4 := by positivity
  nlinarith only [hlag, hsq_uv, hr4]

/- ## Case d = 2 -/

private lemma equilateral_pq_identities (a b c x y : ℝ²) (r : ℝ)
    (hr : 0 < r) (hab : dist a b = r) (hac : dist a c = r) (hbc : dist b c = r) :
    let Px := dist x a ^ 2 + r ^ 2 - dist x b ^ 2
    let Qx := dist x a ^ 2 + r ^ 2 - dist x c ^ 2
    let Py := dist y a ^ 2 + r ^ 2 - dist y b ^ 2
    let Qy := dist y a ^ 2 + r ^ 2 - dist y c ^ 2
    3 * r ^ 2 * dist x a ^ 2 = Px ^ 2 - Px * Qx + Qx ^ 2 ∧
    3 * r ^ 2 * dist x y ^ 2 = (Px - Py) ^ 2 - (Px - Py) * (Qx - Qy) + (Qx - Qy) ^ 2 := by
  let u := b - a
  let v := c - a
  have hu : u 0 ^ 2 + u 1 ^ 2 = r ^ 2 := by
    have : dist b a ^ 2 = r ^ 2 := by rw [dist_comm, hab]
    simpa [u, dist_sq_r2] using this
  have hv : v 0 ^ 2 + v 1 ^ 2 = r ^ 2 := by
    have : dist c a ^ 2 = r ^ 2 := by rw [dist_comm, hac]
    simpa [v, dist_sq_r2] using this
  have huv : 2 * (u 0 * v 0 + u 1 * v 1) = r ^ 2 := by
    have h1 : (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = r ^ 2 := by
      have : (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 := by
        simp [u, v]
      rw [this, ← dist_sq_r2, hbc]
    linarith
  let Δ := u 0 * v 1 - u 1 * v 0
  have hΔ : 4 * Δ ^ 2 = 3 * r ^ 4 := by
    have hlag : (u 0 * v 0 + u 1 * v 1) ^ 2 + Δ ^ 2 = (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
      dsimp [Δ]; ring
    rw [hu, hv] at hlag
    nlinarith
  have hproj : ∀ z : ℝ²,
      2 * ((z 0 - a 0) * u 0 + (z 1 - a 1) * u 1) = dist z a ^ 2 + r ^ 2 - dist z b ^ 2 ∧
      2 * ((z 0 - a 0) * v 0 + (z 1 - a 1) * v 1) = dist z a ^ 2 + r ^ 2 - dist z c ^ 2 := by
    intro z
    constructor
    · rw [dist_sq_r2, dist_sq_r2]
      have hu' : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 = r ^ 2 := by simpa [u] using hu
      change 2 * ((z 0 - a 0) * (b 0 - a 0) + (z 1 - a 1) * (b 1 - a 1)) = _
      linarith
    · rw [dist_sq_r2, dist_sq_r2]
      have hv' : (c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2 = r ^ 2 := by simpa [v] using hv
      change 2 * ((z 0 - a 0) * (c 0 - a 0) + (z 1 - a 1) * (c 1 - a 1)) = _
      linarith
  have hgram : ∀ w0 w1 P Q : ℝ,
      2 * (w0 * u 0 + w1 * u 1) = P → 2 * (w0 * v 0 + w1 * v 1) = Q →
      3 * r ^ 2 * (w0 ^ 2 + w1 ^ 2) = P ^ 2 - P * Q + Q ^ 2 := by
    intro w0 w1 P Q hP hQ
    have hc0 : 2 * Δ * w0 = v 1 * P - u 1 * Q := by
      rw [← hP, ← hQ]; dsimp [Δ]; ring
    have hc1 : 2 * Δ * w1 = -v 0 * P + u 0 * Q := by
      rw [← hP, ← hQ]; dsimp [Δ]; ring
    have hsum : (2 * Δ * w0) ^ 2 + (2 * Δ * w1) ^ 2 =
        (v 1 * P - u 1 * Q) ^ 2 + (-v 0 * P + u 0 * Q) ^ 2 := by rw [hc0, hc1]
    have hlhs : (2 * Δ * w0) ^ 2 + (2 * Δ * w1) ^ 2 = 3 * r ^ 4 * (w0 ^ 2 + w1 ^ 2) := by
      have : (2 * Δ * w0) ^ 2 + (2 * Δ * w1) ^ 2 = (4 * Δ ^ 2) * (w0 ^ 2 + w1 ^ 2) := by ring
      rw [this, hΔ]
    have hrhs : (v 1 * P - u 1 * Q) ^ 2 + (-v 0 * P + u 0 * Q) ^ 2 =
        r ^ 2 * (P ^ 2 - P * Q + Q ^ 2) := by
      have hexp : (v 1 * P - u 1 * Q) ^ 2 + (-v 0 * P + u 0 * Q) ^ 2 =
          (v 0 ^ 2 + v 1 ^ 2) * P ^ 2 - (2 * (u 0 * v 0 + u 1 * v 1)) * P * Q +
          (u 0 ^ 2 + u 1 ^ 2) * Q ^ 2 := by ring
      rw [hexp, hu, hv, huv]; ring
    rw [hlhs, hrhs] at hsum
    have hr2 : r ^ 2 ≠ 0 := by positivity
    have hmul : r ^ 2 * (3 * r ^ 2 * (w0 ^ 2 + w1 ^ 2) - (P ^ 2 - P * Q + Q ^ 2)) = 0 := by
      linarith
    linarith [(mul_eq_zero.mp hmul).resolve_left hr2]
  obtain ⟨hPx, hQx⟩ := hproj x
  obtain ⟨hPy, hQy⟩ := hproj y
  refine ⟨?_, ?_⟩
  · have h1 := hgram (x 0 - a 0) (x 1 - a 1) _ _ hPx hQx
    rwa [← dist_sq_r2] at h1
  · have h2 := hgram (x 0 - y 0) (x 1 - y 1)
      ((dist x a ^ 2 + r ^ 2 - dist x b ^ 2) - (dist y a ^ 2 + r ^ 2 - dist y b ^ 2))
      ((dist x a ^ 2 + r ^ 2 - dist x c ^ 2) - (dist y a ^ 2 + r ^ 2 - dist y c ^ 2))
      (by linear_combination hPx - hPy) (by linear_combination hQx - hQy)
    rwa [← dist_sq_r2] at h2

private lemma two_dist_no_two_extra_of_equilateral (a b c x y : ℝ²) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (hxy : x ≠ y)
    (hab : dist a b = r) (hac : dist a c = r) (hbc : dist b c = r)
    (hxa : dist x a = r ∨ dist x a = s) (hxb : dist x b = r ∨ dist x b = s)
    (hxc : dist x c = r ∨ dist x c = s)
    (hya : dist y a = r ∨ dist y a = s) (hyb : dist y b = r ∨ dist y b = s)
    (hyc : dist y c = r ∨ dist y c = s)
    (hxy_d : dist x y = r ∨ dist x y = s) : False := by
  have h1 := equilateral_pq_identities a b c x y r hr hab hac hbc
  have h2 := equilateral_pq_identities a b c y x r hr hab hac hbc
  set R := r ^ 2
  set S := s ^ 2
  have hR : 0 < R := sq_pos_of_pos hr
  have hS : 0 < S := sq_pos_of_pos hs
  have hRS : R ≠ S := fun he =>
    hrs (le_antisymm ((sq_le_sq₀ hr.le hs.le).mp he.le) ((sq_le_sq₀ hs.le hr.le).mp he.ge))
  have hdxy_pos : 0 < dist x y ^ 2 := sq_pos_of_pos (dist_pos.mpr hxy)
  have hsq : ∀ {d : ℝ}, (d = r ∨ d = s) → d ^ 2 = R ∨ d ^ 2 = S := by
    intro d hd; rcases hd with rfl | rfl <;> simp [R, S]
  have hcls : ∀ (z : ℝ²),
      (dist z a ^ 2 = R ∨ dist z a ^ 2 = S) →
      (dist z b ^ 2 = R ∨ dist z b ^ 2 = S) →
      (dist z c ^ 2 = R ∨ dist z c ^ 2 = S) →
      3 * R * dist z a ^ 2 = (dist z a ^ 2 + R - dist z b ^ 2) ^ 2 -
        (dist z a ^ 2 + R - dist z b ^ 2) * (dist z a ^ 2 + R - dist z c ^ 2) +
        (dist z a ^ 2 + R - dist z c ^ 2) ^ 2 →
      (3 * S = R ∧ dist z a ^ 2 + R - dist z b ^ 2 = R ∧ dist z a ^ 2 + R - dist z c ^ 2 = R) ∨
      (S = 3 * R ∧
        ((dist z a ^ 2 + R - dist z b ^ 2 = 3 * R ∧ dist z a ^ 2 + R - dist z c ^ 2 = 3 * R) ∨
         (dist z a ^ 2 + R - dist z b ^ 2 = -R ∧ dist z a ^ 2 + R - dist z c ^ 2 = R) ∨
         (dist z a ^ 2 + R - dist z b ^ 2 = R ∧ dist z a ^ 2 + R - dist z c ^ 2 = -R))) ∨
      (S ^ 2 - 4 * R * S + R ^ 2 = 0 ∧
        ((dist z a ^ 2 + R - dist z b ^ 2 = 2 * R - S ∧ dist z a ^ 2 + R - dist z c ^ 2 = 2 * R - S) ∨
         (dist z a ^ 2 + R - dist z b ^ 2 = S ∧ dist z a ^ 2 + R - dist z c ^ 2 = R) ∨
         (dist z a ^ 2 + R - dist z b ^ 2 = R ∧ dist z a ^ 2 + R - dist z c ^ 2 = S))) := by
    intro z hza hzb hzc heq
    rcases hza with ha' | ha' <;> rcases hzb with hb' | hb' <;> rcases hzc with hc' | hc' <;>
      rw [ha', hb', hc'] at heq ⊢
    · exfalso; nlinarith only [heq, hR]
    · right; left
      have hS3 : S = 3 * R := by nlinarith only [heq, hR, hS, hRS]
      exact ⟨hS3, Or.inr (Or.inr ⟨by ring, by linarith⟩)⟩
    · right; left
      have hS3 : S = 3 * R := by nlinarith only [heq, hR, hS, hRS]
      exact ⟨hS3, Or.inr (Or.inl ⟨by linarith, by ring⟩)⟩
    · right; right; exact ⟨by nlinarith only [heq], Or.inl ⟨by ring, by ring⟩⟩
    · right; left
      have hS3 : S = 3 * R := by nlinarith only [heq, hR, hS, hRS]
      exact ⟨hS3, Or.inl ⟨by linarith, by linarith⟩⟩
    · right; right; exact ⟨by nlinarith only [heq], Or.inr (Or.inl ⟨by ring, by ring⟩)⟩
    · right; right; exact ⟨by nlinarith only [heq], Or.inr (Or.inr ⟨by ring, by ring⟩)⟩
    · left; exact ⟨by nlinarith only [heq, hR], by ring, by ring⟩
  have hdist_eq : 3 * R * dist x y ^ 2 =
      ((dist x a ^ 2 + R - dist x b ^ 2) - (dist y a ^ 2 + R - dist y b ^ 2)) ^ 2 -
      ((dist x a ^ 2 + R - dist x b ^ 2) - (dist y a ^ 2 + R - dist y b ^ 2)) *
      ((dist x a ^ 2 + R - dist x c ^ 2) - (dist y a ^ 2 + R - dist y c ^ 2)) +
      ((dist x a ^ 2 + R - dist x c ^ 2) - (dist y a ^ 2 + R - dist y c ^ 2)) ^ 2 := h1.2
  have hcx := hcls x (hsq hxa) (hsq hxb) (hsq hxc) h1.1
  have hcy := hcls y (hsq hya) (hsq hyb) (hsq hyc) h2.1
  have hxy2 := hsq hxy_d
  rcases hcx with ⟨h3S, hPx, hQx⟩ | ⟨hS3, hx3⟩ | ⟨hqx, hx4⟩ <;>
    rcases hcy with ⟨h3S', hPy, hQy⟩ | ⟨hS3', hy3⟩ | ⟨hqy, hy4⟩
  · rw [hPx, hQx, hPy, hQy] at hdist_eq; nlinarith only [hdist_eq, hR, hdxy_pos]
  · nlinarith only [h3S, hS3', hR]
  · nlinarith only [h3S, hqy, hR]
  · nlinarith only [hS3, h3S', hR]
  · rcases hx3 with ⟨hPx, hQx⟩ | ⟨hPx, hQx⟩ | ⟨hPx, hQx⟩ <;>
      rcases hy3 with ⟨hPy, hQy⟩ | ⟨hPy, hQy⟩ | ⟨hPy, hQy⟩ <;>
      rw [hPx, hQx, hPy, hQy] at hdist_eq
    all_goals
      rcases hxy2 with hxy' | hxy' <;> rw [hxy'] at hdist_eq <;>
        nlinarith only [hdist_eq, hS3, hR, hS, hdxy_pos]
  · nlinarith only [hS3, hqy, hR]
  · nlinarith only [hqx, h3S', hR]
  · nlinarith only [hqx, hS3', hR]
  · have hno_6RS : ¬ (3 * R * R = 6 * R * S) := fun h => by
      have h2 : R = 2 * S := by
        have : R * (R - 2 * S) = 0 := by linarith only [h]
        linarith only [(mul_eq_zero.mp this).resolve_left hR.ne']
      nlinarith only [hqx, h2, hS]
    rcases hx4 with ⟨hPx, hQx⟩ | ⟨hPx, hQx⟩ | ⟨hPx, hQx⟩ <;>
      rcases hy4 with ⟨hPy, hQy⟩ | ⟨hPy, hQy⟩ | ⟨hPy, hQy⟩ <;>
      rw [hPx, hQx, hPy, hQy] at hdist_eq
    all_goals
      rcases hxy2 with hxy' | hxy' <;> rw [hxy'] at hdist_eq <;>
        first
        | nlinarith only [hdist_eq, hqx, hR, hS, hdxy_pos]
        | exact hno_6RS (by linarith only [hdist_eq, hqx])

private lemma card_le_five_of_dist_le_two (A : Finset ℝ²) (h : distinctDistances A ≤ 2) :
    A.card ≤ 5 := by
  by_contra! hgt
  obtain ⟨B, hBA, hB6⟩ := Finset.exists_subset_card_eq (show 6 ≤ A.card by omega)
  have hBd : distinctDistances B ≤ 2 := (Finset.card_le_card (distanceSet_mono hBA)).trans h
  have hBgt1 : 1 < distinctDistances B := by
    by_contra! hle
    have := card_le_three_of_dist_le_one B hle
    omega
  have hB2 : (distanceSet B).card = 2 := by
    change distinctDistances B = 2
    omega
  obtain ⟨r0, s0, hrs0, hD_eq⟩ := Finset.card_eq_two.mp hB2
  have hmem_D : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → dist u v = r0 ∨ dist u v = s0 := by
    intro u hu v hv huv
    have := dist_mem hu hv huv
    rw [hD_eq] at this
    simpa using this
  -- Ramsey R(3, 3) = 6 gives an equilateral triangle
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  let B' := B.erase v0
  have hB'5 : B'.card = 5 := by rw [Finset.card_erase_of_mem hv0, hB6]
  let Fr := B'.filter fun z => dist v0 z = r0
  let Fs := B'.filter fun z => dist v0 z = s0
  have hcov : B' ⊆ Fr ∪ Fs := by
    intro z hz
    obtain ⟨hzne, hzB⟩ := Finset.mem_erase.mp hz
    rcases hmem_D v0 hv0 z hzB hzne.symm with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, h⟩)
  have hcard_u : 5 ≤ Fr.card + Fs.card := by
    have := (Finset.card_le_card hcov).trans (Finset.card_union_le Fr Fs)
    omega
  have htri : ∃ (r s : ℝ), r ≠ s ∧ (∀ u ∈ B, ∀ v ∈ B, u ≠ v → dist u v = r ∨ dist u v = s) ∧
      ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        dist a b = r ∧ dist a c = r ∧ dist b c = r := by
    have hstep : ∀ (r s : ℝ), r ≠ s → (∀ u ∈ B, ∀ v ∈ B, u ≠ v → dist u v = r ∨ dist u v = s) →
        3 ≤ (B'.filter fun z => dist v0 z = r).card →
        ∃ (r' s' : ℝ), r' ≠ s' ∧ (∀ u ∈ B, ∀ v ∈ B, u ≠ v → dist u v = r' ∨ dist u v = s') ∧
        ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          dist a b = r' ∧ dist a c = r' ∧ dist b c = r' := by
      intro r s hrs hD h3
      have h2lt : 2 < (B'.filter fun z => dist v0 z = r).card := by omega
      obtain ⟨x1, x2, x3, hx1, hx2, hx3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp h2lt
      obtain ⟨hx1', hd1⟩ := Finset.mem_filter.mp hx1
      obtain ⟨hx2', hd2⟩ := Finset.mem_filter.mp hx2
      obtain ⟨hx3', hd3⟩ := Finset.mem_filter.mp hx3
      obtain ⟨hx1ne, hx1B⟩ := Finset.mem_erase.mp hx1'
      obtain ⟨hx2ne, hx2B⟩ := Finset.mem_erase.mp hx2'
      obtain ⟨hx3ne, hx3B⟩ := Finset.mem_erase.mp hx3'
      rcases hD x1 hx1B x2 hx2B h12 with h12r | h12s
      · exact ⟨r, s, hrs, hD, v0, hv0, x1, hx1B, x2, hx2B, hx1ne.symm, hx2ne.symm, h12, hd1, hd2, h12r⟩
      rcases hD x1 hx1B x3 hx3B h13 with h13r | h13s
      · exact ⟨r, s, hrs, hD, v0, hv0, x1, hx1B, x3, hx3B, hx1ne.symm, hx3ne.symm, h13, hd1, hd3, h13r⟩
      rcases hD x2 hx2B x3 hx3B h23 with h23r | h23s
      · exact ⟨r, s, hrs, hD, v0, hv0, x2, hx2B, x3, hx3B, hx2ne.symm, hx3ne.symm, h23, hd2, hd3, h23r⟩
      exact ⟨s, r, hrs.symm, fun u hu v hv huv => (hD u hu v hv huv).symm,
        x1, hx1B, x2, hx2B, x3, hx3B, h12, h13, h23, h12s, h13s, h23s⟩
    by_cases hFr : 3 ≤ Fr.card
    · exact hstep r0 s0 hrs0 hmem_D hFr
    · have hFs : 3 ≤ Fs.card := by omega
      exact hstep s0 r0 hrs0.symm (fun u hu v hv huv => (hmem_D u hu v hv huv).symm) hFs
  obtain ⟨r, s, hrs, hD, a, ha, b, hb, c, hc, hab, hac, hbc, hdab, hdac, hdbc⟩ := htri
  have hrpos : 0 < r := (dist_pos.mpr hab).trans_eq hdab
  have hspos : 0 < s := by
    have hs_mem : s ∈ distanceSet B := by
      have : r = r0 ∧ s = s0 ∨ r = s0 ∧ s = r0 := by
        have hm := hdab ▸ dist_mem ha hb hab
        rw [hD_eq] at hm
        have hsd : ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ dist u v = s := by
          by_contra! hno
          have hsub : distanceSet B ⊆ {r} := by
            intro d hd
            obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hd
            obtain ⟨hu, hv, hne⟩ := Finset.mem_offDiag.mp huv
            rcases hD u hu v hv hne with h' | h'
            · exact Finset.mem_singleton.mpr h'
            · exact (hno u hu v hv hne h').elim
          have := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton r)
          omega
        obtain ⟨u, hu, v, hv, hne, hduv⟩ := hsd
        have hms := hduv ▸ dist_mem hu hv hne
        rw [hD_eq] at hms
        simp at hm hms
        rcases hm with rfl | rfl <;> rcases hms with rfl | rfl
        · exact (hrs rfl).elim
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact (hrs rfl).elim
      rw [hD_eq]
      rcases this with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    obtain ⟨⟨u, v⟩, huv, hduv⟩ := Finset.mem_image.mp hs_mem
    obtain ⟨_, _, hne⟩ := Finset.mem_offDiag.mp huv
    exact (dist_pos.mpr hne).trans_eq hduv
  let E := ((B.erase a).erase b).erase c
  have hE3 : E.card = 3 := by
    have hc1 : (B.erase a).card = 5 := by rw [Finset.card_erase_of_mem ha, hB6]
    have hba : b ∈ B.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hc2 : ((B.erase a).erase b).card = 4 := by rw [Finset.card_erase_of_mem hba, hc1]
    have hcab : c ∈ (B.erase a).erase b :=
      Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, hc⟩⟩
    rw [Finset.card_erase_of_mem hcab, hc2]
  obtain ⟨x, hxE, y, hyE, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < E.card)
  have hx_info : x ∈ B ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c := by
    obtain ⟨hxc, hx2⟩ := Finset.mem_erase.mp hxE
    obtain ⟨hxb, hx1⟩ := Finset.mem_erase.mp hx2
    obtain ⟨hxa, hxB⟩ := Finset.mem_erase.mp hx1
    exact ⟨hxB, hxa, hxb, hxc⟩
  have hy_info : y ∈ B ∧ y ≠ a ∧ y ≠ b ∧ y ≠ c := by
    obtain ⟨hyc, hy2⟩ := Finset.mem_erase.mp hyE
    obtain ⟨hyb, hy1⟩ := Finset.mem_erase.mp hy2
    obtain ⟨hya, hyB⟩ := Finset.mem_erase.mp hy1
    exact ⟨hyB, hya, hyb, hyc⟩
  exact two_dist_no_two_extra_of_equilateral a b c x y r s hrpos hspos hrs hxy hdab hdac hdbc
    (hD x hx_info.1 a ha hx_info.2.1) (hD x hx_info.1 b hb hx_info.2.2.1)
    (hD x hx_info.1 c hc hx_info.2.2.2)
    (hD y hy_info.1 a ha hy_info.2.1) (hD y hy_info.1 b hb hy_info.2.2.1)
    (hD y hy_info.1 c hc hy_info.2.2.2)
    (hD x hx_info.1 y hy_info.1 hxy)

/- ## Case d = 3, Step 1: At least 7 diameter vertices -/

private lemma rectangle_contradiction {A : Finset ℝ²} {x y u1 u2 v1 v2 : ℝ²}
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hD : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → dist u v = a ∨ dist u v = b ∨ dist u v = c)
    (hxy : x ≠ y) (hxy_ab : dist x y = a ∨ dist x y = b)
    (hu1A : u1 ∈ A) (hu2A : u2 ∈ A) (hv1A : v1 ∈ A) (hv2A : v2 ∈ A)
    (hu12 : u1 ≠ u2) (hv12 : v1 ≠ v2)
    (hu1x : dist u1 x = a) (hu1y : dist u1 y = b)
    (hu2x : dist u2 x = a) (hu2y : dist u2 y = b)
    (hv1x : dist v1 x = b) (hv1y : dist v1 y = a)
    (hv2x : dist v2 x = b) (hv2y : dist v2 y = a) : False := by
  let m : ℝ² := (1 / 2 : ℝ) • (x + y)
  let e : ℝ² := (1 / 2 : ℝ) • (y - x)
  have he_norm : 4 * dot2 e e = dist x y ^ 2 := by
    rw [dist_sq_r2]
    simp only [e, dot2, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have he_pos : 0 < dot2 e e := by
    have : 0 < dist x y ^ 2 := sq_pos_of_pos (dist_pos.mpr hxy)
    linarith
  have h_coords : ∀ w : ℝ², ∀ r1 r2 : ℝ, dist w x = r1 → dist w y = r2 →
      2 * (dot2 (w - m) (w - m) + dot2 e e) = r1 ^ 2 + r2 ^ 2 ∧
      4 * dot2 (w - m) e = r1 ^ 2 - r2 ^ 2 := by
    intro w r1 r2 h1 h2
    have hd1 : dist w x ^ 2 = r1 ^ 2 := by rw [h1]
    have hd2 : dist w y ^ 2 = r2 ^ 2 := by rw [h2]
    rw [dist_sq_r2] at hd1 hd2
    simp only [m, e, dot2, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    constructor <;> linarith
  obtain ⟨hu1n, hu1d⟩ := h_coords u1 a b hu1x hu1y
  obtain ⟨hu2n, hu2d⟩ := h_coords u2 a b hu2x hu2y
  obtain ⟨hv1n, hv1d⟩ := h_coords v1 b a hv1x hv1y
  obtain ⟨hv2n, hv2d⟩ := h_coords v2 b a hv2x hv2y
  have hdet_sq : ∀ w : ℝ²,
      dot2 (w - m) (w - m) = dot2 (u1 - m) (u1 - m) →
      dot2 (w - m) e ^ 2 = dot2 (u1 - m) e ^ 2 →
      det2 e (w - m) ^ 2 = det2 e (u1 - m) ^ 2 := by
    intro w hwn hwd
    have hL1 := lagrange_r2 e (w - m)
    have hL2 := lagrange_r2 e (u1 - m)
    have hsym : ∀ z : ℝ², dot2 e z = dot2 z e := fun z => by simp only [dot2]; ring
    rw [hsym, hsym] at hL1 hL2
    rw [hwn, hwd] at hL1
    linarith only [hL1, hL2]
  have hdu2_sq : det2 e (u2 - m) ^ 2 = det2 e (u1 - m) ^ 2 :=
    hdet_sq u2 (by linarith only [hu1n, hu2n])
      (by rw [show dot2 (u2 - m) e = dot2 (u1 - m) e by linarith only [hu1d, hu2d]])
  have hdv1_sq : det2 e (v1 - m) ^ 2 = det2 e (u1 - m) ^ 2 :=
    hdet_sq v1 (by linarith only [hu1n, hv1n]) (by
      have : dot2 (v1 - m) e = -dot2 (u1 - m) e := by linarith only [hu1d, hv1d]
      rw [this, neg_sq])
  have hdv2_sq : det2 e (v2 - m) ^ 2 = det2 e (u1 - m) ^ 2 :=
    hdet_sq v2 (by linarith only [hu1n, hv2n]) (by
      have : dot2 (v2 - m) e = -dot2 (u1 - m) e := by linarith only [hu1d, hv2d]
      rw [this, neg_sq])
  have hv_opp : det2 e (v1 - m) = -det2 e (v2 - m) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hdv1_sq.trans hdv2_sq.symm) with heq | hneg
    · exfalso
      apply hv12
      have hsub : v1 - v2 = 0 := eq_zero_of_dot2_det2 (u := 0) (v := 0) he_pos
        (by simp only [dot2, PiLp.sub_apply] at hv1d hv2d ⊢; linarith only [hv1d, hv2d])
        (by simp only [det2, PiLp.sub_apply] at heq ⊢; linarith only [heq]) rfl rfl
      exact sub_eq_zero.mp hsub
    · exact hneg
  have hex_vs : ∃ vp ∈ A, ∃ vm ∈ A,
      dist vp x = b ∧ dist vp y = a ∧ dist vm x = b ∧ dist vm y = a ∧
      det2 e (vp - m) = det2 e (u1 - m) ∧ det2 e (vm - m) = -det2 e (u1 - m) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdv1_sq with h1 | h1
    · exact ⟨v1, hv1A, v2, hv2A, hv1x, hv1y, hv2x, hv2y, h1, by linarith only [h1, hv_opp]⟩
    · exact ⟨v2, hv2A, v1, hv1A, hv2x, hv2y, hv1x, hv1y, by linarith only [h1, hv_opp], h1⟩
  obtain ⟨vp, hvpA, vm, hvmA, hvpx, hvpy, hvmx, hvmy, hvp_det, hvm_det⟩ := hex_vs
  obtain ⟨hvpn, hvpd⟩ := h_coords vp b a hvpx hvpy
  obtain ⟨hvmn, hvmd⟩ := h_coords vm b a hvmx hvmy
  have hu_opp : det2 e (u2 - m) = -det2 e (u1 - m) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdu2_sq with heq | hneg
    · exfalso
      apply hu12
      have hsub : u1 - u2 = 0 := eq_zero_of_dot2_det2 (u := 0) (v := 0) he_pos
        (by simp only [dot2, PiLp.sub_apply] at hu1d hu2d ⊢; linarith only [hu1d, hu2d])
        (by simp only [det2, PiLp.sub_apply] at heq ⊢; linarith only [heq]) rfl rfl
      exact sub_eq_zero.mp hsub
    · exact hneg
  have hvm_eq : (u1 - m) + (vm - m) = 0 :=
    eq_zero_of_dot2_det2 (u := 0) (v := 0) he_pos
      (by simp only [dot2, PiLp.add_apply, PiLp.sub_apply] at hu1d hvmd ⊢; linarith only [hu1d, hvmd])
      (by simp only [det2, PiLp.add_apply, PiLp.sub_apply] at hvm_det ⊢; linarith only [hvm_det]) rfl rfl
  have hdiag_sq : dist u1 vm ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 - dist x y ^ 2 := by
    have hsub : u1 - vm = (2 : ℝ) • (u1 - m) := by
      ext i
      have hi := congrArg (fun z : ℝ² => z i) hvm_eq
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply] at hi
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      linarith only [hi]
    rw [← dot2_sub_norm_sq, hsub]
    have h4 : dot2 ((2 : ℝ) • (u1 - m)) ((2 : ℝ) • (u1 - m)) = 4 * dot2 (u1 - m) (u1 - m) := by
      simp only [dot2, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h4]
    linarith only [hu1n, he_norm]
  have hhoriz_sq : dist x y ^ 2 * dist u1 vp ^ 2 = (b ^ 2 - a ^ 2) ^ 2 := by
    have hL := lagrange_r2 e (u1 - vp)
    have hdot : 2 * dot2 e (u1 - vp) = a ^ 2 - b ^ 2 := by
      simp only [dot2, PiLp.sub_apply] at hu1d hvpd ⊢; linarith only [hu1d, hvpd]
    have hdet : det2 e (u1 - vp) = 0 := by
      simp only [det2, PiLp.sub_apply] at hvp_det ⊢; linarith only [hvp_det]
    rw [dot2_sub_norm_sq, hdet] at hL
    have hsq1 : (2 * dot2 e (u1 - vp)) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 := by rw [hdot]
    nlinarith only [hL, hsq1, he_norm]
  have hpyth : dist u1 vp ^ 2 + dist u1 u2 ^ 2 = dist u1 vm ^ 2 := by
    have hL_p := lagrange_r2 e (u1 - vp)
    have hL_u := lagrange_r2 e (u1 - u2)
    have hL_m := lagrange_r2 e (u1 - vm)
    rw [dot2_sub_norm_sq] at hL_p hL_u hL_m
    have hdot_p : 2 * dot2 e (u1 - vp) = a ^ 2 - b ^ 2 := by
      simp only [dot2, PiLp.sub_apply] at hu1d hvpd ⊢; linarith only [hu1d, hvpd]
    have hdet_p : det2 e (u1 - vp) = 0 := by
      simp only [det2, PiLp.sub_apply] at hvp_det ⊢; linarith only [hvp_det]
    have hdot_u : dot2 e (u1 - u2) = 0 := by
      simp only [dot2, PiLp.sub_apply] at hu1d hu2d ⊢; linarith only [hu1d, hu2d]
    have hdet_u : det2 e (u1 - u2) = 2 * det2 e (u1 - m) := by
      simp only [det2, PiLp.sub_apply] at hu_opp ⊢; linarith only [hu_opp]
    have hdot_m : 2 * dot2 e (u1 - vm) = a ^ 2 - b ^ 2 := by
      simp only [dot2, PiLp.sub_apply] at hu1d hvmd ⊢; linarith only [hu1d, hvmd]
    have hdet_m : det2 e (u1 - vm) = 2 * det2 e (u1 - m) := by
      simp only [det2, PiLp.sub_apply] at hvm_det ⊢; linarith only [hvm_det]
    have hdot_pm : dot2 e (u1 - vp) = dot2 e (u1 - vm) := by linarith only [hdot_p, hdot_m]
    have hdet_um : det2 e (u1 - u2) = det2 e (u1 - vm) := by linarith only [hdet_u, hdet_m]
    have hmul : dot2 e e * (dist u1 vp ^ 2 + dist u1 u2 ^ 2 - dist u1 vm ^ 2) = 0 := by
      rw [hdot_pm, hdet_p] at hL_p
      rw [hdot_u, hdet_um] at hL_u
      linarith only [hL_p, hL_u, hL_m]
    linarith only [(mul_eq_zero.mp hmul).resolve_left he_pos.ne']
  have hu1_vp_ne : u1 ≠ vp := fun he => by
    have h1 := he ▸ hu1x
    linarith only [h1, hvpx, hab]
  have hu1_vm_ne : u1 ≠ vm := fun he => by
    have h1 := he ▸ hu1x
    linarith only [h1, hvmx, hab]
  have hdiag_le : dist u1 vm ≤ c := by
    rcases hD u1 hu1A vm hvmA hu1_vm_ne with h | h | h <;> linarith only [h, hab, hbc]
  have hpos_p : 0 < dist u1 vp ^ 2 := sq_pos_of_pos (dist_pos.mpr hu1_vp_ne)
  have hpos_u : 0 < dist u1 u2 ^ 2 := sq_pos_of_pos (dist_pos.mpr hu12)
  have hvp_lt_c : dist u1 vp < c := by
    nlinarith only [hpyth, hdiag_le, hpos_p, hpos_u, dist_nonneg (x := u1) (y := vp), dist_nonneg (x := u1) (y := vm)]
  have hu2_lt_c : dist u1 u2 < c := by
    nlinarith only [hpyth, hdiag_le, hpos_p, hpos_u, dist_nonneg (x := u1) (y := u2), dist_nonneg (x := u1) (y := vm)]
  have hvp_ab : dist u1 vp = a ∨ dist u1 vp = b := by
    rcases hD u1 hu1A vp hvpA hu1_vp_ne with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · linarith only [h, hvp_lt_c]
  have hu2_ab : dist u1 u2 = a ∨ dist u1 u2 = b := by
    rcases hD u1 hu1A u2 hu2A hu12 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · linarith only [h, hu2_lt_c]
  rcases hxy_ab with hxy_eq | hxy_eq
  · rw [hxy_eq] at hdiag_sq
    rcases hvp_ab with h1 | h1 <;> rcases hu2_ab with h2 | h2
    all_goals
      rw [h1, h2] at hpyth
      nlinarith only [hdiag_sq, hpyth, ha, hab]
  · rw [hxy_eq] at hdiag_sq hhoriz_sq
    have hvp_a : dist u1 vp = a := by
      rcases hvp_ab with h1 | h1
      · exact h1
      · rw [h1] at hhoriz_sq
        have hba : a ^ 2 < b ^ 2 := by nlinarith only [ha, hab]
        have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
        have hzero : a ^ 2 * (2 * b ^ 2 - a ^ 2) = 0 := by linarith only [hhoriz_sq]
        nlinarith only [hzero, ha2, hba]
    rw [hvp_a] at hpyth
    rcases hu2_ab with h2 | h2
    all_goals
      rw [h2] at hpyth
      nlinarith only [hdiag_sq, hpyth, ha, hab]

private lemma card_diameter_vertices_ge_seven {A : Finset ℝ²}
    (hA : NonTrilinear (A : Set ℝ²)) (hA8 : A.card = 8)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hD : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → dist u v = a ∨ dist u v = b ∨ dist u v = c) :
    7 ≤ (A.filter fun v => ∃ w ∈ A, dist v w = c).card := by
  let VD := A.filter fun v => ∃ w ∈ A, dist v w = c
  by_contra! hlt
  change VD.card < 7 at hlt
  have hdiff : 2 ≤ (A \ VD).card := by
    have := Finset.card_sdiff_add_card_inter A VD
    have hint : A ∩ VD = VD := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hint] at this
    omega
  obtain ⟨x, hxI, y, hyI, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (A \ VD).card)
  obtain ⟨hxA, hxVD⟩ := Finset.mem_sdiff.mp hxI
  obtain ⟨hyA, hyVD⟩ := Finset.mem_sdiff.mp hyI
  have hxno : ∀ z ∈ A, dist x z ≠ c := fun z hz h =>
    hxVD (Finset.mem_filter.mpr ⟨hxA, z, hz, h⟩)
  have hyno : ∀ z ∈ A, dist y z ≠ c := fun z hz h =>
    hyVD (Finset.mem_filter.mpr ⟨hyA, z, hz, h⟩)
  have hxab : ∀ z ∈ A, z ≠ x → dist z x = a ∨ dist z x = b := by
    intro z hz hzx
    rcases hD z hz x hxA hzx with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hxno z hz (by simpa [dist_comm] using h)).elim
  have hyab : ∀ z ∈ A, z ≠ y → dist z y = a ∨ dist z y = b := by
    intro z hz hzy
    rcases hD z hz y hyA hzy with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hyno z hz (by simpa [dist_comm] using h)).elim
  let R := (A.erase x).erase y
  have hR6 : R.card = 6 := by
    have h1 : (A.erase x).card = 7 := by rw [Finset.card_erase_of_mem hxA, hA8]
    have hyx : y ∈ A.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyA⟩
    rw [Finset.card_erase_of_mem hyx, h1]
  let Seq := R.filter fun z => dist z x = dist z y
  let Sab := R.filter fun z => dist z x = a ∧ dist z y = b
  let Sba := R.filter fun z => dist z x = b ∧ dist z y = a
  have hRsub : R ⊆ A := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hcov : R ⊆ Seq ∪ (Sab ∪ Sba) := by
    intro z hz
    obtain ⟨hzy, hz1⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzx, hzA⟩ := Finset.mem_erase.mp hz1
    rcases hxab z hzA hzx with hxa | hxb <;> rcases hyab z hzA hzy with hya | hyb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, by rw [hxa, hya]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hxa, hyb⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hxb, hya⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, by rw [hxb, hyb]⟩)
  have hSeq : Seq.card ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hRsub)).trans (card_equidistant_le_two hA hxy)
  have hSab : Sab.card ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hRsub)).trans (card_dist_eq_pair_le_two A x y a b hxy)
  have hSba : Sba.card ≤ 2 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hRsub)).trans (card_dist_eq_pair_le_two A x y b a hxy)
  have hsum : 6 ≤ Seq.card + Sab.card + Sba.card := by
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le Seq (Sab ∪ Sba)
    have h3 := Finset.card_union_le Sab Sba
    omega
  obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < Sab.card)
  obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp (by omega : 1 < Sba.card)
  obtain ⟨hu1R, hu1x, hu1y⟩ := Finset.mem_filter.mp hu1
  obtain ⟨hu2R, hu2x, hu2y⟩ := Finset.mem_filter.mp hu2
  obtain ⟨hv1R, hv1x, hv1y⟩ := Finset.mem_filter.mp hv1
  obtain ⟨hv2R, hv2x, hv2y⟩ := Finset.mem_filter.mp hv2
  have hxy_ab : dist x y = a ∨ dist x y = b := by
    simpa [dist_comm] using hxab y hyA hxy.symm
  exact rectangle_contradiction ha hab hbc hD hxy hxy_ab
    (hRsub hu1R) (hRsub hu2R) (hRsub hv1R) (hRsub hv2R) hu12 hv12
    hu1x hu1y hu2x hu2y hv1x hv1y hv2x hv2y

/- ## Case d = 3, Step 2: CCW ordering of 7 extreme points -/

private noncomputable def toComplex (v : ℝ²) : ℂ := ⟨v 0, v 1⟩

private lemma toComplex_norm (v : ℝ²) : ‖toComplex v‖ = ‖v‖ := by
  have h1 : ‖toComplex v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, norm_sq_r2]
    simp [toComplex, sq]
  exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1.le)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1.ge)

private lemma toComplex_re_im (v : ℝ²) :
    v 0 = ‖v‖ * Real.cos (Complex.arg (toComplex v)) ∧
    v 1 = ‖v‖ * Real.sin (Complex.arg (toComplex v)) := by
  have h1 := Complex.norm_mul_cos_arg (toComplex v)
  have h2 := Complex.norm_mul_sin_arg (toComplex v)
  rw [toComplex_norm] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

private lemma det2_eq_norm_sin (u v : ℝ²) :
    det2 u v = ‖u‖ * ‖v‖ * Real.sin (Complex.arg (toComplex v) - Complex.arg (toComplex u)) := by
  obtain ⟨hu0, hu1⟩ := toComplex_re_im u
  obtain ⟨hv0, hv1⟩ := toComplex_re_im v
  simp only [det2]
  rw [hu0, hu1, hv0, hv1, Real.sin_sub]
  ring

private lemma ccw_ordering_of_supported (S : Finset ℝ²) (hS : S.card = 7)
    (hsup : ∀ x ∈ S, ∃ n : ℝ², ∀ y ∈ S, y ≠ x → dot2 (y - x) n < 0) :
    ∃ p : Fin 7 → ℝ², (∀ i, p i ∈ S) ∧ Function.Injective p ∧
      ∀ i j k : Fin 7, i < j → j < k → 0 < det2 (p j - p i) (p k - p i) := by
  let O : ℝ² := ((1 : ℝ) / 7) • ∑ z ∈ S, z
  have hO_lt : ∀ x ∈ S, ∀ n : ℝ², (∀ y ∈ S, y ≠ x → dot2 (y - x) n < 0) →
      dot2 (O - x) n < 0 := by
    intro x hx n hn
    have hsum_eq : dot2 (O - x) n = (1 / 7 : ℝ) * ∑ z ∈ S, dot2 (z - x) n := by
      have hO0 : O 0 - x 0 = (1 / 7 : ℝ) * ∑ z ∈ S, (z 0 - x 0) := by
        have h1 : O 0 = (1 / 7 : ℝ) * ∑ z ∈ S, z 0 := by
          simp [O, Finset.sum_apply]
        have h2 : ∑ z ∈ S, (z 0 - x 0) = (∑ z ∈ S, z 0) - 7 * x 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, hS, nsmul_eq_mul]
          ring
        linarith
      have hO1 : O 1 - x 1 = (1 / 7 : ℝ) * ∑ z ∈ S, (z 1 - x 1) := by
        have h1 : O 1 = (1 / 7 : ℝ) * ∑ z ∈ S, z 1 := by
          simp [O, Finset.sum_apply]
        have h2 : ∑ z ∈ S, (z 1 - x 1) = (∑ z ∈ S, z 1) - 7 * x 1 := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, hS, nsmul_eq_mul]
          ring
        linarith
      simp only [dot2, PiLp.sub_apply]
      rw [hO0, hO1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    rw [hsum_eq]
    have hne : (S.erase x).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx, hS]; omega)
    obtain ⟨y0, hy0⟩ := hne
    have hsum_neg : ∑ z ∈ S, dot2 (z - x) n < 0 := by
      rw [← Finset.add_sum_erase S _ hx]
      have hx0 : dot2 (x - x) n = 0 := by simp [dot2]
      rw [hx0, zero_add]
      exact Finset.sum_neg (fun z hz => hn z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz))
        ⟨y0, hy0⟩
    linarith
  have hO_ne : ∀ x ∈ S, x - O ≠ 0 := by
    intro x hx h0
    obtain ⟨n, hn⟩ := hsup x hx
    have hlt := hO_lt x hx n hn
    have heq : O - x = 0 := by
      have : x = O := sub_eq_zero.mp h0
      simp [this]
    rw [heq] at hlt
    simp [dot2] at hlt
  have harg_inj : Set.InjOn (fun x : ℝ² => Complex.arg (toComplex (x - O))) (S : Set ℝ²) := by
    intro x hx y hy harg
    by_contra hxy
    have hnx : 0 < ‖x - O‖ := norm_pos_iff.mpr (hO_ne x hx)
    have hny : 0 < ‖y - O‖ := norm_pos_iff.mpr (hO_ne y hy)
    obtain ⟨hx0, hx1⟩ := toComplex_re_im (x - O)
    obtain ⟨hy0, hy1⟩ := toComplex_re_im (y - O)
    dsimp only at harg
    rw [harg] at hx0 hx1
    have hscale : y - O = (‖y - O‖ / ‖x - O‖) • (x - O) := by
      apply r2_ext
      · change (y - O) 0 = (‖y - O‖ / ‖x - O‖) * (x - O) 0
        rw [hy0, hx0]
        field_simp [hnx.ne']
      · change (y - O) 1 = (‖y - O‖ / ‖x - O‖) * (x - O) 1
        rw [hy1, hx1]
        field_simp [hnx.ne']
    let t := ‖y - O‖ / ‖x - O‖
    have ht_pos : 0 < t := div_pos hny hnx
    have hy0_eq : y 0 = O 0 + t * (x 0 - O 0) := by
      have := congrArg (fun z : ℝ² => z 0) hscale
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
      linarith
    have hy1_eq : y 1 = O 1 + t * (x 1 - O 1) := by
      have := congrArg (fun z : ℝ² => z 1) hscale
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
      linarith
    rcases lt_trichotomy t 1 with htlt | hteq | htgt
    · -- y = (1 - t) O + t x, contradicts support at y
      obtain ⟨n, hn⟩ := hsup y hy
      have h1 := hO_lt y hy n hn
      have h2 := hn x hx hxy
      have hcomb : (1 - t) * dot2 (O - y) n + t * dot2 (x - y) n = 0 := by
        simp only [dot2, PiLp.sub_apply]
        rw [hy0_eq, hy1_eq]
        ring
      nlinarith only [hcomb, h1, h2, ht_pos, htlt]
    · apply hxy
      have : y - O = x - O := by simpa [t, hteq] using hscale
      exact (sub_left_inj.mp this).symm
    · -- x = (1 - 1/t) O + (1/t) y, contradicts support at x
      obtain ⟨n, hn⟩ := hsup x hx
      have h1 := hO_lt x hx n hn
      have h2 := hn y hy (Ne.symm hxy)
      have hcomb : (t - 1) * dot2 (O - x) n + dot2 (y - x) n = 0 := by
        simp only [dot2, PiLp.sub_apply]
        rw [hy0_eq, hy1_eq]
        ring
      nlinarith only [hcomb, h1, h2, htgt]
  let f : ℝ² → ℝ := fun x => Complex.arg (toComplex (x - O))
  let T := S.image f
  have hT7 : T.card = 7 := by rw [Finset.card_image_of_injOn harg_inj, hS]
  let emb : Fin 7 ↪o ℝ := T.orderEmbOfFin hT7
  have hpre : ∀ i : Fin 7, ∃ x ∈ S, f x = emb i := fun i =>
    Finset.mem_image.mp (Finset.orderEmbOfFin_mem T hT7 i)
  let p : Fin 7 → ℝ² := fun i => (hpre i).choose
  have hp_mem : ∀ i, p i ∈ S := fun i => (hpre i).choose_spec.1
  have hp_val : ∀ i, f (p i) = emb i := fun i => (hpre i).choose_spec.2
  have hp_mono : ∀ i j : Fin 7, i < j → f (p i) < f (p j) := fun i j hij => by
    rw [hp_val, hp_val]
    exact emb.strictMono hij
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hp_mono i j hlt).ne (congrArg f hij)
    · exact (hp_mono j i hgt).ne (congrArg f hij.symm)
  -- Helper: if a, b, c ∈ S have gap from a to c through b in (0, π], then det2 (b - a) (c - a) > 0
  have hsector : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ∀ θ1 θ2 : ℝ, 0 < θ1 → 0 < θ2 → θ1 + θ2 ≤ Real.pi →
      (Complex.arg (toComplex (b - O)) - Complex.arg (toComplex (a - O)) = θ1 ∨
       Complex.arg (toComplex (b - O)) - Complex.arg (toComplex (a - O)) = θ1 - 2 * Real.pi) →
      (Complex.arg (toComplex (c - O)) - Complex.arg (toComplex (b - O)) = θ2 ∨
       Complex.arg (toComplex (c - O)) - Complex.arg (toComplex (b - O)) = θ2 - 2 * Real.pi) →
      0 < det2 (b - a) (c - a) := by
    intro a ha b hb c hc hab hbc hac θ1 θ2 h1 h2 h12 hd1 hd2
    have hna : 0 < ‖a - O‖ := norm_pos_iff.mpr (hO_ne a ha)
    have hnb : 0 < ‖b - O‖ := norm_pos_iff.mpr (hO_ne b hb)
    have hnc : 0 < ‖c - O‖ := norm_pos_iff.mpr (hO_ne c hc)
    have hs1 : Real.sin (f b - f a) = Real.sin θ1 := by
      rcases hd1 with h | h
      · rw [h]
      · rw [h, Real.sin_sub_two_pi]
    have hs2 : Real.sin (f c - f b) = Real.sin θ2 := by
      rcases hd2 with h | h
      · rw [h]
      · rw [h, Real.sin_sub_two_pi]
    have hs12 : Real.sin (f c - f a) = Real.sin (θ1 + θ2) := by
      have hdiff : f c - f a = (f c - f b) + (f b - f a) := by ring
      rw [hdiff]
      rcases hd1 with h1' | h1' <;> rcases hd2 with h2' | h2'
      · rw [h1', h2', add_comm]
      · rw [h1', h2', show θ2 - 2 * Real.pi + θ1 = (θ1 + θ2) - 2 * Real.pi by ring,
          Real.sin_sub_two_pi]
      · rw [h1', h2', show θ2 + (θ1 - 2 * Real.pi) = (θ1 + θ2) - 2 * Real.pi by ring,
          Real.sin_sub_two_pi]
      · rw [h1', h2', show θ2 - 2 * Real.pi + (θ1 - 2 * Real.pi) =
          ((θ1 + θ2) - 2 * Real.pi) - 2 * Real.pi by ring,
          Real.sin_sub_two_pi, Real.sin_sub_two_pi]
    have hdet_ab : 0 < det2 (a - O) (b - O) := by
      rw [det2_eq_norm_sin]
      change 0 < ‖a - O‖ * ‖b - O‖ * Real.sin (f b - f a)
      rw [hs1]
      exact mul_pos (mul_pos hna hnb) (Real.sin_pos_of_pos_of_lt_pi h1 (by linarith))
    have hdet_bc : 0 < det2 (b - O) (c - O) := by
      rw [det2_eq_norm_sin]
      change 0 < ‖b - O‖ * ‖c - O‖ * Real.sin (f c - f b)
      rw [hs2]
      exact mul_pos (mul_pos hnb hnc) (Real.sin_pos_of_pos_of_lt_pi h2 (by linarith))
    rcases eq_or_lt_of_le h12 with hpi | hlt_pi
    · -- θ1 + θ2 = π, so c - O = -λ (a - O) with λ > 0
      have hcos_ac : Real.cos (f c - f a) = -1 := by
        have hdiff : f c - f a = (f c - f b) + (f b - f a) := by ring
        rw [hdiff]
        rcases hd1 with h1' | h1' <;> rcases hd2 with h2' | h2'
        · rw [h1', h2', show θ2 + θ1 = Real.pi by linarith, Real.cos_pi]
        · rw [h1', h2', show θ2 - 2 * Real.pi + θ1 = Real.pi - 2 * Real.pi by linarith,
            Real.cos_sub_two_pi, Real.cos_pi]
        · rw [h1', h2', show θ2 + (θ1 - 2 * Real.pi) = Real.pi - 2 * Real.pi by linarith,
            Real.cos_sub_two_pi, Real.cos_pi]
        · rw [h1', h2', show θ2 - 2 * Real.pi + (θ1 - 2 * Real.pi) =
            (Real.pi - 2 * Real.pi) - 2 * Real.pi by linarith,
            Real.cos_sub_two_pi, Real.cos_sub_two_pi, Real.cos_pi]
      have hsin_ac : Real.sin (f c - f a) = 0 := by rw [hs12, hpi, Real.sin_pi]
      obtain ⟨ha0, ha1⟩ := toComplex_re_im (a - O)
      obtain ⟨hc0, hc1⟩ := toComplex_re_im (c - O)
      have hc_eq : c - O = (-(‖c - O‖ / ‖a - O‖)) • (a - O) := by
        have hfc : f c = (f c - f a) + f a := by ring
        have hcosc : Real.cos (f c) = -Real.cos (f a) := by
          rw [hfc, Real.cos_add, hcos_ac, hsin_ac]; ring
        have hsinc : Real.sin (f c) = -Real.sin (f a) := by
          rw [hfc, Real.sin_add, hcos_ac, hsin_ac]; ring
        apply r2_ext
        · change (c - O) 0 = -(‖c - O‖ / ‖a - O‖) * (a - O) 0
          rw [hc0, ha0]
          change ‖c - O‖ * Real.cos (f c) = -(‖c - O‖ / ‖a - O‖) * (‖a - O‖ * Real.cos (f a))
          rw [hcosc]; field_simp [hna.ne']
        · change (c - O) 1 = -(‖c - O‖ / ‖a - O‖) * (a - O) 1
          rw [hc1, ha1]
          change ‖c - O‖ * Real.sin (f c) = -(‖c - O‖ / ‖a - O‖) * (‖a - O‖ * Real.sin (f a))
          rw [hsinc]; field_simp [hna.ne']
      have hdet_eq : det2 (b - a) (c - a) = (1 + ‖c - O‖ / ‖a - O‖) * det2 (a - O) (b - O) := by
        set k := ‖c - O‖ / ‖a - O‖
        have h0 : c 0 = O 0 - k * (a 0 - O 0) := by
          have := congrArg (fun z : ℝ² => z 0) hc_eq
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
          linarith
        have h1' : c 1 = O 1 - k * (a 1 - O 1) := by
          have := congrArg (fun z : ℝ² => z 1) hc_eq
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
          linarith
        simp only [det2, PiLp.sub_apply]
        rw [h0, h1']
        ring
      rw [hdet_eq]
      exact mul_pos (by positivity) hdet_ab
    · -- θ1 + θ2 < π
      have hdet_ac : 0 < det2 (a - O) (c - O) := by
        rw [det2_eq_norm_sin]
        change 0 < ‖a - O‖ * ‖c - O‖ * Real.sin (f c - f a)
        rw [hs12]
        exact mul_pos (mul_pos hna hnc) (Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt_pi)
      let α := det2 (b - O) (c - O) / det2 (a - O) (c - O)
      let β := det2 (a - O) (b - O) / det2 (a - O) (c - O)
      have hα : 0 < α := div_pos hdet_bc hdet_ac
      have hβ : 0 < β := div_pos hdet_ab hdet_ac
      have hcramer : b - O = α • (a - O) + β • (c - O) := by
        have hlin0 : det2 (a - O) (c - O) * (b - O) 0 =
            det2 (b - O) (c - O) * (a - O) 0 + det2 (a - O) (b - O) * (c - O) 0 := by
          simp only [det2, PiLp.sub_apply]; ring
        have hlin1 : det2 (a - O) (c - O) * (b - O) 1 =
            det2 (b - O) (c - O) * (a - O) 1 + det2 (a - O) (b - O) * (c - O) 1 := by
          simp only [det2, PiLp.sub_apply]; ring
        apply r2_ext
        · change (b - O) 0 = α * (a - O) 0 + β * (c - O) 0
          dsimp only [α, β]
          field_simp [hdet_ac.ne']
          linarith only [hlin0]
        · change (b - O) 1 = α * (a - O) 1 + β * (c - O) 1
          dsimp only [α, β]
          field_simp [hdet_ac.ne']
          linarith only [hlin1]
      have hb0 : b 0 = O 0 + α * (a 0 - O 0) + β * (c 0 - O 0) := by
        have := congrArg (fun z : ℝ² => z 0) hcramer
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at this
        linarith
      have hb1 : b 1 = O 1 + α * (a 1 - O 1) + β * (c 1 - O 1) := by
        have := congrArg (fun z : ℝ² => z 1) hcramer
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at this
        linarith
      have hsum_gt : 1 < α + β := by
        by_contra! hle
        obtain ⟨n, hn⟩ := hsup b hb
        have hOn := hO_lt b hb n hn
        have han := hn a ha hab
        have hcn := hn c hc hbc.symm
        have hcomb : (1 - α - β) * dot2 (O - b) n + α * dot2 (a - b) n + β * dot2 (c - b) n = 0 := by
          simp only [dot2, PiLp.sub_apply]
          rw [hb0, hb1]
          ring
        nlinarith only [hcomb, hOn, han, hcn, hα, hβ, hle]
      have hdet_eq : det2 (b - a) (c - a) = (α + β - 1) * det2 (a - O) (c - O) := by
        simp only [det2, PiLp.sub_apply]
        rw [hb0, hb1]
        ring
      rw [hdet_eq]
      exact mul_pos (by linarith) hdet_ac
  refine ⟨p, hp_mem, hp_inj, ?_⟩
  intro i j k hij hjk
  let a := p i; let b := p j; let c := p k
  have ha : a ∈ S := hp_mem i; have hb : b ∈ S := hp_mem j; have hc : c ∈ S := hp_mem k
  have hab : a ≠ b := hp_inj.ne hij.ne
  have hbc : b ≠ c := hp_inj.ne hjk.ne
  have hac : a ≠ c := hp_inj.ne (hij.trans hjk).ne
  have hfa_lt : f a < f b := hp_mono i j hij
  have hfb_lt : f b < f c := hp_mono j k hjk
  have hfa_gt : -Real.pi < f a := Complex.neg_pi_lt_arg _
  have hfc_le : f c ≤ Real.pi := Complex.arg_le_pi _
  let g1 := f b - f a
  let g2 := f c - f b
  let g3 := 2 * Real.pi - (f c - f a)
  have hg1 : 0 < g1 := by dsimp [g1]; linarith
  have hg2 : 0 < g2 := by dsimp [g2]; linarith
  have hg3 : 0 < g3 := by dsimp [g3]; linarith
  have hcyc1 : det2 (b - a) (c - a) = det2 (c - b) (a - b) := by simp only [det2, PiLp.sub_apply]; ring
  have hcyc2 : det2 (b - a) (c - a) = det2 (a - c) (b - c) := by simp only [det2, PiLp.sub_apply]; ring
  by_cases h12 : g1 + g2 ≤ Real.pi
  · exact hsector a ha b hb c hc hab hbc hac g1 g2 hg1 hg2 h12 (Or.inl rfl) (Or.inl rfl)
  by_cases h23 : g2 + g3 ≤ Real.pi
  · rw [hcyc1]
    exact hsector b hb c hc a ha hbc hac.symm hab.symm g2 g3 hg2 hg3 h23 (Or.inl rfl)
      (Or.inr (by dsimp [g3]; ring))
  by_cases h31 : g3 + g1 ≤ Real.pi
  · rw [hcyc2]
    exact hsector c hc a ha b hb hac.symm hab hbc.symm g3 g1 hg3 hg1 h31
      (Or.inr (by dsimp [g3]; ring)) (Or.inl rfl)
  -- Otherwise all three gaps g1, g2, g3 < π
  have hna : 0 < ‖a - O‖ := norm_pos_iff.mpr (hO_ne a ha)
  have hnb : 0 < ‖b - O‖ := norm_pos_iff.mpr (hO_ne b hb)
  have hnc : 0 < ‖c - O‖ := norm_pos_iff.mpr (hO_ne c hc)
  have hg1_lt : g1 < Real.pi := by dsimp [g1, g2, g3] at h23 ⊢; linarith
  have hg2_lt : g2 < Real.pi := by dsimp [g1, g2, g3] at h31 ⊢; linarith
  have hg3_lt : g3 < Real.pi := by dsimp [g1, g2, g3] at h12 ⊢; linarith
  have hd1 : 0 < det2 (a - O) (b - O) := by
    rw [det2_eq_norm_sin]
    exact mul_pos (mul_pos hna hnb) (Real.sin_pos_of_pos_of_lt_pi hg1 hg1_lt)
  have hd2 : 0 < det2 (b - O) (c - O) := by
    rw [det2_eq_norm_sin]
    exact mul_pos (mul_pos hnb hnc) (Real.sin_pos_of_pos_of_lt_pi hg2 hg2_lt)
  have hd3 : 0 < det2 (c - O) (a - O) := by
    rw [det2_eq_norm_sin]
    have hsin : Real.sin (f a - f c) = Real.sin g3 := by
      rw [show f a - f c = g3 - 2 * Real.pi by dsimp [g3]; ring, Real.sin_sub_two_pi]
    change 0 < ‖c - O‖ * ‖a - O‖ * Real.sin (f a - f c)
    rw [hsin]
    exact mul_pos (mul_pos hnc hna) (Real.sin_pos_of_pos_of_lt_pi hg3 hg3_lt)
  have hsum : det2 (b - a) (c - a) = det2 (a - O) (b - O) + det2 (b - O) (c - O) + det2 (c - O) (a - O) := by
    simp only [det2, PiLp.sub_apply]; ring
  linarith

/- ## Case d = 3, Step 3: Crossing-diagonal inequality and 7-gon rigidity -/

private lemma dist_lt_add_of_det2_ne_zero (u q v : ℝ²) (h : det2 (u - q) (v - q) ≠ 0) :
    dist u v < dist u q + dist q v := by
  have hL := lagrange_r2 (u - q) (v - q)
  rw [dot2_sub_norm_sq, dot2_sub_norm_sq] at hL
  have hdet_pos : 0 < det2 (u - q) (v - q) ^ 2 := sq_pos_of_ne_zero h
  have hprod : -dot2 (u - q) (v - q) < dist u q * dist v q := by
    by_contra! hle
    have hnn : 0 ≤ dist u q * dist v q := mul_nonneg dist_nonneg dist_nonneg
    have hsq_le : (dist u q * dist v q) ^ 2 ≤ (-dot2 (u - q) (v - q)) ^ 2 := by
      nlinarith only [hle, hnn]
    nlinarith only [hL, hdet_pos, hsq_le]
  have hexp : dist u v ^ 2 = dist u q ^ 2 + dist v q ^ 2 - 2 * dot2 (u - q) (v - q) := by
    rw [dist_sq_r2, dist_sq_r2, dist_sq_r2]
    simp only [dot2, PiLp.sub_apply]
    ring
  have hsq : dist u v ^ 2 < (dist u q + dist q v) ^ 2 := by
    rw [dist_comm q v]
    nlinarith only [hexp, hprod]
  nlinarith only [hsq, dist_nonneg (x := u) (y := v), dist_nonneg (x := u) (y := q),
    dist_nonneg (x := q) (y := v)]

private lemma crossing_diag_gt (x y z w : ℝ²)
    (hd1 : 0 < det2 (z - x) (w - x)) (hd2 : 0 < det2 (y - x) (z - x))
    (hd3 : 0 < det2 (y - x) (w - x)) (hd4 : 0 < det2 (z - y) (w - y)) :
    dist x y + dist z w < dist x z + dist y w ∧
    dist y z + dist w x < dist x z + dist y w := by
  set d1 := det2 (z - x) (w - x)
  set d2 := det2 (y - x) (z - x)
  set d3 := det2 (y - x) (w - x)
  set d4 := det2 (z - y) (w - y)
  have hsum : d1 + d2 = d3 + d4 := by
    simp only [d1, d2, d3, d4, det2, PiLp.sub_apply]; ring
  have hden : 0 < d1 + d2 := by linarith
  let q : ℝ² := (d1 / (d1 + d2)) • y + (d2 / (d1 + d2)) • w
  have hq_xz : q = (d4 / (d1 + d2)) • x + (d3 / (d1 + d2)) • z := by
    apply r2_ext
    · change (d1 / (d1 + d2)) * y 0 + (d2 / (d1 + d2)) * w 0 =
        (d4 / (d1 + d2)) * x 0 + (d3 / (d1 + d2)) * z 0
      field_simp [hden.ne']
      simp only [d1, d2, d3, d4, det2, PiLp.sub_apply]; ring
    · change (d1 / (d1 + d2)) * y 1 + (d2 / (d1 + d2)) * w 1 =
        (d4 / (d1 + d2)) * x 1 + (d3 / (d1 + d2)) * z 1
      field_simp [hden.ne']
      simp only [d1, d2, d3, d4, det2, PiLp.sub_apply]; ring
  have hseg : ∀ (u v : ℝ²) (t : ℝ), 0 < t → t < 1 →
      dist u ((1 - t) • u + t • v) + dist ((1 - t) • u + t • v) v = dist u v := by
    intro u v t ht0 ht1
    have h1 : (1 - t) • u + t • v - u = t • (v - u) := by
      ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have h2 : v - ((1 - t) • u + t • v) = (1 - t) • (v - u) := by
      ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [dist_comm u _, dist_eq_norm, h1, norm_smul, Real.norm_of_nonneg ht0.le,
      dist_comm _ v, dist_eq_norm, h2, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - t),
      dist_comm u v, dist_eq_norm]
    ring
  have hxz : dist x q + dist q z = dist x z := by
    have h1 : q = (1 - d3 / (d1 + d2)) • x + (d3 / (d1 + d2)) • z := by
      rw [hq_xz]
      congr 1
      have : 1 - d3 / (d1 + d2) = d4 / (d1 + d2) := by field_simp [hden.ne']; linarith
      rw [this]
    rw [h1]
    exact hseg x z (d3 / (d1 + d2)) (div_pos hd3 hden) ((div_lt_one hden).mpr (by linarith))
  have hyw : dist y q + dist q w = dist y w := by
    have h1 : q = (1 - d2 / (d1 + d2)) • y + (d2 / (d1 + d2)) • w := by
      dsimp [q]
      congr 1
      have : 1 - d2 / (d1 + d2) = d1 / (d1 + d2) := by field_simp [hden.ne']; ring
      rw [this]
    rw [h1]
    exact hseg y w (d2 / (d1 + d2)) (div_pos hd2 hden) ((div_lt_one hden).mpr (by linarith))
  have hq_sub_x : x - q = (-(d3 / (d1 + d2))) • (z - x) := by
    rw [hq_xz]
    ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hden.ne']; rw [hsum]; ring
  have hq_sub_z : z - q = (d4 / (d1 + d2)) • (z - x) := by
    rw [hq_xz]
    ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hden.ne']; rw [hsum]; ring
  have hq_sub_y : y - q = (-(d2 / (d1 + d2))) • (w - y) := by
    dsimp [q]
    ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hden.ne']; ring
  have hq_sub_w : w - q = (d1 / (d1 + d2)) • (w - y) := by
    dsimp [q]
    ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hden.ne']; ring
  have hdet_zx_wy : det2 (z - x) (w - y) = d1 + d2 := by
    simp only [d1, d2, det2, PiLp.sub_apply]; ring
  have hdet_smul : ∀ (a' b' : ℝ) (u v : ℝ²), det2 (a' • u) (b' • v) = a' * b' * det2 u v := by
    intro a' b' u v; simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring
  have hdet_xy : det2 (x - q) (y - q) ≠ 0 := by
    rw [hq_sub_x, hq_sub_y, hdet_smul, hdet_zx_wy]
    have hval : -(d3 / (d1 + d2)) * -(d2 / (d1 + d2)) * (d1 + d2) = d3 * d2 / (d1 + d2) := by
      field_simp [hden.ne']
    rw [hval]
    exact (div_pos (mul_pos hd3 hd2) hden).ne'
  have hdet_zw : det2 (z - q) (w - q) ≠ 0 := by
    rw [hq_sub_z, hq_sub_w, hdet_smul, hdet_zx_wy]
    have hval : d4 / (d1 + d2) * (d1 / (d1 + d2)) * (d1 + d2) = d4 * d1 / (d1 + d2) := by
      field_simp [hden.ne']
    rw [hval]
    exact (div_pos (mul_pos hd4 hd1) hden).ne'
  have hdet_yz : det2 (y - q) (z - q) ≠ 0 := by
    rw [hq_sub_y, hq_sub_z, hdet_smul]
    have hanti : det2 (w - y) (z - x) = -(d1 + d2) := by
      rw [← hdet_zx_wy]; simp only [det2]; ring
    rw [hanti]
    have hval : -(d2 / (d1 + d2)) * (d4 / (d1 + d2)) * -(d1 + d2) = d2 * d4 / (d1 + d2) := by
      field_simp [hden.ne']
    rw [hval]
    exact (div_pos (mul_pos hd2 hd4) hden).ne'
  have hdet_wx : det2 (w - q) (x - q) ≠ 0 := by
    rw [hq_sub_w, hq_sub_x, hdet_smul]
    have hanti : det2 (w - y) (z - x) = -(d1 + d2) := by
      rw [← hdet_zx_wy]; simp only [det2]; ring
    rw [hanti]
    have hval : d1 / (d1 + d2) * -(d3 / (d1 + d2)) * -(d1 + d2) = d1 * d3 / (d1 + d2) := by
      field_simp [hden.ne']
    rw [hval]
    exact (div_pos (mul_pos hd1 hd3) hden).ne'
  have hxy_lt := dist_lt_add_of_det2_ne_zero x q y hdet_xy
  have hzw_lt := dist_lt_add_of_det2_ne_zero z q w hdet_zw
  have hyz_lt := dist_lt_add_of_det2_ne_zero y q z hdet_yz
  have hwx_lt := dist_lt_add_of_det2_ne_zero w q x hdet_wx
  constructor
  · rw [← hxz, ← hyw]
    linarith [dist_comm q y, dist_comm q z]
  · rw [← hxz, ← hyw]
    linarith [dist_comm q z, dist_comm q x, dist_comm q w]

private lemma convex_seven_unique (d : ZMod 7 → ZMod 7 → ℝ) (a b c : ℝ)
    (hab : a < b) (hbc : b < c)
    (hsym : ∀ i j, d i j = d j i)
    (hval : ∀ i j, i ≠ j → d i j = a ∨ d i j = b ∨ d i j = c)
    (hcross : ∀ (i : ZMod 7) (s1 s2 s3 : ℕ), 0 < s1 → s1 < s2 → s2 < s3 → s3 < 7 →
      d i (i + s1) + d (i + s2) (i + s3) < d i (i + s2) + d (i + s1) (i + s3) ∧
      d (i + s1) (i + s2) + d (i + s3) i < d i (i + s2) + d (i + s1) (i + s3)) :
    (∀ i : ZMod 7, d i (i + 1) = a) ∧ (∀ i : ZMod 7, d i (i + 2) = b) := by
  have hle : ∀ i j, i ≠ j → a ≤ d i j ∧ d i j ≤ c := by
    intro i j hij
    rcases hval i j hij with h | h | h <;> constructor <;> linarith
  have hq : ∀ (i : ZMod 7) (s1 s2 s3 : ℕ), 0 < s1 → s1 < s2 → s2 < s3 → s3 < 7 →
      d i (i + (s1 : ZMod 7)) + d (i + (s2 : ZMod 7)) (i + (s3 : ZMod 7)) <
        d i (i + (s2 : ZMod 7)) + d (i + (s1 : ZMod 7)) (i + (s3 : ZMod 7)) ∧
      d (i + (s1 : ZMod 7)) (i + (s2 : ZMod 7)) + d (i + (s3 : ZMod 7)) i <
        d i (i + (s2 : ZMod 7)) + d (i + (s1 : ZMod 7)) (i + (s3 : ZMod 7)) := hcross
  have hne : ∀ (i : ZMod 7) (k : ℕ), 0 < k → k < 7 → i ≠ i + (k : ZMod 7) := by
    intro i k hk0 hk7 he
    have h0 : (k : ZMod 7) = 0 := by
      have := congrArg (· - i) he
      simpa using this.symm
    have hdvd : 7 ∣ k := (ZMod.natCast_eq_zero_iff k 7).mp h0
    omega
  have hne_add : ∀ (i : ZMod 7) (u v : ℕ), u < v → v < 7 →
      i + (u : ZMod 7) ≠ i + (v : ZMod 7) := by
    intro i u v huv hv he
    have hsub : ((v - u : ℕ) : ZMod 7) = 0 := by
      rw [Nat.cast_sub huv.le]
      have := congrArg (· - i - (u : ZMod 7)) he
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
    have hdvd : 7 ∣ v - u := (ZMod.natCast_eq_zero_iff (v - u) 7).mp hsub
    omega
  -- Lemma 1: no step-1 edge is c
  have hL1 : ∀ i : ZMod 7, d i (i + 1) ≠ c := by
    intro i hc01
    have hab_sub : ∀ (u v : ℕ), 2 ≤ u → u < v → v ≤ 6 →
        d (i + (u : ZMod 7)) (i + (v : ZMod 7)) = a ∨
        d (i + (u : ZMod 7)) (i + (v : ZMod 7)) = b := by
      intro u v hu huv hv
      have hcr := (hq i 1 u v (by omega) (by omega) huv (by omega)).1
      have hiu : i ≠ i + (u : ZMod 7) := hne i u (by omega) (by omega)
      have h1v : i + (1 : ZMod 7) ≠ i + (v : ZMod 7) := by
        simpa using hne_add i 1 v (by omega) (by omega)
      have huv_ne : i + (u : ZMod 7) ≠ i + (v : ZMod 7) := hne_add i u v huv (by omega)
      have h1 := (hle _ _ hiu).2
      have h2 := (hle _ _ h1v).2
      rcases hval _ _ huv_ne with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · simp only [Nat.cast_one] at hcr
        linarith
    -- On 5-subset {i+2, i+3, i+4, i+5, i+6}, all edges lie in {a, b}
    have hab_ge : ∀ (u v : ℕ), 2 ≤ u → u < v → v ≤ 6 →
        a ≤ d (i + (u : ZMod 7)) (i + (v : ZMod 7)) := fun u v hu huv hv => by
      rcases hab_sub u v hu huv hv with h | h <;> linarith
    have h24 : d (i + 2) (i + 4) = b := by
      rcases hab_sub 2 4 (by omega) (by omega) (by omega) with h24a | h24b
      · exfalso
        have hcr1 := hq (i + 2) 1 2 3 (by omega) (by omega) (by omega) (by omega)
        have hcr2 := hq (i + 2) 1 2 4 (by omega) (by omega) (by omega) (by omega)
        have hcr3 := hq (i + 2) 2 3 4 (by omega) (by omega) (by omega) (by omega)
        have hge23 := hab_ge 2 3 (by omega) (by omega) (by omega)
        have hge34 := hab_ge 3 4 (by omega) (by omega) (by omega)
        have hge45 := hab_ge 4 5 (by omega) (by omega) (by omega)
        have hge46 := hab_ge 4 6 (by omega) (by omega) (by omega)
        have hge56 := hab_ge 5 6 (by omega) (by omega) (by omega)
        have hs35 := hab_sub 3 5 (by omega) (by omega) (by omega)
        have hs25 := hab_sub 2 5 (by omega) (by omega) (by omega)
        have hs36 := hab_sub 3 6 (by omega) (by omega) (by omega)
        have hs46 := hab_sub 4 6 (by omega) (by omega) (by omega)
        simp only [Nat.cast_one, Nat.cast_ofNat, add_assoc] at hcr1 hcr2 hcr3 hge23 hge34 hge45 hge46 hge56 hs35 hs25 hs36 hs46 h24a
        norm_num at hcr1 hcr2 hcr3
        rw [hsym (i + 5) (i + 2)] at hcr1
        rw [hsym (i + 6) (i + 2)] at hcr2 hcr3
        have h35 : d (i + 3) (i + 5) = b := by rcases hs35 with h | h <;> linarith [hcr1.1]
        have h25 : d (i + 2) (i + 5) = a := by rcases hs25 with h | h <;> linarith [hcr1.2]
        have h36 : d (i + 3) (i + 6) = b := by rcases hs36 with h | h <;> linarith [hcr2.1]
        have h46 : d (i + 4) (i + 6) = a := by rcases hs46 with h | h <;> linarith [hcr2.1]
        linarith [hcr3.1]
      · exact h24b
    have h35 : d (i + 3) (i + 5) = b := by
      rcases hab_sub 3 5 (by omega) (by omega) (by omega) with h35a | h35b
      · exfalso
        have hcr1 := hq (i + 2) 1 2 3 (by omega) (by omega) (by omega) (by omega)
        have hcr2 := hq (i + 3) 1 2 3 (by omega) (by omega) (by omega) (by omega)
        have hcr3 := hq (i + 2) 1 2 4 (by omega) (by omega) (by omega) (by omega)
        have hge23 := hab_ge 2 3 (by omega) (by omega) (by omega)
        have hge34 := hab_ge 3 4 (by omega) (by omega) (by omega)
        have hge45 := hab_ge 4 5 (by omega) (by omega) (by omega)
        have hge56 := hab_ge 5 6 (by omega) (by omega) (by omega)
        have hs25 := hab_sub 2 5 (by omega) (by omega) (by omega)
        have hs46 := hab_sub 4 6 (by omega) (by omega) (by omega)
        have hs36 := hab_sub 3 6 (by omega) (by omega) (by omega)
        have hs26 := hab_sub 2 6 (by omega) (by omega) (by omega)
        simp only [Nat.cast_one, Nat.cast_ofNat, add_assoc] at hcr1 hcr2 hcr3 hge23 hge34 hge45 hge56 hs25 hs46 hs36 hs26 h35a
        norm_num at hcr1 hcr2 hcr3
        rw [hsym (i + 5) (i + 2)] at hcr1
        rw [hsym (i + 6) (i + 3)] at hcr2
        rw [hsym (i + 6) (i + 2)] at hcr3
        have h25 : d (i + 2) (i + 5) = a := by rcases hs25 with h | h <;> linarith [hcr1.2, h24]
        have h46 : d (i + 4) (i + 6) = b := by rcases hs46 with h | h <;> linarith [hcr2.1]
        have h36 : d (i + 3) (i + 6) = a := by rcases hs36 with h | h <;> linarith [hcr2.2]
        have hcr4 := (hq (i + 2) 1 3 4 (by omega) (by omega) (by omega) (by omega)).1
        simp only [Nat.cast_one, Nat.cast_ofNat, add_assoc] at hcr4
        norm_num at hcr4
        linarith [hcr4]
      · exact h35b
    have hcr0124 := (hq i 1 2 4 (by omega) (by omega) (by omega) (by omega)).1
    have hcr0135 := (hq i 1 3 5 (by omega) (by omega) (by omega) (by omega)).1
    have hcr0235 := (hq i 2 3 5 (by omega) (by omega) (by omega) (by omega)).1
    simp only [Nat.cast_one, Nat.cast_ofNat] at hcr0124 hcr0135 hcr0235
    have h14_le : d (i + 1) (i + 4) ≤ c := (hle _ _ (by simpa using hne_add i 1 4 (by omega) (by omega))).2
    have h15_le : d (i + 1) (i + 5) ≤ c := (hle _ _ (by simpa using hne_add i 1 5 (by omega) (by omega))).2
    have h02 : d i (i + 2) = c := by
      rcases hval i (i + 2) (hne i 2 (by omega) (by omega)) with h | h | h <;> linarith
    have h03 : d i (i + 3) = c := by
      rcases hval i (i + 3) (hne i 3 (by omega) (by omega)) with h | h | h <;> linarith
    have hs25 := hab_sub 2 5 (by omega) (by omega) (by omega)
    simp only [Nat.cast_ofNat] at hs25
    rcases hs25 with h25 | h25 <;> linarith
  -- Lemma 2: no step-3 edge is a
  have hL2 : ∀ i : ZMod 7, d i (i + 3) ≠ a := by
    intro i ha03
    have hcross_bc : ∀ (u v : ℕ), (u = 1 ∨ u = 2) → (v = 4 ∨ v = 5 ∨ v = 6) →
        d (i + (u : ZMod 7)) (i + (v : ZMod 7)) = b ∨
        d (i + (u : ZMod 7)) (i + (v : ZMod 7)) = c := by
      intro u v hu hv
      have hcr := (hq i u 3 v (by omega) (by omega) (by omega) (by omega)).1
      have hiu : a ≤ d i (i + (u : ZMod 7)) := (hle _ _ (hne i u (by omega) (by omega))).1
      have h3v : a ≤ d (i + 3) (i + (v : ZMod 7)) :=
        (hle _ _ (by simpa using hne_add i 3 v (by omega) (by omega))).1
      have huv : i + (u : ZMod 7) ≠ i + (v : ZMod 7) := hne_add i u v (by omega) (by omega)
      rcases hval _ _ huv with h | h | h
      · norm_num at hcr; linarith
      · exact Or.inl h
      · exact Or.inr h
    have hforce : ∀ (u v : ℕ), (u = 1 ∨ u = 2) → (v = 4 ∨ v = 5 ∨ v = 6) →
        d (i + (u : ZMod 7)) (i + (v : ZMod 7)) = b →
        d i (i + (u : ZMod 7)) = a ∧ d (i + (u : ZMod 7)) (i + 3) = a ∧
        d (i + 3) (i + (v : ZMod 7)) = a ∧ d (i + (v : ZMod 7)) i = a := by
      intro u v hu hv hbv
      have hcr := hq i u 3 v (by omega) (by omega) (by omega) (by omega)
      norm_num at hcr
      have hne1 : i ≠ i + (u : ZMod 7) := hne i u (by omega) (by omega)
      have hne2 : i + (u : ZMod 7) ≠ i + 3 := by simpa using hne_add i u 3 (by omega) (by omega)
      have hne3 : i + 3 ≠ i + (v : ZMod 7) := by simpa using hne_add i 3 v (by omega) (by omega)
      have hne4 : i + (v : ZMod 7) ≠ i := (hne i v (by omega) (by omega)).symm
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hval _ _ hne1 with h | h | h <;> linarith [(hle _ _ hne3).1]
      · rcases hval _ _ hne2 with h | h | h <;> linarith [(hle _ _ hne4).1]
      · rcases hval _ _ hne3 with h | h | h <;> linarith [(hle _ _ hne1).1]
      · rcases hval _ _ hne4 with h | h | h <;> linarith [(hle _ _ hne2).1]
    have h15_or_24 : d (i + 1) (i + 5) = b ∨ d (i + 2) (i + 4) = b := by
      have hcr := (hq (i + 1) 1 3 4 (by omega) (by omega) (by omega) (by omega)).2
      simp only [Nat.cast_one, Nat.cast_ofNat, add_assoc] at hcr; norm_num at hcr
      rw [hsym (i + 5) (i + 1)] at hcr
      have h14 := (hle (i + 1) (i + 4) (by simpa using hne_add i 1 4 (by omega) (by omega))).2
      have h25 := (hle (i + 2) (i + 5) (by simpa using hne_add i 2 5 (by omega) (by omega))).2
      rcases hcross_bc 1 5 (Or.inl rfl) (Or.inr (Or.inl rfl)) with h15 | h15
      · exact Or.inl (by simpa using h15)
      rcases hcross_bc 2 4 (Or.inr rfl) (Or.inl rfl) with h24 | h24
      · exact Or.inr (by simpa using h24)
      simp only [Nat.cast_one, Nat.cast_ofNat] at h15 h24
      linarith
    have h16_or_25 : d (i + 1) (i + 6) = b ∨ d (i + 2) (i + 5) = b := by
      have hcr := (hq (i + 1) 1 4 5 (by omega) (by omega) (by omega) (by omega)).2
      simp only [Nat.cast_one, Nat.cast_ofNat, add_assoc] at hcr; norm_num at hcr
      rw [hsym (i + 6) (i + 1)] at hcr
      have h15 := (hle (i + 1) (i + 5) (by simpa using hne_add i 1 5 (by omega) (by omega))).2
      have h26 := (hle (i + 2) (i + 6) (by simpa using hne_add i 2 6 (by omega) (by omega))).2
      rcases hcross_bc 1 6 (Or.inl rfl) (Or.inr (Or.inr rfl)) with h16 | h16
      · exact Or.inl (by simpa using h16)
      rcases hcross_bc 2 5 (Or.inr rfl) (Or.inr (Or.inl rfl)) with h25 | h25
      · exact Or.inr (by simpa using h25)
      simp only [Nat.cast_one, Nat.cast_ofNat] at h16 h25
      linarith
    rcases h15_or_24 with h15 | h24 <;> rcases h16_or_25 with h16 | h25
    · have f1 := hforce 1 5 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by simpa using h15)
      have f2 := hforce 1 6 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by simpa using h16)
      have hcr := (hq i 3 5 6 (by omega) (by omega) (by omega) (by omega)).1
      simp only [Nat.cast_ofNat] at f1 f2 hcr
      rw [hsym (i + 5) i] at f1
      have h56 := (hle (i + 5) (i + 6) (by simpa using hne_add i 5 6 (by omega) (by omega))).1
      linarith
    · have f1 := hforce 1 5 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by simpa using h15)
      have f2 := hforce 2 5 (Or.inr rfl) (Or.inr (Or.inl rfl)) (by simpa using h25)
      have hcr := (hq i 1 2 3 (by omega) (by omega) (by omega) (by omega)).1
      simp only [Nat.cast_one, Nat.cast_ofNat] at f1 f2 hcr
      have h01 := (hle i (i + 1) (hne i 1 (by omega) (by omega))).1
      have h23 := (hle (i + 2) (i + 3) (by simpa using hne_add i 2 3 (by omega) (by omega))).1
      linarith
    · have f1 := hforce 2 4 (Or.inr rfl) (Or.inl rfl) (by simpa using h24)
      have f2 := hforce 1 6 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by simpa using h16)
      have hcr := (hq i 1 2 3 (by omega) (by omega) (by omega) (by omega)).1
      simp only [Nat.cast_one, Nat.cast_ofNat] at f1 f2 hcr
      have h01 := (hle i (i + 1) (hne i 1 (by omega) (by omega))).1
      have h23 := (hle (i + 2) (i + 3) (by simpa using hne_add i 2 3 (by omega) (by omega))).1
      linarith
    · have f1 := hforce 2 4 (Or.inr rfl) (Or.inl rfl) (by simpa using h24)
      have f2 := hforce 2 5 (Or.inr rfl) (Or.inr (Or.inl rfl)) (by simpa using h25)
      have hcr := (hq i 3 4 5 (by omega) (by omega) (by omega) (by omega)).1
      simp only [Nat.cast_ofNat] at f1 f2 hcr
      rw [hsym (i + 4) i] at f1
      have h45 := (hle (i + 4) (i + 5) (by simpa using hne_add i 4 5 (by omega) (by omega))).1
      linarith
  have hL2' : ∀ i : ZMod 7, d i (i + 4) ≠ a := by
    intro i h
    rw [hsym] at h
    have hi : (i + 4) + 3 = i := by rw [add_assoc, show (4 : ZMod 7) + 3 = 0 by decide, add_zero]
    have h' : d (i + 4) ((i + 4) + 3) = a := by rwa [hi]
    exact hL2 (i + 4) h'
  -- Lemma 3: no step-2 edge is a
  have hL3 : ∀ i : ZMod 7, d i (i + 2) ≠ a := by
    intro i ha02
    have hcr1 := (hq i 1 2 3 (by omega) (by omega) (by omega) (by omega)).2
    have hcr2 := (hq i 1 2 4 (by omega) (by omega) (by omega) (by omega)).2
    have hcr3 := (hq i 1 3 4 (by omega) (by omega) (by omega) (by omega)).2
    simp only [Nat.cast_one, Nat.cast_ofNat] at hcr1 hcr2 hcr3
    rw [hsym (i + 3) i] at hcr1
    rw [hsym (i + 4) i] at hcr2 hcr3
    have h12 : a ≤ d (i + 1) (i + 2) := (hle _ _ (by simpa using hne_add i 1 2 (by omega) (by omega))).1
    have h03_ge : b ≤ d i (i + 3) := by
      rcases hval i (i + 3) (hne i 3 (by omega) (by omega)) with h | h | h
      · exact (hL2 i h).elim
      · linarith
      · linarith
    have h04_ge : b ≤ d i (i + 4) := by
      rcases hval i (i + 4) (hne i 4 (by omega) (by omega)) with h | h | h
      · exact (hL2' i h).elim
      · linarith
      · linarith
    have h13 : d (i + 1) (i + 3) = c := by
      rcases hval (i + 1) (i + 3) (by simpa using hne_add i 1 3 (by omega) (by omega)) with h | h | h <;> linarith
    have h14 : d (i + 1) (i + 4) = c := by
      rcases hval (i + 1) (i + 4) (by simpa using hne_add i 1 4 (by omega) (by omega)) with h | h | h <;> linarith
    have h03 : d i (i + 3) = b := by
      rcases hval i (i + 3) (hne i 3 (by omega) (by omega)) with h | h | h
      · exact (hL2 i h).elim
      · exact h
      · linarith
    have h04 : d i (i + 4) = b := by
      rcases hval i (i + 4) (hne i 4 (by omega) (by omega)) with h | h | h
      · exact (hL2' i h).elim
      · exact h
      · linarith
    linarith
  have hL3' : ∀ i : ZMod 7, d i (i + 5) ≠ a := by
    intro i h
    rw [hsym] at h
    have hi : (i + 5) + 2 = i := by rw [add_assoc, show (5 : ZMod 7) + 2 = 0 by decide, add_zero]
    have h' : d (i + 5) ((i + 5) + 2) = a := by rwa [hi]
    exact hL3 (i + 5) h'
  -- Lemma 4: every step-3 edge is c
  have hL4 : ∀ i : ZMod 7, d i (i + 3) = c := by
    intro i
    rcases hval i (i + 3) (hne i 3 (by omega) (by omega)) with h03a | h03b | h03c
    · exact (hL2 i h03a).elim
    · exfalso
      have hcr1 := (hq i 1 3 4 (by omega) (by omega) (by omega) (by omega)).2
      have hcr2 := (hq i 1 3 5 (by omega) (by omega) (by omega) (by omega)).2
      have hcr3 := (hq i 1 4 5 (by omega) (by omega) (by omega) (by omega)).2
      simp only [Nat.cast_one, Nat.cast_ofNat] at hcr1 hcr2 hcr3
      rw [hsym (i + 4) i] at hcr1
      rw [hsym (i + 5) i] at hcr2 hcr3
      have h13_ge : b ≤ d (i + 1) (i + 3) := by
        rcases hval (i + 1) (i + 3) (by simpa using hne_add i 1 3 (by omega) (by omega)) with h | h | h
        · rw [show i + 3 = (i + 1) + 2 by ring] at h; exact (hL3 (i + 1) h).elim
        · linarith
        · linarith
      have h04_ge : b ≤ d i (i + 4) := by
        rcases hval i (i + 4) (hne i 4 (by omega) (by omega)) with h | h | h
        · exact (hL2' i h).elim
        · linarith
        · linarith
      have h05_ge : b ≤ d i (i + 5) := by
        rcases hval i (i + 5) (hne i 5 (by omega) (by omega)) with h | h | h
        · exact (hL3' i h).elim
        · linarith
        · linarith
      have h14 : d (i + 1) (i + 4) = c := by
        rcases hval (i + 1) (i + 4) (by simpa using hne_add i 1 4 (by omega) (by omega)) with h | h | h <;> linarith
      have h15 : d (i + 1) (i + 5) = c := by
        rcases hval (i + 1) (i + 5) (by simpa using hne_add i 1 5 (by omega) (by omega)) with h | h | h <;> linarith
      have h04 : d i (i + 4) = b := by
        rcases hval i (i + 4) (hne i 4 (by omega) (by omega)) with h | h | h
        · exact (hL2' i h).elim
        · exact h
        · linarith
      have h05 : d i (i + 5) = b := by
        rcases hval i (i + 5) (hne i 5 (by omega) (by omega)) with h | h | h
        · exact (hL3' i h).elim
        · exact h
        · linarith
      linarith
    · exact h03c
  have hL4' : ∀ i : ZMod 7, d i (i + 4) = c := by
    intro i
    rw [hsym]
    have hi : i = (i + 4) + 3 := by rw [add_assoc, show (4 : ZMod 7) + 3 = 0 by decide, add_zero]
    conv_lhs => rhs; rw [hi]
    exact hL4 (i + 4)
  -- Lemma 5: every step-2 edge is b
  have hL5 : ∀ i : ZMod 7, d i (i + 2) = b := by
    intro i
    have hcr := (hq (i - 1) 1 3 4 (by omega) (by omega) (by omega) (by omega)).2
    simp only [Nat.cast_one, Nat.cast_ofNat] at hcr
    have h1 : (i - 1) + 1 = i := by ring
    have h2 : (i - 1) + 3 = i + 2 := by ring
    have h3 : (i - 1) + 4 = i + 3 := by ring
    rw [h1, h2, h3] at hcr
    have hc1 : d (i - 1) (i + 2) = c := by rw [show i + 2 = (i - 1) + 3 by ring]; exact hL4 (i - 1)
    have hc2 : d i (i + 3) = c := hL4 i
    have hc3 : d (i + 3) (i - 1) = c := by
      rw [hsym, show i + 3 = (i - 1) + 4 by ring]; exact hL4' (i - 1)
    rcases hval i (i + 2) (hne i 2 (by omega) (by omega)) with h | h | h
    · exact (hL3 i h).elim
    · exact h
    · linarith
  -- Lemma 6: every step-1 edge is a
  have hL6 : ∀ i : ZMod 7, d i (i + 1) = a := by
    intro i
    have hcr := (hq i 1 2 5 (by omega) (by omega) (by omega) (by omega)).1
    simp only [Nat.cast_one, Nat.cast_ofNat] at hcr
    have hb02 : d i (i + 2) = b := hL5 i
    have hc15 : d (i + 1) (i + 5) = c := by
      rw [show i + 5 = (i + 1) + 4 by ring]; exact hL4' (i + 1)
    have hc25 : d (i + 2) (i + 5) = c := by
      rw [show i + 5 = (i + 2) + 3 by ring]; exact hL4 (i + 2)
    rcases hval i (i + 1) (hne i 1 (by omega) (by omega)) with h | h | h
    · exact h
    · linarith
    · linarith
  exact ⟨hL6, hL5⟩

/- ## Case d = 3, Step 4: Concyclicity of an equilateral-chord 7-gon -/

private lemma circumcenter_exists (p0 p1 p2 : ℝ²) (hdet : det2 (p1 - p0) (p2 - p0) ≠ 0) :
    ∃ O : ℝ², dist p0 O = dist p1 O ∧ dist p1 O = dist p2 O := by
  let u := p1 - p0
  let v := p2 - p0
  let Δ := det2 u v
  have hΔ2 : Δ ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  have hgram : dot2 u u * dot2 v v - dot2 u v ^ 2 = Δ ^ 2 := by
    have := lagrange_r2 u v; dsimp [Δ]; linarith
  have hgram_ne : dot2 u u * dot2 v v - dot2 u v ^ 2 ≠ 0 := by rw [hgram]; exact hΔ2
  let s := (dot2 u u * dot2 v v - dot2 v v * dot2 u v) / (2 * Δ ^ 2)
  let t := (dot2 u u * dot2 v v - dot2 u u * dot2 u v) / (2 * Δ ^ 2)
  let O := p0 + s • u + t • v
  have hdot_u : 2 * dot2 (O - p0) u = dot2 u u := by
    have hsub : O - p0 = s • u + t • v := by dsimp [O]; abel
    rw [hsub]
    have hlin : dot2 (s • u + t • v) u = s * dot2 u u + t * dot2 u v := by
      simp only [dot2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hlin]
    dsimp [s, t]
    rw [← hgram]
    field_simp [hgram_ne]
    ring
  have hdot_v : 2 * dot2 (O - p0) v = dot2 v v := by
    have hsub : O - p0 = s • u + t • v := by dsimp [O]; abel
    rw [hsub]
    have hlin : dot2 (s • u + t • v) v = s * dot2 u v + t * dot2 v v := by
      simp only [dot2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hlin]
    dsimp [s, t]
    rw [← hgram]
    field_simp [hgram_ne]
    ring
  have h01 : dist p0 O ^ 2 = dist p1 O ^ 2 := by
    have : dist p1 O ^ 2 = dist p0 O ^ 2 + dot2 u u - 2 * dot2 (O - p0) u := by
      rw [dist_sq_r2, dist_sq_r2]
      simp only [u, dot2, PiLp.sub_apply]
      ring
    linarith
  have h02 : dist p0 O ^ 2 = dist p2 O ^ 2 := by
    have : dist p2 O ^ 2 = dist p0 O ^ 2 + dot2 v v - 2 * dot2 (O - p0) v := by
      rw [dist_sq_r2, dist_sq_r2]
      simp only [v, dot2, PiLp.sub_apply]
      ring
    linarith
  have e01 : dist p0 O = dist p1 O :=
    le_antisymm ((sq_le_sq₀ dist_nonneg dist_nonneg).mp h01.le)
      ((sq_le_sq₀ dist_nonneg dist_nonneg).mp h01.ge)
  have e02 : dist p0 O = dist p2 O :=
    le_antisymm ((sq_le_sq₀ dist_nonneg dist_nonneg).mp h02.le)
      ((sq_le_sq₀ dist_nonneg dist_nonneg).mp h02.ge)
  exact ⟨O, e01, e01.symm.trans e02⟩

private lemma concyclic_step (A B C D O : ℝ²) (a b : ℝ) (ha : 0 < a)
    (hAB : dist A B = a) (hBC : dist B C = a) (hCD : dist C D = a)
    (hAC : dist A C = b) (hBD : dist B D = b)
    (hdet1 : 0 < det2 (B - A) (C - A)) (hdet2 : 0 < det2 (C - B) (D - B))
    (hBO : dist B O = dist C O) :
    dist D O = dist A O := by
  let u := C - B
  have hu : dot2 u u = a ^ 2 := by
    rw [dot2_sub_norm_sq, dist_comm, hBC]
  have hu_pos : 0 < dot2 u u := by rw [hu]; positivity
  have hdot_A : 2 * dot2 (A - B) u = 2 * a ^ 2 - b ^ 2 := by
    have h1 : dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 - 2 * dot2 (A - B) u := by
      rw [dist_sq_r2, dist_sq_r2, dist_sq_r2]
      simp only [u, dot2, PiLp.sub_apply]
      ring
    rw [hAC, hAB, hBC] at h1
    linarith
  have hdot_D : 2 * dot2 (D - B) u = b ^ 2 := by
    have h1 : dist D C ^ 2 = dist D B ^ 2 + dist B C ^ 2 - 2 * dot2 (D - B) u := by
      rw [dist_sq_r2, dist_sq_r2, dist_sq_r2]
      simp only [u, dot2, PiLp.sub_apply]
      ring
    rw [dist_comm D C, hCD, dist_comm D B, hBD, hBC] at h1
    linarith
  have hdetA_pos : 0 < det2 u (A - B) := by
    have : det2 u (A - B) = det2 (B - A) (C - A) := by simp only [u, det2, PiLp.sub_apply]; ring
    linarith
  have hdetA_sq : det2 u (A - B) ^ 2 = a ^ 2 * b ^ 2 - b ^ 4 / 4 := by
    have hL := lagrange_r2 u (A - B)
    have hsym : dot2 u (A - B) = dot2 (A - B) u := by simp only [dot2]; ring
    rw [hsym, hu, dot2_sub_norm_sq, hAB] at hL
    nlinarith
  have hdetD_sq : det2 u (D - B) ^ 2 = a ^ 2 * b ^ 2 - b ^ 4 / 4 := by
    have hL := lagrange_r2 u (D - B)
    have hsym : dot2 u (D - B) = dot2 (D - B) u := by simp only [dot2]; ring
    rw [hsym, hu, dot2_sub_norm_sq, dist_comm, hBD] at hL
    nlinarith
  have hdet_eq : det2 u (D - B) = det2 u (A - B) := by
    nlinarith [hdetA_pos, hdet2]
  have hdet_DA : det2 u (D - A) = 0 := by
    simp only [det2, PiLp.sub_apply] at hdet_eq ⊢
    linarith
  have hO_perp : dot2 ((B + C) - (2 : ℝ) • O) u = 0 := by
    have h1 : dist B O ^ 2 = dist C O ^ 2 := by rw [hBO]
    rw [dist_sq_r2, dist_sq_r2] at h1
    simp only [u, dot2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linarith
  have hAD_perp : dot2 ((A + D) - (2 : ℝ) • O) u = 0 := by
    have hsum : dot2 ((A + D) - (B + C)) u = 0 := by
      simp only [u, dot2, PiLp.sub_apply, PiLp.add_apply] at hdot_A hdot_D hu ⊢
      linarith
    simp only [dot2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hsum hO_perp ⊢
    linarith
  have hDA_perp : dot2 (D - A) ((A + D) - (2 : ℝ) • O) = 0 := by
    have hmul : dot2 u u * dot2 (D - A) ((A + D) - (2 : ℝ) • O) =
        dot2 (D - A) u * dot2 ((A + D) - (2 : ℝ) • O) u +
        det2 u (D - A) * det2 u ((A + D) - (2 : ℝ) • O) := by
      simp only [dot2, det2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hAD_perp, hdet_DA] at hmul
    have h0 : dot2 u u * dot2 (D - A) ((A + D) - (2 : ℝ) • O) = 0 := by linarith
    exact (mul_eq_zero.mp h0).resolve_left hu_pos.ne'
  have hsq : dist D O ^ 2 = dist A O ^ 2 := by
    have : dist D O ^ 2 - dist A O ^ 2 = dot2 (D - A) ((A + D) - (2 : ℝ) • O) := by
      rw [dist_sq_r2, dist_sq_r2]
      simp only [dot2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    linarith
  exact le_antisymm ((sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq.le)
    ((sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq.ge)

/- ## Case d = 3: Putting it all together -/

private lemma card_le_seven_of_dist_le_three (A : Finset ℝ²)
    (hA : NonTrilinear (A : Set ℝ²)) (h : distinctDistances A ≤ 3) :
    A.card ≤ 7 := by
  by_contra! hgt
  obtain ⟨B, hBA, hB8⟩ := Finset.exists_subset_card_eq (show 8 ≤ A.card by omega)
  have hBnt : NonTrilinear (B : Set ℝ²) := Set.Triplewise.mono (Finset.coe_subset.mpr hBA) hA
  have hBd : distinctDistances B ≤ 3 := (Finset.card_le_card (distanceSet_mono hBA)).trans h
  have hBgt2 : 2 < distinctDistances B := by
    by_contra! hle
    have := card_le_five_of_dist_le_two B hle
    omega
  have hB3 : (distanceSet B).card = 3 := by
    change distinctDistances B = 3
    omega
  obtain ⟨d1, d2, d3, h12, h13, h23, hD_eq⟩ := Finset.card_eq_three.mp hB3
  -- Sort d1, d2, d3 into 0 < a < b < c
  have hsort : ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧ distanceSet B = {a, b, c} := by
    have hpos_mem : ∀ d ∈ distanceSet B, 0 < d := by
      intro d hd
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨_, _, hne⟩ := Finset.mem_offDiag.mp huv
      exact dist_pos.mpr hne
    have h3 : ∀ x y z : ℝ, x ≠ y → x ≠ z → y ≠ z →
        ∃ a b c : ℝ, a < b ∧ b < c ∧ ({x, y, z} : Finset ℝ) = {a, b, c} := by
      intro x y z hxy hxz hyz
      rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
        rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
        rcases lt_or_gt_of_ne hyz with h3 | h3
      · exact ⟨x, y, z, h1, h3, rfl⟩
      · exact ⟨x, z, y, h2, h3, by ext w; simp; tauto⟩
      · exact (not_lt_of_gt (h1.trans h3) h2).elim
      · exact ⟨z, x, y, h2, h1, by ext w; simp; tauto⟩
      · exact ⟨y, x, z, h1, h2, by ext w; simp; tauto⟩
      · exact (not_lt_of_gt (h3.trans h1) h2).elim
      · exact ⟨y, z, x, h3, h2, by ext w; simp; tauto⟩
      · exact ⟨z, y, x, h3, h1, by ext w; simp; tauto⟩
    obtain ⟨a, b, c, hab, hbc, heq⟩ := h3 d1 d2 d3 h12 h13 h23
    rw [heq] at hD_eq
    have ha_pos : 0 < a := hpos_mem a (by rw [hD_eq]; simp)
    exact ⟨a, b, c, ha_pos, hab, hbc, hD_eq⟩
  obtain ⟨a, b, c, ha, hab, hbc, hD_set⟩ := hsort
  have hD : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → dist u v = a ∨ dist u v = b ∨ dist u v = c := by
    intro u hu v hv huv
    have hm := dist_mem hu hv huv
    rw [hD_set] at hm
    simpa using hm
  have hVD7 := card_diameter_vertices_ge_seven hBnt hB8 ha hab hbc hD
  obtain ⟨S, hSVD, hS7⟩ := Finset.exists_subset_card_eq hVD7
  have hSB : S ⊆ B := hSVD.trans (Finset.filter_subset _ _)
  have hsup : ∀ x ∈ S, ∃ n : ℝ², ∀ y ∈ S, y ≠ x → dot2 (y - x) n < 0 := by
    intro x hx
    obtain ⟨hxB, w, hwB, hxw⟩ := Finset.mem_filter.mp (hSVD hx)
    refine ⟨x - w, ?_⟩
    intro y hy hyx
    have hyw_le : dist y w ≤ c := by
      by_cases hyw : y = w
      · rw [hyw, dist_self]; linarith
      · rcases hD y (hSB hy) w hwB hyw with h | h | h <;> linarith
    have hyw2 : dist y w ^ 2 ≤ dist x w ^ 2 := by
      rw [hxw]
      exact (sq_le_sq₀ dist_nonneg (by linarith)).mpr hyw_le
    have hexp : dist y w ^ 2 = dist y x ^ 2 + dist x w ^ 2 + 2 * dot2 (y - x) (x - w) := by
      rw [dist_sq_r2, dist_sq_r2, dist_sq_r2]
      simp only [dot2, PiLp.sub_apply]
      ring
    have hpos : 0 < dist y x ^ 2 := sq_pos_of_pos (dist_pos.mpr hyx)
    linarith
  obtain ⟨p0, hp_mem, hp_inj, hp_ccw⟩ := ccw_ordering_of_supported S hS7 hsup
  -- Lift p0 : Fin 7 → ℝ² to p : ZMod 7 → ℝ²
  let p : ZMod 7 → ℝ² := fun i => p0 ⟨i.val, ZMod.val_lt i⟩
  have hp_det_cyc : ∀ (i : ZMod 7) (s1 s2 : ℕ), 0 < s1 → s1 < s2 → s2 < 7 →
      0 < det2 (p (i + (s1 : ZMod 7)) - p i) (p (i + (s2 : ZMod 7)) - p i) := by
    intro i s1 s2 hs1 hs12 hs2
    have hlt_i : i.val < 7 := ZMod.val_lt i
    have hv1 : (i + (s1 : ZMod 7)).val = (i.val + s1) % 7 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
    have hv2 : (i + (s2 : ZMod 7)).val = (i.val + s2) % 7 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
    have hcyc1 : ∀ x y z : ℝ², det2 (y - x) (z - x) = det2 (z - y) (x - y) := by
      intro x y z; simp only [det2, PiLp.sub_apply]; ring
    have hcyc2 : ∀ x y z : ℝ², det2 (y - x) (z - x) = det2 (x - z) (y - z) := by
      intro x y z; simp only [det2, PiLp.sub_apply]; ring
    by_cases h2 : i.val + s2 < 7
    · exact hp_ccw ⟨i.val, hlt_i⟩ ⟨(i + s1).val, ZMod.val_lt _⟩ ⟨(i + s2).val, ZMod.val_lt _⟩
        (by simp [Fin.lt_def, hv1]; omega) (by simp [Fin.lt_def, hv1, hv2]; omega)
    · by_cases h1 : i.val + s1 < 7
      · rw [hcyc2]
        exact hp_ccw ⟨(i + s2).val, ZMod.val_lt _⟩ ⟨i.val, hlt_i⟩ ⟨(i + s1).val, ZMod.val_lt _⟩
          (by simp [Fin.lt_def, hv2]; omega) (by simp [Fin.lt_def, hv1]; omega)
      · rw [hcyc1]
        exact hp_ccw ⟨(i + s1).val, ZMod.val_lt _⟩ ⟨(i + s2).val, ZMod.val_lt _⟩ ⟨i.val, hlt_i⟩
          (by simp [Fin.lt_def, hv1, hv2]; omega) (by simp [Fin.lt_def, hv2]; omega)
  have hp_zmod_inj : Function.Injective p := by
    intro i j hij
    have hfin := hp_inj hij
    have hval : i.val = j.val := congrArg Fin.val hfin
    exact (ZMod.val_injective 7) hval
  have hp_cross : ∀ (i : ZMod 7) (s1 s2 s3 : ℕ), 0 < s1 → s1 < s2 → s2 < s3 → s3 < 7 →
      dist (p i) (p (i + s1)) + dist (p (i + s2)) (p (i + s3)) <
        dist (p i) (p (i + s2)) + dist (p (i + s1)) (p (i + s3)) ∧
      dist (p (i + s1)) (p (i + s2)) + dist (p (i + s3)) (p i) <
        dist (p i) (p (i + s2)) + dist (p (i + s1)) (p (i + s3)) := by
    intro i s1 s2 s3 hs1 hs12 hs23 hs3
    have hd1 := hp_det_cyc i s2 s3 (by omega) hs23 hs3
    have hd2 := hp_det_cyc i s1 s2 hs1 hs12 (by omega)
    have hd3 := hp_det_cyc i s1 s3 hs1 (by omega) hs3
    have hd4 : 0 < det2 (p (i + s2) - p (i + s1)) (p (i + s3) - p (i + s1)) := by
      have h1 := hp_det_cyc (i + s1) (s2 - s1) (s3 - s1) (by omega) (by omega) (by omega)
      have he1 : (i + (s1 : ZMod 7)) + ((s2 - s1 : ℕ) : ZMod 7) = i + (s2 : ZMod 7) := by
        rw [add_assoc]; congr 1; rw [← Nat.cast_add, Nat.add_sub_of_le hs12.le]
      have he2 : (i + (s1 : ZMod 7)) + ((s3 - s1 : ℕ) : ZMod 7) = i + (s3 : ZMod 7) := by
        rw [add_assoc]; congr 1; rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
      rwa [he1, he2] at h1
    exact crossing_diag_gt (p i) (p (i + s1)) (p (i + s2)) (p (i + s3)) hd1 hd2 hd3 hd4
  obtain ⟨hstep1, hstep2⟩ := convex_seven_unique (fun i j => dist (p i) (p j)) a b c hab hbc
    (fun i j => dist_comm _ _)
    (fun i j hij => hD (p i) (hSB (hp_mem _)) (p j) (hSB (hp_mem _)) (hp_zmod_inj.ne hij))
    hp_cross
  have hdet012 : 0 < det2 (p 1 - p 0) (p 2 - p 0) := by
    simpa using hp_det_cyc 0 1 2 (by omega) (by omega) (by omega)
  obtain ⟨O, hO01, hO12⟩ := circumcenter_exists (p 0) (p 1) (p 2) hdet012.ne'
  have hstep_O : ∀ i : ZMod 7, dist (p i) O = dist (p (i + 1)) O →
      dist (p (i + 1)) O = dist (p (i + 2)) O →
      dist (p (i + 3)) O = dist (p i) O := by
    intro i _ h12O
    have hdetA : 0 < det2 (p (i + 1) - p i) (p (i + 2) - p i) := by
      simpa using hp_det_cyc i 1 2 (by omega) (by omega) (by omega)
    have hdetB : 0 < det2 (p (i + 2) - p (i + 1)) (p (i + 3) - p (i + 1)) := by
      have h := hp_det_cyc (i + 1) 1 2 (by omega) (by omega) (by omega)
      simp only [Nat.cast_one, Nat.cast_ofNat] at h
      rwa [show (i + 1) + 1 = i + 2 by ring, show (i + 1) + 2 = i + 3 by ring] at h
    exact concyclic_step (p i) (p (i + 1)) (p (i + 2)) (p (i + 3)) O a b ha
      (hstep1 i)
      (by rw [show i + 2 = (i + 1) + 1 by ring]; exact hstep1 (i + 1))
      (by rw [show i + 3 = (i + 2) + 1 by ring]; exact hstep1 (i + 2))
      (hstep2 i)
      (by rw [show i + 3 = (i + 1) + 2 by ring]; exact hstep2 (i + 1))
      hdetA hdetB h12O
  let R := dist (p 0) O
  have hR0 : dist (p 0) O = R := rfl
  have hR1 : dist (p 1) O = R := hO01.symm
  have hR2 : dist (p 2) O = R := hO12.symm.trans hR1
  have hR3 : dist (p 3) O = R := by
    have := hstep_O 0
    rw [show (0 : ZMod 7) + 1 = 1 by decide, show (0 : ZMod 7) + 2 = 2 by decide,
      show (0 : ZMod 7) + 3 = 3 by decide] at this
    exact (this (hR0.trans hR1.symm) (hR1.trans hR2.symm)).trans hR0
  have hR4 : dist (p 4) O = R := by
    have := hstep_O 1
    rw [show (1 : ZMod 7) + 1 = 2 by decide, show (1 : ZMod 7) + 2 = 3 by decide,
      show (1 : ZMod 7) + 3 = 4 by decide] at this
    exact (this (hR1.trans hR2.symm) (hR2.trans hR3.symm)).trans hR1
  have hR5 : dist (p 5) O = R := by
    have := hstep_O 2
    rw [show (2 : ZMod 7) + 1 = 3 by decide, show (2 : ZMod 7) + 2 = 4 by decide,
      show (2 : ZMod 7) + 3 = 5 by decide] at this
    exact (this (hR2.trans hR3.symm) (hR3.trans hR4.symm)).trans hR2
  have hR6 : dist (p 6) O = R := by
    have := hstep_O 3
    rw [show (3 : ZMod 7) + 1 = 4 by decide, show (3 : ZMod 7) + 2 = 5 by decide,
      show (3 : ZMod 7) + 3 = 6 by decide] at this
    exact (this (hR3.trans hR4.symm) (hR4.trans hR5.symm)).trans hR3
  have hS_on_circle : ∀ x ∈ S, dist x O = R := by
    have himg : Finset.univ.image p = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact hp_mem _
      · rw [Finset.card_image_of_injective _ hp_zmod_inj, Finset.card_univ, ZMod.card, hS7]
    intro x hx
    rw [← himg] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact hR0
    · exact hR1
    · exact hR2
    · exact hR3
    · exact hR4
    · exact hR5
    · exact hR6
  have hdiff1 : (B \ S).card = 1 := by
    have := Finset.card_sdiff_add_card_inter B S
    rw [Finset.inter_eq_right.mpr hSB, hB8, hS7] at this
    omega
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hdiff1
  have hBerase : B.erase q = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxq, hxB⟩ := Finset.mem_erase.mp hx
      by_contra hxS
      have hm : x ∈ B \ S := Finset.mem_sdiff.mpr ⟨hxB, hxS⟩
      rw [hq_eq, Finset.mem_singleton] at hm
      exact hxq hm
    · intro hx
      apply Finset.mem_erase.mpr
      refine ⟨?_, hSB hx⟩
      intro hxq
      have hqmem : q ∈ B \ S := hq_eq ▸ Finset.mem_singleton_self q
      exact (Finset.mem_sdiff.mp hqmem).2 (hxq ▸ hx)
  have hbound := all_but_one_concyclic B O R hBnt q (by rw [hBerase]; exact hS_on_circle)
  omega

end OMA.Erdos1082_H1_Proof

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1.H1 := by
  intro A hA hd
  have h0 : distinctDistances A = 0 → A.card / 2 ≤ distinctDistances A := fun h => by
    have := OMA.Erdos1082_H1_Proof.card_le_one_of_dist_eq_zero A h
    omega
  have h1 : distinctDistances A = 1 → A.card / 2 ≤ distinctDistances A := fun h => by
    have := OMA.Erdos1082_H1_Proof.card_le_three_of_dist_le_one A (by omega)
    omega
  have h2 : distinctDistances A = 2 → A.card / 2 ≤ distinctDistances A := fun h => by
    have := OMA.Erdos1082_H1_Proof.card_le_five_of_dist_le_two A (by omega)
    omega
  have h3 : distinctDistances A = 3 → A.card / 2 ≤ distinctDistances A := fun h => by
    have := OMA.Erdos1082_H1_Proof.card_le_seven_of_dist_le_three A hA (by omega)
    omega
  omega
