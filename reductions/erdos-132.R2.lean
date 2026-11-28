import OMAStatements.S_erdos_132

-- Reduction erdos-132.R2 of Erdős Problem 132
-- Credit: @sanchan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This reduction strictly strengthens erdos-132.R1 by proving in Lean:
--   1. The 2-point circle intersection bound and Erdős's 1946 bound |A| - 2 <= 2 |D(A)|^2;
--   2. An algebraic three-neighbor lemma yielding a uniform top-k degeneracy bound
--      pairMultiplicity S d <= (4m + 1) * |S| for any distance d with m strictly larger
--      distances (including exact Hopf-Pannwitz pairMultiplicity S d_1 <= |S| at m = 0);
--   3. The onion-peeling variance lemma showing every pair realizing one of the k largest
--      distances lies in the first k extreme-point convex layers A \ peel^[k] A.
-- This discharges all configurations with |A \ peel^[2] A| <= |A| / 5 in Part 1 and all
-- configurations with |A \ peel^[k] A| <= |A| / (4k - 3) in Part 2 (including all grids,
-- lattice balls, and sublinear-layer sets).

namespace OMA.R_erdos_132_R2

open Filter
open scoped Classical Topology
open OMA.S_erdos_132 (pairMultiplicity rareDistances minRareCount)

-- Part 1 restricted to sets with at most |A|/2 distinct distances and > |A|/5 points in the
-- first two convex layers.
def H1 : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ A.card / 2 →
    A.card < 5 * (A \ (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
      S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[2] A).card →
    2 ≤ (rareDistances A).card

-- Part 2 restricted to sets with |D(A)| + 2 <= |A|/2 + k and > |A| / (4k - 3) points in the
-- first k convex layers (forcing a strictly convex layer of linear size).
def H2 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card + 2 ≤ A.card / 2 + k →
    A.card < (4 * k - 3) * (A \ (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
      S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[k] A).card →
    k ≤ (rareDistances A).card

lemma dist_sq_coords (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x.ofLp 0 - y.ofLp 0) ^ 2 + (x.ofLp 1 - y.ofLp 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma pt_eq_of_coords {x y : EuclideanSpace ℝ (Fin 2)}
    (h0 : x.ofLp 0 = y.ofLp 0) (h1 : x.ofLp 1 = y.ofLp 1) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma multiplicity_pos {A : Finset (EuclideanSpace ℝ (Fin 2))} {d : ℝ}
    (hd : d ∈ A.offDiag.image (fun p => dist p.1 p.2)) :
    1 ≤ pairMultiplicity A d := by
  obtain ⟨⟨x, y⟩, hxy, hdist⟩ := Finset.mem_image.mp hd
  have hm := Finset.mem_offDiag.mp hxy
  have hyx : (y, x) ∈ A.offDiag :=
    Finset.mem_offDiag.mpr ⟨hm.2.1, hm.1, hm.2.2.symm⟩
  have hdistinct : (x, y) ≠ (y, x) := fun h => hm.2.2 (congrArg Prod.fst h)
  let F := A.offDiag.filter (fun p => dist p.1 p.2 = d)
  have hfirst : (x, y) ∈ F := Finset.mem_filter.mpr ⟨hxy, hdist⟩
  have hsecond : (y, x) ∈ F :=
    Finset.mem_filter.mpr ⟨hyx, (dist_comm y x).trans hdist⟩
  have hcard : 1 < F.card := Finset.one_lt_card.mpr ⟨_, hfirst, _, hsecond, hdistinct⟩
  change 1 ≤ F.card / 2
  omega

lemma dist_pos_of_mem_image {A : Finset (EuclideanSpace ℝ (Fin 2))} {d : ℝ}
    (hd : d ∈ A.offDiag.image (fun p => dist p.1 p.2)) : 0 < d := by
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
  exact dist_pos.mpr (Finset.mem_offDiag.mp hxy).2.2

lemma distinct_lt_half_add_rare (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hA : 2 ≤ A.card) :
    (A.offDiag.image (fun p => dist p.1 p.2)).card < A.card / 2 + (rareDistances A).card := by
  let f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun p => dist p.1 p.2
  let D := A.offDiag.image f
  let B := D \ rareDistances A
  have hrare : rareDistances A ⊆ D := Finset.filter_subset _ _
  have hheavy (d : ℝ) (hd : d ∈ B) :
      2 * (A.card + 1) ≤ (A.offDiag.filter (fun p => f p = d)).card := by
    have hd' := Finset.mem_sdiff.mp hd
    have hpos := multiplicity_pos hd'.1
    have hlarge : A.card < pairMultiplicity A d := by
      by_contra! hsmall
      exact hd'.2 (Finset.mem_filter.mpr ⟨hd'.1, hpos, hsmall⟩)
    change A.card < (A.offDiag.filter (fun p => f p = d)).card / 2 at hlarge
    omega
  have hpairs : B.card * (2 * (A.card + 1)) ≤ A.card * (A.card - 1) := by
    calc
      B.card * (2 * (A.card + 1)) = ∑ _d ∈ B, 2 * (A.card + 1) := by simp
      _ ≤ ∑ d ∈ B, (A.offDiag.filter (fun p => f p = d)).card :=
        Finset.sum_le_sum fun d hd => hheavy d hd
      _ = (A.offDiag.filter (fun p => f p ∈ B)).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ A.offDiag.card := Finset.card_filter_le _ _
      _ = A.card * (A.card - 1) := by
        simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]
  have hB : B.card < A.card / 2 := by
    by_contra! hlarge
    have hwidth : A.card - 1 ≤ B.card * 2 := by omega
    have hlt : A.card * (A.card - 1) < (A.card - 1) * (A.card + 1) := by
      rw [mul_comm (A.card - 1)]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by omega)
    have hle := Nat.mul_le_mul_right (A.card + 1) hwidth
    rw [Nat.mul_assoc] at hle
    exact (not_le_of_gt hlt) (hle.trans hpairs)
  have hsplit : B.card + (rareDistances A).card = D.card :=
    Finset.card_sdiff_add_card_eq_card hrare
  change D.card < A.card / 2 + _
  omega

lemma card_circle_inter_le_two (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) (r₁ r₂ : ℝ) :
    (S.filter (fun x => dist x p = r₁ ∧ dist x q = r₂)).card ≤ 2 := by
  by_contra hgt
  have h2lt : 2 < (S.filter (fun x => dist x p = r₁ ∧ dist x q = r₂)).card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp h2lt
  have hxp := (Finset.mem_filter.mp hx).2.1
  have hxq := (Finset.mem_filter.mp hx).2.2
  have hyp := (Finset.mem_filter.mp hy).2.1
  have hyq := (Finset.mem_filter.mp hy).2.2
  have hzp := (Finset.mem_filter.mp hz).2.1
  have hzq := (Finset.mem_filter.mp hz).2.2
  have hxp2 : (x.ofLp 0 - p.ofLp 0) ^ 2 + (x.ofLp 1 - p.ofLp 1) ^ 2 = r₁ ^ 2 := by
    rw [← dist_sq_coords, hxp]
  have hxq2 : (x.ofLp 0 - q.ofLp 0) ^ 2 + (x.ofLp 1 - q.ofLp 1) ^ 2 = r₂ ^ 2 := by
    rw [← dist_sq_coords, hxq]
  have hyp2 : (y.ofLp 0 - p.ofLp 0) ^ 2 + (y.ofLp 1 - p.ofLp 1) ^ 2 = r₁ ^ 2 := by
    rw [← dist_sq_coords, hyp]
  have hyq2 : (y.ofLp 0 - q.ofLp 0) ^ 2 + (y.ofLp 1 - q.ofLp 1) ^ 2 = r₂ ^ 2 := by
    rw [← dist_sq_coords, hyq]
  have hzp2 : (z.ofLp 0 - p.ofLp 0) ^ 2 + (z.ofLp 1 - p.ofLp 1) ^ 2 = r₁ ^ 2 := by
    rw [← dist_sq_coords, hzp]
  have hzq2 : (z.ofLp 0 - q.ofLp 0) ^ 2 + (z.ofLp 1 - q.ofLp 1) ^ 2 = r₂ ^ 2 := by
    rw [← dist_sq_coords, hzq]
  set dx := q.ofLp 0 - p.ofLp 0
  set dy := q.ofLp 1 - p.ofLp 1
  set a := y.ofLp 0 - x.ofLp 0
  set b := y.ofLp 1 - x.ofLp 1
  set c := z.ofLp 0 - x.ofLp 0
  set d := z.ofLp 1 - x.ofLp 1
  have hdpq : 0 < dx ^ 2 + dy ^ 2 := by
    have hne : dx ≠ 0 ∨ dy ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hpq (pt_eq_of_coords (by linarith only [h0.1]) (by linarith only [h0.2]))
    rcases hne with h0 | h1 <;> positivity
  have hab : 0 < a ^ 2 + b ^ 2 := by
    have hne : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hxy (pt_eq_of_coords (by linarith only [h0.1]) (by linarith only [h0.2]))
    rcases hne with h0 | h1 <;> positivity
  have hcd : 0 < c ^ 2 + d ^ 2 := by
    have hne : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hxz (pt_eq_of_coords (by linarith only [h0.1]) (by linarith only [h0.2]))
    rcases hne with h0 | h1 <;> positivity
  have horth1 : dx * a + dy * b = 0 := by
    linear_combination (hyp2 - hxp2 - hyq2 + hxq2) / 2
  have horth2 : dx * c + dy * d = 0 := by
    linear_combination (hzp2 - hxp2 - hzq2 + hxq2) / 2
  have hdet : a * d - b * c = 0 := by
    have h1 : dx * (a * d - b * c) = 0 := by linear_combination d * horth1 - b * horth2
    have h2 : dy * (a * d - b * c) = 0 := by linear_combination -c * horth1 + a * horth2
    have h3 : (dx ^ 2 + dy ^ 2) * (a * d - b * c) = 0 := by linear_combination dx * h1 + dy * h2
    exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hdpq)
  have hcirc1 : a ^ 2 + b ^ 2 + 2 * (x.ofLp 0 - p.ofLp 0) * a + 2 * (x.ofLp 1 - p.ofLp 1) * b = 0 := by
    linear_combination hyp2 - hxp2
  have hcirc2 : c ^ 2 + d ^ 2 + 2 * (x.ofLp 0 - p.ofLp 0) * c + 2 * (x.ofLp 1 - p.ofLp 1) * d = 0 := by
    linear_combination hzp2 - hxp2
  have heqA : (a - c) * (a * c + b * d) = 0 := by
    linear_combination c * hcirc1 - a * hcirc2 +
      (2 * (x.ofLp 1 - p.ofLp 1) + b + d) * hdet
  have heqB : (b - d) * (a * c + b * d) = 0 := by
    linear_combination d * hcirc1 - b * hcirc2 -
      (2 * (x.ofLp 0 - p.ofLp 0) + a + c) * hdet
  have hdot_sq : (a * c + b * d) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    linear_combination -(a * d - b * c) * hdet
  have hdot_ne : a * c + b * d ≠ 0 := by
    intro h0
    have hpos : 0 < (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := mul_pos hab hcd
    rw [h0, zero_pow (by decide : 2 ≠ 0)] at hdot_sq
    linarith only [hdot_sq, hpos]
  have hac : a = c := sub_eq_zero.mp ((mul_eq_zero.mp heqA).resolve_right hdot_ne)
  have hbd : b = d := sub_eq_zero.mp ((mul_eq_zero.mp heqB).resolve_right hdot_ne)
  exact hyz (pt_eq_of_coords (by linarith only [hac]) (by linarith only [hbd]))

lemma card_sub_two_le_two_mul_sq (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hA : 2 ≤ A.card) :
    A.card - 2 ≤ 2 * (A.offDiag.image (fun p => dist p.1 p.2)).card ^ 2 := by
  have h1lt : 1 < A.card := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1lt
  let D := A.offDiag.image (fun r => dist r.1 r.2)
  let R := (A.erase p).erase q
  let g : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun x => (dist x p, dist x q)
  have hRcard : R.card = A.card - 2 := by
    have hq' : q ∈ A.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
    rw [Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hp]
    omega
  have hImgSub : R.image g ⊆ D ×ˢ D := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
    have hx' := Finset.mem_erase.mp (Finset.mem_erase.mp hx).2
    have hxp : x ≠ p := hx'.1
    have hxA : x ∈ A := hx'.2
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(x, p), Finset.mem_offDiag.mpr ⟨hxA, hp, hxp⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(x, q), Finset.mem_offDiag.mpr ⟨hxA, hq, hxq⟩, rfl⟩
  have hFiber : ∀ b ∈ R.image g, (R.filter (fun x => g x = b)).card ≤ 2 := by
    intro ⟨r₁, r₂⟩ _
    have hsub : R.filter (fun x => g x = (r₁, r₂)) ⊆
        R.filter (fun x => dist x p = r₁ ∧ dist x q = r₂) := by
      intro x hx
      have hm := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hm.1, Prod.mk.inj hm.2⟩
    exact (Finset.card_le_card hsub).trans (card_circle_inter_le_two R p q hpq r₁ r₂)
  have hstep := Finset.card_le_mul_card_image R 2 hFiber
  have himg : (R.image g).card ≤ D.card ^ 2 := by
    calc (R.image g).card ≤ (D ×ˢ D).card := Finset.card_le_card hImgSub
      _ = D.card * D.card := Finset.card_product D D
      _ = D.card ^ 2 := by ring
  rw [hRcard] at hstep
  exact hstep.trans (Nat.mul_le_mul_left 2 himg)

lemma three_neighbor_gt {v a₁ a₂ a₃ w : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r) (ha₁ : dist a₁ v = r) (ha₂ : dist a₂ v = r) (ha₃ : dist a₃ v = r)
    (hw : dist w a₂ = r) (hwv : w ≠ v)
    (hdet₁ : (a₂.ofLp 0 - v.ofLp 0) * (a₁.ofLp 1 - v.ofLp 1) -
      (a₂.ofLp 1 - v.ofLp 1) * (a₁.ofLp 0 - v.ofLp 0) < 0)
    (hdet₃ : 0 < (a₂.ofLp 0 - v.ofLp 0) * (a₃.ofLp 1 - v.ofLp 1) -
      (a₂.ofLp 1 - v.ofLp 1) * (a₃.ofLp 0 - v.ofLp 0)) :
    r < dist w a₁ ∨ r < dist w a₃ := by
  set e0 := a₂.ofLp 0 - v.ofLp 0
  set e1 := a₂.ofLp 1 - v.ofLp 1
  set z10 := a₁.ofLp 0 - v.ofLp 0
  set z11 := a₁.ofLp 1 - v.ofLp 1
  set z30 := a₃.ofLp 0 - v.ofLp 0
  set z31 := a₃.ofLp 1 - v.ofLp 1
  set u0 := w.ofLp 0 - a₂.ofLp 0
  set u1 := w.ofLp 1 - a₂.ofLp 1
  have he2 : e0 ^ 2 + e1 ^ 2 = r ^ 2 := by rw [← dist_sq_coords, ha₂]
  have hz12 : z10 ^ 2 + z11 ^ 2 = r ^ 2 := by rw [← dist_sq_coords, ha₁]
  have hz32 : z30 ^ 2 + z31 ^ 2 = r ^ 2 := by rw [← dist_sq_coords, ha₃]
  have hu2 : u0 ^ 2 + u1 ^ 2 = r ^ 2 := by rw [← dist_sq_coords, hw]
  have hwv_pos : 0 < (e0 + u0) ^ 2 + (e1 + u1) ^ 2 := by
    have h : (e0 + u0) ^ 2 + (e1 + u1) ^ 2 = dist w v ^ 2 := by
      rw [dist_sq_coords]; ring
    rw [h]
    exact sq_pos_of_pos (dist_pos.mpr hwv)
  have hru_pos : 0 < r ^ 2 + (e0 * u0 + e1 * u1) := by
    have hexp : (e0 + u0) ^ 2 + (e1 + u1) ^ 2 = 2 * (r ^ 2 + (e0 * u0 + e1 * u1)) := by
      linear_combination he2 + hu2
    linarith only [hwv_pos, hexp]
  have hz1_pos : 0 < r ^ 2 - (e0 * z10 + e1 * z11) := by
    have hexp : (e0 - z10) ^ 2 + (e1 - z11) ^ 2 = 2 * (r ^ 2 - (e0 * z10 + e1 * z11)) := by
      linear_combination he2 + hz12
    have hne : 0 < (e0 - z10) ^ 2 + (e1 - z11) ^ 2 := by
      have h0 : ¬ (e0 = z10 ∧ e1 = z11) := by
        rintro ⟨hx, hy⟩
        have hzero : e0 * z11 - e1 * z10 = 0 := by rw [hx, hy]; ring
        linarith only [hdet₁, hzero]
      by_cases hx : e0 = z10
      · have hy : e1 ≠ z11 := fun h => h0 ⟨hx, h⟩
        have hpos : 0 < (e1 - z11) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
        have hnn : 0 ≤ (e0 - z10) ^ 2 := sq_nonneg _
        linarith only [hpos, hnn]
      · have hpos : 0 < (e0 - z10) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
        have hnn : 0 ≤ (e1 - z11) ^ 2 := sq_nonneg _
        linarith only [hpos, hnn]
    linarith only [hne, hexp]
  have hz3_pos : 0 < r ^ 2 - (e0 * z30 + e1 * z31) := by
    have hexp : (e0 - z30) ^ 2 + (e1 - z31) ^ 2 = 2 * (r ^ 2 - (e0 * z30 + e1 * z31)) := by
      linear_combination he2 + hz32
    have hne : 0 < (e0 - z30) ^ 2 + (e1 - z31) ^ 2 := by
      have h0 : ¬ (e0 = z30 ∧ e1 = z31) := by
        rintro ⟨hx, hy⟩
        have hzero : e0 * z31 - e1 * z30 = 0 := by rw [hx, hy]; ring
        linarith only [hdet₃, hzero]
      by_cases hx : e0 = z30
      · have hy : e1 ≠ z31 := fun h => h0 ⟨hx, h⟩
        have hpos : 0 < (e1 - z31) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
        have hnn : 0 ≤ (e0 - z30) ^ 2 := sq_nonneg _
        linarith only [hpos, hnn]
      · have hpos : 0 < (e0 - z30) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
        have hnn : 0 ≤ (e1 - z31) ^ 2 := sq_nonneg _
        linarith only [hpos, hnn]
    linarith only [hne, hexp]
  have hid1 : r ^ 2 * (dist w a₁ ^ 2 - r ^ 2) =
      2 * (r ^ 2 + (e0 * u0 + e1 * u1)) * (r ^ 2 - (e0 * z10 + e1 * z11)) -
      2 * (e0 * z11 - e1 * z10) * (e0 * u1 - e1 * u0) := by
    have hdw1 : dist w a₁ ^ 2 = (e0 - z10 + u0) ^ 2 + (e1 - z11 + u1) ^ 2 := by
      rw [dist_sq_coords]; ring
    rw [hdw1]
    linear_combination
      (r ^ 2 + 2 * (z10 * u0 + z11 * u1)) * he2 + r ^ 2 * hz12 + r ^ 2 * hu2
  have hid3 : r ^ 2 * (dist w a₃ ^ 2 - r ^ 2) =
      2 * (r ^ 2 + (e0 * u0 + e1 * u1)) * (r ^ 2 - (e0 * z30 + e1 * z31)) -
      2 * (e0 * z31 - e1 * z30) * (e0 * u1 - e1 * u0) := by
    have hdw3 : dist w a₃ ^ 2 = (e0 - z30 + u0) ^ 2 + (e1 - z31 + u1) ^ 2 := by
      rw [dist_sq_coords]; ring
    rw [hdw3]
    linear_combination
      (r ^ 2 + 2 * (z30 * u0 + z31 * u1)) * he2 + r ^ 2 * hz32 + r ^ 2 * hu2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  by_cases hsign : 0 ≤ e0 * u1 - e1 * u0
  · left
    have hgt : 0 < r ^ 2 * (dist w a₁ ^ 2 - r ^ 2) := by
      rw [hid1]
      have hterm1 : 0 < 2 * (r ^ 2 + (e0 * u0 + e1 * u1)) * (r ^ 2 - (e0 * z10 + e1 * z11)) := by
        positivity
      have hterm2 : 0 ≤ -(2 * (e0 * z11 - e1 * z10) * (e0 * u1 - e1 * u0)) := by
        nlinarith only [hdet₁, hsign]
      linarith only [hterm1, hterm2]
    have hsq : r ^ 2 < dist w a₁ ^ 2 := by nlinarith only [hr2, hgt]
    nlinarith only [hr, hsq, dist_nonneg (x := w) (y := a₁)]
  · right
    have hgt : 0 < r ^ 2 * (dist w a₃ ^ 2 - r ^ 2) := by
      rw [hid3]
      have hterm1 : 0 < 2 * (r ^ 2 + (e0 * u0 + e1 * u1)) * (r ^ 2 - (e0 * z30 + e1 * z31)) := by
        positivity
      have hterm2 : 0 ≤ -(2 * (e0 * z31 - e1 * z30) * (e0 * u1 - e1 * u0)) := by
        nlinarith only [hdet₃, hsign]
      linarith only [hterm1, hterm2]
    have hsq : r ^ 2 < dist w a₃ ^ 2 := by nlinarith only [hr2, hgt]
    nlinarith only [hr, hsq, dist_nonneg (x := w) (y := a₃)]

lemma det_pos_of_circle_order {c2 s2 c3 s3 R : ℝ}
    (hcs2 : c2 ^ 2 + s2 ^ 2 = R) (hcs3 : c3 ^ 2 + s3 ^ 2 = R)
    (hc3_lt : c3 < c2) (h2pos : 0 < s2) (h3pos : 0 < s3) :
    0 < c2 * s3 - s2 * c3 := by
  by_cases hc2 : 0 ≤ c2
  · by_cases hc3 : 0 ≤ c3
    · have hs_lt : s2 < s3 := by nlinarith
      nlinarith
    · nlinarith
  · have hs_lt : s3 < s2 := by nlinarith
    nlinarith

lemma exists_sandwich_of_three_on_circle {v : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r) (T : Finset (EuclideanSpace ℝ (Fin 2))) (hT : 3 ≤ T.card)
    (hdist : ∀ a ∈ T, dist a v = r) :
    ∃ a₁ ∈ T, ∃ a₂ ∈ T, ∃ a₃ ∈ T,
      (a₂.ofLp 0 - v.ofLp 0) * (a₁.ofLp 1 - v.ofLp 1) -
        (a₂.ofLp 1 - v.ofLp 1) * (a₁.ofLp 0 - v.ofLp 0) < 0 ∧
      0 < (a₂.ofLp 0 - v.ofLp 0) * (a₃.ofLp 1 - v.ofLp 1) -
        (a₂.ofLp 1 - v.ofLp 1) * (a₃.ofLp 0 - v.ofLp 0) := by
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a₀, ha₀⟩ := hTne
  set e0 := a₀.ofLp 0 - v.ofLp 0
  set e1 := a₀.ofLp 1 - v.ofLp 1
  have he2 : e0 ^ 2 + e1 ^ 2 = r ^ 2 := by rw [← dist_sq_coords, hdist a₀ ha₀]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hcol : ∀ x ∈ T,
      e0 * (x.ofLp 1 - v.ofLp 1) - e1 * (x.ofLp 0 - v.ofLp 0) = 0 →
      x = a₀ ∨ (x.ofLp 0 - v.ofLp 0 = -e0 ∧ x.ofLp 1 - v.ofLp 1 = -e1) := by
    intro x hx hdet
    have hx2 : (x.ofLp 0 - v.ofLp 0) ^ 2 + (x.ofLp 1 - v.ofLp 1) ^ 2 = r ^ 2 := by
      rw [← dist_sq_coords, hdist x hx]
    set x0 := x.ofLp 0 - v.ofLp 0
    set x1 := x.ofLp 1 - v.ofLp 1
    have hdot2 : (e0 * x0 + e1 * x1) ^ 2 = (r ^ 2) ^ 2 := by
      calc (e0 * x0 + e1 * x1) ^ 2
          = (e0 * x0 + e1 * x1) ^ 2 + (e0 * x1 - e1 * x0) ^ 2 := by rw [hdet]; ring
        _ = (e0 ^ 2 + e1 ^ 2) * (x0 ^ 2 + x1 ^ 2) := by ring
        _ = (r ^ 2) ^ 2 := by rw [he2, hx2]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdot2 with hpos | hneg
    · left
      have hsq : (x0 - e0) ^ 2 + (x1 - e1) ^ 2 = 0 := by
        linear_combination hx2 + he2 - 2 * hpos
      have h0 : x0 - e0 = 0 := by nlinarith only [hsq]
      have h1 : x1 - e1 = 0 := by nlinarith only [hsq]
      exact pt_eq_of_coords (by linarith only [h0]) (by linarith only [h1])
    · right
      have hsq : (x0 + e0) ^ 2 + (x1 + e1) ^ 2 = 0 := by
        linear_combination hx2 + he2 + 2 * hneg
      have h0 : x0 + e0 = 0 := by nlinarith only [hsq]
      have h1 : x1 + e1 = 0 := by nlinarith only [hsq]
      exact ⟨by linarith only [h0], by linarith only [h1]⟩
  by_cases hant : ∃ b ∈ T, b.ofLp 0 - v.ofLp 0 = -e0 ∧ b.ofLp 1 - v.ofLp 1 = -e1
  · obtain ⟨b, hb, hb0, hb1⟩ := hant
    have hba0 : b ≠ a₀ := by
      intro heq
      have h0 : e0 = -e0 := by rw [← hb0, heq]
      have h1 : e1 = -e1 := by rw [← hb1, heq]
      have he0z : e0 = 0 := by linarith only [h0]
      have he1z : e1 = 0 := by linarith only [h1]
      rw [he0z, he1z] at he2
      nlinarith only [he2, hr2]
    have hrem : ((T.erase a₀).erase b).Nonempty := by
      rw [← Finset.card_pos]
      have hb' : b ∈ T.erase a₀ := Finset.mem_erase.mpr ⟨hba0, hb⟩
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha₀]
      omega
    obtain ⟨a₂, ha₂'⟩ := hrem
    have ha₂b : a₂ ≠ b := (Finset.mem_erase.mp ha₂').1
    have ha₂0 : a₂ ≠ a₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp ha₂').2).1
    have ha₂ : a₂ ∈ T := (Finset.mem_erase.mp (Finset.mem_erase.mp ha₂').2).2
    have hne : (a₂.ofLp 0 - v.ofLp 0) * e1 - (a₂.ofLp 1 - v.ofLp 1) * e0 ≠ 0 := by
      intro hz
      rcases hcol a₂ ha₂ (by linarith only [hz]) with rfl | ⟨h0, h1⟩
      · exact ha₂0 rfl
      · exact ha₂b (pt_eq_of_coords (by linarith only [h0, hb0]) (by linarith only [h1, hb1]))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨a₀, ha₀, a₂, ha₂, b, hb, hlt, ?_⟩
      rw [hb0, hb1]; linarith only [hlt]
    · refine ⟨b, hb, a₂, ha₂, a₀, ha₀, ?_, hgt⟩
      rw [hb0, hb1]; linarith only [hgt]
  · push Not at hant
    let T' := T.erase a₀
    have hT'card : 2 ≤ T'.card := by
      rw [Finset.card_erase_of_mem ha₀]; omega
    have hdet_ne : ∀ x ∈ T', e0 * (x.ofLp 1 - v.ofLp 1) - e1 * (x.ofLp 0 - v.ofLp 0) ≠ 0 := by
      intro x hx hz
      have hxm := Finset.mem_erase.mp hx
      rcases hcol x hxm.2 hz with rfl | ⟨h0, h1⟩
      · exact hxm.1 rfl
      · exact hant x hxm.2 h0 h1
    by_cases hboth :
        (∃ a₁ ∈ T', e0 * (a₁.ofLp 1 - v.ofLp 1) - e1 * (a₁.ofLp 0 - v.ofLp 0) < 0) ∧
        (∃ a₃ ∈ T', 0 < e0 * (a₃.ofLp 1 - v.ofLp 1) - e1 * (a₃.ofLp 0 - v.ofLp 0))
    · obtain ⟨⟨a₁, ha₁, h1⟩, ⟨a₃, ha₃, h3⟩⟩ := hboth
      exact ⟨a₁, (Finset.mem_erase.mp ha₁).2, a₀, ha₀, a₃, (Finset.mem_erase.mp ha₃).2, h1, h3⟩
    · have hT'ne : T'.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a₂, ha₂', hmax⟩ := Finset.exists_max_image T'
        (fun x => e0 * (x.ofLp 0 - v.ofLp 0) + e1 * (x.ofLp 1 - v.ofLp 1)) hT'ne
      have hrem : (T'.erase a₂).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha₂']; omega
      obtain ⟨a₃, ha₃'⟩ := hrem
      have ha₃2 : a₃ ≠ a₂ := (Finset.mem_erase.mp ha₃').1
      have ha₃T' : a₃ ∈ T' := (Finset.mem_erase.mp ha₃').2
      have ha₂T : a₂ ∈ T := (Finset.mem_erase.mp ha₂').2
      have ha₃T : a₃ ∈ T := (Finset.mem_erase.mp ha₃T').2
      set c2 := e0 * (a₂.ofLp 0 - v.ofLp 0) + e1 * (a₂.ofLp 1 - v.ofLp 1)
      set s2 := e0 * (a₂.ofLp 1 - v.ofLp 1) - e1 * (a₂.ofLp 0 - v.ofLp 0)
      set c3 := e0 * (a₃.ofLp 0 - v.ofLp 0) + e1 * (a₃.ofLp 1 - v.ofLp 1)
      set s3 := e0 * (a₃.ofLp 1 - v.ofLp 1) - e1 * (a₃.ofLp 0 - v.ofLp 0)
      have hc3_le : c3 ≤ c2 := hmax a₃ ha₃T'
      have hcs2 : c2 ^ 2 + s2 ^ 2 = (r ^ 2) ^ 2 := by
        have h2 : (a₂.ofLp 0 - v.ofLp 0) ^ 2 + (a₂.ofLp 1 - v.ofLp 1) ^ 2 = r ^ 2 := by
          rw [← dist_sq_coords, hdist a₂ ha₂T]
        calc c2 ^ 2 + s2 ^ 2
            = (e0 ^ 2 + e1 ^ 2) *
              ((a₂.ofLp 0 - v.ofLp 0) ^ 2 + (a₂.ofLp 1 - v.ofLp 1) ^ 2) := by ring
          _ = (r ^ 2) ^ 2 := by rw [he2, h2]; ring
      have hcs3 : c3 ^ 2 + s3 ^ 2 = (r ^ 2) ^ 2 := by
        have h3 : (a₃.ofLp 0 - v.ofLp 0) ^ 2 + (a₃.ofLp 1 - v.ofLp 1) ^ 2 = r ^ 2 := by
          rw [← dist_sq_coords, hdist a₃ ha₃T]
        calc c3 ^ 2 + s3 ^ 2
            = (e0 ^ 2 + e1 ^ 2) *
              ((a₃.ofLp 0 - v.ofLp 0) ^ 2 + (a₃.ofLp 1 - v.ofLp 1) ^ 2) := by ring
          _ = (r ^ 2) ^ 2 := by rw [he2, h3]; ring
      have hdet23 : r ^ 2 * ((a₂.ofLp 0 - v.ofLp 0) * (a₃.ofLp 1 - v.ofLp 1) -
          (a₂.ofLp 1 - v.ofLp 1) * (a₃.ofLp 0 - v.ofLp 0)) = c2 * s3 - s2 * c3 := by
        rw [← he2]; ring
      have hsame_pos_or_neg : (0 < s2 ∧ 0 < s3) ∨ (s2 < 0 ∧ s3 < 0) := by
        have hs2ne := hdet_ne a₂ ha₂'
        have hs3ne := hdet_ne a₃ ha₃T'
        rcases lt_or_gt_of_ne hs2ne with h2neg | h2pos
        · rcases lt_or_gt_of_ne hs3ne with h3neg | h3pos
          · exact Or.inr ⟨h2neg, h3neg⟩
          · exact False.elim (hboth ⟨⟨a₂, ha₂', h2neg⟩, ⟨a₃, ha₃T', h3pos⟩⟩)
        · rcases lt_or_gt_of_ne hs3ne with h3neg | h3pos
          · exact False.elim (hboth ⟨⟨a₃, ha₃T', h3neg⟩, ⟨a₂, ha₂', h2pos⟩⟩)
          · exact Or.inl ⟨h2pos, h3pos⟩
      have hc3_lt : c3 < c2 := by
        refine lt_of_le_of_ne hc3_le fun heqc => ?_
        have hs_eq : s3 = s2 := by
          have hsq : s3 ^ 2 = s2 ^ 2 := by linear_combination hcs3 - hcs2 - (c3 + c2) * heqc
          rcases hsame_pos_or_neg with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> nlinarith only [hsq, h2, h3]
        have hd0 : e0 * (a₃.ofLp 0 - a₂.ofLp 0) + e1 * (a₃.ofLp 1 - a₂.ofLp 1) = 0 := by
          linear_combination heqc
        have hd1 : e0 * (a₃.ofLp 1 - a₂.ofLp 1) - e1 * (a₃.ofLp 0 - a₂.ofLp 0) = 0 := by
          linear_combination hs_eq
        have hsq0 : r ^ 2 * ((a₃.ofLp 0 - a₂.ofLp 0) ^ 2 + (a₃.ofLp 1 - a₂.ofLp 1) ^ 2) = 0 := by
          calc r ^ 2 * ((a₃.ofLp 0 - a₂.ofLp 0) ^ 2 + (a₃.ofLp 1 - a₂.ofLp 1) ^ 2)
              = (e0 ^ 2 + e1 ^ 2) *
                ((a₃.ofLp 0 - a₂.ofLp 0) ^ 2 + (a₃.ofLp 1 - a₂.ofLp 1) ^ 2) := by rw [he2]
            _ = (e0 * (a₃.ofLp 0 - a₂.ofLp 0) + e1 * (a₃.ofLp 1 - a₂.ofLp 1)) ^ 2 +
                (e0 * (a₃.ofLp 1 - a₂.ofLp 1) - e1 * (a₃.ofLp 0 - a₂.ofLp 0)) ^ 2 := by ring
            _ = 0 := by rw [hd0, hd1]; ring
        have hzero : (a₃.ofLp 0 - a₂.ofLp 0) ^ 2 + (a₃.ofLp 1 - a₂.ofLp 1) ^ 2 = 0 :=
          (mul_eq_zero.mp hsq0).resolve_left (ne_of_gt hr2)
        have h0 : a₃.ofLp 0 - a₂.ofLp 0 = 0 := by nlinarith only [hzero]
        have h1 : a₃.ofLp 1 - a₂.ofLp 1 = 0 := by nlinarith only [hzero]
        exact ha₃2 (pt_eq_of_coords (by linarith only [h0]) (by linarith only [h1]))
      rcases hsame_pos_or_neg with ⟨h2pos, h3pos⟩ | ⟨h2neg, h3neg⟩
      · have hcs_pos : 0 < c2 * s3 - s2 * c3 :=
          det_pos_of_circle_order hcs2 hcs3 hc3_lt h2pos h3pos
        refine ⟨a₀, ha₀, a₂, ha₂T, a₃, ha₃T, ?_, ?_⟩
        · change (a₂.ofLp 0 - v.ofLp 0) * e1 - (a₂.ofLp 1 - v.ofLp 1) * e0 < 0
          linarith only [h2pos]
        · exact pos_of_mul_pos_right (hdet23.symm ▸ hcs_pos) (le_of_lt hr2)
      · have hcs_pos' : 0 < c2 * (-s3) - (-s2) * c3 :=
          det_pos_of_circle_order (R := (r ^ 2) ^ 2)
            (by rw [neg_sq]; exact hcs2) (by rw [neg_sq]; exact hcs3)
            hc3_lt (neg_pos.mpr h2neg) (neg_pos.mpr h3neg)
        have hcs_neg : c2 * s3 - s2 * c3 < 0 := by linarith only [hcs_pos']
        refine ⟨a₃, ha₃T, a₂, ha₂T, a₀, ha₀, ?_, ?_⟩
        · have hneg' : 0 < r ^ 2 * (-((a₂.ofLp 0 - v.ofLp 0) * (a₃.ofLp 1 - v.ofLp 1) -
              (a₂.ofLp 1 - v.ofLp 1) * (a₃.ofLp 0 - v.ofLp 0))) := by
            linarith only [hdet23, hcs_neg]
          have hpos' := pos_of_mul_pos_right hneg' (le_of_lt hr2)
          linarith only [hpos']
        · change 0 < (a₂.ofLp 0 - v.ofLp 0) * e1 - (a₂.ofLp 1 - v.ofLp 1) * e0
          linarith only [h2neg]

lemma deg_le_of_sandwich {S : Finset (EuclideanSpace ℝ (Fin 2))}
    {d : ℝ} (hd : 0 < d) {m : ℕ}
    (hm : ((S.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')).card ≤ m)
    {v a₁ a₂ a₃ : EuclideanSpace ℝ (Fin 2)}
    (hv : v ∈ S) (ha₁ : a₁ ∈ S) (_ha₂ : a₂ ∈ S) (ha₃ : a₃ ∈ S)
    (hd₁ : dist a₁ v = d) (hd₂ : dist a₂ v = d) (hd₃ : dist a₃ v = d)
    (hdet₁ : (a₂.ofLp 0 - v.ofLp 0) * (a₁.ofLp 1 - v.ofLp 1) -
      (a₂.ofLp 1 - v.ofLp 1) * (a₁.ofLp 0 - v.ofLp 0) < 0)
    (hdet₃ : 0 < (a₂.ofLp 0 - v.ofLp 0) * (a₃.ofLp 1 - v.ofLp 1) -
      (a₂.ofLp 1 - v.ofLp 1) * (a₃.ofLp 0 - v.ofLp 0)) :
    (S.filter (fun w => dist a₂ w = d)).card ≤ 4 * m + 1 := by
  let U := (S.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')
  have hUm : U.card ≤ m := hm
  let N := (S.filter (fun w => dist a₂ w = d)).erase v
  have ha₂₁ : a₂ ≠ a₁ := by
    intro h; rw [h] at hdet₁; linarith only [hdet₁]
  have ha₂₃ : a₂ ≠ a₃ := by
    intro h; rw [h] at hdet₃; linarith only [hdet₃]
  have hvmem : v ∈ S.filter (fun w => dist a₂ w = d) :=
    Finset.mem_filter.mpr ⟨hv, hd₂⟩
  have hsub : N ⊆ (S.filter (fun w => dist w a₂ = d ∧ dist w a₁ ∈ U)) ∪
      (S.filter (fun w => dist w a₂ = d ∧ dist w a₃ ∈ U)) := by
    intro w hw
    have hwm := Finset.mem_erase.mp hw
    have hwv : w ≠ v := hwm.1
    have hwf := Finset.mem_filter.mp hwm.2
    have hwa₂ : dist w a₂ = d := (dist_comm w a₂).trans hwf.2
    rcases three_neighbor_gt hd hd₁ hd₂ hd₃ hwa₂ hwv hdet₁ hdet₃ with hgt1 | hgt3
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwf.1, hwa₂, ?_⟩)
      have hne1 : w ≠ a₁ := dist_pos.mp (lt_trans hd hgt1)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(w, a₁), Finset.mem_offDiag.mpr ⟨hwf.1, ha₁, hne1⟩, rfl⟩, hgt1⟩
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwf.1, hwa₂, ?_⟩)
      have hne3 : w ≠ a₃ := dist_pos.mp (lt_trans hd hgt3)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(w, a₃), Finset.mem_offDiag.mpr ⟨hwf.1, ha₃, hne3⟩, rfl⟩, hgt3⟩
  have hbound : ∀ a ∈ S, a₂ ≠ a →
      (S.filter (fun w => dist w a₂ = d ∧ dist w a ∈ U)).card ≤ 2 * U.card := by
    intro a _ hne
    have hsplit : (S.filter (fun w => dist w a₂ = d ∧ dist w a ∈ U)).card =
        ∑ d' ∈ U, (S.filter (fun w => dist w a₂ = d ∧ dist w a = d')).card := by
      let S₀ := S.filter (fun w => dist w a₂ = d)
      have h1 : S.filter (fun w => dist w a₂ = d ∧ dist w a ∈ U) =
          S₀.filter (fun w => dist w a ∈ U) := by
        ext w; simp [S₀, and_assoc]
      rw [h1, ← Finset.sum_card_fiberwise_eq_card_filter]
      refine Finset.sum_congr rfl fun d' _ => ?_
      congr 1; ext w; simp [S₀, and_assoc]
    rw [hsplit]
    calc ∑ d' ∈ U, (S.filter (fun w => dist w a₂ = d ∧ dist w a = d')).card
        ≤ ∑ _d' ∈ U, 2 := Finset.sum_le_sum fun d' _ =>
          card_circle_inter_le_two S a₂ a hne d d'
      _ = 2 * U.card := by simp [mul_comm]
  have hN : N.card ≤ 4 * U.card := by
    calc N.card
        ≤ ((S.filter (fun w => dist w a₂ = d ∧ dist w a₁ ∈ U)) ∪
            (S.filter (fun w => dist w a₂ = d ∧ dist w a₃ ∈ U))).card :=
          Finset.card_le_card hsub
      _ ≤ (S.filter (fun w => dist w a₂ = d ∧ dist w a₁ ∈ U)).card +
          (S.filter (fun w => dist w a₂ = d ∧ dist w a₃ ∈ U)).card :=
          Finset.card_union_le _ _
      _ ≤ 2 * U.card + 2 * U.card :=
          Nat.add_le_add (hbound a₁ ha₁ ha₂₁) (hbound a₃ ha₃ ha₂₃)
      _ = 4 * U.card := by ring
  have hcard : (S.filter (fun w => dist a₂ w = d)).card = N.card + 1 :=
    (Finset.card_erase_add_one hvmem).symm
  omega

lemma offDiag_dist_card_le_of_upper_rank (n : ℕ) :
    ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) (m : ℕ),
      S.card = n → 0 < d →
      ((S.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')).card ≤ m →
      (S.offDiag.filter (fun p => dist p.1 p.2 = d)).card ≤ 2 * (4 * m + 1) * S.card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S d m hScard hd hm
    by_cases hdeg : ∀ v ∈ S, (S.filter (fun u => dist v u = d)).card ≤ 2
    · have hsum : (S.offDiag.filter (fun p => dist p.1 p.2 = d)).card =
          ∑ v ∈ S, (S.filter (fun u => dist v u = d)).card := by
        have hfilt : (S.offDiag.filter (fun p => dist p.1 p.2 = d)).filter
            (fun p => p.1 ∈ S) = S.offDiag.filter (fun p => dist p.1 p.2 = d) := by
          ext ⟨x, y⟩; simp [Finset.mem_offDiag]; tauto
        rw [← hfilt, ← Finset.sum_card_fiberwise_eq_card_filter
          (s := S.offDiag.filter (fun p => dist p.1 p.2 = d)) (t := S) (g := Prod.fst)]
        refine Finset.sum_congr rfl fun v hv => ?_
        refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro ⟨x, y⟩ hp
          have h1 := Finset.mem_filter.mp hp
          have h2 := Finset.mem_filter.mp h1.1
          have h3 := Finset.mem_offDiag.mp h2.1
          have hxv : x = v := h1.2
          rw [hxv] at h2
          exact Finset.mem_filter.mpr ⟨h3.2.1, h2.2⟩
        · intro ⟨x₁, y₁⟩ hp₁ ⟨x₂, y₂⟩ hp₂ hEq
          have hx₁ : x₁ = v := (Finset.mem_filter.mp hp₁).2
          have hx₂ : x₂ = v := (Finset.mem_filter.mp hp₂).2
          exact Prod.ext (hx₁.trans hx₂.symm) hEq
        · intro u hu
          have huf := Finset.mem_filter.mp hu
          have hvu : v ≠ u := dist_pos.mp (huf.2.symm ▸ hd)
          exact ⟨(v, u), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hv, huf.1, hvu⟩, huf.2⟩, rfl⟩, rfl⟩
      rw [hsum]
      calc ∑ v ∈ S, (S.filter (fun u => dist v u = d)).card
          ≤ ∑ _v ∈ S, 2 := Finset.sum_le_sum fun v hv => hdeg v hv
        _ = 2 * S.card := by simp [mul_comm]
        _ ≤ 2 * (4 * m + 1) * S.card := by
            have : 2 ≤ 2 * (4 * m + 1) := by omega
            exact Nat.mul_le_mul_right S.card this
    · push Not at hdeg
      obtain ⟨v, hv, hv3⟩ := hdeg
      let T := S.filter (fun u => dist u v = d)
      have hTcard : 3 ≤ T.card := by
        have hEq : T = S.filter (fun u => dist v u = d) := by
          ext u; simp [T, dist_comm]
        rw [hEq]; omega
      have hTdist : ∀ a ∈ T, dist a v = d := fun a ha => (Finset.mem_filter.mp ha).2
      obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hdet₁, hdet₃⟩ :=
        exists_sandwich_of_three_on_circle hd T hTcard hTdist
      have ha₁S : a₁ ∈ S := (Finset.mem_filter.mp ha₁).1
      have ha₂S : a₂ ∈ S := (Finset.mem_filter.mp ha₂).1
      have ha₃S : a₃ ∈ S := (Finset.mem_filter.mp ha₃).1
      have hdeg2 : (S.filter (fun w => dist a₂ w = d)).card ≤ 4 * m + 1 :=
        deg_le_of_sandwich hd hm hv ha₁S ha₂S ha₃S (hTdist a₁ ha₁) (hTdist a₂ ha₂)
          (hTdist a₃ ha₃) hdet₁ hdet₃
      let S' := S.erase a₂
      have hS'card : S'.card < n := by
        rw [← hScard, Finset.card_erase_of_mem ha₂S]
        have : 1 ≤ S.card := Finset.one_le_card.mpr ⟨a₂, ha₂S⟩
        omega
      have hm' : ((S'.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')).card ≤ m := by
        refine (Finset.card_le_card ?_).trans hm
        intro x hx
        have hxm := Finset.mem_filter.mp hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxm.1
        have hpo := Finset.mem_offDiag.mp hp
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨p, Finset.mem_offDiag.mpr
            ⟨Finset.mem_of_mem_erase hpo.1, Finset.mem_of_mem_erase hpo.2.1, hpo.2.2⟩, rfl⟩,
          hxm.2⟩
      have hIH := ih S'.card hS'card S' d m rfl hd hm'
      let E := S.offDiag.filter (fun p => dist p.1 p.2 = d)
      let E' := S'.offDiag.filter (fun p => dist p.1 p.2 = d)
      let E1 := E.filter (fun p => p.1 = a₂)
      let E2 := E.filter (fun p => p.2 = a₂)
      have hE'le : E'.card ≤ 2 * (4 * m + 1) * S'.card := hIH
      have hEsub : E ⊆ E' ∪ (E1 ∪ E2) := by
        intro ⟨x, y⟩ hp
        have hpf := Finset.mem_filter.mp hp
        have hpo := Finset.mem_offDiag.mp hpf.1
        by_cases hx : x = a₂
        · exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hp, hx⟩))
        · by_cases hy : y = a₂
          · exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hp, hy⟩))
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨Finset.mem_offDiag.mpr
                ⟨Finset.mem_erase.mpr ⟨hx, hpo.1⟩, Finset.mem_erase.mpr ⟨hy, hpo.2.1⟩, hpo.2.2⟩,
              hpf.2⟩)
      have hE1 : E1.card ≤ (S.filter (fun w => dist a₂ w = d)).card := by
        refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
        · intro ⟨x, y⟩ hp
          have h1 := Finset.mem_filter.mp hp
          have h2 := Finset.mem_filter.mp h1.1
          have h3 := Finset.mem_offDiag.mp h2.1
          have hx : x = a₂ := h1.2
          rw [hx] at h2
          exact Finset.mem_filter.mpr ⟨h3.2.1, h2.2⟩
        · intro ⟨x₁, y₁⟩ hp₁ ⟨x₂, y₂⟩ hp₂ hEq
          have hx₁ : x₁ = a₂ := (Finset.mem_filter.mp hp₁).2
          have hx₂ : x₂ = a₂ := (Finset.mem_filter.mp hp₂).2
          exact Prod.ext (hx₁.trans hx₂.symm) hEq
      have hE2 : E2.card ≤ (S.filter (fun w => dist a₂ w = d)).card := by
        refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
        · intro ⟨x, y⟩ hp
          have h1 := Finset.mem_filter.mp hp
          have h2 := Finset.mem_filter.mp h1.1
          have h3 := Finset.mem_offDiag.mp h2.1
          have hy : y = a₂ := h1.2
          rw [hy] at h2
          exact Finset.mem_filter.mpr ⟨h3.1, (dist_comm a₂ x).trans h2.2⟩
        · intro ⟨x₁, y₁⟩ hp₁ ⟨x₂, y₂⟩ hp₂ hEq
          have hy₁ : y₁ = a₂ := (Finset.mem_filter.mp hp₁).2
          have hy₂ : y₂ = a₂ := (Finset.mem_filter.mp hp₂).2
          exact Prod.ext hEq (hy₁.trans hy₂.symm)
      have hScard_eq : S'.card + 1 = S.card := Finset.card_erase_add_one ha₂S
      calc E.card
          ≤ (E' ∪ (E1 ∪ E2)).card := Finset.card_le_card hEsub
        _ ≤ E'.card + (E1 ∪ E2).card := Finset.card_union_le _ _
        _ ≤ E'.card + (E1.card + E2.card) :=
            Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ ≤ 2 * (4 * m + 1) * S'.card + ((4 * m + 1) + (4 * m + 1)) := by omega
        _ = 2 * (4 * m + 1) * (S'.card + 1) := by ring
        _ = 2 * (4 * m + 1) * S.card := by rw [hScard_eq]

lemma pairMultiplicity_le_of_upper_rank (S : Finset (EuclideanSpace ℝ (Fin 2)))
    {d : ℝ} (hd : 0 < d) {m : ℕ}
    (hm : ((S.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')).card ≤ m) :
    pairMultiplicity S d ≤ (4 * m + 1) * S.card := by
  have h := offDiag_dist_card_le_of_upper_rank S.card S d m rfl hd hm
  change (S.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2 ≤ (4 * m + 1) * S.card
  rw [Nat.mul_assoc] at h
  exact Nat.div_le_of_le_mul h

lemma exists_dist_gt_of_mem_convexHull_erase
    {S : Finset (EuclideanSpace ℝ (Fin 2))} {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)) :
    ∃ u ∈ S.erase x, dist x y < dist u y := by
  let t := S.erase x
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw0, hwsum, hcm⟩ := hx
  rw [Finset.centerMass_eq_of_sum_1 t id hwsum] at hcm
  have hcoord : ∀ i : Fin 2, ∑ u ∈ t, w u * u.ofLp i = x.ofLp i := by
    intro i
    have hi := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp i) hcm
    simpa [smul_eq_mul] using hi
  have hdiff0 : ∑ u ∈ t, w u * (u.ofLp 0 - x.ofLp 0) = 0 := by
    have : ∑ u ∈ t, w u * (u.ofLp 0 - x.ofLp 0) =
        (∑ u ∈ t, w u * u.ofLp 0) - (∑ u ∈ t, w u) * x.ofLp 0 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => by ring
    rw [this, hcoord 0, hwsum, one_mul, sub_self]
  have hdiff1 : ∑ u ∈ t, w u * (u.ofLp 1 - x.ofLp 1) = 0 := by
    have : ∑ u ∈ t, w u * (u.ofLp 1 - x.ofLp 1) =
        (∑ u ∈ t, w u * u.ofLp 1) - (∑ u ∈ t, w u) * x.ofLp 1 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => by ring
    rw [this, hcoord 1, hwsum, one_mul, sub_self]
  have hvar : ∑ u ∈ t, w u * dist u y ^ 2 =
      dist x y ^ 2 + ∑ u ∈ t, w u * dist u x ^ 2 := by
    have hpt : ∀ u ∈ t, w u * dist u y ^ 2 =
        w u * dist x y ^ 2 + w u * dist u x ^ 2 +
        2 * (x.ofLp 0 - y.ofLp 0) * (w u * (u.ofLp 0 - x.ofLp 0)) +
        2 * (x.ofLp 1 - y.ofLp 1) * (w u * (u.ofLp 1 - x.ofLp 1)) := by
      intro u _
      rw [dist_sq_coords u y, dist_sq_coords x y, dist_sq_coords u x]
      ring
    calc ∑ u ∈ t, w u * dist u y ^ 2
        = ∑ u ∈ t, (w u * dist x y ^ 2 + w u * dist u x ^ 2 +
            2 * (x.ofLp 0 - y.ofLp 0) * (w u * (u.ofLp 0 - x.ofLp 0)) +
            2 * (x.ofLp 1 - y.ofLp 1) * (w u * (u.ofLp 1 - x.ofLp 1))) :=
          Finset.sum_congr rfl hpt
      _ = (∑ u ∈ t, w u) * dist x y ^ 2 + (∑ u ∈ t, w u * dist u x ^ 2) +
          2 * (x.ofLp 0 - y.ofLp 0) * (∑ u ∈ t, w u * (u.ofLp 0 - x.ofLp 0)) +
          2 * (x.ofLp 1 - y.ofLp 1) * (∑ u ∈ t, w u * (u.ofLp 1 - x.ofLp 1)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ = dist x y ^ 2 + ∑ u ∈ t, w u * dist u x ^ 2 := by
          rw [hwsum, one_mul, hdiff0, hdiff1]; ring
  have hexpos : ∃ u₀ ∈ t, 0 < w u₀ := by
    by_contra hall
    push Not at hall
    have hz : ∑ u ∈ t, w u = 0 :=
      Finset.sum_eq_zero fun u hu => le_antisymm (hall u hu) (hw0 u hu)
    linarith only [hwsum, hz]
  obtain ⟨u₀, hu₀, hwu₀⟩ := hexpos
  have hu₀_ne : u₀ ≠ x := (Finset.mem_erase.mp hu₀).1
  have hvar_pos : 0 < ∑ u ∈ t, w u * dist u x ^ 2 := by
    have hterm_pos : 0 < w u₀ * dist u₀ x ^ 2 :=
      mul_pos hwu₀ (sq_pos_of_pos (dist_pos.mpr hu₀_ne))
    have hle : w u₀ * dist u₀ x ^ 2 ≤ ∑ u ∈ t, w u * dist u x ^ 2 :=
      Finset.single_le_sum (f := fun u => w u * dist u x ^ 2)
        (fun u hu => mul_nonneg (hw0 u hu) (sq_nonneg _)) hu₀
    linarith only [hterm_pos, hle]
  have hstrict : dist x y ^ 2 < ∑ u ∈ t, w u * dist u y ^ 2 := by
    linarith only [hvar, hvar_pos]
  by_contra hnone
  push Not at hnone
  have hle : ∑ u ∈ t, w u * dist u y ^ 2 ≤ dist x y ^ 2 := by
    calc ∑ u ∈ t, w u * dist u y ^ 2
        ≤ ∑ u ∈ t, w u * dist x y ^ 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ dist_nonneg (hnone u hu) 2) (hw0 u hu)
      _ = (∑ u ∈ t, w u) * dist x y ^ 2 := (Finset.sum_mul _ _ _).symm
      _ = dist x y ^ 2 := by rw [hwsum, one_mul]
  linarith only [hstrict, hle]

lemma peel_iter_subset (A : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) :
    (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
      S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[k] A ⊆ A := by
  induction k with
  | zero => exact Finset.Subset.refl A
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (Finset.filter_subset _ _).trans ih

lemma upper_rank_ge_of_mem_peel (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∀ (k : ℕ) {x y : EuclideanSpace ℝ (Fin 2)},
      x ∈ (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
        S.filter (fun z => z ∈ convexHull ℝ ((S.erase z : Finset _) : Set _)))^[k] A →
      y ∈ A →
      k ≤ ((A.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => dist x y < d')).card := by
  intro k
  induction k with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ k ih =>
    intro x y hx hy
    rw [Function.iterate_succ_apply'] at hx
    let R := (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
      S.filter (fun z => z ∈ convexHull ℝ ((S.erase z : Finset _) : Set _)))^[k] A
    have hxf := Finset.mem_filter.mp hx
    obtain ⟨u, hu, hgt⟩ := exists_dist_gt_of_mem_convexHull_erase hxf.2
    have huR : u ∈ R := Finset.mem_of_mem_erase hu
    have huA : u ∈ A := peel_iter_subset A k huR
    have hIH := ih huR hy
    let D := A.offDiag.image (fun p => dist p.1 p.2)
    have huy_ne : u ≠ y := dist_pos.mp (lt_of_le_of_lt dist_nonneg hgt)
    have hduy_mem : dist u y ∈ D :=
      Finset.mem_image.mpr ⟨(u, y), Finset.mem_offDiag.mpr ⟨huA, hy, huy_ne⟩, rfl⟩
    have hsub : insert (dist u y) (D.filter (fun d' => dist u y < d')) ⊆
        D.filter (fun d' => dist x y < d') := by
      intro d' hd'
      rcases Finset.mem_insert.mp hd' with rfl | hd''
      · exact Finset.mem_filter.mpr ⟨hduy_mem, hgt⟩
      · have hm := Finset.mem_filter.mp hd''
        exact Finset.mem_filter.mpr ⟨hm.1, lt_trans hgt hm.2⟩
    have hnotmem : dist u y ∉ D.filter (fun d' => dist u y < d') := by
      simp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotmem] at hcard
    dsimp only [D] at hcard
    omega

lemma topK_card (D : Finset ℝ) {k : ℕ} (hk : k ≤ D.card) :
    (D.filter (fun d => (D.filter (fun d' => d < d')).card < k)).card = k := by
  let rank : ℝ → ℕ := fun d => (D.filter (fun d' => d < d')).card
  have hinj : Set.InjOn rank D := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hssub : D.filter (fun d' => b < d') ⊂ D.filter (fun d' => a < d') := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro x hx
          have hm := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hm.1, lt_trans hlt hm.2⟩
        · intro heq
          have hb_in : b ∈ D.filter (fun d' => a < d') := Finset.mem_filter.mpr ⟨hb, hlt⟩
          rw [← heq] at hb_in
          exact lt_irrefl b (Finset.mem_filter.mp hb_in).2
      have hcard_lt : rank b < rank a := Finset.card_lt_card hssub
      omega
    · have hssub : D.filter (fun d' => a < d') ⊂ D.filter (fun d' => b < d') := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro x hx
          have hm := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hm.1, lt_trans hgt hm.2⟩
        · intro heq
          have ha_in : a ∈ D.filter (fun d' => b < d') := Finset.mem_filter.mpr ⟨ha, hgt⟩
          rw [← heq] at ha_in
          exact lt_irrefl a (Finset.mem_filter.mp ha_in).2
      have hcard_lt : rank a < rank b := Finset.card_lt_card hssub
      omega
  have hmaps : D.image rank ⊆ Finset.range D.card := by
    intro r hr
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hr
    refine Finset.mem_range.mpr ?_
    have hssub : D.filter (fun d' => d < d') ⊂ D := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hdin : d ∈ D.filter (fun d' => d < d') := heq.symm ▸ hd
      exact lt_irrefl d (Finset.mem_filter.mp hdin).2
    exact Finset.card_lt_card hssub
  have himg_eq : D.image rank = Finset.range D.card := by
    refine Finset.eq_of_subset_of_card_le hmaps ?_
    rw [Finset.card_range, Finset.card_image_of_injOn hinj]
  have hfilt_img : (D.filter (fun d => rank d < k)).image rank = Finset.range k := by
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨d, ⟨_, hlt⟩, rfl⟩; exact hlt
    · intro hrk
      have hmem : r ∈ D.image rank := by
        rw [himg_eq]; exact Finset.mem_range.mpr (lt_of_lt_of_le hrk hk)
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hmem
      exact ⟨d, ⟨hd, hrk⟩, rfl⟩
  have hinj' : Set.InjOn rank (D.filter (fun d => rank d < k)) :=
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  calc (D.filter (fun d => rank d < k)).card
      = ((D.filter (fun d => rank d < k)).image rank).card :=
        (Finset.card_image_of_injOn hinj').symm
    _ = (Finset.range k).card := by rw [hfilt_img]
    _ = k := Finset.card_range k

lemma rare_ge_of_small_peel (A : Finset (EuclideanSpace ℝ (Fin 2)))
    {k : ℕ} (hk : 1 ≤ k) (hD : k ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card)
    (hpeel : (4 * k - 3) * (A \ (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
      S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[k] A).card ≤ A.card) :
    k ≤ (rareDistances A).card := by
  let P := (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
    S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[k] A
  let S := A \ P
  let D := A.offDiag.image (fun p => dist p.1 p.2)
  let TopK := D.filter (fun d => (D.filter (fun d' => d < d')).card < k)
  have hTopSub : TopK ⊆ rareDistances A := by
    intro d hd
    have hdm := Finset.mem_filter.mp hd
    have hdD : d ∈ D := hdm.1
    have hrank : ((A.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')).card < k :=
      hdm.2
    refine Finset.mem_filter.mpr ⟨hdD, multiplicity_pos hdD, ?_⟩
    have hpair_eq : A.offDiag.filter (fun p => dist p.1 p.2 = d) =
        S.offDiag.filter (fun p => dist p.1 p.2 = d) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, S, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxA, hyA, hxy⟩, hdist⟩
        have hxnotP : x ∉ P := by
          intro hxP
          have hge := upper_rank_ge_of_mem_peel A k hxP hyA
          rw [hdist] at hge
          omega
        have hynotP : y ∉ P := by
          intro hyP
          have hge := upper_rank_ge_of_mem_peel A k hyP hxA
          rw [dist_comm, hdist] at hge
          omega
        exact ⟨⟨⟨hxA, hxnotP⟩, ⟨hyA, hynotP⟩, hxy⟩, hdist⟩
      · rintro ⟨⟨⟨hxA, _⟩, ⟨hyA, _⟩, hxy⟩, hdist⟩
        exact ⟨⟨hxA, hyA, hxy⟩, hdist⟩
    have hmult_eq : pairMultiplicity A d = pairMultiplicity S d := by
      unfold pairMultiplicity
      rw [hpair_eq]
    have hSsub : S ⊆ A := Finset.sdiff_subset
    have hmS : ((S.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d')).card ≤
        k - 1 := by
      have hsubD : (S.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d') ⊆
          (A.offDiag.image (fun p => dist p.1 p.2)).filter (fun d' => d < d') := by
        intro r hr
        have hrf := Finset.mem_filter.mp hr
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hrf.1
        have hpo := Finset.mem_offDiag.mp hp
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨p, Finset.mem_offDiag.mpr ⟨hSsub hpo.1, hSsub hpo.2.1, hpo.2.2⟩, rfl⟩,
          hrf.2⟩
      have hle := Finset.card_le_card hsubD
      omega
    have hposd : 0 < d := dist_pos_of_mem_image hdD
    have hdeg := pairMultiplicity_le_of_upper_rank S hposd hmS
    have hcoef : 4 * (k - 1) + 1 = 4 * k - 3 := by omega
    rw [hmult_eq]
    rw [hcoef] at hdeg
    exact hdeg.trans hpeel
  calc k = TopK.card := (topK_card D hD).symm
    _ ≤ (rareDistances A).card := Finset.card_le_card hTopSub

lemma configuration_exists (n : ℕ) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n := by
  let e : ℕ ↪ EuclideanSpace ℝ (Fin 2) :=
    ⟨fun i => WithLp.toLp 2 (fun _ : Fin 2 => (i : ℝ)), by
      intro i j h
      have heq : (i : ℝ) = (j : ℝ) :=
        congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x (0 : Fin 2)) h
      exact_mod_cast heq⟩
  exact ⟨(Finset.range n).map e, by simp⟩

theorem main : H1 → H2 → type_of% @OMA.S_erdos_132.main := by
  intro hpart1 hpart2
  constructor
  · intro A hA
    by_cases hD : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ A.card / 2
    · by_cases hP : A.card < 5 * (A \ (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
          S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[2] A).card
      · exact hpart1 A hA hD hP
      · have hD2 : 2 ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card := by
          have hsq := card_sub_two_le_two_mul_sq A (by omega)
          by_contra hlt
          have hle1 : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 1 := by omega
          have hsq1 : (A.offDiag.image (fun p => dist p.1 p.2)).card ^ 2 ≤ 1 := by nlinarith
          omega
        exact rare_ge_of_small_peel A (by omega : 1 ≤ 2) hD2 (by omega)
    · have hcount := distinct_lt_half_add_rare A (by omega)
      omega
  · refine tendsto_atTop.2 (fun b => ?_)
    let k := max 2 ⌈b⌉₊
    have hk2 : 2 ≤ k := le_max_left 2 _
    have hk1 : 1 ≤ k := by omega
    obtain ⟨N, hN⟩ := hpart2 k hk2
    filter_upwards [eventually_ge_atTop (max N (2 * k ^ 2 + 3))] with n hn
    have hnk : k ≤ minRareCount n := by
      unfold minRareCount
      apply le_csInf
      · obtain ⟨A, hA⟩ := configuration_exists n
        exact ⟨(rareDistances A).card, A, hA, rfl⟩
      · rintro j ⟨A, hA, rfl⟩
        by_cases hD :
            (A.offDiag.image (fun p => dist p.1 p.2)).card + 2 ≤ A.card / 2 + k
        · by_cases hP : A.card < (4 * k - 3) * (A \ (fun S : Finset (EuclideanSpace ℝ (Fin 2)) =>
              S.filter (fun x => x ∈ convexHull ℝ ((S.erase x : Finset _) : Set _)))^[k] A).card
          · exact hN A (by omega) hD hP
          · have hDk : k ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card := by
              have hsq := card_sub_two_le_two_mul_sq A (by omega)
              have hn2 : 2 * k ^ 2 + 3 ≤ A.card := by omega
              by_contra hlt
              have hle : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ k - 1 := by omega
              have hsqle : (A.offDiag.image (fun p => dist p.1 p.2)).card ^ 2 ≤ k ^ 2 := by
                nlinarith
              omega
            exact rare_ge_of_small_peel A hk1 hDk (by omega)
        · have hcount := distinct_lt_half_add_rare A (by omega)
          omega
    have hbk : b ≤ (k : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast le_max_right 2 ⌈b⌉₊)
    exact hbk.trans (by exact_mod_cast hnk)

end OMA.R_erdos_132_R2
