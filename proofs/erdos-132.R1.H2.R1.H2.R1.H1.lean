import OMAReductions.R_erdos_132_R1_H2_R1_H2_R1

/-
Step erdos-132.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction erdos-132.R1.H2.R1.H2.R1.
Credit: @Pampasgras

A planar set A with at most G points on every circle centred at one of its points and at most L
displacement vectors x - y at every distance has at least k rare distances once k * G * L <= |A|.

Proof. Put t = |A| / L. For a unit vector u, a low point is a point of A with at most t points of
A strictly below it and at least t + 1 weakly below it (heights are inner products with u); a
high point is a low point for -u. Over the unit directions of the displacements of A and all low
points b and high points p of each, take the triple maximising W = <p - b, u>.

(1) Let v be a displacement of A with |v| > W, and take a low point b and a high point p for the
direction of v, so <p - b, v/|v|> <= W < |v|. If x and x + v are in A, then either x is strictly
below b, or x + v is strictly above p. So at most 2 t points x of A have x + v in A. A distance
d > W therefore has at most 2 t * L ordered pairs, hence multiplicity at most t * L <= |A|.

(2) For the maximising triple (u, b, p), every q weakly below b has dist p q >= <p - q, u> >= W,
and dist p q <= W forces q = p - W u (equality in Cauchy-Schwarz). So p has at least t partners
at distances above W, at most G of them at any one distance: at least t / G >= k rare distances.

This is a finite form (no continuity, no order statistics) of the trimmed-projection idea in the
note of @TanmayPatil-1 on erdos-132 (note 48541).
-/
open Finset
open scoped Classical InnerProductSpace
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

namespace OMA.FewDirections

section general

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `b` is a point of `A` with at most `t` points of `A` strictly below it and at least `t + 1`
points weakly below it, heights being measured by the inner product with `u`. -/
def LowPt (A : Finset V) (t : ℕ) (u b : V) : Prop :=
  b ∈ A ∧ (A.filter (fun y => ⟪y, u⟫_ℝ < ⟪b, u⟫_ℝ)).card ≤ t ∧
    t + 1 ≤ (A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪b, u⟫_ℝ)).card

lemma lowPt_exists (A : Finset V) (t : ℕ) (u : V) (h : t + 1 ≤ A.card) :
    ∃ b, LowPt A t u b := by
  have hA : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨m, hmA, hm⟩ := A.exists_max_image (fun x => ⟪x, u⟫_ℝ) hA
  have hmC : m ∈ A.filter
      (fun x => t + 1 ≤ (A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ)).card) := by
    refine mem_filter.mpr ⟨hmA, ?_⟩
    rw [filter_true_of_mem hm]
    exact h
  obtain ⟨b, hbC, hb⟩ := (A.filter
      (fun x => t + 1 ≤ (A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ)).card)).exists_min_image
      (fun x => ⟪x, u⟫_ℝ) ⟨m, hmC⟩
  refine ⟨b, (mem_filter.mp hbC).1, ?_, (mem_filter.mp hbC).2⟩
  by_contra hgt
  rw [not_le] at hgt
  have hSne : (A.filter (fun y => ⟪y, u⟫_ℝ < ⟪b, u⟫_ℝ)).Nonempty := card_pos.mp (by omega)
  obtain ⟨y, hyS, hy⟩ := (A.filter (fun y => ⟪y, u⟫_ℝ < ⟪b, u⟫_ℝ)).exists_max_image
    (fun x => ⟪x, u⟫_ℝ) hSne
  have hyC : y ∈ A.filter
      (fun x => t + 1 ≤ (A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ)).card) := by
    refine mem_filter.mpr ⟨(mem_filter.mp hyS).1, ?_⟩
    have hsub : A.filter (fun z => ⟪z, u⟫_ℝ < ⟪b, u⟫_ℝ) ⊆
        A.filter (fun z => ⟪z, u⟫_ℝ ≤ ⟪y, u⟫_ℝ) := by
      intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).1, hy z hz⟩
    have := card_le_card hsub
    omega
  have h1 := hb y hyC
  have h2 := (mem_filter.mp hyS).2
  linarith

/-- A translation longer than the trimmed width of `A` in its own direction maps at most `2 t`
points of `A` into `A`. -/
lemma shift_count_le {A : Finset V} {t : ℕ} {u b p : V} (hu : ‖u‖ = 1)
    (hb : LowPt A t u b) (hp : LowPt A t (-u) p) {d : ℝ}
    (hd : ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < d) :
    (A.filter (fun x => x + d • u ∈ A)).card ≤ 2 * t := by
  have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have h1 : ((A.filter (fun x => x + d • u ∈ A)).filter
      (fun x => ⟪x, u⟫_ℝ < ⟪b, u⟫_ℝ)).card ≤ t := by
    refine (card_le_card ?_).trans hb.2.1
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx1).1, hx2⟩
  have h2 : ((A.filter (fun x => x + d • u ∈ A)).filter
      (fun x => ¬ ⟪x, u⟫_ℝ < ⟪b, u⟫_ℝ)).card ≤ t := by
    refine le_trans ?_ hp.2.1
    refine card_le_card_of_injOn (fun x => x + d • u) ?_ ?_
    · intro x hx
      obtain ⟨hx1, hx2⟩ := mem_filter.mp (mem_coe.mp hx)
      have hge := not_lt.mp hx2
      refine mem_coe.mpr (mem_filter.mpr ⟨(mem_filter.mp hx1).2, ?_⟩)
      rw [inner_neg_right, inner_neg_right, inner_add_left, real_inner_smul_left, huu]
      linarith
    · intro x _ y _ hxy
      exact add_right_cancel hxy
  have h3 := card_filter_add_card_filter_not
    (s := A.filter (fun x => x + d • u ∈ A)) (fun x => ⟪x, u⟫_ℝ < ⟪b, u⟫_ℝ)
  omega

/-- Seen from any point `p`, all but at most one of the points weakly below a low point `b` are
farther from `p` than the height difference of `p` and `b`. -/
lemma pin_partners {A : Finset V} {t : ℕ} {u b : V} (p : V) (hu : ‖u‖ = 1)
    (hb : LowPt A t u b) :
    ∃ Q ⊆ A, t ≤ Q.card ∧ ∀ q ∈ Q, q ≠ p ∧ ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < dist p q := by
  have key : ∀ q ∈ A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪b, u⟫_ℝ),
      ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ ≤ dist p q ∧
      (dist p q ≤ ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ → q = p - (⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ) • u) := by
    intro q hq
    have hq' := (mem_filter.mp hq).2
    have h1 : ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ ≤ ⟪p - q, u⟫_ℝ := by rw [inner_sub_left]; linarith
    have h2 : ⟪p - q, u⟫_ℝ ≤ ‖p - q‖ := by
      have := real_inner_le_norm (p - q) u
      rwa [hu, mul_one] at this
    rw [dist_eq_norm]
    refine ⟨h1.trans h2, fun h3 => ?_⟩
    have h4 : ⟪p - q, u⟫_ℝ = ‖p - q‖ * ‖u‖ := by rw [hu, mul_one]; linarith
    have h5 := inner_eq_norm_mul_iff_real.mp h4
    rw [hu, one_smul] at h5
    have h6 : ‖p - q‖ = ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ := le_antisymm h3 (h1.trans h2)
    rw [h6] at h5
    rw [← h5]
    abel
  refine ⟨(A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪b, u⟫_ℝ)).filter
    (fun q => q ≠ p ∧ ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < dist p q),
    (filter_subset _ _).trans (filter_subset _ _), ?_, fun q hq => (mem_filter.mp hq).2⟩
  have all : ∀ q ∈ (A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪b, u⟫_ℝ)).filter
      (fun q => ¬ (q ≠ p ∧ ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < dist p q)),
      q = if ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < 0 then p else p - (⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ) • u := by
    intro q hq
    obtain ⟨hqB, hqn⟩ := mem_filter.mp hq
    obtain ⟨hWle, heq⟩ := key q hqB
    by_cases hneg : ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < 0
    · rw [if_pos hneg]
      by_contra hne
      exact hqn ⟨hne, lt_of_lt_of_le hneg dist_nonneg⟩
    · rw [if_neg hneg]
      by_cases hqp : q = p
      · have hW0 : ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ = 0 := by
          have h := hWle
          rw [hqp, dist_self] at h
          linarith [not_lt.mp hneg]
        rw [hqp, hW0, zero_smul, sub_zero]
      · apply heq
        by_contra hgt
        exact hqn ⟨hqp, not_le.mp hgt⟩
  have hexc : ((A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪b, u⟫_ℝ)).filter
      (fun q => ¬ (q ≠ p ∧ ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < dist p q))).card ≤ 1 :=
    card_le_one.mpr fun a ha c hc => (all a ha).trans (all c hc).symm
  have hsplit := card_filter_add_card_filter_not
    (s := A.filter (fun y => ⟪y, u⟫_ℝ ≤ ⟪b, u⟫_ℝ))
    (fun q => q ≠ p ∧ ⟪p, u⟫_ℝ - ⟪b, u⟫_ℝ < dist p q)
  have := hb.2.2
  omega

end general

lemma mult_pos {A : Finset (EuclideanSpace ℝ (Fin 2))} {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) : 1 ≤ pairMultiplicity A (dist x y) := by
  have h1 : (x, y) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = dist x y) :=
    mem_filter.mpr ⟨mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
  have h2 : (y, x) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = dist x y) :=
    mem_filter.mpr ⟨mem_offDiag.mpr ⟨hy, hx, hxy.symm⟩, dist_comm y x⟩
  have hne : (x, y) ≠ (y, x) := fun h => hxy (congrArg Prod.fst h)
  have hcard : 1 < (A.offDiag.filter (fun p => dist p.1 p.2 = dist x y)).card :=
    one_lt_card.mpr ⟨_, h1, _, h2, hne⟩
  unfold pairMultiplicity
  omega

theorem few_directions (A : Finset (EuclideanSpace ℝ (Fin 2))) (G L k : ℕ) (hA : 2 ≤ A.card)
    (hG : ∀ p ∈ A, ∀ d : ℝ, (A.filter (fun q => dist p q = d)).card ≤ G)
    (hL : ∀ d : ℝ, ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).image
      (fun p => p.1 - p.2)).card ≤ L)
    (hk : k * G * L ≤ A.card) : k ≤ (rareDistances A).card := by
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := one_lt_card.mp (by omega : 1 < A.card)
  have hz0 : (x0, y0) ∈ A.offDiag := mem_offDiag.mpr ⟨hx0, hy0, hxy0⟩
  have hL2 : 2 ≤ L := by
    refine le_trans ?_ (hL (dist x0 y0))
    have hsub : ({x0 - y0, y0 - x0} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆
        (A.offDiag.filter (fun p => dist p.1 p.2 = dist x0 y0)).image (fun p => p.1 - p.2) := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_image.mpr ⟨(x0, y0), mem_filter.mpr ⟨hz0, rfl⟩, rfl⟩
      · rw [mem_singleton.mp hv]
        exact mem_image.mpr ⟨(y0, x0), mem_filter.mpr
          ⟨mem_offDiag.mpr ⟨hy0, hx0, hxy0.symm⟩, dist_comm _ _⟩, rfl⟩
    have hne : x0 - y0 ≠ y0 - x0 := by
      intro h
      have h' : (2 : ℝ) • (x0 - y0) = 0 := by
        rw [two_smul]
        nth_rewrite 2 [h]
        abel
      rcases smul_eq_zero.mp h' with h2 | h2
      · norm_num at h2
      · exact hxy0 (sub_eq_zero.mp h2)
    calc 2 = ({x0 - y0, y0 - x0} : Finset (EuclideanSpace ℝ (Fin 2))).card :=
          (card_pair hne).symm
      _ ≤ _ := card_le_card hsub
  have hG1 : 1 ≤ G :=
    le_trans (card_pos.mpr ⟨x0, mem_filter.mpr ⟨hx0, dist_self x0⟩⟩) (hG x0 hx0 0)
  have htL : A.card / L * L ≤ A.card := Nat.div_mul_le_self _ _
  have ht1 : A.card / L + 1 ≤ A.card := by
    have : A.card / L * 2 ≤ A.card / L * L := Nat.mul_le_mul_left _ hL2
    omega
  have hkt : k * G ≤ A.card / L := (Nat.le_div_iff_mul_le (by omega)).mpr hk
  generalize A.card / L = t at htL ht1 hkt
  -- unit directions of the displacements of `A`
  have hdir : ∀ z ∈ A.offDiag, ‖‖z.1 - z.2‖⁻¹ • (z.1 - z.2)‖ = 1 := fun z hz =>
    norm_smul_inv_norm (sub_ne_zero.mpr (mem_offDiag.mp hz).2.2)
  have hdir' : ∀ z ∈ A.offDiag, ‖z.1 - z.2‖ • (‖z.1 - z.2‖⁻¹ • (z.1 - z.2)) = z.1 - z.2 :=
    fun z hz => smul_inv_smul₀
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (mem_offDiag.mp hz).2.2)) _
  -- every direction has a low and a high point; maximise the trimmed width
  have hTr : ∀ z ∈ A.offDiag, ∃ b p, (z, (b, p)) ∈ (A.offDiag ×ˢ (A ×ˢ A)).filter
      (fun w => LowPt A t (‖w.1.1 - w.1.2‖⁻¹ • (w.1.1 - w.1.2)) w.2.1 ∧
        LowPt A t (-(‖w.1.1 - w.1.2‖⁻¹ • (w.1.1 - w.1.2))) w.2.2) := by
    intro z hz
    obtain ⟨b, hb⟩ := lowPt_exists A t (‖z.1 - z.2‖⁻¹ • (z.1 - z.2)) ht1
    obtain ⟨p, hp⟩ := lowPt_exists A t (-(‖z.1 - z.2‖⁻¹ • (z.1 - z.2))) ht1
    exact ⟨b, p, mem_filter.mpr
      ⟨mem_product.mpr ⟨hz, mem_product.mpr ⟨hb.1, hp.1⟩⟩, hb, hp⟩⟩
  obtain ⟨b1, p1, h1⟩ := hTr _ hz0
  obtain ⟨w0, hw0, hmax⟩ := ((A.offDiag ×ˢ (A ×ˢ A)).filter
      (fun w => LowPt A t (‖w.1.1 - w.1.2‖⁻¹ • (w.1.1 - w.1.2)) w.2.1 ∧
        LowPt A t (-(‖w.1.1 - w.1.2‖⁻¹ • (w.1.1 - w.1.2))) w.2.2)).exists_max_image
      (fun w => ⟪w.2.2, ‖w.1.1 - w.1.2‖⁻¹ • (w.1.1 - w.1.2)⟫_ℝ -
        ⟪w.2.1, ‖w.1.1 - w.1.2‖⁻¹ • (w.1.1 - w.1.2)⟫_ℝ) ⟨_, h1⟩
  obtain ⟨hw0mem, hb0, hp0⟩ := mem_filter.mp hw0
  have hw0z : w0.1 ∈ A.offDiag := (mem_product.mp hw0mem).1
  -- a displacement longer than the maximal trimmed width occurs at most `2 t` times
  have sparse : ∀ z ∈ A.offDiag,
      ⟪w0.2.2, ‖w0.1.1 - w0.1.2‖⁻¹ • (w0.1.1 - w0.1.2)⟫_ℝ -
        ⟪w0.2.1, ‖w0.1.1 - w0.1.2‖⁻¹ • (w0.1.1 - w0.1.2)⟫_ℝ < dist z.1 z.2 →
      (A.filter (fun x => x + (z.1 - z.2) ∈ A)).card ≤ 2 * t := by
    intro z hz hlong
    obtain ⟨b, p, hbp⟩ := hTr z hz
    have hle := hmax _ hbp
    obtain ⟨_, hb, hp⟩ := mem_filter.mp hbp
    have h := shift_count_le (hdir z hz) hb hp (d := ‖z.1 - z.2‖)
      (by rw [← dist_eq_norm]; exact lt_of_le_of_lt hle hlong)
    rw [hdir' z hz] at h
    convert h
  -- hence every distance above that width is rare
  have rare : ∀ z ∈ A.offDiag,
      ⟪w0.2.2, ‖w0.1.1 - w0.1.2‖⁻¹ • (w0.1.1 - w0.1.2)⟫_ℝ -
        ⟪w0.2.1, ‖w0.1.1 - w0.1.2‖⁻¹ • (w0.1.1 - w0.1.2)⟫_ℝ < dist z.1 z.2 →
      dist z.1 z.2 ∈ rareDistances A := by
    intro z hz hlong
    have hzm := mem_offDiag.mp hz
    have hcount : (A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2)).card ≤
        2 * t * L := by
      refine (card_le_mul_card_image _ (2 * t) ?_).trans (Nat.mul_le_mul_left _ (hL _))
      intro v hv
      obtain ⟨z', hz', rfl⟩ := mem_image.mp hv
      obtain ⟨hz'O, hz'd⟩ := mem_filter.mp hz'
      refine le_trans ?_ (sparse z' hz'O (by rw [hz'd]; exact hlong))
      refine card_le_card_of_injOn (fun w => w.2) ?_ ?_
      · intro w hw
        obtain ⟨hw1, hw2⟩ := mem_filter.mp (mem_coe.mp hw)
        have hwO := mem_offDiag.mp (mem_filter.mp hw1).1
        refine mem_coe.mpr (mem_filter.mpr ⟨hwO.2.1, ?_⟩)
        rw [← hw2, add_sub_cancel]
        exact hwO.1
      · intro w hw w' hw' heq
        have e1 := (mem_filter.mp (mem_coe.mp hw)).2
        have e2 := (mem_filter.mp (mem_coe.mp hw')).2
        have e3 : w.2 = w'.2 := heq
        have e4 : w.1 = w'.1 := by
          have := e1.trans e2.symm
          rw [e3] at this
          exact sub_left_injective this
        exact Prod.ext e4 e3
    refine mem_filter.mpr ⟨mem_image.mpr ⟨z, hz, rfl⟩, mult_pos hzm.1 hzm.2.1 hzm.2.2, ?_⟩
    unfold pairMultiplicity
    have : 2 * t * L = 2 * (t * L) := by ring
    omega
  -- the high point of the maximising direction sees at least `t` such distances
  obtain ⟨Q, hQA, hQcard, hQ⟩ := pin_partners w0.2.2 (hdir w0.1 hw0z) hb0
  have himg : Q.image (fun q => dist w0.2.2 q) ⊆ rareDistances A := by
    intro d hd
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hd
    obtain ⟨hne, hlt⟩ := hQ q hq
    exact rare (w0.2.2, q) (mem_offDiag.mpr ⟨hp0.1, hQA hq, hne.symm⟩) hlt
  have hfib : Q.card ≤ G * (Q.image (fun q => dist w0.2.2 q)).card := by
    refine card_le_mul_card_image _ G ?_
    intro d _
    refine (card_le_card ?_).trans (hG w0.2.2 hp0.1 d)
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hQA hq1, hq2⟩
  have h6 : k * G ≤ G * (rareDistances A).card :=
    hkt.trans (hQcard.trans (hfib.trans (Nat.mul_le_mul_left G (card_le_card himg))))
  rw [mul_comm] at h6
  exact Nat.le_of_mul_le_mul_left h6 hG1

end OMA.FewDirections

theorem OMA.solution : OMA.R_erdos_132_R1_H2_R1_H2_R1.H1 :=
  fun A G L k hA hG hL hk => OMA.FewDirections.few_directions A G L k hA hG hL hk
