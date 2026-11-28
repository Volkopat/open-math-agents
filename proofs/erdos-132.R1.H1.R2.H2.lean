import OMAReductions.R_erdos_132_R1_H1_R2

-- Step erdos-132.R1.H1.R2.H2: hypothesis H2 of reduction erdos-132.R1.H1.R2
-- Credit: @yhay81

open Finset
open scoped Classical
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

namespace Erdos132LineCover

private lemma dist_sq_line (p₀ v y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    dist (t • v +ᵥ p₀) y ^ 2 =
      ‖v‖ ^ 2 * t ^ 2 + (2 * @inner ℝ _ _ v (p₀ - y)) * t + ‖p₀ - y‖ ^ 2 := by
  rw [vadd_eq_add, dist_eq_norm, show t • v + p₀ - y = t • v + (p₀ - y) by abel,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_left]
  simp only [conj_trivial]
  ring

private lemma strict_convex_dist {p₀ v y : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    {t₁ t t₂ : ℝ} (h₁ : t₁ < t) (h₂ : t < t₂) :
    dist (t • v +ᵥ p₀) y < dist (t₁ • v +ᵥ p₀) y ∨
      dist (t • v +ᵥ p₀) y < dist (t₂ • v +ᵥ p₀) y := by
  have hvpos : 0 < ‖v‖ ^ 2 := by positivity
  have hsq :
      dist (t • v +ᵥ p₀) y ^ 2 < dist (t₁ • v +ᵥ p₀) y ^ 2 ∨
        dist (t • v +ᵥ p₀) y ^ 2 < dist (t₂ • v +ᵥ p₀) y ^ 2 := by
    rw [dist_sq_line, dist_sq_line, dist_sq_line]
    by_contra! h
    have hcomb :
        (t₂ - t) * (‖v‖ ^ 2 * t₁ ^ 2 + 2 * @inner ℝ _ _ v (p₀ - y) * t₁ + ‖p₀ - y‖ ^ 2 -
          (‖v‖ ^ 2 * t ^ 2 + 2 * @inner ℝ _ _ v (p₀ - y) * t + ‖p₀ - y‖ ^ 2)) +
        (t - t₁) * (‖v‖ ^ 2 * t₂ ^ 2 + 2 * @inner ℝ _ _ v (p₀ - y) * t₂ + ‖p₀ - y‖ ^ 2 -
          (‖v‖ ^ 2 * t ^ 2 + 2 * @inner ℝ _ _ v (p₀ - y) * t + ‖p₀ - y‖ ^ 2)) =
        ‖v‖ ^ 2 * (t₂ - t) * (t - t₁) * (t₂ - t₁) := by ring
    have hpos : 0 < ‖v‖ ^ 2 * (t₂ - t) * (t - t₁) * (t₂ - t₁) := by
      have : 0 < t₂ - t := by linarith
      have : 0 < t - t₁ := by linarith
      have : 0 < t₂ - t₁ := by linarith
      positivity
    nlinarith [h.1, h.2]
  rcases hsq with h | h
  · left
    nlinarith [dist_nonneg (x := t • v +ᵥ p₀) (y := y), dist_nonneg (x := t₁ • v +ᵥ p₀) (y := y)]
  · right
    nlinarith [dist_nonneg (x := t • v +ᵥ p₀) (y := y), dist_nonneg (x := t₂ • v +ᵥ p₀) (y := y)]

private lemma collinear_param {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : Collinear ℝ S) :
    ∃ p₀ v : EuclideanSpace ℝ (Fin 2), ∀ p ∈ S, ∃ r : ℝ, p = r • v +ᵥ p₀ :=
  (collinear_iff_exists_forall_eq_smul_vadd (k := ℝ) S).mp hS

private lemma collinear_dist_filter_card_le_two
    {L : Finset (EuclideanSpace ℝ (Fin 2))} (hL : Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2))))
    (x : EuclideanSpace ℝ (Fin 2)) (d : ℝ) :
    (L.filter (fun y => dist x y = d)).card ≤ 2 := by
  by_contra! hgt
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.mp hgt
  obtain ⟨p₀, v, hpv⟩ := collinear_param hL
  obtain ⟨hy₁L, hd₁⟩ := mem_filter.mp hy₁
  obtain ⟨hy₂L, hd₂⟩ := mem_filter.mp hy₂
  obtain ⟨hy₃L, hd₃⟩ := mem_filter.mp hy₃
  obtain ⟨t₁, ht₁⟩ := hpv y₁ hy₁L
  obtain ⟨t₂, ht₂⟩ := hpv y₂ hy₂L
  obtain ⟨t₃, ht₃⟩ := hpv y₃ hy₃L
  have hv : v ≠ 0 := by
    intro h0
    apply h₁₂
    rw [ht₁, ht₂, h0, smul_zero, smul_zero]
  have ht₁₂ : t₁ ≠ t₂ := fun h => h₁₂ (by rw [ht₁, ht₂, h])
  have ht₁₃ : t₁ ≠ t₃ := fun h => h₁₃ (by rw [ht₁, ht₃, h])
  have ht₂₃ : t₂ ≠ t₃ := fun h => h₂₃ (by rw [ht₂, ht₃, h])
  set a₀ : ℝ := ‖v‖ ^ 2
  set b₀ : ℝ := 2 * @inner ℝ _ _ v (p₀ - x)
  set c₀ : ℝ := ‖p₀ - x‖ ^ 2
  have hq₁ : a₀ * t₁ ^ 2 + b₀ * t₁ + c₀ = d ^ 2 := by
    rw [← dist_sq_line, ← ht₁, dist_comm, hd₁]
  have hq₂ : a₀ * t₂ ^ 2 + b₀ * t₂ + c₀ = d ^ 2 := by
    rw [← dist_sq_line, ← ht₂, dist_comm, hd₂]
  have hq₃ : a₀ * t₃ ^ 2 + b₀ * t₃ + c₀ = d ^ 2 := by
    rw [← dist_sq_line, ← ht₃, dist_comm, hd₃]
  have hvpos : 0 < a₀ := by positivity
  have h12 : (t₁ - t₂) * (a₀ * (t₁ + t₂) + b₀) = 0 := by nlinarith only [hq₁, hq₂]
  have h13 : (t₁ - t₃) * (a₀ * (t₁ + t₃) + b₀) = 0 := by nlinarith only [hq₁, hq₃]
  have s12 : a₀ * (t₁ + t₂) + b₀ = 0 :=
    (mul_eq_zero.mp h12).resolve_left (sub_ne_zero.mpr ht₁₂)
  have s13 : a₀ * (t₁ + t₃) + b₀ = 0 :=
    (mul_eq_zero.mp h13).resolve_left (sub_ne_zero.mpr ht₁₃)
  have hdiff : a₀ * (t₂ - t₃) = 0 := by linarith only [s12, s13]
  exact (sub_ne_zero.mpr ht₂₃) ((mul_eq_zero.mp hdiff).resolve_left hvpos.ne')

private lemma collinear_endpoints
    {S : Finset (EuclideanSpace ℝ (Fin 2))} (hS : Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ E : Finset (EuclideanSpace ℝ (Fin 2)), E ⊆ S ∧ E.card ≤ 2 ∧
      ∀ x ∈ S, x ∉ E → ∀ y : EuclideanSpace ℝ (Fin 2), ∃ x' ∈ E, dist x y < dist x' y := by
  by_cases hcard : S.card ≤ 2
  · exact ⟨S, Subset.rfl, hcard, fun _ hx hnx => (hnx hx).elim⟩
  have hne : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨p₀, v, hpv⟩ := collinear_param hS
  have hv : v ≠ 0 := by
    intro h0
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    obtain ⟨ta, hta⟩ := hpv a ha
    obtain ⟨tb, htb⟩ := hpv b hb
    exact hab (by rw [hta, htb, h0, smul_zero, smul_zero])
  let t : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
    if h : p ∈ S then Classical.choose (hpv p h) else 0
  have ht_spec : ∀ p ∈ S, p = t p • v +ᵥ p₀ := fun p hp => by
    simp only [t, dif_pos hp]
    exact Classical.choose_spec (hpv p hp)
  obtain ⟨xmin, hxmin, hmin⟩ := S.exists_min_image t hne
  obtain ⟨xmax, hxmax, hmax⟩ := S.exists_max_image t hne
  refine ⟨{xmin, xmax}, ?_, card_le_two, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hxmin
    · exact (mem_singleton.mp hz) ▸ hxmax
  · intro x hx hnx y
    have hne_min : x ≠ xmin := fun h => hnx (by simp [h])
    have hne_max : x ≠ xmax := fun h => hnx (by simp [h])
    have ht_lt_min : t xmin < t x :=
      lt_of_le_of_ne (hmin x hx) (fun h => hne_min (by rw [ht_spec x hx, ht_spec xmin hxmin, h]))
    have ht_lt_max : t x < t xmax :=
      lt_of_le_of_ne (hmax x hx) (fun h => hne_max (by rw [ht_spec x hx, ht_spec xmax hxmax, h]))
    have hsc := strict_convex_dist (p₀ := p₀) (y := y) hv ht_lt_min ht_lt_max
    rw [← ht_spec x hx, ← ht_spec xmin hxmin, ← ht_spec xmax hxmax] at hsc
    rcases hsc with h | h
    · exact ⟨xmin, by simp, h⟩
    · exact ⟨xmax, by simp, h⟩

private lemma filter_dist_card_le
    {A : Finset (EuclideanSpace ℝ (Fin 2))}
    {C : Finset (Finset (EuclideanSpace ℝ (Fin 2)))}
    (hcov : A ⊆ C.biUnion id)
    (hcol : ∀ L ∈ C, Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2))))
    (x : EuclideanSpace ℝ (Fin 2)) (d : ℝ) :
    (A.filter (fun y => dist x y = d)).card ≤ 2 * C.card := by
  have hsub : A.filter (fun y => dist x y = d) ⊆
      C.biUnion (fun L => L.filter (fun y => dist x y = d)) := by
    intro y hy
    obtain ⟨hyA, hdy⟩ := mem_filter.mp hy
    obtain ⟨L, hLC, hyL⟩ := mem_biUnion.mp (hcov hyA)
    exact mem_biUnion.mpr ⟨L, hLC, mem_filter.mpr ⟨hyL, hdy⟩⟩
  calc
    (A.filter (fun y => dist x y = d)).card
        ≤ (C.biUnion (fun L => L.filter (fun y => dist x y = d))).card := card_le_card hsub
    _ ≤ ∑ L ∈ C, (L.filter (fun y => dist x y = d)).card := card_biUnion_le
    _ ≤ ∑ _L ∈ C, 2 := sum_le_sum fun L hLC => collinear_dist_filter_card_le_two (hcol L hLC) x d
    _ = 2 * C.card := by simp [mul_comm]

private lemma card_distances_ge_two
    {A : Finset (EuclideanSpace ℝ (Fin 2))}
    {C : Finset (Finset (EuclideanSpace ℝ (Fin 2)))}
    (hC : C.Nonempty) (hcov : A ⊆ C.biUnion id)
    (hcol : ∀ L ∈ C, Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2))))
    (hA : 4 * C.card ^ 2 ≤ A.card) :
    2 ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card := by
  have hm : 1 ≤ C.card := card_pos.mpr hC
  have hA4 : 4 ≤ A.card := by nlinarith
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < A.card)
  by_contra! hlt
  have hne : (A.offDiag.image (fun p => dist p.1 p.2)).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    exact ⟨dist a b, mem_image.mpr ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩⟩
  have hcard1 : (A.offDiag.image (fun p => dist p.1 p.2)).card = 1 := by
    have := card_pos.mpr hne
    omega
  obtain ⟨d, hd⟩ := card_eq_one.mp hcard1
  have hsub : A.erase x ⊆ A.filter (fun y => dist x y = d) := by
    intro y hy
    obtain ⟨hyx, hyA⟩ := mem_erase.mp hy
    have hmem : dist x y ∈ A.offDiag.image (fun p => dist p.1 p.2) :=
      mem_image.mpr ⟨(x, y), mem_offDiag.mpr ⟨hx, hyA, hyx.symm⟩, rfl⟩
    rw [hd, mem_singleton] at hmem
    exact mem_filter.mpr ⟨hyA, hmem⟩
  have hle1 : A.card - 1 ≤ (A.filter (fun y => dist x y = d)).card := by
    rw [← card_erase_of_mem hx]
    exact card_le_card hsub
  have hle2 := filter_dist_card_le hcov hcol x d
  have hstrict : 2 * C.card + 1 < 4 * C.card ^ 2 := by nlinarith
  omega

private lemma rare_of_cover_endpoints
    {A E : Finset (EuclideanSpace ℝ (Fin 2))}
    {C : Finset (Finset (EuclideanSpace ℝ (Fin 2)))}
    (hcov : A ⊆ C.biUnion id)
    (hcol : ∀ L ∈ C, Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2))))
    (hA : 4 * C.card ^ 2 ≤ A.card)
    (hEcard : E.card ≤ 2 * C.card)
    {d : ℝ} (hd : d ∈ A.offDiag.image (fun p => dist p.1 p.2))
    (htouch : ∀ p ∈ A.offDiag, dist p.1 p.2 = d → p.1 ∈ E ∨ p.2 ∈ E) :
    d ∈ rareDistances A := by
  rw [rareDistances, mem_filter]
  refine ⟨hd, ?_, ?_⟩
  · obtain ⟨⟨x, y⟩, hxy, hdxy⟩ := mem_image.mp hd
    obtain ⟨hxA, hyA, hne⟩ := mem_offDiag.mp hxy
    let P := A.offDiag.filter (fun p => dist p.1 p.2 = d)
    have h1 : (x, y) ∈ P := mem_filter.mpr ⟨mem_offDiag.mpr ⟨hxA, hyA, hne⟩, hdxy⟩
    have h2 : (y, x) ∈ P := mem_filter.mpr ⟨mem_offDiag.mpr ⟨hyA, hxA, hne.symm⟩, by
      rw [dist_comm]; exact hdxy⟩
    have hpair : ({(x, y), (y, x)} : Finset _) ⊆ P := by
      intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact h1
      · exact (mem_singleton.mp hp) ▸ h2
    have hne_pair : (x, y) ≠ (y, x) := fun h => hne (congrArg Prod.fst h)
    have hge2 : 2 ≤ P.card := by
      have := card_le_card hpair
      rwa [card_pair hne_pair] at this
    change 1 ≤ P.card / 2
    omega
  · let P := A.offDiag.filter (fun p => dist p.1 p.2 = d)
    let P₁ := P.filter (fun p => p.1 ∈ E)
    let P₂ := P.filter (fun p => p.2 ∈ E)
    have hPsub : P ⊆ P₁ ∪ P₂ := by
      intro p hp
      obtain ⟨hpO, hpd⟩ := mem_filter.mp hp
      rcases htouch p hpO hpd with h1 | h2
      · exact mem_union_left _ (mem_filter.mpr ⟨hp, h1⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hp, h2⟩)
    have hP2eq : P₂.card = P₁.card := by
      refine card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpP, hp2⟩ := mem_filter.mp hp
        obtain ⟨hpO, hpd⟩ := mem_filter.mp hpP
        obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hpO
        exact mem_filter.mpr
          ⟨mem_filter.mpr ⟨mem_offDiag.mpr ⟨h2, h1, hne.symm⟩, by rw [dist_comm]; exact hpd⟩, hp2⟩
      · intro a _ b _ hab
        ext <;> simp_all
      · intro q hq
        obtain ⟨hqP, hq1⟩ := mem_filter.mp hq
        obtain ⟨hqO, hqd⟩ := mem_filter.mp hqP
        obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hqO
        refine ⟨(q.2, q.1), mem_filter.mpr
          ⟨mem_filter.mpr ⟨mem_offDiag.mpr ⟨h2, h1, hne.symm⟩, by rw [dist_comm]; exact hqd⟩, hq1⟩,
          by ext <;> rfl⟩
    have hP_le : P.card ≤ 2 * P₁.card := by
      calc
        P.card ≤ (P₁ ∪ P₂).card := card_le_card hPsub
        _ ≤ P₁.card + P₂.card := card_union_le P₁ P₂
        _ = 2 * P₁.card := by omega
    have hP1sub : P₁ ⊆ E.biUnion (fun x => (A.filter (fun y => dist x y = d)).image (fun y => (x, y))) := by
      intro p hp
      obtain ⟨hpP, hp1⟩ := mem_filter.mp hp
      obtain ⟨hpO, hpd⟩ := mem_filter.mp hpP
      obtain ⟨_, hyA, _⟩ := mem_offDiag.mp hpO
      exact mem_biUnion.mpr ⟨p.1, hp1, mem_image.mpr ⟨p.2, mem_filter.mpr ⟨hyA, hpd⟩, rfl⟩⟩
    have hP1_le : P₁.card ≤ 4 * C.card ^ 2 := by
      calc
        P₁.card ≤ (E.biUnion (fun x => (A.filter (fun y => dist x y = d)).image (fun y => (x, y)))).card :=
          card_le_card hP1sub
        _ ≤ ∑ x ∈ E, ((A.filter (fun y => dist x y = d)).image (fun y => (x, y))).card :=
          card_biUnion_le
        _ ≤ ∑ x ∈ E, (A.filter (fun y => dist x y = d)).card :=
          sum_le_sum fun _ _ => card_image_le
        _ ≤ ∑ _x ∈ E, (2 * C.card) :=
          sum_le_sum fun x _ => filter_dist_card_le hcov hcol x d
        _ = E.card * (2 * C.card) := by simp
        _ ≤ (2 * C.card) * (2 * C.card) := Nat.mul_le_mul_right _ hEcard
        _ = 4 * C.card ^ 2 := by ring
    change P.card / 2 ≤ A.card
    omega

end Erdos132LineCover

theorem OMA.solution : OMA.R_erdos_132_R1_H1_R2.H2 := by
  intro A C hC hcov hcol hA
  have hEL : ∀ L ∈ C, ∃ E_L : Finset (EuclideanSpace ℝ (Fin 2)),
      E_L ⊆ A ∩ L ∧ E_L.card ≤ 2 ∧
      ∀ x ∈ A ∩ L, x ∉ E_L → ∀ y : EuclideanSpace ℝ (Fin 2), ∃ x' ∈ E_L, dist x y < dist x' y := by
    intro L hLC
    exact Erdos132LineCover.collinear_endpoints
      ((hcol L hLC).subset (by intro z hz; exact (mem_inter.mp hz).2))
  let EL : Finset (EuclideanSpace ℝ (Fin 2)) → Finset (EuclideanSpace ℝ (Fin 2)) :=
    fun L => if h : L ∈ C then Classical.choose (hEL L h) else ∅
  have hEL_sub : ∀ L ∈ C, EL L ⊆ A ∩ L := fun L h => by
    simp only [EL, dif_pos h]
    exact (Classical.choose_spec (hEL L h)).1
  have hEL_card : ∀ L ∈ C, (EL L).card ≤ 2 := fun L h => by
    simp only [EL, dif_pos h]
    exact (Classical.choose_spec (hEL L h)).2.1
  have hEL_strict : ∀ L ∈ C, ∀ x ∈ A ∩ L, x ∉ EL L → ∀ y : EuclideanSpace ℝ (Fin 2),
      ∃ x' ∈ EL L, dist x y < dist x' y := fun L h => by
    simp only [EL, dif_pos h]
    exact (Classical.choose_spec (hEL L h)).2.2
  let E := C.biUnion EL
  have hEA : E ⊆ A := by
    intro x hx
    obtain ⟨L, hLC, hxL⟩ := mem_biUnion.mp hx
    exact (mem_inter.mp (hEL_sub L hLC hxL)).1
  have hEcard : E.card ≤ 2 * C.card := by
    calc
      E.card ≤ ∑ L ∈ C, (EL L).card := card_biUnion_le
      _ ≤ ∑ _L ∈ C, 2 := sum_le_sum hEL_card
      _ = 2 * C.card := by simp [mul_comm]
  have hE_strict : ∀ x ∈ A, x ∉ E → ∀ y : EuclideanSpace ℝ (Fin 2),
      ∃ x' ∈ E, dist x y < dist x' y := by
    intro x hxA hnxE y
    obtain ⟨L, hLC, hxL⟩ := mem_biUnion.mp (hcov hxA)
    have hnxEL : x ∉ EL L := fun h => hnxE (mem_biUnion.mpr ⟨L, hLC, h⟩)
    obtain ⟨x', hx'EL, hlt⟩ := hEL_strict L hLC x (mem_inter.mpr ⟨hxA, hxL⟩) hnxEL y
    exact ⟨x', mem_biUnion.mpr ⟨L, hLC, hx'EL⟩, hlt⟩
  let D := A.offDiag.image (fun p => dist p.1 p.2)
  have hD2 : 2 ≤ D.card := Erdos132LineCover.card_distances_ge_two hC hcov hcol hA
  have hDne : D.Nonempty := card_pos.mp (by omega)
  let d₁ := D.max' hDne
  have hd₁ : d₁ ∈ D := max'_mem D hDne
  let D' := D.erase d₁
  have hD'ne : D'.Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hd₁]
    omega
  let d₂ := D'.max' hD'ne
  have hd₂' : d₂ ∈ D' := max'_mem D' hD'ne
  have hd₂ : d₂ ∈ D := (mem_erase.mp hd₂').2
  have hd₁₂ : d₁ ≠ d₂ := (mem_erase.mp hd₂').1.symm
  have hnot_both_out : ∀ p ∈ A.offDiag, p.1 ∉ E → p.2 ∉ E →
      dist p.1 p.2 ≠ d₁ ∧ dist p.1 p.2 ≠ d₂ := by
    intro ⟨x, y⟩ hxy hxE hyE
    obtain ⟨hxA, hyA, hne⟩ := mem_offDiag.mp hxy
    have hpos : 0 < dist x y := dist_pos.mpr hne
    obtain ⟨x', hx'E, hlt1⟩ := hE_strict x hxA hxE y
    obtain ⟨y', hy'E, hlt2⟩ := hE_strict y hyA hyE x'
    rw [dist_comm y x', dist_comm y' x'] at hlt2
    have hx'A : x' ∈ A := hEA hx'E
    have hy'A : y' ∈ A := hEA hy'E
    have hne1 : x' ≠ y := dist_pos.mp (hpos.trans hlt1)
    have hne2 : x' ≠ y' := dist_pos.mp ((hpos.trans hlt1).trans hlt2)
    have hmem1 : dist x' y ∈ D := mem_image.mpr ⟨(x', y), mem_offDiag.mpr ⟨hx'A, hyA, hne1⟩, rfl⟩
    have hmem2 : dist x' y' ∈ D := mem_image.mpr ⟨(x', y'), mem_offDiag.mpr ⟨hx'A, hy'A, hne2⟩, rfl⟩
    have hle2 : dist x' y' ≤ d₁ := le_max' D _ hmem2
    have hlt_d1 : dist x' y < d₁ := lt_of_lt_of_le hlt2 hle2
    have hmem1' : dist x' y ∈ D' := mem_erase.mpr ⟨hlt_d1.ne, hmem1⟩
    have hle_d2 : dist x' y ≤ d₂ := le_max' D' _ hmem1'
    exact ⟨(hlt1.trans hlt_d1).ne, (lt_of_lt_of_le hlt1 hle_d2).ne⟩
  have hr₁ : d₁ ∈ rareDistances A :=
    Erdos132LineCover.rare_of_cover_endpoints hcov hcol hA hEcard hd₁ (by
      intro p hp hpd
      by_contra h
      push Not at h
      exact (hnot_both_out p hp h.1 h.2).1 hpd)
  have hr₂ : d₂ ∈ rareDistances A :=
    Erdos132LineCover.rare_of_cover_endpoints hcov hcol hA hEcard hd₂ (by
      intro p hp hpd
      by_contra h
      push Not at h
      exact (hnot_both_out p hp h.1 h.2).2 hpd)
  have hsub : ({d₁, d₂} : Finset ℝ) ⊆ rareDistances A := by
    intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · exact hr₁
    · exact (mem_singleton.mp hd) ▸ hr₂
  have hcard := card_le_card hsub
  rwa [card_pair hd₁₂] at hcard
