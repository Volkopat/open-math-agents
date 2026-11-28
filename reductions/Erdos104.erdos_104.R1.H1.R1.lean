import OMAReductions.R_Erdos104_erdos_104_R1

/-!
# Reduction Erdos104.erdos_104.R1.H1.R1

Reduces `Erdos104.erdos_104.R1.H1` (exact-three non-diametral unit circles on arbitrary planar
point sets) to two localized, minimum-degree core statements inside the fixed compact box `[0, 6)²`:

1. **Two-point multiplicity bound**: any two distinct points of `ℝ²` lie on at most two unit
   circles, so every finite family `T` of exact-three unit circles on `P` satisfies
   `T.card ≤ P.card ^ 2` (reusing `RichIncidences.heavy_bound` from the parent reduction).
2. **Shifted `6 × 6` grid localization**: every unit circle fits strictly inside some half-open
   cell `[6i + tₓ, 6(i+1) + tₓ) × [6j + tᵧ, 6(j+1) + tᵧ)` for one of the 9 shifts
   `(tₓ, tᵧ) ∈ {0, 2, 4}²`. Translating each cell isometrically into `[0, 6)²` and using convexity
   `∑ n_c² ≤ (∑ n_c)²` reduces arbitrary planar point sets `P ⊆ ℝ²` to `P ⊆ [0, 6)²`.
3. **Iterative minimum-degree core extraction**: deleting points incident to fewer than `d`
   circles (along with their incident circles) preserves all three contacts of every surviving
   circle and produces a core `Q ⊆ [0, 6)²` where every `p ∈ Q` lies on at least `c * |Q|` circles.
4. **Chord-regime split**: partitions exact-three non-diametral unit circles on `Q ⊆ [0, 6)²` into
   well-spread triples (all pairwise contact distances `≥ 1/2`, `H1`) and short-chord triples
   (containing a pair of contacts at distance `< 1/2`, `H2`).
-/

namespace OMA.R_Erdos104_erdos_104_R1_H1_R1

open EuclideanGeometry Finset
open scoped EuclideanGeometry Classical

/-- Well-spread localized exact-3 non-diametral unit circles: no large finite point set in
`[0, 6)²` admits a finite family of exact-3 unit circles whose pairwise contact distances all
satisfy `1/2 ≤ dist a b` and `dist a b ≠ 2`, with every point incident to at least `c * |Q|`
circles. -/
def H1 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ Q : Finset ℝ², N ≤ Q.card →
    (∀ p ∈ Q, 0 ≤ p 0 ∧ p 0 < 6 ∧ 0 ≤ p 1 ∧ p 1 < 6) →
    ∀ T : Finset (Sphere ℝ²),
      (∀ s ∈ T, s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3 ∧
        (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → a ∈ s → b ∈ s → (1 / 2 : ℝ) ≤ dist a b ∧ dist a b ≠ 2)) →
      ¬ (∀ p ∈ Q, c * (Q.card : ℝ) ≤ ((T.filter (fun s => p ∈ s)).card : ℝ))

/-- Short-chord localized exact-3 non-diametral unit circles: same compact `[0, 6)²`
minimum-degree core statement for unit circles containing two contacts at distance `< 1/2`. -/
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ Q : Finset ℝ², N ≤ Q.card →
    (∀ p ∈ Q, 0 ≤ p 0 ∧ p 0 < 6 ∧ 0 ≤ p 1 ∧ p 1 < 6) →
    ∀ T : Finset (Sphere ℝ²),
      (∀ s ∈ T, s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3 ∧
        (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → a ∈ s → b ∈ s → dist a b ≠ 2) ∧
        (∃ a ∈ Q, ∃ b ∈ Q, a ≠ b ∧ a ∈ s ∧ b ∈ s ∧ dist a b < (1 / 2 : ℝ))) →
      ¬ (∀ p ∈ Q, c * (Q.card : ℝ) ≤ ((T.filter (fun s => p ∈ s)).card : ℝ))

namespace Erdos104Loc

theorem contacts_card (P : Finset ℝ²) (s : Sphere ℝ²) :
    (P.filter fun p => p ∈ s).card = {p ∈ (P : Set ℝ²) | p ∈ s}.ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp

theorem pair_circles_finite {a b : ℝ²} (hab : a ≠ b) :
    ({s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s}).Finite ∧
      ({s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s}).ncard ≤ 2 := by
  classical
  let A : Sphere ℝ² := ⟨a, 1⟩
  let B : Sphere ℝ² := ⟨b, 1⟩
  have hAB : A ≠ B := fun h => hab (congrArg Sphere.center h)
  have ha (s : Sphere ℝ²) (hs : s.radius = 1 ∧ a ∈ s ∧ b ∈ s) : s.center ∈ A :=
    mem_sphere'.mpr ((mem_sphere.mp hs.2.1).trans hs.1)
  have hb (s : Sphere ℝ²) (hs : s.radius = 1 ∧ a ∈ s ∧ b ∈ s) : s.center ∈ B :=
    mem_sphere'.mpr ((mem_sphere.mp hs.2.2).trans hs.1)
  have byCentre (s t : Sphere ℝ²) (hs : s.radius = 1 ∧ a ∈ s ∧ b ∈ s)
      (ht : t.radius = 1 ∧ a ∈ t ∧ b ∈ t) (h : s.center = t.center) : s = t := by
    rw [← Sphere.mk_center_radius s, ← Sphere.mk_center_radius t, h, hs.1, ht.1]
  by_cases hsub : ({s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s}).Subsingleton
  · have hone := (Set.ncard_le_one_iff hsub.finite).mpr (fun hs ht => hsub hs ht)
    exact ⟨hsub.finite, hone.trans (by decide)⟩
  obtain ⟨s, hs, t, ht, hst⟩ := Set.not_subsingleton_iff.mp hsub
  have hstc : s.center ≠ t.center := fun h => hst (byCentre s t hs ht h)
  have hsubset : {u : Sphere ℝ² | u.radius = 1 ∧ a ∈ u ∧ b ∈ u} ⊆ ({s, t} : Set (Sphere ℝ²)) := by
    intro u hu
    rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := ℝ²) (by simp) hAB hstc (ha s hs) (ha t ht) (ha u hu) (hb s hs) (hb t ht) (hb u hu)
      with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (byCentre u s hu hs h))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (byCentre u t hu ht h)))
  have hf : ({s, t} : Set (Sphere ℝ²)).Finite := Set.toFinite _
  refine ⟨hf.subset hsubset, ?_⟩
  exact (Set.ncard_le_ncard hsubset hf).trans (by rw [Set.ncard_pair hst])

theorem exact_circles_finite (P : Finset ℝ²) :
    ({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3}).Finite := by
  classical
  let block (p : ℝ² × ℝ²) : Finset (Sphere ℝ²) :=
    if h : p.1 ≠ p.2 then (pair_circles_finite h).1.toFinset else ∅
  refine (P.offDiag.biUnion block).finite_toSet.subset ?_
  intro s hs
  have hc : (P.filter fun p => p ∈ s).card = 3 := (contacts_card P s).trans hs.2
  have hd : 2 < (P.filter fun p => p ∈ s).card := by omega
  obtain ⟨a, b, _, ha, hb, _, hab, _, _⟩ := Finset.two_lt_card_iff.mp hd
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha'.1, hb'.1, hab⟩, ?_⟩
  have hpair : s ∈ {u : Sphere ℝ² | u.radius = 1 ∧ a ∈ u ∧ b ∈ u} := ⟨hs.1, ha'.2, hb'.2⟩
  simpa only [block, dif_pos hab, Set.Finite.mem_toFinset] using hpair

theorem exact_finset_card_le_sq (P : Finset ℝ²) (T : Finset (Sphere ℝ²))
    (hT : ∀ s ∈ T, s.radius = 1 ∧ (P.filter fun p => p ∈ s).card = 3) :
    T.card ≤ P.card ^ 2 := by
  classical
  have hheavy := OMA.R_Erdos104_erdos_104_R1.RichIncidences.heavy_bound P T
    (fun s => P.filter fun p => p ∈ s) 2 2
    (fun s _ => filter_subset _ _)
    (fun s hs => by have := (hT s hs).2; omega)
    (fun p hp => by
      have hne := (Finset.mem_offDiag.mp hp).2.2
      have hsub : (↑(T.filter fun c => p.1 ∈ P.filter (· ∈ c) ∧ p.2 ∈ P.filter (· ∈ c)) :
          Set (Sphere ℝ²)) ⊆ {s : Sphere ℝ² | s.radius = 1 ∧ p.1 ∈ s ∧ p.2 ∈ s} := by
        intro s hs
        obtain ⟨hsT, hm1, hm2⟩ := Finset.mem_filter.mp hs
        exact ⟨(hT s hsT).1, (Finset.mem_filter.mp hm1).2, (Finset.mem_filter.mp hm2).2⟩
      obtain ⟨hf, hbound⟩ := pair_circles_finite hne
      rw [← Set.ncard_coe_finset]
      exact (Set.ncard_le_ncard hsub hf).trans hbound)
  have hoff : P.offDiag.card ≤ P.card ^ 2 := by
    rw [Finset.offDiag_card, pow_two]; exact Nat.sub_le _ _
  omega

-- Iterative minimum-degree core extraction preserving all three contacts of every surviving circle.
theorem min_degree_core :
    ∀ (m : ℕ) (P : Finset ℝ²), P.card = m →
    ∀ (T : Finset (Sphere ℝ²)),
      (∀ s ∈ T, (P.filter fun p => p ∈ s).card = 3) →
      ∀ (d : ℝ), 0 ≤ d → d * (P.card : ℝ) < (T.card : ℝ) →
      ∃ Q ⊆ P, ∃ T' ⊆ T,
        (∀ s ∈ T', P.filter (fun p => p ∈ s) ⊆ Q) ∧
        (T.card : ℝ) - d * (P.card : ℝ) ≤ (T'.card : ℝ) ∧
        (∀ p ∈ Q, d ≤ ((T'.filter fun s => p ∈ s).card : ℝ)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro P hP T hT d hd hlt
    rw [hP] at hlt
    simp only [Nat.cast_zero, mul_zero] at hlt
    have hne : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast hlt)
    obtain ⟨s, hs⟩ := hne
    have h0 := hT s hs
    have hP0 : P = ∅ := Finset.card_eq_zero.mp hP
    rw [hP0] at h0
    simp at h0
  | succ m ih =>
    intro P hP T hT d hd hlt
    by_cases hall : ∀ p ∈ P, d ≤ ((T.filter fun s => p ∈ s).card : ℝ)
    · refine ⟨P, Subset.rfl, T, Subset.rfl, fun s _ => filter_subset _ _, ?_, hall⟩
      have : 0 ≤ d * (P.card : ℝ) := mul_nonneg hd (Nat.cast_nonneg _)
      linarith
    · push Not at hall
      obtain ⟨p, hpP, hdeg⟩ := hall
      let P1 := P.erase p
      let T1 := T.filter fun s => p ∉ s
      have hP1card : P1.card = m := by
        dsimp [P1]; rw [Finset.card_erase_of_mem hpP, hP]; omega
      have hfilt_eq : ∀ s ∈ T1, P1.filter (fun q => q ∈ s) = P.filter (fun q => q ∈ s) := by
        intro s hs
        have hps : p ∉ s := (Finset.mem_filter.mp hs).2
        ext q
        simp only [P1, Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨fun heq => hps (heq ▸ h.2), h.1⟩, h.2⟩⟩
      have hT1card : T1.card + (T.filter fun s => p ∈ s).card = T.card := by
        dsimp [T1]
        rw [add_comm]
        exact Finset.card_filter_add_card_filter_not (fun s => p ∈ s)
      have hPcast : (P.card : ℝ) = (P1.card : ℝ) + 1 := by
        rw [hP, hP1card]; push_cast; ring
      have hT1cast : (T.card : ℝ) - d * (P.card : ℝ) ≤ (T1.card : ℝ) - d * (P1.card : ℝ) := by
        have hsum : (T1.card : ℝ) + ((T.filter fun s => p ∈ s).card : ℝ) = (T.card : ℝ) := by
          exact_mod_cast hT1card
        rw [hPcast]
        linarith
      have hlt1 : d * (P1.card : ℝ) < (T1.card : ℝ) := by linarith
      obtain ⟨Q, hQP1, T', hT'T1, hsubQ, hcard', hmindeg⟩ :=
        ih P1 hP1card T1 (fun s hs => by rw [hfilt_eq s hs]; exact hT s (Finset.mem_filter.mp hs).1)
          d hd hlt1
      refine ⟨Q, hQP1.trans (Finset.erase_subset p P), T', hT'T1.trans (filter_subset _ _),
        fun s hs => ?_, hT1cast.trans hcard', hmindeg⟩
      rw [← hfilt_eq s (hT'T1 hs)]
      exact hsubQ s hs

-- Coordinate deviation on a unit circle: every point on a unit circle lies within 1 of center
-- in each coordinate.
theorem coord_diff_le_one {s : Sphere ℝ²} (hr : s.radius = 1) {p : ℝ²} (hp : p ∈ s) (j : Fin 2) :
    |p j - s.center j| ≤ 1 := by
  have hd : dist p s.center = 1 := (mem_sphere.mp hp).trans hr
  have h1 : ‖p j - s.center j‖ ≤ ‖p - s.center‖ := by
    simpa [PiLp.sub_apply] using PiLp.norm_apply_le (p - s.center) j
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (by rw [← dist_eq_norm, hd])

-- Every closed interval [x - 1, x + 1] lies strictly inside [6i + t, 6(i+1) + t) for some
-- shift t ∈ {0, 2, 4} and integer i.
theorem exists_shift_interval (x : ℝ) :
    ∃ t ∈ ({0, 2, 4} : Finset ℤ), ∃ i : ℤ,
      (6 * i + t : ℝ) ≤ x - 1 ∧ x + 1 < (6 * (i + 1) + t : ℝ) := by
  let k : ℤ := ⌊x - 1⌋
  let q : ℤ := k / 6
  let r : ℤ := k % 6
  have hqr : 6 * q + r = k := Int.mul_ediv_add_emod k 6
  have hr0 : 0 ≤ r := Int.emod_nonneg k (by decide)
  have hr6 : r < 6 := Int.emod_lt_of_pos k (by decide)
  have hk_le : (k : ℝ) ≤ x - 1 := Int.floor_le (x - 1)
  have hk_lt : x - 1 < (k : ℝ) + 1 := Int.lt_floor_add_one (x - 1)
  have hqr' : (6 : ℝ) * (q : ℝ) + (r : ℝ) = (k : ℝ) := by exact_mod_cast hqr
  by_cases h2 : r < 2
  · refine ⟨0, by decide, q, ?_, ?_⟩
    · have hr0' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
      push_cast; linarith
    · have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast (show r ≤ 1 by omega)
      push_cast; linarith
  · by_cases h4 : r < 4
    · refine ⟨2, by decide, q, ?_, ?_⟩
      · have hr2' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 2 ≤ r by omega)
        push_cast; linarith
      · have hr3' : (r : ℝ) ≤ 3 := by exact_mod_cast (show r ≤ 3 by omega)
        push_cast; linarith
    · refine ⟨4, by decide, q, ?_, ?_⟩
      · have hr4' : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 4 ≤ r by omega)
        push_cast; linarith
      · have hr5' : (r : ℝ) ≤ 5 := by exact_mod_cast (show r ≤ 5 by omega)
        push_cast; linarith

-- Convexity: ∑ x_i^2 ≤ (∑ x_i)^2 for natural numbers.
theorem sum_sq_le_sq_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat]
    have h1 : (f a + ∑ i ∈ t, f i) ^ 2 = f a ^ 2 + 2 * f a * ∑ i ∈ t, f i + (∑ i ∈ t, f i) ^ 2 := by
      ring
    omega

-- Translation into [0, 6)^2 preserves exact-3 non-diametral unit circle counts.
theorem translate_box_count (B : Finset ℝ²) (v : ℝ²)
    (hv : ∀ p ∈ B, v 0 ≤ p 0 ∧ p 0 < v 0 + 6 ∧ v 1 ≤ p 1 ∧ p 1 < v 1 + 6) :
    ∃ Q : Finset ℝ², Q.card = B.card ∧
      (∀ q ∈ Q, 0 ≤ q 0 ∧ q 0 < 6 ∧ 0 ≤ q 1 ∧ q 1 < 6) ∧
      ({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (B : Set ℝ²) | p ∈ s}.ncard = 3} \
        {s : Sphere ℝ² | s.radius = 1 ∧
          ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard =
      ({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3} \
        {s : Sphere ℝ² | s.radius = 1 ∧
          ∃ a ∈ Q, ∃ b ∈ Q, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard := by
  classical
  let τ : ℝ² ≃ ℝ² := Equiv.subRight v
  let Q : Finset ℝ² := B.image τ
  have hQcard : Q.card = B.card := Finset.card_image_of_injective B τ.injective
  have hQbox : ∀ q ∈ Q, 0 ≤ q 0 ∧ q 0 < 6 ∧ 0 ≤ q 1 ∧ q 1 < 6 := by
    intro q hq
    obtain ⟨p, hpB, rfl⟩ := Finset.mem_image.mp hq
    have hp := hv p hpB
    simp only [τ, Equiv.subRight_apply, PiLp.sub_apply]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  let φ : Sphere ℝ² ≃ Sphere ℝ² :=
    { toFun := fun s => ⟨s.center - v, s.radius⟩
      invFun := fun s => ⟨s.center + v, s.radius⟩
      left_inv := fun s => by cases s; simp
      right_inv := fun s => by cases s; simp }
  have hmem_iff (p : ℝ²) (s : Sphere ℝ²) : τ p ∈ φ s ↔ p ∈ s := by
    change dist (p - v) (s.center - v) = s.radius ↔ dist p s.center = s.radius
    rw [dist_sub_right]
  have hdist_eq (a b : ℝ²) : dist (τ a) (τ b) = dist a b := by
    simp only [τ, Equiv.subRight_apply, dist_sub_right]
  have hncard_eq (s : Sphere ℝ²) :
      {p ∈ (Q : Set ℝ²) | p ∈ φ s}.ncard = {p ∈ (B : Set ℝ²) | p ∈ s}.ncard := by
    rw [← contacts_card, ← contacts_card]
    have hfilt : Q.filter (fun q => q ∈ φ s) = (B.filter (fun p => p ∈ s)).image τ := by
      ext q
      simp only [Q, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p, hpB, rfl⟩, hqs⟩
        exact ⟨p, ⟨hpB, (hmem_iff p s).mp hqs⟩, rfl⟩
      · rintro ⟨p, ⟨hpB, hps⟩, rfl⟩
        exact ⟨⟨p, hpB, rfl⟩, (hmem_iff p s).mpr hps⟩
    rw [hfilt, Finset.card_image_of_injective _ τ.injective]
  let SB := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (B : Set ℝ²) | p ∈ s}.ncard = 3} \
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}
  let SQ := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3} \
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}
  have himage : φ '' SB = SQ := by
    ext t
    constructor
    · rintro ⟨s, ⟨⟨hr, h3⟩, hnd⟩, rfl⟩
      refine ⟨⟨hr, by rw [hncard_eq]; exact h3⟩, ?_⟩
      rintro ⟨_, a', ha', b', hb', hab', hd', has', hbs'⟩
      obtain ⟨a, haB, rfl⟩ := Finset.mem_image.mp ha'
      obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hb'
      exact hnd ⟨hr, a, haB, b, hbB, fun h => hab' (congrArg τ h),
        (hdist_eq a b).symm.trans hd', (hmem_iff a s).mp has', (hmem_iff b s).mp hbs'⟩
    · rintro ⟨⟨hr, h3⟩, hnd⟩
      refine ⟨φ.symm t, ⟨⟨hr, ?_⟩, ?_⟩, φ.apply_symm_apply t⟩
      · have := hncard_eq (φ.symm t)
        rw [φ.apply_symm_apply] at this
        linarith
      · rintro ⟨_, a, haB, b, hbB, hab, hd, has, hbs⟩
        have ha' : τ a ∈ Q := Finset.mem_image.mpr ⟨a, haB, rfl⟩
        have hb' : τ b ∈ Q := Finset.mem_image.mpr ⟨b, hbB, rfl⟩
        have has' : τ a ∈ t := by
          have := (hmem_iff a (φ.symm t)).mpr has; rwa [φ.apply_symm_apply] at this
        have hbs' : τ b ∈ t := by
          have := (hmem_iff b (φ.symm t)).mpr hbs; rwa [φ.apply_symm_apply] at this
        exact hnd ⟨hr, τ a, ha', τ b, hb', fun h => hab (τ.injective h),
          (hdist_eq a b).trans hd, has', hbs'⟩
  refine ⟨Q, hQcard, hQbox, ?_⟩
  change SB.ncard = SQ.ncard
  rw [← himage]
  exact (Set.ncard_image_of_injective SB φ.injective).symm

-- From H1 and H2, derive the localized bound inside [0, 6)^2.
theorem localized_bound (h1 : H1) (h2 : H2) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ Q : Finset ℝ², N0 ≤ Q.card →
      (∀ q ∈ Q, 0 ≤ q 0 ∧ q 0 < 6 ∧ 0 ≤ q 1 ∧ q 1 < 6) →
      (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3} \
        {s : Sphere ℝ² | s.radius = 1 ∧
          ∃ a ∈ Q, ∃ b ∈ Q, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard : ℝ) ≤
        δ * (Q.card : ℝ) ^ 2 := by
  classical
  intro δ hδ
  have hc : (0 : ℝ) < δ / 4 := by positivity
  obtain ⟨N1, hN1⟩ := h1 (δ / 4) hc
  obtain ⟨N2, hN2⟩ := h2 (δ / 4) hc
  let M : ℕ := max N1 N2
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((M : ℝ) / Real.sqrt (δ / 4))
  refine ⟨max 1 N0, fun Q hQcard hQbox => ?_⟩
  let S_all := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3} \
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}
  have hfin : S_all.Finite := (exact_circles_finite Q).subset Set.sdiff_subset
  let Tall : Finset (Sphere ℝ²) := hfin.toFinset
  have hTall_card : Tall.card = S_all.ncard := (Set.ncard_eq_toFinset_card S_all hfin).symm
  have hTall_mem : ∀ s ∈ Tall, s.radius = 1 ∧ (Q.filter fun p => p ∈ s).card = 3 ∧
      (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → a ∈ s → b ∈ s → dist a b ≠ 2) := by
    intro s hs
    have hs' : s ∈ S_all := hfin.mem_toFinset.mp hs
    refine ⟨hs'.1.1, by rw [contacts_card]; exact hs'.1.2, fun a ha b hb hab has hbs hd2 =>
      hs'.2 ⟨hs'.1.1, a, ha, b, hb, hab, hd2, has, hbs⟩⟩
  let Twide := Tall.filter fun s =>
    ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → a ∈ s → b ∈ s → (1 / 2 : ℝ) ≤ dist a b
  let Tshort := Tall.filter fun s =>
    ¬ (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → a ∈ s → b ∈ s → (1 / 2 : ℝ) ≤ dist a b)
  have hsplit : Twide.card + Tshort.card = Tall.card :=
    Finset.card_filter_add_card_filter_not _
  have hN0_sq : (M : ℝ) ^ 2 ≤ (δ / 4) * (Q.card : ℝ) ^ 2 := by
    have hsqrt_pos : 0 < Real.sqrt (δ / 4) := Real.sqrt_pos.mpr hc
    have hQge : (M : ℝ) / Real.sqrt (δ / 4) < (Q.card : ℝ) :=
      hN0.trans_le (by exact_mod_cast (le_max_right 1 N0).trans hQcard)
    have hMle : (M : ℝ) ≤ Real.sqrt (δ / 4) * (Q.card : ℝ) := by
      have := (div_lt_iff₀ hsqrt_pos).mp hQge
      linarith
    have hsq := mul_self_le_mul_self (Nat.cast_nonneg M) hMle
    calc (M : ℝ) ^ 2 = (M : ℝ) * (M : ℝ) := sq (M : ℝ)
      _ ≤ (Real.sqrt (δ / 4) * (Q.card : ℝ)) * (Real.sqrt (δ / 4) * (Q.card : ℝ)) := hsq
      _ = (Real.sqrt (δ / 4) * Real.sqrt (δ / 4)) * (Q.card : ℝ) ^ 2 := by ring
      _ = (δ / 4) * (Q.card : ℝ) ^ 2 := by rw [Real.mul_self_sqrt hc.le]
  have hwide : (Twide.card : ℝ) ≤ (δ / 2) * (Q.card : ℝ) ^ 2 := by
    by_contra hgt
    push Not at hgt
    let d : ℝ := (δ / 4) * (Q.card : ℝ)
    have hd : 0 ≤ d := by positivity
    have hlt : d * (Q.card : ℝ) < (Twide.card : ℝ) := by
      have : d * (Q.card : ℝ) = (δ / 4) * (Q.card : ℝ) ^ 2 := by dsimp [d]; ring
      nlinarith [sq_nonneg (Q.card : ℝ)]
    obtain ⟨Q', hQ'Q, T', hT'sub, hsubQ', hcard', hmindeg⟩ :=
      min_degree_core Q.card Q rfl Twide
        (fun s hs => (hTall_mem s (Finset.mem_filter.mp hs).1).2.1) d hd hlt
    have hT'low : (δ / 4) * (Q.card : ℝ) ^ 2 < (T'.card : ℝ) := by
      have : d * (Q.card : ℝ) = (δ / 4) * (Q.card : ℝ) ^ 2 := by dsimp [d]; ring
      linarith
    have hT'prop : ∀ s ∈ T', s.radius = 1 ∧ (Q'.filter fun p => p ∈ s).card = 3 := by
      intro s hs
      have hsW := hT'sub hs
      have hsAll := (Finset.mem_filter.mp hsW).1
      have heq : Q'.filter (fun p => p ∈ s) = Q.filter (fun p => p ∈ s) := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨hQ'Q h.1, h.2⟩, fun h => ⟨hsubQ' s hs (Finset.mem_filter.mpr h), h.2⟩⟩
      exact ⟨(hTall_mem s hsAll).1, by rw [heq]; exact (hTall_mem s hsAll).2.1⟩
    have hT'le : (T'.card : ℝ) ≤ (Q'.card : ℝ) ^ 2 := by
      exact_mod_cast exact_finset_card_le_sq Q' T' hT'prop
    have hQ'geM : M ≤ Q'.card := by
      have hsq : (M : ℝ) ^ 2 ≤ (Q'.card : ℝ) ^ 2 := by linarith
      have hle : (M : ℝ) ≤ (Q'.card : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) Q'.card]
      exact_mod_cast hle
    refine hN1 Q' ((le_max_left N1 N2).trans hQ'geM) (fun p hp => hQbox p (hQ'Q hp)) T' ?_ ?_
    · intro s hs
      have hsW := hT'sub hs
      have hsAll := (Finset.mem_filter.mp hsW).1
      refine ⟨(hT'prop s hs).1, by rw [← contacts_card]; exact (hT'prop s hs).2, ?_⟩
      intro a ha b hb hab has hbs
      exact ⟨(Finset.mem_filter.mp hsW).2 a (hQ'Q ha) b (hQ'Q hb) hab has hbs,
        (hTall_mem s hsAll).2.2 a (hQ'Q ha) b (hQ'Q hb) hab has hbs⟩
    · intro p hp
      have hleQ : (Q'.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast Finset.card_le_card hQ'Q
      have : (δ / 4) * (Q'.card : ℝ) ≤ d := mul_le_mul_of_nonneg_left hleQ hc.le
      exact this.trans (hmindeg p hp)
  have hshort : (Tshort.card : ℝ) ≤ (δ / 2) * (Q.card : ℝ) ^ 2 := by
    by_contra hgt
    push Not at hgt
    let d : ℝ := (δ / 4) * (Q.card : ℝ)
    have hd : 0 ≤ d := by positivity
    have hlt : d * (Q.card : ℝ) < (Tshort.card : ℝ) := by
      have : d * (Q.card : ℝ) = (δ / 4) * (Q.card : ℝ) ^ 2 := by dsimp [d]; ring
      nlinarith [sq_nonneg (Q.card : ℝ)]
    obtain ⟨Q', hQ'Q, T', hT'sub, hsubQ', hcard', hmindeg⟩ :=
      min_degree_core Q.card Q rfl Tshort
        (fun s hs => (hTall_mem s (Finset.mem_filter.mp hs).1).2.1) d hd hlt
    have hT'low : (δ / 4) * (Q.card : ℝ) ^ 2 < (T'.card : ℝ) := by
      have : d * (Q.card : ℝ) = (δ / 4) * (Q.card : ℝ) ^ 2 := by dsimp [d]; ring
      linarith
    have hT'prop : ∀ s ∈ T', s.radius = 1 ∧ (Q'.filter fun p => p ∈ s).card = 3 := by
      intro s hs
      have hsS := hT'sub hs
      have hsAll := (Finset.mem_filter.mp hsS).1
      have heq : Q'.filter (fun p => p ∈ s) = Q.filter (fun p => p ∈ s) := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨hQ'Q h.1, h.2⟩, fun h => ⟨hsubQ' s hs (Finset.mem_filter.mpr h), h.2⟩⟩
      exact ⟨(hTall_mem s hsAll).1, by rw [heq]; exact (hTall_mem s hsAll).2.1⟩
    have hT'le : (T'.card : ℝ) ≤ (Q'.card : ℝ) ^ 2 := by
      exact_mod_cast exact_finset_card_le_sq Q' T' hT'prop
    have hQ'geM : M ≤ Q'.card := by
      have hsq : (M : ℝ) ^ 2 ≤ (Q'.card : ℝ) ^ 2 := by linarith
      have hle : (M : ℝ) ≤ (Q'.card : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) Q'.card]
      exact_mod_cast hle
    refine hN2 Q' ((le_max_right N1 N2).trans hQ'geM) (fun p hp => hQbox p (hQ'Q hp)) T' ?_ ?_
    · intro s hs
      have hsS := hT'sub hs
      have hsAll := (Finset.mem_filter.mp hsS).1
      have hneg := (Finset.mem_filter.mp hsS).2
      push Not at hneg
      obtain ⟨a, haQ, b, hbQ, hab, has, hbs, hdist⟩ := hneg
      have haQ' : a ∈ Q' := hsubQ' s hs (Finset.mem_filter.mpr ⟨haQ, has⟩)
      have hbQ' : b ∈ Q' := hsubQ' s hs (Finset.mem_filter.mpr ⟨hbQ, hbs⟩)
      refine ⟨(hT'prop s hs).1, by rw [← contacts_card]; exact (hT'prop s hs).2,
        fun u hu v hv huv hus hvs => (hTall_mem s hsAll).2.2 u (hQ'Q hu) v (hQ'Q hv) huv hus hvs,
        a, haQ', b, hbQ', hab, has, hbs, hdist⟩
    · intro p hp
      have hleQ : (Q'.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast Finset.card_le_card hQ'Q
      have : (δ / 4) * (Q'.card : ℝ) ≤ d := mul_le_mul_of_nonneg_left hleQ hc.le
      exact this.trans (hmindeg p hp)
  have hsum : (S_all.ncard : ℝ) = (Twide.card : ℝ) + (Tshort.card : ℝ) := by
    rw [← hTall_card, ← hsplit]; push_cast; rfl
  change (S_all.ncard : ℝ) ≤ δ * (Q.card : ℝ) ^ 2
  linarith

-- For a fixed shift pair (tx, ty), cells partition P and capture all unit circles staying inside one cell.
theorem shift_partition_bound (P : Finset ℝ²) (tx ty : ℤ) (N0 : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hloc : ∀ Q : Finset ℝ², N0 ≤ Q.card →
      (∀ q ∈ Q, 0 ≤ q 0 ∧ q 0 < 6 ∧ 0 ≤ q 1 ∧ q 1 < 6) →
      (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (Q : Set ℝ²) | p ∈ s}.ncard = 3} \
        {s : Sphere ℝ² | s.radius = 1 ∧
          ∃ a ∈ Q, ∃ b ∈ Q, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard : ℝ) ≤
        δ * (Q.card : ℝ) ^ 2) :
    let cell : ℝ² → ℤ × ℤ := fun p => (⌊(p 0 - (tx : ℝ)) / 6⌋, ⌊(p 1 - (ty : ℝ)) / 6⌋)
    let cells := P.image cell
    (∑ c ∈ cells,
      (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ ((P.filter fun p => cell p = c) : Set ℝ²) | p ∈ s}.ncard = 3} \
        {s : Sphere ℝ² | s.radius = 1 ∧
          ∃ a ∈ P.filter (fun p => cell p = c), ∃ b ∈ P.filter (fun p => cell p = c),
            a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard : ℝ)) ≤
      (N0 : ℝ) * (P.card : ℝ) + δ * (P.card : ℝ) ^ 2 := by
  classical
  intro cell cells
  have hpart : ∑ c ∈ cells, (P.filter fun p => cell p = c).card = P.card :=
    Finset.sum_card_fiberwise_eq_card_filter P cells cell |>.trans (by
      rw [Finset.filter_true_of_mem (fun p hp => Finset.mem_image_of_mem cell hp)])
  have hcell_bound : ∀ c ∈ cells,
      (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ ((P.filter fun p => cell p = c) : Set ℝ²) | p ∈ s}.ncard = 3} \
        {s : Sphere ℝ² | s.radius = 1 ∧
          ∃ a ∈ P.filter (fun p => cell p = c), ∃ b ∈ P.filter (fun p => cell p = c),
            a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard : ℝ) ≤
      (N0 : ℝ) * ((P.filter fun p => cell p = c).card : ℝ) +
        δ * ((P.filter fun p => cell p = c).card : ℝ) ^ 2 := by
    intro c _
    let B := P.filter fun p => cell p = c
    let SB := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (B : Set ℝ²) | p ∈ s}.ncard = 3} \
      {s : Sphere ℝ² | s.radius = 1 ∧
        ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}
    change (SB.ncard : ℝ) ≤ (N0 : ℝ) * (B.card : ℝ) + δ * (B.card : ℝ) ^ 2
    by_cases hbig : N0 ≤ B.card
    · let v : ℝ² := WithLp.toLp 2 ![6 * (c.1 : ℝ) + (tx : ℝ), 6 * (c.2 : ℝ) + (ty : ℝ)]
      have hv : ∀ p ∈ B, v 0 ≤ p 0 ∧ p 0 < v 0 + 6 ∧ v 1 ≤ p 1 ∧ p 1 < v 1 + 6 := by
        intro p hp
        have hcp : cell p = c := (Finset.mem_filter.mp hp).2
        have h0 : ⌊(p 0 - (tx : ℝ)) / 6⌋ = c.1 := congrArg Prod.fst hcp
        have h1 : ⌊(p 1 - (ty : ℝ)) / 6⌋ = c.2 := congrArg Prod.snd hcp
        obtain ⟨hl0, hu0⟩ := Int.floor_eq_iff.mp h0
        obtain ⟨hl1, hu1⟩ := Int.floor_eq_iff.mp h1
        have hv0 : v 0 = 6 * (c.1 : ℝ) + (tx : ℝ) := rfl
        have hv1 : v 1 = 6 * (c.2 : ℝ) + (ty : ℝ) := rfl
        rw [hv0, hv1]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      obtain ⟨Q, hQcard, hQbox, hQnc⟩ := translate_box_count B v hv
      have hQb := hloc Q (hQcard.symm ▸ hbig) hQbox
      rw [← hQnc, hQcard] at hQb
      have hnn : 0 ≤ (N0 : ℝ) * (B.card : ℝ) := by positivity
      linarith
    · have hfinB : SB.Finite := (exact_circles_finite B).subset Set.sdiff_subset
      have hle_sq : SB.ncard ≤ B.card ^ 2 := by
        rw [Set.ncard_eq_toFinset_card SB hfinB]
        exact exact_finset_card_le_sq B hfinB.toFinset fun s hs => by
          have hs' := hfinB.mem_toFinset.mp hs
          exact ⟨hs'.1.1, by rw [contacts_card]; exact hs'.1.2⟩
      have hltN0 : B.card ≤ N0 := by omega
      have hle_lin : SB.ncard ≤ N0 * B.card :=
        hle_sq.trans (by rw [pow_two]; exact Nat.mul_le_mul_right B.card hltN0)
      have hle_r : (SB.ncard : ℝ) ≤ (N0 : ℝ) * (B.card : ℝ) := by exact_mod_cast hle_lin
      have hnn : 0 ≤ δ * (B.card : ℝ) ^ 2 := by positivity
      linarith
  have hsum_le := Finset.sum_le_sum hcell_bound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_le
  have hlin : ∑ c ∈ cells, ((P.filter fun p => cell p = c).card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast hpart
  have hsq : ∑ c ∈ cells, ((P.filter fun p => cell p = c).card : ℝ) ^ 2 ≤ (P.card : ℝ) ^ 2 := by
    have hnat := sum_sq_le_sq_sum cells (fun c => (P.filter fun p => cell p = c).card)
    rw [hpart] at hnat
    exact_mod_cast hnat
  rw [hlin] at hsum_le
  have hmul := mul_le_mul_of_nonneg_left hsq hδ.le
  linarith

end Erdos104Loc

theorem main : H1 → H2 → OMA.R_Erdos104_erdos_104_R1.H1 := by
  classical
  intro h1 h2 ε hε
  have hδ : (0 : ℝ) < ε / 18 := by positivity
  obtain ⟨N0, hloc⟩ := Erdos104Loc.localized_bound h1 h2 (ε / 18) hδ
  obtain ⟨M, hM⟩ := exists_nat_gt (18 * (N0 : ℝ) / ε)
  refine ⟨max 1 M, fun n hn P hPn => ?_⟩
  let S_all := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3} \
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}
  let shifts : Finset ℤ := {0, 2, 4}
  let shiftPairs : Finset (ℤ × ℤ) := shifts ×ˢ shifts
  let cell (t : ℤ × ℤ) (p : ℝ²) : ℤ × ℤ :=
    (⌊(p 0 - (t.1 : ℝ)) / 6⌋, ⌊(p 1 - (t.2 : ℝ)) / 6⌋)
  let cellCircles (t c : ℤ × ℤ) : Set (Sphere ℝ²) :=
    {s : Sphere ℝ² | s.radius = 1 ∧
      {p ∈ ((P.filter fun p => cell t p = c) : Set ℝ²) | p ∈ s}.ncard = 3} \
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P.filter (fun p => cell t p = c), ∃ b ∈ P.filter (fun p => cell t p = c),
        a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}
  have hcellFin (t c : ℤ × ℤ) : (cellCircles t c).Finite :=
    (Erdos104Loc.exact_circles_finite (P.filter fun p => cell t p = c)).subset Set.sdiff_subset
  let cellFin (t c : ℤ × ℤ) : Finset (Sphere ℝ²) := (hcellFin t c).toFinset
  let cover : Finset (Sphere ℝ²) :=
    shiftPairs.biUnion fun t => (P.image (cell t)).biUnion fun c => cellFin t c
  have hsub : S_all ⊆ (cover : Set (Sphere ℝ²)) := by
    intro s hs
    obtain ⟨⟨hr, h3⟩, hnd⟩ := hs
    obtain ⟨tx, htx, ix, hlx, hux⟩ := Erdos104Loc.exists_shift_interval (s.center 0)
    obtain ⟨ty, hty, iy, hly, huy⟩ := Erdos104Loc.exists_shift_interval (s.center 1)
    have ht_mem : (tx, ty) ∈ shiftPairs := Finset.mem_product.mpr ⟨htx, hty⟩
    have hall_in : ∀ p ∈ s, cell (tx, ty) p = (ix, iy) := by
      intro p hp
      have hx := abs_le.mp (Erdos104Loc.coord_diff_le_one hr hp 0)
      have hy := abs_le.mp (Erdos104Loc.coord_diff_le_one hr hp 1)
      apply Prod.ext
      · apply Int.floor_eq_iff.mpr
        constructor <;> linarith
      · apply Int.floor_eq_iff.mpr
        constructor <;> linarith
    have hPne : (P.filter fun p => p ∈ s).Nonempty := by
      apply Finset.card_pos.mp
      rw [Erdos104Loc.contacts_card, h3]; omega
    obtain ⟨p0, hp0⟩ := hPne
    have hp0P := (Finset.mem_filter.mp hp0).1
    have hp0s := (Finset.mem_filter.mp hp0).2
    have hc_mem : (ix, iy) ∈ P.image (cell (tx, ty)) :=
      Finset.mem_image.mpr ⟨p0, hp0P, hall_in p0 hp0s⟩
    have hset_eq : {p ∈ ((P.filter fun p => cell (tx, ty) p = (ix, iy)) : Set ℝ²) | p ∈ s} =
        {p ∈ (P : Set ℝ²) | p ∈ s} := by
      ext p
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hall_in p h.2⟩, h.2⟩⟩
    have hs_cell : s ∈ cellCircles (tx, ty) (ix, iy) := by
      refine ⟨⟨hr, by rw [hset_eq]; exact h3⟩, ?_⟩
      rintro ⟨_, a, ha, b, hb, hab, hd2, has, hbs⟩
      exact hnd ⟨hr, a, (Finset.mem_filter.mp ha).1, b, (Finset.mem_filter.mp hb).1,
        hab, hd2, has, hbs⟩
    rw [Finset.mem_coe]
    refine Finset.mem_biUnion.mpr ⟨(tx, ty), ht_mem, Finset.mem_biUnion.mpr ⟨(ix, iy), hc_mem, ?_⟩⟩
    exact Set.Finite.mem_toFinset _ |>.mpr hs_cell
  have hcard_le : S_all.ncard ≤
      ∑ t ∈ shiftPairs, ∑ c ∈ P.image (cell t), (cellCircles t c).ncard := by
    calc S_all.ncard
        ≤ (cover : Set (Sphere ℝ²)).ncard := Set.ncard_le_ncard hsub cover.finite_toSet
      _ = cover.card := Set.ncard_coe_finset cover
      _ ≤ ∑ t ∈ shiftPairs, ((P.image (cell t)).biUnion fun c => cellFin t c).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ t ∈ shiftPairs, ∑ c ∈ P.image (cell t), (cellFin t c).card :=
          Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ = ∑ t ∈ shiftPairs, ∑ c ∈ P.image (cell t), (cellCircles t c).ncard := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun c _ => ?_
          exact (Set.ncard_eq_toFinset_card _ _).symm
  have hcast : (S_all.ncard : ℝ) ≤
      ∑ t ∈ shiftPairs, ∑ c ∈ P.image (cell t), ((cellCircles t c).ncard : ℝ) := by
    exact_mod_cast hcard_le
  have hshift_each : ∀ t ∈ shiftPairs,
      (∑ c ∈ P.image (cell t), ((cellCircles t c).ncard : ℝ)) ≤
        (N0 : ℝ) * (P.card : ℝ) + (ε / 18) * (P.card : ℝ) ^ 2 := fun t _ =>
    Erdos104Loc.shift_partition_bound P t.1 t.2 N0 (ε / 18) hδ hloc
  have hsum9 : (∑ t ∈ shiftPairs, ∑ c ∈ P.image (cell t), ((cellCircles t c).ncard : ℝ)) ≤
      9 * ((N0 : ℝ) * (P.card : ℝ) + (ε / 18) * (P.card : ℝ) ^ 2) := by
    have h9 : (shiftPairs.card : ℝ) = 9 := by
      have : shiftPairs.card = 9 := by decide
      exact_mod_cast this
    calc _ ≤ ∑ _t ∈ shiftPairs, ((N0 : ℝ) * (P.card : ℝ) + (ε / 18) * (P.card : ℝ) ^ 2) :=
          Finset.sum_le_sum hshift_each
      _ = (shiftPairs.card : ℝ) * ((N0 : ℝ) * (P.card : ℝ) + (ε / 18) * (P.card : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 9 * ((N0 : ℝ) * (P.card : ℝ) + (ε / 18) * (P.card : ℝ) ^ 2) := by rw [h9]
  have hPn' : (P.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hPn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 M).trans hn))
  have h9N0 : 9 * (N0 : ℝ) ≤ (ε / 2) * (n : ℝ) := by
    have hlt : 18 * (N0 : ℝ) / ε < (n : ℝ) :=
      hM.trans_le (by exact_mod_cast (le_max_right 1 M).trans hn)
    have := (div_lt_iff₀ hε).mp hlt
    linarith
  have hsq : (P.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self (Nat.cast_nonneg _) hPn'
  have hstep1 : (N0 : ℝ) * (P.card : ℝ) ≤ (N0 : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hPn' (Nat.cast_nonneg N0)
  have hstep2 : (ε / 18) * (P.card : ℝ) ^ 2 ≤ (ε / 18) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hδ.le
  change (S_all.ncard : ℝ) ≤ ε * (n : ℝ) ^ 2
  calc (S_all.ncard : ℝ)
      ≤ 9 * ((N0 : ℝ) * (P.card : ℝ) + (ε / 18) * (P.card : ℝ) ^ 2) := hcast.trans hsum9
    _ ≤ 9 * ((N0 : ℝ) * (n : ℝ) + (ε / 18) * (n : ℝ) ^ 2) := by linarith
    _ = (9 * (N0 : ℝ)) * (n : ℝ) + (ε / 2) * (n : ℝ) ^ 2 := by ring
    _ ≤ ((ε / 2) * (n : ℝ)) * (n : ℝ) + (ε / 2) * (n : ℝ) ^ 2 := by
        nlinarith [hn_pos]
    _ = ε * (n : ℝ) ^ 2 := by ring

end OMA.R_Erdos104_erdos_104_R1_H1_R1
