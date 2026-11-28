import OMAReductions.R_Erdos211_erdos_211_variants_one_sixth_R1

/-! # Melchior's mean-multiplicity inequality

Draw the two lifts of each determined line and join consecutive lifts around each dual circle.
This planar graph has twice as many vertices as determined lines and twice as many edges as
point-line incidences. The planar edge bound thus gives the result. Credit: @JaviSoto. -/

/- # Euler's edge bound for simple graphs drawn by arcs in the plane

Split each arc into two vertex branches and a middle connector. Rounding the compact pieces
together to a fine square grid preserves their intersections and connectedness. This realizes
the graph as a minor of a finite grid subgraph. Discrete integration identifies grid circulations
with the differences of face potentials, a property preserved by contracting connected branch
sets. Rank-nullity and counting the nonzero entries of face boundaries give `E ≤ 3V`.
Credit: @JaviSoto. -/

section

/- Discretization of compact connected drawings by connected subgraphs of the square lattice. -/

open Set Filter Topology

namespace OMA.Grid652

/-- Integer lattice with the four axis-aligned unit steps. -/
def squareGrid : SimpleGraph (ℤ × ℤ) where
  Adj v w := (v.1 = w.1 ∧ |v.2 - w.2| = 1) ∨ (v.2 = w.2 ∧ |v.1 - w.1| = 1)
  symm := ⟨by
    intro v w h
    rcases h with ⟨h,k⟩ | ⟨h,k⟩
    · exact Or.inl ⟨h.symm, (abs_sub_comm _ _).trans k⟩
    · exact Or.inr ⟨h.symm, (abs_sub_comm _ _).trans k⟩⟩
  loopless := ⟨by intro v; simp⟩

noncomputable def snap (p : ℝ × ℝ) : ℤ × ℤ := (⌊p.1⌋, ⌊p.2⌋)

/-- The nine grid vertices centered on the lower-left corner of the unit square containing p. -/
def pixel (p : ℝ × ℝ) : Set (ℤ × ℤ) :=
  {v | |v.1 - (snap p).1| ≤ 1 ∧ |v.2 - (snap p).2| ≤ 1}

def raster (K : Set (ℝ × ℝ)) : Set (ℤ × ℤ) := {v | ∃ p ∈ K, v ∈ pixel p}

lemma snap_mem (p : ℝ × ℝ) : snap p ∈ pixel p := by simp [pixel]

lemma floor_close {a b : ℝ} (hab : |a - b| < 1) : |⌊a⌋ - ⌊b⌋| ≤ 1 := by
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hab
  have h₃ := Int.floor_le a
  have h₄ := Int.floor_le b
  have h₅ := Int.lt_floor_add_one a
  have h₆ := Int.lt_floor_add_one b
  have h₇ : (⌊a⌋ : ℝ) < (⌊b⌋ : ℝ) + 2 := by linarith
  have h₈ : (⌊b⌋ : ℝ) < (⌊a⌋ : ℝ) + 2 := by linarith
  have h₉ : ⌊a⌋ < ⌊b⌋ + 2 := by exact_mod_cast h₇
  have h₁₀ : ⌊b⌋ < ⌊a⌋ + 2 := by exact_mod_cast h₈
  rw [abs_le]
  omega

lemma snap_mem_of_close {p q : ℝ × ℝ} (h : dist q p < 1) : snap q ∈ pixel p := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at h
  exact ⟨floor_close h.1, floor_close h.2⟩

lemma pixel_reachable {S : Set (ℤ × ℤ)} {p : ℝ × ℝ} (hS : pixel p ⊆ S)
    {v : ℤ × ℤ} (hv : v ∈ pixel p) :
    (squareGrid.induce S).Reachable ⟨snap p, hS (snap_mem p)⟩ ⟨v, hS hv⟩ := by
  obtain ⟨hx,hy⟩ := hv
  let m : ℤ × ℤ := (v.1, (snap p).2)
  have hm : m ∈ pixel p := ⟨hx, by simp [m]⟩
  have h₁ : (squareGrid.induce S).Reachable ⟨snap p, hS (snap_mem p)⟩ ⟨m, hS hm⟩ := by
    by_cases h : v.1 = (snap p).1
    · have he : (⟨snap p, hS (snap_mem p)⟩ : S) = ⟨m, hS hm⟩ :=
        Subtype.ext (Prod.ext h.symm rfl)
      rw [he]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.induce_adj]
      apply Or.inr
      have hpos := abs_pos.mpr (sub_ne_zero.mpr h)
      exact ⟨rfl, by rw [abs_sub_comm]; change |v.1 - (snap p).1| = 1; omega⟩
  apply h₁.trans
  by_cases h : v.2 = (snap p).2
  · have he : (⟨m, hS hm⟩ : S) = ⟨v, hS ⟨hx,hy⟩⟩ := Subtype.ext (Prod.ext rfl h.symm)
    rw [he]
  · apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.induce_adj]
    apply Or.inl
    have hpos := abs_pos.mpr (sub_ne_zero.mpr h)
    exact ⟨rfl, by rw [abs_sub_comm]; change |v.2 - (snap p).2| = 1; omega⟩

lemma raster_preconnected {K : Set (ℝ × ℝ)} (hK : IsPreconnected K) :
    (squareGrid.induce (raster K)).Preconnected := by
  let toVertex (p : K) : raster K := ⟨snap p.val, p.val, p.property, snap_mem _⟩
  have sameComponent (p q : K) (h : dist q.val p.val < 1) :
      (squareGrid.induce (raster K)).Reachable (toVertex p) (toVertex q) :=
    pixel_reachable (S := raster K) (p := p.val) (fun _ hv => ⟨p.val, p.property,hv⟩)
      (snap_mem_of_close h)
  intro a b
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  let P (z : K) := (squareGrid.induce (raster K)).Reachable (toVertex ⟨x,hx⟩) (toVertex z)
  have hl : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro z
    filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < 1 by norm_num)] with w hw
    have h := sameComponent z w hw
    exact propext ⟨(·.trans h.symm), (·.trans h)⟩
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hxy : P ⟨y,hy⟩ := (hl.apply_eq_of_preconnectedSpace ⟨y,hy⟩ ⟨x,hx⟩).symm ▸
    SimpleGraph.Reachable.refl _
  exact (pixel_reachable (S := raster K) (p := x) (fun _ hv => ⟨x,hx,hv⟩) hax).symm.trans
    (hxy.trans (pixel_reachable (S := raster K) (p := y) (fun _ hv => ⟨y,hy,hv⟩) hby))

lemma raster_finite {K : Set (ℝ × ℝ)} (hK : IsCompact K) : (raster K).Finite := by
  obtain ⟨lx,hlx⟩ := (hK.image continuous_fst).bddBelow
  obtain ⟨ly,hly⟩ := (hK.image continuous_snd).bddBelow
  obtain ⟨ux,hux⟩ := (hK.image continuous_fst).bddAbove
  obtain ⟨uy,huy⟩ := (hK.image continuous_snd).bddAbove
  apply (Set.finite_Icc (⌊lx⌋ - 1, ⌊ly⌋ - 1) (⌊ux⌋ + 1, ⌊uy⌋ + 1)).subset
  rintro v ⟨p,hp,hx,hy⟩
  have ax' : ⌊lx⌋ ≤ ⌊p.1⌋ := Int.floor_mono (hlx ⟨p,hp,rfl⟩)
  have ay' : ⌊ly⌋ ≤ ⌊p.2⌋ := Int.floor_mono (hly ⟨p,hp,rfl⟩)
  have bx' : ⌊p.1⌋ ≤ ⌊ux⌋ := Int.floor_mono (hux ⟨p,hp,rfl⟩)
  have by'' : ⌊p.2⌋ ≤ ⌊uy⌋ := Int.floor_mono (huy ⟨p,hp,rfl⟩)
  change |v.1 - ⌊p.1⌋| ≤ 1 at hx
  change |v.2 - ⌊p.2⌋| ≤ 1 at hy
  rw [abs_le] at hx hy
  exact ⟨⟨by dsimp; omega, by dsimp; omega⟩, ⟨by dsimp; omega, by dsimp; omega⟩⟩

noncomputable def scale (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1/h, p.2/h)

lemma scale_continuous (h : ℝ) : Continuous (scale h) :=
  (continuous_fst.div_const h).prodMk (continuous_snd.div_const h)

def rasterAt (h : ℝ) (K : Set (ℝ × ℝ)) := raster (scale h '' K)

private lemma pixel_error {z : ℤ} {p h : ℝ} (hh : 0 < h) (hz : |z - ⌊p/h⌋| ≤ 1) :
    |h * z - p| < 2*h := by
  have h₁ := Int.floor_le (p/h)
  have h₂ := Int.lt_floor_add_one (p/h)
  obtain ⟨hx,hy⟩ := abs_le.mp hz
  have hx' : (-1 : ℝ) ≤ z - (⌊p/h⌋ : ℤ) := by exact_mod_cast hx
  have hy' : (z : ℝ) - (⌊p/h⌋ : ℤ) ≤ 1 := by exact_mod_cast hy
  have h₃ := (le_div_iff₀ hh).mp h₁
  have h₄ := (div_lt_iff₀ hh).mp h₂
  rw [abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hx' hh.le,
    mul_le_mul_of_nonneg_right hy' hh.le]

lemma rasterAt_thickening {z : ℤ × ℤ} {h : ℝ} {K : Set (ℝ × ℝ)}
    (hh : 0 < h) (hz : z ∈ rasterAt h K) :
    (h * z.1, h * z.2) ∈ Metric.thickening (2*h) K := by
  obtain ⟨_,⟨p,hp,rfl⟩,hx,hy⟩ := hz
  apply Metric.mem_thickening_iff.mpr
  refine ⟨p,hp,?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨pixel_error hh hx, pixel_error hh hy⟩

lemma eventually_rasterAt_disjoint_iff {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), Disjoint (rasterAt h K) (rasterAt h L) ↔ Disjoint K L := by
  by_cases hd : Disjoint K L
  · obtain ⟨r,hr,hsep⟩ := hd.exists_thickenings hK hL.isClosed
    have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < r/2 :=
      eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhr
    refine ⟨fun _ => hd,fun _ => Set.disjoint_left.mpr ?_⟩
    intro z hz hw
    have hlt : 2*h ≤ r := by linarith
    exact Set.disjoint_left.mp hsep
      (Metric.thickening_mono hlt _ (rasterAt_thickening hh hz))
      (Metric.thickening_mono hlt _ (rasterAt_thickening hh hw))
  · filter_upwards with h
    refine ⟨fun hgrid => ?_, fun hdis => (hd hdis).elim⟩
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp hgrid
      (show snap (scale h p) ∈ rasterAt h K from ⟨_,⟨p,hp,rfl⟩,snap_mem _⟩)
      (show snap (scale h p) ∈ rasterAt h L from ⟨_,⟨p,hq,rfl⟩,snap_mem _⟩)

/-- A finite family of compact connected plane sets admits finite connected lattice models
    with exactly the same intersection relation, and the mesh may be chosen arbitrarily fine. -/
theorem finite_grid_realization {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∀ i, (rasterAt h (K i)).Finite ∧ (squareGrid.induce (rasterAt h (K i))).Preconnected) ∧
      (∀ i j, Disjoint (rasterAt h (K i)) (rasterAt h (K j)) ↔ Disjoint (K i) (K j)) := by
  have pairs : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ i j, Disjoint (rasterAt h (K i)) (rasterAt h (K j)) ↔ Disjoint (K i) (K j) := by
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_rasterAt_disjoint_iff (hc i) (hc j)
  filter_upwards [pairs] with h hh
  exact ⟨fun i => ⟨raster_finite ((hc i).image (scale_continuous h)),
    raster_preconnected ((hp i).image _ (scale_continuous h).continuousOn)⟩, hh⟩

open scoped EuclideanGeometry

def coords (p : ℝ²) : ℝ × ℝ := (p 0, p 1)

lemma coords_injective : Function.Injective coords := by
  intro p q h
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma coords_continuous : Continuous coords :=
  (PiLp.continuous_apply 2 _ 0).prodMk (PiLp.continuous_apply 2 _ 1)

/-- Joint rasterization for the formal conjecture's Euclidean-space model, including empty sets. -/
theorem plane_grid_realization {ι : Type*} [Finite ι] (K : ι → Set ℝ²)
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    ∃ A : ι → Set (ℤ × ℤ),
      (∀ i, (A i).Finite ∧ (squareGrid.induce (A i)).Preconnected) ∧
      (∀ i j, Disjoint (A i) (A j) ↔ Disjoint (K i) (K j)) := by
  obtain ⟨h, h₁, h₂⟩ := (finite_grid_realization (fun i => coords '' K i)
    (fun i => (hc i).image coords_continuous)
    (fun i => (hp i).image _ coords_continuous.continuousOn)).exists
  exact ⟨_,h₁,fun i j => (h₂ i j).trans (Set.disjoint_image_iff coords_injective)⟩


end OMA.Grid652

/- Face potentials under deletion and contraction of finite directed networks. -/

open scoped BigOperators

namespace OMA.Grid652

variable {W V E J F : Type*}

noncomputable def atom (w : W) (u : W) : ℚ := by classical exact if w = u then 1 else 0

/-- Push a function of finite support forward, summing its coefficients over each fiber. -/
noncomputable def push [Fintype W] (f : W → V) : (W → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun z := ∑ w, z w • atom (f w)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.smul_sum, mul_smul]

lemma push_atom [Fintype W] (f : W → V) (w : W) : push f (atom w) = atom (f w) := by
  classical
  change (∑ u, (if w = u then (1 : ℚ) else 0) • atom (f u)) = _
  simp [ite_smul]

lemma push_comp [Fintype W] [Fintype V] {U : Type*} (f : W → V) (g : V → U)
    (z : W → ℚ) : push g (push f z) = push (g ∘ f) z := by
  change push g (∑ w, z w • atom (f w)) = _
  simp only [map_sum, map_smul, push_atom]
  rfl

lemma push_id [Fintype W] (z : W → ℚ) : push id z = z := by
  classical
  ext w
  simp [push, atom]

noncomputable def net [Fintype E] (s t : E → V) : (E → ℚ) →ₗ[ℚ] (V → ℚ) :=
  push t - push s

lemma net_atom [Fintype E] (s t : E → V) (e : E) : net s t (atom e) = atom (t e) - atom (s e) := by
  simp [net, push_atom]

lemma net_push [Fintype W] [Fintype E] (s t : E → W) (π : W → V) (z : E → ℚ) :
    push π (net s t z) = net (π ∘ s) (π ∘ t) z := by simp [net, map_sub, push_comp]

lemma net_sum [Fintype E] [Fintype J] (s t : E ⊕ J → W) (z : E → ℚ) (w : J → ℚ) :
    net s t (Sum.elim z w) =
      net (s ∘ Sum.inl) (t ∘ Sum.inl) z + net (s ∘ Sum.inr) (t ∘ Sum.inr) w := by
  simp [net, push, Fintype.sum_sum_type]
  abel

/-- An exact dual means the divergence-free flows are exactly the edge differences of
    face potentials. The face on either side need not be different. -/
def ExactDual [Fintype E] (s t : E → V) (l r : E → F) : Prop :=
  ∀ z : E → ℚ, net s t z = 0 ↔ ∃ c : F → ℚ, ∀ e, z e = c (l e) - c (r e)

/-- Connectedness of a fiber is needed only to route the difference of two unit sources
    along its internal edges. The equivalence closure of edge endpoint pairs suffices. -/
lemma atom_sub_mem_range_of_joined [Fintype J] (s t : J → W) {a b : W}
    (h : Relation.EqvGen (fun x y => ∃ j, s j = x ∧ t j = y) a b) :
    atom b - atom a ∈ LinearMap.range (net s t) := by
  induction h with
  | rel a b h =>
    obtain ⟨j,rfl,rfl⟩ := h
    exact ⟨atom j,net_atom s t j⟩
  | refl a => simp
  | symm a b _ ih => simpa using (LinearMap.range (net s t)).neg_mem ih
  | trans a b c _ _ ih₁ ih₂ =>
    convert (LinearMap.range (net s t)).add_mem ih₂ ih₁ using 1
    abel

lemma mem_internal_range [Fintype J] [Fintype W] [Fintype V] (s t : J → W)
    (π : W → V) (anchor : V → W)
    (joined : ∀ w, Relation.EqvGen (fun x y => ∃ j, s j = x ∧ t j = y) (anchor (π w)) w)
    {b : W → ℚ} (hb : push π b = 0) :
    b ∈ LinearMap.range (net s t) := by
  have h₁ : (∑ w, b w • (atom w - atom (anchor (π w)))) ∈ LinearMap.range (net s t) :=
    Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (atom_sub_mem_range_of_joined s t (joined w))
  have h₂ : push (anchor ∘ π) b = 0 := by rw [← push_comp, hb, map_zero]
  simp only [smul_sub, Finset.sum_sub_distrib] at h₁
  change push id b - push (anchor ∘ π) b ∈ _ at h₁
  simpa [push_id, h₂] using h₁

/-- Contract connected internal branch sets by forgetting their edges in the dual. -/
theorem exactDual_contract [Fintype E] [Fintype J] [Fintype W] [Fintype V]
    (s t : E ⊕ J → W) (l r : E ⊕ J → F) (hD : ExactDual s t l r)
    (π : W → V) (anchor : V → W) (internal : ∀ j : J, π (s (.inr j)) = π (t (.inr j)))
    (joined : ∀ w, Relation.EqvGen
      (fun x y => ∃ j : J, s (.inr j) = x ∧ t (.inr j) = y) (anchor (π w)) w) :
    ExactDual (π ∘ s ∘ Sum.inl) (π ∘ t ∘ Sum.inl) (l ∘ Sum.inl) (r ∘ Sum.inl) := by
  have collapsed (w : J → ℚ) : push π (net (s ∘ Sum.inr) (t ∘ Sum.inr) w) = 0 := by
    rw [net_push]
    have heq : π ∘ s ∘ Sum.inr = π ∘ t ∘ Sum.inr := funext internal
    simp [heq, net]
  intro z
  constructor
  · intro hz
    obtain ⟨w,hw⟩ := mem_internal_range (s ∘ Sum.inr) (t ∘ Sum.inr) π anchor joined
      (b := -net (s ∘ Sum.inl) (t ∘ Sum.inl) z) (by rw [map_neg, net_push, hz, neg_zero])
    have hfull : net s t (Sum.elim z w) = 0 := by rw [net_sum, hw, add_neg_cancel]
    obtain ⟨c,hc⟩ := (hD _).mp hfull
    exact ⟨c,fun e => hc (.inl e)⟩
  · rintro ⟨c,hc⟩
    let w (j : J) := c (l (.inr j)) - c (r (.inr j))
    have hfull : net s t (Sum.elim z w) = 0 :=
      (hD _).mpr ⟨c,fun e => by cases e with | inl e => exact hc e | inr j => rfl⟩
    have hh := congrArg (push π) hfull
    simpa only [net_sum, map_add, collapsed, add_zero, net_push, map_zero] using hh

abbrev GridPoint := ℤ × ℤ
abbrev GridEdge := GridPoint ⊕ GridPoint

/-- Each oriented edge is indexed by its head, with horizontal edges in the left summand. -/
def gridHead : GridEdge → GridPoint := Sum.elim id id
def gridTail : GridEdge → GridPoint :=
  Sum.elim (fun p => (p.1-1,p.2)) (fun p => (p.1,p.2-1))
def faceLeft : GridEdge → GridPoint :=
  Sum.elim id (fun p => (p.1+1,p.2))
def faceRight : GridEdge → GridPoint :=
  Sum.elim (fun p => (p.1,p.2+1)) id

/-- A discrete integral on all integer coordinates, based at zero. -/
def primitive (f : ℤ → ℚ) (x : ℤ) : ℚ :=
  x.inductionOn' 0 0 (fun i _ a => a + f i) (fun i _ a => a - f (i-1))

lemma primitive_zero (f : ℤ → ℚ) : primitive f 0 = 0 := Int.inductionOn'_self

lemma primitive_succ (f : ℤ → ℚ) (x : ℤ) : primitive f (x+1) = primitive f x + f x := by
  by_cases hx : 0 ≤ x
  · exact Int.inductionOn'_add_one hx
  · have he : primitive f (x+1-1) = primitive f (x+1) - f (x+1-1) :=
      Int.inductionOn'_sub_one (by omega : x+1 ≤ (0:ℤ))
    simp only [add_sub_cancel_right] at he
    linarith

lemma grid_integral (H V : ℤ → ℤ → ℚ)
    (hdiv : ∀ i j, H (i+1) j + V i (j+1) = H i j + V i j) :
    ∃ c : GridPoint → ℚ, (∀ i j, H i j = c (i,j) - c (i,j+1)) ∧
      (∀ i j, V i j = c (i+1,j) - c (i,j)) := by
  let c (p : GridPoint) := primitive (fun i => V i p.2) p.1 - primitive (H 0) p.2
  have hv (i j : ℤ) : c (i+1,j) = c (i,j) + V i j := by simp [c, primitive_succ]; ring
  refine ⟨c,?_,fun i j => by rw [hv]; ring⟩
  intro i j
  have step (i : ℤ) :
      (H i j = c (i,j) - c (i,j+1)) ↔ (H (i+1) j = c (i+1,j) - c (i+1,j+1)) := by
    rw [hv, hv]
    constructor <;> intro hh <;> linarith [hdiv i j]
  refine Int.inductionOn' i 0 ?_ (fun n _ => (step n).mp) ?_
  · simp [c,primitive_zero,primitive_succ]
  · intro n _ ih
    apply (step (n-1)).mpr
    simpa using ih

lemma push_inj_apply [Fintype E] (f : E → W) (hf : Function.Injective f) (z : E → ℚ) (e : E) :
    push f z (f e) = z e := by
  classical
  simp [push, atom, hf.eq_iff, mul_ite]

lemma push_outside [Fintype E] (f : E → W) (z : E → ℚ) (w : W) (hw : w ∉ Set.range f) :
    push f z w = 0 := by
  classical
  have hn : ∀ e, f e ≠ w := fun e he => hw ⟨e,he⟩
  simp [push,atom,hn]

private lemma head_atom (e : GridEdge) (i j : ℤ) :
    atom (gridHead e) (i,j) = atom e (.inl (i,j)) + atom e (.inr (i,j)) := by
  classical
  cases e with
  | inl p => by_cases h : p = (i,j) <;> simp [gridHead,atom,h]
  | inr p => by_cases h : p = (i,j) <;> simp [gridHead,atom,h]

private lemma tail_atom (e : GridEdge) (i j : ℤ) :
    atom (gridTail e) (i,j) = atom e (.inl (i+1,j)) + atom e (.inr (i,j+1)) := by
  classical
  rcases e with ⟨x,y⟩ | ⟨x,y⟩ <;> simp [gridTail,atom,Prod.mk.injEq,sub_eq_iff_eq_add]

lemma grid_net_apply [Fintype E] (key : E → GridEdge) (z : E → ℚ) (i j : ℤ) :
    net (gridTail ∘ key) (gridHead ∘ key) z (i,j) =
      (push key z (.inl (i,j)) + push key z (.inr (i,j))) -
      (push key z (.inl (i+1,j)) + push key z (.inr (i,j+1))) := by
  classical
  simp [net, push, head_atom, tail_atom, mul_add, Finset.sum_add_distrib]

def missing (key : E → GridEdge) (a b : GridPoint) : Prop :=
  ∃ d ∉ Set.range key, faceLeft d = a ∧ faceRight d = b

/-- Every finite subgraph of the infinite square lattice has an exact dual. Faces are
    obtained by identifying neighboring unit squares across all omitted grid edges. -/
theorem grid_exactDual [Fintype E] (key : E → GridEdge) (inj : Function.Injective key) :
    ExactDual (gridTail ∘ key) (gridHead ∘ key)
      (Quot.mk (missing key) ∘ faceLeft ∘ key) (Quot.mk (missing key) ∘ faceRight ∘ key) := by
  classical
  intro z
  let H (i j : ℤ) := push key z (.inl (i,j))
  let V (i j : ℤ) := push key z (.inr (i,j))
  have diviff : net (gridTail ∘ key) (gridHead ∘ key) z = 0 ↔
      ∀ i j, H (i+1) j + V i (j+1) = H i j + V i j := by
    constructor
    · intro hz i j
      have he := congrFun hz (i,j)
      rw [grid_net_apply] at he
      exact (sub_eq_zero.mp he).symm
    · intro he
      funext ⟨i,j⟩
      exact (grid_net_apply key z i j).trans (sub_eq_zero.mpr (he i j).symm)
  rw [diviff]
  constructor
  · intro hdiv
    obtain ⟨c,hH,hV⟩ := grid_integral H V hdiv
    have hgrad (e : GridEdge) : push key z e = c (faceLeft e) - c (faceRight e) := by
      rcases e with ⟨i,j⟩ | ⟨i,j⟩
      · exact hH i j
      · exact hV i j
    have compat : ∀ a b, missing key a b → c a = c b := by
      rintro _ _ ⟨e,he,rfl,rfl⟩
      exact sub_eq_zero.mp ((hgrad e).symm.trans (push_outside key z e he))
    exact ⟨Quot.lift c compat,fun e => (push_inj_apply key inj z e).symm.trans (hgrad (key e))⟩
  · rintro ⟨c,hc⟩
    let q := Quot.mk (missing key)
    have he (d : GridEdge) : push key z d = c (q (faceLeft d)) - c (q (faceRight d)) := by
      by_cases hd : d ∈ Set.range key
      · obtain ⟨e,rfl⟩ := hd
        exact (push_inj_apply key inj z e).trans (hc e)
      · have hq : q (faceLeft d) = q (faceRight d) := Quot.sound ⟨d,hd,rfl,rfl⟩
        simp [hq, push_outside key z d hd]
    intro i j
    dsimp only [H,V]
    rw [he,he,he,he]
    simp [faceLeft,faceRight]

end OMA.Grid652

/- A linear-algebraic Euler bound from the two faces on either side of an edge.
    Neither facial walks nor a choice of spanning trees are required. -/

open Set Matrix Module
open scoped BigOperators

namespace OMA.Grid652

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
variable {k : Type*} [Field k]

omit [Fintype V] in
/-- A nonzero circulation on a finite simple graph uses at least three edges. Both the
    ordinary oriented incidence matrix and the unsigned matrix over ZMod 2 satisfy this. -/
lemma circulation_support_card [DecidableEq k] (edge : E → Finset V)
    (two : ∀ e, (edge e).card = 2) (simple : Function.Injective edge)
    (M : Matrix V E k) (suppM : ∀ v e, M v e ≠ 0 ↔ v ∈ edge e)
    {z : E → k} (hne : z ≠ 0) (hcycle : M.mulVec z = 0) :
    3 ≤ (Finset.univ.filter fun e => z e ≠ 0).card := by
  classical
  let S := Finset.univ.filter fun e => z e ≠ 0
  have hs {e : E} : e ∈ S ↔ z e ≠ 0 := by simp [S]
  have another {e : E} (he : e ∈ S) {v : V} (hv : v ∈ edge e) :
      ∃ f ∈ S.erase e, v ∈ edge f := by
    by_contra! no
    have eq : (M.mulVec z) v = M v e * z e := by
      apply Finset.sum_eq_single e
      · intro f _ hfe
        by_cases hf : f ∈ S
        · have hvf := no f (Finset.mem_erase.mpr ⟨hfe,hf⟩)
          have hM : M v f = 0 := not_ne_iff.mp (fun hp => hvf ((suppM v f).mp hp))
          simp [hM]
        · have hz : z f = 0 := by simpa [S] using hf
          simp [hz]
      · simp
    have hzero : (M.mulVec z) v = 0 := congrFun hcycle v
    exact (mul_ne_zero ((suppM v e).mpr hv) (hs.mp he)) (eq.symm.trans hzero)
  by_contra! hcard
  have hz : ∃ e, z e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨e,he⟩ := hz
  have hem := hs.mpr he
  have hone : (S.erase e).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hem]
    change S.card < 3 at hcard
    omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [two]; decide : 0 < (edge e).card)
  obtain ⟨f,hf,_⟩ := another hem hv
  have sub : edge e ⊆ edge f := by
    intro w hw
    obtain ⟨g,hg,hwg⟩ := another hem hw
    exact (Finset.card_le_one.mp hone g hg f hf) ▸ hwg
  have heq : e = f := simple (Finset.eq_of_subset_of_card_le sub (by rw [two,two]))
  exact (Finset.mem_erase.mp hf).1 heq.symm

/-- Boundary of one dual face. Its value on a primal edge is determined by the two
    adjacent faces, which may coincide. -/
noncomputable def faceBoundary (l r : E → F) (f : F) (e : E) : k := by
  classical exact (if l e = f then 1 else 0) - (if r e = f then 1 else 0)

/-- Euler's weak edge bound for graphs whose cycle space is generated by edge differences
    of face potentials and whose individual face boundaries have zero divergence. -/
theorem euler_of_face_potentials (edge : E → Finset V) (two : ∀ e, (edge e).card = 2)
    (simple : Function.Injective edge) (M : Matrix V E k) (suppM : ∀ v e, M v e ≠ 0 ↔ v ∈ edge e)
    (l r : E → F) (hface : ∀ f, M.mulVec (faceBoundary l r f) = 0)
    (hfill : ∀ z : E → k, M.mulVec z = 0 → ∃ c : F → k, ∀ e, z e = c (l e) - c (r e)) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let B := faceBoundary (k := k) l r
  let A : Finset F := Finset.univ.filter fun f => B f ≠ 0
  have doubleCount : A.card • (3 : ℕ) ≤ (Finset.univ : Finset E).card • 2 := by
    apply Finset.card_nsmul_le_card_nsmul (fun f e => B f e ≠ 0)
    · intro f hf
      exact circulation_support_card edge two simple M suppM
        (Finset.mem_filter.mp hf).2 (hface f)
    · intro e _
      apply le_trans (Finset.card_le_card (t := {l e,r e}) ?_) Finset.card_le_two
      intro f hf
      by_contra! hn
      have hz := (Finset.mem_filter.mp hf).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      exact hz (by simp [B, faceBoundary, Ne.symm hn.1, Ne.symm hn.2])
  let column (f : A) := B f.val
  have hspan : LinearMap.ker M.mulVecLin ≤ Submodule.span k (Set.range column) := by
    intro z hz
    obtain ⟨c,hc⟩ := hfill z (by exact hz)
    have hcomb : z = ∑ f : F, c f • B f := by
      ext e
      rw [hc]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B, faceBoundary,
        mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
      simp
    rw [hcomb]
    apply Submodule.sum_mem
    intro f _
    by_cases hf : f ∈ A
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f,hf⟩,rfl⟩)
    · have hzero : B f = 0 := by simpa [A] using hf
      simp [hzero]
  have hker := (Submodule.finrank_mono hspan).trans (finrank_range_le_card (R := k) column)
  have hrange := (LinearMap.range M.mulVecLin).finrank_le
  have htotal := M.mulVecLin.finrank_range_add_finrank_ker
  simp only [finrank_pi, Fintype.card_coe] at hker hrange htotal
  have hcount : A.card * 3 ≤ Fintype.card E * 2 := by simpa using doubleCount
  omega

end OMA.Grid652

/- Every simple graph represented by disjoint connected branch sets in a finite square-grid
    subgraph has at most three times as many edges as vertices. -/

open Set Matrix Module

namespace OMA.Grid652

variable {W V E J F : Type*}

lemma exactDual_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (different : ∀ e, s e ≠ t e)
    (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (l r : E → F) (hD : ExactDual s t l r) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let D := Finset.univ.image l ∪ Finset.univ.image r
  let L (e : E) : D := ⟨l e,Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let R (e : E) : D := ⟨r e,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let M (v : V) (e : E) := atom (t e) v - atom (s e) v
  have eq (z : E → ℚ) : Matrix.mulVec M z = net s t z := by
    ext v
    simp [Matrix.mulVec,dotProduct,M,net,push,mul_comm,mul_sub,Finset.sum_sub_distrib]
  apply euler_of_face_potentials (fun e => ({s e,t e} : Finset V)) (fun e => by simp [different e])
    simple M _ L R
  · intro f
    rw [eq]
    apply (hD _).mpr
    refine ⟨fun p => atom p f.val,fun e => ?_⟩
    simp only [faceBoundary,atom]
    have h₁ : (L e = f) ↔ l e = f.val := Subtype.ext_iff
    have h₂ : (R e = f) ↔ r e = f.val := Subtype.ext_iff
    simp [h₁,h₂]
  · intro z hz
    obtain ⟨c,hc⟩ := (hD _).mp ((eq z).symm.trans hz)
    exact ⟨fun p => c p.val,hc⟩
  · intro v e
    by_cases h : s e = v
    · subst v
      simp [M,atom,(different e).symm]
    · by_cases h' : t e = v
      · subst v
        simp [M,atom,h]
      · simp [M,atom,h,h',Ne.symm h,Ne.symm h']

/-- Extending a finite network along an injective vertex map leaves its cycle space unchanged. -/
lemma injective_net [Fintype E] [Fintype W] (s t : E → W) (p : W → V)
    (hp : Function.Injective p) (z : E → ℚ) :
    net (p ∘ s) (p ∘ t) z = 0 ↔ net s t z = 0 := by
  rw [← net_push]
  refine ⟨fun h => funext fun w => ?_,fun h => by simp [h]⟩
  exact (push_inj_apply p hp _ w).symm.trans (congrFun h (p w))

/-- Exact planar edge bound for any simple grid minor: the finite network has one
    extra edge per desired graph edge and arbitrary connected internal branch edges. -/
theorem euler_grid_minor [DecidableEq V] [Fintype E] [Fintype J] [Fintype W] [Fintype V]
    (s t : E ⊕ J → W) (p : W → GridPoint) (hp : Function.Injective p)
    (key : E ⊕ J → GridEdge) (inj : Function.Injective key)
    (tail : gridTail ∘ key = p ∘ s) (head : gridHead ∘ key = p ∘ t)
    (π : W → V) (anchor : V → W)
    (internal : ∀ j : J, π (s (.inr j)) = π (t (.inr j)))
    (joined : ∀ w, Relation.EqvGen
      (fun x y => ∃ j : J, s (.inr j) = x ∧ t (.inr j) = y) (anchor (π w)) w)
    (different : ∀ e : E, π (s (.inl e)) ≠ π (t (.inl e)))
    (simple : Function.Injective (fun e : E => ({π (s (.inl e)),π (t (.inl e))} : Finset V))) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  let l := Quot.mk (missing key) ∘ faceLeft ∘ key
  let r := Quot.mk (missing key) ∘ faceRight ∘ key
  have hD : ExactDual s t l r := by
    intro z
    have hD := grid_exactDual key inj z
    rw [tail,head,injective_net s t p hp] at hD
    exact hD
  exact exactDual_bound _ _ different simple _ _ (exactDual_contract s t l r hD π anchor internal joined)

end OMA.Grid652

/- Turn a family of disjoint vertex patches and disjoint edge connectors into a grid minor. -/

open Set

namespace OMA.Grid652

variable {X V E : Type*}

/-- Follow a walk until it first touches the target, retaining its connected prefix. -/
lemma before_target (G : SimpleGraph X) {C T : Set X} {a b : C}
    (p : (G.induce C).Walk a b) (ha : a.val ∉ T) (hb : b.val ∈ T) :
    ∃ D : Set X, D ⊆ C ∧ a.val ∈ D ∧ Disjoint D T ∧ (G.induce D).Preconnected ∧
      ∃ x ∈ D, ∃ y ∈ T, G.Adj x y := by
  classical
  induction p with
  | nil => exact (ha hb).elim
  | @cons a u b au p ih =>
    by_cases hu : u.val ∈ T
    · refine ⟨{a.val},Set.singleton_subset_iff.mpr a.property,rfl,?_,?_,a.val,rfl,u.val,hu,au⟩
      · simpa using ha
      · intro x y
        have he : x = y := Subtype.ext (x.property.trans y.property.symm)
        rw [he]
    · obtain ⟨D,hDC,huD,hd,hc,tail⟩ := ih hu hb
      let S : Set X := {a.val,u.val}
      have aS : a.val ∈ S := by simp [S]
      have uS : u.val ∈ S := by simp [S]
      refine ⟨S ∪ D,Set.union_subset ?_ hDC, Or.inl aS,disjoint_union_left.mpr ⟨?_,hd⟩,?_,?_⟩
      · intro x hx
        rcases hx with rfl | h
        · exact a.property
        · exact h ▸ u.property
      · intro I hS hT x hx
        rcases hS hx with he | he
        · exact ha (he ▸ hT hx)
        · exact hu (he ▸ hT hx)
      · exact (G.induce_union_connected (G.induce_pair_connected_of_adj au).preconnected hc
          ⟨u.val,uS,huD⟩).preconnected
      · obtain ⟨x,hx,y,hy,hxy⟩ := tail
        exact ⟨x,Or.inr hx,y,hy,hxy⟩

lemma patches_reach {G : SimpleGraph X} {A B : Set X} (h : A ⊆ B)
    {x y : A} (p : (G.induce A).Reachable x y) :
    (G.induce B).Reachable ⟨x.val,h x.property⟩ ⟨y.val,h y.property⟩ := by
  exact p.map (⟨Set.inclusion h,fun {a b} ha => ha⟩ : G.induce A →g G.induce B)

/-- A bipartite incidence model whose connector patches meet only their two prescribed
    end patches can be refined to disjoint connected branch sets with a single adjacency
    for each edge. -/
theorem shrink_connectors [Finite E] (G : SimpleGraph X) (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (B : V → Set X) (C : E → Set X)
    (Bfin : ∀ v, (B v).Finite) (Cfin : ∀ e, (C e).Finite)
    (Bne : ∀ v, (B v).Nonempty) (Bconn : ∀ v, (G.induce (B v)).Preconnected)
    (Cconn : ∀ e, (G.induce (C e)).Preconnected)
    (BB : ∀ v w, v ≠ w → Disjoint (B v) (B w)) (CC : ∀ e f, e ≠ f → Disjoint (C e) (C f))
    (touch : ∀ e v, ¬Disjoint (C e) (B v) ↔ s e = v ∨ t e = v) :
    ∃ R : V → Set X, (∀ v, (R v).Finite ∧ (R v).Nonempty ∧ (G.induce (R v)).Preconnected) ∧
      (∀ v w, v ≠ w → Disjoint (R v) (R w)) ∧
      ∀ e, ∃ x ∈ R (s e), ∃ y ∈ R (t e), G.Adj x y := by
  classical
  have expandBranch (e : E) : ∃ D : Set X, D ⊆ C e ∧ (D ∩ B (s e)).Nonempty ∧
      Disjoint D (B (t e)) ∧ (G.induce D).Preconnected ∧ ∃ x ∈ D, ∃ y ∈ B (t e), G.Adj x y := by
    obtain ⟨x,hx,hxs⟩ := Set.not_disjoint_iff.mp ((touch e (s e)).mpr (Or.inl rfl))
    obtain ⟨y,hy,hyt⟩ := Set.not_disjoint_iff.mp ((touch e (t e)).mpr (Or.inr rfl))
    have hxt := Set.disjoint_left.mp (BB _ _ (hne e)) hxs
    obtain ⟨p⟩ := Cconn e ⟨x,hx⟩ ⟨y,hy⟩
    obtain ⟨D,hDC,hxD,hdt,hD,htouch⟩ := before_target G p hxt hyt
    exact ⟨D,hDC,⟨x,hxD,hxs⟩,hdt,hD,htouch⟩
  choose D sub inter avoid conn bridge using expandBranch
  let R (v : V) := B v ∪ ⋃ e : {e // s e = v}, D e.val
  have Bsub (v : V) : B v ⊆ R v := Set.subset_union_left
  have Dsub (e : E) : D e ⊆ R (s e) := fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨⟨e,rfl⟩,hx⟩)
  have avoid' (e : E) (v : V) (h : s e ≠ v) : Disjoint (D e) (B v) := by
    by_cases ht : t e = v
    · exact ht ▸ avoid e
    · apply Disjoint.mono_left (sub e)
      by_contra! hh
      exact ((touch e v).mp hh).elim h ht
  refine ⟨R,?_,?_,?_⟩
  · intro v
    refine ⟨(Bfin v).union (Set.finite_iUnion fun e => (Cfin e.val).subset (sub e.val)),
      (Bne v).mono (Bsub v),?_⟩
    obtain ⟨a,ha⟩ := Bne v
    have reaches (p : R v) : (G.induce (R v)).Reachable ⟨a,Bsub v ha⟩ p := by
      rcases p with ⟨p,hp | hp⟩
      · exact patches_reach (Bsub v) (Bconn v ⟨a,ha⟩ ⟨p,hp⟩)
      · obtain ⟨⟨e,rfl⟩,he⟩ := Set.mem_iUnion.mp hp
        obtain ⟨d,hd,hb⟩ := inter e
        exact (patches_reach (Bsub _) (Bconn _ ⟨a,ha⟩ ⟨d,hb⟩)).trans
          (patches_reach (Dsub e) (conn e ⟨d,hd⟩ ⟨p,he⟩))
    exact fun p q => (reaches p).symm.trans (reaches q)
  · intro v w hvw
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) (hy | hy)
    · exact Set.disjoint_left.mp (BB _ _ hvw) hx hy
    · obtain ⟨⟨e,he⟩,hy'⟩ := Set.mem_iUnion.mp hy
      exact Set.disjoint_left.mp (avoid' e v (he ▸ hvw.symm)) hy' hx
    · obtain ⟨⟨e,he⟩,hx'⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (avoid' e w (he ▸ hvw)) hx' hy
    · obtain ⟨⟨e,he⟩,hx'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨f,hf⟩,hy'⟩ := Set.mem_iUnion.mp hy
      have hef : e ≠ f := fun h => hvw (he.symm.trans ((congrArg s h).trans hf))
      exact Set.disjoint_left.mp (CC _ _ hef) (sub _ hx') (sub _ hy')
  · intro e
    obtain ⟨x,hx,y,hy,h⟩ := bridge e
    exact ⟨x,Dsub e hx,y,Bsub _ hy,h⟩

/-- An undirected grid adjacency has a canonical horizontal or vertical orientation. -/
lemma grid_arrow {x y : GridPoint} (h : squareGrid.Adj x y) :
    (∃ d, gridTail d = x ∧ gridHead d = y) ∨ (∃ d, gridTail d = y ∧ gridHead d = x) := by
  obtain ⟨i,j⟩ := x
  obtain ⟨k,m⟩ := y
  rcases h with ⟨h,hd⟩ | ⟨h,hd⟩
  · change i = k at h
    subst k
    change |j - m| = 1 at hd
    rcases abs_choice (j-m) with hab | hab
    · exact Or.inr ⟨.inr (i,j),Prod.ext rfl (by dsimp [gridTail]; omega),rfl⟩
    · exact Or.inl ⟨.inr (i,m),Prod.ext rfl (by dsimp [gridTail]; omega),rfl⟩
  · change j = m at h
    subst m
    change |i - k| = 1 at hd
    rcases abs_choice (i-k) with hab | hab
    · exact Or.inr ⟨.inl (i,j),Prod.ext (by dsimp [gridTail]; omega) rfl,rfl⟩
    · exact Or.inl ⟨.inl (k,j),Prod.ext (by dsimp [gridTail]; omega) rfl,rfl⟩

/-- Construct the finite grid minor from the branch-set formulation. The orientation of
    each selected bridge follows the canonical orientation of its lattice edge. -/
theorem grid_branch_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (R : V → Set GridPoint)
    (Rprop : ∀ v, (R v).Finite ∧ (R v).Nonempty ∧ (squareGrid.induce (R v)).Preconnected)
    (Rdis : ∀ v w, v ≠ w → Disjoint (R v) (R w))
    (bridge : ∀ e, ∃ x ∈ R (s e), ∃ y ∈ R (t e), squareGrid.Adj x y) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let (v : V) : Fintype (R v) := (Rprop v).1.fintype
  let W := (v : V) × R v
  let pos (w : W) : GridPoint := w.2.val
  have posinj : Function.Injective pos := by
    rintro ⟨v,x⟩ ⟨w,y⟩ he
    have hvw : v = w := by
      by_contra h
      exact Set.disjoint_left.mp (Rdis _ _ h) x.property ((show x.val = y.val from he) ▸ y.property)
    subst w
    exact congrArg (Sigma.mk v) (Subtype.ext he)
  have chooseBridge (e : E) : ∃ (a b : W) (d : GridEdge),
      (a.1 = s e ∧ b.1 = t e ∨ a.1 = t e ∧ b.1 = s e) ∧
      gridTail d = pos a ∧ gridHead d = pos b := by
    obtain ⟨x,hx,y,hy,hxy⟩ := bridge e
    rcases grid_arrow hxy with ⟨d,hd1,hd2⟩ | ⟨d,hd1,hd2⟩
    · exact ⟨⟨_,x,hx⟩,⟨_,y,hy⟩,d,Or.inl ⟨rfl,rfl⟩,hd1,hd2⟩
    · exact ⟨⟨_,y,hy⟩,⟨_,x,hx⟩,d,Or.inr ⟨rfl,rfl⟩,hd1,hd2⟩
  choose a b d owners tail head using chooseBridge
  have pairEq (e : E) : ({(a e).1,(b e).1} : Finset V) = {s e,t e} := by
    rcases owners e with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp [ha,hb]
    · rw [ha,hb,Finset.pair_comm]
  have distinct (e : E) : (a e).1 ≠ (b e).1 := by
    rcases owners e with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa [ha,hb] using hne e
    · simpa [ha,hb] using (hne e).symm
  let J := {p : W × W // p.1.1 = p.2.1 ∧ ∃ k, gridTail k = pos p.1 ∧ gridHead k = pos p.2}
  have hJ (j : J) := j.property.2
  choose d' jt jh using hJ
  let src : E ⊕ J → W := Sum.elim a (fun j => j.val.1)
  let dst : E ⊕ J → W := Sum.elim b (fun j => j.val.2)
  let key : E ⊕ J → GridEdge := Sum.elim d d'
  have T (k : E ⊕ J) : gridTail (key k) = pos (src k) := by
    rcases k with e | j
    · exact tail e
    · exact jt j
  have H (k : E ⊕ J) : gridHead (key k) = pos (dst k) := by
    rcases k with e | j
    · exact head e
    · exact jh j
  have inj : Function.Injective key := by
    intro k k' he
    have hs := posinj ((T k).symm.trans ((congrArg gridTail he).trans (T k')))
    have ht := posinj ((H k).symm.trans ((congrArg gridHead he).trans (H k')))
    rcases k with e | j <;> rcases k' with f | i
    · apply congrArg Sum.inl
      apply simple
      exact (pairEq e).symm.trans ((congrArg₂ (fun x y : W => ({x.1,y.1} : Finset V)) hs ht).trans
        (pairEq f))
    · exfalso
      exact distinct e ((congrArg Sigma.fst hs).trans (i.property.1.trans (congrArg Sigma.fst ht).symm))
    · exfalso
      exact distinct f ((congrArg Sigma.fst hs).symm.trans (j.property.1.trans (congrArg Sigma.fst ht)))
    · exact congrArg Sum.inr (Subtype.ext (Prod.ext hs ht))
  let anchor (v : V) : W := ⟨v, Classical.choose (Rprop v).2.1, Classical.choose_spec (Rprop v).2.1⟩
  let rel (x y : W) := ∃ j : J, src (.inr j) = x ∧ dst (.inr j) = y
  have step {v : V} {x y : R v} (adj : (squareGrid.induce (R v)).Adj x y) :
      Relation.EqvGen rel (⟨v,x⟩ : W) ⟨v,y⟩ := by
    rcases grid_arrow adj with h | h
    · exact .rel _ _ ⟨⟨(⟨v,x⟩,⟨v,y⟩),rfl,h⟩,rfl,rfl⟩
    · exact .symm _ _ (.rel _ _ ⟨⟨(⟨v,y⟩,⟨v,x⟩),rfl,h⟩,rfl,rfl⟩)
  have joins {v : V} {x y : R v} (p : (squareGrid.induce (R v)).Walk x y) :
      Relation.EqvGen rel (⟨v,x⟩ : W) ⟨v,y⟩ := by
    induction p with
    | nil => exact .refl _
    | cons adj _ ih => exact .trans _ _ _ (step adj) ih
  apply euler_grid_minor src dst pos posinj key inj (funext T) (funext H) Sigma.fst anchor
    (fun j => j.property.1) _ distinct
  · intro e f he
    exact simple ((pairEq e).symm.trans (he.trans (pairEq f)))
  · rintro ⟨v,w⟩
    obtain ⟨p⟩ := (Rprop v).2.2 (anchor v).2 w
    exact joins p

open scoped EuclideanGeometry

/-- The Euler edge bound directly in terms of disjoint compact connected Euclidean patches
    and disjoint compact connected edge corridors with the prescribed incidence relation. -/
theorem grid_patch_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (B : V → Set ℝ²) (C : E → Set ℝ²)
    (Bprop : ∀ v, (B v).Nonempty ∧ IsCompact (B v) ∧ IsPreconnected (B v))
    (Cprop : ∀ e, IsCompact (C e) ∧ IsPreconnected (C e))
    (BB : ∀ v w, v ≠ w → Disjoint (B v) (B w)) (CC : ∀ e f, e ≠ f → Disjoint (C e) (C f))
    (touch : ∀ e v, ¬Disjoint (C e) (B v) ↔ s e = v ∨ t e = v) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  let K : V ⊕ E → Set ℝ² := Sum.elim B C
  obtain ⟨A,info,dis⟩ := plane_grid_realization K
    (fun i => by cases i with | inl v => exact (Bprop v).2.1 | inr e => exact (Cprop e).1)
    (fun i => by cases i with | inl v => exact (Bprop v).2.2 | inr e => exact (Cprop e).2)
  have nonempty (v : V) : (A (.inl v)).Nonempty := by
    by_contra! hn
    have hD := (dis (.inl v) (.inl v)).mp (by simp [hn])
    exact (Bprop v).1.ne_empty (disjoint_self.mp hD)
  obtain ⟨R,hR,hdis,hbridge⟩ := shrink_connectors squareGrid s t hne (A ∘ Sum.inl) (A ∘ Sum.inr)
    (fun v => (info (.inl v)).1) (fun e => (info (.inr e)).1) nonempty
    (fun v => (info (.inl v)).2) (fun e => (info (.inr e)).2)
    (fun v w h => (dis _ _).mpr (BB v w h)) (fun e f h => (dis _ _).mpr (CC e f h))
    (fun e v => (not_congr (dis (.inr e) (.inl v))).trans (touch e v))
  exact grid_branch_bound s t hne simple R hR hdis hbridge

end OMA.Grid652

/- Splitting a finite plane drawing into disjoint vertex stars and the
middle thirds of its arcs, with exactly the original incidence relation. -/
namespace OMA.Grid652
open Set
open scoped EuclideanGeometry Classical

private noncomputable def loCut : unitInterval := ⟨1/3, by constructor <;> norm_num⟩
private noncomputable def hiCut : unitInterval := ⟨2/3, by constructor <;> norm_num⟩

private lemma cuts : (0 : unitInterval) < loCut ∧ loCut < hiCut ∧ hiCut < 1 := by
  change (0:ℝ) < 1/3 ∧ (1:ℝ)/3 < 2/3 ∧ (2:ℝ)/3 < 1
  norm_num

private structure DrawArc (Q : Finset ℝ²) where
  src : Q
  dst : Q
  path : Path (src : ℝ²) (dst : ℝ²)
  inj : Function.Injective path
  vertex : ∀ (v : Q), (v : ℝ²) ∈ range path → v = src ∨ v = dst

private def DrawArc.tip {Q} (d : DrawArc Q) : Bool → Q
  | false => d.src
  | true => d.dst

private def outerTimes : Bool → Set unitInterval
  | false => Icc 0 loCut
  | true => Icc hiCut 1

private def DrawArc.outer {Q} (d : DrawArc Q) (b : Bool) : Set ℝ² :=
  d.path '' outerTimes b

private def DrawArc.middle {Q} (d : DrawArc Q) : Set ℝ² :=
  d.path '' Icc loCut hiCut

private lemma DrawArc.outer_props {Q} (d : DrawArc Q) (b : Bool) :
    (d.tip b : ℝ²) ∈ d.outer b ∧ IsCompact (d.outer b) ∧ IsPreconnected (d.outer b) := by
  cases b
  · exact ⟨⟨0, ⟨le_rfl, cuts.1.le⟩, d.path.source⟩, isCompact_Icc.image d.path.continuous,
      isPreconnected_Icc.image _ d.path.continuous.continuousOn⟩
  · exact ⟨⟨1, ⟨cuts.2.2.le, le_rfl⟩, d.path.target⟩, isCompact_Icc.image d.path.continuous,
      isPreconnected_Icc.image _ d.path.continuous.continuousOn⟩

private lemma DrawArc.outer_vertex {Q} (d : DrawArc Q) (b : Bool) (v : Q)
    (h : (v : ℝ²) ∈ d.outer b) : v = d.tip b := by
  obtain ⟨t, ht, hv⟩ := h
  rcases d.vertex v ⟨t, hv⟩ with hx | hy
  · cases b
    · exact hx
    · have he : t = 0 := d.inj (hv.trans ((congrArg Subtype.val hx).trans d.path.source.symm))
      have hle : hiCut ≤ 0 := he ▸ ht.1
      exact ((cuts.1.trans cuts.2.1).not_ge hle).elim
  · cases b
    · have he : t = 1 := d.inj (hv.trans ((congrArg Subtype.val hy).trans d.path.target.symm))
      have hle : 1 ≤ loCut := he ▸ ht.2
      exact ((cuts.2.1.trans cuts.2.2).not_ge hle).elim
    · exact hy

private lemma DrawArc.middle_avoids {Q} (d : DrawArc Q) (v : Q) :
    (v : ℝ²) ∉ d.middle := by
  rintro ⟨t, ht, hv⟩
  rcases d.vertex v ⟨t, hv⟩ with hx | hy
  · have he : t = 0 := d.inj (hv.trans ((congrArg Subtype.val hx).trans d.path.source.symm))
    exact cuts.1.not_ge (he ▸ ht.1)
  · have he : t = 1 := d.inj (hv.trans ((congrArg Subtype.val hy).trans d.path.target.symm))
    exact cuts.2.2.not_ge (he ▸ ht.2)

private lemma DrawArc.side_unique {Q} (d : DrawArc Q) {b c : Bool} {z : ℝ²}
    (hb : z ∈ d.outer b) (hc : z ∈ d.outer c) : b = c := by
  obtain ⟨t, ht, rfl⟩ := hb
  obtain ⟨u, hu, he⟩ := hc
  have := d.inj he
  subst u
  cases b <;> cases c
  · rfl
  · exact (cuts.2.1.not_ge (le_trans hu.1 ht.2)).elim
  · exact (cuts.2.1.not_ge (le_trans ht.1 hu.2)).elim
  · rfl

private lemma DrawArc.middle_meets {Q} (d : DrawArc Q) (b : Bool) :
    (d.middle ∩ d.outer b).Nonempty := by
  cases b
  · exact ⟨d.path loCut, ⟨loCut, ⟨le_rfl, cuts.2.1.le⟩, rfl⟩,
      ⟨loCut, ⟨cuts.1.le, le_rfl⟩, rfl⟩⟩
  · exact ⟨d.path hiCut, ⟨hiCut, ⟨cuts.2.1.le, le_rfl⟩, rfl⟩,
      ⟨hiCut, ⟨le_rfl, cuts.2.2.le⟩, rfl⟩⟩

/-- Each branch set consists of its vertex and the adjacent outer thirds. Each
connector is a middle third. The compact pieces can then be rasterized jointly. -/
theorem split_drawing (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
    (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²)
    (hd : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (hcross : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆
      Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) :
    ∃ (B : S → Set ℝ²) (C : E → Set ℝ²),
      (∀ v, (B v).Nonempty ∧ IsCompact (B v) ∧ IsPreconnected (B v)) ∧
      (∀ e, IsCompact (C e) ∧ IsPreconnected (C e)) ∧
      (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ e f, e ≠ f → Disjoint (C e) (C f)) ∧
      (∀ e v, ¬ Disjoint (C e) (B v) ↔ v.val ∈ edge e.val) := by
  classical
  have arcs (e : E) : ∃ d : DrawArc Q, edge e.val = {d.src,d.dst} ∧
      curve e.val = range d.path := by
    obtain ⟨x,y,_,hed,γ,hi,hγ,hv⟩ := hd e e.2
    refine ⟨⟨x,y,γ,hi,fun v h => ?_⟩, hed, hγ⟩
    simpa only [hed, Finset.mem_insert, Finset.mem_singleton] using hv v (hγ ▸ h)
  choose d ends full using arcs
  have crossing {e f : E} (hef : e ≠ f) {z : ℝ²} (he : z ∈ range (d e).path)
      (hf : z ∈ range (d f).path) : ∃ v : Q, (v : ℝ²) = z := by
    have h := hcross e e.2 f f.2 (fun h => hef (Subtype.ext h))
      ⟨(full e).symm ▸ he, (full f).symm ▸ hf⟩
    exact ⟨h.choose,h.choose_spec.2⟩
  let tips (v : S) := {p : E × Bool // (d p.1).tip p.2 = v.val}
  let part (v : S) : Option (tips v) → Set ℝ²
    | none => {(v.val : ℝ²)}
    | some p => (d p.val.1).outer p.val.2
  let B (v : S) := ⋃ k, part v k
  have piece (v : S) (k : Option (tips v)) :
      (v.val : ℝ²) ∈ part v k ∧ IsCompact (part v k) ∧ IsPreconnected (part v k) := by
    cases k with
    | none => exact ⟨mem_singleton _, isCompact_singleton, isPreconnected_singleton⟩
    | some p => simpa only [part, ← p.property] using (d p.val.1).outer_props p.val.2
  have memB {v : S} {z : ℝ²} (h : z ∈ B v) :
      z = (v.val : ℝ²) ∨ ∃ e b, (d e).tip b = v.val ∧ z ∈ (d e).outer b := by
    obtain ⟨k,hk⟩ := mem_iUnion.mp h
    cases k with
    | none => exact Or.inl hk
    | some p => exact Or.inr ⟨_,_,p.property,hk⟩
  have vertexB {v : S} (x : Q) (h : (x : ℝ²) ∈ B v) : x = v.val := by
    rcases memB h with hx | ⟨e,b,ht,hx⟩
    · exact Subtype.ext hx
    · exact ((d e).outer_vertex b x hx).trans ht
  have wholeOuter {e : E} {b z} (h : z ∈ (d e).outer b) : z ∈ range (d e).path :=
    ⟨h.choose, h.choose_spec.2⟩
  have wholeMiddle {e : E} {z} (h : z ∈ (d e).middle) : z ∈ range (d e).path :=
    ⟨h.choose, h.choose_spec.2⟩
  refine ⟨B,fun e => (d e).middle, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨⟨_,mem_iUnion.mpr ⟨none,(piece v none).1⟩⟩,
      isCompact_iUnion (fun k => (piece v k).2.1),
      isPreconnected_iUnion ⟨_,mem_iInter.mpr (fun k => (piece v k).1)⟩
        (fun k => (piece v k).2.2)⟩
  · exact fun e => ⟨isCompact_Icc.image (d e).path.continuous,
      isPreconnected_Icc.image _ (d e).path.continuous.continuousOn⟩
  · intro v w hne
    apply disjoint_left.mpr
    intro z hv hw
    apply hne
    apply Subtype.ext
    rcases memB hv with rfl | ⟨e,b,ht,he⟩
    · exact vertexB _ hw
    rcases memB hw with rfl | ⟨f,c,hu,hf⟩
    · exact (vertexB _ hv).symm
    by_cases h : e = f
    · subst f
      rw [← ht, ← hu, (d e).side_unique he hf]
    · obtain ⟨x,rfl⟩ := crossing h (wholeOuter he) (wholeOuter hf)
      exact (vertexB x hv).symm.trans (vertexB x hw)
  · intro e f hne
    apply disjoint_left.mpr
    intro z he hf
    obtain ⟨x,rfl⟩ := crossing hne (wholeMiddle he) (wholeMiddle hf)
    exact (d e).middle_avoids x he
  · intro e v
    constructor
    · intro hn
      obtain ⟨z, he, hv⟩ := not_disjoint_iff.mp hn
      rcases memB hv with rfl | ⟨f,b,ht,hf⟩
      · exact ((d e).middle_avoids _ he).elim
      by_cases h : e = f
      · subst f
        rw [ends, ← ht]
        cases b <;> simp [DrawArc.tip]
      · obtain ⟨x,rfl⟩ := crossing h (wholeMiddle he) (wholeOuter hf)
        exact ((d e).middle_avoids x he).elim
    · intro hv
      have side : ∃ b, (d e).tip b = v.val := by
        rw [ends, Finset.mem_insert, Finset.mem_singleton] at hv
        exact hv.elim (fun h => ⟨false,h.symm⟩) (fun h => ⟨true,h.symm⟩)
      obtain ⟨b,hb⟩ := side
      obtain ⟨z,hz,hleg⟩ := (d e).middle_meets b
      exact not_disjoint_iff.mpr ⟨z,hz,mem_iUnion.mpr ⟨some (⟨(e,b),hb⟩ : tips v),hleg⟩⟩

end OMA.Grid652

namespace OMA.Grid652
open Set
open scoped EuclideanGeometry Classical

theorem plane_drawing_bound (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
    (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²)
    (hd : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (inside : ∀ i ∈ E, edge i ⊆ S) (inj : Set.InjOn edge (E : Set ℕ))
    (cross : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆
      Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) : E.card ≤ 3 * S.card := by
  classical
  have ep (e : E) : ∃ s t : S, s ≠ t ∧ edge e.val = {s.val,t.val} := by
    obtain ⟨x,y,hne,hed,_⟩ := hd e e.2
    have hx := inside e e.2 (show x ∈ edge e.val by simp [hed])
    have hy := inside e e.2 (show y ∈ edge e.val by simp [hed])
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,fun h => hne (congrArg Subtype.val h),hed⟩
  choose s t hne hed using ep
  have simple : Function.Injective (fun e => ({s e,t e} : Finset S)) := by
    intro e f h
    apply Subtype.ext
    apply inj e.2 f.2
    rw [hed e, hed f]
    simpa using congrArg (Finset.image (Subtype.val : S → Q)) h
  obtain ⟨B,C,hB,hC,hBB,hCC,ht⟩ := split_drawing Q S E edge curve hd cross
  have touch (e : E) (v : S) : ¬ Disjoint (C e) (B v) ↔ s e = v ∨ t e = v := by
    rw [ht, hed e, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.imp (fun h => Subtype.ext h.symm) (fun h => Subtype.ext h.symm)
    · exact fun h => h.imp (fun h => congrArg Subtype.val h.symm) (fun h => congrArg Subtype.val h.symm)
  simpa using grid_patch_bound s t hne simple B C hB hC hBB hCC touch

end OMA.Grid652

end




/- # Consecutive arcs of an antipodally symmetric cyclic ordering -/

namespace OMA.Melchior211

open Finset
open scoped EuclideanGeometry Classical

structure LocalCycle (Q : Finset ℝ²) (F : ℝ → ℝ²) (opp : ℝ² → ℝ²) (m : ℕ) where
  edge : Fin (2*m) → Finset Q
  curve : Fin (2*m) → Set ℝ²
  drawn : ∀ i, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path x.val y.val, Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, v.val ∈ curve i → v ∈ edge i
  simple : Function.Injective edge
  on : ∀ i, curve i ⊆ Set.range F
  uniqueOutside : ∀ i j z, z ∉ Q → z ∈ curve i → z ∈ curve j → i=j
  notOpposite : ∀ i x y, x ∈ edge i → y ∈ edge i → x ≠ y → y.val ≠ opp x.val

private def remIndex {m : ℕ} (hm : 2 ≤ m) (i : ℤ) : Fin m :=
  ⟨(i % m).toNat, by
    have := Int.emod_nonneg i (show (m : ℤ) ≠ 0 by omega)
    have := Int.emod_lt_of_pos i (show (0 : ℤ) < m by omega)
    omega⟩

private theorem rem_val {m : ℕ} (hm : 2 ≤ m) (i : ℤ) :
    ((remIndex hm i).val : ℤ) = i%m :=
  Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))

private noncomputable def liftAngle {m : ℕ} (hm : 2 ≤ m) (θ : Fin m ↪o ℝ) (i : ℤ) : ℝ :=
  θ (remIndex hm i) + ((i / (m : ℤ) : ℤ) : ℝ) * Real.pi

private theorem lift_base {m : ℕ} (hm : 2 ≤ m) (θ : Fin m ↪o ℝ) (j : Fin m) :
    liftAngle hm θ j.val = θ j := by
  have hj : (j.val : ℤ) < m := by exact_mod_cast j.isLt
  have h0 : (0 : ℤ) ≤ j.val := by positivity
  have hr : remIndex hm (j.val : ℤ) = j := by
    apply Fin.ext
    exact_mod_cast (rem_val hm j.val).trans (Int.emod_eq_of_lt h0 hj)
  simp [liftAngle,hr,Int.ediv_eq_zero_of_lt h0 hj]

private theorem lift_shift {m : ℕ} (hm : 2 ≤ m) (θ : Fin m ↪o ℝ) (i k : ℤ) :
    liftAngle hm θ (i+k*m) = liftAngle hm θ i + (k : ℝ)*Real.pi := by
  have hne : (m : ℤ) ≠ 0 := by omega
  have hr : remIndex hm (i+k*m) = remIndex hm i := by
    apply Fin.ext
    simp [remIndex]
  simp only [liftAngle, hr, Int.add_mul_ediv_right _ _ hne, Int.cast_add]
  ring

private theorem lift_mono {m : ℕ} (hm : 2 ≤ m) (θ : Fin m ↪o ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 Real.pi) : StrictMono (liftAngle hm θ) := by
  intro i j hij
  have hq := Int.ediv_le_ediv (show 0 < (m : ℤ) by omega) hij.le
  rcases hq.lt_or_eq with hlt | heq
  · have hr : ((i/(m:ℤ) : ℤ) : ℝ) + 1 ≤ ((j/(m:ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (show i/(m:ℤ)+1 ≤ j/m by omega)
    have hmul := mul_le_mul_of_nonneg_right hr Real.pi_pos.le
    have hi := (hθ (remIndex hm i)).2
    have hj := (hθ (remIndex hm j)).1
    unfold liftAngle; linarith
  · have h1 := Int.emod_add_mul_ediv i (m:ℤ)
    have h2 := Int.emod_add_mul_ediv j (m:ℤ)
    rw [heq] at h1
    have hrem : remIndex hm i < remIndex hm j := by
      have hi := rem_val hm i
      have hj := rem_val hm j
      change (remIndex hm i).val < (remIndex hm j).val
      omega
    simpa [liftAngle,heq] using θ.strictMono hrem

private theorem classified {Q : Finset ℝ²} {F : ℝ → ℝ²} {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin m ↪o ℝ)
    (period : ∀ s t, F s = F t ↔ ∃ k : ℤ, s = t + (k : ℝ)*(2*Real.pi))
    (covers : ∀ t, F t ∈ Q ↔ ∃ j, F t = F (θ j) ∨ F t = F (θ j+Real.pi)) (t : ℝ) :
    F t ∈ Q ↔ ∃ j : ℤ, t = liftAngle hm θ j := by
  constructor
  · intro h
    obtain ⟨j,h|h⟩ := (covers t).mp h
    · obtain ⟨k,hk⟩ := (period _ _).mp h
      refine ⟨(j.val:ℤ)+(2*k)*(m:ℤ),?_⟩
      rw [lift_shift, lift_base,hk]; push_cast; ring
    · obtain ⟨k,hk⟩ := (period _ _).mp h
      refine ⟨(j.val:ℤ)+(2*k+1)*(m:ℤ),?_⟩
      rw [lift_shift, lift_base,hk]; push_cast; ring
  · rintro ⟨j,rfl⟩
    apply (covers _).mpr
    refine ⟨remIndex hm j,?_⟩
    set q := j/(m:ℤ)
    rcases Int.emod_two_eq_zero_or_one q with h|h
    · left
      apply (period _ _).mpr
      refine ⟨q/2,?_⟩
      have he : q = 2*(q/2) := by omega
      change θ (remIndex hm j) + (q:ℝ)*Real.pi = _
      nth_rw 1 [he]; push_cast; ring
    · right
      apply (period _ _).mpr
      refine ⟨q/2,?_⟩
      have he : q = 2*(q/2)+1 := by omega
      change θ (remIndex hm j) + (q:ℝ)*Real.pi = _
      nth_rw 1 [he]; push_cast; ring

private theorem period_small {F : ℝ → ℝ²}
    (period : ∀ s t, F s = F t ↔ ∃ k : ℤ, s = t + (k : ℝ)*(2*Real.pi))
    {s t : ℝ} (hl : t-2*Real.pi < s) (hr : s < t+2*Real.pi) (he : F s = F t) : s=t := by
  obtain ⟨k,hk⟩ := (period _ _).mp he
  rcases lt_trichotomy k 0 with h|rfl|h
  · have hneg : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hneg Real.pi_pos.le]
  · simpa using hk
  · have hpos : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith [mul_le_mul_of_nonneg_right hpos Real.pi_pos.le]

/-- Sort the half-circle angles periodically on the integer line. Consecutive
angles there give a cycle of 2m arcs after identifying full periods. -/
noncomputable def cycle (Q : Finset ℝ²) (F : ℝ → ℝ²) (opp : ℝ² → ℝ²) (m : ℕ)
    (hm : 2 ≤ m) (θ : Fin m ↪o ℝ) (hθ : ∀ i, θ i ∈ Set.Ico 0 Real.pi)
    (cont : Continuous F)
    (period : ∀ s t, F s = F t ↔ ∃ k : ℤ, s = t + (k : ℝ)*(2*Real.pi))
    (flip : ∀ t, F (t+Real.pi) = opp (F t))
    (covers : ∀ t, F t ∈ Q ↔ ∃ i, F t = F (θ i) ∨ F t = F (θ i+Real.pi)) :
    LocalCycle Q F opp m := by
  classical
  let L := liftAngle hm θ
  have mono : StrictMono L := lift_mono hm θ hθ
  have hshift (i k : ℤ) : L (i+k*m) = L i + (k : ℝ)*Real.pi := lift_shift hm θ i k
  have hclass (t : ℝ) : F t ∈ Q ↔ ∃ i : ℤ, t=L i := classified hm θ period covers t
  let v (i : ℤ) : Q := ⟨F (L i), (hclass _).mpr ⟨i,rfl⟩⟩
  have gap (i : ℤ) : L i < L (i+1) ∧ L (i+1) < L i + Real.pi := by
    refine ⟨mono (by omega),?_⟩
    have h := mono (show i+1 < i+1*(m:ℤ) by omega)
    rw [hshift] at h
    simpa only [Int.cast_one,one_mul] using h
  have inj_local {i j : ℤ} (hl : j-2*(m:ℤ) < i) (hr : i < j+2*(m:ℤ))
      (he : v i = v j) : i=j := by
    have hs := mono (show j+(-2)*(m:ℤ) < i by omega)
    have ht := mono hr
    rw [hshift] at hs ht
    push_cast at hs ht
    exact mono.injective (period_small period (by linarith) (by linarith) (congrArg Subtype.val he))
  let idx (i : Fin (2*m)) : ℤ := i.val
  have idxrange (i : Fin (2*m)) : 0 ≤ idx i ∧ idx i < 2*(m:ℤ) := by
    dsimp [idx]; exact ⟨by positivity, by exact_mod_cast i.isLt⟩
  let edge (i : Fin (2*m)) : Finset Q := {v (idx i), v (idx i+1)}
  let curve (i : Fin (2*m)) : Set ℝ² := F '' Set.Icc (L (idx i)) (L (idx i+1))
  have hne (i : ℤ) : v i ≠ v (i+1) := fun he => by
    have := inj_local (i:=i) (j:=i+1) (by omega) (by omega) he
    omega
  have unequal {i j : Fin (2*m)} (hij : i<j) (he : edge i = edge j) : False := by
    have hi := idxrange i
    have hj := idxrange j
    have hlt : idx i < idx j := by
      dsimp [idx]; exact_mod_cast (show i.val < j.val from hij)
    have hmem (x : Q) (h : x=v (idx i) ∨ x=v (idx i+1)) :
        x=v (idx j) ∨ x=v (idx j+1) := by
      have hx : x ∈ edge i := by simpa [edge] using h
      rw [he] at hx
      simpa [edge] using hx
    rcases hmem _ (Or.inl rfl) with h1 | h1
    · have := inj_local (by omega) (by omega) h1; omega
    rcases hmem _ (Or.inr rfl) with h2 | h2
    · have h2' := inj_local (by omega) (by omega) h2
      have := inj_local (i:=idx i) (j:=idx j+1) (by omega) (by omega) h1
      omega
    · exact (hne (idx i)) (h1.trans h2.symm)
  refine
    { edge := edge
      curve := curve
      drawn := ?_
      simple := ?_
      on := fun _ => Set.image_subset_range _ _
      uniqueOutside := ?_
      notOpposite := ?_ }
  · intro i
    let n := idx i
    have hg := gap n
    let γ : Path (v n).val (v (n+1)).val := (Path.segment (L n) (L (n+1))).map cont
    have hpath (u : unitInterval) : Path.segment (L n) (L (n+1)) u ∈ Set.Icc (L n) (L (n+1)) := by
      rw [← segment_eq_Icc hg.1.le, ← Path.range_segment]
      exact Set.mem_range_self _
    refine ⟨v n,v (n+1),hne n,rfl,γ,?_,?_,?_⟩
    · intro u w he
      apply Path.segment_injective_of_ne hg.1.ne
      have hu := hpath u
      have hw := hpath w
      exact period_small period (by linarith [hu.1,hw.2,Real.pi_pos])
        (by linarith [hu.2,hw.1,Real.pi_pos]) he
    · change F '' Set.Icc (L n) (L (n+1)) = Set.range (F ∘ Path.segment (L n) (L (n+1)))
      rw [Set.range_comp,Path.range_segment,segment_eq_Icc hg.1.le]
    · rintro z ⟨t,ht,he⟩
      obtain ⟨j,rfl⟩ := (hclass t).mp (he ▸ z.property)
      have hlow := mono.le_iff_le.mp ht.1
      have hhigh := mono.le_iff_le.mp ht.2
      have hcase : j = n ∨ j=n+1 := by change n ≤ j at hlow; change j ≤ n+1 at hhigh; omega
      rcases hcase with rfl | rfl
      · exact mem_insert_self _ _
          |> fun h => (show z = v n from Subtype.ext he.symm) ▸ h
      · have h : z = v (n+1) := Subtype.ext he.symm
        simp [edge,n,h]
  · intro i j he
    rcases lt_trichotomy i j with h|h|h
    · exact (unequal h he).elim
    · exact h
    · exact (unequal h he.symm).elim
  · rintro i j z hnot ⟨s,hs,hes⟩ ⟨t,ht,het⟩
    have interior {n : ℤ} {u : ℝ} (hu : u ∈ Set.Icc (L n) (L (n+1))) (he : F u=z) :
        L n < u ∧ u < L (n+1) := by
      refine ⟨lt_of_le_of_ne hu.1 (fun eq => ?_),lt_of_le_of_ne hu.2 (fun eq => ?_)⟩
      · apply hnot; rw [← he,← eq]; exact (v n).property
      · apply hnot; rw [← he,eq]; exact (v (n+1)).property
    obtain ⟨hs1,hs2⟩ := interior hs hes
    obtain ⟨ht1,ht2⟩ := interior ht het
    obtain ⟨k,hk⟩ := (period _ _).mp (hes.trans het.symm)
    let n := idx j + (2*k)*m
    have hsn : L n < s ∧ s < L (n+1) := by
      have e1 : L n = L (idx j) + ((2*k:ℤ):ℝ)*Real.pi := hshift _ _
      have e2 : L (n+1) = L (idx j+1) + ((2*k:ℤ):ℝ)*Real.pi := by
        dsimp [n]; rw [show idx j + (2*k)*m+1 = (idx j+1)+(2*k)*m by ring,hshift]
      rw [e1,e2]; push_cast; constructor <;> linarith
    have hnlt := mono.lt_iff_lt.mp (hs1.trans hsn.2)
    have hnlt' := mono.lt_iff_lt.mp (hsn.1.trans hs2)
    have hn : idx i = n := by omega
    have hvEq : v (idx i) = v (idx j) := by
      apply Subtype.ext
      apply (period _ _).mpr
      refine ⟨k,?_⟩
      rw [hn,show L n = _ from hshift (idx j) (2*k)]; push_cast; ring
    have hi := idxrange i
    have hj := idxrange j
    have eq := inj_local (by omega) (by omega) hvEq
    apply Fin.ext
    dsimp [idx] at eq
    exact_mod_cast eq
  · intro i x y hx hy hxy
    have hg := gap (idx i)
    have helper {s t : ℝ} (hl : t-Real.pi < s) (hr : s < t+Real.pi) : F s ≠ opp (F t) := by
      intro eh
      have h := period_small period (t:=t+Real.pi) (s:=s) (by linarith) (by linarith [Real.pi_pos])
        (eh.trans (flip t).symm)
      linarith
    simp only [edge,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact (hxy rfl).elim
    · apply helper <;> linarith [Real.pi_pos]
    · apply helper <;> linarith [Real.pi_pos]
    · exact (hxy rfl).elim

end OMA.Melchior211



/- An affine picture of the double cover of projective line duality.
On the ray with unit normal (cos t,sin t), the circle associated to p has
positive radius h+√(h²+1), where h is the signed projection of p. -/
namespace OMA.Melchior211
open Real Set Finset EuclideanGeometry Erdos211
open scoped Classical EuclideanGeometry

noncomputable def proj (t : ℝ) (p : ℝ²) : ℝ := p 0 * cos t + p 1 * sin t

private noncomputable def radius (h : ℝ) := h+√(h^2+1)

private lemma rad_pos (h : ℝ) : 0 < radius h := by
  have hh := Real.sq_sqrt (show 0 ≤ h^2+1 by positivity)
  have ht := Real.sqrt_nonneg (h^2+1)
  dsimp [radius]
  nlinarith

private lemma rad_quad (h : ℝ) : (radius h)^2 - 2*h*radius h = 1 := by
  dsimp [radius]
  nlinarith only [Real.sq_sqrt (show 0≤h^2+1 by positivity)]

private lemma rad_inj : Function.Injective radius := by
  intro x y h
  have hx := rad_quad x
  rw [h] at hx
  have h0 : (x-y)*radius y = 0 := by linarith [rad_quad y]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (rad_pos y).ne')

private lemma rad_neg (h : ℝ) : radius (-h)*radius h = 1 := by
  simp only [radius,neg_sq]
  nlinarith only [Real.sq_sqrt (show 0≤h^2+1 by positivity)]

noncomputable def ray (p : ℝ²) (t : ℝ) : ℝ² :=
  !₂[radius (proj t p)*cos t, radius (proj t p)*sin t]

private def normSq (z : ℝ²) : ℝ := z 0^2 + z 1^2

noncomputable def opp (z : ℝ²) : ℝ² := (-(normSq z)⁻¹) • z

lemma ray_continuous (p : ℝ²) : Continuous (ray p) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun t : ℝ => radius (proj t p)*_) <;>
    unfold radius proj <;> fun_prop

private lemma ray_sq (p : ℝ²) (t : ℝ) : normSq (ray p t) = radius (proj t p)^2 := by
  change (_ * cos t)^2 + (_ * sin t)^2 = _
  linear_combination (radius (proj t p))^2 * Real.sin_sq_add_cos_sq t

private lemma ray_components {p q : ℝ²} {s t : ℝ} (h : ray p s = ray q t) :
    cos s = cos t ∧ sin s = sin t ∧ proj s p = proj t q := by
  have hsq := congrArg normSq h
  simp only [ray_sq] at hsq
  have hrs : radius (proj s p) = radius (proj t q) := by
    nlinarith only [hsq, rad_pos (proj s p), rad_pos (proj t q)]
  have h₀ := congrArg (fun z : ℝ² => z 0) h
  have h₁ := congrArg (fun z : ℝ² => z 1) h
  change radius (proj s p)*cos s = radius (proj t q)*cos t at h₀
  change radius (proj s p)*sin s = radius (proj t q)*sin t at h₁
  rw [hrs] at h₀ h₁
  exact ⟨mul_left_cancel₀ (rad_pos _).ne' h₀,mul_left_cancel₀ (rad_pos _).ne' h₁,rad_inj hrs⟩

lemma ray_period (p : ℝ²) (s t : ℝ) :
    ray p s = ray p t ↔ ∃ k : ℤ, s = t + k*(2*π) := by
  constructor
  · intro h
    obtain ⟨hc,hs,-⟩ := ray_components h
    have he : cos (s-t)=1 := by rw [Real.cos_sub,hc,hs]; nlinarith only [Real.sin_sq_add_cos_sq t]
    obtain ⟨k,hk⟩ := (Real.cos_eq_one_iff _).mp he
    exact ⟨k,by linarith⟩
  · rintro ⟨k,rfl⟩
    simp only [ray,proj,Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]

lemma ray_opp (p : ℝ²) (t : ℝ) : ray p (t+π) = opp (ray p t) := by
  have ht : proj (t+π) p = -proj t p := by simp [proj,Real.cos_add_pi,Real.sin_add_pi]; ring
  have rr := rad_neg (proj t p)
  have r0 := (rad_pos (proj t p)).ne'
  ext i
  fin_cases i
  · change radius (proj (t+π) p)*cos (t+π)= -(normSq (ray p t))⁻¹*(radius (proj t p)*cos t)
    rw [ray_sq,ht,Real.cos_add_pi]
    field_simp [r0]
    linear_combination -(cos t)*rr
  · change radius (proj (t+π) p)*sin (t+π)= -(normSq (ray p t))⁻¹*(radius (proj t p)*sin t)
    rw [ray_sq,ht,Real.sin_add_pi]
    field_simp [r0]
    linear_combination -(sin t)*rr

private noncomputable def tangent (t : ℝ) : ℝ² := !₂[-sin t,cos t]

private noncomputable def lineAt (p : ℝ²) (t : ℝ) := line[ℝ,p,p+tangent t]

private lemma lineAt_is (p : ℝ²) (t : ℝ) : IsLine (lineAt p t) := by
  apply isLine_pair
  intro h
  have ht : tangent t = 0 := add_left_cancel (show p+tangent t=p+0 by simpa using h.symm)
  have h₀ := congrArg (fun z : ℝ² => z 0) ht
  have h₁ := congrArg (fun z : ℝ² => z 1) ht
  change -sin t = 0 at h₀
  change cos t = 0 at h₁
  nlinarith only [Real.sin_sq_add_cos_sq t,h₀,h₁]

private lemma lineAt_mem {p q : ℝ²} {t : ℝ} : q ∈ lineAt p t ↔ proj t q = proj t p := by
  have evaluate (a : ℝ) :
      (AffineMap.lineMap p (p+tangent t) a) 0 = p 0-a*sin t ∧
      (AffineMap.lineMap p (p+tangent t) a) 1 = p 1+a*cos t := by
    rw [AffineMap.lineMap_apply_module']
    constructor
    · change a*((p 0+ -sin t)-p 0)+p 0=_; ring
    · change a*((p 1+cos t)-p 1)+p 1=_; ring
  rw [lineAt,mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨a,rfl⟩
    simp only [proj,(evaluate a).1,(evaluate a).2]
    ring
  · intro h
    let a := -(q 0-p 0)*sin t+(q 1-p 1)*cos t
    refine ⟨a,?_⟩
    dsimp [proj] at h
    ext i
    fin_cases i
    · change (AffineMap.lineMap p (p+tangent t) a) 0=q 0
      rw [(evaluate a).1]
      dsimp [a]
      linear_combination (q 0-p 0)*(Real.sin_sq_add_cos_sq t) - cos t*h
    · change (AffineMap.lineMap p (p+tangent t) a) 1=q 1
      rw [(evaluate a).2]
      dsimp [a]
      linear_combination (q 1-p 1)*(Real.sin_sq_add_cos_sq t) - sin t*h

private lemma half_normal (p q : ℝ²) : ∃ t ∈ Ico 0 π, proj t p = proj t q := by
  let g (t : ℝ) := proj t p - proj t q
  have hc : Continuous g := by dsimp [g,proj]; fun_prop
  have he : g π = -g 0 := by simp [g,proj]; ring
  have hi : ∃ t ∈ Icc 0 π, g t = 0 := by
    rcases le_total (g 0) 0 with h|h
    · exact intermediate_value_Icc pi_pos.le hc.continuousOn ⟨h,by rw [he]; linarith⟩
    · exact intermediate_value_Icc' pi_pos.le hc.continuousOn ⟨by rw [he]; linarith,h⟩
  obtain ⟨t,ht,hg⟩ := hi
  rcases ht.2.eq_or_lt with e|e
  · exact ⟨0,⟨le_rfl,pi_pos⟩,sub_eq_zero.mp (show g 0=0 by rw [e,he] at hg; linarith)⟩
  · exact ⟨t,⟨ht.1,e⟩,sub_eq_zero.mp hg⟩

private lemma proj_flip (t : ℝ) (p : ℝ²) : proj (t+π) p = -proj t p := by
  simp [proj,Real.sin_add_pi,Real.cos_add_pi]; ring

private lemma ray_on {p q : ℝ²} {t : ℝ} :
    ray p t ∈ Set.range (ray q) ↔ proj t p = proj t q := by
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨hc,hs,h⟩ := ray_components hu
    unfold proj at h ⊢
    rw [hc,hs] at h
    exact h.symm
  · intro h
    exact ⟨t,by simp only [ray,h]⟩

private lemma two_rays {p : ℝ²} {s t : ℝ} (h : lineAt p s = lineAt p t) :
    ray p s = ray p t ∨ ray p s = ray p (t+π) := by
  have hv : p+tangent t ∈ lineAt p s := h.symm ▸ right_mem_affineSpan_pair ℝ p (p+tangent t)
  have he := lineAt_mem.mp hv
  change (p 0+ -sin t)*cos s + (p 1+cos t)*sin s = _ at he
  have hz : sin (s-t) = 0 := by rw [Real.sin_sub]; dsimp [proj] at he; linarith
  have hsq := Real.sin_sq_add_cos_sq (s-t)
  rw [hz,zero_pow (by decide : 2≠0),zero_add] at hsq
  rcases sq_eq_one_iff.mp hsq with hcos | hcos
  · left
    have hc : cos s = cos t := by
      calc cos s = cos ((s-t)+t) := congrArg cos (sub_add_cancel s t).symm
           _ = _ := by rw [Real.cos_add,hcos,hz]; ring
    have hs : sin s = sin t := by
      calc sin s = sin ((s-t)+t) := congrArg sin (sub_add_cancel s t).symm
           _ = _ := by rw [Real.sin_add,hcos,hz]; ring
    simp only [ray,proj,hc,hs]
  · right
    have hc : cos s = -cos t := by
      calc cos s = cos ((s-t)+t) := congrArg cos (sub_add_cancel s t).symm
           _ = _ := by rw [Real.cos_add,hcos,hz]; ring
    have hs : sin s = -sin t := by
      calc sin s = sin ((s-t)+t) := congrArg sin (sub_add_cancel s t).symm
           _ = _ := by rw [Real.sin_add,hcos,hz]; ring
    simp only [ray,proj,Real.cos_add_pi,Real.sin_add_pi,hc,hs]

private structure Axis (l : AffineSubspace ℝ ℝ²) where
  base : ℝ²
  time : ℝ
  half : time ∈ Ico 0 π
  spec : l = lineAt base time

private noncomputable def axis {A : Finset ℝ²} (l : determinedLines A) : Axis l.val := by
  apply Classical.choice
  obtain ⟨p,_,q,_,hne,he⟩ := mem_determinedLines.mp l.property
  obtain ⟨t,ht,hd⟩ := half_normal p q
  refine ⟨⟨p,t,ht, he ▸ ?_⟩⟩
  exact line_pair_eq (lineAt_is p t) (lineAt_mem.mpr rfl) (lineAt_mem.mpr hd.symm) hne

private abbrev Lifts (A : Finset ℝ²) := (determinedLines A) × Bool

private noncomputable def node {A : Finset ℝ²} (w : Lifts A) : ℝ² :=
  ray (axis w.1).base ((axis w.1).time + if w.2 then π else 0)

private lemma node_on {A : Finset ℝ²} (l : determinedLines A) (b : Bool) (p : ℝ²) :
    node (l,b) ∈ Set.range (ray p) ↔ p ∈ l.val := by
  cases b <;> simp only [node,Bool.false_eq_true,↓reduceIte,add_zero, ray_on,
    (axis l).spec,lineAt_mem,proj_flip,neg_inj,eq_comm]

private lemma node_at {A : Finset ℝ²} {l : determinedLines A} {p : ℝ²} (hp : p ∈ l.val) (b : Bool) :
    node (l,b) = ray p ((axis l).time + if b then π else 0) := by
  have he := ray_on.mp ((node_on l b p).mpr hp)
  change ray _ _ = _
  simp only [ray,he]

private lemma plane_eq {A : Finset ℝ²} {l : determinedLines A} {p : ℝ²} (hp : p ∈ l.val) :
    lineAt p (axis l).time = l.val := by
  rw [(axis l).spec] at hp
  apply Eq.trans _ (axis l).spec.symm
  ext q
  simp only [lineAt_mem, lineAt_mem.mp hp]

private lemma node_inj {A : Finset ℝ²} : Function.Injective (@node A) := by
  rintro ⟨l,b⟩ ⟨m,c⟩ h
  have lineEq : l=m := by
    apply Subtype.ext
    ext p
    rw [← node_on l b p, ← node_on m c p, h]
  subst m
  congr 1
  by_contra hbc
  have coords := ray_components h
  cases b <;> cases c <;> simp_all only [Bool.false_eq_true, ↓reduceIte,add_zero,
    Real.sin_add_pi,Real.cos_add_pi, not_true_eq_false]
  all_goals nlinarith only [coords.1,coords.2.1, Real.sin_sq_add_cos_sq (axis l).time]

private lemma node_swap {A : Finset ℝ²} (l : determinedLines A) (b : Bool) :
    node (l,!b) = opp (node (l,b)) := by
  cases b
  · simpa [node] using ray_opp (axis l).base (axis l).time
  · simp only [node,Bool.not_true,Bool.false_eq_true,↓reduceIte,add_zero,← ray_opp]
    apply (ray_period _ _ _).mpr
    exact ⟨-1,by push_cast; ring⟩

private lemma classify {A : Finset ℝ²} {p q : A} (hne : p≠q) {z : ℝ²}
    (hp : z ∈ Set.range (ray p.val)) (hq : z ∈ Set.range (ray q.val)) :
    ∃ l : determinedLines A, l.val = line[ℝ,p.val,q.val] ∧ ∃ b, z=node (l,b) := by
  let l : determinedLines A := ⟨line[ℝ,p.val,q.val],
    mem_determinedLines.mpr ⟨_,p.property,_,q.property,fun h => hne (Subtype.ext h),rfl⟩⟩
  have hl : p.val ∈ l.val := left_mem_affineSpan_pair _ _ _
  obtain ⟨t,rfl⟩ := hp
  have hq' : q.val ∈ lineAt p.val t := lineAt_mem.mpr (ray_on.mp hq).symm
  have hatt : l.val = lineAt p.val t := line_pair_eq (lineAt_is _ _)
    (lineAt_mem.mpr rfl) hq' (fun h => hne (Subtype.ext h))
  refine ⟨l,rfl,?_⟩
  rcases two_rays (hatt.symm.trans (plane_eq hl).symm) with h | h
  · refine ⟨false,?_⟩
    simpa only [node_at hl,Bool.false_eq_true,↓reduceIte,add_zero] using h
  · refine ⟨true,?_⟩
    simpa only [node_at hl,↓reduceIte] using h

private noncomputable def vertices (A : Finset ℝ²) : Finset ℝ² := univ.image (@node A)

private lemma vertices_card (A : Finset ℝ²) : (vertices A).card = 2*(determinedLines A).card := by
  rw [vertices,card_image_of_injective _ node_inj,card_univ]
  simp [Lifts,Nat.mul_comm]

private noncomputable def pencil {A : Finset ℝ²} (p : A) : Finset (determinedLines A) :=
  univ.filter fun l => p.val ∈ l.val

private lemma pencil_count (A : Finset ℝ²) :
    ∑ p : A, (pencil p).card = ∑ l ∈ determinedLines A, (A.filter fun p => p ∈ l).card := by
  let F := determinedLines A
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (p : A) (l : F) => p.val ∈ l.val) (s := univ) (t := univ)
  change (∑ p : A, (pencil p).card) = ∑ l : F, ((univ : Finset A).filter fun p => p.val ∈ l.val).card at h
  rw [h,← sum_coe_sort F]
  apply sum_congr rfl
  intro l _
  change (A.attach.filter fun p => p.val ∈ l.val).card = _
  rw [filter_attach (fun p : ℝ² => p ∈ l.val),card_map,card_attach]

private lemma pencil_ge {A : Finset ℝ²} (hsize : 2 ≤ A.card)
    (hn : ∀ l : AffineSubspace ℝ ℝ², IsLine l → (A.filter fun p => p ∈ l).card < A.card)
    (p : A) : 2 ≤ (pencil p).card := by
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < A.card by omega)
  have other : ∃ q ∈ A, p.val ≠ q := by
    by_cases h : p.val=x
    · exact ⟨y,hy,h ▸ hxy⟩
    · exact ⟨x,hx,h⟩
  obtain ⟨q,hq,hpq⟩ := other
  let l : determinedLines A := ⟨line[ℝ,p.val,q],mem_determinedLines.mpr ⟨_,p.property,_,hq,hpq,rfl⟩⟩
  have outside : ∃ b ∈ A, b ∉ l.val := by
    by_contra! h
    have := hn l.val (isLine_pair hpq)
    rw [filter_eq_self.mpr h] at this
    exact lt_irrefl _ this
  obtain ⟨b,hb,ho⟩ := outside
  have hpb : p.val ≠ b := by rintro rfl; exact ho (left_mem_affineSpan_pair _ _ _)
  let m : determinedLines A := ⟨line[ℝ,p.val,b],mem_determinedLines.mpr ⟨_,p.property,_,hb,hpb,rfl⟩⟩
  apply one_lt_card.mpr
  refine ⟨l,mem_filter.mpr ⟨mem_univ _,left_mem_affineSpan_pair _ _ _⟩,
    m,mem_filter.mpr ⟨mem_univ _,left_mem_affineSpan_pair _ _ _⟩,?_⟩
  intro he
  exact ho ((congrArg Subtype.val he).symm ▸ (show b ∈ m.val from right_mem_affineSpan_pair _ _ _))

private theorem angles {A : Finset ℝ²} (p : A) :
    ∃ θ : Fin (pencil p).card ↪o ℝ, (∀ i, θ i ∈ Ico 0 π) ∧
      ∀ t, ray p.val t ∈ vertices A ↔ ∃ i, ray p.val t=ray p.val (θ i) ∨
        ray p.val t=ray p.val (θ i+π) := by
  let f (l : determinedLines A) := (axis l).time
  let U := (pencil p).image f
  have inj : Set.InjOn f (pencil p : Set (determinedLines A)) := by
    intro l hl m hm he
    apply Subtype.ext
    have h₁ := plane_eq (mem_filter.mp hl).2
    have h₂ := plane_eq (mem_filter.mp hm).2
    exact h₁.symm.trans ((congrArg (lineAt p.val) he).trans h₂)
  have count : U.card = (pencil p).card := card_image_of_injOn inj
  let θ := U.orderEmbOfFin count
  have θ_mem (i) : θ i ∈ U := U.orderEmbOfFin_mem count i
  have all_mem {l : determinedLines A} (hl : l ∈ pencil p) : ∃ i, θ i = f l := by
    have : f l ∈ (U : Set ℝ) := mem_image_of_mem _ hl
    rwa [← U.range_orderEmbOfFin count] at this
  refine ⟨θ,?_,?_⟩
  · intro i
    obtain ⟨l,_,he⟩ := mem_image.mp (θ_mem i)
    exact he ▸ (axis l).half
  · intro t
    constructor
    · intro hz
      obtain ⟨⟨l,b⟩,_,he⟩ := mem_image.mp hz
      have hr : node (l,b) ∈ Set.range (ray p.val) := he ▸ Set.mem_range_self _
      have hl := (node_on l b p.val).mp hr
      obtain ⟨i,hi⟩ := all_mem (mem_filter.mpr ⟨mem_univ _,hl⟩)
      refine ⟨i,?_⟩
      rw [← he,node_at hl,hi]
      cases b <;> simp [f]
    · rintro ⟨i,hi⟩
      obtain ⟨l,hl,he⟩ := mem_image.mp (θ_mem i)
      have hp' := (mem_filter.mp hl).2
      rcases hi with h | h
      · refine mem_image.mpr ⟨(l,false),mem_univ _,?_⟩
        rw [node_at hp',h,← he]
        simp [f]
      · refine mem_image.mpr ⟨(l,true),mem_univ _,?_⟩
        rw [node_at hp',h,← he]
        rfl

end OMA.Melchior211



/- Apply the plane edge bound to the two-sheeted incidence drawing. -/
namespace OMA.Melchior211
open Finset EuclideanGeometry Erdos211
open scoped Classical EuclideanGeometry

private lemma cycle_mem {Q : Finset ℝ²} {F : ℝ → ℝ²} {g m}
    (c : LocalCycle Q F g m) (i : Fin (2*m)) (v : Q) :
    (v.val ∈ c.curve i) ↔ v ∈ c.edge i := by
  obtain ⟨x,y,_,he,γ,_,hc,hin⟩ := c.drawn i
  refine ⟨hin v,?_⟩
  rw [he,Finset.mem_insert,Finset.mem_singleton,hc]
  rintro (rfl | rfl)
  · exact ⟨0,γ.source⟩
  · exact ⟨1,γ.target⟩

private noncomputable def arrangement {A : Finset ℝ²} (hsize : 2 ≤ A.card)
    (hn : ∀ l : AffineSubspace ℝ ℝ², IsLine l → (A.filter fun p => p ∈ l).card < A.card)
    (p : A) : LocalCycle (vertices A) (ray p.val) opp (pencil p).card :=
  cycle _ _ _ _ (pencil_ge hsize hn p) (angles p).choose (angles p).choose_spec.1
    (ray_continuous p.val) (ray_period p.val) (ray_opp p.val) (angles p).choose_spec.2

private abbrev ArcTag (A : Finset ℝ²) := (p : A) × Fin (2*(pencil p).card)

private lemma same_or_opposite {A : Finset ℝ²} {p q : A} (hne : p≠q) {z w : ℝ²}
    (zp : z ∈ Set.range (ray p.val)) (zq : z ∈ Set.range (ray q.val))
    (wp : w ∈ Set.range (ray p.val)) (wq : w ∈ Set.range (ray q.val)) :
    z=w ∨ w=opp z := by
  obtain ⟨l,hl,b,rfl⟩ := classify hne zp zq
  obtain ⟨k,hk,c,rfl⟩ := classify hne wp wq
  obtain rfl : l=k := Subtype.ext (hl.trans hk.symm)
  by_cases h : b=c
  · exact Or.inl (h ▸ rfl)
  · have he : c = !b := by cases b <;> cases c <;> simp_all
    exact Or.inr (he ▸ node_swap _ _)

private theorem arrangement_simple {A : Finset ℝ²}
    (D : (p : A) → LocalCycle (vertices A) (ray p.val) opp (pencil p).card) :
    Function.Injective (fun u : ArcTag A => (D u.1).edge u.2) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ he
  change (D p).edge i = (D q).edge j at he
  have hpq : p=q := by
    by_contra hne
    obtain ⟨x,y,hxy,hend,_⟩ := (D p).drawn i
    have hxp : x ∈ (D p).edge i := by simp [hend]
    have hyp : y ∈ (D p).edge i := by simp [hend]
    have on {r : A} (a) (v : vertices A) (h : v ∈ (D r).edge a) :
        v.val ∈ Set.range (ray r.val) := (D r).on a ((cycle_mem _ _ _).mpr h)
    rcases same_or_opposite hne (on i x hxp) (on j x (he ▸ hxp))
      (on i y hyp) (on j y (he ▸ hyp)) with h | h
    · exact hxy (Subtype.ext h)
    · exact (D p).notOpposite i x y hxp hyp hxy h
  subst q
  obtain rfl := (D p).simple he
  rfl

theorem melchior_of_planar
    (planar : ∀ (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
      (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²),
      (∀ i ∈ E, ∃ x y : Q, x≠y ∧ edge i={x,y} ∧
        ∃ γ : Path x.val y.val, Function.Injective γ ∧ curve i=Set.range γ ∧
          ∀ v : Q, v.val ∈ curve i → v ∈ edge i) →
      (∀ i ∈ E, edge i ⊆ S) → Set.InjOn edge (E : Set ℕ) →
      (∀ i ∈ E, ∀ j ∈ E, i≠j → curve i ∩ curve j ⊆
        Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) → E.card ≤ 3*S.card)
    (A : Finset ℝ²) (hn : 2 ≤ A.card)
    (hcap : ∀ l : AffineSubspace ℝ ℝ², IsLine l → (A.filter fun p => p ∈ l).card < A.card) :
    (∑ l ∈ determinedLines A, ((A.filter fun p => p ∈ l).card : ℝ)) ≤
      3 * ((determinedLines A).card : ℝ) := by
  let Q := vertices A
  let D := arrangement hn hcap
  let encode (u : ArcTag A) := (Fintype.equivFin (ArcTag A) u).val
  have hinj : Function.Injective encode := Fin.val_injective.comp (Fintype.equivFin _).injective
  let E := univ.image encode
  let edge := Function.extend encode (fun u => (D u.1).edge u.2) (fun _ => ∅)
  let curve := Function.extend encode (fun u => (D u.1).curve u.2) (fun _ => ∅)
  have e_eq (u : ArcTag A) : edge (encode u)=(D u.1).edge u.2 := hinj.extend_apply _ _ u
  have c_eq (u : ArcTag A) : curve (encode u)=(D u.1).curve u.2 := hinj.extend_apply _ _ u
  have size := card_image_of_injective (univ : Finset (ArcTag A)) hinj
  have graph : E.card ≤ 3 * Q.card := by
    have bound := planar Q univ E edge curve
    simp only [card_univ,Fintype.card_coe] at bound
    apply bound
    · intro i hi
      obtain ⟨u,_,rfl⟩ := mem_image.mp hi
      rw [e_eq,c_eq]
      exact (D u.1).drawn u.2
    · exact fun _ _ => subset_univ _
    · intro i hi j hj h
      obtain ⟨u,_,rfl⟩ := mem_image.mp hi
      obtain ⟨v,_,rfl⟩ := mem_image.mp hj
      rw [e_eq,e_eq] at h
      exact congrArg encode (arrangement_simple D h)
    · intro i hi j hj hne z hz
      obtain ⟨⟨p,i'⟩,_,rfl⟩ := mem_image.mp hi
      obtain ⟨⟨q,j'⟩,_,rfl⟩ := mem_image.mp hj
      obtain ⟨h₁,h₂⟩ := hz
      rw [c_eq] at h₁ h₂
      have hz : z ∈ Q := by
        by_cases hpq : p=q
        · subst q
          by_contra hz
          obtain rfl := (D p).uniqueOutside i' j' z hz h₁ h₂
          exact hne rfl
        · obtain ⟨l,_,b,rfl⟩ := classify hpq ((D p).on _ h₁) ((D q).on _ h₂)
          exact mem_image.mpr ⟨(l,b),mem_univ _,rfl⟩
      refine ⟨⟨z,hz⟩,?_,rfl⟩
      rw [e_eq,e_eq]
      exact mem_inter.mpr ⟨(cycle_mem _ _ _).mp h₁,(cycle_mem _ _ _).mp h₂⟩
  change (univ.image encode).card ≤ 3*(vertices A).card at graph
  rw [size,card_univ,vertices_card] at graph
  change Fintype.card ((p : A) × Fin (2*(pencil p).card)) ≤ _ at graph
  rw [Fintype.card_sigma] at graph
  simp only [Fintype.card_fin, ← mul_sum, pencil_count] at graph
  have h : (∑ l ∈ determinedLines A, (A.filter fun p => p ∈ l).card) ≤
      3*(determinedLines A).card := by omega
  exact_mod_cast h

end OMA.Melchior211

theorem OMA.solution : OMA.R_Erdos211_erdos_211_variants_one_sixth_R1.H2 :=
  OMA.Melchior211.melchior_of_planar OMA.Grid652.plane_drawing_bound
