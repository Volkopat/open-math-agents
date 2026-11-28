import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H1_R1

-- Step PoincareConjecture.poincare_conjecture.R1.H3.R1.H1.R1.H2: hypothesis H2 of reduction PoincareConjecture.poincare_conjecture.R1.H3.R1.H1.R1
-- Credit: @luciusacarr
-- H2 := let Triangulates (X : Type) [TopologicalSpace X] : Prop :=     ∃ n : ℕ,       let E := EuclideanSpace ℝ (Fin n)       letI : DecidableEq E := Classical.decEq E       ∃ K : SimplicialComplex ℝ E,         let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}         let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}         let carrier (faces : Set (Finset E)) := ⋃ t ∈ faces, convexHull ℝ (t : Set E)         K.faces.Finite ∧         (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧         (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧         (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧         (∀ p : E, {p} ∈ K.faces →           ∃ f : E → EuclideanSpace ℝ (Fin 3),             (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3),               EqOn f a (convexHull ℝ (s : Set E))) ∧             InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty) ∧         Nonempty (X ≃ₜ K.space)   ∀ (ι : Type) [Finite ι] (X : ι → Type) [∀ i, TopologicalSpace (X i)],     (∀ i, Triangulates (X i)) → Triangulates (Σ i, X i)

/-!
Finite disjoint unions of triangulated spaces are triangulated. Each complex is moved
into a common Euclidean space by padding coordinates and putting a distinct value in a
last coordinate, so different components lie in disjoint parallel hyperplanes. Faces,
links, stars and vertex charts of the union are images of those of the components, and
the sigma type of the carriers maps homeomorphically onto the union by a continuous
bijection from a compact space to a Hausdorff space.
-/

open Geometry Set Topology

noncomputable section

namespace OMAH2

structure Emb {ι : Type} (F : ι → Type) [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  φ : ∀ i, F i →ᴬ[ℝ] E
  ψ : ∀ i, E →ᴬ[ℝ] F i
  left : ∀ i x, ψ i (φ i x) = x
  τ : E →ᵃ[ℝ] ℝ
  c : ι → ℝ
  c_inj : Function.Injective c
  hτ : ∀ i x, τ (φ i x) = c i

namespace Emb

variable {ι : Type} {F : ι → Type} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : Emb F E)

lemma inj (i : ι) : Function.Injective (D.φ i) := fun x y h => by
  rw [← D.left i x, ← D.left i y, h]

def e (i : ι) : F i ↪ E := ⟨D.φ i, D.inj i⟩

@[simp] lemma e_apply (i : ι) (x : F i) : D.e i x = D.φ i x := rfl

lemma tag {i j : ι} {x : F i} {y : F j} (h : D.φ i x = D.φ j y) : i = j :=
  D.c_inj (by rw [← D.hτ i x, ← D.hτ j y, h])

lemma hull_tag {i : ι} (S : Set (F i)) {y : E} (hy : y ∈ convexHull ℝ (D.φ i '' S)) :
    D.τ y = D.c i := by
  have : convexHull ℝ (D.φ i '' S) ⊆ D.τ ⁻¹' {D.c i} :=
    convexHull_min (by rintro _ ⟨x, -, rfl⟩; simp [D.hτ])
      ((convex_singleton _).affine_preimage D.τ)
  exact this hy

lemma map_hull (i : ι) (s : Finset (F i)) :
    convexHull ℝ ((s.map (D.e i) : Finset E) : Set E) = D.φ i '' convexHull ℝ (s : Set (F i)) := by
  rw [Finset.coe_map]
  exact ((D.φ i).toAffineMap.image_convexHull _).symm

def faces (K : ∀ i, SimplicialComplex ℝ (F i)) : Set (Finset E) :=
  {s | ∃ i, ∃ t ∈ (K i).faces, s = t.map (D.e i)}

lemma comp {K : ∀ i, SimplicialComplex ℝ (F i)} {s : Finset E} (hs : s ∈ D.faces K)
    {i : ι} {x : F i} (hx : D.φ i x ∈ s) : ∃ t ∈ (K i).faces, s = t.map (D.e i) := by
  obtain ⟨j, t, ht, rfl⟩ := hs
  obtain ⟨x', -, hx'⟩ := Finset.mem_map.1 hx
  obtain rfl := D.tag hx'.symm
  exact ⟨t, ht, rfl⟩

def cplx (K : ∀ i, SimplicialComplex ℝ (F i)) : SimplicialComplex ℝ E where
  faces := D.faces K
  isRelLowerSet_faces := by
    rintro s ⟨i, t, ht, rfl⟩
    refine ⟨((K i).nonempty_of_mem_faces ht).map, ?_⟩
    intro u hu hne
    obtain ⟨u', hu', rfl⟩ := Finset.subset_map_iff.1 hu
    exact ⟨i, u', (K i).down_closed ht hu' (by simpa using hne), rfl⟩
  indep := by
    rintro s ⟨i, t, ht, rfl⟩
    have h1 := ((K i).indep ht).map' (D.φ i).toAffineMap (D.inj i)
    let eq : t ≃ (t.map (D.e i) : Finset E) :=
      Equiv.ofBijective (fun x => ⟨D.φ i x, Finset.mem_map_of_mem (D.e i) x.2⟩)
        ⟨fun a b h => Subtype.ext (D.inj i (congrArg Subtype.val h)),
         fun ⟨y, hy⟩ => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
          exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [← affineIndependent_equiv eq]
    exact h1
  inter_subset_convexHull := by
    classical
    rintro s s' ⟨i, t, ht, rfl⟩ ⟨j, t', ht', rfl⟩
    by_cases hij : i = j
    · subst hij
      rw [map_hull, map_hull, ← Set.image_inter (D.inj i), ← Finset.coe_inter, ← Finset.map_inter,
        map_hull]
      rw [Finset.coe_inter]
      exact Set.image_mono ((K i).inter_subset_convexHull ht ht')
    · rintro y ⟨h1, h2⟩
      rw [Finset.coe_map] at h1 h2
      exact absurd (D.c_inj ((D.hull_tag _ h1).symm.trans (D.hull_tag _ h2))) hij

variable {K : ∀ i, SimplicialComplex ℝ (F i)}

lemma mem_cplx {s : Finset E} : s ∈ (D.cplx K).faces ↔ s ∈ D.faces K := Iff.rfl

lemma mem_map_faces {i : ι} {v : Finset (F i)} :
    v.map (D.e i) ∈ (D.cplx K).faces ↔ v ∈ (K i).faces := by
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := Finset.map_nonempty.1 ((D.cplx K).nonempty_of_mem_faces hv)
    obtain ⟨w, hw, h⟩ := D.comp hv (Finset.mem_map_of_mem (D.e i) hx)
    rwa [Finset.map_injective (D.e i) h]
  · intro hv
    exact ⟨i, v, hv, rfl⟩

lemma comp' {i : ι} {u : Finset E} (hu : u ∈ (D.cplx K).faces) {w : Finset (F i)}
    (huw : u ⊆ w.map (D.e i)) : ∃ u' ∈ (K i).faces, u = u'.map (D.e i) := by
  obtain ⟨y, hy⟩ := (D.cplx K).nonempty_of_mem_faces hu
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 (huw hy)
  exact D.comp hu hy

lemma faces_cplx {s : Finset E} (hs : s ∈ (D.cplx K).faces) :
    ∃ i, ∃ t ∈ (K i).faces, s = t.map (D.e i) := hs

def lk {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq V]
    (L : SimplicialComplex ℝ V) (s : Finset V) : Set (Finset V) :=
  {t | t ∈ L.faces ∧ Disjoint s t ∧ s ∪ t ∈ L.faces}

def st {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq V]
    (L : SimplicialComplex ℝ V) (p : V) : Set (Finset V) :=
  {t | t ∈ L.faces ∧ {p} ∪ t ∈ L.faces}

def carrier {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set (Finset V)) : Set V :=
  ⋃ t ∈ S, convexHull ℝ (t : Set V)

lemma carrier_map (i : ι) (S : Set (Finset (F i))) :
    carrier (Finset.map (D.e i) '' S) = D.φ i '' carrier S := by
  unfold carrier
  rw [Set.biUnion_image, Set.image_iUnion₂]
  simp_rw [map_hull]

variable [∀ i, DecidableEq (F i)] [DecidableEq E]

lemma lk_map {i : ι} (t : Finset (F i)) (ht : t ∈ (K i).faces) :
    lk (D.cplx K) (t.map (D.e i)) = Finset.map (D.e i) '' lk (K i) t := by
  ext u
  constructor
  · rintro ⟨hu, hd, hun⟩
    obtain ⟨x, hx⟩ := (K i).nonempty_of_mem_faces ht
    obtain ⟨w, -, hw⟩ := D.comp hun
      (Finset.mem_union_left _ (Finset.mem_map_of_mem (D.e i) hx))
    obtain ⟨u', hu', rfl⟩ := D.comp' hu (hw ▸ Finset.subset_union_right)
    refine ⟨u', ⟨hu', (Finset.disjoint_map _).1 hd, ?_⟩, rfl⟩
    rwa [← Finset.map_union, D.mem_map_faces] at hun
  · rintro ⟨u', ⟨hu', hd, hun⟩, rfl⟩
    refine ⟨D.mem_map_faces.2 hu', (Finset.disjoint_map _).2 hd, ?_⟩
    rwa [← Finset.map_union, D.mem_map_faces]

lemma st_map {i : ι} (x : F i) :
    st (D.cplx K) (D.φ i x) = Finset.map (D.e i) '' st (K i) x := by
  ext u
  constructor
  · rintro ⟨hu, hun⟩
    obtain ⟨w, -, hw⟩ := D.comp hun (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    obtain ⟨u', hu', rfl⟩ := D.comp' hu (hw ▸ Finset.subset_union_right)
    refine ⟨u', ⟨hu', ?_⟩, rfl⟩
    have : ({D.φ i x} : Finset E) = ({x} : Finset (F i)).map (D.e i) := by simp
    rwa [this, ← Finset.map_union, D.mem_map_faces] at hun
  · rintro ⟨u', ⟨hu', hun⟩, rfl⟩
    refine ⟨D.mem_map_faces.2 hu', ?_⟩
    have : ({D.φ i x} : Finset E) = ({x} : Finset (F i)).map (D.e i) := by simp
    rwa [this, ← Finset.map_union, D.mem_map_faces]

lemma singleton_lk {i : ι} (t : Finset (F i)) (ht : t ∈ (K i).faces) :
    {q : E | {q} ∈ lk (D.cplx K) (t.map (D.e i))} = D.φ i '' {q | {q} ∈ lk (K i) t} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_image, D.lk_map t ht]
  constructor
  · rintro ⟨u, hu, hq⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 (hq ▸ Finset.mem_singleton_self q)
    refine ⟨x, ?_, rfl⟩
    have : u = {x} := Finset.map_injective (D.e i) (by rw [hq]; simp)
    exact this ▸ hu
  · rintro ⟨x, hx, rfl⟩
    exact ⟨{x}, hx, by simp⟩

omit [∀ i, DecidableEq (F i)] [DecidableEq E] in
lemma singleton_face {p : E} (hp : {p} ∈ (D.cplx K).faces) :
    ∃ i, ∃ x : F i, p = D.φ i x ∧ {x} ∈ (K i).faces := by
  obtain ⟨i, t, ht, h⟩ := hp
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 (h ▸ Finset.mem_singleton_self p)
  refine ⟨i, x, rfl, ?_⟩
  have : t = {x} := Finset.map_injective (D.e i) (by rw [← h]; simp)
  exact this ▸ ht

end Emb

def Good {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq V]
    (L : SimplicialComplex ℝ V) : Prop :=
  L.faces.Finite ∧
  (∀ s ∈ L.faces, ∃ t ∈ L.faces, s ⊆ t ∧ t.card = 4) ∧
  (∀ t ∈ L.faces, t.card = 2 → IsConnected (Emb.carrier (Emb.lk L t))) ∧
  (∀ t ∈ L.faces, t.card = 3 → ({q : V | {q} ∈ Emb.lk L t} : Set V).ncard = 2) ∧
  (∀ p : V, {p} ∈ L.faces →
    ∃ f : V → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ Emb.st L p, ∃ a : V →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn f a (convexHull ℝ (s : Set V))) ∧
      InjOn f (Emb.carrier (Emb.st L p)) ∧ (interior (f '' Emb.carrier (Emb.st L p))).Nonempty)

namespace Emb

variable {ι : Type} {F : ι → Type} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : Emb F E)
  {K : ∀ i, SimplicialComplex ℝ (F i)} [∀ i, DecidableEq (F i)] [DecidableEq E]

theorem good [Finite ι] (hK : ∀ i, Good (K i)) : Good (D.cplx K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (Set.finite_iUnion fun i => ((hK i).1.image (Finset.map (D.e i)))).subset ?_
    rintro s ⟨i, t, ht, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, t, ht, rfl⟩
  · rintro s ⟨i, t, ht, rfl⟩
    obtain ⟨u, hu, htu, hc⟩ := (hK i).2.1 t ht
    exact ⟨u.map (D.e i), D.mem_map_faces.2 hu, Finset.map_subset_map.2 htu, by simpa using hc⟩
  · rintro s ⟨i, t, ht, rfl⟩ hc
    rw [D.lk_map t ht, D.carrier_map]
    exact ((hK i).2.2.1 t ht (by simpa using hc)).image _ (D.φ i).continuous.continuousOn
  · rintro s ⟨i, t, ht, rfl⟩ hc
    rw [D.singleton_lk t ht, Set.ncard_image_of_injective _ (D.inj i)]
    exact (hK i).2.2.2.1 t ht (by simpa using hc)
  · intro p hp
    obtain ⟨i, x, rfl, hx⟩ := D.singleton_face hp
    obtain ⟨f, hf1, hf2, hf3⟩ := (hK i).2.2.2.2 x hx
    refine ⟨fun y => f (D.ψ i y), ?_, ?_, ?_⟩
    · rintro s hs
      rw [D.st_map] at hs
      obtain ⟨s', hs', rfl⟩ := hs
      obtain ⟨a, ha⟩ := hf1 s' hs'
      refine ⟨a.comp (D.ψ i), ?_⟩
      rw [D.map_hull]
      rintro _ ⟨z, hz, rfl⟩
      simp only [ContinuousAffineMap.coe_comp, Function.comp_apply, D.left]
      exact ha hz
    · rw [D.st_map, D.carrier_map]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
      simp only [D.left] at h
      rw [hf2 ha hb h]
    · rw [D.st_map, D.carrier_map, Set.image_image]
      simpa only [D.left] using hf3

end Emb


namespace Emb

variable {ι : Type} {F : ι → Type} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : Emb F E)
  {K : ∀ i, SimplicialComplex ℝ (F i)}

lemma space_compact {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : SimplicialComplex ℝ V) (h : L.faces.Finite) : IsCompact L.space := by
  unfold SimplicialComplex.space
  exact h.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)

def toSpace (p : Σ i, (K i).space) : (D.cplx K).space :=
  ⟨D.φ p.1 p.2.1, by
    obtain ⟨s, hs, hy⟩ := SimplicialComplex.mem_space_iff.1 p.2.2
    exact SimplicialComplex.mem_space_iff.2
      ⟨s.map (D.e p.1), ⟨p.1, s, hs, rfl⟩, by rw [D.map_hull]; exact ⟨_, hy, rfl⟩⟩⟩

theorem homeo [Finite ι] (hK : ∀ i, (K i).faces.Finite) :
    Nonempty ((Σ i, (K i).space) ≃ₜ (D.cplx K).space) := by
  have : ∀ i, CompactSpace (K i).space :=
    fun i => isCompact_iff_compactSpace.1 (space_compact _ (hK i))
  have hbij : Function.Bijective (D.toSpace (K := K)) := by
    constructor
    · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
      have h' : D.φ i x = D.φ j y := congrArg Subtype.val h
      obtain rfl := D.tag h'
      obtain rfl := D.inj i h'
      rfl
    · rintro ⟨z, hz⟩
      obtain ⟨s, ⟨i, t, ht, rfl⟩, hzs⟩ := SimplicialComplex.mem_space_iff.1 hz
      rw [D.map_hull] at hzs
      obtain ⟨x, hx, rfl⟩ := hzs
      exact ⟨⟨i, x, SimplicialComplex.mem_space_iff.2 ⟨t, ht, hx⟩⟩, rfl⟩
  have hc : Continuous (D.toSpace (K := K)) := by
    apply continuous_sigma
    intro i
    exact Continuous.subtype_mk ((D.φ i).continuous.comp continuous_subtype_val) _
  exact ⟨hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij)⟩

end Emb

def mkA {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (L : V →L[ℝ] W) (v : W) : V →ᴬ[ℝ] W where
  toFun x := L x + v
  linear := L
  map_vadd' p w := by simp [vadd_eq_add, add_assoc]
  cont := L.continuous.add continuous_const

@[simp] lemma mkA_apply {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) (v : W) (x : V) :
    mkA L v x = L x + v := rfl

def padLin (k N : ℕ) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N+1)) where
  toFun x := WithLp.toLp 2 (fun j => if hj : (j : ℕ) < k then x ⟨j, hj⟩ else 0)
  map_add' x y := by
    refine PiLp.ext fun j => ?_
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    refine PiLp.ext fun j => ?_
    simp only [PiLp.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def truncLin (k N : ℕ) (h : k ≤ N) :
    EuclideanSpace ℝ (Fin (N+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun y := WithLp.toLp 2 (fun j : Fin k => y ⟨j, by omega⟩)
  map_add' x y := by
    refine PiLp.ext fun j => ?_
    simp
  map_smul' a x := by
    refine PiLp.ext fun j => ?_
    simp

def concrete {ι : Type} (n : ι → ℕ) (m : ℕ) (hn : ∀ i, n i ≤ m) (c : ι → ℝ)
    (hc : Function.Injective c) :
    Emb (fun i => EuclideanSpace ℝ (Fin (n i))) (EuclideanSpace ℝ (Fin (m+1))) where
  φ i := mkA (LinearMap.toContinuousLinearMap (padLin (n i) m))
    (c i • EuclideanSpace.single (Fin.last m) 1)
  ψ i := mkA (LinearMap.toContinuousLinearMap (truncLin (n i) m (hn i))) 0
  left i x := by
    refine PiLp.ext fun j => ?_
    have hj := j.2
    have := hn i
    have hne : (⟨j, by omega⟩ : Fin (m+1)) ≠ Fin.last m := by
      intro h; have h2 := congrArg Fin.val h; simp only [Fin.val_last] at h2; omega
    simp [padLin, truncLin, hne]
  τ := (EuclideanSpace.proj (Fin.last m) : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ).toLinearMap.toAffineMap
  c := c
  c_inj := hc
  hτ i x := by
    have : ¬ (m < n i) := by have := hn i; omega
    simp [padLin, this]

end OMAH2

end

open OMAH2 in
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H1_R1.H2 := by
  intro ι _ X _ h
  have h' : ∀ i, ∃ n, ∃ K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      @Good _ _ _ (Classical.decEq _) K ∧ Nonempty (X i ≃ₜ K.space) := fun i => by
    obtain ⟨n, K, a, b, c, d, e, f⟩ := h i
    exact ⟨n, K, ⟨a, b, c, d, e⟩, f⟩
  choose n K hK hX using h'
  let := Fintype.ofFinite ι
  let m := Finset.univ.sup n
  have hn : ∀ i, n i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  let c : ι → ℝ := fun i => ((Fintype.equivFin ι i : ℕ) : ℝ)
  have hc : Function.Injective c := fun a b hab =>
    (Fintype.equivFin ι).injective (Fin.ext (by simpa [c] using hab))
  let D := concrete n m hn c hc
  let : ∀ i, DecidableEq (EuclideanSpace ℝ (Fin (n i))) := fun i => Classical.decEq _
  let : DecidableEq (EuclideanSpace ℝ (Fin (m+1))) := Classical.decEq _
  obtain ⟨a, b, c', d, e⟩ := D.good hK
  obtain ⟨φ⟩ := D.homeo (fun i => (hK i).1)
  let g : (Σ i, X i) ≃ₜ (Σ i, (K i).space) :=
    { Equiv.sigmaCongrRight (fun i => (hX i).some.toEquiv) with
      continuous_toFun := continuous_sigma fun i => continuous_sigmaMk.comp (hX i).some.continuous
      continuous_invFun :=
        continuous_sigma fun i => continuous_sigmaMk.comp (hX i).some.symm.continuous }
  exact ⟨m+1, D.cplx K, a, b, c', d, e, ⟨g.trans φ⟩⟩
