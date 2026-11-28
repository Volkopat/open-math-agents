import OMAReductions.R_gillibert_geodesic_deletion_R1
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Tactic

/-!
Formalization of the known Cartesian-factor transitivity theorem, exact step R1.H2.
The full geodesic-deletion conjecture remains open: H1 retains its open core.

This independently written proof uses convex factor layers and repeated extraction
of one Cartesian-prime factor. A recursive restriction compares diagonal target
vertices. Strong induction on the first order handles decomposable factors.
No unique-prime-factorization theorem or unproved result is used as a premise.

Sources and credit:
* R. Hammack, W. Imrich, S. Klavzar, Handbook of Product Graphs, 2nd ed.,
  CRC Press2011, Cartesian products, convex layers, and factor transitivity.
  https://www.routledge.com/Handbook-of-Product-Graphs/Hammack-Imrich-Klavzar/p/book/9781439813041
  Scholarly monograph; refereeing status not independently verified.
* A. Soltani, A. Iranmanesh, On the Edge Wiener Index, Filomat28:3 (2014),
  541-549, Theorem2.14, DOI10.2298/FIL1403541S, refereed.
  This supplies the known statement, not a Lean proof used here.
* @Gillibert, parent statement PR334: Luc Gillibert and GPT6Astra,
  The Geodesic Deletion Conjecture, 17 November2026, unrefereed,
  https://github.com/Gillibert/ConjecturesGillibert/blob/main/geodesic_deletion_conjecture.tex.
  The reduction is PR13005. All proof code here was written in this workspace;
  no other agent's note or proof PR supplied an idea or code used here.
-/

namespace CartesianConvex
open SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def IntervalClosed (J : SimpleGraph V) (C : Set V) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z,
    J.dist x y=J.dist x z+J.dist z y → z ∈ C

lemma dist_product (hG : G.Connected) (hH : H.Connected) (x y : V × W) :
    (G □ H).dist x y=G.dist x.1 y.1+H.dist x.2 y.2 := by
  have heq := SimpleGraph.edist_boxProd (G := G) (H := H) x y
  rw [← ((hG.boxProd hH) x y).coe_dist_eq_edist,
    ← (hG x.1 y.1).coe_dist_eq_edist,← (hH x.2 y.2).coe_dist_eq_edist] at heq
  exact_mod_cast heq

lemma cross_corner_mem (hG : G.Connected) (hH : H.Connected)
    {C : Set (V × W)} (hC : IntervalClosed (G □ H) C)
    {x y : V × W} (hx : x ∈ C) (hy : y ∈ C) : (x.1,y.2) ∈ C := by
  apply hC x hx y hy (x.1,y.2)
  simp only [dist_product hG hH,SimpleGraph.dist_self,zero_add,add_zero]
  exact Nat.add_comm _ _

lemma closed_eq_box (hG : G.Connected) (hH : H.Connected)
    {C : Set (V × W)} (hC : IntervalClosed (G □ H) C) :
    C=(Prod.fst '' C) ×ˢ (Prod.snd '' C) := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨z,hz,rfl⟩,⟨z,hz,rfl⟩⟩
  · rintro ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
    have heq : (x.1,y.2)=z := Prod.ext hxz hyz
    exact heq ▸ cross_corner_mem hG hH hC (x := x) (y := y) hx hy

lemma layer_closed (hG : G.Connected) (hH : H.Connected) (b : W) :
    IntervalClosed (G □ H) {x | x.2=b} := by
  intro x hx y hy z hz
  change x.2=b at hx
  change y.2=b at hy
  have htriangle : G.dist x.1 y.1 ≤ G.dist x.1 z.1+G.dist z.1 y.1 := hG.dist_triangle
  simp only [dist_product hG hH,hx,hy,SimpleGraph.dist_self,add_zero] at hz
  have hzero : H.dist b z.2=0 := by omega
  exact ((hH.dist_eq_zero_iff).mp hzero).symm

lemma iso_dist {A B : Type*} {J : SimpleGraph A} {K : SimpleGraph B}
    (e : J ≃g K) (hJ : J.Connected) (x y : A) : K.dist (e x) (e y)=J.dist x y := by
  obtain ⟨p,hp⟩ := hJ.exists_walk_length_eq_dist x y
  obtain ⟨q,hq⟩ := (e.connected_iff.mp hJ).exists_walk_length_eq_dist (e x) (e y)
  have h1 : K.dist (e x) (e y) ≤ p.length := by
    simpa only [Walk.length_map,RelEmbedding.coe_toRelHom,RelIso.coe_toRelEmbedding] using
      SimpleGraph.dist_le (p.map e.toHom)
  have h2 : J.dist x y ≤ q.length := by
    simpa only [Walk.length_copy,Walk.length_map] using SimpleGraph.dist_le
      ((q.map e.symm.toHom).copy (e.symm_apply_apply x) (e.symm_apply_apply y))
  rw [hp] at h1
  rw [hq] at h2
  omega

lemma iso_image_closed {A B : Type*} {J : SimpleGraph A} {K : SimpleGraph B}
    (e : J ≃g K) (hJ : J.Connected) {C : Set A} (hC : IntervalClosed J C) :
    IntervalClosed K (e '' C) := by
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ z hz
  have hza : e (e.symm z)=z := e.apply_symm_apply z
  have hdist : J.dist a b=J.dist a (e.symm z)+J.dist (e.symm z) b := by
    rw [← iso_dist e hJ a b,← iso_dist e hJ a (e.symm z),
      ← iso_dist e hJ (e.symm z) b,hza]
    exact hz
  exact ⟨e.symm z,hC a ha b hb _ hdist,hza⟩

lemma automorphism_layer_box (hG : G.Connected) (hH : H.Connected)
    (e : (G □ H) ≃g (G □ H)) (b : W) :
    e '' {x : V × W | x.2=b} =
      (Prod.fst '' (e '' {x : V × W | x.2=b})) ×ˢ
      (Prod.snd '' (e '' {x : V × W | x.2=b})) := by
  exact closed_eq_box hG hH (iso_image_closed e (hG.boxProd hH) (layer_closed hG hH b))

def layerIso (b : W) : G ≃g (G □ H).induce {x | x.2=b} where
  toFun a := ⟨(a,b),rfl⟩
  invFun x := x.val.1
  left_inv a := rfl
  right_inv x := Subtype.ext (Prod.ext rfl x.property.symm)
  map_rel_iff' := by
    intro a c
    change (G □ H).Adj (a,b) (c,b) ↔ G.Adj a c
    exact SimpleGraph.boxProd_adj_left

def inducedBoxIso (A : Set V) (B : Set W) :
    (G □ H).induce (A ×ˢ B) ≃g (G.induce A) □ (H.induce B) where
  toFun x := (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
  invFun x := ⟨(x.1.val,x.2.val),⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_rel_iff' := by
    intro x y
    change (G.Adj x.val.1 y.val.1 ∧
        (⟨x.val.2,x.property.2⟩ : B)=⟨y.val.2,y.property.2⟩ ∨
      H.Adj x.val.2 y.val.2 ∧
        (⟨x.val.1,x.property.1⟩ : A)=⟨y.val.1,y.property.1⟩) ↔
      (G.Adj x.val.1 y.val.1 ∧ x.val.2=y.val.2 ∨ H.Adj x.val.2 y.val.2 ∧ x.val.1=y.val.1)
    simp only [Subtype.mk.injEq]

lemma automorphism_layer_factorization (hG : G.Connected) (hH : H.Connected)
    (e : (G □ H) ≃g (G □ H)) (b : W) :
    let C := e '' {x : V × W | x.2=b}
    Nonempty (G ≃g (G.induce (Prod.fst '' C)) □ (H.induce (Prod.snd '' C))) := by
  let L : Set (V × W) := {x | x.2=b}
  let C := e '' L
  let A := Prod.fst '' C
  let B := Prod.snd '' C
  have hbij : Set.BijOn e L C := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro x hx;exact ⟨x,hx,rfl⟩
    · rintro y ⟨x,hx,rfl⟩;exact ⟨x,hx,rfl⟩
  have hbox : C=A ×ˢ B := automorphism_layer_box hG hH e b
  let congr : (G □ H).induce C ≃g (G □ H).induce (A ×ˢ B) :=
    (SimpleGraph.Iso.refl : (G □ H) ≃g (G □ H)).induce (by
      rw [← hbox]
      exact Set.bijOn_id C)
  exact ⟨((layerIso (G := G) (H := H) b).trans (e.induce hbij)).trans
    (congr.trans (inducedBoxIso A B))⟩

end CartesianConvex

namespace Longhaul
open SimpleGraph

section PrimeDefinition
variable {V : Type} [Fintype V]
/-- Cartesian indecomposability; unlike prime order, this includes composite orders. -/
def CartesianPrime (G : SimpleGraph V) : Prop :=
  1 < Fintype.card V ∧
  ∀ {A B : Type} [Fintype A] [Fintype B]
    (J : SimpleGraph A) (K : SimpleGraph B),
    Nonempty (G ≃g J □ K) → Fintype.card A=1 ∨ Fintype.card B=1
end PrimeDefinition

section Mixed
variable {V B C : Type} [Fintype V] [Fintype B] [Fintype C]
variable {G : SimpleGraph V} {J : SimpleGraph B} {K : SimpleGraph C}

def MixedHorizontal (e : (G □ J) ≃g (G □ K)) (b : B) : Prop :=
  ∃ c, ∀ a : V, (e (a,b)).2=c

def MixedVertical (e : (G □ J) ≃g (G □ K)) (b : B) : Prop :=
  ∃ c, ∀ a : V, (e (a,b)).1=c

lemma mixed_layer_factorization (hG : G.Connected) (hJ : J.Connected) (hK : K.Connected)
    (e : (G □ J) ≃g (G □ K)) (b : B) :
    let L := e '' {x : V × B | x.2=b}
    Nonempty (G ≃g (G.induce (Prod.fst '' L)) □ (K.induce (Prod.snd '' L))) := by
  let L₀ : Set (V × B) := {x | x.2=b}
  let L := e '' L₀
  let A := Prod.fst '' L
  let D := Prod.snd '' L
  have hbij : Set.BijOn e L₀ L := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro x hx;exact ⟨x,hx,rfl⟩
    · rintro y ⟨x,hx,rfl⟩;exact ⟨x,hx,rfl⟩
  have hbox : L=A ×ˢ D := CartesianConvex.closed_eq_box hG hK
    (CartesianConvex.iso_image_closed e (hG.boxProd hJ) (CartesianConvex.layer_closed hG hJ b))
  let congr : (G □ K).induce L ≃g (G □ K).induce (A ×ˢ D) :=
    (SimpleGraph.Iso.refl : (G □ K) ≃g (G □ K)).induce (by
      rw [← hbox]
      exact Set.bijOn_id L)
  exact ⟨((CartesianConvex.layerIso (G := G) (H := J) b).trans (e.induce hbij)).trans
    (congr.trans (CartesianConvex.inducedBoxIso A D))⟩

lemma mixed_layer_axis (hG : G.Connected) (hJ : J.Connected) (hK : K.Connected)
    (hp : CartesianPrime G) (e : (G □ J) ≃g (G □ K)) (b : B) :
    MixedHorizontal e b ∨ MixedVertical e b := by
  classical
  let L := e '' {x : V × B | x.2=b}
  let A := Prod.fst '' L
  let D := Prod.snd '' L
  obtain ⟨f⟩ := mixed_layer_factorization hG hJ hK e b
  obtain ⟨a₀⟩ := hG.nonempty
  have hL (a : V) : e (a,b) ∈ L := ⟨(a,b),rfl,rfl⟩
  have hA (a : V) : (e (a,b)).1 ∈ A := ⟨e (a,b),hL a,rfl⟩
  have hD (a : V) : (e (a,b)).2 ∈ D := ⟨e (a,b),hL a,rfl⟩
  rcases hp.2 (G.induce A) (K.induce D) ⟨f⟩ with ha | hd
  · letI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact Or.inr ⟨(e (a₀,b)).1,fun a => congrArg Subtype.val
      (Subsingleton.elim (⟨(e (a,b)).1,hA a⟩ : A) ⟨(e (a₀,b)).1,hA a₀⟩)⟩
  · letI : Subsingleton D := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact Or.inl ⟨(e (a₀,b)).2,fun a => congrArg Subtype.val
      (Subsingleton.elim (⟨(e (a,b)).2,hD a⟩ : D) ⟨(e (a₀,b)).2,hD a₀⟩)⟩

lemma mixed_horizontal_not_vertical_neighbor [Nontrivial V]
    (e : (G □ J) ≃g (G □ K)) {b c : B} (hbc : J.Adj b c)
    (hb : MixedHorizontal e b) : ¬ MixedVertical e c := by
  classical
  obtain ⟨d,hd⟩ := hb
  rintro ⟨a,ha⟩
  let f : V → V := fun x => (e (x,b)).1
  have hinj : Function.Injective f := by
    intro x y hxy
    have heq : e (x,b)=e (y,b) := Prod.ext hxy ((hd x).trans (hd y).symm)
    exact congrArg Prod.fst (e.injective heq)
  have hsurj := Finite.surjective_of_injective hinj
  have hne (x : V) : (e (x,c)).2 ≠ d := by
    intro hx
    obtain ⟨u,hu⟩ := hsurj (e (x,c)).1
    have heq : e (u,b)=e (x,c) := Prod.ext hu ((hd u).trans hx.symm)
    exact hbc.ne (congrArg Prod.snd (e.injective heq))
  have hconst (x : V) : (e (x,b)).1=a := by
    have h : (G □ K).Adj (e (x,b)) (e (x,c)) := e.map_rel_iff.mpr (Or.inr ⟨hbc,rfl⟩)
    rcases h with h | h
    · exact False.elim (hne x (h.2.symm.trans (hd x)))
    · exact h.2.trans (ha x)
  obtain ⟨x,y,hxy⟩ := exists_pair_ne V
  apply hxy
  have heq : e (x,b)=e (y,b) := Prod.ext ((hconst x).trans (hconst y).symm)
    ((hd x).trans (hd y).symm)
  exact congrArg Prod.fst (e.injective heq)

lemma mixed_all_horizontal_of_one (hG : G.Connected) (hJ : J.Connected) (hK : K.Connected)
    (hp : CartesianPrime G) (e : (G □ J) ≃g (G □ K))
    {b : B} (hb : MixedHorizontal e b) : ∀ c, MixedHorizontal e c := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hp.1
  intro c
  obtain ⟨p⟩ := hJ b c
  induction p with
  | nil => exact hb
  | @cons b u c h p ih =>
    apply ih
    rcases mixed_layer_axis hG hJ hK hp e u with hu | hu
    · exact hu
    · exact False.elim (mixed_horizontal_not_vertical_neighbor e h hb hu)

lemma mixed_horizontal_restrict (e : (G □ J) ≃g (G □ K)) {b : B}
    (hb : MixedHorizontal e b) : ∃ φ : G ≃g G, ∀ a, φ a=(e (a,b)).1 := by
  classical
  obtain ⟨d,hd⟩ := hb
  let f : V → V := fun a => (e (a,b)).1
  have hinj : Function.Injective f := by
    intro a c hac
    have heq : e (a,b)=e (c,b) := Prod.ext hac ((hd a).trans (hd c).symm)
    exact congrArg Prod.fst (e.injective heq)
  have hsurj := Finite.surjective_of_injective hinj
  let φ : G ≃g G := {
    toEquiv := Equiv.ofBijective f ⟨hinj,hsurj⟩
    map_rel_iff' := by
      intro a c
      have h := e.map_rel_iff (a := (a,b)) (b := (c,b))
      change G.Adj (f a) (f c) ↔ G.Adj a c
      simpa only [SimpleGraph.boxProd_adj,hd a,hd c,and_true,
        SimpleGraph.irrefl,false_and,or_false] using h }
  exact ⟨φ,fun _ => rfl⟩

/-- Restrict a mixed isomorphism to a target layer when every source layer is vertical. -/
lemma mixed_vertical_restrict (hV : Nonempty V) (e : (G □ J) ≃g (G □ K))
    (hv : ∀ b, MixedVertical e b) (v₀ : V) :
    ∃ (T : Set B) (f : (G □ J.induce T) ≃g K),
      (∀ a b, b ∈ T ↔ (e (a,b)).1=v₀) ∧
      (∀ (a : V) (b : T), f (a,b)=(e (a,b.val)).2) := by
  classical
  obtain ⟨a₀⟩ := hV
  let T : Set B := {b | (e (a₀,b)).1=v₀}
  have hmem (a : V) (b : B) : b ∈ T ↔ (e (a,b)).1=v₀ := by
    obtain ⟨c,hc⟩ := hv b
    change (e (a₀,b)).1=v₀ ↔ (e (a,b)).1=v₀
    rw [hc a₀,hc a]
  let f : V × T → C := fun x => (e (x.1,x.2.val)).2
  have hfirst (a : V) (b : T) : (e (a,b.val)).1=v₀ := (hmem a b.val).mp b.property
  have hinj : Function.Injective f := by
    intro x y h
    change (e (x.1,x.2.val)).2=(e (y.1,y.2.val)).2 at h
    have heq : e (x.1,x.2.val)=e (y.1,y.2.val) :=
      Prod.ext ((hfirst x.1 x.2).trans (hfirst y.1 y.2).symm) h
    have hxy := e.injective heq
    exact Prod.ext (congrArg (fun z : V × B => z.1) hxy)
      (Subtype.ext (congrArg (fun z : V × B => z.2) hxy))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z,hz⟩ := e.surjective (v₀,y)
    have hzT : z.2 ∈ T := (hmem z.1 z.2).mpr (congrArg Prod.fst hz)
    exact ⟨(z.1,⟨z.2,hzT⟩),congrArg Prod.snd hz⟩
  let φ : (G □ J.induce T) ≃g K := {
    toEquiv := Equiv.ofBijective f ⟨hinj,hsurj⟩
    map_rel_iff' := by
      intro x y
      change K.Adj (f x) (f y) ↔
        (G.Adj x.1 y.1 ∧ x.2=y.2 ∨ J.Adj x.2.val y.2.val ∧ x.1=y.1)
      have hrel : (G □ K).Adj (e (x.1,x.2.val)) (e (y.1,y.2.val)) ↔
          (G □ J).Adj (x.1,x.2.val) (y.1,y.2.val) := e.map_rel_iff
      have h₁ : e (x.1,x.2.val)=(v₀,f x) := Prod.ext (hfirst x.1 x.2) rfl
      have h₂ : e (y.1,y.2.val)=(v₀,f y) := Prod.ext (hfirst y.1 y.2) rfl
      rw [h₁,h₂,SimpleGraph.boxProd_adj_right] at hrel
      simpa only [SimpleGraph.boxProd_adj,Subtype.ext_iff] using hrel }
  exact ⟨T,φ,hmem,fun _ _ => rfl⟩
end Mixed

section Powers

def boxCongr {A B C D : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    {J : SimpleGraph C} {K : SimpleGraph D} (e : G ≃g J) (f : H ≃g K) :
    (G □ H) ≃g (J □ K) where
  toEquiv := e.toEquiv.prodCongr f.toEquiv
  map_rel_iff' := by
    intro x y
    change (J.Adj (e x.1) (e y.1) ∧ f x.2=f y.2 ∨
      K.Adj (f x.2) (f y.2) ∧ e x.1=e y.1) ↔
      (G.Adj x.1 y.1 ∧ x.2=y.2 ∨ H.Adj x.2 y.2 ∧ x.1=y.1)
    simp only [e.map_rel_iff,f.map_rel_iff,e.injective.eq_iff,f.injective.eq_iff]

def PowerVertex (V W : Type) : ℕ → Type
  | 0 => W
  | n+1 => V × PowerVertex V W n

instance powerFintype (V W : Type) [Fintype V] [Fintype W] (n : ℕ) :
    Fintype (PowerVertex V W n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype W)
  | succ n ih =>
    change Fintype (V × PowerVertex V W n)
    letI := ih
    infer_instance

def powerGraph {V W : Type} (G : SimpleGraph V) (K : SimpleGraph W) :
    (n : ℕ) → SimpleGraph (PowerVertex V W n)
  | 0 => K
  | n+1 => G □ powerGraph G K n

def powerPoint {V W : Type} (v : V) (w : W) : (n : ℕ) → PowerVertex V W n
  | 0 => w
  | n+1 => (v,powerPoint v w n)

lemma power_connected {V W : Type} {G : SimpleGraph V} {K : SimpleGraph W}
    (hG : G.Connected) (hK : K.Connected) (n : ℕ) : (powerGraph G K n).Connected := by
  induction n with
  | zero => exact hK
  | succ n ih => exact hG.boxProd ih

/-- Existence of a finite Cartesian factor, allowing a singleton residual. -/
def HasFactor {V W : Type} (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (J : SimpleGraph A), Nonempty ((G □ J) ≃g K)

/-- Extract repeated copies of one fixed factor; no uniqueness theorem is used. -/
lemma extract_power {V : Type} [Fintype V] (G : SimpleGraph V)
    (hsize : 2 ≤ Fintype.card V) :
    ∀ {W : Type} [Fintype W] (H : SimpleGraph W), H.Connected →
      ∃ (r : ℕ) (A : Type) (_ : Fintype A) (K : SimpleGraph A),
        K.Connected ∧ ¬ HasFactor G K ∧ Nonempty (H ≃g powerGraph G K r) := by
  classical
  have core : ∀ n : ℕ, ∀ {W : Type} [Fintype W] (H : SimpleGraph W),
      Fintype.card W=n → H.Connected →
      ∃ (r : ℕ) (A : Type) (_ : Fintype A) (K : SimpleGraph A),
        K.Connected ∧ ¬ HasFactor G K ∧ Nonempty (H ≃g powerGraph G K r) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hcard hH
      by_cases hh : HasFactor G H
      · obtain ⟨A,fa,J,⟨e⟩⟩ := hh
        letI : Fintype A := fa
        have hJ : J.Connected := (SimpleGraph.connected_boxProd.mp (e.connected_iff.mpr hH)).2
        have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr hJ.nonempty
        have hc : Fintype.card V * Fintype.card A=n := by
          simpa only [Fintype.card_prod,hcard] using Fintype.card_congr e.toEquiv
        have hlt : Fintype.card A<n := by nlinarith
        obtain ⟨r,B,fb,K,hK,hno,⟨f⟩⟩ := ih (Fintype.card A) hlt J rfl hJ
        letI : Fintype B := fb
        refine ⟨r+1,B,fb,K,hK,hno,⟨?_⟩⟩
        exact e.symm.trans (boxCongr (SimpleGraph.Iso.refl : G ≃g G) f)
      · exact ⟨0,W,inferInstance,H,hH,hh,⟨SimpleGraph.Iso.refl⟩⟩
  intro W _ H hH
  exact core (Fintype.card W) H rfl hH

/-- A prime factor cannot be hidden in a product whose remaining factor has no copy of it.
The diagonal target lets a horizontal restriction recover the desired vertex map. -/
lemma diagonal_transfer {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W}
    (hG : G.Connected) (hK : K.Connected) (hp : CartesianPrime G) (hno : ¬ HasFactor G K) :
    ∀ r : ℕ, ∀ {B : Type} [Fintype B] (J : SimpleGraph B), J.Connected →
      ∀ (e : (G □ J) ≃g powerGraph G K r) (u v : V) (b : B) (k : W),
        e (u,b)=powerPoint v k r → ∃ φ : G ≃g G, φ u=v := by
  classical
  intro r
  induction r with
  | zero =>
    intro B _ J _ e _ _ _ _ _
    exact False.elim (hno ⟨B,inferInstance,J,⟨e⟩⟩)
  | succ r ih =>
    intro B _ J hJ e u v b k he
    have hR : (powerGraph G K r).Connected := power_connected hG hK r
    by_cases hh : ∃ c, MixedHorizontal e c
    · obtain ⟨c,hc⟩ := hh
      have hb := mixed_all_horizontal_of_one hG hJ hR hp e hc b
      obtain ⟨φ,hφ⟩ := mixed_horizontal_restrict e hb
      exact ⟨φ,(hφ u).trans (congrArg Prod.fst he)⟩
    · have hv : ∀ c, MixedVertical e c := fun c =>
        (mixed_layer_axis hG hJ hR hp e c).resolve_left (fun hc => hh ⟨c,hc⟩)
      obtain ⟨T,f,hmem,hval⟩ := mixed_vertical_restrict hG.nonempty e hv v
      have hb : b ∈ T := (hmem u b).mpr (congrArg Prod.fst he)
      have hT : (J.induce T).Connected :=
        (SimpleGraph.connected_boxProd.mp (f.connected_iff.mpr hR)).2
      have hpoint : f (u,⟨b,hb⟩)=powerPoint v k r :=
        (hval u ⟨b,hb⟩).trans (congrArg Prod.snd he)
      exact ih (J.induce T) hT f u v ⟨b,hb⟩ k hpoint

def VertexTransitive {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : G ≃g G, e u=v

/-- Full factor transitivity for Cartesian-prime first factors, including shared factors. -/
theorem factor_transitive_prime {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.Connected) (hH : H.Connected) (hp : CartesianPrime G)
    (ht : VertexTransitive (G □ H)) : VertexTransitive G := by
  classical
  have hsize : 2 ≤ Fintype.card V := by
    have h := hp.1
    omega
  obtain ⟨r,A,fa,K,hK,hno,⟨eH⟩⟩ := extract_power G hsize H hH
  letI : Fintype A := fa
  obtain ⟨k⟩ := hK.nonempty
  obtain ⟨b⟩ := hH.nonempty
  intro u v
  let E : (G □ H) ≃g powerGraph G K (r+1) :=
    boxCongr (SimpleGraph.Iso.refl : G ≃g G) eH
  let target := powerPoint v k (r+1)
  obtain ⟨φ,hφ⟩ := ht (u,b) (E.symm target)
  let e : (G □ H) ≃g powerGraph G K (r+1) := φ.trans E
  have he : e (u,b)=target := by
    change E (φ (u,b))=target
    rw [hφ,E.apply_symm_apply]
  exact diagonal_transfer hG hK hp hno (r+1) H hH e u v b k he

end Powers

section GeneralTransitivity

lemma transitive_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : VertexTransitive G) : VertexTransitive H := by
  intro x y
  obtain ⟨φ,hφ⟩ := hG (e.symm x) (e.symm y)
  refine ⟨(e.symm.trans φ).trans e,?_⟩
  change e (φ (e.symm x))=y
  rw [hφ,e.apply_symm_apply]

lemma transitive_box {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : VertexTransitive G) (hH : VertexTransitive H) : VertexTransitive (G □ H) := by
  intro x y
  obtain ⟨φ,hφ⟩ := hG x.1 y.1
  obtain ⟨ψ,hψ⟩ := hH x.2 y.2
  refine ⟨boxCongr φ ψ,?_⟩
  exact Prod.ext hφ hψ

/-- Cartesian factors of a connected finite vertex-transitive product are vertex-transitive.
This proof uses convex layers, extraction of repeated copies of one prime factor,
and induction on the first order; it does not invoke unique prime factorization. -/
theorem factor_transitive {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.Connected) (hH : H.Connected) (ht : VertexTransitive (G □ H)) :
    VertexTransitive G := by
  classical
  have core : ∀ n : ℕ, ∀ {A : Type} [Fintype A] (J : SimpleGraph A),
      Fintype.card A=n → J.Connected →
      ∀ {B : Type} [Fintype B] (K : SimpleGraph B), K.Connected →
        VertexTransitive (J □ K) → VertexTransitive J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ J hcard hJ B _ K hK ht
      by_cases hsmall : Fintype.card A ≤ 1
      · letI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hsmall
        intro x y
        exact ⟨SimpleGraph.Iso.refl,Subsingleton.elim x y⟩
      have hbig : 1 < Fintype.card A := by omega
      by_cases hp : CartesianPrime J
      · exact factor_transitive_prime hJ hK hp ht
      have hbad : ¬ ∀ {X Y : Type} [Fintype X] [Fintype Y]
          (P : SimpleGraph X) (Q : SimpleGraph Y),
          Nonempty (J ≃g P □ Q) → Fintype.card X=1 ∨ Fintype.card Y=1 := by
        intro hh
        exact hp ⟨hbig,hh⟩
      push_neg at hbad
      obtain ⟨X,Y,fx,fy,P,Q,⟨e⟩,hpx,hqy⟩ := hbad
      letI : Fintype X := fx
      letI : Fintype Y := fy
      have hPQ : (P □ Q).Connected := e.connected_iff.mp hJ
      have hP : P.Connected := (SimpleGraph.connected_boxProd.mp hPQ).1
      have hQ : Q.Connected := (SimpleGraph.connected_boxProd.mp hPQ).2
      have hpxpos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr hP.nonempty
      have hqypos : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr hQ.nonempty
      have hpx2 : 2 ≤ Fintype.card X := by omega
      have hqy2 : 2 ≤ Fintype.card Y := by omega
      have hc : n=Fintype.card X * Fintype.card Y := by
        simpa only [Fintype.card_prod,hcard] using Fintype.card_congr e.toEquiv
      have hltP : Fintype.card X<n := by nlinarith
      have hltQ : Fintype.card Y<n := by nlinarith
      let E₁ : (J □ K) ≃g P □ (Q □ K) :=
        (boxCongr e (SimpleGraph.Iso.refl : K ≃g K)).trans (SimpleGraph.boxProdAssoc P Q K)
      have htP : VertexTransitive P :=
        ih (Fintype.card X) hltP P rfl hP (Q □ K) (hQ.boxProd hK) (transitive_iso E₁ ht)
      let eSwap : J ≃g Q □ P := e.trans (SimpleGraph.boxProdComm P Q)
      let E₂ : (J □ K) ≃g Q □ (P □ K) :=
        (boxCongr eSwap (SimpleGraph.Iso.refl : K ≃g K)).trans (SimpleGraph.boxProdAssoc Q P K)
      have htQ : VertexTransitive Q :=
        ih (Fintype.card Y) hltQ Q rfl hQ (P □ K) (hP.boxProd hK) (transitive_iso E₂ ht)
      exact transitive_iso e.symm (transitive_box htP htQ)
  exact core (Fintype.card V) G rfl hG H hH ht

end GeneralTransitivity

end Longhaul

theorem OMA.solution : OMA.R_gillibert_geodesic_deletion_R1.H2 := by
  intro m n A B hA hB ht
  exact Longhaul.factor_transitive hA hB ht
