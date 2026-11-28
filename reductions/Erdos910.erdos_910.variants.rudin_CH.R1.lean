import FormalConjectures.ErdosProblems.«910»

/-! # Rudin’s connected planar set under CH

This formalizes the transfinite assembly and the final topological argument of
M. E. Rudin, *A connected subset of the plane*, Fundamenta Mathematicae 46
(1958), 15–24, from the local extensions and the enumeration of requirements. -/
-- Credit: @yuka30240. The separator argument was suggested in desk note #73386.
-- uses note #73386

namespace OMA.R_Erdos910_erdos_910_variants_rudin_CH_R1

open Set TopologicalSpace
open scoped Cardinal

/-- The local extensions in Rudin's sections 2–3. In a condition (A, Z), A is
the countable set of selected points and Z the region excluded from all later
choices. A partial transversal meets each proper subcontinuum in at most one
point. Conditions may be restricted to extensions of a two-point condition. -/
def H1 : Prop :=
  let E := EuclideanSpace ℝ (Fin 2)
  ∃ (I : Set E) (P : Set (Set E × Set E)), IsClosed I ∧
    let transversal := fun B : Set E =>
      ∀ K : Set E, K ⊂ I → IsClosed K → IsConnected K → (B ∩ K).Subsingleton
    let separates := fun T : Set E => ¬ IsPreconnected (I \ T)
    (∀ p ∈ P, p.1 ⊆ I ∧ p.1.Countable ∧ p.1.Nontrivial ∧
      Disjoint p.1 p.2 ∧ transversal p.1) ∧
    (∀ C ⊆ P, C.Countable → IsChain (· ≤ ·) C → ∃ p ∈ P, ∀ q ∈ C, q ≤ p) ∧
    (∀ T : Set E, IsClosed T → separates T → ∀ p ∈ P,
      ∃ q ∈ P, p ≤ q ∧ (q.1 ∩ T).Nonempty) ∧
    (∀ B : Set E, B ⊆ I → B.Countable → B.Nonempty → transversal B → ∀ p ∈ P,
      ∃ q ∈ P, p ≤ q ∧ ((B ∩ q.2).Nonempty ∨
        (∃ T : Set E, IsClosed T ∧ separates T ∧ (I ∩ T) \ B ⊆ q.2) ∨
        ∃ W : Set E, IsOpen W ∧ (B ∩ W).Nonempty ∧ (W ∩ closure B) \ q.1 ⊆ q.2))

/-- Under CH the closed-set and countable-set requirements in the plane can
be put in a single well-order with countable proper initial segments. -/
def H2 : Prop :=
  let E := EuclideanSpace ℝ (Fin 2)
  let J := Closeds E ⊕ {B : Set E // B.Countable}
  ((ℵ₁ : Cardinal.{0}) = 𝔠) → ∃ r : J → J → Prop, IsWellOrder J r ∧ ∀ i, {j | r j i}.Countable

/-- Meet one requirement at each stage, taking an upper bound for all earlier
conditions before extending. The empty chain supplies the first condition. -/
lemma meet_requirements {J Q : Type} [Preorder Q] (r : J → J → Prop)
    (hr : IsWellOrder J r) (hc : ∀ i, {j | r j i}.Countable)
    (P : Set Q) (upper : ∀ C ⊆ P, C.Countable → IsChain (· ≤ ·) C →
      ∃ p ∈ P, ∀ q ∈ C, q ≤ p)
    (D : J → Set Q) (extend : ∀ i p, p ∈ P → ∃ q ∈ P, p ≤ q ∧ q ∈ D i) :
    ∃ f : J → Q, (∀ i, f i ∈ P ∩ D i) ∧ ∀ i j, r i j → f i ≤ f j := by
  classical
  have base := upper ∅ (empty_subset _) countable_empty (by simp)
  have step (i : J) (prev : ∀ j, r j i → Q) :
      ∃ q ∈ P ∩ D i, (∀ j h, prev j h ∈ P) →
        IsChain (· ≤ ·) (range fun j : {j // r j i} => prev j j.2) →
          ∀ j h, prev j h ≤ q := by
    let C := range fun j : {j // r j i} => prev j j.2
    by_cases good : C ⊆ P ∧ IsChain (· ≤ ·) C
    · have : Countable {j // r j i} := hc i
      obtain ⟨p, hp, hub⟩ := upper C good.1 (countable_range _) good.2
      obtain ⟨q, hq, hpq, hd⟩ := extend i p hp
      exact ⟨q, ⟨hq, hd⟩, fun _ _ j h => (hub _ ⟨⟨j,h⟩, rfl⟩).trans hpq⟩
    · obtain ⟨p, hp, _⟩ := base
      obtain ⟨q, hq, _, hd⟩ := extend i p hp
      exact ⟨q, ⟨hq, hd⟩, fun hp hc => False.elim (good ⟨by
        rintro _ ⟨j, rfl⟩
        exact hp j j.2, hc⟩)⟩
  let f := hr.wf.fix fun i prev => (step i prev).choose
  have spec (i : J) : f i ∈ P ∩ D i ∧ ((∀ j, r j i → f j ∈ P) →
      IsChain (· ≤ ·) (range fun j : {j // r j i} => f j) → ∀ j, r j i → f j ≤ f i) := by
    have h := (step i (fun j _ => f j)).choose_spec
    have heq : f i = (step i (fun j _ => f j)).choose := hr.wf.fix_eq _ i
    exact ⟨heq ▸ h.1, fun hp hc j hj => (h.2 hp hc j hj).trans_eq heq.symm⟩
  refine ⟨f, fun i => (spec i).1, ?_⟩
  suffices h : ∀ j i, r i j → f i ≤ f j from fun i j => h j i
  intro j
  induction j using hr.wf.induction with
  | h j ih =>
    apply (spec j).2 (fun i _ => (spec i).1.1)
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    rcases trichotomous_of r a.val b.val with hab | hab | hba
    · exact Or.inl (ih b b.2 a hab)
    · exact (hne (congrArg f hab)).elim
    · exact Or.inr (ih a a.2 b hba)

/-- A set meeting all the relatively closed separators of a closed metric
subspace is preconnected. A separation extends to disjoint ambient opens. -/
lemma preconnected_of_hits {E : Type*} [MetricSpace E] {I M : Set E}
    (hI : IsClosed I) (hMI : M ⊆ I)
    (hits : ∀ T : Set E, IsClosed T → ¬ IsPreconnected (I \ T) → (M ∩ T).Nonempty) :
    IsPreconnected M := by
  intro u v hu hv hcover hMu hMv
  by_contra hmeet
  have hd : Disjoint (M ∩ u) v := disjoint_left.2 fun x hx h => hmeet ⟨x, hx.1, hx.2, h⟩
  have hd' : Disjoint u (M ∩ v) := disjoint_left.2 fun x h hx => hmeet ⟨x, hx.1, h, hx.2⟩
  have hsep : SeparatedNhds (M ∩ u) (M ∩ v) := separatedNhds_iff_disjoint.2
    (completely_normal
      (Disjoint.mono (closure_minimal (disjoint_left.1 hd) hv.isClosed_compl) inter_subset_right
        disjoint_compl_left)
      (Disjoint.mono inter_subset_right (closure_minimal (disjoint_right.1 hd') hu.isClosed_compl)
        disjoint_compl_right))
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := hsep
  have coverM : M ⊆ U ∪ V := by
    intro x hx
    exact (hcover hx).elim (fun h => Or.inl (huU ⟨hx, h⟩)) (fun h => Or.inr (hvV ⟨hx, h⟩))
  let T := I \ (U ∪ V)
  have cut : ¬ IsPreconnected (I \ T) := by
    intro conn
    have cover : I \ T ⊆ U ∪ V := by dsimp [T]; grind
    have sub : M ⊆ I \ T := fun x hx => ⟨hMI hx, fun h => h.2 (coverM hx)⟩
    obtain ⟨a, ha⟩ := hMu
    obtain ⟨b, hb⟩ := hMv
    obtain hor | hor := conn.subset_or_subset hU hV hUV cover
    · exact disjoint_left.1 hUV (hor (sub hb.1)) (hvV hb)
    · exact disjoint_left.1 hUV (huU ha) (hor (sub ha.1))
  obtain ⟨x, hx, hT⟩ := hits T (hI.sdiff (hU.union hV)) cut
  exact hT.2 (coverM hx)

/-- Extract a countable sample of an uncountable set S such that near each
sample point uncountably many points of S belong to the sample's closure. -/
lemma condensation_sample {E : Type*} [MetricSpace E] [SecondCountableTopology E]
    {S : Set E} (hS : ¬ S.Countable) :
    ∃ B ⊆ S, B.Countable ∧ B.Nonempty ∧ ∀ W : Set E, IsOpen W →
      (B ∩ W).Nonempty → ¬ (S ∩ (W ∩ closure B)).Countable := by
  classical
  let small := {W : Set E | IsOpen W ∧ (W ∩ S).Countable}
  obtain ⟨F, hFc, hF, heq⟩ := isOpen_sUnion_countable small fun _ h => h.1
  have negligible : (⋃₀ small ∩ S).Countable := by
    rw [← heq, sUnion_eq_biUnion]
    simpa only [iUnion_inter] using hFc.biUnion (fun U hU => (hF hU).2)
  let core := S \ ⋃₀ small
  have split : S ⊆ core ∪ (⋃₀ small ∩ S) := by dsimp [core]; grind
  obtain ⟨B, hB, hBc, hdense⟩ := (IsSeparable.of_separableSpace core).exists_countable_dense_subset
  have hBne : B.Nonempty := by
    by_contra! hempty
    rw [hempty, closure_empty] at hdense
    exact hS (negligible.mono (fun x hx => (split hx).elim (fun h => (hdense h).elim) id))
  refine ⟨B, hB.trans sdiff_subset, hBc, hBne, ?_⟩
  rintro W hW ⟨b, hb, hbW⟩ hct
  apply (hB hb).2
  apply mem_sUnion_of_mem hbW
  refine ⟨hW, (hct.union negligible).mono ?_⟩
  intro x hx
  exact (split hx.2).elim (fun h => Or.inl ⟨hx.2, hx.1, hdense h⟩) Or.inr

theorem main : H1 → H2 → type_of% @Erdos910.erdos_910.variants.rudin_CH := by
  classical
  intro hlocal horder hCH
  obtain ⟨I, P, hI, valid, upper, hit, thin⟩ := hlocal
  let E := EuclideanSpace ℝ (Fin 2)
  let J := Closeds E ⊕ {B : Set E // B.Countable}
  let tr := fun B : Set E =>
    ∀ K : Set E, K ⊂ I → IsClosed K → IsConnected K → (B ∩ K).Subsingleton
  let outcome := fun (B : Set E) (p : Set E × Set E) =>
    (B ∩ p.2).Nonempty ∨
    (∃ T : Set E, IsClosed T ∧ ¬ IsPreconnected (I \ T) ∧ (I ∩ T) \ B ⊆ p.2) ∨
    ∃ W : Set E, IsOpen W ∧ (B ∩ W).Nonempty ∧ (W ∩ closure B) \ p.1 ⊆ p.2
  let D : J → Set (Set E × Set E) := Sum.elim
    (fun T => {p | ¬ IsPreconnected (I \ T) → (p.1 ∩ T).Nonempty})
    (fun B => {p | B.val ⊆ I → B.val.Nonempty → tr B.val → outcome B.val p})
  have extend : ∀ i p, p ∈ P → ∃ q ∈ P, p ≤ q ∧ q ∈ D i := by
    rintro (T | B) p hp
    · by_cases h : IsPreconnected (I \ T)
      · exact ⟨p, hp, le_rfl, fun hn => (hn h).elim⟩
      · obtain ⟨q, hq, hle, hqt⟩ := hit T T.isClosed h p hp
        exact ⟨q, hq, hle, fun _ => hqt⟩
    · by_cases h : B.val ⊆ I ∧ B.val.Nonempty ∧ tr B.val
      · obtain ⟨q, hq, hle, ho⟩ := thin B h.1 B.2 h.2.1 h.2.2 p hp
        exact ⟨q, hq, hle, fun _ _ _ => ho⟩
      · exact ⟨p, hp, le_rfl, fun hB hn ht => (h ⟨hB, hn, ht⟩).elim⟩
  have ch0 : (ℵ₁ : Cardinal.{0}) = 𝔠 := by
    apply Cardinal.lift_inj.mp
    simpa using hCH
  obtain ⟨r, hr, hc⟩ := horder ch0
  obtain ⟨f, hf, hmono⟩ := meet_requirements r hr hc P upper D extend
  have common (i j : J) : ∃ k, f i ≤ f k ∧ f j ≤ f k := by
    rcases trichotomous_of r i j with h | rfl | h
    · exact ⟨j, hmono i j h, le_rfl⟩
    · exact ⟨i, le_rfl, le_rfl⟩
    · exact ⟨i, le_rfl, hmono j i h⟩
  let M := ⋃ i, (f i).1
  have stage (i : J) := valid (f i) (hf i).1
  have hMI : M ⊆ I := iUnion_subset fun i => (stage i).1
  have avoids (i : J) : Disjoint M (f i).2 := by
    refine disjoint_left.2 ?_
    rintro x hx hz
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    obtain ⟨k, hik, hjk⟩ := common i j
    exact disjoint_left.1 (stage k).2.2.2.1 (hjk.1 hj) (hik.2 hz)
  have htr : tr M := by
    intro K hK hclosed hconn x hx y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx.1
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy.1
    obtain ⟨k, hik, hjk⟩ := common i j
    exact (stage k).2.2.2.2 K hK hclosed hconn ⟨hik.1 hi, hx.2⟩ ⟨hjk.1 hj, hy.2⟩
  have hnt : M.Nontrivial :=
    ((stage (.inl ⊥)).2.2.1).mono (subset_iUnion (fun i => (f i).1) _)
  refine ⟨M, ⟨hnt.nonempty, preconnected_of_hits hI hMI ?_⟩, hnt, ?_⟩
  · intro T hclosed hcut
    let i : J := .inl ⟨T, hclosed⟩
    obtain ⟨x, hx, hT⟩ := (hf i).2 hcut
    exact ⟨x, mem_iUnion.2 ⟨i, hx⟩, hT⟩
  intro N hNM hconn hn
  by_contra hunc
  obtain ⟨B, hBS, hBc, hBne, hlarge⟩ := condensation_sample hunc
  have hBM : B ⊆ M := hBS.trans sdiff_subset
  let i : J := .inr ⟨B, hBc⟩
  have hBt : tr B := fun K hK hcl hc => Set.Subsingleton.anti (htr K hK hcl hc) (inter_subset_inter_left K hBM)
  rcases (hf i).2 (hBM.trans hMI) hBne hBt with ⟨b, hb, hz⟩ | ⟨T, _, cut, ban⟩ | ⟨W, hw, hb, ban⟩
  · exact disjoint_left.1 (avoids i) (hBM hb) hz
  · have hNT : N ⊆ I \ T := by
      intro x hx
      refine ⟨hMI (hNM hx), fun hT => ?_⟩
      exact disjoint_left.1 (avoids i) (hNM hx)
        (ban ⟨⟨hMI (hNM hx), hT⟩, fun hB => (hBS hB).2 hx⟩)
    have hKI : closure N ⊂ I := by
      refine ssubset_iff_subset_ne.2 ⟨closure_minimal (hNM.trans hMI) hI, fun heq => ?_⟩
      exact cut (hconn.2.subset_closure hNT (heq ▸ sdiff_subset))
    exact hn.not_subsingleton (Set.Subsingleton.anti (htr _ hKI isClosed_closure hconn.closure)
      (subset_inter hNM subset_closure))
  · apply hlarge W hw hb
    refine (stage i).2.1.mono ?_
    rintro x ⟨hx, hxW⟩
    by_contra ha
    exact disjoint_left.1 (avoids i) hx.1 (ban ⟨hxW, ha⟩)

end OMA.R_Erdos910_erdos_910_variants_rudin_CH_R1
