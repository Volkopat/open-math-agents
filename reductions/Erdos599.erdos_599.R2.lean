import FormalConjectures.ErdosProblems.«599»
import Mathlib

/-!
# Strongly maximal path packings and finite Menger duality

The infinite input concerns only packings. The finite input is the usual cardinal
form of Menger's theorem on the graph induced by a finite vertex set. To separate
all paths, choose one vertex from each packed path in a product of finite spaces.
A finite collection of test paths touches only finitely many packed paths. Keeping
those packed paths in full makes their packing maximum in the resulting finite
region. A finite minimum cut there gives the required choices for all the tests.

See Aharoni and Berger, *Menger's theorem for infinite graphs*, Section 4, for
strong maximality of path families.
-/

-- Reduction Erdos599.erdos_599.R2 of Erdős Problem 599
-- Credit: @yuka30240

namespace OMA.R_Erdos599_erdos_599_R2

/-- If finite packings have unbounded size, some packing admits no improving
finite exchange. The bounded case is proved below. -/
def H1 : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) (A B : Set V),
    Disjoint A B → G.IsIndepSet A → G.IsIndepSet B →
    let paths : Set (Finset V) := {s | ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ p.support.toFinset = s}
    (∀ k : ℕ, ∃ F : Finset (Finset V), ↑F ⊆ paths ∧
      (F : Set (Finset V)).Pairwise Disjoint ∧ k < F.card) →
    ∃ M : Set (Finset V), M ⊆ paths ∧ M.Pairwise Disjoint ∧
      ∀ D F : Finset (Finset V), ↑D ⊆ M → ↑F ⊆ paths →
        (F : Set (Finset V)).Pairwise Disjoint →
        (∀ d ∈ M, d ∉ D → ∀ s ∈ F, Disjoint d s) → F.card ≤ D.card

/-- The cardinal form of Menger's theorem for finite graphs. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Set V),
    let paths : Set (Finset V) := {s | ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ p.support.toFinset = s}
    ∃ (F : Finset (Finset V)) (C : Finset V), ↑F ⊆ paths ∧
      (F : Set (Finset V)).Pairwise Disjoint ∧ C.card ≤ F.card ∧
      ∀ s ∈ paths, ∃ v ∈ C, v ∈ s

/-- Apply finite Menger to the induced graph and transport both witnesses back
along the inclusion. Every test path supported in U lifts to the induced graph. -/
theorem finite_region (hdual : H2) {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (A B : Set V) (U : Finset V) :
    let P : Set (Finset V) := {s | ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ p.support.toFinset = s}
    ∃ (F : Finset (Finset V)) (C : Finset V),
      (∀ s ∈ F, s ∈ P ∧ s ⊆ U) ∧ (F : Set (Finset V)).Pairwise Disjoint ∧
      C ⊆ U ∧ C.card ≤ F.card ∧ ∀ s ∈ P, s ⊆ U → ∃ v ∈ C, v ∈ s := by
  classical
  intro P
  let incl : G.induce (U : Set V) ↪g G := SimpleGraph.Embedding.induce _
  let e : U ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let liftSet : Finset U ↪ Finset V := ⟨Finset.map e, Finset.map_injective e⟩
  have support {a b : U} (p : (G.induce (U : Set V)).Walk a b) :
      (p.map incl.toHom).support.toFinset = p.support.toFinset.map e := by
    ext v
    simp only [SimpleGraph.Walk.support_map, List.mem_toFinset, List.mem_map, Finset.mem_map]
    rfl
  have inside (s : Finset U) : s.map e ⊆ U := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hv
    exact u.2
  obtain ⟨F, C, hF, hd, hcard, hcut⟩ :=
    hdual U (G.induce (U : Set V)) (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B)
  refine ⟨F.map liftSet, C.map e, ?_, ?_, inside C, by simpa using hcard, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨a, ha, b, hb, p, hp, rfl⟩ := hF ht
    exact ⟨⟨a.1, ha, b.1, hb, p.map incl.toHom, hp.map incl.injective, support p⟩, inside _⟩
  · intro s hs t ht hne
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact (Finset.disjoint_map e).mpr (hd hs' ht' (fun h => hne (congrArg liftSet h)))
  · rintro s ⟨a, ha, b, hb, p, hp, rfl⟩ hsU
    have hw (v) (hv : v ∈ p.support) : v ∈ (U : Set V) := hsU (List.mem_toFinset.mpr hv)
    let q := p.induce (U : Set V) hw
    have hq : q.map incl.toHom = p := p.map_induce hw
    have hpath : q.IsPath :=
      (SimpleGraph.Walk.isPath_map_iff_of_injective incl.injective).mp (hq.symm ▸ hp)
    obtain ⟨v, hvC, hv⟩ := hcut q.support.toFinset ⟨_, ha, _, hb, q, hpath, rfl⟩
    refine ⟨v.1, Finset.mem_map.mpr ⟨v, hvC, rfl⟩, ?_⟩
    have heq : p.support.toFinset = q.support.toFinset.map e :=
      (congrArg (fun w : G.Walk a b => w.support.toFinset) hq.symm).trans (support q)
    exact heq.symm ▸ (show v.1 ∈ q.support.toFinset.map e from Finset.mem_map.mpr ⟨v, hv, rfl⟩)

/-- A finite vertex set touches only finitely many members of a disjoint family. -/
theorem touching {V : Type} (M : Set (Finset V)) (hd : M.Pairwise Disjoint)
    (U : Finset V) :
    ∃ D : Finset (Finset V), ∀ d, d ∈ D ↔ d ∈ M ∧ ¬ Disjoint d U := by
  classical
  let through (v : V) : Set (Finset V) := {d | d ∈ M ∧ v ∈ d}
  have hfin (v : V) : (through v).Finite := by
    apply Set.Subsingleton.finite
    intro d h e h'
    by_contra hne
    exact Finset.disjoint_left.mp (hd h.1 h'.1 hne) h.2 h'.2
  have h := U.finite_toSet.biUnion (fun v _ => hfin v)
  refine ⟨h.toFinset, fun d => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
    through, Set.mem_ofPred_eq, Finset.not_disjoint_iff]
  grind

/-- A largest finite packing permits no improving finite exchange. -/
theorem bounded_packing {V : Type} (P : Set (Finset V)) (hn : ∀ s ∈ P, s.Nonempty)
    (hbound : ¬ ∀ k : ℕ, ∃ F : Finset (Finset V), ↑F ⊆ P ∧
      (F : Set (Finset V)).Pairwise Disjoint ∧ k < F.card) :
    ∃ M : Set (Finset V), M ⊆ P ∧ M.Pairwise Disjoint ∧
      ∀ D F : Finset (Finset V), ↑D ⊆ M → ↑F ⊆ P →
        (F : Set (Finset V)).Pairwise Disjoint →
        (∀ d ∈ M, d ∉ D → ∀ s ∈ F, Disjoint d s) → F.card ≤ D.card := by
  classical
  let sizes : Set ℕ := {n | ∃ F : Finset (Finset V), ↑F ⊆ P ∧
    (F : Set (Finset V)).Pairwise Disjoint ∧ F.card = n}
  have hzero : 0 ∈ sizes := ⟨∅, by simp, by simp, rfl⟩
  push Not at hbound
  obtain ⟨k, hk⟩ := hbound
  have hb : BddAbove sizes := by
    refine ⟨k, ?_⟩
    rintro n ⟨F, hF, hd, rfl⟩
    exact hk F hF hd
  obtain ⟨n, ⟨M, hM, hdis, rfl⟩, hmax⟩ :=
    hb.exists_isGreatest_of_nonempty ⟨0, hzero⟩
  refine ⟨M, hM, hdis, ?_⟩
  intro D F hD hF hd hcross
  have hrest : (↑(M \ D) : Set (Finset V)) ⊆ M :=
    fun _ h => (Finset.mem_sdiff.mp h).1
  have cross : ∀ d ∈ M \ D, ∀ s ∈ F, Disjoint d s := by
    intro d h
    exact hcross d (Finset.mem_sdiff.mp h).1 (Finset.mem_sdiff.mp h).2
  have hsep : Disjoint (M \ D) F := by
    refine Finset.disjoint_left.mpr (fun {s} hm hf => ?_)
    obtain ⟨v, hv⟩ := hn s (hF hf)
    exact Finset.disjoint_left.mp (cross s hm s hf) hv hv
  have hpack : (↑((M \ D) ∪ F) : Set (Finset V)).Pairwise Disjoint := by
    rw [Finset.coe_union, Set.pairwise_union]
    exact ⟨hdis.mono hrest, hd, fun x hx y hy _ => ⟨cross x hx y hy, (cross x hx y hy).symm⟩⟩
  have hsize := hmax (show ((M \ D) ∪ F).card ∈ sizes from
    ⟨_, by rw [Finset.coe_union]; exact Set.union_subset (hrest.trans hM) hF, hpack, rfl⟩)
  rw [Finset.card_union_of_disjoint hsep] at hsize
  have heq := Finset.card_sdiff_add_card_eq_card (show D ⊆ M from hD)
  omega

/-- Extend the finite cut to a choice on every member of the packing. -/
theorem finite_choices {V : Type} (P M : Set (Finset V)) (hM : M ⊆ P)
    (hn : ∀ d ∈ M, d.Nonempty) (hd : M.Pairwise Disjoint)
    (hmax : ∀ D F : Finset (Finset V), ↑D ⊆ M → ↑F ⊆ P →
      (F : Set (Finset V)).Pairwise Disjoint →
      (∀ d ∈ M, d ∉ D → ∀ s ∈ F, Disjoint d s) → F.card ≤ D.card)
    (hdual : ∀ U : Finset V, ∃ (F : Finset (Finset V)) (C : Finset V),
      (∀ s ∈ F, s ∈ P ∧ s ⊆ U) ∧ (F : Set (Finset V)).Pairwise Disjoint ∧
      C ⊆ U ∧ C.card ≤ F.card ∧ ∀ s ∈ P, s ⊆ U → ∃ v ∈ C, v ∈ s)
    (T : Finset P) :
    ∃ f : ∀ i : M, ↥i.1, ∀ s ∈ T, ∃ i : M, (f i).1 ∈ s.1 := by
  classical
  let W := T.biUnion (fun s => s.1)
  obtain ⟨D, hD⟩ := touching M hd W
  have hDM : (D : Set (Finset V)) ⊆ M := fun d h => ((hD d).mp h).1
  let U := W ∪ D.biUnion id
  have hsub (d) (hd' : d ∈ D) : d ⊆ U := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd', hv⟩)
  obtain ⟨F, C, hF, hFd, _, hCF, hcut⟩ := hdual U
  have hCD : C.card ≤ D.card := by
    apply hCF.trans (hmax D F hDM (fun s hs => (hF s hs).1) hFd ?_)
    intro d hdm hnot s hs
    refine Finset.disjoint_left.mpr (fun {v} hv hvs => ?_)
    rcases Finset.mem_union.mp ((hF s hs).2 hvs) with hw | hpacked
    · exact hnot ((hD d).mpr ⟨hdm, Finset.not_disjoint_iff.mpr ⟨v, hv, hw⟩⟩)
    · obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hpacked
      exact Finset.disjoint_left.mp (hd hdm (hDM he) (fun h => hnot (h ▸ he))) hv hve
  have meet (d) (he : d ∈ D) := hcut d (hM (hDM he)) (hsub d he)
  choose f hfC hfd using meet
  have onto := Finset.surj_on_of_inj_on_of_card_le f hfC (fun d e h₁ h₂ h => by
    by_contra hne
    exact Finset.disjoint_left.mp (hd (hDM h₁) (hDM h₂) hne)
      (hfd d h₁) (h ▸ hfd e h₂)) hCD
  let pick (i : M) : ↥i.1 := if h : i.1 ∈ D then ⟨f i.1 h, hfd i.1 h⟩
    else ⟨(hn i.1 i.2).choose, (hn i.1 i.2).choose_spec⟩
  refine ⟨pick, ?_⟩
  intro s hs
  have hsU : s.1 ⊆ U := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨s, hs, hv⟩)
  obtain ⟨v, hvC, hv⟩ := hcut s.1 s.2 hsU
  obtain ⟨d, he, rfl⟩ := onto v hvC
  exact ⟨⟨d, hDM he⟩, by simpa [pick, he] using hv⟩

/-- The condition of hitting one finite test set is closed in the product
of the finite packed supports. Only the coordinates touching that set occur. -/
theorem global_choices {V : Type} (P M : Set (Finset V)) (hd : M.Pairwise Disjoint)
    (hfinite : ∀ T : Finset P, ∃ f : ∀ i : M, ↥i.1,
      ∀ s ∈ T, ∃ i : M, (f i).1 ∈ s.1) :
    ∃ f : ∀ i : M, ↥i.1, ∀ s : P, ∃ i : M, (f i).1 ∈ s.1 := by
  classical
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  let X := (i : M) → ↥i.1
  let hits (s : P) : Set X := {f | ∃ i : M, (f i).1 ∈ s.1}
  have hclosed (s : P) : IsClosed (hits s) := by
    obtain ⟨D, hD⟩ := touching M hd s.1
    let idx (d : D) : M := ⟨d.1, ((hD _).mp d.2).1⟩
    have heq : hits s = ⋃ d : D, {f : X | (f (idx d)).1 ∈ s.1} := by
      ext f
      constructor
      · rintro ⟨i, hi⟩
        have hm := (hD i.1).mpr ⟨i.2, Finset.not_disjoint_iff.mpr
          ⟨(f i).1, (f i).2, hi⟩⟩
        exact Set.mem_iUnion.mpr ⟨⟨i.1, hm⟩, hi⟩
      · intro h
        obtain ⟨d, hv⟩ := Set.mem_iUnion.mp h
        exact ⟨idx d, hv⟩
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro d
    exact s.1.finite_toSet.isClosed.preimage
      (continuous_subtype_val.comp (continuous_apply (idx d)))
  have hinter : (⋂ s, hits s).Nonempty := by
    apply CompactSpace.iInter_nonempty hclosed
    intro T
    obtain ⟨f, hf⟩ := hfinite T
    exact ⟨f, Set.mem_iInter₂.mpr hf⟩
  obtain ⟨f, hf⟩ := hinter
  exact ⟨f, Set.mem_iInter.mp hf⟩

theorem main : H1 → H2 → type_of% @Erdos599.erdos_599 := by
  classical
  intro hinf hdual V G A B hAB hA hB
  let P : Set (Finset V) := {s | ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
    p.IsPath ∧ p.support.toFinset = s}
  have hnon (s) (hs : s ∈ P) : s.Nonempty := by
    obtain ⟨a, _, b, _, p, _, rfl⟩ := hs
    exact ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩
  have hpack : ∃ M : Set (Finset V), M ⊆ P ∧ M.Pairwise Disjoint ∧
      ∀ D F : Finset (Finset V), ↑D ⊆ M → ↑F ⊆ P →
        (F : Set (Finset V)).Pairwise Disjoint →
        (∀ d ∈ M, d ∉ D → ∀ s ∈ F, Disjoint d s) → F.card ≤ D.card := by
    by_cases hu : ∀ k : ℕ, ∃ F : Finset (Finset V), ↑F ⊆ P ∧
      (F : Set (Finset V)).Pairwise Disjoint ∧ k < F.card
    · exact hinf V G A B hAB hA hB hu
    · exact bounded_packing P hnon hu
  obtain ⟨M, hM, hd, hmax⟩ := hpack
  obtain ⟨f, hf⟩ := global_choices P M hd (finite_choices P M hM
    (fun s hs => hnon s (hM hs)) hd hmax (finite_region hdual G A B))
  have realize (i : M) : ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ p.support.toFinset = i.1 := hM i.2
  choose a ha b hb p hp hs using realize
  have mem (i : M) (v : V) : v ∈ (p i).support ↔ v ∈ i.1 := by
    rw [← hs i, List.mem_toFinset]
  let select (i : M) : V := (f i).1
  have own (i : M) : select i ∈ i.1 := (f i).2
  refine ⟨M, a, b, p, Set.range select, ha, hb, hp, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr (fun {v} h₁ h₂ =>
      Finset.disjoint_left.mp (hd i.2 j.2 (fun h => hij (Subtype.ext h)))
        ((mem i v).mp h₁) ((mem j v).mp h₂))
  · rintro v ⟨i, rfl⟩
    exact ⟨i, (mem i _).mpr (own i)⟩
  · intro i
    refine ⟨select i, ⟨⟨i, rfl⟩, (mem i _).mpr (own i)⟩, ?_⟩
    rintro v ⟨⟨j, rfl⟩, hv⟩
    by_cases he : i = j
    · rw [he]
    · exact (Finset.disjoint_left.mp (hd i.2 j.2 (fun h => he (Subtype.ext h)))
        ((mem i _).mp hv) (own j)).elim
  · intro x hx y hy q hq
    obtain ⟨i, hi⟩ := hf ⟨q.support.toFinset, x, hx, y, hy, q, hq, rfl⟩
    exact ⟨select i, List.mem_toFinset.mp hi, i, rfl⟩

end OMA.R_Erdos599_erdos_599_R2
