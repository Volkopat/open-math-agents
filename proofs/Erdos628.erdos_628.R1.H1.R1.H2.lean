import OMAReductions.R_Erdos628_erdos_628_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sum

/-!
Stiebitz's five-chromatic case of double criticality. A maximal chain of
uniquely three-colorable induced graphs yields two obstructed extensions.
They force a four-clique, and the minimum-overlap exchange gives the split.
See Proposition 2.2 of https://kostochk.web.illinois.edu/math583/stiebitz.pdf.
-/

namespace OMA.Erdos628Recolor

open Finset SimpleGraph
open scoped Classical

private theorem colorable_of_missed_class {V : Type*} (G : SimpleGraph V)
    (s : Finset V) {m : ℕ} (C : (G.induce (s : Set V)ᶜ).Coloring (Fin m)) (j : Fin m)
    (misses : ∀ (v : {x : V // x ∉ s}), C v = j → ∃ u : s, ¬ G.Adj v.val u.val) :
    G.Colorable (s.card + (m - 1)) := by
  classical
  let D := {i : Fin m // i ≠ j}
  let choice (v : {x : V // x ∉ s}) (hv : C v = j) : s := (misses v hv).choose
  have hChoice (v : {x : V // x ∉ s}) (hv : C v = j) : ¬ G.Adj v.val (choice v hv).val :=
    (misses v hv).choose_spec
  let paint (x : V) : s ⊕ D :=
    if hx : x ∈ s then Sum.inl ⟨x, hx⟩ else
      let v : {v : V // v ∉ s} := ⟨x, hx⟩
      if hv : C v = j then Sum.inl (choice v hv) else Sum.inr ⟨C v, hv⟩
  have cross (u v : V) (hu : u ∈ s) (hv : v ∉ s) (hadj : G.Adj u v)
      (heq : paint u = paint v) : False := by
    let z : {z : V // z ∉ s} := ⟨v, hv⟩
    by_cases hz : C z = j
    · have equ : (⟨u, hu⟩ : s) = choice z hz := by simpa [paint, hu, hv, z, hz] using heq
      have hvu : u = (choice z hz).val := congrArg Subtype.val equ
      exact hChoice z hz (hvu ▸ hadj.symm)
    · simp [paint, hu, hv, z, hz] at heq
  let coloring : G.Coloring (s ⊕ D) := Coloring.mk paint (by
    intro u v hadj heq
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
    · have equ : (⟨u, hu⟩ : s) = ⟨v, hv⟩ := by simpa [paint, hu, hv] using heq
      exact hadj.ne (congrArg Subtype.val equ)
    · exact cross u v hu hv hadj heq
    · exact cross v u hv hu hadj.symm heq.symm
    · let x : {x : V // x ∉ s} := ⟨u, hu⟩
      let y : {y : V // y ∉ s} := ⟨v, hv⟩
      have hne := C.valid (v := x) (w := y) hadj
      by_cases hx : C x = j <;> by_cases hy : C y = j
      · exact hne (hx.trans hy.symm)
      · simp [paint, hu, hv, x, y, hx, hy] at heq
      · simp [paint, hu, hv, x, y, hx, hy] at heq
      · have pu : paint u = Sum.inr (⟨C x, hx⟩ : D) := by simp [paint, hu, x, hx]
        have pv : paint v = Sum.inr (⟨C y, hy⟩ : D) := by simp [paint, hv, y, hy]
        rw [pu, pv] at heq
        exact hne (congrArg Subtype.val (Sum.inr.inj heq)))
  simpa [D] using coloring.colorable

theorem common_vertex_in_each_color {V : Type*} (G : SimpleGraph V) (s : Finset V)
    (m : ℕ) (large : ((s.card + (m - 1) : ℕ) : ℕ∞) < G.chromaticNumber)
    (C : (G.induce (s : Set V)ᶜ).Coloring (Fin m)) (j : Fin m) :
    ∃ v : {v : V // v ∉ s}, (∀ u ∈ s, G.Adj v.val u) ∧ C v = j := by
  classical
  by_contra noCommon
  have misses (v : {v : V // v ∉ s}) (hv : C v = j) : ∃ u : s, ¬ G.Adj v.val u.val := by
    by_contra h
    have adj (u : V) (hu : u ∈ s) : G.Adj v.val u := by
      by_contra hnot
      exact h ⟨⟨u, hu⟩, hnot⟩
    exact noCommon ⟨v, adj, hv⟩
  exact large.not_ge (colorable_of_missed_class G s C j misses).chromaticNumber_le

theorem common_card_ge_of_colorable_compl {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (m : ℕ)
    (large : ((s.card + (m - 1) : ℕ) : ℕ∞) < G.chromaticNumber)
    (colorable : (G.induce (s : Set V)ᶜ).Colorable m) :
    m ≤ (univ.filter (fun v => ∀ u ∈ s, G.Adj v u)).card := by
  classical
  let common := univ.filter (fun v => ∀ u ∈ s, G.Adj v u)
  let C := colorable.some
  let outside (v : common) : {x : V // x ∉ s} := ⟨v.val, fun hv =>
    G.irrefl ((mem_filter.mp v.property).2 _ hv)⟩
  let color (v : common) : Fin m := C (outside v)
  have hSurj : Function.Surjective color := by
    intro j
    by_contra noCommon
    have misses (v : {x : V // x ∉ s}) (hv : C v = j) : ∃ u : s, ¬ G.Adj v.val u.val := by
      by_contra h
      have adj (u : V) (hu : u ∈ s) : G.Adj v.val u := by
        by_contra hnot
        exact h ⟨⟨u, hu⟩, hnot⟩
      let z : common := ⟨v.val, mem_filter.mpr ⟨mem_univ _, adj⟩⟩
      exact noCommon ⟨z, hv⟩
    exact large.not_ge (colorable_of_missed_class G s C j misses).chromaticNumber_le
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_surjective color hSurj

theorem split_of_small_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k a b : ℕ) (chrom : G.chromaticNumber = (k : ℕ∞)) (hb : 2 ≤ b) (hab : a + b = k + 1)
    (s : Finset V) (clique : G.IsNClique a s)
    (few : (univ.filter (fun v => ∀ u ∈ s, G.Adj v u)).card < b - 1) :
    ∃ t : Set V, (a : ℕ∞) ≤ (G.induce t).chromaticNumber ∧
      (b : ℕ∞) ≤ (G.induce tᶜ).chromaticNumber := by
  refine ⟨(s : Set V), ?_, ?_⟩
  · rw [induce_eq_top.mpr clique.isClique, chromaticNumber_top]
    change (a : ℕ∞) ≤ (Fintype.card s : ℕ)
    simp only [Fintype.card_coe, clique.card_eq, le_refl]
  · by_contra! inadequate
    let m := b - 1
    have hb' : b = m + 1 := by dsimp [m]; omega
    have C : (G.induce (s : Set V)ᶜ).Colorable m := by
      apply chromaticNumber_le_iff_colorable.mp
      apply ENat.lt_natCast_add_one_iff.mp
      rw [← Nat.cast_one, ← Nat.cast_add, ← hb']
      exact inadequate
    have hl : ((s.card + ((b - 1) - 1) : ℕ) : ℕ∞) < G.chromaticNumber := by
      rw [chrom, ENat.natCast_lt_natCast, clique.card_eq]
      omega
    exact few.not_ge (common_card_ge_of_colorable_compl G s (b - 1) hl C)

end OMA.Erdos628Recolor

namespace OMA.Erdos628UniqueThree

open Finset SimpleGraph

/-- A global labelling is proper on a finite set of vertices. -/
def ProperOn {V α : Type*} (G : SimpleGraph V) (s : Finset V) (c : V → α) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v

theorem ProperOn.mono {V α : Type*} {G : SimpleGraph V} {s t : Finset V} {c : V → α}
    (h : ProperOn G t c) (hst : s ⊆ t) : ProperOn G s c :=
  fun u hu v hv hadj => h u (hst hu) v (hst hv) hadj

theorem properOn_iff_colorable {V : Type*} (G : SimpleGraph V) (s : Finset V) {m : ℕ}
    (hm : 0 < m) :
    (∃ c : V → Fin m, ProperOn G s c) ↔ (G.induce (s : Set V)).Colorable m := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v.val)
      (fun {u v} h => hc u.val u.property v.val v.property h)⟩
  · rintro ⟨C⟩
    let c (v : V) : Fin m := if hv : v ∈ s then C ⟨v, hv⟩ else ⟨0, hm⟩
    refine ⟨c, fun u hu v hv h => ?_⟩
    simpa only [c, dif_pos hu, dif_pos hv] using C.valid (v := ⟨u, hu⟩) (w := ⟨v, hv⟩) h

/-- Within the set, every proper three-coloring gives the same color partition. -/
def UniqueThree {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  (∃ c : V → Fin 3, ProperOn G s c) ∧
    ∀ c d : V → Fin 3, ProperOn G s c → ProperOn G s d →
      ∀ u ∈ s, ∀ v ∈ s, c u = c v ↔ d u = d v

theorem uniqueThree_of_clique {V : Type*} (G : SimpleGraph V) (s : Finset V)
    (hs : G.IsClique s) (hcard : s.card ≤ 3) : UniqueThree G s := by
  have hc : (G.induce (s : Set V)).Colorable 3 :=
    (G.induce (s : Set V)).colorable_of_fintype.mono (by
      change Fintype.card s ≤ 3
      simpa only [Fintype.card_coe] using hcard)
  refine ⟨(properOn_iff_colorable G s (by decide)).mpr hc, ?_⟩
  intro c d hc hd u hu v hv
  by_cases heq : u = v
  · subst v
    simp
  · exact iff_of_false (hc u hu v hv (hs hu hv heq)) (hd u hu v hv (hs hu hv heq))

theorem fin_three_same_of_distinct_pair : ∀ x y z w : Fin 3,
    x ≠ y → z ≠ x → z ≠ y → (z = w ↔ w ≠ x ∧ w ≠ y) := by decide

/-- Adding a common neighbor of an edge to a uniquely three-colorable graph
preserves uniqueness whenever the larger graph remains three-colorable. -/
theorem uniqueThree_insert_of_triangle {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {s : Finset V} {x y z : V} (hs : UniqueThree G s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : G.Adj x y) (hzx : G.Adj z x) (hzy : G.Adj z y)
    (hcolor : (G.induce (insert z s : Finset V)).Colorable 3) :
    UniqueThree G (insert z s) := by
  refine ⟨(properOn_iff_colorable G (insert z s) (by decide)).mpr hcolor, ?_⟩
  intro c d hc hd
  have hx' : x ∈ insert z s := mem_insert_of_mem hx
  have hy' : y ∈ insert z s := mem_insert_of_mem hy
  have hz : z ∈ insert z s := mem_insert_self _ _
  have old := hs.2 c d (hc.mono (subset_insert _ _)) (hd.mono (subset_insert _ _))
  have fixed (w : V) (hw : w ∈ s) : c z = c w ↔ d z = d w := by
    rw [fin_three_same_of_distinct_pair (c x) (c y) (c z) (c w)
      (hc x hx' y hy' hxy) (hc z hz x hx' hzx) (hc z hz y hy' hzy),
      fin_three_same_of_distinct_pair (d x) (d y) (d z) (d w)
      (hd x hx' y hy' hxy) (hd z hz x hx' hzx) (hd z hz y hy' hzy)]
    exact and_congr (not_congr (old w hw x hx)) (not_congr (old w hw y hy))
  intro u hu v hv
  rcases mem_insert.mp hu with he | huold
  · subst u
    rcases mem_insert.mp hv with he | hvold
    · subst v
      simp
    · exact fixed v hvold
  · rcases mem_insert.mp hv with he | hvold
    · subst v
      simpa only [eq_comm] using fixed u huold
    · exact old u huold v hvold

section Prefix

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A sequence of additions whose induced prefixes are uniquely three-colorable.
After the first vertex, each new vertex has an edge to an earlier one. -/
inductive Built : Finset V → Prop
  | empty : Built ∅
  | insert {s : Finset V} {v : V} :
      Built s → v ∉ s → (s = ∅ ∨ ∃ u ∈ s, G.Adj v u) →
      UniqueThree G (Insert.insert v s) → Built (Insert.insert v s)

theorem Built.uniqueThree {s : Finset V} (h : Built G s) : UniqueThree G s := by
  cases h with
  | empty =>
    exact uniqueThree_of_clique G ∅
      (by simpa only [Finset.coe_empty] using G.isClique_empty) (by simp)
  | insert _ _ _ h => exact h

private theorem Built.latest {s t : Finset V} (h : Built G s) (hst : t ⊆ s) (ht : t.Nonempty) :
    ∃ x ∈ t, ∃ p : Finset V, Built G p ∧ p ⊆ s ∧ x ∉ p ∧ t.erase x ⊆ p := by
  induction h generalizing t with
  | empty =>
    obtain ⟨x, hx⟩ := ht
    exact (notMem_empty x (hst hx)).elim
  | @insert s v hs hv _ _ ih =>
    by_cases hvt : v ∈ t
    · refine ⟨v, hvt, s, hs, subset_insert _ _, hv, ?_⟩
      intro u hu
      exact (mem_insert.mp (hst (mem_of_mem_erase hu))).resolve_left (mem_erase.mp hu).1
    · have hsub : t ⊆ s := by
        intro u hu
        exact (mem_insert.mp (hst hu)).resolve_left (fun he => hvt (by rw [← he]; exact hu))
      obtain ⟨x, hx, p, hp, hps, hxp, htpx⟩ := ih hsub ht
      exact ⟨x, hx, p, hp, hps.trans (subset_insert _ _), hxp, htpx⟩

private theorem built_pair {x y : V} (hxy : G.Adj x y) : Built G {x, y} := by
  have singleton : Built G {y} := by
    exact Built.insert Built.empty (notMem_empty y) (Or.inl rfl)
      (uniqueThree_of_clique G {y}
        (by simpa only [Finset.coe_singleton] using G.isClique_singleton y) (by simp))
  exact Built.insert singleton (by simpa only [mem_singleton] using hxy.ne)
    (Or.inr ⟨y, mem_singleton_self _, hxy⟩)
    (uniqueThree_of_clique G {x, y}
      (by simpa only [Finset.coe_insert, Finset.coe_singleton] using
        (G.isClique_pair).mpr (fun _ => hxy)) (by rw [card_pair hxy.ne]; decide))

/-- In a maximal chain, the last vertex and its latest earlier neighbor form
an edge whose in-chain common neighbors all lie in an earlier unique prefix. -/
theorem exists_terminal_prefix [Fintype V] {x y : V} (hxy : G.Adj x y) :
    ∃ s p : Finset V, UniqueThree G s ∧ UniqueThree G p ∧ p ⊆ s ∧
      (∀ v ∉ s, (∃ u ∈ s, G.Adj v u) → ¬ UniqueThree G (insert v s)) ∧
      ∃ z ∈ s, ∃ w ∈ s, G.Adj z w ∧ z ∉ p ∧ w ∉ p ∧
        ∀ u ∈ s, G.Adj u z → G.Adj u w → u ∈ p := by
  classical
  let family := (univ : Finset (Finset V)).filter (Built G)
  have hb : {x, y} ∈ family := mem_filter.mpr ⟨mem_univ _, built_pair G hxy⟩
  obtain ⟨s, hs, hmax⟩ := family.exists_max_image card ⟨_, hb⟩
  have hsBuilt := (mem_filter.mp hs).2
  have hcard : 2 ≤ s.card := by
    have h := hmax _ hb
    rw [card_pair hxy.ne] at h
    exact h
  have hterminal (v : V) (hv : v ∉ s) (hne : ∃ u ∈ s, G.Adj v u)
      (hu : UniqueThree G (insert v s)) : False := by
    have hB : insert v s ∈ family :=
      mem_filter.mpr ⟨mem_univ _, Built.insert hsBuilt hv (Or.inr hne) hu⟩
    have h := hmax _ hB
    rw [card_insert_of_notMem hv] at h
    omega
  have hEdge :
      ∃ p : Finset V, UniqueThree G p ∧ p ⊆ s ∧
        ∃ z ∈ s, ∃ w ∈ s, G.Adj z w ∧ z ∉ p ∧ w ∉ p ∧
          ∀ u ∈ s, G.Adj u z → G.Adj u w → u ∈ p := by
    cases hsBuilt with
    | empty => simp at hcard
    | @insert t z ht hzt hprev _ =>
      have hne : t ≠ ∅ := by
        intro ht'
        simp [ht'] at hcard
      obtain ⟨w, hw, hzw⟩ := hprev.resolve_left hne
      let neighbors := t.filter (G.Adj z)
      have hN : neighbors.Nonempty := ⟨w, mem_filter.mpr ⟨hw, hzw⟩⟩
      obtain ⟨w', hw', p, hp, hpt, hwp, hcover⟩ :=
        ht.latest G (filter_subset _ _) hN
      have hwt := (mem_filter.mp hw').1
      have hzw' := (mem_filter.mp hw').2
      refine ⟨p, hp.uniqueThree G, hpt.trans (subset_insert _ _), z, mem_insert_self _ _,
        w', mem_insert_of_mem hwt, hzw', fun hz => hzt (hpt hz), hwp, ?_⟩
      intro u hu huz huw
      have hut : u ∈ t := (mem_insert.mp hu).resolve_left huz.ne
      apply hcover
      exact mem_erase.mpr ⟨huw.ne, mem_filter.mpr ⟨hut, huz.symm⟩⟩
  obtain ⟨p, hp, hps, hrest⟩ := hEdge
  exact ⟨s, p, hsBuilt.uniqueThree G, hp, hps, hterminal, hrest⟩

end Prefix

end OMA.Erdos628UniqueThree

namespace OMA.Erdos628UniqueThree

open Finset SimpleGraph

private theorem two_common_outside {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {s p : Finset V} {x y : V} (hs : UniqueThree G s) (hp : UniqueThree G p)
    (hps : p ⊆ s) (hxs : x ∈ s) (hys : y ∈ s) (hxy : G.Adj x y)
    (hxp : x ∉ p) (hyp : y ∉ p)
    (hPrefix : ∀ u ∈ s, G.Adj u x → G.Adj u y → u ∈ p)
    (c : V → Fin 3) (hc : ProperOn G (univ \ {x, y}) c)
    (hsat : ∀ j : Fin 3, ∃ u, G.Adj u x ∧ G.Adj u y ∧ c u = j) :
    ∃ u v, u ∉ s ∧ v ∉ s ∧ u ≠ v ∧
      G.Adj u x ∧ G.Adj u y ∧ G.Adj v x ∧ G.Adj v y := by
  classical
  obtain ⟨d, hd⟩ := hs.1
  have hsub : p ⊆ univ \ {x, y} := by
    intro u hu
    exact mem_sdiff.mpr ⟨mem_univ _, by
      simp only [mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · exact hxp hu
      · exact hyp hu⟩
  choose rep hrep using hsat
  have hinj : Function.Injective rep := fun i j he =>
    (hrep i).2.2.symm.trans (he ▸ (hrep j).2.2)
  have hOne (i j : Fin 3) (hij : i ≠ j) (hi : rep i ∈ s) (hj : rep j ∈ s) : False := by
    obtain ⟨hix, hiy, hic⟩ := hrep i
    obtain ⟨hjx, hjy, hjc⟩ := hrep j
    have hip := hPrefix _ hi hix hiy
    have hjp := hPrefix _ hj hjx hjy
    have he : d (rep i) = d (rep j) :=
      (fin_three_same_of_distinct_pair (d x) (d y) (d (rep i)) (d (rep j))
        (hd x hxs y hys hxy) (hd _ hi x hxs hix) (hd _ hi y hys hiy)).mpr
          ⟨hd _ hj x hxs hjx, hd _ hj y hys hjy⟩
    have hc' := (hp.2 d c (hd.mono hps) (hc.mono hsub) _ hip _ hjp).mp he
    exact hij (hic.symm.trans (hc'.trans hjc))
  have pair (i j : Fin 3) (hij : i ≠ j) (hi : rep i ∉ s) (hj : rep j ∉ s) :
      ∃ u v, u ∉ s ∧ v ∉ s ∧ u ≠ v ∧
        G.Adj u x ∧ G.Adj u y ∧ G.Adj v x ∧ G.Adj v y :=
    ⟨rep i, rep j, hi, hj, fun he => hij (hinj he),
      (hrep i).1, (hrep i).2.1, (hrep j).1, (hrep j).2.1⟩
  by_cases h₀ : rep 0 ∈ s
  · exact pair 1 2 (by decide) (fun h => hOne 0 1 (by decide) h₀ h)
      (fun h => hOne 0 2 (by decide) h₀ h)
  by_cases h₁ : rep 1 ∈ s
  · exact pair 0 2 (by decide) h₀ (fun h => hOne 1 2 (by decide) h₁ h)
  exact pair 0 1 (by decide) h₀ h₁

/-- Stiebitz's pair of extensions, expressed using only five-chromaticity
and three-colorability after deleting either endpoint pair of any edge. -/
theorem exists_bad_extensions {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hχ : G.chromaticNumber = 5)
    (hdelete : ∀ x y, G.Adj x y → (G.induce ({x, y}ᶜ : Set V)).Colorable 3) :
    ∃ S : Set V, (G.induce S).Colorable 3 ∧
      ∃ x y u v : V, G.Adj x y ∧ u ≠ v ∧
        G.Adj u x ∧ G.Adj u y ∧ G.Adj v x ∧ G.Adj v y ∧
        ¬ (G.induce (insert u S)).Colorable 3 ∧ ¬ (G.induce (insert v S)).Colorable 3 := by
  have hnot4 : ¬ G.Colorable 4 := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [hχ] at hle
    exact (show ¬ (5 : ℕ∞) ≤ (4 : ℕ) by decide) hle
  have edge : ∃ x y, G.Adj x y := by
    by_contra h
    have C : G.Coloring (Fin 4) :=
      Coloring.mk (fun _ => 0) (fun {u v} e => (h ⟨u, v, e⟩).elim)
    exact hnot4 ⟨C⟩
  obtain ⟨x₀, y₀, e₀⟩ := edge
  obtain ⟨s, p, hs, hp, hps, hterm, x, hxs, y, hys, hxy, hxp, hyp, hPrefix⟩ :=
    exists_terminal_prefix G e₀
  let e : Finset V := {x, y}
  have hcol : (G.induce ((e : Set V)ᶜ)).Colorable 3 := by
    change (G.induce ((({x, y} : Finset V) : Set V)ᶜ)).Colorable 3
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact hdelete x y hxy
  let C := hcol.some
  let c (w : V) : Fin 3 := if hw : w ∉ e then C ⟨w, hw⟩ else 0
  have hc : ProperOn G (univ \ {x, y}) c := by
    intro u hu v hv huv
    have hu' : u ∉ e := (mem_sdiff.mp hu).2
    have hv' : v ∉ e := (mem_sdiff.mp hv).2
    simpa only [c, dif_pos hu', dif_pos hv'] using
      C.valid (v := ⟨u, hu'⟩) (w := ⟨v, hv'⟩) huv
  have hlarge : ((e.card + (3 - 1) : ℕ) : ℕ∞) < G.chromaticNumber := by
    rw [hχ, show e.card = 2 from card_pair hxy.ne]
    decide
  have hrep (j : Fin 3) : ∃ w, G.Adj w x ∧ G.Adj w y ∧ c w = j := by
    obtain ⟨w, hw, hj⟩ := OMA.Erdos628Recolor.common_vertex_in_each_color G e 3 hlarge C j
    refine ⟨w.val, hw x (by simp [e]), hw y (by simp [e]), ?_⟩
    change (if hw : w.val ∉ e then C ⟨w.val, hw⟩ else 0) = j
    rw [dif_pos w.property]
    have he : (⟨w.val, w.property⟩ : ((e : Set V)ᶜ : Set V)) = w := Subtype.ext rfl
    rwa [he]
  obtain ⟨u, v, hu, hv, huv, hux, huy, hvx, hvy⟩ :=
    two_common_outside G hs hp hps hxs hys hxy hxp hyp hPrefix c hc hrep
  have hbad (z : V) (hz : z ∉ s) (hzx : G.Adj z x) (hzy : G.Adj z y) :
      ¬ (G.induce (insert z (s : Set V))).Colorable 3 := by
    intro h
    apply hterm z hz ⟨x, hxs, hzx⟩
    apply uniqueThree_insert_of_triangle G hs hxs hys hxy hzx hzy
    rwa [Finset.coe_insert]
  exact ⟨(s : Set V), (properOn_iff_colorable G s (by decide)).mp hs.1,
    x, y, u, v, hxy, huv, hux, huy, hvx, hvy, hbad u hu hux huy, hbad v hv hvx hvy⟩

end OMA.Erdos628UniqueThree

namespace OMA.Erdos628K5Extensions

open SimpleGraph Finset

private theorem colorable_four_of_independent_outside {V : Type*} (G : SimpleGraph V)
    (S : Set V) (hc : (G.induce S).Colorable 3)
    (hind : ∀ x y, x ∉ S → y ∉ S → ¬ G.Adj x y) : G.Colorable 4 := by
  classical
  let C := hc.some
  let color (x : V) : Fin 3 ⊕ Unit := if hx : x ∈ S then Sum.inl (C ⟨x, hx⟩) else Sum.inr ()
  let D : G.Coloring (Fin 3 ⊕ Unit) := Coloring.mk color (by
    intro x y hxy heq
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · have h := C.valid (v := ⟨x, hx⟩) (w := ⟨y, hy⟩) hxy
      exact h (by simpa [color, hx, hy] using heq)
    · simp [color, hx, hy] at heq
    · simp [color, hx, hy] at heq
    · exact hind x y hx hy hxy)
  simpa using D.colorable

theorem four_clique_of_two_extensions {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hfive : ¬ G.Colorable 4)
    (hdelete : ∀ x y, G.Adj x y → (G.induce ({x, y}ᶜ : Set V)).Colorable 3)
    (hcol : (G.induce S).Colorable 3)
    {x z u v : V} (hxz : G.Adj x z) (huv : u ≠ v)
    (hux : G.Adj u x) (huz : G.Adj u z) (hvx : G.Adj v x) (hvz : G.Adj v z)
    (hbadU : ¬ (G.induce (insert u S)).Colorable 3)
    (hbadV : ¬ (G.induce (insert v S)).Colorable 3) :
    ∃ T : Finset V, G.IsNClique 4 T := by
  classical
  have edge : ∃ i j, i ∉ S ∧ j ∉ S ∧ G.Adj i j := by
    by_contra he
    apply hfive
    apply colorable_four_of_independent_outside G S hcol
    intro i j hi hj hij
    exact he ⟨i, j, hi, hj, hij⟩
  obtain ⟨i, j, hi, hj, hij⟩ := edge
  have forced (w : V) (hbad : ¬ (G.induce (insert w S)).Colorable 3) : i = w ∨ j = w := by
    by_contra he
    have hie : i ≠ w := fun h => he (Or.inl h)
    have hje : j ≠ w := fun h => he (Or.inr h)
    have hsub : insert w S ⊆ ({i, j}ᶜ : Set V) := by
      intro a ha
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · rintro rfl
        exact (Set.mem_insert_iff.mp ha).elim hie hi
      · rintro rfl
        exact (Set.mem_insert_iff.mp ha).elim hje hj
    exact hbad ((hdelete i j hij).of_hom (G.induceHomOfLE hsub).toHom)
  have uv : G.Adj u v := by
    rcases forced u hbadU with hiu | hju <;> rcases forced v hbadV with hiv | hjv
    · exact (huv (hiu.symm.trans hiv)).elim
    · exact hiu ▸ hjv ▸ hij
    · exact hju ▸ hiv ▸ hij.symm
    · exact (huv (hju.symm.trans hjv)).elim
  let T : Finset V := {x, z, u, v}
  have hxu : x ≠ u := hux.symm.ne
  have hxv : x ≠ v := hvx.symm.ne
  have hzu : z ≠ u := huz.symm.ne
  have hzv : z ≠ v := hvz.symm.ne
  refine ⟨T, ?_, ?_⟩
  · intro r hr t ht hrt
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr ht
    rcases hr with rfl | rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl | rfl <;>
      first | exact (hrt rfl).elim | exact hxz | exact hxz.symm |
        exact hux | exact hux.symm | exact huz | exact huz.symm |
        exact hvx | exact hvx.symm | exact hvz | exact hvz.symm | exact uv | exact uv.symm
  · simp [T, Finset.card_insert_of_notMem, hxz.ne, hxu, hxv, hzu, hzv, huv]

end OMA.Erdos628K5Extensions

namespace OMA.Erdos628K5CliqueExchange

open Finset SimpleGraph
open scoped Classical

private theorem induce_clique_chromatic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : Finset V) (hL : G.IsClique L) :
    (L.card : ℕ∞) ≤ (G.induce (L : Set V)).chromaticNumber := by
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj
    (ι := (L : Set V)) (by simp [Nat.card_eq_fintype_card]) id
  intro u v huv
  exact hL u.property v.property (fun he => huv (Subtype.ext he))

private theorem clique_sdiff_card_le_of_colorable {V : Type*} [Fintype V]
    (G : SimpleGraph V) (X L : Finset V) {m : ℕ} (hX : G.IsClique X)
    (hcolor : (G.induce ((L : Set V)ᶜ)).Colorable m) :
    (X \ L).card ≤ m := by
  let f : (X \ L : Finset V) → ((L : Set V)ᶜ : Set V) :=
    fun u => ⟨u.val, (mem_sdiff.mp u.property).2⟩
  have hadj : Pairwise fun u v => (G.induce ((L : Set V)ᶜ)).Adj (f u) (f v) := by
    intro u v huv
    exact hX (mem_sdiff.mp u.property).1 (mem_sdiff.mp v.property).1
      (fun he => huv (Subtype.ext he))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    hcolor.card_le_of_pairwise_adj f hadj

/-- If the larger requested part fits in a clique, there is a Tihany partition.
The only input beyond the chromatic and clique conditions is the bound from
recoloring one color class into the vertices of a removed finite set. -/
theorem split_of_large_clique {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcommon : ∀ (s : Finset V) (m : ℕ),
      ((s.card + (m - 1) : ℕ) : ℕ∞) < G.chromaticNumber →
      (G.induce ((s : Set V)ᶜ)).Colorable m →
      m ≤ ((Finset.univ : Finset V).filter (fun v => ∀ u ∈ s, G.Adj v u)).card)
    {a b k : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hk : a + b = k + 1)
    (hχ : G.chromaticNumber = (k : ℕ∞)) (hfree : G.CliqueFree k)
    {X : Finset V} (hX : G.IsNClique b X) :
    ∃ s : Set V, (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
      (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber := by
  classical
  by_contra hsplit
  obtain ⟨L, hL', hmin⟩ := (G.cliqueFinset b).exists_min_image
    (fun T => (T ∩ X).card) ⟨X, mem_cliqueFinset_iff.mpr hX⟩
  have hL : G.IsNClique b L := mem_cliqueFinset_iff.mp hL'
  have hLχ : (b : ℕ∞) ≤ (G.induce (L : Set V)).chromaticNumber := by
    simpa only [hL.card_eq] using induce_clique_chromatic G L hL.isClique
  have hcomp : (G.induce ((L : Set V)ᶜ)).chromaticNumber < (a : ℕ∞) := by
    apply lt_of_not_ge
    intro h
    refine hsplit ⟨(L : Set V)ᶜ, h, ?_⟩
    rw [show ((L : Set V)ᶜ)ᶜ = (L : Set V) from compl_compl _]
    exact hLχ
  let m := a - 1
  have ha' : a = m + 1 := by dsimp [m]; omega
  have hcolor : (G.induce ((L : Set V)ᶜ)).Colorable m := by
    apply chromaticNumber_le_iff_colorable.mp
    apply ENat.lt_natCast_add_one_iff.mp
    rw [← Nat.cast_one, ← Nat.cast_add, ← ha']
    exact hcomp
  have hdiff : (X \ L).card ≤ m := clique_sdiff_card_le_of_colorable G X L hX.isClique hcolor
  let N := (Finset.univ : Finset V).filter (fun v => ∀ u ∈ L, G.Adj v u)
  have hcardN : m ≤ N.card := by
    refine hcommon L m ?_ hcolor
    rw [hχ, ENat.natCast_lt_natCast, hL.card_eq]
    dsimp [m]
    omega
  have hlinks (v : V) (hv : v ∈ N) (u : V) (hu : u ∈ L) : G.Adj v u :=
    (mem_filter.mp hv).2 u hu
  have hout (v : V) (hv : v ∈ N) : v ∉ L := fun h => G.irrefl (hlinks v hv v h)
  have hNX : ¬ N ⊆ X := by
    intro hNX
    have hNcl : G.IsClique N := hX.isClique.subset (Finset.coe_subset.mpr hNX)
    have hunion : G.IsClique (L ∪ N : Finset V) := by
      intro u hu v hv huv
      obtain hu | hu := mem_union.mp (mem_coe.mp hu)
      · obtain hv | hv := mem_union.mp (mem_coe.mp hv)
        · exact hL.isClique hu hv huv
        · exact (hlinks v hv u hu).symm
      · obtain hv | hv := mem_union.mp (mem_coe.mp hv)
        · exact hlinks u hu v hv
        · exact hNcl hu hv huv
    have hdisj : Disjoint L N := disjoint_left.mpr fun v hv hv' => hout v hv' hv
    have hk' : k ≤ (L ∪ N).card := by
      rw [card_union_of_disjoint hdisj, hL.card_eq]
      dsimp [m] at hcardN
      omega
    obtain ⟨T, hT, hsize⟩ := exists_subset_card_eq hk'
    exact hfree T ⟨hunion.subset (Finset.coe_subset.mpr hT), hsize⟩
  obtain ⟨w, hwN, hwX⟩ := Finset.not_subset.mp hNX
  have hinter : (L ∩ X).Nonempty := by
    have hsum := card_sdiff_add_card_inter X L
    rw [hX.card_eq] at hsum
    apply card_pos.mp
    rw [inter_comm]
    dsimp [m] at hdiff
    omega
  obtain ⟨v, hv⟩ := hinter
  have hvL := (mem_inter.mp hv).1
  let L' := insert w (L.erase v)
  have hL'clique : G.IsClique L' := by
    have hsub : G.IsClique (L.erase v : Finset V) :=
      hL.isClique.subset (Finset.coe_subset.mpr (erase_subset v L))
    change G.IsClique ((insert w (L.erase v) : Finset V) : Set V)
    rw [Finset.coe_insert]
    exact hsub.insert (fun u hu _ => hlinks w hwN u (mem_of_mem_erase hu))
  have hL'card : L'.card = b := by
    have hn : w ∉ L.erase v := fun hw => hout w hwN (mem_of_mem_erase hw)
    change (insert w (L.erase v)).card = b
    rw [card_insert_of_notMem hn, card_erase_of_mem hvL, hL.card_eq]
    omega
  have hL'valid : L' ∈ G.cliqueFinset b := mem_cliqueFinset_iff.mpr ⟨hL'clique, hL'card⟩
  have hnewInter : L' ∩ X = (L ∩ X).erase v := by
    change insert w (L.erase v) ∩ X = (L ∩ X).erase v
    rw [insert_inter_of_notMem hwX]
    ext u
    simp only [mem_inter, mem_erase]
    tauto
  have hlt : (L' ∩ X).card < (L ∩ X).card := by
    rw [hnewInter, card_erase_of_mem hv]
    have hp : 0 < (L ∩ X).card := card_pos.mpr ⟨v, hv⟩
    omega
  exact (not_lt_of_ge (hmin L' hL'valid)) hlt

end OMA.Erdos628K5CliqueExchange

open SimpleGraph

theorem OMA.solution : OMA.R_Erdos628_erdos_628_R1_H1_R1.H2 := by
  intro n k G chrom hfree _critical hk
  subst k
  by_contra noSplit
  have hnot4 : ¬ G.Colorable 4 := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [chrom] at hle
    exact (show ¬ (5 : ℕ∞) ≤ (4 : ℕ) by decide) hle
  have hdelete (x y : Fin n) (adj : G.Adj x y) :
      (G.induce ({x, y}ᶜ : Set (Fin n))).Colorable 3 := by
    have hedge : (2 : ℕ∞) ≤ (G.induce ({x, y} : Set (Fin n))).chromaticNumber :=
      two_le_chromaticNumber_of_adj (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩) adj
    apply chromaticNumber_le_iff_colorable.mp
    apply ENat.lt_natCast_add_one_iff.mp
    rw [show ((3 : ℕ) : ℕ∞) + 1 = (4 : ℕ∞) by decide]
    exact lt_of_not_ge (fun h => noSplit ⟨{x, y}, hedge, h⟩)
  obtain ⟨S, hS, x, y, u, v, hxy, huv, hux, huy, hvx, hvy, hbadU, hbadV⟩ :=
    OMA.Erdos628UniqueThree.exists_bad_extensions G chrom hdelete
  obtain ⟨T, hT⟩ := OMA.Erdos628K5Extensions.four_clique_of_two_extensions G S hnot4 hdelete hS
    hxy huv hux huy hvx hvy hbadU hbadV
  exact noSplit (OMA.Erdos628K5CliqueExchange.split_of_large_clique G
    (OMA.Erdos628Recolor.common_card_ge_of_colorable_compl G) (a := 2) (b := 4) (k := 5)
    (by decide) (by decide) (by decide) chrom hfree hT)
