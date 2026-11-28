import FormalConjectures.ErdosProblems.«1111»
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr

/-!
# A Lean disproof of the El-Zahar–Erdős conjecture (Erdős problem 1111)

Mathematical construction by Chenghua Liu and Boning Meng, 2026,
“A disproof of the El-Zahar–Erdős conjecture”, https://arxiv.org/abs/2611.24735.
Formalization by LDJAI. The triangle-free case suffices for the catalogue statement.
-/

section
open SimpleGraph
namespace Erdos640Reduction
variable {V : Type*} {G : SimpleGraph V}
lemma high_iff_not_colorable {n : ℕ} :
    ((n+1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔ ¬ G.Colorable n := by
  rw [Nat.cast_add_one, ENat.add_one_le_iff (ENat.natCast_ne_top n), ← not_le,
    chromaticNumber_le_iff_colorable]
end Erdos640Reduction
end

section
open SimpleGraph Finset
namespace Erdos1111Blocks

def Anti {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

def Cut {r : ℕ} (F : Fin r → Fin r → Prop) : Prop :=
  ∃ s : ℕ, ∀ i j, F i j → i.val ≤ s ∧ s < j.val

/-- Two opposite families of ordered pairs without a strictly increasing
pair of left and right endpoints have a cut through every edge of one family. -/
theorem cut_alternative {r : ℕ} (F H : Fin r → Fin r → Prop)
    (hord : ∀ i j, F i j ∨ H i j → i < j)
    (hFH : ∀ i j k l, F i j → H k l → i < k → j < l → False)
    (hHF : ∀ i j k l, H i j → F k l → i < k → j < l → False) :
    Cut F ∨ Cut H := by
  classical
  let rights := univ.filter (fun j => ∃ i, F i j ∨ H i j)
  by_cases h : rights.Nonempty
  · let j := rights.min' h
    obtain ⟨i₀, hi₀⟩ := (mem_filter.mp (rights.min'_mem h)).2
    let lefts := univ.filter (fun i => F i j ∨ H i j)
    have h' : lefts.Nonempty := ⟨i₀, mem_filter.mpr ⟨mem_univ _, hi₀⟩⟩
    let i := lefts.max' h'
    have hi : F i j ∨ H i j := (mem_filter.mp (lefts.max'_mem h')).2
    have hij := hord i j hi
    have hbound : ∀ k l, F k l ∨ H k l → j ≤ l ∧ (j = l → k ≤ i) := by
      intro k l hk
      refine ⟨rights.min'_le l (mem_filter.mpr ⟨mem_univ _, k, hk⟩), ?_⟩
      rintro rfl
      exact lefts.le_max' k (mem_filter.mpr ⟨mem_univ _, hk⟩)
    rcases hi with hi | hi
    · right
      refine ⟨i.val, fun k l hk => ?_⟩
      obtain ⟨hl, hsame⟩ := hbound k l (Or.inr hk)
      refine ⟨?_, lt_of_lt_of_le hij hl⟩
      rcases hl.eq_or_lt with he | he
      · exact hsame he
      · exact le_of_not_gt fun hlt => hFH i j k l hi hk hlt he
    · left
      refine ⟨i.val, fun k l hk => ?_⟩
      obtain ⟨hl, hsame⟩ := hbound k l (Or.inl hk)
      refine ⟨?_, lt_of_lt_of_le hij hl⟩
      rcases hl.eq_or_lt with he | he
      · exact hsame he
      · exact le_of_not_gt fun hlt => hHF i j k l hi hk hlt he
  · left
    exact ⟨0, fun i j hij => (h ⟨j, mem_filter.mpr ⟨mem_univ _, i, Or.inl hij⟩⟩).elim⟩

variable {V : Type*} {r : ℕ}

noncomputable def mass (b : V → Fin r) (X : Set V) (i : Fin r) : ℕ :=
  Nat.card {v : V // v ∈ X ∧ b v = i}

def Strong (b : V → Fin r) (w : Fin r → Fin r → ℕ) (X : Set V) (i j : Fin r) : Prop :=
  i < j ∧ w i j < mass b X i ∧ w i j < mass b X j

def Later {r : ℕ} (i j k l : Fin r) : Prop := j < l ∨ (j = l ∧ k < i)

/-- Mixing and separation of consecutive thresholds imply that strong pairs
on opposite anticomplete sets cannot increase in both endpoints. -/
theorem no_cross {G : SimpleGraph V} {b : V → Fin r} {w m : Fin r → Fin r → ℕ}
    (ordered : ∀ i j k l, i < j → k < l → Later i j k l → m k l ≤ w i j + 1)
    (mix : ∀ (A B : Set V) i j, i < j → m i j ≤ mass b A i → m i j ≤ mass b B j →
      ∃ a ∈ A, ∃ z ∈ B, G.Adj a z)
    {A B : Set V} (h : Anti G A B) (i j k l : Fin r)
    (ha : Strong b w A i j) (hb : Strong b w B k l) (hik : i < k) (hjl : j < l) : False := by
  have hil := hik.trans hb.1
  have h1 := ordered i j i l ha.1 hil (Or.inl hjl)
  have h2 := ordered k l i l hb.1 hil (Or.inr ⟨rfl, hik⟩)
  obtain ⟨a, hA, z, hB, hadj⟩ := mix A B i l hil (h1.trans ha.2.1) (h2.trans hb.2.2)
  exact h.2 a hA z hB hadj

def WeakGraph (G : SimpleGraph V) (b : V → Fin r) (w : Fin r → Fin r → ℕ) (X : Set V) :
    SimpleGraph X where
  Adj u v := G.Adj u.val v.val ∧ ¬ Strong b w X (b u) (b v) ∧ ¬ Strong b w X (b v) (b u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem color_of_cut (G : SimpleGraph V) (b : V → Fin r) (w : Fin r → Fin r → ℕ) (X : Set V)
    (q : ℕ) (weak : (WeakGraph G b w X).Colorable q) (hc : Cut (Strong b w X)) :
    (G.induce X).Colorable (2*q) := by
  classical
  obtain ⟨s, hs⟩ := hc
  obtain ⟨c⟩ := weak
  let color (x : X) : Bool × Fin q := (decide ((b x).val ≤ s), c x)
  let C : (G.induce X).Coloring (Bool × Fin q) := Coloring.mk color (by
    intro x y hxy he
    have hside : ((b x).val ≤ s) ↔ ((b y).val ≤ s) := by
      simpa [color] using congrArg Prod.fst he
    have hweak : (WeakGraph G b w X).Adj x y := by
      refine ⟨hxy, fun h => ?_, fun h => ?_⟩
      · obtain ⟨hx, hy⟩ := hs _ _ h
        exact (not_lt_of_ge (hside.mp hx)) hy
      · obtain ⟨hy, hx⟩ := hs _ _ h
        exact (not_lt_of_ge (hside.mpr hy)) hx
    exact c.valid hweak (congrArg Prod.snd he))
  simpa using C.colorable

theorem six_color_side {G : SimpleGraph V} (b : V → Fin r) (w m : Fin r → Fin r → ℕ)
    (ordered : ∀ i j k l, i < j → k < l → Later i j k l → m k l ≤ w i j + 1)
    (mix : ∀ (A B : Set V) i j, i < j → m i j ≤ mass b A i → m i j ≤ mass b B j →
      ∃ a ∈ A, ∃ z ∈ B, G.Adj a z)
    (weak : ∀ X, (WeakGraph G b w X).Colorable 3)
    {A B : Set V} (h : Anti G A B) : (G.induce A).Colorable 6 ∨ (G.induce B).Colorable 6 := by
  have h' : Anti G B A := ⟨h.1.symm, fun z hz a ha e => h.2 a ha z hz e.symm⟩
  have hc := cut_alternative (Strong b w A) (Strong b w B)
    (fun _ _ hh => hh.elim And.left And.left) (no_cross ordered mix h) (no_cross ordered mix h')
  exact hc.imp (color_of_cut G b w A 3 (weak A)) (color_of_cut G b w B 3 (weak B))

end Erdos1111Blocks
end

section
open SimpleGraph Finset Erdos1111Blocks
namespace Erdos1111Sparsity
variable {V : Type*}

noncomputable def neighbors (G : SimpleGraph V) (X : Finset V) (v : V) : Finset V := by
  classical exact X.filter (G.Adj v)

lemma mem_neighbors {G : SimpleGraph V} {X : Finset V} {v y : V} :
    y ∈ neighbors G X v ↔ y ∈ X ∧ G.Adj v y := by classical simp [neighbors]

/-- Greedy extension from smaller vertex sets. -/
theorem greedy (G : SimpleGraph V) (q : ℕ) (hq : 0 < q) (X : Finset V)
    (sparse : ∀ Y ⊆ X, Y.Nonempty → ∃ v ∈ Y, (neighbors G Y v).card < q) :
    ∃ f : V → Fin q, ∀ u ∈ X, ∀ v ∈ X, G.Adj u v → f u ≠ f v := by
  classical
  induction X using Finset.strongInductionOn
  rename_i X ih
  rcases X.eq_empty_or_nonempty with rfl | hX
  · exact ⟨fun _ => ⟨0,hq⟩, by simp⟩
  obtain ⟨v,hv,hd⟩ := sparse X (Subset.rfl) hX
  obtain ⟨f,hf⟩ := ih (X.erase v) (erase_ssubset hv)
    (fun Y hY => sparse Y (hY.trans (erase_subset _ _)))
  have hcard : ((neighbors G X v).image f).card < (univ : Finset (Fin q)).card := by
    simpa only [card_univ, Fintype.card_fin] using lt_of_le_of_lt card_image_le hd
  obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨Function.update f v c, ?_⟩
  intro x hx y hy hxy
  by_cases he : x = v
  · subst x
    rw [Function.update_self, Function.update_of_ne hxy.ne.symm]
    exact fun eq => hc (eq ▸ mem_image_of_mem f (mem_neighbors.mpr ⟨hy,hxy⟩))
  · by_cases he' : y = v
    · subst y
      rw [Function.update_of_ne he, Function.update_self]
      exact fun eq => hc (eq ▸ mem_image_of_mem f (mem_neighbors.mpr ⟨hx,hxy.symm⟩))
    · rw [Function.update_of_ne he, Function.update_of_ne he']
      exact hf x (mem_erase.mpr ⟨he,hx⟩) y (mem_erase.mpr ⟨he',hy⟩) hxy

def WeakAmbient {r : ℕ} (G : SimpleGraph V) (b : V → Fin r) (w : Fin r → Fin r → ℕ) (X : Set V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ Strong b w X (b u) (b v) ∧ ¬ Strong b w X (b v) (b u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem mass_mono [Finite V] {r : ℕ} (b : V → Fin r) {X Y : Set V} (h : X ⊆ Y) (i : Fin r) :
    mass b X i ≤ mass b Y i := by
  let f : {v : V // v ∈ X ∧ b v = i} → {v : V // v ∈ Y ∧ b v = i} :=
    fun x => ⟨x.val,h x.property.1,x.property.2⟩
  exact Nat.card_le_card_of_injective f (fun x y e => Subtype.ext (congrArg (fun z : {v : V // v ∈ Y ∧ b v = i} => z.val) e))

lemma strong_mono [Finite V] {r : ℕ} {b : V → Fin r} {w} {X Y : Set V} (h : X ⊆ Y) {i j}
    (hs : Strong b w X i j) : Strong b w Y i j :=
  ⟨hs.1,lt_of_lt_of_le hs.2.1 (mass_mono b h i),lt_of_lt_of_le hs.2.2 (mass_mono b h j)⟩

/-- Ordered-edge version of condition (S) of Liu and Meng. Each weak edge
contributes exactly twice, once at each endpoint. -/
def Sparse [Fintype V] {r : ℕ} (G : SimpleGraph V) (b : V → Fin r) (w : Fin r → Fin r → ℕ) :
    Prop := ∀ Y : Finset V, Y.Nonempty →
      (∑ v ∈ Y, (neighbors (WeakAmbient G b w (Y : Set V)) Y v).card) < 3*Y.card

theorem weak_three_colorable [Fintype V] {r : ℕ} {G : SimpleGraph V} {b : V → Fin r} {w}
    (h : Sparse G b w) (X : Set V) : (WeakGraph G b w X).Colorable 3 := by
  classical
  have hs : ∀ Y ⊆ X.toFinset, Y.Nonempty → ∃ v ∈ Y, (neighbors (WeakAmbient G b w X) Y v).card < 3 := by
    intro Y hY ne
    have sub : (Y : Set V) ⊆ X := fun v hv => Set.mem_toFinset.mp (hY hv)
    by_contra! hbad
    have hh : 3 * Y.card ≤ ∑ v ∈ Y, (neighbors (WeakAmbient G b w (Y : Set V)) Y v).card := by
      calc
        3 * Y.card = ∑ _ ∈ Y, 3 := by simp [Nat.mul_comm]
        _ ≤ _ := sum_le_sum fun v hv => le_trans (hbad v hv) (card_le_card (by
          intro a ha
          obtain ⟨hay,he,h₁,h₂⟩ := mem_neighbors.mp ha
          exact mem_neighbors.mpr ⟨hay,he,fun k => h₁ (strong_mono sub k),fun k => h₂ (strong_mono sub k)⟩))
    exact (h Y ne).not_ge hh
  obtain ⟨f,hf⟩ := greedy (WeakAmbient G b w X) 3 (by decide) _ hs
  exact ⟨Coloring.mk (fun x => f x.val) (fun {x y} e =>
    hf x.val (Set.mem_toFinset.mpr x.property) y.val (Set.mem_toFinset.mpr y.property) e)⟩

theorem six_color_of_sparse [Fintype V] {r : ℕ} {G : SimpleGraph V}
    (b : V → Fin r) (w m : Fin r → Fin r → ℕ)
    (ordered : ∀ i j k l, i < j → k < l → Later i j k l → m k l ≤ w i j + 1)
    (mix : ∀ (A B : Set V) i j, i < j → m i j ≤ mass b A i → m i j ≤ mass b B j →
      ∃ a ∈ A, ∃ z ∈ B, G.Adj a z) (h : Sparse G b w)
    {A B : Set V} (hab : Anti G A B) : (G.induce A).Colorable 6 ∨ (G.induce B).Colorable 6 :=
  six_color_side b w m ordered mix (weak_three_colorable h) hab

end Erdos1111Sparsity
end

section
open SimpleGraph Erdos1111Blocks
namespace Erdos1111Transfer
variable {V : Type*} {G : SimpleGraph V}

def OneSide (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ A B, Anti G A B → (G.induce A).Colorable n ∨ (G.induce B).Colorable n

theorem oneSide_induce {n : ℕ} (h : OneSide G n) (S : Set V) : OneSide (G.induce S) n := by
  intro A B hAB
  let f : S → V := Subtype.val
  have him : Anti G (f '' A) (f '' B) := by
    constructor
    · apply Set.disjoint_left.mpr
      rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
      exact Set.disjoint_left.mp hAB.1 ha (Subtype.val_injective he ▸ hb)
    · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
      exact hAB.2 a ha b hb
  have pull : ∀ X : Set S, (G.induce (f '' X)).Colorable n →
      ((G.induce S).induce X).Colorable n := by
    intro X hc
    apply Colorable.of_hom _ hc
    exact ⟨fun x => ⟨f x.val, x.val, x.property, rfl⟩, fun e => e⟩
  exact (h _ _ him).imp (pull A) (pull B)
end Erdos1111Transfer
end

section
open SimpleGraph Finset Erdos1111Blocks Erdos1111Sparsity Erdos1111Transfer
namespace Erdos1111Endgame

def Mixing {V : Type*} {r : ℕ} (G : SimpleGraph V) (b : V → Fin r) (m : Fin r → Fin r → ℕ) :=
  ∀ (A B : Set V) i j, i < j → m i j ≤ mass b A i → m i j ≤ mass b B j →
    ∃ a ∈ A, ∃ z ∈ B, G.Adj a z

variable {V : Type*} [Fintype V] {r : ℕ}
omit [Fintype V] in
lemma mass_filter (b : V → Fin r) (I : Finset V) (i : Fin r) :
    mass b (I : Set V) i = (I.filter (fun v => b v = i)).card := by
  classical
  let e : {v : V // v ∈ (I : Set V) ∧ b v = i} ≃ ↥(I.filter (fun v => b v = i)) :=
    Equiv.subtypeEquivRight (fun v => by simp)
  exact (Nat.card_congr e).trans (Nat.card_eq_fintype_card.trans (Fintype.card_coe _))
omit [Fintype V] in
lemma card_eq_sum_mass (b : V → Fin r) (I : Finset V) :
    I.card = ∑ i, mass b (I : Set V) i := by
  classical
  simp_rw [mass_filter]
  exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)

theorem independent_bound {G : SimpleGraph V} (b : V → Fin r) (m : Fin r → Fin r → ℕ)
    (mix : Mixing G b m) (n t : ℕ) (blocks : ∀ i, mass b Set.univ i ≤ n)
    (cutoff : ∀ i j, i < j → m i j ≤ t) (I : Finset V)
    (ind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) : I.card ≤ n+r*t := by
  classical
  let a (i : Fin r) := mass b (I : Set V) i
  have unique : ∀ i j, i < j → t ≤ a i → t ≤ a j → False := by
    intro i j hij hi hj
    obtain ⟨x,hx,y,hy,e⟩ := mix I I i j hij ((cutoff i j hij).trans hi) ((cutoff i j hij).trans hj)
    exact ind x hx y hy e
  rw [card_eq_sum_mass b I]
  by_cases h : ∃ i, t ≤ a i
  · obtain ⟨i,hi⟩ := h
    have point : ∀ j, a j ≤ (if j = i then n else 0) + t := by
      intro j
      by_cases e : j = i
      · subst j
        have hc := (mass_mono b (Set.subset_univ (I : Set V)) i).trans (blocks i)
        simpa [a] using le_trans hc (Nat.le_add_right n t)
      · have : ¬ t ≤ a j := by
          intro hj
          rcases lt_or_gt_of_ne e with hj' | hj'
          · exact unique j i hj' hj hi
          · exact unique i j hj' hi hj
        simp [e]
        omega
    calc
      ∑ j, mass b (I : Set V) j ≤ ∑ j, ((if j = i then n else 0) + t) := sum_le_sum fun j _ => point j
      _ = _ := by simp [sum_add_distrib]
  · have bound : (∑ i, a i) ≤ ∑ _ : Fin r, t := sum_le_sum fun i _ => le_of_lt (lt_of_not_ge fun e => h ⟨i,e⟩)
    simpa [a] using bound.trans (by simp)

omit [Fintype V] in
theorem size_of_colorable {G : SimpleGraph V} (S : Finset V) (q K : ℕ)
    (bound : ∀ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) → I.card ≤ K)
    (hc : (G.induce (S : Set V)).Colorable q) : S.card ≤ q*K := by
  classical
  obtain ⟨c⟩ := hc
  let f : ↥S → Fin q := fun v => c v
  have ha (j : Fin q) : (univ.filter (fun v : ↥S => f v = j)).card ≤ K := by
    let I := (univ.filter (fun v : ↥S => f v = j)).map (Function.Embedding.subtype (· ∈ S))
    have h := bound I (by
      intro x hx y hy e
      change x ∈ (univ.filter (fun v : ↥S => f v = j)).map _ at hx
      change y ∈ (univ.filter (fun v : ↥S => f v = j)).map _ at hy
      obtain ⟨x',hx',ex⟩ := mem_map.mp hx
      obtain ⟨y',hy',ey⟩ := mem_map.mp hy
      have ex' : x'.val = x := ex
      have ey' : y'.val = y := ey
      have hxy : (G.induce (S : Set V)).Adj x' y' := by
        change G.Adj x'.val y'.val
        simpa [ex',ey'] using e
      exact c.valid hxy ((show f x' = j from (mem_filter.mp hx').2).trans
        (show f y' = j from (mem_filter.mp hy').2).symm))
    simpa [I] using h
  have he := card_eq_sum_card_fiberwise (s := (univ : Finset ↥S)) (t := univ) (f := f)
    (fun _ _ => mem_univ _)
  have h := (le_of_eq he).trans (sum_le_sum (s := univ) fun j _ => ha j)
  simpa using h

noncomputable def triangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical exact univ.filter (G.IsNClique 3)

/-- Delete at most one vertex per triangle, counting collisions only once. -/
theorem clear_triangles (G : SimpleGraph V) :
    ∃ S : Finset V, Fintype.card V ≤ S.card + (triangles G).card ∧ (G.induce (S : Set V)).CliqueFree 3 := by
  classical
  let T := triangles G
  have hne (s : ↥T) : s.val.Nonempty := by
    have h := (mem_filter.mp s.property).2
    have h3 : s.val.card = 3 := (show G.IsNClique 3 s.val from h).2
    exact card_pos.mp (by omega)
  let bad := univ.image (fun s : ↥T => (hne s).choose)
  let S := univ \ bad
  refine ⟨S, ?_, ?_⟩
  · have h1 := card_sdiff_add_card_eq_card (show bad ⊆ (univ : Finset V) from subset_univ _)
    have h2 : bad.card ≤ (triangles G).card := by
      simpa [bad,T] using (card_image_le (s := (univ : Finset ↥T)) (f := fun s : ↥T => (hne s).choose))
    simp only [card_univ] at h1
    change Fintype.card V ≤ (univ \ bad).card + (triangles G).card
    omega
  · intro s hs
    let z := s.map (Function.Embedding.subtype (· ∈ S))
    have hz : G.IsNClique 3 z := (isNClique_induce_iff (S : Set V) s 3).mp hs
    let u : ↥T := ⟨z, mem_filter.mpr ⟨mem_univ _,hz⟩⟩
    have hbad : (hne u).choose ∈ bad := mem_image_of_mem _ (mem_univ u)
    obtain ⟨v,_,hv⟩ := mem_map.mp (hne u).choose_spec
    have ev : v.val = (hne u).choose := hv
    exact (mem_sdiff.mp v.property).2 (ev.symm ▸ hbad)

/-- A single remaining finite existence statement of the random-block type.
The block size is r*t. All conditions concern the unmodified graph. -/
def BlockRealization : Prop :=
  ∀ d : ℕ, let r := 2*d+2
    ∃ t : ℕ, 0 < t ∧
    ∃ G : SimpleGraph (Fin r × Fin (r*t)), ∃ w m : Fin r → Fin r → ℕ,
      (∀ i j k l, i < j → k < l → Later i j k l → m k l ≤ w i j + 1) ∧
      (∀ i j, i < j → m i j ≤ t) ∧ Mixing G Prod.fst m ∧ Sparse G Prod.fst w ∧
      (triangles G).card ≤ r*t

theorem counterexamples (sample : BlockRealization) (d : ℕ) :
    ∃ N : ℕ, ∃ S : Finset (Fin (2*d+2) × Fin N),
      ∃ H : SimpleGraph (S : Set (Fin (2*d+2) × Fin N)),
      H.CliqueFree 3 ∧ (d : ℕ∞) ≤ H.chromaticNumber ∧ OneSide H 6 := by
  classical
  let r := 2*d+2
  obtain ⟨t,ht,G,w,m,order,cutoff,mix,hs,htri⟩ := sample d
  let n := r*t
  have hn : 0 < n := Nat.mul_pos (by dsimp [r]; omega) ht
  have blocks (i : Fin r) : mass (Prod.fst : Fin r × Fin n → Fin r) Set.univ i ≤ n := by
    let f (v : {v : Fin r × Fin n // v ∈ (Set.univ : Set (Fin r × Fin n)) ∧ v.1 = i}) : Fin n := v.val.2
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (Prod.ext (x.property.2.trans y.property.2.symm) he)
    simpa [mass] using Nat.card_le_card_of_injective f hf
  obtain ⟨S,hsize,hfree⟩ := clear_triangles G
  refine ⟨n,S,G.induce (S : Set _),hfree,?_,
    oneSide_induce (fun _ _ h => six_color_of_sparse Prod.fst w m order mix hs h) _⟩
  cases d with
  | zero => simp
  | succ a =>
    apply Erdos640Reduction.high_iff_not_colorable.mpr
    intro hc
    have hsmall := size_of_colorable S a (n+r*t)
      (independent_bound Prod.fst m mix n t blocks cutoff) hc
    have hsize' : r*n ≤ S.card + (triangles G).card := by simpa [r,n] using hsize
    change (triangles G).card ≤ n at htri
    have hh : r*n ≤ a*(n+n)+n := hsize'.trans (Nat.add_le_add hsmall htri)
    dsimp [r] at hh
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.two_mul] at hh
    omega

/-- The quantifiers and inequalities of the upstream declaration, in every
vertex universe. The graph witnessing failure is transported from Type 0. -/
theorem disproof_of_realization (sample : BlockRealization) :
    ¬ (∀ t c : ℕ, 1 ≤ t → 1 ≤ c → ∃ d : ℕ, 1 ≤ d ∧
      ∀ (W : Type*) [Finite W] (G : SimpleGraph W),
        (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
          ∃ A B : Set W, Anti G A B ∧
            (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
            (c : ℕ∞) ≤ (G.induce B).chromaticNumber) := by
  classical
  intro hall
  obtain ⟨d,_,hd⟩ := hall 3 7 (by decide) (by decide)
  obtain ⟨N,S,H,hfree,hchi,hside⟩ := counterexamples sample d
  let e : ULift ↥S ≃ ↥S := Equiv.ulift
  let I := Iso.comap e H
  obtain ⟨A,B,hab,ha,hb⟩ := hd _ (H.comap e) (hchi.trans_eq (chromaticNumber_congr I).symm)
    (hfree.comap I.toEmbedding.isContained)
  have himg : Anti H (e '' A) (e '' B) := by
    constructor
    · apply Set.disjoint_left.mpr
      rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
      exact Set.disjoint_left.mp hab.1 ha (e.injective he ▸ hb)
    · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
      exact hab.2 a ha b hb
  have pull (X : Set (ULift ↥S)) (hc : (H.induce (e '' X)).Colorable 6) :
      ((H.comap e).induce X).Colorable 6 := by
    apply Colorable.of_hom _ hc
    exact ⟨fun x => ⟨e x.val,x.val,x.property,rfl⟩,fun adj => adj⟩
  exact (hside _ _ himg).elim (fun ca => Erdos640Reduction.high_iff_not_colorable.mp ha (pull A ca))
    (fun cb => Erdos640Reduction.high_iff_not_colorable.mp hb (pull B cb))

end Erdos1111Endgame
end

section
open Finset
open scoped NNReal
noncomputable section
namespace Erdos1111Sampling
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- An independent bit for each possible edge, with edge-specific weights. -/
def weight (p : E → Bool → ℝ≥0) (x : E → Bool) : ℝ≥0 := ∏ e, p e (x e)

noncomputable def prob (p : E → Bool → ℝ≥0) (A : (E → Bool) → Prop) : ℝ≥0 := by
  classical exact ∑ x, if A x then weight p x else 0

theorem expectation_product (p f : E → Bool → ℝ≥0) :
    (∑ x, weight p x * ∏ e, f e (x e)) =
      ∏ e, (p e false * f e false + p e true * f e true) := by
  classical
  simp only [weight, ← prod_mul_distrib]
  have h := prod_univ_sum (ι := E) (fun _ => (univ : Finset Bool))
    (fun e j => p e j * f e j)
  rw [Fintype.piFinset_univ] at h
  simpa only [Fintype.sum_bool, add_comm] using h.symm

/-- Exact probability that every edge in S takes a specified value. -/
theorem cylinder (p : E → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (S : Finset E) (b : Bool) :
    prob p (fun x => ∀ e ∈ S, x e = b) = ∏ e ∈ S, p e b := by
  classical
  let f (e : E) (v : Bool) : ℝ≥0 := if e ∈ S → v = b then 1 else 0
  have event (x : E → Bool) : (∏ e, f e (x e)) = if ∀ e ∈ S, x e = b then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one fun e _ => if_pos (h e)
    · push Not at h
      obtain ⟨e,he,hb⟩ := h
      exact prod_eq_zero (mem_univ e) (by simp [f,he,hb])
  have localFactor (e : E) : p e false * f e false + p e true * f e true =
      if e ∈ S then p e b else 1 := by
    by_cases he : e ∈ S <;> cases b <;> simp [f,he,norm]
  calc
    _ = ∑ x, weight p x * ∏ e, f e (x e) := by
      unfold prob
      apply sum_congr rfl
      intro x _
      by_cases h : ∀ e ∈ S, x e = b <;> simp [event,h]
    _ = _ := by simpa only [localFactor,prod_ite_mem_eq] using expectation_product p f

theorem probability_one (p : E → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1) :
    (∑ x, weight p x) = 1 := by
  simpa [prob] using cylinder p norm ∅ false

theorem union_bound {J : Type*} (p : E → Bool → ℝ≥0) (J₀ : Finset J)
    (A : J → (E → Bool) → Prop) :
    prob p (fun x => ∃ j ∈ J₀, A j x) ≤ ∑ j ∈ J₀, prob p (A j) := by
  classical
  unfold prob
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  split_ifs with hx
  · obtain ⟨j,hj,ha⟩ := hx
    exact le_trans (by simp [ha] : weight p x ≤ (if A j x then weight p x else 0))
      (single_le_sum (f := fun j => if A j x then weight p x else 0) (fun _ _ => zero_le) hj)
  · exact zero_le

/-- The weak-edge upper-tail estimate before simplifying the elementary
symmetric polynomial. The edge probabilities need not be equal. -/
theorem weak_edge_tail (p : E → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (W : Finset E) (q : ℕ) :
    prob p (fun x => q ≤ (W.filter (fun e => x e = true)).card) ≤
      ∑ T ∈ W.powersetCard q, ∏ e ∈ T, p e true := by
  classical
  have event (x : E → Bool) : q ≤ (W.filter (fun e => x e = true)).card ↔
      ∃ T ∈ W.powersetCard q, ∀ e ∈ T, x e = true := by
    constructor
    · intro h
      obtain ⟨T,hT,hcard⟩ := exists_subset_card_eq h
      exact ⟨T, mem_powersetCard.mpr ⟨hT.trans (filter_subset _ _),hcard⟩,
        fun e he => (mem_filter.mp (hT he)).2⟩
    · rintro ⟨T,hT,ht⟩
      obtain ⟨hsub,rfl⟩ := mem_powersetCard.mp hT
      exact card_le_card fun e he => mem_filter.mpr ⟨hsub he,ht e he⟩
  simp_rw [event]
  exact (union_bound p (W.powersetCard q) (fun T x => ∀ e ∈ T, x e = true)).trans
    (le_of_eq (sum_congr rfl fun T _ => cylinder p norm T true))

/-- Elementary symmetric polynomials of edge probabilities. -/
def elem (a : E → ℝ≥0) (W : Finset E) (q : ℕ) : ℝ≥0 :=
  ∑ T ∈ W.powersetCard q, ∏ e ∈ T, a e

omit [Fintype E] in
theorem elem_insert (a : E → ℝ≥0) (W : Finset E) {v : E} (hv : v ∉ W) (q : ℕ) :
    elem a (insert v W) (q+1) = elem a W (q+1) + a v * elem a W q := by
  classical
  have avoid {T : Finset E} {k} (h : T ∈ W.powersetCard k) : v ∉ T :=
    fun ht => hv ((mem_powersetCard.mp h).1 ht)
  have hd : Disjoint (W.powersetCard (q+1)) ((W.powersetCard q).image (insert v)) := by
    apply Finset.disjoint_left.mpr
    intro z h hm
    obtain ⟨T,_,e⟩ := mem_image.mp hm
    exact avoid h (e ▸ mem_insert_self v T)
  unfold elem
  rw [powersetCard_succ_insert hv, sum_union hd, sum_image, mul_sum]
  · congr 1
    apply sum_congr rfl
    intro T hT
    exact prod_insert (avoid hT)
  · intro A hA B hB he
    have heq := congrArg (fun t : Finset E => t.erase v) he
    simpa [erase_insert (avoid hA),erase_insert (avoid hB)] using heq

omit [Fintype E] in
theorem factorial_elem_bound (a : E → ℝ≥0) (W : Finset E) (q : ℕ) :
    (q.factorial : ℝ≥0) * elem a W q ≤ (∑ e ∈ W, a e)^q := by
  classical
  induction W using Finset.induction_on generalizing q with
  | empty =>
    cases q with
    | zero => simp [elem]
    | succ k => simp [elem]
  | @insert v W hv ih =>
    cases q with
    | zero => simp [elem]
    | succ q =>
      rw [elem_insert a W hv, sum_insert hv]
      let U := ∑ e ∈ W, a e
      calc
        _ = ((q+1).factorial : ℝ≥0) * elem a W (q+1) +
            ((q+1 : ℕ) : ℝ≥0) * (((q.factorial : ℝ≥0) * elem a W q) * a v) := by
          rw [Nat.factorial_succ, Nat.cast_mul]; ring
        _ ≤ U^(q+1) + ((q+1 : ℕ) : ℝ≥0) * (U^q * a v) :=
          add_le_add (ih (q+1)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ih q) zero_le) zero_le)
        _ ≤ _ := by
          change U^(q+1) + ((q+1 : ℕ) : ℝ≥0) * (U^q * a v) ≤ (a v + U)^(q+1)
          rw [add_comm (a v) U]
          simpa only [Nat.add_sub_cancel, mul_assoc] using
            (pow_add_mul_le_add_pow (a := U) (b := a v) zero_le zero_le (q+1))

/-- The factorial-moment inequality used for the sparse weak edges in Lemma 3. -/
theorem factorial_tail (p : E → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (W : Finset E) (q : ℕ) :
    (q.factorial : ℝ≥0) * prob p (fun x => q ≤ (W.filter (fun e => x e = true)).card) ≤
      (∑ e ∈ W, p e true)^q :=
  (mul_le_mul_of_nonneg_left (weak_edge_tail p norm W q) zero_le).trans (factorial_elem_bound _ _ _)

end Erdos1111Sampling
end
end

section
open SimpleGraph Finset Erdos1111Sampling Erdos1111Endgame
open scoped NNReal
noncomputable section
namespace Erdos1111RandomGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

def graph (x : Sym2 V → Bool) : SimpleGraph V := fromEdgeSet {e | x e = true}

def cross (A B : Finset V) := (A ×ˢ B).image (fun z => s(z.1,z.2))

omit [Fintype V] in
theorem cross_card (A B : Finset V) (h : Disjoint A B) : (cross A B).card = A.card * B.card := by
  rw [cross, card_image_of_injOn, card_product]
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd e
  obtain ⟨ea,eb⟩ | ⟨ea,_⟩ := Sym2.eq_iff.mp e
  · exact Prod.ext ea eb
  · exact False.elim (disjoint_left.mp h (mem_product.mp hab).1 (ea.symm ▸ (mem_product.mp hcd).2))

theorem missing_rectangle (p : Sym2 V → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (A B : Finset V) (h : Disjoint A B) :
    prob p (fun x => ∀ a ∈ A, ∀ b ∈ B, ¬ (graph x).Adj a b) = ∏ e ∈ cross A B, p e false := by
  classical
  rw [← cylinder p norm]
  congr 1
  funext x
  apply propext
  constructor
  · intro hn e he
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp he
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    have hn' := hn a ha b hb
    have hne : a ≠ b := fun eq => disjoint_left.mp h ha (eq.symm ▸ hb)
    cases val : x s(a,b)
    · rfl
    · exact False.elim (hn' ⟨val,hne⟩)
  · intro hc a ha b hb e
    have hmem : (a,b) ∈ A ×ˢ B := mem_product.mpr ⟨ha,hb⟩
    have hf := hc s(a,b) (mem_image_of_mem (fun z : V × V => s(z.1,z.2)) hmem)
    exact Bool.false_ne_true (hf.symm.trans e.1)

theorem triangle_probability (p : Sym2 V → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    prob p (fun x => (graph x).IsClique ({a,b,c} : Set V)) =
      p s(a,b) true * p s(a,c) true * p s(b,c) true := by
  classical
  let T : Finset (Sym2 V) := {s(a,b),s(a,c),s(b,c)}
  have hprob := cylinder p norm T true
  have hmem (x : Sym2 V → Bool) : (graph x).IsClique ({a,b,c} : Set V) ↔ ∀ e ∈ T, x e = true := by
    constructor
    · intro hh e he
      simp only [T, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact (hh (by simp) (by simp) hab).1
      · exact (hh (by simp) (by simp) hac).1
      · exact (hh (by simp) (by simp) hbc).1
    · intro hh
      have ab : (graph x).Adj a b := ⟨hh _ (by simp [T]),hab⟩
      have ac : (graph x).Adj a c := ⟨hh _ (by simp [T]),hac⟩
      have bc : (graph x).Adj b c := ⟨hh _ (by simp [T]),hbc⟩
      intro u hu v hv hn
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | exact (hn rfl).elim | exact ab | exact ac | exact bc | exact ab.symm | exact ac.symm | exact bc.symm
  simp_rw [hmem]
  rw [hprob]
  have e₁ : s(a,b) ≠ s(a,c) := by simp [Sym2.eq_iff, hab, hac, hbc]
  have e₂ : s(a,b) ≠ s(b,c) := by simp [Sym2.eq_iff, hab, hac, hbc]
  have e₃ : s(a,c) ≠ s(b,c) := by simp [Sym2.eq_iff, hab, hac, hbc]
  simp [T,e₁,e₂,e₃,mul_assoc]

/-- Relate the expected number of triangles directly to its graph definition. -/
theorem expected_triangles (p : Sym2 V → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (D : ℝ≥0) (hp : ∀ e, p e true ≤ D) :
    (∑ x, weight p x * ((triangles (graph x)).card : ℝ≥0)) ≤
      ((Fintype.card V).choose 3 : ℝ≥0) * D^3 := by
  classical
  let T := (univ : Finset V).powersetCard 3
  have hcount (x : Sym2 V → Bool) : triangles (graph x) = T.filter (fun s : Finset V => (graph x).IsClique (s : Set V)) := by
    ext s
    simp [triangles,T,isNClique_iff,and_comm]
  have hexp (x : Sym2 V → Bool) : weight p x * ((triangles (graph x)).card : ℝ≥0) =
      ∑ s ∈ T, if (graph x).IsClique (s : Set V) then weight p x else 0 := by
    rw [hcount, ← sum_filter]
    simp [mul_comm]
  simp_rw [hexp]
  rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ T, D^3 := by
      apply sum_le_sum
      intro s hs
      obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp (mem_powersetCard.mp hs).2
      let A : Set V := (({a,b,c} : Finset V) : Set V)
      have he : (∑ x, if (graph x).IsClique A then weight p x else 0) =
          prob p (fun x => (graph x).IsClique A) := by
        unfold prob
        apply sum_congr rfl
        intro x _
        by_cases h : (graph x).IsClique A <;> simp [h]
      rw [he]
      dsimp only [A]
      simp only [coe_insert,coe_singleton]
      rw [triangle_probability p norm hab hac hbc]
      calc
        _ ≤ D*D*D := mul_le_mul' (mul_le_mul' (hp _) (hp _)) (hp _)
        _ = D^3 := by ring
    _ = _ := by simp [T,card_powersetCard]

theorem triangle_tail (p : Sym2 V → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (D : ℝ≥0) (hp : ∀ e, p e true ≤ D) (n : ℕ) :
    (n+1 : ℕ) * prob p (fun x => n < (triangles (graph x)).card) ≤
      ((Fintype.card V).choose 3 : ℝ≥0) * D^3 := by
  classical
  apply le_trans _ (expected_triangles p norm D hp)
  unfold prob
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  split_ifs with h
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) zero_le
  · simp

open Erdos1111Blocks Erdos1111Sparsity

/-- For a fixed candidate vertex set, the weak-pair test is determined
before edges are sampled. Extend the induced weak graph by isolated vertices. -/
def internalWeak {r : ℕ} (G : SimpleGraph V) (b : V → Fin r) (w : Fin r → Fin r → ℕ)
    (Y : Finset V) : SimpleGraph V where
  Adj u v := u ∈ Y ∧ v ∈ Y ∧ (WeakAmbient G b w (Y : Set V)).Adj u v
  symm := ⟨fun _ _ h => ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.ne rfl⟩

noncomputable def slots {r : ℕ} (b : V → Fin r) (w : Fin r → Fin r → ℕ) (Y : Finset V) :
    Finset (Sym2 V) := by
  classical exact (internalWeak ⊤ b w Y).edgeFinset

noncomputable def weakDegreeSum {r : ℕ} (G : SimpleGraph V) (b : V → Fin r) (w : Fin r → Fin r → ℕ)
    (Y : Finset V) : ℕ := ∑ v ∈ Y, (neighbors (WeakAmbient G b w (Y : Set V)) Y v).card

theorem degreeSum_slots {r : ℕ} (x : Sym2 V → Bool) (b : V → Fin r)
    (w : Fin r → Fin r → ℕ) (Y : Finset V) :
    weakDegreeSum (graph x) b w Y = 2*((slots b w Y).filter (fun e => x e = true)).card := by
  classical
  let K := internalWeak (graph x) b w Y
  have hdeg (v : V) : K.degree v =
      if v ∈ Y then (neighbors (WeakAmbient (graph x) b w (Y : Set V)) Y v).card else 0 := by
    rw [← card_neighborFinset_eq_degree]
    by_cases hv : v ∈ Y
    · rw [if_pos hv]
      congr 1
      ext z
      rw [mem_neighborFinset,mem_neighbors]; change (_ ∧ _ ∧ _) ↔ _; simp [hv]
    · rw [if_neg hv, card_eq_zero]
      ext z
      rw [mem_neighborFinset]; change (_ ∧ _ ∧ _) ↔ _; simp [hv]
  have he : K.edgeFinset = (slots b w Y).filter (fun e => x e = true) := by
    ext e
    induction e using Sym2.ind with
    | _ a z =>
      simp only [slots,mem_filter,mem_edgeFinset,mem_edgeSet]
      change (a ∈ Y ∧ z ∈ Y ∧ (x s(a,z) = true ∧ a ≠ z) ∧ _) ↔
        (a ∈ Y ∧ z ∈ Y ∧ (a ≠ z) ∧ _) ∧ x s(a,z) = true
      tauto
  have hh := K.sum_degrees_eq_twice_card_edges
  simp_rw [hdeg,he] at hh
  simpa only [←sum_filter,filter_mem_eq_inter,univ_inter,weakDegreeSum] using hh

/-- Exact connection between condition (S) and the independent-edge
factorial bound, for each of the vertex sets occurring in the union bound. -/
theorem weak_failure {r : ℕ} (p : Sym2 V → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1)
    (b : V → Fin r) (w : Fin r → Fin r → ℕ) (Y : Finset V) :
    let q := (3*Y.card+1)/2
    (q.factorial : ℝ≥0)*prob p (fun x => 3*Y.card ≤ weakDegreeSum (graph x) b w Y) ≤
      (∑ e ∈ slots b w Y, p e true)^q := by
  dsimp only
  have h (x : Sym2 V → Bool) :
      (3*Y.card ≤ weakDegreeSum (graph x) b w Y) ↔
      (3*Y.card+1)/2 ≤ ((slots b w Y).filter (fun e => x e = true)).card := by
    rw [degreeSum_slots]
    omega
  simp_rw [h]
  exact factorial_tail p norm _ _

end Erdos1111RandomGraph
end
end

section
namespace Erdos1111Estimates
/-- The elementary factorial estimate required by both union bounds. -/
theorem factorial_bound (k : ℕ) : (k : ℝ)^k ≤ 3^k * k.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have he : Real.exp (k : ℝ) ≤ 3^k := by
    simpa only [← Real.exp_nat_mul, mul_one] using
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  exact (div_le_iff₀ (by positivity : 0 < (k.factorial : ℝ))).mp (h.trans he)

/-- A single weak pair contributes at most the geometric interpolation of
its density cutoff and the total number of chosen vertices. -/
theorem weak_interpolation (D u m : ℝ) (hu : 0 ≤ u) (hum : u ≤ m)
    (hsmall : D^8*u ≤ 1) : D^4 * (D*u)^4 ≤ m^3 := by
  calc
    _ = (D^8*u)*u^3 := by ring
    _ ≤ 1*u^3 := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ _ := by simpa using pow_le_pow_left₀ hu hum 3

theorem sparse_union_term (N m q : ℕ) (hm : 0 < m) (hmq : m ≤ q) (hq : 4*m ≤ 3*q)
    (y P μ : ℝ) (hy : 0 < y) (hy' : y ≤ 1) (hP : 0 ≤ P) (hμ : 0 ≤ μ)
    (hscale : (N : ℝ)*y^4 = m) (hmean : 48*μ ≤ (q : ℝ)*y^3)
    (htail : (q.factorial : ℝ) * P ≤ μ^q) :
    (N.choose m : ℝ) * P ≤ (3/16 : ℝ)^m := by
  have hpq : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le hm hmq
  have hpm : (0 : ℝ) < m := by exact_mod_cast hm
  have hfq : (0 : ℝ) < q.factorial := by positivity
  have hfm : (0 : ℝ) < m.factorial := by positivity
  have hqbound : P ≤ (y^3/16)^q := by
    apply (le_of_mul_le_mul_left (a := (q : ℝ)^q) _ (by positivity))
    calc
      _ ≤ (3^q * (q.factorial : ℝ))*P := mul_le_mul_of_nonneg_right (factorial_bound q) hP
      _ ≤ 3^q * μ^q := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (3*μ)^q := (mul_pow ..).symm
      _ ≤ ((q : ℝ)*(y^3/16))^q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ = _ := mul_pow ..
  have hc : (N.choose m : ℝ)*y^(4*m) ≤ 3^m := by
    have hh := (le_div_iff₀ hfm).mp (Nat.choose_le_pow_div (α := ℝ) m N)
    have h1 := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (y^4)^m)
    have heq : (N : ℝ)^m*(y^4)^m = (m : ℝ)^m := by rw [←mul_pow,hscale]
    rw [heq] at h1
    apply le_of_mul_le_mul_right (a := (m.factorial : ℝ)) _ hfm
    calc
      _ = (N.choose m : ℝ)*m.factorial*(y^4)^m := by rw [pow_mul]; ring
      _ ≤ _ := h1.trans (factorial_bound m)
  have hyp : y^(3*q) ≤ y^(4*m) := pow_le_pow_of_le_one hy.le hy' hq
  have h16 : (1/16 : ℝ)^q ≤ (1/16 : ℝ)^m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmq
  calc
    _ ≤ (N.choose m : ℝ)*(y^3/16)^q := mul_le_mul_of_nonneg_left hqbound (by positivity)
    _ = (N.choose m : ℝ)*y^(3*q)*(1/16 : ℝ)^q := by rw [pow_mul,div_pow,div_pow]; ring
    _ ≤ ((N.choose m : ℝ)*y^(4*m))*(1/16 : ℝ)^m :=
      mul_le_mul (mul_le_mul_of_nonneg_left hyp (by positivity)) h16 (by positivity) (by positivity)
    _ ≤ 3^m*(1/16 : ℝ)^m := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [←mul_pow]; norm_num

end Erdos1111Estimates
end

section
open Finset SimpleGraph Erdos1111Sampling Erdos1111RandomGraph Erdos1111Estimates
open scoped NNReal
noncomputable section
namespace Erdos1111Union
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite geometric budget independent of the number of vertices. -/
theorem budget (N : ℕ) : (∑ k ∈ range N, (3/16 : ℝ)^(k+1)) ≤ 3/13 := by
  have h : (∑ k ∈ range N, (3/16 : ℝ)^(k+1)) = (3/13)*(1-(3/16 : ℝ)^N) := by
    induction N with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih,pow_succ]; ring
  rw [h]
  have : 0 ≤ (3/16 : ℝ)^N := by positivity
  linarith

/-- If the Liu–Meng mean bound is available for each nonempty vertex set,
all the weak-sparsity failures together have probability at most 3/13. -/
theorem probability_not_sparse {r : ℕ} (p : Sym2 V → Bool → ℝ≥0)
    (norm : ∀ e, p e false + p e true = 1) (b : V → Fin r) (w : Fin r → Fin r → ℕ)
    (mean : ∀ Y : Finset V, Y.Nonempty → ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧
      (Fintype.card V : ℝ)*y^4 = Y.card ∧
      48*((∑ e ∈ slots b w Y, p e true : ℝ≥0) : ℝ) ≤ (( (3*Y.card+1)/2 : ℕ) : ℝ)*y^3) :
    (prob p (fun x => ¬ Erdos1111Sparsity.Sparse (graph x) b w) : ℝ) ≤ 3/13 := by
  classical
  let N := Fintype.card V
  let bad (Y : Finset V) (x : Sym2 V → Bool) := 3*Y.card ≤ weakDegreeSum (graph x) b w Y
  let sets (m : ℕ) := (univ : Finset V).powersetCard m
  have hsingle (Y : Finset V) (hne : Y.Nonempty) :
      (N.choose Y.card : ℝ) * (prob p (bad Y) : ℝ) ≤ (3/16 : ℝ)^Y.card := by
    obtain ⟨y,hy,hy',hs,hm⟩ := mean Y hne
    let q := (3*Y.card+1)/2
    have ht := weak_failure p norm b w Y
    have ht' : (q.factorial : ℝ) * (prob p (bad Y) : ℝ) ≤
        ((∑ e ∈ slots b w Y, p e true : ℝ≥0) : ℝ)^q := by exact_mod_cast ht
    exact sparse_union_term N Y.card q (card_pos.mpr hne) (by dsimp [q];omega)
      (by dsimp [q];omega) y _ _ hy hy' (by positivity) (by positivity) hs hm ht'
  let someBad (m : ℕ) (x : Sym2 V → Bool) := ∃ Y ∈ sets m, bad Y x
  have hclass (m : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
      (prob p (someBad m) : ℝ) ≤ (3/16 : ℝ)^m := by
    have hcount : (sets m).card = N.choose m := by simp [sets,N,card_powersetCard]
    have hc : (0 : ℝ) < N.choose m := by exact_mod_cast Nat.choose_pos hmN
    have hu := union_bound p (sets m) bad
    have hreal : (prob p (someBad m) : ℝ) ≤ ∑ Y ∈ sets m, (prob p (bad Y) : ℝ) := by exact_mod_cast hu
    apply hreal.trans
    calc
      _ ≤ ∑ _ ∈ sets m, (3/16 : ℝ)^m / N.choose m := by
        apply sum_le_sum
        intro Y hY
        have he := (mem_powersetCard.mp hY).2
        have hh := hsingle Y (card_pos.mp (he.symm ▸ hm))
        rw [he,mul_comm] at hh
        exact (le_div_iff₀ hc).mpr hh
      _ = _ := by
        simp only [sum_const,nsmul_eq_mul,hcount]
        field_simp
  have hevent (x : Sym2 V → Bool) : (¬ Erdos1111Sparsity.Sparse (graph x) b w) ↔
      ∃ k ∈ range N, someBad (k+1) x := by
    constructor
    · intro h
      unfold Erdos1111Sparsity.Sparse at h
      push Not at h
      obtain ⟨Y,hY,hb⟩ := h
      have hpos := card_pos.mpr hY
      have hmax : Y.card ≤ N := card_le_univ Y
      exact ⟨Y.card-1,mem_range.mpr (by omega),Y,mem_powersetCard.mpr ⟨subset_univ _,by omega⟩,hb⟩
    · rintro ⟨k,_,Y,hY,hb⟩ hs
      have hcard := (mem_powersetCard.mp hY).2
      exact (hs Y (card_pos.mp (by omega))).not_ge hb
  simp_rw [hevent]
  have hu := union_bound p (range N) (fun k => someBad (k+1))
  have hu' : ((prob p (fun x => ∃ k ∈ range N, someBad (k+1) x)) : ℝ) ≤
      ∑ k ∈ range N, (prob p (someBad (k+1)) : ℝ) := by exact_mod_cast hu
  exact hu'.trans ((sum_le_sum (fun k hk => hclass (k+1) (by omega) (mem_range.mp hk))).trans (budget N))

end Erdos1111Union
end
end

section
noncomputable section
open SimpleGraph Finset Erdos1111Blocks Erdos1111RandomGraph Erdos1111Sparsity Erdos1111Endgame
open scoped NNReal
namespace Erdos1111Densities
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

lemma ordered_rep (b : V → Fin r) (e : Sym2 V) :
    ∃ z : V × V, s(z.1,z.2) = e ∧ b z.1 ≤ b z.2 := by
  induction e using Sym2.ind with
  | _ a c =>
    rcases le_total (b a) (b c) with h | h
    · exact ⟨(a,c),rfl,h⟩
    · exact ⟨(c,a),Sym2.eq_swap,h⟩

def ends (b : V → Fin r) (e : Sym2 V) : V × V := (ordered_rep b e).choose
def key (b : V → Fin r) (e : Sym2 V) : Fin r × Fin r := (b (ends b e).1,b (ends b e).2)
lemma ends_spec (b : V → Fin r) (e : Sym2 V) :
    s((ends b e).1,(ends b e).2) = e ∧ (key b e).1 ≤ (key b e).2 := (ordered_rep b e).choose_spec

lemma key_mk (b : V → Fin r) {a c : V} (h : b a < b c) : key b s(a,c) = (b a,b c) := by
  obtain ⟨he,hle⟩ := ends_spec b s(a,c)
  change b _ ≤ b _ at hle
  rcases Sym2.eq_iff.mp he with he | he
  · exact Prod.ext (congrArg b he.1) (congrArg b he.2)
  · rw [he.1,he.2] at hle
    exact (not_le_of_gt h hle).elim

def fiber (b : V → Fin r) (Y : Finset V) (i : Fin r) := Y.filter (fun v => b v = i)
def group (b : V → Fin r) (w : Fin r → Fin r → ℕ) (Y : Finset V) (ij : Fin r × Fin r) :=
  (slots b w Y).filter (fun e => key b e = ij)

lemma group_info (b : V → Fin r) (w : Fin r → Fin r → ℕ) (Y : Finset V)
    (ij : Fin r × Fin r) {e : Sym2 V} (h : e ∈ group b w Y ij) :
    ends b e ∈ fiber b Y ij.1 ×ˢ fiber b Y ij.2 ∧ ¬ Strong b w (Y : Set V) ij.1 ij.2 := by
  classical
  obtain ⟨hslot,heq⟩ := mem_filter.mp h
  obtain ⟨ee,_⟩ := ends_spec b e
  rw [←ee] at hslot
  change _ ∈ (internalWeak (⊤ : SimpleGraph V) b w Y).edgeFinset at hslot
  have had := mem_edgeFinset.mp hslot
  change _ ∈ Y ∧ _ ∈ Y ∧ _ ∧ ¬Strong _ _ _ _ _ ∧ _ at had
  have h₁ : b (ends b e).1 = ij.1 := congrArg Prod.fst heq
  have h₂ : b (ends b e).2 = ij.2 := congrArg Prod.snd heq
  exact ⟨mem_product.mpr ⟨mem_filter.mpr ⟨had.1,h₁⟩,mem_filter.mpr ⟨had.2.1,h₂⟩⟩,
    h₁ ▸ h₂ ▸ had.2.2.2.1⟩

theorem group_size (b : V → Fin r) (w : Fin r → Fin r → ℕ) (Y : Finset V) (ij : Fin r × Fin r) :
    (group b w Y ij).card ≤ (fiber b Y ij.1).card*(fiber b Y ij.2).card := by
  classical
  rw [←card_product]
  apply card_le_card_of_injOn (ends b)
  · exact fun e he => (group_info b w Y ij he).1
  · intro e he e' he' h
    exact (ends_spec b e).1.symm.trans ((congrArg (fun z : V × V => s(z.1,z.2)) h).trans (ends_spec b e').1)

/-- Real form of a block-pair contribution. The sizes u and v are counts,
the cube y^3 is the fourth-root scale from the union bound. -/
theorem pair_mean (R n M d u v y : ℝ) (hR : 1 ≤ R) (hn : 0 < n) (hd : 48*R^3 ≤ d)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huM : u ≤ M) (hvM : v ≤ M) (hy : 0 ≤ y)
    (hscale : R*n*y^4 = M) (hweak : d^8*u ≤ n ∨ d^8*v ≤ n) :
    48*R^2*((u*v)*(d/n)) ≤ M*y^3 := by
  have hR0 : 0 < R := by linarith
  have hD : 0 < d := lt_of_lt_of_le (by positivity) hd
  have estimate (s : ℝ) (hs : 0 ≤ s) (hsM : s ≤ M) (hw : d^8*s ≤ n) :
      48*R^2*(d*(s/n)) ≤ y^3 := by
    have hh := Erdos1111Estimates.weak_interpolation d (s/n) (M/n) (by positivity)
      (div_le_div_of_nonneg_right hsM hn.le) (by rw [←mul_div_assoc,div_le_one hn];exact hw)
    have hmean : M/n = R*y^4 := by apply (div_eq_iff hn.ne').mpr; rw [←hscale];ring
    rw [hmean] at hh
    have hR3 : R^3 ≤ R^4 := by
      rw [show (4 : ℕ) = 3+1 by decide, pow_succ]
      exact le_mul_of_one_le_right (by positivity) hR
    have hlarge : (d*(d*(s/n)))^4 ≤ (R*y^3)^4 := by
      calc
        _ = d^4*(d*(s/n))^4 := mul_pow .. 
        _ ≤ _ := hh
        _ = R^3*(y^3)^4 := by ring
        _ ≤ R^4*(y^3)^4 := mul_le_mul_of_nonneg_right hR3 (by positivity)
        _ = _ := (mul_pow ..).symm
    have hone := (pow_le_pow_iff_left₀ (by positivity : 0 ≤ d*(d*(s/n))) (by positivity : 0 ≤ R*y^3) (by decide : 4 ≠ 0)).mp hlarge
    apply (mul_le_mul_iff_right₀ hR0).mp
    calc
      _ = (48*R^3)*(d*(s/n)) := by ring
      _ ≤ d*(d*(s/n)) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ _ := hone
  rcases hweak with h | h
  · calc
      _ = v*(48*R^2*(d*(u/n))) := by ring
      _ ≤ M*y^3 := mul_le_mul hvM (estimate _ hu huM h) (by positivity) (by linarith)
  · calc
      _ = u*(48*R^2*(d*(v/n))) := by ring
      _ ≤ M*y^3 := mul_le_mul huM (estimate _ hv hvM h) (by positivity) (by linarith)


/-- The expected weak-edge contribution of all block pairs, with a
deliberately coarse r² count that the initial density absorbs. -/
theorem total_mean (b : V → Fin r) (D : Fin r → Fin r → ℕ) (n : ℕ) (hr : 1 ≤ r)
    (hn : 0 < n) (Dmin : ∀ i j, i < j → 48*r^3 ≤ D i j)
    (p : Sym2 V → ℝ≥0)
    (mass_eq : ∀ e, (p e : ℝ) = if (key b e).1 < (key b e).2 then
      (D (key b e).1 (key b e).2 : ℝ)/n else 0)
    (Y : Finset V) (y : ℝ) (hy : 0 ≤ y) (hscale : (r : ℝ)*n*y^4 = Y.card) :
    48*((∑ e ∈ slots b (fun i j => n/(D i j)^8) Y, p e : ℝ≥0) : ℝ) ≤
      (((3*Y.card+1)/2 : ℕ) : ℝ)*y^3 := by
  classical
  let w (i j : Fin r) := n/(D i j)^8
  let W := slots b w Y
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have one (ij : Fin r × Fin r) : 48*(r : ℝ)^2 *
      (∑ e ∈ group b w Y ij, (p e : ℝ)) ≤ (Y.card : ℝ)*y^3 := by
    by_cases hne : (group b w Y ij).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp hne]; simp; positivity
    obtain ⟨e,he⟩ := hne
    have keyE := (mem_filter.mp he).2
    have nstrong := (group_info b w Y ij he).2
    have hconst : ∀ a ∈ group b w Y ij, (p a : ℝ) =
        if ij.1 < ij.2 then (D ij.1 ij.2 : ℝ)/n else 0 := by
      intro a ha
      rw [mass_eq,show key b a = ij from (mem_filter.mp ha).2]
    simp_rw [Finset.sum_congr rfl hconst, sum_const, nsmul_eq_mul]
    by_cases hij : ij.1 < ij.2
    swap
    · rw [if_neg hij]; simp; positivity
    rw [if_pos hij]
    let u := (fiber b Y ij.1).card
    let v := (fiber b Y ij.2).card
    have hu : u ≤ Y.card := card_le_card (filter_subset _ _)
    have hv : v ≤ Y.card := card_le_card (filter_subset _ _)
    have ho : u ≤ w ij.1 ij.2 ∨ v ≤ w ij.1 ij.2 := by
      by_contra! h
      exact nstrong ⟨hij, by rw [mass_filter]; exact h.1, by rw [mass_filter];exact h.2⟩
    have hw (z : ℕ) (hz : z ≤ w ij.1 ij.2) : (D ij.1 ij.2 : ℝ)^8*z ≤ n := by
      have h : (D ij.1 ij.2)^8*z ≤ n :=
        (Nat.mul_le_mul_left _ hz).trans (Nat.mul_div_le _ _)
      exact_mod_cast h
    have hgroup : ((group b w Y ij).card : ℝ) ≤ (u : ℝ)*v := by exact_mod_cast group_size b w Y ij
    calc
      _ ≤ 48*(r : ℝ)^2*((u*v)*((D ij.1 ij.2 : ℝ)/n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgroup (by positivity)) (by positivity)
      _ ≤ _ := pair_mean _ _ _ _ _ _ _ hR hN (by exact_mod_cast Dmin _ _ hij)
        (by positivity) (by positivity) (by exact_mod_cast hu) (by exact_mod_cast hv) hy hscale
        (ho.imp (hw u) (hw v))
  have hsum := sum_le_sum (s := (univ : Finset (Fin r × Fin r))) fun ij _ => one ij
  have hf : (∑ ij : Fin r × Fin r, ∑ e ∈ group b w Y ij, (p e : ℝ)) =
      ∑ e ∈ W, (p e : ℝ) := sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
  rw [←mul_sum,hf] at hsum
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul] at hsum
  have hrpos : 0 < (r : ℝ)^2 := by positivity
  have hs : 48 * (∑ e ∈ W, (p e : ℝ)) ≤ (Y.card : ℝ)*y^3 := by
    apply (mul_le_mul_iff_right₀ hrpos).mp
    calc
      _ = 48*(r : ℝ)^2*(∑ e ∈ W, (p e : ℝ)) := by ring
      _ ≤ _ := hsum.trans_eq (by ring)
  rw [NNReal.coe_sum]
  have hq : Y.card ≤ (3*Y.card+1)/2 := by omega
  exact hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hq) (by positivity))


end Erdos1111Densities
end
end

section
noncomputable section
open Finset SimpleGraph Erdos1111Sampling Erdos1111RandomGraph Erdos1111Endgame Erdos1111Blocks
open scoped NNReal
namespace Erdos1111Mixing
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem prob_eq_zero (p : Sym2 V → Bool → ℝ≥0) {B : (Sym2 V → Bool) → Prop}
    (h : ∀ x, ¬ B x) : prob p B = 0 := by classical simp [prob,h]
theorem prob_mono (p : Sym2 V → Bool → ℝ≥0) {A B : (Sym2 V → Bool) → Prop}
    (h : ∀ x, A x → B x) : prob p A ≤ prob p B := by
  classical
  unfold prob
  apply sum_le_sum
  intro x _
  by_cases ha : A x
  · simp [ha,h x ha]
  · simp [ha]

/-- Counting candidate rectangles in the entire host costs at most r² 4^N.
This coarse count suffices because the starting density can depend on r. -/
theorem mixing_failure (b : V → Fin r) (m : Fin r → Fin r → ℕ)
    (p : Sym2 V → Bool → ℝ≥0) (norm : ∀ e, p e false + p e true = 1) (ε : ℝ≥0)
    (miss : ∀ i j, i < j → ∀ U B : Finset V,
      (∀ a ∈ U, b a = i) → (∀ a ∈ B, b a = j) → m i j ≤ U.card → m i j ≤ B.card →
      (∏ e ∈ cross U B, p e false) ≤ ε) :
    prob p (fun x => ¬ Mixing (graph x) b m) ≤
      ((r : ℝ≥0)^2 * 4^(Fintype.card V)) * ε := by
  classical
  let J := (Fin r × Fin r) × Finset V × Finset V
  let elig (z : J) := z.1.1 < z.1.2 ∧ (∀ a ∈ z.2.1, b a = z.1.1) ∧
    (∀ a ∈ z.2.2, b a = z.1.2) ∧ m z.1.1 z.1.2 ≤ z.2.1.card ∧ m z.1.1 z.1.2 ≤ z.2.2.card
  let event (z : J) (x : Sym2 V → Bool) := elig z ∧
    ∀ a ∈ z.2.1, ∀ c ∈ z.2.2, ¬(graph x).Adj a c
  have cover (x : Sym2 V → Bool) (h : ¬ Mixing (graph x) b m) : ∃ z ∈ (univ : Finset J), event z x := by
    unfold Mixing at h
    push Not at h
    obtain ⟨A,B,i,j,hij,hi,hj,hn⟩ := h
    let U := A.toFinset.filter (fun v => b v = i)
    let W := B.toFinset.filter (fun v => b v = j)
    have hk (X : Set V) (k : Fin r) : mass b X k = (X.toFinset.filter (fun v => b v = k)).card := by
      convert mass_filter b X.toFinset k using 1
      simp
    exact ⟨((i,j),U,W),mem_univ _,⟨hij,fun _ h => (mem_filter.mp h).2,
      fun _ h => (mem_filter.mp h).2, (hk A i) ▸ hi, (hk B j) ▸ hj⟩,
      fun a ha c hc => hn a (Set.mem_toFinset.mp (mem_filter.mp ha).1) c
        (Set.mem_toFinset.mp (mem_filter.mp hc).1)⟩
  have small (z : J) : prob p (event z) ≤ ε := by
    by_cases h : elig z
    · obtain ⟨hij,hU,hW,hmU,hmW⟩ := h
      have hd : Disjoint z.2.1 z.2.2 := Finset.disjoint_left.mpr
        (fun a ha hb => hij.ne ((hU a ha).symm.trans (hW a hb)))
      have hle := prob_mono p (fun x (hx : event z x) => hx.2)
      exact hle.trans ((missing_rectangle p norm _ _ hd).le.trans (miss _ _ hij _ _ hU hW hmU hmW))
    · rw [prob_eq_zero p (fun _ h' => h h'.1)]
      exact zero_le
  apply (prob_mono p cover).trans
  apply (union_bound p (univ : Finset J) event).trans
  calc
    _ ≤ ∑ _ : J, ε := sum_le_sum (fun z _ => small z)
    _ = _ := by
      simp only [sum_const,card_univ,J,Fintype.card_prod,Fintype.card_fin,Fintype.card_finset,nsmul_eq_mul,
        Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [← mul_pow]; norm_num [pow_two]

/-- Simple finite replacement for the asymptotic mixing estimate. -/
theorem no_edge_exp_bound (P : ℝ) (hP : 0 ≤ P) (h₁ : P ≤ 1) (L N : ℕ)
    (h : 4*(N : ℝ) ≤ P*L) : (1-P)^L ≤ (1/16 : ℝ)^N := by
  calc
    _ ≤ (Real.exp (-P))^L := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg P) L
    _ = Real.exp (-(P*L)) := by rw [←Real.exp_nat_mul];congr 1;ring
    _ ≤ Real.exp (-(4*(N : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ = ((Real.exp 1)^4)⁻¹ ^ N := by
      rw [← Real.exp_nat_mul, ←Real.exp_neg, ←Real.exp_nat_mul]
      congr 1; push_cast; ring
    _ ≤ _ := by
      have h₂ : (2 : ℝ) ≤ Real.exp 1 := by simpa only [show (1:ℝ)+1=2 by norm_num] using Real.add_one_le_exp 1
      have h₄ : 16 ≤ (Real.exp 1)^4 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h₂ 4
        norm_num at hh ⊢;exact hh
      apply pow_le_pow_left₀ (by positivity)
      rw [←one_div]
      exact one_div_le_one_div_of_le (by norm_num) h₄

lemma count_rectangles_budget (r N : ℕ) (hr : r*r ≤ N) (hN : 0 < N) :
    ((r : ℝ)^2 * 4^N)*(1/16 : ℝ)^N ≤ 1/4 := by
  have power (k : ℕ) : 4*(k+1) ≤ 4^(k+1) := by
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ]; omega
  have hb : 4*(r*r) ≤ 4^N := by
    have hh := power (N-1)
    rw [Nat.sub_add_cancel hN] at hh
    omega
  have hreal : 4*(r : ℝ)^2 ≤ 4^N := by exact_mod_cast (by simpa [pow_two] using hb : 4*r^2 ≤ 4^N)
  calc
    _ = (r : ℝ)^2/4^N := by rw [mul_assoc,←mul_pow]; norm_num; simp [div_eq_mul_inv]
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith)

end Erdos1111Mixing
end
end

section
namespace Erdos1111Parameters
open Erdos1111Blocks
variable {r : ℕ}
def rank (i j : Fin r) := j.val * r + (r - 1 - i.val)
def base (r : ℕ) := 48*r^3 + 4*r + 2
def scale (r h : ℕ) := (base r)^(25^h)
def z (i j : Fin r) := scale r (rank i j)
def D (i j : Fin r) := (z i j)^3
def Dmax (r : ℕ) := (scale r (r*r))^3
def width (r : ℕ) := 4*r^3*(Dmax r)^3+2

theorem rank_lt {i j k l : Fin r} (h : Later i j k l) : rank i j < rank k l := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hl := l.isLt
  rcases h with hjl | ⟨rfl,hki⟩
  · have hh := Nat.mul_le_mul_right r (show j.val+1 ≤ l.val from hjl)
    rw [Nat.add_mul,one_mul] at hh
    unfold rank
    omega
  · change k.val < i.val at hki
    unfold rank
    omega

theorem rank_bdd (i j : Fin r) : rank i j ≤ r*r := by
  have h := Nat.mul_le_mul_right r (show j.val+1 ≤ r from j.isLt)
  rw [Nat.add_mul,one_mul] at h
  unfold rank
  omega

theorem base_lb (r h : ℕ) : base r ≤ scale r h := by
  have hpos : 0 < 25^h := Nat.pow_pos (by decide)
  simpa only [scale,pow_one] using Nat.pow_le_pow_right (by unfold base;omega : 0 < base r) hpos

theorem z_gap {i j k l : Fin r} (h : Later i j k l) : D i j ^8 ≤ z k l := by
  have hrank := rank_lt h
  have he := Nat.pow_le_pow_right (by decide : 0 < 25) (show rank i j+1 ≤ rank k l from hrank)
  rw [pow_succ] at he
  have h24 : 25^(rank i j)*3*8 ≤ 25^(rank k l) := by omega
  simp only [D,z,scale,←pow_mul]
  exact Nat.pow_le_pow_right (by unfold base;omega) h24

theorem d_bdd (i j : Fin r) : D i j ≤ Dmax r := by
  unfold D Dmax z scale
  exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by unfold base;omega)
    (Nat.pow_le_pow_right (by decide) (rank_bdd i j))) _

theorem density_lb (i j : Fin r) : 48*r^3 ≤ D i j := by
  have a : 48*r^3 ≤ base r := by unfold base;omega
  have b : base r ≤ z i j := base_lb r _
  have hp : 0 < z i j := Nat.lt_of_lt_of_le (by unfold base;omega : 0 < base r) b
  apply (a.trans b).trans
  simpa only [D,pow_one] using Nat.pow_le_pow_right hp (by decide : 1 ≤ 3)

theorem threshold_order (n : ℕ) {i j k l : Fin r} (h : Later i j k l) :
    n / z k l + 1 ≤ n / (D i j)^8 + 1 := by
  have hp : 0 < z i j := by have h := base_lb r (rank i j); unfold base at h;exact Nat.lt_of_lt_of_le (by omega) h
  exact Nat.add_le_add_right (Nat.div_le_div_left (z_gap h) (Nat.pow_pos (Nat.pow_pos hp))) 1

theorem threshold_cutoff (i j : Fin r) (t : ℕ) (ht : 2 ≤ t) :
    r*t / z i j + 1 ≤ t := by
  have hr : 0 < r := Nat.zero_lt_of_lt i.isLt
  have zz : 2*r ≤ z i j := by have h := base_lb r (rank i j); unfold base at h; change 2*r ≤ scale r _;omega
  have hh : r*t/z i j ≤ r*t/(2*r) := Nat.div_le_div_left zz (by omega)
  have heq : r*t / (2*r) = t/2 := by
    rw [Nat.mul_comm 2 r, ←Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ hr]
  rw [heq] at hh
  omega

end Erdos1111Parameters
end

section
noncomputable section
open Finset SimpleGraph Erdos1111Endgame Erdos1111Sampling Erdos1111RandomGraph Erdos1111Estimates
open Erdos1111Densities Erdos1111Union Erdos1111Mixing Erdos1111Parameters Erdos1111Sparsity Erdos1111Blocks
open scoped NNReal
namespace Erdos1111Realization

lemma fourth_scale {N m : ℕ} (hm : 0 < m) (h : m ≤ N) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧ (N : ℝ)*y^4 = m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hm h
  let a : ℝ := m/N
  have ha : 0 < a := div_pos hm' hN
  have h1 : a ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast h)
  refine ⟨Real.sqrt (Real.sqrt a),by positivity,?_,?_⟩
  · exact (Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr h1))
  · have h₂ := Real.sq_sqrt (Real.sqrt_nonneg a)
    have h₄ : (Real.sqrt (Real.sqrt a))^4 = a := by
      rw [show (4 : ℕ) = 2*2 by decide,pow_mul,h₂,Real.sq_sqrt ha.le]
    rw [h₄]; dsimp [a]; field_simp

lemma obtain_good {E : Type*} [Fintype E] [DecidableEq E] (p : E → Bool → ℝ≥0)
    (norm : ∀ e, p e false + p e true = 1) (A B C : (E → Bool) → Prop)
    (hA : (prob p A : ℝ) ≤ 1/4) (hB : (prob p B : ℝ) ≤ 3/13)
    (hC : (prob p C : ℝ) ≤ 1/4) : ∃ x, ¬ A x ∧ ¬ B x ∧ ¬ C x := by
  classical
  by_contra! h
  let event : Fin 3 → (E → Bool) → Prop := ![A,B,C]
  have hall (x : E → Bool) : ∃ j ∈ (univ : Finset (Fin 3)), event j x := by
    by_cases ha : A x
    · exact ⟨0,mem_univ _,ha⟩
    by_cases hb : B x
    · exact ⟨1,mem_univ _,hb⟩
    exact ⟨2,mem_univ _,h x ha hb⟩
  have hu := union_bound p (univ : Finset (Fin 3)) event
  have htotal : prob p (fun x => ∃ j ∈ (univ : Finset (Fin 3)), event j x) = 1 := by
    unfold prob
    calc
      _ = ∑ x, weight p x := sum_congr rfl (fun x _ => if_pos (hall x))
      _ = 1 := probability_one p norm
  rw [htotal,Fin.sum_univ_three] at hu
  have hreal : (1 : ℝ) ≤ prob p A + (prob p B : ℝ) + prob p C := by exact_mod_cast hu
  linarith

theorem realization : BlockRealization := by
  classical
  intro d₀
  let r := 2*d₀+2
  let t := width r
  let n := r*t
  let N := r*n
  let V := Fin r × Fin n
  let b : V → Fin r := Prod.fst
  have hr : 1 ≤ r := by dsimp [r];omega
  have ht : 2 ≤ t := by dsimp [t,width];omega
  have hn : 0 < n := Nat.mul_pos hr (by omega)
  have hN : 0 < N := Nat.mul_pos hr hn
  have hcard : Fintype.card V = N := by simp [V,N]
  have dpos : 0 < Dmax r := by
    dsimp [Dmax,scale,base]; positivity
  have hdBound : Dmax r ≤ n := by
    change Dmax r ≤ r*(4*r^3*Dmax r^3+2)
    have hpow : Dmax r ≤ Dmax r^3 := by simpa only [pow_one] using Nat.pow_le_pow_right dpos (by decide : 1≤3)
    have hr3 : 1 ≤ r^3 := Nat.pow_pos hr
    have hfac : 1 ≤ 4*r^3 := by omega
    have hs := Nat.mul_le_mul_right (Dmax r^3) hfac
    simp only [one_mul] at hs
    apply hpow.trans
    exact hs.trans ((Nat.le_add_right _ 2).trans (by simpa only [one_mul] using Nat.mul_le_mul_right (4*r^3*Dmax r^3+2) hr))
  let raw (e : Sym2 V) : ℝ≥0 := if (key b e).1 < (key b e).2 then
    (D (key b e).1 (key b e).2 : ℝ≥0)/n else 0
  have raw_le (e : Sym2 V) : raw e ≤ (Dmax r : ℝ≥0)/n := by
    dsimp only [raw];split_ifs
    · exact div_le_div_of_nonneg_right (by exact_mod_cast d_bdd _ _) zero_le
    · exact zero_le
  have raw_one (e : Sym2 V) : raw e ≤ 1 := (raw_le e).trans <|
    (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hdBound)
  let p (e : Sym2 V) (a : Bool) : ℝ≥0 := if a then raw e else 1-raw e
  have norm (e : Sym2 V) : p e false+p e true = 1 := by simp [p,tsub_add_cancel_of_le (raw_one e)]
  let w (i j : Fin r) := n/(D i j)^8
  let m (i j : Fin r) := n/z i j+1
  have hweak : (prob p (fun x => ¬ Sparse (graph x) b w) : ℝ) ≤ 3/13 := by
    apply probability_not_sparse p norm b w
    intro Y hY
    have hmax : Y.card ≤ N := hcard ▸ card_le_univ Y
    obtain ⟨y,hy,hy',hs⟩ := fourth_scale (card_pos.mpr hY) hmax
    refine ⟨y,hy,hy',hcard ▸ hs,?_⟩
    apply total_mean b D n hr hn (fun _ _ _ => density_lb _ _) raw
      (fun e => by dsimp [raw];split_ifs <;> simp) _ y hy.le
    exact_mod_cast (by simpa only [N,Nat.cast_mul] using hs : (r : ℝ)*n*y^4 = Y.card)
  have htri : (prob p (fun x => n < (triangles (graph x)).card) : ℝ) ≤ 1/4 := by
    have H := triangle_tail p norm ((Dmax r : ℝ≥0)/n) raw_le n
    have cc : (Fintype.card V).choose 3 ≤ N^3 := hcard ▸ Nat.choose_le_pow _ _
    have H' : ((n+1 : ℕ) : ℝ)*(prob p (fun x => n < (triangles (graph x)).card) : ℝ) ≤
        (N : ℝ)^3*((Dmax r : ℝ)/n)^3 := by
      have H₁ : ((n+1 : ℕ) : ℝ)*(prob p (fun x => n < (triangles (graph x)).card) : ℝ) ≤
        ((Fintype.card V).choose 3 : ℝ)*((Dmax r : ℝ)/n)^3 := by exact_mod_cast H
      exact H₁.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast cc) (by positivity))
    have he : (N : ℝ)^3*((Dmax r : ℝ)/n)^3 = (r : ℝ)^3*(Dmax r : ℝ)^3 := by
      dsimp [N];push_cast;field_simp
    rw [he] at H'
    have sw : 4*r^3*(Dmax r)^3 ≤ n := by
      have h1 : 4*r^3*(Dmax r)^3 ≤ t := by dsimp [t,width];omega
      exact h1.trans (by change t ≤ r*t; simpa using Nat.mul_le_mul_right t hr)
    have sw' : 4*(r : ℝ)^3*(Dmax r : ℝ)^3 ≤ n := by exact_mod_cast sw
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < ((n+1 : ℕ) : ℝ))).mp
    push_cast at H' ⊢
    linarith
  have hmix : (prob p (fun x => ¬ Mixing (graph x) b m) : ℝ) ≤ 1/4 := by
    let ε : ℝ≥0 := (1/16)^N
    have he (i j : Fin r) (hij : i < j) (U W : Finset V)
        (hU : ∀ a ∈ U, b a = i) (hW : ∀ a ∈ W, b a = j)
        (u : m i j ≤ U.card) (v : m i j ≤ W.card) :
        (∏ e ∈ cross U W, p e false) ≤ ε := by
      have hd : Disjoint U W := Finset.disjoint_left.mpr
        (fun a ha hb => hij.ne ((hU a ha).symm.trans (hW a hb)))
      have pv (e : Sym2 V) (he : e ∈ cross U W) : raw e = (D i j : ℝ≥0)/n := by
        obtain ⟨⟨a,c⟩,hac,rfl⟩ := mem_image.mp he
        obtain ⟨ha,hc⟩ := mem_product.mp hac
        have hb : b a < b c := (hU a ha).symm ▸ (hW c hc).symm ▸ hij
        simp [raw,key_mk b hb,hU a ha,hW c hc,hij]
      have hconst : (∏ e ∈ cross U W, p e false) = (1-(D i j : ℝ≥0)/n)^((cross U W).card) :=
        prod_eq_pow_card (fun e he => by simp [p,pv e he])
      rw [hconst,cross_card U W hd]
      have hd1 : (D i j : ℝ≥0)/n ≤ 1 := (div_le_one (by exact_mod_cast hn)).mpr
        (by exact_mod_cast (d_bdd i j).trans hdBound)
      have zs : 4*r ≤ z i j := by have H := base_lb r (rank i j);unfold base at H; change 4*r ≤ scale r _;omega
      have hzp : 0 < z i j := by omega
      have hU' := (Nat.div_lt_iff_lt_mul hzp).mp (show n/z i j < U.card from u)
      have hW' := (Nat.div_lt_iff_lt_mul hzp).mp (show n/z i j < W.card from v)
      have bb : 4*r*n*n ≤ D i j * (U.card*W.card) := by
        calc
          _ ≤ z i j*(n*n) := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (n*n) zs
          _ ≤ z i j*((U.card*z i j)*(W.card*z i j)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hU'.le hW'.le)
          _ = _ := by unfold D;ring
      have H := no_edge_exp_bound ((D i j : ℝ)/n) (by positivity) (by exact_mod_cast hd1) (U.card*W.card) N
        (by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))]
          dsimp [N]
          push_cast
          exact_mod_cast (by simpa only [Nat.mul_assoc] using bb : 4*(r*n)*n ≤ D i j * (U.card*W.card)))
      apply NNReal.coe_le_coe.mp
      simpa only [NNReal.coe_pow,NNReal.coe_sub hd1,NNReal.coe_one,NNReal.coe_div,
        NNReal.coe_natCast,ε,NNReal.coe_ofNat] using H
    have H := mixing_failure b m p norm ε he
    have H₁ : (prob p (fun x => ¬ Mixing (graph x) b m) : ℝ) ≤
        ((r : ℝ)^2*4^N)*(1/16 : ℝ)^N := by
      rw [hcard] at H
      exact_mod_cast H
    exact H₁.trans (count_rectangles_budget _ _ (Nat.mul_le_mul_left _ (by
      change r ≤ r*t
      simpa using Nat.mul_le_mul_left r (show 1 ≤ t by omega))) hN)
  obtain ⟨x,h₁,h₂,h₃⟩ := obtain_good p norm _ _ _ hmix hweak htri
  exact ⟨t,by omega,graph x,w,m, fun _ _ _ _ _ _ h => threshold_order _ h,
    fun i j _ => threshold_cutoff i j t ht,Classical.not_not.mp h₁,
    Classical.not_not.mp h₂,Nat.le_of_not_gt h₃⟩

end Erdos1111Realization
end
end

theorem OMA.disproof : ¬ (type_of% @Erdos1111.erdos_1111) :=
  Erdos1111Endgame.disproof_of_realization Erdos1111Realization.realization
