import OMAReductions.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2
import Mathlib

/-!
# Reduction of step `R1.H1.R2.H1` of Written on the Wall II - Conjecture 40

The step `R1.H1.R2.H1` (bipartite 2-connected graphs above the scattering bound in which no
maximum induced forest is in the block class, while some maximum induced forest has at most three
outside neighbours at every vertex) is PROVED here for every graph having a maximum induced forest
`U` and two vertices `x1`, `x2` (equal, or of different colours) such that every vertex of `U`
other than `x1`, `x2` satisfies the block condition of `R1.H1.R2`, and `x1`, `x2` have at most
three neighbours outside `U` when they lie in `U`. So in each colour class of `U` one vertex with
three unseparated outside neighbours is allowed.

Set-system core (pure form, notation of `R1.H1.R2`; `HP`: `c(S) ≤ |S|`, `LC`: Lovász condition):

- `theorem_GL3`: if `HP` holds, every element lies in at most two sets except one element `x`
  lying in at most three sets, then P1 holds (for every prescribed `v` there are 2-subsets of the
  sets forming a linear forest with `v` of degree at most one). Proof: call `y` bad at a set `a`
  if some L-tight collection of sets contains `a` and no other set containing `y`. Under `HP` an
  element is bad at no two of its sets (`bad_unique`, from `tight_inter`). If `v = x` or `v` lies
  in at most one set, use `theorem_RF1` for `x`. Otherwise `v` lies in exactly two sets; take a set
  `a ∋ v` at which `v` is not bad, the other set `b ∋ v`, and two sets `ti`, `ti'` containing `x`
  at which `x` is not bad. Delete `x` from `ti` (or `ti'`) and `v` from `a`. If both double
  deletions violate LC, the violating collections `X`, `Y` lose both `x` and `v`, have
  `|A(X)| = |X| + 2` (`fail_shape`), contain `a`, avoid `b`, and `x ∈ A(X) ∩ A(Y)` but
  `x ∉ A(X ∩ Y)`. Submodularity then makes `X ∩ Y` or `X ∪ Y` L-tight, so `v` is bad at `a`,
  a contradiction (`core_pair`). Lovász pairs of the doubly deleted family give the linear forest
  (`p1_of_sub`).
- `theorem_BLX`: the induction of Theorem BL (cut element reduction `theorem_CE`, `lemma_SEP`)
  with the block condition required only at elements other than `x`, and `x` in at most three sets;
  the base case is `theorem_GL3`.
- The graph part is that of `R1.H1.R2` (copied, private lemmas), applied once per colour class
  with the exceptional vertex of that colour (`p1_side`, `k2_bipartite_core`, `k2_forest_classX`).

The remaining graphs (for every maximum induced forest `U` and every admissible pair `x1`, `x2`
some other vertex of `U` is bad) are split by the number of bad vertices per colour in the
maximum induced forests with at most three outside neighbours at every vertex: some such forest
has at most two bad vertices of each colour (`H1`), or every such forest has three bad vertices of
one colour (`H2`). A vertex `x ∈ U` is bad if it has three distinct outside neighbours that no
split at `x` separates (as in `R1.H1.R2`).
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2_H1_R1

open SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2 (lc_of_hp tight_inter
  theorem_GL theorem_RF1 lovasz_pairs biUnion_inter_sub biUnion_union_eq theorem_CE hp_sub bridge)

/-- The graphs of step `R1.H1.R2.H1` not covered by Theorem BLX (for every maximum induced forest
`U` and any two vertices `x1`, `x2`, equal or of different colours, with at most three neighbours
outside `U` when in `U`, some other vertex of `U` is bad), having a maximum induced forest with at
most three outside neighbours at every vertex and at most two bad vertices of each colour. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    4 ≤ Fintype.card V → G.Connected → (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic → U.card = G.largestInducedForestSize →
      ∀ x1 x2 : V, (∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → x1 = x2 ∨ c x1 ≠ c x2) →
      (x1 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x1 t} ≤ 3) →
      (x2 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x2 t} ≤ 3) →
      ∃ x ∈ U, x ≠ x1 ∧ x ≠ x2 ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        G.Adj x a ∧ G.Adj x b ∧ G.Adj x d ∧ ∀ p : V → Prop,
          (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = x) →
          (p a ↔ p b) ∧ (p a ↔ p d)) →
    (∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧ U.card = G.largestInducedForestSize ∧
      (∀ x ∈ U, Set.ncard {t | t ∉ U ∧ G.Adj x t} ≤ 3) ∧
      ∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → ∀ i : Fin 2,
        Set.ncard {y | y ∈ U ∧ c y = i ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          G.Adj y a ∧ G.Adj y b ∧ G.Adj y d ∧ ∀ p : V → Prop,
            (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = y) →
            (p a ↔ p b) ∧ (p a ↔ p d)} ≤ 2) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

/-- The graphs of step `R1.H1.R2.H1` not covered by Theorem BLX, having a maximum induced forest
with at most three outside neighbours at every vertex, in which every such forest has three bad
vertices of the same colour. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    4 ≤ Fintype.card V → G.Connected → (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic → U.card = G.largestInducedForestSize →
      ∀ x1 x2 : V, (∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → x1 = x2 ∨ c x1 ≠ c x2) →
      (x1 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x1 t} ≤ 3) →
      (x2 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x2 t} ≤ 3) →
      ∃ x ∈ U, x ≠ x1 ∧ x ≠ x2 ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        G.Adj x a ∧ G.Adj x b ∧ G.Adj x d ∧ ∀ p : V → Prop,
          (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = x) →
          (p a ↔ p b) ∧ (p a ↔ p d)) →
    (∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧ U.card = G.largestInducedForestSize ∧
      (∀ x ∈ U, Set.ncard {t | t ∉ U ∧ G.Adj x t} ≤ 3)) →
    (∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic → U.card = G.largestInducedForestSize →
      (∀ x ∈ U, Set.ncard {t | t ∉ U ∧ G.Adj x t} ≤ 3) →
      ∃ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) ∧ ∃ i : Fin 2,
        3 ≤ Set.ncard {y | y ∈ U ∧ c y = i ∧ ∃ a b d : V, a ∉ U ∧ b ∉ U ∧ d ∉ U ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          G.Adj y a ∧ G.Adj y b ∧ G.Adj y d ∧ ∀ p : V → Prop,
            (∀ s r, s ∉ U → r ∉ U → p s → ¬ p r → ∀ z ∈ U, G.Adj s z → G.Adj r z → z = y) →
            (p a ↔ p b) ∧ (p a ↔ p d)}) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

section fam

variable {T B : Type} [Fintype T] [DecidableEq T] [DecidableEq B]

/-- Under HP an element is bad at no two distinct sets containing it. -/
theorem bad_unique (A : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (y : B) (a a' : T) (ha : y ∈ A a) (ha' : y ∈ A a') (hne : a ≠ a')
    (h1 : (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ a ∈ ybX ∧ ∀ ybt ∈ ybX, y ∈ A ybt → ybt = a)) (h2 : (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ a' ∈ ybX ∧ ∀ ybt ∈ ybX, y ∈ A ybt → ybt = a')) : False := by
  obtain ⟨X, hX, haX, hXy⟩ := h1
  obtain ⟨Y, hY, haY, hYy⟩ := h2
  have hvX : y ∈ X.biUnion A := Finset.mem_biUnion.mpr ⟨a, haX, ha⟩
  have hvY : y ∈ Y.biUnion A := Finset.mem_biUnion.mpr ⟨a', haY, ha'⟩
  obtain ⟨_, hv⟩ := tight_inter A h X Y hX hY y hvX hvY
  obtain ⟨t, ht, hyt⟩ := Finset.mem_biUnion.mp hv
  rw [Finset.mem_inter] at ht
  exact hne ((hXy t ht.1 hyt).symm.trans (hYy t ht.2 hyt))

/-- Membership in the doubly deleted family: `x` deleted from `A ti`, `v` deleted from every set
except `A keep`. -/
theorem mem_dfam (A : T → Finset B) (x v : B) (ti keep t : T) (z : B) :
    z ∈ (fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = keep))) t ↔ z ∈ A t ∧ (z = x → t ≠ ti) ∧ (z = v → t = keep) := by
  exact Finset.mem_filter

/-- Shape of a failure of LC for the doubly deleted family, when `ti` is good for `x` and the
deleted set `a` is good for `v`. -/
theorem fail_shape (A : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (x v : B) (hxv : x ≠ v) (ti a b : T) (hvb : v ∈ A b)
    (hvs : ∀ t, v ∈ A t → t = a ∨ t = b) (hgx : ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ ti ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = ti)) (hgv : ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ a ∈ ybX ∧ ∀ ybt ∈ ybX, v ∈ A ybt → ybt = a))
    (X : Finset T) (hX : X.Nonempty)
    (hfail : (X.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b))))).card < X.card + 1) :
    (X.biUnion A).card = X.card + 2 ∧ ti ∈ X ∧ a ∈ X ∧ b ∉ X ∧
      (∀ t ∈ X, x ∈ A t → t = ti) := by
  classical
  have hLC := lc_of_hp A h X hX
  have hsub : X.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b)))) ⊆ X.biUnion A := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨t, ht, ((mem_dfam A x v ti b t z).mp hzt).1⟩
  set D := X.biUnion A \ X.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b)))) with hDdef
  have hcard : (X.biUnion A).card = (X.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b))))).card + D.card := by
    rw [hDdef, Finset.card_sdiff_of_subset hsub]
    have := Finset.card_le_card hsub
    omega
  have hD : ∀ z ∈ D, z = x ∨ z = v := by
    intro z hz
    rw [hDdef, Finset.mem_sdiff] at hz
    by_contra hc
    push Not at hc
    obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz.1
    exact hz.2 (Finset.mem_biUnion.mpr ⟨t, ht, (mem_dfam A x v ti b t z).mpr
      ⟨hzt, fun e => absurd e hc.1, fun e => absurd e hc.2⟩⟩)
  have hDx : x ∈ D → ∀ t ∈ X, x ∈ A t → t = ti := by
    intro hx t ht hxt
    by_contra hne
    rw [hDdef, Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_biUnion.mpr ⟨t, ht, (mem_dfam A x v ti b t x).mpr
      ⟨hxt, fun _ => hne, fun e => absurd e hxv⟩⟩)
  have hDx2 : x ∈ D → x ∈ X.biUnion A := fun hx => (Finset.mem_sdiff.mp hx).1
  have hDv : v ∈ D → b ∉ X := by
    intro hv hb
    rw [hDdef, Finset.mem_sdiff] at hv
    exact hv.2 (Finset.mem_biUnion.mpr ⟨b, hb, (mem_dfam A x v ti b b v).mpr
      ⟨hvb, fun e => absurd e.symm hxv, fun _ => rfl⟩⟩)
  have hDv2 : v ∈ D → v ∈ X.biUnion A := fun hv => (Finset.mem_sdiff.mp hv).1
  -- v lost: a ∈ X and every set of X containing v is a
  have hvlost : v ∈ D → a ∈ X ∧ ∀ t ∈ X, v ∈ A t → t = a := by
    intro hv
    have hbX := hDv hv
    have hall : ∀ t ∈ X, v ∈ A t → t = a := by
      intro t ht hvt
      rcases hvs t hvt with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ ht) hbX
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp (hDv2 hv)
    exact ⟨hall t ht hvt ▸ ht, hall⟩
  have hxlost : x ∈ D → ti ∈ X := by
    intro hx
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp (hDx2 hx)
    exact hDx hx t ht hxt ▸ ht
  by_cases hxD : x ∈ D
  · by_cases hvD : v ∈ D
    · have hD2 : D ⊆ {x, v} := by
        intro z hz
        rcases hD z hz with rfl | rfl <;> simp
      have hc2 : D.card ≤ 2 := (Finset.card_le_card hD2).trans Finset.card_le_two
      have hne1 : (X.biUnion A).card ≠ X.card + 1 := by
        intro he
        exact hgx ⟨X, ⟨hX, he⟩, hxlost hxD, hDx hxD⟩
      obtain ⟨haX, _⟩ := hvlost hvD
      exact ⟨by omega, hxlost hxD, haX, hDv hvD, hDx hxD⟩
    · have hD1 : D ⊆ {x} := by
        intro z hz
        rcases hD z hz with rfl | rfl
        · simp
        · exact absurd hz hvD
      have hc1 := Finset.card_le_card hD1
      rw [Finset.card_singleton] at hc1
      exact absurd ⟨X, ⟨hX, by omega⟩, hxlost hxD, hDx hxD⟩ hgx
  · by_cases hvD : v ∈ D
    · have hD1 : D ⊆ {v} := by
        intro z hz
        rcases hD z hz with rfl | rfl
        · exact absurd hz hxD
        · simp
      have hc1 := Finset.card_le_card hD1
      rw [Finset.card_singleton] at hc1
      obtain ⟨haX, hall⟩ := hvlost hvD
      exact absurd ⟨X, ⟨hX, by omega⟩, haX, hall⟩ hgv
    · have hD0 : D = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rcases hD z hz with rfl | rfl
        · exact hxD hz
        · exact hvD hz
      rw [hD0, Finset.card_empty] at hcard
      omega

/-- Two `x`-good sets and a `v`-good set: one of the two double deletions keeps LC. -/
theorem core_pair (A : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (x v : B) (hxv : x ≠ v) (ti ti' a b : T) (hii : ti ≠ ti') (hxi : x ∈ A ti) (hxi' : x ∈ A ti')
    (hvb : v ∈ A b) (hvs : ∀ t, v ∈ A t → t = a ∨ t = b)
    (hg1 : ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ ti ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = ti)) (hg2 : ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ ti' ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = ti')) (hgv : ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ a ∈ ybX ∧ ∀ ybt ∈ ybX, v ∈ A ybt → ybt = a)) :
    (∀ lcX : Finset T, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b))))).card) ∨
    (∀ lcX : Finset T, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti') ∧ (dfz = v → dft = b))))).card) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  push Not at h1 h2
  obtain ⟨X, hX, hXf⟩ := h1
  obtain ⟨Y, hY, hYf⟩ := h2
  obtain ⟨cX, tiX, aX, bX, xX⟩ := fail_shape A h x v hxv ti a b hvb hvs hg1 hgv X hX hXf
  obtain ⟨cY, tiY, aY, bY, xY⟩ := fail_shape A h x v hxv ti' a b hvb hvs hg2 hgv Y hY hYf
  have hLC := lc_of_hp A h
  have hIne : (X ∩ Y).Nonempty := ⟨a, Finset.mem_inter.mpr ⟨aX, aY⟩⟩
  have hUne : (X ∪ Y).Nonempty := hX.mono Finset.subset_union_left
  have hxXY : x ∈ X.biUnion A ∩ Y.biUnion A :=
    Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨ti, tiX, hxi⟩,
      Finset.mem_biUnion.mpr ⟨ti', tiY, hxi'⟩⟩
  have hIsub : (X ∩ Y).biUnion A ⊆ (X.biUnion A ∩ Y.biUnion A).erase x := by
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, biUnion_inter_sub A X Y hz⟩
    rintro rfl
    obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz
    rw [Finset.mem_inter] at ht
    exact hii ((xX t ht.1 hzt).symm.trans (xY t ht.2 hzt))
  have cI := Finset.card_le_card hIsub
  rw [Finset.card_erase_of_mem hxXY] at cI
  have hpos : 0 < (X.biUnion A ∩ Y.biUnion A).card := Finset.card_pos.mpr ⟨x, hxXY⟩
  have sA := Finset.card_union_add_card_inter (X.biUnion A) (Y.biUnion A)
  have sT := Finset.card_union_add_card_inter X Y
  have lU := hLC (X ∪ Y) hUne
  have lI := hLC (X ∩ Y) hIne
  rw [biUnion_union_eq] at lU
  -- every set of X ∪ Y containing v is a
  have hvU : ∀ t ∈ X ∪ Y, v ∈ A t → t = a := by
    intro t ht hvt
    rcases hvs t hvt with h1 | h1
    · exact h1
    · subst h1
      rcases Finset.mem_union.mp ht with h2 | h2
      · exact absurd h2 bX
      · exact absurd h2 bY
  by_cases hIt : ((X ∩ Y).biUnion A).card = (X ∩ Y).card + 1
  · exact hgv ⟨X ∩ Y, ⟨hIne, hIt⟩, Finset.mem_inter.mpr ⟨aX, aY⟩,
      fun t ht hvt => hvU t (Finset.mem_union_left _ (Finset.mem_inter.mp ht).1) hvt⟩
  · have hUt : ((X ∪ Y).biUnion A).card = (X ∪ Y).card + 1 := by
      rw [biUnion_union_eq]
      omega
    exact hgv ⟨X ∪ Y, ⟨hUne, hUt⟩, Finset.mem_union_left _ aX, hvU⟩

/-- A subfamily satisfying LC with element degrees at most two (and at most one at `v`) gives the
P1 conclusion for the family. -/
theorem p1_of_sub (A A2 : T → Finset B) (hsub : ∀ t, A2 t ⊆ A t)
    (hL : ∀ lcX : Finset T, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion A2).card)
    (hd : ∀ z, (Finset.univ.filter (fun t => z ∈ A2 t)).card ≤ 2) (v : B)
    (hv : (Finset.univ.filter (fun t => v ∈ A2 t)).card ≤ 1) :
    ∃ p1e : T → B × B, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => v ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1 := by
  obtain ⟨e, he, hLe⟩ := lovasz_pairs _ A2 le_rfl hL
  have hpe : ∀ z, Finset.univ.filter (fun t => z ∈ ({(e t).1, (e t).2} : Finset B)) ⊆
      Finset.univ.filter (fun t => z ∈ A2 t) := by
    intro z t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at ht ⊢
    rcases ht with rfl | rfl
    · exact (he t).1
    · exact (he t).2.1
  refine ⟨e, fun t => ⟨hsub t (he t).1, hsub t (he t).2.1, (he t).2.2⟩, hLe,
    fun z => (Finset.card_le_card (hpe z)).trans (hd z), (Finset.card_le_card (hpe v)).trans hv⟩

/-- Theorem GL3: HP, every element in at most two sets except one element `x` in at most three
sets ⟹ P1. -/
theorem theorem_GL3 (A : T → Finset B)
    (h : ∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)
    (x : B) (hdeg : ∀ b, b ≠ x → (Finset.univ.filter (fun t => b ∈ A t)).card ≤ 2)
    (hx : (Finset.univ.filter (fun t => x ∈ A t)).card ≤ 3) (v : B) :
    ∃ p1e : T → B × B, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => v ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1 := by
  classical
  by_cases hx2 : (Finset.univ.filter (fun t => x ∈ A t)).card ≤ 2
  · exact theorem_GL A h (fun b => by
      by_cases hb : b = x
      · subst hb; exact hx2
      · exact hdeg b hb) v
  have hx3 : (Finset.univ.filter (fun t => x ∈ A t)).card = 3 := by omega
  obtain ⟨t1, t2, t3, h12, h13, h23, hXs⟩ := Finset.card_eq_three.mp hx3
  have hxs : ∀ t, x ∈ A t ↔ t = t1 ∨ t = t2 ∨ t = t3 := by
    intro t
    have := congrArg (fun s => t ∈ s) hXs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, eq_iff_iff] at this
    exact this
  have hx1 : x ∈ A t1 := (hxs t1).mpr (Or.inl rfl)
  have hx2' : x ∈ A t2 := (hxs t2).mpr (Or.inr (Or.inl rfl))
  have hx3' : x ∈ A t3 := (hxs t3).mpr (Or.inr (Or.inr rfl))
  by_cases hv1 : v = x ∨ (Finset.univ.filter (fun t => v ∈ A t)).card ≤ 1
  · obtain ⟨t0, _, hL⟩ := theorem_RF1 A h x ⟨t1, hx1⟩
    refine p1_of_sub A _ (fun t => ?_) hL (fun z => ?_) v ?_
    · beta_reduce; split_ifs
      · exact subset_rfl
      · exact Finset.erase_subset _ _
    · have hsub1 : Finset.univ.filter (fun t => z ∈ (fun kpt => if kpt = t0 then A kpt else (A kpt).erase x) t) ⊆
          Finset.univ.filter (fun t => z ∈ A t) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        split_ifs at ht
        · exact ht
        · exact Finset.mem_of_mem_erase ht
      by_cases hz : z = x
      · subst hz
        have hsub2 : Finset.univ.filter (fun t => z ∈ (fun kpt => if kpt = t0 then A kpt else (A kpt).erase z) t) ⊆ {t0} := by
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          rw [Finset.mem_singleton]
          by_contra hne
          rw [if_neg hne] at ht
          exact Finset.notMem_erase _ _ ht
        have := Finset.card_le_card hsub2
        rw [Finset.card_singleton] at this
        exact le_trans this (by norm_num)
      · exact (Finset.card_le_card hsub1).trans (hdeg z hz)
    · rcases hv1 with hv1 | hv1
      · subst hv1
        have hsub2 : Finset.univ.filter (fun t => v ∈ (fun kpt => if kpt = t0 then A kpt else (A kpt).erase v) t) ⊆ {t0} := by
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          rw [Finset.mem_singleton]
          by_contra hne
          rw [if_neg hne] at ht
          exact Finset.notMem_erase _ _ ht
        have := Finset.card_le_card hsub2
        rw [Finset.card_singleton] at this
        exact this
      · refine le_trans (Finset.card_le_card ?_) hv1
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        split_ifs at ht
        · exact ht
        · exact Finset.mem_of_mem_erase ht
  rw [not_or] at hv1
  obtain ⟨hvx, hv2⟩ := hv1
  have hv2' : (Finset.univ.filter (fun t => v ∈ A t)).card = 2 := by
    have := hdeg v hvx
    omega
  obtain ⟨s1, s2, hs12, hSs⟩ := Finset.card_eq_two.mp hv2'
  have hvs : ∀ t, v ∈ A t ↔ t = s1 ∨ t = s2 := by
    intro t
    have := congrArg (fun s => t ∈ s) hSs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, eq_iff_iff] at this
    exact this
  have hvs1 : v ∈ A s1 := (hvs s1).mpr (Or.inl rfl)
  have hvs2 : v ∈ A s2 := (hvs s2).mpr (Or.inr rfl)
  have hxv : x ≠ v := fun e => hvx e.symm
  -- finishing from one good double deletion
  have fin : ∀ ti b, (ti = t1 ∨ ti = t2 ∨ ti = t3) →
      (∀ lcX : Finset T, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b))))).card) →
      ∃ p1e : T → B × B, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => v ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1 := by
    intro ti b hti hL
    have hvb1 : (Finset.univ.filter (fun t => v ∈ (fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b))) t)).card ≤ 1 := by
      have hsub2 : Finset.univ.filter (fun t => v ∈ (fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b))) t) ⊆ {b} := by
        intro t ht
        have ht' := (mem_dfam A x v ti b t v).mp (Finset.mem_filter.mp ht).2
        exact Finset.mem_singleton.mpr (ht'.2.2 rfl)
      have := Finset.card_le_card hsub2
      rwa [Finset.card_singleton] at this
    refine p1_of_sub A ((fun dft => (A dft).filter (fun dfz => (dfz = x → dft ≠ ti) ∧ (dfz = v → dft = b)))) (fun t z hz => ((mem_dfam A x v ti b t z).mp hz).1) hL
      (fun z => ?_) v hvb1
    by_cases hz : z = x
    · subst hz
      have hsub2 : Finset.univ.filter (fun t => z ∈ (fun dft => (A dft).filter (fun dfz => (dfz = z → dft ≠ ti) ∧ (dfz = v → dft = b))) t) ⊆
          (({t1, t2, t3} : Finset T).erase ti) := by
        intro t ht
        have ht := (mem_dfam A z v ti b t z).mp (Finset.mem_filter.mp ht).2
        refine Finset.mem_erase.mpr ⟨ht.2.1 rfl, ?_⟩
        have := (hxs t).mp ht.1
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact this
      have hmem : ti ∈ ({t1, t2, t3} : Finset T) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; exact hti
      have hc3 : ({t1, t2, t3} : Finset T).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair h23]
        simp [h12, h13]
      have := Finset.card_le_card hsub2
      rw [Finset.card_erase_of_mem hmem, hc3] at this
      omega
    · refine le_trans (Finset.card_le_card ?_) (hdeg z hz)
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_filter.mp ht).2).1⟩
  -- choose a v-good set a (and b the other one)
  have hab : ∃ a b, a ≠ b ∧ v ∈ A b ∧ (∀ t, v ∈ A t → t = a ∨ t = b) ∧ ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ a ∈ ybX ∧ ∀ ybt ∈ ybX, v ∈ A ybt → ybt = a) := by
    by_cases hb1 : (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ s1 ∈ ybX ∧ ∀ ybt ∈ ybX, v ∈ A ybt → ybt = s1)
    · refine ⟨s2, s1, hs12.symm, hvs1, fun t ht => ?_, fun hb2 =>
        bad_unique A h v s1 s2 hvs1 hvs2 hs12 hb1 hb2⟩
      rcases (hvs t).mp ht with e | e
      · exact Or.inr e
      · exact Or.inl e
    · exact ⟨s1, s2, hs12, hvs2, fun t ht => (hvs t).mp ht, hb1⟩
  obtain ⟨a, b, _, hvb, hvsab, hga⟩ := hab
  -- choose two x-good sets
  have hgood : ∃ ti ti', ti ≠ ti' ∧ (ti = t1 ∨ ti = t2 ∨ ti = t3) ∧
      (ti' = t1 ∨ ti' = t2 ∨ ti' = t3) ∧ ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ ti ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = ti) ∧ ¬ (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ ti' ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = ti') := by
    by_cases hb1 : (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ t1 ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = t1)
    · exact ⟨t2, t3, h23, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
        fun hb => bad_unique A h x t1 t2 hx1 hx2' h12 hb1 hb,
        fun hb => bad_unique A h x t1 t3 hx1 hx3' h13 hb1 hb⟩
    · by_cases hb2 : (∃ ybX : Finset T, (ybX.Nonempty ∧ (ybX.biUnion A).card = ybX.card + 1) ∧ t2 ∈ ybX ∧ ∀ ybt ∈ ybX, x ∈ A ybt → ybt = t2)
      · exact ⟨t1, t3, h13, Or.inl rfl, Or.inr (Or.inr rfl), hb1,
          fun hb => bad_unique A h x t2 t3 hx2' hx3' h23 hb2 hb⟩
      · exact ⟨t1, t2, h12, Or.inl rfl, Or.inr (Or.inl rfl), hb1, hb2⟩
  obtain ⟨ti, ti', hii, hti, hti', hg1, hg2⟩ := hgood
  have hxi : x ∈ A ti := (hxs ti).mpr hti
  have hxi' : x ∈ A ti' := (hxs ti').mpr hti'
  rcases core_pair A h x v hxv ti ti' a b hii hxi hxi' hvb hvsab hg1 hg2 hga with hL | hL
  · exact fin ti b hti hL
  · exact fin ti' b hti' hL

omit [Fintype T] [DecidableEq T] in
/-- The block condition away from `x` is inherited by subfamilies with smaller sets. -/
theorem blx_mono {T' : Type} (A : T → Finset B) (x : B) (h : (∀ (blb : _), blb ≠ x → ∀ (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A blt1 → blb ∈ A blt2 → blb ∈ A blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3)))) (f : T' → T)
    (hf : Function.Injective f) (A' : T' → Finset B) (hA' : ∀ t, A' t ⊆ A (f t)) :
    (∀ (blb : _), blb ≠ x → ∀ (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A' blt1 → blb ∈ A' blt2 → blb ∈ A' blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A' bls ∩ A' bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3))) := by
  intro b hbx t1 t2 t3 h12 h13 h23 hb1 hb2 hb3
  obtain ⟨p, hsep, hns⟩ := h b hbx (f t1) (f t2) (f t3) (fun e => h12 (hf e)) (fun e => h13 (hf e))
    (fun e => h23 (hf e)) (hA' _ hb1) (hA' _ hb2) (hA' _ hb3)
  refine ⟨fun s => p (f s), fun s s' hs hs' => ?_, hns⟩
  exact (Finset.inter_subset_inter (hA' s) (hA' s')).trans (hsep _ _ hs hs')

/-- Degrees do not increase in subfamilies. -/
theorem deg_mono {T' : Type} [Fintype T'] (A : T → Finset B) (f : T' → T)
    (hf : Function.Injective f) (A' : T' → Finset B) (hA' : ∀ t, A' t ⊆ A (f t)) (x : B) :
    (Finset.univ.filter (fun t => x ∈ A' t)).card ≤ (Finset.univ.filter (fun t => x ∈ A t)).card := by
  have hsub : (Finset.univ.filter (fun t => x ∈ A' t)).map ⟨f, hf⟩ ⊆
      Finset.univ.filter (fun t => x ∈ A t) := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    exact hA' t' ht'
  have := Finset.card_le_card hsub
  rwa [Finset.card_map] at this

/-- Theorem BLX: HP, the block condition at every element other than `x`, and `x` in at most three
sets ⟹ P1. -/
theorem theorem_BLX : ∀ (n : ℕ) (T : Type) [Fintype T] [DecidableEq T] (A : T → Finset B) (x : B),
    Fintype.card T = n → (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card) → (∀ (blb : _), blb ≠ x → ∀ (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A blt1 → blb ∈ A blt2 → blb ∈ A blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3))) →
    (Finset.univ.filter (fun t => x ∈ A t)).card ≤ 3 → (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro T _ _ A x hn hHP hBL hx3
  classical
  by_cases hthree : ∃ b, b ≠ x ∧ 2 < (Finset.univ.filter (fun t => b ∈ A t)).card
  · obtain ⟨b, hbx, hb⟩ := hthree
    obtain ⟨t1, ht1, t2, ht2, t3, ht3, h12, h13, h23⟩ := Finset.two_lt_card.mp hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2 ht3
    obtain ⟨p, hsep, hns⟩ := hBL b hbx t1 t2 t3 h12 h13 h23 ht1 ht2 ht3
    have hboth : (∃ s, p s) ∧ (∃ s, ¬ p s) := by
      by_cases hp1 : p t1
      · by_cases hp2 : p t2
        · by_cases hp3 : p t3
          · exact absurd ⟨iff_of_true hp1 hp2, iff_of_true hp1 hp3⟩ hns
          · exact ⟨⟨t1, hp1⟩, ⟨t3, hp3⟩⟩
        · exact ⟨⟨t1, hp1⟩, ⟨t2, hp2⟩⟩
      · by_cases hp2 : p t2
        · exact ⟨⟨t2, hp2⟩, ⟨t1, hp1⟩⟩
        · by_cases hp3 : p t3
          · exact ⟨⟨t3, hp3⟩, ⟨t1, hp1⟩⟩
          · exact absurd ⟨iff_of_false hp1 hp2, iff_of_false hp1 hp3⟩ hns
    obtain ⟨⟨s1, hs1⟩, ⟨s2, hs2⟩⟩ := hboth
    have c1 : Fintype.card {t // p t} < n := hn ▸ Fintype.card_subtype_lt hs2
    have c2 : Fintype.card {t // ¬ p t} < n := hn ▸ Fintype.card_subtype_lt (not_not.mpr hs1)
    have v1 := Subtype.val_injective (p := p)
    have v2 := Subtype.val_injective (p := fun t => ¬ p t)
    exact theorem_CE A hHP b p hsep
      (fun hm => ih _ c1 {t // p t} _ x rfl hm
        (blx_mono A x hBL Subtype.val v1 _ (fun t => Finset.erase_subset _ _))
        ((deg_mono A Subtype.val v1 _ (fun t => Finset.erase_subset _ _) x).trans hx3))
      (ih _ c1 {t // p t} _ x rfl (hp_sub A hHP Subtype.val v1)
        (blx_mono A x hBL Subtype.val v1 _ (fun t => subset_rfl))
        ((deg_mono A Subtype.val v1 _ (fun t => subset_rfl) x).trans hx3))
      (fun hm => ih _ c2 {t // ¬ p t} _ x rfl hm
        (blx_mono A x hBL Subtype.val v2 _ (fun t => Finset.erase_subset _ _))
        ((deg_mono A Subtype.val v2 _ (fun t => Finset.erase_subset _ _) x).trans hx3))
      (ih _ c2 {t // ¬ p t} _ x rfl (hp_sub A hHP Subtype.val v2)
        (blx_mono A x hBL Subtype.val v2 _ (fun t => subset_rfl))
        ((deg_mono A Subtype.val v2 _ (fun t => subset_rfl) x).trans hx3))
  · push Not at hthree
    intro v
    exact theorem_GL3 A hHP x hthree hx3 v

/-- Theorem BLX in the graph form of the R3 statement `H1`. -/
theorem BLX_R3form (A : T → Finset B) (x : B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (hBL : (∀ (blb : _), blb ≠ x → ∀ (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A blt1 → blb ∈ A blt2 → blb ∈ A blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3))))
    (hx : (Finset.univ.filter (fun t => x ∈ A t)).card ≤ 3) (v : B) :
    ∃ e : T → B × B,
      (∀ t : T, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      Function.Injective (fun t : T => s((e t).1, (e t).2)) ∧
      (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).IsAcyclic ∧
      (∀ x a b c : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x b →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x c →
        a = b ∨ a = c ∨ b = c) ∧
      (∀ a b : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v b → a = b) := by
  obtain ⟨e, he, hL, hd2, hd1⟩ := theorem_BLX _ T A x rfl h hBL hx v
  obtain ⟨b1, b2, b3, b4⟩ := bridge e (fun t => (he t).2.2) hL hd2 v hd1
  exact ⟨e, he, b1, b2, b3, b4⟩

end fam

section

private lemma isAcyclic_of_all_adj_eq {W : Type*} (H : SimpleGraph W) (r : W)
    (hstar : ∀ a b : W, H.Adj a b → a = r ∨ b = r) : H.IsAcyclic := by
  intro u c hc
  have hlen := hc.three_le_length
  cases c with
  | nil => simp at hlen
  | @cons _ x _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ y _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 c3 =>
        have hnd : (x :: y :: c3.support).Nodup := hc.support_nodup
        rw [List.nodup_cons] at hnd
        have hx_not : x ∉ y :: c3.support := hnd.1
        have hy_nd : (y :: c3.support).Nodup := hnd.2
        rw [List.nodup_cons] at hy_nd
        have hy_not : y ∉ c3.support := hy_nd.1
        have hz_mem : z ∈ c3.support := c3.start_mem_support
        have hu_mem : u ∈ c3.support := c3.end_mem_support
        rcases hstar u x h1 with rfl | rfl
        · rcases hstar x y h2 with hxr | rfl
          · exact H.ne_of_adj h1 hxr.symm
          · exact hy_not hu_mem
        · rcases hstar y z h3 with hyx | rfl
          · exact H.ne_of_adj h2 hyx.symm
          · exact hx_not (List.mem_cons_of_mem _ hz_mem)

private lemma indep_add_one_le_forest {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hconn : H.Connected) (hn : 1 < Fintype.card W)
    (I : Finset W) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H.Adj x y) :
    I.card + 1 ≤ H.largestInducedForestSize := by
  obtain ⟨w, hw⟩ : ∃ w : W, w ∉ I := by
    by_contra hall
    push Not at hall
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hn
    obtain ⟨p⟩ := hconn.preconnected x y
    cases p with
    | nil => exact hxy rfl
    | @cons _ z _ hxz _ => exact hind x (hall x) z (hall z) hxz
  let T : Finset W := insert w I
  have hTcard : T.card = I.card + 1 := Finset.card_insert_of_notMem hw
  have hTacyc : (H.induce (T : Set W)).IsAcyclic := by
    apply isAcyclic_of_all_adj_eq (H.induce (T : Set W)) ⟨w, Finset.mem_insert_self w I⟩
    intro a b hadj
    have ha : a.val = w ∨ a.val ∈ I := Finset.mem_insert.mp a.prop
    have hb : b.val = w ∨ b.val ∈ I := Finset.mem_insert.mp b.prop
    rcases ha with haw | haI
    · exact Or.inl (Subtype.ext haw)
    · rcases hb with hbw | hbI
      · exact Or.inr (Subtype.ext hbw)
      · exact (hind a.val haI b.val hbI hadj).elim
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card W, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨T, hTacyc, hTcard⟩

private lemma ncvr_exists_acyclic_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ F : Finset α, (G.induce (F : Set α)).IsAcyclic ∧
      F.card = G.largestInducedForestSize := by
  have hne : { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    intro u
    exact False.elim (Finset.notMem_empty u.1 u.2)
  have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact Nat.sSup_mem hne hbdd

private lemma ncvr_card_le_largestInducedForestSize {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (F : Finset α) (hF : (G.induce (F : Set α)).IsAcyclic) :
    F.card ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨F, hF, rfl⟩

private lemma r2_isPathCover_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} (hle : K ≤ G) {P : Finset (Finset V)} (hP : K.IsPathCover P) :
    G.IsPathCover P := by
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  refine ⟨hdisj, hcov, ?_⟩
  intro s hs
  rcases hpaths s hs with ⟨u, w, p, hp, rfl⟩
  refine ⟨u, w, p.mapLe hle, hp.mapLe hle, ?_⟩
  rw [Walk.support_mapLe_eq_support]

end

section

private lemma p1_reach_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (ψ : V → W)
    (hψ : ∀ u w, G.Adj u w → ψ u = ψ w ∨ H.Adj (ψ u) (ψ w)) {u w : V}
    (h : G.Reachable u w) : H.Reachable (ψ u) (ψ w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih =>
    rcases hψ _ _ hadj with heq | hadj'
    · rw [heq]; exact ih
    · exact hadj'.reachable.trans ih

private lemma p1_path_interior {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (x : V) (hx : x ∈ p.support) :
    x = u ∨ x = v ∨ ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
  induction p with
  | nil =>
    left
    simpa using hx
  | @cons u w v h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with hxu | hx
    · exact Or.inl hxu
    · rcases ih hp.1 hx with hxw | hxv | h3
      · subst hxw
        cases q with
        | nil => exact Or.inr (Or.inl rfl)
        | @cons _ w' _ h' q' =>
          refine Or.inr (Or.inr ⟨u, w', ?_, h.symm, h'⟩)
          intro huw
          apply hp.2
          rw [Walk.support_cons, List.mem_cons]
          right
          rw [huw]
          exact q'.start_mem_support
      · exact Or.inr (Or.inl hxv)
      · exact Or.inr (Or.inr h3)

private lemma p1_reachable_of_mem_support {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) : G.Reachable x y :=
  (Walk.reachable (p.takeUntil x hx)).symm.trans (Walk.reachable (p.takeUntil y hy))

/-- A path whose vertex set contains a vertex `x` without two distinct neighbours can be
re-oriented to end at `x`. -/
private lemma p1_path_to_end {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (x : V) (hx : x ∈ p.support)
    (hdeg : ∀ a b, G.Adj x a → G.Adj x b → a = b) :
    ∃ (z : V) (q : G.Walk z x), q.IsPath ∧ q.support.toFinset = p.support.toFinset := by
  rcases p1_path_interior p hp x hx with rfl | rfl | ⟨a, b, hab, ha, hb⟩
  · refine ⟨v, p.reverse, hp.reverse, ?_⟩
    rw [Walk.support_reverse, List.toFinset_reverse]
  · exact ⟨u, p, hp, rfl⟩
  · exact (hab (hdeg a b ha hb)).elim

/-- Path cover from a linear forest given by a finite edge set: every edge is a bridge and no
vertex lies on three edges. -/
private lemma p1_linear_forest_cover {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (hdiag : ∀ x y, s(x, y) ∈ E → x ≠ y)
    (hdeg : ∀ x a b c, s(x, a) ∈ E → s(x, b) ∈ E → s(x, c) ∈ E → a = b ∨ a = c ∨ b = c)
    (hbr : ∀ x y, s(x, y) ∈ E →
      ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y) :
    ∃ P : Finset (Finset V),
      (fromEdgeSet (E : Set (Sym2 V))).IsPathCover P ∧ P.card + E.card = Fintype.card V := by
  suffices hmain : ∀ E' : Finset (Sym2 V), E' ⊆ E → ∃ P : Finset (Finset V),
      (fromEdgeSet (E' : Set (Sym2 V))).IsPathCover P ∧ P.card + E'.card = Fintype.card V from
    hmain E (Finset.Subset.refl E)
  intro E'
  induction E' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨Finset.univ.image (fun x : V => ({x} : Finset V)), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro s1 hs1 s2 hs2 hne_s
      rcases Finset.mem_image.mp hs1 with ⟨x1, _, rfl⟩
      rcases Finset.mem_image.mp hs2 with ⟨x2, _, rfl⟩
      rw [Finset.disjoint_singleton]
      intro hx
      exact hne_s (by rw [hx])
    · intro x _
      rw [Finset.mem_biUnion]
      exact ⟨{x}, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, Finset.mem_singleton_self x⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
      exact ⟨x, x, Walk.nil, Walk.IsPath.nil, by simp⟩
    · rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_empty,
        Finset.card_univ, Nat.add_zero]
  | @insert e E0 he ih =>
    intro hsub
    have hE0 : E0 ⊆ E := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    have heE : e ∈ E := hsub (Finset.mem_insert_self e E0)
    obtain ⟨P0, hP0, hcard0⟩ := ih hE0
    obtain ⟨hdisj, hcov, hpaths⟩ := hP0
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : x ≠ y := hdiag x y heE
    have hle : fromEdgeSet (E0 : Set (Sym2 V)) ≤
        fromEdgeSet ((insert s(x, y) E0 : Finset (Sym2 V)) : Set (Sym2 V)) := by
      apply fromEdgeSet_mono
      intro z hz
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hz))
    have hadj : (fromEdgeSet ((insert s(x, y) E0 : Finset (Sym2 V)) : Set (Sym2 V))).Adj x y := by
      rw [fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr (Finset.mem_insert_self _ _), hxy⟩
    have hnr : ¬ (fromEdgeSet (E0 : Set (Sym2 V))).Reachable x y := by
      intro hr
      apply hbr x y heE
      refine hr.mono (fromEdgeSet_mono ?_)
      intro z hz
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, hE0 (Finset.mem_coe.mp hz)⟩
      rintro rfl
      exact he (Finset.mem_coe.mp hz)
    have hdx : ∀ a b, (fromEdgeSet (E0 : Set (Sym2 V))).Adj x a →
        (fromEdgeSet (E0 : Set (Sym2 V))).Adj x b → a = b := by
      intro a b ha hb
      rw [fromEdgeSet_adj] at ha hb
      have ha' : s(x, a) ∈ E0 := Finset.mem_coe.mp ha.1
      have hb' : s(x, b) ∈ E0 := Finset.mem_coe.mp hb.1
      rcases hdeg x a b y (hE0 ha') (hE0 hb') heE with h | h | h
      · exact h
      · exact (he (h ▸ ha')).elim
      · exact (he (h ▸ hb')).elim
    have hdy : ∀ a b, (fromEdgeSet (E0 : Set (Sym2 V))).Adj y a →
        (fromEdgeSet (E0 : Set (Sym2 V))).Adj y b → a = b := by
      intro a b ha hb
      rw [fromEdgeSet_adj] at ha hb
      have ha' : s(y, a) ∈ E0 := Finset.mem_coe.mp ha.1
      have hb' : s(y, b) ∈ E0 := Finset.mem_coe.mp hb.1
      have heE' : s(y, x) ∈ E := Sym2.eq_swap ▸ heE
      have he' : s(y, x) ∉ E0 := Sym2.eq_swap ▸ he
      rcases hdeg y a b x (hE0 ha') (hE0 hb') heE' with h | h | h
      · exact h
      · exact (he' (h ▸ ha')).elim
      · exact (he' (h ▸ hb')).elim
    obtain ⟨s1, hs1P, hxs1⟩ : ∃ s ∈ P0, x ∈ s := by
      have := hcov (Finset.mem_univ x)
      rw [Finset.mem_biUnion] at this
      exact this
    obtain ⟨s2, hs2P, hys2⟩ : ∃ s ∈ P0, y ∈ s := by
      have := hcov (Finset.mem_univ y)
      rw [Finset.mem_biUnion] at this
      exact this
    obtain ⟨u1, v1, p1, hp1, hs1eq⟩ := hpaths s1 hs1P
    obtain ⟨u2, v2, p2, hp2, hs2eq⟩ := hpaths s2 hs2P
    have hx1 : x ∈ p1.support := by
      rw [hs1eq] at hxs1
      exact List.mem_toFinset.mp hxs1
    have hy2 : y ∈ p2.support := by
      rw [hs2eq] at hys2
      exact List.mem_toFinset.mp hys2
    have hs12 : s1 ≠ s2 := by
      intro h
      apply hnr
      have hy1 : y ∈ p1.support := by
        rw [← h, hs1eq] at hys2
        exact List.mem_toFinset.mp hys2
      exact p1_reachable_of_mem_support p1 hx1 hy1
    have hd12 : Disjoint s1 s2 := hdisj s1 hs1P s2 hs2P hs12
    obtain ⟨z1, q1, hq1, hq1s⟩ := p1_path_to_end p1 hp1 x hx1 hdx
    obtain ⟨z2, q2, hq2, hq2s⟩ := p1_path_to_end p2 hp2 y hy2 hdy
    rw [← hs1eq] at hq1s
    rw [← hs2eq] at hq2s
    let w := (q1.mapLe hle).append (Walk.cons hadj (q2.mapLe hle).reverse)
    have hwsupp : w.support = q1.support ++ q2.support.reverse := by
      simp only [w, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_reverse,
        Walk.support_mapLe_eq_support]
    have hwpath : w.IsPath := by
      rw [Walk.isPath_def, hwsupp, List.nodup_append]
      refine ⟨hq1.support_nodup, List.nodup_reverse.mpr hq2.support_nodup, ?_⟩
      intro a ha b hb hab
      subst hab
      have h1 : a ∈ s1 := by
        rw [← hq1s]
        exact List.mem_toFinset.mpr ha
      have h2 : a ∈ s2 := by
        rw [← hq2s]
        exact List.mem_toFinset.mpr (List.mem_reverse.mp hb)
      exact Finset.disjoint_left.mp hd12 h1 h2
    have hwfin : s1 ∪ s2 = w.support.toFinset := by
      rw [hwsupp, List.toFinset_append, List.toFinset_reverse, hq1s, hq2s]
    have hs2P' : s2 ∈ P0.erase s1 := Finset.mem_erase.mpr ⟨fun h => hs12 h.symm, hs2P⟩
    have hnew : s1 ∪ s2 ∉ (P0.erase s1).erase s2 := by
      intro h
      have h3 := Finset.mem_erase.mp h
      have h4 := Finset.mem_erase.mp h3.2
      have hd := hdisj (s1 ∪ s2) h4.2 s1 hs1P h4.1
      exact Finset.disjoint_left.mp hd (Finset.mem_union_left _ hxs1) hxs1
    refine ⟨insert (s1 ∪ s2) ((P0.erase s1).erase s2), ⟨?_, ?_, ?_⟩, ?_⟩
    · have hkey : ∀ t ∈ (P0.erase s1).erase s2, Disjoint (s1 ∪ s2) t := by
        intro t ht
        have h3 := Finset.mem_erase.mp ht
        have h4 := Finset.mem_erase.mp h3.2
        rw [Finset.disjoint_union_left]
        exact ⟨hdisj s1 hs1P t h4.2 (Ne.symm h4.1), hdisj s2 hs2P t h4.2 (Ne.symm h3.1)⟩
      intro t1 ht1 t2 ht2 hne
      rcases Finset.mem_insert.mp ht1 with rfl | ht1'
      · rcases Finset.mem_insert.mp ht2 with rfl | ht2'
        · exact (hne rfl).elim
        · exact hkey t2 ht2'
      · rcases Finset.mem_insert.mp ht2 with rfl | ht2'
        · exact (hkey t1 ht1').symm
        · exact hdisj t1 (Finset.mem_erase.mp (Finset.mem_erase.mp ht1').2).2 t2
            (Finset.mem_erase.mp (Finset.mem_erase.mp ht2').2).2 hne
    · intro a _
      have := hcov (Finset.mem_univ a)
      rw [Finset.mem_biUnion] at this ⊢
      obtain ⟨t, htP, hat⟩ := this
      by_cases ht1 : t = s1
      · exact ⟨s1 ∪ s2, Finset.mem_insert_self _ _, Finset.mem_union_left _ (ht1 ▸ hat)⟩
      · by_cases ht2 : t = s2
        · exact ⟨s1 ∪ s2, Finset.mem_insert_self _ _, Finset.mem_union_right _ (ht2 ▸ hat)⟩
        · exact ⟨t, Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨ht2, Finset.mem_erase.mpr ⟨ht1, htP⟩⟩), hat⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact ⟨z1, z2, w, hwpath, hwfin⟩
      · obtain ⟨a, b, p, hp, hpe⟩ := hpaths t (Finset.mem_erase.mp (Finset.mem_erase.mp ht').2).2
        refine ⟨a, b, p.mapLe hle, hp.mapLe hle, ?_⟩
        rw [Walk.support_mapLe_eq_support]
        exact hpe
    · rw [Finset.card_insert_of_notMem hnew, Finset.card_erase_of_mem hs2P',
        Finset.card_erase_of_mem hs1P, Finset.card_insert_of_notMem he]
      have h1 : 0 < P0.card := Finset.card_pos.mpr ⟨s1, hs1P⟩
      have h2 : 0 < (P0.erase s1).card := Finset.card_pos.mpr ⟨s2, hs2P'⟩
      rw [Finset.card_erase_of_mem hs1P] at h2
      omega

/-- Exchange: adding to a subforest an independent set of vertices each having at most one
neighbour in it keeps the induced graph acyclic. -/
private lemma p1_exchange_acyclic {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U R D : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic) (hRU : R ⊆ U)
    (hDU : ∀ d ∈ D, d ∉ U)
    (hDind : ∀ d ∈ D, ∀ d' ∈ D, ¬ G.Adj d d')
    (hD1 : ∀ d ∈ D, ∀ a ∈ R, ∀ b ∈ R, G.Adj d a → G.Adj d b → a = b) :
    (G.induce ((R ∪ D : Finset V) : Set V)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  have hleaf : ∀ u w : ((R ∪ D : Finset V) : Set V), u.1 ∈ D →
      (G.induce ((R ∪ D : Finset V) : Set V)).Adj u w →
      ¬ ((G.induce ((R ∪ D : Finset V) : Set V)).deleteEdges {s(u, w)}).Reachable u w := by
    intro u w hu hadj hreach
    have hGw : G.Adj u.1 w.1 := hadj
    have hwR : w.1 ∈ R := by
      rcases Finset.mem_union.mp (Finset.mem_coe.mp w.2) with h | h
      · exact h
      · exact (hDind u.1 hu w.1 h hGw).elim
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact hGw.ne rfl
    | @cons _ z _ h _ =>
      rw [deleteEdges_adj] at h
      have hGz : G.Adj u.1 z.1 := h.1
      have hzR : z.1 ∈ R := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with h' | h'
        · exact h'
        · exact (hDind u.1 hu z.1 h' hGz).elim
      have hzw : z.1 = w.1 := hD1 u.1 hu z.1 hzR w.1 hwR hGz hGw
      apply h.2
      rw [Set.mem_singleton_iff, Subtype.ext hzw]
  intro u w hadj
  rw [isBridge_iff]
  by_cases hu : u.1 ∈ D
  · exact hleaf u w hu hadj
  by_cases hw : w.1 ∈ D
  · intro hreach
    apply hleaf w u hw hadj.symm
    rw [Sym2.eq_swap]
    exact hreach.symm
  have huR : u.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp u.2)).resolve_right hu
  have hwR : w.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp w.2)).resolve_right hw
  have huU : u.1 ∈ U := hRU huR
  have hwU : w.1 ∈ U := hRU hwR
  intro hreach
  classical
  let ψ : ((R ∪ D : Finset V) : Set V) → ((U : Set V)) := fun z =>
    if hz : z.1 ∈ U then ⟨z.1, hz⟩ else
      if hex : ∃ a, a ∈ R ∧ G.Adj z.1 a then ⟨hex.choose, hRU hex.choose_spec.1⟩
      else ⟨u.1, huU⟩
  have hψU : ∀ (z : ((R ∪ D : Finset V) : Set V)) (hz : z.1 ∈ U), ψ z = ⟨z.1, hz⟩ :=
    fun z hz => dif_pos hz
  have hbridge := (isAcyclic_iff_forall_adj_isBridge.mp hU)
    (show (G.induce (U : Set V)).Adj ⟨u.1, huU⟩ ⟨w.1, hwU⟩ from hadj)
  rw [isBridge_iff] at hbridge
  apply hbridge
  have key : ∀ y y' : ((R ∪ D : Finset V) : Set V), G.Adj y.1 y'.1 → y.1 ∉ U → y'.1 ∈ U →
      ψ y = ψ y' := by
    intro y y' hyy hy hy'
    have hyD : y.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp y.2)).resolve_left
      (fun h => hy (hRU h))
    have hy'R : y'.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp y'.2)).resolve_right
      (fun h => hDU _ h hy')
    have hex : ∃ a, a ∈ R ∧ G.Adj y.1 a := ⟨y'.1, hy'R, hyy⟩
    rw [hψU y' hy']
    have h1 : ψ y = ⟨hex.choose, hRU hex.choose_spec.1⟩ := by
      dsimp only [ψ]
      rw [dif_neg hy, dif_pos hex]
    rw [h1]
    exact Subtype.ext (hD1 y.1 hyD _ hex.choose_spec.1 _ hy'R hex.choose_spec.2 hyy)
  have hmap := p1_reach_map
    (H := (G.induce (U : Set V)).deleteEdges {s(⟨u.1, huU⟩, ⟨w.1, hwU⟩)}) ψ ?_ hreach
  · rwa [hψU u huU, hψU w hwU] at hmap
  intro z z' hzz
  rw [deleteEdges_adj] at hzz
  obtain ⟨hG, hne⟩ := hzz
  have hG' : G.Adj z.1 z'.1 := hG
  by_cases hz : z.1 ∈ U
  · by_cases hz' : z'.1 ∈ U
    · right
      rw [hψU z hz, hψU z' hz', deleteEdges_adj]
      refine ⟨hG', ?_⟩
      intro hmem
      apply hne
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext (Subtype.mk.inj h1), Subtype.ext (Subtype.mk.inj h2)⟩
      · exact Or.inr ⟨Subtype.ext (Subtype.mk.inj h1), Subtype.ext (Subtype.mk.inj h2)⟩
    · left
      exact (key z' z hG'.symm hz' hz).symm
  · by_cases hz' : z'.1 ∈ U
    · left
      exact key z z' hG' hz hz'
    · exfalso
      have hzD : z.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp z.2)).resolve_left
        (fun h => hz (hRU h))
      have hz'D : z'.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp z'.2)).resolve_left
        (fun h => hz' (hRU h))
      exact hDind _ hzD _ hz'D hG'

/-- The all-but-one Hall condition HP for the neighbourhoods, inside a maximum induced forest
`U`, of the outside vertices of one colour. -/
private lemma p1_hp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {κ : Type*} [DecidableEq κ] (c : V → κ)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card) (i : κ)
    (S : Finset V) :
    (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).card ≤ S.card := by
  obtain ⟨D, hD⟩ : ∃ D : Finset V, D = (Finset.univ.filter
      (fun t : {t : V // t ∉ U ∧ c t = i} =>
        ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).image Subtype.val := ⟨_, rfl⟩
  have hDcard : D.card = (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).card := by
    rw [hD]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hmem : ∀ d ∈ D, d ∉ U ∧ c d = i ∧ ((U.filter (fun x => G.Adj d x)) \ S).card ≤ 1 := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    exact ⟨t.2.1, t.2.2, (Finset.mem_filter.mp ht).2⟩
  have hac := p1_exchange_acyclic G U (U \ S) D hU Finset.sdiff_subset
    (fun d hd => (hmem d hd).1)
    (fun d hd d' hd' hadj => hc d d' hadj ((hmem d hd).2.1.trans (hmem d' hd').2.1.symm))
    (fun d hd a ha b hb hda hdb => Finset.card_le_one.mp (hmem d hd).2.2 a
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, hda⟩,
        (Finset.mem_sdiff.mp ha).2⟩) b
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hdb⟩,
        (Finset.mem_sdiff.mp hb).2⟩))
  have h1 := hmax _ hac
  have hdisj : Disjoint (U \ S) D :=
    Finset.disjoint_left.mpr (fun x hx hxD => (hmem x hxD).1 (Finset.mem_sdiff.mp hx).1)
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 : U.card ≤ (U \ S).card + S.card := by
    rw [Finset.card_sdiff_add_card]
    exact Finset.card_le_card Finset.subset_union_left
  rw [← hDcard]
  omega

/-- One colour side: from Theorem BL, a set of edges between the outside vertices of colour `i` and
the maximum induced forest `U` forming a linear forest with degree two at every such outside
vertex and degree at most one at the prescribed forest vertex `v`. -/
private lemma p1_side {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V → Fin 2) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card)
    (i : Fin 2) (x0 : V)
    (hBLG : ∀ x ∈ U, x ≠ x0 → c x ≠ i → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
        (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
        ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3)))
    (hx0 : x0 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
      G.Adj x0 t1 → G.Adj x0 t2 → G.Adj x0 t3 → G.Adj x0 t4 →
      t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (v : V) (hvU : v ∈ U) :
    ∃ E : Finset (Sym2 V),
      (∀ p q, s(p, q) ∈ E →
        G.Adj p q ∧ ((p ∉ U ∧ c p = i ∧ q ∈ U) ∨ (q ∉ U ∧ c q = i ∧ p ∈ U))) ∧
      E.card = 2 * (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = i)).card ∧
      (∀ x p q r, s(x, p) ∈ E → s(x, q) ∈ E → s(x, r) ∈ E → p = q ∨ p = r ∨ q = r) ∧
      (∀ p q, s(v, p) ∈ E → s(v, q) ∈ E → p = q) ∧
      (∀ x y, s(x, y) ∈ E →
        ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y) := by
  classical
  have hdeg0 : (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      x0 ∈ U.filter (fun x => G.Adj t.1 x))).card ≤ 3 := by
    by_contra hbig
    push Not at hbig
    obtain ⟨s0, hs0⟩ : (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0 ∈ U.filter (fun x => G.Adj t.1 x))).Nonempty := Finset.card_pos.mp (by omega)
    have hlt : 2 < ((Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0 ∈ U.filter (fun x => G.Adj t.1 x))).erase s0).card := by
      rw [Finset.card_erase_of_mem hs0]; omega
    obtain ⟨s1, hs1, s2, hs2, s3, hs3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
    have adj : ∀ s ∈ Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
        x0 ∈ U.filter (fun x => G.Adj t.1 x)), G.Adj x0 s.1 := by
      intro s hs
      exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hs).2).2).symm
    have e1 := Finset.ne_of_mem_erase hs1
    have e2 := Finset.ne_of_mem_erase hs2
    have e3 := Finset.ne_of_mem_erase hs3
    have f1 := Finset.mem_of_mem_erase hs1
    have f2 := Finset.mem_of_mem_erase hs2
    have f3 := Finset.mem_of_mem_erase hs3
    rcases hx0 (Finset.mem_filter.mp (Finset.mem_filter.mp hs0).2).1 s0.1 s1.1 s2.1 s3.1 s0.2.1 s1.2.1 s2.2.1 s3.2.1 (adj s0 hs0) (adj s1 f1)
      (adj s2 f2) (adj s3 f3) with h | h | h | h | h | h
    · exact e1 (Subtype.ext h).symm
    · exact e2 (Subtype.ext h).symm
    · exact e3 (Subtype.ext h).symm
    · exact h12 (Subtype.ext h)
    · exact h13 (Subtype.ext h)
    · exact h23 (Subtype.ext h)
  obtain ⟨e, he1, hinj, hacyc, hdeg, hv⟩ := BLX_R3form
    (fun t : {t : V // t ∉ U ∧ c t = i} => U.filter (fun x => G.Adj t.1 x)) x0
    (p1_hp G c hc U hU hmax i) (by
      intro b hbx0 t1 t2 t3 h12 h13 h23 hb1 hb2 hb3
      have m1 : b ∈ U ∧ G.Adj t1.1 b := Finset.mem_filter.mp hb1
      have m2 : b ∈ U ∧ G.Adj t2.1 b := Finset.mem_filter.mp hb2
      have m3 : b ∈ U ∧ G.Adj t3.1 b := Finset.mem_filter.mp hb3
      have hcb : c b ≠ i := fun e => hc t1.1 b m1.2 (t1.2.2.trans e.symm)
      obtain ⟨p, hsep, hns⟩ := hBLG b m1.1 hbx0 hcb t1.1 t2.1 t3.1 t1.2.1 t2.2.1 t3.2.1
        (fun h => h12 (Subtype.ext h)) (fun h => h13 (Subtype.ext h)) (fun h => h23 (Subtype.ext h))
        m1.2.symm m2.2.symm m3.2.symm
      refine ⟨fun s => p s.1, fun s s' hs hs' => ?_, hns⟩
      intro z hz
      have z1 : z ∈ U ∧ G.Adj s.1 z := Finset.mem_filter.mp (Finset.mem_inter.mp hz).1
      have z2 : z ∈ U ∧ G.Adj s'.1 z := Finset.mem_filter.mp (Finset.mem_inter.mp hz).2
      exact Finset.mem_singleton.mpr (hsep s.1 s'.1 s.2.1 s'.2.1 hs hs' z z1.1 z1.2 z2.2)) hdeg0 v
  obtain ⟨Pg, hPg⟩ : ∃ Pg : SimpleGraph V, Pg = SimpleGraph.fromRel
      (fun x y : V => ∃ t : {t : V // t ∉ U ∧ c t = i}, e t = (x, y)) := ⟨_, rfl⟩
  rw [← hPg] at hacyc hdeg hv
  let X : {t : V // t ∉ U ∧ c t = i} → Bool → V := fun t k => cond k (e t).1 (e t).2
  have hXU : ∀ t k, X t k ∈ U := by
    intro t k
    cases k
    · exact (Finset.mem_filter.mp (he1 t).2.1).1
    · exact (Finset.mem_filter.mp (he1 t).1).1
  have hXadj : ∀ t k, G.Adj t.1 (X t k) := by
    intro t k
    cases k
    · exact (Finset.mem_filter.mp (he1 t).2.1).2
    · exact (Finset.mem_filter.mp (he1 t).1).2
  have hXne : ∀ t k, X t k ≠ X t (!k) := by
    intro t k
    cases k
    · exact (he1 t).2.2.symm
    · exact (he1 t).2.2
  have hXP : ∀ t k, Pg.Adj (X t k) (X t (!k)) := by
    intro t k
    rw [hPg, SimpleGraph.fromRel_adj]
    refine ⟨hXne t k, ?_⟩
    cases k
    · exact Or.inr ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
  have hXs : ∀ t k, s(X t k, X t (!k)) = s((e t).1, (e t).2) := by
    intro t k
    cases k
    · exact Sym2.eq_swap
    · rfl
  have hfin : ∀ t k t' k', X t k = X t' k' → X t (!k) = X t' (!k') → t = t' := by
    intro t k t' k' h1 h2
    apply hinj
    show s((e t).1, (e t).2) = s((e t').1, (e t').2)
    rw [← hXs t k, ← hXs t' k', h1, h2]
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 V), E = (Finset.univ :
      Finset ({t : V // t ∉ U ∧ c t = i} × Bool)).image
        (fun tk => s(tk.1.1, X tk.1 tk.2)) := ⟨_, rfl⟩
  have hE : ∀ p q, s(p, q) ∈ E → ∃ t k, (p = t.1 ∧ q = X t k) ∨ (q = t.1 ∧ p = X t k) := by
    intro p q h
    rw [hEdef] at h
    obtain ⟨⟨t, k⟩, _, htk⟩ := Finset.mem_image.mp h
    rw [Sym2.eq_iff] at htk
    rcases htk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨t, k, Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨t, k, Or.inr ⟨h1.symm, h2.symm⟩⟩
  have hEU : ∀ x p, x ∈ U → s(x, p) ∈ E → ∃ t k, p = t.1 ∧ x = X t k := by
    intro x p hx h
    obtain ⟨t, k, h' | h'⟩ := hE x p h
    · exact (t.2.1 (h'.1 ▸ hx)).elim
    · exact ⟨t, k, h'⟩
  have hEN : ∀ x p, x ∉ U → s(x, p) ∈ E → ∃ t k, x = t.1 ∧ p = X t k := by
    intro x p hx h
    obtain ⟨t, k, h' | h'⟩ := hE x p h
    · exact ⟨t, k, h'⟩
    · exact (hx (h'.2 ▸ hXU t k)).elim
  have hbool : ∀ k k' : Bool, k ≠ k' → k' = !k := by decide
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h
    obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE p q h
    · exact ⟨hXadj t k, Or.inl ⟨t.2.1, t.2.2, hXU t k⟩⟩
    · exact ⟨(hXadj t k).symm, Or.inr ⟨t.2.1, t.2.2, hXU t k⟩⟩
  · rw [hEdef, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_subtype, Nat.mul_comm]
    rintro ⟨t, k⟩ ⟨t', k'⟩ h
    simp only at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have htt : t = t' := Subtype.ext h1
      subst htt
      have hkk : k = k' := by
        by_contra hne
        have hk' : k' = !k := hbool k k' hne
        rw [hk'] at h2
        exact hXne t k h2
      rw [hkk]
    · exact (t.2.1 (h1 ▸ hXU t' k')).elim
  · intro x p q r hp hq hr
    by_cases hx : x ∈ U
    · obtain ⟨tp, kp, hp1, hp2⟩ := hEU x p hx hp
      obtain ⟨tq, kq, hq1, hq2⟩ := hEU x q hx hq
      obtain ⟨tr, kr, hr1, hr2⟩ := hEU x r hx hr
      have hap : Pg.Adj x (X tp (!kp)) := by
        rw [hp2]
        exact hXP tp kp
      have haq : Pg.Adj x (X tq (!kq)) := by
        rw [hq2]
        exact hXP tq kq
      have har : Pg.Adj x (X tr (!kr)) := by
        rw [hr2]
        exact hXP tr kr
      rcases hdeg x _ _ _ hap haq har with h | h | h
      · left
        rw [hp1, hq1, hfin tp kp tq kq (hp2.symm.trans hq2) h]
      · right
        left
        rw [hp1, hr1, hfin tp kp tr kr (hp2.symm.trans hr2) h]
      · right
        right
        rw [hq1, hr1, hfin tq kq tr kr (hq2.symm.trans hr2) h]
    · obtain ⟨tp, kp, hp1, hp2⟩ := hEN x p hx hp
      obtain ⟨tq, kq, hq1, hq2⟩ := hEN x q hx hq
      obtain ⟨tr, kr, hr1, hr2⟩ := hEN x r hx hr
      have e1 : tq = tp := Subtype.ext (hq1.symm.trans hp1)
      have e2 : tr = tp := Subtype.ext (hr1.symm.trans hp1)
      rw [e1] at hq2
      rw [e2] at hr2
      rw [hp2, hq2, hr2]
      cases kp <;> cases kq <;> cases kr <;> simp
  · intro p q hp hq
    obtain ⟨tp, kp, hp1, hp2⟩ := hEU v p hvU hp
    obtain ⟨tq, kq, hq1, hq2⟩ := hEU v q hvU hq
    have hap : Pg.Adj v (X tp (!kp)) := by
      rw [hp2]
      exact hXP tp kp
    have haq : Pg.Adj v (X tq (!kq)) := by
      rw [hq2]
      exact hXP tq kq
    rw [hp1, hq1, hfin tp kp tq kq (hp2.symm.trans hq2) (hv _ _ hap haq)]
  · have hbr0 : ∀ (t0 : {t : V // t ∉ U ∧ c t = i}) (k0 : Bool),
        ¬ (fromEdgeSet ((E.erase s(t0.1, X t0 k0) : Finset (Sym2 V)) :
          Set (Sym2 V))).Reachable t0.1 (X t0 k0) := by
      intro t0 k0 hreach
      have hbP := (isAcyclic_iff_forall_adj_isBridge.mp hacyc) (hXP t0 k0)
      rw [isBridge_iff] at hbP
      apply hbP
      let ψ : V → V := fun z =>
        if h : z ∉ U ∧ c z = i then (if z = t0.1 then X t0 (!k0) else X ⟨z, h⟩ true) else z
      have hψT : ∀ t : {t : V // t ∉ U ∧ c t = i},
          ψ t.1 = if t.1 = t0.1 then X t0 (!k0) else X t true := fun t => dif_pos t.2
      have hψU : ∀ z, z ∈ U → ψ z = z := fun z hz => dif_neg (fun h => h.1 hz)
      have hkey : ∀ t k, (t, k) ≠ (t0, k0) →
          (ψ t.1 = ψ (X t k) ∨
            (Pg.deleteEdges {s(X t0 k0, X t0 (!k0))}).Adj (ψ t.1) (ψ (X t k))) := by
        intro t k hne
        rw [hψT t, hψU _ (hXU t k)]
        by_cases ht : t = t0
        · subst ht
          rw [if_pos rfl]
          left
          have hk : k = !k0 := hbool k0 k (fun h => hne (by rw [h]))
          rw [hk]
        · rw [if_neg (fun h => ht (Subtype.ext h))]
          cases k
          · right
            rw [deleteEdges_adj]
            refine ⟨hXP t true, ?_⟩
            intro hmem
            rw [Set.mem_singleton_iff] at hmem
            apply ht
            apply hinj
            show s((e t).1, (e t).2) = s((e t0).1, (e t0).2)
            rw [← hXs t0 k0]
            exact hmem
          · left
            rfl
      have hmap := p1_reach_map (H := Pg.deleteEdges {s(X t0 k0, X t0 (!k0))}) ψ ?_ hreach
      · rw [hψT t0, if_pos rfl, hψU _ (hXU t0 k0)] at hmap
        exact hmap.symm
      intro p q hpq
      rw [fromEdgeSet_adj] at hpq
      obtain ⟨hmem, _⟩ := hpq
      rw [Finset.mem_coe, Finset.mem_erase] at hmem
      obtain ⟨hne2, hin⟩ := hmem
      obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE p q hin
      · apply hkey t k
        intro h
        apply hne2
        rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]
      · have h3 := hkey t k (by
          intro h
          apply hne2
          rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2, Sym2.eq_swap])
        rcases h3 with h3 | h3
        · exact Or.inl h3.symm
        · exact Or.inr h3.symm
    intro x y hxy
    obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE x y hxy
    · exact hbr0 t k
    · intro h
      rw [Sym2.eq_swap] at h
      exact hbr0 t k h.symm

/-- The two one-sided linear forests and one edge of the maximum induced forest `U` form a linear
forest with `2 (n - f) + 1` edges, hence a path cover with `2 f - n - 1` paths, as soon as the
outside neighbourhoods of `U` are in the block class. -/
private lemma k2_bipartite_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 1 < Fintype.card V) (c : V → Fin 2)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w) (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hUcard : U.card = G.largestInducedForestSize) (x1 x2 : V)
    (hBLG : ∀ x ∈ U, x ≠ x1 → x ≠ x2 → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
        (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
        ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3)))
    (hx1 : x1 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
      G.Adj x1 t1 → G.Adj x1 t2 → G.Adj x1 t3 → G.Adj x1 t4 →
      t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (hx2 : x2 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
      G.Adj x2 t1 → G.Adj x2 t2 → G.Adj x2 t3 → G.Adj x2 t4 →
      t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (hcol : x1 = x2 ∨ c x1 ≠ c x2) :
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize := by
  classical
  have hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card := by
    intro W hW
    rw [hUcard]
    exact ncvr_card_le_largestInducedForestSize G W hW
  obtain ⟨a, haU, b, hbU, hab⟩ : ∃ a ∈ U, ∃ b ∈ U, G.Adj a b := by
    by_contra hno
    push Not at hno
    have := indep_add_one_le_forest G hconn hn U hno
    omega
  have hcab : c a ≠ c b := hc a b hab
  have hfin2 : ∀ x y z : Fin 2, y ≠ z → x = y ∨ x = z := by decide
  have hpig : ∀ z, c z = c a ∨ c z = c b := fun z => hfin2 (c z) (c a) (c b) hcab
  have hfin2' : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide
  have hside : ∀ i : Fin 2, ∃ x0 : V, (∀ x ∈ U, x ≠ x0 → c x ≠ i → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
          ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3))) ∧
      (x0 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x0 t1 → G.Adj x0 t2 → G.Adj x0 t3 → G.Adj x0 t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4) := by
    intro i
    by_cases h1i : c x1 ≠ i
    · refine ⟨x1, fun x hx hx0 hxi => hBLG x hx hx0 ?_, hx1⟩
      rintro rfl
      rcases hcol with h | h
      · exact hx0 h.symm
      · exact h (hfin2' _ _ _ h1i hxi)
    · push Not at h1i
      refine ⟨x2, fun x hx hx0 hxi => hBLG x hx ?_ hx0, hx2⟩
      rintro rfl
      exact hxi h1i
  obtain ⟨y0, hy0, hy0d⟩ := hside (c b)
  obtain ⟨y1, hy1, hy1d⟩ := hside (c a)
  obtain ⟨E0, h0form, h0card, h0deg, h0v, h0br⟩ := p1_side G c hc U hU hmax (c b) y0 hy0 hy0d a haU
  obtain ⟨E1, h1form, h1card, h1deg, h1v, h1br⟩ := p1_side G c hc U hU hmax (c a) y1 hy1 hy1d b hbU
  obtain ⟨s0, hs0⟩ : ∃ s0 : V → Prop, s0 = fun z => (z ∈ U ↔ c z = c a) := ⟨_, rfl⟩
  have hs0a : s0 a := by
    rw [hs0]
    exact ⟨fun _ => rfl, fun _ => haU⟩
  have hs0b : ¬ s0 b := by
    rw [hs0]
    intro h
    exact hcab (h.mp hbU).symm
  have h0side : ∀ p q, s(p, q) ∈ E0 → s0 p ∧ s0 q := by
    have key : ∀ p q, G.Adj p q → p ∉ U → c p = c b → q ∈ U → s0 p ∧ s0 q := by
      intro p q hadj hp hcp hq
      rw [hs0]
      refine ⟨⟨fun h => (hp h).elim, fun h => (hcab (h.symm.trans hcp)).elim⟩,
        ⟨fun _ => ?_, fun _ => hq⟩⟩
      rcases hpig q with h | h
      · exact h
      · exact (hc p q hadj (hcp.trans h.symm)).elim
    intro p q h
    obtain ⟨hadj, ⟨hp, hcp, hq⟩ | ⟨hq, hcq, hp⟩⟩ := h0form p q h
    · exact key p q hadj hp hcp hq
    · exact (key q p hadj.symm hq hcq hp).symm
  have h1side : ∀ p q, s(p, q) ∈ E1 → ¬ s0 p ∧ ¬ s0 q := by
    have key : ∀ p q, G.Adj p q → p ∉ U → c p = c a → q ∈ U → ¬ s0 p ∧ ¬ s0 q := by
      intro p q hadj hp hcp hq
      rw [hs0]
      refine ⟨fun h => hp (h.mpr hcp), fun h => ?_⟩
      exact hc p q hadj (hcp.trans (h.mp hq).symm)
    intro p q h
    obtain ⟨hadj, ⟨hp, hcp, hq⟩ | ⟨hq, hcq, hp⟩⟩ := h1form p q h
    · exact key p q hadj hp hcp hq
    · exact (key q p hadj.symm hq hcq hp).symm
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 V), E = insert s(a, b) (E0 ∪ E1) := ⟨_, rfl⟩
  have hEcases : ∀ p q, s(p, q) ∈ E → s(p, q) = s(a, b) ∨ s(p, q) ∈ E0 ∨ s(p, q) ∈ E1 := by
    intro p q h
    rw [hEdef, Finset.mem_insert, Finset.mem_union] at h
    exact h
  have hab_cases : ∀ p q, s(p, q) = s(a, b) → (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
    intro p q h
    exact Sym2.eq_iff.mp h
  have hEadj : ∀ p q, s(p, q) ∈ E → G.Adj p q := by
    intro p q h
    rcases hEcases p q h with h | h | h
    · rcases hab_cases p q h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    · exact (h0form p q h).1
    · exact (h1form p q h).1
  have hnab : s(a, b) ∉ E0 ∪ E1 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hs0b (h0side a b h).2
    · exact (h1side a b h).1 hs0a
  have hdisj01 : Disjoint E0 E1 := by
    rw [Finset.disjoint_left]
    intro z
    induction z using Sym2.ind with
    | _ p q =>
      intro h0 h1
      exact (h1side p q h1).1 (h0side p q h0).1
  have hEcard : E.card = 1 + E0.card + E1.card := by
    rw [hEdef, Finset.card_insert_of_notMem hnab, Finset.card_union_of_disjoint hdisj01]
    omega
  have hcount : (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = c b)).card +
      (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = c a)).card = Fintype.card V - U.card := by
    rw [← Finset.card_compl, ← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_compl]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        rcases hpig z with h' | h'
        · exact Or.inr ⟨h, h'⟩
        · exact Or.inl ⟨h, h'⟩
    · rw [Finset.disjoint_left]
      intro z h1 h2
      exact hcab ((Finset.mem_filter.mp h2).2.2.symm.trans (Finset.mem_filter.mp h1).2.2)
  have hdegE : ∀ x p q r, s(x, p) ∈ E → s(x, q) ∈ E → s(x, r) ∈ E → p = q ∨ p = r ∨ q = r := by
    have hgen : ∀ (E' : Finset (Sym2 V)) (x : V),
        (∀ p q r, s(x, p) ∈ E' → s(x, q) ∈ E' → s(x, r) ∈ E' → p = q ∨ p = r ∨ q = r) →
        (∀ p, s(x, p) = s(a, b) → ∀ q r, s(x, q) ∈ E' → s(x, r) ∈ E' → q = r) →
        ∀ p q r, (s(x, p) = s(a, b) ∨ s(x, p) ∈ E') → (s(x, q) = s(a, b) ∨ s(x, q) ∈ E') →
          (s(x, r) = s(a, b) ∨ s(x, r) ∈ E') → p = q ∨ p = r ∨ q = r := by
      intro E' x hd hv' p q r hp hq hr
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr
      · exact Or.inl (Sym2.congr_right.mp (hp.trans hq.symm))
      · exact Or.inl (Sym2.congr_right.mp (hp.trans hq.symm))
      · exact Or.inr (Or.inl (Sym2.congr_right.mp (hp.trans hr.symm)))
      · exact Or.inr (Or.inr (hv' p hp q r hq hr))
      · exact Or.inr (Or.inr (Sym2.congr_right.mp (hq.trans hr.symm)))
      · exact Or.inr (Or.inl (hv' q hq p r hp hr))
      · exact Or.inl (hv' r hr p q hp hq)
      · exact hd p q r hp hq hr
    intro x p q r hp hq hr
    by_cases hx : s0 x
    · have hconv : ∀ p, s(x, p) ∈ E → s(x, p) = s(a, b) ∨ s(x, p) ∈ E0 := by
        intro p h
        rcases hEcases x p h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact ((h1side x p h).1 hx).elim
      refine hgen E0 x (h0deg x) ?_ p q r (hconv p hp) (hconv q hq) (hconv r hr)
      intro p' hp' q' r' hq' hr'
      have hxa : x = a := by
        rcases hab_cases x p' hp' with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact (hs0b (h ▸ hx)).elim
      rw [hxa] at hq' hr'
      exact h0v q' r' hq' hr'
    · have hconv : ∀ p, s(x, p) ∈ E → s(x, p) = s(a, b) ∨ s(x, p) ∈ E1 := by
        intro p h
        rcases hEcases x p h with h | h | h
        · exact Or.inl h
        · exact (hx (h0side x p h).1).elim
        · exact Or.inr h
      refine hgen E1 x (h1deg x) ?_ p q r (hconv p hp) (hconv q hq) (hconv r hr)
      intro p' hp' q' r' hq' hr'
      have hxb : x = b := by
        rcases hab_cases x p' hp' with ⟨h, _⟩ | ⟨h, _⟩
        · exact (hx (h ▸ hs0a)).elim
        · exact h
      rw [hxb] at hq' hr'
      exact h1v q' r' hq' hr'
  have hbrE : ∀ x y, s(x, y) ∈ E →
      ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y := by
    intro x y hxy hreach
    have hedge : ∀ p q, (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) :
        Set (Sym2 V))).Adj p q →
        s(p, q) ≠ s(x, y) ∧ p ≠ q ∧ (s(p, q) = s(a, b) ∨ s(p, q) ∈ E0 ∨ s(p, q) ∈ E1) := by
      intro p q hpq
      rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase] at hpq
      exact ⟨hpq.1.1, hpq.2, hEcases p q hpq.1.2⟩
    rcases hEcases x y hxy with h | h | h
    · have hmap := p1_reach_map (H := (⊥ : SimpleGraph Prop)) s0 ?_ hreach
      · rw [reachable_bot] at hmap
        rcases hab_cases x y h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hs0b (hmap ▸ hs0a)
        · exact hs0b (hmap.symm ▸ hs0a)
      intro p q hpq
      left
      obtain ⟨hne, _, h' | h' | h'⟩ := hedge p q hpq
      · exact (hne (h'.trans h.symm)).elim
      · exact propext ⟨fun _ => (h0side p q h').2, fun _ => (h0side p q h').1⟩
      · exact propext ⟨fun hp => ((h1side p q h').1 hp).elim, fun hq => ((h1side p q h').2 hq).elim⟩
    · apply h0br x y h
      have hmap := p1_reach_map
        (H := fromEdgeSet ((E0.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V)))
        (fun z => if s0 z then z else a) ?_ hreach
      · simp only [if_pos (h0side x y h).1, if_pos (h0side x y h).2] at hmap
        exact hmap
      intro p q hpq
      obtain ⟨hne, hpq', h' | h' | h'⟩ := hedge p q hpq
      · left
        rcases hab_cases p q h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [if_pos hs0a, if_neg hs0b]
        · simp only [if_pos hs0a, if_neg hs0b]
      · right
        simp only [if_pos (h0side p q h').1, if_pos (h0side p q h').2]
        rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase]
        exact ⟨⟨hne, h'⟩, hpq'⟩
      · left
        simp only [if_neg (h1side p q h').1, if_neg (h1side p q h').2]
    · apply h1br x y h
      have hmap := p1_reach_map
        (H := fromEdgeSet ((E1.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V)))
        (fun z => if s0 z then b else z) ?_ hreach
      · simp only [if_neg (h1side x y h).1, if_neg (h1side x y h).2] at hmap
        exact hmap
      intro p q hpq
      obtain ⟨hne, hpq', h' | h' | h'⟩ := hedge p q hpq
      · left
        rcases hab_cases p q h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [if_pos hs0a, if_neg hs0b]
        · simp only [if_pos hs0a, if_neg hs0b]
      · left
        simp only [if_pos (h0side p q h').1, if_pos (h0side p q h').2]
      · right
        simp only [if_neg (h1side p q h').1, if_neg (h1side p q h').2]
        rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase]
        exact ⟨⟨hne, h'⟩, hpq'⟩
  obtain ⟨P, hP, hPcard⟩ := p1_linear_forest_cover E
    (fun x y h => (hEadj x y h).ne) hdegE hbrE
  have hle : fromEdgeSet (E : Set (Sym2 V)) ≤ G := by
    intro p q h
    rw [fromEdgeSet_adj] at h
    exact hEadj p q (Finset.mem_coe.mp h.1)
  have hpc : G.pathCoverNumber ≤ P.card := by
    unfold SimpleGraph.pathCoverNumber
    exact Nat.sInf_le ⟨P, rfl, r2_isPathCover_mono hle hP⟩
  have hUle : U.card ≤ Fintype.card V := Finset.card_le_univ U
  omega


private lemma out3_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (x : V) : Set.ncard {t | t ∉ U ∧ G.Adj x t} ≤ 3 ↔
      ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → G.Adj x t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4 := by
  classical
  have hS : {t | t ∉ U ∧ G.Adj x t} = ↑(Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t)) := by
    ext t
    simp
  rw [hS, Set.ncard_coe_finset]
  constructor
  · intro h t1 t2 t3 t4 n1 n2 n3 n4 a1 a2 a3 a4
    by_contra hc
    push Not at hc
    obtain ⟨h12, h13, h14, h23, h24, h34⟩ := hc
    have hsub : ({t1, t2, t3, t4} : Finset V) ⊆ Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> simp [*]
    have h4 : ({t1, t2, t3, t4} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h34]
      · simp [h23, h24]
      · simp [h12, h13, h14]
    have := Finset.card_le_card hsub
    omega
  · intro h
    by_contra hbig
    push Not at hbig
    obtain ⟨s0, hs0⟩ : (Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t)).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hlt : 2 < ((Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t)).erase s0).card := by
      rw [Finset.card_erase_of_mem hs0]; omega
    obtain ⟨s1, hs1, s2, hs2, s3, hs3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
    have m : ∀ s ∈ Finset.univ.filter (fun t => t ∉ U ∧ G.Adj x t), s ∉ U ∧ G.Adj x s :=
      fun s hs => (Finset.mem_filter.mp hs).2
    have f0 := m s0 hs0
    have f1 := m s1 (Finset.mem_of_mem_erase hs1)
    have f2 := m s2 (Finset.mem_of_mem_erase hs2)
    have f3 := m s3 (Finset.mem_of_mem_erase hs3)
    rcases h s0 s1 s2 s3 f0.1 f1.1 f2.1 f3.1 f0.2 f1.2 f2.2 f3.2 with e | e | e | e | e | e
    · exact Finset.ne_of_mem_erase hs1 e.symm
    · exact Finset.ne_of_mem_erase hs2 e.symm
    · exact Finset.ne_of_mem_erase hs3 e.symm
    · exact h12 e
    · exact h13 e
    · exact h23 e

/-- Corollary BLXG: `p + n + 1 ≤ 2 f` for every connected bipartite graph on at least two vertices
having a maximum induced forest `U` and two vertices `x1`, `x2` of `U`, equal or of different
colours, with at most three outside neighbours each, such that every other vertex of `U` satisfies
the block condition. -/
private lemma k2_forest_classX {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 1 < Fintype.card V) (hbip : G.IsBipartite)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hUc : U.card = G.largestInducedForestSize) (x1 x2 : V)
    (hBLG : ∀ x ∈ U, x ≠ x1 → x ≠ x2 → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
        (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
        ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3)))
    (hx1 : x1 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x1 t1 → G.Adj x1 t2 → G.Adj x1 t3 → G.Adj x1 t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (hx2 : x2 ∈ U → ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x2 t1 → G.Adj x2 t2 → G.Adj x2 t3 → G.Adj x2 t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4)
    (hcol : ∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → x1 = x2 ∨ c x1 ≠ c x2) :
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize := by
  classical
  obtain ⟨col⟩ := hbip
  exact k2_bipartite_core G hconn hn (fun z => col z) (fun u w h => col.valid h) U hU hUc x1 x2
    hBLG hx1 hx2 (hcol (fun z => col z) (fun u w h => col.valid h))

end

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2.H1 := by
  intro h1 h2 V _ _ G hn hconn h2c hbip hscat _ hB
  classical
  by_cases hE : ∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧
      U.card = G.largestInducedForestSize ∧ ∃ x1 x2 : V,
      (∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → x1 = x2 ∨ c x1 ≠ c x2) ∧
      (x1 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x1 t} ≤ 3) ∧
      (x2 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x2 t} ≤ 3) ∧
      ∀ x ∈ U, x ≠ x1 → x ≠ x2 → ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
          G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
            (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
            ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3))
  · obtain ⟨U, hU, hUc, x1, x2, hcol, hx1, hx2, hBLG⟩ := hE
    exact k2_forest_classX G hconn (by omega) hbip U hU hUc x1 x2 hBLG
      (fun h => (out3_iff G U x1).mp (hx1 h)) (fun h => (out3_iff G U x2).mp (hx2 h)) hcol
  have hres : ∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic →
      U.card = G.largestInducedForestSize →
      ∀ x1 x2 : V, (∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → x1 = x2 ∨ c x1 ≠ c x2) →
      (x1 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x1 t} ≤ 3) →
      (x2 ∈ U → Set.ncard {t | t ∉ U ∧ G.Adj x2 t} ≤ 3) →
      ∃ x ∈ U, x ≠ x1 ∧ x ≠ x2 ∧ ∃ t1 t2 t3 : V, t1 ∉ U ∧ t2 ∉ U ∧ t3 ∉ U ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
        G.Adj x t1 ∧ G.Adj x t2 ∧ G.Adj x t3 ∧ ∀ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) →
          (p t1 ↔ p t2) ∧ (p t1 ↔ p t3) := by
    intro U hU hUc x1 x2 hcol hx1 hx2
    by_contra hno
    apply hE
    refine ⟨U, hU, hUc, x1, x2, hcol, hx1, hx2, ?_⟩
    intro x hx hn1 hn2 t1 t2 t3 n1 n2 n3 d12 d13 d23 a1 a2 a3
    by_contra hp
    apply hno
    refine ⟨x, hx, hn1, hn2, t1, t2, t3, n1, n2, n3, d12, d13, d23, a1, a2, a3, ?_⟩
    intro p hsep
    by_contra hsame
    exact hp ⟨p, hsep, hsame⟩
  by_cases hS : ∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧
      U.card = G.largestInducedForestSize ∧
      (∀ x ∈ U, Set.ncard {t | t ∉ U ∧ G.Adj x t} ≤ 3) ∧
      ∀ c : V → Fin 2, (∀ u w, G.Adj u w → c u ≠ c w) → ∀ i : Fin 2,
        Set.ncard {y | y ∈ U ∧ c y = i ∧ ∃ t1 t2 t3 : V, t1 ∉ U ∧ t2 ∉ U ∧ t3 ∉ U ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
          G.Adj y t1 ∧ G.Adj y t2 ∧ G.Adj y t3 ∧ ∀ p : V → Prop,
            (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = y) →
            (p t1 ↔ p t2) ∧ (p t1 ↔ p t3)} ≤ 2
  · exact h1 V G hn hconn h2c hbip hscat hres hS
  · obtain ⟨U0, hU0, hU0c, hD0⟩ := hB
    apply h2 V G hn hconn h2c hbip hscat hres
      ⟨U0, hU0, hU0c, fun x hx => (out3_iff G U0 x).mpr (hD0 x hx)⟩
    intro U hU hUc hD
    by_contra hno
    apply hS
    refine ⟨U, hU, hUc, hD, fun c hc i => ?_⟩
    by_contra hlt
    exact hno ⟨c, hc, i, by omega⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2_H1_R1
