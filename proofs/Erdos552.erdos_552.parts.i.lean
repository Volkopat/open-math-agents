import FormalConjectures.ErdosProblems.«552»
import Mathlib

/-!
# Erdős Problem 552, part i: the value of `R(C₄, K_{1,n})`

`OMA.answer n` is the least `N ≤ 2n+2` such that every graph on `N` labelled vertices,
given by its edge set `E ⊆ {(i,j) : i < j}`, either contains a 4-cycle `x u y v` or has a
vertex with at least `n` non-neighbours. A finite search over explicit edge sets.

Proof:
* `C₄ ⊑ C` iff `C` has distinct `x ≠ y`, `u ≠ v` with `x ~ u ~ y ~ v ~ x`;
  `K_{1,n} ⊑ Cᶜ` iff some vertex has `n` non-neighbours.
* Graphs on `Fin N` correspond to edge sets `E ⊆ {(i,j) : i < j}`.
* Every graph on `2n+2` vertices qualifies: if all vertices have fewer than `n` non-neighbours,
  vertices `0` and `1` have at least `n+2` neighbours each, hence two common neighbours.
* So the search hits the least qualifying `N`, which is the `sInf` defining `graphRamsey`.
-/

namespace OMA.E552

open Finset SimpleGraph

/-- Adjacency read off an edge set of ordered pairs. -/
def adjE {N : ℕ} (E : Finset (Fin N × Fin N)) (i j : Fin N) : Prop := (i, j) ∈ E ∨ (j, i) ∈ E

instance {N : ℕ} (E : Finset (Fin N × Fin N)) : DecidableRel (adjE E) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The candidate edge sets on `Fin N`. -/
def pairs (N : ℕ) : Finset (Fin N × Fin N) := univ.filter (fun p => p.1 < p.2)

/-- `E` contains a 4-cycle or a vertex with at least `n` non-neighbours. -/
def okE (n N : ℕ) (E : Finset (Fin N × Fin N)) : Prop :=
  (∃ x u y v : Fin N, x ≠ y ∧ u ≠ v ∧ adjE E x u ∧ adjE E u y ∧ adjE E y v ∧ adjE E v x) ∨
    ∃ v : Fin N, n ≤ (univ.filter fun w => w ≠ v ∧ ¬ adjE E v w).card

instance (n N : ℕ) (E : Finset (Fin N × Fin N)) : Decidable (okE n N E) := by
  unfold okE; infer_instance

/-- Every graph on `Fin N` qualifies. -/
def good (n N : ℕ) : Prop := ∀ E ∈ (pairs N).powerset, okE n N E

instance (n N : ℕ) : Decidable (good n N) := by unfold good; infer_instance

/-- First qualifying `N` in `k, k+1, …, k+f` (or `k+f` if none). -/
def search (n : ℕ) : ℕ → ℕ → ℕ
  | k, 0 => k
  | k, f + 1 => if good n k then k else search n (k + 1) f

end OMA.E552

/-- The value `R(C₄, K_{1,n})`, by explicit search. -/
def OMA.answer (n : ℕ) : ℕ := OMA.E552.search n 0 (2 * n + 2)

namespace OMA.E552

open Finset SimpleGraph

lemma search_spec (n : ℕ) : ∀ f k : ℕ,
    (∀ N, k ≤ N → N < search n k f → ¬ good n N) ∧
      (good n (k + f) → good n (search n k f)) := by
  intro f
  induction f with
  | zero =>
    intro k
    refine ⟨fun N h1 h2 => ?_, fun h => ?_⟩
    · simp [search] at h2; omega
    · simpa [search] using h
  | succ f ih =>
    intro k
    by_cases hk : good n k
    · rw [search, if_pos hk]
      exact ⟨fun N h1 h2 => by omega, fun _ => hk⟩
    · rw [search, if_neg hk]
      obtain ⟨h1, h2⟩ := ih (k + 1)
      refine ⟨fun N hN hlt => ?_, fun h => h2 (by rwa [show k + 1 + f = k + (f + 1) by ring])⟩
      rcases Nat.eq_or_lt_of_le hN with rfl | hN'
      · exact hk
      · exact h1 N hN' hlt

/-! ## Containment in elementary terms -/

lemma c4_iff {N : ℕ} (C : SimpleGraph (Fin N)) :
    (cycleGraph 4).IsContained C ↔
      ∃ x u y v : Fin N, x ≠ y ∧ u ≠ v ∧ C.Adj x u ∧ C.Adj u y ∧ C.Adj y v ∧ C.Adj v x := by
  constructor
  · rintro ⟨f⟩
    have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → C.Adj (f i) (f j) :=
      fun i j h => f.toHom.map_adj h
    have hinj : Function.Injective f := f.injective
    refine ⟨f 0, f 1, f 2, f 3, fun h => by simpa using hinj h, fun h => by simpa using hinj h,
      hadj 0 1 (by decide), hadj 1 2 (by decide), hadj 2 3 (by decide), hadj 3 0 (by decide)⟩
  · rintro ⟨x, u, y, v, hxy, huv, h1, h2, h3, h4⟩
    let g : Fin 4 → Fin N := ![x, u, y, v]
    have hxu := C.ne_of_adj h1
    have huy := C.ne_of_adj h2
    have hyv := C.ne_of_adj h3
    have hvx := C.ne_of_adj h4
    have hinj : Function.Injective g := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [g, eq_comm]
    have hhom : ∀ {i j : Fin 4}, (cycleGraph 4).Adj i j → C.Adj (g i) (g j) := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd h (by decide)
        | (simp only [g, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
           first
           | exact h1 | exact h2 | exact h3 | exact h4
           | exact h1.symm | exact h2.symm | exact h3.symm | exact h4.symm)
    exact ⟨⟨⟨g, hhom⟩, hinj⟩⟩

lemma star_iff {N n : ℕ} (C : SimpleGraph (Fin N)) [DecidableRel C.Adj] :
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Cᶜ ↔
      ∃ v : Fin N, n ≤ (univ.filter fun w => w ≠ v ∧ ¬ C.Adj v w).card := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f (Sum.inl 0), ?_⟩
    let g : Fin n → Fin N := fun i => f (Sum.inr i)
    have hg : Function.Injective g := fun i j h => by
      simpa using f.injective h
    have hsub : univ.image g ⊆ univ.filter fun w => w ≠ f (Sum.inl 0) ∧ ¬ C.Adj (f (Sum.inl 0)) w := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := mem_image.mp hw
      have hadj : Cᶜ.Adj (f (Sum.inl 0)) (g i) :=
        f.toHom.map_adj (by simp [completeBipartiteGraph])
      rw [compl_adj] at hadj
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨hadj.1.symm, hadj.2⟩
    have := card_le_card hsub
    rwa [card_image_of_injective _ hg, card_univ, Fintype.card_fin] at this
  · rintro ⟨v, hv⟩
    obtain ⟨T, hT, hcard⟩ := exists_subset_card_eq hv
    let e := T.equivFin
    let g : Fin 1 ⊕ Fin n → Fin N := fun s => match s with
      | Sum.inl _ => v
      | Sum.inr i => (e.symm (Fin.cast hcard.symm i)).1
    have hmem : ∀ i : Fin n, (e.symm (Fin.cast hcard.symm i)).1 ∈
        univ.filter fun w => w ≠ v ∧ ¬ C.Adj v w := fun i => hT (e.symm _).2
    have hinj : Function.Injective g := by
      rintro (a | a) (b | b) h
      · simp [Subsingleton.elim a b]
      · have := (mem_filter.mp (hmem b)).2.1
        exact absurd h.symm this
      · have := (mem_filter.mp (hmem a)).2.1
        exact absurd h this
      · have h' : e.symm (Fin.cast hcard.symm a) = e.symm (Fin.cast hcard.symm b) := Subtype.ext h
        have := e.symm.injective h'
        simp [Fin.cast_inj] at this
        rw [this]
    have hhom : ∀ {a b : Fin 1 ⊕ Fin n}, (completeBipartiteGraph (Fin 1) (Fin n)).Adj a b →
        Cᶜ.Adj (g a) (g b) := by
      rintro (a | a) (b | b) h
      · simp [completeBipartiteGraph] at h
      · have := (mem_filter.mp (hmem b)).2
        rw [compl_adj]
        exact ⟨fun h' => this.1 h'.symm, this.2⟩
      · have := (mem_filter.mp (hmem a)).2
        rw [compl_adj]
        exact ⟨this.1, fun h' => this.2 h'.symm⟩
      · simp [completeBipartiteGraph] at h
    exact ⟨⟨⟨g, hhom⟩, hinj⟩⟩

/-! ## Graphs versus edge sets -/

lemma adjE_ne {N : ℕ} {E : Finset (Fin N × Fin N)} (hE : E ⊆ pairs N) {i j : Fin N}
    (h : adjE E i j) : i ≠ j := by
  rcases h with h | h
  · have := (mem_filter.mp (hE h)).2; exact ne_of_lt this
  · have := (mem_filter.mp (hE h)).2; exact (ne_of_lt this).symm

/-- The set whose infimum is `graphRamsey`. -/
def S (n : ℕ) : Set ℕ := { N : ℕ | ∀ (C : SimpleGraph (Fin N)),
  (cycleGraph 4).IsContained C ∨ (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Cᶜ }

lemma mem_S_iff (n N : ℕ) : N ∈ S n ↔ good n N := by
  classical
  constructor
  · intro hS E hE
    rw [mem_powerset] at hE
    let C : SimpleGraph (Fin N) := SimpleGraph.fromRel (adjE E)
    have hC : ∀ i j, C.Adj i j ↔ adjE E i j := by
      intro i j
      simp only [C, fromRel_adj]
      constructor
      · rintro ⟨_, h | h⟩
        · exact h
        · rcases h with h | h
          · exact Or.inr h
          · exact Or.inl h
      · intro h; exact ⟨adjE_ne hE h, Or.inl h⟩
    rcases hS C with h | h
    · left
      obtain ⟨x, u, y, v, h0, h1, h2, h3, h4, h5⟩ := (c4_iff C).mp h
      exact ⟨x, u, y, v, h0, h1, (hC _ _).mp h2, (hC _ _).mp h3, (hC _ _).mp h4, (hC _ _).mp h5⟩
    · right
      obtain ⟨v, hv⟩ := (star_iff C).mp h
      refine ⟨v, le_trans hv (le_of_eq ?_)⟩
      congr 1
      ext w
      simp [hC]
  · intro hg C
    let E : Finset (Fin N × Fin N) := (pairs N).filter (fun p => C.Adj p.1 p.2)
    have hE : E ∈ (pairs N).powerset := mem_powerset.mpr (filter_subset _ _)
    have hC : ∀ i j, adjE E i j ↔ C.Adj i j := by
      intro i j
      simp only [adjE, E, pairs, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact h
        · exact h.symm
      · intro h
        rcases lt_or_gt_of_ne (C.ne_of_adj h) with hl | hl
        · exact Or.inl ⟨hl, h⟩
        · exact Or.inr ⟨hl, h.symm⟩
    rcases hg E hE with h | h
    · left
      obtain ⟨x, u, y, v, h0, h1, h2, h3, h4, h5⟩ := h
      exact (c4_iff C).mpr ⟨x, u, y, v, h0, h1, (hC _ _).mp h2, (hC _ _).mp h3,
        (hC _ _).mp h4, (hC _ _).mp h5⟩
    · right
      obtain ⟨v, hv⟩ := h
      refine (star_iff C).mpr ⟨v, le_trans hv (le_of_eq ?_)⟩
      congr 1
      ext w
      simp [hC]

/-! ## The upper bound `2n+2` -/

lemma nbr_card {N : ℕ} (C : SimpleGraph (Fin N)) [DecidableRel C.Adj] (v : Fin N) :
    (univ.filter (C.Adj v)).card + (univ.filter fun w => w ≠ v ∧ ¬ C.Adj v w).card + 1 = N := by
  have h1 : univ.filter (C.Adj v) = (univ.erase v).filter (C.Adj v) := by
    ext w; simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact ⟨fun h => ⟨(C.ne_of_adj h).symm, h⟩, fun h => h.2⟩
  have h2 : (univ.filter fun w => w ≠ v ∧ ¬ C.Adj v w) = (univ.erase v).filter (fun w => ¬ C.Adj v w) := by
    ext w; simp [mem_erase]
  rw [h1, h2, card_filter_add_card_filter_not, card_erase_of_mem (mem_univ v), card_univ,
    Fintype.card_fin]
  have : 0 < N := Fin.pos v
  omega

lemma good_bound (n : ℕ) : good n (2 * n + 2) := by
  classical
  rw [← mem_S_iff]
  intro C
  by_cases h : ∃ v : Fin (2 * n + 2), n ≤ (univ.filter fun w => w ≠ v ∧ ¬ C.Adj v w).card
  · exact Or.inr ((star_iff C).mpr h)
  · push Not at h
    left
    let x : Fin (2 * n + 2) := ⟨0, by omega⟩
    let y : Fin (2 * n + 2) := ⟨1, by omega⟩
    have hxy : x ≠ y := by simp [x, y]
    have dx := nbr_card C x
    have dy := nbr_card C y
    have hx := h x
    have hy := h y
    have hunion := card_union_add_card_inter (univ.filter (C.Adj x)) (univ.filter (C.Adj y))
    have hle : (univ.filter (C.Adj x) ∪ univ.filter (C.Adj y)).card ≤ 2 * n + 2 := by
      simpa using card_le_univ (univ.filter (C.Adj x) ∪ univ.filter (C.Adj y))
    have hint : 1 < (univ.filter (C.Adj x) ∩ univ.filter (C.Adj y)).card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hint
    simp only [mem_inter, mem_filter, mem_univ, true_and] at hu hv
    exact (c4_iff C).mpr ⟨x, u, y, v, hxy, huv, hu.1, hu.2.symm, hv.2, hv.1.symm⟩

end OMA.E552

theorem OMA.solution : Erdos552.erdos_552.parts.i.answer = OMA.answer →
    type_of% @Erdos552.erdos_552.parts.i := by
  intro hans n
  rw [hans]
  show sInf (OMA.E552.S n) = OMA.answer n
  obtain ⟨h1, h2⟩ := OMA.E552.search_spec n (2 * n + 2) 0
  have hgood : OMA.E552.good n (OMA.answer n) := h2 (by simpa using OMA.E552.good_bound n)
  have hmem : OMA.answer n ∈ OMA.E552.S n := (OMA.E552.mem_S_iff n _).mpr hgood
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  intro N hN
  by_contra hlt
  push Not at hlt
  exact h1 N (Nat.zero_le _) hlt ((OMA.E552.mem_S_iff n N).mp hN)
