import OMAStatements.S_mo_461267
import Mathlib

/-
Counterexample family (after the answer posted on MathOverflow). For every k take four
independent layers A, B, C, D with |A| = |D| = k + 1 and |B| = |C| = k, and join all of A to B,
all of B to C and all of C to D. A vertex is a pair (s, t): the side s is false for A and B and
true for C and D, and t is inl i for the big layer (A or D) and inr j for the small one (B or C).
The graph is k-connected, a path through all of A and B is vmax, a path through all of C and D
is vmax, and these two paths are disjoint.
-/

namespace OMA.P461267

open OMA.S_mo_461267

abbrev Vtx (k : ℕ) : Type := Bool × (Fin (k + 1) ⊕ Fin k)

def rel (k : ℕ) (x y : Vtx k) : Prop :=
  (x.1 = y.1 ∧ x.2.isLeft = true ∧ y.2.isRight = true) ∨
    (x.1 ≠ y.1 ∧ x.2.isRight = true ∧ y.2.isRight = true)

def gr (k : ℕ) : SimpleGraph (Vtx k) := SimpleGraph.fromRel (rel k)

lemma adj_lr (k : ℕ) (s : Bool) (i : Fin (k + 1)) (j : Fin k) :
    (gr k).Adj (s, Sum.inl i) (s, Sum.inr j) := by
  rw [gr, SimpleGraph.fromRel_adj]
  refine ⟨by simp, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩

lemma adj_rr (k : ℕ) (s s' : Bool) (h : s ≠ s') (j j' : Fin k) :
    (gr k).Adj (s, Sum.inr j) (s', Sum.inr j') := by
  rw [gr, SimpleGraph.fromRel_adj]
  refine ⟨by simp [h], Or.inl (Or.inr ⟨h, rfl, rfl⟩)⟩

/- the neighbours of a big-layer vertex lie in the small layer of the same side -/
lemma adj_left (k : ℕ) (x y : Vtx k) (h : (gr k).Adj x y) (hx : x.2.isLeft = true) :
    y.1 = x.1 ∧ y.2.isRight = true := by
  rw [gr, SimpleGraph.fromRel_adj] at h
  obtain ⟨s, i | j⟩ := x
  · obtain ⟨s', i' | j'⟩ := y
    · simp [rel] at h
    · simp only [rel, Sum.isLeft_inl, Sum.isRight_inr, Sum.isRight_inl, Sum.isLeft_inr] at h
      obtain ⟨-, h⟩ := h
      rcases h with (⟨h1, -⟩ | ⟨-, h2, -⟩) | (⟨h1, h2, -⟩ | ⟨-, -, h2⟩)
      · exact ⟨h1.symm, rfl⟩
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
  · simp at hx

/- Counting along a chain: if every neighbour of a `P0` element is a `P1` element, then a chain
that contains an element outside `P0` and `P1` has at most as many `P0` as `P1` elements. -/
lemma count_aux {V : Type} (R : V → V → Prop) (P0 P1 : V → Bool)
    (h01 : ∀ x, P0 x = true → P1 x = false)
    (hadj : ∀ x y, R x y → P0 x = true → P1 y = true)
    (hadj' : ∀ x y, R x y → P0 y = true → P1 x = true) :
    ∀ (l : List V) (x : V), List.IsChain R (x :: l) →
      (P0 x = true → (x :: l).countP P0 ≤ (x :: l).countP P1 + 1 ∧
        ((∃ z ∈ x :: l, P0 z = false ∧ P1 z = false) →
          (x :: l).countP P0 ≤ (x :: l).countP P1)) ∧
      (P0 x = false → (x :: l).countP P0 ≤ (x :: l).countP P1 ∧
        (P1 x = true → (∃ z ∈ x :: l, P0 z = false ∧ P1 z = false) →
          (x :: l).countP P0 + 1 ≤ (x :: l).countP P1)) := by
  intro l
  induction l with
  | nil =>
    intro x _
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have h1 := h01 x hx
      refine ⟨by simp [hx, h1], ?_⟩
      rintro ⟨z, hz, hz0, -⟩
      simp only [List.mem_singleton] at hz
      subst hz
      rw [hx] at hz0
      exact absurd hz0 (by simp)
    · refine ⟨by simp [List.countP_cons, hx], fun h1 _ => by simp [hx, h1]⟩
  | cons y t ih =>
    intro x hc
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hxy, hc'⟩ := hc
    obtain ⟨ih0, ih1⟩ := ih y hc'
    have e0 : (x :: y :: t).countP P0 = (y :: t).countP P0 + if P0 x = true then 1 else 0 :=
      List.countP_cons
    have e1 : (x :: y :: t).countP P1 = (y :: t).countP P1 + if P1 x = true then 1 else 0 :=
      List.countP_cons
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have h1 := h01 x hx
      have hy1 := hadj x y hxy hx
      have hy0 : P0 y = false := by
        by_contra hne
        have := h01 y (by simpa using hne)
        rw [hy1] at this
        exact absurd this (by simp)
      obtain ⟨ihA, ihB⟩ := ih1 hy0
      rw [e0, e1, hx, h1]
      simp only [if_true, Bool.false_eq_true, if_false, add_zero]
      refine ⟨by omega, ?_⟩
      rintro ⟨z, hz, hz0, hz1⟩
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · rw [hx] at hz0
        exact absurd hz0 (by simp)
      · have := ihB hy1 ⟨z, hz, hz0, hz1⟩
        omega
    · rw [e0, e1, hx]
      simp only [Bool.false_eq_true, if_false, add_zero]
      by_cases hx1 : P1 x = true
      · rw [hx1]
        simp only [if_true]
        by_cases hy0 : P0 y = true
        · obtain ⟨ihA, ihB⟩ := ih0 hy0
          refine ⟨by omega, fun _ hz => ?_⟩
          obtain ⟨z, hz, hz0, hz1⟩ := hz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · rw [hx1] at hz1
            exact absurd hz1 (by simp)
          · have := ihB ⟨z, hz, hz0, hz1⟩
            omega
        · have hy0' : P0 y = false := by simpa using hy0
          obtain ⟨ihA, -⟩ := ih1 hy0'
          exact ⟨by omega, fun _ _ => by omega⟩
      · have hx1' : P1 x = false := by simpa using hx1
        rw [hx1']
        simp only [Bool.false_eq_true, if_false, add_zero]
        have hy0 : P0 y = false := by
          by_contra hne
          have := hadj' x y hxy (by simpa using hne)
          exact hx1 this
        obtain ⟨ihA, -⟩ := ih1 hy0
        exact ⟨ihA, fun h => absurd h (by simp)⟩

lemma count_le {V : Type} (R : V → V → Prop) (P0 P1 : V → Bool)
    (h01 : ∀ x, P0 x = true → P1 x = false)
    (hadj : ∀ x y, R x y → P0 x = true → P1 y = true)
    (hadj' : ∀ x y, R x y → P0 y = true → P1 x = true)
    (l : List V) (hc : List.IsChain R l) (h2 : ∃ z ∈ l, P0 z = false ∧ P1 z = false) :
    l.countP P0 ≤ l.countP P1 := by
  cases l with
  | nil =>
    obtain ⟨z, hz, -⟩ := h2
    simp at hz
  | cons x t =>
    obtain ⟨hA, hB⟩ := count_aux R P0 P1 h01 hadj hadj' t x hc
    by_cases hx : P0 x = true
    · exact (hA hx).2 h2
    · exact (hB (by simpa using hx)).1

/- the big layer and the small layer of side `s` -/
def big (k : ℕ) (s : Bool) (x : Vtx k) : Bool := (x.1 == s) && x.2.isLeft

def small (k : ℕ) (s : Bool) (x : Vtx k) : Bool := (x.1 == s) && x.2.isRight

/- No path contains the whole big layer of side `s` together with a vertex of the other side. -/
lemma no_bigger (k : ℕ) (s : Bool) (l : List (Vtx k)) (hn : l.Nodup)
    (hc : List.IsChain (gr k).Adj l) (hA : ∀ i : Fin (k + 1), (s, Sum.inl i) ∈ l)
    (z : Vtx k) (hz : z ∈ l) (hzs : z.1 ≠ s) : False := by
  have hle : l.countP (big k s) ≤ l.countP (small k s) := by
    refine count_le (gr k).Adj (big k s) (small k s) ?_ ?_ ?_ l hc ⟨z, hz, ?_, ?_⟩
    · rintro ⟨b, i | j⟩ hx <;> simp_all [big, small]
    · intro x y hxy hx
      simp only [big, Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨h1, h2⟩ := adj_left k x y hxy hx.2
      simp [small, h1, h2, hx.1]
    · intro x y hxy hy
      simp only [big, Bool.and_eq_true, beq_iff_eq] at hy
      obtain ⟨h1, h2⟩ := adj_left k y x hxy.symm hy.2
      simp [small, h1, h2, hy.1]
    · simp [big, hzs]
    · simp [small, hzs]
  have hlow : k + 1 ≤ l.countP (big k s) := by
    have hnd : ((List.finRange (k + 1)).map (fun i => ((s, Sum.inl i) : Vtx k))).Nodup := by
      refine List.Nodup.map ?_ (List.nodup_finRange _)
      intro i i' h
      simpa using h
    have hsub : (List.finRange (k + 1)).map (fun i => ((s, Sum.inl i) : Vtx k)) ⊆ l := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hA i
    have h1 := List.Subperm.countP_le (big k s) (List.subperm_of_subset hnd hsub)
    have h2 : ((List.finRange (k + 1)).map (fun i => ((s, Sum.inl i) : Vtx k))).countP (big k s)
        = ((List.finRange (k + 1)).map (fun i => ((s, Sum.inl i) : Vtx k))).length := by
      rw [List.countP_eq_length]
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      simp [big]
    rw [h2, List.length_map, List.length_finRange] at h1
    exact h1
  have hup : l.countP (small k s) ≤ k := by
    rw [List.countP_eq_length_filter]
    have hnd : (l.filter (small k s)).Nodup := hn.filter _
    have hsub : l.filter (small k s) ⊆
        (List.finRange k).map (fun j => ((s, Sum.inr j) : Vtx k)) := by
      intro x hx
      rw [List.mem_filter] at hx
      obtain ⟨-, hx⟩ := hx
      obtain ⟨b, i | j⟩ := x
      · simp [small] at hx
      · simp only [small, Bool.and_eq_true, beq_iff_eq] at hx
        rw [List.mem_map]
        exact ⟨j, List.mem_finRange j, by rw [hx.1]⟩
    have h1 := (List.subperm_of_subset hnd hsub).length_le
    rw [List.length_map, List.length_finRange] at h1
    exact h1
  omega

/- A path through exactly the vertices of side `s`, built from the front:
a_n, b_(n-1), a_(n-1), ..., b_0, a_0. -/
lemma path_aux (k : ℕ) (s : Bool) : ∀ (n : ℕ) (hn : n < k + 1), ∃ t : List (Vtx k),
    (((s, Sum.inl ⟨n, hn⟩) : Vtx k) :: t).Nodup ∧
    List.IsChain (gr k).Adj (((s, Sum.inl ⟨n, hn⟩) : Vtx k) :: t) ∧
    ∀ x : Vtx k, x ∈ ((s, Sum.inl ⟨n, hn⟩) : Vtx k) :: t ↔
      (∃ i : Fin (k + 1), i.val ≤ n ∧ x = (s, Sum.inl i)) ∨
      (∃ j : Fin k, j.val < n ∧ x = (s, Sum.inr j)) := by
  intro n
  induction n with
  | zero =>
    intro hn
    refine ⟨[], by simp, List.isChain_singleton _, ?_⟩
    intro x
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact Or.inl ⟨⟨0, hn⟩, le_rfl, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
      · have : i = ⟨0, hn⟩ := Fin.ext (by simpa using hi)
        rw [this]
      · omega
  | succ n ih =>
    intro hn
    have hn' : n < k + 1 := by omega
    have hnk : n < k := by omega
    obtain ⟨t, hnd, hch, hmem⟩ := ih hn'
    refine ⟨((s, Sum.inr ⟨n, hnk⟩) : Vtx k) :: ((s, Sum.inl ⟨n, hn'⟩) : Vtx k) :: t, ?_, ?_, ?_⟩
    · rw [List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, hnd⟩
      · rw [List.mem_cons]
        rintro (h | h)
        · simp at h
        · rcases (hmem _).1 h with ⟨i, hi, h⟩ | ⟨j, hj, h⟩
          · simp only [Prod.mk.injEq, Sum.inl.injEq, true_and] at h
            rw [← h] at hi
            simp at hi
          · simp at h
      · intro h
        rcases (hmem _).1 h with ⟨i, hi, h⟩ | ⟨j, hj, h⟩
        · simp at h
        · simp only [Prod.mk.injEq, Sum.inr.injEq, true_and] at h
          rw [← h] at hj
          simp at hj
    · rw [List.isChain_cons_cons, List.isChain_cons_cons]
      exact ⟨adj_lr k s _ _, (adj_lr k s _ _).symm, hch⟩
    · intro x
      rw [List.mem_cons, List.mem_cons, hmem x]
      constructor
      · rintro (rfl | rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
        · exact Or.inl ⟨⟨n + 1, hn⟩, le_rfl, rfl⟩
        · exact Or.inr ⟨⟨n, hnk⟩, Nat.lt_succ_self n, rfl⟩
        · exact Or.inl ⟨i, by omega, rfl⟩
        · exact Or.inr ⟨j, by omega, rfl⟩
      · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
        · by_cases h : i.val = n + 1
          · left
            have : i = ⟨n + 1, hn⟩ := Fin.ext h
            rw [this]
          · right; right; left
            exact ⟨i, by omega, rfl⟩
        · by_cases h : j.val = n
          · right; left
            have : j = ⟨n, hnk⟩ := Fin.ext h
            rw [this]
          · right; right; right
            exact ⟨j, by omega, rfl⟩

lemma exists_path (k : ℕ) (s : Bool) : ∃ l : List (Vtx k), l ≠ [] ∧ l.Nodup ∧
    List.IsChain (gr k).Adj l ∧ ∀ x : Vtx k, x ∈ l ↔ x.1 = s := by
  obtain ⟨t, hnd, hch, hmem⟩ := path_aux k s k (Nat.lt_succ_self k)
  refine ⟨_, List.cons_ne_nil _ _, hnd, hch, ?_⟩
  intro x
  rw [hmem x]
  constructor
  · rintro (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩) <;> rfl
  · intro hx
    obtain ⟨b, i | j⟩ := x
    · exact Or.inl ⟨i, Nat.lt_succ_iff.mp i.isLt, by rw [show b = s from hx]⟩
    · exact Or.inr ⟨j, j.isLt, by rw [show b = s from hx]⟩

/- A vmax path whose vertices are exactly those of side `s`. -/
lemma exists_vmax (k : ℕ) (s : Bool) : ∃ (a b : Vtx k) (p : (gr k).Walk a b),
    IsVMax (gr k) p ∧ ∀ x : Vtx k, x ∈ p.support ↔ x.1 = s := by
  obtain ⟨l, hne, hnd, hch, hmem⟩ := exists_path k s
  have hsup : (SimpleGraph.Walk.ofSupport l hne hch).support = l :=
    SimpleGraph.Walk.support_ofSupport hne hch
  refine ⟨l.head hne, l.getLast hne, SimpleGraph.Walk.ofSupport l hne hch, ⟨?_, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, hsup]
    exact hnd
  · intro c d r hr hss
    rw [hsup] at hss
    obtain ⟨z, hz, hz'⟩ := Set.exists_of_ssubset hss
    have hzs : z.1 ≠ s := fun h => hz' ((hmem z).2 h)
    refine no_bigger k s r.support hr.support_nodup r.isChain_adj_support ?_ z hz hzs
    intro i
    exact hss.subset ((hmem (s, Sum.inl i)).2 rfl)
  · intro x
    rw [hsup]
    exact hmem x

/- fewer than k vertices cannot cover a whole small layer -/
lemma exists_rep (k : ℕ) (X : Finset (Vtx k)) (hX : X.card < k) (s : Bool) :
    ∃ j : Fin k, ((s, Sum.inr j) : Vtx k) ∉ X := by
  by_contra hcon
  have hall : ∀ j : Fin k, ((s, Sum.inr j) : Vtx k) ∈ X := by
    intro j
    by_contra hj
    exact hcon ⟨j, hj⟩
  have hle : (Finset.univ : Finset (Fin k)).card ≤ X.card := by
    refine Finset.card_le_card_of_injOn (fun j => ((s, Sum.inr j) : Vtx k)) ?_ ?_
    · intro j _
      exact hall j
    · intro j _ j' _ h
      simpa using h
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

lemma kconn (k : ℕ) : IsKConnected (gr k) k := by
  refine ⟨?_, ?_⟩
  · rw [ENat.card_eq_coe_fintype_card]
    have : Fintype.card (Vtx k) = 2 * (k + 1 + k) := by
      simp [Fintype.card_prod, Fintype.card_sum]
    rw [this]
    exact_mod_cast (by omega : k < 2 * (k + 1 + k))
  · intro X hX
    obtain ⟨jf, hjf⟩ := exists_rep k X hX false
    obtain ⟨jt, hjt⟩ := exists_rep k X hX true
    have hf : ((false, Sum.inr jf) : Vtx k) ∈ ((X : Set (Vtx k))ᶜ) := by simpa using hjf
    have ht : ((true, Sum.inr jt) : Vtx k) ∈ ((X : Set (Vtx k))ᶜ) := by simpa using hjt
    have hft : ((gr k).induce ((X : Set (Vtx k))ᶜ)).Reachable ⟨_, ht⟩ ⟨_, hf⟩ := by
      refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.induce_adj]
      exact adj_rr k true false (by simp) jt jf
    have key : ∀ v : ((X : Set (Vtx k))ᶜ : Set (Vtx k)),
        ((gr k).induce ((X : Set (Vtx k))ᶜ)).Reachable v ⟨_, hf⟩ := by
      rintro ⟨⟨b, i | j⟩, hv⟩
      · cases b
        · refine SimpleGraph.Adj.reachable ?_
          rw [SimpleGraph.induce_adj]
          exact adj_lr k false i jf
        · refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hft
          rw [SimpleGraph.induce_adj]
          exact adj_lr k true i jt
      · cases b
        · refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hft
          rw [SimpleGraph.induce_adj]
          exact adj_rr k false true (by simp) j jt
        · refine SimpleGraph.Adj.reachable ?_
          rw [SimpleGraph.induce_adj]
          exact adj_rr k true false (by simp) j jf
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => (key u).trans (key v).symm, ⟨⟨_, hf⟩⟩⟩

end OMA.P461267

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_461267.main) := by
  rintro ⟨K, h⟩
  obtain ⟨a, b, p, hp, hps⟩ := OMA.P461267.exists_vmax K false
  obtain ⟨c, d, q, hq, hqs⟩ := OMA.P461267.exists_vmax K true
  obtain ⟨x, hx1, hx2⟩ :=
    h K le_rfl (OMA.P461267.Vtx K) (OMA.P461267.gr K) (OMA.P461267.kconn K) a b c d p q hp hq
  have h1 := (hps x).1 hx1
  have h2 := (hqs x).1 hx2
  rw [h1] at h2
  exact absurd h2 (by simp)
