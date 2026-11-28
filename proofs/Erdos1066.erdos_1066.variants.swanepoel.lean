import FormalConjectures.ErdosProblems.«1066»
import Mathlib

/-!
This formalization follows Theorem 1, §§3–4, of Konrad J. Swanepoel,
*Independence Numbers of Planar Contact Graphs*,
Discrete & Computational Geometry 28 (2002), 649–670.
DOI: 10.1007/s00454-002-2897-y.

The straight-line planar geometry adapts the Harborth formalization in
*Prove Erdos1084.erdos_1084.variants.triangular_optimal_d2*:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7646
The reduction and angle accounting adapt parts of
*Erdos1066.erdos_1066.variants.swanepoel.R1* and
*Erdos1066.erdos_1066.variants.swanepoel.R2*:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10257
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/14247
-/

namespace Swanepoel

theorem corners_injective {V Q Q' : Type*} [Fintype V] [Fintype Q] [Fintype Q']
    (corner : V → Q) (f : {q : Q // q ∉ Set.range corner} ↪ Q')
    (hmiss : ∃ x : Q', x ∉ Set.range f)
    (hcard : Fintype.card Q' + Fintype.card V = Fintype.card Q + 1) :
    Function.Injective corner := by
  classical
  let s := Finset.univ.image corner
  have hmem (q : Q) : q ∈ s ↔ q ∈ Set.range corner := by
    simp [s, Finset.mem_image, Set.mem_range]
  let t : Finset Q := Finset.univ \ s
  let g (q : t) : {q : Q // q ∉ Set.range corner} :=
    ⟨q.val, fun h ↦ (Finset.mem_sdiff.mp q.property).2 ((hmem q.val).mpr h)⟩
  have hlt : t.card < Fintype.card Q' := by
    have h := Fintype.card_lt_of_injective_not_surjective (f := fun q : t ↦ f (g q))
      (fun q r h ↦ Subtype.ext (show q.val = r.val from congrArg
        (fun x : {a : Q // a ∉ Set.range corner} => x.val) (f.injective h))) (by
        rintro hsurj
        obtain ⟨x, hx⟩ := hmiss
        obtain ⟨q, hq⟩ := hsurj x
        exact hx ⟨g q, hq⟩)
    simpa using h
  have ht : t.card = Fintype.card Q - s.card := by
    change (Finset.univ \ s).card = Fintype.card Q - s.card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]
  have hsQ : s.card ≤ Fintype.card Q := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  have hsV : s.card ≤ Fintype.card V := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset V)) (f := corner))
  have hs : s.card = (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  have hinj : Set.InjOn corner (↑(Finset.univ : Finset V) : Set V) :=
    Finset.card_image_iff.mp hs
  intro x y hxy
  exact hinj (Finset.mem_univ x) (Finset.mem_univ y) hxy

theorem corners_injective_of_delete {V D D' Q Q' : Type*}
    [Fintype V] [Fintype Q] [Fintype Q']
    (φ : Equiv.Perm D) (ψ : Equiv.Perm D') (lift : D' ↪ D)
    (face : D → Q) (face' : D' → Q') (corner : V → Q)
    (onto : Function.Surjective face)
    (hφ : ∀ x y, face x = face y ↔ ∃ k : ℕ, (φ ^ k) x = y)
    (hψ : ∀ x y, face' x = face' y ↔ ∃ k : ℕ, (ψ ^ k) x = y)
    (hcover : ∀ d, face d ∉ Set.range corner → d ∈ Set.range lift)
    (hstep : ∀ d, face (lift d) ∉ Set.range corner → lift (ψ d) = φ (lift d))
    (hhit : ∃ d, face (lift d) ∈ Set.range corner)
    (hcard : Fintype.card Q' + Fintype.card V = Fintype.card Q + 1) :
    Function.Injective corner := by
  have hpres (d : D') (hd : face (lift d) ∉ Set.range corner) :
      ∀ k : ℕ, lift ((ψ ^ k) d) = (φ ^ k) (lift d) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have heq := (hφ (lift d) (lift ((ψ ^ k) d))).2 ⟨k, ih.symm⟩
      have hn : face (lift ((ψ ^ k) d)) ∉ Set.range corner := heq ▸ hd
      rw [pow_succ', Equiv.Perm.mul_apply, hstep _ hn, ih, pow_succ', Equiv.Perm.mul_apply]
  have hcert (q : {q : Q // q ∉ Set.range corner}) : ∃ d, face (lift d) = q.val := by
    obtain ⟨d, hd⟩ := onto q.val
    obtain ⟨e, rfl⟩ := hcover d (hd.symm ▸ q.property)
    exact ⟨e, hd⟩
  classical
  choose rep hrep using hcert
  have hb (q : {q : Q // q ∉ Set.range corner}) : face (lift (rep q)) ∉ Set.range corner :=
    (hrep q).symm ▸ q.property
  let fn : {q : Q // q ∉ Set.range corner} ↪ Q' :=
    ⟨fun q => face' (rep q), by
      intro q r h
      obtain ⟨k, hk⟩ := (hψ _ _).1 h
      apply Subtype.ext
      rw [← hrep q, ← hrep r]
      exact (hφ _ _).2 ⟨k, (hpres _ (hb q) k).symm.trans (congrArg lift hk)⟩⟩
  obtain ⟨d, hd⟩ := hhit
  apply corners_injective corner fn _ hcard
  refine ⟨face' d, ?_⟩
  rintro ⟨q, hq⟩
  obtain ⟨k, hk⟩ := (hψ _ _).1 hq
  have he := (hφ _ _).2 ⟨k, (hpres _ (hb q) k).symm.trans (congrArg lift hk)⟩
  exact hb q (he.symm ▸ hd)

end Swanepoel

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def keepLeaf (v u : V) : SimpleGraph V :=
  G.deleteEdges {e | v ∈ e ∧ e ≠ s(v, u)}

theorem keepLeaf_le (v u : V) : G.keepLeaf v u ≤ G :=
  SimpleGraph.deleteEdges_le _

theorem keepLeaf_edge (v u : V) (h : G.Adj v u) : (G.keepLeaf v u).Adj v u :=
  SimpleGraph.deleteEdges_adj.mpr ⟨h, by simp⟩

theorem keepLeaf_of_ne {v u x y : V} (hx : x ≠ v) (hy : y ≠ v) (h : G.Adj x y) :
    (G.keepLeaf v u).Adj x y := by
  exact SimpleGraph.deleteEdges_adj.mpr ⟨h, by simp [Ne.symm hx, Ne.symm hy]⟩

theorem keepLeaf_connected {v u : V} (h : G.Adj v u)
    (hc : (G.induce {x | x ≠ v}).Connected) : (G.keepLeaf v u).Connected := by
  let J := G.keepLeaf v u
  have hu : u ≠ v := h.symm.ne
  have huv : J.Adj v u := keepLeaf_edge G v u h
  let f : G.induce {x | x ≠ v} →g J :=
    ⟨Subtype.val, fun {x y} hxy => keepLeaf_of_ne G x.property y.property hxy⟩
  have hreach (x : V) : J.Reachable u x := by
    by_cases hx : x = v
    · subst x
      exact huv.symm.reachable
    · exact (hc ⟨u, hu⟩ ⟨x, hx⟩).map f
  letI : Nonempty V := ⟨u⟩
  exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩

theorem keepLeaf_card [Fintype V] {v u : V} (h : G.Adj v u) :
    haveI := Classical.decRel G.Adj
    haveI := Classical.decRel (G.keepLeaf v u).Adj
    (G.keepLeaf v u).edgeFinset.card + G.degree v = G.edgeFinset.card + 1 := by
  classical
  let S := (G.incidenceFinset v).erase s(v, u)
  have he : s(v, u) ∈ G.incidenceFinset v := by
    simp [h]
  have hsub : S ⊆ G.edgeFinset :=
    (Finset.erase_subset ..).trans (G.incidenceFinset_subset v)
  have hs : S.card + 1 = G.degree v := by
    change ((G.incidenceFinset v).erase s(v, u)).card + 1 = G.degree v
    rw [Finset.card_erase_add_one he, SimpleGraph.card_incidenceFinset_eq_degree]
  have hJ : G.keepLeaf v u = G.deleteEdges (S : Set (Sym2 V)) := by
    ext x y
    by_cases hx : G.Adj x y <;>
      simp [keepLeaf, SimpleGraph.deleteEdges_adj, S, SimpleGraph.mk'_mem_incidenceSet_iff, hx]
  rw [hJ, SimpleGraph.edgeFinset_deleteEdges]
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  omega

end SimpleGraph

open Equiv.Perm

namespace Swanepoel

theorem index_cycle {A : Type*} {f : Equiv.Perm A} {s : Finset A}
    (hf : f.IsCycleOn (s : Set A)) (a : A) (ha : a ∈ s) :
    ∃ e : Fin s.card ≃ ↥s, ∀ i, (e (finRotate s.card i)).val = f (e i).val := by
  classical
  have hm (k : ℕ) : (f ^ k) a ∈ s := by
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hf.1.mapsTo ih
  let g (i : Fin s.card) : ↥s := ⟨(f ^ (i : ℕ)) a, hm i⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j h
      have h' := (hf.pow_apply_eq_pow_apply ha).1 (congrArg (fun v : ↥s => v.val) h)
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h'
    · intro b
      obtain ⟨k, hk, he⟩ := hf.exists_pow_eq ha b.property
      exact ⟨⟨k, hk⟩, Subtype.ext he⟩
  refine ⟨Equiv.ofBijective g hg, fun i => ?_⟩
  change (f ^ (finRotate s.card i).val) a = f ((f ^ i.val) a)
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  apply (hf.pow_apply_eq_pow_apply ha).2
  rw [finRotate_apply, Fin.val_add]
  change (i.val + 1 % s.card) % s.card ≡ i.val + 1 [MOD s.card]
  rw [Nat.add_mod_mod]
  exact Nat.mod_modEq _ _

theorem connected_of_cut {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (cut : ∀ A : Finset V, A.Nonempty → (Finset.univ \ A).Nonempty →
      ∃ x ∈ A, ∃ y ∈ Finset.univ \ A, G.Adj x y) : G.Connected := by
  classical
  refine ⟨fun u v => ?_⟩
  by_contra h
  let A := Finset.univ.filter (G.Reachable u)
  have hu : u ∈ A := by simp [A]
  have hv : v ∈ Finset.univ \ A := by simpa [A] using h
  obtain ⟨x, hx, y, hy, hxy⟩ := cut A ⟨u, hu⟩ ⟨v, hv⟩
  have hux : G.Reachable u x := (Finset.mem_filter.mp hx).2
  exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hux.trans hxy.reachable⟩)

end Swanepoel

namespace CyclicGap

variable {n : ℕ} {mark : Finset (Fin n)}

private theorem rotate_val (a : Fin n) :
    (finRotate n a).val = (a.val + 1) % n := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n =>
    rw [coe_finRotate]
    split
    · rename_i h
      subst a
      simp
    · rename_i h
      have ha := a.isLt
      have hne : a.val ≠ n := fun he => h (Fin.ext he)
      exact (Nat.mod_eq_of_lt (by omega)).symm

private theorem rotate_pow_val (i : ℕ) (a : Fin n) :
    ((finRotate n ^ i) a).val = (a.val + i) % n := by
  induction i with
  | zero => simpa using (Nat.mod_eq_of_lt a.isLt).symm
  | succ i ih =>
    rw [pow_succ']
    change (finRotate n ((finRotate n ^ i) a)).val = _
    rw [rotate_val, ih, Nat.mod_add_mod]
    congr 1

private theorem full_turn (a : Fin n) : (finRotate n ^ n) a = a := by
  apply Fin.ext
  rw [rotate_pow_val, Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]

private theorem reachable (a v : Fin n) : ∃ i : ℕ, (finRotate n ^ i) a = v := by
  by_cases h : a.val ≤ v.val
  · refine ⟨v.val - a.val, Fin.ext ?_⟩
    rw [rotate_pow_val, show a.val + (v.val - a.val) = v.val by omega,
      Nat.mod_eq_of_lt v.isLt]
  · refine ⟨n + v.val - a.val, Fin.ext ?_⟩
    have ha := a.isLt
    rw [rotate_pow_val, show a.val + (n + v.val - a.val) = v.val + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]

private theorem step_add (i j : ℕ) (a : Fin n) :
    (finRotate n ^ (i + j)) a = (finRotate n ^ i) ((finRotate n ^ j) a) := by
  rw [pow_add]
  rfl

private theorem return_exists (a : ↥mark) :
    ∃ i : ℕ, 0 < i ∧ (finRotate n ^ i) a.val ∈ mark :=
  ⟨n, Nat.zero_lt_of_lt a.val.isLt, by rw [full_turn]; exact a.property⟩

noncomputable def length (a : ↥mark) : ℕ := by
  classical
  exact Nat.find (return_exists a)

private theorem return_spec (a : ↥mark) :
    0 < length a ∧ (finRotate n ^ length a) a.val ∈ mark := by
  classical
  exact Nat.find_spec (return_exists a)

theorem length_pos (a : ↥mark) : 0 < length a := (return_spec a).1

theorem interior_unmarked (a : ↥mark) {i : ℕ} (hi : 0 < i) (hlt : i < length a) :
    (finRotate n ^ i) a.val ∉ mark := by
  classical
  exact fun hm => Nat.find_min (return_exists a) hlt ⟨hi, hm⟩

private theorem representation_exists (hm : mark.Nonempty) (v : Fin n) :
    ∃ a : ↥mark, ∃ i : ℕ, i < length a ∧ (finRotate n ^ i) a.val = v := by
  classical
  have hex : ∃ i : ℕ, ∃ a : ↥mark, (finRotate n ^ i) a.val = v := by
    obtain ⟨a, ha⟩ := hm
    obtain ⟨i, hi⟩ := reachable a v
    exact ⟨i, ⟨a, ha⟩, hi⟩
  let i := Nat.find hex
  obtain ⟨a, ha⟩ : ∃ a : ↥mark, (finRotate n ^ i) a.val = v := Nat.find_spec hex
  refine ⟨a, i, ?_, ha⟩
  by_contra! h
  have hb := (return_spec a).2
  have he : (i - length a) + length a = i := Nat.sub_add_cancel h
  have hp : (finRotate n ^ (i - length a)) ((finRotate n ^ length a) a.val) = v := by
    rw [← step_add, he, ha]
  exact Nat.find_min hex (show i - length a < i by have := length_pos a; omega)
    ⟨⟨_, hb⟩, hp⟩

private theorem representation_not_lt {a b : ↥mark} {i j : ℕ}
    (hj : j < length b) (h : (finRotate n ^ i) a.val = (finRotate n ^ j) b.val) : ¬ i < j := by
  intro hij
  have he : i + (j - i) = j := by omega
  have hab : a.val = (finRotate n ^ (j - i)) b.val := by
    apply (finRotate n ^ i).injective
    rwa [← step_add, he]
  exact interior_unmarked b (by omega : 0 < j - i) (by omega : j - i < length b)
    (hab ▸ a.property)

private theorem representation_injective {a b : ↥mark} {i j : ℕ}
    (hi : i < length a) (hj : j < length b)
    (h : (finRotate n ^ i) a.val = (finRotate n ^ j) b.val) : a = b ∧ i = j := by
  have h₁ := representation_not_lt hj h
  have h₂ := representation_not_lt hi h.symm
  have he : i = j := by omega
  subst j
  exact ⟨Subtype.ext ((finRotate n ^ i).injective h), rfl⟩

theorem existsUnique_representation (hm : mark.Nonempty) (v : Fin n) :
    ∃! p : ↥mark × ℕ, p.2 < length p.1 ∧ (finRotate n ^ p.2) p.1.val = v := by
  obtain ⟨a, i, hi, hv⟩ := representation_exists hm v
  refine ⟨(a, i), ⟨hi, hv⟩, ?_⟩
  rintro ⟨b, j⟩ ⟨hj, hw⟩
  have heq := representation_injective hj hi (hw.trans hv.symm)
  exact Prod.ext heq.1 heq.2

private noncomputable def endpoint (a : ↥mark) : ↥mark :=
  ⟨(finRotate n ^ length a) a.val, (return_spec a).2⟩

private theorem endpoint_injective : Function.Injective (endpoint (mark := mark)) := by
  intro a b h
  have ha : 1 + (length a - 1) = length a := by have := length_pos a; omega
  have hb : 1 + (length b - 1) = length b := by have := length_pos b; omega
  have hp : (finRotate n ^ (length a - 1)) a.val = (finRotate n ^ (length b - 1)) b.val := by
    apply (finRotate n ^ (1 : ℕ)).injective
    rw [← step_add, ← step_add, ha, hb]
    exact congrArg Subtype.val h
  have hla : length a - 1 < length a := by have := length_pos a; omega
  have hlb : length b - 1 < length b := by have := length_pos b; omega
  exact (representation_injective hla hlb hp).1

noncomputable def nextMark (mark : Finset (Fin n)) : Equiv.Perm ↥mark :=
  Equiv.ofBijective endpoint ⟨endpoint_injective, Finite.surjective_of_injective endpoint_injective⟩

theorem nextMark_apply (a : ↥mark) :
    (finRotate n ^ length a) a.val = (nextMark mark a).val := rfl

end CyclicGap

namespace Swanepoel

private theorem chord_rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = (i.val + 1) % n := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [coe_finRotate]
    split
    · rename_i h
      subst i
      simp
    · rename_i h
      have hi := i.isLt
      have hne : i.val ≠ n := fun he => h (Fin.ext he)
      exact (Nat.mod_eq_of_lt (by omega)).symm

private theorem chord_rotate_pow_val {n : ℕ} (a : Fin n) (j : ℕ) :
    ((finRotate n ^ j) a).val = (a.val + j) % n := by
  induction j with
  | zero => simpa using (Nat.mod_eq_of_lt a.isLt).symm
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, chord_rotate_val, ih, Nat.mod_add_mod]
    congr 1

private theorem chord_mod_eq_sub {k t : ℕ} (h₁ : k ≤ t) (h₂ : t < k + k) :
    t % k = t - k := by
  calc
    t % k = ((t - k) + k) % k := congrArg (· % k) (by omega)
    _ = (t - k) % k := Nat.add_mod_right _ _
    _ = t - k := Nat.mod_eq_of_lt (by omega)

variable {k m : ℕ} {V : Type*}

def chordIndices (hmk : m ≤ k) (a : Fin k) : Fin m ↪ Fin k where
  toFun i := (finRotate k ^ i.val) a
  inj' := by
    intro i j h
    have he := congrArg Fin.val h
    change ((finRotate k ^ i.val) a).val = ((finRotate k ^ j.val) a).val at he
    rw [chord_rotate_pow_val, chord_rotate_pow_val] at he
    have ha := a.isLt
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    rcases lt_or_ge (a.val + i.val) k with hil | hih <;>
      rcases lt_or_ge (a.val + j.val) k with hjl | hjh
    · rw [Nat.mod_eq_of_lt hil, Nat.mod_eq_of_lt hjl] at he
      omega
    · rw [Nat.mod_eq_of_lt hil, chord_mod_eq_sub hjh (by omega)] at he
      omega
    · rw [chord_mod_eq_sub hih (by omega), Nat.mod_eq_of_lt hjl] at he
      omega
    · rw [chord_mod_eq_sub hih (by omega), chord_mod_eq_sub hjh (by omega)] at he
      omega

def chordSegment (b : Fin k ↪ V) (hmk : m ≤ k) (a : Fin k) : Fin m ↪ V where
  toFun i := b (chordIndices hmk a i)
  inj' := (b.injective.comp (chordIndices hmk a).injective)

@[simp] theorem chordSegment_apply (b : Fin k ↪ V) (hmk : m ≤ k) (a : Fin k) (i : Fin m) :
    chordSegment b hmk a i = b ((finRotate k ^ i.val) a) := rfl

def chordFirst (hm : 3 ≤ m) : Fin m := ⟨0, by omega⟩

def chordLast (hm : 3 ≤ m) : Fin m := ⟨m - 1, by omega⟩

theorem chordFirst_ne_last (hm : 3 ≤ m) : chordFirst hm ≠ chordLast hm := by
  intro h
  have he := congrArg Fin.val h
  change 0 = m - 1 at he
  omega

@[simp] theorem chordSegment_first (b : Fin k ↪ V) (hmk : m ≤ k) (a : Fin k) (hm : 3 ≤ m) :
    chordSegment b hmk a (chordFirst hm) = b a := by
  rw [chordSegment_apply]
  change b ((finRotate k ^ (0 : ℕ)) a) = b a
  simp

theorem chordIndices_next (hmk : m ≤ k) (a : Fin k) (hm : 3 ≤ m) (i : Fin m)
    (hi : i ≠ chordLast hm) :
    chordIndices hmk a (finRotate m i) = finRotate k (chordIndices hmk a i) := by
  have hv := i.isLt
  have hne : i.val ≠ m - 1 := fun h => hi (Fin.ext h)
  have hval : (finRotate m i).val = i.val + 1 := by
    rw [chord_rotate_val, Nat.mod_eq_of_lt (by omega)]
  change (finRotate k ^ (finRotate m i).val) a = finRotate k ((finRotate k ^ i.val) a)
  rw [hval, pow_succ', Equiv.Perm.mul_apply]

theorem chordIndices_prev (hmk : m ≤ k) (a : Fin k) (hm : 3 ≤ m) (i : Fin m)
    (hi : i ≠ chordFirst hm) :
    chordIndices hmk a ((finRotate m).symm i) = (finRotate k).symm (chordIndices hmk a i) := by
  have hwrap : finRotate m (chordLast hm) = chordFirst hm := by
    apply Fin.ext
    rw [chord_rotate_val]
    change (m - 1 + 1) % m = 0
    rw [show m - 1 + 1 = m by omega, Nat.mod_self]
  have hne : (finRotate m).symm i ≠ chordLast hm := by
    intro h
    apply hi
    rw [← hwrap, ← h, Equiv.apply_symm_apply]
  apply (finRotate k).injective
  rw [Equiv.apply_symm_apply, ← chordIndices_next hmk a hm _ hne, Equiv.apply_symm_apply]

theorem chordSegment_interior_neighbors (b : Fin k ↪ V) (hmk : m ≤ k) (a : Fin k)
    (hm : 3 ≤ m) (i : Fin m) (hfirst : i ≠ chordFirst hm) (hlast : i ≠ chordLast hm) :
    chordSegment b hmk a ((finRotate m).symm i) = b ((finRotate k).symm (chordIndices hmk a i)) ∧
      chordSegment b hmk a (finRotate m i) = b (finRotate k (chordIndices hmk a i)) :=
  ⟨congrArg b (chordIndices_prev hmk a hm i hfirst),
    congrArg b (chordIndices_next hmk a hm i hlast)⟩

theorem chordSegment_adj (G : SimpleGraph V) (b : Fin k ↪ V) (hmk : m ≤ k) (a : Fin k)
    (hm : 3 ≤ m) (hstep : ∀ j, G.Adj (b j) (b (finRotate k j)))
    (hchord : G.Adj (chordSegment b hmk a (chordLast hm)) (b a)) (i : Fin m) :
    G.Adj (chordSegment b hmk a i) (chordSegment b hmk a (finRotate m i)) := by
  by_cases hi : i = chordLast hm
  · subst i
    have hwrap : finRotate m (chordLast hm) = chordFirst hm := by
      apply Fin.ext
      rw [chord_rotate_val]
      change (m - 1 + 1) % m = 0
      rw [show m - 1 + 1 = m by omega, Nat.mod_self]
    rw [hwrap, chordSegment_first]
    exact hchord
  · change G.Adj (b (chordIndices hmk a i)) (b (chordIndices hmk a (finRotate m i)))
    rw [chordIndices_next hmk a hm i hi]
    exact hstep _

def chordInterior (hm : 3 ≤ m) : Finset (Fin m) :=
  (Finset.univ.erase (chordFirst hm)).erase (chordLast hm)

@[simp] theorem mem_chordInterior (hm : 3 ≤ m) (i : Fin m) :
    i ∈ chordInterior hm ↔ i ≠ chordFirst hm ∧ i ≠ chordLast hm := by
  simp [chordInterior, and_comm]

theorem chord_sum_endpoints {A : Type*} [AddCommMonoid A] (hm : 3 ≤ m) (f : Fin m → A) :
    (∑ i, f i) = (∑ i ∈ chordInterior hm, f i) + f (chordLast hm) + f (chordFirst hm) := by
  have he : chordLast hm ∈ Finset.univ.erase (chordFirst hm) :=
    Finset.mem_erase.mpr ⟨(chordFirst_ne_last hm).symm, Finset.mem_univ _⟩
  rw [chordInterior, Finset.sum_erase_add _ _ he, Finset.sum_erase_add _ _ (Finset.mem_univ _)]

theorem chord_degree_deficit_nonpos {d : ℕ} (hd : 4 ≤ d) :
    (4 - (d : ℝ)) * (Real.pi / 3) ≤ 0 := by
  have h : (4 : ℝ) ≤ d := by exact_mod_cast hd
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity)

theorem chord_interior_degree_deficit (hm : 3 ≤ m) (degree : Fin m → ℕ)
    (hmin : ∀ i ∈ chordInterior hm, 3 ≤ degree i)
    (hone : ∀ i ∈ chordInterior hm, ∀ j ∈ chordInterior hm,
      degree i < 4 → degree j < 4 → i = j) :
    (∑ i ∈ chordInterior hm, (4 - (degree i : ℝ)) * (Real.pi / 3)) ≤ Real.pi / 3 := by
  classical
  let f (i : Fin m) : ℝ := (4 - (degree i : ℝ)) * (Real.pi / 3)
  change (∑ i ∈ chordInterior hm, f i) ≤ Real.pi / 3
  by_cases hex : ∃ i ∈ chordInterior hm, degree i < 4
  · obtain ⟨i, hi, hil⟩ := hex
    have hd : degree i = 3 := by have := hmin i hi; omega
    have hf : f i = Real.pi / 3 := by simp [f, hd]; ring
    have hs : (∑ j ∈ (chordInterior hm).erase i, f j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
      apply chord_degree_deficit_nonpos
      exact le_of_not_gt (fun hjl => hne (hone j hj i hi hjl hil))
    rw [← Finset.sum_erase_add (chordInterior hm) f hi, hf]
    linarith
  · have hs : (∑ i ∈ chordInterior hm, f i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact chord_degree_deficit_nonpos (le_of_not_gt (fun hil => hex ⟨i, hi, hil⟩))
    exact hs.trans (by positivity)

end Swanepoel

namespace FacingRays

noncomputable def left (α : ℝ) : ℂ := ⟨Real.cos α, Real.sin α⟩

noncomputable def right (β : ℝ) : ℂ := ⟨1 - Real.cos β, Real.sin β⟩

private theorem dist_sq (α β : ℝ) :
    dist (left α) (right β) ^ 2 =
      1 + 4 * Real.cos ((α + β) / 2) *
        (Real.cos ((α + β) / 2) - Real.cos ((α - β) / 2)) := by
  let s := (α + β) / 2
  let d := (α - β) / 2
  change _ = 1 + 4 * Real.cos s * (Real.cos s - Real.cos d)
  have hsum : Real.cos α + Real.cos β = 2 * Real.cos s * Real.cos d := by
    have ha : s + d = α := by dsimp [s, d]; ring
    have hb : s - d = β := by dsimp [s, d]; ring
    rw [← ha, ← hb, Real.cos_add, Real.cos_sub]
    ring
  have hadd : Real.cos (α + β) = 2 * Real.cos s ^ 2 - 1 := by
    have hs : α + β = 2 * s := by dsimp [s]; ring
    exact (congrArg Real.cos hs).trans (Real.cos_two_mul s)
  calc
    dist (left α) (right β) ^ 2 =
        3 + 2 * Real.cos (α + β) - 2 * (Real.cos α + Real.cos β) := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
        Complex.sub_im, Real.cos_add]
      change (Real.cos α - (1 - Real.cos β)) * (Real.cos α - (1 - Real.cos β)) +
        (Real.sin α - Real.sin β) * (Real.sin α - Real.sin β) = _
      linear_combination Real.sin_sq_add_cos_sq α + Real.sin_sq_add_cos_sq β
    _ = _ := by rw [hadd, hsum]; ring

theorem dist_lt_one_of_pos_of_add_lt_pi {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β < Real.pi) :
    dist (left α) (right β) < 1 := by
  have hd : |(α - β) / 2| < (α + β) / 2 :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have hc : Real.cos ((α + β) / 2) < Real.cos ((α - β) / 2) := by
    rw [← Real.cos_abs ((α - β) / 2)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hd
  have hp : 0 < Real.cos ((α + β) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsq : dist (left α) (right β) ^ 2 < 1 := by
    rw [dist_sq]
    linarith only [mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0 : ℝ) < 4) hp)
      (sub_neg.mpr hc)]
  by_contra! h
  nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ dist (left α) (right β) + 1 by linarith)]

end FacingRays

namespace Swanepoel.ChainStep

noncomputable def cis (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

noncomputable def w : ℂ := cis (Real.pi / 3)

theorem cis_add (s t : ℝ) : cis (s + t) = cis s * cis t := by
  rw [cis, cis, cis, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem cis_re (t : ℝ) : (cis t).re = Real.cos t :=
  Complex.exp_ofReal_mul_I_re t

private theorem cis_im (t : ℝ) : (cis t).im = Real.sin t :=
  Complex.exp_ofReal_mul_I_im t

private theorem cis_neg_add (t : ℝ) :
    cis (-t) + cis t = ((2 * Real.cos t : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, cis_re, Real.cos_neg, Complex.ofReal_re]
    ring
  · simp [cis_im, Real.sin_neg]

theorem one_sub_w : 1 - w = cis (-(Real.pi / 3)) := by
  have h := cis_neg_add (Real.pi / 3)
  rw [Real.cos_pi_div_three, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    Complex.ofReal_one] at h
  exact (eq_sub_of_add_eq h).symm

theorem displacement (a b : ℝ) :
    (1 - w) * cis a + w * cis b =
      ((2 * Real.cos (Real.pi / 3 - (a - b) / 2) : ℝ) : ℂ) * cis ((a + b) / 2) := by
  let x := Real.pi / 3 - (a - b) / 2
  let m := (a + b) / 2
  have ha : -(Real.pi / 3) + a = -x + m := by dsimp [x, m]; ring
  have hb : Real.pi / 3 + b = x + m := by dsimp [x, m]; ring
  change (1 - w) * cis a + w * cis b = ((2 * Real.cos x : ℝ) : ℂ) * cis m
  rw [one_sub_w, w, ← cis_add, ← cis_add, ha, hb, cis_add (-x) m, cis_add x m,
    ← add_mul, cis_neg_add]

theorem displacement_re_ge {a b : ℝ} (hb : -(Real.pi / 6) ≤ b) (hba : b ≤ a)
    (ha : a ≤ Real.pi / 6) :
    Real.sqrt 3 / 2 ≤ ((1 - w) * cis a + w * cis b).re := by
  have hp := Real.pi_pos
  let x := Real.pi / 3 - (a - b) / 2
  have hx : 1 / 2 ≤ Real.cos x := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by dsimp [x]; linarith)
      (by linarith) (by dsimp [x]; linarith)
  have hm : ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi / 6 → Real.sqrt 3 / 2 ≤ Real.cos t := by
    intro t ht ht'
    rw [← Real.cos_pi_div_six]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ht (by linarith) ht'
  have hc : Real.sqrt 3 / 2 ≤ Real.cos ((a + b) / 2) := by
    by_cases h : 0 ≤ (a + b) / 2
    · exact hm _ h (by linarith)
    · rw [← Real.cos_neg ((a + b) / 2)]
      exact hm _ (by linarith) (by linarith)
  rw [displacement]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, cis_re, zero_mul, sub_zero]
  have hx' : 1 ≤ 2 * Real.cos x := by linarith
  simpa only [one_mul] using mul_le_mul hx' hc (by positivity) (by linarith)

private theorem cos_shift_bounds {t : ℝ} (hl : Real.pi / 6 ≤ t) (hu : t ≤ Real.pi / 2) :
    0 ≤ Real.cos t ∧ Real.cos t ≤ Real.sqrt 3 / 2 := by
  have hp := Real.pi_pos
  constructor
  · rw [← Real.cos_pi_div_two]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hu
  · rw [← Real.cos_pi_div_six]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hl

theorem w_mul_cis_re_bounds {a : ℝ} (hl : -(Real.pi / 6) ≤ a) (hu : a ≤ Real.pi / 6) :
    0 ≤ (w * cis a).re ∧ (w * cis a).re ≤ Real.sqrt 3 / 2 := by
  rw [w, ← cis_add, cis_re]
  exact cos_shift_bounds (by linarith) (by linarith)

theorem one_sub_w_mul_cis_re_bounds {a : ℝ} (hl : -(Real.pi / 6) ≤ a)
    (hu : a ≤ Real.pi / 6) :
    0 ≤ ((1 - w) * cis a).re ∧ ((1 - w) * cis a).re ≤ Real.sqrt 3 / 2 := by
  rw [one_sub_w, ← cis_add, cis_re, ← Real.cos_neg (-(Real.pi / 3) + a)]
  exact cos_shift_bounds (by linarith) (by linarith)

end Swanepoel.ChainStep

open scoped ComplexConjugate

namespace EdgeCharge

noncomputable def cis (t : ℝ) : ℂ := ⟨Real.cos t, Real.sin t⟩

private theorem cis_add (a b : ℝ) : cis (a + b) = cis a * cis b := by
  apply Complex.ext
  · exact Real.cos_add a b
  · simpa only [cis, Complex.mul_im, add_comm] using Real.sin_add a b

private theorem conj_cis (a : ℝ) : conj (cis a) = cis (-a) := by
  exact Complex.ext (Real.cos_neg a).symm (Real.sin_neg a).symm

private theorem dist_eq_normalized {A B X Y : ℂ} {γ δ : ℝ}
    (hAB : ‖B - A‖ = 1) (hx : X - A = (B - A) * cis γ)
    (hy : Y - B = (A - B) * cis δ) : dist X Y = dist (cis γ) (1 - cis δ) := by
  have hsub : X - Y = (B - A) * (cis γ - (1 - cis δ)) := by
    calc
      X - Y = (X - A) - (Y - B) - (B - A) := by ring
      _ = _ := by rw [hx, hy]; ring
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_mul, hAB, one_mul]

theorem pi_le_add_of_facing
    (facing : ∀ {a b : ℝ}, 0 < a → 0 < b → a + b < Real.pi →
      dist (cis a) (1 - cis (-b)) < 1)
    {A B X Y : ℂ} {α β : ℝ} (hAB : ‖B - A‖ = 1)
    (_hAX : ‖X - A‖ = 1) (_hBY : ‖Y - B‖ = 1) (_hne : X ≠ Y)
    (hsep : 1 ≤ dist X Y) (hα : 0 < α) (hβ : 0 < β)
    (hx : X - A = (B - A) * cis (-α)) (hy : Y - B = (A - B) * cis β) :
    Real.pi ≤ α + β := by
  apply le_of_not_gt
  intro hsum
  have hconj : dist (cis (-α)) (1 - cis β) = dist (cis α) (1 - cis (-β)) := by
    simpa only [map_sub, map_one, conj_cis, neg_neg] using
      Complex.dist_conj_conj (cis α) (1 - cis (-β))
  rw [dist_eq_normalized hAB hx hy, hconj] at hsep
  exact (not_le_of_gt (facing hα hβ hsum)) hsep

end EdgeCharge

namespace Swanepoel.ChainStep

theorem cis_arg {z : ℂ} (hz : ‖z‖ = 1) : cis z.arg = z := by
  apply Complex.ext
  · rw [cis_re, Complex.cos_arg (by aesop), hz, div_one]
  · rw [cis_im, Complex.sin_arg, hz, div_one]

theorem unit_angle {z : ℂ} (hz : ‖z‖ = 1) : ∃ a : ℝ, 0 ≤ a ∧ a < 2 * Real.pi ∧ cis a = z := by
  have hp := Real.pi_pos
  by_cases h : 0 ≤ z.arg
  · exact ⟨z.arg, h, by linarith [Complex.arg_le_pi z], cis_arg hz⟩
  · refine ⟨z.arg + 2 * Real.pi, by linarith [Complex.neg_pi_lt_arg z], by linarith, ?_⟩
    rw [cis_add, show cis (2 * Real.pi) = 1 by
      apply Complex.ext <;> simp [cis_re, cis_im], mul_one, cis_arg hz]

theorem equilateral_gap {t : ℝ} (ht : 0 ≤ t) (ht' : t < 2 * Real.pi)
    (hd : ‖cis t - 1‖ = 1) : t = Real.pi / 3 ∨ t = 5 * Real.pi / 3 := by
  have hsq := Complex.sq_norm (cis t - 1)
  simp only [hd, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, cis_re, cis_im, sub_zero, one_pow] at hsq
  have hc : Real.cos t = 1 / 2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  rw [← Real.cos_pi_div_three] at hc
  by_cases h : t ≤ Real.pi
  · exact Or.inl (Real.strictAntiOn_cos.injOn
      (show t ∈ Set.Icc 0 Real.pi from ⟨ht, h⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩) hc)
  · right
    have he : Real.cos (2 * Real.pi - t) = Real.cos (Real.pi / 3) := by
      rw [show 2 * Real.pi - t = -t + 2 * Real.pi by ring, Real.cos_add_two_pi, Real.cos_neg, hc]
    have := Real.strictAntiOn_cos.injOn
      (show 2 * Real.pi - t ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩) he
    linarith

end Swanepoel.ChainStep

namespace Swanepoel.CircleMeet

open Swanepoel.ChainStep

private theorem normalized_norms {A B X : ℂ} (hu : B - A ≠ 0)
    (hXA : ‖X - A‖ = 1) (hXB : ‖X - B‖ = 1) :
    ‖(X - A) / (B - A)‖ = 1 / ‖B - A‖ ∧
      ‖(X - A) / (B - A) - 1‖ = 1 / ‖B - A‖ := by
  have h : (X - A) / (B - A) - 1 = (X - B) / (B - A) := by
    rw [← div_self hu, ← sub_div]
    congr 1
    ring
  constructor
  · rw [norm_div, hXA]
  · rw [h, norm_div, hXB]

private theorem re_eq_half {x : ℂ} (h : ‖x‖ = ‖x - 1‖) : x.re = 1 / 2 := by
  have hnorm : ‖x‖ ^ 2 = ‖x - 1‖ ^ 2 := by rw [h]
  have h₁ := Complex.sq_norm x
  have h₂ := Complex.sq_norm (x - 1)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero] at h₁ h₂
  nlinarith only [h₁, h₂, hnorm]

theorem common_neighbors_sum {A B X Z : ℂ} (hAB : A ≠ B) (hXZ : X ≠ Z)
    (hXA : ‖X - A‖ = 1) (hXB : ‖X - B‖ = 1)
    (hZA : ‖Z - A‖ = 1) (hZB : ‖Z - B‖ = 1) : X + Z = A + B := by
  let u := B - A
  let x := (X - A) / u
  let z := (Z - A) / u
  have hu : u ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hx : x * u = X - A := div_mul_cancel₀ _ hu
  have hz : z * u = Z - A := div_mul_cancel₀ _ hu
  obtain ⟨hxn, hxn'⟩ := normalized_norms hu hXA hXB
  obtain ⟨hzn, hzn'⟩ := normalized_norms hu hZA hZB
  have hxr : x.re = 1 / 2 := re_eq_half (hxn.trans hxn'.symm)
  have hzr : z.re = 1 / 2 := re_eq_half (hzn.trans hzn'.symm)
  have hsx := Complex.sq_norm x
  have hsz := Complex.sq_norm z
  have hn : ‖x‖ = ‖z‖ := hxn.trans hzn.symm
  rw [hn] at hsx
  simp only [Complex.normSq_apply, hxr, hzr] at hsx hsz
  have hi : (x.im - z.im) * (x.im + z.im) = 0 := by
    nlinarith only [hsx, hsz]
  have hsum : x.im + z.im = 0 := by
    rcases mul_eq_zero.mp hi with he | he
    · have hxz : x = z := Complex.ext (hxr.trans hzr.symm) (sub_eq_zero.mp he)
      exact (hXZ (sub_left_inj.mp (hx.symm.trans (hxz ▸ hz)))).elim
    · exact he
  have hunit : x + z = 1 := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, hxr, hzr]
      norm_num
    · simpa only [Complex.add_im, Complex.one_im] using hsum
  have hm : (X - A) + (Z - A) = u := by
    calc
      (X - A) + (Z - A) = x * u + z * u := by rw [hx, hz]
      _ = (x + z) * u := (add_mul x z u).symm
      _ = u := by rw [hunit, one_mul]
  change (X - A) + (Z - A) = B - A at hm
  linear_combination hm

theorem common_neighbor_eq_or_eq {A B X Z Y : ℂ} (hAB : A ≠ B) (hXZ : X ≠ Z)
    (hXA : ‖X - A‖ = 1) (hXB : ‖X - B‖ = 1)
    (hZA : ‖Z - A‖ = 1) (hZB : ‖Z - B‖ = 1)
    (hYA : ‖Y - A‖ = 1) (hYB : ‖Y - B‖ = 1) : Y = X ∨ Y = Z := by
  by_cases hYX : Y = X
  · exact Or.inl hYX
  · right
    have hsum := (common_neighbors_sum hAB (Ne.symm hYX) hXA hXB hYA hYB).trans
      (common_neighbors_sum hAB hXZ hXA hXB hZA hZB).symm
    exact add_left_cancel hsum

theorem contact_ne {A B : ℂ} (h : ‖B - A‖ = 1) : A ≠ B := by
  rintro rfl
  simpa using h

end Swanepoel.CircleMeet

open Finset
open scoped EuclideanGeometry

namespace Swanepoel

def ProblemGood (X : Finset ℝ²) : Prop :=
  ∃ I ⊆ X, (I : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) ∧ 8 * X.card ≤ 31 * I.card

structure MinBad (X : Finset ℝ²) : Prop where
  separated : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y)
  not_good : ¬ ProblemGood X
  smaller_good : ∀ Y ⊆ X, Y.card < X.card → ProblemGood Y

theorem exists_minBad_subset {X : Finset ℝ²}
    (hX : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y)) (hbad : ¬ ProblemGood X) :
    ∃ Y ⊆ X, MinBad Y := by
  have select (n : ℕ) : ∀ Z : Finset ℝ², Z.card = n →
      (Z : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) → ¬ ProblemGood Z →
      ∃ Y ⊆ Z, MinBad Y := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Z hz hsep hbadZ
      by_cases hmin : ∀ W ⊆ Z, W.card < Z.card → ProblemGood W
      · exact ⟨Z, Subset.rfl, ⟨hsep, hbadZ, hmin⟩⟩
      · push_neg at hmin
        obtain ⟨W, hW, hlt, hbadW⟩ := hmin
        have hsepW := hsep.mono (show (W : Set ℝ²) ⊆ (Z : Set ℝ²) from hW)
        obtain ⟨Y, hY, hYbad⟩ := ih W.card (hz ▸ hlt) W rfl hsepW hbadW
        exact ⟨Y, hY.trans hW, hYbad⟩
  exact select X.card X rfl hX hbad

theorem MinBad.nonempty {X : Finset ℝ²} (h : MinBad X) : X.Nonempty := by
  by_contra! he
  subst X
  exact h.not_good ⟨∅, Subset.rfl, by simp, by simp⟩

noncomputable def closedNeighborhood (X S : Finset ℝ²) : Finset ℝ² := by
  classical
  exact X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, dist y x = 1)

noncomputable def unitNeighbors (X : Finset ℝ²) (x : ℝ²) : Finset ℝ² := by
  classical
  exact X.filter (fun y => dist x y = 1)

private theorem good_of_union {X I J : Finset ℝ²} (hi : I ⊆ X) (hj : J ⊆ X)
    (hd : Disjoint I J) (ii : (I : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1))
    (ij : (J : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1))
    (hcross : ∀ x ∈ I, ∀ y ∈ J, dist x y ≠ 1)
    (hc : 8 * X.card ≤ 31 * (I.card + J.card)) : ProblemGood X := by
  classical
  refine ⟨I ∪ J, union_subset hi hj, ?_, by rwa [card_union_of_disjoint hd]⟩
  intro x hx y hy hn
  obtain hx | hx := mem_union.mp hx <;> obtain hy | hy := mem_union.mp hy
  · exact ii hx hy hn
  · exact hcross x hx y hy
  · rw [dist_comm]; exact hcross y hy x hx
  · exact ij hx hy hn

theorem MinBad.small_expansion {X S : Finset ℝ²} (h : MinBad X) (hs : S ⊆ X)
    (hi : (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1)) (hk : S.card ≤ 8) :
    4 * S.card ≤ (closedNeighborhood X S).card := by
  classical
  let D := closedNeighborhood X S
  change 4 * S.card ≤ D.card
  by_contra! hf
  have hsd : S ⊆ D := fun x hx => mem_filter.mpr ⟨hs hx, Or.inl hx⟩
  have hdx : D ⊆ X := filter_subset _ _
  have hsn := card_le_card hsd
  have hdn := card_le_card hdx
  have hcard := card_sdiff_of_subset hdx
  obtain ⟨I, hI, iI, hc⟩ := h.smaller_good (X \ D) sdiff_subset (by omega)
  have hcros (x) (hx : x ∈ S) (y) (hy : y ∈ I) : dist x y ≠ 1 := by
    intro e
    obtain ⟨hyX, hyD⟩ := mem_sdiff.mp (hI hy)
    exact hyD (mem_filter.mpr ⟨hyX, Or.inr ⟨x, hx, e⟩⟩)
  exact h.not_good (good_of_union hs (hI.trans sdiff_subset)
    (disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp (hI hy)).2 (hsd hx))) hi iI hcros (by omega))

theorem MinBad.three_le_degree {X : Finset ℝ²} (h : MinBad X) {x : ℝ²} (hx : x ∈ X) :
    3 ≤ (unitNeighbors X x).card := by
  classical
  have h₄ := h.small_expansion (S := {x}) (singleton_subset_iff.mpr hx) (by simp) (by simp)
  have heq : closedNeighborhood X {x} = insert x (unitNeighbors X x) := by
    ext y
    simp only [closedNeighborhood, unitNeighbors, mem_filter, mem_insert, mem_singleton,
      exists_eq_left]
    constructor
    · rintro ⟨hy, e | e⟩
      · exact Or.inl e
      · exact Or.inr ⟨hy, e⟩
    · rintro (rfl | ⟨hy, e⟩)
      · exact ⟨hx, Or.inl rfl⟩
      · exact ⟨hy, Or.inr e⟩
  have hn : x ∉ unitNeighbors X x := by simp [unitNeighbors]
  rw [heq, card_insert_of_notMem hn, card_singleton] at h₄
  omega

theorem MinBad.no_separator {X A B : Finset ℝ²} (h : MinBad X) (ha : A ⊆ X) (hb : B ⊆ X)
    (hna : A.Nonempty) (hnb : B.Nonempty) (hab : Disjoint A B)
    (hrep : (X \ (A ∪ B)).card ≤ 1) : ∃ x ∈ A, ∃ y ∈ B, dist x y = 1 := by
  classical
  by_contra! hcross
  have hxA := card_sdiff_of_subset ha
  have hxB := card_sdiff_of_subset hb
  have hcnt := card_le_card (union_subset ha hb)
  rw [card_union_of_disjoint hab] at hcnt
  have hna' := card_pos.mpr hna
  have hnb' := card_pos.mpr hnb
  obtain ⟨I, hi, iI, hI⟩ := h.smaller_good (X \ B) sdiff_subset (by omega)
  obtain ⟨L, hl, iL, hL⟩ := h.smaller_good B hb (by omega)
  have hIcapL : Disjoint I L :=
    disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp (hi hx)).2 (hl hy))
  apply h.not_good
  by_cases hsub : I ⊆ A
  · exact good_of_union (hi.trans sdiff_subset) (hl.trans hb) hIcapL iI iL
      (fun x hx y hy => hcross x (hsub hx) y (hl hy)) (by omega)
  obtain ⟨v, hv, hva⟩ := not_subset.mp hsub
  have hvs := mem_sdiff.mp (hi hv)
  have hvC : v ∈ X \ (A ∪ B) :=
    mem_sdiff.mpr ⟨hvs.1, fun e => (mem_union.mp e).elim hva hvs.2⟩
  have only_v {y : ℝ²} (hy : y ∈ X \ (A ∪ B)) : y = v :=
    card_le_one.mp hrep y hy v hvC
  obtain ⟨K, hk, iK, hK⟩ := h.smaller_good A ha (by omega)
  by_cases large : I.card ≤ K.card
  · exact good_of_union (hk.trans ha) (hl.trans hb) (hab.mono hk hl) iK iL
      (fun x hx y hy => hcross x (hk hx) y (hl hy)) (by omega)
  obtain ⟨J, hj, iJ, hJ⟩ := h.smaller_good (X \ A) sdiff_subset (by omega)
  have haI : I.erase v ⊆ A := by
    intro x hx
    obtain ⟨hxv, hxi⟩ := mem_erase.mp hx
    obtain ⟨hxX, hxB⟩ := mem_sdiff.mp (hi hxi)
    by_contra hxA'
    exact hxv (only_v (mem_sdiff.mpr ⟨hxX, fun e => (mem_union.mp e).elim hxA' hxB⟩))
  have hcros : ∀ x ∈ I.erase v, ∀ y ∈ J, dist x y ≠ 1 := by
    intro x hx y hy
    obtain ⟨hyX, hyA⟩ := mem_sdiff.mp (hj hy)
    by_cases e : y ∈ B
    · exact hcross x (haI hx) y e
    · have hyv := only_v (mem_sdiff.mpr ⟨hyX, fun f => (mem_union.mp f).elim hyA e⟩)
      subst y
      exact iI (mem_erase.mp hx).2 hv (mem_erase.mp hx).1
  refine good_of_union (haI.trans ha) (hj.trans sdiff_subset) ?_ ?_ iJ hcros ?_
  · exact disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp (hj hy)).2 (haI hx))
  · exact iI.mono (by exact_mod_cast (erase_subset v I))
  · rw [card_erase_of_mem hv]
    omega

private theorem separated_config (n : ℕ) : ∃ X : Finset ℝ², X.card = n ∧
    (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) := by
  classical
  let f : ℕ → ℝ² := fun t => EuclideanSpace.single 0 (t : ℝ)
  have hf : Function.Injective f := by
    intro a b h
    have hv := congrArg (fun z : ℝ² => z 0) h
    have hc : (a : ℝ) = (b : ℝ) := by simpa [f, PiLp.single_apply] using hv
    exact_mod_cast hc
  refine ⟨(range n).image f, by rw [card_image_of_injective _ hf, card_range], ?_⟩
  intro x hx y hy hn
  obtain ⟨a, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨b, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hy)
  have hab : a ≠ b := fun h => hn (congrArg f h)
  change (1 : ℝ) ≤ dist (EuclideanSpace.single (0 : Fin 2) (a : ℝ))
    (EuclideanSpace.single (0 : Fin 2) (b : ℝ))
  rw [PiLp.dist_single_same, Real.dist_eq]
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem graph_card_of_independent {X S : Finset ℝ²} (hs : S ⊆ X)
    (hi : (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1)) :
    S.card ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).indepNum := by
  classical
  let T : Finset (X : Set ℝ²) := S.subtype (fun p => p ∈ (X : Set ℝ²))
  have hT : (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).IsIndepSet (T : Set (X : Set ℝ²)) := by
    intro a ha b hb hab h
    have ha' : (a : ℝ²) ∈ S := by simpa [T] using ha
    have hb' : (b : ℝ²) ∈ S := by simpa [T] using hb
    exact hi ha' hb' (fun he => hab (Subtype.ext he)) h
  have hcard : T.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun p hp => Finset.mem_coe.mpr (hs hp))
  rw [← hcard]
  exact hT.card_le_indepNum

theorem ratio_of_finite_sets
    (h : ∀ X : Finset ℝ², (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) → ProblemGood X)
    (n : ℕ) : (8 / 31 : ℝ) * n ≤ (Erdos1066.g n : ℝ) := by
  let V : Set ℕ := {m | ∀ X : Finset ℝ², X.card = n →
    (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) →
    m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).indepNum}
  have hmem : (8 * n + 30) / 31 ∈ V := by
    intro X hXn hx
    obtain ⟨S, hs, hi, hc⟩ := h X hx
    have hS := graph_card_of_independent hs hi
    omega
  have hbd : BddAbove V := by
    obtain ⟨X, hXn, hX⟩ := separated_config n
    exact ⟨_, fun m hm => hm X hXn hX⟩
  have hl : (8 * n + 30) / 31 ≤ Erdos1066.g n := le_csSup hbd hmem
  have hnat : 8 * n ≤ 31 * Erdos1066.g n := by omega
  have hr : (8 : ℝ) * n ≤ 31 * (Erdos1066.g n : ℝ) := by exact_mod_cast hnat
  linarith

end Swanepoel

open scoped BigOperators

namespace Swanepoel

theorem arc_charges {V : Type*} [Fintype V]
    (next : Equiv.Perm V) (negative : V → ℕ) (large lead bent : V → Prop)
    [DecidablePred large] [DecidablePred lead] [DecidablePred bent]
    (hLead : ∀ i, lead i → 1 ≤ negative i)
    (hNext : ∀ i, ¬ large i → negative i ≤ (if lead i then 1 else 0) → lead (next i))
    (hBent : ∀ i, bent i → large i)
    (hBudget : (∑ i, negative i) + (∑ i, if bent i then 1 else 0) + 6 ≤ Fintype.card V) :
    ∃ i, large i ∧ ¬ bent i := by
  have hLeadCount (i : V) : (if lead i then 1 else 0) ≤ negative i := by
    by_cases hi : lead i
    · simpa only [if_pos hi] using hLead i hi
    · simp [hi]
  have hPoint (i : V) :
      1 + (if lead i then 1 else 0) ≤
        negative i + (if large i then 1 else 0) + (if lead (next i) then 1 else 0) := by
    have hc := hLeadCount i
    by_cases hi : large i
    · rw [if_pos hi]
      omega
    · rw [if_neg hi]
      by_cases hs : negative i ≤ (if lead i then 1 else 0)
      · rw [if_pos (hNext i hi hs)]
        omega
      · omega
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hPoint i)
  have hPerm : (∑ i, (if lead (next i) then 1 else 0 : ℕ)) =
      ∑ i, (if lead i then 1 else 0 : ℕ) :=
    Equiv.sum_comp next (fun i => if lead i then 1 else 0)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one] at hSum
  rw [hPerm] at hSum
  by_contra hNone
  have hEq : (∑ i, (if large i then 1 else 0 : ℕ)) =
      ∑ i, (if bent i then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hb : bent i
    · simp [hb, hBent i hb]
    · have hl : ¬ large i := fun h => hNone ⟨i, h, hb⟩
      simp [hb, hl]
  rw [hEq] at hSum
  omega

theorem chain_union {V : Type*} [DecidableEq V] (N : ℕ → Finset V) (n : ℕ) :
    ((Finset.range (n + 1)).biUnion N).card +
        (∑ i ∈ Finset.range n, (N i ∩ N (i+1)).card) ≤
      ∑ i ∈ Finset.range (n+1), (N i).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.range_add_one (n := n+1), Finset.biUnion_insert]
    have hsub : N n ⊆ (Finset.range (n+1)).biUnion N := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), hx⟩
    have hle : (N n ∩ N (n+1)).card ≤
        (N (n+1) ∩ (Finset.range (n+1)).biUnion N).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hl, hr⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hr, hsub hl⟩
    have hcard := Finset.card_union_add_card_inter (N (n+1))
      ((Finset.range (n+1)).biUnion N)
    omega

end Swanepoel

namespace Swanepoel

open scoped BigOperators

theorem gap_union_lt {V : Type*} [DecidableEq V] (N : ℕ → Finset V) (r : ℕ)
    (hr : 0 < r) (hdeg : ∀ i ≤ r, (N i).card ≤ 4) (hhead : (N 0).card ≤ 3)
    (hoverlap : ∀ i < r, 1 ≤ (N i ∩ N (i + 1)).card)
    (htail : (N r).card ≤ 3 ∨ 2 ≤ (N (r - 1) ∩ N r).card) :
    ((Finset.range (r + 1)).biUnion N).card < 3 * (r + 1) := by
  cases r with
  | zero => omega
  | succ k =>
    have hprefix : ∀ n ≤ k, (∑ i ∈ Finset.range (n + 1), (N i).card) ≤ 3 + 4 * n := by
      intro n
      induction n with
      | zero =>
        intro _
        simpa using hhead
      | succ n ih =>
        intro hn
        rw [Finset.sum_range_succ]
        have hi := ih (by omega)
        have hd := hdeg (n + 1) (by omega)
        omega
    have hinitial : k ≤ ∑ i ∈ Finset.range k, (N i ∩ N (i + 1)).card := by
      calc
        k = ∑ _i ∈ Finset.range k, (1 : ℕ) := by simp
        _ ≤ ∑ i ∈ Finset.range k, (N i ∩ N (i + 1)).card := by
          apply Finset.sum_le_sum
          intro i hi
          have hik := Finset.mem_range.mp hi
          exact hoverlap i (by omega)
    have hc := chain_union N (k + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hc
    have hp := hprefix k le_rfl
    have hd := hdeg (k + 1) le_rfl
    have ho := hoverlap k (by omega)
    change (N (k + 1)).card ≤ 3 ∨ 2 ≤ (N k ∩ N (k + 1)).card at htail
    rcases htail with ht | ht <;> omega

open scoped Classical in

theorem alternating_gap_contradiction {V : Type*} [DecidableEq V]
    (X : Finset V) (E : V → V → Prop) (p : ℕ → V) (N : ℕ → Finset V) (r : ℕ)
    (hr : 0 < r) (hk : r + 1 ≤ 8)
    (hp : Set.InjOn p ↑(Finset.range (r + 1))) (hX : ∀ i ≤ r, p i ∈ X)
    (hi : ∀ i ≤ r, ∀ j ≤ r, i ≠ j → ¬ E (p i) (p j))
    (hN : ∀ i ≤ r, ∀ x ∈ X, E (p i) x → x ∈ N i)
    (hdeg : ∀ i ≤ r, (N i).card ≤ 4) (hhead : (N 0).card ≤ 3)
    (hoverlap : ∀ i < r, 1 ≤ (N i ∩ N (i + 1)).card)
    (htail : (N r).card ≤ 3 ∨ 2 ≤ (N (r - 1) ∩ N r).card)
    (hexpand : ∀ S : Finset V, S ⊆ X → (S : Set V).Pairwise (fun x y => ¬ E x y) →
      S.card ≤ 8 → 4 * S.card ≤ (X.filter fun x => x ∈ S ∨ ∃ y ∈ S, E y x).card) : False := by
  let S := (Finset.range (r + 1)).image p
  let U := (Finset.range (r + 1)).biUnion N
  have hS : S ⊆ X := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hX i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hcardS : S.card = r + 1 := by
    change ((Finset.range (r + 1)).image p).card = r + 1
    rw [Finset.card_image_of_injOn hp, Finset.card_range]
  have hsub : (X.filter fun x => x ∈ S ∨ ∃ y ∈ S, E y x) ⊆ S ∪ U := by
    intro x hx
    obtain ⟨hxX, hxS | ⟨y, hy, hE⟩⟩ := Finset.mem_filter.mp hx
    · exact Finset.mem_union.mpr (Or.inl hxS)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨i, hi, hN i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) x hxX hE⟩))
  have hind : (S : Set V).Pairwise (fun x y => ¬ E x y) := by
    intro x hx y hy hxy
    obtain ⟨i, hir, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨j, hjr, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hi i (Nat.le_of_lt_succ (Finset.mem_range.mp hir))
      j (Nat.le_of_lt_succ (Finset.mem_range.mp hjr)) (fun e => hxy (congrArg p e))
  have hl := hexpand S hS hind (by simpa [hcardS] using hk)
  have hu := Finset.card_le_card hsub
  have hc := Finset.card_union_add_card_inter S U
  have hs : U.card < 3 * (r + 1) := gap_union_lt N r hr hdeg hhead hoverlap htail
  omega

end Swanepoel

namespace Swanepoel.ArcExtract

open scoped BigOperators Classical

noncomputable section

variable {n : ℕ}

def marks (deg : Fin n → ℕ) : Finset (Fin n) := Finset.univ.filter fun v => deg v = 3

variable {deg : Fin n → ℕ} (bad : Fin n → Prop)

abbrev x (a : ↥(marks deg)) (i : ℕ) : Fin n := (finRotate n ^ i) a.val

private theorem x_zero (a : ↥(marks deg)) : x a 0 = a.val := by simp [x]

def lead (a : ↥(marks deg)) : Prop :=
  2 ≤ CyclicGap.length a ∧ (bad a.val ∨ 5 ≤ deg (x a 1))

def negative (a : ↥(marks deg)) : ℕ :=
  ((Finset.range (CyclicGap.length a)).filter fun i => bad (x a i)).card +
    ((Finset.range (CyclicGap.length a)).filter fun i => 5 ≤ deg (x a i)).card

def eligible (a : ↥(marks deg)) : Prop :=
  15 ≤ CyclicGap.length a ∧
    (∀ i, 2 ≤ i → i < CyclicGap.length a → deg (x a i) = 4) ∧
    (∀ i, 1 ≤ i → i < CyclicGap.length a → ¬ bad (x a i)) ∧
    ¬ lead bad (CyclicGap.nextMark (marks deg) a)

def ShortImpossible : Prop := ∀ a : ↥(marks deg),
  CyclicGap.length a ≤ 14 → ¬ lead bad (CyclicGap.nextMark (marks deg) a) →
  (∀ i, 2 ≤ i → i < CyclicGap.length a → deg (x a i) = 4) →
  (∀ i, 1 ≤ i → i < CyclicGap.length a → ¬ bad (x a i)) →
  (CyclicGap.length a = 1 → ¬ bad a.val) → False

private theorem one_le_card_of_mem {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) : 1 ≤ s.card :=
  Finset.card_pos.mpr ⟨i, hi⟩

private theorem two_le_card_of_mem {s : Finset ℕ} {i j : ℕ}
    (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) : 2 ≤ s.card := by
  have hs : ({i, j} : Finset ℕ) ⊆ s := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  simpa [hne] using Finset.card_le_card hs

private theorem lead_negative (a : ↥(marks deg)) (h : lead bad a) :
    1 ≤ negative bad a := by
  obtain ⟨hd, hb | hh⟩ := h
  · have h0 : 0 ∈ (Finset.range (CyclicGap.length a)).filter (fun i => bad (x a i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa only [x_zero]⟩
    have := one_le_card_of_mem h0
    unfold negative
    omega
  · have h1 : 1 ∈ (Finset.range (CyclicGap.length a)).filter (fun i => 5 ≤ deg (x a i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩
    have := one_le_card_of_mem h1
    unfold negative
    omega

private theorem next_lead (hdeg : ∀ v, 3 ≤ deg v) (hshort : ShortImpossible (deg := deg) bad)
    (a : ↥(marks deg)) (he : ¬ eligible (deg := deg) bad a)
    (hn : negative bad a ≤ (if lead bad a then 1 else 0)) :
    lead bad (CyclicGap.nextMark (marks deg) a) := by
  by_contra hnext
  let B := (Finset.range (CyclicGap.length a)).filter fun i => bad (x a i)
  let H := (Finset.range (CyclicGap.length a)).filter fun i => 5 ≤ deg (x a i)
  change B.card + H.card ≤ _ at hn
  have low_or_first : B.card + H.card = 0 ∨
      (0 ∈ B ∧ B.card + H.card ≤ 1) ∨ (1 ∈ H ∧ B.card + H.card ≤ 1) := by
    by_cases hl : lead bad a
    · rw [if_pos hl] at hn
      obtain ⟨hd, hb | hh⟩ := hl
      · exact Or.inr (Or.inl ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), by simpa only [x_zero] using hb⟩, hn⟩)
      · exact Or.inr (Or.inr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hh⟩, hn⟩)
    · rw [if_neg hl] at hn
      exact Or.inl (by omega)
  have good : ∀ i, 1 ≤ i → i < CyclicGap.length a → ¬ bad (x a i) := by
    intro i hi hd hb
    have hm : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd, hb⟩
    have hB := one_le_card_of_mem hm
    rcases low_or_first with hz | ⟨h0, ht⟩ | ⟨h1, ht⟩
    · omega
    · have := two_le_card_of_mem h0 hm (by omega)
      omega
    · have := one_le_card_of_mem h1
      omega
  have four : ∀ i, 2 ≤ i → i < CyclicGap.length a → deg (x a i) = 4 := by
    intro i hi hd
    have h3 : deg (x a i) ≠ 3 := by
      intro h
      exact CyclicGap.interior_unmarked a (by omega : 0 < i) hd
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hlow := hdeg (x a i)
    by_contra h4
    have hm : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd, by omega⟩
    have hH := one_le_card_of_mem hm
    rcases low_or_first with hz | ⟨h0, ht⟩ | ⟨h1, ht⟩
    · omega
    · have := one_le_card_of_mem h0
      omega
    · have := two_le_card_of_mem h1 hm (by omega)
      omega
  have hfirst (hd : CyclicGap.length a = 1) : ¬ bad a.val := by
    have hl : ¬ lead bad a := fun h => by have := h.1; omega
    rw [if_neg hl] at hn
    intro hb
    have hm : 0 ∈ B := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by simpa only [x_zero] using hb⟩
    have := one_le_card_of_mem hm
    omega
  have hd : CyclicGap.length a ≤ 14 := by
    by_contra hd
    exact he ⟨by omega, four, good, hnext⟩
  exact hshort a hd hnext four good hfirst

private noncomputable def gapEquiv (hm : (marks deg).Nonempty) :
    (Σ a : ↥(marks deg), Fin (CyclicGap.length a)) ≃ Fin n :=
  Equiv.ofBijective (fun p => x p.1 p.2.val) (by
    constructor
    · rintro ⟨a, i⟩ ⟨b, j⟩ h
      obtain ⟨q, _, uniq⟩ := CyclicGap.existsUnique_representation hm (x b j.val)
      have e : (a, i.val) = (b, j.val) :=
        (uniq (a, i.val) ⟨i.isLt, h⟩).trans (uniq (b, j.val) ⟨j.isLt, rfl⟩).symm
      have e₁ := congrArg Prod.fst e
      dsimp at e₁
      subst b
      have e₂ : i = j := Fin.ext (congrArg Prod.snd e)
      subst j
      rfl
    · intro v
      obtain ⟨⟨a, i⟩, ⟨hi, hx⟩, _⟩ := CyclicGap.existsUnique_representation hm v
      exact ⟨⟨a, ⟨i, hi⟩⟩, hx⟩)

private theorem sum_gap_filter (hm : (marks deg).Nonempty) (p : Fin n → Prop)
    [DecidablePred p] :
    (∑ a : ↥(marks deg), ((Finset.range (CyclicGap.length a)).filter
      fun i => p (x a i)).card) = (Finset.univ.filter p).card := by
  calc
    _ = ∑ a : ↥(marks deg), ∑ i : Fin (CyclicGap.length a),
        (if p (x a i.val) then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _
      have hsum :
          (∑ i : Fin (CyclicGap.length a), (if p (x a i.val) then 1 else 0 : ℕ)) =
            ∑ i ∈ Finset.range (CyclicGap.length a), (if p (x a i) then 1 else 0 : ℕ) := by
        exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (if p (x a i) then 1 else 0 : ℕ))
          (CyclicGap.length a)
      rw [hsum, ← Finset.sum_filter]
      simp
    _ = ∑ q : (Σ a : ↥(marks deg), Fin (CyclicGap.length a)),
        (if p (x q.1 q.2.val) then 1 else 0 : ℕ) := by rw [Fintype.sum_sigma]
    _ = ∑ v : Fin n, (if p v then 1 else 0 : ℕ) :=
      Equiv.sum_comp (gapEquiv hm) (fun v => if p v then 1 else 0)
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem sum_negative (hm : (marks deg).Nonempty) :
    (∑ a : ↥(marks deg), negative bad a) =
      (Finset.univ.filter bad).card + (Finset.univ.filter fun v => 5 ≤ deg v).card := by
  unfold negative
  rw [Finset.sum_add_distrib, sum_gap_filter (deg := deg) hm bad]
  exact congrArg ((Finset.univ.filter bad).card + ·)
    (sum_gap_filter (deg := deg) hm (fun v => 5 ≤ deg v))

theorem exists_eligible_not_bent (hdeg : ∀ v, 3 ≤ deg v)
    (hshort : ShortImpossible (deg := deg) bad) (bent : ↥(marks deg) → Prop)
    (budget : (Finset.univ.filter bad).card + (Finset.univ.filter fun v => 5 ≤ deg v).card +
      (Finset.univ.filter bent).card + 6 ≤ (marks deg).card) :
    ∃ a, eligible (deg := deg) bad a ∧ ¬ bent a := by
  have hm : (marks deg).Nonempty := Finset.card_pos.mp (by omega)
  rcases (em (∃ a, eligible (deg := deg) bad a ∧ ¬ bent a)) with h | h
  · exact h
  let b : ↥(marks deg) → Prop := fun a => bent a ∧ eligible (deg := deg) bad a
  have hb : (∑ a : ↥(marks deg), if b a then 1 else 0 : ℕ) ≤ (Finset.univ.filter bent).card := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    exact Finset.card_le_card (fun a ha => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩)
  have hbud : (∑ a : ↥(marks deg), negative bad a) +
      (∑ a : ↥(marks deg), if b a then 1 else 0 : ℕ) + 6 ≤ Fintype.card ↥(marks deg) := by
    rw [sum_negative (deg := deg) bad hm, Fintype.card_coe]
    omega
  obtain ⟨a, he, hb'⟩ := Swanepoel.arc_charges (CyclicGap.nextMark (marks deg))
    (negative bad) (eligible (deg := deg) bad) (lead bad) b (lead_negative bad) (next_lead bad hdeg hshort)
    (fun _ ha => ha.2) hbud
  exact False.elim (h ⟨a, he, fun hc => hb' ⟨hc, he⟩⟩)

end

end Swanepoel.ArcExtract

open scoped BigOperators

namespace Swanepoel

theorem boundary_budget {B A : Type*} [Fintype B] [DecidableEq B]
    [Fintype A] [DecidableEq A] (next : Equiv.Perm B) (deg : B → ℕ)
    (surplus left right : B → ℝ) (bad : B → Prop) [DecidablePred bad]
    (bend : A → Finset B) (hdeg : ∀ v, 3 ≤ deg v)
    (hl : ∀ v, 0 ≤ left v) (hr : ∀ v, 0 ≤ right v)
    (hs : ∀ v, left v + right v ≤ surplus v)
    (hbad : ∀ i, bad i → Real.pi / 3 ≤ left i + right (next i))
    (hdisj : ∀ a b, a ≠ b → Disjoint (bend a) (bend b))
    (hbend : ∀ a, Real.pi / 3 ≤ ∑ v ∈ bend a, surplus v)
    (hzero : ∀ a v, v ∈ bend a → left v + right v = 0)
    (hangle : (∑ v, (((deg v : ℝ) - 1) * (Real.pi / 3) + surplus v)) ≤
      ((Fintype.card B : ℝ) - 2) * Real.pi) :
    (Finset.univ.filter bad).card + (Finset.univ.filter fun v => 5 ≤ deg v).card +
      Fintype.card A + 6 ≤ (Finset.univ.filter fun v => deg v = 3).card := by
  classical
  let k : ℝ := Real.pi / 3
  have hk : 0 < k := div_pos Real.pi_pos (by norm_num)
  let E := Finset.univ.filter bad
  let U := (Finset.univ : Finset A).biUnion bend
  have hE : (E.card : ℝ) * k ≤ ∑ v, (left v + right v) := calc
    (E.card : ℝ) * k = ∑ _v ∈ E, k := by simp [nsmul_eq_mul]
    _ ≤ ∑ v ∈ E, (left v + right (next v)) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hbad v (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v, (left v + right (next v)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun v _ _ => add_nonneg (hl v) (hr (next v)))
    _ = ∑ v, (left v + right v) := by
      simp only [Finset.sum_add_distrib, Equiv.sum_comp next right]
  have hU : (Fintype.card A : ℝ) * k ≤ ∑ v ∈ U, surplus v := calc
    (Fintype.card A : ℝ) * k = ∑ _a : A, k := by simp [nsmul_eq_mul]
    _ ≤ ∑ a, ∑ v ∈ bend a, surplus v := Finset.sum_le_sum fun a _ => hbend a
    _ = ∑ v ∈ U, surplus v := by
      symm
      dsimp only [U]
      rw [Finset.sum_biUnion]
      intro a _ b _ hab
      exact hdisj a b hab
  have hfilter : (Finset.univ.filter fun v => v ∈ U) = U := by
    ext v
    simp
  have hsum : (∑ v, (left v + right v)) + (∑ v ∈ U, surplus v) ≤ ∑ v, surplus v := by
    rw [← hfilter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v ∈ U
    · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hv
      simp [hv, hzero a v ha]
    · simpa [hv] using hs v
  have hcharges := (add_le_add hE hU).trans hsum
  let H := Finset.univ.filter fun v => 5 ≤ deg v
  let L := Finset.univ.filter fun v => deg v = 3
  have hH : (∑ v : B, if 5 ≤ deg v then (1 : ℝ) else 0) = (H.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [H]
  have hL : (∑ v : B, if deg v = 3 then (1 : ℝ) else 0) = (L.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [L]
  have hcoeff : 3 * (Fintype.card B : ℝ) + H.card - L.card ≤ ∑ v, ((deg v : ℝ) - 1) := calc
    _ = ∑ v : B, (3 + (if 5 ≤ deg v then (1 : ℝ) else 0) - (if deg v = 3 then 1 else 0)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hH, hL]
      simp [nsmul_eq_mul, mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : deg v = 3
      · norm_num [hv]
      · by_cases hh : 5 ≤ deg v
        · have h5 : (5 : ℝ) ≤ deg v := by exact_mod_cast hh
          simp only [hv, hh, if_true, if_false]
          linarith
        · have h4 : deg v = 4 := by have := hdeg v; omega
          norm_num [h4]
  have hscaled := mul_le_mul_of_nonneg_right hcoeff hk.le
  have hbudget := hangle
  change (∑ v, (((deg v : ℝ) - 1) * k + surplus v)) ≤ _ at hbudget
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hbudget
  have hpi : Real.pi = 3 * k := by dsimp [k]; ring
  rw [hpi] at hbudget
  have hresult : ((E.card : ℝ) + H.card + Fintype.card A + 6) * k ≤ (L.card : ℝ) * k := by
    linarith only [hcharges, hscaled, hbudget]
  have hcast := le_of_mul_le_mul_right hresult hk
  change E.card + H.card + Fintype.card A + 6 ≤ L.card
  exact_mod_cast hcast

end Swanepoel

namespace Swanepoel

variable {n : ℕ}

open Swanepoel.ArcExtract
open scoped BigOperators Classical

variable {deg : Fin n → ℕ}

theorem arc_step (a : ↥(marks deg)) (i : ℕ) :
    finRotate n (x a i) = x a (i + 1) := by
  change finRotate n ((finRotate n ^ i) a.val) = (finRotate n ^ (i + 1)) a.val
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem arc_halfOpen_injective {a b : ↥(marks deg)} {i j : ℕ}
    (hi : i < CyclicGap.length a) (hj : j < CyclicGap.length b)
    (h : x a i = x b j) : (a, i) = (b, j) := by
  obtain ⟨p, _, hp⟩ := CyclicGap.existsUnique_representation ⟨a.val, a.property⟩ (x b j)
  exact (hp (a, i) ⟨hi, h⟩).trans (hp (b, j) ⟨hj, rfl⟩).symm

noncomputable def arcBendVertices (a : ↥(marks deg)) : Finset (Fin n) :=
  (Finset.Ico 2 (CyclicGap.length a)).image (x a)

theorem arcBendVertices_disjoint {a b : ↥(marks deg)} (hab : a ≠ b) :
    Disjoint (arcBendVertices a) (arcBendVertices b) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
  obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hw
  exact hab (congrArg Prod.fst (arc_halfOpen_injective (Finset.mem_Ico.mp hi).2
    (Finset.mem_Ico.mp hj).2 (hiv.trans hjv.symm)))

theorem arcBend_position {bad : Fin n → Prop} {a : ↥(marks deg)}
    (he : eligible bad a) {i : ℕ} (hi : 2 ≤ i) (hid : i < CyclicGap.length a) :
    deg (x a i) = 4 ∧ ¬ bad (x a (i - 1)) ∧ ¬ bad (x a i) :=
  ⟨he.2.1 i hi hid, he.2.2.1 (i - 1) (by omega) (by omega),
    he.2.2.1 i (by omega) hid⟩

theorem arcBendVertices_good {bad : Fin n → Prop} {a : ↥(marks deg)}
    (he : eligible bad a) {v : Fin n} (hv : v ∈ arcBendVertices a) :
    deg v = 4 ∧ ¬ bad ((finRotate n).symm v) ∧ ¬ bad v := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
  have hstep : finRotate n (x a (i - 1)) = x a i := by
    rw [arc_step, show i - 1 + 1 = i by omega]
  have hprev : (finRotate n).symm (x a i) = x a (i - 1) := by
    rw [← hstep, Equiv.symm_apply_apply]
  rw [hprev]
  exact arcBend_position he hlo hhi

noncomputable def arcBendCost (surplus : Fin n → ℝ) (a : ↥(marks deg)) : ℝ :=
  ∑ v ∈ arcBendVertices a, surplus v

theorem arcBendCost_eq_sum (surplus : Fin n → ℝ) (a : ↥(marks deg)) :
    arcBendCost surplus a = ∑ i ∈ Finset.Ico 2 (CyclicGap.length a), surplus (x a i) := by
  unfold arcBendCost arcBendVertices
  apply Finset.sum_image
  intro i hi j hj h
  exact congrArg Prod.snd (arc_halfOpen_injective (Finset.mem_Ico.mp hi).2
    (Finset.mem_Ico.mp hj).2 h)

def arcBent (deg : Fin n → ℕ) (bad : Fin n → Prop) (surplus : Fin n → ℝ)
    (a : ↥(marks deg)) : Prop := eligible bad a ∧ Real.pi / 3 ≤ arcBendCost surplus a

theorem exists_eligible_low_bend (deg : Fin n → ℕ) (bad : Fin n → Prop)
    (surplus left right : Fin n → ℝ) (hdeg : ∀ v, 3 ≤ deg v)
    (hshort : ShortImpossible (deg := deg) bad)
    (hl : ∀ v, 0 ≤ left v) (hr : ∀ v, 0 ≤ right v)
    (hs : ∀ v, left v + right v ≤ surplus v)
    (hleft : ∀ v, ¬ bad v → left v = 0)
    (hright : ∀ v, ¬ bad v → right (finRotate n v) = 0)
    (hbad : ∀ v, bad v → Real.pi / 3 ≤ left v + right (finRotate n v))
    (hangle : (∑ v, (((deg v : ℝ) - 1) * (Real.pi / 3) + surplus v)) ≤
      ((n : ℝ) - 2) * Real.pi) :
    ∃ a : ↥(marks deg), eligible bad a ∧ arcBendCost surplus a < Real.pi / 3 := by
  classical
  let B := (Finset.univ : Finset ↥(marks deg)).filter (arcBent deg bad surplus)
  have hb (a : ↥B) : arcBent deg bad surplus a.val := (Finset.mem_filter.mp a.property).2
  have hbudget := Swanepoel.boundary_budget (A := ↥B) (finRotate n) deg surplus left right bad
    (fun a => arcBendVertices a.val) hdeg hl hr hs hbad
    (fun a b hab => arcBendVertices_disjoint (fun h => hab (Subtype.ext h)))
    (fun a => (hb a).2)
    (fun a v hv => by
      obtain ⟨_, hin, hout⟩ := arcBendVertices_good (hb a).1 hv
      have hr0 := hright ((finRotate n).symm v) hin
      rw [Equiv.apply_symm_apply] at hr0
      rw [hleft v hout, hr0, add_zero])
    (by simpa only [Fintype.card_fin] using hangle)
  rw [Fintype.card_coe] at hbudget
  obtain ⟨a, he, hn⟩ := exists_eligible_not_bent bad hdeg hshort (arcBent deg bad surplus)
    (by simpa only [B, marks] using hbudget)
  exact ⟨a, he, lt_of_not_ge (fun hc => hn ⟨he, hc⟩)⟩

theorem arc_right_suffix {bad : Fin n → Prop} {a : ↥(marks deg)}
    (he : eligible bad a) {j : ℕ} (hj : j < 13) :
    let i := CyclicGap.length a - 13 + j
    deg (x a i) = 4 ∧ ¬ bad (x a (i - 1)) ∧ ¬ bad (x a i) := by
  dsimp only
  have hd := he.1
  exact arcBend_position he (by omega) (by omega)

theorem arc_right_suffix_turn_budget {bad : Fin n → Prop} {a : ↥(marks deg)}
    (he : eligible bad a) (surplus τ : Fin n → ℝ) (hs : ∀ v, 0 ≤ surplus v)
    (hτ : ∀ v, deg v = 4 → τ v = surplus v)
    (hlow : arcBendCost surplus a < Real.pi / 3) :
    (∑ i ∈ Finset.Ico (CyclicGap.length a - 12) (CyclicGap.length a), τ (x a i)) <
      Real.pi / 3 := by
  have hd := he.1
  rw [arcBendCost_eq_sum] at hlow
  apply lt_of_le_of_lt _ hlow
  calc
    _ = ∑ i ∈ Finset.Ico (CyclicGap.length a - 12) (CyclicGap.length a), surplus (x a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
      exact hτ _ (he.2.1 i (by omega) hhi)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
      exact Finset.mem_Ico.mpr ⟨by omega, hhi⟩) (fun i _ _ => hs (x a i))

theorem arc_nextMark_degree (a : ↥(marks deg)) :
    deg (x a (CyclicGap.length a)) = 3 := by
  change deg (CyclicGap.nextMark (marks deg) a).val = 3
  exact (Finset.mem_filter.mp (CyclicGap.nextMark (marks deg) a).property).2

theorem arc_no_lead_step {bad : Fin n → Prop} (hdeg : ∀ v, 3 ≤ deg v)
    {a : ↥(marks deg)} (hn : ¬ lead bad a) :
    (CyclicGap.length a = 1 ∧ deg (x a 1) = 3) ∨
      (2 ≤ CyclicGap.length a ∧ ¬ bad a.val ∧ deg (x a 1) = 4) := by
  by_cases h : 2 ≤ CyclicGap.length a
  · have hnot3 : deg (x a 1) ≠ 3 := fun h3 =>
      CyclicGap.interior_unmarked a (by decide : 0 < (1 : ℕ)) (by omega)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
    have hnot5 : ¬ 5 ≤ deg (x a 1) := fun h5 => hn ⟨h, Or.inr h5⟩
    have hlo := hdeg (x a 1)
    exact Or.inr ⟨h, fun hb => hn ⟨h, Or.inl hb⟩, by omega⟩
  · have hpos := CyclicGap.length_pos a
    have hone : CyclicGap.length a = 1 := by omega
    exact Or.inl ⟨hone, by simpa only [hone] using arc_nextMark_degree a⟩

theorem arc_eligible_next_step {bad : Fin n → Prop} (hdeg : ∀ v, 3 ≤ deg v)
    {a : ↥(marks deg)} (he : eligible bad a) :
    let b := CyclicGap.nextMark (marks deg) a
    (CyclicGap.length b = 1 ∧ deg (x b 1) = 3) ∨
      (2 ≤ CyclicGap.length b ∧ ¬ bad b.val ∧ deg (x b 1) = 4) :=
  arc_no_lead_step hdeg he.2.2.2

end Swanepoel

namespace Swanepoel

open scoped Classical

private theorem shortGap_end_lt {n : ℕ} {M : Finset (Fin n)}
    (hM : 6 ≤ M.card) (a : ↥M) : CyclicGap.length a + 1 < n := by
  let d := CyclicGap.length a
  let f : ℕ → Fin n := fun i => (finRotate n ^ (i + 1)) a.val
  let U := (Finset.range (d - 1)).image f
  have hint : ∀ i ∈ Finset.range (d - 1), i + 1 < d := by
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  have hinj : Set.InjOn f ↑(Finset.range (d - 1)) := by
    intro i hi j hj hij
    obtain ⟨p, _, hp⟩ := CyclicGap.existsUnique_representation ⟨a.val, a.property⟩ (f j)
    have hi' := hp (a, i + 1) ⟨hint i (Finset.mem_coe.mp hi), hij⟩
    have hj' := hp (a, j + 1) ⟨hint j (Finset.mem_coe.mp hj), rfl⟩
    have he := congrArg Prod.snd (hi'.trans hj'.symm)
    change i + 1 = j + 1 at he
    omega
  have hc : U.card = d - 1 := by
    change ((Finset.range (d - 1)).image f).card = d - 1
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hdisj : Disjoint U M := by
    apply Finset.disjoint_left.mpr
    intro z hz hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact CyclicGap.interior_unmarked a (by omega : 0 < i + 1) (hint i hi) hm
  have hcard := Finset.card_le_card (Finset.subset_univ (U ∪ M))
  rw [Finset.card_union_of_disjoint hdisj, hc, Finset.card_univ, Fintype.card_fin] at hcard
  change d + 1 < n
  omega

private theorem shortGap_two_le {V : Type*} [DecidableEq V] {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) : 2 ≤ S.card := by
  have hs : ({u, v} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  simpa [hne] using Finset.card_le_card hs

theorem shortImpossible {V : Type*} [DecidableEq V] {n : ℕ}
    (X : Finset V) (b : Fin n ↪ V) (E : V → V → Prop) (N : V → Finset V)
    (deg : Fin n → ℕ) (bad : Fin n → Prop) (hX : ∀ i, b i ∈ X)
    (hsymm : Symmetric E) (hirr : Irreflexive E)
    (hstep : ∀ i, E (b i) (b (finRotate n i)))
    (hmem : ∀ i y, E (b i) y → y ∈ N (b i))
    (hcard : ∀ i, (N (b i)).card = deg i) (hmin : ∀ i, 3 ≤ deg i)
    (hmarks : 6 ≤ (ArcExtract.marks deg).card)
    (htip : ∀ i, ¬ bad i → ∃ z, E (b i) z ∧ E (b (finRotate n i)) z)
    (no_chord : ∀ (a : Fin n) (i j : ℕ), i < j → j < n → (j - i) % 2 = 0 →
      (∀ u v : ℕ, i < u → u < j → i < v → v < j →
        deg ((finRotate n ^ u) a) < 4 → deg ((finRotate n ^ v) a) < 4 → u = v) →
      ¬ E (b ((finRotate n ^ i) a)) (b ((finRotate n ^ j) a)))
    (hexpand : ∀ S : Finset V, S ⊆ X → (S : Set V).Pairwise (fun x y => ¬ E x y) →
      S.card ≤ 8 → 4 * S.card ≤ (X.filter fun x => x ∈ S ∨ ∃ y ∈ S, E y x).card) :
    ArcExtract.ShortImpossible (deg := deg) bad := by
  intro a hd14 hnlead hfour hgood hfirst
  let d := CyclicGap.length a
  let r := (d + 1) / 2
  let a' := CyclicGap.nextMark (ArcExtract.marks deg) a
  let q : ℕ → Fin n := ArcExtract.x a
  let v : ℕ → V := fun i => b (q i)
  let p : ℕ → V := fun i => v (2 * i)
  change d ≤ 14 at hd14
  have hd : 0 < d := CyclicGap.length_pos a
  have hr : 0 < r := by dsimp only [r]; omega
  have hr8 : r + 1 ≤ 8 := by dsimp only [r]; omega
  have hrend : d ≤ 2 * r ∧ 2 * r ≤ d + 1 := by dsimp only [r]; omega
  have hbound : d + 1 < n := shortGap_end_lt hmarks a
  have hqnext (i : ℕ) : q (i + 1) = finRotate n (q i) := by
    change (finRotate n ^ (i + 1)) a.val = finRotate n ((finRotate n ^ i) a.val)
    rw [pow_succ', Equiv.Perm.mul_apply]
  have hqshift (i : ℕ) : q (d + i) = ArcExtract.x a' i := by
    change (finRotate n ^ (d + i)) a.val = (finRotate n ^ i) a'.val
    rw [Nat.add_comm d i, pow_add, Equiv.Perm.mul_apply, CyclicGap.nextMark_apply a]
  have hvstep (i : ℕ) : E (v i) (v (i + 1)) := by
    change E (b (q i)) (b (q (i + 1)))
    rw [hqnext]
    exact hstep _
  have hvtip (i : ℕ) (hi : ¬ bad (q i)) : ∃ z, E (v i) z ∧ E (v (i + 1)) z := by
    change ∃ z, E (b (q i)) z ∧ E (b (q (i + 1))) z
    rw [hqnext]
    exact htip _ hi
  have marked3 (c : ↥(ArcExtract.marks deg)) : deg c.val = 3 :=
    (Finset.mem_filter.mp c.property).2
  have head3 : deg (q 0) = 3 := by simpa [q, ArcExtract.x] using marked3 a
  have gap3 : deg (q d) = 3 := by
    have he : q d = a'.val := CyclicGap.nextMark_apply a
    rw [he]
    exact marked3 a'
  have interior4 (i : ℕ) (hi : 0 < i) (hid : i < d) : 4 ≤ deg (q i) := by
    have hne : deg (q i) ≠ 3 := fun he =>
      CyclicGap.interior_unmarked a hi hid (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    have := hmin (q i)
    omega
  have hlow (i : ℕ) (hi : 0 < i) (hir : i < 2 * r) (hl : deg (q i) < 4) : i = d := by
    by_contra hne
    have := interior4 i hi (by omega)
    omega
  have hv_inj {i j : ℕ} (hi : i ≤ d + 1) (hj : j ≤ d + 1) (h : v i = v j) : i = j := by
    let emb := chordIndices (m := d + 2) (by omega : d + 2 ≤ n) a.val
    have he : emb ⟨i, by omega⟩ = emb ⟨j, by omega⟩ := b.injective h
    exact congrArg Fin.val (emb.injective he)
  have hind_lt (i j : ℕ) (hij : i < j) (hj : j ≤ r) : ¬ E (p i) (p j) := by
    apply no_chord a.val (2 * i) (2 * j) (by omega) (by omega) (by omega)
    intro u w hiu hu hiw hw hlu hlw
    exact (hlow u (by omega) (by omega) hlu).trans (hlow w (by omega) (by omega) hlw).symm
  have hind (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ r) (hne : i ≠ j) : ¬ E (p i) (p j) := by
    intro he
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hind_lt i j hij hj he
    · exact hind_lt j i hji hi (hsymm he)
  have overlap (i : ℕ) : v (2 * i + 1) ∈ N (p i) ∩ N (p (i + 1)) := by
    apply Finset.mem_inter.mpr
    refine ⟨hmem _ _ (hvstep (2 * i)), hmem _ _ (hsymm ?_)⟩
    simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using hvstep (2 * i + 1)
  have htail : deg (q (2 * r)) ≤ 3 ∨
      (deg (q (2 * r)) = 4 ∧ 2 ≤ (N (p (r - 1)) ∩ N (p r)).card) := by
    by_cases heven : 2 * r = d
    · left
      rw [heven, gap3]
    have hodd : 2 * r = d + 1 := by omega
    have hshift : q (d + 1) = ArcExtract.x a' 1 := hqshift 1
    have hd' := CyclicGap.length_pos a'
    by_cases hone : CyclicGap.length a' = 1
    · left
      rw [hodd, hshift, ← hone]
      have he : ArcExtract.x a' (CyclicGap.length a') = (CyclicGap.nextMark _ a').val :=
        CyclicGap.nextMark_apply a'
      rw [he]
      exact le_of_eq (marked3 ((CyclicGap.nextMark _ ) a'))
    have hlong : 2 ≤ CyclicGap.length a' := by omega
    have hgood' : ¬ bad a'.val := fun hb => hnlead ⟨hlong, Or.inl hb⟩
    have hnot5 : ¬ 5 ≤ deg (ArcExtract.x a' 1) := fun h => hnlead ⟨hlong, Or.inr h⟩
    have hnot3 : deg (ArcExtract.x a' 1) ≠ 3 := fun h =>
      CyclicGap.interior_unmarked a' (by omega : 0 < (1 : ℕ)) (by omega)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hfour' : deg (ArcExtract.x a' 1) = 4 := by
      have := hmin (ArcExtract.x a' 1)
      omega
    right
    refine ⟨by rw [hodd, hshift, hfour'], ?_⟩
    have hd0 : 2 * (r - 1) = d - 1 := by omega
    have hprev : d - 1 + 1 = d := by omega
    have hmark : q d = a'.val := CyclicGap.nextMark_apply a
    have hleft : ¬ bad (q (d - 1)) := by
      by_cases h : d = 1
      · simpa [h, q, ArcExtract.x] using hfirst h
      · exact hgood _ (by omega) (by omega)
    obtain ⟨z, hlz, hmz⟩ := hvtip (d - 1) hleft
    rw [hprev] at hmz
    obtain ⟨w, hmw, hrw⟩ := hvtip d (hmark ▸ hgood' : ¬ bad (q d))
    have hends : ¬ E (v (d - 1)) (v (d + 1)) := by
      simpa only [p, hd0, hodd] using hind_lt (r - 1) r (by omega) le_rfl
    have hab : v (d - 1) ≠ v (d + 1) := fun h => by
      have := hv_inj (by omega) (by omega) h
      omega
    have haz : v (d - 1) ≠ z := fun h => hirr _ (h ▸ hlz)
    have hbz : v (d + 1) ≠ z := fun h => hends (h.symm ▸ hlz)
    have hwa : w ≠ v (d - 1) := fun h => hends (hsymm (h ▸ hrw))
    have hwb : w ≠ v (d + 1) := fun h => hirr _ (h ▸ hrw)
    have hfull : ({v (d - 1), v (d + 1), z} : Finset V) = N (v d) := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hmem _ _ (hsymm (hprev ▸ hvstep (d - 1)))
        · exact hmem _ _ (hvstep d)
        · exact hmem _ _ hmz
      · change (N (b (q d))).card ≤ _
        rw [hcard, gap3]
        simp [hab, haz, hbz]
    have hw : w ∈ ({v (d - 1), v (d + 1), z} : Finset V) := hfull.symm ▸ hmem _ _ hmw
    have hwz : w = z := by simpa [hwa, hwb] using hw
    subst w
    have hmiddle : v d ∈ N (p (r - 1)) ∩ N (p r) := by
      simpa only [p, hd0, hprev, Nat.sub_add_cancel (show 1 ≤ r by omega)] using overlap (r - 1)
    have hcommon : z ∈ N (p (r - 1)) ∩ N (p r) := by
      simpa only [p, hd0, hodd] using Finset.mem_inter.mpr ⟨hmem _ _ hlz, hmem _ _ hrw⟩
    exact shortGap_two_le hmiddle hcommon (fun h => hirr _ (h ▸ hmz))
  apply alternating_gap_contradiction X E p (fun i => N (p i)) r hr hr8 ?_ ?_ hind ?_ ?_ ?_ ?_ ?_ hexpand
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    have hh : 2 * i = 2 * j := hv_inj (by omega) (by omega) he
    omega
  · intro i _
    exact hX (q (2 * i))
  · intro i _ y _ he
    exact hmem (q (2 * i)) y he
  · intro i hi
    change (N (b (q (2 * i)))).card ≤ 4
    rw [hcard]
    by_cases hz : i = 0
    · simpa [hz, head3]
    by_cases ht : i = r
    · subst i
      rcases htail with ht | ⟨ht, _⟩ <;> omega
    have hdi : 2 * i < d := by omega
    rw [hfour _ (by omega) hdi]
  · change (N (b (q (2 * 0)))).card ≤ 3
    simpa [hcard, head3]
  · intro i _
    exact Finset.card_pos.mpr ⟨_, overlap i⟩
  · rcases htail with ht | ⟨_, ht⟩
    · exact Or.inl (by change (N (b (q (2 * r)))).card ≤ 3; rwa [hcard])
    · exact Or.inr ht

end Swanepoel

namespace Swanepoel.TipIndependence

noncomputable section

private def cis (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

def w : ℂ := cis (Real.pi / 3)

private theorem cis_add (a b : ℝ) : cis (a + b) = cis a * cis b := by
  rw [cis, cis, cis, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem cis_im (a : ℝ) : (cis a).im = Real.sin a :=
  Complex.exp_ofReal_mul_I_im a

private theorem one_sub_w : 1 - w = cis (-(Real.pi / 3)) := by
  apply Complex.ext
  · simp only [w, cis, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Real.cos_neg, Real.cos_pi_div_three]
    norm_num
  · simp [w, cis_im, Complex.sub_im, Real.sin_neg]

theorem middleNorm_of_angles {a b : ℝ} (hba : b ≤ a) (hturn : a - b < Real.pi / 3) :
    1 < ‖w * Complex.exp ((b : ℂ) * Complex.I) -
      (1 - w) * Complex.exp ((a : ℂ) * Complex.I)‖ := by
  change 1 < ‖w * cis b - (1 - w) * cis a‖
  let x := Real.pi / 3 - (a - b) / 2
  let m := (a + b) / 2
  have hp := Real.pi_pos
  have ha : -(Real.pi / 3) + a = -x + m := by dsimp [x, m]; ring
  have hb : Real.pi / 3 + b = x + m := by dsimp [x, m]; ring
  have hn : ‖cis m‖ = 1 := by
    simp [cis, Complex.norm_exp, Complex.mul_re]
  rw [one_sub_w, w, ← cis_add, ← cis_add, hb, ha, cis_add x m, cis_add (-x) m,
    ← sub_mul, norm_mul, hn, mul_one]
  have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := Real.pi / 6) (y := x) (by linarith) (by dsimp [x]; linarith)
    (by dsimp [x]; linarith)
  rw [Real.sin_pi_div_six] at hs
  have him : 1 < (cis x - cis (-x)).im := by
    rw [Complex.sub_im, cis_im, cis_im, Real.sin_neg]
    linarith
  exact him.trans_le ((le_abs_self _).trans (Complex.abs_im_le_norm _))

structure Arc where
  p : ℕ → ℂ
  h : ℕ → ℂ
  step : ∀ i, p (i + 1) - p i = h i
  unit : ∀ i, ‖h i‖ = 1
  heading_re : ∀ i, Real.sqrt 3 / 2 ≤ (h i).re
  left_re : ∀ i, 0 ≤ (w * h i).re
  right_re : ∀ i, 0 ≤ ((1 - w) * h i).re
  pair_re : ∀ i j, i ≤ j → Real.sqrt 3 / 2 ≤ ((1 - w) * h i + w * h j).re
  middleNorm : ∀ i, 1 < ‖w * h (i + 1) - (1 - w) * h i‖

namespace Arc

variable (A : Arc)

def q (i : ℕ) : ℂ := A.p i + w * A.h i

def z (i : ℕ) : ℂ := A.p i + w * (A.h i + A.h (i + 1))

theorem z_eq_q_add_q_sub_p (i : ℕ) : A.z i = A.q i + A.q (i + 1) - A.p (i + 1) := by
  unfold z q
  rw [mul_add]
  ring

private theorem one_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by
  simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)

private theorem step_re (i : ℕ) : (A.p (i + 1)).re - (A.p i).re = (A.h i).re := by
  simpa only [Complex.sub_re] using congrArg Complex.re (A.step i)

private theorem split_re (i : ℕ) :
    ((1 - w) * A.h i).re + (w * A.h i).re = (A.h i).re := by
  rw [← Complex.add_re, ← add_mul, sub_add_cancel, one_mul]

private theorem pair_re' (i j : ℕ) (hij : i ≤ j) :
    Real.sqrt 3 / 2 ≤ ((1 - w) * A.h i).re + (w * A.h j).re := by
  simpa only [Complex.add_re] using A.pair_re i j hij

private theorem monotone_re : Monotone (fun i => (A.p i).re) := by
  apply monotone_nat_of_le_succ
  intro i
  linarith only [one_lt_sqrt_three, A.step_re i, A.heading_re i]

private theorem two_step_re {i j : ℕ} (hij : i + 2 ≤ j) :
    Real.sqrt 3 ≤ (A.p j).re - (A.p i).re := by
  have h := A.monotone_re hij
  change (A.p (i + 2)).re ≤ (A.p j).re at h
  linarith only [h, A.step_re i, A.step_re (i + 1), A.heading_re i, A.heading_re (i + 1)]

private theorem one_lt_dist_of_re {u v : ℂ} (h : 1 < v.re - u.re) : 1 < dist u v := by
  rw [dist_comm, dist_eq_norm]
  rw [← Complex.sub_re] at h
  exact h.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm _))

theorem dist_p_p {i j : ℕ} (hij : i + 2 ≤ j) : 1 < dist (A.p i) (A.p j) :=
  one_lt_dist_of_re (one_lt_sqrt_three.trans_le (A.two_step_re hij))

theorem dist_q_p_before {i j : ℕ} (hji : j + 2 ≤ i) : 1 < dist (A.q i) (A.p j) := by
  rw [dist_comm]
  apply one_lt_dist_of_re
  simp only [q, Complex.add_re]
  linarith only [one_lt_sqrt_three, A.two_step_re hji, A.left_re i]

theorem dist_q_p_after {i j : ℕ} (hij : i + 3 ≤ j) : 1 < dist (A.q i) (A.p j) := by
  apply one_lt_dist_of_re
  simp only [q, Complex.add_re]
  have ht := A.two_step_re (i := i + 1) (j := j) hij
  linarith only [one_lt_sqrt_three, ht, A.step_re i, A.split_re i, A.right_re i]

theorem dist_q_q_three (i : ℕ) : 1 < dist (A.q i) (A.q (i + 3)) := by
  apply one_lt_dist_of_re
  simp only [q, Complex.add_re]
  have ht := A.two_step_re (i := i + 1) (j := i + 3) (by omega)
  have hp := A.pair_re' i (i + 3) (by omega)
  linarith only [one_lt_sqrt_three, ht, A.step_re i, A.split_re i, hp]

theorem dist_z_p_before {j k : ℕ} (hkj : k + 2 ≤ j) : 1 < dist (A.z j) (A.p k) := by
  rw [dist_comm]
  apply one_lt_dist_of_re
  simp only [z, mul_add, Complex.add_re]
  linarith only [one_lt_sqrt_three, A.two_step_re hkj, A.left_re j, A.left_re (j + 1)]

theorem dist_z_p_after {j k : ℕ} (hjk : j + 4 ≤ k) : 1 < dist (A.z j) (A.p k) := by
  apply one_lt_dist_of_re
  simp only [z, mul_add, Complex.add_re]
  have ht := A.two_step_re (i := j + 2) (j := k) hjk
  linarith only [one_lt_sqrt_three, ht, A.step_re j, A.step_re (j + 1), A.split_re j,
    A.split_re (j + 1), A.right_re j, A.right_re (j + 1)]

theorem dist_z_p_middle (j : ℕ) : 1 < dist (A.z j) (A.p (j + 1)) := by
  rw [dist_eq_norm]
  have hz : A.z j - A.p (j + 1) = w * A.h (j + 1) - (1 - w) * A.h j := by
    unfold z
    have hs := A.step j
    linear_combination -hs
  rw [hz]
  exact A.middleNorm j

theorem z_re_lt_next (j : ℕ) : (A.z j).re < (A.z (j + 1)).re := by
  simp only [z, mul_add, Complex.add_re]
  linarith only [one_lt_sqrt_three, A.step_re j, A.split_re j,
    A.pair_re' j (j + 2) (by omega)]

theorem z_ne_next (j : ℕ) : A.z j ≠ A.z (j + 1) :=
  fun h => (A.z_re_lt_next j).ne (congrArg Complex.re h)

theorem q_re_lt_z_next (i : ℕ) : (A.q i).re < (A.z (i + 1)).re := by
  simp only [q, z, mul_add, Complex.add_re]
  linarith only [one_lt_sqrt_three, A.step_re i, A.split_re i, A.left_re (i + 2),
    A.pair_re' i (i + 1) (by omega)]

theorem z_ne_q_prev (i : ℕ) : A.z (i + 1) ≠ A.q i :=
  fun h => (A.q_re_lt_z_next i).ne (congrArg Complex.re h.symm)

theorem z_re_lt_q_after (j : ℕ) : (A.z j).re < (A.q (j + 2)).re := by
  simp only [q, z, mul_add, Complex.add_re]
  linarith only [one_lt_sqrt_three, A.step_re j, A.step_re (j + 1), A.split_re j,
    A.split_re (j + 1), A.right_re j, A.pair_re' (j + 1) (j + 2) (by omega)]

theorem z_ne_q_after (j : ℕ) : A.z j ≠ A.q (j + 2) :=
  fun h => (A.z_re_lt_q_after j).ne (congrArg Complex.re h)

end Arc
end
end Swanepoel.TipIndependence

namespace Swanepoel.ArcHeading

open Swanepoel.ChainStep
noncomputable section

def turnSum (τ : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range i, τ (j + 1)

@[simp] theorem turnSum_zero (τ : ℕ → ℝ) : turnSum τ 0 = 0 := by
  simp [turnSum]

theorem turnSum_succ (τ : ℕ → ℝ) (i : ℕ) :
    turnSum τ (i + 1) = turnSum τ i + τ (i + 1) := by
  simp only [turnSum, Finset.sum_range_succ]

structure Chain (m : ℕ) where
  p : ℕ → ℂ
  q : ℕ → ℂ
  h : ℕ → ℂ
  τ : ℕ → ℝ
  unit : ‖h 0‖ = 1
  step : ∀ i, i ≤ m → p (i + 1) - p i = h i
  next : ∀ i, i < m → h (i + 1) = h i * cis (-τ (i + 1))
  turn_nonneg : ∀ i, i < m → 0 ≤ τ (i + 1)
  total_lt : turnSum τ m < Real.pi / 3
  tip : ∀ i, i ≤ m → q i = p i + w * h i

namespace Chain

variable {m : ℕ} (C : Chain m)

def θ (i : ℕ) : ℝ := -turnSum C.τ (min i m)

def center : ℝ := turnSum C.τ m / 2

def angle (i : ℕ) : ℝ := C.center + C.θ i

@[simp] theorem θ_zero : C.θ 0 = 0 := by simp [θ]

theorem θ_succ {i : ℕ} (hi : i < m) : C.θ (i + 1) = C.θ i - C.τ (i + 1) := by
  rw [θ, θ, min_eq_left (show i + 1 ≤ m by omega), min_eq_left hi.le, turnSum_succ]
  ring

theorem θ_antitone : Antitone C.θ := by
  apply antitone_nat_of_succ_le
  intro i
  by_cases hi : i < m
  · rw [C.θ_succ hi]
    linarith [C.turn_nonneg i hi]
  · have hm : m ≤ i := by omega
    simp only [θ, min_eq_right hm, min_eq_right (show m ≤ i + 1 by omega), le_refl]

theorem angle_antitone : Antitone C.angle := by
  intro i j hij
  exact add_le_add_right (C.θ_antitone hij) C.center

theorem θ_bounds (i : ℕ) : -turnSum C.τ m ≤ C.θ i ∧ C.θ i ≤ 0 := by
  have hc := C.θ_antitone (min_le_right i m)
  have h0 := C.θ_antitone (Nat.zero_le i)
  have he : C.θ m = -turnSum C.τ m := by simp [θ]
  have hi : C.θ (min i m) = C.θ i := by simp [θ, min_assoc]
  rw [he, hi] at hc
  simpa only [C.θ_zero] using And.intro hc h0

theorem angle_bounds (i : ℕ) : -(Real.pi / 6) ≤ C.angle i ∧ C.angle i ≤ Real.pi / 6 := by
  obtain ⟨hl, hu⟩ := C.θ_bounds i
  unfold angle center
  constructor <;> linarith [C.total_lt]

theorem heading {i : ℕ} (hi : i ≤ m) : C.h i = C.h 0 * cis (C.θ i) := by
  induction i with
  | zero => simp [cis]
  | succ i ih =>
      have him : i < m := by omega
      rw [C.next i him, ih him.le, C.θ_succ him, mul_assoc, ← cis_add, sub_eq_add_neg]

private theorem cis_im (a : ℝ) : (cis a).im = Real.sin a :=
  Complex.exp_ofReal_mul_I_im a

private theorem cis_unit (a : ℝ) : ‖cis a‖ = 1 := by
  simp [cis, Complex.norm_exp, Complex.mul_re]

theorem heading_re {i : ℕ} (hi : i ≤ m) :
    (C.h i).re = (C.h 0).re * Real.cos (C.θ i) - (C.h 0).im * Real.sin (C.θ i) := by
  rw [C.heading hi, Complex.mul_re, cis_re, cis_im]

def rotation (a : ℝ) : ℂ := cis a * (C.h 0)⁻¹

def frame (a : ℝ) (z : ℂ) : ℂ := C.rotation a * (z - C.p 0)

@[simp] theorem frame_initial (a : ℝ) : C.frame a (C.p 0) = 0 := by simp [frame]

theorem frame_sub (a : ℝ) (x y : ℂ) :
    C.frame a x - C.frame a y = C.rotation a * (x - y) := by
  unfold frame
  ring

theorem dist_frame (a : ℝ) (x y : ℂ) : dist (C.frame a x) (C.frame a y) = dist x y := by
  simp only [dist_eq_norm, C.frame_sub, rotation, norm_mul, norm_inv, cis_unit, C.unit,
    inv_one, one_mul]

theorem rotate_heading (a : ℝ) {i : ℕ} (hi : i ≤ m) :
    C.rotation a * C.h i = cis (a + C.θ i) := by
  have hn : C.h 0 ≠ 0 := by
    intro hz
    simpa [hz] using C.unit
  rw [C.heading hi, rotation, cis_add]
  calc
    cis a * (C.h 0)⁻¹ * (C.h 0 * cis (C.θ i)) =
        cis a * cis (C.θ i) * ((C.h 0)⁻¹ * C.h 0) := by ring
    _ = cis a * cis (C.θ i) := by simp [hn]

theorem frame_step (a : ℝ) {i : ℕ} (hi : i ≤ m) :
    C.frame a (C.p (i + 1)) - C.frame a (C.p i) = cis (a + C.θ i) := by
  rw [C.frame_sub, C.step i hi, C.rotate_heading a hi]

theorem frame_tip (a : ℝ) {i : ℕ} (hi : i ≤ m) :
    C.frame a (C.q i) = C.frame a (C.p i) + w * cis (a + C.θ i) := by
  rw [← C.rotate_heading a hi, C.tip i hi]
  unfold frame
  ring

def centeredPath (D : Chain m) : ℕ → ℂ
  | 0 => 0
  | i + 1 => centeredPath D i + cis (D.angle i)

theorem centeredPath_eq {i : ℕ} (hi : i ≤ m + 1) :
    C.centeredPath i = C.frame C.center (C.p i) := by
  induction i with
  | zero => simp [centeredPath]
  | succ i ih =>
      have him : i ≤ m := by omega
      rw [centeredPath, ih (by omega)]
      have hs := C.frame_step C.center him
      change C.frame C.center (C.p (i + 1)) - C.frame C.center (C.p i) = cis (C.angle i) at hs
      linear_combination -hs

def toArc : TipIndependence.Arc where
  p := C.centeredPath
  h i := cis (C.angle i)
  step i := by rw [centeredPath, add_sub_cancel_left]
  unit i := cis_unit _
  heading_re i := by
    rw [cis_re, ← Real.cos_pi_div_six, ← Real.cos_abs (C.angle i)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [Real.pi_pos]) (abs_le.mpr (C.angle_bounds i))
  left_re i := (w_mul_cis_re_bounds (C.angle_bounds i).1 (C.angle_bounds i).2).1
  right_re i := (one_sub_w_mul_cis_re_bounds (C.angle_bounds i).1 (C.angle_bounds i).2).1
  pair_re i j hij := displacement_re_ge (C.angle_bounds j).1 (C.angle_antitone hij)
    (C.angle_bounds i).2
  middleNorm i := by
    apply TipIndependence.middleNorm_of_angles (C.angle_antitone (Nat.le_succ i))
    have hl := (C.θ_bounds (i + 1)).1
    have hu := (C.θ_bounds i).2
    unfold angle
    linarith [C.total_lt]

theorem arc_p {i : ℕ} (hi : i ≤ m + 1) :
    C.toArc.p i = C.frame C.center (C.p i) := C.centeredPath_eq hi

theorem arc_q {i : ℕ} (hi : i ≤ m) :
    C.toArc.q i = C.frame C.center (C.q i) := by
  change C.centeredPath i + w * cis (C.angle i) = C.frame C.center (C.q i)
  rw [C.centeredPath_eq (by omega)]
  exact (C.frame_tip C.center hi).symm

end Chain
end
end Swanepoel.ArcHeading

namespace Swanepoel

theorem lemma8_neighbor_card {V : Type*} [DecidableEq V]
    (N : V → Finset V) (p q : ℕ → V) (U extra : Finset V) (k i : ℕ)
    (_hi : 1 ≤ i) (hU : U.card ≤ 3 * k) (hp : p i ∈ U) (hq : q (i - 1) ∈ U)
    (hdeg : (N (p (i + 2))).card ≤ 4)
    (hp' : p (i + 1) ∈ N (p (i + 2))) (hq' : q (i + 1) ∈ N (p (i + 2)))
    (hN : N (q i) ⊆ {p i, p (i + 1), q (i - 1), q (i + 1)} ∪ extra)
    (hextra : extra.card ≤ 1) :
    (U ∪ N (p (i + 2)) ∪ N (q i)).card ≤ 3 * k + 5 := by
  have hcover : U ∪ N (p (i + 2)) ∪ N (q i) ⊆ U ∪ N (p (i + 2)) ∪ extra := by
    intro x hx
    simp only [Finset.mem_union] at hx ⊢
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · have h := hN hx
      have h₁ : x = p i → x ∈ U := fun e => e.symm ▸ hp
      have h₂ : x = p (i + 1) → x ∈ N (p (i + 2)) := fun e => e.symm ▸ hp'
      have h₃ : x = q (i - 1) → x ∈ U := fun e => e.symm ▸ hq
      have h₄ : x = q (i + 1) → x ∈ N (p (i + 2)) := fun e => e.symm ▸ hq'
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      tauto
  have h₁ := Finset.card_le_card hcover
  have h₂ := Finset.card_union_le (U ∪ N (p (i + 2))) extra
  have h₃ := Finset.card_union_le U (N (p (i + 2)))
  omega

theorem lemma9_neighbor_card {V : Type*} [DecidableEq V]
    (N : V → Finset V) (p q r s : ℕ → V) (U extra : Finset V) (k a : ℕ)
    (_ha : 1 ≤ a) (hU : U.card ≤ 3 * k) (hp : p a ∈ U) (hq : q (a - 1) ∈ U)
    (h₁ : N (q a) ⊆ {p a, p (a + 1), q (a - 1), q (a + 1), r a, s a})
    (h₂ : N (p (a + 2)) ⊆ {p (a + 1), p (a + 3), q (a + 1), q (a + 2)})
    (h₃ : N (q (a + 3)) ⊆ {p (a + 3), p (a + 4), q (a + 2), q (a + 4),
      s (a + 2), s (a + 3)})
    (h₄ : N (p (a + 5)) ⊆ {p (a + 4), p (a + 6), q (a + 4), q (a + 5)})
    (h₅ : N (s (a + 1)) ⊆ {q (a + 1), q (a + 2), s a, s (a + 2)} ∪ extra)
    (hextra : extra.card ≤ 2) :
    (U ∪ N (q a) ∪ N (p (a + 2)) ∪ N (q (a + 3)) ∪ N (p (a + 5)) ∪
      N (s (a + 1))).card ≤ 3 * k + 14 := by
  let C : Finset V := {p (a + 1), p (a + 3), p (a + 4), p (a + 6),
    q (a + 1), q (a + 2), q (a + 4), q (a + 5), r a, s a, s (a + 2), s (a + 3)}
  have hcover : U ∪ N (q a) ∪ N (p (a + 2)) ∪ N (q (a + 3)) ∪ N (p (a + 5)) ∪
      N (s (a + 1)) ⊆ U ∪ C ∪ extra := by
    intro x hx
    simp only [Finset.mem_union] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))
    · have h := h₁ hx
      have hp' : x = p a → x ∈ U := fun e => e.symm ▸ hp
      have hq' : x = q (a - 1) → x ∈ U := fun e => e.symm ▸ hq
      simp only [C, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
    · have h := h₂ hx
      simp only [C, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
    · have h := h₃ hx
      simp only [C, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
    · have h := h₄ hx
      simp only [C, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
    · have h := h₅ hx
      simp only [C, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
  have hC : C.card ≤ 12 := by
    have insert_bound (v : V) (T : Finset V) {n : ℕ} (h : T.card ≤ n) :
        (insert v T).card ≤ Nat.succ n :=
      (Finset.card_insert_le v T).trans (Nat.succ_le_succ h)
    dsimp only [C]
    iterate 11 apply insert_bound
    simp only [Finset.card_singleton, le_refl]
  have hcard := Finset.card_le_card hcover
  have hUC := Finset.card_union_le U C
  have hUCe := Finset.card_union_le (U ∪ C) extra
  omega

end Swanepoel

namespace Swanepoel

open scoped Classical in

theorem expansion_false_of_neighbor_cover {V : Type*} [DecidableEq V]
    (X : Finset V) (E : V → V → Prop) (S U : Finset V)
    (hS : S ⊆ X) (hind : (S : Set V).Pairwise (fun x y => ¬ E x y))
    (hsmall : S.card ≤ 8) (hU : U.card < 3 * S.card)
    (hcover : ∀ y ∈ S, ∀ x ∈ X, E y x → x ∈ U)
    (hexpand : ∀ T : Finset V, T ⊆ X → (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ (X.filter fun x => x ∈ T ∨ ∃ y ∈ T, E y x).card) :
    False := by
  have hsub : (X.filter fun x => x ∈ S ∨ ∃ y ∈ S, E y x) ⊆ S ∪ U := by
    intro x hx
    obtain ⟨hxX, hxS | ⟨y, hy, hE⟩⟩ := Finset.mem_filter.mp hx
    · exact Finset.mem_union.mpr (Or.inl hxS)
    · exact Finset.mem_union.mpr (Or.inr (hcover y hy x hxX hE))
  have hl := hexpand S hS hind hsmall
  have hu := Finset.card_le_card hsub
  have hsum := Finset.card_union_le S U
  omega

open scoped Classical in
private theorem layer_extension_contradiction {V : Type*} [DecidableEq V]
    (X : Finset V) (E : V → V → Prop) (N : V → Finset V)
    (C U W : Finset V) (L : List V)
    (hdistinct : L.Nodup) (hdisjoint : Disjoint C L.toFinset)
    (hX : C ∪ L.toFinset ⊆ X)
    (hind : (↑(C ∪ L.toFinset) : Set V).Pairwise (fun x y => ¬ E x y))
    (hsmall : C.card + L.length ≤ 8) (hW : W.card < 3 * (C.card + L.length))
    (hprefix : ∀ y ∈ C, ∀ x ∈ X, E y x → x ∈ U) (hUW : U ⊆ W)
    (hN : ∀ y ∈ L.toFinset, ∀ x ∈ X, E y x → x ∈ N y)
    (hNW : ∀ y ∈ L.toFinset, N y ⊆ W)
    (hexpand : ∀ T : Finset V, T ⊆ X → (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ (X.filter fun x => x ∈ T ∨ ∃ y ∈ T, E y x).card) :
    False := by
  have hcard : (C ∪ L.toFinset).card = C.card + L.length := by
    rw [Finset.card_union_of_disjoint hdisjoint, List.toFinset_card_of_nodup hdistinct]
  refine expansion_false_of_neighbor_cover X E (C ∪ L.toFinset) W hX hind
    (by rwa [hcard]) (by rwa [hcard]) ?_ hexpand
  intro y hy x hx hE
  rcases Finset.mem_union.mp hy with hy | hy
  · exact hUW (hprefix y hy x hx hE)
  · exact hNW y hy (hN y hy x hx hE)

open scoped Classical in

theorem lemma8_layer_contradiction {V : Type*} [DecidableEq V]
    (X : Finset V) (E : V → V → Prop) (N : V → Finset V) (p q : ℕ → V)
    (C U extra : Finset V) (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 11)
    (hC : C.card = i / 2 + 1) (hU : U.card ≤ 3 * C.card)
    (hprefix : ∀ y ∈ C, ∀ x ∈ X, E y x → x ∈ U)
    (hdistinct : [p (i + 2), q i].Nodup)
    (hdisjoint : Disjoint C [p (i + 2), q i].toFinset)
    (hX : C ∪ [p (i + 2), q i].toFinset ⊆ X)
    (hind : (↑(C ∪ [p (i + 2), q i].toFinset) : Set V).Pairwise (fun x y => ¬ E x y))
    (hN : ∀ y ∈ [p (i + 2), q i].toFinset, ∀ x ∈ X, E y x → x ∈ N y)
    (hp : p i ∈ U) (hq : q (i - 1) ∈ U)
    (hdeg : (N (p (i + 2))).card ≤ 4)
    (hp' : p (i + 1) ∈ N (p (i + 2))) (hq' : q (i + 1) ∈ N (p (i + 2)))
    (hqN : N (q i) ⊆ {p i, p (i + 1), q (i - 1), q (i + 1)} ∪ extra)
    (hextra : extra.card ≤ 1)
    (hexpand : ∀ T : Finset V, T ⊆ X → (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ (X.filter fun x => x ∈ T ∨ ∃ y ∈ T, E y x).card) :
    False := by
  have hW := lemma8_neighbor_card N p q U extra C.card i hi hU hp hq hdeg hp' hq' hqN hextra
  refine layer_extension_contradiction X E N C U (U ∪ N (p (i + 2)) ∪ N (q i))
    [p (i + 2), q i] hdistinct hdisjoint hX hind ?_ ?_ hprefix ?_ hN ?_ hexpand
  · change C.card + 2 ≤ 8
    omega
  · change _ < 3 * (C.card + 2)
    omega
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))
  · intro y hy x hx
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx)))
    · exact Finset.mem_union.mpr (Or.inr hx)

open scoped Classical in

theorem lemma9_layer_contradiction {V : Type*} [DecidableEq V]
    (X : Finset V) (E : V → V → Prop) (N : V → Finset V) (p q r s : ℕ → V)
    (C U extra : Finset V) (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 5)
    (hC : C.card = a / 2 + 1) (hU : U.card ≤ 3 * C.card)
    (hprefix : ∀ y ∈ C, ∀ x ∈ X, E y x → x ∈ U)
    (hdistinct : [q a, p (a + 2), q (a + 3), p (a + 5), s (a + 1)].Nodup)
    (hdisjoint : Disjoint C [q a, p (a + 2), q (a + 3), p (a + 5), s (a + 1)].toFinset)
    (hX : C ∪ [q a, p (a + 2), q (a + 3), p (a + 5), s (a + 1)].toFinset ⊆ X)
    (hind : (↑(C ∪ [q a, p (a + 2), q (a + 3), p (a + 5), s (a + 1)].toFinset) : Set V).Pairwise
      (fun x y => ¬ E x y))
    (hN : ∀ y ∈ [q a, p (a + 2), q (a + 3), p (a + 5), s (a + 1)].toFinset,
      ∀ x ∈ X, E y x → x ∈ N y)
    (hp : p a ∈ U) (hq : q (a - 1) ∈ U)
    (h₁ : N (q a) ⊆ {p a, p (a + 1), q (a - 1), q (a + 1), r a, s a})
    (h₂ : N (p (a + 2)) ⊆ {p (a + 1), p (a + 3), q (a + 1), q (a + 2)})
    (h₃ : N (q (a + 3)) ⊆ {p (a + 3), p (a + 4), q (a + 2), q (a + 4),
      s (a + 2), s (a + 3)})
    (h₄ : N (p (a + 5)) ⊆ {p (a + 4), p (a + 6), q (a + 4), q (a + 5)})
    (h₅ : N (s (a + 1)) ⊆ {q (a + 1), q (a + 2), s a, s (a + 2)} ∪ extra)
    (hextra : extra.card ≤ 2)
    (hexpand : ∀ T : Finset V, T ⊆ X → (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ (X.filter fun x => x ∈ T ∨ ∃ y ∈ T, E y x).card) :
    False := by
  have hW := lemma9_neighbor_card N p q r s U extra C.card a ha hU hp hq h₁ h₂ h₃ h₄ h₅ hextra
  refine layer_extension_contradiction X E N C U
    (U ∪ N (q a) ∪ N (p (a + 2)) ∪ N (q (a + 3)) ∪ N (p (a + 5)) ∪ N (s (a + 1)))
    [q a, p (a + 2), q (a + 3), p (a + 5), s (a + 1)] hdistinct hdisjoint hX hind
    ?_ ?_ hprefix ?_ hN ?_ hexpand
  · change C.card + 5 ≤ 8
    omega
  · change _ < 3 * (C.card + 5)
    omega
  · intro x hx
    simp only [Finset.mem_union]
    tauto
  · intro y hy x hx
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp only [Finset.mem_union] <;> tauto

end Swanepoel

namespace Swanepoel

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

def layerPrefixVertex (p : ℕ → V) (pNeg : V) (i j : ℕ) : V :=
  if i % 2 = 0 then (if j = 0 then pNeg else p (2 * j - 1)) else p (2 * j)

def layerPrefix (p : ℕ → V) (pNeg : V) (i : ℕ) : Finset V :=
  (Finset.range (i / 2 + 1)).image (layerPrefixVertex p pNeg i)

theorem mem_layerPrefix {p : ℕ → V} {pNeg x : V} {i : ℕ} :
    x ∈ layerPrefix p pNeg i ↔
      (i % 2 = 0 ∧ x = pNeg) ∨ (∃ k < i, (k + 1) % 2 = i % 2 ∧ x = p k) := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' := Finset.mem_range.mp hj
    by_cases he : i % 2 = 0
    · by_cases hz : j = 0
      · exact Or.inl ⟨he, by simp [layerPrefixVertex, he, hz]⟩
      · exact Or.inr ⟨2 * j - 1, by omega, by omega,
          by simp [layerPrefixVertex, he, hz]⟩
    · exact Or.inr ⟨2 * j, by omega, by omega, by simp [layerPrefixVertex, he]⟩
  · rintro (⟨he, rfl⟩ | ⟨k, hk, hp, rfl⟩)
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega),
        by simp [layerPrefixVertex, he]⟩
    · by_cases he : i % 2 = 0
      · have hj : (k + 1) / 2 ≠ 0 := by omega
        have hindex : 2 * ((k + 1) / 2) - 1 = k := by omega
        exact Finset.mem_image.mpr ⟨(k + 1) / 2, Finset.mem_range.mpr (by omega),
          by simp [layerPrefixVertex, he, hj, hindex]⟩
      · have hindex : 2 * (k / 2) = k := by omega
        exact Finset.mem_image.mpr ⟨k / 2, Finset.mem_range.mpr (by omega),
          by simp [layerPrefixVertex, he, hindex]⟩

theorem layerPrefix_card {p : ℕ → V} {pNeg : V} {i : ℕ}
    (hinj : Set.InjOn (layerPrefixVertex p pNeg i) ↑(Finset.range (i / 2 + 1))) :
    (layerPrefix p pNeg i).card = i / 2 + 1 := by
  unfold layerPrefix
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

theorem layerPrefix_top {p : ℕ → V} {pNeg : V} {i : ℕ} (hi : 0 < i) :
    p (i - 1) ∈ layerPrefix p pNeg i :=
  mem_layerPrefix.mpr (Or.inr ⟨i - 1, by omega, by omega, rfl⟩)

theorem layerPrefix_boundary {N : V → Finset V} {p q : ℕ → V} {pNeg : V} {i : ℕ}
    (hi : 0 < i) (htriangle : p i ∈ N (p (i - 1)) ∧ q (i - 1) ∈ N (p (i - 1))) :
    p i ∈ (layerPrefix p pNeg i).biUnion N ∧
      q (i - 1) ∈ (layerPrefix p pNeg i).biUnion N :=
  ⟨Finset.mem_biUnion.mpr ⟨_, layerPrefix_top hi, htriangle.1⟩,
    Finset.mem_biUnion.mpr ⟨_, layerPrefix_top hi, htriangle.2⟩⟩

private theorem layerPrefix_chain_card (A : ℕ → Finset V) (n : ℕ)
    (hdeg : ∀ j ≤ n, (A j).card ≤ 4)
    (hoverlap : ∀ j < n, 1 ≤ (A j ∩ A (j + 1)).card)
    (hstart : (A 0).card ≤ 3 ∨ (0 < n ∧ 2 ≤ (A 0 ∩ A 1).card)) :
    ((Finset.range (n + 1)).biUnion A).card ≤ 3 * (n + 1) := by
  have hsum : ∀ k ≤ n, (∑ j ∈ Finset.range (k + 1), (A j).card) ≤ (A 0).card + 4 * k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ]
        have hprev := ih (by omega)
        have hd := hdeg (k + 1) (by omega)
        omega
  have hlower : ∀ k ≤ n, k ≤ ∑ j ∈ Finset.range k, (A j ∩ A (j + 1)).card := by
    intro k hk
    calc
      k = ∑ _j ∈ Finset.range k, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => hoverlap j (by have := Finset.mem_range.mp hj; omega)
  have hc := chain_union A n
  have hs := hsum n le_rfl
  rcases hstart with hd | ⟨hn, ho⟩
  · have hl := hlower n le_rfl
    omega
  · have hstrong : ∀ k ≤ n, 0 < k →
        k + 1 ≤ ∑ j ∈ Finset.range k, (A j ∩ A (j + 1)).card := by
      intro k
      induction k with
      | zero => omega
      | succ k ih =>
          intro hk _
          cases k with
          | zero => simpa using ho
          | succ k =>
              rw [Finset.sum_range_succ]
              have hp := ih (by omega) (by omega)
              have hstep := hoverlap (k + 1) (by omega)
              omega
    have hl := hstrong n le_rfl hn
    have hd := hdeg 0 (Nat.zero_le n)
    omega

theorem layerPrefix_biUnion_card (N : V → Finset V) (p q : ℕ → V) (pNeg : V)
    (i : ℕ) (hi : 0 < i)
    (hdeg : ∀ j < i, (N (p j)).card ≤ 4) (hzero : (N (p 0)).card ≤ 3)
    (hterminal : ((N pNeg).card ≤ 3 ∧ p 0 ∈ N pNeg) ∨
      ((N pNeg).card ≤ 4 ∧ p 0 ≠ q 0 ∧ p 0 ∈ N pNeg ∧ q 0 ∈ N pNeg ∧
        p 0 ∈ N (p 1) ∧ q 0 ∈ N (p 1)))
    (hforward : ∀ j, j + 1 < i → p (j + 1) ∈ N (p j))
    (hbackward : ∀ j, j + 1 < i → p j ∈ N (p (j + 1))) :
    ((layerPrefix p pNeg i).biUnion N).card ≤ 3 * (i / 2 + 1) := by
  let A : ℕ → Finset V := fun j => N (layerPrefixVertex p pNeg i j)
  have heq : (layerPrefix p pNeg i).biUnion N = (Finset.range (i / 2 + 1)).biUnion A := by
    ext x
    simp only [layerPrefix, Finset.mem_biUnion, Finset.mem_image, A]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      exact ⟨j, hj, hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨_, ⟨j, hj, rfl⟩, hx⟩
  rw [heq]
  have hneg : (N pNeg).card ≤ 4 := by
    rcases hterminal with h | h
    · omega
    · exact h.1
  have hneg01 : p 0 ∈ N pNeg := by
    rcases hterminal with h | h
    · exact h.2
    · exact h.2.2.1
  apply layerPrefix_chain_card A (i / 2)
  · intro j hj
    by_cases he : i % 2 = 0
    · by_cases hz : j = 0
      · simpa [A, layerPrefixVertex, he, hz] using hneg
      · simpa [A, layerPrefixVertex, he, hz] using hdeg (2 * j - 1) (by omega)
    · simpa [A, layerPrefixVertex, he] using hdeg (2 * j) (by omega)
  · intro j hj
    apply Finset.one_le_card.mpr
    by_cases he : i % 2 = 0
    · have hz' : j + 1 ≠ 0 := by omega
      have hs : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      by_cases hz : j = 0
      · subst j
        exact ⟨p 0, Finset.mem_inter.mpr (by
          simpa [A, layerPrefixVertex, he] using
            And.intro hneg01 (hbackward 0 (by omega)))⟩
      · have hp : (2 * j - 1) + 1 = 2 * j := by omega
        refine ⟨p (2 * j), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · simpa [A, layerPrefixVertex, he, hz, hp] using
            hforward (2 * j - 1) (by omega)
        · simpa [A, layerPrefixVertex, he, hz', hs] using hbackward (2 * j) (by omega)
    · have hs : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      exact ⟨p (2 * j + 1), Finset.mem_inter.mpr (by
        simpa [A, layerPrefixVertex, he, hs] using
          And.intro (hforward (2 * j) (by omega)) (hbackward (2 * j + 1) (by omega)))⟩
  · by_cases he : i % 2 = 0
    · rcases hterminal with hd | ⟨_, hne, hp, hq, hp', hq'⟩
      · exact Or.inl (by simpa [A, layerPrefixVertex, he] using hd.1)
      · refine Or.inr ⟨by omega, ?_⟩
        have hsub : ({p 0, q 0} : Finset V) ⊆ N pNeg ∩ N (p 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp, hp'⟩
          · exact Finset.mem_inter.mpr ⟨hq, hq'⟩
        simpa [A, layerPrefixVertex, he, hne] using Finset.card_le_card hsub
    · exact Or.inl (by simpa [A, layerPrefixVertex, he] using hzero)

end Swanepoel

namespace Swanepoel.TipWindow

open Swanepoel.ChainStep

private theorem cis_re (t : ℝ) : (cis t).re = Real.cos t :=
  Complex.exp_ofReal_mul_I_re t

private theorem cis_im (t : ℝ) : (cis t).im = Real.sin t :=
  Complex.exp_ofReal_mul_I_im t

theorem dist_sq (φ θ ρ : ℝ) :
    dist (cis φ) ((ρ : ℂ) * cis θ) ^ 2 = 1 + ρ ^ 2 - 2 * ρ * Real.cos (φ - θ) := by
  simp only [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    cis_re, cis_im, zero_mul, sub_zero, add_zero, Real.cos_sub]
  linear_combination Real.sin_sq_add_cos_sq φ + ρ ^ 2 * Real.sin_sq_add_cos_sq θ

theorem dist_lt_one_of_abs_sub_lt {φ θ δ : ℝ} (hδ₀ : 0 ≤ δ)
    (hδ : δ < Real.pi / 2) (hgap : |φ - θ| < δ) :
    dist (cis φ) ((↑(2 * Real.cos δ) : ℂ) * cis θ) < 1 := by
  have hcos : 0 < Real.cos δ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ⟩
  have hcmp : Real.cos δ < Real.cos (φ - θ) := by
    rw [← Real.cos_abs (φ - θ)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hgap
  have hsq : dist (cis φ) ((↑(2 * Real.cos δ) : ℂ) * cis θ) ^ 2 < 1 := by
    rw [dist_sq]
    nlinarith only [mul_pos hcos (sub_pos.mpr hcmp)]
  by_contra! h
  nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ dist (cis φ) ((↑(2 * Real.cos δ) : ℂ) * cis θ) + 1 by linarith)]

theorem pi_div_three_le_abs_sub {φ θ : ℝ} (h : 1 ≤ dist (cis φ) (cis θ)) :
    Real.pi / 3 ≤ |φ - θ| := by
  by_contra! hg
  have hd := dist_lt_one_of_abs_sub_lt (by positivity : (0 : ℝ) ≤ Real.pi / 3)
    (by linarith [Real.pi_pos] : Real.pi / 3 < Real.pi / 2) hg
  norm_num [Real.cos_pi_div_three] at hd
  exact (not_lt_of_ge h) hd

theorem bounds {L M R φ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hsum : L + M + R < Real.pi / 3) (hφ₀ : 0 ≤ φ) (hφ₂ : φ < 2 * Real.pi)
    (hA : 1 ≤ dist (cis φ) (cis (4 * Real.pi / 3 - M)))
    (hB : 1 ≤ dist (cis φ) (cis (5 * Real.pi / 3)))
    (hC : 1 ≤ dist (cis φ)
      ((↑(2 * Real.cos (Real.pi / 3 - (L + M) / 2)) : ℂ) *
        cis (Real.pi + (L - M) / 2)))
    (hD : 1 ≤ dist (cis φ)
      ((↑(2 * Real.cos (Real.pi / 3 - (M + R) / 2)) : ℂ) *
        cis (-(M + R) / 2))) :
    Real.pi / 3 - M - R ≤ φ ∧ φ ≤ 2 * Real.pi / 3 + L := by
  have hp := Real.pi_pos
  constructor
  · by_contra! h
    have hg : |φ - (-(M + R) / 2)| < Real.pi / 3 - (M + R) / 2 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (not_lt_of_ge hD) (dist_lt_one_of_abs_sub_lt (by linarith : 0 ≤ Real.pi / 3 - (M + R) / 2) (by linarith) hg)
  · by_contra! h
    by_cases h₁ : φ < 4 * Real.pi / 3 - M
    · have hg : |φ - (Real.pi + (L - M) / 2)| < Real.pi / 3 - (L + M) / 2 :=
        abs_lt.mpr ⟨by linarith, by linarith⟩
      exact (not_lt_of_ge hC) (dist_lt_one_of_abs_sub_lt (by linarith : 0 ≤ Real.pi / 3 - (L + M) / 2) (by linarith) hg)
    · by_cases h₂ : φ ≤ 4 * Real.pi / 3
      · have hg : |φ - (4 * Real.pi / 3 - M)| < Real.pi / 3 :=
          abs_lt.mpr ⟨by linarith, by linarith⟩
        exact (not_lt_of_ge (pi_div_three_le_abs_sub hA)) hg
      · have hg : |φ - (5 * Real.pi / 3)| < Real.pi / 3 :=
          abs_lt.mpr ⟨by linarith, by linarith⟩
        exact (not_lt_of_ge (pi_div_three_le_abs_sub hB)) hg

private theorem ordered_gap {a b : ℝ} (h : 1 ≤ dist (cis a) (cis b)) :
    Real.pi / 3 ≤ b - a ∨ Real.pi / 3 ≤ a - b := by
  have hg := pi_div_three_le_abs_sub h
  by_cases hab : 0 ≤ a - b
  · exact Or.inr (by simpa only [abs_of_nonneg hab] using hg)
  · rw [abs_of_neg (lt_of_not_ge hab)] at hg
    exact Or.inl (by linarith)

theorem not_three_separated {lo hi a b c : ℝ} (hwidth : hi - lo < 2 * Real.pi / 3)
    (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi) (hc : c ∈ Set.Icc lo hi) :
    ¬ (1 ≤ dist (cis a) (cis b) ∧ 1 ≤ dist (cis a) (cis c) ∧
      1 ≤ dist (cis b) (cis c)) := by
  rintro ⟨hab, hac, hbc⟩
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  obtain ⟨hc₁, hc₂⟩ := hc
  rcases ordered_gap hab with h₁ | h₁ <;>
    rcases ordered_gap hac with h₂ | h₂ <;>
    rcases ordered_gap hbc with h₃ | h₃ <;>
    linarith [Real.pi_pos]

theorem width_lt {L M R : ℝ} (hsum : L + M + R < Real.pi / 3) :
    (2 * Real.pi / 3 + L) - (Real.pi / 3 - M - R) < 2 * Real.pi / 3 := by
  linarith

end Swanepoel.TipWindow

namespace Swanepoel.TipCoordinates

open Swanepoel.ChainStep
noncomputable section

private theorem cis_im (t : ℝ) : (cis t).im = Real.sin t :=
  Complex.exp_ofReal_mul_I_im t

private theorem cis_pi : cis Real.pi = -1 := by
  apply Complex.ext <;> simp [cis_re, cis_im, Real.cos_pi, Real.sin_pi]

private theorem cis_five_pi_div_three : cis (5 * Real.pi / 3) = 1 - w := by
  rw [show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 by ring]
  apply Complex.ext
  · simp [w, cis_re, Real.cos_two_pi_sub, Real.cos_pi_div_three] <;> norm_num
  · simp [w, cis_im, Real.sin_two_pi_sub, Real.sin_pi_div_three] <;> norm_num

private theorem cis_four_pi_div_three : cis (4 * Real.pi / 3) = -w := by
  rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, cis_add, cis_pi]
  simp [w, mul_comm]

private theorem rotate_phase (θ x : ℝ) : cis (-θ) * cis (θ + x) = cis x := by
  calc
    cis (-θ) * cis (θ + x) = cis (θ + x) * cis (-θ) := mul_comm _ _
    _ = cis ((θ + x) + -θ) := (cis_add _ _).symm
    _ = cis x := by congr 1 <;> ring

private theorem neg_displacement (a b : ℝ) :
    -((1 - w) * cis a + w * cis b) =
      ((2 * Real.cos (Real.pi / 3 - (a - b) / 2) : ℝ) : ℂ) *
        cis (Real.pi + (a + b) / 2) := by
  rw [displacement, cis_add, cis_pi]
  ring

def q (p h : ℂ) : ℂ := p + w * h

def z (p h hNext : ℂ) : ℂ := p + w * (h + hNext)

theorem firstLayer (θ L R : ℝ) (p : ℂ) :
    cis (-θ) * (p - q p (cis θ)) = cis (4 * Real.pi / 3) ∧
    cis (-θ) * ((p + cis θ) - q p (cis θ)) = cis (5 * Real.pi / 3) ∧
    cis (-θ) * (q (p - cis (θ + L)) (cis (θ + L)) - q p (cis θ)) =
      ((2 * Real.cos (Real.pi / 3 - L / 2) : ℝ) : ℂ) * cis (Real.pi + L / 2) ∧
    cis (-θ) * (q (p + cis θ) (cis (θ - R)) - q p (cis θ)) =
      ((2 * Real.cos (Real.pi / 3 - R / 2) : ℝ) : ℂ) * cis (-R / 2) := by
  constructor
  · calc
      cis (-θ) * (p - q p (cis θ)) =
          -w * (cis (-θ) * cis θ) := by simp only [q]; ring
      _ = -w := by
        rw [show cis θ = cis (θ + 0) by simp, rotate_phase]
        simp [cis]
      _ = cis (4 * Real.pi / 3) := cis_four_pi_div_three.symm
  constructor
  · calc
      cis (-θ) * ((p + cis θ) - q p (cis θ)) =
          (1 - w) * (cis (-θ) * cis θ) := by simp only [q]; ring
      _ = 1 - w := by
        rw [show cis θ = cis (θ + 0) by simp, rotate_phase]
        simp [cis]
      _ = cis (5 * Real.pi / 3) := cis_five_pi_div_three.symm
  constructor
  · calc
      cis (-θ) * (q (p - cis (θ + L)) (cis (θ + L)) - q p (cis θ)) =
          -((1 - w) * (cis (-θ) * cis (θ + L)) +
            w * (cis (-θ) * cis θ)) := by simp only [q]; ring
      _ = -((1 - w) * cis L + w) := by
        rw [show cis θ = cis (θ + 0) by simp, rotate_phase θ 0, rotate_phase]
        simp [cis]
      _ = ((2 * Real.cos (Real.pi / 3 - L / 2) : ℝ) : ℂ) *
          cis (Real.pi + L / 2) := by
        have h0 : cis 0 = 1 := by simp [cis]
        simpa [h0] using neg_displacement L 0
  · calc
      cis (-θ) * (q (p + cis θ) (cis (θ - R)) - q p (cis θ)) =
          (1 - w) * (cis (-θ) * cis θ) +
            w * (cis (-θ) * cis (θ - R)) := by simp only [q]; ring
      _ = (1 - w) * cis 0 + w * cis (-R) := by
        rw [show cis θ = cis (θ + 0) by simp, rotate_phase θ 0,
          show θ - R = θ + -R by ring, rotate_phase]
      _ = ((2 * Real.cos (Real.pi / 3 - R / 2) : ℝ) : ℂ) * cis (-R / 2) := by
        simpa using displacement 0 (-R)

theorem matchedSecondLayer (θ L M R : ℝ) (p : ℂ) :
    cis (-θ) * (q p (cis θ) - z p (cis θ) (cis (θ - M))) = cis (4 * Real.pi / 3 - M) ∧
    cis (-θ) * (q (p + cis θ) (cis (θ - M)) - z p (cis θ) (cis (θ - M))) =
      cis (5 * Real.pi / 3) ∧
    cis (-θ) * (z (p - cis (θ + L)) (cis (θ + L)) (cis θ) -
      z p (cis θ) (cis (θ - M))) =
      ((2 * Real.cos (Real.pi / 3 - (L + M) / 2) : ℝ) : ℂ) *
        cis (Real.pi + (L - M) / 2) ∧
    cis (-θ) * (z (p + cis θ) (cis (θ - M)) (cis (θ - M - R)) -
      z p (cis θ) (cis (θ - M))) =
      ((2 * Real.cos (Real.pi / 3 - (M + R) / 2) : ℝ) : ℂ) * cis (-(M + R) / 2) := by
  constructor
  · calc
      cis (-θ) * (q p (cis θ) - z p (cis θ) (cis (θ - M))) =
          -w * (cis (-θ) * cis (θ - M)) := by simp only [q, z]; ring
      _ = -w * cis (-M) := by
        rw [show θ - M = θ + -M by ring, rotate_phase]
      _ = cis (4 * Real.pi / 3 - M) := by
        calc
          -w * cis (-M) = cis (4 * Real.pi / 3) * cis (-M) := by
            rw [cis_four_pi_div_three.symm]
          _ = cis (4 * Real.pi / 3 + -M) := (cis_add _ _).symm
          _ = cis (4 * Real.pi / 3 - M) := by congr 1 <;> ring
  constructor
  · calc
      cis (-θ) * (q (p + cis θ) (cis (θ - M)) - z p (cis θ) (cis (θ - M))) =
          (1 - w) * (cis (-θ) * cis θ) := by simp only [q, z]; ring
      _ = 1 - w := by
        rw [show cis θ = cis (θ + 0) by simp, rotate_phase]
        simp [cis]
      _ = cis (5 * Real.pi / 3) := cis_five_pi_div_three.symm
  constructor
  · calc
      cis (-θ) * (z (p - cis (θ + L)) (cis (θ + L)) (cis θ) -
        z p (cis θ) (cis (θ - M))) =
          -((1 - w) * (cis (-θ) * cis (θ + L)) +
            w * (cis (-θ) * cis (θ - M))) := by simp only [z]; ring
      _ = -((1 - w) * cis L + w * cis (-M)) := by
        rw [show θ - M = θ + -M by ring, rotate_phase θ L, rotate_phase]
      _ = ((2 * Real.cos (Real.pi / 3 - (L + M) / 2) : ℝ) : ℂ) *
          cis (Real.pi + (L - M) / 2) := by
        simpa only [sub_eq_add_neg, neg_neg] using neg_displacement L (-M)
  · calc
      cis (-θ) * (z (p + cis θ) (cis (θ - M)) (cis (θ - M - R)) -
        z p (cis θ) (cis (θ - M))) =
          (1 - w) * (cis (-θ) * cis θ) +
            w * (cis (-θ) * cis (θ - M - R)) := by simp only [z]; ring
      _ = (1 - w) * cis 0 + w * cis (-(M + R)) := by
        rw [show cis θ = cis (θ + 0) by simp, rotate_phase θ 0,
          show θ - M - R = θ + (-(M + R)) by ring, rotate_phase]
      _ = ((2 * Real.cos (Real.pi / 3 - (M + R) / 2) : ℝ) : ℂ) *
          cis (-(M + R) / 2) := by
        simpa using displacement 0 (-(M + R))

end
end Swanepoel.TipCoordinates

open scoped EuclideanGeometry

namespace Swanepoel.TipRayOrder

noncomputable def cis (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem cis_re (t : ℝ) : (cis t).re = Real.cos t :=
  Complex.exp_ofReal_mul_I_re t

private theorem cis_im (t : ℝ) : (cis t).im = Real.sin t :=
  Complex.exp_ofReal_mul_I_im t

private theorem cis_add (a b : ℝ) : cis (a + b) = cis a * cis b := by
  rw [cis, cis, cis, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem cis_add_cis (a b : ℝ) :
    cis a + cis b = ((2 * Real.cos ((a - b) / 2) : ℝ) : ℂ) * cis ((a + b) / 2) := by
  let d := (a - b) / 2
  let m := (a + b) / 2
  have ha : d + m = a := by dsimp [d, m]; ring
  have hb : -d + m = b := by dsimp [d, m]; ring
  have hd : cis d + cis (-d) = ((2 * Real.cos d : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, cis_re, Real.cos_neg, Complex.ofReal_re]
      ring
    · simp [cis_im, Real.sin_neg]
  change cis a + cis b = ((2 * Real.cos d : ℝ) : ℂ) * cis m
  rw [← ha, ← hb, cis_add d m, cis_add (-d) m, ← add_mul, hd]

theorem seam_ray_order {δ lo hiNext : ℝ}
    (hlo : Real.pi / 3 - δ ≤ lo) (hhi : hiNext ≤ 2 * Real.pi / 3 + δ) :
    -δ + (Real.pi / 3 + hiNext) / 2 ≤ (2 * Real.pi / 3 + lo) / 2 := by
  linarith

end Swanepoel.TipRayOrder

namespace Swanepoel.NearTip

open Swanepoel.ChainStep

noncomputable section

private theorem cis_norm (t : ℝ) : ‖cis t‖ = 1 := by
  simp [cis, Complex.norm_exp, Complex.mul_re]

private theorem sqrt_three_gt_one : (1 : ℝ) < Real.sqrt 3 := by
  simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)

private theorem displacement_norm_gt_one {a b : ℝ} (hab₁ : Real.pi / 3 ≤ a - b)
    (hab₂ : a - b < 2 * Real.pi / 3) :
    1 < ‖(1 - w) * cis a + w * cis b‖ := by
  rw [displacement, norm_mul, Complex.norm_real, cis_norm]
  have hp := Real.pi_pos
  let x := Real.pi / 3 - (a - b) / 2
  have hx₀ : 0 < x := by dsimp [x]; linarith
  have hx₁ : x ≤ Real.pi / 6 := by dsimp [x]; linarith
  have hc : Real.sqrt 3 / 2 ≤ Real.cos x := by
    rw [← Real.cos_pi_div_six]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hx₁
  have hscale : 1 < 2 * Real.cos x := by
    have hs := sqrt_three_gt_one
    linarith
  have hcpos : 0 < Real.cos x := lt_of_lt_of_le (by positivity) hc
  simpa [x, abs_of_pos hcpos] using hscale

private theorem one_lt_dist_of_re {u v : ℂ} (h : 1 < v.re - u.re) : 1 < dist u v := by
  rw [dist_eq_norm]
  rw [← Complex.sub_re] at h
  calc
    1 < (v - u).re := h
    _ ≤ |(v - u).re| := le_abs_self _
    _ ≤ ‖v - u‖ := Complex.abs_re_le_norm (v - u)
    _ = ‖u - v‖ := norm_sub_rev _ _

private theorem one_sub_w_cis_add (t : ℝ) :
    (1 - w) * cis (t + Real.pi / 3) = cis t := by
  rw [ChainStep.one_sub_w, ← cis_add]
  congr 1 <;> ring

private theorem w_cis_sub (t : ℝ) :
    w * cis (t - Real.pi / 3) = cis t := by
  rw [w, ← cis_add]
  congr 1 <;> ring

structure Suffix where
  p : ℕ → ℂ
  θ : ℕ → ℝ
  p0 : p 0 = 0
  θ0 : θ 0 = 0
  step : ∀ i, p (i + 1) - p i = cis (θ i)
  range : ∀ i, -(Real.pi / 3) ≤ θ i ∧ θ i ≤ 0
  turn : ∀ i, 0 ≤ θ i - θ (i + 1) ∧ θ i - θ (i + 1) < Real.pi / 3

namespace Suffix

variable (S : Suffix)

def q (i : ℕ) : ℂ := S.p i + w * cis (S.θ i)

def z (i : ℕ) : ℂ := S.p i + w * cis (S.θ i) + w * cis (S.θ (i + 1))

private theorem p_one_eq_one : S.p 1 = 1 := by
  have h := S.step 0
  rw [S.θ0, S.p0] at h
  simpa [cis] using h

private theorem q_one_form : S.q 1 = 1 + cis (Real.pi / 3 + S.θ 1) := by
  simp only [Suffix.q]
  rw [S.p_one_eq_one, w, ← cis_add]

private theorem cos_heading_ge_half (i : ℕ) : 1 / 2 ≤ Real.cos (S.θ i) := by
  have hr := S.range i
  rw [← Real.cos_neg (S.θ i), ← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private theorem cos_rotated_ge_half (i : ℕ) :
    1 / 2 ≤ Real.cos (Real.pi / 3 + S.θ i) := by
  have hr := S.range i
  rw [← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private theorem step_re (i : ℕ) :
    (S.p (i + 1)).re - (S.p i).re = Real.cos (S.θ i) := by
  simpa only [Complex.sub_re, cis_re] using congrArg Complex.re (S.step i)

private theorem mono_re : Monotone (fun i => (S.p i).re) := by
  apply monotone_nat_of_le_succ
  intro i
  linarith [S.step_re i, S.cos_heading_ge_half i]

private theorem p_re_gt_three_halves {i : ℕ} (hi : 2 ≤ i) :
    3 / 2 < (S.p i).re := by
  have hp : 3 / 2 < (S.p 2).re := by
    have hturn := S.turn 0
    rw [S.θ0] at hturn
    have hstrict : -(Real.pi / 3) < S.θ 1 := by
      linarith [hturn.2]
    have hcos : 1 / 2 < Real.cos (S.θ 1) := by
      rw [← Real.cos_neg (S.θ 1), ← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) (by linarith [hstrict])
    have hs0 : (S.p 1).re = 1 := by
      simpa [S.p0, S.θ0] using S.step_re 0
    have hs1 : (S.p 2).re - (S.p 1).re = Real.cos (S.θ 1) := by
      simpa using S.step_re 1
    have hsum : (S.p 2).re = 1 + Real.cos (S.θ 1) := by linarith [hs0, hs1]
    rw [hsum]
    linarith
  have hmono := S.mono_re (show 2 ≤ i from hi)
  linarith

theorem dist_q_succ_p (i : ℕ) : 1 < dist (S.q (i + 1)) (S.p i) := by
  rw [dist_eq_norm]
  have hd : S.q (i + 1) - S.p i =
      (1 - w) * cis (S.θ i + Real.pi / 3) + w * cis (S.θ (i + 1)) := by
    simp only [Suffix.q]
    calc
      S.p (i + 1) + w * cis (S.θ (i + 1)) - S.p i =
          (S.p (i + 1) - S.p i) + w * cis (S.θ (i + 1)) := by ring
      _ = cis (S.θ i) + w * cis (S.θ (i + 1)) := by rw [S.step i]
      _ = (1 - w) * cis (S.θ i + Real.pi / 3) + w * cis (S.θ (i + 1)) := by
        rw [← one_sub_w_cis_add (S.θ i)]
  rw [hd]
  apply displacement_norm_gt_one
  · have ht := (S.turn i).1
    linarith
  · have ht := (S.turn i).2
    linarith [Real.pi_pos]

theorem dist_q_p_two_after (i : ℕ) : 1 < dist (S.q i) (S.p (i + 2)) := by
  rw [dist_comm, dist_eq_norm]
  have hd : S.p (i + 2) - S.q i =
      (1 - w) * cis (S.θ i) + w * cis (S.θ (i + 1) - Real.pi / 3) := by
    simp only [Suffix.q]
    calc
      S.p (i + 2) - (S.p i + w * cis (S.θ i)) =
          (S.p (i + 1) - S.p i) + (S.p (i + 2) - S.p (i + 1)) -
            w * cis (S.θ i) := by ring
      _ = cis (S.θ i) + cis (S.θ (i + 1)) - w * cis (S.θ i) := by
        rw [S.step i, S.step (i + 1)]
      _ = (1 - w) * cis (S.θ i) + cis (S.θ (i + 1)) := by ring
      _ = (1 - w) * cis (S.θ i) + w * cis (S.θ (i + 1) - Real.pi / 3) := by
        rw [← w_cis_sub (S.θ (i + 1))]
  rw [hd]
  apply displacement_norm_gt_one
  · have ht := (S.turn i).1
    linarith
  · have ht := (S.turn i).2
    linarith [Real.pi_pos]
private theorem cos_two_thirds : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

private theorem endpoint_x_bound {φ : ℝ} (hφ₁ : 2 * Real.pi / 3 ≤ φ)
    (hφ₂ : φ ≤ 5 * Real.pi / 3) : Real.cos φ ≤ 1 / 2 := by
  have hp := Real.pi_pos
  by_cases hφ : φ ≤ Real.pi
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := 2 * Real.pi / 3) (y := φ)
      (show 0 ≤ 2 * Real.pi / 3 by nlinarith [Real.pi_pos])
      (show φ ≤ Real.pi from hφ) hφ₁
    rw [cos_two_thirds] at h
    linarith
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := Real.pi / 3) (y := 2 * Real.pi - φ)
      (show 0 ≤ Real.pi / 3 by nlinarith [Real.pi_pos])
      (show 2 * Real.pi - φ ≤ Real.pi by linarith)
      (by linarith)
    rw [Real.cos_two_pi_sub] at h
    rw [← Real.cos_pi_div_three]
    exact h

private theorem endpoint_angle_of_x_eq {φ : ℝ} (hφ₁ : 2 * Real.pi / 3 ≤ φ)
    (hφ₂ : φ ≤ 5 * Real.pi / 3) (hx : Real.cos φ = 1 / 2) :
    φ = 5 * Real.pi / 3 := by
  have hp := Real.pi_pos
  have hnot : ¬ φ ≤ Real.pi := by
    intro hφ
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := 2 * Real.pi / 3) (y := φ)
      (show 0 ≤ 2 * Real.pi / 3 by nlinarith [Real.pi_pos])
      (show φ ≤ Real.pi from hφ) hφ₁
    rw [cos_two_thirds] at h
    linarith
  have hr : Real.cos (2 * Real.pi - φ) = Real.cos (Real.pi / 3) := by
    rw [Real.cos_two_pi_sub, Real.cos_pi_div_three, hx]
  have hinj := Real.strictAntiOn_cos.injOn
    (show 2 * Real.pi - φ ∈ Set.Icc 0 Real.pi by constructor <;> linarith)
    (show Real.pi / 3 ∈ Set.Icc 0 Real.pi by constructor <;> nlinarith [Real.pi_pos]) hr
  linarith

private theorem theta_one_of_x_eq (S : Suffix)
    (hx : Real.cos (Real.pi / 3 + S.θ 1) = 1 / 2) : S.θ 1 = 0 := by
  have hθ := S.range 1
  have hp := Real.pi_pos
  have hrange : Real.pi / 3 + S.θ 1 ∈ Set.Icc 0 Real.pi := by
    constructor <;> linarith
  have hinj := Real.strictAntiOn_cos.injOn hrange
    (show Real.pi / 3 ∈ Set.Icc 0 Real.pi by constructor <;> nlinarith [Real.pi_pos])
    (by rw [Real.cos_pi_div_three, hx])
  linarith

theorem endpoint_dist_q_gt_one (S : Suffix) (φ : ℝ)
    (hφ₁ : 2 * Real.pi / 3 ≤ φ) (hφ₂ : φ ≤ 5 * Real.pi / 3) :
    ∀ i, 1 ≤ i → 1 < dist (cis φ) (S.q i) := by
  intro i hi
  have hxend := endpoint_x_bound hφ₁ hφ₂
  have hxend' : (cis φ).re ≤ 1 / 2 := by simpa only [cis_re] using hxend
  by_cases h1 : i = 1
  · subst i
    have hqre : 3 / 2 ≤ (S.q 1).re := by
      rw [S.q_one_form]
      simp only [Complex.add_re, Complex.one_re, cis_re]
      linarith [S.cos_rotated_ge_half 1]
    by_contra! hd
    have hnorm : ‖S.q 1 - cis φ‖ ≤ 1 := by
      calc
        ‖S.q 1 - cis φ‖ = dist (S.q 1) (cis φ) := (dist_eq_norm _ _).symm
        _ = dist (cis φ) (S.q 1) := dist_comm _ _
        _ ≤ 1 := hd
    have hdx : 1 ≤ (S.q 1).re - (cis φ).re := by linarith
    have hdx' : (S.q 1).re - (cis φ).re ≤ 1 := by
      calc
        _ ≤ |(S.q 1 - cis φ).re| := by
          rw [Complex.sub_re]
          exact le_abs_self _
        _ ≤ ‖S.q 1 - cis φ‖ := Complex.abs_re_le_norm _
        _ ≤ 1 := hnorm
    have hxeq : (S.q 1).re = 3 / 2 ∧ (cis φ).re = 1 / 2 := by
      constructor <;> nlinarith [hqre, hxend', hdx, hdx']
    have hθ : S.θ 1 = 0 := by
      have hqeq := hxeq.1
      rw [S.q_one_form, Complex.add_re, Complex.one_re, cis_re] at hqeq
      have hc : Real.cos (Real.pi / 3 + S.θ 1) = 1 / 2 := by linarith
      exact theta_one_of_x_eq S hc
    have hφ : φ = 5 * Real.pi / 3 := endpoint_angle_of_x_eq hφ₁ hφ₂ (by
      simpa only [cis_re] using hxeq.2)
    have hyq : (S.q 1).im = Real.sqrt 3 / 2 := by
      rw [S.q_one_form, hθ]
      simp [Complex.add_im, Complex.one_im, cis_im, Real.sin_pi_div_three]
    have hye : (cis φ).im = -(Real.sqrt 3 / 2) := by
      rw [hφ, cis_im, show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 by ring,
        Real.sin_two_pi_sub, Real.sin_pi_div_three]
    have hyne : (S.q 1 - cis φ).im ≠ 0 := by
      rw [Complex.sub_im, hyq, hye]
      norm_num
    have hsq := Complex.sq_norm (S.q 1 - cis φ)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hsq
    have hdx_eq : (S.q 1).re - (cis φ).re = 1 := le_antisymm hdx' hdx
    have hy2 : 0 < ((S.q 1 - cis φ).im) ^ 2 := sq_pos_of_ne_zero hyne
    rw [Complex.sub_im] at hy2
    have hnormsq : ‖S.q 1 - cis φ‖ ^ 2 ≤ 1 := by
      have hnorm0 : 0 ≤ ‖S.q 1 - cis φ‖ := norm_nonneg _
      nlinarith [hnorm, hnorm0]
    nlinarith [hsq, hy2, hnormsq, hdx_eq]
  · have hge : 2 ≤ i := by omega
    have hp := S.p_re_gt_three_halves hge
    have hrot := S.cos_rotated_ge_half i
    have hq : 2 < (S.q i).re := by
      simp only [Suffix.q, Complex.add_re]
      have hrot' : 1 / 2 ≤ (w * cis (S.θ i)).re := by
        rw [w, ← cis_add, cis_re]
        exact S.cos_rotated_ge_half i
      linarith
    have hx : 1 < (S.q i).re - (cis φ).re := by
      linarith [hq, hxend']
    exact one_lt_dist_of_re hx

theorem endpoint_dist_p_gt_one (S : Suffix) (φ : ℝ)
    (hφ₁ : 2 * Real.pi / 3 ≤ φ) (hφ₂ : φ ≤ 5 * Real.pi / 3) :
    ∀ i, 2 ≤ i → 1 < dist (cis φ) (S.p i) := by
  intro i hi
  have hp := S.p_re_gt_three_halves hi
  have hxend := endpoint_x_bound hφ₁ hφ₂
  have hxend' : (cis φ).re ≤ 1 / 2 := by simpa only [cis_re] using hxend
  apply one_lt_dist_of_re
  linarith [hp, hxend']

theorem endpoint_dist_z_gt_one (S : Suffix) (φ : ℝ)
    (hφ₁ : 2 * Real.pi / 3 ≤ φ) (hφ₂ : φ ≤ 5 * Real.pi / 3) :
    ∀ i, 2 ≤ i → 1 < dist (cis φ) (S.z i) := by
  intro i hi
  have hp := S.p_re_gt_three_halves hi
  have hxend := endpoint_x_bound hφ₁ hφ₂
  have hxend' : (cis φ).re ≤ 1 / 2 := by simpa only [cis_re] using hxend
  have hz : 5 / 2 < (S.z i).re := by
    simp only [Suffix.z, Complex.add_re]
    have hr₁ : 1 / 2 ≤ (w * cis (S.θ i)).re := by
      rw [w, ← cis_add, cis_re]
      exact S.cos_rotated_ge_half i
    have hr₂ : 1 / 2 ≤ (w * cis (S.θ (i + 1))).re := by
      rw [w, ← cis_add, cis_re]
      exact S.cos_rotated_ge_half (i + 1)
    linarith
  apply one_lt_dist_of_re
  linarith [hz, hxend']

end Suffix
end
end Swanepoel.NearTip

namespace Swanepoel.LayerWindows

open Swanepoel.ChainStep

noncomputable section

variable {V : Type*} [DecidableEq V]

theorem dist_frame (θ : ℝ) (c x y : ℂ) :
    dist (cis (-θ) * (x - c)) (cis (-θ) * (y - c)) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, show x - c - (y - c) = x - y by ring, norm_mul]
  change ‖Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ * ‖x - y‖ = ‖x - y‖
  rw [Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem heading_window (f : V → ℂ) (sep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y))
    (c a b d e x : V) (θ L M R : ℝ)
    (ha : cis (-θ) * (f a - f c) = cis (4 * Real.pi / 3 - M))
    (hb : cis (-θ) * (f b - f c) = cis (5 * Real.pi / 3))
    (hd : cis (-θ) * (f d - f c) =
      ((2 * Real.cos (Real.pi / 3 - (L + M) / 2) : ℝ) : ℂ) * cis (Real.pi + (L - M) / 2))
    (he : cis (-θ) * (f e - f c) =
      ((2 * Real.cos (Real.pi / 3 - (M + R) / 2) : ℝ) : ℂ) * cis (-(M + R) / 2))
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : L + M + R < Real.pi / 3)
    (hu : ‖f x - f c‖ = 1) (hne : x ≠ a ∧ x ≠ b ∧ x ≠ d ∧ x ≠ e) :
    ∃ φ ∈ Set.Icc (Real.pi / 3 - M - R) (2 * Real.pi / 3 + L),
      cis φ = cis (-θ) * (f x - f c) := by
  have hunit : ‖cis (-θ) * (f x - f c)‖ = 1 := by
    rw [norm_mul, hu, mul_one]
    exact Complex.norm_exp_ofReal_mul_I _
  obtain ⟨φ, h0, h2, hφ⟩ := unit_angle hunit
  have hsep (y : V) (h : x ≠ y) :
      1 ≤ dist (cis φ) (cis (-θ) * (f y - f c)) := by
    rw [hφ, dist_frame]
    exact sep h
  refine ⟨φ, ?_, hφ⟩
  have h₁ := hsep a hne.1
  have h₂ := hsep b hne.2.1
  have h₃ := hsep d hne.2.2.1
  have h₄ := hsep e hne.2.2.2
  rw [ha] at h₁
  rw [hb] at h₂
  rw [hd] at h₃
  rw [he] at h₄
  exact TipWindow.bounds hL hM hR hS h0 h2 h₁ h₂ h₃ h₄

theorem extras_le_two (f : V → ℂ) (sep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y))
    (c a b d e : V) (N : Finset V) (θ L M R : ℝ)
    (ha : cis (-θ) * (f a - f c) = cis (4 * Real.pi / 3 - M))
    (hb : cis (-θ) * (f b - f c) = cis (5 * Real.pi / 3))
    (hd : cis (-θ) * (f d - f c) =
      ((2 * Real.cos (Real.pi / 3 - (L + M) / 2) : ℝ) : ℂ) * cis (Real.pi + (L - M) / 2))
    (he : cis (-θ) * (f e - f c) =
      ((2 * Real.cos (Real.pi / 3 - (M + R) / 2) : ℝ) : ℂ) * cis (-(M + R) / 2))
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : L + M + R < Real.pi / 3)
    (hN : ∀ x ∈ N, ‖f x - f c‖ = 1) :
    (N \ {a, b, d, e}).card ≤ 2 := by
  have hheading {x : V} (hx : x ∈ N \ {a, b, d, e}) :
      ∃ φ ∈ Set.Icc (Real.pi / 3 - M - R) (2 * Real.pi / 3 + L),
        cis φ = cis (-θ) * (f x - f c) := by
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_sdiff.mp hx
    have hne : x ≠ a ∧ x ≠ b ∧ x ≠ d ∧ x ≠ e := by simpa using hx₂
    exact heading_window f sep c a b d e x θ L M R ha hb hd he hL hM hR hS (hN x hx₁) hne
  by_contra! hgt
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hgt
  obtain ⟨φ, hφ, hxφ⟩ := hheading hx
  obtain ⟨ψ, hψ, hyψ⟩ := hheading hy
  obtain ⟨ω, hω, hzω⟩ := hheading hz
  apply TipWindow.not_three_separated (TipWindow.width_lt hS) hφ hψ hω
  rw [hxφ, hyψ, hzω, dist_frame, dist_frame, dist_frame]
  exact ⟨sep hxy, sep hxz, sep hyz⟩

theorem first_pair (f : V → ℂ) (sep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y))
    (c a b d e x y : V) (θ L R : ℝ)
    (ha : cis (-θ) * (f a - f c) = cis (4 * Real.pi / 3))
    (hb : cis (-θ) * (f b - f c) = cis (5 * Real.pi / 3))
    (hd : cis (-θ) * (f d - f c) =
      ((2 * Real.cos (Real.pi / 3 - L / 2) : ℝ) : ℂ) * cis (Real.pi + L / 2))
    (he : cis (-θ) * (f e - f c) =
      ((2 * Real.cos (Real.pi / 3 - R / 2) : ℝ) : ℂ) * cis (-R / 2))
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : L + R < Real.pi / 3)
    (hx : ‖f x - f c‖ = 1) (hy : ‖f y - f c‖ = 1) (hxy : x ≠ y)
    (hxn : x ≠ a ∧ x ≠ b ∧ x ≠ d ∧ x ≠ e) (hyn : y ≠ a ∧ y ≠ b ∧ y ≠ d ∧ y ≠ e) :
    ∃ r s : V, ((r = x ∧ s = y) ∨ (r = y ∧ s = x)) ∧
      ∃ hi lo : ℝ, Real.pi / 3 - R ≤ lo ∧ hi ≤ 2 * Real.pi / 3 + L ∧ Real.pi / 3 ≤ hi - lo ∧
        cis hi = cis (-θ) * (f r - f c) ∧ cis lo = cis (-θ) * (f s - f c) := by
  have hh (z : V) (hz : ‖f z - f c‖ = 1) (hzn : z ≠ a ∧ z ≠ b ∧ z ≠ d ∧ z ≠ e) :=
    heading_window f sep c a b d e z θ L 0 R (by simpa using ha) hb (by simpa using hd)
      (by simpa using he) hL (by norm_num) hR (by simpa using hS) hz hzn
  obtain ⟨u, hu, heu⟩ := hh x hx hxn
  obtain ⟨v, hv, hev⟩ := hh y hy hyn
  have hsep : 1 ≤ dist (cis u) (cis v) := by rw [heu, hev, dist_frame]; exact sep hxy
  have hgap := TipWindow.pi_div_three_le_abs_sub hsep
  by_cases huv : v ≤ u
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)] at hgap
    exact ⟨x, y, Or.inl ⟨rfl, rfl⟩, u, v, by simpa using hv.1, hu.2, hgap, heu, hev⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge huv)), neg_sub] at hgap
    exact ⟨y, x, Or.inr ⟨rfl, rfl⟩, v, u, by simpa using hu.1, hv.2, hgap, hev, heu⟩

end

end Swanepoel.LayerWindows

open Real

namespace Swanepoel.Charges

lemma radius_bounds {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ π / 3) :
    1 ≤ 2 * cos a ∧ 2 * cos a ≤ 2 := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith [Real.pi_pos]) hb
  rw [Real.cos_pi_div_three] at h
  constructor <;> linarith [Real.cos_le_one a]

lemma gap_of_test {u v θ t : ℝ} (hu : 0 < u) (hv : 0 < v) (hθ : 0 ≤ θ) (ht : t ≤ π)
    (hobs : 1 ≤ u^2 + v^2 - 2*u*v*cos θ)
    (htest : u^2 + v^2 - 2*u*v*cos t ≤ 1) : t ≤ θ := by
  by_contra! hlt
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ ht hlt
  have h := mul_lt_mul_of_pos_left hc (mul_pos (mul_pos (by norm_num : 0 < (2:ℝ)) hu) hv)
  linarith

lemma sin_twice_lower {a : ℝ} (ha : π / 6 ≤ a) (hb : a ≤ π / 3) :
    √3 / 2 ≤ sin (2 * a) := by
  rw [← Real.sin_pi_div_three]
  by_cases hl : 2 * a ≤ π / 2
  · apply Real.sin_le_sin_of_le_of_le_pi_div_two _ hl <;> linarith [Real.pi_pos]
  · rw [← Real.sin_pi_sub (2 * a)]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith [Real.pi_pos]

lemma annulus_test {u c v : ℝ} (h1 : 1 ≤ v) (h2 : v ≤ 2)
    (hleft : u^2 + 1 - 2*u*c ≤ 1) (hright : u^2 + 4 - 4*u*c ≤ 1) :
    u^2 + v^2 - 2*u*v*c ≤ 1 := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hleft),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hright),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

lemma one_side {a θ v : ℝ} (ha : 0 ≤ a) (hau : a ≤ π / 3) (hθ : 0 ≤ θ)
    (hv : 1 ≤ v) (hvu : v ≤ 2)
    (hsep : 1 ≤ (2*cos a)^2 + v^2 - 2*(2*cos a)*v*cos θ) :
    min a (π / 3 - a) ≤ θ := by
  have rad := radius_bounds ha hau
  have cp : 0 < cos a := by linarith [rad.1]
  by_cases hs : a ≤ π / 6
  · rw [min_eq_left (by linarith)]
    apply gap_of_test (by linarith : 0 < 2*cos a) (by linarith) hθ (by linarith [pi_pos]) hsep
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith [pi_pos]) hs
    rw [Real.cos_pi_div_six] at hc
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ √3 / 2) hc
    have ht : v + 1 ≤ 4 * (cos a)^2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr ht)]
  · rw [min_eq_right (by linarith)]
    apply gap_of_test (by linarith : 0 < 2*cos a) (by linarith) hθ (by linarith [pi_pos]) hsep
    apply annulus_test hv hvu
    · have hc := Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr hau)
        (by linarith [pi_pos]) (by linarith : π/3 - a ≤ a)
      nlinarith only [mul_nonneg cp.le (sub_nonneg.mpr hc)]
    · have hh := mul_le_mul_of_nonneg_left (sin_twice_lower (le_of_not_ge hs) hau)
        (by positivity : 0 ≤ √3)
      rw [Real.sin_two_mul] at hh
      rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
      nlinarith only [hh, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

lemma thirty_degree_factor (a b : ℝ) :
    (2*cos a)^2 + (2*cos b)^2 - 2*(2*cos a)*(2*cos b)*cos (π/6) - 1 =
      (2*cos (a+b) - √3) * (2*cos (a-b) - √3) := by
  symm
  calc
    _ = (2*cos a*cos b - √3)^2 - 4*(sin a)^2*(sin b)^2 := by
      rw [Real.cos_add, Real.cos_sub]
      ring
    _ = _ := by
      rw [show (sin a)^2 = 1-(cos a)^2 by nlinarith only [Real.sin_sq_add_cos_sq a],
        show (sin b)^2 = 1-(cos b)^2 by nlinarith only [Real.sin_sq_add_cos_sq b],
        Real.cos_pi_div_six]
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

lemma central_gap {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hau : a ≤ π/6)
    (hbu : b ≤ π/6) (hsum : π/6 ≤ a+b) (hθ : 0 ≤ θ)
    (hsep : 1 ≤ (2*cos a)^2 + (2*cos b)^2 - 2*(2*cos a)*(2*cos b)*cos θ) :
    π/6 ≤ θ := by
  have pa := (radius_bounds ha (show a ≤ π/3 by linarith [pi_pos])).1
  have pb := (radius_bounds hb (show b ≤ π/3 by linarith [pi_pos])).1
  apply gap_of_test (by linarith) (by linarith) hθ (by linarith [pi_pos]) hsep
  have hplus := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos])
    (by linarith [pi_pos]) hsum
  have ha' : |a-b| ≤ π/6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hminus := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) ha'
  rw [Real.cos_pi_div_six] at hplus
  rw [Real.cos_pi_div_six, Real.cos_abs] at hminus
  have ht := mul_nonpos_of_nonpos_of_nonneg (by linarith : 2*cos (a+b) - √3 ≤ 0)
    (by linarith : 0 ≤ 2*cos (a-b) - √3)
  linarith only [thirty_degree_factor a b, ht]

theorem seam_charges {a b θ l m r : ℝ}
    (ha : 0 ≤ a) (hau : a ≤ π/3) (hb : 0 ≤ b) (hbu : b ≤ π/3) (hθ : 0 ≤ θ)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hl' : π/3-2*a ≤ l) (hr' : π/3-2*b ≤ r) (hmid : m = a+θ+b-π/3)
    (hsep : 1 ≤ (2*cos a)^2 + (2*cos b)^2 - 2*(2*cos a)*(2*cos b)*cos θ) :
    b ≤ l+m ∧ a ≤ m+r ∧ π/3 ≤ l+2*m+r := by
  have ra := radius_bounds ha hau
  have rb := radius_bounds hb hbu
  have hag := one_side ha hau hθ rb.1 rb.2 hsep
  have hbg := one_side hb hbu hθ ra.1 ra.2 (by linarith only [hsep])
  constructor
  · rcases le_total a (π/3-a) with h | h
    · rw [min_eq_left h] at hag; linarith
    · rw [min_eq_right h] at hag; linarith
  constructor
  · rcases le_total b (π/3-b) with h | h
    · rw [min_eq_left h] at hbg; linarith
    · rw [min_eq_right h] at hbg; linarith
  · by_cases h1 : a ≤ π/6
    · by_cases h2 : b ≤ π/6
      · by_cases h3 : π/6 ≤ a+b
        · linarith [central_gap ha hb h1 h2 h3 hθ hsep]
        · linarith
      · rw [min_eq_right (by linarith)] at hbg; linarith
    · rw [min_eq_right (by linarith)] at hag; linarith

end Swanepoel.Charges

namespace Swanepoel.SeamHeading

open Real Finset Swanepoel.ChainStep

noncomputable section

def A (hi : ℝ) : ℝ := (hi - π / 3) / 2

def B (lo : ℝ) : ℝ := (2 * π / 3 - lo) / 2

theorem heading_bounds {l m hi lo : ℝ} (hl : l ≤ π / 3) (hm : m ≤ π / 3)
    (hlo : π / 3 - m ≤ lo) (hhi : hi ≤ 2 * π / 3 + l) (hgap : π / 3 ≤ hi - lo) :
    0 ≤ A hi ∧ A hi ≤ π / 3 ∧ 0 ≤ B lo ∧ B lo ≤ π / 3 ∧
    π / 3 ≤ A hi + B lo ∧ π / 3 - 2 * B lo ≤ l ∧ π / 3 - 2 * A hi ≤ m := by
  dsimp [A, B]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem cis_im (t : ℝ) : (cis t).im = sin t :=
  Complex.exp_ofReal_mul_I_im t

theorem normSq_radial_sub (u v α β : ℝ) :
    Complex.normSq ((u : ℂ) * cis α - (v : ℂ) * cis β) =
      u ^ 2 + v ^ 2 - 2 * u * v * cos (α - β) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, cis_re, cis_im,
    zero_mul, sub_zero, add_zero, Real.cos_sub]
  linear_combination u ^ 2 * Real.sin_sq_add_cos_sq α + v ^ 2 * Real.sin_sq_add_cos_sq β

def rightVector (lo : ℝ) : ℂ := cis (2 * π / 3) + cis lo

def nextLeftVector (m hi : ℝ) : ℂ := cis (-m) * (cis (π / 3) + cis hi)

theorem seam_vectors (m hi lo : ℝ) :
    TipCoordinates.q 0 (cis 0) + cis lo - 1 = rightVector lo ∧
    TipCoordinates.q 1 (cis (-m)) + cis (-m) * cis hi - 1 = nextLeftVector m hi := by
  have hw : w - 1 = cis (2 * π / 3) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, w, cis_re, Real.cos_pi_div_three]
      rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    · simp only [Complex.sub_im, Complex.one_im, sub_zero, w, cis_im]
      rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub]
  have hzero : cis 0 = 1 := by simp [cis]
  constructor
  · simp only [TipCoordinates.q, hzero, mul_one, zero_add, rightVector, ← hw]
    ring
  · simp only [TipCoordinates.q, nextLeftVector, w]
    ring

private theorem right_bisector (lo : ℝ) :
    rightVector lo = ((2 * cos (B lo) : ℝ) : ℂ) * cis ((2 * π / 3 + lo) / 2) :=
  TipRayOrder.cis_add_cis _ _

private theorem next_left_bisector (m hi : ℝ) :
    nextLeftVector m hi = ((2 * cos (A hi) : ℝ) : ℂ) * cis (-m + (π / 3 + hi) / 2) := by
  have h := TipRayOrder.cis_add_cis (π / 3) hi
  have hA : (π / 3 - hi) / 2 = -A hi := by unfold A; ring
  rw [hA, Real.cos_neg] at h
  change cis (π / 3) + cis hi =
    ((2 * cos (A hi) : ℝ) : ℂ) * cis ((π / 3 + hi) / 2) at h
  unfold nextLeftVector
  rw [h]
  calc
    cis (-m) * (((2 * cos (A hi) : ℝ) : ℂ) * cis ((π / 3 + hi) / 2)) =
        ((2 * cos (A hi) : ℝ) : ℂ) *
          (cis (-m) * cis ((π / 3 + hi) / 2)) := by ring
    _ = ((2 * cos (A hi) : ℝ) : ℂ) * cis (-m + (π / 3 + hi) / 2) := by
      rw [← cis_add]

theorem normalized_seam
    (seam_charges : ∀ {a b θ l m r : ℝ},
      0 ≤ a → a ≤ π / 3 → 0 ≤ b → b ≤ π / 3 → 0 ≤ θ →
      0 ≤ l → 0 ≤ m → 0 ≤ r → π / 3 - 2 * a ≤ l → π / 3 - 2 * b ≤ r →
      m = a + θ + b - π / 3 →
      1 ≤ (2 * cos a)^2 + (2 * cos b)^2 - 2 * (2 * cos a) * (2 * cos b) * cos θ →
      b ≤ l + m ∧ a ≤ m + r ∧ π / 3 ≤ l + 2 * m + r)
    {l m r hi lo hiNext loNext : ℝ}
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hl' : l ≤ π / 3) (hm' : m ≤ π / 3) (hr' : r ≤ π / 3)
    (hlo : π / 3 - m ≤ lo) (hhi : hi ≤ 2 * π / 3 + l) (hgap : π / 3 ≤ hi - lo)
    (hloNext : π / 3 - r ≤ loNext) (hhiNext : hiNext ≤ 2 * π / 3 + m)
    (hgapNext : π / 3 ≤ hiNext - loNext)
    (hsep : 1 ≤ dist (rightVector lo) (nextLeftVector m hiNext)) :
    A hiNext ≤ l + m ∧ B lo ≤ m + r ∧ π / 3 ≤ l + 2 * m + r := by
  obtain ⟨_, _, ha, hau, _, hal, _⟩ := heading_bounds hl' hm' hlo hhi hgap
  obtain ⟨hb, hbu, _, _, _, _, hbr⟩ := heading_bounds hm' hr' hloNext hhiNext hgapNext
  let θ := (2 * π / 3 + lo) / 2 - (-m + (π / 3 + hiNext) / 2)
  have hθ : 0 ≤ θ := sub_nonneg.mpr (TipRayOrder.seam_ray_order hlo hhiNext)
  have hmid : m = B lo + θ + A hiNext - π / 3 := by dsimp [A, B, θ]; ring
  have hsq : 1 ≤ dist (rightVector lo) (nextLeftVector m hiNext) ^ 2 := by
    nlinarith only [hsep, sq_nonneg (dist (rightVector lo) (nextLeftVector m hiNext) - 1)]
  rw [right_bisector, next_left_bisector, dist_eq_norm, Complex.sq_norm, normSq_radial_sub] at hsq
  exact seam_charges ha hau hb hbu hθ hl hm hr hal hbr hmid hsq

theorem two_triples_impossible
    (seam_charges : ∀ {a b θ l m r : ℝ},
      0 ≤ a → a ≤ π / 3 → 0 ≤ b → b ≤ π / 3 → 0 ≤ θ →
      0 ≤ l → 0 ≤ m → 0 ≤ r → π / 3 - 2 * a ≤ l → π / 3 - 2 * b ≤ r →
      m = a + θ + b - π / 3 →
      1 ≤ (2 * cos a)^2 + (2 * cos b)^2 - 2 * (2 * cos a) * (2 * cos b) * cos θ →
      b ≤ l + m ∧ a ≤ m + r ∧ π / 3 ≤ l + 2 * m + r)
    (τ hi lo : ℕ → ℝ) (fails : ℕ → Prop)
    (hn : ∀ i < 8, 0 ≤ τ i) (ht : (∑ i ∈ range 8, τ i) < π / 3)
    (hlo : ∀ i < 7, π / 3 - τ (i + 1) ≤ lo i)
    (hhi : ∀ i < 7, hi i ≤ 2 * π / 3 + τ i)
    (hgap : ∀ i < 7, π / 3 ≤ hi i - lo i)
    (hsep : ∀ i < 6, fails i →
      1 ≤ dist (rightVector (lo i)) (nextLeftVector (τ (i + 1)) (hi (i + 1))))
    (first : ∃ i < 3, fails i) (last : ∃ j, 3 ≤ j ∧ j < 6 ∧ fails j) : False := by
  have hu (i : ℕ) (hi : i < 8) : τ i ≤ π / 3 := by
    have h := Finset.single_le_sum (f := τ)
      (fun j hj => hn j (mem_range.mp hj)) (mem_range.mpr hi)
    exact (h.trans ht.le)
  have seam (i : ℕ) (hi' : i < 6) (hf : fails i) :
      A (hi (i + 1)) ≤ τ i + τ (i + 1) ∧
      B (lo i) ≤ τ (i + 1) + τ (i + 2) ∧
      π / 3 ≤ τ i + 2 * τ (i + 1) + τ (i + 2) :=
    normalized_seam (@seam_charges) (hn i (by omega)) (hn (i + 1) (by omega))
      (hn (i + 2) (by omega)) (hu i (by omega)) (hu (i + 1) (by omega))
      (hu (i + 2) (by omega)) (hlo i (by omega)) (hhi i (by omega)) (hgap i (by omega))
      (hlo (i + 1) (by omega)) (hhi (i + 1) (by omega)) (hgap (i + 1) (by omega))
      (hsep i hi' hf)
  obtain ⟨i, hi', fi⟩ := first
  obtain ⟨j, hj, hj', fj⟩ := last
  have n0 := hn 0 (by decide)
  have n1 := hn 1 (by decide)
  have n2 := hn 2 (by decide)
  have n3 := hn 3 (by decide)
  have n4 := hn 4 (by decide)
  have n5 := hn 5 (by decide)
  have n6 := hn 6 (by decide)
  have n7 := hn 7 (by decide)
  have budget := ht
  norm_num [Finset.sum_range_succ] at budget
  by_cases h : j = i + 1
  · have ei : i = 2 := by omega
    have ej : j = 3 := by omega
    subst i
    subst j
    have left := (seam 2 (by decide) fi).1
    have right := (seam 3 (by decide) fj).2.1
    have center : π / 3 ≤ A (hi 3) + B (lo 3) := by
      dsimp [A, B]
      linarith [hgap 3 (by decide)]
    change (hi 3 - π / 3) / 2 ≤ τ 2 + τ 3 at left
    dsimp [B] at right
    norm_num at right
    dsimp [A, B] at center
    linarith only [left, right, center, budget, n0, n1, n6, n7]
  · have left := (seam i (by omega) fi).2.2
    have right := (seam j hj' fj).2.2
    interval_cases i <;> interval_cases j <;> first
    | omega
    | norm_num at left right; linarith only [left, right, budget, n0, n1, n2, n3, n4, n5, n6, n7]

end
end Swanepoel.SeamHeading

namespace Swanepoel.MatchedTips

open CircleMeet TipIndependence

noncomputable section

private theorem root_pos : 0 < Real.sqrt 3 / 2 := by positivity

private theorem norm_w : ‖TipIndependence.w‖ = 1 := by
  change ‖ChainStep.cis (Real.pi / 3)‖ = 1
  simp [ChainStep.cis, Complex.norm_exp, Complex.mul_re]

private theorem norm_one_sub_w : ‖1 - TipIndependence.w‖ = 1 := by
  change ‖1 - ChainStep.w‖ = 1
  rw [ChainStep.one_sub_w]
  simp [ChainStep.cis, Complex.norm_exp, Complex.mul_re]

private theorem flip_unit {x y : ℂ} (h : ‖x - y‖ = 1) : ‖y - x‖ = 1 := by
  rwa [norm_sub_rev]

variable (A : Arc)

private theorem step_re (i : ℕ) : (A.p (i + 1)).re - (A.p i).re = (A.h i).re := by
  simpa only [Complex.sub_re] using congrArg Complex.re (A.step i)

private theorem split_re (i : ℕ) :
    ((1 - w) * A.h i).re + (w * A.h i).re = (A.h i).re := by
  rw [← Complex.add_re, ← add_mul, sub_add_cancel, one_mul]

theorem q_ne_next (i : ℕ) : A.q i ≠ A.q (i + 1) := by
  have hp := A.pair_re i (i + 1) (Nat.le_succ i)
  simp only [Complex.add_re] at hp
  intro he
  have hr := congrArg Complex.re he
  simp only [Arc.q, Complex.add_re] at hr
  linarith only [root_pos, hp, hr, step_re A i, split_re A i]

theorem q_unit_left (i : ℕ) : ‖A.q i - A.p i‖ = 1 := by
  rw [Arc.q, add_sub_cancel_left, norm_mul, norm_w, A.unit i, one_mul]

theorem q_unit_right (i : ℕ) : ‖A.q i - A.p (i + 1)‖ = 1 := by
  have h : A.p (i + 1) - A.q i = (1 - w) * A.h i := by
    unfold Arc.q
    linear_combination A.step i
  rw [norm_sub_rev, h, norm_mul, norm_one_sub_w, A.unit i, one_mul]

theorem z_unit_left (i : ℕ) : ‖A.z i - A.q i‖ = 1 := by
  have h : A.z i - A.q i = w * A.h (i + 1) := by simp [Arc.z, Arc.q, mul_add, add_assoc]
  rw [h, norm_mul, norm_w, A.unit (i + 1), one_mul]

theorem z_unit_right (i : ℕ) : ‖A.z i - A.q (i + 1)‖ = 1 := by
  have h : A.z i - A.q (i + 1) = A.q i - A.p (i + 1) := by
    rw [A.z_eq_q_add_q_sub_p i]
    ring
  rw [h, q_unit_right A i]

theorem matched_eq_tip (i : ℕ) {s r : ℂ} (he : s = r) (hs : s ≠ A.p (i + 1))
    (hl : ‖s - A.q i‖ = 1) (hr : ‖r - A.q (i + 1)‖ = 1) : s = A.z i := by
  have h := common_neighbors_sum (q_ne_next A i) hs hl (he.symm ▸ hr)
    (flip_unit (q_unit_right A i)) (flip_unit (q_unit_left A (i + 1)))
  rw [A.z_eq_q_add_q_sub_p i]
  linear_combination h

private theorem headings_add_ne_zero (i : ℕ) : A.h i + A.h (i + 1) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.zero_re] at hr
  linarith only [root_pos, hr, A.heading_re i, A.heading_re (i + 1)]

private theorem z_ne_p_left (i : ℕ) : A.z i ≠ A.p i := by
  intro he
  have hz : w * (A.h i + A.h (i + 1)) = 0 := by
    change A.p i + w * (A.h i + A.h (i + 1)) = A.p i at he
    linear_combination he
  rcases mul_eq_zero.mp hz with hw | hh
  · have h := norm_w
    rw [hw] at h
    norm_num at h
  · exact headings_add_ne_zero A i hh

private theorem z_ne_p_right (i : ℕ) : A.z i ≠ A.p (i + 2) := by
  intro he
  change A.p i + w * (A.h i + A.h (i + 1)) = A.p (i + 2) at he
  have hz : (1 - w) * (A.h i + A.h (i + 1)) = 0 := by
    linear_combination -he - A.step i - A.step (i + 1)
  rcases mul_eq_zero.mp hz with hw | hh
  · have h := norm_one_sub_w
    rw [hw] at h
    norm_num [hw] at h
  · exact headings_add_ne_zero A i hh

private theorem no_third_common_neighbor {a b x y z : ℂ}
    (hab : a ≠ b) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hxa : ‖x - a‖ = 1) (hxb : ‖x - b‖ = 1)
    (hya : ‖y - a‖ = 1) (hyb : ‖y - b‖ = 1)
    (hza : ‖z - a‖ = 1) (hzb : ‖z - b‖ = 1) : False :=
  (common_neighbor_eq_or_eq hab hxy hxa hxb hya hyb hza hzb).elim hzx hzy

theorem middle_tip_ne_outer_q (i : ℕ) :
    A.z (i + 1) ≠ A.q i ∧ A.z (i + 1) ≠ A.q (i + 3) :=
  ⟨A.z_ne_q_prev i, A.z_ne_q_after (i + 1)⟩

theorem middle_tip_nonadjacent_outer_q (i : ℕ) :
    ‖A.z (i + 1) - A.q i‖ ≠ 1 ∧ ‖A.z (i + 1) - A.q (i + 3)‖ ≠ 1 := by
  constructor
  · intro h
    have hzp : A.z i ≠ A.p (i + 1) := by
      intro he
      have hd := A.dist_z_p_middle i
      norm_num [he] at hd
    exact no_third_common_neighbor (q_ne_next A i) hzp (A.z_ne_next i).symm
      (z_ne_p_left A (i + 1)) (z_unit_left A i) (z_unit_right A i)
      (flip_unit (q_unit_right A i)) (flip_unit (q_unit_left A (i + 1)))
      h (z_unit_left A (i + 1))
  · intro h
    have hzp : A.z (i + 2) ≠ A.p (i + 3) := by
      intro he
      have hd := A.dist_z_p_middle (i + 2)
      norm_num [he] at hd
    exact no_third_common_neighbor (q_ne_next A (i + 2)) hzp (A.z_ne_next (i + 1))
      (z_ne_p_right A (i + 1)) (z_unit_left A (i + 2)) (z_unit_right A (i + 2))
      (flip_unit (q_unit_right A (i + 2))) (flip_unit (q_unit_left A (i + 3)))
      (z_unit_right A (i + 1)) h

theorem standard_neighbors_nodup (i : ℕ) :
    [A.p i, A.p (i + 2), A.q i, A.q (i + 1)].Nodup := by
  have hpp : A.p i ≠ A.p (i + 2) := by
    intro he
    have hd := A.dist_p_p (show i + 2 ≤ i + 2 from le_rfl)
    norm_num [he] at hd
  have hpq : A.p i ≠ A.q (i + 1) := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Arc.q, Complex.add_re] at hr
    linarith only [hr, root_pos, step_re A i, A.heading_re i, A.left_re (i + 1)]
  have hqp : A.p (i + 2) ≠ A.q i := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Arc.q, Complex.add_re] at hr
    linarith only [hr, root_pos, step_re A i, step_re A (i + 1), split_re A i,
      A.heading_re (i + 1), A.right_re i]
  simp [hpp, hpq, hqp, contact_ne (q_unit_left A i), contact_ne (q_unit_right A (i + 1)),
    q_ne_next A i]

end

end Swanepoel.MatchedTips

namespace Swanepoel.LayerIndependent

variable {V : Type*} [DecidableEq V]

def Far (E : V → V → Prop) (x y : V) : Prop := x ≠ y ∧ ¬ E x y

theorem Far.reverse {E : V → V → Prop} (hE : Symmetric E) {x y : V}
    (h : Far E x y) : Far E y x :=
  ⟨h.1.symm, fun hyx => h.2 (hE hyx)⟩

theorem far_of_dist {E : V → V → Prop} {f : V → ℂ} {x y : V}
    (h : 1 < dist (f x) (f y))
    (hE : ∀ {x y}, E x y → dist (f x) (f y) = 1) : Far E x y := by
  constructor
  · rintro rfl
    rw [dist_self] at h
    norm_num at h
  · intro he
    rw [hE he] at h
    exact (lt_irrefl _ h)

private theorem list_far_mem {E : V → V → Prop} (hE : Symmetric E)
    {L : List V} (hL : L.Pairwise (Far E)) :
    ∀ x ∈ L, ∀ y ∈ L, x ≠ y → ¬ E x y := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hL
    intro x hx y hy hxy
    simp only [List.mem_cons] at hx hy
    rcases hx with hxa | hxL
    · subst x
      rcases hy with hya | hyL
      · subst y
        exact (hxy rfl).elim
      · exact (hhead y hyL).2
    · rcases hy with hya | hyL
      · subst y
        exact ((hhead x hxL).reverse hE).2
      · exact ih htail x hxL y hyL hxy

def IndependentExtension (E : V → V → Prop) (C : Finset V) (L : List V) : Prop :=
  L.Nodup ∧ Disjoint C L.toFinset ∧
    (↑(C ∪ L.toFinset) : Set V).Pairwise (fun x y => ¬ E x y)

theorem independentExtension_of_far {E : V → V → Prop} (hE : Symmetric E)
    {C : Finset V} {L : List V} (hC : (C : Set V).Pairwise (fun x y => ¬ E x y))
    (hL : L.Pairwise (Far E)) (hcross : ∀ x ∈ C, ∀ y ∈ L, Far E x y) :
    IndependentExtension E C L := by
  refine ⟨hL.imp (fun h => h.1), Finset.disjoint_left.mpr ?_, ?_⟩
  · intro x hx hy
    exact (hcross x hx x (List.mem_toFinset.mp hy)).1 rfl
  · intro x hx y hy hxy
    change x ∈ C ∪ L.toFinset at hx
    change y ∈ C ∪ L.toFinset at hy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact hC hx hy hxy
    · exact (hcross x hx y (List.mem_toFinset.mp hy)).2
    · exact ((hcross y hy x (List.mem_toFinset.mp hx)).reverse hE).2
    · exact list_far_mem hE hL x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy) hxy

structure BaseSeparation (f : V → ℂ) (p q : ℕ → V) (pNeg : V) (n : ℕ) : Prop where
  pp : ∀ j k, j + 2 ≤ k → k ≤ n → 1 < dist (f (p j)) (f (p k))
  qp_before : ∀ j k, k + 2 ≤ j → j ≤ n → 1 < dist (f (q j)) (f (p k))
  qp_succ : ∀ k, k + 1 ≤ n → 1 < dist (f (q (k + 1))) (f (p k))
  qp_two_after : ∀ j, j + 2 ≤ n → 1 < dist (f (q j)) (f (p (j + 2)))
  neg_p : ∀ j, 2 ≤ j → j ≤ n → 1 < dist (f pNeg) (f (p j))
  neg_q : ∀ j, 1 ≤ j → j ≤ n → 1 < dist (f pNeg) (f (q j))

variable {E : V → V → Prop} {f : V → ℂ} {p q : ℕ → V} {pNeg : V} {n : ℕ}

private theorem prefix_independent (hE : Symmetric E)
    (hunit : ∀ {x y}, E x y → dist (f x) (f y) = 1)
    (B : BaseSeparation f p q pNeg n) {i : ℕ} (hi : i ≤ n)
    (hchord : i % 2 = 0 → Far E pNeg (p 1)) :
    (layerPrefix p pNeg i : Set V).Pairwise (fun x y => ¬ E x y) := by
  have endpoint : ∀ k < i, (k + 1) % 2 = i % 2 → i % 2 = 0 → Far E pNeg (p k) := by
    intro k hk hpar he
    by_cases hk1 : k = 1
    · exact hk1 ▸ hchord he
    · exact far_of_dist (B.neg_p k (by omega) (by omega)) hunit
  intro x hx y hy hxy
  rcases mem_layerPrefix.mp hx with ⟨he, rfl⟩ | ⟨j, hj, hjpar, rfl⟩ <;>
    rcases mem_layerPrefix.mp hy with ⟨he', rfl⟩ | ⟨k, hk, hkpar, rfl⟩
  · exact (hxy rfl).elim
  · exact (endpoint k hk hkpar he).2
  · exact ((endpoint j hj hjpar he').reverse hE).2
  · have hjk : j ≠ k := fun h => hxy (congrArg p h)
    by_cases hlt : j < k
    · exact (far_of_dist (B.pp j k (by omega) (by omega)) hunit).2
    · exact ((far_of_dist (B.pp k j (by omega) (by omega)) hunit).reverse hE).2

private theorem prefix_far_p
    (B : BaseSeparation f p q pNeg n)
    (hunit : ∀ {x y}, E x y → dist (f x) (f y) = 1)
    {i k : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) (hkn : k ≤ n) {x : V} (hx : x ∈ layerPrefix p pNeg i) :
    Far E x (p k) := by
  rcases mem_layerPrefix.mp hx with ⟨_, rfl⟩ | ⟨j, hj, _, rfl⟩
  · exact far_of_dist (B.neg_p k (by omega) hkn) hunit
  · exact far_of_dist (B.pp j k (by omega) hkn) hunit

private theorem prefix_far_q (hE : Symmetric E)
    (B : BaseSeparation f p q pNeg n)
    (hunit : ∀ {x y}, E x y → dist (f x) (f y) = 1)
    {i k : ℕ} (hi : 1 ≤ i)
    (hik : i ≤ k) (hkn : k ≤ n) {x : V} (hx : x ∈ layerPrefix p pNeg i) :
    Far E x (q k) := by
  rcases mem_layerPrefix.mp hx with ⟨_, rfl⟩ | ⟨j, hj, _, rfl⟩
  · exact far_of_dist (B.neg_q k (by omega) hkn) hunit
  · apply Far.reverse hE
    by_cases hjk : j + 1 = k
    · simpa only [hjk] using far_of_dist (B.qp_succ j (by omega)) hunit
    · exact far_of_dist (B.qp_before k j (by omega) hkn) hunit

theorem lemma8_layer_independent (hE : Symmetric E)
    (hunit : ∀ {x y}, E x y → dist (f x) (f y) = 1)
    (B : BaseSeparation f p q pNeg n) {i : ℕ} (hi : 1 ≤ i) (hn : i + 2 ≤ n)
    (hchord : i % 2 = 0 → Far E pNeg (p 1)) :
    IndependentExtension E (layerPrefix p pNeg i) [p (i + 2), q i] := by
  have hpq := (far_of_dist (B.qp_two_after i hn) hunit).reverse hE
  apply independentExtension_of_far hE (prefix_independent hE hunit B (by omega) hchord)
  · apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact hpq
    · simp
  · intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact prefix_far_p B hunit (i := i) (k := i + 2) hi (by omega) hn hx
    · exact prefix_far_q hE B hunit (i := i) (k := i) hi le_rfl (by omega) hx

structure Lemma9TipSeparation (f : V → ℂ) (p q : ℕ → V) (pNeg : V)
    (n a : ℕ) (z : V) : Prop where
  qp_after : ∀ j k, j + 3 ≤ k → k ≤ n → 1 < dist (f (q j)) (f (p k))
  qq_three : ∀ j, j + 3 ≤ n → 1 < dist (f (q j)) (f (q (j + 3)))
  zp_before : ∀ k, k + 2 ≤ a + 1 → 1 < dist (f z) (f (p k))
  zp_after : 1 < dist (f z) (f (p (a + 5)))
  zp_middle : 1 < dist (f z) (f (p (a + 2)))
  neg_z : 1 < dist (f pNeg) (f z)

theorem lemma9_layer_independent (hE : Symmetric E)
    (hunit : ∀ {x y}, E x y → dist (f x) (f y) = 1)
    (B : BaseSeparation f p q pNeg n)
    {a : ℕ} {z : V} (T : Lemma9TipSeparation f p q pNeg n a z)
    (ha : 1 ≤ a) (hn : a + 5 ≤ n)
    (hchord : a % 2 = 0 → Far E pNeg (p 1))
    (hzprev : Far E z (q a)) (hznext : Far E z (q (a + 3))) :
    IndependentExtension E (layerPrefix p pNeg a)
      [q a, p (a + 2), q (a + 3), p (a + 5), z] := by
  have h12 := far_of_dist (B.qp_two_after a (by omega)) hunit
  have h13 := far_of_dist (T.qq_three a (by omega)) hunit
  have h14 := far_of_dist (T.qp_after a (a + 5) (by omega) hn) hunit
  have h15 := hzprev.reverse hE
  have h23 : Far E (p (a + 2)) (q (a + 3)) :=
    (far_of_dist (B.qp_succ (a + 2) (by omega)) hunit).reverse hE
  have h24 := far_of_dist (B.pp (a + 2) (a + 5) (by omega) hn) hunit
  have h25 : Far E (p (a + 2)) z :=
    (far_of_dist T.zp_middle hunit).reverse hE
  have h34 : Far E (q (a + 3)) (p (a + 5)) :=
    far_of_dist (B.qp_two_after (a + 3) (by omega)) hunit
  have h35 := hznext.reverse hE
  have h45 := (far_of_dist T.zp_after hunit).reverse hE
  apply independentExtension_of_far hE (prefix_independent hE hunit B (by omega) hchord)
  · apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h12
      · exact h13
      · exact h14
      · exact h15
    · apply List.pairwise_cons.mpr
      constructor
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact h23
        · exact h24
        · exact h25
      · apply List.pairwise_cons.mpr
        constructor
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact h34
          · exact h35
        · apply List.pairwise_cons.mpr
          constructor
          · intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl
            exact h45
          · apply List.pairwise_cons.mpr
            constructor
            · simp
            · simp
  · intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact prefix_far_q hE B hunit (i := a) (k := a) ha le_rfl (by omega) hx
    · exact prefix_far_p B hunit (i := a) (k := a + 2) ha (by omega) (by omega) hx
    · exact prefix_far_q hE B hunit (i := a) (k := a + 3) ha (by omega) (by omega) hx
    · exact prefix_far_p B hunit (i := a) (k := a + 5) ha (by omega) hn hx
    · rcases mem_layerPrefix.mp hx with ⟨_, rfl⟩ | ⟨k, hk, _, rfl⟩
      · exact far_of_dist T.neg_z hunit
      · exact (far_of_dist (T.zp_before k (by omega)) hunit).reverse hE

end Swanepoel.LayerIndependent

namespace Swanepoel

open ChainStep (cis)

structure FirstLayerPair {V : Type*} [DecidableEq V] (f : V → ℂ) (N : V → Finset V)
    (p q : ℕ → V) (i : ℕ) (θ L R : ℝ) where
  r : V
  s : V
  hi : ℝ
  lo : ℝ
  distinct : r ≠ s
  r_mem : r ∈ N (q i) \ {p i, p (i + 1), q (i - 1), q (i + 1)}
  s_mem : s ∈ N (q i) \ {p i, p (i + 1), q (i - 1), q (i + 1)}
  extras_eq : N (q i) \ {p i, p (i + 1), q (i - 1), q (i + 1)} = {r, s}
  cover : N (q i) ⊆ {p i, p (i + 1), q (i - 1), q (i + 1), r, s}
  lo_bound : Real.pi / 3 - R ≤ lo
  hi_bound : hi ≤ 2 * Real.pi / 3 + L
  gap : Real.pi / 3 ≤ hi - lo
  r_phase : cis hi = cis (-θ) * (f r - f (q i))
  s_phase : cis lo = cis (-θ) * (f s - f (q i))

open scoped Classical in

theorem firstLayerPair {V : Type*} [DecidableEq V]
    (f : V → ℂ) (sep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y))
    (X : Finset V) (E : V → V → Prop) (N : V → Finset V) (p q : ℕ → V)
    (C U : Finset V) (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 11)
    (hC : C.card = i / 2 + 1) (hU : U.card ≤ 3 * C.card)
    (hprefix : ∀ y ∈ C, ∀ x ∈ X, E y x → x ∈ U)
    (hdistinct : [p (i + 2), q i].Nodup)
    (hdisjoint : Disjoint C [p (i + 2), q i].toFinset)
    (hX : C ∪ [p (i + 2), q i].toFinset ⊆ X)
    (hind : (↑(C ∪ [p (i + 2), q i].toFinset) : Set V).Pairwise (fun x y => ¬ E x y))
    (hN : ∀ y ∈ [p (i + 2), q i].toFinset, ∀ x ∈ X, E y x → x ∈ N y)
    (hp : p i ∈ U) (hq : q (i - 1) ∈ U)
    (hdeg : (N (p (i + 2))).card ≤ 4)
    (hp' : p (i + 1) ∈ N (p (i + 2))) (hq' : q (i + 1) ∈ N (p (i + 2)))
    (hexpand : ∀ T : Finset V, T ⊆ X → (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ (X.filter fun x => x ∈ T ∨ ∃ y ∈ T, E y x).card)
    (hunit : ∀ x ∈ N (q i), ‖f x - f (q i)‖ = 1)
    (θ L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R) (hturn : L + R < Real.pi / 3)
    (hstepPrev : f (p (i - 1)) + cis (θ + L) = f (p i))
    (hstep : f (p (i + 1)) = f (p i) + cis θ)
    (htipPrev : f (q (i - 1)) = TipCoordinates.q (f (p (i - 1))) (cis (θ + L)))
    (htip : f (q i) = TipCoordinates.q (f (p i)) (cis θ))
    (htipNext : f (q (i + 1)) = TipCoordinates.q (f (p (i + 1))) (cis (θ - R))) :
    Nonempty (FirstLayerPair f N p q i θ L R) := by
  let O : Finset V := {p i, p (i + 1), q (i - 1), q (i + 1)}
  let extra := N (q i) \ O
  have split : N (q i) ⊆ O ∪ extra := by
    intro x hx
    by_cases ho : x ∈ O
    · exact Finset.mem_union.mpr (Or.inl ho)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, ho⟩))
  have hmore : 1 < extra.card := by
    by_contra! hsmall
    exact lemma8_layer_contradiction X E N p q C U extra i hi hi' hC hU hprefix
      hdistinct hdisjoint hX hind hN hp hq hdeg hp' hq' split hsmall hexpand
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hmore
  have hprev : f (p (i - 1)) = f (p i) - cis (θ + L) := eq_sub_of_add_eq hstepPrev
  obtain ⟨ha, hb, hd, he⟩ := TipCoordinates.firstLayer θ L R (f (p i))
  have ha' : cis (-θ) * (f (p i) - f (q i)) = cis (4 * Real.pi / 3) := by
    rw [htip]; exact ha
  have hb' : cis (-θ) * (f (p (i + 1)) - f (q i)) = cis (5 * Real.pi / 3) := by
    rw [hstep, htip]; exact hb
  have hd' : cis (-θ) * (f (q (i - 1)) - f (q i)) =
      ((2 * Real.cos (Real.pi / 3 - L / 2) : ℝ) : ℂ) * cis (Real.pi + L / 2) := by
    rw [htipPrev, hprev, htip]; exact hd
  have he' : cis (-θ) * (f (q (i + 1)) - f (q i)) =
      ((2 * Real.cos (Real.pi / 3 - R / 2) : ℝ) : ℂ) * cis (-R / 2) := by
    rw [htipNext, hstep, htip]; exact he
  have htwo : extra.card ≤ 2 :=
    LayerWindows.extras_le_two f sep (q i) (p i) (p (i + 1)) (q (i - 1)) (q (i + 1))
      (N (q i)) θ L 0 R (by simpa only [sub_zero] using ha') hb'
      (by simpa only [add_zero, sub_zero] using hd') (by simpa only [zero_add] using he')
      hL le_rfl hR (by simpa only [add_zero] using hturn) hunit
  have outside {z : V} (hz : z ∈ extra) :
      z ≠ p i ∧ z ≠ p (i + 1) ∧ z ≠ q (i - 1) ∧ z ≠ q (i + 1) := by
    have hn := (Finset.mem_sdiff.mp hz).2
    simpa only [O, Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  obtain ⟨r, s, horder, a, b, hlo, hhi, hgap, hr, hs⟩ :=
    LayerWindows.first_pair f sep (q i) (p i) (p (i + 1)) (q (i - 1)) (q (i + 1))
      x y θ L R ha' hb' hd' he' hL hR hturn
      (hunit x (Finset.mem_sdiff.mp hx).1) (hunit y (Finset.mem_sdiff.mp hy).1)
      hxy (outside hx) (outside hy)
  have hmem : r ∈ extra ∧ s ∈ extra ∧ r ≠ s := by
    rcases horder with ⟨hrx, hsy⟩ | ⟨hry, hsx⟩
    · exact ⟨hrx.symm ▸ hx, hsy.symm ▸ hy, hrx.symm ▸ hsy.symm ▸ hxy⟩
    · exact ⟨hry.symm ▸ hy, hsx.symm ▸ hx, hry.symm ▸ hsx.symm ▸ hxy.symm⟩
  have hpair : extra = {r, s} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hmem.1
      · exact hmem.2.1
    · simpa [hmem.2.2] using htwo
  refine ⟨⟨r, s, a, b, hmem.2.2, hmem.1, hmem.2.1, hpair, ?_, hlo, hhi, hgap, hr, hs⟩⟩
  intro z hz
  have hm := split hz
  rw [hpair] at hm
  simp only [O, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
  tauto

end Swanepoel

namespace Swanepoel.NormalGeometry

open Swanepoel.ChainStep

noncomputable section

variable {V : Type*} {m : ℕ} (C : ArcHeading.Chain m) (F : V → ℂ)

def f (x : V) : ℂ := C.frame 0 (F x)

theorem dist_f (x y : V) : dist (f C F x) (f C F y) = dist (F x) (F y) :=
  C.dist_frame 0 _ _

variable {p q z : ℕ → V} {pNeg : V}

theorem p_step {i : ℕ} (hi : i ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) :
    f C F (p (i + 1)) - f C F (p i) = cis (C.θ i) := by
  simpa only [f, hp (i + 1) (by omega), hp i (by omega), zero_add] using C.frame_step 0 hi

theorem q_eq {i : ℕ} (hi : i ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j)) :
    f C F (q i) = f C F (p i) + w * cis (C.θ i) := by
  simpa only [f, hp i (by omega), hq i hi, zero_add] using C.frame_tip 0 hi

theorem z_eq {i : ℕ} (hi : i + 1 ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j))
    (hz : F (z i) = TipCoordinates.z (C.p i) (C.h i) (C.h (i + 1))) :
    f C F (z i) = TipCoordinates.z (f C F (p i)) (cis (C.θ i)) (cis (C.θ (i + 1))) := by
  have h₀ := C.rotate_heading 0 (show i ≤ m by omega)
  have h₁ := C.rotate_heading 0 hi
  simp only [zero_add] at h₀ h₁
  rw [← h₀, ← h₁]
  simp only [f, hz, ← hp i (by omega), TipCoordinates.z, ArcHeading.Chain.frame]
  ring

def horizontalPath (D : ArcHeading.Chain m) : ℕ → ℂ
  | 0 => 0
  | i + 1 => horizontalPath D i + cis (D.θ i)

theorem horizontalPath_eq {i : ℕ} (hi : i ≤ m + 1) :
    horizontalPath C i = C.frame 0 (C.p i) := by
  induction i with
  | zero => simp [horizontalPath]
  | succ i ih =>
      have hs := C.frame_step 0 (show i ≤ m by omega)
      simp only [zero_add] at hs
      rw [horizontalPath, ih (by omega)]
      linear_combination -hs

def suffix : NearTip.Suffix where
  p := horizontalPath C
  θ := C.θ
  p0 := rfl
  θ0 := C.θ_zero
  step i := by rw [horizontalPath, add_sub_cancel_left]
  range i := by
    obtain ⟨hl, hu⟩ := C.θ_bounds i
    exact ⟨by linarith [C.total_lt], hu⟩
  turn i := by
    obtain ⟨hl, _⟩ := C.θ_bounds (i + 1)
    obtain ⟨_, hu⟩ := C.θ_bounds i
    exact ⟨sub_nonneg.mpr (C.θ_antitone (Nat.le_succ i)), by linarith [C.total_lt]⟩

theorem suffix_p (hp : ∀ j ≤ m + 1, C.p j = F (p j)) {i : ℕ} (hi : i ≤ m + 1) :
    (suffix C).p i = f C F (p i) := by
  change horizontalPath C i = C.frame 0 (F (p i))
  rw [horizontalPath_eq C hi, hp i hi]

theorem suffix_q (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j))
    {i : ℕ} (hi : i ≤ m) : (suffix C).q i = f C F (q i) := by
  change (suffix C).p i + w * cis (C.θ i) = f C F (q i)
  rw [suffix_p C F hp (by omega), q_eq C F hi hp hq]

theorem suffix_z (hp : ∀ j ≤ m + 1, C.p j = F (p j)) {i : ℕ} (hi : i + 1 ≤ m)
    (hz : F (z i) = TipCoordinates.z (C.p i) (C.h i) (C.h (i + 1))) :
    (suffix C).z i = f C F (z i) := by
  change (suffix C).p i + w * cis (C.θ i) + w * cis (C.θ (i + 1)) = f C F (z i)
  rw [suffix_p C F hp (by omega), z_eq C F hi hp hz]
  unfold TipCoordinates.z
  ring

private theorem arc_p (hp : ∀ j ≤ m + 1, C.p j = F (p j)) {i : ℕ} (hi : i ≤ m + 1) :
    C.toArc.p i = C.frame C.center (F (p i)) := by rw [C.arc_p hi, hp i hi]

private theorem arc_q (hq : ∀ j ≤ m, C.q j = F (q j)) {i : ℕ} (hi : i ≤ m) :
    C.toArc.q i = C.frame C.center (F (q i)) := by rw [C.arc_q hi, hq i hi]

theorem baseSeparation {n : ℕ} (hn : n ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j))
    {φ : ℝ} (hneg : f C F pNeg = cis φ)
    (hφ₁ : 2 * Real.pi / 3 ≤ φ) (hφ₂ : φ ≤ 5 * Real.pi / 3) :
    LayerIndependent.BaseSeparation F p q pNeg n := by
  constructor
  · intro j k hjk hk
    simpa only [arc_p C F hp (i := j) (by omega), arc_p C F hp (i := k) (by omega),
      C.dist_frame] using C.toArc.dist_p_p hjk
  · intro j k hkj hj
    simpa only [arc_q C F hq (i := j) (by omega), arc_p C F hp (i := k) (by omega),
      C.dist_frame] using C.toArc.dist_q_p_before hkj
  · intro k hk
    simpa only [suffix_q C F hp hq (i := k + 1) (by omega), suffix_p C F hp (i := k) (by omega),
      dist_f] using (suffix C).dist_q_succ_p k
  · intro j hj
    simpa only [suffix_q C F hp hq (i := j) (by omega), suffix_p C F hp (i := j + 2) (by omega),
      dist_f] using (suffix C).dist_q_p_two_after j
  · intro j hj hjn
    simpa only [← hneg, suffix_p C F hp (i := j) (by omega), dist_f] using
      (suffix C).endpoint_dist_p_gt_one φ hφ₁ hφ₂ j hj
  · intro j hj hjn
    simpa only [← hneg, suffix_q C F hp hq (i := j) (by omega), dist_f] using
      (suffix C).endpoint_dist_q_gt_one φ hφ₁ hφ₂ j hj

private theorem rotate_horizontalPath (i : ℕ) :
    cis C.center * horizontalPath C i = C.toArc.p i := by
  change cis C.center * horizontalPath C i = C.centeredPath i
  induction i with
  | zero => simp [horizontalPath, ArcHeading.Chain.centeredPath]
  | succ i ih =>
      rw [horizontalPath, ArcHeading.Chain.centeredPath, mul_add, ih, ArcHeading.Chain.angle, cis_add]

private theorem rotate_z (i : ℕ) : cis C.center * (suffix C).z i = C.toArc.z i := by
  change cis C.center * (horizontalPath C i + w * cis (C.θ i) + w * cis (C.θ (i + 1))) =
    C.toArc.p i + w * (cis (C.angle i) + cis (C.angle (i + 1)))
  rw [← rotate_horizontalPath C i]
  simp only [ArcHeading.Chain.angle, cis_add]
  ring

private theorem rotate_frame (x : ℂ) :
    cis C.center * C.frame 0 x = C.frame C.center x := by
  simp [ArcHeading.Chain.frame, ArcHeading.Chain.rotation, cis, mul_assoc]

private theorem dist_rotate (a : ℝ) (u v : ℂ) :
    dist (cis a * u) (cis a * v) = dist u v := by
  have h : ‖cis a‖ = 1 := by simp [cis, Complex.norm_exp, Complex.mul_re]
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, h, one_mul]

private structure IdealTipBounds (p q : ℕ → ℂ) (pNeg z : ℂ) (n a : ℕ) : Prop where
  qp_after : ∀ j k, j + 3 ≤ k → k ≤ n → 1 < dist (q j) (p k)
  qq_three : ∀ j, j + 3 ≤ n → 1 < dist (q j) (q (j + 3))
  zp_before : ∀ k, k + 2 ≤ a + 1 → 1 < dist z (p k)
  zp_after : 1 < dist z (p (a + 5))
  zp_middle : 1 < dist z (p (a + 2))
  neg_z : 1 < dist pNeg z

private theorem idealTipBounds {n a : ℕ} (ha : 1 ≤ a) (han : a + 5 ≤ n) (hn : n ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j))
    {φ : ℝ} (hneg : f C F pNeg = cis φ)
    (hφ₁ : 2 * Real.pi / 3 ≤ φ) (hφ₂ : φ ≤ 5 * Real.pi / 3) :
    IdealTipBounds (fun i => f C F (p i)) (fun i => f C F (q i)) (f C F pNeg)
      ((suffix C).z (a + 1)) n a := by
  have hpc (i : ℕ) (hi : i ≤ m + 1) : C.toArc.p i = cis C.center * f C F (p i) := by
    rw [arc_p C F hp hi, f, rotate_frame]
  have hqc (i : ℕ) (hi : i ≤ m) : C.toArc.q i = cis C.center * f C F (q i) := by
    rw [arc_q C F hq hi, f, rotate_frame]
  have hzc : C.toArc.z (a + 1) = cis C.center * (suffix C).z (a + 1) :=
    (rotate_z C (a + 1)).symm
  constructor
  · intro j k hjk hk
    simpa only [hqc j (by omega), hpc k (by omega), dist_rotate] using
      C.toArc.dist_q_p_after hjk
  · intro j hj
    simpa only [hqc j (by omega), hqc (j + 3) (by omega), dist_rotate] using
      C.toArc.dist_q_q_three j
  · intro k hkj
    simpa only [hzc, hpc k (by omega), dist_rotate] using
      C.toArc.dist_z_p_before hkj
  · simpa only [hzc, hpc (a + 5) (by omega), dist_rotate] using
      C.toArc.dist_z_p_after (j := a + 1) (k := a + 5) (by omega)
  · simpa only [hzc, hpc (a + 2) (by omega), dist_rotate] using
      C.toArc.dist_z_p_middle (a + 1)
  · have hcap : 2 ≤ a + 1 := by omega
    simpa only [← hneg, hzc] using
      (suffix C).endpoint_dist_z_gt_one φ hφ₁ hφ₂ (a + 1) hcap

theorem layer9TipBounds {n a : ℕ} (ha : 1 ≤ a) (han : a + 5 ≤ n) (hn : n ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j))
    {φ : ℝ} (hneg : f C F pNeg = cis φ)
    (hφ₁ : 2 * Real.pi / 3 ≤ φ) (hφ₂ : φ ≤ 5 * Real.pi / 3)
    (hz : F (z (a + 1)) = TipCoordinates.z (C.p (a + 1)) (C.h (a + 1)) (C.h (a + 2))) :
    LayerIndependent.Lemma9TipSeparation F p q pNeg n a (z (a + 1)) := by
  have T := idealTipBounds C F ha han hn hp hq hneg hφ₁ hφ₂ (a := a)
  have hz' := suffix_z C F (z := z) hp (i := a + 1) (by omega) hz
  constructor
  · intro j k hjk hk
    simpa only [dist_f] using T.qp_after j k hjk hk
  · intro j hj
    simpa only [dist_f] using T.qq_three j hj
  · intro k hka
    simpa only [hz', dist_f] using T.zp_before k hka
  · simpa only [hz', dist_f] using T.zp_after
  · simpa only [hz', dist_f] using T.zp_middle
  · simpa only [hz', dist_f] using T.neg_z

end
end Swanepoel.NormalGeometry

namespace Swanepoel.Layer9Glue

open Swanepoel.ChainStep

open scoped Classical in

theorem lemma9_of_three_matched_seams {V : Type*} [DecidableEq V]
    (X : Finset V) (E : V → V → Prop) (f : V → ℂ)
    (p q r s z : ℕ → V) (C U : Finset V) (a : ℕ) (ha : 2 ≤ a) (ha' : a ≤ 5)
    (sep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y))
    (hunit : ∀ {x y}, E x y → dist (f x) (f y) = 1)
    (hC : C.card = a / 2 + 1) (hU : U.card ≤ 3 * C.card)
    (hprefix : ∀ y ∈ C, ∀ x ∈ X, E y x → x ∈ U)
    (hpU : p a ∈ U) (hqU : q (a - 1) ∈ U)
    (hind : LayerIndependent.IndependentExtension E C
      [q a, p (a + 2), q (a + 3), p (a + 5), z (a + 1)])
    (hX : C ∪ [q a, p (a + 2), q (a + 3), p (a + 5), z (a + 1)].toFinset ⊆ X)
    (hqN : ∀ i, i = a ∨ i = a + 3 → ∀ x ∈ X, E (q i) x →
      x ∈ ({p i, p (i + 1), q (i - 1), q (i + 1), r i, s i} : Finset V))
    (hpN : ∀ i, i = a + 2 ∨ i = a + 5 → ∀ x ∈ X, E (p i) x →
      x ∈ ({p (i - 1), p (i + 1), q (i - 1), q i} : Finset V))
    (hmatch : ∀ i, a ≤ i → i ≤ a + 2 → r (i + 1) = s i)
    (hvertex : ∀ i, a ≤ i → i ≤ a + 2 → z i = s i)
    (θ τ : ℕ → ℝ)
    (hstep : ∀ i, a ≤ i → i ≤ a + 1 → f (p (i + 1)) - f (p i) = cis (θ i))
    (hq : ∀ i, a + 1 ≤ i → i ≤ a + 2 → f (q i) = TipCoordinates.q (f (p i)) (cis (θ i)))
    (hz : ∀ i, a ≤ i → i ≤ a + 2 →
      f (z i) = TipCoordinates.z (f (p i)) (cis (θ i)) (cis (θ (i + 1))))
    (hθ : ∀ i, a ≤ i → i ≤ a + 2 → θ (i + 1) = θ i - τ (i + 1))
    (hτ : ∀ i, a + 1 ≤ i → i ≤ a + 3 → 0 ≤ τ i)
    (hbudget : τ (a + 1) + τ (a + 2) + τ (a + 3) < Real.pi / 3)
    (hexpand : ∀ T : Finset V, T ⊆ X → (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ (X.filter fun x => x ∈ T ∨ ∃ y ∈ T, E y x).card) :
    False := by
  classical
  let N (y : V) := X.filter (E y)
  let extra := N (s (a + 1)) \ {q (a + 1), q (a + 2), s a, s (a + 2)}
  have hleft : θ a = θ (a + 1) + τ (a + 1) := by
    linarith only [hθ a le_rfl (by omega)]
  have hmiddle := hθ (a + 1) (by omega) (by omega)
  have hright : θ (a + 3) = θ (a + 1) - τ (a + 2) - τ (a + 3) := by
    linarith only [hmiddle, hθ (a + 2) (by omega) le_rfl]
  have hpLeft : f (p a) = f (p (a + 1)) - cis (θ (a + 1) + τ (a + 1)) := by
    rw [← hleft]
    linear_combination -(hstep a le_rfl (by omega))
  have hpRight : f (p (a + 2)) = f (p (a + 1)) + cis (θ (a + 1)) := by
    linear_combination hstep (a + 1) (by omega) le_rfl
  have hza := (congrArg f (hvertex a le_rfl (by omega))).symm.trans (hz a le_rfl (by omega))
  have hzb := (congrArg f (hvertex (a + 1) (by omega) (by omega))).symm.trans
    (hz (a + 1) (by omega) (by omega))
  have hzc := (congrArg f (hvertex (a + 2) (by omega) le_rfl)).symm.trans
    (hz (a + 2) (by omega) le_rfl)
  have hobstacles := TipCoordinates.matchedSecondLayer (θ (a + 1)) (τ (a + 1)) (τ (a + 2))
    (τ (a + 3)) (f (p (a + 1)))
  have hextra : extra.card ≤ 2 := by
    apply LayerWindows.extras_le_two f sep (s (a + 1)) (q (a + 1)) (q (a + 2)) (s a)
      (s (a + 2)) (N (s (a + 1))) (θ (a + 1)) (τ (a + 1)) (τ (a + 2)) (τ (a + 3))
    · simpa only [hq (a + 1) le_rfl (by omega), hzb, hmiddle] using hobstacles.1
    · simpa only [hq (a + 2) (by omega) le_rfl, hzb, hmiddle, hpRight] using hobstacles.2.1
    · simpa only [hza, hzb, hleft, hmiddle, hpLeft] using hobstacles.2.2.1
    · simpa only [hzc, hzb, hmiddle, hright, hpRight] using hobstacles.2.2.2
    · exact hτ (a + 1) le_rfl (by omega)
    · exact hτ (a + 2) (by omega) (by omega)
    · exact hτ (a + 3) (by omega) le_rfl
    · exact hbudget
    · intro x hx
      have he := hunit (Finset.mem_filter.mp hx).2
      rw [dist_eq_norm, norm_sub_rev] at he
      exact he
  have hzs := hvertex (a + 1) (by omega) (by omega)
  rw [hzs] at hind hX
  obtain ⟨hdistinct, hdisjoint, hind⟩ := hind
  refine lemma9_layer_contradiction X E N p q r s C U extra a (by omega) ha' hC hU hprefix
    hdistinct hdisjoint hX hind ?_ hpU hqU ?_ ?_ ?_ ?_ ?_ hextra hexpand
  · intro y _ x hx he
    exact Finset.mem_filter.mpr ⟨hx, he⟩
  · intro x hx
    exact hqN a (Or.inl rfl) x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro x hx
    simpa only [show a + 2 - 1 = a + 1 by omega] using
      hpN (a + 2) (Or.inl rfl) x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro x hx
    have hlast : r (a + 3) = s (a + 2) := hmatch (a + 2) (by omega) le_rfl
    simpa only [show a + 3 - 1 = a + 2 by omega, hlast] using
      hqN (a + 3) (Or.inr rfl) x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro x hx
    simpa only [show a + 5 - 1 = a + 4 by omega] using
      hpN (a + 5) (Or.inr rfl) x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro x hx
    by_cases hm : x ∈ ({q (a + 1), q (a + 2), s a, s (a + 2)} : Finset V)
    · exact Finset.mem_union.mpr (Or.inl hm)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hm⟩))

end Swanepoel.Layer9Glue

namespace Swanepoel

open ChainStep
open scoped BigOperators

private theorem seam_rotate (θ ψ : ℝ) : cis (-θ) * cis (θ + ψ) = cis ψ := by
  rw [← cis_add, neg_add_cancel_left]

private theorem seam_distance (f : V → ℂ) (p q r s : ℕ → V) (θ τ hi lo : ℕ → ℝ)
    (i : ℕ) (hs : f (p (i + 1)) - f (p i) = cis (θ i))
    (hq : f (q i) = f (p i) + w * cis (θ i))
    (hqn : f (q (i + 1)) = f (p (i + 1)) + w * cis (θ (i + 1)))
    (ht : θ (i + 1) = θ i - τ (i + 1))
    (hr : cis (hi (i + 1)) = cis (-θ (i + 1)) * (f (r (i + 1)) - f (q (i + 1))))
    (hl : cis (lo i) = cis (-θ i) * (f (s i) - f (q i))) :
    dist (SeamHeading.rightVector (lo i))
      (SeamHeading.nextLeftVector (τ (i + 1)) (hi (i + 1))) =
      dist (f (s i)) (f (r (i + 1))) := by
  have h1 : cis (-θ i) * cis (θ i) = 1 := by rw [← cis_add, neg_add_cancel]; simp [cis]
  have h2 : cis (-θ i) * cis (θ (i + 1)) = cis (-τ (i + 1)) := by
    rw [ht, sub_eq_add_neg, seam_rotate]
  have h3 : cis (-τ (i + 1)) * cis (-θ (i + 1)) = cis (-θ i) := by
    rw [← cis_add, ht]
    congr 1
    ring
  have hv := SeamHeading.seam_vectors (τ (i + 1)) (hi (i + 1)) (lo i)
  have h0 : cis 0 = 1 := by simp [cis]
  have hleft : cis (-θ i) * (f (s i) - f (p (i + 1))) =
      SeamHeading.rightVector (lo i) := by
    rw [← hv.1, hl, h0]
    dsimp [TipCoordinates.q]
    calc
      _ = cis (-θ i) * (f (s i) - f (q i)) +
          cis (-θ i) * (f (q i) - f (p (i + 1))) := by ring
      _ = _ := by
        rw [hq, show f (p (i + 1)) = f (p i) + cis (θ i) by linear_combination hs]
        calc
          _ = cis (-θ i) * (f (s i) - (f (p i) + w * cis (θ i))) +
              (w - 1) * (cis (-θ i) * cis (θ i)) := by ring
          _ = _ := by rw [h1]; ring
  have hright : cis (-θ i) * (f (r (i + 1)) - f (p (i + 1))) =
      SeamHeading.nextLeftVector (τ (i + 1)) (hi (i + 1)) := by
    rw [← hv.2, hr]
    dsimp [TipCoordinates.q]
    calc
      _ = cis (-θ i) * (f (r (i + 1)) - f (q (i + 1))) +
          cis (-θ i) * (f (q (i + 1)) - f (p (i + 1))) := by ring
      _ = _ := by
        rw [hqn, ← mul_assoc, h3]
        calc
          _ = cis (-θ i) * (f (r (i + 1)) - (f (p (i + 1)) + w * cis (θ (i + 1)))) +
              w * (cis (-θ i) * cis (θ (i + 1))) := by ring
          _ = _ := by rw [h2]; ring
  rw [← hleft, ← hright, LayerWindows.dist_frame]

private theorem turn_sum_subset {m : ℕ} (τ : ℕ → ℝ)
    (hn : ∀ i < m, 0 ≤ τ (i + 1)) {a t : ℕ} (ht : a + t ≤ m) :
    (∑ i ∈ Finset.range t, τ (a + i + 1)) ≤ ArcHeading.turnSum τ m := by
  let e : ℕ ↪ ℕ := ⟨fun i => a + i, fun _ _ h => Nat.add_left_cancel h⟩
  unfold ArcHeading.turnSum
  change (∑ i ∈ Finset.range t, τ (e i + 1)) ≤ _
  rw [← Finset.sum_map (Finset.range t) e (fun j => τ (j + 1))]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    have hj' := Finset.mem_range.mp hj
    change a + j = i at hji
    exact Finset.mem_range.mpr (by omega)
  · intro i hi _
    exact hn i (Finset.mem_range.mp hi)

theorem exists_matched_triple (f : V → ℂ) (p q r s : ℕ → V) (θ τ hi lo : ℕ → ℝ)
    (sep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y))
    (hstep : ∀ i < 9, f (p (i + 1)) - f (p i) = cis (θ i))
    (hq : ∀ i < 9, f (q i) = f (p i) + w * cis (θ i))
    (hθ : ∀ i < 8, θ (i + 1) = θ i - τ (i + 1))
    (hn : ∀ i < 9, 0 ≤ τ (i + 1)) (ht : ArcHeading.turnSum τ 9 < Real.pi / 3)
    (hlo : ∀ i, 2 ≤ i → i ≤ 8 → Real.pi / 3 - τ (i + 1) ≤ lo i)
    (hhi : ∀ i, 2 ≤ i → i ≤ 8 → hi i ≤ 2 * Real.pi / 3 + τ i)
    (hgap : ∀ i, 2 ≤ i → i ≤ 8 → Real.pi / 3 ≤ hi i - lo i)
    (hr : ∀ i, 2 ≤ i → i ≤ 8 → cis (hi i) = cis (-θ i) * (f (r i) - f (q i)))
    (hs : ∀ i, 2 ≤ i → i ≤ 8 → cis (lo i) = cis (-θ i) * (f (s i) - f (q i))) :
    ∃ a, (a = 2 ∨ a = 5) ∧ s a = r (a + 1) ∧ s (a + 1) = r (a + 2) ∧
      s (a + 2) = r (a + 3) := by
  classical
  by_contra h
  have ht' := (turn_sum_subset τ hn (a := 1) (t := 8) (by decide)).trans_lt ht
  have first : ∃ i < 3, s (2 + i) ≠ r (2 + (i + 1)) := by
    by_contra! hc
    exact h ⟨2, Or.inl rfl, hc 0 (by decide), hc 1 (by decide), hc 2 (by decide)⟩
  have last : ∃ i, 3 ≤ i ∧ i < 6 ∧ s (2 + i) ≠ r (2 + (i + 1)) := by
    by_contra! hc
    exact h ⟨5, Or.inr rfl, hc 3 (by decide) (by decide), hc 4 (by decide) (by decide),
      hc 5 (by decide) (by decide)⟩
  refine SeamHeading.two_triples_impossible (@Charges.seam_charges) (fun i => τ (2 + i))
    (fun i => hi (2 + i)) (fun i => lo (2 + i))
    (fun i => s (2 + i) ≠ r (2 + (i + 1))) ?_ ?_ ?_ ?_ ?_ ?_ first last
  · intro i hi
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn (1 + i) (by omega)
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht'
  · intro i hi
    exact hlo (2 + i) (by omega) (by omega)
  · intro i hi'
    exact hhi (2 + i) (by omega) (by omega)
  · intro i hi'
    exact hgap (2 + i) (by omega) (by omega)
  · intro i hi' hne
    simp only [← Nat.add_assoc] at hne ⊢
    rw [seam_distance f p q r s θ τ hi lo (2 + i) (hstep _ (by omega)) (hq _ (by omega))
      (hq _ (by omega)) (hθ _ (by omega)) (hr _ (by omega) (by omega)) (hs _ (by omega) (by omega))]
    exact sep hne

end Swanepoel

namespace Swanepoel.ActualMatchedTips

noncomputable section

variable {V : Type*} {m : ℕ} (C : ArcHeading.Chain m) (F : V → ℂ)
variable {p q z r : ℕ → V}

private theorem frame_norm (x y : ℂ) :
    ‖C.frame C.center x - C.frame C.center y‖ = ‖x - y‖ := by
  simpa only [dist_eq_norm] using C.dist_frame C.center x y

private theorem frame_injective : Function.Injective (C.frame C.center) := by
  intro x y h
  apply dist_eq_zero.mp
  rw [← C.dist_frame C.center x y, h, dist_self]

private theorem arc_tip {i : ℕ} (hi : i + 1 ≤ m) :
    C.toArc.z i = C.frame C.center (TipCoordinates.z (C.p i) (C.h i) (C.h (i + 1))) := by
  change C.toArc.p i + ChainStep.w * (ChainStep.cis (C.angle i) +
    ChainStep.cis (C.angle (i + 1))) = _
  rw [C.arc_p (show i ≤ m + 1 by omega)]
  change C.frame C.center (C.p i) + ChainStep.w * (ChainStep.cis (C.center + C.θ i) +
    ChainStep.cis (C.center + C.θ (i + 1))) = _
  rw [← C.rotate_heading C.center (show i ≤ m by omega), ← C.rotate_heading C.center hi]
  unfold TipCoordinates.z ArcHeading.Chain.frame
  ring

structure SeamMatch (p q : ℕ → V) (i : ℕ) (s t : V) : Prop where
  eq_image : F s = F t
  left_unit : ‖F s - F (q i)‖ = 1
  right_unit : ‖F t - F (q (i + 1))‖ = 1
  ne_contact : F s ≠ F (p (i + 1))

theorem matched_eq_tip {i : ℕ} (hi : i + 1 ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j))
    {s t : V} (H : SeamMatch F p q i s t) :
    F s = TipCoordinates.z (C.p i) (C.h i) (C.h (i + 1)) := by
  apply frame_injective C
  rw [← arc_tip C hi]
  refine MatchedTips.matched_eq_tip C.toArc i (congrArg (C.frame C.center) H.eq_image) ?_ ?_ ?_
  · rw [C.arc_p (show i + 1 ≤ m + 1 by omega), hp _ (by omega)]
    exact fun h => H.ne_contact (frame_injective C h)
  · rw [C.arc_q (show i ≤ m by omega), hq _ (by omega), frame_norm]
    exact H.left_unit
  · rw [C.arc_q hi, hq _ hi, frame_norm]
    exact H.right_unit

theorem middle_far_outer_q {i : ℕ} (hi : i + 3 ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j))
    {s t : V} (H : SeamMatch F p q (i + 1) s t) {E : V → V → Prop}
    (hE : ∀ ⦃x y⦄, E x y → ‖F x - F y‖ = 1) :
    LayerIndependent.Far E s (q i) ∧ LayerIndependent.Far E s (q (i + 3)) := by
  have hz := matched_eq_tip C F (by omega) hp hq H
  have hzc : C.toArc.z (i + 1) = C.frame C.center (F s) := by
    rw [arc_tip C (show i + 1 + 1 ≤ m by omega), ← hz]
  have hqc (j : ℕ) (hj : j ≤ m) : C.toArc.q j = C.frame C.center (F (q j)) := by
    rw [C.arc_q hj, hq j hj]
  have hn := MatchedTips.middle_tip_ne_outer_q C.toArc i
  have hu := MatchedTips.middle_tip_nonadjacent_outer_q C.toArc i
  have far (j : ℕ) (hj : j ≤ m) (hne : C.toArc.z (i + 1) ≠ C.toArc.q j)
      (hunit : ‖C.toArc.z (i + 1) - C.toArc.q j‖ ≠ 1) : LayerIndependent.Far E s (q j) := by
    rw [hzc, hqc j hj] at hne hunit
    rw [frame_norm] at hunit
    exact ⟨fun h => hne (congrArg (C.frame C.center ∘ F) h), fun h => hunit (hE h)⟩
  exact ⟨far i (by omega) hn.1 hu.1, far (i + 3) hi hn.2 hu.2⟩

def standardNeighbors (p q : ℕ → V) (i : ℕ) : List V :=
  [p i, p (i + 2), q i, q (i + 1)]

theorem standard_neighbors_nodup {i : ℕ} (hi : i + 1 ≤ m)
    (hp : ∀ j ≤ m + 1, C.p j = F (p j)) (hq : ∀ j ≤ m, C.q j = F (q j)) :
    (standardNeighbors p q i).Nodup := by
  have hmap : ((standardNeighbors p q i).map (C.frame C.center ∘ F)).Nodup := by
    have h := MatchedTips.standard_neighbors_nodup C.toArc i
    rw [C.arc_p (show i ≤ m + 1 by omega), C.arc_p (show i + 2 ≤ m + 1 by omega),
      C.arc_q (show i ≤ m by omega), C.arc_q hi, hp i (by omega), hp (i + 2) (by omega),
      hq i (by omega), hq (i + 1) hi] at h
    exact h
  generalize standardNeighbors p q i = l at hmap ⊢
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hmap
    exact List.nodup_cons.mpr ⟨fun h => hmap.1 (List.mem_map.mpr ⟨x, h, rfl⟩), ih hmap.2⟩

end
end Swanepoel.ActualMatchedTips

namespace Swanepoel

open ChainStep
open scoped BigOperators

noncomputable section

variable {V : Type*} [DecidableEq V]

private theorem prefix_inj (p : ℕ → V) (pNeg : V) (i : ℕ)
    (hp : Set.InjOn p {j | j < i}) (hneg : ∀ j < i, pNeg ≠ p j) :
    Set.InjOn (layerPrefixVertex p pNeg i) ↑(Finset.range (i / 2 + 1)) := by
  intro j hj k hk he
  replace hj := Finset.mem_range.mp (Finset.mem_coe.mp hj)
  replace hk := Finset.mem_range.mp (Finset.mem_coe.mp hk)
  by_cases hpar : i % 2 = 0
  · by_cases hj0 : j = 0 <;> by_cases hk0 : k = 0
    · exact hj0.trans hk0.symm
    · exact (hneg (2 * k - 1) (by omega)
        (by simpa [layerPrefixVertex, hpar, hj0, hk0] using he)).elim
    · exact (hneg (2 * j - 1) (by omega)
        (by simpa [layerPrefixVertex, hpar, hj0, hk0] using he.symm)).elim
    · have h := hp (show 2 * j - 1 < i by omega) (show 2 * k - 1 < i by omega)
        (by simpa [layerPrefixVertex, hpar, hj0, hk0] using he)
      omega
  · have h := hp (show 2 * j < i by omega) (show 2 * k < i by omega)
      (by simpa [layerPrefixVertex, hpar] using he)
    omega

open scoped Classical in
private theorem gentle_arc_false [Fintype V] (C : ArcHeading.Chain 12) (F : V → ℂ)
    (E : V → V → Prop) (p q : ℕ → V) (pNeg : V)
    (hE : Symmetric E) (hunit : ∀ {x y}, E x y → dist (F x) (F y) = 1)
    (hsep : ∀ {x y}, x ≠ y → 1 ≤ dist (F x) (F y))
    (hp : ∀ j ≤ 13, C.p j = F (p j)) (hq : ∀ j ≤ 12, C.q j = F (q j))
    (hφ : ∃ φ, 2 * Real.pi / 3 ≤ φ ∧ φ ≤ 5 * Real.pi / 3 ∧ NormalGeometry.f C F pNeg = cis φ)
    (hpinj : Set.InjOn p (Set.Iic 12)) (hneg : ∀ j ≤ 12, pNeg ≠ p j)
    (hchord : ¬ E pNeg (p 1))
    (hedge : ∀ j < 12, E (p j) (p (j + 1)))
    (htip : ∀ j < 12, E (p j) (q j) ∧ E (p (j + 1)) (q j))
    (hdeg : ∀ j, 1 ≤ j → j ≤ 12 → ((Finset.univ : Finset V).filter (E (p j))).card = 4)
    (hzero : ((Finset.univ : Finset V).filter (E (p 0))).card = 3)
    (hterminal : (((Finset.univ : Finset V).filter (E pNeg)).card ≤ 3 ∧ E pNeg (p 0)) ∨
      (((Finset.univ : Finset V).filter (E pNeg)).card ≤ 4 ∧ E pNeg (p 0) ∧ E pNeg (q 0)))
    (hexpand : ∀ T : Finset V, (T : Set V).Pairwise (fun x y => ¬ E x y) →
      T.card ≤ 8 → 4 * T.card ≤ ((Finset.univ : Finset V).filter fun x =>
        x ∈ T ∨ ∃ y ∈ T, E y x).card) : False := by
  classical
  let N (v : V) := (Finset.univ : Finset V).filter (E v)
  let f := NormalGeometry.f C F
  let P (i : ℕ) := layerPrefix p pNeg i
  let U (i : ℕ) := (P i).biUnion N
  have hn : ∀ {v w}, w ∈ N v ↔ E v w := by simp [N]
  have hN (y x : V) (he : E y x) : x ∈ N y := hn.mpr he
  have he' (T : Finset V) (_ : T ⊆ Finset.univ) := hexpand T
  have hu : ∀ {x y}, E x y → dist (f x) (f y) = 1 := by
    intro x y h
    rw [NormalGeometry.dist_f]
    exact hunit h
  have hfsep : ∀ {x y}, x ≠ y → 1 ≤ dist (f x) (f y) := by
    intro x y h
    rw [NormalGeometry.dist_f]
    exact hsep h
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := hφ
  have B := NormalGeometry.baseSeparation C F (n := 12) le_rfl hp hq hφ₃ hφ₁ hφ₂
  have hfar : LayerIndependent.Far E pNeg (p 1) := ⟨hneg 1 (by decide), hchord⟩
  have hcard (i : ℕ) (hi : i ≤ 8) : (P i).card = i / 2 + 1 := by
    apply layerPrefix_card (prefix_inj p pNeg i _ _)
    · intro j hj k hk
      change j < i at hj
      change k < i at hk
      exact hpinj (by simp only [Set.mem_Iic]; omega) (by simp only [Set.mem_Iic]; omega)
    · exact fun j hj => hneg j (by omega)
  have hpcard (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 8) : (U i).card ≤ 3 * (P i).card := by
    rw [hcard i hi']
    apply layerPrefix_biUnion_card N p q pNeg i (by omega)
    · intro j hj
      by_cases hz : j = 0
      · simpa only [hz] using hzero.le.trans (by decide : 3 ≤ 4)
      · exact (hdeg j (by omega) (by omega)).le
    · exact hzero.le
    · rcases hterminal with h | h
      · exact Or.inl ⟨h.1, hN _ _ h.2⟩
      · have ht := htip 0 (by decide)
        refine Or.inr ⟨h.1, ?_, hN _ _ h.2.1, hN _ _ h.2.2,
          hN _ _ (hE (hedge 0 (by decide))), hN _ _ ht.2⟩
        intro heq
        have he := hunit ht.1
        rw [heq, dist_self] at he
        norm_num at he
    · intro j hj
      exact hN _ _ (hedge j (by omega))
    · intro j hj
      exact hN _ _ (hE (hedge j (by omega)))
  have hprefix (i : ℕ) (y : V) (hy : y ∈ P i) (x : V) (_ : x ∈ (Finset.univ : Finset V))
      (he : E y x) : x ∈ U i := Finset.mem_biUnion.mpr ⟨y, hy, hN _ _ he⟩
  have hpu (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 8) : p i ∈ U i ∧ q (i - 1) ∈ U i := by
    have he : i - 1 + 1 = i := by omega
    apply layerPrefix_boundary (by omega)
    exact ⟨hN _ _ (by simpa only [he] using hedge (i - 1) (by omega)),
      hN _ _ (htip (i - 1) (by omega)).1⟩
  have hstep (i : ℕ) (hi : i ≤ 12) : f (p (i + 1)) - f (p i) = cis (C.θ i) :=
    NormalGeometry.p_step C F hi hp
  have hcoordQ (i : ℕ) (hi : i ≤ 12) : f (q i) = TipCoordinates.q (f (p i)) (cis (C.θ i)) :=
    NormalGeometry.q_eq C F hi hp hq
  have htwo (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 8) :
      C.τ i + C.τ (i + 1) < Real.pi / 3 := by
    have hb := (turn_sum_subset C.τ C.turn_nonneg (a := i - 1) (t := 2) (by omega)).trans_lt C.total_lt
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at hb
    simpa only [show i - 1 + 1 = i by omega, show i - 1 + 1 + 1 = i + 1 by omega] using hb
  have hPair (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 8) :
      Nonempty (FirstLayerPair f N p q i (C.θ i) (C.τ i) (C.τ (i + 1))) := by
    obtain ⟨hd, hdisj, hind⟩ := LayerIndependent.lemma8_layer_independent hE hunit B hi
      (by omega : i + 2 ≤ 12) (fun _ => hfar)
    have hiEq : i - 1 + 1 = i := by omega
    have hθPrev : C.θ (i - 1) = C.θ i + C.τ i := by
      have h := C.θ_succ (show i - 1 < 12 by omega)
      rw [hiEq] at h
      linarith only [h]
    have hτPrev : 0 ≤ C.τ i := by simpa only [hiEq] using C.turn_nonneg (i - 1) (by omega)
    refine firstLayerPair f hfsep Finset.univ E N p q (P i) (U i) i hi (by omega)
      (hcard i hi') (hpcard i hi hi') (hprefix i) hd hdisj (Finset.subset_univ _) hind
      (fun y _ x _ => hN y x) (hpu i hi hi').1 (hpu i hi hi').2
      (hdeg (i + 2) (by omega) (by omega)).le (hN _ _ (hE (hedge (i + 1) (by omega))))
      (hN _ _ (htip (i + 1) (by omega)).2) he' ?_ (C.θ i) (C.τ i) (C.τ (i + 1))
      hτPrev (C.turn_nonneg i (by omega)) (htwo i hi hi') ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hu (hn.mp hx)
    · have hs := hstep (i - 1) (by omega)
      rw [hiEq, hθPrev] at hs
      linear_combination -hs
    · linear_combination hstep i (by omega)
    · simpa only [hθPrev] using hcoordQ (i - 1) (by omega)
    · exact hcoordQ i (by omega)
    · simpa only [C.θ_succ (show i < 12 by omega)] using hcoordQ (i + 1) (by omega)
  let pair (i : ℕ) (hi : 1 ≤ i ∧ i ≤ 8) := Classical.choice (hPair i hi.1 hi.2)
  let r (i : ℕ) := if hi : 1 ≤ i ∧ i ≤ 8 then (pair i hi).r else p 0
  let s (i : ℕ) := if hi : 1 ≤ i ∧ i ≤ 8 then (pair i hi).s else p 0
  let hi (i : ℕ) := if h : 1 ≤ i ∧ i ≤ 8 then (pair i h).hi else 0
  let lo (i : ℕ) := if h : 1 ≤ i ∧ i ≤ 8 then (pair i h).lo else 0
  have rEq (i : ℕ) (h : 1 ≤ i ∧ i ≤ 8) : r i = (pair i h).r := dif_pos h
  have sEq (i : ℕ) (h : 1 ≤ i ∧ i ≤ 8) : s i = (pair i h).s := dif_pos h
  have ht9 : ArcHeading.turnSum C.τ 9 < Real.pi / 3 := by
    have hb := turn_sum_subset C.τ C.turn_nonneg (a := 0) (t := 9) (by decide)
    exact (by simpa only [ArcHeading.turnSum, zero_add] using hb : _ ≤ _).trans_lt C.total_lt
  obtain ⟨a, ha, hm₁, hm₂, hm₃⟩ := exists_matched_triple f p q r s C.θ C.τ hi lo hfsep
    (fun i h => hstep i (by omega)) (fun i h => hcoordQ i (by omega))
    (fun i h => C.θ_succ (by omega)) (fun i h => C.turn_nonneg i (by omega)) ht9
    (fun i il iu => by simpa only [lo, dif_pos (show 1 ≤ i ∧ i ≤ 8 by omega)] using (pair i ⟨by omega, iu⟩).lo_bound)
    (fun i il iu => by simpa only [hi, dif_pos (show 1 ≤ i ∧ i ≤ 8 by omega)] using (pair i ⟨by omega, iu⟩).hi_bound)
    (fun i il iu => by simpa only [hi, lo, dif_pos (show 1 ≤ i ∧ i ≤ 8 by omega)] using (pair i ⟨by omega, iu⟩).gap)
    (fun i il iu => by simpa only [hi, r, dif_pos (show 1 ≤ i ∧ i ≤ 8 by omega)] using (pair i ⟨by omega, iu⟩).r_phase)
    (fun i il iu => by simpa only [lo, s, dif_pos (show 1 ≤ i ∧ i ≤ 8 by omega)] using (pair i ⟨by omega, iu⟩).s_phase)
  have ha₂ : 2 ≤ a := by omega
  have ha₅ : a ≤ 5 := by omega
  have hf₀ : Function.Injective F := by
    intro x y he
    by_contra hn'
    have h := hsep hn'
    rw [he, dist_self] at h
    norm_num at h
  have hm (i : ℕ) (hl : a ≤ i) (hr : i ≤ a + 2) : r (i + 1) = s i := by
    have hd : i = a ∨ i = a + 1 ∨ i = a + 2 := by omega
    rcases hd with rfl | rfl | rfl
    · exact hm₁.symm
    · exact hm₂.symm
    · exact hm₃.symm
  have hw (i : ℕ) (hl : a ≤ i) (hr : i ≤ a + 2) :
      ActualMatchedTips.SeamMatch F p q i (s i) (r (i + 1)) := by
    have hs' : 1 ≤ i ∧ i ≤ 8 := by omega
    have hr' : 1 ≤ i + 1 ∧ i + 1 ≤ 8 := by omega
    have hsm := (pair i hs').s_mem
    have hrm := (pair (i + 1) hr').r_mem
    rw [← sEq i hs'] at hsm
    rw [← rEq (i + 1) hr'] at hrm
    apply ActualMatchedTips.SeamMatch.mk (congrArg F (hm i hl hr).symm)
    · rw [norm_sub_rev, ← dist_eq_norm]
      exact hunit (hn.mp (Finset.mem_sdiff.mp hsm).1)
    · rw [norm_sub_rev, ← dist_eq_norm]
      exact hunit (hn.mp (Finset.mem_sdiff.mp hrm).1)
    · intro he
      have he' := hf₀ he
      exact (Finset.mem_sdiff.mp hsm).2 (by simp [he'])
  have hzF (i : ℕ) (hl : a ≤ i) (hr : i ≤ a + 2) :
      F (s i) = TipCoordinates.z (C.p i) (C.h i) (C.h (i + 1)) :=
    ActualMatchedTips.matched_eq_tip C F (by omega) hp hq (hw i hl hr)
  have hfarQ := ActualMatchedTips.middle_far_outer_q C F (i := a) (by omega) hp hq
    (hw (a + 1) (by omega) (by omega))
    (E := E) (by intro x y h; rw [← dist_eq_norm]; exact hunit h)
  have T := NormalGeometry.layer9TipBounds C F (n := 12) (a := a) (z := s)
    (by omega) (by omega) le_rfl hp hq hφ₃ hφ₁ hφ₂ (hzF (a + 1) (by omega) (by omega))
  have hind := LayerIndependent.lemma9_layer_independent hE hunit B T
    (by omega) (by omega) (fun _ => hfar) hfarQ.1 hfarQ.2
  have hpcov (i : ℕ) (hl : 1 ≤ i) (hr : i ≤ 11) :
      N (p i) ⊆ {p (i - 1), p (i + 1), q (i - 1), q i} := by
    let L := ActualMatchedTips.standardNeighbors p q (i - 1)
    have he₁ : i - 1 + 1 = i := by omega
    have he₂ : i - 1 + 2 = i + 1 := by omega
    have hLd : L.Nodup := ActualMatchedTips.standard_neighbors_nodup C F
      (by omega : i - 1 + 1 ≤ 12) hp hq
    have hLcard : L.toFinset.card = 4 := by
      rw [List.toFinset_card_of_nodup hLd]
      rfl
    have hLsub : L.toFinset ⊆ N (p i) := by
      intro x hx
      rw [List.mem_toFinset] at hx
      simp only [L, ActualMatchedTips.standardNeighbors, List.mem_cons, List.not_mem_nil, or_false,
        he₁, he₂] at hx
      apply hn.mpr
      rcases hx with rfl | rfl | rfl | rfl
      · exact hE (by simpa only [he₁] using hedge (i - 1) (by omega))
      · exact hedge i (by omega)
      · simpa only [he₁] using (htip (i - 1) (by omega)).2
      · exact (htip i (by omega)).1
    have hLall := Finset.eq_of_subset_of_card_le hLsub (by rw [hLcard]; exact (hdeg i hl (by omega)).le)
    rw [← hLall]
    intro x hx
    simpa [L, ActualMatchedTips.standardNeighbors, he₁, he₂] using hx
  refine Layer9Glue.lemma9_of_three_matched_seams Finset.univ E f p q r s s (P a) (U a)
    a ha₂ ha₅ hfsep hu (hcard a (by omega)) (hpcard a (by omega) (by omega))
    (hprefix a) (hpu a (by omega) (by omega)).1 (hpu a (by omega) (by omega)).2
    hind (Finset.subset_univ _) ?_ ?_ hm (fun _ _ _ => rfl) C.θ C.τ
    (fun i _ h => hstep i (by omega)) (fun i _ h => hcoordQ i (by omega)) ?_
    (fun i _ h => C.θ_succ (by omega)) ?_ ?_ he'
  · intro i hi' x _ he
    have hi₀ : 1 ≤ i ∧ i ≤ 8 := by rcases hi' with rfl | rfl <;> omega
    rw [rEq i hi₀, sEq i hi₀]
    exact (pair i hi₀).cover (hN _ _ he)
  · intro i hi' x _ he
    have hi₀ : 1 ≤ i ∧ i ≤ 11 := by rcases hi' with rfl | rfl <;> omega
    exact hpcov i hi₀.1 hi₀.2 (hN _ _ he)
  · intro i hl hr
    exact NormalGeometry.z_eq C F (z := s) (by omega) hp (hzF i hl hr)
  · intro i hl hr
    have h := C.turn_nonneg (i - 1) (by omega)
    simpa only [show i - 1 + 1 = i by omega] using h
  · have hb := (turn_sum_subset C.τ C.turn_nonneg (a := a) (t := 3) (by omega)).trans_lt C.total_lt
    simpa [Finset.sum_range_succ, Nat.add_assoc] using hb

end
end Swanepoel

namespace Erdos1084Harborth

open scoped BigOperators EuclideanGeometry
open Finset

section GraphComb

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma deleteEdges_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) [DecidableRel (G.deleteEdges {e}).Adj] :
    (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
  ext x
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
    Set.mem_singleton_iff, Finset.mem_erase]
  tauto

private lemma deleteEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) [DecidableRel (G.deleteEdges {e}).Adj] :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  rw [deleteEdges_edgeFinset G e]
  exact Finset.card_erase_add_one he

private lemma components_deleteEdges_eq_of_reachable (G : SimpleGraph V) {u v : V}
    (hr : (G.deleteEdges {s(u, v)}).Reachable u v) :
    Nat.card (G.deleteEdges {s(u, v)}).ConnectedComponent = Nat.card G.ConnectedComponent := by
  classical
  let J := G.deleteEdges {s(u, v)}
  have hs {x y : V} (h : G.Adj x y) : J.Reachable x y := by
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hr
      · exact hr.symm
    · exact (show J.Adj x y from SimpleGraph.deleteEdges_adj.mpr ⟨h, by simpa using he⟩).reachable
  have hwalk {x y : V} (p : G.Walk x y) : J.Reachable x y := by
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons x y z hxy p ih => exact (hs hxy).trans ih
  let q : J.ConnectedComponent → G.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))
  refine Nat.card_congr (Equiv.ofBijective q ⟨?_, ?_⟩)
  · intro a b h
    induction a using SimpleGraph.ConnectedComponent.ind with | _ x =>
    induction b using SimpleGraph.ConnectedComponent.ind with | _ y =>
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact h
    apply SimpleGraph.ConnectedComponent.sound
    exact hwalk p
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | _ x =>
    exact ⟨J.connectedComponentMk x, rfl⟩

private lemma card_le_edges_add_components (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ≤ G.edgeFinset.card + Nat.card G.ConnectedComponent := by
  classical
  let emb (c : G.ConnectedComponent) : c ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let edges (c : G.ConnectedComponent) : Finset (Sym2 V) :=
    c.toSimpleGraph.edgeFinset.map (emb c).sym2Map
  have mem_edges (c : G.ConnectedComponent) (u v : V) :
      s(u, v) ∈ edges c ↔ u ∈ c.supp ∧ G.Adj u v := by
    change s(u, v) ∈ c.toSimpleGraph.edgeFinset.map (emb c).sym2Map ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨e, he, huv⟩
      induction e using Sym2.ind with | _ a b =>
      have hab : G.Adj a.val b.val := c.toSimpleGraph.mem_edgeFinset.mp he
      change s(a.val, b.val) = s(u, v) at huv
      rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.property, hab⟩
      · exact ⟨b.property, hab.symm⟩
    · rintro ⟨hu, huv⟩
      have hv := c.mem_supp_of_adj_mem_supp hu huv
      exact ⟨s((⟨u, hu⟩ : c), (⟨v, hv⟩ : c)), c.toSimpleGraph.mem_edgeFinset.mpr huv, rfl⟩
  have hd : (↑(univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint edges := by
    intro c _ d _ hcd
    refine Finset.disjoint_left.mpr fun e hc hd ↦ ?_
    induction e using Sym2.ind with | _ u v =>
    exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex
      ((mem_edges c u v).mp hc).1 ((mem_edges d u v).mp hd).1)
  have he : (∑ c, (edges c).card) ≤ G.edgeFinset.card := by
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro e he
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp he
    induction e using Sym2.ind with | _ u v =>
    exact G.mem_edgeFinset.mpr ((mem_edges c u v).mp hc).2
  have hv (c : G.ConnectedComponent) : Fintype.card c.supp ≤ (edges c).card + 1 := by
    have h := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] at h
    have e : c.supp ≃ c := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
    calc
      Fintype.card c.supp = Fintype.card c := Fintype.card_congr e
      _ ≤ (edges c).card + 1 := by simpa only [edges, Finset.card_map] using h
  calc
    Fintype.card V = ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk).symm
    _ ≤ ∑ c : G.ConnectedComponent, ((edges c).card + 1) :=
      Finset.sum_le_sum fun c _ ↦ hv c
    _ ≤ G.edgeFinset.card + Nat.card G.ConnectedComponent := by
      rw [Finset.sum_add_distrib, Nat.card_eq_fintype_card]
      simpa using Nat.add_le_add_right he (Fintype.card G.ConnectedComponent)

private lemma connected_natCard_components {W : Type*} [Fintype W] {G : SimpleGraph W}
    (hconn : G.Connected) : Nat.card G.ConnectedComponent = 1 := by
  classical
  haveI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  obtain ⟨v₀⟩ := hconn.nonempty
  refine ⟨G.connectedComponentMk v₀, fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with | _ x =>
  exact SimpleGraph.ConnectedComponent.sound (hconn x v₀)

private lemma card_le_edges_add_components_of_cycle_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (he : G.Adj u v) (hr : (G.deleteEdges {s(u, v)}).Reachable u v) :
    Fintype.card V + 1 ≤ G.edgeFinset.card + Nat.card G.ConnectedComponent := by
  classical
  have h1 := card_le_edges_add_components (G.deleteEdges {s(u, v)})
  have h2 := deleteEdges_card G s(u, v) (G.mem_edgeFinset.mpr he)
  have h3 := components_deleteEdges_eq_of_reachable G hr
  omega

private def sameOrbit {α : Type*} (φ : Equiv.Perm α) (x y : α) : Prop :=
  ∃ k : ℕ, (φ ^ k) x = y

private lemma sameOrbit_refl {α : Type*} (φ : Equiv.Perm α) (x : α) : sameOrbit φ x x :=
  ⟨0, rfl⟩

private lemma sameOrbit_trans {α : Type*} (φ : Equiv.Perm α) {x y z : α}
    (h1 : sameOrbit φ x y) (h2 : sameOrbit φ y z) : sameOrbit φ x z := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := h2
  exact ⟨m + k, by rw [pow_add, Equiv.Perm.mul_apply]⟩

private lemma sameOrbit_symm {α : Type*} [Fintype α] (φ : Equiv.Perm α) {x y : α}
    (h : sameOrbit φ x y) : sameOrbit φ y x := by
  classical
  obtain ⟨k, rfl⟩ := h
  have hord : 0 < orderOf φ := orderOf_pos φ
  let m := orderOf φ - (k % orderOf φ)
  refine ⟨m, ?_⟩
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  have hdvd : orderOf φ ∣ m + k := by
    have h1 : k = orderOf φ * (k / orderOf φ) + k % orderOf φ := (Nat.div_add_mod k (orderOf φ)).symm
    have h2 : k % orderOf φ < orderOf φ := Nat.mod_lt k hord
    refine ⟨k / orderOf φ + 1, ?_⟩
    dsimp [m]
    rw [mul_add, mul_one]
    omega
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, pow_mul, pow_orderOf_eq_one, one_pow]
  rfl

private def orbitSetoid {α : Type*} [Fintype α] (φ : Equiv.Perm α) : Setoid α where
  r := sameOrbit φ
  iseqv := ⟨sameOrbit_refl φ, fun h => sameOrbit_symm φ h, fun h1 h2 => sameOrbit_trans φ h1 h2⟩

private noncomputable def numOrbits {α : Type*} [Fintype α] (φ : Equiv.Perm α) : ℕ :=
  Nat.card (Quotient (orbitSetoid φ))

private lemma sameOrbit_step {α : Type*} (φ : Equiv.Perm α) (x : α) :
    sameOrbit φ x (φ x) := ⟨1, by simp⟩

private abbrev DartOf {W : Type*} (H : SimpleGraph W) := {d : W × W // H.Adj d.1 d.2}

private def dartPerm {W : Type*} (H : SimpleGraph W)
    (σ : ∀ v : W, Equiv.Perm {u : W // H.Adj v u}) : Equiv.Perm (DartOf H) where
  toFun d := ⟨(d.1.2, (σ d.1.2 ⟨d.1.1, d.2.symm⟩).1), (σ d.1.2 ⟨d.1.1, d.2.symm⟩).2⟩
  invFun d := ⟨(((σ d.1.1).symm ⟨d.1.2, d.2⟩).1, d.1.1), (((σ d.1.1).symm ⟨d.1.2, d.2⟩).2).symm⟩
  left_inv d := by
    rcases d with ⟨⟨u, v⟩, huv⟩
    simp
  right_inv d := by
    rcases d with ⟨⟨u, v⟩, huv⟩
    simp

private def IsCyclicPerm {A : Type*} [Fintype A] (σ : Equiv.Perm A) : Prop :=
  ∀ x y : A, sameOrbit σ x y

private abbrev OrbitAway {D : Type*} [Fintype D] (p : Equiv.Perm D) (a b : D) :=
  {C : Quotient (orbitSetoid p) //
    ¬ (C = Quotient.mk (orbitSetoid p) a ∨ C = Quotient.mk (orbitSetoid p) b)}

private lemma orbitAway_transfer {D : Type*} [Fintype D]
    (p q : Equiv.Perm D) {a b x : D}
    (hstep : ∀ z, z ≠ a → z ≠ b → q z = p z)
    (hx : ¬ sameOrbit p x a) (hy : ¬ sameOrbit p x b) :
    ∀ y, sameOrbit p x y ↔ sameOrbit q x y := by
  have hpow (n : ℕ) : (q ^ n) x = (p ^ n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ' q n, pow_succ' p n, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      exact hstep _ (fun h => hx ⟨n, h⟩) (fun h => hy ⟨n, h⟩)
  intro y
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (hpow n).trans hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (hpow n).symm.trans hn⟩

private noncomputable def orbitAway_map {D : Type*} [Fintype D]
    (p q : Equiv.Perm D) (a b : D)
    (hstep : ∀ z, z ≠ a → z ≠ b → q z = p z) : OrbitAway p a b → OrbitAway q a b :=
  fun C => by
    let x := C.val.out
    have hx : Quotient.mk (orbitSetoid p) x = C.val := Quotient.out_eq' _
    have h := orbitAway_transfer p q hstep (x := x)
      (fun ha => C.prop (Or.inl (hx.symm.trans (Quotient.sound ha))))
      (fun hb => C.prop (Or.inr (hx.symm.trans (Quotient.sound hb))))
    refine ⟨Quotient.mk (orbitSetoid q) x, ?_⟩
    rintro (ha | hb)
    · exact C.prop (Or.inl (hx.symm.trans (Quotient.sound ((h a).mpr (Quotient.exact ha)))))
    · exact C.prop (Or.inr (hx.symm.trans (Quotient.sound ((h b).mpr (Quotient.exact hb)))))

private lemma orbitAway_map_rep {D : Type*} [Fintype D]
    (p q : Equiv.Perm D) {a b : D}
    (hstep : ∀ z, z ≠ a → z ≠ b → q z = p z) (C : OrbitAway p a b)
    {x : D} (hx : Quotient.mk (orbitSetoid p) x = C.val) :
    (orbitAway_map p q a b hstep C).val = Quotient.mk (orbitSetoid q) x := by
  let y := C.val.out
  have hy : Quotient.mk (orbitSetoid p) y = C.val := Quotient.out_eq' _
  apply Quotient.sound
  exact (orbitAway_transfer p q hstep (x := y)
    (fun ha => C.prop (Or.inl (hy.symm.trans (Quotient.sound ha))))
    (fun hb => C.prop (Or.inr (hy.symm.trans (Quotient.sound hb)))) x).mp
    (Quotient.exact (hy.trans hx.symm))

private noncomputable def orbitAway_equiv {D : Type*} [Fintype D]
    (p q : Equiv.Perm D) (a b : D)
    (hstep : ∀ z, z ≠ a → z ≠ b → q z = p z) : OrbitAway p a b ≃ OrbitAway q a b where
  toFun := orbitAway_map p q a b hstep
  invFun := orbitAway_map q p a b (fun z ha hb => (hstep z ha hb).symm)
  left_inv C := by
    apply Subtype.ext
    have hC : Quotient.mk (orbitSetoid p) C.val.out = C.val := Quotient.out_eq' _
    exact (orbitAway_map_rep q p (fun z ha hb => (hstep z ha hb).symm) _
      (orbitAway_map_rep p q hstep C hC).symm).trans hC
  right_inv C := by
    apply Subtype.ext
    have hC : Quotient.mk (orbitSetoid q) C.val.out = C.val := Quotient.out_eq' _
    exact (orbitAway_map_rep p q hstep _
      (orbitAway_map_rep q p (fun z ha hb => (hstep z ha hb).symm) C hC).symm).trans hC

private lemma numOrbits_eq_away_add {D : Type*} [Fintype D]
    (p : Equiv.Perm D) (a b : D) [Decidable (sameOrbit p a b)] :
    numOrbits p = Nat.card (OrbitAway p a b) + (if sameOrbit p a b then 1 else 2) := by
  classical
  let Q := Quotient (orbitSetoid p)
  let A : Q := Quotient.mk (orbitSetoid p) a
  let B : Q := Quotient.mk (orbitSetoid p) b
  letI : Fintype Q := Fintype.ofFinite Q
  let P := fun C : Q => C = A ∨ C = B
  have hsum := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum] at hsum
  change Nat.card Q = Nat.card {C : Q // ¬ P C} + _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← hsum]
  by_cases h : sameOrbit p a b
  · have hab : A = B := Quotient.sound h
    have hcard : Fintype.card {C : Q // P C} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨A, Or.inl rfl⟩, ?_⟩
      intro C
      apply Subtype.ext
      exact C.prop.elim (fun hC => hC) (fun hC => hC.trans hab.symm)
    rw [hcard, if_pos h, Nat.add_comm]
  · have hab : A ≠ B := fun heq => h (Quotient.exact heq)
    have hcard : Fintype.card {C : Q // P C} = 2 :=
      Fintype.card_subtype_eq_or_eq_of_ne hab
    rw [hcard, if_neg h, Nat.add_comm]

private lemma orbitAway_card_mul_swap {D : Type*} [Fintype D] [DecidableEq D]
    (p : Equiv.Perm D) (a b : D) :
    Nat.card (OrbitAway p a b) = Nat.card (OrbitAway (p * Equiv.swap a b) a b) :=
  Nat.card_congr (orbitAway_equiv p (p * Equiv.swap a b) a b (by
    intro z ha hb
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ha hb]))

private lemma numOrbits_mul_swap_le {D : Type*} [Fintype D] [DecidableEq D]
    (p : Equiv.Perm D) {a b : D} (_hne : a ≠ b) :
    numOrbits (p * Equiv.swap a b) ≤ numOrbits p + 1 := by
  classical
  rw [numOrbits_eq_away_add (p * Equiv.swap a b) a b, numOrbits_eq_away_add p a b,
    ← orbitAway_card_mul_swap p a b]
  split <;> split <;> omega

private lemma sameOrbit_mul_swap_of_not_sameOrbit {D : Type*} [Fintype D] [DecidableEq D]
    (p : Equiv.Perm D) {a b : D} (h : ¬ sameOrbit p a b) :
    sameOrbit (p * Equiv.swap a b) a b := by
  classical
  let q := p * Equiv.swap a b
  have hex : ∃ n : ℕ, (p ^ (n + 1)) a = a := by
    refine ⟨orderOf p - 1, ?_⟩
    have hp : 0 < orderOf p := orderOf_pos p
    rw [show orderOf p - 1 + 1 = orderOf p by omega, pow_orderOf_eq_one]
    rfl
  let k := Nat.find hex
  have hk : (p ^ (k + 1)) a = a := Nat.find_spec hex
  have hpow (n : ℕ) (hn : n ≤ k) : (q ^ (n + 1)) b = (p ^ (n + 1)) a := by
    induction n with
    | zero => simp only [q, Nat.zero_add, pow_one, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    | succ n ih =>
      have ha : (p ^ (n + 1)) a ≠ a := Nat.find_min hex (show n < k by omega)
      have hb : (p ^ (n + 1)) a ≠ b := fun heq => h ⟨n + 1, heq⟩
      rw [pow_succ' q (n + 1), pow_succ' p (n + 1), Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, ih (by omega)]
      change p (Equiv.swap a b ((p ^ (n + 1)) a)) = p ((p ^ (n + 1)) a)
      rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  exact sameOrbit_symm q ⟨k + 1, (hpow k le_rfl).trans hk⟩

private lemma numOrbits_mul_swap_lt {D : Type*} [Fintype D] [DecidableEq D]
    (p : Equiv.Perm D) {a b : D} (h : ¬ sameOrbit p a b) :
    numOrbits (p * Equiv.swap a b) < numOrbits p := by
  classical
  rw [numOrbits_eq_away_add (p * Equiv.swap a b) a b, numOrbits_eq_away_add p a b,
    ← orbitAway_card_mul_swap p a b,
    if_pos (sameOrbit_mul_swap_of_not_sameOrbit p h), if_neg h]
  omega

private def eulerRotation (J : SimpleGraph V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) : Equiv.Perm (DartOf J) where
  toFun d := ⟨(d.1.1, (σ d.1.1 ⟨d.1.2, d.2⟩).1), (σ d.1.1 ⟨d.1.2, d.2⟩).2⟩
  invFun d := ⟨(d.1.1, ((σ d.1.1).symm ⟨d.1.2, d.2⟩).1),
    ((σ d.1.1).symm ⟨d.1.2, d.2⟩).2⟩
  left_inv d := by rcases d with ⟨⟨u, v⟩, huv⟩; simp
  right_inv d := by rcases d with ⟨⟨u, v⟩, huv⟩; simp

private def eulerReverse {J : SimpleGraph V} (d : DartOf J) : DartOf J :=
  ⟨(d.1.2, d.1.1), d.2.symm⟩

private def eulerEdge {J : SimpleGraph V} (d : DartOf J) : Sym2 V := s(d.1.1, d.1.2)

private lemma eulerReverse_reverse {J : SimpleGraph V} (d : DartOf J) :
    eulerReverse (eulerReverse d) = d := by
  rcases d with ⟨⟨u, v⟩, huv⟩
  rfl

private lemma eulerReverse_edge {J : SimpleGraph V} (d : DartOf J) :
    eulerEdge (eulerReverse d) = eulerEdge d := Sym2.eq_swap

private lemma eulerReverse_ne {J : SimpleGraph V} (d : DartOf J) : d ≠ eulerReverse d :=
  fun h => d.2.ne (congrArg (fun x : DartOf J => x.1.1) h)

private def eulerPartialReverse (J : SimpleGraph V) (F : Finset (Sym2 V)) :
    Equiv.Perm (DartOf J) :=
  let f := fun d : DartOf J => if eulerEdge d ∈ F then eulerReverse d else d
  have hf : Function.Involutive f := by
    intro d
    by_cases hd : eulerEdge d ∈ F <;>
      simp [f, hd, eulerReverse_edge, eulerReverse_reverse]
  ⟨f, f, hf, hf⟩

private def eulerPartial (J : SimpleGraph V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) (F : Finset (Sym2 V)) :
    Equiv.Perm (DartOf J) := eulerRotation J σ * eulerPartialReverse J F

private lemma eulerPartial_empty (J : SimpleGraph V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) :
    eulerPartial J σ ∅ = eulerRotation J σ := by
  apply Equiv.ext
  intro d
  simp [eulerPartial, Equiv.Perm.mul_apply, eulerPartialReverse]

private lemma eulerPartial_full (J : SimpleGraph V) [DecidableRel J.Adj]
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) :
    eulerPartial J σ J.edgeFinset = dartPerm J σ := by
  apply Equiv.ext
  intro d
  have hd : eulerEdge d ∈ J.edgeFinset := SimpleGraph.mem_edgeFinset.mpr d.2
  simp only [eulerPartial, Equiv.Perm.mul_apply]
  change eulerRotation J σ (if eulerEdge d ∈ J.edgeFinset then eulerReverse d else d) = _
  rw [if_pos hd]
  rfl

private lemma eulerPartial_insert (J : SimpleGraph V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) (F : Finset (Sym2 V))
    (d : DartOf J) (hd : eulerEdge d ∉ F) :
    eulerPartial J σ (insert (eulerEdge d) F) =
      eulerPartial J σ F * Equiv.swap d (eulerReverse d) := by
  classical
  apply Equiv.ext
  intro x
  simp only [eulerPartial, Equiv.Perm.mul_apply]
  apply congrArg (eulerRotation J σ)
  change (if eulerEdge x ∈ insert (eulerEdge d) F then eulerReverse x else x) =
    (if eulerEdge (Equiv.swap d (eulerReverse d) x) ∈ F then
      eulerReverse (Equiv.swap d (eulerReverse d) x) else Equiv.swap d (eulerReverse d) x)
  by_cases hxd : x = d
  · subst x
    simp [eulerReverse_edge, hd]
  by_cases hxr : x = eulerReverse d
  · rw [hxr]
    simp [eulerReverse_reverse, eulerReverse_edge, hd]
  rw [Equiv.swap_apply_of_ne_of_ne hxd hxr]
  have hxe : eulerEdge x ≠ eulerEdge d := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hxd (Subtype.ext (Prod.ext h₁ h₂))
    · exact hxr (Subtype.ext (Prod.ext h₁ h₂))
  simp [Finset.mem_insert, hxe]

private lemma eulerRotation_pow (J : SimpleGraph V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u})
    (v : V) (a : {u : V // J.Adj v u}) (n : ℕ) :
    (eulerRotation J σ ^ n) ⟨(v, a.1), a.2⟩ =
      ⟨(v, ((σ v ^ n) a).1), ((σ v ^ n) a).2⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    rfl

private lemma eulerRotation_orbits (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (hn : 2 ≤ Fintype.card V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) (hσ : ∀ v, IsCyclicPerm (σ v)) :
    numOrbits (eulerRotation J σ) = Fintype.card V := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let R := orbitSetoid (eulerRotation J σ)
  let source : Quotient R → V := Quotient.lift (fun d : DartOf J => d.1.1) (by
    intro x y h
    change sameOrbit (eulerRotation J σ) x y at h
    obtain ⟨k, rfl⟩ := h
    rcases x with ⟨⟨u, v⟩, huv⟩
    rw [eulerRotation_pow J σ u ⟨v, huv⟩ k])
  have hinj : Function.Injective source := by
    intro x y
    induction x using Quotient.ind with | _ x =>
      induction y using Quotient.ind with | _ y =>
        rcases x with ⟨⟨u, v⟩, huv⟩
        rcases y with ⟨⟨w, z⟩, hwz⟩
        intro h
        change u = w at h
        subst w
        apply Quotient.sound
        change sameOrbit (eulerRotation J σ) ⟨(u, v), huv⟩ ⟨(u, z), hwz⟩
        obtain ⟨k, hk⟩ := hσ u ⟨v, huv⟩ ⟨z, hwz⟩
        exact ⟨k, by rw [eulerRotation_pow J σ u ⟨v, huv⟩ k, hk]⟩
  have hsurj : Function.Surjective source := by
    intro v
    obtain ⟨u, huv⟩ := hconn.preconnected.exists_adj_of_nontrivial v
    exact ⟨Quotient.mk R ⟨(v, u), huv⟩, rfl⟩
  unfold numOrbits
  exact (Nat.card_congr (Equiv.ofBijective source ⟨hinj, hsurj⟩)).trans Nat.card_eq_fintype_card

private lemma eulerPartial_reachable (J : SimpleGraph V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) (F : Finset (Sym2 V))
    {x y : DartOf J} (h : sameOrbit (eulerPartial J σ F) x y) :
    (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable x.1.1 y.1.1 := by
  have step (d : DartOf J) : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable
      d.1.1 ((eulerPartial J σ F) d).1.1 := by
    change (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable d.1.1
      (if eulerEdge d ∈ F then eulerReverse d else d).1.1
    split_ifs with hd
    · have hadj : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Adj
          d.1.1 (eulerReverse d).1.1 := by
        change eulerEdge d ∈ F ∧ d.1.1 ≠ d.1.2
        exact ⟨hd, d.2.ne⟩
      exact hadj.reachable
    · exact SimpleGraph.Reachable.refl _
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (step _)

private lemma eulerPartial_tree_orbits (J : SimpleGraph V) [DecidableRel J.Adj]
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u})
    (T : SimpleGraph V) [DecidableRel T.Adj] (hTJ : T ≤ J) (hT : T.IsAcyclic)
    (F : Finset (Sym2 V)) (hF : F ⊆ T.edgeFinset) (d : DartOf J)
    (hdT : eulerEdge d ∈ T.edgeFinset) (hdF : eulerEdge d ∉ F) :
    ¬ sameOrbit (eulerPartial J σ F) d (eulerReverse d) := by
  intro h
  have hle : SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)) ≤ T.deleteEdges {eulerEdge d} := by
    intro u v huv
    change s(u, v) ∈ (↑F : Set (Sym2 V)) ∧ u ≠ v at huv
    obtain ⟨he, _⟩ := huv
    have heF : s(u, v) ∈ F := he
    exact SimpleGraph.deleteEdges_adj.mpr
      ⟨SimpleGraph.mem_edgeFinset.mp (hF heF), fun heq => hdF ((Set.mem_singleton_iff.mp heq) ▸ heF)⟩
  have hb : T.IsBridge (eulerEdge d) :=
    (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hT) (SimpleGraph.mem_edgeFinset.mp hdT)
  exact (SimpleGraph.isBridge_iff.mp hb)
    (SimpleGraph.Reachable.mono hle (eulerPartial_reachable J σ F h))

private lemma rotation_euler_upper (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (hn : 2 ≤ Fintype.card V)
    (σ : ∀ v, Equiv.Perm {u : V // J.Adj v u}) (hσ : ∀ v, IsCyclicPerm (σ v)) :
    numOrbits (dartPerm J σ) + Fintype.card V ≤ J.edgeFinset.card + 2 := by
  classical
  obtain ⟨T, hTJ, hT⟩ := hconn.exists_isTree_le
  let E := J.edgeFinset
  let S := T.edgeFinset
  let N := fun F : Finset (Sym2 V) => numOrbits (eulerPartial J σ F)
  have hSE : S ⊆ E := fun _ he =>
    SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hTJ (SimpleGraph.mem_edgeFinset.mp he))
  have hScard : S.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hzero : N ∅ = Fintype.card V := by
    dsimp [N]
    rw [eulerPartial_empty, eulerRotation_orbits J hconn hn σ hσ]
  have dartOfEdge (e : Sym2 V) (he : e ∈ E) : ∃ d : DartOf J, eulerEdge d = e := by
    induction e using Sym2.ind with
    | h u v => exact ⟨⟨(u, v), SimpleGraph.mem_edgeFinset.mp he⟩, rfl⟩
  have htree (F : Finset (Sym2 V)) : F ⊆ S → N F + F.card ≤ Fintype.card V := by
    induction F using Finset.induction_on with
    | empty => simp [hzero]
    | @insert e F he ih =>
      intro hF
      have heS := hF (Finset.mem_insert_self e F)
      have hFS := (Finset.subset_insert e F).trans hF
      obtain ⟨d, rfl⟩ := dartOfEdge e (hSE heS)
      have hs := numOrbits_mul_swap_lt (eulerPartial J σ F)
        (eulerPartial_tree_orbits J σ T hTJ hT.isAcyclic F hFS d heS he)
      have hlt : N (insert (eulerEdge d) F) < N F := by
        dsimp [N]
        rw [eulerPartial_insert J σ F d he]
        exact hs
      rw [Finset.card_insert_of_notMem he]
      have := ih hFS
      omega
  have hrest (F : Finset (Sym2 V)) : F ⊆ E \ S → N (F ∪ S) ≤ N S + F.card := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert e F he ih =>
      intro hF
      have heES := Finset.mem_sdiff.mp (hF (Finset.mem_insert_self e F))
      have he' : e ∉ F ∪ S := fun h => (Finset.mem_union.mp h).elim he heES.2
      have hprev := ih ((Finset.subset_insert e F).trans hF)
      obtain ⟨d, rfl⟩ := dartOfEdge e heES.1
      have hle : N (insert (eulerEdge d) (F ∪ S)) ≤ N (F ∪ S) + 1 := by
        dsimp [N]
        rw [eulerPartial_insert J σ (F ∪ S) d he']
        exact numOrbits_mul_swap_le (eulerPartial J σ (F ∪ S)) (eulerReverse_ne d)
      rw [Finset.insert_union, Finset.card_insert_of_notMem he]
      omega
  have htree' := htree S (fun _ h => h)
  have hrest' := hrest (E \ S) (fun _ h => h)
  rw [Finset.sdiff_union_of_subset hSE, Finset.card_sdiff_of_subset hSE] at hrest'
  have hcards := Finset.card_le_card hSE
  have hfull : N E = numOrbits (dartPerm J σ) := by
    dsimp [N, E]
    rw [eulerPartial_full]
  rw [hfull] at hrest'
  change numOrbits (dartPerm J σ) + Fintype.card V ≤ E.card + 2
  omega

end GraphComb

section Geom2D

private lemma exists_generic_unit_rot (S : Finset ℂ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (ω * x).re ≠ (ω * y).re := by
  classical
  let u (t : ℝ) : ℂ := ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩
  have hu_norm (t : ℝ) : ‖u t‖ = 1 := by
    have hpos : 0 < 1 + t ^ 2 := by positivity
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    have h1 : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
      field_simp; ring
    simp only [u, h1, Real.sqrt_one]
  let poly (z : ℂ) : Polynomial ℝ :=
    Polynomial.C (-z.re) * Polynomial.X ^ 2 + Polynomial.C (-2 * z.im) * Polynomial.X +
      Polynomial.C z.re
  have hpoly_ne (z : ℂ) (hz : z ≠ 0) : poly z ≠ 0 := by
    intro h0
    have hc0 : (poly z).coeff 0 = 0 := by rw [h0]; simp
    have hc1 : (poly z).coeff 1 = 0 := by rw [h0]; simp
    simp only [poly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at hc0 hc1
    norm_num at hc0 hc1
    exact hz (Complex.ext hc0 hc1)
  let bad : Finset ℝ := S.offDiag.biUnion (fun p => (poly (p.1 - p.2)).roots.toFinset)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨u t, hu_norm t, fun x hx y hy hxy hre => ?_⟩
  have hmem : (x, y) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hre' : (u t * (x - y)).re = 0 := by
    rw [mul_sub, Complex.sub_re]; linarith
  have heval : (poly (x - y)).eval t = 0 := by
    simp only [poly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    simp only [Complex.mul_re, u] at hre'
    have hmul : (1 + t ^ 2) * ((1 - t ^ 2) / (1 + t ^ 2) * (x - y).re -
        2 * t / (1 + t ^ 2) * (x - y).im) = 0 := by rw [hre', mul_zero]
    have hden : (1 + t ^ 2) ≠ 0 := ne_of_gt hpos
    have hsim : (1 - t ^ 2) * (x - y).re - 2 * t * (x - y).im = 0 := by
      field_simp [hden] at hmul; linarith
    linarith
  have hroot : t ∈ (poly (x - y)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hpoly_ne _ (sub_ne_zero.mpr hxy))]
    exact heval
  exact ht (Finset.mem_biUnion.mpr ⟨(x, y), hmem, hroot⟩)

private lemma not_on_closed_unit_seg {a b c : ℂ}
    (hab : ‖a - b‖ = 1) (hac : 1 ≤ ‖a - c‖) (hbc : 1 ≤ ‖b - c‖)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : c = (1 - t) • a + t • b) : False := by
  have h1 : c - a = t • (b - a) := by
    rw [heq, Complex.real_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
  have h2 : b - c = (1 - t) • (b - a) := by
    rw [heq, Complex.real_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
  have hn1 : ‖a - c‖ = t := by
    rw [norm_sub_rev, h1, norm_smul, Real.norm_of_nonneg ht0, norm_sub_rev, hab, mul_one]
  have hn2 : ‖b - c‖ = 1 - t := by
    rw [h2, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev, hab, mul_one]
  linarith

private lemma no_unit_seg_crossing {a b c d : ℂ}
    (hab : ‖a - b‖ = 1) (hcd : ‖c - d‖ = 1)
    (hac : 1 ≤ ‖a - c‖) (hcb : 1 ≤ ‖c - b‖) (hbd : 1 ≤ ‖b - d‖) (hda : 1 ≤ ‖d - a‖)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : (1 - s) • a + s • b = (1 - t) • c + t • d) : False := by
  set q : ℂ := (1 - s) • a + s • b
  have haq : ‖a - q‖ = s := by
    have : a - q = s • (a - b) := by
      simp only [q, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg hs0, hab, mul_one]
  have hbq : ‖b - q‖ = 1 - s := by
    have : b - q = (1 - s) • (b - a) := by
      simp only [q, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev, hab, mul_one]
  have hcq : ‖c - q‖ = t := by
    have : c - q = t • (c - d) := by
      simp only [q, heq, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg ht0, hcd, mul_one]
  have hdq : ‖d - q‖ = 1 - t := by
    have : d - q = (1 - t) • (d - c) := by
      simp only [q, heq, Complex.real_smul]; push_cast; ring
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev, hcd, mul_one]
  have t1 : 1 ≤ s + t := by
    calc (1 : ℝ) ≤ ‖a - c‖ := hac
      _ = ‖(a - q) + (q - c)‖ := by ring_nf
      _ ≤ ‖a - q‖ + ‖q - c‖ := norm_add_le _ _
      _ = s + t := by rw [haq, norm_sub_rev, hcq]
  have t2 : 1 ≤ t + (1 - s) := by
    calc (1 : ℝ) ≤ ‖c - b‖ := hcb
      _ = ‖(c - q) + (q - b)‖ := by ring_nf
      _ ≤ ‖c - q‖ + ‖q - b‖ := norm_add_le _ _
      _ = t + (1 - s) := by rw [hcq, norm_sub_rev, hbq]
  have t3 : 1 ≤ (1 - s) + (1 - t) := by
    calc (1 : ℝ) ≤ ‖b - d‖ := hbd
      _ = ‖(b - q) + (q - d)‖ := by ring_nf
      _ ≤ ‖b - q‖ + ‖q - d‖ := norm_add_le _ _
      _ = (1 - s) + (1 - t) := by rw [hbq, norm_sub_rev, hdq]
  have t4 : 1 ≤ (1 - t) + s := by
    calc (1 : ℝ) ≤ ‖d - a‖ := hda
      _ = ‖(d - q) + (q - a)‖ := by ring_nf
      _ ≤ ‖d - q‖ + ‖q - a‖ := norm_add_le _ _
      _ = (1 - t) + s := by rw [hdq, norm_sub_rev, haq]
  have hs_half : s = 1 / 2 := by linarith
  have ht_half : t = 1 / 2 := by linarith

  let u := a - q
  let v := c - q
  have hu : ‖u‖ = 1 / 2 := by rw [haq, hs_half]
  have hv : ‖v‖ = 1 / 2 := by rw [hcq, ht_half]
  have huv_sub : 1 ≤ ‖u - v‖ := by
    have : u - v = a - c := by simp only [u, v]; ring
    rw [this]; exact hac
  have huv_add : 1 ≤ ‖u + v‖ := by
    have hd_eq : d - q = -v := by
      have : (d - q) + (c - q) = 0 := by
        simp only [q, heq, ht_half, Complex.real_smul]; push_cast; ring
      exact eq_neg_of_add_eq_zero_left this
    have : u + v = a - d := by
      calc u + v = (a - q) - (d - q) := by rw [hd_eq]; ring
        _ = a - d := by ring
    rw [this, norm_sub_rev]; exact hda
  have hpara : ‖u - v‖ ^ 2 + ‖u + v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im]
    ring
  have hsub2 : 1 ≤ ‖u - v‖ ^ 2 := by nlinarith
  have hadd2 : 1 ≤ ‖u + v‖ ^ 2 := by nlinarith
  rw [hu, hv] at hpara
  linarith

private noncomputable def edgeY {V : Type*} (p : V → ℂ) (a b : V) (x : ℝ) : ℝ :=
  (p a).im + ((p b).im - (p a).im) * ((x - (p a).re) / ((p b).re - (p a).re))

private lemma edgeY_point_eq {V : Type*} (p : V → ℂ) {a b : V} (hab : (p a).re < (p b).re) (x : ℝ) :
    let t := (x - (p a).re) / ((p b).re - (p a).re)
    (⟨x, edgeY p a b x⟩ : ℂ) = (1 - t) • p a + t • p b := by
  intro t
  have hne : (p b).re - (p a).re ≠ 0 := ne_of_gt (by linarith)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, t]
    field_simp [hne]; ring
  · simp only [edgeY, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, t]
    ring

private lemma edgeY_at_left {V : Type*} (p : V → ℂ) (a b : V) :
    edgeY p a b (p a).re = (p a).im := by
  simp [edgeY]

private lemma edgeY_at_right {V : Type*} (p : V → ℂ) {a b : V} (hab : (p a).re < (p b).re) :
    edgeY p a b (p b).re = (p b).im := by
  unfold edgeY
  have hne : (p b).re - (p a).re ≠ 0 := ne_of_gt (by linarith)
  rw [div_self hne, mul_one]; ring

private noncomputable def edgeSlope {V : Type*} (p : V → ℂ) (a b : V) : ℝ :=
  ((p b).im - (p a).im) / ((p b).re - (p a).re)

private lemma edgeY_eq_left_add_slope {V : Type*} (p : V → ℂ) (a b : V) (x : ℝ) :
    edgeY p a b x = (p a).im + edgeSlope p a b * (x - (p a).re) := by
  unfold edgeY edgeSlope; ring

private lemma edgeY_eq_right_sub_slope {V : Type*} (p : V → ℂ) {a b : V}
    (hab : (p a).re < (p b).re) (x : ℝ) :
    edgeY p a b x = (p b).im - edgeSlope p a b * ((p b).re - x) := by
  unfold edgeY edgeSlope
  have hne : (p b).re - (p a).re ≠ 0 := ne_of_gt (by linarith)
  field_simp [hne]; ring

end Geom2D

section HeadingAndRot

private noncomputable def heading (z : ℂ) : ℝ :=
  if 0 < z.re then z.arg
  else if 0 ≤ z.arg then z.arg else z.arg + 2 * Real.pi

private lemma cos_heading {z : ℂ} (hz : z ≠ 0) : Real.cos (heading z) = z.re / ‖z‖ := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.cos z.arg = z.re / ‖z‖ := by
    rw [eq_div_iff (ne_of_gt hpos), mul_comm, Complex.norm_mul_cos_arg]
  unfold heading
  split_ifs
  · exact h1
  · exact h1
  · rw [Real.cos_add_two_pi]; exact h1

private lemma sin_heading {z : ℂ} (hz : z ≠ 0) : Real.sin (heading z) = z.im / ‖z‖ := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.sin z.arg = z.im / ‖z‖ := by
    rw [eq_div_iff (ne_of_gt hpos), mul_comm, Complex.norm_mul_sin_arg]
  unfold heading
  split_ifs
  · exact h1
  · exact h1
  · rw [Real.sin_add_two_pi]; exact h1

private lemma heading_bounds_pos {z : ℂ} (hz : 0 < z.re) :
    -(Real.pi / 2) < heading z ∧ heading z < Real.pi / 2 := by
  unfold heading
  rw [if_pos hz]
  have hcos : 0 < Real.cos z.arg := by
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => by simp [h] at hz)
    have : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
    nlinarith
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  constructor
  · by_contra! hle
    have : Real.cos z.arg ≤ 0 := by
      have : -z.arg ∈ Set.Icc (Real.pi / 2) Real.pi := ⟨by linarith, by linarith⟩
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le this.1 (by linarith)
    linarith
  · by_contra! hle
    have : Real.cos z.arg ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith)
    linarith

private lemma heading_bounds_neg {z : ℂ} (hz : z.re < 0) :
    Real.pi / 2 < heading z ∧ heading z < 3 * Real.pi / 2 := by
  have hne : z ≠ 0 := fun h => by simp [h] at hz
  have hcos : Real.cos z.arg < 0 := by
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hne
    have : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
    nlinarith
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  unfold heading
  rw [if_neg (not_lt.mpr hz.le)]
  split_ifs with h0
  · constructor
    · by_contra! hle
      have : 0 ≤ Real.cos z.arg := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩
      linarith
    · linarith [Real.pi_pos]
  · push_neg at h0
    constructor
    · linarith [Real.pi_pos]
    · by_contra! hge
      have : 0 ≤ Real.cos z.arg := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      linarith

private lemma heading_neg_of_pos {z : ℂ} (hz : 0 < z.re) :
    heading (-z) = heading z + Real.pi := by
  have hnz : (-z).re < 0 := by simp [hz]
  have h1 := heading_bounds_pos hz
  have h2 := heading_bounds_neg hnz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hcos : Real.cos (heading (-z)) = Real.cos (heading z + Real.pi) := by
    rw [Real.cos_add_pi, cos_heading (neg_ne_zero.mpr hz0), cos_heading hz0,
      Complex.neg_re, norm_neg, neg_div]
  have hsin : Real.sin (heading (-z)) = Real.sin (heading z + Real.pi) := by
    rw [Real.sin_add_pi, sin_heading (neg_ne_zero.mpr hz0), sin_heading hz0,
      Complex.neg_im, norm_neg, neg_div]

  have hlt1 : heading (-z) - Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hlt2 : heading z ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hsin' : Real.sin (heading (-z) - Real.pi) = Real.sin (heading z) := by
    rw [Real.sin_sub_pi, hsin, Real.sin_add_pi, neg_neg]
  have heq := Real.strictMonoOn_sin.injOn hlt1 hlt2 hsin'
  linarith

private lemma heading_neg_of_neg {z : ℂ} (hz : z.re < 0) :
    heading (-z) = heading z - Real.pi := by
  have hp : 0 < (-z).re := by simp [hz]
  have h := heading_neg_of_pos hp
  rw [neg_neg] at h
  linarith

private lemma heading_lt_iff_slope_pos {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) :
    heading z₁ < heading z₂ ↔ z₁.im / z₁.re < z₂.im / z₂.re := by
  have hb1 := heading_bounds_pos h1
  have hb2 := heading_bounds_pos h2
  have hz1 : z₁ ≠ 0 := fun h => by simp [h] at h1
  have hz2 : z₂ ≠ 0 := fun h => by simp [h] at h2
  have htan (z : ℂ) (hz : 0 < z.re) : Real.tan (heading z) = z.im / z.re := by
    have hne : z ≠ 0 := fun h => by simp [h] at hz
    rw [Real.tan_eq_sin_div_cos, sin_heading hne, cos_heading hne,
      div_div_div_cancel_right₀ (ne_of_gt (norm_pos_iff.mpr hne))]
  rw [← htan z₁ h1, ← htan z₂ h2]
  exact ⟨fun h => Real.strictMonoOn_tan hb1 hb2 h, fun h => by
    by_contra! hle
    rcases eq_or_lt_of_le hle with heq | hgt
    · rw [heq] at h; exact lt_irrefl _ h
    · exact not_lt.mpr (Real.strictMonoOn_tan hb2 hb1 hgt).le h⟩

private lemma heading_lt_iff_slope_neg {z₁ z₂ : ℂ} (h1 : z₁.re < 0) (h2 : z₂.re < 0) :
    heading z₁ < heading z₂ ↔ z₁.im / z₁.re < z₂.im / z₂.re := by
  have h1' : 0 < (-z₁).re := by simp [h1]
  have h2' : 0 < (-z₂).re := by simp [h2]
  have heq : heading z₁ < heading z₂ ↔ heading (-z₁) < heading (-z₂) := by
    rw [heading_neg_of_neg h1, heading_neg_of_neg h2]; constructor <;> intro h <;> linarith
  rw [heq, heading_lt_iff_slope_pos h1' h2']
  simp [neg_div_neg_eq]

private lemma heading_gap_ge_pi_div_three {x y : ℂ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hd : 1 ≤ ‖x - y‖)
    (hxre : x.re ≠ 0) (hyre : y.re ≠ 0) (hlt : heading x < heading y) :
    Real.pi / 3 ≤ heading y - heading x ∧ heading y - heading x ≤ 5 * Real.pi / 3 := by

  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hxr : x.re = Real.cos (heading x) := by rw [cos_heading hx0, hx, div_one]
  have hxi : x.im = Real.sin (heading x) := by rw [sin_heading hx0, hx, div_one]
  have hyr : y.re = Real.cos (heading y) := by rw [cos_heading hy0, hy, div_one]
  have hyi : y.im = Real.sin (heading y) := by rw [sin_heading hy0, hy, div_one]
  have hcos : Real.cos (heading y - heading x) ≤ 1 / 2 := by
    have hsq : 1 ≤ ‖x - y‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hxr, hxi, hyr, hyi] at hsq
    rw [Real.cos_sub]
    nlinarith only [hsq, Real.sin_sq_add_cos_sq (heading x), Real.sin_sq_add_cos_sq (heading y)]
  have hb (z : ℂ) (hz : z.re ≠ 0) : -(Real.pi / 2) < heading z ∧ heading z < 3 * Real.pi / 2 := by
    rcases lt_or_gt_of_ne hz with h | h
    · have := heading_bounds_neg h; exact ⟨by linarith [Real.pi_pos], this.2⟩
    · have := heading_bounds_pos h; exact ⟨this.1, by linarith [Real.pi_pos]⟩
  have hbx := hb x hxre
  have hby := hb y hyre
  have hπ := Real.pi_pos
  have hid : Real.cos (2 * Real.pi - (heading y - heading x)) = Real.cos (heading y - heading x) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
  constructor
  · by_contra! H
    have hlt' := Real.strictAntiOn_cos
      (show heading y - heading x ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩) H
    rw [Real.cos_pi_div_three] at hlt'; linarith
  · by_contra! H
    have hlt' := Real.strictAntiOn_cos
      (show 2 * Real.pi - (heading y - heading x) ∈ Set.Icc 0 Real.pi from
        ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show 2 * Real.pi - (heading y - heading x) < Real.pi / 3 by linarith)
    rw [Real.cos_pi_div_three, hid] at hlt'; linarith

private def finPredPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  if h : 0 < n then
    { toFun := fun i => if hi : i.val = 0 then ⟨n - 1, by omega⟩ else ⟨i.val - 1, by omega⟩
      invFun := fun i => if hi : i.val + 1 = n then ⟨0, h⟩ else ⟨i.val + 1, by omega⟩
      left_inv := fun i => by
        apply Fin.ext; dsimp only
        rcases Nat.eq_zero_or_pos i.val with hi | hi
        · simp only [hi, ↓reduceDIte, Fin.val_mk, Nat.sub_add_cancel h]
        · have hne : i.val ≠ 0 := by omega
          simp only [hne, ↓reduceDIte, Fin.val_mk]
          have hne2 : i.val - 1 + 1 ≠ n := by omega
          simp only [hne2, ↓reduceDIte, Fin.val_mk]
          omega
      right_inv := fun i => by
        apply Fin.ext; dsimp only
        by_cases hi : i.val + 1 = n
        · simp only [hi, ↓reduceDIte, Fin.val_mk]
          omega
        · simp only [hi, ↓reduceDIte, Fin.val_mk]
          have hne2 : i.val + 1 ≠ 0 := by omega
          simp only [hne2, ↓reduceDIte, Fin.val_mk]
          omega }
  else Equiv.refl _

private lemma finPredPerm_apply_zero {n : ℕ} (h : 0 < n) (i : Fin n) (hi : i.val = 0) :
    (finPredPerm n i).val = n - 1 := by
  unfold finPredPerm; rw [dif_pos h]; simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]

private lemma finPredPerm_apply_pos {n : ℕ} (h : 0 < n) (i : Fin n) (hi : 0 < i.val) :
    (finPredPerm n i).val = i.val - 1 := by
  unfold finPredPerm; rw [dif_pos h]
  have hne : i.val ≠ 0 := by omega
  simp only [Equiv.coe_fn_mk, hne, ↓reduceDIte]

private lemma finPredPerm_isCyclic (n : ℕ) : IsCyclicPerm (finPredPerm n) := by
  intro x y
  have hpos : 0 < n := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 x)

  have hto0 : ∀ k : ℕ, ∀ i : Fin n, i.val = k → sameOrbit (finPredPerm n) i ⟨0, hpos⟩ := by
    intro k; induction k with
    | zero => intro i hi; exact ⟨0, Fin.ext hi⟩
    | succ k ihk =>
      intro i hi
      have h1 : (finPredPerm n i).val = k := by rw [finPredPerm_apply_pos hpos i (by omega)]; omega
      exact sameOrbit_trans _ (sameOrbit_step _ i) (ihk (finPredPerm n i) h1)
  have hfrom0 : ∀ d : ℕ, ∀ j : Fin n, n - 1 - j.val = d → sameOrbit (finPredPerm n) ⟨n - 1, by omega⟩ j := by
    intro d; induction d with
    | zero =>
      intro j hj; exact ⟨0, Fin.ext (by simp; omega)⟩
    | succ d ihd =>
      intro j hj
      have hjlt : j.val + 1 < n := by omega
      let j1 : Fin n := ⟨j.val + 1, hjlt⟩
      have hprev : finPredPerm n j1 = j := by
        apply Fin.ext; rw [finPredPerm_apply_pos hpos j1 (by simp [j1])]; simp [j1]
      have h1 := ihd j1 (by simp [j1]; omega)
      exact sameOrbit_trans _ h1 ⟨1, by simp [hprev]⟩
  have hx0 := hto0 x.val x rfl
  have h0last : sameOrbit (finPredPerm n) ⟨0, hpos⟩ ⟨n - 1, by omega⟩ :=
    ⟨1, Fin.ext (by simpa using finPredPerm_apply_zero hpos ⟨0, hpos⟩ rfl)⟩
  have hlasty := hfrom0 (n - 1 - y.val) y rfl
  exact sameOrbit_trans _ hx0 (sameOrbit_trans _ h0last hlasty)

private noncomputable def cwPredEquiv {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) : A ≃ Fin (Fintype.card A) := by
  classical
  let s : Finset ℝ := Finset.univ.image f
  have hcard : s.card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let emb : Fin (Fintype.card A) ↪o ℝ := s.orderEmbOfFin hcard
  have hmem : ∀ a : A, f a ∈ Set.range emb := by
    intro a; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem f (Finset.mem_univ a)
  let toFin : A → Fin (Fintype.card A) := fun a => Classical.choose (hmem a)
  have htoFin : ∀ a : A, emb (toFin a) = f a := fun a => Classical.choose_spec (hmem a)
  have hbij : Function.Bijective toFin :=
    (Fintype.bijective_iff_injective_and_card toFin).mpr
      ⟨fun a b h => hinj ((htoFin a).symm.trans ((congrArg emb h).trans (htoFin b))), by simp⟩
  exact Equiv.ofBijective toFin hbij

private lemma cwPredEquiv_strictMono {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a b : A) :
    f a < f b ↔ cwPredEquiv f hinj a < cwPredEquiv f hinj b := by
  classical
  unfold cwPredEquiv
  dsimp only
  set s := Finset.univ.image f
  have hcard : s.card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let emb := s.orderEmbOfFin hcard
  have hmem : ∀ x : A, f x ∈ Set.range emb := by
    intro x; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem f (Finset.mem_univ x)
  have hspec (x : A) : emb (Classical.choose (hmem x)) = f x := Classical.choose_spec (hmem x)
  change f a < f b ↔ Classical.choose (hmem a) < Classical.choose (hmem b)
  rw [← emb.lt_iff_lt, hspec a, hspec b]

private lemma cwPredEquiv_mono {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a b : A) :
    f a ≤ f b ↔ cwPredEquiv f hinj a ≤ cwPredEquiv f hinj b := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, cwPredEquiv_strictMono f hinj, hinj.eq_iff,
    (cwPredEquiv f hinj).injective.eq_iff]

private noncomputable def cwPredPerm {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) : Equiv.Perm A :=
  let e := cwPredEquiv f hinj
  e.trans ((finPredPerm (Fintype.card A)).trans e.symm)

private lemma cwPredPerm_isCyclic {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) :
    IsCyclicPerm (cwPredPerm f hinj) := by
  intro x y
  let e := cwPredEquiv f hinj
  obtain ⟨k, hk⟩ := finPredPerm_isCyclic (Fintype.card A) (e x) (e y)
  refine ⟨k, ?_⟩
  have hconj : ∀ m : ℕ, ∀ z : A,
      ((cwPredPerm f hinj) ^ m) z = e.symm (((finPredPerm (Fintype.card A)) ^ m) (e z)) := by
    intro m; induction m with
    | zero => intro z; simp
    | succ m ihm =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply, ihm, pow_succ', Equiv.Perm.mul_apply]
      simp [cwPredPerm, e]
  rw [hconj, hk, e.symm_apply_apply]

private lemma cwPredPerm_spec {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a : A) :
    ((∀ b : A, f a ≤ f b) ∧ (∀ b : A, f b ≤ f (cwPredPerm f hinj a))) ∨
    (f (cwPredPerm f hinj a) < f a ∧ ∀ b : A, f (cwPredPerm f hinj a) < f b → f a ≤ f b) := by
  have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  let e := cwPredEquiv f hinj
  have he_prev : e (cwPredPerm f hinj a) = finPredPerm (Fintype.card A) (e a) := by
    simp [cwPredPerm, e]
  rcases Nat.eq_zero_or_pos (e a).val with hi0 | hipos
  · left
    have hval := finPredPerm_apply_zero hpos (e a) hi0
    constructor
    · intro b
      rw [cwPredEquiv_mono f hinj]
      change (e a).val ≤ (e b).val; omega
    · intro b
      rw [cwPredEquiv_mono f hinj]
      change (e b).val ≤ (e (cwPredPerm f hinj a)).val
      rw [he_prev, hval]; have := (e b).isLt; omega
  · right
    have hval := finPredPerm_apply_pos hpos (e a) hipos
    constructor
    · rw [cwPredEquiv_strictMono f hinj]
      change (e (cwPredPerm f hinj a)).val < (e a).val
      rw [he_prev, hval]; omega
    · intro b hb
      rw [cwPredEquiv_strictMono f hinj] at hb
      change (e (cwPredPerm f hinj a)).val < (e b).val at hb
      rw [he_prev, hval] at hb
      rw [cwPredEquiv_mono f hinj]
      change (e a).val ≤ (e b).val; omega

private lemma cwPredPerm_isMin_iff {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (a : A) :
    (∀ b : A, f a ≤ f b) ↔ f a ≤ f (cwPredPerm f hinj a) := by
  rcases cwPredPerm_spec f hinj a with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
  · exact ⟨fun _ => hmin _, fun _ => hmin⟩
  · exact ⟨fun h => absurd (h _) (not_le_of_gt hlt), fun h => absurd h (not_le_of_gt hlt)⟩

private lemma cwPredPerm_ne_self {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℝ) (hinj : Function.Injective f) (hcard : 2 ≤ Fintype.card A) (a : A) :
    cwPredPerm f hinj a ≠ a := by
  rcases cwPredPerm_spec f hinj a with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
  · intro heq
    rw [heq] at hmax
    have huniq : ∀ b : A, b = a := fun b => hinj (le_antisymm (hmax b) (hmin b))
    have : Fintype.card A ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => (huniq x).trans (huniq y).symm)
    omega
  · intro heq; rw [heq] at hlt; exact lt_irrefl _ hlt

end HeadingAndRot

section SlabAndSqueeze

private structure GeoSetup (n : ℕ) where
  hn : 4 ≤ n
  p : Fin n → ℂ
  hx_mono : StrictMono (fun i => (p i).re)
  hsep : ∀ i j : Fin n, i ≠ j → 1 ≤ ‖p i - p j‖

namespace GeoSetup

variable {n : ℕ} (S : GeoSetup n)
include S

private def G : SimpleGraph (Fin n) where
  Adj i j := ‖S.p i - S.p j‖ = 1
  symm := ⟨fun i j h => by rwa [norm_sub_rev]⟩
  loopless := ⟨fun i h => by simp at h⟩

private lemma G_adj_iff (i j : Fin n) : S.G.Adj i j ↔ ‖S.p i - S.p j‖ = 1 := Iff.rfl

private lemma re_ne {i j : Fin n} (h : i ≠ j) : (S.p i).re ≠ (S.p j).re :=
  S.hx_mono.injective.ne h

private lemma p_sub_re_ne {i j : Fin n} (h : i ≠ j) : (S.p i - S.p j).re ≠ 0 := by
  rw [Complex.sub_re]; exact sub_ne_zero.mpr (S.re_ne h)

private lemma p_sub_re_pos_iff {i j : Fin n} : 0 < (S.p i - S.p j).re ↔ j < i := by
  rw [Complex.sub_re, sub_pos]; exact S.hx_mono.lt_iff_lt

private lemma p_sub_re_neg_iff {i j : Fin n} : (S.p i - S.p j).re < 0 ↔ i < j := by
  rw [Complex.sub_re, sub_neg]; exact S.hx_mono.lt_iff_lt

private lemma heading_inj_at (v : Fin n) :
    Function.Injective (fun u : {u : Fin n // S.G.Adj v u} => heading (S.p u.1 - S.p v)) := by
  intro u₁ u₂ heq
  apply Subtype.ext
  by_contra hne
  have hsep := S.hsep u₁.1 u₂.1 hne
  have h1 : ‖S.p u₁.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact u₁.2
  have h2 : ‖S.p u₂.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact u₂.2
  have hz1 : S.p u₁.1 - S.p v ≠ 0 := fun h => by simp [h] at h1
  have hz2 : S.p u₂.1 - S.p v ≠ 0 := fun h => by simp [h] at h2
  have hvec : S.p u₁.1 - S.p v = S.p u₂.1 - S.p v := by
    apply Complex.ext
    · have c1 := cos_heading hz1; have c2 := cos_heading hz2
      rw [h1, div_one] at c1; rw [h2, div_one] at c2; linarith [congrArg Real.cos heq]
    · have s1 := sin_heading hz1; have s2 := sin_heading hz2
      rw [h1, div_one] at s1; rw [h2, div_one] at s2; linarith [congrArg Real.sin heq]
  have hp : S.p u₁.1 = S.p u₂.1 := sub_left_inj.mp hvec
  rw [hp, sub_self, norm_zero] at hsep
  norm_num at hsep

private lemma edgeY_ne_of_ne_edges {a₁ b₁ a₂ b₂ : Fin n}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hadj₁ : S.G.Adj a₁ b₁) (hadj₂ : S.G.Adj a₂ b₂)
    (hne : (a₁, b₁) ≠ (a₂, b₂))
    {x : ℝ} (hx₁ : (S.p a₁).re < x) (hx₂ : x < (S.p b₁).re)
    (hx₃ : (S.p a₂).re < x) (hx₄ : x < (S.p b₂).re) :
    edgeY S.p a₁ b₁ x ≠ edgeY S.p a₂ b₂ x := by
  intro hy
  have hr₁ : (S.p a₁).re < (S.p b₁).re := S.hx_mono h₁
  have hr₂ : (S.p a₂).re < (S.p b₂).re := S.hx_mono h₂
  set s := (x - (S.p a₁).re) / ((S.p b₁).re - (S.p a₁).re)
  set t := (x - (S.p a₂).re) / ((S.p b₂).re - (S.p a₂).re)
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hpt : (1 - s) • S.p a₁ + s • S.p b₁ = (1 - t) • S.p a₂ + t • S.p b₂ := by
    rw [← edgeY_point_eq S.p hr₁ x, ← edgeY_point_eq S.p hr₂ x, hy]

  by_cases ha12 : a₁ = a₂
  · subst ha12
    have hdir : s • (S.p b₁ - S.p a₁) = t • (S.p b₂ - S.p a₁) := by
      simp only [Complex.real_smul] at hpt ⊢; push_cast at hpt ⊢; linear_combination hpt
    have hnorm := congrArg norm hdir
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs0.le, Real.norm_of_nonneg ht0.le,
      norm_sub_rev, hadj₁, norm_sub_rev, hadj₂, mul_one, mul_one] at hnorm
    rw [← hnorm] at hdir
    have hpb : S.p b₁ = S.p b₂ := by
      have : S.p b₁ - S.p a₁ = S.p b₂ - S.p a₁ := smul_right_injective ℂ (ne_of_gt hs0) hdir
      exact sub_left_inj.mp this
    have hb12 : b₁ = b₂ := S.hx_mono.injective (congrArg Complex.re hpb)
    exact hne (Prod.ext rfl hb12)
  · by_cases hb12 : b₁ = b₂
    · subst hb12
      have hdir : (1 - s) • (S.p a₁ - S.p b₁) = (1 - t) • (S.p a₂ - S.p b₁) := by
        simp only [Complex.real_smul] at hpt ⊢; push_cast at hpt ⊢; linear_combination hpt
      have hnorm := congrArg norm hdir
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith),
        hadj₁, hadj₂, mul_one, mul_one] at hnorm
      have hst : 1 - s = 1 - t := hnorm
      have hpa : S.p a₁ = S.p a₂ := by
        rw [hst] at hdir
        have : S.p a₁ - S.p b₁ = S.p a₂ - S.p b₁ := smul_right_injective ℂ (by linarith) hdir
        exact sub_left_inj.mp this
      have ha : a₁ = a₂ := S.hx_mono.injective (congrArg Complex.re hpa)
      exact ha12 ha
    · have ha1b2 : a₁ ≠ b₂ := fun h => by subst h; linarith
      have hb1a2 : b₁ ≠ a₂ := fun h => by subst h; linarith
      exact no_unit_seg_crossing hadj₁ hadj₂
        (S.hsep _ _ ha12) (S.hsep _ _ (Ne.symm hb1a2)) (S.hsep _ _ hb12) (S.hsep _ _ (Ne.symm ha1b2))
        hs0.le hs1.le ht0.le ht1.le hpt

private lemma edgeY_order_preserved {a₁ b₁ a₂ b₂ : Fin n}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hadj₁ : S.G.Adj a₁ b₁) (hadj₂ : S.G.Adj a₂ b₂)
    (hne : (a₁, b₁) ≠ (a₂, b₂))
    {x x' : ℝ}
    (hx₁ : (S.p a₁).re < x) (hx₂ : x < (S.p b₁).re)
    (hx₃ : (S.p a₂).re < x) (hx₄ : x < (S.p b₂).re)
    (hx₁' : (S.p a₁).re < x') (hx₂' : x' < (S.p b₁).re)
    (hx₃' : (S.p a₂).re < x') (hx₄' : x' < (S.p b₂).re)
    (hlt : edgeY S.p a₁ b₁ x < edgeY S.p a₂ b₂ x) :
    edgeY S.p a₁ b₁ x' < edgeY S.p a₂ b₂ x' := by
  by_contra! hge
  have hne' := S.edgeY_ne_of_ne_edges h₁ h₂ hadj₁ hadj₂ hne hx₁' hx₂' hx₃' hx₄'
  have hgt : edgeY S.p a₂ b₂ x' < edgeY S.p a₁ b₁ x' := lt_of_le_of_ne hge (Ne.symm hne')

  let f (z : ℝ) : ℝ := edgeY S.p a₁ b₁ z - edgeY S.p a₂ b₂ z
  have hfx : f x < 0 := sub_neg.mpr hlt
  have hfx' : 0 < f x' := sub_pos.mpr hgt
  let lam : ℝ := -f x / (f x' - f x)
  have hlam0 : 0 < lam := div_pos (by linarith) (by linarith)
  have hlam1 : lam < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let xstar : ℝ := (1 - lam) * x + lam * x'
  have haff : ∀ z : ℝ, f z = f 0 + (edgeSlope S.p a₁ b₁ - edgeSlope S.p a₂ b₂) * z := by
    intro z; simp only [f, edgeY_eq_left_add_slope]; ring
  have hfstar : f xstar = 0 := by
    have hlin : f xstar = (1 - lam) * f x + lam * f x' := by
      rw [haff xstar, haff x, haff x']; simp only [xstar]; ring
    rw [hlin]
    have hden : f x' - f x ≠ 0 := by linarith
    dsimp [lam]; field_simp [hden]; ring
  have hbet : min x x' < xstar ∧ xstar < max x x' := by
    rcases le_total x x' with hxx | hxx
    · have hlt_xx : x < x' := lt_of_le_of_ne hxx (fun h => by rw [h] at hlt; linarith)
      rw [min_eq_left hxx, max_eq_right hxx]
      exact ⟨by dsimp [xstar]; nlinarith, by dsimp [xstar]; nlinarith⟩
    · have hlt_xx : x' < x := lt_of_le_of_ne hxx (fun h => by rw [← h] at hlt; linarith)
      rw [min_eq_right hxx, max_eq_left hxx]
      exact ⟨by dsimp [xstar]; nlinarith, by dsimp [xstar]; nlinarith⟩
  have h1 : (S.p a₁).re < xstar := lt_of_lt_of_le (lt_min hx₁ hx₁') hbet.1.le
  have h2 : xstar < (S.p b₁).re := lt_of_le_of_lt hbet.2.le (max_lt hx₂ hx₂')
  have h3 : (S.p a₂).re < xstar := lt_of_lt_of_le (lt_min hx₃ hx₃') hbet.1.le
  have h4 : xstar < (S.p b₂).re := lt_of_le_of_lt hbet.2.le (max_lt hx₄ hx₄')
  exact S.edgeY_ne_of_ne_edges h₁ h₂ hadj₁ hadj₂ hne h1 h2 h3 h4 (sub_eq_zero.mp hfstar)

private lemma edgeY_ne_vertex {a b v : Fin n} (hav : a < v) (hvb : v < b)
    (hadj : S.G.Adj a b) : edgeY S.p a b (S.p v).re ≠ (S.p v).im := by
  intro hy
  have hab : (S.p a).re < (S.p b).re := S.hx_mono (hav.trans hvb)
  set t := ((S.p v).re - (S.p a).re) / ((S.p b).re - (S.p a).re)
  have ht0 : 0 ≤ t := (div_pos (sub_pos.mpr (S.hx_mono hav)) (by linarith)).le
  have ht1 : t ≤ 1 := ((div_lt_one (by linarith)).mpr (sub_lt_sub_right (S.hx_mono hvb) _)).le
  have heq : S.p v = (1 - t) • S.p a + t • S.p b := by
    rw [← edgeY_point_eq S.p hab (S.p v).re, hy]
  exact not_on_closed_unit_seg hadj (S.hsep a v hav.ne) (S.hsep b v hvb.ne.symm) ht0 ht1 heq

private lemma edgeY_lt_incident_right {a b v w : Fin n}
    (hav : a < v) (hvb : v < b) (hvw : v < w) (hadj₁ : S.G.Adj a b) (hadj₂ : S.G.Adj v w)
    {x : ℝ} (hx₁ : (S.p v).re < x) (hx₂ : x < (S.p b).re) (hx₃ : x < (S.p w).re) :
    edgeY S.p a b x < edgeY S.p v w x ↔ edgeY S.p a b (S.p v).re < (S.p v).im := by
  have hab : a < b := hav.trans hvb
  have hne : (a, b) ≠ (v, w) := fun h => hav.ne (congrArg Prod.fst h)
  have hxa : (S.p a).re < x := (S.hx_mono hav).trans hx₁

  let f (z : ℝ) : ℝ := edgeY S.p a b z - edgeY S.p v w z
  have hfv : f (S.p v).re = edgeY S.p a b (S.p v).re - (S.p v).im := by
    simp only [f, edgeY_at_left]
  have hfv_ne : f (S.p v).re ≠ 0 := by
    rw [hfv]; exact sub_ne_zero.mpr (S.edgeY_ne_vertex hav hvb hadj₁)
  have hfx_ne : f x ≠ 0 := sub_ne_zero.mpr (S.edgeY_ne_of_ne_edges hab hvw hadj₁ hadj₂ hne hxa hx₂ hx₁ hx₃)
  have hno_opp : ¬ (f (S.p v).re * f x < 0) := by
    intro hneg
    have hdiff : f x - f (S.p v).re ≠ 0 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        linarith
      · have h2 : f x < 0 := by nlinarith
        linarith
    let lam := -f (S.p v).re / (f x - f (S.p v).re)
    have hlam0 : 0 < lam := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact div_pos (by linarith) (by linarith)
      · have h2 : f x < 0 := by nlinarith
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hlam1 : lam < 1 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact (div_lt_one (by linarith)).mpr (by linarith)
      · have h2 : f x < 0 := by nlinarith
        rw [div_lt_iff_of_neg (by linarith)]; linarith
    let xstar := (1 - lam) * (S.p v).re + lam * x
    have haff : ∀ z : ℝ, f z = f 0 + (edgeSlope S.p a b - edgeSlope S.p v w) * z := by
      intro z; simp only [f, edgeY_eq_left_add_slope]; ring
    have hfstar : f xstar = 0 := by
      have hlin : f xstar = (1 - lam) * f (S.p v).re + lam * f x := by
        rw [haff xstar, haff (S.p v).re, haff x]; simp only [xstar]; ring
      rw [hlin]; dsimp [lam]; field_simp [hdiff]; ring
    have h1 : (S.p v).re < xstar := by dsimp [xstar]; nlinarith
    have h2 : xstar < x := by dsimp [xstar]; nlinarith
    exact S.edgeY_ne_of_ne_edges hab hvw hadj₁ hadj₂ hne ((S.hx_mono hav).trans h1)
      (h2.trans hx₂) h1 (h2.trans hx₃) (sub_eq_zero.mp hfstar)
  constructor
  · intro hlt
    have hfx : f x < 0 := sub_neg.mpr hlt
    by_contra! hge
    have hfv_pos : 0 < f (S.p v).re := by
      rw [hfv]; exact sub_pos.mpr (lt_of_le_of_ne hge (S.edgeY_ne_vertex hav hvb hadj₁).symm)
    exact hno_opp (mul_neg_of_pos_of_neg hfv_pos hfx)
  · intro hlt
    have hfv_neg : f (S.p v).re < 0 := by rw [hfv]; exact sub_neg.mpr hlt
    by_contra! hge
    have hfx_pos : 0 < f x := lt_of_le_of_ne (sub_nonneg.mpr hge) hfx_ne.symm
    exact hno_opp (mul_neg_of_neg_of_pos hfv_neg hfx_pos)

private lemma edgeY_lt_incident_left {a b u v : Fin n}
    (hav : a < v) (hvb : v < b) (huv : u < v) (hadj₁ : S.G.Adj a b) (hadj₂ : S.G.Adj u v)
    {x : ℝ} (hx₁ : (S.p a).re < x) (hx₂ : (S.p u).re < x) (hx₃ : x < (S.p v).re) :
    edgeY S.p a b x < edgeY S.p u v x ↔ edgeY S.p a b (S.p v).re < (S.p v).im := by
  have hab : a < b := hav.trans hvb
  have hne : (a, b) ≠ (u, v) := fun h => hvb.ne (congrArg Prod.snd h).symm
  have hxb : x < (S.p b).re := hx₃.trans (S.hx_mono hvb)
  let f (z : ℝ) : ℝ := edgeY S.p a b z - edgeY S.p u v z
  have hfv : f (S.p v).re = edgeY S.p a b (S.p v).re - (S.p v).im := by
    simp only [f, edgeY_at_right S.p (S.hx_mono huv)]
  have hfv_ne : f (S.p v).re ≠ 0 := by
    rw [hfv]; exact sub_ne_zero.mpr (S.edgeY_ne_vertex hav hvb hadj₁)
  have hfx_ne : f x ≠ 0 := sub_ne_zero.mpr (S.edgeY_ne_of_ne_edges hab huv hadj₁ hadj₂ hne hx₁ hxb hx₂ hx₃)
  have hno_opp : ¬ (f (S.p v).re * f x < 0) := by
    intro hneg
    have hdiff : f x - f (S.p v).re ≠ 0 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        linarith
      · have h2 : f x < 0 := by nlinarith
        linarith
    let lam := -f (S.p v).re / (f x - f (S.p v).re)
    have hlam0 : 0 < lam := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact div_pos (by linarith) (by linarith)
      · have h2 : f x < 0 := by nlinarith
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hlam1 : lam < 1 := by
      rcases lt_or_gt_of_ne hfv_ne with h1 | h1
      · have h2 : 0 < f x := by nlinarith
        exact (div_lt_one (by linarith)).mpr (by linarith)
      · have h2 : f x < 0 := by nlinarith
        rw [div_lt_iff_of_neg (by linarith)]; linarith
    let xstar := (1 - lam) * (S.p v).re + lam * x
    have haff : ∀ z : ℝ, f z = f 0 + (edgeSlope S.p a b - edgeSlope S.p u v) * z := by
      intro z; simp only [f, edgeY_eq_left_add_slope]; ring
    have hfstar : f xstar = 0 := by
      have hlin : f xstar = (1 - lam) * f (S.p v).re + lam * f x := by
        rw [haff xstar, haff (S.p v).re, haff x]; simp only [xstar]; ring
      rw [hlin]; dsimp [lam]; field_simp [hdiff]; ring
    have h1 : x < xstar := by dsimp [xstar]; nlinarith
    have h2 : xstar < (S.p v).re := by dsimp [xstar]; nlinarith
    exact S.edgeY_ne_of_ne_edges hab huv hadj₁ hadj₂ hne (hx₁.trans h1)
      (h2.trans (S.hx_mono hvb)) (hx₂.trans h1) h2 (sub_eq_zero.mp hfstar)
  constructor
  · intro hlt
    have hfx : f x < 0 := sub_neg.mpr hlt
    by_contra! hge
    have hfv_pos : 0 < f (S.p v).re := by
      rw [hfv]; exact sub_pos.mpr (lt_of_le_of_ne hge (S.edgeY_ne_vertex hav hvb hadj₁).symm)
    exact hno_opp (mul_neg_of_pos_of_neg hfv_pos hfx)
  · intro hlt
    have hfv_neg : f (S.p v).re < 0 := by rw [hfv]; exact sub_neg.mpr hlt
    by_contra! hge
    have hfx_pos : 0 < f x := lt_of_le_of_ne (sub_nonneg.mpr hge) hfx_ne.symm
    exact hno_opp (mul_neg_of_neg_of_pos hfv_neg hfx_pos)

section Subgraph

open Classical

variable (H : SimpleGraph (Fin n))

private lemma heading_inj_H (hHG : H ≤ S.G) (v : Fin n) :
    Function.Injective (fun u : {u : Fin n // H.Adj v u} => heading (S.p u.1 - S.p v)) := by
  intro u₁ u₂ heq
  have h1 : (⟨u₁.1, hHG u₁.2⟩ : {u : Fin n // S.G.Adj v u}) = ⟨u₂.1, hHG u₂.2⟩ :=
    S.heading_inj_at v heq
  exact Subtype.ext (congrArg (Subtype.val : {u : Fin n // S.G.Adj v u} → Fin n) h1)

private noncomputable def geoSigma (hHG : H ≤ S.G) (v : Fin n) : Equiv.Perm {u : Fin n // H.Adj v u} :=
  cwPredPerm (fun u : {u : Fin n // H.Adj v u} => heading (S.p u.1 - S.p v)) (S.heading_inj_H H hHG v)

private lemma geoSigma_isCyclic (hHG : H ≤ S.G) (v : Fin n) :
    IsCyclicPerm (S.geoSigma H hHG v) :=
  cwPredPerm_isCyclic _ (S.heading_inj_H H hHG v)

private lemma geoSigma_spec (hHG : H ≤ S.G) (v : Fin n) (a : {u : Fin n // H.Adj v u}) :
    ((∀ b : {u : Fin n // H.Adj v u}, heading (S.p a.1 - S.p v) ≤ heading (S.p b.1 - S.p v)) ∧
     (∀ b : {u : Fin n // H.Adj v u}, heading (S.p b.1 - S.p v) ≤ heading (S.p (S.geoSigma H hHG v a).1 - S.p v))) ∨
    (heading (S.p (S.geoSigma H hHG v a).1 - S.p v) < heading (S.p a.1 - S.p v) ∧
     ∀ b : {u : Fin n // H.Adj v u}, heading (S.p (S.geoSigma H hHG v a).1 - S.p v) < heading (S.p b.1 - S.p v) →
       heading (S.p a.1 - S.p v) ≤ heading (S.p b.1 - S.p v)) :=
  cwPredPerm_spec _ (S.heading_inj_H H hHG v) a

private lemma geoSigma_ne_self (hHG : H ≤ S.G) (v : Fin n)
    (hdeg2 : ∃ u₁ u₂ : Fin n, H.Adj v u₁ ∧ H.Adj v u₂ ∧ u₁ ≠ u₂) (a : {u : Fin n // H.Adj v u}) :
    S.geoSigma H hHG v a ≠ a := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := hdeg2
  have hcard2 : 2 ≤ Fintype.card {u : Fin n // H.Adj v u} := by
    have hne' : (⟨u₁, hu₁⟩ : {u : Fin n // H.Adj v u}) ≠ ⟨u₂, hu₂⟩ := fun h => hne (congrArg Subtype.val h)
    have hle := Finset.card_le_univ ({⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩} : Finset {u : Fin n // H.Adj v u})
    rw [Finset.card_pair hne'] at hle
    exact hle
  exact cwPredPerm_ne_self _ (S.heading_inj_H H hHG v) hcard2 a

private noncomputable def geoPhi (hHG : H ≤ S.G) : Equiv.Perm (DartOf H) :=
  dartPerm H (S.geoSigma H hHG)

private def isMinNeighbor (d : DartOf H) : Prop :=
  ∀ w : Fin n, H.Adj d.1.2 w → heading (S.p d.1.1 - S.p d.1.2) ≤ heading (S.p w - S.p d.1.2)

private noncomputable def gapAngle (hHG : H ≤ S.G) (d : DartOf H) : ℝ :=
  let v := d.1.2
  let u := d.1.1
  let w := (S.geoSigma H hHG v ⟨u, d.2.symm⟩).1
  let α_in := heading (S.p u - S.p v)
  let α_out := heading (S.p w - S.p v)
  α_in - α_out + if S.isMinNeighbor H d then 2 * Real.pi else 0

private lemma gapAngle_sum_at_vertex (hHG : H ≤ S.G) (v : Fin n) (hdeg : ∃ u, H.Adj v u) :
    ∑ u : {u : Fin n // H.Adj v u}, S.gapAngle H hHG ⟨(u.1, v), u.2.symm⟩ = 2 * Real.pi := by
  let f : {u : Fin n // H.Adj v u} → ℝ := fun u => heading (S.p u.1 - S.p v)
  have h1 : ∑ u : {u : Fin n // H.Adj v u}, (f u - f (S.geoSigma H hHG v u)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hcomp : ∑ u : {u : Fin n // H.Adj v u}, f (S.geoSigma H hHG v u) =
        ∑ u : {u : Fin n // H.Adj v u}, f u :=
      Fintype.sum_equiv (S.geoSigma H hHG v) (fun u => f (S.geoSigma H hHG v u)) f (fun _ => rfl)
    rw [hcomp, sub_self]
  obtain ⟨u₁, hu₁⟩ := hdeg
  have hne : (Finset.univ : Finset {u : Fin n // H.Adj v u}).Nonempty := ⟨⟨u₁, hu₁⟩, Finset.mem_univ _⟩
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_min_image Finset.univ f hne
  have hmin_iff : ∀ u : {u : Fin n // H.Adj v u},
      S.isMinNeighbor H ⟨(u.1, v), u.2.symm⟩ ↔ u = u₀ := by
    intro u
    constructor
    · intro h
      exact S.heading_inj_H H hHG v (le_antisymm (h u₀.1 u₀.2) (hu₀ u (Finset.mem_univ u)))
    · rintro rfl w hw
      exact hu₀ ⟨w, hw⟩ (Finset.mem_univ _)
  have h2 : ∑ u : {u : Fin n // H.Adj v u},
      (if S.isMinNeighbor H ⟨(u.1, v), u.2.symm⟩ then (2 * Real.pi : ℝ) else 0) = 2 * Real.pi := by
    rw [Finset.sum_eq_single u₀]
    · exact if_pos ((hmin_iff u₀).mpr rfl)
    · intro u _ hne
      exact if_neg (fun h => hne ((hmin_iff u).mp h))
    · intro h; exact (h (Finset.mem_univ u₀)).elim
  have hunf : ∀ u : {u : Fin n // H.Adj v u},
      S.gapAngle H hHG ⟨(u.1, v), u.2.symm⟩ =
      (f u - f (S.geoSigma H hHG v u)) +
      if S.isMinNeighbor H ⟨(u.1, v), u.2.symm⟩ then (2 * Real.pi : ℝ) else 0 := by
    intro ⟨u, hu⟩
    simp only [gapAngle, f]
  rw [Finset.sum_congr rfl (fun u _ => hunf u), Finset.sum_add_distrib, h1, h2, zero_add]

private lemma gapAngle_ge_pi_div_three (hHG : H ≤ S.G) (d : DartOf H) :
    Real.pi / 3 ≤ S.gapAngle H hHG d := by
  classical
  let v := d.1.2
  let u : {x : Fin n // H.Adj v x} := ⟨d.1.1, d.2.symm⟩
  let w := S.geoSigma H hHG v u
  have hnorm_u : ‖S.p u.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact hHG u.2
  have hnorm_w : ‖S.p w.1 - S.p v‖ = 1 := by rw [norm_sub_rev]; exact hHG w.2
  have hre_u : (S.p u.1 - S.p v).re ≠ 0 := S.p_sub_re_ne (H.ne_of_adj u.2).symm
  have hre_w : (S.p w.1 - S.p v).re ≠ 0 := S.p_sub_re_ne (H.ne_of_adj w.2).symm
  by_cases huw : u = w
  ·
    have hmin : S.isMinNeighbor H d := by
      have hspec := (cwPredPerm_isMin_iff _ (S.heading_inj_H H hHG v) u).mpr (by rw [show cwPredPerm _ _ u = w from rfl, ← huw])
      intro x hx; exact hspec ⟨x, hx⟩
    unfold gapAngle
    dsimp only
    change heading (S.p u.1 - S.p v) - heading (S.p w.1 - S.p v) +
      (if S.isMinNeighbor H d then 2 * Real.pi else 0) ≥ Real.pi / 3
    rw [huw, sub_self, zero_add, if_pos hmin]
    linarith [Real.pi_pos]
  · have hsep_uw : 1 ≤ ‖(S.p u.1 - S.p v) - (S.p w.1 - S.p v)‖ := by
      rw [sub_sub_sub_cancel_right]
      exact S.hsep u.1 w.1 (fun h => huw (Subtype.ext h))
    rcases cwPredPerm_spec (fun x : {x : Fin n // H.Adj v x} => heading (S.p x.1 - S.p v))
        (S.heading_inj_H H hHG v) u with ⟨hmin, hmax⟩ | ⟨hlt, _⟩
    · have hmin' : S.isMinNeighbor H d := fun x hx => hmin ⟨x, hx⟩
      have hlt : heading (S.p u.1 - S.p v) < heading (S.p w.1 - S.p v) :=
        lt_of_le_of_ne (hmin w) (fun h => huw (S.heading_inj_H H hHG v h))
      have hgap := heading_gap_ge_pi_div_three hnorm_u hnorm_w hsep_uw hre_u hre_w hlt
      unfold gapAngle; dsimp only
      change Real.pi / 3 ≤ heading (S.p u.1 - S.p v) - heading (S.p w.1 - S.p v) +
        (if S.isMinNeighbor H d then 2 * Real.pi else 0)
      rw [if_pos hmin']
      linarith [hgap.2]
    · have hnotmin : ¬ S.isMinNeighbor H d := fun h => not_lt_of_ge (h w.1 w.2) hlt
      have hsep_wu : 1 ≤ ‖(S.p w.1 - S.p v) - (S.p u.1 - S.p v)‖ := by
        rw [norm_sub_rev]; exact hsep_uw
      have hgap := heading_gap_ge_pi_div_three hnorm_w hnorm_u hsep_wu hre_w hre_u hlt
      unfold gapAngle; dsimp only
      change Real.pi / 3 ≤ heading (S.p u.1 - S.p v) - heading (S.p w.1 - S.p v) +
        (if S.isMinNeighbor H d then 2 * Real.pi else 0)
      rw [if_neg hnotmin, add_zero]
      exact hgap.1

private def isLeftTip (d : DartOf H) : Prop :=
  d.1.2 < d.1.1 ∧ ¬ S.isMinNeighbor H d

private def isRightCap (d : DartOf H) : Prop :=
  d.1.1 < d.1.2 ∧ S.isMinNeighbor H d

private lemma gapAngle_telescoping (hHG : H ≤ S.G) (d : DartOf H) :
    S.gapAngle H hHG d =
      Real.pi + heading (S.p d.1.2 - S.p d.1.1) -
      heading (S.p (S.geoPhi H hHG d).1.2 - S.p (S.geoPhi H hHG d).1.1) +
      (if S.isRightCap H d then 2 * Real.pi else 0) -
      (if S.isLeftTip H d then 2 * Real.pi else 0) := by
  rcases d with ⟨⟨u, v⟩, huv_adj⟩
  have huv_ne : u ≠ v := H.ne_of_adj huv_adj
  have hneg : S.p v - S.p u = -(S.p u - S.p v) := by ring
  unfold gapAngle isRightCap isLeftTip
  dsimp only [geoPhi, dartPerm, Equiv.coe_fn_mk]
  rcases lt_or_gt_of_ne huv_ne with huv | hvu
  · have hre : (S.p u - S.p v).re < 0 := S.p_sub_re_neg_iff.mpr huv
    have hhead : heading (S.p v - S.p u) = heading (S.p u - S.p v) - Real.pi := by
      rw [hneg]; exact heading_neg_of_neg hre
    have hnot : ¬ (v < u) := not_lt.mpr huv.le
    rw [hhead]
    by_cases hmin : S.isMinNeighbor H ⟨(u, v), huv_adj⟩
    · simp only [if_pos hmin, if_pos (And.intro huv hmin), hnot, false_and, if_false]; ring
    · simp only [hmin, and_false, hnot, false_and, if_false]; ring
  · have hre : 0 < (S.p u - S.p v).re := S.p_sub_re_pos_iff.mpr hvu
    have hhead : heading (S.p v - S.p u) = heading (S.p u - S.p v) + Real.pi := by
      rw [hneg]; exact heading_neg_of_pos hre
    have hnot : ¬ (u < v) := not_lt.mpr hvu.le
    rw [hhead]
    by_cases hmin : S.isMinNeighbor H ⟨(u, v), huv_adj⟩
    · simp only [hmin, not_true_eq_false, and_false, hnot, false_and, if_true, if_false]; ring
    · simp only [if_neg hmin, hnot, false_and, if_pos (And.intro hvu hmin), if_false]; ring

private lemma invariant_set_angle_sum (hHG : H ≤ S.G) (C : Finset (DartOf H))
    (hinv : ∀ d ∈ C, S.geoPhi H hHG d ∈ C) :
    haveI := Classical.decPred (S.isLeftTip H)
    haveI := Classical.decPred (S.isRightCap H)
    ∑ d ∈ C, S.gapAngle H hHG d =
      (C.card : ℝ) * Real.pi -
      2 * Real.pi * (((C.filter (S.isLeftTip H)).card : ℝ) -
                     ((C.filter (S.isRightCap H)).card : ℝ)) := by
  classical

  have hbij : Finset.image (S.geoPhi H hHG) C = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact hinv d hd
    · rw [Finset.card_image_of_injective C (S.geoPhi H hHG).injective]
  have htele : ∑ d ∈ C, heading (S.p (S.geoPhi H hHG d).1.2 - S.p (S.geoPhi H hHG d).1.1) =
      ∑ d ∈ C, heading (S.p d.1.2 - S.p d.1.1) := by
    conv_rhs => rw [← hbij]
    rw [Finset.sum_image (fun a _ b _ h => (S.geoPhi H hHG).injective h)]
  have hsum : ∑ d ∈ C, S.gapAngle H hHG d =
      ∑ d ∈ C, (Real.pi + heading (S.p d.1.2 - S.p d.1.1) -
        heading (S.p (S.geoPhi H hHG d).1.2 - S.p (S.geoPhi H hHG d).1.1) +
        (if S.isRightCap H d then (2 * Real.pi : ℝ) else 0) -
        (if S.isLeftTip H d then (2 * Real.pi : ℝ) else 0)) :=
    Finset.sum_congr rfl (fun d _ => S.gapAngle_telescoping H hHG d)
  rw [hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [htele]
  ring

private noncomputable def orientEdges : Finset (Fin n × Fin n) := by
  classical
  let _ := S
  exact Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2 ∧ H.Adj e.1 e.2)

private lemma orientEdges_card :
    haveI := Classical.decRel H.Adj
    (S.orientEdges H).card = H.edgeFinset.card := by
  classical
  let f : Fin n × Fin n → Sym2 (Fin n) := fun e => s(e.1, e.2)
  have hinj : Set.InjOn f ↑(S.orientEdges H) := by
    intro e₁ he₁ e₂ he₂ hf
    simp only [Finset.mem_coe, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    rcases Sym2.eq_iff.mp hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; rw [h1, h2] at he₁; exact lt_asymm he₁.1 he₂.1
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext x
  induction x using Sym2.ind with | _ a b =>
  simp only [Finset.mem_image, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_edgeFinset, f]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨_, hadj⟩, hEq⟩
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · intro hab
    rcases lt_or_gt_of_ne (H.ne_of_adj hab) with h | h
    · exact ⟨(a, b), ⟨h, hab⟩, rfl⟩
    · exact ⟨(b, a), ⟨h, hab.symm⟩, Sym2.eq_swap⟩

private noncomputable def activeEdges (i : Fin (n + 1)) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.1.val < i.val ∧ i.val ≤ e.2.val)

private lemma activeEdges_zero : S.activeEdges H 0 = ∅ := by
  classical
  ext e; simp [activeEdges]

private lemma activeEdges_last : S.activeEdges H (Fin.last n) = ∅ := by
  classical
  ext e
  simp only [activeEdges, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and,
    Fin.val_last]
  intro _ _ hle
  omega

private noncomputable def slabMid (i : Fin (n + 1)) : ℝ :=
  if h1 : 0 < i.val then
    if h2 : i.val < n then
      ((S.p ⟨i.val - 1, by omega⟩).re + (S.p ⟨i.val, h2⟩).re) / 2
    else (S.p ⟨n - 1, by have := S.hn; omega⟩).re + 1
  else (S.p ⟨0, by have := S.hn; omega⟩).re - 1

private lemma slabMid_between {i : Fin (n + 1)} {e : Fin n × Fin n}
    (he : e ∈ S.activeEdges H i) :
    (S.p e.1).re < S.slabMid i ∧ S.slabMid i < (S.p e.2).re := by
  classical
  simp only [activeEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  have h1 : 0 < i.val := by omega
  have h2 : i.val < n := by omega
  unfold slabMid
  rw [dif_pos h1, dif_pos h2]
  have ha : (S.p e.1).re ≤ (S.p ⟨i.val - 1, by omega⟩).re :=
    S.hx_mono.monotone (show e.1 ≤ ⟨i.val - 1, by omega⟩ from by change e.1.val ≤ i.val - 1; omega)
  have hb : (S.p ⟨i.val, h2⟩).re ≤ (S.p e.2).re :=
    S.hx_mono.monotone (show ⟨i.val, h2⟩ ≤ e.2 from by change i.val ≤ e.2.val; omega)
  have hlt : (S.p ⟨i.val - 1, by omega⟩).re < (S.p ⟨i.val, h2⟩).re :=
    S.hx_mono (show (⟨i.val - 1, by omega⟩ : Fin n) < ⟨i.val, h2⟩ from by change i.val - 1 < i.val; omega)
  exact ⟨by linarith, by linarith⟩

private lemma slabMid_castSucc_lt {v : Fin n} (h1 : 0 < v.val) :
    S.slabMid v.castSucc < (S.p v).re := by
  unfold slabMid
  rw [dif_pos (by simp [h1]), dif_pos (by simp [v.isLt])]
  have hlt := S.hx_mono (show (⟨v.val - 1, by omega⟩ : Fin n) < v from by change v.val - 1 < v.val; omega)
  have h1' : (⟨v.castSucc.val - 1, by simp; omega⟩ : Fin n) = ⟨v.val - 1, by omega⟩ := Fin.ext (by simp)
  have h2' : (⟨v.castSucc.val, by simp [v.isLt]⟩ : Fin n) = v := Fin.ext rfl
  rw [h1', h2']; linarith

private lemma lt_slabMid_succ {v : Fin n} (h2 : v.val + 1 < n) :
    (S.p v).re < S.slabMid v.succ := by
  unfold slabMid
  rw [dif_pos (by simp), dif_pos (by simp [h2])]
  have hlt := S.hx_mono (show v < ⟨v.val + 1, h2⟩ from by change v.val < v.val + 1; omega)
  have h1' : (⟨v.succ.val - 1, by simp⟩ : Fin n) = v := Fin.ext (by simp)
  have h2' : (⟨v.succ.val, by simp [h2]⟩ : Fin n) = ⟨v.val + 1, h2⟩ := Fin.ext (by simp)
  rw [h1', h2']; linarith

private noncomputable def passEdges (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.1 < v ∧ v < e.2)

private noncomputable def passBelow (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.passEdges H v).filter (fun e => edgeY S.p e.1 e.2 (S.p v).re < (S.p v).im)

private noncomputable def passAbove (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.passEdges H v).filter (fun e => (S.p v).im < edgeY S.p e.1 e.2 (S.p v).re)

private noncomputable def leftEdges (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.2 = v)

private noncomputable def rightEdges (v : Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact (S.orientEdges H).filter (fun e => e.1 = v)

private lemma passEdges_partition (hHG : H ≤ S.G) (v : Fin n) :
    S.passEdges H v = S.passBelow H v ∪ S.passAbove H v ∧
    Disjoint (S.passBelow H v) (S.passAbove H v) := by
  classical
  constructor
  · ext e
    simp only [passBelow, passAbove, passEdges, orientEdges, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hadj⟩, h1, h2⟩
      rcases lt_or_gt_of_ne (S.edgeY_ne_vertex h1 h2 (hHG hadj)) with h | h
      · exact Or.inl ⟨⟨⟨h1.trans h2, hadj⟩, h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨⟨h1.trans h2, hadj⟩, h1, h2⟩, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [passBelow, passAbove, Finset.mem_filter] at h1 h2
    linarith

private lemma activeEdges_castSucc_eq (v : Fin n) :
    S.activeEdges H v.castSucc = S.passEdges H v ∪ S.leftEdges H v ∧
    Disjoint (S.passEdges H v) (S.leftEdges H v) := by
  classical
  constructor
  · ext e
    simp only [activeEdges, passEdges, leftEdges, orientEdges, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_castSucc, Fin.lt_def]
    constructor
    · rintro ⟨⟨hlt, hadj⟩, h1, h2⟩
      by_cases hev : e.2 = v
      · exact Or.inr ⟨⟨hlt, hadj⟩, hev⟩
      · left; refine ⟨⟨hlt, hadj⟩, h1, lt_of_le_of_ne h2 (fun h => hev (Fin.ext h.symm))⟩
    · rintro (⟨⟨hlt, hadj⟩, h1, h2⟩ | ⟨⟨hlt, hadj⟩, rfl⟩)
      · exact ⟨⟨hlt, hadj⟩, h1, h2.le⟩
      · exact ⟨⟨hlt, hadj⟩, hlt, le_rfl⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [passEdges, leftEdges, Finset.mem_filter] at h1 h2
    exact h1.2.2.ne h2.2.symm

private lemma activeEdges_succ_eq (v : Fin n) :
    S.activeEdges H v.succ = S.passEdges H v ∪ S.rightEdges H v ∧
    Disjoint (S.passEdges H v) (S.rightEdges H v) := by
  classical
  constructor
  · ext e
    simp only [activeEdges, passEdges, rightEdges, orientEdges, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_succ, Fin.lt_def]
    constructor
    · rintro ⟨⟨hlt, hadj⟩, h1, h2⟩
      by_cases hev : e.1 = v
      · exact Or.inr ⟨⟨hlt, hadj⟩, hev⟩
      · left; refine ⟨⟨hlt, hadj⟩, by omega, by omega⟩
    · rintro (⟨⟨hlt, hadj⟩, h1, h2⟩ | ⟨⟨hlt, hadj⟩, rfl⟩)
      · exact ⟨⟨hlt, hadj⟩, by omega, by omega⟩
      · exact ⟨⟨hlt, hadj⟩, by omega, by omega⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [passEdges, rightEdges, Finset.mem_filter] at h1 h2
    exact h1.2.1.ne h2.2

private lemma activeEdges_card_step (v : Fin n) :
    (S.activeEdges H v.castSucc).card + (S.rightEdges H v).card =
    (S.activeEdges H v.succ).card + (S.leftEdges H v).card := by
  have h1 := S.activeEdges_castSucc_eq H v
  have h2 := S.activeEdges_succ_eq H v
  have c1 : (S.activeEdges H v.castSucc).card = (S.passEdges H v).card + (S.leftEdges H v).card := by
    rw [h1.1, Finset.card_union_of_disjoint h1.2]
  have c2 : (S.activeEdges H v.succ).card = (S.passEdges H v).card + (S.rightEdges H v).card := by
    rw [h2.1, Finset.card_union_of_disjoint h2.2]
  omega

private lemma passBelow_add_left_le (hHG : H ≤ S.G) (v : Fin n) :
    (S.passBelow H v).card + (S.leftEdges H v).card ≤ (S.activeEdges H v.castSucc).card := by
  have h1 := S.activeEdges_castSucc_eq H v
  have hp := S.passEdges_partition H hHG v
  rw [h1.1, Finset.card_union_of_disjoint h1.2, hp.1, Finset.card_union_of_disjoint hp.2]
  omega

private lemma passBelow_add_right_le (hHG : H ≤ S.G) (v : Fin n) :
    (S.passBelow H v).card + (S.rightEdges H v).card ≤ (S.activeEdges H v.succ).card := by
  have h2 := S.activeEdges_succ_eq H v
  have hp := S.passEdges_partition H hHG v
  rw [h2.1, Finset.card_union_of_disjoint h2.2, hp.1, Finset.card_union_of_disjoint hp.2]
  omega

private lemma leftEdges_add_rightEdges_eq_degree (v : Fin n) :
    haveI := Classical.decRel H.Adj
    (S.leftEdges H v).card + (S.rightEdges H v).card = H.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hL : (S.leftEdges H v).card = ((H.neighborFinset v).filter (· < v)).card := by
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      simp only [leftEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨he.2 ▸ he.1.2.symm, he.2 ▸ he.1.1⟩
    · intro e₁ he₁ e₂ he₂ h
      simp only [leftEdges, Finset.mem_filter] at he₁ he₂
      exact Prod.ext h (he₁.2.trans he₂.2.symm)
    · intro u hu
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
      exact ⟨(u, v), by simp [leftEdges, orientEdges, hu.2, hu.1.symm], rfl⟩
  have hR : (S.rightEdges H v).card = ((H.neighborFinset v).filter (fun u => ¬ u < v)).card := by
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he
      simp only [rightEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨he.2 ▸ he.1.2, not_lt.mpr (he.2 ▸ he.1.1).le⟩
    · intro e₁ he₁ e₂ he₂ h
      simp only [rightEdges, Finset.mem_filter] at he₁ he₂
      exact Prod.ext (he₁.2.trans he₂.2.symm) h
    · intro u hu
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu
      have hvu : v < u := lt_of_le_of_ne (not_lt.mp hu.2) (H.ne_of_adj hu.1)
      exact ⟨(v, u), by simp [rightEdges, orientEdges, hvu, hu.1], rfl⟩
  rw [hL, hR, Finset.card_filter_add_card_filter_not]

private abbrev SlabVert : Type :=
  Σ i : Fin (n + 1), Fin ((S.activeEdges H i).card + 1)

private lemma slabVert_ext {i₁ i₂ : Fin (n + 1)} {r₁ : Fin ((S.activeEdges H i₁).card + 1)}
    {r₂ : Fin ((S.activeEdges H i₂).card + 1)} (hi : i₁ = i₂) (hr : r₁.val = r₂.val) :
    (⟨i₁, r₁⟩ : S.SlabVert H) = ⟨i₂, r₂⟩ := by
  subst hi; exact Sigma.ext rfl (heq_of_eq (Fin.ext hr))

private def slabGlueAcross (v : Fin n)
    (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1)) : Prop :=
  let p := (S.passBelow H v).card
  let dL := (S.leftEdges H v).card
  let dR := (S.rightEdges H v).card
  (r₁.val ≤ p ∧ r₂.val = r₁.val) ∨
  (p + dL ≤ r₁.val ∧ r₂.val + dL = r₁.val + dR)

private def slabGraph : SimpleGraph (S.SlabVert H) where
  Adj x y :=
    (∃ (v : Fin n) (h₁ : x.1 = v.castSucc) (h₂ : y.1 = v.succ),
      S.slabGlueAcross H v (h₁ ▸ x.2) (h₂ ▸ y.2)) ∨
    (∃ (v : Fin n) (h₁ : y.1 = v.castSucc) (h₂ : x.1 = v.succ),
      S.slabGlueAcross H v (h₁ ▸ y.2) (h₂ ▸ x.2))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨v, h1, h2, _⟩ | ⟨v, h1, h2, _⟩
    · have : v.castSucc = v.succ := h1.symm.trans h2
      have := congrArg Fin.val this; simp at this
    · have : v.castSucc = v.succ := h1.symm.trans h2
      have := congrArg Fin.val this; simp at this⟩

private lemma slabGraph_adj_step (v : Fin n)
    (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1))
    (h : S.slabGlueAcross H v r₁ r₂) :
    (S.slabGraph H).Adj ⟨v.castSucc, r₁⟩ ⟨v.succ, r₂⟩ :=
  Or.inl ⟨v, rfl, rfl, h⟩

private lemma slabGraph_adj_step_iff (v : Fin n)
    (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1)) :
    (S.slabGraph H).Adj ⟨v.castSucc, r₁⟩ ⟨v.succ, r₂⟩ ↔ S.slabGlueAcross H v r₁ r₂ := by
  constructor
  · rintro (⟨w, h1, h2, hg⟩ | ⟨w, h1, h2, _⟩)
    · have hvw : v = w := Fin.ext (by simpa using congrArg Fin.val h1)
      subst hvw; exact hg
    · have : v.val + 1 = w.val := by simpa using congrArg Fin.val h1
      have : v.val = w.val + 1 := by simpa using congrArg Fin.val h2
      omega
  · exact S.slabGraph_adj_step H v r₁ r₂

private noncomputable def slabInEdges (t : S.SlabVert H) : Finset (S.SlabVert H) := by
  classical
  exact Finset.univ.filter (fun s : S.SlabVert H => s.1.val + 1 = t.1.val ∧ (S.slabGraph H).Adj s t)

private lemma slabInEdges_zero (r : Fin ((S.activeEdges H 0).card + 1)) :
    (S.slabInEdges H ⟨0, r⟩).card = 0 := by
  classical
  unfold slabInEdges
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ ⟨h, _⟩
  simp at h

private lemma slabInEdges_succ_card (hHG : H ≤ S.G)
    (v : Fin n) (r : Fin ((S.activeEdges H v.succ).card + 1)) :
    let p := (S.passBelow H v).card
    let dL := (S.leftEdges H v).card
    let dR := (S.rightEdges H v).card
    (S.slabInEdges H ⟨v.succ, r⟩).card =
      if p < r.val ∧ r.val < p + dR then 0
      else if r.val = p ∧ dR = 0 ∧ 0 < dL then 2
      else 1 := by
  classical
  intro p dL dR
  have hstep := S.activeEdges_card_step H v
  have hpL := S.passBelow_add_left_le H hHG v
  have hpR := S.passBelow_add_right_le H hHG v

  have hmem : ∀ s : S.SlabVert H, s ∈ S.slabInEdges H ⟨v.succ, r⟩ ↔
      ∃ (hs : s.1 = v.castSucc), S.slabGlueAcross H v (hs ▸ s.2) r := by
    intro s
    simp only [slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ]
    constructor
    · rintro ⟨hval, hadj⟩
      have hs : s.1 = v.castSucc := Fin.ext (by simp; omega)
      refine ⟨hs, ?_⟩
      rcases s with ⟨i, r₁⟩
      dsimp at hs; subst hs
      exact (S.slabGraph_adj_step_iff H v r₁ r).mp hadj
    · rintro ⟨hs, hg⟩
      rcases s with ⟨i, r₁⟩
      dsimp at hs; subst hs
      exact ⟨rfl, S.slabGraph_adj_step H v r₁ r hg⟩
  split_ifs with htip hcap
  ·
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs_in
    obtain ⟨hs, hg⟩ := (hmem s).mp hs_in
    rcases s with ⟨i, r₁⟩; dsimp only at hs; subst hs; dsimp only at hg
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  ·
    have hdL : 0 < dL := hcap.2.2
    let s₁ : S.SlabVert H := ⟨v.castSucc, ⟨p, by omega⟩⟩
    let s₂ : S.SlabVert H := ⟨v.castSucc, ⟨p + dL, by omega⟩⟩
    have hne : s₁ ≠ s₂ := fun h => by
      have : p = p + dL := by
        have := congrArg (fun x : S.SlabVert H => x.2.val) h
        simpa [s₁, s₂] using this
      omega
    have heq : S.slabInEdges H ⟨v.succ, r⟩ = {s₁, s₂} := by
      ext s
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hs, hg⟩
        rcases s with ⟨i, r₁⟩
        dsimp only at hs; subst hs; dsimp only at hg
        rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact S.slabVert_ext H rfl (by dsimp [s₁]; omega)
        · right; exact S.slabVert_ext H rfl (by dsimp [s₂]; omega)
      · rintro (rfl | rfl)
        · exact ⟨rfl, Or.inl ⟨le_rfl, hcap.1⟩⟩
        · exact ⟨rfl, Or.inr ⟨le_rfl, by dsimp [s₂]; omega⟩⟩
    rw [heq, Finset.card_pair hne]
  ·
    by_cases hle : r.val ≤ p
    ·
      let s₁ : S.SlabVert H := ⟨v.castSucc, ⟨r.val, by omega⟩⟩
      have heq : S.slabInEdges H ⟨v.succ, r⟩ = {s₁} := by
        ext s
        rw [hmem, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, hg⟩
          rcases s with ⟨i, r₁⟩
          dsimp only at hs; subst hs; dsimp only at hg
          rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact S.slabVert_ext H rfl (by dsimp [s₁]; omega)
          · exact S.slabVert_ext H rfl (by dsimp [s₁]; omega)
        · rintro rfl
          exact ⟨rfl, Or.inl ⟨hle, rfl⟩⟩
      rw [heq, Finset.card_singleton]
    ·
      have hge : p + dR ≤ r.val := by omega
      let s₂ : S.SlabVert H := ⟨v.castSucc, ⟨r.val - dR + dL, by omega⟩⟩
      have heq : S.slabInEdges H ⟨v.succ, r⟩ = {s₂} := by
        ext s
        rw [hmem, Finset.mem_singleton]
        constructor
        · rintro ⟨hs, hg⟩
          rcases s with ⟨i, r₁⟩
          dsimp only at hs; subst hs; dsimp only at hg
          rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exfalso; omega
          · exact S.slabVert_ext H rfl (by dsimp [s₂]; omega)
        · rintro rfl
          exact ⟨rfl, Or.inr ⟨by dsimp [s₂]; omega, by dsimp [s₂]; omega⟩⟩
      rw [heq, Finset.card_singleton]

private lemma sum_slabInEdges_eq_edges :
    haveI := Classical.decRel (S.slabGraph H).Adj
    ∑ t : S.SlabVert H, (S.slabInEdges H t).card = (S.slabGraph H).edgeFinset.card := by
  classical

  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => s(p.2, p.1)) ?_ ?_ ?_
  · intro ⟨t, s⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter] at hp
    exact (S.slabGraph H).mem_edgeFinset.mpr hp.2
  · intro ⟨t₁, s₁⟩ h1 ⟨t₂, s₂⟩ h2 heq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter] at h1 h2
    rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · dsimp only at hs ht; exact Sigma.ext ht (heq_of_eq hs)
    · exfalso
      dsimp only at hs ht
      have hval1 := h1.1
      have hval2 := h2.1
      rw [hs, ht] at hval1
      omega
  · intro e he
    induction e using Sym2.ind with | _ x y =>
    have hadj : (S.slabGraph H).Adj x y := (S.slabGraph H).mem_edgeFinset.mp he
    rcases hadj with ⟨v, h1, h2, hg⟩ | ⟨v, h1, h2, hg⟩
    · refine ⟨⟨y, x⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter]
      exact ⟨by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩
    · refine ⟨⟨x, y⟩, ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slabInEdges, Finset.mem_filter]
      exact ⟨by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩

private lemma slab_vert_sub_edge_active (hHG : H ≤ S.G) :
    haveI := Classical.decRel (S.slabGraph H).Adj
    (Fintype.card (S.SlabVert H) : ℤ) - ((S.slabGraph H).edgeFinset.card : ℤ) =
      ((S.orientEdges H).card : ℤ) -
        ((Finset.univ.filter fun v => 0 < (S.leftEdges H v).card + (S.rightEdges H v).card).card : ℤ) + 1 := by
  classical

  rw [← S.sum_slabInEdges_eq_edges H, Fintype.card_sigma]
  rw [Fin.sum_univ_succ (f := fun i : Fin (n + 1) => Fintype.card (Fin ((S.activeEdges H i).card + 1)))]
  rw [Fintype.sum_sigma, Fin.sum_univ_succ (f := fun i : Fin (n + 1) => ∑ r : Fin ((S.activeEdges H i).card + 1), (S.slabInEdges H ⟨i, r⟩).card)]
  have h0_v : Fintype.card (Fin ((S.activeEdges H 0).card + 1)) = 1 := by
    rw [Fintype.card_fin, S.activeEdges_zero, Finset.card_empty]
  have h0_e : ∑ r : Fin ((S.activeEdges H 0).card + 1), (S.slabInEdges H ⟨0, r⟩).card = 0 := by
    simp [S.slabInEdges_zero]
  rw [h0_v, h0_e]

  have hstep_sum : ∀ v : Fin n,
      ((Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) : ℤ) -
        ((∑ r : Fin ((S.activeEdges H v.succ).card + 1), (S.slabInEdges H ⟨v.succ, r⟩).card : ℕ) : ℤ)) =
      ((S.rightEdges H v).card : ℤ) -
        (if 0 < (S.leftEdges H v).card + (S.rightEdges H v).card then 1 else 0) := by
    intro v
    have hcard : Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) =
        (S.activeEdges H v.succ).card + 1 := Fintype.card_fin _
    rw [hcard]
    push_cast
    rw [show ((S.activeEdges H v.succ).card : ℤ) + 1 =
        ∑ _ : Fin ((S.activeEdges H v.succ).card + 1), (1 : ℤ) by simp]
    rw [← Finset.sum_sub_distrib]
    set p := (S.passBelow H v).card
    set dL := (S.leftEdges H v).card
    set dR := (S.rightEdges H v).card
    have hpR := S.passBelow_add_right_le H hHG v
    have hterm : ∀ r : Fin ((S.activeEdges H v.succ).card + 1),
        (1 : ℤ) - ((S.slabInEdges H ⟨v.succ, r⟩).card : ℤ) =
          (if p < r.val ∧ r.val < p + dR then (1 : ℤ) else 0) -
          (if r.val = p ∧ dR = 0 ∧ 0 < dL then (1 : ℤ) else 0) := by
      intro r
      rw [S.slabInEdges_succ_card H hHG v r]
      split_ifs with h1 h2 <;> omega
    simp_rw [hterm, Finset.sum_sub_distrib]
    by_cases hdR : dR = 0
    · have h1 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if p < r.val ∧ r.val < p + dR then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro r _; rw [if_neg (by omega)]
      have h2 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if r.val = p ∧ dR = 0 ∧ 0 < dL then (1 : ℤ) else 0) =
            (if 0 < dL then 1 else 0) := by
        by_cases hdL : 0 < dL
        · have hp_lt : p < (S.activeEdges H v.succ).card + 1 := by omega
          have heq : ∀ r : Fin ((S.activeEdges H v.succ).card + 1),
              (r.val = p ∧ dR = 0 ∧ 0 < dL) ↔ r = ⟨p, hp_lt⟩ := by
            intro r; simp [hdR, hdL, Fin.ext_iff]
          simp_rw [heq]; simp [hdL]
        · simp [hdL]
      rw [h1, h2, hdR, add_zero, Int.natCast_zero, zero_sub]
    · have h2 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if r.val = p ∧ dR = 0 ∧ 0 < dL then (1 : ℤ) else 0) = 0 := by
        simp [hdR]
      have h1 : ∑ r : Fin ((S.activeEdges H v.succ).card + 1),
          (if p < r.val ∧ r.val < p + dR then (1 : ℤ) else 0) = (dR : ℤ) - 1 := by
        rw [Finset.sum_boole]
        have hcnt : (Finset.univ.filter (fun r : Fin ((S.activeEdges H v.succ).card + 1) =>
            p < r.val ∧ r.val < p + dR)).card = dR - 1 := by
          have : (Finset.univ.filter (fun r : Fin ((S.activeEdges H v.succ).card + 1) =>
              p < r.val ∧ r.val < p + dR)).card = (Finset.Ioo p (p + dR)).card := by
            refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
            · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
              exact Finset.mem_Ioo.mpr hr
            · intro r₁ _ r₂ _ h; exact Fin.ext h
            · intro k hk
              rw [Finset.mem_Ioo] at hk
              exact ⟨⟨k, by omega⟩, by simp [hk.1, hk.2], rfl⟩
          rw [this, Nat.card_Ioo]; omega
        rw [hcnt]
        have : 1 ≤ dR := Nat.one_le_iff_ne_zero.mpr hdR
        push_cast [Nat.cast_sub this]; rfl
      rw [h1, h2, if_pos (show 0 < dL + dR by omega), sub_zero]
  have hsumR : ∑ v : Fin n, (S.rightEdges H v).card = (S.orientEdges H).card := by
    have hpart : S.orientEdges H = Finset.univ.biUnion (fun v : Fin n => S.rightEdges H v) := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, rightEdges, Finset.mem_filter]
      exact ⟨fun h => ⟨e.1, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
    rw [hpart, Finset.card_biUnion]
    intro v₁ _ v₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [rightEdges, Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  push_cast
  have hdiff :
      (1 + ∑ v : Fin n, (Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) : ℤ)) -
      (0 + ∑ v : Fin n, ∑ r : Fin ((S.activeEdges H v.succ).card + 1), ((S.slabInEdges H ⟨v.succ, r⟩).card : ℤ)) =
      1 + ∑ v : Fin n, ((Fintype.card (Fin ((S.activeEdges H v.succ).card + 1)) : ℤ) -
        ((∑ r : Fin ((S.activeEdges H v.succ).card + 1), (S.slabInEdges H ⟨v.succ, r⟩).card : ℕ) : ℤ)) := by
    push_cast; rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  simp_rw [hstep_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_boole]
  have hRcast : (∑ v : Fin n, ((S.rightEdges H v).card : ℤ)) = ((S.orientEdges H).card : ℤ) := by
    exact_mod_cast hsumR
  rw [hRcast]; ring

private lemma slab_vert_sub_edge (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    haveI := Classical.decRel (S.slabGraph H).Adj
    (Fintype.card (S.SlabVert H) : ℤ) - ((S.slabGraph H).edgeFinset.card : ℤ) =
      ((S.orientEdges H).card : ℤ) - (n : ℤ) + 1 := by
  classical
  simpa [show ∀ v : Fin n, 0 < (S.leftEdges H v).card + (S.rightEdges H v).card from hdeg]
    using S.slab_vert_sub_edge_active H hHG

private def outerVert : S.SlabVert H := ⟨0, ⟨0, Nat.succ_pos _⟩⟩

private lemma slab_outer_cycle_at (hHG : H ≤ S.G) (v : Fin n)
    (hL : (S.activeEdges H v.castSucc).card = 0)
    (hR : 0 < (S.activeEdges H v.succ).card) :
    haveI := Classical.decRel (S.slabGraph H).Adj
    let u : S.SlabVert H := ⟨v.castSucc, Fin.last _⟩
    let w : S.SlabVert H := ⟨v.succ, Fin.last _⟩
    (S.slabGraph H).Reachable (S.outerVert H) u ∧
    (S.slabGraph H).Reachable (S.outerVert H) w ∧
    (S.slabGraph H).Adj u w ∧
    ((S.slabGraph H).deleteEdges {s(u, w)}).Reachable u w := by
  classical
  intro u w
  let G' := (S.slabGraph H).deleteEdges {s(u, w)}
  let bot (i : Fin (n + 1)) : S.SlabVert H := ⟨i, ⟨0, Nat.succ_pos _⟩⟩
  let top (i : Fin (n + 1)) : S.SlabVert H := ⟨i, Fin.last _⟩
  have htop_adj (k : Fin n) : (S.slabGraph H).Adj (top k.castSucc) (top k.succ) := by
    apply S.slabGraph_adj_step H k
    right
    have hstep := S.activeEdges_card_step H k
    have hpL := S.passBelow_add_left_le H hHG k
    simp only [Fin.val_last]
    omega
  have hbot : ∀ k : ℕ, (hk : k ≤ n) →
      G'.Reachable (S.outerVert H) (bot ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      intro hk
      let vk : Fin n := ⟨k, by omega⟩
      have hadj : (S.slabGraph H).Adj (bot vk.castSucc) (bot vk.succ) := by
        apply S.slabGraph_adj_step H vk
        left
        exact ⟨Nat.zero_le _, rfl⟩
      have hne : s(bot vk.castSucc, bot vk.succ) ≠ s(u, w) := by
        intro he
        rcases Sym2.eq_iff.mp he with ⟨_, he⟩ | ⟨he, _⟩
        all_goals
          have hr := congrArg (fun x : S.SlabVert H => x.2.val) he
          change (0 : ℕ) = (S.activeEdges H v.succ).card at hr
          omega
      have hs : G'.Adj (bot vk.castSucc) (bot vk.succ) :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hadj, fun he => hne (Set.mem_singleton_iff.mp he)⟩
      exact (ih (by omega)).trans hs.reachable
  have htop : ∀ d : ℕ, (hd : d ≤ n - v.succ.val) →
      G'.Reachable (top ⟨n - d, by omega⟩) (top (Fin.last n)) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hi : (⟨n - 0, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
      rw [hi]
    | succ d ih =>
      intro hd
      let vk : Fin n := ⟨n - (d + 1), by omega⟩
      have hv : v.val + 1 ≤ n - (d + 1) := by
        have hvn := v.isLt
        change d + 1 ≤ n - (v.val + 1) at hd
        omega
      have hne : s(top vk.castSucc, top vk.succ) ≠ s(u, w) := by
        intro he
        rcases Sym2.eq_iff.mp he with ⟨he, _⟩ | ⟨_, he⟩
        · have hi := congrArg (fun x : S.SlabVert H => x.1.val) he
          change n - (d + 1) = v.val at hi
          omega
        · have hi := congrArg (fun x : S.SlabVert H => x.1.val) he
          change n - (d + 1) + 1 = v.val at hi
          omega
      have hs : G'.Adj (top vk.castSucc) (top vk.succ) :=
        SimpleGraph.deleteEdges_adj.mpr
          ⟨htop_adj vk, fun he => hne (Set.mem_singleton_iff.mp he)⟩
      have hi : vk.succ = (⟨n - d, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        change n - (d + 1) + 1 = n - d
        omega
      rw [hi] at hs
      exact hs.reachable.trans (ih (by omega))
  have hu : bot v.castSucc = u := S.slabVert_ext H rfl (by simpa only [Fin.val_last] using hL.symm)
  have hlast : bot (Fin.last n) = top (Fin.last n) :=
    S.slabVert_ext H rfl (by simp [Fin.val_last, S.activeEdges_last])
  have hu' : G'.Reachable (S.outerVert H) u := by
    rw [← hu]
    exact hbot v.val (Nat.le_of_lt v.isLt)
  have hw' : G'.Reachable (S.outerVert H) w := by
    have h1 : G'.Reachable (S.outerVert H) (bot (Fin.last n)) := hbot n le_rfl
    rw [hlast] at h1
    have h2 := htop (n - v.succ.val) le_rfl
    have hi : (⟨n - (n - v.succ.val), by omega⟩ : Fin (n + 1)) = v.succ := by
      have hvn := v.succ.isLt
      apply Fin.ext
      change n - (n - v.succ.val) = v.succ.val
      omega
    rw [hi] at h2
    exact h1.trans h2.symm
  have lift (x : S.SlabVert H) (hx : G'.Reachable (S.outerVert H) x) :
      (S.slabGraph H).Reachable (S.outerVert H) x := by
    obtain ⟨p⟩ := hx
    exact (p.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))).reachable
  exact ⟨lift u hu', lift w hw', htop_adj v, hu'.symm.trans hw'⟩

private lemma slab_exists_active_start (he : ∃ a b, H.Adj a b) :
    ∃ v : Fin n, (S.activeEdges H v.castSucc).card = 0 ∧
      0 < (S.activeEdges H v.succ).card := by
  classical
  have hex : ∃ k : ℕ, ∃ e ∈ S.orientEdges H, e.1.val = k := by
    obtain ⟨a, b, hab⟩ := he
    rcases lt_or_gt_of_ne (H.ne_of_adj hab) with h | h
    · exact ⟨a.val, (a, b), by simp [orientEdges, h, hab], rfl⟩
    · exact ⟨b.val, (b, a), by simp [orientEdges, h, hab.symm], rfl⟩
  obtain ⟨e, he, hmin⟩ := Nat.find_spec hex
  refine ⟨e.1, ?_, ?_⟩
  · unfold activeEdges
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f hf hactive
    have hv : f.1.val < e.1.val := hactive.1
    have hlt : f.1.val < Nat.find hex := by omega
    exact Nat.find_min hex hlt ⟨f, hf, rfl⟩
  · apply Finset.card_pos.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    have h := he
    simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hlt : e.1.val < e.2.val := h.1
    change e.1.val < e.1.val + 1 ∧ e.1.val + 1 ≤ e.2.val
    omega

private lemma slab_outer_cycle_of_edge (hHG : H ≤ S.G) (he : ∃ a b, H.Adj a b) :
    haveI := Classical.decRel (S.slabGraph H).Adj
    ∃ v : Fin n,
      let u : S.SlabVert H := ⟨v.castSucc, Fin.last _⟩
      let w : S.SlabVert H := ⟨v.succ, Fin.last _⟩
      (S.slabGraph H).Reachable (S.outerVert H) u ∧
      (S.slabGraph H).Reachable (S.outerVert H) w ∧
      (S.slabGraph H).Adj u w ∧
      ((S.slabGraph H).deleteEdges {s(u, w)}).Reachable u w := by
  classical
  obtain ⟨v, hL, hR⟩ := S.slab_exists_active_start H he
  exact ⟨v, S.slab_outer_cycle_at H hHG v hL hR⟩

private lemma exists_edge_of_slab_degree
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    ∃ a b, H.Adj a b := by
  classical
  let v : Fin n := ⟨0, by have := S.hn; omega⟩
  have h := hdeg v
  rw [S.leftEdges_add_rightEdges_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree] at h
  obtain ⟨w, hw⟩ := Finset.card_pos.mp h
  exact ⟨v, w, (H.mem_neighborFinset _ _).mp hw⟩

private lemma slab_components_ge (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    (S.orientEdges H).card + 2 ≤ Nat.card (S.slabGraph H).ConnectedComponent + n := by
  classical
  have hve := S.slab_vert_sub_edge H hHG hdeg
  obtain ⟨_, _, _, hadj, hreach⟩ :=
    S.slab_outer_cycle_of_edge H hHG (S.exists_edge_of_slab_degree H hdeg)
  have := card_le_edges_add_components_of_cycle_edge (S.slabGraph H) hadj hreach
  omega

private lemma slab_outer_component_V_le_E (hHG : H ≤ S.G) (he : ∃ a b, H.Adj a b) :
    let F_out : Finset (S.SlabVert H) := by
      classical
      exact Finset.univ.filter (fun t => (S.slabGraph H).Reachable (S.outerVert H) t)
    F_out.card ≤ ∑ t ∈ F_out, (S.slabInEdges H t).card := by
  classical
  intro F_out
  let G := S.slabGraph H
  let C := G.connectedComponentMk (S.outerVert H)
  let Gout := C.toSimpleGraph
  have hC (t : S.SlabVert H) : t ∈ C.supp ↔ G.Reachable (S.outerVert H) t := by
    simp [C, SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
  obtain ⟨v, hu, hw, hadj, hreach⟩ := S.slab_outer_cycle_of_edge H hHG he
  let u : C := ⟨⟨v.castSucc, Fin.last _⟩, (hC _).2 hu⟩
  let w : C := ⟨⟨v.succ, Fin.last _⟩, (hC _).2 hw⟩
  let D := G.deleteEdges {s(u.1, w.1)}
  let K := D.connectedComponentMk u.1
  have hsub : K.supp ⊆ C.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp
      (SimpleGraph.deleteEdges_le _) C u.2
  let f : K.toSimpleGraph →g Gout.deleteEdges {s(u, w)} :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_rel' := fun {x y} h => by
        have h' : D.Adj x.1 y.1 := h
        obtain ⟨hxy, hne⟩ := SimpleGraph.deleteEdges_adj.mp h'
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun hm => hne ?_⟩
        exact Set.mem_singleton_iff.mpr
          (congrArg (Sym2.map (fun z : C => z.1)) (Set.mem_singleton_iff.mp hm)) }
  have hreach_del : (Gout.deleteEdges {s(u, w)}).Reachable u w := by
    have hwu : w.1 ∈ K.supp := SimpleGraph.ConnectedComponent.sound hreach.symm
    exact (K.reachable_toSimpleGraph (hu := (show u.1 ∈ K.supp from rfl)) (hv := hwu)).map f
  have hbound := card_le_edges_add_components_of_cycle_edge Gout (show Gout.Adj u w from hadj) hreach_del
  rw [connected_natCard_components C.connected_toSimpleGraph] at hbound
  have hcardW : Fintype.card C = F_out.card := by
    have hm (t : S.SlabVert H) : t ∈ C ↔ t ∈ F_out := by
      change t ∈ C.supp ↔ t ∈ F_out
      simpa only [F_out, Finset.mem_filter, Finset.mem_univ, true_and] using hC t
    simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.subtypeEquivRight hm)
  have hedgesW : Gout.edgeFinset.card = ∑ t ∈ F_out, (S.slabInEdges H t).card := by
    rw [← Finset.card_sigma]
    symm
    refine Finset.card_bij
      (fun p hp => s(⟨p.2, (hC _).2 (by
        have h1 := (Finset.mem_sigma.mp hp).1
        have h2 := (Finset.mem_sigma.mp hp).2
        simp only [F_out, slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h1.trans h2.2.symm.reachable)⟩,
        ⟨p.1, (hC _).2 (by simpa [F_out] using (Finset.mem_sigma.mp hp).1)⟩)) ?_ ?_ ?_
    · intro ⟨t, s⟩ hp
      have h2 := (Finset.mem_sigma.mp hp).2
      simp only [slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h2
      exact Gout.mem_edgeFinset.mpr h2.2
    · intro ⟨t₁, s₁⟩ h1 ⟨t₂, s₂⟩ h2 heq
      have h1' := (Finset.mem_sigma.mp h1).2
      have h2' := (Finset.mem_sigma.mp h2).2
      simp only [slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h1' h2'
      rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Sigma.ext (congrArg Subtype.val ht) (heq_of_eq (congrArg Subtype.val hs))
      · have hv1 := h1'.1; have hv2 := h2'.1
        have hs' : s₁ = t₂ := congrArg Subtype.val hs
        have ht' : t₁ = s₂ := congrArg Subtype.val ht
        rw [hs', ht'] at hv1; omega
    · intro e he
      induction e using Sym2.ind with | _ x y =>
      have hadj' : (S.slabGraph H).Adj x.1 y.1 := Gout.mem_edgeFinset.mp he
      rcases hadj' with ⟨v, h1, h2, hg⟩ | ⟨v, h1, h2, hg⟩
      · refine ⟨⟨y.1, x.1⟩, ?_, by simp⟩
        simp only [Finset.mem_sigma, F_out, slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(hC _).1 y.2, by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩
      · refine ⟨⟨x.1, y.1⟩, ?_, by simp [Sym2.eq_swap]⟩
        simp only [Finset.mem_sigma, F_out, slabInEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(hC _).1 x.2, by rw [h1, h2]; simp, Or.inl ⟨v, h1, h2, hg⟩⟩
  omega

private noncomputable def edgeRank (i : Fin (n + 1)) (e : Fin n × Fin n) : ℕ := by
  classical
  exact ((S.activeEdges H i).filter (fun e' =>
    edgeY S.p e'.1 e'.2 (S.slabMid i) < edgeY S.p e.1 e.2 (S.slabMid i))).card

private lemma edgeRank_lt {i : Fin (n + 1)} {e : Fin n × Fin n} (he : e ∈ S.activeEdges H i) :
    S.edgeRank H i e < (S.activeEdges H i).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have : e ∈ (S.activeEdges H i).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid i) < edgeY S.p e.1 e.2 (S.slabMid i)) := by rw [h]; exact he
  simp only [Finset.mem_filter] at this
  exact lt_irrefl _ this.2

private lemma edgeRank_passBelow (hHG : H ≤ S.G) {v : Fin n} {e : Fin n × Fin n} (he : e ∈ S.passBelow H v) :
    S.edgeRank H v.castSucc e < (S.passBelow H v).card ∧
    S.edgeRank H v.succ e = S.edgeRank H v.castSucc e := by
  classical
  have hpe : e ∈ S.passEdges H v := (Finset.mem_filter.mp he).1
  have he_lt : edgeY S.p e.1 e.2 (S.p v).re < (S.p v).im := (Finset.mem_filter.mp he).2
  have hpe' := Finset.mem_filter.mp hpe
  have he_or := Finset.mem_filter.mp hpe'.1
  have he_ac1 : e ∈ S.activeEdges H v.castSucc := by
    rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hpe
  have he_ac2 : e ∈ S.activeEdges H v.succ := by
    rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hpe
  have hmid1 := S.slabMid_between H he_ac1
  have hmid2 := S.slabMid_between H he_ac2
  have hmid1_lt_v : S.slabMid v.castSucc < (S.p v).re :=
    S.slabMid_castSucc_lt (by have := hpe'.2.1; omega)
  have hv_lt_mid2 : (S.p v).re < S.slabMid v.succ :=
    S.lt_slabMid_succ (by have := hpe'.2.2; omega)

  have hfilt1 : (S.activeEdges H v.castSucc).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) =
      (S.passBelow H v).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid1' := S.slabMid_between H he'ac
      rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'L
      · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at he'p
        rcases he'p with he'b | he'a
        · exact ⟨he'b, hlt⟩
        · exfalso
          have ha_gt := (Finset.mem_filter.mp he'a).2
          have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp he'a).1
          have ho' := Finset.mem_filter.mp hp'.1
          have hne : e' ≠ e := fun h => by rw [h] at ha_gt; linarith
          have := S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
            hmid1'.1 hmid1'.2 hmid1.1 hmid1.2
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt
          linarith
      · exfalso
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have huv : e'.1 < v := hL'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj e'.1 v := hL'.2 ▸ hHG ho'.2.2
        have hlt_inc := (S.edgeY_lt_incident_left hpe'.2.1 hpe'.2.2 huv (hHG he_or.2.2) hadj'
          hmid1.1 hmid1'.1 hmid1_lt_v).mpr he_lt
        rw [hL'.2] at hlt
        linarith
    · rintro ⟨he'b, hlt⟩
      refine ⟨?_, hlt⟩
      rw [(S.activeEdges_castSucc_eq H v).1]
      exact Finset.mem_union_left _ (Finset.mem_filter.mp he'b).1
  have hfilt2 : (S.activeEdges H v.succ).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.succ) < edgeY S.p e.1 e.2 (S.slabMid v.succ)) =
      (S.passBelow H v).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid2' := S.slabMid_between H he'ac
      rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'R
      · have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
        have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid1' := S.slabMid_between H he'ac1
        have hlt_v := S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt
        have hlt_1 := S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2
          hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hlt
        exact ⟨Finset.mem_filter.mpr ⟨he'p, hlt_v.trans he_lt⟩, hlt_1⟩
      · exfalso
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hvw : v < e'.2 := hR'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj v e'.2 := hR'.2 ▸ hHG ho'.2.2
        have hlt_inc := (S.edgeY_lt_incident_right hpe'.2.1 hpe'.2.2 hvw (hHG he_or.2.2) hadj'
          hv_lt_mid2 hmid2.2 hmid2'.2).mpr he_lt
        rw [hR'.2] at hlt
        linarith
    · rintro ⟨he'b, hlt⟩
      have he'p := (Finset.mem_filter.mp he'b).1
      have hp' := Finset.mem_filter.mp he'p
      have ho' := Finset.mem_filter.mp hp'.1
      have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
        rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
      have he'ac2 : e' ∈ S.activeEdges H v.succ := by
        rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
      have hmid1' := S.slabMid_between H he'ac1
      have hmid2' := S.slabMid_between H he'ac2
      have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      exact ⟨he'ac2, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
        hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hmid2'.1 hmid2'.2 hmid2.1 hmid2.2 hlt⟩
  constructor
  · unfold edgeRank
    rw [hfilt1]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have : e ∈ (S.passBelow H v).filter (fun e' =>
        edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) := by
      rw [h]; exact he
    exact lt_irrefl _ (Finset.mem_filter.mp this).2
  · unfold edgeRank; rw [hfilt1, hfilt2]

private lemma edgeRank_passAbove (hHG : H ≤ S.G) {v : Fin n} {e : Fin n × Fin n} (he : e ∈ S.passAbove H v) :
    (S.passBelow H v).card + (S.leftEdges H v).card ≤ S.edgeRank H v.castSucc e ∧
    S.edgeRank H v.succ e + (S.leftEdges H v).card =
      S.edgeRank H v.castSucc e + (S.rightEdges H v).card := by
  classical
  have hpe : e ∈ S.passEdges H v := (Finset.mem_filter.mp he).1
  have he_gt : (S.p v).im < edgeY S.p e.1 e.2 (S.p v).re := (Finset.mem_filter.mp he).2
  have hpe' := Finset.mem_filter.mp hpe
  have he_or := Finset.mem_filter.mp hpe'.1
  have he_ac1 : e ∈ S.activeEdges H v.castSucc := by
    rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ hpe
  have he_ac2 : e ∈ S.activeEdges H v.succ := by
    rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ hpe
  have hmid1 := S.slabMid_between H he_ac1
  have hmid2 := S.slabMid_between H he_ac2
  have hmid1_lt_v : S.slabMid v.castSucc < (S.p v).re :=
    S.slabMid_castSucc_lt (by have := hpe'.2.1; omega)
  have hv_lt_mid2 : (S.p v).re < S.slabMid v.succ :=
    S.lt_slabMid_succ (by have := hpe'.2.2; omega)
  let Q := (S.passAbove H v).filter (fun e' =>
    edgeY S.p e'.1 e'.2 (S.p v).re < edgeY S.p e.1 e.2 (S.p v).re)
  have hfilt1 : (S.activeEdges H v.castSucc).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p e.1 e.2 (S.slabMid v.castSucc)) =
      (S.passBelow H v ∪ S.leftEdges H v) ∪ Q := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union, Q]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid1' := S.slabMid_between H he'ac
      rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'L
      · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at he'p
        rcases he'p with he'b | he'a
        · exact Or.inl (Or.inl he'b)
        · right
          have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp he'a).1
          have ho' := Finset.mem_filter.mp hp'.1
          have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          exact ⟨he'a, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
            hmid1'.1 hmid1'.2 hmid1.1 hmid1.2
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt⟩
      · exact Or.inl (Or.inr he'L)
    · rintro ((he'b | he'L) | ⟨he'a, hltv⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid1' := S.slabMid_between H he'ac1
        have hltv : edgeY S.p e'.1 e'.2 (S.p v).re < edgeY S.p e.1 e.2 (S.p v).re :=
          (Finset.mem_filter.mp he'b).2.trans he_gt
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac1, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hltv⟩
      · have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_right _ he'L
        have hmid1' := S.slabMid_between H he'ac1
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have huv : e'.1 < v := hL'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj e'.1 v := hL'.2 ▸ hHG ho'.2.2
        have hnot := (S.edgeY_lt_incident_left hpe'.2.1 hpe'.2.2 huv (hHG he_or.2.2) hadj'
          hmid1.1 hmid1'.1 hmid1_lt_v).not.mpr (not_lt.mpr he_gt.le)
        have hne_y := S.edgeY_ne_of_ne_edges he_or.2.1 huv (hHG he_or.2.2) hadj'
          (fun h => hpe'.2.2.ne (congrArg Prod.snd h).symm)
          hmid1.1 hmid1.2 hmid1'.1 hmid1_lt_v
        rw [hL'.2]
        exact ⟨he'ac1, lt_of_le_of_ne (not_lt.mp hnot) hne_y.symm⟩
      · have he'p := (Finset.mem_filter.mp he'a).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac1 : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid1' := S.slabMid_between H he'ac1
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac1, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid1'.1 hmid1'.2 hmid1.1 hmid1.2 hltv⟩
  have hfilt2 : (S.activeEdges H v.succ).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.succ) < edgeY S.p e.1 e.2 (S.slabMid v.succ)) =
      (S.passBelow H v ∪ S.rightEdges H v) ∪ Q := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union, Q]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid2' := S.slabMid_between H he'ac
      rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'R
      · rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at he'p
        rcases he'p with he'b | he'a
        · exact Or.inl (Or.inl he'b)
        · right
          have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp he'a).1
          have ho' := Finset.mem_filter.mp hp'.1
          have hne : e' ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          exact ⟨he'a, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
            hmid2'.1 hmid2'.2 hmid2.1 hmid2.2
            (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2) hlt⟩
      · exact Or.inl (Or.inr he'R)
    · rintro ((he'b | he'R) | ⟨he'a, hltv⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac2 : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid2' := S.slabMid_between H he'ac2
        have hltv : edgeY S.p e'.1 e'.2 (S.p v).re < edgeY S.p e.1 e.2 (S.p v).re :=
          (Finset.mem_filter.mp he'b).2.trans he_gt
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac2, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2 hltv⟩
      · have he'ac2 : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_right _ he'R
        have hmid2' := S.slabMid_between H he'ac2
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hvw : v < e'.2 := hR'.2 ▸ ho'.2.1
        have hadj' : S.G.Adj v e'.2 := hR'.2 ▸ hHG ho'.2.2
        have hnot := (S.edgeY_lt_incident_right hpe'.2.1 hpe'.2.2 hvw (hHG he_or.2.2) hadj'
          hv_lt_mid2 hmid2.2 hmid2'.2).not.mpr (not_lt.mpr he_gt.le)
        have hne_y := S.edgeY_ne_of_ne_edges he_or.2.1 hvw (hHG he_or.2.2) hadj'
          (fun h => hpe'.2.1.ne (congrArg Prod.fst h))
          hmid2.1 hmid2.2 hv_lt_mid2 hmid2'.2
        rw [hR'.2]
        exact ⟨he'ac2, lt_of_le_of_ne (not_lt.mp hnot) hne_y.symm⟩
      · have he'p := (Finset.mem_filter.mp he'a).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac2 : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid2' := S.slabMid_between H he'ac2
        have hne : e' ≠ e := fun h => by rw [h] at hltv; exact lt_irrefl _ hltv
        exact ⟨he'ac2, S.edgeY_order_preserved ho'.2.1 he_or.2.1 (hHG ho'.2.2) (hHG he_or.2.2) hne
          (S.hx_mono hp'.2.1) (S.hx_mono hp'.2.2) (S.hx_mono hpe'.2.1) (S.hx_mono hpe'.2.2)
          hmid2'.1 hmid2'.2 hmid2.1 hmid2.2 hltv⟩
  have hdisj1 : Disjoint (S.passBelow H v) (S.leftEdges H v) :=
    Disjoint.mono_left (Finset.filter_subset _ _) (S.activeEdges_castSucc_eq H v).2
  have hdisj2 : Disjoint (S.passBelow H v) (S.rightEdges H v) :=
    Disjoint.mono_left (Finset.filter_subset _ _) (S.activeEdges_succ_eq H v).2
  have hdisjQ1 : Disjoint (S.passBelow H v ∪ S.leftEdges H v) Q := by
    rw [Finset.disjoint_union_left]
    exact ⟨Disjoint.mono_right (Finset.filter_subset _ _) (S.passEdges_partition H hHG v).2,
      Disjoint.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        (S.activeEdges_castSucc_eq H v).2.symm⟩
  have hdisjQ2 : Disjoint (S.passBelow H v ∪ S.rightEdges H v) Q := by
    rw [Finset.disjoint_union_left]
    exact ⟨Disjoint.mono_right (Finset.filter_subset _ _) (S.passEdges_partition H hHG v).2,
      Disjoint.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        (S.activeEdges_succ_eq H v).2.symm⟩
  have hc1 : S.edgeRank H v.castSucc e = (S.passBelow H v).card + (S.leftEdges H v).card + Q.card := by
    unfold edgeRank
    rw [hfilt1, Finset.card_union_of_disjoint hdisjQ1, Finset.card_union_of_disjoint hdisj1]
  have hc2 : S.edgeRank H v.succ e = (S.passBelow H v).card + (S.rightEdges H v).card + Q.card := by
    unfold edgeRank
    rw [hfilt2, Finset.card_union_of_disjoint hdisjQ2, Finset.card_union_of_disjoint hdisj2]
  omega

private lemma edgeRank_rightEdge (hHG : H ≤ S.G) {v w : Fin n} (hvw : v < w) (hadj : H.Adj v w) :
    S.edgeRank H v.succ (v, w) =
      (S.passBelow H v).card +
      ((S.rightEdges H v).filter (fun e' =>
        heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v))).card := by
  classical
  have hmem : (v, w) ∈ S.activeEdges H v.succ := by
    rw [(S.activeEdges_succ_eq H v).1]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw, hadj⟩, rfl⟩)
  have hmid := S.slabMid_between H hmem
  have hv_lt_mid : (S.p v).re < S.slabMid v.succ := hmid.1
  have hfilt : (S.activeEdges H v.succ).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.succ) < edgeY S.p v w (S.slabMid v.succ)) =
      S.passBelow H v ∪ (S.rightEdges H v).filter (fun e' =>
        heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid' := S.slabMid_between H he'ac
      rw [(S.activeEdges_succ_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'R
      · left
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        refine Finset.mem_filter.mpr ⟨he'p, ?_⟩
        exact (S.edgeY_lt_incident_right hp'.2.1 hp'.2.2 hvw (hHG ho'.2.2) (hHG hadj)
          hv_lt_mid hmid'.2 hmid.2).mp hlt
      · right
        refine ⟨he'R, ?_⟩
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hve' : v < e'.2 := hR'.2 ▸ ho'.2.1
        rw [hR'.2] at hlt
        rw [edgeY_eq_left_add_slope, edgeY_eq_left_add_slope] at hlt
        have hsl : edgeSlope S.p v e'.2 < edgeSlope S.p v w := by
          have : 0 < S.slabMid v.succ - (S.p v).re := by linarith
          nlinarith
        exact (heading_lt_iff_slope_pos (S.p_sub_re_pos_iff.mpr hve')
          (S.p_sub_re_pos_iff.mpr hvw)).mpr (by simpa [edgeSlope, Complex.sub_re, Complex.sub_im] using hsl)
    · rintro (he'b | ⟨he'R, hlt⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid' := S.slabMid_between H he'ac
        exact ⟨he'ac, (S.edgeY_lt_incident_right hp'.2.1 hp'.2.2 hvw (hHG ho'.2.2) (hHG hadj)
          hv_lt_mid hmid'.2 hmid.2).mpr (Finset.mem_filter.mp he'b).2⟩
      · have he'ac : e' ∈ S.activeEdges H v.succ := by
          rw [(S.activeEdges_succ_eq H v).1]; exact Finset.mem_union_right _ he'R
        have hR' := Finset.mem_filter.mp he'R
        have ho' := Finset.mem_filter.mp hR'.1
        have hve' : v < e'.2 := hR'.2 ▸ ho'.2.1
        have hsl : edgeSlope S.p v e'.2 < edgeSlope S.p v w := by
          have := (heading_lt_iff_slope_pos (S.p_sub_re_pos_iff.mpr hve')
            (S.p_sub_re_pos_iff.mpr hvw)).mp hlt
          simpa [edgeSlope, Complex.sub_re, Complex.sub_im] using this
        refine ⟨he'ac, ?_⟩
        rw [hR'.2, edgeY_eq_left_add_slope, edgeY_eq_left_add_slope]
        have : 0 < S.slabMid v.succ - (S.p v).re := by linarith
        nlinarith
  have hdisj : Disjoint (S.passBelow H v)
      ((S.rightEdges H v).filter (fun e' => heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v))) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (S.activeEdges_succ_eq H v).2
  unfold edgeRank
  rw [hfilt, Finset.card_union_of_disjoint hdisj]

private lemma edgeRank_leftEdge (hHG : H ≤ S.G) {u v : Fin n} (huv : u < v) (hadj : H.Adj u v) :
    S.edgeRank H v.castSucc (u, v) =
      (S.passBelow H v).card +
      ((S.leftEdges H v).filter (fun e' =>
        heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v))).card := by
  classical
  have hmem : (u, v) ∈ S.activeEdges H v.castSucc := by
    rw [(S.activeEdges_castSucc_eq H v).1]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, rfl⟩)
  have hmid := S.slabMid_between H hmem
  have hmid_lt_v : S.slabMid v.castSucc < (S.p v).re := hmid.2
  have hfilt : (S.activeEdges H v.castSucc).filter (fun e' =>
      edgeY S.p e'.1 e'.2 (S.slabMid v.castSucc) < edgeY S.p u v (S.slabMid v.castSucc)) =
      S.passBelow H v ∪ (S.leftEdges H v).filter (fun e' =>
        heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨he'ac, hlt⟩
      have hmid' := S.slabMid_between H he'ac
      rw [(S.activeEdges_castSucc_eq H v).1, Finset.mem_union] at he'ac
      rcases he'ac with he'p | he'L
      · left
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        refine Finset.mem_filter.mpr ⟨he'p, ?_⟩
        exact (S.edgeY_lt_incident_left hp'.2.1 hp'.2.2 huv (hHG ho'.2.2) (hHG hadj)
          hmid'.1 hmid.1 hmid_lt_v).mp hlt
      · right
        refine ⟨he'L, ?_⟩
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have he'v : e'.1 < v := hL'.2 ▸ ho'.2.1
        rw [hL'.2] at hlt
        rw [edgeY_eq_right_sub_slope S.p (S.hx_mono he'v), edgeY_eq_right_sub_slope S.p (S.hx_mono huv)] at hlt
        have hsl : edgeSlope S.p u v < edgeSlope S.p e'.1 v := by
          have : 0 < (S.p v).re - S.slabMid v.castSucc := by linarith
          nlinarith
        have hsl' : (S.p u - S.p v).im / (S.p u - S.p v).re < (S.p e'.1 - S.p v).im / (S.p e'.1 - S.p v).re := by
          have h1 : (S.p u - S.p v).im / (S.p u - S.p v).re = edgeSlope S.p u v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]
            rw [← neg_div_neg_eq]; ring_nf
          have h2 : (S.p e'.1 - S.p v).im / (S.p e'.1 - S.p v).re = edgeSlope S.p e'.1 v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]
            rw [← neg_div_neg_eq]; ring_nf
          linarith
        exact (heading_lt_iff_slope_neg (S.p_sub_re_neg_iff.mpr huv)
          (S.p_sub_re_neg_iff.mpr he'v)).mpr hsl'
    · rintro (he'b | ⟨he'L, hlt⟩)
      · have he'p := (Finset.mem_filter.mp he'b).1
        have hp' := Finset.mem_filter.mp he'p
        have ho' := Finset.mem_filter.mp hp'.1
        have he'ac : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_left _ he'p
        have hmid' := S.slabMid_between H he'ac
        exact ⟨he'ac, (S.edgeY_lt_incident_left hp'.2.1 hp'.2.2 huv (hHG ho'.2.2) (hHG hadj)
          hmid'.1 hmid.1 hmid_lt_v).mpr (Finset.mem_filter.mp he'b).2⟩
      · have he'ac : e' ∈ S.activeEdges H v.castSucc := by
          rw [(S.activeEdges_castSucc_eq H v).1]; exact Finset.mem_union_right _ he'L
        have hL' := Finset.mem_filter.mp he'L
        have ho' := Finset.mem_filter.mp hL'.1
        have he'v : e'.1 < v := hL'.2 ▸ ho'.2.1
        have hsl' := (heading_lt_iff_slope_neg (S.p_sub_re_neg_iff.mpr huv)
          (S.p_sub_re_neg_iff.mpr he'v)).mp hlt
        have hsl : edgeSlope S.p u v < edgeSlope S.p e'.1 v := by
          have h1 : (S.p u - S.p v).im / (S.p u - S.p v).re = edgeSlope S.p u v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
          have h2 : (S.p e'.1 - S.p v).im / (S.p e'.1 - S.p v).re = edgeSlope S.p e'.1 v := by
            simp only [edgeSlope, Complex.sub_re, Complex.sub_im]; rw [← neg_div_neg_eq]; ring_nf
          linarith
        refine ⟨he'ac, ?_⟩
        rw [hL'.2, edgeY_eq_right_sub_slope S.p (S.hx_mono he'v), edgeY_eq_right_sub_slope S.p (S.hx_mono huv)]
        have : 0 < (S.p v).re - S.slabMid v.castSucc := by linarith
        nlinarith
  have hdisj : Disjoint (S.passBelow H v)
      ((S.leftEdges H v).filter (fun e' => heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v))) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (S.activeEdges_castSucc_eq H v).2
  unfold edgeRank
  rw [hfilt, Finset.card_union_of_disjoint hdisj]

private lemma edge_top_connected (hHG : H ≤ S.G) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    (i j : Fin (n + 1)) (hi1 : a.val < i.val) (hi2 : i.val ≤ b.val)
    (hj1 : a.val < j.val) (hj2 : j.val ≤ b.val) :
    have hi : (a, b) ∈ S.activeEdges H i :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hi1, hi2⟩
    have hj : (a, b) ∈ S.activeEdges H j :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hj1, hj2⟩
    (S.slabGraph H).Reachable
      ⟨i, ⟨S.edgeRank H i (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hi)⟩⟩
      ⟨j, ⟨S.edgeRank H j (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hj)⟩⟩ := by
  classical

  have hstep : ∀ (v : Fin n) (hav : a < v) (hvb : v < b),
      have h1 : (a, b) ∈ S.activeEdges H v.castSucc :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simpa, by simpa using hvb.le⟩
      have h2 : (a, b) ∈ S.activeEdges H v.succ :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp; omega, by simp; omega⟩
      (S.slabGraph H).Adj
        ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h1)⟩⟩
        ⟨v.succ, ⟨S.edgeRank H v.succ (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h2)⟩⟩ := by
    intro v hav hvb
    have hp : (a, b) ∈ S.passEdges H v :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hav, hvb⟩
    rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at hp
    apply S.slabGraph_adj_step H v
    rcases hp with hpb | hpa
    · have hr := S.edgeRank_passBelow H hHG hpb
      left; dsimp only; exact ⟨by omega, by omega⟩
    · have hr := S.edgeRank_passAbove H hHG hpa
      right; dsimp only; exact ⟨by omega, by omega⟩
  suffices hmono : ∀ (d : ℕ) (k : Fin (n + 1)) (hk1 : a.val < k.val) (hk2 : k.val + d ≤ b.val),
      ∀ (h1 : (a, b) ∈ S.activeEdges H k)
        (h2 : (a, b) ∈ S.activeEdges H ⟨k.val + d, by have := b.isLt; omega⟩),
      (S.slabGraph H).Reachable
        ⟨k, ⟨S.edgeRank H k (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h1)⟩⟩
        ⟨⟨k.val + d, by have := b.isLt; omega⟩, ⟨S.edgeRank H ⟨k.val + d, by have := b.isLt; omega⟩ (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H h2)⟩⟩ by
    intro hi hj
    rcases le_total i.val j.val with hij | hji
    · have hi' : (⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      have hres := hmono (j.val - i.val) i hi1 (by omega) hi (hi' ▸ hj)
      have heq_j : (⟨⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ (a, b) + 1,
            Nat.succ_lt_succ (S.edgeRank_lt H (hi' ▸ hj))⟩⟩ : S.SlabVert H) =
          ⟨j, ⟨S.edgeRank H j (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hj)⟩⟩ :=
        S.slabVert_ext H hi' (by dsimp; rw [hi'])
      rw [heq_j] at hres; exact hres
    · have hj' : (⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
      have hres := hmono (i.val - j.val) j hj1 (by omega) hj (hj' ▸ hi)
      have heq_i : (⟨⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ (a, b) + 1,
            Nat.succ_lt_succ (S.edgeRank_lt H (hj' ▸ hi))⟩⟩ : S.SlabVert H) =
          ⟨i, ⟨S.edgeRank H i (a, b) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hi)⟩⟩ :=
        S.slabVert_ext H hj' (by dsimp; rw [hj'])
      rw [heq_i] at hres; exact hres.symm
  intro d
  induction d with
  | zero => intro k _ _ h1 h2; exact SimpleGraph.Reachable.refl _
  | succ d ihd =>
    intro k hk1 hk2 h1 h2
    let v : Fin n := ⟨k.val + d, by have := b.isLt; omega⟩
    have hm : (a, b) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp [v]; omega, by simp [v]; omega⟩
    have hprev := ihd k hk1 (by omega) h1 hm
    have hst := hstep v (by show a.val < v.val; simp [v]; omega) (by show v.val < b.val; simp [v]; omega)
    exact hprev.trans hst.reachable

private lemma edge_bot_connected (hHG : H ≤ S.G) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    (i j : Fin (n + 1)) (hi1 : a.val < i.val) (hi2 : i.val ≤ b.val)
    (hj1 : a.val < j.val) (hj2 : j.val ≤ b.val) :
    have hi : (a, b) ∈ S.activeEdges H i :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hi1, hi2⟩
    have hj : (a, b) ∈ S.activeEdges H j :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hj1, hj2⟩
    (S.slabGraph H).Reachable
      ⟨i, ⟨S.edgeRank H i (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hi)⟩⟩
      ⟨j, ⟨S.edgeRank H j (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hj)⟩⟩ := by
  classical
  have hstep : ∀ (v : Fin n) (hav : a < v) (hvb : v < b),
      have h1 : (a, b) ∈ S.activeEdges H v.castSucc :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simpa, by simpa using hvb.le⟩
      have h2 : (a, b) ∈ S.activeEdges H v.succ :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp; omega, by simp; omega⟩
      (S.slabGraph H).Adj
        ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h1)⟩⟩
        ⟨v.succ, ⟨S.edgeRank H v.succ (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h2)⟩⟩ := by
    intro v hav hvb
    have hp : (a, b) ∈ S.passEdges H v :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, hav, hvb⟩
    rw [(S.passEdges_partition H hHG v).1, Finset.mem_union] at hp
    apply S.slabGraph_adj_step H v
    rcases hp with hpb | hpa
    · have hr := S.edgeRank_passBelow H hHG hpb
      left; dsimp only; exact ⟨by omega, by omega⟩
    · have hr := S.edgeRank_passAbove H hHG hpa
      right; dsimp only; exact ⟨by omega, by omega⟩
  suffices hmono : ∀ (d : ℕ) (k : Fin (n + 1)) (hk1 : a.val < k.val) (hk2 : k.val + d ≤ b.val),
      ∀ (h1 : (a, b) ∈ S.activeEdges H k)
        (h2 : (a, b) ∈ S.activeEdges H ⟨k.val + d, by have := b.isLt; omega⟩),
      (S.slabGraph H).Reachable
        ⟨k, ⟨S.edgeRank H k (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h1)⟩⟩
        ⟨⟨k.val + d, by have := b.isLt; omega⟩, ⟨S.edgeRank H ⟨k.val + d, by have := b.isLt; omega⟩ (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H h2)⟩⟩ by
    intro hi hj
    rcases le_total i.val j.val with hij | hji
    · have hi' : (⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      have hres := hmono (j.val - i.val) i hi1 (by omega) hi (hi' ▸ hj)
      have heq_j : (⟨⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨i.val + (j.val - i.val), by have := b.isLt; omega⟩ (a, b),
            Nat.lt_succ_of_lt (S.edgeRank_lt H (hi' ▸ hj))⟩⟩ : S.SlabVert H) =
          ⟨j, ⟨S.edgeRank H j (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hj)⟩⟩ :=
        S.slabVert_ext H hi' (by dsimp; rw [hi'])
      rw [heq_j] at hres; exact hres
    · have hj' : (⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
      have hres := hmono (i.val - j.val) j hj1 (by omega) hj (hj' ▸ hi)
      have heq_i : (⟨⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩,
          ⟨S.edgeRank H ⟨j.val + (i.val - j.val), by have := b.isLt; omega⟩ (a, b),
            Nat.lt_succ_of_lt (S.edgeRank_lt H (hj' ▸ hi))⟩⟩ : S.SlabVert H) =
          ⟨i, ⟨S.edgeRank H i (a, b), Nat.lt_succ_of_lt (S.edgeRank_lt H hi)⟩⟩ :=
        S.slabVert_ext H hj' (by dsimp; rw [hj'])
      rw [heq_i] at hres; exact hres.symm
  intro d
  induction d with
  | zero => intro k _ _ h1 h2; exact SimpleGraph.Reachable.refl _
  | succ d ihd =>
    intro k hk1 hk2 h1 h2
    let v : Fin n := ⟨k.val + d, by have := b.isLt; omega⟩
    have hm : (a, b) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hadj⟩, by simp [v]; omega, by simp [v]; omega⟩
    have hprev := ihd k hk1 (by omega) h1 hm
    have hst := hstep v (by show a.val < v.val; simp [v]; omega) (by show v.val < b.val; simp [v]; omega)
    exact hprev.trans hst.reachable

private noncomputable def dartMap (d : DartOf H) : S.SlabVert H := by
  classical
  exact if h : d.1.1 < d.1.2 then
    have hmem : (d.1.1, d.1.2) ∈ S.activeEdges H d.1.1.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, d.2⟩, by simp, by simp; omega⟩
    ⟨d.1.1.succ, ⟨S.edgeRank H d.1.1.succ (d.1.1, d.1.2) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hmem)⟩⟩
  else
    have hvu : d.1.2 < d.1.1 := lt_of_le_of_ne (not_lt.mp h) (H.ne_of_adj d.2).symm
    have hmem : (d.1.2, d.1.1) ∈ S.activeEdges H d.1.1.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, d.2.symm⟩, by simpa, by simp⟩
    ⟨d.1.1.castSucc, ⟨S.edgeRank H d.1.1.castSucc (d.1.2, d.1.1), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩

private lemma dartMap_to_target_left (hHG : H ≤ S.G) {u v : Fin n} (huv : u < v) (hadj : H.Adj u v) :
    have hmem : (u, v) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, by simpa, by simp⟩
    (S.slabGraph H).Reachable (S.dartMap H ⟨(u, v), hadj⟩)
      ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_pos huv]
  exact S.edge_top_connected H hHG huv hadj u.succ v.castSucc (by simp) (by simp; omega) (by simpa) (by simp)

private lemma dartMap_to_target_right (hHG : H ≤ S.G) {u v : Fin n} (hvu : v < u) (hadj : H.Adj u v) :
    have hmem : (v, u) ∈ S.activeEdges H v.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, hadj.symm⟩, by simp, by simp; omega⟩
    (S.slabGraph H).Reachable (S.dartMap H ⟨(u, v), hadj⟩)
      ⟨v.succ, ⟨S.edgeRank H v.succ (v, u), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_neg (not_lt.mpr hvu.le)]
  exact S.edge_bot_connected H hHG hvu hadj.symm u.castSucc v.succ (by simpa) (by simp) (by simp) (by simp; omega)

private lemma dartMap_at_source_right {v w : Fin n} (hvw : v < w) (hadj : H.Adj v w) :
    have hmem : (v, w) ∈ S.activeEdges H v.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw, hadj⟩, by simp, by simp; omega⟩
    S.dartMap H ⟨(v, w), hadj⟩ =
      ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, Nat.succ_lt_succ (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_pos hvw]

private lemma dartMap_at_source_left {v w : Fin n} (hwv : w < v) (hadj : H.Adj v w) :
    have hmem : (w, v) ∈ S.activeEdges H v.castSucc :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv, hadj.symm⟩, by simpa, by simp⟩
    S.dartMap H ⟨(v, w), hadj⟩ =
      ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩ := by
  classical
  unfold dartMap; rw [dif_neg (not_lt.mpr hwv.le)]

private lemma heading_right_lt_left {v u w : Fin n} (hvw : v < w) (huv : u < v) :
    heading (S.p w - S.p v) < heading (S.p u - S.p v) := by
  have h1 := heading_bounds_pos (S.p_sub_re_pos_iff.mpr hvw)
  have h2 := heading_bounds_neg (S.p_sub_re_neg_iff.mpr huv)
  linarith

private lemma dartMap_phi_reachable (hHG : H ≤ S.G) (d : DartOf H) :
    (S.slabGraph H).Reachable (S.dartMap H d) (S.dartMap H (S.geoPhi H hHG d)) := by
  classical
  rcases d with ⟨⟨u, v⟩, huv⟩
  let w_sub := S.geoSigma H hHG v ⟨u, huv.symm⟩
  let w := w_sub.1
  have hvw : H.Adj v w := w_sub.2
  change (S.slabGraph H).Reachable (S.dartMap H ⟨(u, v), huv⟩) (S.dartMap H ⟨(v, w), hvw⟩)
  set p := (S.passBelow H v).card
  set dL := (S.leftEdges H v).card
  set dR := (S.rightEdges H v).card
  have hpL := S.passBelow_add_left_le H hHG v
  have hpR := S.passBelow_add_right_le H hHG v
  have hstep_c := S.activeEdges_card_step H v
  rcases S.geoSigma_spec H hHG v ⟨u, huv.symm⟩ with ⟨hmin, hmax⟩ | ⟨hlt, hgap⟩
  ·
    rcases lt_or_gt_of_ne (H.ne_of_adj huv) with hlt_uv | hgt_uv
    ·
      have hdR0 : dR = 0 := by
        dsimp only [dR]; unfold rightEdges
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h1
        simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have hve : v < e.2 := h1 ▸ he.1
        have hadj : H.Adj v e.2 := h1 ▸ he.2
        have h1' := hmin ⟨e.2, hadj⟩
        have h2' := S.heading_right_lt_left hve hlt_uv
        linarith
      have hlt_wv : w < v := by
        rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with h | h
        · exact h
        · exfalso; have := hmin ⟨w, hvw⟩; have := S.heading_right_lt_left h hlt_uv; linarith

      have hru : S.edgeRank H v.castSucc (u, v) = p + dL - 1 := by
        rw [S.edgeRank_leftEdge H hHG hlt_uv huv]
        have hfilt : (S.leftEdges H v).filter (fun e' =>
            heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v)) = (S.leftEdges H v).erase (u, v) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
          · rintro ⟨hne', he'⟩
            have hL' := Finset.mem_filter.mp he'
            have ho' := Finset.mem_filter.mp hL'.1
            have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
            refine ⟨he', lt_of_le_of_ne (hmin ⟨e'.1, hadj'⟩) (fun h => hne' ?_)⟩
            have hsub : (⟨u, huv.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hadj'⟩ := S.heading_inj_H H hHG v h
            have hu' : u = e'.1 := congrArg Subtype.val hsub
            exact Prod.ext hu'.symm hL'.2
        have hu_mem : (u, v) ∈ S.leftEdges H v :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩
        rw [hfilt, Finset.card_erase_of_mem hu_mem]
        have hdL1 : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v), hu_mem⟩
        dsimp only [p, dL]; omega
      have hrw : S.edgeRank H v.castSucc (w, v) = p := by
        rw [S.edgeRank_leftEdge H hHG hlt_wv hvw.symm]
        have hfilt : (S.leftEdges H v).filter (fun e' =>
            heading (S.p w - S.p v) < heading (S.p e'.1 - S.p v)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro e' he' hlt'
          have hL' := Finset.mem_filter.mp he'
          have ho' := Finset.mem_filter.mp hL'.1
          have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
          exact not_lt.mpr (hmax ⟨e'.1, hadj'⟩) hlt'
        rw [hfilt, Finset.card_empty, add_zero]
      have hdL1 : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v),
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩⟩
      have h1 := S.dartMap_to_target_left H hHG hlt_uv huv
      have h2 := S.dartMap_at_source_left H hlt_wv hvw

      have hmid : (S.slabGraph H).Adj
          ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, by omega⟩⟩
          ⟨v.succ, ⟨p, by omega⟩⟩ := by
        apply S.slabGraph_adj_step H v; right; dsimp; omega
      have hmid2 : (S.slabGraph H).Adj
          ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), by omega⟩⟩
          ⟨v.succ, ⟨p, by omega⟩⟩ := by
        apply S.slabGraph_adj_step H v; left; dsimp; omega
      rw [h2]
      exact h1.trans (hmid.reachable.trans hmid2.symm.reachable)
    ·
      have hru : S.edgeRank H v.succ (v, u) = p := by
        rw [S.edgeRank_rightEdge H hHG hgt_uv huv.symm]
        have hfilt : (S.rightEdges H v).filter (fun e' =>
            heading (S.p e'.2 - S.p v) < heading (S.p u - S.p v)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro e' he' hlt'
          have hR' := Finset.mem_filter.mp he'
          have ho' := Finset.mem_filter.mp hR'.1
          have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
          exact not_lt.mpr (hmin ⟨e'.2, hadj'⟩) hlt'
        rw [hfilt, Finset.card_empty, add_zero]
      have h1 := S.dartMap_to_target_right H hHG hgt_uv huv
      rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with hlt_wv | hgt_wv
      ·
        have hrw : S.edgeRank H v.castSucc (w, v) = p := by
          rw [S.edgeRank_leftEdge H hHG hlt_wv hvw.symm]
          have hfilt : (S.leftEdges H v).filter (fun e' =>
              heading (S.p w - S.p v) < heading (S.p e'.1 - S.p v)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro e' he' hlt'
            have hL' := Finset.mem_filter.mp he'
            have ho' := Finset.mem_filter.mp hL'.1
            have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
            exact not_lt.mpr (hmax ⟨e'.1, hadj'⟩) hlt'
          rw [hfilt, Finset.card_empty, add_zero]
        have h2 := S.dartMap_at_source_left H hlt_wv hvw
        have hglue : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, u), by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; left; dsimp; omega
        rw [h2]
        exact h1.trans hglue.symm.reachable
      ·
        have hdL0 : dL = 0 := by
          dsimp only [dL]; unfold leftEdges
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro e he h2
          simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
          have hev : e.1 < v := h2 ▸ he.1
          have hadj : H.Adj v e.1 := h2 ▸ he.2.symm
          have h1' := hmax ⟨e.1, hadj⟩
          have h2' := S.heading_right_lt_left hgt_wv hev
          linarith
        have hrw : S.edgeRank H v.succ (v, w) = p + dR - 1 := by
          rw [S.edgeRank_rightEdge H hHG hgt_wv hvw]
          have hfilt : (S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v)) = (S.rightEdges H v).erase (v, w) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
            · rintro ⟨hne', he'⟩
              have hR' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hR'.1
              have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
              refine ⟨he', lt_of_le_of_ne (hmax ⟨e'.2, hadj'⟩) (fun h => hne' ?_)⟩
              have hsub : (⟨e'.2, hadj'⟩ : {x : Fin n // H.Adj v x}) = ⟨w, hvw⟩ := S.heading_inj_H H hHG v h
              have hw' : e'.2 = w := congrArg Subtype.val hsub
              exact Prod.ext hR'.2 hw'
          have hw_mem : (v, w) ∈ S.rightEdges H v :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩
          rw [hfilt, Finset.card_erase_of_mem hw_mem]
          have hdR1 : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w), hw_mem⟩
          dsimp only [p, dR]; omega
        have hdR1 : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩⟩
        have h2 := S.dartMap_at_source_right H hgt_wv hvw
        have hglue1 : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨p, by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, u), by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; left; dsimp; omega
        have hglue2 : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨p, by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; right; dsimp; omega
        rw [h2]
        exact h1.trans (hglue1.symm.reachable.trans hglue2.reachable)
  ·
    rcases lt_or_gt_of_ne (H.ne_of_adj huv) with hlt_uv | hgt_uv
    ·
      have h1 := S.dartMap_to_target_left H hHG hlt_uv huv
      rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with hlt_wv | hgt_wv
      ·
        have hr_eq : S.edgeRank H v.castSucc (w, v) = S.edgeRank H v.castSucc (u, v) + 1 := by
          rw [S.edgeRank_leftEdge H hHG hlt_wv hvw.symm, S.edgeRank_leftEdge H hHG hlt_uv huv]
          have hfilt : (S.leftEdges H v).filter (fun e' =>
              heading (S.p w - S.p v) < heading (S.p e'.1 - S.p v)) =
              insert (u, v) ((S.leftEdges H v).filter (fun e' =>
                heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v))) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨he', hlt'⟩
              have hL' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hL'.1
              have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
              have hge := hgap ⟨e'.1, hadj'⟩ hlt'
              rcases eq_or_lt_of_le hge with heq | hgt
              · left
                have hsub : (⟨u, huv.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hadj'⟩ := S.heading_inj_H H hHG v heq
                have hu' : u = e'.1 := congrArg Subtype.val hsub
                exact Prod.ext hu'.symm hL'.2
              · right; exact ⟨he', hgt⟩
            · rintro (rfl | ⟨he', hgt⟩)
              · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩, hlt⟩
              · exact ⟨he', hlt.trans hgt⟩
          rw [hfilt, Finset.card_insert_of_notMem (by simp [lt_irrefl])]
          dsimp only [p]; omega
        have h2 := S.dartMap_at_source_left H hlt_wv hvw
        rw [h2]
        have heq_vert : (⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, by
              have hm : (u, v) ∈ S.activeEdges H v.castSucc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, by simpa, by simp⟩
              exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩ : S.SlabVert H) =
            ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (w, v), by
              have hm : (w, v) ∈ S.activeEdges H v.castSucc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_wv, hvw.symm⟩, by simpa, by simp⟩
              exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ := by
          refine Sigma.ext rfl (heq_of_eq (Fin.ext hr_eq.symm))
        rw [← heq_vert]; exact h1
      ·
        have hru : S.edgeRank H v.castSucc (u, v) = p + dL - 1 := by
          rw [S.edgeRank_leftEdge H hHG hlt_uv huv]
          have hfilt : (S.leftEdges H v).filter (fun e' =>
              heading (S.p u - S.p v) < heading (S.p e'.1 - S.p v)) = (S.leftEdges H v).erase (u, v) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
            · rintro ⟨hne', he'⟩
              have hL' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hL'.1
              have he'v : e'.1 < v := hL'.2 ▸ ho'.2.1
              have hadj' : H.Adj v e'.1 := hL'.2 ▸ ho'.2.2.symm
              have hge := hgap ⟨e'.1, hadj'⟩ (S.heading_right_lt_left hgt_wv he'v)
              refine ⟨he', lt_of_le_of_ne hge (fun h => hne' ?_)⟩
              have hsub : (⟨u, huv.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hadj'⟩ := S.heading_inj_H H hHG v h
              exact Prod.ext (congrArg Subtype.val hsub).symm hL'.2
          have hu_mem : (u, v) ∈ S.leftEdges H v :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩
          rw [hfilt, Finset.card_erase_of_mem hu_mem]
          have : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v), hu_mem⟩; dsimp only [p, dL]; omega
        have hrw : S.edgeRank H v.succ (v, w) = p + dR - 1 := by
          rw [S.edgeRank_rightEdge H hHG hgt_wv hvw]
          have hfilt : (S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v)) = (S.rightEdges H v).erase (v, w) := by
            ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
            · rintro ⟨hne', he'⟩
              have hR' := Finset.mem_filter.mp he'
              have ho' := Finset.mem_filter.mp hR'.1
              have hve' : v < e'.2 := hR'.2 ▸ ho'.2.1
              have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
              have hle : heading (S.p e'.2 - S.p v) ≤ heading (S.p w - S.p v) := by
                by_contra! hgt'
                have hge := hgap ⟨e'.2, hadj'⟩ hgt'
                have := S.heading_right_lt_left hve' hlt_uv
                linarith
              refine ⟨he', lt_of_le_of_ne hle (fun h => hne' ?_)⟩
              have hsub : (⟨e'.2, hadj'⟩ : {x : Fin n // H.Adj v x}) = ⟨w, hvw⟩ := S.heading_inj_H H hHG v h
              exact Prod.ext hR'.2 (congrArg Subtype.val hsub)
          have hw_mem : (v, w) ∈ S.rightEdges H v :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩
          rw [hfilt, Finset.card_erase_of_mem hw_mem]
          have : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w), hw_mem⟩; dsimp only [p, dR]; omega
        have hdL1 : 1 ≤ dL := Finset.card_pos.mpr ⟨(u, v),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_uv, huv⟩, rfl⟩⟩
        have hdR1 : 1 ≤ dR := Finset.card_pos.mpr ⟨(v, w),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩⟩
        have h2 := S.dartMap_at_source_right H hgt_wv hvw
        have hglue : (S.slabGraph H).Adj
            ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (u, v) + 1, by omega⟩⟩
            ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, by omega⟩⟩ := by
          apply S.slabGraph_adj_step H v; right; dsimp; omega
        rw [h2]
        exact h1.trans hglue.reachable
    ·
      have hgt_wv : v < w := by
        rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with h | h
        · exfalso; have := S.heading_right_lt_left hgt_uv h; linarith
        · exact h
      have hr_eq : S.edgeRank H v.succ (v, u) = S.edgeRank H v.succ (v, w) + 1 := by
        rw [S.edgeRank_rightEdge H hHG hgt_uv huv.symm, S.edgeRank_rightEdge H hHG hgt_wv hvw]
        have hfilt : (S.rightEdges H v).filter (fun e' =>
            heading (S.p e'.2 - S.p v) < heading (S.p u - S.p v)) =
            insert (v, w) ((S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p w - S.p v))) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨he', hlt'⟩
            have hR' := Finset.mem_filter.mp he'
            have ho' := Finset.mem_filter.mp hR'.1
            have hadj' : H.Adj v e'.2 := hR'.2 ▸ ho'.2.2
            have hle : heading (S.p e'.2 - S.p v) ≤ heading (S.p w - S.p v) := by
              by_contra! hgt'
              have := hgap ⟨e'.2, hadj'⟩ hgt'
              linarith
            rcases eq_or_lt_of_le hle with heq | hlt2
            · left
              have hsub : (⟨e'.2, hadj'⟩ : {x : Fin n // H.Adj v x}) = ⟨w, hvw⟩ := S.heading_inj_H H hHG v heq
              exact Prod.ext hR'.2 (congrArg Subtype.val hsub)
            · right; exact ⟨he', hlt2⟩
          · rintro (rfl | ⟨he', hlt2⟩)
            · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, rfl⟩, hlt⟩
            · exact ⟨he', hlt2.trans hlt⟩
        rw [hfilt, Finset.card_insert_of_notMem (by simp [lt_irrefl])]
        dsimp only [p]; omega
      have h1 := S.dartMap_to_target_right H hHG hgt_uv huv
      have h2 := S.dartMap_at_source_right H hgt_wv hvw
      rw [h2]
      have heq_vert : (⟨v.succ, ⟨S.edgeRank H v.succ (v, u), by
            have hm : (v, u) ∈ S.activeEdges H v.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_uv, huv.symm⟩, by simp, by simp; omega⟩
            exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ : S.SlabVert H) =
          ⟨v.succ, ⟨S.edgeRank H v.succ (v, w) + 1, by
            have hm : (v, w) ∈ S.activeEdges H v.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt_wv, hvw⟩, by simp, by simp; omega⟩
            exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩ := by
        refine Sigma.ext rfl (heq_of_eq (Fin.ext hr_eq))
      rw [← heq_vert]; exact h1

private noncomputable def orbitToComp (hHG : H ≤ S.G) :
    Quotient (orbitSetoid (S.geoPhi H hHG)) → (S.slabGraph H).ConnectedComponent :=
  Quotient.lift (fun d => (S.slabGraph H).connectedComponentMk (S.dartMap H d)) (by
    intro d₁ d₂ h
    obtain ⟨k, rfl⟩ := h
    induction k generalizing d₁ with
    | zero => rfl
    | succ k ihk =>
      have h1 : (S.slabGraph H).connectedComponentMk (S.dartMap H d₁) =
          (S.slabGraph H).connectedComponentMk (S.dartMap H (S.geoPhi H hHG d₁)) :=
        SimpleGraph.ConnectedComponent.sound (S.dartMap_phi_reachable H hHG d₁)
      rw [h1, show (S.geoPhi H hHG ^ (k + 1)) d₁ = (S.geoPhi H hHG ^ k) (S.geoPhi H hHG d₁) by
        rw [pow_add, pow_one, Equiv.Perm.mul_apply]]
      exact ihk _)

private lemma orbitToComp_surjective_of_outer (hHG : H ≤ S.G)
    (hout : ∃ d : DartOf H, (S.slabGraph H).Reachable (S.outerVert H) (S.dartMap H d)) :
    Function.Surjective (S.orbitToComp H hHG) := by
  classical
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with | _ x =>
  rcases x with ⟨i, r⟩
  rcases Nat.eq_zero_or_pos r.val with hr0 | hrpos
  ·
    have hbot : ∀ k : ℕ, (hk : k ≤ n) →
        (S.slabGraph H).Reachable (S.outerVert H) ⟨⟨k, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ := by
      intro k; induction k with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ k ihk =>
        intro hk
        let vk : Fin n := ⟨k, by omega⟩
        exact (ihk (by omega)).trans
          (S.slabGraph_adj_step H vk ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ (Or.inl ⟨Nat.zero_le _, rfl⟩)).reachable
    obtain ⟨d, hd⟩ := hout
    refine ⟨Quotient.mk _ d, SimpleGraph.ConnectedComponent.sound ?_⟩
    have h3 := hbot i.val (by omega)
    have hr_eq : (⟨i, r⟩ : S.SlabVert H) = ⟨⟨i.val, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ :=
      Sigma.ext rfl (heq_of_eq (Fin.ext hr0))
    rw [hr_eq]
    exact hd.symm.trans h3
  ·
    have hcard_i : r.val - 1 < (S.activeEdges H i).card := by omega
    have hinj : Set.InjOn (fun e : Fin n × Fin n => edgeY S.p e.1 e.2 (S.slabMid i)) ↑(S.activeEdges H i) := by
      intro e₁ h1 e₂ h2 heq
      by_contra hne
      have hm1 := S.slabMid_between H h1
      have hm2 := S.slabMid_between H h2
      have ho1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have ho2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      exact S.edgeY_ne_of_ne_edges ho1.1 ho2.1 (hHG ho1.2) (hHG ho2.2) hne hm1.1 hm1.2 hm2.1 hm2.2 heq
    let ys := (S.activeEdges H i).image (fun e => edgeY S.p e.1 e.2 (S.slabMid i))
    have hys_card : ys.card = (S.activeEdges H i).card := Finset.card_image_of_injOn hinj
    let emb := ys.orderEmbOfFin hys_card
    have hy_mem : emb ⟨r.val - 1, hcard_i⟩ ∈ ys := ys.orderEmbOfFin_mem hys_card ⟨r.val - 1, hcard_i⟩
    obtain ⟨e, he_mem, he_y⟩ := Finset.mem_image.mp hy_mem
    have hrank : S.edgeRank H i e = r.val - 1 := by
      unfold edgeRank
      have hmem_emb : ∀ e' ∈ S.activeEdges H i, ∃ j, emb j = edgeY S.p e'.1 e'.2 (S.slabMid i) :=
        fun e' he' => Set.mem_range.mp (by rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem _ he')
      have hcard_lt : ((S.activeEdges H i).filter (fun e' =>
          edgeY S.p e'.1 e'.2 (S.slabMid i) < edgeY S.p e.1 e.2 (S.slabMid i))).card =
          (Finset.univ.filter (fun j : Fin (S.activeEdges H i).card => j.val < r.val - 1)).card := by
        refine Finset.card_bij
          (fun e' he' => Classical.choose (hmem_emb e' (Finset.mem_filter.mp he').1))
          ?_ ?_ ?_
        · intro e' he'
          have hspec := Classical.choose_spec (hmem_emb e' (Finset.mem_filter.mp he').1)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hlt : emb (Classical.choose (hmem_emb e' (Finset.mem_filter.mp he').1)) < emb ⟨r.val - 1, hcard_i⟩ := by
            rw [hspec, ← he_y]; exact (Finset.mem_filter.mp he').2
          exact emb.lt_iff_lt.mp hlt
        · intro e₁ h1 e₂ h2 heq
          have hs1 := Classical.choose_spec (hmem_emb e₁ (Finset.mem_filter.mp h1).1)
          have hs2 := Classical.choose_spec (hmem_emb e₂ (Finset.mem_filter.mp h2).1)
          exact hinj (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
            (hs1.symm.trans ((congrArg emb heq).trans hs2))
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          obtain ⟨e', he'_mem, he'_y⟩ := Finset.mem_image.mp (ys.orderEmbOfFin_mem hys_card j)
          refine ⟨e', Finset.mem_filter.mpr ⟨he'_mem, ?_⟩, ?_⟩
          · rw [he'_y, he_y]; exact emb.strictMono hj
          · apply emb.injective
            rw [Classical.choose_spec (hmem_emb e' he'_mem), he'_y]
      rw [hcard_lt]
      have : (Finset.univ.filter (fun j : Fin (S.activeEdges H i).card => j.val < r.val - 1)).card =
          (Finset.range (r.val - 1)).card := by
        refine Finset.card_bij (fun j _ => j.val)
          (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
          (fun j₁ _ j₂ _ h => Fin.ext h)
          (fun k hk => ⟨⟨k, by rw [Finset.mem_range] at hk; omega⟩, by simp [Finset.mem_range.mp hk], rfl⟩)
      rw [this, Finset.card_range]
    have he_or := (Finset.mem_filter.mp (Finset.mem_filter.mp he_mem).1).2
    have he_sl := (Finset.mem_filter.mp he_mem).2
    let d : DartOf H := ⟨(e.1, e.2), he_or.2⟩
    refine ⟨Quotient.mk _ d, ?_⟩
    apply SimpleGraph.ConnectedComponent.sound
    have htop := S.edge_top_connected H hHG he_or.1 he_or.2 e.1.succ i (by simp) (by simp; omega) he_sl.1 he_sl.2
    dsimp only at htop
    rw [S.dartMap_at_source_right H he_or.1 he_or.2]
    have heq_i : (⟨i, ⟨S.edgeRank H i (e.1, e.2) + 1, Nat.succ_lt_succ (S.edgeRank_lt H (by
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_or.1, he_or.2⟩, he_sl.1, he_sl.2⟩))⟩⟩ : S.SlabVert H) =
        ⟨i, r⟩ :=
      S.slabVert_ext H rfl (by dsimp; rw [Prod.mk.eta, hrank]; omega)
    rw [heq_i] at htop; exact htop

private lemma slab_bottom_connected (i : Fin (n + 1)) :
    (S.slabGraph H).Reachable (S.outerVert H) ⟨i, ⟨0, Nat.succ_pos _⟩⟩ := by
  classical
  have hbot : ∀ k : ℕ, (hk : k ≤ n) →
      (S.slabGraph H).Reachable (S.outerVert H) ⟨⟨k, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩ := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      intro hk
      let vk : Fin n := ⟨k, by omega⟩
      exact (ih (by omega)).trans
        (S.slabGraph_adj_step H vk ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
          (Or.inl ⟨Nat.zero_le _, rfl⟩)).reachable
  have h := hbot i.val (Nat.le_of_lt_succ i.isLt)
  have hi : (⟨i.val, by omega⟩ : Fin (n + 1)) = i := Fin.ext rfl
  simpa only [hi] using h

private lemma outer_has_dart_of_edge (hHG : H ≤ S.G) (he : ∃ a b, H.Adj a b) :
    ∃ d : DartOf H, (S.slabGraph H).Reachable (S.outerVert H) (S.dartMap H d) := by
  classical
  obtain ⟨v, hL, hR⟩ := S.slab_exists_active_start H he
  have hA1 : (S.activeEdges H v.succ).Nonempty := Finset.card_pos.mp hR
  obtain ⟨emin, hemin_mem, hemin_min⟩ :=
    Finset.exists_min_image (S.activeEdges H v.succ)
      (fun e => edgeY S.p e.1 e.2 (S.slabMid v.succ)) hA1
  have hrank0 : S.edgeRank H v.succ emin = 0 := by
    rw [edgeRank]
    unfold activeEdges
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e' he' hlt
    exact not_lt.mpr (hemin_min e' he') hlt
  have hemin_or := Finset.mem_filter.mp (Finset.mem_filter.mp hemin_mem).1
  have hlt_e : emin.1 < emin.2 := hemin_or.2.1
  have hadj_e : H.Adj emin.2 emin.1 := hemin_or.2.2.symm
  have he1_v : emin.1 = v := by
    have hactive := (Finset.mem_filter.mp hemin_mem).2
    have hactive1 : emin.1.val < v.val + 1 := by
      have h := hactive.1
      change emin.1.val + 1 ≤ v.val + 1 at h
      omega
    have hactive2 : v.val + 1 ≤ emin.2.val := by
      have h := hactive.2
      change v.val + 1 ≤ emin.2.val at h
      exact h
    have hle : emin.1.val ≤ v.val := by omega
    by_contra hne
    have hneval : emin.1.val ≠ v.val := fun h => hne (Fin.ext h)
    have hlt : emin.1.val < v.val := by omega
    have hleft : emin ∈ S.activeEdges H v.castSucc := by
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_filter.mp hemin_mem).1, ?_⟩
      change emin.1.val < v.val ∧ v.val ≤ emin.2.val
      constructor
      · exact hlt
      · omega
    have hpos : 0 < (S.activeEdges H v.castSucc).card :=
      Finset.card_pos.mpr ⟨emin, hleft⟩
    omega
  let d : DartOf H := ⟨(emin.2, emin.1), hadj_e⟩
  have hmap := S.dartMap_to_target_right H hHG hlt_e hadj_e
  have heq : (⟨emin.1.succ, ⟨S.edgeRank H emin.1.succ (emin.1, emin.2),
        Nat.lt_succ_of_lt (S.edgeRank_lt H (by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_e, hadj_e.symm⟩,
              by simp, by simp; omega⟩))⟩⟩ : S.SlabVert H) =
      ⟨v.succ, ⟨0, Nat.succ_pos _⟩⟩ := by
    apply S.slabVert_ext H (congrArg Fin.succ he1_v)
    dsimp
    calc
      S.edgeRank H emin.1.succ (emin.1, emin.2) =
          S.edgeRank H v.succ emin :=
        congrArg₂ (S.edgeRank H) (congrArg Fin.succ he1_v) Prod.mk.eta
      _ = 0 := hrank0
  have hmap' : (S.slabGraph H).Reachable (S.dartMap H d)
      ⟨v.succ, ⟨0, Nat.succ_pos _⟩⟩ := by
    dsimp only at hmap
    rw [heq] at hmap
    exact hmap
  refine ⟨d, ?_⟩
  exact (S.slab_bottom_connected H v.succ).trans hmap'.symm

private lemma orbitToComp_surjective (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    Function.Surjective (S.orbitToComp H hHG) := by
  classical
  apply S.orbitToComp_surjective_of_outer H hHG
  apply S.outer_has_dart_of_edge H hHG
  let v : Fin n := ⟨0, by have := S.hn; omega⟩
  have h := hdeg v
  rw [S.leftEdges_add_rightEdges_eq_degree H v, ← H.card_neighborFinset_eq_degree] at h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h
  exact ⟨v, a, H.mem_neighborFinset v a |>.mp ha⟩
private lemma slab_components_le_orbits (hHG : H ≤ S.G)
    (hdeg : ∀ v : Fin n, 1 ≤ (S.leftEdges H v).card + (S.rightEdges H v).card) :
    Nat.card (S.slabGraph H).ConnectedComponent ≤ numOrbits (S.geoPhi H hHG) := by
  classical
  unfold numOrbits
  haveI : Fintype (S.slabGraph H).ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitSetoid (S.geoPhi H hHG))) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective (S.orbitToComp H hHG) (S.orbitToComp_surjective H hHG hdeg)

private lemma component_turning_identity (hHG : H ≤ S.G)
    (c : (S.slabGraph H).ConnectedComponent) :
    let F : Finset (S.SlabVert H) :=
      Finset.univ.filter (fun t => (S.slabGraph H).connectedComponentMk t = c)
    let D_F : Finset (DartOf H) :=
      Finset.univ.filter (fun d => (S.slabGraph H).connectedComponentMk (S.dartMap H d) = c)
    ((D_F.filter (S.isLeftTip H)).card : ℤ) - ((D_F.filter (S.isRightCap H)).card : ℤ) =
      (F.card : ℤ) - ((∑ t ∈ F, (S.slabInEdges H t).card : ℕ) : ℤ) -
        (if S.outerVert H ∈ F then (1 : ℤ) else 0) := by
  classical
  intro F D_F

  let isTipV (t : S.SlabVert H) : Prop :=
    ∃ (v : Fin n) (ht : t.1 = v.succ),
      (S.passBelow H v).card < t.2.val ∧ t.2.val < (S.passBelow H v).card + (S.rightEdges H v).card
  let isCapV (t : S.SlabVert H) : Prop :=
    ∃ (v : Fin n) (ht : t.1 = v.succ),
      t.2.val = (S.passBelow H v).card ∧ (S.rightEdges H v).card = 0 ∧
      0 < (S.leftEdges H v).card
  have hterm : ∀ t : S.SlabVert H,
      (1 : ℤ) - ((S.slabInEdges H t).card : ℤ) =
        (if t = S.outerVert H then (1 : ℤ) else 0) +
        (if isTipV t then (1 : ℤ) else 0) -
        (if isCapV t then (1 : ℤ) else 0) := by
    rintro ⟨i, r⟩
    cases i using Fin.cases with
    | zero =>
      have hr0 : r = ⟨0, Nat.succ_pos _⟩ := by
        apply Fin.ext
        have hrlt : r.val < (S.activeEdges H 0).card + 1 := r.isLt
        have h0 : (S.activeEdges H 0).card = 0 := by rw [S.activeEdges_zero, Finset.card_empty]
        omega
      have h1 : (⟨0, r⟩ : S.SlabVert H) = S.outerVert H := Sigma.ext rfl (heq_of_eq hr0)
      have h2 : ¬ isTipV ⟨0, r⟩ := by rintro ⟨v, ht, _⟩; exact Fin.succ_ne_zero v ht.symm
      have h3 : ¬ isCapV ⟨0, r⟩ := by rintro ⟨v, ht, _⟩; exact Fin.succ_ne_zero v ht.symm
      rw [S.slabInEdges_zero, if_pos h1, if_neg h2, if_neg h3]; norm_num
    | succ v =>
      have hnot0 : (⟨v.succ, r⟩ : S.SlabVert H) ≠ S.outerVert H := fun h =>
        Fin.succ_ne_zero v (congrArg Sigma.fst h)
      have htip_iff : isTipV ⟨v.succ, r⟩ ↔
          (S.passBelow H v).card < r.val ∧ r.val < (S.passBelow H v).card + (S.rightEdges H v).card := by
        constructor
        · rintro ⟨w, ht, h1, h2⟩; have := Fin.succ_injective _ ht; subst this; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨v, rfl, h1, h2⟩
      have hcap_iff : isCapV ⟨v.succ, r⟩ ↔
          r.val = (S.passBelow H v).card ∧ (S.rightEdges H v).card = 0 ∧
            0 < (S.leftEdges H v).card := by
        constructor
        · rintro ⟨w, ht, h1, h2, h3⟩; have := Fin.succ_injective _ ht; subst this
          exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨v, rfl, h1, h2, h3⟩
      rw [if_neg hnot0, S.slabInEdges_succ_card H hHG v r]
      simp only [htip_iff, hcap_iff]
      split_ifs with h1 h2 <;> omega
  have hsum : (F.card : ℤ) - ((∑ t ∈ F, (S.slabInEdges H t).card : ℕ) : ℤ) =
      (if S.outerVert H ∈ F then (1 : ℤ) else 0) +
      ((F.filter isTipV).card : ℤ) - ((F.filter isCapV).card : ℤ) := by
    have h1 : (F.card : ℤ) - ((∑ t ∈ F, (S.slabInEdges H t).card : ℕ) : ℤ) =
        ∑ t ∈ F, ((1 : ℤ) - ((S.slabInEdges H t).card : ℤ)) := by
      push_cast; rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have htip : ∑ x ∈ F, (if isTipV x then (1 : ℤ) else 0) = ((F.filter isTipV).card : ℤ) := by
      rw [Finset.sum_boole]
    have hcap : ∑ x ∈ F, (if isCapV x then (1 : ℤ) else 0) = ((F.filter isCapV).card : ℤ) := by
      rw [Finset.sum_boole]
    rw [h1]
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', htip, hcap]

  have hbij_tip : (D_F.filter (S.isLeftTip H)).card = (F.filter isTipV).card := by
    refine Finset.card_bij
      (fun d hd =>
        have hlt : d.1.2 < d.1.1 := (Finset.mem_filter.mp hd).2.1
        have hmem : (d.1.2, d.1.1) ∈ S.activeEdges H d.1.2.succ :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, d.2.symm⟩, by simp, by simp; omega⟩
        ⟨d.1.2.succ, ⟨S.edgeRank H d.1.2.succ (d.1.2, d.1.1), Nat.lt_succ_of_lt (S.edgeRank_lt H hmem)⟩⟩)
      ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, D_F, F, Finset.mem_univ, true_and] at hd ⊢
      rcases hd with ⟨hcomp, hvu, hnotmin⟩
      have hreach := S.dartMap_to_target_right H hHG hvu d.2
      refine ⟨(SimpleGraph.ConnectedComponent.sound hreach).symm.trans hcomp, d.1.2, rfl, ?_, ?_⟩
      · dsimp only
        rw [S.edgeRank_rightEdge H hHG hvu d.2.symm]
        have hex : ∃ w, H.Adj d.1.2 w ∧ heading (S.p w - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2) := by
          unfold isMinNeighbor at hnotmin; push Not at hnotmin; exact hnotmin
        obtain ⟨w, hvw, hlt_w⟩ := hex
        have hvw_lt : d.1.2 < w := by
          rcases lt_or_gt_of_ne (H.ne_of_adj hvw).symm with h | h
          · exfalso; have := S.heading_right_lt_left hvu h; linarith
          · exact h
        have hpos : 0 < ((S.rightEdges H d.1.2).filter (fun e' =>
            heading (S.p e'.2 - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2))).card :=
          Finset.card_pos.mpr ⟨(d.1.2, w), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw_lt, hvw⟩, rfl⟩, hlt_w⟩⟩
        omega
      · dsimp only
        rw [S.edgeRank_rightEdge H hHG hvu d.2.symm]
        have hlt_card : ((S.rightEdges H d.1.2).filter (fun e' =>
            heading (S.p e'.2 - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2))).card <
            (S.rightEdges H d.1.2).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
          have : (d.1.2, d.1.1) ∈ (S.rightEdges H d.1.2).filter (fun e' =>
              heading (S.p e'.2 - S.p d.1.2) < heading (S.p d.1.1 - S.p d.1.2)) := by
            rw [h]; exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, d.2.symm⟩, rfl⟩
          exact lt_irrefl _ (Finset.mem_filter.mp this).2
        omega
    · intro d₁ h1 d₂ h2 heq
      have hv : d₁.1.2 = d₂.1.2 := Fin.succ_injective _ (congrArg Sigma.fst heq)
      have hvu1 : d₁.1.2 < d₁.1.1 := (Finset.mem_filter.mp h1).2.1
      have hvu2 : d₂.1.2 < d₂.1.1 := (Finset.mem_filter.mp h2).2.1
      have hr : S.edgeRank H d₁.1.2.succ (d₁.1.2, d₁.1.1) = S.edgeRank H d₂.1.2.succ (d₂.1.2, d₂.1.1) := by
        simpa using congrArg (fun x : S.SlabVert H => x.2.val) heq
      rcases d₁ with ⟨⟨u₁, v₁⟩, hadj1⟩
      rcases d₂ with ⟨⟨u₂, v₂⟩, hadj2⟩
      dsimp at hv hr hvu1 hvu2; subst hv
      rw [S.edgeRank_rightEdge H hHG hvu1 hadj1.symm, S.edgeRank_rightEdge H hHG hvu2 hadj2.symm] at hr
      have hcard_eq : ((S.rightEdges H v₁).filter (fun e' =>
          heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁))).card =
          ((S.rightEdges H v₁).filter (fun e' =>
          heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁))).card := by omega
      have hhead : heading (S.p u₁ - S.p v₁) = heading (S.p u₂ - S.p v₁) := by
        rcases lt_trichotomy (heading (S.p u₁ - S.p v₁)) (heading (S.p u₂ - S.p v₁)) with hlt | heq' | hgt
        · exfalso
          have hss : (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁)) ⊂
              (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁)) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.trans hlt⟩, fun h => ?_⟩
            have hm : (v₁, u₁) ∈ (S.rightEdges H v₁).filter (fun e' =>
                heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu1, hadj1.symm⟩, rfl⟩, hlt⟩
            rw [← h] at hm; exact lt_irrefl _ (Finset.mem_filter.mp hm).2
          have := Finset.card_lt_card hss; omega
        · exact heq'
        · exfalso
          have hss : (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₂ - S.p v₁)) ⊂
              (S.rightEdges H v₁).filter (fun e' =>
              heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁)) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun e' he' => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he').1, (Finset.mem_filter.mp he').2.trans hgt⟩, fun h => ?_⟩
            have hm : (v₁, u₂) ∈ (S.rightEdges H v₁).filter (fun e' =>
                heading (S.p e'.2 - S.p v₁) < heading (S.p u₁ - S.p v₁)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu2, hadj2.symm⟩, rfl⟩, hgt⟩
            rw [← h] at hm; exact lt_irrefl _ (Finset.mem_filter.mp hm).2
          have := Finset.card_lt_card hss; omega
      have hsub : (⟨u₁, hadj1.symm⟩ : {x : Fin n // H.Adj v₁ x}) = ⟨u₂, hadj2.symm⟩ :=
        S.heading_inj_H H hHG v₁ hhead
      have hu : u₁ = u₂ := congrArg Subtype.val hsub
      exact Subtype.ext (Prod.ext hu rfl)
    · intro t ht
      simp only [Finset.mem_filter, F, Finset.mem_univ, true_and] at ht
      rcases ht with ⟨hcomp, v, hv, hr1, hr2⟩
      rcases t with ⟨i, r⟩; dsimp at hv hr1 hr2; subst hv
      let k := r.val - (S.passBelow H v).card
      have hk1 : 1 ≤ k := by omega
      have hk2 : k < (S.rightEdges H v).card := by omega
      let hs := (S.rightEdges H v).image (fun e => heading (S.p e.2 - S.p v))
      have hinjR : Set.InjOn (fun e : Fin n × Fin n => heading (S.p e.2 - S.p v)) ↑(S.rightEdges H v) := by
        intro e₁ h1 e₂ h2 heq
        have hR1 := Finset.mem_filter.mp h1; have hR2 := Finset.mem_filter.mp h2
        have ho1 := Finset.mem_filter.mp hR1.1; have ho2 := Finset.mem_filter.mp hR2.1
        have hsub : (⟨e₁.2, hR1.2 ▸ ho1.2.2⟩ : {x : Fin n // H.Adj v x}) = ⟨e₂.2, hR2.2 ▸ ho2.2.2⟩ :=
          S.heading_inj_H H hHG v heq
        exact Prod.ext (hR1.2.trans hR2.2.symm) (congrArg Subtype.val hsub)
      have hcardR : hs.card = (S.rightEdges H v).card := Finset.card_image_of_injOn hinjR
      let embR := hs.orderEmbOfFin hcardR
      obtain ⟨e, he_mem, he_h⟩ := Finset.mem_image.mp (hs.orderEmbOfFin_mem hcardR ⟨k, hk2⟩)
      obtain ⟨e0, he0_mem, he0_h⟩ := Finset.mem_image.mp (hs.orderEmbOfFin_mem hcardR ⟨0, by omega⟩)
      have hRe := Finset.mem_filter.mp he_mem
      have hoe := Finset.mem_filter.mp hRe.1
      have hve : v < e.2 := hRe.2 ▸ hoe.2.1
      have hadj_e : H.Adj e.2 v := (hRe.2 ▸ hoe.2.2).symm
      have hRe0 := Finset.mem_filter.mp he0_mem
      have hoe0 := Finset.mem_filter.mp hRe0.1
      have hadj_e0 : H.Adj v e0.2 := hRe0.2 ▸ hoe0.2.2
      have hlt0 : heading (S.p e0.2 - S.p v) < heading (S.p e.2 - S.p v) := by
        rw [he0_h, he_h]; exact embR.strictMono (show (⟨0, by omega⟩ : Fin _) < ⟨k, hk2⟩ from by change 0 < k; omega)
      have hmem_embR : ∀ e' ∈ S.rightEdges H v, ∃ j, embR j = heading (S.p e'.2 - S.p v) :=
        fun e' he' => Set.mem_range.mp (by rw [Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem _ he')
      have hrank_e : S.edgeRank H v.succ (v, e.2) = r.val := by
        rw [S.edgeRank_rightEdge H hHG hve hadj_e.symm]
        have hcnt : ((S.rightEdges H v).filter (fun e' =>
            heading (S.p e'.2 - S.p v) < heading (S.p e.2 - S.p v))).card = k := by
          have h1 : ((S.rightEdges H v).filter (fun e' =>
              heading (S.p e'.2 - S.p v) < heading (S.p e.2 - S.p v))).card =
              (Finset.range k).card := by
            refine Finset.card_bij
              (fun e' he' => (Classical.choose (hmem_embR e' (Finset.mem_filter.mp he').1)).val)
              ?_ ?_ ?_
            · intro e' he'
              have hsp := Classical.choose_spec (hmem_embR e' (Finset.mem_filter.mp he').1)
              rw [Finset.mem_range]
              have hlt : embR (Classical.choose (hmem_embR e' (Finset.mem_filter.mp he').1)) < embR ⟨k, hk2⟩ := by
                rw [hsp, ← he_h]; exact (Finset.mem_filter.mp he').2
              exact embR.lt_iff_lt.mp hlt
            · intro e₁ h1 e₂ h2 hval
              have hsp1 := Classical.choose_spec (hmem_embR e₁ (Finset.mem_filter.mp h1).1)
              have hsp2 := Classical.choose_spec (hmem_embR e₂ (Finset.mem_filter.mp h2).1)
              exact hinjR (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
                (hsp1.symm.trans ((congrArg embR (Fin.ext hval)).trans hsp2))
            · intro j hj
              rw [Finset.mem_range] at hj
              obtain ⟨e', he'm, he'h⟩ := Finset.mem_image.mp (hs.orderEmbOfFin_mem hcardR ⟨j, by omega⟩)
              refine ⟨e', Finset.mem_filter.mpr ⟨he'm, by rw [he'h, he_h]; exact embR.strictMono (by change j < k; exact hj)⟩, ?_⟩
              have hsp := Classical.choose_spec (hmem_embR e' he'm)
              exact congrArg Fin.val (embR.injective (hsp.trans he'h))
          rw [h1, Finset.card_range]
        omega
      let d : DartOf H := ⟨(e.2, v), hadj_e⟩
      have hreach := S.dartMap_to_target_right H hHG hve hadj_e
      have heq_t : (⟨v.succ, ⟨S.edgeRank H v.succ (v, e.2), by
            have hm : (v, e.2) ∈ S.activeEdges H v.succ :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hve, hadj_e.symm⟩, by simp, by simp; omega⟩
            exact Nat.lt_succ_of_lt (S.edgeRank_lt H hm)⟩⟩ : S.SlabVert H) = ⟨v.succ, r⟩ :=
        Sigma.ext rfl (heq_of_eq (Fin.ext hrank_e))
      refine ⟨d, ?_, heq_t⟩
      simp only [Finset.mem_filter, D_F, Finset.mem_univ, true_and]
      refine ⟨(SimpleGraph.ConnectedComponent.sound hreach).trans (by rw [heq_t]; exact hcomp),
        hve, fun hmin => not_lt.mpr (hmin e0.2 hadj_e0) hlt0⟩

  have hbij_cap : (D_F.filter (S.isRightCap H)).card = (F.filter isCapV).card := by
    refine Finset.card_bij
      (fun d hd =>
        have hpR := S.passBelow_add_right_le H hHG d.1.2
        ⟨d.1.2.succ, ⟨(S.passBelow H d.1.2).card, by omega⟩⟩)
      ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, D_F, F, Finset.mem_univ, true_and] at hd ⊢
      rcases hd with ⟨hcomp, huv, hmin⟩
      have hdR0 : (S.rightEdges H d.1.2).card = 0 := by
        unfold rightEdges
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he h1; simp only [orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have h1' := hmin e.2 (h1 ▸ he.2)
        have h2' := S.heading_right_lt_left (h1 ▸ he.1) huv; linarith
      have hu_mem : (d.1.1, d.1.2) ∈ S.leftEdges H d.1.2 :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, d.2⟩, rfl⟩
      have hdL1 : 1 ≤ (S.leftEdges H d.1.2).card := Finset.card_pos.mpr ⟨(d.1.1, d.1.2), hu_mem⟩
      have hru : S.edgeRank H d.1.2.castSucc (d.1.1, d.1.2) =
          (S.passBelow H d.1.2).card + (S.leftEdges H d.1.2).card - 1 := by
        rw [S.edgeRank_leftEdge H hHG huv d.2]
        have hfilt : (S.leftEdges H d.1.2).filter (fun e' =>
            heading (S.p d.1.1 - S.p d.1.2) < heading (S.p e'.1 - S.p d.1.2)) =
            (S.leftEdges H d.1.2).erase (d.1.1, d.1.2) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
          · rintro ⟨hne', he'⟩
            have hL' := Finset.mem_filter.mp he'; have ho' := Finset.mem_filter.mp hL'.1
            refine ⟨he', lt_of_le_of_ne (hmin e'.1 (hL'.2 ▸ ho'.2.2.symm)) (fun h => hne' ?_)⟩
            have hsub : (⟨d.1.1, d.2.symm⟩ : {x : Fin n // H.Adj d.1.2 x}) = ⟨e'.1, hL'.2 ▸ ho'.2.2.symm⟩ :=
              S.heading_inj_H H hHG d.1.2 h
            exact Prod.ext (congrArg Subtype.val hsub).symm hL'.2
        rw [hfilt, Finset.card_erase_of_mem hu_mem]
        omega
      have hreach := S.dartMap_to_target_left H hHG huv d.2
      have hglue : (S.slabGraph H).Adj
          ⟨d.1.2.castSucc, ⟨S.edgeRank H d.1.2.castSucc (d.1.1, d.1.2) + 1, by
            have hm : (d.1.1, d.1.2) ∈ S.activeEdges H d.1.2.castSucc :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, d.2⟩, by simpa, by simp⟩
            exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩
          ⟨d.1.2.succ, ⟨(S.passBelow H d.1.2).card, by have := S.passBelow_add_right_le H hHG d.1.2; omega⟩⟩ := by
        apply S.slabGraph_adj_step H d.1.2; right; dsimp; omega
      exact ⟨(SimpleGraph.ConnectedComponent.sound (hreach.trans hglue.reachable)).symm.trans hcomp,
        d.1.2, rfl, rfl, hdR0, hdL1⟩
    · intro d₁ h1 d₂ h2 heq
      have hv : d₁.1.2 = d₂.1.2 := Fin.succ_injective _ (congrArg Sigma.fst heq)
      rcases d₁ with ⟨⟨u₁, v₁⟩, hadj1⟩; rcases d₂ with ⟨⟨u₂, v₂⟩, hadj2⟩
      dsimp at hv; subst hv
      have hm1 := (Finset.mem_filter.mp h1).2.2
      have hm2 := (Finset.mem_filter.mp h2).2.2
      have hhead : heading (S.p u₁ - S.p v₁) = heading (S.p u₂ - S.p v₁) :=
        le_antisymm (hm1 u₂ hadj2.symm) (hm2 u₁ hadj1.symm)
      have hsub : (⟨u₁, hadj1.symm⟩ : {x : Fin n // H.Adj v₁ x}) = ⟨u₂, hadj2.symm⟩ :=
        S.heading_inj_H H hHG v₁ hhead
      have hu : u₁ = u₂ := congrArg Subtype.val hsub
      exact Subtype.ext (Prod.ext hu rfl)
    · intro t ht
      simp only [Finset.mem_filter, F, Finset.mem_univ, true_and] at ht
      rcases ht with ⟨hcomp, v, hv, hrp, hdR0, hdL1⟩
      rcases t with ⟨i, r⟩; dsimp at hv hrp hdR0; subst hv
      have hneL : (S.leftEdges H v).Nonempty := Finset.card_pos.mp hdL1
      obtain ⟨e, he_mem, he_min⟩ :=
        Finset.exists_min_image (S.leftEdges H v) (fun e => heading (S.p e.1 - S.p v)) hneL
      have hLe := Finset.mem_filter.mp he_mem
      have hoe := Finset.mem_filter.mp hLe.1
      have huv : e.1 < v := hLe.2 ▸ hoe.2.1
      have hadj : H.Adj e.1 v := hLe.2 ▸ hoe.2.2
      have hmin : S.isMinNeighbor H ⟨(e.1, v), hadj⟩ := by
        intro w hw
        have hwv : w < v := by
          rcases lt_or_gt_of_ne (H.ne_of_adj hw).symm with h | h
          · exact h
          · exfalso
            have : (v, w) ∈ S.rightEdges H v :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hw⟩, rfl⟩
            have := Finset.card_pos.mpr ⟨(v, w), this⟩; omega
        exact he_min (w, v) (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv, hw.symm⟩, rfl⟩)
      have hev_mem : (e.1, v) ∈ S.leftEdges H v :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, rfl⟩
      have hru : S.edgeRank H v.castSucc (e.1, v) =
          (S.passBelow H v).card + (S.leftEdges H v).card - 1 := by
        rw [S.edgeRank_leftEdge H hHG huv hadj]
        have hfilt : (S.leftEdges H v).filter (fun e' =>
            heading (S.p e.1 - S.p v) < heading (S.p e'.1 - S.p v)) = (S.leftEdges H v).erase (e.1, v) := by
          ext e'; simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨he', hlt'⟩; exact ⟨fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt', he'⟩
          · rintro ⟨hne', he'⟩
            have hL' := Finset.mem_filter.mp he'; have ho' := Finset.mem_filter.mp hL'.1
            refine ⟨he', lt_of_le_of_ne (hmin e'.1 (hL'.2 ▸ ho'.2.2.symm)) (fun h => hne' ?_)⟩
            have hsub : (⟨e.1, hadj.symm⟩ : {x : Fin n // H.Adj v x}) = ⟨e'.1, hL'.2 ▸ ho'.2.2.symm⟩ :=
              S.heading_inj_H H hHG v h
            exact Prod.ext (congrArg Subtype.val hsub).symm hL'.2
        rw [hfilt, Finset.card_erase_of_mem hev_mem]
        omega
      have hreach := S.dartMap_to_target_left H hHG huv hadj
      have hglue : (S.slabGraph H).Adj
          ⟨v.castSucc, ⟨S.edgeRank H v.castSucc (e.1, v) + 1, by
            have hm : (e.1, v) ∈ S.activeEdges H v.castSucc :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, by simpa, by simp⟩
            exact Nat.succ_lt_succ (S.edgeRank_lt H hm)⟩⟩
          ⟨v.succ, r⟩ := by
        apply S.slabGraph_adj_step H v; right; dsimp; omega
      refine ⟨⟨(e.1, v), hadj⟩, ?_, Sigma.ext rfl (heq_of_eq (Fin.ext hrp.symm))⟩
      simp only [Finset.mem_filter, D_F, Finset.mem_univ, true_and]
      exact ⟨(SimpleGraph.ConnectedComponent.sound (hreach.trans hglue.reachable)).trans hcomp, huv, hmin⟩
  rw [hbij_tip, hbij_cap]
  linarith

end Subgraph

private lemma squeeze_bijection (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G)
    (hconn : J.Connected) :
    haveI := Classical.decRel J.Adj
    numOrbits (S.geoPhi J hJ) + n = J.edgeFinset.card + 2 ∧
    Function.Bijective (S.orbitToComp J hJ) := by
  classical
  have hn : 2 ≤ n := by have := S.hn; omega
  haveI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Fintype.card_fin]
    omega)
  have hdeg (v : Fin n) : 1 ≤ (S.leftEdges J v).card + (S.rightEdges J v).card := by
    rw [S.leftEdges_add_rightEdges_eq_degree]
    exact hconn.preconnected.degree_pos_of_nontrivial v
  have hup : numOrbits (S.geoPhi J hJ) + n ≤ J.edgeFinset.card + 2 := by
    simpa only [Fintype.card_fin, geoPhi] using
      rotation_euler_upper J hconn (by simpa only [Fintype.card_fin] using hn)
        (S.geoSigma J hJ) (S.geoSigma_isCyclic J hJ)
  have hlow := S.slab_components_ge J hJ hdeg
  rw [S.orientEdges_card J] at hlow
  have hle := S.slab_components_le_orbits J hJ hdeg
  have hcard : Nat.card (S.slabGraph J).ConnectedComponent = numOrbits (S.geoPhi J hJ) := by omega
  refine ⟨by omega, ?_⟩
  apply (Nat.bijective_iff_surjective_and_card (S.orbitToComp J hJ)).mpr
  exact ⟨S.orbitToComp_surjective J hJ hdeg, hcard.symm⟩

private noncomputable def outerDarts (J : SimpleGraph (Fin n)) : Finset (DartOf J) := by
  classical
  exact Finset.univ.filter fun d =>
    (S.slabGraph J).connectedComponentMk (S.dartMap J d) =
      (S.slabGraph J).connectedComponentMk (S.outerVert J)

private lemma mem_outerDarts (J : SimpleGraph (Fin n)) (d : DartOf J) :
    d ∈ S.outerDarts J ↔
      (S.slabGraph J).connectedComponentMk (S.dartMap J d) =
        (S.slabGraph J).connectedComponentMk (S.outerVert J) := by
  classical
  simp [outerDarts]

private lemma outer_darts_orbit (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G)
    (hconn : J.Connected) :
    ∃ d ∈ S.outerDarts J, ∀ e, e ∈ S.outerDarts J ↔ sameOrbit (S.geoPhi J hJ) d e := by
  classical
  let c := (S.slabGraph J).connectedComponentMk (S.outerVert J)
  have hb := (S.squeeze_bijection J hJ hconn).2
  obtain ⟨q, hq⟩ := hb.2 c
  induction q using Quotient.ind with | _ d =>
  have hd : d ∈ S.outerDarts J := (S.mem_outerDarts J d).2 hq
  refine ⟨d, hd, fun e => ⟨?_, ?_⟩⟩
  · intro he
    exact Quotient.exact (hb.1 (hq.trans ((S.mem_outerDarts J e).1 he).symm))
  · intro he
    apply (S.mem_outerDarts J e).2
    exact (congrArg (S.orbitToComp J hJ) (Quotient.sound he)).symm.trans hq

private lemma outer_angle_lower_of_edge (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G)
    (he : ∃ a b, J.Adj a b) :
    ((S.outerDarts J).card + 2 : ℝ) * Real.pi ≤
      ∑ d ∈ S.outerDarts J, S.gapAngle J hJ d := by
  classical
  have hinv (d : DartOf J) (hd : d ∈ S.outerDarts J) :
      S.geoPhi J hJ d ∈ S.outerDarts J := by
    apply (S.mem_outerDarts J _).2
    exact (SimpleGraph.ConnectedComponent.sound (S.dartMap_phi_reachable J hJ d)).symm.trans
      ((S.mem_outerDarts J d).1 hd)
  rw [S.invariant_set_angle_sum J hJ _ hinv]
  let c := (S.slabGraph J).connectedComponentMk (S.outerVert J)
  let F := Finset.univ.filter fun t => (S.slabGraph J).connectedComponentMk t = c
  have ht := S.component_turning_identity J hJ c
  have hf := S.slab_outer_component_V_le_E J hJ he
  have hF : F = Finset.univ.filter (fun t => (S.slabGraph J).Reachable (S.outerVert J) t) := by
    ext t
    simp [F, c, SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
  have hmem : S.outerVert J ∈ F := by simp [F, c]
  change ((S.outerDarts J).filter (S.isLeftTip J)).card -
      (((S.outerDarts J).filter (S.isRightCap J)).card : ℤ) =
        (F.card : ℤ) - (∑ t ∈ F, (S.slabInEdges J t).card : ℕ) -
          (if S.outerVert J ∈ F then 1 else 0) at ht
  rw [if_pos hmem, hF] at ht
  dsimp only at hf
  have hturn : ((S.outerDarts J).filter (S.isLeftTip J)).card -
      (((S.outerDarts J).filter (S.isRightCap J)).card : ℤ) ≤ -1 := by omega
  have hreal : ((S.outerDarts J).filter (S.isLeftTip J)).card -
      (((S.outerDarts J).filter (S.isRightCap J)).card : ℝ) ≤ -1 := by exact_mod_cast hturn
  nlinarith [Real.pi_pos]

private lemma outer_angle_lower (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G)
    (hdeg : ∀ v, 1 ≤ (S.leftEdges J v).card + (S.rightEdges J v).card) :
    ((S.outerDarts J).card + 2 : ℝ) * Real.pi ≤
      ∑ d ∈ S.outerDarts J, S.gapAngle J hJ d :=
  S.outer_angle_lower_of_edge J hJ (S.exists_edge_of_slab_degree J hdeg)

private lemma cwPred_restrict {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → ℝ) (hf : Function.Injective f)
    (e : B → A) (he : Function.Injective e) (a b : B)
    (hb : e b = cwPredPerm f hf (e a)) :
    e (cwPredPerm (f ∘ e) (hf.comp he) a) = cwPredPerm f hf (e a) := by
  have hA := cwPredPerm_spec f hf (e a)
  have hB := cwPredPerm_spec (f ∘ e) (hf.comp he) a
  simp only [Function.comp_apply] at hB
  rcases hA with ⟨hmin, hmax⟩ | ⟨hdec, hgap⟩
  · rcases hB with ⟨_, hmax'⟩ | ⟨hdec', _⟩
    · apply hf
      refine le_antisymm (hmax _) ?_
      rw [← hb]
      exact hmax' b
    · exact ((not_lt_of_ge (hmin _)) hdec').elim
  · rcases hB with ⟨hmin', _⟩ | ⟨hdec', hgap'⟩
    · exact ((not_lt_of_ge (hmin' b)) (hb.symm ▸ hdec)).elim
    · apply hf
      apply le_antisymm
      · by_contra! h
        exact (not_le_of_gt hdec') (hgap _ h)
      · by_contra! h
        rw [← hb] at h hdec
        exact (not_le_of_gt hdec) (hgap' b h)

open Classical in
private lemma face_corners_inj (hconn : S.G.Connected) (v u : Fin n) (hu : S.G.Adj v u)
    (hcut : (S.G.induce {w | w ≠ v}).Connected) :
    let φ := S.geoPhi S.G le_rfl
    Function.Injective (fun a : {w : Fin n // S.G.Adj v w} =>
      (Quotient.mk (orbitSetoid φ) ⟨(a.1, v), a.property.symm⟩)) := by
  classical
  let φ := S.geoPhi S.G le_rfl
  let J := S.G.keepLeaf v u
  have hJ : J ≤ S.G := S.G.keepLeaf_le v u
  let ψ := S.geoPhi J hJ
  let Q := Quotient (orbitSetoid φ)
  let Q' := Quotient (orbitSetoid ψ)
  letI : Fintype Q := Fintype.ofFinite _
  letI : Fintype Q' := Fintype.ofFinite _
  let face : DartOf S.G → Q := Quotient.mk _
  let face' : DartOf J → Q' := Quotient.mk _
  let corner (a : {w : Fin n // S.G.Adj v w}) : Q := face ⟨(a.val, v), a.property.symm⟩
  let inc : DartOf J ↪ DartOf S.G :=
    ⟨fun d => ⟨d.val, hJ d.property⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun d : DartOf S.G => d.val) h)⟩
  have hφ (a b : DartOf S.G) : face a = face b ↔ ∃ k : ℕ, (φ ^ k) a = b :=
    ⟨fun h => show sameOrbit φ a b from Quotient.exact h,
      fun h => Quotient.sound (show sameOrbit φ a b from h)⟩
  have hψ (a b : DartOf J) : face' a = face' b ↔ ∃ k : ℕ, (ψ ^ k) a = b :=
    ⟨fun h => show sameOrbit ψ a b from Quotient.exact h,
      fun h => Quotient.sound (show sameOrbit ψ a b from h)⟩
  have hcorner (d : DartOf S.G) (hd : d.val.2 = v) : face d ∈ Set.range corner := by
    rcases d with ⟨⟨a, b⟩, hab⟩
    change b = v at hd
    subst b
    exact ⟨⟨a, hab.symm⟩, rfl⟩
  have hcover (d : DartOf S.G) (hd : face d ∉ Set.range corner) : d ∈ Set.range inc := by
    have hh : d.val.2 ≠ v := fun h => hd (hcorner d h)
    have ht : d.val.1 ≠ v := by
      intro h
      have hprev := hcorner (φ.symm d) h
      have he := (hφ (φ.symm d) d).2 ⟨1, by simp⟩
      exact hd (he ▸ hprev)
    exact ⟨⟨d.val, S.G.keepLeaf_of_ne ht hh d.property⟩, Subtype.ext rfl⟩
  have hstep (d : DartOf J) (hd : face (inc d) ∉ Set.range corner) :
      inc (ψ d) = φ (inc d) := by
    have hh : d.val.2 ≠ v := fun h => hd (hcorner (inc d) h)
    have ht : (φ (inc d)).val.2 ≠ v := by
      intro h
      have he := (hφ (inc d) _).2 (sameOrbit_step φ (inc d))
      exact hd (he.symm ▸ hcorner _ h)
    let a : {w : Fin n // J.Adj d.val.2 w} := ⟨d.val.1, d.property.symm⟩
    let e (w : {w : Fin n // J.Adj d.val.2 w}) : {w : Fin n // S.G.Adj d.val.2 w} :=
      ⟨w.val, hJ w.property⟩
    let b := S.geoSigma S.G le_rfl d.val.2 (e a)
    let b' : {w : Fin n // J.Adj d.val.2 w} :=
      ⟨b.val, S.G.keepLeaf_of_ne hh ht b.property⟩
    have he : Function.Injective e := fun _ _ h =>
      Subtype.ext (congrArg (fun w : {w : Fin n // S.G.Adj d.val.2 w} => w.val) h)
    have eq := S.cwPred_restrict (fun w : {w : Fin n // S.G.Adj d.val.2 w} =>
      heading (S.p w.val - S.p d.val.2)) (S.heading_inj_H S.G le_rfl d.val.2) e he a b' (by rfl)
    exact Subtype.ext (Prod.ext rfl (congrArg Subtype.val eq))
  have hhit : ∃ d : DartOf J, face (inc d) ∈ Set.range corner :=
    ⟨⟨(u, v), (S.G.keepLeaf_edge v u hu).symm⟩, ⟨⟨u, hu⟩, rfl⟩⟩
  have hA := (S.squeeze_bijection S.G le_rfl hconn).1
  have hB := (S.squeeze_bijection J hJ (S.G.keepLeaf_connected hu hcut)).1
  change Nat.card Q + n = S.G.edgeFinset.card + 2 at hA
  change Nat.card Q' + n = J.edgeFinset.card + 2 at hB
  rw [Nat.card_eq_fintype_card] at hA hB
  have hE : J.edgeFinset.card + S.G.degree v = S.G.edgeFinset.card + 1 :=
    S.G.keepLeaf_card hu
  have hdegree : Fintype.card {w : Fin n // S.G.Adj v w} = S.G.degree v :=
    S.G.card_neighborSet_eq_degree v
  apply Swanepoel.corners_injective_of_delete φ ψ inc face face' corner
    Quotient.mk_surjective hφ hψ hcover hstep hhit
  omega

private lemma outer_dest_inj (hconn : S.G.Connected)
    (hcut : ∀ v, (S.G.induce {w | w ≠ v}).Connected) :
    Set.InjOn (fun d : DartOf S.G => d.val.2) (S.outerDarts S.G : Set (DartOf S.G)) := by
  classical
  obtain ⟨base, _, hbase⟩ := S.outer_darts_orbit S.G le_rfl hconn
  rintro ⟨⟨a, v⟩, ha⟩ hd ⟨⟨b, w⟩, hb⟩ he (h : v = w)
  subst w
  have ha' := (hbase ⟨(a, v), ha⟩).1 (Finset.mem_coe.mp hd)
  have hb' := (hbase ⟨(b, v), hb⟩).1 (Finset.mem_coe.mp he)
  let φ := S.geoPhi S.G le_rfl
  let face := Quotient.mk (orbitSetoid φ)
  have ha'' : face base = face ⟨(a, v), ha⟩ := Quotient.sound ha'
  have hb'' : face base = face ⟨(b, v), hb⟩ := Quotient.sound hb'
  have hab := ha''.symm.trans hb''
  have key := S.face_corners_inj hconn v a ha.symm (hcut v)
    (a₁ := ⟨a, ha.symm⟩) (a₂ := ⟨b, hb.symm⟩) hab
  exact Subtype.ext (Prod.ext (congrArg (fun e : {w : Fin n // S.G.Adj v w} => e.val) key) rfl)

private lemma outer_index (hconn : S.G.Connected)
    (hcut : ∀ v, (S.G.induce {w | w ≠ v}).Connected) :
    ∃ e : Fin (S.outerDarts S.G).card ≃ ↥(S.outerDarts S.G),
      Function.Injective (fun i => (e i).val.val.2) ∧
      (∀ i, (e (finRotate (S.outerDarts S.G).card i)).val =
        S.geoPhi S.G le_rfl (e i).val) := by
  classical
  let D := S.outerDarts S.G
  let f := S.geoPhi S.G le_rfl
  obtain ⟨b, hb, h⟩ := S.outer_darts_orbit S.G le_rfl hconn
  have hc : f.IsCycleOn (D : Set (DartOf S.G)) := by
    refine ⟨⟨?_, f.injective.injOn, ?_⟩, ?_⟩
    · intro x hx
      exact (h _).2 (sameOrbit_trans f ((h _).1 hx) (sameOrbit_step f x))
    · intro x hx
      have hstep : sameOrbit f (f.symm x) x := ⟨1, by simp⟩
      exact ⟨f.symm x, (h _).2 (sameOrbit_trans f ((h _).1 hx) (sameOrbit_symm f hstep)),
        f.apply_symm_apply x⟩
    · intro x hx y hy
      obtain ⟨k, hk⟩ := sameOrbit_trans f (sameOrbit_symm f ((h _).1 hx)) ((h _).1 hy)
      exact ⟨k, by simpa only [zpow_natCast] using hk⟩
  obtain ⟨e, he⟩ := Swanepoel.index_cycle hc b hb
  refine ⟨e, ?_, he⟩
  intro i j hij
  exact e.injective (Subtype.ext (S.outer_dest_inj hconn hcut (e i).property (e j).property hij))

open Classical in
private lemma gap_excess_le_interior (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G) (v : Fin n)
    (a : {w : Fin n // J.Adj v w}) (T : Finset {w : Fin n // J.Adj v w})
    (ha : a ∉ T) :
    ∑ b ∈ T, (S.gapAngle J hJ ⟨(b.val, v), b.property.symm⟩ - Real.pi / 3) ≤
      2 * Real.pi - S.gapAngle J hJ ⟨(a.val, v), a.property.symm⟩ -
        ((Fintype.card {w : Fin n // J.Adj v w} : ℝ) - 1) * (Real.pi / 3) := by
  classical
  let f (b : {w : Fin n // J.Adj v w}) :=
    S.gapAngle J hJ ⟨(b.val, v), b.property.symm⟩ - Real.pi / 3
  have hsub : T ⊆ Finset.univ.erase a := fun b hb =>
    Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hb), Finset.mem_univ _⟩
  have hnonneg (b : {w : Fin n // J.Adj v w}) : 0 ≤ f b :=
    sub_nonneg.mpr (S.gapAngle_ge_pi_div_three J hJ _)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => hnonneg b)
  have hsum : (∑ b, f b) = 2 * Real.pi -
      (Fintype.card {w : Fin n // J.Adj v w} : ℝ) * (Real.pi / 3) := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [S.gapAngle_sum_at_vertex J hJ v ⟨a.val, a.property⟩]
  have he := Finset.sum_erase_add (Finset.univ : Finset {w : Fin n // J.Adj v w})
    f (Finset.mem_univ a)
  change (∑ b ∈ T, f b) ≤ _
  dsimp [f] at he
  have hfa : f a =
      S.gapAngle J hJ ⟨(a.val, v), a.property.symm⟩ - Real.pi / 3 := rfl
  change (∑ b ∈ Finset.univ.erase a, f b) + f a = ∑ b, f b at he
  linarith only [hle, hsum, he, hfa]

private noncomputable def retainedBelow (J H : SimpleGraph (Fin n))
    (i : Fin (n + 1)) (r : ℕ) : Finset (Fin n × Fin n) :=
  (S.activeEdges J i).filter fun e => S.edgeRank H i e < r

private noncomputable def retainedAbove (J H : SimpleGraph (Fin n))
    (i : Fin (n + 1)) (r : ℕ) : Finset (Fin n × Fin n) :=
  (S.activeEdges J i).filter fun e => ¬ S.edgeRank H i e < r

private lemma retained_active_mono {J H : SimpleGraph (Fin n)} (hJH : J ≤ H)
    {i : Fin (n + 1)} {e : Fin n × Fin n} (he : e ∈ S.activeEdges J i) :
    e ∈ S.activeEdges H i := by
  simp only [activeEdges, orientEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨⟨he.1.1, hJH he.1.2⟩, he.2⟩

private lemma retained_active_even (J : SimpleGraph (Fin n))
    (hdeg : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    (i : Fin (n + 1)) : (S.activeEdges J i).card % 2 = 0 := by
  induction i using Fin.induction with
  | zero => simp [S.activeEdges_zero J]
  | succ v ih =>
    have hstep := S.activeEdges_card_step J v
    have hv := hdeg v
    omega

private lemma retained_pass_between (J : SimpleGraph (Fin n)) (v : Fin n)
    {e : Fin n × Fin n} (hp : e ∈ S.passEdges H v) :
    e ∈ S.activeEdges J v.castSucc ↔ e ∈ S.activeEdges J v.succ := by
  have h := (Finset.mem_filter.mp hp).2
  simp only [activeEdges, Finset.mem_filter, Fin.val_castSucc, Fin.val_succ]
  have hl : e.1.val < v.val := h.1
  have hr : v.val < e.2.val := h.2
  constructor <;> intro he <;> exact ⟨he.1, by omega, by omega⟩

private lemma retained_rank_castSucc_cases (hHG : H ≤ S.G) (v : Fin n)
    {e : Fin n × Fin n} (he : e ∈ S.activeEdges H v.castSucc) :
    e ∈ S.passBelow H v ∨ e ∈ S.passAbove H v ∨
      (S.passBelow H v).card ≤ S.edgeRank H v.castSucc e ∧
      S.edgeRank H v.castSucc e < (S.passBelow H v).card + (S.leftEdges H v).card := by
  classical
  rw [(S.activeEdges_castSucc_eq H v).1, (S.passEdges_partition H hHG v).1,
    Finset.mem_union, Finset.mem_union] at he
  rcases he with (hb | ha) | hl
  · exact Or.inl hb
  · exact Or.inr (Or.inl ha)
  · have h := Finset.mem_filter.mp hl
    have ho := Finset.mem_filter.mp h.1
    obtain ⟨_, hv⟩ := h
    subst_vars
    rw [S.edgeRank_leftEdge H hHG ho.2.1 ho.2.2]
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    have hlt : ((S.leftEdges H e.2).filter (fun e' =>
        heading (S.p e.1 - S.p e.2) < heading (S.p e'.1 - S.p e.2))).card <
        (S.leftEdges H e.2).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have hm := hl
      rw [← heq] at hm
      exact lt_irrefl _ (Finset.mem_filter.mp hm).2
    omega

private lemma retained_rank_succ_cases (hHG : H ≤ S.G) (v : Fin n)
    {e : Fin n × Fin n} (he : e ∈ S.activeEdges H v.succ) :
    e ∈ S.passBelow H v ∨ e ∈ S.passAbove H v ∨
      (S.passBelow H v).card ≤ S.edgeRank H v.succ e ∧
      S.edgeRank H v.succ e < (S.passBelow H v).card + (S.rightEdges H v).card := by
  classical
  rw [(S.activeEdges_succ_eq H v).1, (S.passEdges_partition H hHG v).1,
    Finset.mem_union, Finset.mem_union] at he
  rcases he with (hb | ha) | hr
  · exact Or.inl hb
  · exact Or.inr (Or.inl ha)
  · have h := Finset.mem_filter.mp hr
    have ho := Finset.mem_filter.mp h.1
    obtain ⟨_, hv⟩ := h
    subst_vars
    rw [S.edgeRank_rightEdge H hHG ho.2.1 ho.2.2]
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    have hlt : ((S.rightEdges H e.1).filter (fun e' =>
        heading (S.p e'.2 - S.p e.1) < heading (S.p e.2 - S.p e.1))).card <
        (S.rightEdges H e.1).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have hm := hr
      rw [← heq] at hm
      exact lt_irrefl _ (Finset.mem_filter.mp hm).2
    omega

private lemma retainedBelow_glue_lower (J : SimpleGraph (Fin n))
    (hJH : J ≤ H) (hHG : H ≤ S.G) (v : Fin n) (r : ℕ)
    (hr : r ≤ (S.passBelow H v).card) :
    S.retainedBelow J H v.castSucc r = S.retainedBelow J H v.succ r := by
  ext e
  simp only [retainedBelow, Finset.mem_filter]
  constructor <;> rintro ⟨he, hlt⟩
  · rcases S.retained_rank_castSucc_cases (H := H) (hHG := hHG) (v := v)
      (S.retained_active_mono hJH he) with hb | ha | hm
    · have hk := (S.edgeRank_passBelow H hHG hb).2
      exact ⟨(S.retained_pass_between (H := H) (J := J) (v := v)
        (Finset.mem_filter.mp hb).1).mp he, by omega⟩
    · have hk := (S.edgeRank_passAbove H hHG ha).1
      omega
    · omega
  · rcases S.retained_rank_succ_cases (H := H) (hHG := hHG) (v := v)
      (S.retained_active_mono hJH he) with hb | ha | hm
    · have hk := (S.edgeRank_passBelow H hHG hb).2
      exact ⟨(S.retained_pass_between (H := H) (J := J) (v := v)
        (Finset.mem_filter.mp hb).1).mpr he, by omega⟩
    · obtain ⟨hk, hs⟩ := S.edgeRank_passAbove H hHG ha
      omega
    · omega

private lemma retainedAbove_glue_upper (J : SimpleGraph (Fin n))
    (hJH : J ≤ H) (hHG : H ≤ S.G) (v : Fin n) (r₁ r₂ : ℕ)
    (hr : (S.passBelow H v).card + (S.leftEdges H v).card ≤ r₁)
    (hs : r₂ + (S.leftEdges H v).card = r₁ + (S.rightEdges H v).card) :
    S.retainedAbove J H v.castSucc r₁ = S.retainedAbove J H v.succ r₂ := by
  ext e
  simp only [retainedAbove, Finset.mem_filter]
  constructor <;> rintro ⟨he, hge⟩
  · rcases S.retained_rank_castSucc_cases (H := H) (hHG := hHG) (v := v)
      (S.retained_active_mono hJH he) with hb | ha | hm
    · have hk := (S.edgeRank_passBelow H hHG hb).1
      omega
    · have hk := (S.edgeRank_passAbove H hHG ha).2
      exact ⟨(S.retained_pass_between (H := H) (J := J) (v := v)
        (Finset.mem_filter.mp ha).1).mp he, by omega⟩
    · omega
  · rcases S.retained_rank_succ_cases (H := H) (hHG := hHG) (v := v)
      (S.retained_active_mono hJH he) with hb | ha | hm
    · obtain ⟨hk, ht⟩ := S.edgeRank_passBelow H hHG hb
      omega
    · have hk := (S.edgeRank_passAbove H hHG ha).2
      exact ⟨(S.retained_pass_between (H := H) (J := J) (v := v)
        (Finset.mem_filter.mp ha).1).mpr he, by omega⟩
    · omega

private lemma retainedBelow_parity_eq_above (J : SimpleGraph (Fin n))
    (hdeg : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    (i : Fin (n + 1)) (r : ℕ) :
    (S.retainedBelow J H i r).card % 2 = (S.retainedAbove J H i r).card % 2 := by
  have he := S.retained_active_even (J := J) hdeg i
  have hp : (S.retainedBelow J H i r).card + (S.retainedAbove J H i r).card =
      (S.activeEdges J i).card := by
    unfold retainedBelow retainedAbove
    exact Finset.card_filter_add_card_filter_not _
  omega

private lemma retainedBelow_parity_glue (J : SimpleGraph (Fin n))
    (hJH : J ≤ H) (hHG : H ≤ S.G)
    (hdeg : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    (v : Fin n) (r₁ : Fin ((S.activeEdges H v.castSucc).card + 1))
    (r₂ : Fin ((S.activeEdges H v.succ).card + 1)) (hg : S.slabGlueAcross H v r₁ r₂) :
    (S.retainedBelow J H v.castSucc r₁.val).card % 2 =
      (S.retainedBelow J H v.succ r₂.val).card % 2 := by
  rcases hg with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · rw [hs, S.retainedBelow_glue_lower (H := H) (J := J) hJH hHG v _ hr]
  · rw [S.retainedBelow_parity_eq_above (H := H) (J := J) hdeg,
      S.retainedBelow_parity_eq_above (H := H) (J := J) hdeg,
      S.retainedAbove_glue_upper (H := H) (J := J) hJH hHG v _ _ hr hs]

private lemma retainedBelow_parity_adj (J : SimpleGraph (Fin n))
    (hJH : J ≤ H) (hHG : H ≤ S.G)
    (hdeg : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    {x y : S.SlabVert H} (h : (S.slabGraph H).Adj x y) :
    (S.retainedBelow J H x.1 x.2.val).card % 2 =
      (S.retainedBelow J H y.1 y.2.val).card % 2 := by
  obtain ⟨i, r⟩ := x
  obtain ⟨j, s⟩ := y
  rcases h with ⟨v, hi, hj, hg⟩ | ⟨v, hj, hi, hg⟩
  · dsimp only at hi hj
    subst i j
    exact S.retainedBelow_parity_glue (H := H) (J := J) hJH hHG hdeg v r s hg
  · dsimp only at hi hj
    subst i j
    exact (S.retainedBelow_parity_glue (H := H) (J := J) hJH hHG hdeg v s r hg).symm

private lemma retainedBelow_parity_reachable (J : SimpleGraph (Fin n))
    (hJH : J ≤ H) (hHG : H ≤ S.G)
    (hdeg : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    {x y : S.SlabVert H} (h : (S.slabGraph H).Reachable x y) :
    (S.retainedBelow J H x.1 x.2.val).card % 2 =
      (S.retainedBelow J H y.1 y.2.val).card % 2 := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hab _ ih =>
      exact (S.retainedBelow_parity_adj (H := H) (J := J) hJH hHG hdeg hab).trans ih

private lemma retainedBelow_parity_outer (J : SimpleGraph (Fin n))
    (hJH : J ≤ H) (hHG : H ≤ S.G)
    (hdeg : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    {x : S.SlabVert H} (h : (S.slabGraph H).Reachable (S.outerVert H) x) :
    (S.retainedBelow J H x.1 x.2.val).card % 2 = 0 := by
  have hp := S.retainedBelow_parity_reachable (H := H) (J := J) hJH hHG hdeg h
  simpa [outerVert, retainedBelow, S.activeEdges_zero J] using hp.symm

private lemma retained_degree_even (J : SimpleGraph (Fin n))
    (hdeg : haveI := Classical.decRel J.Adj; ∀ v, J.degree v % 2 = 0) :
    ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0 := by
  classical
  intro v
  rw [S.leftEdges_add_rightEdges_eq_degree J v]
  exact hdeg v

private lemma edgeRank_lt_iff_edgeY_lt {i : Fin (n + 1)} {a b : Fin n × Fin n}
    (ha : a ∈ S.activeEdges H i) :
    S.edgeRank H i a < S.edgeRank H i b ↔
      edgeY S.p a.1 a.2 (S.slabMid i) < edgeY S.p b.1 b.2 (S.slabMid i) := by
  classical
  unfold edgeRank
  constructor
  · intro hr
    by_contra! hy
    have hc := Finset.card_le_card (show
        ((S.activeEdges H i).filter (fun c =>
          edgeY S.p c.1 c.2 (S.slabMid i) < edgeY S.p b.1 b.2 (S.slabMid i))) ⊆
        ((S.activeEdges H i).filter (fun c =>
          edgeY S.p c.1 c.2 (S.slabMid i) < edgeY S.p a.1 a.2 (S.slabMid i))) from by
      intro c hc
      obtain ⟨hca, hcb⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hca, hcb.trans_le hy⟩)
    omega
  · intro hy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, fun heq => ?_⟩
    · intro c hc
      obtain ⟨hca, hcb⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hca, hcb.trans hy⟩
    have hm : a ∈ (S.activeEdges H i).filter (fun c =>
        edgeY S.p c.1 c.2 (S.slabMid i) < edgeY S.p b.1 b.2 (S.slabMid i)) :=
      Finset.mem_filter.mpr ⟨ha, hy⟩
    rw [← heq] at hm
    exact lt_irrefl _ (Finset.mem_filter.mp hm).2

private lemma retainedBelow_at_edge (J : SimpleGraph (Fin n)) (hJH : J ≤ H)
    {i : Fin (n + 1)} {e : Fin n × Fin n} (he : e ∈ S.activeEdges J i) :
    S.retainedBelow J H i (S.edgeRank H i e) =
      S.retainedBelow J J i (S.edgeRank J i e) := by
  ext a
  simp only [retainedBelow, Finset.mem_filter]
  by_cases ha : a ∈ S.activeEdges J i
  · simp only [ha, true_and]
    have haH := S.retained_active_mono hJH ha
    have heH := S.retained_active_mono hJH he
    exact (S.edgeRank_lt_iff_edgeY_lt (H := H) (b := e) haH).trans
      (S.edgeRank_lt_iff_edgeY_lt (H := J) (b := e) ha).symm
  · simp [ha]

private lemma retainedBelow_self_at_edge (J : SimpleGraph (Fin n))
    {i : Fin (n + 1)} {e : Fin n × Fin n} :
    (S.retainedBelow J J i (S.edgeRank J i e)).card = S.edgeRank J i e := by
  classical
  unfold edgeRank at ⊢
  congr 1
  ext a
  simp only [retainedBelow, Finset.mem_filter]
  by_cases ha : a ∈ S.activeEdges J i
  · simp only [ha, true_and]
    exact S.edgeRank_lt_iff_edgeY_lt (H := J) ha
  · simp [ha]

private lemma retainedBelow_succ_at_edge (J : SimpleGraph (Fin n)) (hJH : J ≤ H)
    (hHG : H ≤ S.G) {i : Fin (n + 1)} {e : Fin n × Fin n} (he : e ∈ S.activeEdges J i) :
    S.retainedBelow J H i (S.edgeRank H i e + 1) =
      insert e (S.retainedBelow J H i (S.edgeRank H i e)) := by
  classical
  have heH := S.retained_active_mono hJH he
  ext a
  simp only [retainedBelow, Finset.mem_filter, Finset.mem_insert]
  by_cases h : a = e
  · subst a
    simp [he]
  by_cases ha : a ∈ S.activeEdges J i
  · have haH := S.retained_active_mono hJH ha
    have hne : S.edgeRank H i a ≠ S.edgeRank H i e := by
      intro eq
      have ma := S.slabMid_between H haH
      have me := S.slabMid_between H heH
      have oa := (Finset.mem_filter.mp (Finset.mem_filter.mp haH).1).2
      have oe := (Finset.mem_filter.mp (Finset.mem_filter.mp heH).1).2
      rcases lt_or_gt_of_ne
        (S.edgeY_ne_of_ne_edges oa.1 oe.1 (hHG oa.2) (hHG oe.2) h ma.1 ma.2 me.1 me.2) with lt | gt
      · exact (ne_of_lt ((S.edgeRank_lt_iff_edgeY_lt (H := H) haH).mpr lt)) eq
      · exact (ne_of_gt ((S.edgeRank_lt_iff_edgeY_lt (H := H) heH).mpr gt)) eq
    simp only [h, ha, false_or, true_and]
    omega
  · simp [ha, h]

private lemma retainedBelow_succ_card (J : SimpleGraph (Fin n)) (hJH : J ≤ H)
    (hHG : H ≤ S.G) {i : Fin (n + 1)} {e : Fin n × Fin n} (he : e ∈ S.activeEdges J i) :
    (S.retainedBelow J H i (S.edgeRank H i e + 1)).card =
      (S.retainedBelow J H i (S.edgeRank H i e)).card + 1 := by
  classical
  rw [S.retainedBelow_succ_at_edge (H := H) J hJH hHG he, Finset.card_insert_of_notMem]
  simp [retainedBelow]

private lemma retained_parity_dartMap (J : SimpleGraph (Fin n)) (hJH : J ≤ H)
    (hHG : H ≤ S.G) (d : DartOf J) :
    let d' : DartOf H := ⟨d.val, hJH d.property⟩
    let t := S.dartMap H d'
    (S.retainedBelow J H t.1 t.2.val).card = (S.dartMap J d).2.val := by
  classical
  rcases d with ⟨⟨u, v⟩, hd⟩
  intro d' t
  rcases lt_or_gt_of_ne (J.ne_of_adj hd) with huv | hvu
  · have he : (u,v) ∈ S.activeEdges J u.succ := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hd⟩, by simp, by simp; omega⟩
    dsimp [t, d']
    rw [S.dartMap_at_source_right H huv (hJH hd), S.dartMap_at_source_right J huv hd]
    dsimp only
    rw [S.retainedBelow_succ_card (H := H) J hJH hHG he, S.retainedBelow_at_edge (H := H) J hJH he,
      S.retainedBelow_self_at_edge J]
  · have he : (v,u) ∈ S.activeEdges J u.castSucc := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, hd.symm⟩, by simpa, by simp⟩
    dsimp [t, d']
    rw [S.dartMap_at_source_left H hvu (hJH hd), S.dartMap_at_source_left J hvu hd]
    dsimp only
    rw [S.retainedBelow_at_edge (H := H) J hJH he, S.retainedBelow_self_at_edge J]
section AngleComponents
variable (H : SimpleGraph (Fin n))

omit S in
private lemma cis_heading_of_unit {z : ℂ} (hz : ‖z‖ = 1) :
    Swanepoel.ChainStep.cis (heading z) = z := by
  have hn : z ≠ 0 := by rintro rfl; simp at hz
  apply Complex.ext
  · rw [Swanepoel.ChainStep.cis_re, cos_heading hn, hz, div_one]
  · rw [Swanepoel.ChainStep.cis_im, sin_heading hn, hz, div_one]

private lemma cis_gapAngle (hHG : H ≤ S.G) (v : Fin n) (a : {w : Fin n // H.Adj v w}) :
    (S.p (S.geoSigma H hHG v a).val - S.p v) *
      Swanepoel.ChainStep.cis (S.gapAngle H hHG ⟨(a.val, v), a.property.symm⟩) =
      (S.p a.val - S.p v) := by
  classical
  let b := S.geoSigma H hHG v a
  let x := S.p a.val - S.p v
  let y := S.p b.val - S.p v
  let d : DartOf H := ⟨(a.val, v), a.property.symm⟩
  have hx : ‖x‖ = 1 := hHG a.property.symm
  have hy : ‖y‖ = 1 := hHG b.property.symm
  change y * Swanepoel.ChainStep.cis (S.gapAngle H hHG d) = x
  have he : Swanepoel.ChainStep.cis (S.gapAngle H hHG d) =
      Swanepoel.ChainStep.cis (heading x - heading y) := by
    change Swanepoel.ChainStep.cis (heading x - heading y +
      (if S.isMinNeighbor H d then 2 * Real.pi else 0)) = _
    split_ifs
    · rw [Swanepoel.ChainStep.cis_add, show Swanepoel.ChainStep.cis (2 * Real.pi) = 1 by
        apply Complex.ext <;> simp [Swanepoel.ChainStep.cis_re, Swanepoel.ChainStep.cis_im], mul_one]
    · rw [add_zero]
  rw [he]
  calc
    y * Swanepoel.ChainStep.cis (heading x - heading y) =
        Swanepoel.ChainStep.cis (heading y) *
          Swanepoel.ChainStep.cis (heading x - heading y) :=
      congrArg (· * Swanepoel.ChainStep.cis (heading x - heading y)) (cis_heading_of_unit hy).symm
    _ = x := by
      rw [← Swanepoel.ChainStep.cis_add, show heading y + (heading x - heading y) = heading x by ring]
      exact cis_heading_of_unit hx

private lemma gapAngle_lt_two_pi (hHG : H ≤ S.G) (v : Fin n)
    (a : {w : Fin n // H.Adj v w}) (hne : S.geoSigma H hHG v a ≠ a) :
    S.gapAngle H hHG ⟨(a.val, v), a.property.symm⟩ < 2 * Real.pi := by
  classical
  let b := S.geoSigma H hHG v a
  let f (u : {w : Fin n // H.Adj v w}) := heading (S.p u.val - S.p v)
  let d : DartOf H := ⟨(a.val, v), a.property.symm⟩
  change f a - f b + (if S.isMinNeighbor H d then 2 * Real.pi else 0) < 2 * Real.pi
  have hbound (u : {w : Fin n // H.Adj v w}) : -(Real.pi / 2) < f u ∧ f u < 3 * Real.pi / 2 := by
    have hn := S.p_sub_re_ne (H.ne_of_adj u.property.symm)
    rcases lt_or_gt_of_ne hn with hn | hn
    · obtain ⟨h₁, h₂⟩ := heading_bounds_neg hn
      exact ⟨by dsimp [f]; linarith [Real.pi_pos], h₂⟩
    · obtain ⟨h₁, h₂⟩ := heading_bounds_pos hn
      exact ⟨h₁, by dsimp [f]; linarith [Real.pi_pos]⟩
  rcases S.geoSigma_spec H hHG v a with ⟨hmin, _⟩ | ⟨hlt, _⟩
  · have hm : S.isMinNeighbor H d := fun u hu => hmin ⟨u, hu⟩
    rw [if_pos hm]
    have hle : f a ≤ f b := hmin b
    have hne' : f a ≠ f b := fun h => hne ((S.heading_inj_H H hHG v h).symm)
    have := lt_of_le_of_ne hle hne'
    linarith
  · have hm : ¬ S.isMinNeighbor H d := fun h => not_lt_of_ge (h b.val b.property) hlt
    rw [if_neg hm, add_zero]
    linarith [(hbound a).2, (hbound b).1]

private lemma gapAngle_eq_pi_div_three_of_triangle (hHG : H ≤ S.G) (v : Fin n)
    (a : {w : Fin n // H.Adj v w}) (hne : S.geoSigma H hHG v a ≠ a)
    (ht : S.G.Adj a.val (S.geoSigma H hHG v a).val)
    (hgap : S.gapAngle H hHG ⟨(a.val, v), a.property.symm⟩ ≤ 4 * Real.pi / 3) :
    S.gapAngle H hHG ⟨(a.val, v), a.property.symm⟩ = Real.pi / 3 := by
  let θ := S.gapAngle H hHG ⟨(a.val, v), a.property.symm⟩
  let z := S.p (S.geoSigma H hHG v a).val - S.p v
  have hθ : 0 ≤ θ := (by linarith [S.gapAngle_ge_pi_div_three H hHG ⟨(a.val, v), a.property.symm⟩,
    Real.pi_pos])
  have hz : ‖z‖ = 1 := hHG (S.geoSigma H hHG v a).property.symm
  have he : z * (Swanepoel.ChainStep.cis θ - 1) =
      S.p a.val - S.p (S.geoSigma H hHG v a).val := by
    rw [mul_sub, S.cis_gapAngle H hHG v a, mul_one]
    dsimp [z]
    ring
  have hc : ‖Swanepoel.ChainStep.cis θ - 1‖ = 1 := by
    have hn := congrArg (fun w : ℂ => ‖w‖) he
    rwa [norm_mul, hz, one_mul, show ‖S.p a.val - S.p (S.geoSigma H hHG v a).val‖ = 1 from ht] at hn
  rcases Swanepoel.ChainStep.equilateral_gap hθ (S.gapAngle_lt_two_pi H hHG v a hne) hc with e | e
  · exact e
  · change θ ≤ 4 * Real.pi / 3 at hgap
    linarith [Real.pi_pos]

private lemma zero_lt_gapAngle (hHG : H ≤ S.G) (v : Fin n) (a : {w : Fin n // H.Adj v w}) :
    0 < S.gapAngle H hHG ⟨(a.val, v), a.property.symm⟩ := by
  have h := S.gapAngle_ge_pi_div_three H hHG ⟨(a.val, v), a.property.symm⟩
  linarith [Real.pi_pos]

private lemma adjacent_gaps_pay (hHG : H ≤ S.G) (d : DartOf H)
    (x : {w : Fin n // H.Adj d.val.1 w})
    (hx₁ : x.val = d.val.2)
    (y : {w : Fin n // H.Adj d.val.2 w}) (hy₁ : (S.geoSigma H hHG d.val.2 y).val = d.val.1)
    (hne : (S.geoSigma H hHG d.val.1 x).val ≠ y.val) :
    Real.pi ≤ S.gapAngle H hHG ⟨(x.val, d.val.1), x.property.symm⟩ +
      S.gapAngle H hHG ⟨(y.val, d.val.2), y.property.symm⟩ := by
  let u := d.val.1
  let v := d.val.2
  let X := (S.geoSigma H hHG u x).val
  let Y := y.val
  let α := S.gapAngle H hHG ⟨(x.val, u), x.property.symm⟩
  let β := S.gapAngle H hHG ⟨(Y, v), y.property.symm⟩
  have hAB : ‖S.p v - S.p u‖ = 1 := hHG d.property.symm
  have hz := S.cis_gapAngle H hHG u x
  change (S.p X - S.p u) * Swanepoel.ChainStep.cis α = S.p x.val - S.p u at hz
  rw [hx₁] at hz
  have hxy := S.cis_gapAngle H hHG v y
  change (S.p (S.geoSigma H hHG v y).val - S.p v) * Swanepoel.ChainStep.cis β = S.p Y - S.p v at hxy
  rw [hy₁] at hxy
  have hc (a : ℝ) : Swanepoel.ChainStep.cis a = EdgeCharge.cis a :=
    Complex.ext (Swanepoel.ChainStep.cis_re a) (Swanepoel.ChainStep.cis_im a)
  have hL : S.p X - S.p u = (S.p v - S.p u) * EdgeCharge.cis (-α) := by
    rw [← hc, ← hz, mul_assoc, ← Swanepoel.ChainStep.cis_add, add_neg_cancel]
    simp [Swanepoel.ChainStep.cis]
  have hR : S.p Y - S.p v = (S.p u - S.p v) * EdgeCharge.cis β := by rw [← hc, hxy]
  refine EdgeCharge.pi_le_add_of_facing ?_ hAB (hHG (S.geoSigma H hHG u x).property.symm)
    (hHG y.property.symm) (fun h => S.re_ne hne (congrArg Complex.re h)) ?_
    (S.zero_lt_gapAngle H hHG u x)
    (S.zero_lt_gapAngle H hHG v y) hL hR
  · intro a b ha hb hab
    have hR' : 1 - EdgeCharge.cis (-b) = FacingRays.right b := by
      apply Complex.ext <;> simp [EdgeCharge.cis, FacingRays.right, Real.cos_neg, Real.sin_neg]
    rw [hR']
    exact FacingRays.dist_lt_one_of_pos_of_add_lt_pi ha hb hab
  · rw [dist_eq_norm]
    exact S.hsep X Y hne

open Classical in
private lemma sigma_neighbors_distinct (hHG : H ≤ S.G) (v : Fin n)
    (a : {w : Fin n // H.Adj v w})
    (hdeg : 3 ≤ Fintype.card {w : Fin n // H.Adj v w}) :
    let σ := S.geoSigma H hHG v
    σ a ≠ a ∧ σ.symm a ≠ a ∧ σ a ≠ σ.symm a := by
  classical
  let σ := S.geoSigma H hHG v
  let T : Finset {w : Fin n // H.Adj v w} := {a, σ a}
  have hσ (b : {w : Fin n // H.Adj v w}) : ∃ k : ℕ, (σ ^ k) a = b :=
    S.geoSigma_isCyclic H hHG v a b
  have htwo (h : σ (σ a) = a) : False := by
    have hm (k : ℕ) : (σ ^ k) a ∈ T := by
      induction k with
      | zero => simp [T]
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at ih ⊢
        rcases ih with h' | h' <;> rw [h'] <;> simp [h]
    have hT : Finset.univ ⊆ T := by
      intro b _
      obtain ⟨k, rfl⟩ := hσ b
      exact hm k
    have hle := Finset.card_le_card hT
    rw [Finset.card_univ] at hle
    have hT' : T.card ≤ 2 := by
      simpa [T] using Finset.card_insert_le a ({σ a} : Finset {w : Fin n // H.Adj v w})
    omega
  refine ⟨fun h => htwo (by rw [h, h]), fun h => htwo ?_, fun h => htwo ?_⟩
  · have e : σ a = a := by
      calc
        σ a = σ (σ.symm a) := congrArg σ h.symm
        _ = a := σ.apply_symm_apply a
    rw [e, e]
  · rw [h, σ.apply_symm_apply]

open Classical in
private lemma corner_surplus (hHG : H ≤ S.G) (v : Fin n)
    (a : {w : Fin n // H.Adj v w}) (hdeg : 3 ≤ Fintype.card {w : Fin n // H.Adj v w}) :
    let σ := S.geoSigma H hHG v
    let gap (b : {w : Fin n // H.Adj v w}) := S.gapAngle H hHG ⟨(b.val, v), b.property.symm⟩
    (gap (σ a) - Real.pi / 3) + (gap (σ.symm a) - Real.pi / 3) ≤
      2 * Real.pi - gap a - ((Fintype.card {w : Fin n // H.Adj v w} : ℝ) - 1) * (Real.pi / 3) := by
  classical
  intro σ gap
  obtain ⟨h₁, h₂, h₃⟩ := S.sigma_neighbors_distinct H hHG v a hdeg
  have he := S.gap_excess_le_interior H hHG v a {σ a, σ.symm a}
    (by change a ∉ ({S.geoSigma H hHG v a, (S.geoSigma H hHG v).symm a} : Finset _)
        simp [Ne.symm h₁, Ne.symm h₂])
  rw [Finset.sum_pair (show σ a ≠ σ.symm a from h₃)] at he
  exact he

end AngleComponents

section PolygonGraph

open Classical

variable {m : ℕ} (p : Fin m ↪ Fin n) (hm : 3 ≤ m)

include hm

omit S in
private lemma polygon_rotate_val (i : Fin m) : (finRotate m i).val = (i.val + 1) % m := by
  letI : NeZero m := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add]
  change (i.val + 1 % m) % m = _
  rw [Nat.mod_eq_of_lt (show 1 < m by omega)]

omit S in
private lemma polygon_rotate_ne (i : Fin m) : finRotate m i ≠ i := by
  intro h
  have hi := i.isLt
  have hv := congrArg Fin.val h
  rw [polygon_rotate_val hm] at hv
  by_cases hs : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have he : i.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega

omit S in
private lemma polygon_rotate_twice_ne (i : Fin m) : finRotate m (finRotate m i) ≠ i := by
  intro h
  have hi := i.isLt
  have hv := congrArg Fin.val h
  rw [polygon_rotate_val hm, polygon_rotate_val hm, Nat.mod_add_mod] at hv
  by_cases hs : i.val + 2 < m
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have he : i.val + 1 + 1 = m + (i.val + 2 - m) := by omega
    rw [he, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod] at hv
    rw [Nat.mod_eq_of_lt (show i.val + 2 - m < m by omega)] at hv
    omega

omit S in
private def polygonGraph : SimpleGraph (Fin n) where
  Adj x y := ∃ i : Fin m, (x = p i ∧ y = p (finRotate m i)) ∨
    (x = p (finRotate m i) ∧ y = p i)
  symm := ⟨by
    intro x y h
    rcases h with ⟨i, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · exact ⟨i, Or.inr ⟨hy, hx⟩⟩
    · exact ⟨i, Or.inl ⟨hy, hx⟩⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨i, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · exact polygon_rotate_ne hm i (p.injective (hy.symm.trans hx))
    · exact polygon_rotate_ne hm i (p.injective (hx.symm.trans hy))⟩

private lemma polygonGraph_le (h : ∀ i, S.G.Adj (p i) (p (finRotate m i))) :
    polygonGraph p hm ≤ S.G := by
  rintro x y ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h i
  · exact (h i).symm

omit S in
private lemma polygonGraph_step (i : Fin m) :
    (polygonGraph p hm).Adj (p i) (p (finRotate m i)) :=
  ⟨i, Or.inl ⟨rfl, rfl⟩⟩

omit S in
private lemma polygonGraph_prev (i : Fin m) :
    (polygonGraph p hm).Adj (p i) (p ((finRotate m).symm i)) := by
  simpa only [Equiv.apply_symm_apply] using
    (polygonGraph_step p hm ((finRotate m).symm i)).symm

omit S in
private lemma polygonGraph_neighbor_iff (i : Fin m) (v : Fin n) :
    (polygonGraph p hm).Adj (p i) v ↔
      v = p (finRotate m i) ∨ v = p ((finRotate m).symm i) := by
  constructor
  · rintro ⟨j, ⟨hj, hv⟩ | ⟨hj, hv⟩⟩
    · exact Or.inl (by simpa only [p.injective hj] using hv)
    · have he : (finRotate m).symm i = j := by
        rw [p.injective hj, Equiv.symm_apply_apply]
      exact Or.inr (by simpa only [he] using hv)
  · rintro (rfl | rfl)
    · exact polygonGraph_step p hm i
    · exact polygonGraph_prev p hm i

omit S in
private lemma polygonGraph_neighbor_ne (i : Fin m) :
    p (finRotate m i) ≠ p ((finRotate m).symm i) := by
  intro h
  have he := congrArg (finRotate m) (p.injective h)
  rw [Equiv.apply_symm_apply] at he
  exact polygon_rotate_twice_ne hm i he

omit S in
private lemma polygonGraph_degree (i : Fin m) : (polygonGraph p hm).degree (p i) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have he : (polygonGraph p hm).neighborFinset (p i) =
      {p (finRotate m i), p ((finRotate m).symm i)} := by
    ext v
    simp [polygonGraph_neighbor_iff p hm]
  rw [he, Finset.card_pair (polygonGraph_neighbor_ne p hm i)]

omit S in
private lemma polygonGraph_degree_off (v : Fin n) (hv : v ∉ Set.range p) :
    (polygonGraph p hm).degree v = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  rcases ((polygonGraph p hm).mem_neighborFinset v w).mp hw with ⟨i, ⟨hi, _⟩ | ⟨hi, _⟩⟩
  · exact hv ⟨i, hi.symm⟩
  · exact hv ⟨finRotate m i, hi.symm⟩

omit S in
private def polygonForward (i : Fin m) : DartOf (polygonGraph p hm) :=
  ⟨(p i, p (finRotate m i)), polygonGraph_step p hm i⟩

omit S in
private def polygonReverse (i : Fin m) : DartOf (polygonGraph p hm) :=
  ⟨(p (finRotate m i), p i), (polygonGraph_step p hm i).symm⟩

omit S in
private lemma polygon_dart_cases (d : DartOf (polygonGraph p hm)) :
    (∃ i, d = polygonForward p hm i) ∨ (∃ i, d = polygonReverse p hm i) := by
  rcases d.property with ⟨i, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · left
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> assumption
  · right
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> assumption

variable (hJ : polygonGraph p hm ≤ S.G)

private lemma polygon_geoSigma_other (i : Fin m) (a b : {u // (polygonGraph p hm).Adj (p i) u})
    (hab : a ≠ b) : S.geoSigma (polygonGraph p hm) hJ (p i) a = b := by
  have h₁ := polygonGraph_step p hm i
  have h₂ := polygonGraph_prev p hm i
  have h₃ := polygonGraph_neighbor_ne p hm i
  have hs := S.geoSigma_ne_self (polygonGraph p hm) hJ (p i) ⟨_, _, h₁, h₂, h₃⟩ a
  apply Subtype.ext
  have ha := (polygonGraph_neighbor_iff p hm i a.val).mp a.property
  have hb := (polygonGraph_neighbor_iff p hm i b.val).mp b.property
  let c := S.geoSigma (polygonGraph p hm) hJ (p i) a
  change c.val = b.val
  have hc := (polygonGraph_neighbor_iff p hm i c.val).mp c.property
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  all_goals first
    | exact hb ▸ hc
    | exact (hab (Subtype.ext (ha.trans hb.symm))).elim
    | exact (hs (Subtype.ext (hc.trans ha.symm))).elim

private lemma polygon_geoPhi_forward (i : Fin m) :
    S.geoPhi (polygonGraph p hm) hJ (polygonForward p hm i) =
      polygonForward p hm (finRotate m i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · let a : {u // (polygonGraph p hm).Adj (p (finRotate m i)) u} :=
      ⟨p i, (polygonGraph_step p hm i).symm⟩
    let b : {u // (polygonGraph p hm).Adj (p (finRotate m i)) u} :=
      ⟨p (finRotate m (finRotate m i)), polygonGraph_step p hm (finRotate m i)⟩
    exact congrArg Subtype.val (S.polygon_geoSigma_other p hm hJ (finRotate m i) a b
      (fun h => polygon_rotate_twice_ne hm i (p.injective (congrArg Subtype.val h).symm)))

private lemma polygon_geoPhi_reverse (i : Fin m) :
    S.geoPhi (polygonGraph p hm) hJ (polygonReverse p hm i) =
      polygonReverse p hm ((finRotate m).symm i) := by
  apply Subtype.ext
  apply Prod.ext
  · change p i = p (finRotate m ((finRotate m).symm i))
    rw [Equiv.apply_symm_apply]
  · let a : {u // (polygonGraph p hm).Adj (p i) u} :=
      ⟨p (finRotate m i), polygonGraph_step p hm i⟩
    let b : {u // (polygonGraph p hm).Adj (p i) u} :=
      ⟨p ((finRotate m).symm i), polygonGraph_prev p hm i⟩
    exact congrArg Subtype.val (S.polygon_geoSigma_other p hm hJ i a b
      (fun h => polygonGraph_neighbor_ne p hm i (congrArg Subtype.val h)))

omit S in
private lemma polygon_orbit_of_steps {A : Type*} [Fintype A] (φ : Equiv.Perm A) (g : Fin m → A)
    (h : ∀ i, sameOrbit φ (g i) (g (finRotate m i))) (i j : Fin m) :
    sameOrbit φ (g i) (g j) := by
  let z : Fin m := ⟨0, by omega⟩
  have hr : ∀ k (hk : k < m), sameOrbit φ (g z) (g ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact sameOrbit_refl _ _
    | succ k ih =>
      intro hk
      let t : Fin m := ⟨k, by omega⟩
      have he : finRotate m t = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        rw [polygon_rotate_val hm]
        exact Nat.mod_eq_of_lt hk
      exact sameOrbit_trans φ (ih t.isLt) (he ▸ h t)
  exact sameOrbit_trans φ (sameOrbit_symm φ (hr i.val i.isLt)) (hr j.val j.isLt)

private lemma polygon_sameOrbit_forward (i j : Fin m) :
    sameOrbit (S.geoPhi (polygonGraph p hm) hJ) (polygonForward p hm i) (polygonForward p hm j) := by
  apply polygon_orbit_of_steps hm _ _ _ i j
  intro k
  rw [← S.polygon_geoPhi_forward p hm hJ k]
  exact sameOrbit_step _ _

private lemma polygon_sameOrbit_reverse (i j : Fin m) :
    sameOrbit (S.geoPhi (polygonGraph p hm) hJ) (polygonReverse p hm i) (polygonReverse p hm j) := by
  apply polygon_orbit_of_steps hm _ _ _ i j
  intro k
  apply sameOrbit_symm
  have he := S.polygon_geoPhi_reverse p hm hJ (finRotate m k)
  rw [Equiv.symm_apply_apply] at he
  rw [← he]
  exact sameOrbit_step _ _

end PolygonGraph

section PolygonOrient

open Classical

private lemma retainedBelow_self_at_dart (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G)
    (d : DartOf J) :
    (S.retainedBelow J J (S.dartMap J d).1 (S.dartMap J d).2.val).card =
      (S.dartMap J d).2.val := by
  simpa only using S.retained_parity_dartMap (H := J) J le_rfl hJ d

private lemma opposite_dart_rank_parity (J : SimpleGraph (Fin n)) (hJ : J ≤ S.G)
    (heven : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0)
    {u v : Fin n} (huv : u < v) (hadj : J.Adj u v) :
    (S.dartMap J ⟨(v, u), hadj.symm⟩).2.val % 2 ≠
      (S.dartMap J ⟨(u, v), hadj⟩).2.val % 2 := by
  have hr := S.retainedBelow_parity_reachable (H := J) J le_rfl hJ heven
    (S.dartMap_to_target_right J hJ huv hadj.symm)
  dsimp only at hr
  have he : (u, v) ∈ S.activeEdges J u.succ := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, by simp, by simp; omega⟩
  have hc : (S.retainedBelow J J u.succ (S.edgeRank J u.succ (u, v))).card =
      S.edgeRank J u.succ (u, v) := S.retainedBelow_self_at_edge J
  have hsucc := S.retainedBelow_succ_card (H := J) J le_rfl hJ he
  rw [hc] at hsucc
  have hforward : (S.dartMap J ⟨(u, v), hadj⟩).2.val % 2 =
      (S.edgeRank J u.succ (u, v) + 1) % 2 := by
    rw [S.dartMap_at_source_right J huv hadj]
  rw [hforward]
  have hrev : (S.dartMap J ⟨(v, u), hadj.symm⟩).2.val % 2 =
      S.edgeRank J u.succ (u, v) % 2 := by
    rw [S.retainedBelow_self_at_dart J hJ] at hr
    rw [hc] at hr
    exact hr
  all_goals omega

variable {m : ℕ} (p : Fin m ↪ Fin n) (hm : 3 ≤ m)
variable (hJ : polygonGraph p hm ≤ S.G)

private lemma polygon_orientation (k : Fin m)
    (hk : (⟨(polygonForward p hm k).val, hJ (polygonForward p hm k).property⟩ : DartOf S.G)
      ∈ S.outerDarts S.G) :
    let J := polygonGraph p hm
    let G := S.slabGraph J
    let c := G.connectedComponentMk (S.dartMap J (polygonReverse p hm k))
    (∀ i, polygonForward p hm i ∈ S.outerDarts J) ∧
      c ≠ G.connectedComponentMk (S.outerVert J) ∧
      ∀ i, G.connectedComponentMk (S.dartMap J (polygonReverse p hm i)) = c := by
  classical
  let J := polygonGraph p hm
  let G := S.slabGraph J
  let C (d : DartOf J) := G.connectedComponentMk (S.dartMap J d)
  let c₀ := G.connectedComponentMk (S.outerVert J)
  have heven : ∀ v, ((S.leftEdges J v).card + (S.rightEdges J v).card) % 2 = 0 := by
    apply S.retained_degree_even J
    intro v
    by_cases hv : v ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hv
      rw [polygonGraph_degree p hm i]
    · rw [polygonGraph_degree_off p hm v hv]
  have hcomp {d e : DartOf J} (h : sameOrbit (S.geoPhi J hJ) d e) : C d = C e :=
    congrArg (S.orbitToComp J hJ) (Quotient.sound h)
  have hf : (S.dartMap J (polygonForward p hm k)).2.val % 2 = 0 := by
    let d := polygonForward p hm k
    have ha := (S.mem_outerDarts S.G _).mp hk
    have hp := S.retainedBelow_parity_outer (H := S.G) J hJ le_rfl heven
      (SimpleGraph.ConnectedComponent.exact ha.symm)
    have ht := S.retained_parity_dartMap (H := S.G) J hJ le_rfl d
    dsimp only at ht
    rw [ht] at hp
    exact hp
  have hne : (S.dartMap J (polygonReverse p hm k)).2.val % 2 ≠
      (S.dartMap J (polygonForward p hm k)).2.val % 2 := by
    have ha := polygonGraph_step p hm k
    rcases lt_or_gt_of_ne (J.ne_of_adj ha) with hlt | hgt
    · exact S.opposite_dart_rank_parity J hJ heven hlt ha
    · exact Ne.symm (S.opposite_dart_rank_parity J hJ heven hgt ha.symm)
  have hr : C (polygonReverse p hm k) ≠ c₀ := by
    intro h
    have hp := S.retainedBelow_parity_outer (H := J) J le_rfl hJ heven
      (SimpleGraph.ConnectedComponent.exact h.symm)
    rw [S.retainedBelow_self_at_dart J hJ] at hp
    exact hne (hp.trans hf.symm)
  have hreverse (i : Fin m) : C (polygonReverse p hm i) = C (polygonReverse p hm k) :=
    hcomp (S.polygon_sameOrbit_reverse p hm hJ i k)
  obtain ⟨d, hd⟩ := S.outer_has_dart_of_edge J hJ ⟨_, _, polygonGraph_step p hm k⟩
  have hc : C d = c₀ := (SimpleGraph.ConnectedComponent.sound hd).symm
  rcases polygon_dart_cases p hm d with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · refine ⟨fun i => (S.mem_outerDarts J _).mpr ?_, hr, hreverse⟩
    exact (hcomp (S.polygon_sameOrbit_forward p hm hJ i j)).trans hc
  · exact (hr ((hreverse j).symm.trans hc)).elim

private lemma polygon_reverse_angle_le (k : Fin m)
    (hk : (⟨(polygonForward p hm k).val, hJ (polygonForward p hm k).property⟩ : DartOf S.G)
      ∈ S.outerDarts S.G) :
    ∑ i, S.gapAngle (polygonGraph p hm) hJ (polygonReverse p hm i) ≤
      ((m : ℝ) - 2) * Real.pi := by
  classical
  let J := polygonGraph p hm
  let f := polygonForward p hm
  let r := polygonReverse p hm
  let g := S.gapAngle J hJ
  obtain ⟨hf, hc, hr⟩ := S.polygon_orientation p hm hJ k hk
  have hinj : Function.Injective f := fun _ _ h =>
    p.injective (congrArg (fun d : DartOf J => d.val.1) h)
  have hD : S.outerDarts J = Finset.univ.image f := by
    ext d
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hd
      rcases polygon_dart_cases p hm d with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨i, rfl⟩
      · exact (hc ((hr i).symm.trans ((S.mem_outerDarts J _).mp hd))).elim
    · rintro ⟨i, rfl⟩
      exact hf i
  have houter := S.outer_angle_lower_of_edge J hJ ⟨_, _, polygonGraph_step p hm k⟩
  rw [hD, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
    Finset.sum_image (fun _ _ _ _ h => hinj h)] at houter
  have hpair (i : Fin m) : g (r i) + g (f ((finRotate m).symm i)) = 2 * Real.pi := by
    let a : {u : Fin n // J.Adj (p i) u} := ⟨_, polygonGraph_step p hm i⟩
    let b : {u : Fin n // J.Adj (p i) u} := ⟨_, polygonGraph_prev p hm i⟩
    have hab : a ≠ b := fun h => polygonGraph_neighbor_ne p hm i (congrArg Subtype.val h)
    have hu : Finset.univ = ({a, b} : Finset {u : Fin n // J.Adj (p i) u}) := by
      ext u
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact ((polygonGraph_neighbor_iff p hm i u.val).mp u.property).imp
        (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    have hb : (⟨(b.val, p i), b.property.symm⟩ : DartOf J) = f ((finRotate m).symm i) := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change p i = p (finRotate m ((finRotate m).symm i))
        rw [Equiv.apply_symm_apply]
    have hs := S.gapAngle_sum_at_vertex J hJ (p i) ⟨a.val, a.property⟩
    rw [hu, Finset.sum_pair hab] at hs
    change g (r i) + g ⟨(b.val, p i), b.property.symm⟩ = 2 * Real.pi at hs
    rwa [hb] at hs
  have htotal := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ)
    (fun i _ => hpair i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at htotal
  have hrot : (∑ i, g (f ((finRotate m).symm i))) = ∑ i, g (f i) :=
    Fintype.sum_equiv (finRotate m).symm _ _ (fun _ => rfl)
  rw [hrot] at htotal
  change ((m : ℝ) + 2) * Real.pi ≤ ∑ i, g (f i) at houter
  change (∑ i, g (r i)) ≤ ((m : ℝ) - 2) * Real.pi
  linarith only [houter, htotal]
end PolygonOrient

noncomputable section ExteriorData

open Classical
open scoped BigOperators

private structure Exterior where
  order : Fin (S.outerDarts S.G).card ≃ ↥(S.outerDarts S.G)
  vertex_injective : Function.Injective (fun i => (order i).val.val.2)
  step : ∀ i, (order (finRotate _ i)).val = S.geoPhi S.G le_rfl (order i).val

private lemma exterior_exists (hconn : S.G.Connected)
    (hcut : ∀ v, (S.G.induce {w | w ≠ v}).Connected) : Nonempty (Exterior S) := by
  obtain ⟨e, hi, hs⟩ := S.outer_index hconn hcut
  exact ⟨⟨e, hi, hs⟩⟩

variable (E : Exterior S)

private abbrev exteriorVert : Fin (S.outerDarts S.G).card ↪ Fin n :=
  ⟨fun i => (E.order i).val.val.2, E.vertex_injective⟩

private abbrev exteriorPrev (i : Fin (S.outerDarts S.G).card) :
    {w : Fin n // S.G.Adj (S.exteriorVert E i) w} :=
  ⟨(E.order i).val.val.1, (E.order i).val.property.symm⟩

private lemma exterior_source (i : Fin (S.outerDarts S.G).card) :
    (E.order (finRotate _ i)).val.val.1 = S.exteriorVert E i := by
  rw [E.step]
  rfl

private lemma exterior_edge (i : Fin (S.outerDarts S.G).card) :
    S.G.Adj (S.exteriorVert E i) (S.exteriorVert E (finRotate _ i)) := by
  rw [← S.exterior_source E i]
  exact (E.order (finRotate _ i)).val.property

private abbrev exteriorNext (i : Fin (S.outerDarts S.G).card) :
    {w : Fin n // S.G.Adj (S.exteriorVert E i) w} :=
  S.geoSigma S.G le_rfl (S.exteriorVert E i) (S.exteriorPrev E i)

private lemma exteriorNext_val (i : Fin (S.outerDarts S.G).card) :
    (S.exteriorNext E i).val = S.exteriorVert E (finRotate _ i) := by
  change _ = ((E.order (finRotate _ i)).val).val.2
  rw [E.step]
  rfl

private abbrev exteriorL (i : Fin (S.outerDarts S.G).card) :
    {w : Fin n // S.G.Adj (S.exteriorVert E i) w} :=
  S.geoSigma S.G le_rfl (S.exteriorVert E i) (S.exteriorNext E i)

private abbrev exteriorR (i : Fin (S.outerDarts S.G).card) :
    {w : Fin n // S.G.Adj (S.exteriorVert E i) w} :=
  (S.geoSigma S.G le_rfl (S.exteriorVert E i)).symm (S.exteriorPrev E i)

private def exteriorBad (i : Fin (S.outerDarts S.G).card) : Prop :=
  (S.exteriorL E i).val ≠ (S.exteriorR E (finRotate _ i)).val

private abbrev exteriorGap (i : Fin (S.outerDarts S.G).card)
    (a : {w : Fin n // S.G.Adj (S.exteriorVert E i) w}) : ℝ :=
  S.gapAngle S.G le_rfl ⟨(a.val, S.exteriorVert E i), a.property.symm⟩

private def exteriorInterior (i : Fin (S.outerDarts S.G).card) : ℝ :=
  2 * Real.pi - S.gapAngle S.G le_rfl (E.order i).val

private def exteriorDeg (i : Fin (S.outerDarts S.G).card) : ℕ :=
  Fintype.card {w : Fin n // S.G.Adj (S.exteriorVert E i) w}

private def exteriorSurplus (i : Fin (S.outerDarts S.G).card) : ℝ :=
  S.exteriorInterior E i - ((S.exteriorDeg E i : ℝ) - 1) * (Real.pi / 3)

private def exteriorChargeL (i : Fin (S.outerDarts S.G).card) : ℝ :=
  if S.exteriorBad E i then S.exteriorGap E i (S.exteriorNext E i) - Real.pi / 3 else 0

private def exteriorChargeR (i : Fin (S.outerDarts S.G).card) : ℝ :=
  if S.exteriorBad E ((finRotate _).symm i) then S.exteriorGap E i (S.exteriorR E i) - Real.pi / 3 else 0

private lemma exterior_surplus_ge (i : Fin (S.outerDarts S.G).card) :
    0 ≤ S.exteriorSurplus E i := by
  have h := S.gap_excess_le_interior S.G le_rfl (S.exteriorVert E i) (S.exteriorPrev E i) ∅ (by simp)
  simpa [exteriorSurplus, exteriorInterior, exteriorDeg] using h

private lemma exterior_charges_le (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (i : Fin (S.outerDarts S.G).card) :
    S.exteriorChargeL E i + S.exteriorChargeR E i ≤ S.exteriorSurplus E i := by
  have h := S.corner_surplus S.G le_rfl _ (S.exteriorPrev E i) (hd i)
  dsimp only at h
  change (S.exteriorGap E i (S.exteriorNext E i) - Real.pi / 3) +
    (S.exteriorGap E i (S.exteriorR E i) - Real.pi / 3) ≤ S.exteriorSurplus E i at h
  have hL := S.gapAngle_ge_pi_div_three S.G le_rfl
    (⟨((S.exteriorNext E i).val, S.exteriorVert E i), (S.exteriorNext E i).property.symm⟩ : DartOf S.G)
  have hR := S.gapAngle_ge_pi_div_three S.G le_rfl
    (⟨((S.exteriorR E i).val, S.exteriorVert E i), (S.exteriorR E i).property.symm⟩ : DartOf S.G)
  change Real.pi / 3 ≤ S.exteriorGap E i (S.exteriorNext E i) at hL
  change Real.pi / 3 ≤ S.exteriorGap E i (S.exteriorR E i) at hR
  unfold exteriorChargeL exteriorChargeR
  split_ifs <;> linarith

private lemma exterior_bad_pays (i : Fin (S.outerDarts S.G).card) (hb : S.exteriorBad E i) :
    Real.pi / 3 ≤ S.exteriorChargeL E i + S.exteriorChargeR E (finRotate _ i) := by
  let d : DartOf S.G := ⟨(S.exteriorVert E i, S.exteriorVert E (finRotate _ i)), S.exterior_edge E i⟩
  have hx : (S.exteriorNext E i).val = d.val.2 := S.exteriorNext_val E i
  have hy : (S.geoSigma S.G le_rfl (S.exteriorVert E (finRotate _ i))
      (S.exteriorR E (finRotate _ i))).val = d.val.1 := by
    rw [exteriorR, Equiv.apply_symm_apply]
    exact S.exterior_source E i
  have h := S.adjacent_gaps_pay S.G le_rfl d (S.exteriorNext E i) hx
    (S.exteriorR E (finRotate _ i)) hy hb
  unfold exteriorChargeL exteriorChargeR
  rw [Equiv.symm_apply_apply, if_pos hb, if_pos hb]
  change Real.pi ≤ S.exteriorGap E i (S.exteriorNext E i) +
    S.exteriorGap E (finRotate _ i) (S.exteriorR E (finRotate _ i)) at h
  linarith

private lemma exterior_good_angle (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (i : Fin (S.outerDarts S.G).card) (hg : ¬ S.exteriorBad E i) :
    S.exteriorGap E i (S.exteriorNext E i) = Real.pi / 3 ∧
    S.exteriorGap E (finRotate _ i) (S.exteriorR E (finRotate _ i)) = Real.pi / 3 := by
  have eq : (S.exteriorL E i).val = (S.exteriorR E (finRotate _ i)).val := not_ne_iff.mp hg
  have hcast (j : Fin (S.outerDarts S.G).card) : (3 : ℝ) ≤ S.exteriorDeg E j := by
    exact_mod_cast hd j
  have upper (j : Fin (S.outerDarts S.G).card) :
      S.exteriorGap E j (S.exteriorNext E j) ≤ 4 * Real.pi / 3 ∧
      S.exteriorGap E j (S.exteriorR E j) ≤ 4 * Real.pi / 3 := by
    have h := S.corner_surplus S.G le_rfl _ (S.exteriorPrev E j) (hd j)
    dsimp only at h
    change (S.exteriorGap E j (S.exteriorNext E j) - Real.pi / 3) +
      (S.exteriorGap E j (S.exteriorR E j) - Real.pi / 3) ≤ S.exteriorSurplus E j at h
    have h₀ := S.gapAngle_ge_pi_div_three S.G le_rfl (E.order j).val
    have h₁ : Real.pi / 3 ≤ S.exteriorGap E j (S.exteriorNext E j) :=
      S.gapAngle_ge_pi_div_three S.G le_rfl _
    have h₂ : Real.pi / 3 ≤ S.exteriorGap E j (S.exteriorR E j) :=
      S.gapAngle_ge_pi_div_three S.G le_rfl _
    have h₃ : 2 * (Real.pi / 3) ≤ ((S.exteriorDeg E j : ℝ) - 1) * (Real.pi / 3) :=
      mul_le_mul_of_nonneg_right (by linarith [hcast j]) (by positivity)
    unfold exteriorSurplus exteriorInterior at h
    constructor <;> linarith only [h, h₀, h₁, h₂, h₃]
  have hR : (S.geoSigma S.G le_rfl (S.exteriorVert E (finRotate _ i))
      (S.exteriorR E (finRotate _ i))).val = S.exteriorVert E i := by
    rw [exteriorR, Equiv.apply_symm_apply]
    exact S.exterior_source E i
  constructor
  · apply S.gapAngle_eq_pi_div_three_of_triangle S.G le_rfl _ _
    · exact (S.sigma_neighbors_distinct S.G le_rfl _ _ (hd i)).1
    · change S.G.Adj (S.exteriorNext E i).val (S.exteriorL E i).val
      rw [S.exteriorNext_val E i, eq]
      exact (S.exteriorR E (finRotate _ i)).property
    · exact (upper i).1
  · apply S.gapAngle_eq_pi_div_three_of_triangle S.G le_rfl _ _
    · exact (S.sigma_neighbors_distinct S.G le_rfl _ _ (hd (finRotate _ i))).1
    · rw [hR, ← eq]
      exact (S.exteriorL E i).property.symm
    · exact (upper (finRotate _ i)).2

private lemma exterior_interior_sum (hd : ∀ v, 1 ≤ (S.leftEdges S.G v).card + (S.rightEdges S.G v).card) :
    (∑ i, S.exteriorInterior E i) ≤ ((S.outerDarts S.G).card - 2 : ℝ) * Real.pi := by
  have h := S.outer_angle_lower S.G le_rfl hd
  have he := Equiv.sum_comp E.order (fun d : ↥(S.outerDarts S.G) => S.gapAngle S.G le_rfl d.val)
  rw [Finset.sum_coe_sort] at he
  change (∑ i, (2 * Real.pi - S.gapAngle S.G le_rfl (E.order i).val)) ≤ _
  rw [Finset.sum_sub_distrib, he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end ExteriorData

private noncomputable abbrev exteriorSize := (S.outerDarts S.G).card

open scoped EuclideanGeometry

omit S in

private theorem setup_of_config (X : Finset ℝ²) (h4 : 4 ≤ X.card)
    (hsep : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y)) :
    ∃ T : GeoSetup X.card, ∃ e : Fin X.card ≃ ↥X,
      ∀ i j, T.G.Adj i j ↔ dist (e i).val (e j).val = 1 := by
  classical
  let c := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨ω, hω, hre⟩ := exists_generic_unit_rot (X.image c)
  let p (x : ℝ²) : ℂ := ω * c x
  let xs := X.image (fun x => (p x).re)
  have hp : Set.InjOn (fun x => (p x).re) (X : Set ℝ²) := by
    intro x hx y hy hxy
    by_contra hne
    exact hre (c x) (Finset.mem_image_of_mem _ hx) (c y) (Finset.mem_image_of_mem _ hy)
      (c.injective.ne hne) hxy
  have hcard : xs.card = X.card := Finset.card_image_of_injOn hp
  let b := xs.orderEmbOfFin hcard
  have hex (i : Fin X.card) : ∃ x ∈ X, (p x).re = b i :=
    Finset.mem_image.mp (xs.orderEmbOfFin_mem hcard i)
  let q (i : Fin X.card) : ↥X := ⟨Classical.choose (hex i), (Classical.choose_spec (hex i)).1⟩
  have hq (i : Fin X.card) : (p (q i).val).re = b i := (Classical.choose_spec (hex i)).2
  have hbij : Function.Bijective q :=
    (Fintype.bijective_iff_injective_and_card q).mpr
      ⟨fun i j h => b.injective ((hq i).symm.trans ((congrArg (fun x : ↥X => (p x.val).re) h).trans (hq j))),
        by simp⟩
  let e := Equiv.ofBijective q hbij
  have hd (x y : ℝ²) : ‖p x - p y‖ = dist x y := by
    dsimp only [p]
    rw [← mul_sub, norm_mul, hω, one_mul, ← dist_eq_norm]
    exact c.isometry.dist_eq x y
  let T : GeoSetup X.card :=
    { hn := h4
      p := fun i => p (q i).val
      hx_mono := fun i j hij => by
        change (p (q i).val).re < (p (q j).val).re
        rw [hq i, hq j]
        exact b.strictMono hij
      hsep := fun i j hij => by
        rw [hd]
        exact hsep (q i).property (q j).property (fun h => hij (hbij.injective (Subtype.ext h))) }
  refine ⟨T, e, fun i j => ?_⟩
  change ‖p (q i).val - p (q j).val‖ = 1 ↔ dist (q i).val (q j).val = 1
  rw [hd]

omit S in

private theorem config_connected_of_cut {X : Finset ℝ²} [DecidableEq ℝ²]
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (f : V ↪ ℝ²)
    (hf : ∀ v, f v ∈ X) (hcover : (X \ Finset.univ.map f).card ≤ 1)
    (hadj : ∀ i j, G.Adj i j ↔ dist (f i) (f j) = 1)
    (hcut : ∀ A ⊆ X, ∀ B ⊆ X, A.Nonempty → B.Nonempty → Disjoint A B →
      (X \ (A ∪ B)).card ≤ 1 → ∃ x ∈ A, ∃ y ∈ B, dist x y = 1) : G.Connected := by
  apply Swanepoel.connected_of_cut G
  intro U hU hUc
  let W := Finset.univ \ U
  have hsub (A : Finset V) : A.map f ⊆ X := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact hf i
  have hdis : Disjoint (U.map f) (W.map f) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hy
    exact (Finset.mem_sdiff.mp hj).2 (f.injective hji ▸ hi)
  have hu : U ∪ W = Finset.univ := by
    ext i
    by_cases hi : i ∈ U <;> simp [W, hi]
  have hrest : (X \ (U.map f ∪ W.map f)).card ≤ 1 := by
    rw [← Finset.map_union, hu]
    exact hcover
  obtain ⟨x, hx, y, hy, hxy⟩ := hcut _ (hsub U) _ (hsub W)
    (hU.map (f := f)) (hUc.map (f := f)) hdis hrest

  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
  exact ⟨i, hi, j, hj, (hadj i j).mpr hxy⟩

omit S in

private theorem connected_of_config_cut {X : Finset ℝ²} [DecidableEq ℝ²]
    (T : GeoSetup X.card) (e : Fin X.card ≃ ↥X)
    (hadj : ∀ i j, T.G.Adj i j ↔ dist (e i).val (e j).val = 1)
    (hcut : ∀ A ⊆ X, ∀ B ⊆ X, A.Nonempty → B.Nonempty → Disjoint A B →
      (X \ (A ∪ B)).card ≤ 1 → ∃ x ∈ A, ∃ y ∈ B, dist x y = 1) :
    T.G.Connected ∧ ∀ v, (T.G.induce {w | w ≠ v}).Connected := by
  classical
  have h4 := T.hn
  let f : Fin X.card ↪ ℝ² := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hval (x : ℝ²) (hx : x ∈ X) : f (e.symm ⟨x, hx⟩) = x :=
    congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  haveI : Nonempty (Fin X.card) := ⟨⟨0, by omega⟩⟩
  constructor
  · refine config_connected_of_cut T.G f (fun i => (e i).property) ?_ hadj hcut
    have hsub : X ⊆ Finset.univ.map f := fun x hx =>
      Finset.mem_map.mpr ⟨e.symm ⟨x, hx⟩, Finset.mem_univ _, hval x hx⟩
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
    omega
  · intro v
    let D : Set (Fin X.card) := {w | w ≠ v}
    let a : Fin X.card := ⟨0, by omega⟩
    let b : Fin X.card := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      change (0 : ℕ) = 1 at hv
      omega
    haveI : Nonempty D := by
      by_cases ha : a = v
      · exact ⟨⟨b, fun hb => hab (ha.trans hb.symm)⟩⟩
      · exact ⟨⟨a, ha⟩⟩
    let g : D ↪ ℝ² := (Function.Embedding.subtype _).trans f
    refine config_connected_of_cut (T.G.induce D) g (fun i => (e i.val).property) ?_
      (fun i j => hadj i.val j.val) hcut
    have hsub : X \ Finset.univ.map g ⊆ {f v} := by
      intro x hx
      obtain ⟨hxX, hn⟩ := Finset.mem_sdiff.mp hx
      let i := e.symm ⟨x, hxX⟩
      by_cases hi : i = v
      · exact Finset.mem_singleton.mpr ((hval x hxX).symm.trans (congrArg f hi))
      · exact (hn (Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hval x hxX⟩)).elim
    simpa only [Finset.card_singleton] using Finset.card_le_card hsub

omit S in

private noncomputable def contactNeighborhood {n : ℕ} (T : GeoSetup n)
    (C : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => x ∈ C ∨ ∃ y ∈ C, T.G.Adj y x)

omit S in

private theorem minBad_degree_ge_three {X : Finset ℝ²}
    (h : Swanepoel.MinBad X) (T : GeoSetup X.card) (e : Fin X.card ≃ ↥X)
    (hadj : ∀ i j, T.G.Adj i j ↔ dist (e i).val (e j).val = 1) :
    haveI := Classical.decRel T.G.Adj
    ∀ v, 3 ≤ T.G.degree v := by
  classical
  intro v
  have hcard : (T.G.neighborFinset v).card =
      (Swanepoel.unitNeighbors X (e v).val).card := by
    refine Finset.card_bij (fun w _ => (e w).val) ?_ ?_ ?_
    · intro w hw
      have hadj' : T.G.Adj v w := (T.G.mem_neighborFinset v w).mp hw
      exact Finset.mem_filter.mpr ⟨(e w).property, (hadj v w).mp hadj'⟩
    · intro w₁ _ w₂ _ heq
      exact e.injective (Subtype.ext heq)
    · intro x hx
      obtain ⟨hxX, hdist⟩ := Finset.mem_filter.mp hx
      let w := e.symm ⟨x, hxX⟩
      have hval : (e w).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxX⟩)
      have hadj' : T.G.Adj v w := (hadj v w).2 (by simpa [hval] using hdist)
      exact ⟨w, (T.G.mem_neighborFinset v w).mpr hadj', hval⟩
  rw [← T.G.card_neighborFinset_eq_degree, hcard]
  exact h.three_le_degree (e v).property

omit S in

private theorem minBad_degree_data {X : Finset ℝ²}
    (h : Swanepoel.MinBad X) (T : GeoSetup X.card) (e : Fin X.card ≃ ↥X)
    (hadj : ∀ i j, T.G.Adj i j ↔ dist (e i).val (e j).val = 1) :
    haveI := Classical.decRel T.G.Adj
    (∀ v, 3 ≤ T.G.degree v) ∧
      (∀ v, (T.leftEdges T.G v).card + (T.rightEdges T.G v).card = T.G.degree v) := by
  constructor
  · exact minBad_degree_ge_three h T e hadj
  · intro v
    exact T.leftEdges_add_rightEdges_eq_degree T.G v

omit S in

private theorem minBad_independent_expansion {X : Finset ℝ²}
    (h : Swanepoel.MinBad X) (T : GeoSetup X.card) (e : Fin X.card ≃ ↥X)
    (hadj : ∀ i j, T.G.Adj i j ↔ dist (e i).val (e j).val = 1)
    (C : Finset (Fin X.card))
    (hind : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → ¬ T.G.Adj i j) (hk : C.card ≤ 8) :
    4 * C.card ≤ (contactNeighborhood T C).card := by
  classical
  let f : Fin X.card ↪ ℝ² := e.toEmbedding.trans (Function.Embedding.subtype _)
  let S := C.map f
  have hs : S ⊆ X := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e i).property
  have hi : (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) := by
    intro x hx y hy hxy hdist
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    have hij : i ≠ j := fun he => hxy (congrArg f he)
    exact hind i hi j hj hij ((hadj i j).mpr (by simpa [f] using hdist))
  have hN : (contactNeighborhood T C).map f = Swanepoel.closedNeighborhood X S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hxX : f i ∈ X := (e i).property
      apply Finset.mem_filter.mpr
      refine ⟨hxX, ?_⟩
      obtain ⟨_, hiC | ⟨j, hjC, hji⟩⟩ := Finset.mem_filter.mp hi
      · exact Or.inl (Finset.mem_map.mpr ⟨i, hiC, rfl⟩)
      · exact Or.inr ⟨f j, Finset.mem_map.mpr ⟨j, hjC, rfl⟩,
          (hadj j i).mp hji⟩
    · intro hx
      obtain ⟨hxX, hxC | ⟨y, hyS, hdist⟩⟩ := Finset.mem_filter.mp hx
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hxC
        exact Finset.mem_map.mpr ⟨i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hi⟩, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hyS
        let i := e.symm ⟨x, hxX⟩
        have hfi : f i = x :=
          congrArg Subtype.val (e.apply_symm_apply ⟨x, hxX⟩)
        have hij : T.G.Adj j i := (hadj j i).2 (by
          change dist (f j) (f i) = 1
          rw [hfi]
          exact hdist)
        exact Finset.mem_map.mpr ⟨i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨j, hj, hij⟩⟩, hfi⟩
  have hkS : S.card ≤ 8 := by
    change (C.map f).card ≤ 8
    rw [Finset.card_map]
    exact hk
  have hsmall := h.small_expansion hs hi hkS
  rw [Finset.card_map] at hsmall
  rw [← hN, Finset.card_map] at hsmall
  exact hsmall

private lemma gapAngle_restrict {J : SimpleGraph (Fin n)} (hJ : J ≤ S.G) (v : Fin n)
    (a b : {u // J.Adj v u})
    (hb : (S.geoSigma S.G le_rfl v ⟨a.val, hJ a.property⟩).val = b.val) :
    S.gapAngle J hJ ⟨(a.val, v), a.property.symm⟩ =
      S.gapAngle S.G le_rfl ⟨(a.val, v), hJ a.property.symm⟩ := by
  classical
  let e (u : {u // J.Adj v u}) : {u // S.G.Adj v u} := ⟨u.val, hJ u.property⟩
  let f (u : {u // S.G.Adj v u}) := heading (S.p u.val - S.p v)
  have he : Function.Injective e := fun _ _ h =>
    Subtype.ext (congrArg (fun z : {u // S.G.Adj v u} => z.val) h)
  have hf := S.heading_inj_H S.G le_rfl v
  have hσ : (S.geoSigma J hJ v a).val = (S.geoSigma S.G le_rfl v (e a)).val :=
    congrArg Subtype.val (S.cwPred_restrict f hf e he a b (Subtype.ext hb.symm))
  have hmin : S.isMinNeighbor J ⟨(a.val, v), a.property.symm⟩ ↔
      S.isMinNeighbor S.G ⟨(a.val, v), hJ a.property.symm⟩ := by
    change (∀ w, J.Adj v w → f (e a) ≤ heading (S.p w - S.p v)) ↔
      (∀ w, S.G.Adj v w → f (e a) ≤ heading (S.p w - S.p v))
    constructor
    · intro ha
      have hcmp : f (e a) ≤ f (S.geoSigma S.G le_rfl v (e a)) := by
        change f (e a) ≤ heading (S.p (S.geoSigma S.G le_rfl v (e a)).val - S.p v)
        rw [hb]
        exact ha b.val b.property
      intro w hw
      exact (cwPredPerm_isMin_iff f hf (e a)).2 hcmp ⟨w, hw⟩
    · intro ha w hw
      exact ha w (hJ hw)
  dsimp only [gapAngle]
  rw [hσ, hmin]

section ChordDeficit

open Classical

variable {m : ℕ} (p : Fin m ↪ Fin n) (hm : 3 ≤ m)
variable (hJ : polygonGraph p hm ≤ S.G)
include hJ

private theorem chord_gap_complement (E : Exterior S) (idx : Fin (S.outerDarts S.G).card)
    (i : Fin m) (hcenter : p i = S.exteriorVert E idx)
    (hprev : p ((finRotate m).symm i) = S.exteriorVert E ((finRotate _).symm idx))
    (hnext : p (finRotate m i) = S.exteriorVert E (finRotate _ idx)) :
    S.gapAngle (polygonGraph p hm) hJ (polygonReverse p hm i) +
      S.gapAngle S.G le_rfl (E.order idx).val = 2 * Real.pi := by
  let J := polygonGraph p hm
  let a : {w // J.Adj (p i) w} := ⟨_, polygonGraph_step p hm i⟩
  let b : {w // J.Adj (p i) w} := ⟨_, polygonGraph_prev p hm i⟩
  let d : DartOf S.G := ⟨(b.val, p i), hJ b.property.symm⟩
  have hsrc : (E.order idx).val.val.1 = S.exteriorVert E ((finRotate _).symm idx) := by
    simpa only [Equiv.apply_symm_apply] using S.exterior_source E ((finRotate _).symm idx)
  have hd : d = (E.order idx).val := Subtype.ext (Prod.ext (hprev.trans hsrc.symm) hcenter)
  have hσ := congrArg (fun e : DartOf S.G => e.val.2) ((E.step idx).trans (congrArg (S.geoPhi S.G le_rfl) hd.symm))
  change S.exteriorVert E (finRotate _ idx) = (S.geoSigma S.G le_rfl (p i) ⟨b.val, hJ b.property⟩).val at hσ
  have he := S.gapAngle_restrict hJ (p i) b a (hσ.symm.trans hnext.symm)
  change S.gapAngle J hJ ⟨(b.val, p i), b.property.symm⟩ = S.gapAngle S.G le_rfl d at he
  rw [hd] at he
  have hu : Finset.univ = ({a, b} : Finset {w // J.Adj (p i) w}) := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact ((polygonGraph_neighbor_iff p hm i w.val).mp w.property).imp
      (fun h => Subtype.ext h) (fun h => Subtype.ext h)
  have hab : a ≠ b := fun h => polygonGraph_neighbor_ne p hm i (congrArg Subtype.val h)
  have hs := S.gapAngle_sum_at_vertex J hJ (p i) ⟨a.val, a.property⟩
  rw [hu, Finset.sum_pair hab] at hs
  rw [← he]
  exact hs

theorem chord_interval_degree_contradiction
    (E : Exterior S) (bidx : Fin m → Fin (S.outerDarts S.G).card)
    (hcenter : ∀ i, p i = S.exteriorVert E (bidx i))
    (hprev : ∀ i, i ≠ Swanepoel.chordFirst hm → i ≠ Swanepoel.chordLast hm →
      p ((finRotate m).symm i) = S.exteriorVert E ((finRotate _).symm (bidx i)))
    (hnext : ∀ i, i ≠ Swanepoel.chordLast hm →
      p (finRotate m i) = S.exteriorVert E (finRotate _ (bidx i)))
    (hdeg : ∀ i, i ∈ Swanepoel.chordInterior hm → 3 ≤ S.exteriorDeg E (bidx i))
    (hone : ∀ i, i ∈ Swanepoel.chordInterior hm → ∀ j, j ∈ Swanepoel.chordInterior hm →
      S.exteriorDeg E (bidx i) < 4 → S.exteriorDeg E (bidx j) < 4 → i = j) :
    False := by
  let first := Swanepoel.chordFirst hm
  let last := Swanepoel.chordLast hm
  let J := polygonGraph p hm
  have hnextFirst : first ≠ last := Swanepoel.chordFirst_ne_last hm
  have hsucc : bidx (finRotate m first) = finRotate _ (bidx first) := by
    have h := hnext first hnextFirst
    have hi := hcenter (finRotate m first)
    apply (S.exteriorVert E).injective
    exact hi.symm.trans h
  have hforward_eq :
      (⟨(polygonForward p hm first).val, hJ (polygonForward p hm first).property⟩ : DartOf S.G) =
        (E.order (bidx (finRotate m first))).val := by
    apply Subtype.ext
    apply Prod.ext
    · have hsrc := S.exterior_source E (bidx first)
      change p first = _
      rw [hcenter first, hsucc]
      exact hsrc.symm
    · change p (finRotate m first) = _
      rw [hcenter (finRotate m first), hsucc]
      rfl
  have hk : (⟨(polygonForward p hm first).val,
      hJ (polygonForward p hm first).property⟩ : DartOf S.G) ∈ S.outerDarts S.G := by
    rw [hforward_eq]
    exact (E.order (bidx (finRotate m first))).property
  have htotal := S.polygon_reverse_angle_le p hm hJ first hk
  let deg (i : Fin m) := S.exteriorDeg E (bidx i)
  let angle (i : Fin m) := S.gapAngle J hJ (polygonReverse p hm i)
  let inner := Swanepoel.chordInterior hm
  have hdef := Swanepoel.chord_interior_degree_deficit hm deg hdeg hone
  have hpoint (i : Fin m) (hi : i ∈ inner) :
      Real.pi ≤ (4 - (deg i : ℝ)) * (Real.pi / 3) + angle i := by
    obtain ⟨hp, hn⟩ := (Swanepoel.mem_chordInterior hm i).mp hi
    have h := S.chord_gap_complement p hm hJ E (bidx i) i (hcenter i) (hprev i hp hn) (hnext i hn)
    have hs := S.exterior_surplus_ge E (bidx i)
    simp only [exteriorSurplus, exteriorInterior] at hs
    change Real.pi ≤ (4 - (S.exteriorDeg E (bidx i) : ℝ)) * (Real.pi / 3) +
      S.gapAngle (polygonGraph p hm) hJ (polygonReverse p hm i)
    linarith only [h, hs]
  have hsum := Finset.sum_le_sum (s := inner) hpoint
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : inner.card + 2 = m := by
    have hmem : last ∈ Finset.univ.erase first :=
      Finset.mem_erase.mpr ⟨(Swanepoel.chordFirst_ne_last hm).symm, Finset.mem_univ _⟩
    dsimp only [inner, Swanepoel.chordInterior]
    rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hcount : (inner.card : ℝ) + 2 = (m : ℝ) := by exact_mod_cast hcard
  have hcount_pi := congrArg (· * Real.pi) hcount
  change (∑ i, angle i) ≤ ((m : ℝ) - 2) * Real.pi at htotal
  rw [Swanepoel.chord_sum_endpoints hm angle] at htotal
  have hf : Real.pi / 3 ≤ angle first := S.gapAngle_ge_pi_div_three J hJ _
  have hl : Real.pi / 3 ≤ angle last := S.gapAngle_ge_pi_div_three J hJ _
  change (∑ i ∈ inner, (4 - (deg i : ℝ)) * (Real.pi / 3)) ≤ Real.pi / 3 at hdef
  change (inner.card : ℝ) * Real.pi ≤
    (∑ i ∈ inner, (4 - (deg i : ℝ)) * (Real.pi / 3)) + ∑ i ∈ inner, angle i at hsum
  change (∑ i ∈ inner, angle i) + angle last + angle first ≤ ((m : ℝ) - 2) * Real.pi at htotal
  linarith only [hsum, hdef, htotal, hcount_pi, hf, hl, Real.pi_pos]

end ChordDeficit

section ExteriorNoChord

variable (E : Exterior S)

private lemma exterior_no_chord (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (a : Fin S.exteriorSize) (i j : ℕ) (hij : i < j) (hj : j < S.exteriorSize) (heven : (j - i) % 2 = 0)
    (hone : ∀ u v : ℕ, i < u → u < j → i < v → v < j →
      S.exteriorDeg E ((finRotate S.exteriorSize ^ u) a) < 4 →
      S.exteriorDeg E ((finRotate S.exteriorSize ^ v) a) < 4 → u = v) :
    ¬ S.G.Adj (S.exteriorVert E ((finRotate S.exteriorSize ^ i) a))
      (S.exteriorVert E ((finRotate S.exteriorSize ^ j) a)) := by
  intro h
  let m := j - i + 1
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hmk : m ≤ S.exteriorSize := by dsimp [m]; omega
  let c := (finRotate S.exteriorSize ^ i) a
  let b := Swanepoel.chordIndices hmk c
  let p := Swanepoel.chordSegment (S.exteriorVert E) hmk c
  have hb (u : Fin m) : b u = (finRotate S.exteriorSize ^ (i + u.val)) a := by
    change (finRotate S.exteriorSize ^ u.val) ((finRotate S.exteriorSize ^ i) a) = _
    rw [Nat.add_comm i, pow_add, Equiv.Perm.mul_apply]
  have hend : p (Swanepoel.chordLast hm) = S.exteriorVert E ((finRotate S.exteriorSize ^ j) a) := by
    change S.exteriorVert E (b (Swanepoel.chordLast hm)) = _
    have he : i + (Swanepoel.chordLast hm).val = j := by
      change i + (m - 1) = j
      dsimp [m]
      omega
    rw [hb, he]
  have hclose : S.G.Adj (p (Swanepoel.chordLast hm)) (S.exteriorVert E c) := by
    rw [hend]
    exact h.symm
  have hJ := S.polygonGraph_le p hm
    (Swanepoel.chordSegment_adj S.G (S.exteriorVert E) hmk c hm (S.exterior_edge E) hclose)
  apply S.chord_interval_degree_contradiction p hm hJ E b (fun _ => rfl)
  · intro u hu hv
    exact (Swanepoel.chordSegment_interior_neighbors (S.exteriorVert E) hmk c hm u hu hv).1
  · intro u hu
    exact congrArg (S.exteriorVert E) (Swanepoel.chordIndices_next hmk c hm u hu)
  · exact fun u _ => hd (b u)
  · intro u hu v hv hdu hdv
    rw [hb] at hdu hdv
    have hbetween (w : Fin m) (hw : w ∈ Swanepoel.chordInterior hm) :
        i < i + w.val ∧ i + w.val < j := by
      have hne := (Swanepoel.mem_chordInterior hm w).mp hw
      have h₀ : w.val ≠ 0 := fun he => hne.1 (Fin.ext he)
      have h₁ : w.val ≠ m - 1 := fun he => hne.2 (Fin.ext he)
      have h₂ := w.isLt
      dsimp [m] at h₁ h₂
      omega
    have hu' := hbetween u hu
    have hv' := hbetween v hv
    have he := hone _ _ hu'.1 hu'.2 hv'.1 hv'.2 hdu hdv
    exact Fin.ext (Nat.add_left_cancel he)

end ExteriorNoChord

section ExteriorExtract

open Classical
open scoped BigOperators

variable (E : Exterior S)

private lemma exterior_has_tip (i : Fin S.exteriorSize) (h : ¬ S.exteriorBad E i) :
    ∃ z, S.G.Adj (S.exteriorVert E i) z ∧
      S.G.Adj (S.exteriorVert E (finRotate S.exteriorSize i)) z := by
  have he : (S.exteriorL E i).val = (S.exteriorR E (finRotate S.exteriorSize i)).val := not_ne_iff.mp h
  exact ⟨(S.exteriorL E i).val, (S.exteriorL E i).property,
    he.symm ▸ (S.exteriorR E (finRotate S.exteriorSize i)).property⟩

private lemma exterior_left_nonneg (i : Fin S.exteriorSize) : 0 ≤ S.exteriorChargeL E i := by
  unfold exteriorChargeL
  split_ifs
  · exact sub_nonneg.mpr (S.gapAngle_ge_pi_div_three S.G le_rfl _)
  · exact le_rfl

private lemma exterior_right_nonneg (i : Fin S.exteriorSize) : 0 ≤ S.exteriorChargeR E i := by
  unfold exteriorChargeR
  split_ifs
  · exact sub_nonneg.mpr (S.gapAngle_ge_pi_div_three S.G le_rfl _)
  · exact le_rfl

private lemma exterior_angle_boundary_budget
    (hdeg : ∀ v, 1 ≤ (S.leftEdges S.G v).card + (S.rightEdges S.G v).card) :
    (∑ i, (((S.exteriorDeg E i : ℝ) - 1) * (Real.pi / 3) + S.exteriorSurplus E i)) ≤
      ((S.exteriorSize : ℝ) - 2) * Real.pi := by
  convert S.exterior_interior_sum E hdeg using 1
  apply Finset.sum_congr rfl
  intro i _
  unfold exteriorSurplus
  ring

private lemma exterior_marks_at_least_six (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (hdeg : ∀ v, 1 ≤ (S.leftEdges S.G v).card + (S.rightEdges S.G v).card) :
    6 ≤ (Swanepoel.ArcExtract.marks (S.exteriorDeg E)).card := by
  have h := Swanepoel.boundary_budget (A := Fin 0) (finRotate S.exteriorSize)
    (S.exteriorDeg E) (S.exteriorSurplus E) (S.exteriorChargeL E) (S.exteriorChargeR E)
    (S.exteriorBad E) (fun _ => ∅) hd (S.exterior_left_nonneg E) (S.exterior_right_nonneg E)
    (S.exterior_charges_le E hd) (S.exterior_bad_pays E)
    (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
    (by simpa only [Fintype.card_fin] using S.exterior_angle_boundary_budget E hdeg)
  have hb := (Nat.le_add_left 6 _).trans h
  change Nat.le 6 _ at hb ⊢
  convert hb using 1
  apply congrArg Finset.card
  ext i
  simp [Swanepoel.ArcExtract.marks]

private lemma exterior_exists_eligible (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (hdeg : ∀ v, 1 ≤ (S.leftEdges S.G v).card + (S.rightEdges S.G v).card)
    (hshort : Swanepoel.ArcExtract.ShortImpossible (deg := S.exteriorDeg E) (S.exteriorBad E)) :
    ∃ a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E)),
      Swanepoel.ArcExtract.eligible (S.exteriorBad E) a ∧
      Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3 := by
  apply Swanepoel.exists_eligible_low_bend (S.exteriorDeg E) (S.exteriorBad E)
    (S.exteriorSurplus E) (S.exteriorChargeL E) (S.exteriorChargeR E)
    hd hshort (S.exterior_left_nonneg E) (S.exterior_right_nonneg E)
    (S.exterior_charges_le E hd)
  · intro i hi
    simp [exteriorChargeL, hi]
  · intro i hi
    rw [exteriorChargeR, Equiv.symm_apply_apply, if_neg hi]
  · exact S.exterior_bad_pays E
  · exact S.exterior_angle_boundary_budget E hdeg

end ExteriorExtract

section ExteriorArc

open Classical
open scoped BigOperators

variable (E : Exterior S)

private noncomputable def exteriorArcIdx (a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E)))
    (i : ℕ) : Fin S.exteriorSize := Swanepoel.ArcExtract.x a (CyclicGap.length a - i)

private noncomputable def exteriorArcPoint (a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E)))
    (i : ℕ) : ℂ := S.p (S.exteriorVert E (S.exteriorArcIdx E a i))

private noncomputable def exteriorArcTip (a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E)))
    (i : ℕ) : ℂ := S.p (S.exteriorR E (S.exteriorArcIdx E a i)).val

private noncomputable def exteriorArcHeading (a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E)))
    (i : ℕ) : ℂ := S.exteriorArcPoint E a (i + 1) - S.exteriorArcPoint E a i

private theorem exteriorArc_idx_step
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))} {i : ℕ}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a) (hi : i < 13) :
    finRotate S.exteriorSize (S.exteriorArcIdx E a (i + 1)) = S.exteriorArcIdx E a i := by
  unfold exteriorArcIdx
  rw [Swanepoel.arc_step]
  congr 1
  have hd := he.1
  omega

private theorem exteriorArc_prev_val
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))} {i : ℕ}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a) (hi : i < 13) :
    (S.exteriorPrev E (S.exteriorArcIdx E a i)).val =
      S.exteriorVert E (S.exteriorArcIdx E a (i + 1)) := by
  rw [← S.exterior_source E (S.exteriorArcIdx E a (i + 1)),
    S.exteriorArc_idx_step E he hi]

private theorem exteriorArc_edge
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))} {i : ℕ}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a) (hi : i < 13) :
    S.G.Adj (S.exteriorVert E (S.exteriorArcIdx E a (i + 1)))
      (S.exteriorVert E (S.exteriorArcIdx E a i)) := by
  rw [← S.exteriorArc_idx_step E he hi]
  exact S.exterior_edge E (S.exteriorArcIdx E a (i + 1))

private theorem exteriorArc_four_good
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a) (i : ℕ) (hi : i < 13) :
    S.exteriorDeg E (S.exteriorArcIdx E a (i + 1)) = 4 ∧
      ¬ S.exteriorBad E (S.exteriorArcIdx E a (i + 1)) := by
  have hd := he.1
  have hj : 12 - i < 13 := by omega
  have hs := Swanepoel.arc_right_suffix (j := 12 - i) he hj
  have hs' := hs
  dsimp only at hs'
  have heq : CyclicGap.length a - 13 + (12 - i) = CyclicGap.length a - (i + 1) := by omega
  rw [heq] at hs'
  constructor
  · simpa [exteriorArcIdx] using hs'.1
  · simpa [exteriorArcIdx] using hs'.2.2

private theorem exteriorArc_neg_adj
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))} :
    S.G.Adj (S.exteriorVert E (S.exteriorArcIdx E a 0))
      (S.exteriorNext E (S.exteriorArcIdx E a 0)).val :=
  (S.exteriorNext E (S.exteriorArcIdx E a 0)).property

end ExteriorArc

section ExteriorArcChain

open Classical
open scoped BigOperators

variable (E : Exterior S)

private theorem exteriorArc_cis_pi :
    Swanepoel.ChainStep.cis Real.pi = (-1 : ℂ) := by
  apply Complex.ext <;> simp [Swanepoel.ChainStep.cis_re,
    Swanepoel.ChainStep.cis_im, Real.cos_pi, Real.sin_pi]

private theorem exteriorArc_cis_pi_sub (t : ℝ) :
    Swanepoel.ChainStep.cis (Real.pi - t) = -Swanepoel.ChainStep.cis (-t) := by
  calc
    Swanepoel.ChainStep.cis (Real.pi - t) =
        Swanepoel.ChainStep.cis (Real.pi + -t) := by congr 1 <;> ring
    _ = Swanepoel.ChainStep.cis Real.pi * Swanepoel.ChainStep.cis (-t) :=
      Swanepoel.ChainStep.cis_add _ _
    _ = -Swanepoel.ChainStep.cis (-t) := by rw [exteriorArc_cis_pi S]; ring

private theorem exteriorArc_tip_eq
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hd : ∀ j, 3 ≤ S.exteriorDeg E j) (i : ℕ) (hi : i < 13) :
    S.exteriorArcTip E a i = S.exteriorArcPoint E a i +
      Swanepoel.ChainStep.w * S.exteriorArcHeading E a i := by
  let idx := S.exteriorArcIdx E a i
  let idxNext := S.exteriorArcIdx E a (i + 1)
  have hrotate : finRotate S.exteriorSize idxNext = idx := by
    dsimp [idx, idxNext]
    exact S.exteriorArc_idx_step E he (i := i) hi
  have hgood := S.exteriorArc_four_good E he i hi
  have hangle := S.exterior_good_angle E hd idxNext hgood.2
  have hgap : S.exteriorGap E idx (S.exteriorR E idx) = Real.pi / 3 := by
    rw [← hrotate]
    exact hangle.2
  have hcis := S.cis_gapAngle S.G le_rfl (S.exteriorVert E idx)
    (S.exteriorR E idx)
  have hprev := S.exteriorArc_prev_val E he (i := i) hi
  have hnext' : (S.geoSigma S.G le_rfl (S.exteriorVert E idx)
      (S.exteriorR E idx)).val = S.exteriorVert E idxNext := by
    rw [exteriorR, Equiv.apply_symm_apply]
    exact hprev
  change (S.p (S.geoSigma S.G le_rfl (S.exteriorVert E idx)
      (S.exteriorR E idx)).val - S.p (S.exteriorVert E idx)) *
      Swanepoel.ChainStep.cis (S.exteriorGap E idx (S.exteriorR E idx)) =
      S.p (S.exteriorR E idx).val - S.p (S.exteriorVert E idx) at hcis
  rw [hnext', hgap] at hcis
  change S.p (S.exteriorR E idx).val =
      S.p (S.exteriorVert E idx) +
        Swanepoel.ChainStep.w *
          (S.p (S.exteriorVert E idxNext) - S.p (S.exteriorVert E idx))
  have hq : S.p (S.exteriorR E idx).val - S.p (S.exteriorVert E idx) =
      (S.p (S.exteriorVert E idxNext) - S.p (S.exteriorVert E idx)) *
        Swanepoel.ChainStep.cis (Real.pi / 3) := hcis.symm
  calc
    S.p (S.exteriorR E idx).val =
        S.p (S.exteriorVert E idx) +
          (S.p (S.exteriorR E idx).val - S.p (S.exteriorVert E idx)) := by ring
    _ = S.p (S.exteriorVert E idx) +
        (S.p (S.exteriorVert E idxNext) - S.p (S.exteriorVert E idx)) *
          Swanepoel.ChainStep.cis (Real.pi / 3) := by rw [hq]
    _ = S.p (S.exteriorVert E idx) +
        Swanepoel.ChainStep.w *
          (S.p (S.exteriorVert E idxNext) - S.p (S.exteriorVert E idx)) := by
      rw [Swanepoel.ChainStep.w]
      ring

private theorem exteriorArc_next_heading
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hd : ∀ j, 3 ≤ S.exteriorDeg E j) (i : ℕ) (hi : i < 12) :
    S.exteriorArcHeading E a (i + 1) = S.exteriorArcHeading E a i *
      Swanepoel.ChainStep.cis (-S.exteriorSurplus E
        (S.exteriorArcIdx E a (i + 1))) := by
  let idx := S.exteriorArcIdx E a (i + 1)
  let idxNext := S.exteriorArcIdx E a (i + 2)
  have hrotate : finRotate S.exteriorSize idxNext = idx := by
    dsimp [idx, idxNext]
    exact S.exteriorArc_idx_step E he (i := i + 1) (by omega)
  have h13 : i < 13 := by omega
  have hgood := S.exteriorArc_four_good E he i h13
  have hdegree : S.exteriorDeg E idx = 4 := by
    simpa [idx] using hgood.1
  have hturn : S.exteriorInterior E idx = Real.pi + S.exteriorSurplus E idx := by
    unfold exteriorSurplus
    rw [hdegree]
    ring
  have hdart :
      (⟨((S.exteriorPrev E idx).val, S.exteriorVert E idx),
        (S.exteriorPrev E idx).property.symm⟩ : DartOf S.G) = (E.order idx).val := by
    apply Subtype.ext
    rfl
  have hgap : S.exteriorGap E idx (S.exteriorPrev E idx) =
      Real.pi - S.exteriorSurplus E idx := by
    have hgap' : S.exteriorGap E idx (S.exteriorPrev E idx) =
        2 * Real.pi - S.exteriorInterior E idx := by
      unfold exteriorGap
      rw [hdart]
      change S.gapAngle S.G le_rfl (E.order idx).val =
        2 * Real.pi - (2 * Real.pi - S.gapAngle S.G le_rfl (E.order idx).val)
      ring
    rw [hgap', hturn]
    ring
  have hcis := S.cis_gapAngle S.G le_rfl (S.exteriorVert E idx)
    (S.exteriorPrev E idx)
  have hprev := S.exteriorArc_prev_val E he (i := i + 1) (by omega)
  have hprevIdx : finRotate S.exteriorSize idx = S.exteriorArcIdx E a i := by
    dsimp [idx]
    exact S.exteriorArc_idx_step E he (i := i) (by omega)
  have hnext' : (S.geoSigma S.G le_rfl (S.exteriorVert E idx)
      (S.exteriorPrev E idx)).val = S.exteriorVert E (S.exteriorArcIdx E a i) := by
    change (S.exteriorNext E idx).val = _
    rw [S.exteriorNext_val E idx, hprevIdx]
  change (S.p (S.geoSigma S.G le_rfl (S.exteriorVert E idx)
      (S.exteriorPrev E idx)).val - S.p (S.exteriorVert E idx)) *
      Swanepoel.ChainStep.cis (S.exteriorGap E idx (S.exteriorPrev E idx)) =
      S.p (S.exteriorPrev E idx).val - S.p (S.exteriorVert E idx) at hcis
  rw [hnext', hprev, hgap] at hcis
  rw [exteriorArc_cis_pi_sub S] at hcis
  dsimp [exteriorArcHeading, exteriorArcPoint, exteriorArcIdx, idx] at hcis ⊢
  rw [← hcis]
  ring

private theorem exteriorArc_turn_budget
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hc : Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3) :
    Swanepoel.ArcHeading.turnSum
      (fun i => S.exteriorSurplus E (S.exteriorArcIdx E a i)) 12 < Real.pi / 3 := by
  have hlen := he.1
  have hsum :
      Swanepoel.ArcHeading.turnSum
          (fun i => S.exteriorSurplus E (S.exteriorArcIdx E a i)) 12 =
        ∑ i ∈ Finset.Ico (CyclicGap.length a - 12) (CyclicGap.length a),
          S.exteriorSurplus E (Swanepoel.ArcExtract.x a i) := by
    unfold Swanepoel.ArcHeading.turnSum
    change (∑ j ∈ Finset.range 12,
        S.exteriorSurplus E (Swanepoel.ArcExtract.x a
          (CyclicGap.length a - (j + 1)))) = _
    refine Finset.sum_bij
        (fun j _ => CyclicGap.length a - 12 + (11 - j)) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj
      rw [Finset.mem_Ico]
      constructor <;> omega
    · intro j hj j' hj' heq
      simp only [Finset.mem_range] at hj hj'
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      refine ⟨CyclicGap.length a - 1 - i, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have heq : CyclicGap.length a - (j + 1) =
          CyclicGap.length a - 12 + (11 - j) := by omega
      rw [heq]
  rw [hsum]
  exact Swanepoel.arc_right_suffix_turn_budget he (S.exteriorSurplus E)
    (S.exteriorSurplus E) (fun v => S.exterior_surplus_ge E v)
    (fun _ _ => rfl) hc

private noncomputable def exteriorArc_chain
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hd : ∀ j, 3 ≤ S.exteriorDeg E j)
    (hc : Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3) :
    Swanepoel.ArcHeading.Chain 12 := by
  refine ⟨S.exteriorArcPoint E a, S.exteriorArcTip E a,
    S.exteriorArcHeading E a,
    fun i => S.exteriorSurplus E (S.exteriorArcIdx E a i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := S.exteriorArc_edge E he (i := 0) (by omega)
    change ‖S.exteriorArcPoint E a 1 - S.exteriorArcPoint E a 0‖ = 1
    exact h
  · intro i hi
    rfl
  · intro i hi
    exact S.exteriorArc_next_heading E he hd i hi
  · intro i hi
    exact S.exterior_surplus_ge E (S.exteriorArcIdx E a (i + 1))
  · exact S.exteriorArc_turn_budget E he hc
  · intro i hi
    exact S.exteriorArc_tip_eq E he hd i (by omega)

end ExteriorArcChain

section SwanepoelSetup

open Classical
open scoped EuclideanGeometry

private theorem exterior_degree_card [DecidableRel S.G.Adj] (E : Exterior S)
    (i : Fin S.exteriorSize) : S.G.degree (S.exteriorVert E i) = S.exteriorDeg E i := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  unfold exteriorDeg
  exact congrArg (fun I : Fintype {w : Fin n // S.G.Adj (S.exteriorVert E i) w} =>
    @Fintype.card _ I) (Subsingleton.elim _ _)

private theorem exterior_degree_filter (E : Exterior S) (i : Fin S.exteriorSize) :
    haveI := Classical.decRel S.G.Adj
    (Finset.univ.filter (S.G.Adj (S.exteriorVert E i))).card = S.exteriorDeg E i := by
  rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  exact S.exterior_degree_card E i

private theorem exterior_extract [DecidableRel S.G.Adj] (E : Exterior S)
    (hdeg : ∀ v, 3 ≤ S.G.degree v)
    (hside : ∀ v, 1 ≤ (S.leftEdges S.G v).card + (S.rightEdges S.G v).card)
    (hexpand : ∀ C : Finset (Fin n), (C : Set (Fin n)).Pairwise (fun x y => ¬ S.G.Adj x y) →
      C.card ≤ 8 → 4 * C.card ≤ (contactNeighborhood S C).card) :
    ∃ a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E)),
      Swanepoel.ArcExtract.eligible (S.exteriorBad E) a ∧
      Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3 := by
  classical
  have hcard (i : Fin (S.outerDarts S.G).card) :
      (S.G.neighborFinset (S.exteriorVert E i)).card = S.exteriorDeg E i := by
    exact S.exterior_degree_card E i
  have hd (i : Fin (S.outerDarts S.G).card) : 3 ≤ S.exteriorDeg E i :=
    (hdeg (S.exteriorVert E i)).trans_eq (hcard i)
  have hmarks := S.exterior_marks_at_least_six E hd hside
  have hshort := Swanepoel.shortImpossible Finset.univ (S.exteriorVert E) S.G.Adj (fun v => S.G.neighborFinset v)
    (S.exteriorDeg E) (S.exteriorBad E) (fun _ => Finset.mem_univ _)
    (fun _ _ h => h.symm) (fun _ => S.G.irrefl) (S.exterior_edge E)
    (fun i y h => (S.G.mem_neighborFinset (S.exteriorVert E i) y).mpr h) hcard hd hmarks
    (S.exterior_has_tip E) (S.exterior_no_chord E hd)
    (fun C _ hi hc => by
      have he := hexpand C hi hc
      convert he using 1
      congr 1
      ext x
      simp [contactNeighborhood])
  exact S.exterior_exists_eligible E hd hside hshort

omit S in
private theorem minBad_four_le {X : Finset ℝ²} (h : Swanepoel.MinBad X) : 4 ≤ X.card := by
  classical
  obtain ⟨x, hx⟩ := h.nonempty
  have hsub : Swanepoel.unitNeighbors X x ⊆ X := Finset.filter_subset _ _
  have hlt : (Swanepoel.unitNeighbors X x).card < X.card := by
    apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩)
    intro he
    have hmem : x ∈ Swanepoel.unitNeighbors X x := by rwa [he]
    simp [Swanepoel.unitNeighbors] at hmem
  have hthree := h.three_le_degree hx
  omega

end SwanepoelSetup

section ExteriorTerminal

open Classical
open scoped BigOperators

variable (E : Exterior S)

private noncomputable abbrev exteriorArcNegVertex
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))} : Fin n :=
  (S.exteriorNext E (S.exteriorArcIdx E a 0)).val

private theorem exteriorArc_terminal_choice
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hd : ∀ i, 3 ≤ S.exteriorDeg E i) :
    let b := CyclicGap.nextMark (Swanepoel.ArcExtract.marks (S.exteriorDeg E)) a
    (CyclicGap.length b = 1 ∧
        S.exteriorDeg E (finRotate S.exteriorSize (S.exteriorArcIdx E a 0)) = 3) ∨
      (2 ≤ CyclicGap.length b ∧ ¬ S.exteriorBad E (S.exteriorArcIdx E a 0) ∧
        S.exteriorDeg E (finRotate S.exteriorSize (S.exteriorArcIdx E a 0)) = 4) := by
  let b := CyclicGap.nextMark (Swanepoel.ArcExtract.marks (S.exteriorDeg E)) a
  have hidx : S.exteriorArcIdx E a 0 = b.val := by
    change Swanepoel.ArcExtract.x a (CyclicGap.length a - 0) = b.val
    rw [Nat.sub_zero]
    exact CyclicGap.nextMark_apply a
  have hstep : finRotate S.exteriorSize (S.exteriorArcIdx E a 0) =
      Swanepoel.ArcExtract.x b 1 := by
    rw [hidx]
    exact Swanepoel.arc_step b 0
  have h := Swanepoel.arc_eligible_next_step hd he
  rcases h with hs | hl
  · left
    exact ⟨hs.1, by rw [hstep]; exact hs.2⟩
  · right
    refine ⟨hl.1, ?_, by rw [hstep]; exact hl.2.2⟩
    rw [hidx]
    exact hl.2.1

private theorem exteriorArc_terminal_no_chord
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (hmarks : 6 ≤ (Swanepoel.ArcExtract.marks (S.exteriorDeg E)).card) :
    ¬ S.G.Adj (S.exteriorArcNegVertex E (a := a))
      (S.exteriorVert E (S.exteriorArcIdx E a 1)) := by
  let d := CyclicGap.length a
  have hdpos : 0 < d := CyclicGap.length_pos a
  have hbound : d + 1 < S.exteriorSize := Swanepoel.shortGap_end_lt hmarks a
  have hnot := S.exterior_no_chord E hd a.val (d - 1) (d + 1) (by omega)
    hbound (by omega) (by
      intro u v hiu hu hiv hv hdu hdv
      have hdsub : d - 1 + 1 = d := by omega
      have huLower : d ≤ u := by
        simpa [hdsub] using (Nat.succ_le_of_lt hiu)
      have hvLower : d ≤ v := by
        simpa [hdsub] using (Nat.succ_le_of_lt hiv)
      have huEq : u = d := by omega
      have hvEq : v = d := by omega
      exact huEq.trans hvEq.symm)
  have hidx1 : S.exteriorArcIdx E a 1 =
      (finRotate S.exteriorSize ^ (d - 1)) a.val := by
    rfl
  have hidx0 : S.exteriorArcIdx E a 0 = (finRotate S.exteriorSize ^ d) a.val := by
    change Swanepoel.ArcExtract.x a (d - 0) = _
    rfl
  have hidxNeg : finRotate S.exteriorSize (S.exteriorArcIdx E a 0) =
      (finRotate S.exteriorSize ^ (d + 1)) a.val := by
    rw [hidx0, pow_succ', Equiv.Perm.mul_apply]
  have hNegVal : S.exteriorArcNegVertex E (a := a) =
      S.exteriorVert E (finRotate S.exteriorSize (S.exteriorArcIdx E a 0)) :=
    S.exteriorNext_val E (S.exteriorArcIdx E a 0)
  intro hAdj
  have hAdj' := hAdj.symm
  rw [hidx1, hNegVal, hidxNeg] at hAdj'
  exact hnot hAdj'

private theorem geoSigma_second_next_eq_prev {V : Type*} [Fintype V]
    (σ : Equiv.Perm V) (a : V)
    (h₁ : σ a ≠ a) (h₂ : σ.symm a ≠ a) (h₃ : σ a ≠ σ.symm a)
    (hcard : Fintype.card V = 3) : σ (σ a) = σ.symm a := by
  let T : Finset V := {a, σ a, σ.symm a}
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h₁.symm, h₂.symm⟩)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact h₃)]
    simp
  have hT : T = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ T) (by
      rw [Finset.card_univ, hcard, hTcard])
  have hmem : σ (σ a) ∈ T := by rw [hT]; exact Finset.mem_univ _
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · have he := congrArg σ.symm h
    have hc : σ a = σ.symm a := by simpa using he
    exact (h₃ hc).elim
  · have hc : σ a = a := σ.injective h
    exact (h₁ hc).elim
  · exact h

private theorem exteriorArc_terminal_tip_adj
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (hgood : ¬ S.exteriorBad E (S.exteriorArcIdx E a 0))
    (hdeg0 : S.exteriorDeg E (S.exteriorArcIdx E a 0) = 3) :
    S.G.Adj (S.exteriorArcNegVertex E (a := a))
      ((S.exteriorR E (S.exteriorArcIdx E a 0)).val) := by
  let idx := S.exteriorArcIdx E a 0
  let v := S.exteriorVert E idx
  let prev := S.exteriorPrev E idx
  let σ := S.geoSigma S.G le_rfl v
  have hcard : Fintype.card {w : Fin n // S.G.Adj v w} = 3 := by
    simpa [exteriorDeg, v, idx] using hdeg0
  have hσ := S.sigma_neighbors_distinct S.G le_rfl v prev (by rw [hcard])
  have hsq := S.geoSigma_second_next_eq_prev σ prev hσ.1 hσ.2.1 hσ.2.2 hcard
  have hLq : (S.exteriorL E idx).val = (S.exteriorR E idx).val := by
    change (σ (σ prev)).val = (σ.symm prev).val
    exact congrArg Subtype.val hsq
  have hgood' : (S.exteriorL E idx).val =
      (S.exteriorR E (finRotate S.exteriorSize idx)).val :=
    not_ne_iff.mp hgood
  have hR : (S.exteriorR E (finRotate S.exteriorSize idx)).val =
      (S.exteriorR E idx).val := hgood'.symm.trans hLq
  have hAdj := (S.exteriorR E (finRotate S.exteriorSize idx)).property
  rw [hR] at hAdj
  have hNeg : S.exteriorArcNegVertex E (a := a) =
      S.exteriorVert E (finRotate S.exteriorSize idx) :=
    S.exteriorNext_val E idx
  rw [hNeg]
  exact hAdj

private theorem exteriorArc_terminal_angle
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (hc : Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3)
    (hdeg0 : S.exteriorDeg E (S.exteriorArcIdx E a 0) = 3) :
    ∃ φ : ℝ, 2 * Real.pi / 3 ≤ φ ∧ φ ≤ 5 * Real.pi / 3 ∧
      Swanepoel.NormalGeometry.f (S.exteriorArc_chain E he hd hc) S.p
        (S.exteriorNext E (S.exteriorArcIdx E a 0)).val =
          Swanepoel.ChainStep.cis φ := by
  let C := S.exteriorArc_chain E he hd hc
  let idx := S.exteriorArcIdx E a 0
  let p0 := S.exteriorVert E idx
  let p1 := S.exteriorVert E (S.exteriorArcIdx E a 1)
  let pNeg := (S.exteriorNext E idx).val
  let G := S.exteriorGap E idx (S.exteriorPrev E idx)
  let φ := 2 * Real.pi - G
  have hp0 : C.p 0 = S.p p0 := by rfl
  have hp1 : C.p 1 = S.p p1 := by rfl
  have hrot : C.rotation 0 * (S.p p1 - S.p p0) = 1 := by
    rw [← hp1, ← hp0, ← C.frame_sub]
    simpa [C.θ_zero, Swanepoel.ChainStep.cis] using
      C.frame_step 0 (i := 0) (by decide)
  have hgeom := S.cis_gapAngle S.G le_rfl p0 (S.exteriorPrev E idx)
  change (S.p pNeg - S.p p0) * Swanepoel.ChainStep.cis G =
      S.p (S.exteriorPrev E idx).val - S.p p0 at hgeom
  rw [S.exteriorArc_prev_val E he (i := 0) (by omega)] at hgeom
  have hmul : (C.rotation 0 * (S.p pNeg - S.p p0)) *
      Swanepoel.ChainStep.cis G = 1 := by
    calc
      _ = C.rotation 0 * ((S.p pNeg - S.p p0) * Swanepoel.ChainStep.cis G) := by ring
      _ = C.rotation 0 * (S.p p1 - S.p p0) :=
        congrArg (fun z : ℂ => C.rotation 0 * z) hgeom
      _ = 1 := hrot
  have hcisInv : Swanepoel.ChainStep.cis G *
      Swanepoel.ChainStep.cis (-G) = 1 := by
    rw [← Swanepoel.ChainStep.cis_add]
    simp [Swanepoel.ChainStep.cis]
  have hframe : C.frame 0 (S.p pNeg) = Swanepoel.ChainStep.cis (-G) := by
    have hz : C.frame 0 (S.p p0) = 0 := by
      rw [← hp0]
      exact C.frame_initial 0
    have hval : C.rotation 0 * (S.p pNeg - S.p p0) =
        Swanepoel.ChainStep.cis (-G) := by
      calc
        _ = (C.rotation 0 * (S.p pNeg - S.p p0)) *
            (Swanepoel.ChainStep.cis G * Swanepoel.ChainStep.cis (-G)) := by
              rw [hcisInv, mul_one]
        _ = ((C.rotation 0 * (S.p pNeg - S.p p0)) *
            Swanepoel.ChainStep.cis G) * Swanepoel.ChainStep.cis (-G) := by ring
        _ = Swanepoel.ChainStep.cis (-G) := by rw [hmul, one_mul]
    calc
      C.frame 0 (S.p pNeg) =
          C.frame 0 (S.p pNeg) - C.frame 0 (S.p p0) := by rw [hz]; ring
      _ = C.rotation 0 * (S.p pNeg - S.p p0) := C.frame_sub 0 _ _
      _ = Swanepoel.ChainStep.cis (-G) := hval
  have hlow : Real.pi / 3 ≤ G := by
    dsimp [G, exteriorGap]
    exact S.gapAngle_ge_pi_div_three S.G le_rfl (E.order idx).val
  have hcard : Fintype.card {w : Fin n // S.G.Adj (S.exteriorVert E idx) w} = 3 := by
    simpa [exteriorDeg, idx] using hdeg0
  have hσ := S.sigma_neighbors_distinct S.G le_rfl (S.exteriorVert E idx)
    (S.exteriorPrev E idx) (by rw [hcard])
  have hgapEx := S.gap_excess_le_interior S.G le_rfl (S.exteriorVert E idx)
    (S.exteriorNext E idx) {S.exteriorPrev E idx} (by
      simp only [Finset.mem_singleton]
      change S.geoSigma S.G le_rfl (S.exteriorVert E idx) (S.exteriorPrev E idx) ≠
        S.exteriorPrev E idx
      exact hσ.1)
  have hcardReal : (Fintype.card {w : Fin n // S.G.Adj (S.exteriorVert E idx) w} : ℝ) = 3 := by
    exact_mod_cast hcard
  have hgapEx' :
      G - Real.pi / 3 ≤ 2 * Real.pi -
        S.exteriorGap E idx (S.exteriorNext E idx) -
          ((3 : ℝ) - 1) * (Real.pi / 3) := by
    rw [Finset.sum_singleton, hcardReal] at hgapEx
    simpa [G, exteriorGap] using hgapEx
  have hnextlow : Real.pi / 3 ≤ S.exteriorGap E idx (S.exteriorNext E idx) := by
    change Real.pi / 3 ≤ S.gapAngle S.G le_rfl
      ⟨((S.exteriorNext E idx).val, S.exteriorVert E idx),
        (S.exteriorNext E idx).property.symm⟩
    exact S.gapAngle_ge_pi_div_three S.G le_rfl _
  have hupper : G ≤ 4 * Real.pi / 3 := by linarith
  have hφlo : 2 * Real.pi / 3 ≤ φ := by dsimp [φ]; linarith
  have hφhi : φ ≤ 5 * Real.pi / 3 := by dsimp [φ]; linarith
  have hcis2pi : Swanepoel.ChainStep.cis (2 * Real.pi) = 1 := by
    have hpi : Swanepoel.ChainStep.cis Real.pi = (-1 : ℂ) :=
      exteriorArc_cis_pi S
    rw [show 2 * Real.pi = Real.pi + Real.pi by ring,
      Swanepoel.ChainStep.cis_add]
    simp only [hpi]
    norm_num
  have hcisφ : Swanepoel.ChainStep.cis φ = Swanepoel.ChainStep.cis (-G) := by
    dsimp [φ]
    calc
      Swanepoel.ChainStep.cis (2 * Real.pi - G) =
          Swanepoel.ChainStep.cis (2 * Real.pi + -G) := by congr 1 <;> ring
      _ = Swanepoel.ChainStep.cis (2 * Real.pi) *
          Swanepoel.ChainStep.cis (-G) := Swanepoel.ChainStep.cis_add _ _
      _ = Swanepoel.ChainStep.cis (-G) := by rw [hcis2pi, one_mul]
  refine ⟨φ, hφlo, hφhi, ?_⟩
  change C.frame 0 (S.p pNeg) = Swanepoel.ChainStep.cis φ
  rw [hframe, ← hcisφ]

private theorem exteriorArc_terminal_data
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (hc : Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3)
    (hmarks : 6 ≤ (Swanepoel.ArcExtract.marks (S.exteriorDeg E)).card) :
    S.exteriorDeg E (S.exteriorArcIdx E a 0) = 3 ∧
    (∃ φ : ℝ, 2 * Real.pi / 3 ≤ φ ∧ φ ≤ 5 * Real.pi / 3 ∧
      Swanepoel.NormalGeometry.f (S.exteriorArc_chain E he hd hc) S.p
        (S.exteriorNext E (S.exteriorArcIdx E a 0)).val =
          Swanepoel.ChainStep.cis φ) ∧
    ¬ S.G.Adj (S.exteriorNext E (S.exteriorArcIdx E a 0)).val
      (S.exteriorVert E (S.exteriorArcIdx E a 1)) ∧
    ((S.exteriorDeg E (finRotate S.exteriorSize (S.exteriorArcIdx E a 0)) ≤ 3) ∨
      (S.exteriorDeg E (finRotate S.exteriorSize (S.exteriorArcIdx E a 0)) ≤ 4 ∧
        S.G.Adj (S.exteriorNext E (S.exteriorArcIdx E a 0)).val
          (S.exteriorR E (S.exteriorArcIdx E a 0)).val)) := by
  have hdeg0 : S.exteriorDeg E (S.exteriorArcIdx E a 0) = 3 := by
    change S.exteriorDeg E (Swanepoel.ArcExtract.x a (CyclicGap.length a - 0)) = 3
    rw [Nat.sub_zero]
    exact Swanepoel.arc_nextMark_degree a
  have hφ := S.exteriorArc_terminal_angle E he hd hc hdeg0
  have hchord := S.exteriorArc_terminal_no_chord (a := a) E hd hmarks
  have hchoice := S.exteriorArc_terminal_choice E he hd
  refine ⟨hdeg0, hφ, hchord, ?_⟩
  rcases hchoice with hs | hl
  · exact Or.inl (by rw [hs.2])
  · exact Or.inr ⟨by rw [hl.2.2],
      S.exteriorArc_terminal_tip_adj E hl.2.1 hdeg0⟩

end ExteriorTerminal

section SwanepoelGraph

open scoped EuclideanGeometry
open Classical

private theorem exterior_arc_false (E : Exterior S)
    (hd : ∀ i, 3 ≤ S.exteriorDeg E i)
    (hm : 6 ≤ (Swanepoel.ArcExtract.marks (S.exteriorDeg E)).card)
    {a : ↥(Swanepoel.ArcExtract.marks (S.exteriorDeg E))}
    (he : Swanepoel.ArcExtract.eligible (S.exteriorBad E) a)
    (hc : Swanepoel.arcBendCost (S.exteriorSurplus E) a < Real.pi / 3)
    (hexpand : ∀ T : Finset (Fin n), (T : Set (Fin n)).Pairwise (fun x y => ¬ S.G.Adj x y) →
      T.card ≤ 8 → 4 * T.card ≤ (contactNeighborhood S T).card) : False := by
  classical
  let C := S.exteriorArc_chain E he hd hc
  let idx := S.exteriorArcIdx E a
  let p (j : ℕ) := S.exteriorVert E (idx j)
  let q (j : ℕ) := (S.exteriorR E (idx j)).val
  let z := (S.exteriorNext E (idx 0)).val
  let d := CyclicGap.length a
  have hlen : 15 ≤ d := he.1
  have hdim : d + 1 < S.exteriorSize := Swanepoel.shortGap_end_lt hm a
  have hi (j : ℕ) : idx j = (finRotate S.exteriorSize ^ (d - j)) a.val := rfl
  have hz : z = S.exteriorVert E ((finRotate S.exteriorSize ^ (d + 1)) a.val) := by
    dsimp only [z]
    rw [S.exteriorNext_val]
    change S.exteriorVert E (finRotate S.exteriorSize (idx 0)) = _
    rw [hi, Nat.sub_zero, pow_succ', Equiv.Perm.mul_apply]
  have hpos {i j : ℕ} (hi' : i < S.exteriorSize) (hj' : j < S.exteriorSize)
      (h : S.exteriorVert E ((finRotate S.exteriorSize ^ i) a.val) =
        S.exteriorVert E ((finRotate S.exteriorSize ^ j) a.val)) : i = j := by
    let f := Swanepoel.chordIndices (le_refl S.exteriorSize) a.val
    have hfin : (⟨i, hi'⟩ : Fin S.exteriorSize) = ⟨j, hj'⟩ :=
      f.injective ((S.exteriorVert E).injective h)
    exact congrArg Fin.val hfin
  have hpinj : Set.InjOn p (Set.Iic 12) := by
    intro i hI j hJ h
    change i ≤ 12 at hI
    change j ≤ 12 at hJ
    change S.exteriorVert E (idx i) = S.exteriorVert E (idx j) at h
    rw [hi i, hi j] at h
    have hh := hpos (by omega) (by omega) h
    omega
  have hneg (j : ℕ) (hj : j ≤ 12) : z ≠ p j := by
    intro h
    change z = S.exteriorVert E (idx j) at h
    rw [hz, hi] at h
    have hh := hpos hdim (by omega) h
    omega
  have hedge (j : ℕ) (hj : j < 12) : S.G.Adj (p j) (p (j + 1)) :=
    (S.exteriorArc_edge E he (by omega : j < 13)).symm
  have htip (j : ℕ) (hj : j < 12) : S.G.Adj (p j) (q j) ∧ S.G.Adj (p (j + 1)) (q j) := by
    have hgood := (S.exteriorArc_four_good E he j (by omega)).2
    have ht := (S.exteriorL E (idx (j + 1))).property
    have ht' := not_ne_iff.mp hgood
    rw [S.exteriorArc_idx_step E he (by omega : j < 13)] at ht'
    refine ⟨(S.exteriorR E (idx j)).property, ?_⟩
    change S.G.Adj (p (j + 1)) (S.exteriorR E (idx j)).val
    rw [← ht']
    exact ht
  have hdeg (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 12) :
      (Finset.univ.filter (S.G.Adj (p j))).card = 4 := by
    rw [S.exterior_degree_filter E (idx j)]
    simpa only [Nat.sub_add_cancel hj] using
      (S.exteriorArc_four_good E he (j - 1) (by omega)).1
  obtain ⟨hzero, hφ, hchord, hterminal⟩ := S.exteriorArc_terminal_data E he hd hc hm
  refine Swanepoel.gentle_arc_false C S.p S.G.Adj p q z
    (fun _ _ h => h.symm) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    hφ hpinj hneg hchord hedge htip hdeg ?_ ?_ ?_
  · intro x y h
    rw [dist_eq_norm]
    exact (S.G_adj_iff x y).mp h
  · intro x y h
    rw [dist_eq_norm]
    exact S.hsep x y h
  · rw [S.exterior_degree_filter E (idx 0)]
    exact hzero
  · have hza : S.G.Adj z (p 0) := (S.exteriorArc_neg_adj E (a := a)).symm
    have hzd : (Finset.univ.filter (S.G.Adj z)).card = S.exteriorDeg E (finRotate S.exteriorSize (idx 0)) := by
      calc
        _ = (Finset.univ.filter (S.G.Adj (S.exteriorVert E (finRotate S.exteriorSize (idx 0))))).card :=
          congrArg (fun v => (Finset.univ.filter (S.G.Adj v)).card) (S.exteriorNext_val E (idx 0))
        _ = _ := S.exterior_degree_filter E _
    rw [hzd]
    exact hterminal.elim (fun h => Or.inl ⟨h, hza⟩)
      (fun h => Or.inr ⟨h.1, hza, h.2⟩)
  · intro T ht hk
    have he' := hexpand T ht hk
    convert he' using 1
    congr 1
    ext x
    simp [contactNeighborhood]

omit S in
private theorem minBad_false {X : Finset ℝ²} (h : Swanepoel.MinBad X) : False := by
  classical
  obtain ⟨T, e, ha⟩ := setup_of_config X (minBad_four_le h) h.separated
  obtain ⟨hc, hk⟩ := connected_of_config_cut T e ha (fun _ hA _ hB => h.no_separator hA hB)
  obtain ⟨E⟩ := T.exterior_exists hc hk
  obtain ⟨hg, hlr⟩ := minBad_degree_data h T e ha
  have hs v : 1 ≤ (T.leftEdges T.G v).card + (T.rightEdges T.G v).card := by
    rw [hlr]
    exact (by decide : 1 ≤ 3).trans (hg v)
  have hd (i : Fin T.exteriorSize) : 3 ≤ T.exteriorDeg E i := by
    rw [← T.exterior_degree_card E i]
    exact hg _
  have hx (C : Finset (Fin X.card)) (hi : (C : Set (Fin X.card)).Pairwise (fun x y => ¬ T.G.Adj x y))
      (hn : C.card ≤ 8) : 4 * C.card ≤ (contactNeighborhood T C).card :=
    minBad_independent_expansion h T e ha C (fun _ hi' _ hj' hne => hi hi' hj' hne) hn
  obtain ⟨a, he, hb⟩ := T.exterior_extract E hg hs hx
  exact T.exterior_arc_false E hd (T.exterior_marks_at_least_six E hd hs) he hb hx

end SwanepoelGraph
end GeoSetup

end SlabAndSqueeze

end Erdos1084Harborth

theorem OMA.solution : type_of% @Erdos1066.erdos_1066.variants.swanepoel := by
  intro n
  refine Swanepoel.ratio_of_finite_sets ?_ n
  intro X hX
  by_contra h
  obtain ⟨Y, _, hY⟩ := Swanepoel.exists_minBad_subset hX h
  exact Erdos1084Harborth.GeoSetup.minBad_false hY
