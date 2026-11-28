import OMAReductions.R_opg_directed_cycle_of_length_twice_the_minimum_outdegree_R1
import Mathlib

/-!
Thomassé's conjecture for tournaments.
* Rédei's theorem: a tournament has a Hamiltonian directed path. A vertex `a` is inserted into a
  directed path `b :: t`: in front if `a → b`, otherwise (`b → a`) recursively into `t`; the
  recursion keeps the head of the new path equal to `a` or to the old head.
* Counting: the arcs and the reversed arcs partition the off-diagonal pairs, so there are
  `(n * n - n) / 2` arcs, at least `n * k`; hence `2k + 1 ≤ n`.
-/

namespace OMA.ThomTour

open OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree

lemma insert_path {V : Type} (R : V → V → Prop) (a : V) : ∀ l : List V, List.IsChain R l →
    (∀ x ∈ l, R a x ∨ R x a) →
    ∃ l' : List V, List.IsChain R l' ∧ l'.Perm (a :: l) ∧
      (l'.head? = some a ∨ l'.head? = l.head?) := by
  intro l
  induction l with
  | nil =>
    intro _ _
    exact ⟨[a], List.isChain_singleton a, List.Perm.refl _, Or.inl rfl⟩
  | cons b t ih =>
    intro hl hab
    rcases hab b List.mem_cons_self with h | h
    · refine ⟨a :: b :: t, ?_, List.Perm.refl _, Or.inl rfl⟩
      exact List.isChain_cons_cons.2 ⟨h, hl⟩
    · have hl' := List.isChain_cons.1 hl
      obtain ⟨l'', hc, hp, hh⟩ := ih hl'.2 (fun x hx => hab x (List.mem_cons_of_mem b hx))
      refine ⟨b :: l'', ?_, ?_, Or.inr rfl⟩
      · refine List.isChain_cons.2 ⟨?_, hc⟩
        intro y hy
        rcases hh with hh | hh
        · rw [hh, Option.mem_some_iff] at hy
          subst hy
          exact h
        · rw [hh] at hy
          exact hl'.1 y hy
      · exact (hp.cons b).trans (List.Perm.swap a b t)

lemma ham_path {V : Type} (R : V → V → Prop) (htour : ∀ x y, x ≠ y → R x y ∨ R y x) :
    ∀ L : List V, L.Nodup → ∃ l : List V, List.IsChain R l ∧ l.Perm L := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨[], List.isChain_nil, List.Perm.refl _⟩
  | cons x L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨l, hc, hp⟩ := ih hnd.2
    have hx : ∀ y ∈ l, R x y ∨ R y x := by
      intro y hy
      have hyL : y ∈ L := hp.subset hy
      exact htour x y (fun hxy => hnd.1 (hxy ▸ hyL))
    obtain ⟨l', hc', hp', -⟩ := insert_path R x l hc hx
    exact ⟨l', hc', hp'.trans (hp.cons x)⟩

lemma card_bound {V : Type} [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (k : ℕ) (hor : IsOriented G) (htour : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u)
    (hk : ∀ v, k ≤ outdegree G v) : 2 * k + 1 ≤ Fintype.card V := by
  classical
  set n := Fintype.card V with hn
  let A : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)
  let B : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter (fun p => G.Adj p.2 p.1)
  have hA : A.card = ∑ v, outdegree G v := by
    simp only [A, outdegree, Finset.card_filter]
    rw [Finset.sum_product]
  have hAB : B.card = A.card := by
    apply Finset.card_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [A, B, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product,
        Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p hp
      simp only [A, B, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product,
        Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p _
      rfl
    · intro p _
      rfl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    simp only [A, B, Finset.mem_filter] at hpA hpB
    exact hor _ _ hpA.2 hpB.2
  have hunion : A ∪ B = (Finset.univ : Finset V).offDiag := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, Finset.mem_offDiag]
    constructor
    · rintro (h | h) <;> intro heq
      · rw [heq] at h
        exact hor _ _ h h
      · rw [heq] at h
        exact hor _ _ h h
    · intro h
      exact htour _ _ h
  have hcard : A.card + B.card = n * n - n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.offDiag_card, Finset.card_univ]
  have hsum : n * k ≤ ∑ v, outdegree G v := by
    calc n * k = ∑ _v : V, k := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ v, outdegree G v := Finset.sum_le_sum (fun v _ => hk v)
  have hpos : 0 < n := Fintype.card_pos
  have hle : n * (2 * k + 1) ≤ n * n := by
    have h1 : n ≤ n * n := Nat.le_mul_self n
    have h2 : 2 * (n * k) ≤ n * n - n := by omega
    have h3 : n * (2 * k + 1) = 2 * (n * k) + n := by ring
    omega
  exact Nat.le_of_mul_le_mul_left hle hpos

end OMA.ThomTour

open OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree in
theorem OMA.solution :
    OMA.R_opg_directed_cycle_of_length_twice_the_minimum_outdegree_R1.H1 := by
  intro V _ _ G _ k hor htour hk
  classical
  obtain ⟨l, hc, hp⟩ := OMA.ThomTour.ham_path G.Adj htour (Finset.univ.toList)
    (Finset.nodup_toList _)
  have hlen : l.length = Fintype.card V := by
    rw [hp.length_eq, Finset.length_toList, Finset.card_univ]
  have hnd : l.Nodup := hp.nodup_iff.2 (Finset.nodup_toList _)
  have hn := OMA.ThomTour.card_bound G k hor htour hk
  refine ⟨fun i => l[i.val]'(by omega), ?_, ?_⟩
  · intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hij)
  · intro i
    exact (List.isChain_iff_getElem.1 hc) i.val (by omega)
