import OMAStatements.S_oeis_a182531
import Mathlib

-- Problem: A182531: Extremal graph numbers for a triangle with an edge off it.
-- Upstream: formal-conjectures statements/oeis-a182531.lean:0 (declaration OMA.S_oeis_a182531.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Lower bound: the triangle is contained in the paw, so ex(n, paw) is at least the Turan
-- number ex(n, K3) = n^2/4 (Mathlib); for n = 3 the complete graph has 3 edges and no paw.
-- Upper bound, by induction on n: a paw-free graph without a triangle has at most n^2/4 edges
-- (Turan). If it has a triangle, no vertex outside the triangle is adjacent to it. Deleting a
-- vertex v loses deg v edges and leaves at most ex(n-1, paw) edges: a triangle vertex has
-- degree 2 (used for n >= 5), and for n = 4 the fourth vertex has degree 0.

namespace Paw182531Proof
open SimpleGraph Finset OMA.S_oeis_a182531

lemma paw_isContained {V : Type} {G : SimpleGraph V} {a b c d : V} (hab : G.Adj a b)
    (hac : G.Adj a c) (hbc : G.Adj b c) (had : G.Adj a d) (hdb : d ≠ b) (hdc : d ≠ c) :
    paw ⊑ G := by
  rw [isContained_iff_exists_le_comap]
  have h1 := hab.ne
  have h2 := hac.ne
  have h3 := hbc.ne
  have h4 := had.ne
  have h1' := h1.symm
  have h2' := h2.symm
  have h3' := h3.symm
  have h4' := h4.symm
  have h5' := hdb.symm
  have h6' := hdc.symm
  refine ⟨⟨![a, b, c, d], ?_⟩, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    rw [SimpleGraph.comap_adj]
    have hba := hab.symm
    have hca := hac.symm
    have hcb := hbc.symm
    have hda := had.symm
    change G.Adj (![a, b, c, d] i) (![a, b, c, d] j)
    fin_cases i <;> fin_cases j <;> simp_all [paw]

lemma nbr_mem {V : Type} [DecidableEq V] {G : SimpleGraph V} (hG : paw.Free G) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) {x y : V}
    (hx : x ∈ ({a, b, c} : Finset V)) (hxy : G.Adj x y) : y ∈ ({a, b, c} : Finset V) := by
  by_contra hy
  simp only [mem_insert, mem_singleton, not_or] at hy
  obtain ⟨hya, hyb, hyc⟩ := hy
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx
  · rw [hx] at hxy
    exact hG (paw_isContained hab hac hbc hxy hyb hyc)
  · rw [hx] at hxy
    exact hG (paw_isContained hab.symm hbc hac hxy hya hyc)
  · rw [hx] at hxy
    exact hG (paw_isContained hac.symm hbc.symm hab hxy hya hyb)

def g (n : ℕ) : ℕ := if n = 3 then 3 else n ^ 2 / 4

lemma mantel_bound (n : ℕ) :
    (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 = n ^ 2 / 4 := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · have h1 : n % 2 = 0 := by omega
    rw [h1]
    simp
  · have h1 : n % 2 = 1 := by omega
    have h2 : n ^ 2 = 4 * (k * k + k) + 1 := by rw [hk]; ring
    rw [h1, h2]
    simp
    omega

lemma edge_bound (n : ℕ) (ih : ∀ m, m + 1 = n → extremalNumber m paw ≤ g m)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : paw.Free G) :
    #G.edgeFinset ≤ g n := by
  by_cases hcf : G.CliqueFree 3
  · have h := CliqueFree.card_edgeFinset_le (r := 2) hcf
    simp only [Fintype.card_fin] at h
    rw [mantel_bound] at h
    unfold g
    split_ifs with h3
    · have e : n ^ 2 / 4 ≤ 3 := by rw [h3]; decide
      exact le_trans h e
    · exact h
  · simp only [CliqueFree, not_forall, not_not] at hcf
    obtain ⟨T, hT⟩ := hcf
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hT
    have hcard : ({a, b, c} : Finset (Fin n)).card = 3 := hT.card_eq
    have hn3 : 3 ≤ n := by
      have h := Finset.card_le_univ ({a, b, c} : Finset (Fin n))
      rw [hcard, Fintype.card_fin] at h
      exact h
    have hdel : ∀ v, #G.edgeFinset ≤ extremalNumber (n - 1) paw + G.degree v := by
      intro v
      have h1 := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hG v
      rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin] at h1
      omega
    have ih' := ih (n - 1) (by omega)
    have hdega : G.degree a ≤ 2 := by
      have hsub : G.neighborFinset a ⊆ {b, c} := by
        intro y hy
        rw [mem_neighborFinset] at hy
        have hmem := nbr_mem hG hab hac hbc (x := a) (by simp) hy
        simp only [mem_insert, mem_singleton] at hmem ⊢
        rcases hmem with h | h | h
        · rw [h] at hy
          exact absurd hy (G.irrefl)
        · exact Or.inl h
        · exact Or.inr h
      calc G.degree a = (G.neighborFinset a).card := (G.card_neighborFinset_eq_degree a).symm
        _ ≤ ({b, c} : Finset (Fin n)).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    rcases (by omega : n = 3 ∨ n = 4 ∨ 5 ≤ n) with h3 | h4 | h5
    · have h := G.card_edgeFinset_le_card_choose_two
      rw [Fintype.card_fin] at h
      have hc : n.choose 2 = 3 := by rw [h3]; decide
      rw [hc] at h
      unfold g
      rw [if_pos h3]
      exact h
    · obtain ⟨d, hd⟩ : ∃ d, d ∉ ({a, b, c} : Finset (Fin n)) := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        have hu : ({a, b, c} : Finset (Fin n)) = univ := Finset.eq_univ_iff_forall.mpr hall
        rw [hu, Finset.card_univ, Fintype.card_fin] at hcard
        omega
      have huniv : insert d ({a, b, c} : Finset (Fin n)) = univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_insert_of_notMem hd, hcard, Fintype.card_fin]
        omega
      have hdeg : G.degree d = 0 := by
        rw [← G.card_neighborFinset_eq_degree d, Finset.card_eq_zero,
          Finset.eq_empty_iff_forall_notMem]
        intro y hy
        rw [mem_neighborFinset] at hy
        have hyu : y ∈ insert d ({a, b, c} : Finset (Fin n)) := by rw [huniv]; exact mem_univ y
        rcases Finset.mem_insert.mp hyu with hyd | hyT
        · rw [hyd] at hy
          exact G.irrefl hy
        · exact hd (nbr_mem hG hab hac hbc hyT hy.symm)
      have h := hdel d
      rw [hdeg] at h
      have hg3 : g (n - 1) = 3 := by unfold g; rw [if_pos (by omega)]
      have hg4 : g n = 4 := by unfold g; rw [if_neg (by omega), h4]; decide
      rw [hg3] at ih'
      rw [hg4]
      omega
    · have h := hdel a
      have hg1 : g (n - 1) = (n - 1) ^ 2 / 4 := by unfold g; rw [if_neg (by omega)]
      have hg2 : g n = n ^ 2 / 4 := by unfold g; rw [if_neg (by omega)]
      rw [hg1] at ih'
      rw [hg2]
      have key : (n - 1) ^ 2 / 4 + 2 ≤ n ^ 2 / 4 := by
        obtain ⟨m, hm⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
        have e1 : (n - 1) ^ 2 = m ^ 2 + 8 * m + 16 := by
          have h' : n - 1 = m + 4 := by omega
          rw [h']; ring
        have e2 : n ^ 2 = m ^ 2 + 10 * m + 25 := by rw [hm]; ring
        rw [e1, e2]
        omega
      omega

theorem upper (n : ℕ) : extremalNumber n paw ≤ g n := by
  induction n with
  | zero =>
    have h := (extremalNumber_le_iff (V := Fin 0) paw (g 0)).mpr
      (fun G _ hG => edge_bound 0 (fun m hm => absurd hm (by omega)) G hG)
    rwa [Fintype.card_fin] at h
  | succ k ih =>
    have h := (extremalNumber_le_iff (V := Fin (k + 1)) paw (g (k + 1))).mpr
      (fun G _ hG => edge_bound (k + 1)
        (fun m hm => by
          have hmk : m = k := by omega
          rw [hmk]; exact ih) G hG)
    rwa [Fintype.card_fin] at h

theorem lower (n : ℕ) : n ^ 2 / 4 ≤ extremalNumber n paw := by
  have hK3 : (⊤ : SimpleGraph (Fin 3)) ⊑ paw := by
    rw [isContained_iff_exists_le_comap]
    refine ⟨Fin.castSuccEmb, ?_⟩
    intro i j hij
    rw [SimpleGraph.comap_adj]
    have hne : i ≠ j := hij
    refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
    · intro h
      exact hne (Fin.castSuccEmb.injective h)
    · exact i.isLt
    · exact j.isLt
  have h := hK3.extremalNumber_le (n := n)
  have h2 : Fintype.card (Fin 3) - 1 = 2 := by simp
  rw [extremalNumber_top, card_edgeFinset_turanGraph, h2, mantel_bound] at h
  exact h

theorem lower3 : 3 ≤ extremalNumber 3 paw := by
  have hfree : paw.Free (⊤ : SimpleGraph (Fin 3)) := by
    rintro ⟨f⟩
    have h := Fintype.card_le_of_injective f f.injective
    simp at h
  have h := card_edgeFinset_le_extremalNumber hfree
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at h
  have hc : Nat.choose 3 2 = 3 := by decide
  rw [hc] at h
  exact h

end Paw182531Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182531.main := by
  intro n _
  apply le_antisymm
  · have h := Paw182531Proof.upper n
    unfold Paw182531Proof.g at h
    exact h
  · split_ifs with h3
    · rw [h3]
      exact Paw182531Proof.lower3
    · exact Paw182531Proof.lower n
