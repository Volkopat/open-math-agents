import OMAStatements.S_arxiv_2404_04039
import Mathlib

namespace OMA.P_arxiv_2404_04039

open OMA.S_arxiv_2404_04039

/-- Adjacency predicate for `G₁` on `Fin 8` (14 edges). -/
private def adj1B (u v : Fin 8) : Bool :=
  let a := min u.val v.val
  let b := max u.val v.val
  (a == 0 && (b == 1 || b == 2 || b == 4 || b == 5 || b == 7)) ||
  (a == 1 && (b == 2 || b == 4)) ||
  (a == 2 && (b == 3 || b == 5 || b == 7)) ||
  (a == 3 && b == 6) ||
  (a == 4 && (b == 5 || b == 7)) ||
  (a == 5 && b == 6)

/-- Adjacency predicate for `G₂` on `Fin 8` (13 edges). -/
private def adj2B (u v : Fin 8) : Bool :=
  let a := min u.val v.val
  let b := max u.val v.val
  (a == 0 && (b == 2 || b == 3 || b == 5 || b == 6)) ||
  (a == 1 && (b == 2 || b == 4)) ||
  (a == 2 && (b == 3 || b == 5 || b == 7)) ||
  (a == 3 && b == 6) ||
  (a == 4 && (b == 5 || b == 7)) ||
  (a == 5 && b == 6)

private lemma adj1B_symm : ∀ u v : Fin 8, adj1B u v = adj1B v u := by decide
private lemma adj1B_irrefl : ∀ u : Fin 8, adj1B u u = false := by decide
private lemma adj2B_symm : ∀ u v : Fin 8, adj2B u v = adj2B v u := by decide
private lemma adj2B_irrefl : ∀ u : Fin 8, adj2B u u = false := by decide

def G1 : SimpleGraph (Fin 8) where
  Adj u v := adj1B u v = true
  symm := ⟨fun u v h => by
    rw [adj1B_symm]
    exact h⟩
  loopless := ⟨fun u h => by
    change adj1B u u = true at h
    rw [adj1B_irrefl] at h
    exact Bool.noConfusion h⟩

def G2 : SimpleGraph (Fin 8) where
  Adj u v := adj2B u v = true
  symm := ⟨fun u v h => by
    rw [adj2B_symm]
    exact h⟩
  loopless := ⟨fun u h => by
    change adj2B u u = true at h
    rw [adj2B_irrefl] at h
    exact Bool.noConfusion h⟩

/-- Exact shortest-path distance table for `G1`. -/
private def d1 (u v : Fin 8) : ℕ :=
  match u.val, v.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 1 | 0, 3 => 2 | 0, 4 => 1 | 0, 5 => 1 | 0, 6 => 2 | 0, 7 => 1
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 1 | 1, 3 => 2 | 1, 4 => 1 | 1, 5 => 2 | 1, 6 => 3 | 1, 7 => 2
  | 2, 0 => 1 | 2, 1 => 1 | 2, 2 => 0 | 2, 3 => 1 | 2, 4 => 2 | 2, 5 => 1 | 2, 6 => 2 | 2, 7 => 1
  | 3, 0 => 2 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0 | 3, 4 => 3 | 3, 5 => 2 | 3, 6 => 1 | 3, 7 => 2
  | 4, 0 => 1 | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 | 4, 4 => 0 | 4, 5 => 1 | 4, 6 => 2 | 4, 7 => 1
  | 5, 0 => 1 | 5, 1 => 2 | 5, 2 => 1 | 5, 3 => 2 | 5, 4 => 1 | 5, 5 => 0 | 5, 6 => 1 | 5, 7 => 2
  | 6, 0 => 2 | 6, 1 => 3 | 6, 2 => 2 | 6, 3 => 1 | 6, 4 => 2 | 6, 5 => 1 | 6, 6 => 0 | 6, 7 => 3
  | 7, 0 => 1 | 7, 1 => 2 | 7, 2 => 1 | 7, 3 => 2 | 7, 4 => 1 | 7, 5 => 2 | 7, 6 => 3 | 7, 7 => 0
  | _, _ => 0

/-- Exact shortest-path distance table for `G2`. -/
private def d2 (u v : Fin 8) : ℕ :=
  match u.val, v.val with
  | 0, 0 => 0 | 0, 1 => 2 | 0, 2 => 1 | 0, 3 => 1 | 0, 4 => 2 | 0, 5 => 1 | 0, 6 => 1 | 0, 7 => 2
  | 1, 0 => 2 | 1, 1 => 0 | 1, 2 => 1 | 1, 3 => 2 | 1, 4 => 1 | 1, 5 => 2 | 1, 6 => 3 | 1, 7 => 2
  | 2, 0 => 1 | 2, 1 => 1 | 2, 2 => 0 | 2, 3 => 1 | 2, 4 => 2 | 2, 5 => 1 | 2, 6 => 2 | 2, 7 => 1
  | 3, 0 => 1 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0 | 3, 4 => 3 | 3, 5 => 2 | 3, 6 => 1 | 3, 7 => 2
  | 4, 0 => 2 | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 | 4, 4 => 0 | 4, 5 => 1 | 4, 6 => 2 | 4, 7 => 1
  | 5, 0 => 1 | 5, 1 => 2 | 5, 2 => 1 | 5, 3 => 2 | 5, 4 => 1 | 5, 5 => 0 | 5, 6 => 1 | 5, 7 => 2
  | 6, 0 => 1 | 6, 1 => 3 | 6, 2 => 2 | 6, 3 => 1 | 6, 4 => 2 | 6, 5 => 1 | 6, 6 => 0 | 6, 7 => 3
  | 7, 0 => 2 | 7, 1 => 2 | 7, 2 => 1 | 7, 3 => 2 | 7, 4 => 1 | 7, 5 => 2 | 7, 6 => 3 | 7, 7 => 0
  | _, _ => 0

private lemma dist_eq_of_cert {G : SimpleGraph (Fin 8)} {d : Fin 8 → Fin 8 → ℕ}
    (hdiag : ∀ x : Fin 8, d x x = 0)
    (hlip : ∀ x u v : Fin 8, G.Adj u v → d u x ≤ d v x + 1)
    (h0 : ∀ x y : Fin 8, d x y = 0 → x = y)
    (h1 : ∀ x y : Fin 8, d x y = 1 → G.Adj x y)
    (h2 : ∀ x y : Fin 8, d x y = 2 → ∃ z : Fin 8, G.Adj x z ∧ G.Adj z y)
    (h3 : ∀ x y : Fin 8, d x y = 3 → ∃ z w : Fin 8, G.Adj x z ∧ G.Adj z w ∧ G.Adj w y)
    (hle3 : ∀ x y : Fin 8, d x y ≤ 3) :
    G.Connected ∧ ∀ x y : Fin 8, G.dist x y = d x y := by
  have hex_walk : ∀ x y : Fin 8, ∃ p : G.Walk x y, p.length = d x y := by
    intro x y
    have hbound := hle3 x y
    rcases (show d x y = 0 ∨ d x y = 1 ∨ d x y = 2 ∨ d x y = 3 by omega) with hd | hd | hd | hd
    · obtain rfl := h0 x y hd
      exact ⟨SimpleGraph.Walk.nil, by rw [hd]; rfl⟩
    · exact ⟨SimpleGraph.Walk.cons (h1 x y hd) SimpleGraph.Walk.nil, by rw [hd]; rfl⟩
    · obtain ⟨z, hxz, hzy⟩ := h2 x y hd
      exact ⟨SimpleGraph.Walk.cons hxz (SimpleGraph.Walk.cons hzy SimpleGraph.Walk.nil), by rw [hd]; rfl⟩
    · obtain ⟨z, w, hxz, hzw, hwy⟩ := h3 x y hd
      exact ⟨SimpleGraph.Walk.cons hxz (SimpleGraph.Walk.cons hzw (SimpleGraph.Walk.cons hwy SimpleGraph.Walk.nil)),
        by rw [hd]; rfl⟩
  have hconn : G.Connected :=
    SimpleGraph.Connected.mk fun x y => by
      obtain ⟨p, _⟩ := hex_walk x y
      exact ⟨p⟩
  refine ⟨hconn, fun x y => le_antisymm ?_ ?_⟩
  · obtain ⟨p, hp⟩ := hex_walk x y
    rw [← hp]
    exact SimpleGraph.dist_le p
  · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
    rw [← hp]
    have hlb : ∀ {a b : Fin 8} (q : G.Walk a b), d a b ≤ q.length := by
      intro a b q
      induction q with
      | nil => rw [hdiag]; exact Nat.zero_le _
      | @cons u v w huv q ih =>
          have hstep := hlip w u v huv
          simp only [SimpleGraph.Walk.length_cons]
          omega
    exact hlb p

private lemma G1_cert : G1.Connected ∧ ∀ x y : Fin 8, G1.dist x y = d1 x y := by
  apply dist_eq_of_cert
  · decide
  · intro x u v huv; exact (by decide : ∀ x u v : Fin 8, adj1B u v = true → d1 u x ≤ d1 v x + 1) x u v huv
  · decide
  · intro x y h; exact (by decide : ∀ x y : Fin 8, d1 x y = 1 → adj1B x y = true) x y h
  · intro x y h; exact (by decide : ∀ x y : Fin 8, d1 x y = 2 → ∃ z : Fin 8, adj1B x z = true ∧ adj1B z y = true) x y h
  · intro x y h; exact (by decide : ∀ x y : Fin 8, d1 x y = 3 → ∃ z w : Fin 8, adj1B x z = true ∧ adj1B z w = true ∧ adj1B w y = true) x y h
  · decide

private lemma G2_cert : G2.Connected ∧ ∀ x y : Fin 8, G2.dist x y = d2 x y := by
  apply dist_eq_of_cert
  · decide
  · intro x u v huv; exact (by decide : ∀ x u v : Fin 8, adj2B u v = true → d2 u x ≤ d2 v x + 1) x u v huv
  · decide
  · intro x y h; exact (by decide : ∀ x y : Fin 8, d2 x y = 1 → adj2B x y = true) x y h
  · intro x y h; exact (by decide : ∀ x y : Fin 8, d2 x y = 2 → ∃ z : Fin 8, adj2B x z = true ∧ adj2B z y = true) x y h
  · intro x y h; exact (by decide : ∀ x y : Fin 8, d2 x y = 3 → ∃ z w : Fin 8, adj2B x z = true ∧ adj2B z w = true ∧ adj2B w y = true) x y h
  · decide

lemma G1_connected : G1.Connected := G1_cert.1
lemma G2_connected : G2.Connected := G2_cert.1

lemma boundary_eq : boundarySet G1 = boundarySet G2 := by
  ext v
  change IsBoundaryVertex G1 v ↔ IsBoundaryVertex G2 v
  simp only [IsBoundaryVertex, G1_cert.2, G2_cert.2]
  change (∃ u : Fin 8, u ≠ v ∧ ∀ w : Fin 8, adj1B v w = true → d1 u w ≤ d1 u v) ↔
         (∃ u : Fin 8, u ≠ v ∧ ∀ w : Fin 8, adj2B v w = true → d2 u w ≤ d2 u v)
  revert v
  decide

lemma boundary_dist_eq :
    ∀ x ∈ boundarySet G1, ∀ y ∈ boundarySet G1, G1.dist x y = G2.dist x y := by
  intro x hx y hy
  change IsBoundaryVertex G1 x at hx
  change IsBoundaryVertex G1 y at hy
  simp only [IsBoundaryVertex, G1_cert.2] at hx hy
  rw [G1_cert.2, G2_cert.2]
  have hdec : ∀ a b : Fin 8,
      (∃ u : Fin 8, u ≠ a ∧ ∀ w : Fin 8, adj1B a w = true → d1 u w ≤ d1 u a) →
      (∃ u : Fin 8, u ≠ b ∧ ∀ w : Fin 8, adj1B b w = true → d1 u w ≤ d1 u b) →
      d1 a b = d2 a b := by decide
  exact hdec x y hx hy

lemma G1_not_iso_G2 : ¬ Nonempty (G1 ≃g G2) := by
  rintro ⟨e⟩
  have hsum :
      (∑ u : Fin 8, (Finset.univ.filter (fun v : Fin 8 => adj1B u v = true)).card) =
      (∑ u : Fin 8, (Finset.univ.filter (fun v : Fin 8 => adj2B u v = true)).card) := by
    refine Fintype.sum_equiv e.toEquiv _ _ fun u => ?_
    refine Finset.card_bij (fun v _ => e v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact (e.map_rel_iff).mpr hv
    · intro v1 _ v2 _ h; exact e.injective h
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨e.symm w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply w⟩
      have : G2.Adj (e u) (e (e.symm w)) := by rw [e.apply_symm_apply]; exact hw
      exact (e.map_rel_iff).mp this
  have h1 : (∑ u : Fin 8, (Finset.univ.filter (fun v : Fin 8 => adj1B u v = true)).card) = 28 := by
    decide
  have h2 : (∑ u : Fin 8, (Finset.univ.filter (fun v : Fin 8 => adj2B u v = true)).card) = 26 := by
    decide
  omega

end OMA.P_arxiv_2404_04039

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2404_04039.main) := by
  intro h
  have hiso := h 8 (by norm_num) OMA.P_arxiv_2404_04039.G1 OMA.P_arxiv_2404_04039.G2
    OMA.P_arxiv_2404_04039.G1_connected OMA.P_arxiv_2404_04039.G2_connected
    OMA.P_arxiv_2404_04039.boundary_eq OMA.P_arxiv_2404_04039.boundary_dist_eq
  exact OMA.P_arxiv_2404_04039.G1_not_iso_G2 hiso
