import OMAStatements.S_wp_bipartite_graph
import Mathlib

/-!
# Word representation of bipartite graphs and crown extremality

The upper bounds for orders up to six, order eight, and larger even orders are
separate. On the lower-bound side, a crown on at least two vertices contains a
nonedge and therefore cannot have a uniform representant of multiplicity one.
The remaining crown lower bounds start at order eight.

The bounds used here are from Colbrook and Drysdale, *Crown graphs maximise the
representation number of bipartite graphs*, arXiv:2609.35842, Corollary 1.2 and
Appendix A. Their Apache-2.0 Lean development is at
https://github.com/miinadietrich/crown_graphs_maximise.
-/

namespace OMA.R_wp_bipartite_graph_R1

open OMA.S_wp_bipartite_graph

/-- Bipartite graphs with at most six vertices have a two-uniform representant. -/
def H1 : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  Fintype.card V ≤ 6 → G.Colorable 2 → ∃ w, IsRepresentedBy G 2 w

/-- Bipartite graphs with eight vertices have a three-uniform representant. -/
def H2 : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  Fintype.card V = 8 → G.Colorable 2 → ∃ w, IsRepresentedBy G 3 w

/-- The general upper bound, restricted to the larger even orders. -/
def H3 : Prop := ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  5 ≤ n → Fintype.card V = 2 * n → G.Colorable 2 →
    ∃ k : ℕ, 0 < k ∧ k ≤ (n + 1) / 2 ∧ ∃ w, IsRepresentedBy G k w

/-- The crown lower bounds beyond the elementary nonedge bound. -/
def H4 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ k : ℕ, 0 < k →
  ∀ w, IsRepresentedBy (crownGraph n) k w → (if n = 4 then 3 else (n + 1) / 2) ≤ k

theorem upper {V : Type} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    (hk : 0 < k) (hw : ∃ w, IsRepresentedBy G k w) : representationNumber G ≤ k :=
  sInf_le ⟨k, hk, rfl, hw⟩

private theorem empty_value {V : Type} [DecidableEq V] [IsEmpty V] (G : SimpleGraph V) :
    representationNumber G = 1 := by
  apply le_antisymm
  · exact upper (by decide : 0 < (1 : ℕ))
      ⟨[], fun v => isEmptyElim v, fun a => isEmptyElim a⟩
  · apply le_sInf
    rintro _ ⟨k, hk, rfl, _⟩
    exact_mod_cast hk

private theorem nodup_of_single {V : Type} [DecidableEq V] {w : List V}
    (h : ∀ v, w.count v = 1) : w.Nodup :=
  List.nodup_iff_count.mpr fun v => (h v).le

private theorem crown_two_le {n : ℕ} (hn : 0 < n) : 2 ≤ representationNumber (crownGraph n) := by
  let i : Fin n := ⟨0, hn⟩
  let a : Fin n ⊕ Fin n := .inl i
  let b : Fin n ⊕ Fin n := .inr i
  have hab : a ≠ b := by simp [a, b]
  have hnonedge : ¬ (crownGraph n).Adj a b := by simp [crownGraph, a, b]
  apply le_sInf
  rintro _ ⟨k, hk, rfl, w, hw⟩
  suffices 2 ≤ k by exact_mod_cast this
  by_contra! h
  have hk1 : k = 1 := by omega
  have hnw : w.Nodup := nodup_of_single (fun v => (hw.1 v).trans hk1)
  apply hnonedge ((hw.2 _ _ hab).mpr ?_)
  exact List.Pairwise.isChain (hnw.filter _)

private theorem crown_lower (hl : H4) {n : ℕ} (hn : 4 ≤ n) :
    ((if n = 4 then 3 else (n + 1) / 2 : ℕ) : ℕ∞) ≤ representationNumber (crownGraph n) := by
  apply le_sInf
  rintro _ ⟨k, hk, rfl, w, hw⟩
  exact_mod_cast hl n hn k hk w hw

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_wp_bipartite_graph.main := by
  intro hsmall height hlarge hl n V _ _ hcard G hb
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (by simpa using hcard)
    rw [empty_value G, empty_value (crownGraph 0)]
  by_cases hlow : n ≤ 3
  · exact (upper (by decide : 0 < (2 : ℕ)) (hsmall V G (by omega) hb)).trans (crown_two_le hn)
  by_cases hfour : n = 4
  · subst n
    exact (upper (by decide : 0 < (3 : ℕ)) (height V G (by omega) hb)).trans
      (by simpa using crown_lower hl (n := 4) (by decide))
  obtain ⟨k, hk, hceil, hw⟩ := hlarge n V G (by omega) hcard hb
  have hNat : (k : ℕ∞) ≤ ((n + 1) / 2 : ℕ) := by exact_mod_cast hceil
  exact (upper hk hw).trans (hNat.trans (by simpa [hfour] using crown_lower hl (by omega : 4 ≤ n)))

end OMA.R_wp_bipartite_graph_R1
