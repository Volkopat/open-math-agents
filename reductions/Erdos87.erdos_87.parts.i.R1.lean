import FormalConjectures.ErdosProblems.«87»
import Mathlib

-- Reduction Erdos87.erdos_87.parts.i.R1 of Erdős Problem 87 — i
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Ramsey numbers of graphs of chromatic number `k`: the graphs that contain `K_k`

The target asks, for `0 < ε < 1` and `k` large, for `R(G) > (1 - ε) ^ k R(k)` for every finite
graph `G` with `χ(G) = k`, where `R(G) = R(G, G)` and `R(k) = R(K_k)`.

This file proves, with no hypothesis:

* Ramsey's theorem in the Erdős–Szekeres form: a graph on `C(s + t, s)` vertices has an `s`-clique
  or an independent set of size `t` (split the other vertices into neighbours and non-neighbours of
  one vertex). Hence `R(G)` is a genuine minimum for every finite graph `G`, and not the junk
  value of an empty infimum;
* the monotonicity `R(H) ≤ R(G)` whenever `H` is contained in `G`, and `R(G) ≥ |V(G)|`; in
  particular `R(k) ≥ k ≥ 1`;
* the target for every `G` that contains `K_k` (then `R(G) ≥ R(k) > (1 - ε) ^ k R(k)`) and for
  every `G` with more than `(1 - ε) ^ k R(k)` vertices.

What is left are the `K_k`-free graphs with `χ(G) = k` and at most `(1 - ε) ^ k R(k)` vertices,
split by clique number: exactly `k - 1` (H1) or at most `k - 2` (H2). Both hypotheses are special
cases of the target.
-/

namespace OMA.R_Erdos87_erdos_87_parts_i_R1

open SimpleGraph Filter Finset

/-- Clique number `k - 1`: for `0 < ε < 1` and `k` large, every graph `G` with `χ(G) = k` that
contains `K_(k - 1)` but not `K_k`, and has at most `(1 - ε) ^ k R(k)` vertices, satisfies
`R(G) > (1 - ε) ^ k R(k)`. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ε < 1 → ∀ᶠ k : ℕ in atTop,
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.chromaticNumber = (k : ℕ∞) →
      ¬ completeGraph (Fin k) ⊑ G → completeGraph (Fin (k - 1)) ⊑ G →
      (Fintype.card V : ℝ) ≤ (1 - ε) ^ k * (diagonalRamsey k : ℝ) →
      (diagonalGraphRamsey G : ℝ) > (1 - ε) ^ k * (diagonalRamsey k : ℝ)

/-- Clique number at most `k - 2`: for `0 < ε < 1` and `k` large, every `K_(k - 1)`-free graph `G`
with `χ(G) = k` and at most `(1 - ε) ^ k R(k)` vertices satisfies `R(G) > (1 - ε) ^ k R(k)`. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ε < 1 → ∀ᶠ k : ℕ in atTop,
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.chromaticNumber = (k : ℕ∞) →
      ¬ completeGraph (Fin (k - 1)) ⊑ G →
      (Fintype.card V : ℝ) ≤ (1 - ε) ^ k * (diagonalRamsey k : ℝ) →
      (diagonalGraphRamsey G : ℝ) > (1 - ε) ^ k * (diagonalRamsey k : ℝ)

/-- Ramsey's theorem in the Erdős–Szekeres form, for a set `S` of vertices: if
`C(s + t, s) ≤ |S|`, then `S` contains an `s`-clique of `C` or a `t`-clique of `Cᶜ`. -/
lemma ramsey_finset {V : Type*} [DecidableEq V] (C : SimpleGraph V) [DecidableRel C.Adj] :
    ∀ s t : ℕ, ∀ S : Finset V, (s + t).choose s ≤ S.card →
      (∃ K ⊆ S, C.IsNClique s K) ∨ (∃ K ⊆ S, Cᶜ.IsNClique t K) := by
  intro s
  induction s with
  | zero =>
    intro t S _
    exact Or.inl ⟨∅, empty_subset _, by simp⟩
  | succ s ihs =>
    intro t
    induction t with
    | zero =>
      intro S _
      exact Or.inr ⟨∅, empty_subset _, by simp⟩
    | succ t iht =>
      intro S hS
      have hpos : 0 < S.card := by
        have : 0 < (s + 1 + (t + 1)).choose (s + 1) := Nat.choose_pos (by omega)
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      set N := (S.erase v).filter (fun w => C.Adj v w) with hN
      set M := (S.erase v).filter (fun w => ¬ C.Adj v w) with hM
      have hNM : N.card + M.card = S.card - 1 := by
        rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
      have hpascal : (s + 1 + (t + 1)).choose (s + 1)
          = (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show s + 1 + (t + 1) = (s + (t + 1)) + 1 by omega, Nat.choose_succ_succ,
          show s + (t + 1) = s + 1 + t by omega]
      have hNsub : N ⊆ S := fun w hw => Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
      have hMsub : M ⊆ S := fun w hw => Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
      by_cases hNbig : (s + (t + 1)).choose s ≤ N.card
      · rcases ihs (t + 1) N hNbig with ⟨K, hKN, hK⟩ | ⟨K, hKN, hK⟩
        · left
          refine ⟨insert v K, ?_, ?_⟩
          · intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hv
            · exact hNsub (hKN hw)
          · exact hK.insert (fun b hb => (Finset.mem_filter.mp (hKN hb)).2)
        · exact Or.inr ⟨K, hKN.trans hNsub, hK⟩
      · have hMbig : (s + 1 + t).choose (s + 1) ≤ M.card := by omega
        rcases iht M hMbig with ⟨K, hKM, hK⟩ | ⟨K, hKM, hK⟩
        · exact Or.inl ⟨K, hKM.trans hMsub, hK⟩
        · right
          refine ⟨insert v K, ?_, ?_⟩
          · intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hv
            · exact hMsub (hKM hw)
          · refine hK.insert (fun b hb => ?_)
            have hbM := Finset.mem_filter.mp (hKM hb)
            rw [SimpleGraph.compl_adj]
            exact ⟨fun h => (Finset.mem_erase.mp hbM.1).1 h.symm, hbM.2⟩

/-- Every graph on `m` vertices is contained in `K_m`. -/
lemma isContained_completeGraph {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G ⊑ completeGraph (Fin (Fintype.card V)) :=
  ⟨⟨⟨Fintype.equivFin V, fun {_ _} h => by
      simpa [completeGraph] using (Fintype.equivFin V).injective.ne (G.ne_of_adj h)⟩,
    (Fintype.equivFin V).injective⟩⟩

/-- Ramsey's theorem for a finite graph `G`: some `n` forces `G` in `C` or in `Cᶜ` for every graph
`C` on `n` vertices, so `R(G)` is a genuine minimum. -/
lemma ramsey_nonempty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    {n : ℕ | ∀ C : SimpleGraph (Fin n), G ⊑ C ∨ G ⊑ Cᶜ}.Nonempty := by
  classical
  refine ⟨(Fintype.card V + Fintype.card V).choose (Fintype.card V), fun C => ?_⟩
  have hK := isContained_completeGraph G
  rcases ramsey_finset C (Fintype.card V) (Fintype.card V) Finset.univ (by simp) with
    ⟨K, -, hKc⟩ | ⟨K, -, hKc⟩
  · left
    exact hK.trans ((not_cliqueFree_iff_top_isContained _).mp (fun h => h K hKc))
  · right
    exact hK.trans ((not_cliqueFree_iff_top_isContained _).mp (fun h => h K hKc))

/-- Monotonicity: `R(H) ≤ R(G)` when `H` is contained in `G`. -/
lemma graphRamsey_mono {W V : Type*} [Fintype W] [Fintype V] {H : SimpleGraph W}
    {G : SimpleGraph V} (hHG : H ⊑ G) : graphRamsey H H ≤ graphRamsey G G := by
  unfold graphRamsey
  apply Nat.sInf_le
  intro C
  rcases Nat.sInf_mem (ramsey_nonempty G) C with h | h
  · exact Or.inl (hHG.trans h)
  · exact Or.inr (hHG.trans h)

/-- `R(G) ≥ |V(G)|`: a copy of `G` needs `|V(G)|` vertices. -/
lemma card_le_graphRamsey {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card V ≤ graphRamsey G G := by
  unfold graphRamsey
  refine le_csInf (ramsey_nonempty G) (fun n hn => ?_)
  rcases hn ⊥ with h | h
  · obtain ⟨f⟩ := h
    simpa using Fintype.card_le_of_injective _ f.injective
  · obtain ⟨f⟩ := h
    simpa using Fintype.card_le_of_injective _ f.injective

theorem main : H1 → H2 → type_of% @Erdos87.erdos_87.parts.i := by
  intro h1 h2 ε hε hε1
  filter_upwards [h1 ε hε hε1, h2 ε hε hε1, eventually_ge_atTop 1] with k hk1 hk2 hk V _ G hχ
  have hRk : (k : ℝ) ≤ (diagonalRamsey k : ℝ) := by
    have := card_le_graphRamsey (completeGraph (Fin k))
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hRpos : (0 : ℝ) < (diagonalRamsey k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpow : (1 - ε) ^ k < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hlt : (1 - ε) ^ k * (diagonalRamsey k : ℝ) < (diagonalRamsey k : ℝ) := by
    nlinarith
  by_cases hK : completeGraph (Fin k) ⊑ G
  · have hmono : (diagonalRamsey k : ℝ) ≤ (diagonalGraphRamsey G : ℝ) := by
      exact_mod_cast graphRamsey_mono hK
    show (1 - ε) ^ k * (diagonalRamsey k : ℝ) < (diagonalGraphRamsey G : ℝ)
    linarith
  by_cases hV : (1 - ε) ^ k * (diagonalRamsey k : ℝ) < (Fintype.card V : ℝ)
  · have hcard : (Fintype.card V : ℝ) ≤ (diagonalGraphRamsey G : ℝ) := by
      exact_mod_cast card_le_graphRamsey G
    show (1 - ε) ^ k * (diagonalRamsey k : ℝ) < (diagonalGraphRamsey G : ℝ)
    linarith
  push Not at hV
  by_cases hK1 : completeGraph (Fin (k - 1)) ⊑ G
  · exact hk1 V G hχ hK hK1 hV
  · exact hk2 V G hχ hK1 hV

end OMA.R_Erdos87_erdos_87_parts_i_R1
