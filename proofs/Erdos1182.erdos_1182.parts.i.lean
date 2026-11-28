import FormalConjectures.ErdosProblems.«1182»
-- Port of Liesegang/formal-conjectures@540887d930a6aa7f8ecc111839955ba18de6327a, Attempts/Erdos1182/Main.lean
-- (Apache-2.0; same proof as Liesegang/erdos-1182-lean@92fa79dc, Palomar PALOMAR-2026-11-28-000021).
-- Changes: dropped the parts (ii)/(iii) sections, the statement-check elaborators/examples and #print lines;
-- appended the OMA answer and solution.

/-!
# Erdős Problem 1182: the orders of magnitude of `f(n)` and `F(n)`

Part (i) asks for the order of magnitude of `f(n)`, the largest number of edges of a connected
graph `G` on `n` vertices with `R(K_3, G) = 2n - 1`. With the definitions of
`FormalConjectures/ErdosProblems/1182.lean` (`Erdos1182.f`, `Erdos1182.IsTriangleGood`,
`SimpleGraph.graphRamsey`) this file proves

* `E1182.erdos_1182_i`:
  `(fun n ↦ (f n : ℝ)) =Θ[atTop] (fun n ↦ (n : ℝ) ^ (3 / 2 : ℝ) * √(log n))`.

The lower bound is the one of [BEFRS80, Theorem 2]. The upper bound
`f(n) = O(n^{3/2} √(log n))` (`E1182.f_isBigO_upper`) is the case of Sudakov's conjecture
`R(K_3, G) ≥ c m^{2/3} / (log m)^{1/3}` that is needed for `f`. We know of no refereed proof of it;
an unrefereed preprint of 2026 (Zenodo, DOI 10.5281/zenodo.22697303) claims it, and its Lean archive
assumes the concentration estimates for the triangle-free process as a hypothesis. Here the upper
bound is proved from scratch, by following the first `≈ N^{3/2} √(log N)` steps of the
triangle-free process on `K_N`; all concentration estimates are proved in this file.

Parts (ii) and (iii) of the problem are about `F(n)`, the largest `q` such that every connected
graph on `n` vertices with at most `q` edges has `R(K_3, G) = 2n - 1`. They are known results.
The last parts of the file prove them exactly as they are stated in Formal Conjectures:

* `E1182.erdos_1182_ii`: `(fun n ↦ (F n : ℝ)) =Θ[atTop] erdos_1182.parts.ii.answer`, that is
  `F(n) = Θ(n)`. The lower bound `n - 1 ≤ F n` is Chvátal's theorem for `K_3`. The upper bound
  `F n ≤ 513 n` for `n ≥ 82` uses a sparse graph in which any two disjoint sets of `n / 16`
  vertices are joined; the blow-up of the 5-cycle blocks it. This is the idea of Brandt's bound
  `F(n) ≤ 84 n`, with a weaker constant;
* `E1182.erdos_1182_iii`: `¬ Tendsto (fun n ↦ (F n : ℝ) / n) atTop atTop`.

Other results of the file, with the same definitions:

* `E1182.f_lower`: `∃ A > 0, ∀ᶠ n, A * n^(3/2) * √(log n) < f n`
  (identical to the statement `erdos_1182.variants.f_lower` of Formal Conjectures);
* `E1182.f_upper_sudakov`: `∃ B > 0, ∀ᶠ n, f n < B * n^(3/2) * log n`
  (the `s = 3` case of Sudakov 2007, Theorem 1.1, in the form needed for `f`);
* `E1182.f_upper_befrs`: `∃ B > 0, ∀ᶠ n, f n < B * n^(5/3) * (log n)^(2/3)`
  (identical to `erdos_1182.variants.f_upper`);
* `E1182.tendsto_log_f_div_log`: `log (f n) / log n → 3/2`;
* `E1182.ramsey_ge`: `2n - 1 ≤ R(K_3, G)` for connected `G`
  (identical to `erdos_1182.variants.ramsey_ge`);
* `E1182.f_isTheta_of_sudakovConjecture`: Sudakov's conjecture implies the order of magnitude;
* `E1182.kim_of_f_upper`: an upper bound `f(n) ≤ B n^{3/2} √(log n)` implies Kim's theorem
  `R(3,k) > c k² / log k` (so this file contains a proof of Kim's lower bound);
* `E1182.TFP.blockerAt_of_num`, `E1182.blockerStatement`: for all large `N`, every graph `H`
  with `k ≤ N` vertices, maximum degree at most `N^{9/10}` and at least `A k √(N log N)` edges
  meets, in each of its copies in `K_N`, some triangle-free graph on `N` vertices.

Mechanical checks: in `SummaryPart`, three `example`s check that `ramsey_ge`, `f_lower` and
`f_upper_befrs` have exactly the types of the Formal Conjectures statements; after `FinalPart`, an
`example` checks that `erdos_1182_i` is exactly the statement `erdos_1182.parts.i` of Formal
Conjectures with its placeholder answer replaced by `fun n ↦ (n : ℝ) ^ (3 / 2 : ℝ) * √(log n)`;
in `PartIIPart`, four `example`s check that `erdos_1182_ii`, `erdos_1182_iii`, `F_ge_pred` and
`chvatal` have exactly the types of the Formal Conjectures statements; at the end, `#print axioms`
lists the axioms of the main theorems (`propext`, `Classical.choice`, `Quot.sound` only).
See `NOTES.md` in this folder for sources and an outline of the proof.

The file is self-contained: it imports only the Formal Conjectures module (and through it Mathlib).
The parts (sections) are:

1. `BasicPart`: API for `R(K_3, G)` and `f`;
2. `ShearerPart`: independent sets in triangle-free graphs (Shearer-type bound, by counting);
3. `LowerPart`: the lower bound for `f`;
4. `UpperPart`: the upper bound `f(n) ≪ n^{3/2} log n` (Sudakov's argument, by counting);
5. `SummaryPart`: summary, conditional statement and the link with `R(3,k)`;
6. `ProcPart`: the triangle-free process as a recursion over histories; the master lemma
   (first-failure union bound with supermartingale potentials);
7. `StepPart`: exact one-step counting identities of the process;
8. `MartRealPart`, `MartPart`: one-step supermartingale inequalities;
9. `TrajPart`: the deterministic trajectory and the error sequences;
10. `WCountPart`: second moment of the loss of open pairs of a fixed edge set;
11. `GlobalPart`: good histories; the number of open pairs follows the trajectory;
12. `CausesPart`, `Causes2Part`, `CausesWPart`: the potentials for the pair counts, the degrees,
    the codegrees and the edge sets;
13. `NumDefsPart`, `NumGlobalProofPart`, `NumEdgeProofPart`: parameters and all numerical facts;
14. `ReductionPart`: reduction of the upper bound for `f` to the blocker statement (degree
    splitting);
15. `AssemblePart`, `BlockerPart`, `FinalPart`: the union bound and the final theorem;
16. `TreeEmbedPart`, `ExpanderPart`, `C5Part`, `PartIIPart`: parts (ii) and (iii): greedy
    embedding of trees, sparse expanding graphs by counting, the blow-up of the 5-cycle, and the
    bounds for `F`.
-/

section BasicPart

/-
# Erdős Problem 1182 — basic API

Elementary facts about the Ramsey number `R(K_3, G)` as it is defined in Formal Conjectures
(`SimpleGraph.graphRamsey`), and about the extremal function `Erdos1182.f`.

* `RamseySet G` is the set whose infimum is `R(K_3, G)`; it is upward closed.
* `two_mul_sub_two_notMem`: the Chvátal–Harary lower bound, `2n - 2 ∉ RamseySet G` for a connected
  graph `G` on `n` vertices.
* `le_f_of_embeds`: a connected graph on `n` vertices that embeds in the complement of every
  triangle-free graph on `2n - 1` vertices has at most `f n` edges.
* `f_le_of_forall_exists`: if every connected graph on `n` vertices with more than `B` edges
  is avoided by the complement of some triangle-free graph on `2n - 1` vertices, then `f n ≤ B`.
-/

open SimpleGraph

namespace E1182

export Erdos1182 (IsTriangleGood f F le_F)

/-- The set of `N` such that every graph on `N` vertices contains a triangle or its complement
contains `G`. By definition `R(K_3, G) = sInf (RamseySet G)`. -/
def RamseySet {β : Type*} (G : SimpleGraph β) : Set ℕ :=
  {N | ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ}

theorem graphRamsey_eq_sInf {β : Type*} [Fintype β] (G : SimpleGraph β) :
    graphRamsey (⊤ : SimpleGraph (Fin 3)) G = sInf (RamseySet G) := rfl

/-- A graph contains no copy of `K_3` iff it is `CliqueFree 3`. -/
theorem not_top_isContained_iff {α : Type*} (C : SimpleGraph α) :
    ¬ (⊤ : SimpleGraph (Fin 3)).IsContained C ↔ C.CliqueFree 3 := by
  rw [cliqueFree_iff, IsContained, not_nonempty_iff]

/-- Three pairwise adjacent vertices contradict `CliqueFree 3`. -/
theorem CliqueFree3.false {α : Type*} {C : SimpleGraph α} (h : C.CliqueFree 3) {a b c : α}
    (hab : C.Adj a b) (hac : C.Adj a c) (hbc : C.Adj b c) : False := by
  classical
  exact h {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

/-- A graph in which no three vertices are pairwise adjacent is `CliqueFree 3`. -/
theorem cliqueFree3_of_forall {α : Type*} {C : SimpleGraph α}
    (h : ∀ a b c, C.Adj a b → C.Adj a c → C.Adj b c → False) : C.CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  exact h a b c hab hac hbc

/-- `G` is contained in the complement of `C` iff there is an injective map of the vertices
sending edges of `G` to non-edges of `C`. -/
theorem isContained_compl_iff {α β : Type*} (G : SimpleGraph β) (C : SimpleGraph α) :
    G.IsContained Cᶜ ↔
      ∃ φ : β → α, Function.Injective φ ∧ ∀ a b, G.Adj a b → ¬ C.Adj (φ a) (φ b) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c, c.injective, fun a b hab => ((compl_adj _ _ _).mp (c.toHom.map_adj hab)).2⟩
  · rintro ⟨φ, hφ, h⟩
    exact ⟨⟨⟨φ, fun {a b} hab => (compl_adj _ _ _).mpr ⟨fun e => hab.ne (hφ e), h a b hab⟩⟩, hφ⟩⟩

theorem mem_ramseySet_iff {β : Type*} (G : SimpleGraph β) (N : ℕ) :
    N ∈ RamseySet G ↔ ∀ C : SimpleGraph (Fin N), C.CliqueFree 3 →
      ∃ φ : β → Fin N, Function.Injective φ ∧ ∀ a b, G.Adj a b → ¬ C.Adj (φ a) (φ b) := by
  change (∀ C : SimpleGraph (Fin N), _ ∨ _) ↔ _
  refine forall_congr' fun C => ?_
  rw [← isContained_compl_iff, ← not_top_isContained_iff]
  tauto

/-- `RamseySet G` is upward closed. -/
theorem ramseySet_mono {β : Type*} (G : SimpleGraph β) {N N' : ℕ} (h : N ≤ N')
    (hN : N ∈ RamseySet G) : N' ∈ RamseySet G := by
  rw [mem_ramseySet_iff] at hN ⊢
  intro C' hC'
  let e : Fin N → Fin N' := Fin.castLE h
  have he : Function.Injective e := Fin.castLE_injective h
  obtain ⟨φ, hφ, hφ'⟩ := hN (C'.comap e) (hC'.comap ⟨(Embedding.comap ⟨e, he⟩ C').toCopy⟩)
  exact ⟨e ∘ φ, he.comp hφ, fun a b hab => hφ' a b hab⟩

/-- If `2n - 1 ∈ RamseySet G` and `2n - 2 ∉ RamseySet G`, then `R(K_3, G) = 2n - 1`. -/
theorem isTriangleGood_of {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (h1 : 2 * n - 1 ∈ RamseySet G) (h2 : 2 * n - 2 ∉ RamseySet G) : IsTriangleGood G := by
  unfold IsTriangleGood
  rw [graphRamsey_eq_sInf]
  refine le_antisymm (Nat.sInf_le h1) ?_
  by_contra hlt
  push Not at hlt
  have hmem : sInf (RamseySet G) ∈ RamseySet G := Nat.sInf_mem ⟨_, h1⟩
  exact h2 (ramseySet_mono G (by omega) hmem)

/-- If `2n - 1 ∉ RamseySet G` then `G` is not `K_3`-good. -/
theorem not_isTriangleGood_of {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (h1 : 2 * n - 1 ∉ RamseySet G) : ¬ IsTriangleGood G := by
  intro hgood
  unfold IsTriangleGood at hgood
  rw [graphRamsey_eq_sInf] at hgood
  by_cases hne : (RamseySet G).Nonempty
  · exact h1 (hgood ▸ Nat.sInf_mem hne)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Nat.sInf_empty] at hgood
    omega

/-- **Chvátal–Harary lower bound.** If `G` is a connected graph on `n` vertices, then the complete
bipartite graph `K_{n-1,n-1}` shows `2n - 2 ∉ RamseySet G`, i.e. `R(K_3, G) > 2n - 2`. -/
theorem two_mul_sub_two_notMem {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    2 * n - 2 ∉ RamseySet G := by
  have hn : 1 ≤ n := by
    obtain ⟨v⟩ := hG.nonempty
    exact Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ v).elim0)
  rw [mem_ramseySet_iff]
  push Not
  let e : Fin (2 * n - 2) ≃ Fin (n - 1) ⊕ Fin (n - 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let side : Fin (2 * n - 2) → Bool := fun i => (e i).isLeft
  let C : SimpleGraph (Fin (2 * n - 2)) :=
    { Adj := fun i j => side i ≠ side j
      symm := ⟨fun _ _ h => Ne.symm h⟩
      loopless := ⟨fun i h => h rfl⟩ }
  refine ⟨C, ?_, ?_⟩
  · refine cliqueFree3_of_forall fun a b c hab hac hbc => ?_
    change side a ≠ side b at hab
    change side a ≠ side c at hac
    change side b ≠ side c at hbc
    revert hab hac hbc
    cases side a <;> cases side b <;> cases side c <;> simp
  · intro φ hφ
    by_contra hcon
    push Not at hcon
    have hadj : ∀ a b, G.Adj a b → side (φ a) = side (φ b) := by
      intro a b hab
      have := hcon a b hab
      change ¬ (side (φ a) ≠ side (φ b)) at this
      exact not_not.mp this
    have hreach : ∀ a b, G.Reachable a b → side (φ a) = side (φ b) := by
      rintro a b ⟨w⟩
      induction w with
      | nil => rfl
      | cons h _ ih => exact (hadj _ _ h).trans ih
    have hconst : ∀ a b, side (φ a) = side (φ b) := fun a b => hreach a b (hG.preconnected a b)
    -- collapse the two sides onto `Fin (n - 1)`
    let ψ : Fin n → Fin (n - 1) := fun a => Sum.elim id id (e (φ a))
    have hψ : Function.Injective ψ := by
      intro a b hab
      have hs := hconst a b
      apply hφ
      apply e.injective
      simp only [ψ] at hab
      simp only [side] at hs
      revert hab hs
      cases e (φ a) <;> cases e (φ b) <;> simp
    have := Fintype.card_le_of_injective ψ hψ
    simp only [Fintype.card_fin] at this
    omega

/-- For connected `G`, being `K_3`-good is equivalent to `2n - 1 ∈ RamseySet G`. -/
theorem isTriangleGood_iff {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    IsTriangleGood G ↔ 2 * n - 1 ∈ RamseySet G := by
  have hn : 1 ≤ n := by
    obtain ⟨v⟩ := hG.nonempty
    exact Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ v).elim0)
  constructor
  · intro h
    by_contra hcon
    exact not_isTriangleGood_of hn G hcon h
  · intro h
    exact isTriangleGood_of hn G h (two_mul_sub_two_notMem G hG)

/-- The number of edges of a graph on `n` vertices is at most `n.choose 2`. -/
theorem ncard_edgeSet_le {n : ℕ} (G : SimpleGraph (Fin n)) : G.edgeSet.ncard ≤ n.choose 2 := by
  classical
  have h := G.card_edgeFinset_le_card_choose_two
  rw [Fintype.card_fin] at h
  rwa [← Set.ncard_coe_finset, coe_edgeFinset] at h

/-- The set in the definition of `f n` is bounded above. -/
theorem bddAbove_f_set (n : ℕ) :
    BddAbove {q : ℕ | ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ G.edgeSet.ncard = q ∧ IsTriangleGood G} :=
  ⟨n.choose 2, by rintro q ⟨G, -, rfl, -⟩; exact ncard_edgeSet_le G⟩

/-- A connected `K_3`-good graph on `n` vertices has at most `f n` edges. -/
theorem ncard_edgeSet_le_f {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hgood : IsTriangleGood G) : G.edgeSet.ncard ≤ f n :=
  le_csSup (bddAbove_f_set n) ⟨G, hG, rfl, hgood⟩

/-- `f n ≤ n.choose 2`. -/
theorem f_le_choose (n : ℕ) : f n ≤ n.choose 2 :=
  csSup_le' (by rintro q ⟨G, -, rfl, -⟩; exact ncard_edgeSet_le G)

/-- To bound `f n` from above it suffices to bound the number of edges of every connected
`K_3`-good graph. -/
theorem f_le_of_forall {n B : ℕ}
    (h : ∀ G : SimpleGraph (Fin n), G.Connected → IsTriangleGood G → G.edgeSet.ncard ≤ B) :
    f n ≤ B :=
  csSup_le' (by rintro q ⟨G, hG, rfl, hgood⟩; exact h G hG hgood)

/-- **Upper bounds for `f`.** If for every connected graph `G` on `n` vertices with more than `B`
edges there is a triangle-free graph `C` on `2n - 1` vertices such that every injection of the
vertices of `G` sends some edge of `G` to an edge of `C`, then `f n ≤ B`. -/
theorem f_le_of_forall_exists {n B : ℕ} (hn : 1 ≤ n)
    (h : ∀ G : SimpleGraph (Fin n), G.Connected → B < G.edgeSet.ncard →
      ∃ C : SimpleGraph (Fin (2 * n - 1)), C.CliqueFree 3 ∧
        ∀ φ : Fin n → Fin (2 * n - 1), Function.Injective φ →
          ∃ a b, G.Adj a b ∧ C.Adj (φ a) (φ b)) :
    f n ≤ B := by
  refine f_le_of_forall fun G hG hgood => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC, hCφ⟩ := h G hG hlt
  refine not_isTriangleGood_of hn G ?_ hgood
  rw [mem_ramseySet_iff]
  push Not
  exact ⟨C, hC, fun φ hφ => hCφ φ hφ⟩

/-- **Lower bounds for `f`.** Let `G` be a connected graph on a vertex type with `n` elements.
If for every triangle-free graph `C` on `2n - 1` vertices there is an injection of the vertices of
`G` sending edges of `G` to non-edges of `C`, then `G` has at most `f n` edges. -/
theorem le_f_of_embeds {V : Type*} [Fintype V] {n : ℕ} (hcard : Fintype.card V = n)
    (G : SimpleGraph V) (hG : G.Connected)
    (h : ∀ C : SimpleGraph (Fin (2 * n - 1)), C.CliqueFree 3 →
      ∃ φ : V → Fin (2 * n - 1), Function.Injective φ ∧ ∀ a b, G.Adj a b → ¬ C.Adj (φ a) (φ b)) :
    G.edgeSet.ncard ≤ f n := by
  classical
  let e : V ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let G' : SimpleGraph (Fin n) := G.map e.toEmbedding
  let iso : G ≃g G' := Iso.map e G
  have hG' : G'.Connected := iso.connected_iff.mp hG
  have hgood : IsTriangleGood G' := by
    rw [isTriangleGood_iff G' hG', mem_ramseySet_iff]
    intro C hC
    obtain ⟨φ, hφ, hφ'⟩ := h C hC
    refine ⟨φ ∘ e.symm, hφ.comp e.symm.injective, fun a b hab => hφ' _ _ ?_⟩
    exact iso.symm.map_rel_iff.mpr hab
  have hcardE : G.edgeSet.ncard = G'.edgeSet.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr iso.mapEdgeSet
  rw [hcardE]
  exact ncard_edgeSet_le_f G' hG' hgood

end E1182

end BasicPart

section ShearerPart

/-
# Independent sets in triangle-free graphs

A triangle-free graph on `N` vertices with maximum degree at most `d` has an independent set of
size at least `N * log₂ d / (4 d)`. This is the Ajtai–Komlós–Szemerédi / Shearer bound, in the
form proved by a counting argument over all independent sets (Shearer; see Alon–Spencer,
*The Probabilistic Method*, "Triangle-free graphs have large independence numbers").

The proof here is written as pure double counting, with no probability theory.

Main results:
* `exists_indepSet_of_cliqueFree`: the degree form.
* `exists_indep_subset`: the Ramsey form `R(3, k) ≤ 4k² / log₂ k + 1`, relative to a set `M` of
  vertices.
-/

open Finset

namespace E1182

/-- `log₂ d * (2^x + 1) ≤ 2d + x 2^x`: the numerical heart of the local estimate. -/
theorem log_mul_le (d x : ℕ) : Nat.log 2 d * (2 ^ x + 1) ≤ 2 * d + x * 2 ^ x := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h1 : 2 ^ Nat.log 2 d ≤ d := Nat.pow_log_le_self 2 hd.ne'
  have h2 : Nat.log 2 d ≤ d := (Nat.lt_two_pow_self).le.trans h1
  generalize Nat.log 2 d = l at h1 h2
  rcases le_or_gt l x with hx | hx
  · have h3 : l * 2 ^ x ≤ x * 2 ^ x := Nat.mul_le_mul_right _ hx
    have h4 : l * (2 ^ x + 1) = l * 2 ^ x + l := by ring
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, l = x + j := ⟨l - x, by omega⟩
    have h3 : j * 2 ^ x ≤ d := by
      have h5 : j ≤ 2 ^ j := (Nat.lt_two_pow_self).le
      calc j * 2 ^ x ≤ 2 ^ j * 2 ^ x := Nat.mul_le_mul_right _ h5
        _ = 2 ^ (x + j) := by rw [pow_add, mul_comm]
        _ ≤ d := h1
    have h4 : (x + j) * (2 ^ x + 1) = x * 2 ^ x + j * 2 ^ x + (x + j) := by ring
    omega

/-- `2 * ∑_{T ⊆ X} |T| = |X| * 2^|X|`. -/
theorem two_mul_sum_card_powerset {α : Type*} [DecidableEq α] (X : Finset α) :
    2 * ∑ T ∈ X.powerset, T.card = X.card * 2 ^ X.card := by
  have h : ∑ T ∈ X.powerset, T.card = ∑ T ∈ X.powerset, (X \ T).card := by
    refine Finset.sum_nbij' (fun T => X \ T) (fun T => X \ T) ?_ ?_ ?_ ?_ ?_
    · intro T _; exact mem_powerset.mpr sdiff_subset
    · intro T _; exact mem_powerset.mpr sdiff_subset
    · intro T hT; exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp hT)
    · intro T hT; exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp hT)
    · intro T hT; rw [Finset.sdiff_sdiff_eq_self (mem_powerset.mp hT)]
  calc 2 * ∑ T ∈ X.powerset, T.card
      = ∑ T ∈ X.powerset, T.card + ∑ T ∈ X.powerset, (X \ T).card := by rw [← h]; ring
    _ = ∑ T ∈ X.powerset, (T.card + (X \ T).card) := sum_add_distrib.symm
    _ = ∑ T ∈ X.powerset, X.card := by
        refine sum_congr rfl fun T hT => ?_
        rw [add_comm, card_sdiff_add_card_eq_card (mem_powerset.mp hT)]
    _ = X.card * 2 ^ X.card := by rw [sum_const, card_powerset, smul_eq_mul, mul_comm]

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The family of independent sets of `G`. -/
def indepSets : Finset (Finset V) :=
  univ.filter fun W => ∀ a ∈ W, ∀ b ∈ W, ¬ G.Adj a b

theorem mem_indepSets {W : Finset V} :
    W ∈ indepSets G ↔ ∀ a ∈ W, ∀ b ∈ W, ¬ G.Adj a b := by
  simp [indepSets]

/-- The weight `d * [v ∈ W] + |N(v) ∩ W|` of an independent set `W` at the vertex `v`. -/
def wt (d : ℕ) (v : V) (W : Finset V) : ℕ :=
  d * (if v ∈ W then 1 else 0) + (W.filter (G.Adj v)).card

/-- The part of `W` outside the closed neighbourhood of `v`. -/
def trace (v : V) (W : Finset V) : Finset V :=
  W.filter fun u => u ≠ v ∧ ¬ G.Adj v u

theorem trace_mem_indepSets (v : V) {W : Finset V} (hW : W ∈ indepSets G) :
    trace G v W ∈ indepSets G := by
  rw [mem_indepSets] at hW ⊢
  intro a ha b hb
  exact hW a (mem_filter.mp ha).1 b (mem_filter.mp hb).1

/-- The local estimate on one fibre of `trace`: on the set of independent sets with a prescribed
trace `S` outside `N[v]`, the average weight at `v` is at least `log₂ d / 2`. -/
theorem fiber_bound (hG : G.CliqueFree 3) (d : ℕ) (v : V) (S : Finset V)
    (hS : S ∈ indepSets G) :
    Nat.log 2 d * ((indepSets G).filter fun W => trace G v W = S).card
      ≤ 2 * ∑ W ∈ (indepSets G).filter (fun W => trace G v W = S), wt G d v W := by
  by_cases hS' : ∀ u ∈ S, u ≠ v ∧ ¬ G.Adj v u
  swap
  · have hempty : (indepSets G).filter (fun W => trace G v W = S) = ∅ := by
      refine filter_eq_empty_iff.mpr fun W _ hW => hS' fun u hu => ?_
      rw [← hW] at hu
      exact (mem_filter.mp hu).2
    simp [hempty]
  rw [mem_indepSets] at hS
  set X : Finset V := univ.filter fun u => G.Adj v u ∧ ∀ s ∈ S, ¬ G.Adj u s with hX
  have hXmem : ∀ u, u ∈ X ↔ G.Adj v u ∧ ∀ s ∈ S, ¬ G.Adj u s := by
    intro u; simp [hX]
  have hvS : v ∉ S := fun h => (hS' v h).1 rfl
  -- the neighbours of `v` inside `S ∪ T` are exactly `T`
  have hfilt : ∀ T ⊆ X, (S ∪ T).filter (G.Adj v) = T := by
    intro T hT
    ext u
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hu | hu, hadj⟩
      · exact absurd hadj (hS' u hu).2
      · exact hu
    · intro hu
      exact ⟨Or.inr hu, ((hXmem u).mp (hT hu)).1⟩
  have hfib : (indepSets G).filter (fun W => trace G v W = S)
      = insert (insert v S) (X.powerset.image fun T => S ∪ T) := by
    ext W
    simp only [mem_filter, mem_insert, mem_image, mem_powerset, mem_indepSets]
    constructor
    · rintro ⟨hW, hWS⟩
      have hSW : S ⊆ W := by
        intro u hu
        rw [← hWS] at hu
        exact (mem_filter.mp hu).1
      by_cases hv : v ∈ W
      · left
        ext u
        simp only [mem_insert]
        constructor
        · intro hu
          by_cases huv : u = v
          · exact Or.inl huv
          · right
            rw [← hWS]
            exact mem_filter.mpr ⟨hu, huv, hW v hv u hu⟩
        · rintro (rfl | hu)
          · exact hv
          · exact hSW hu
      · right
        refine ⟨W.filter (G.Adj v), ?_, ?_⟩
        · intro u hu
          rw [mem_filter] at hu
          exact (hXmem u).mpr ⟨hu.2, fun s hs => hW u hu.1 s (hSW hs)⟩
        · ext u
          simp only [mem_union, mem_filter]
          constructor
          · rintro (hu | hu)
            · exact hSW hu
            · exact hu.1
          · intro hu
            by_cases hadj : G.Adj v u
            · exact Or.inr ⟨hu, hadj⟩
            · left
              rw [← hWS]
              exact mem_filter.mpr ⟨hu, fun h => hv (h ▸ hu), hadj⟩
    · rintro (rfl | ⟨T, hT, rfl⟩)
      · refine ⟨?_, ?_⟩
        · intro a ha b hb
          rw [mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact G.irrefl
          · exact (hS' b hb).2
          · exact fun h => (hS' a ha).2 h.symm
          · exact hS a ha b hb
        · ext u
          simp only [trace, mem_filter, mem_insert]
          constructor
          · rintro ⟨rfl | hu, hne, -⟩
            · exact absurd rfl hne
            · exact hu
          · intro hu
            exact ⟨Or.inr hu, hS' u hu⟩
      · refine ⟨?_, ?_⟩
        · intro a ha b hb
          rw [mem_union] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact hS a ha b hb
          · exact fun h => ((hXmem b).mp (hT hb)).2 a ha h.symm
          · exact ((hXmem a).mp (hT ha)).2 b hb
          · exact fun h => CliqueFree3.false hG ((hXmem a).mp (hT ha)).1
              ((hXmem b).mp (hT hb)).1 h
        · ext u
          simp only [trace, mem_filter, mem_union]
          constructor
          · rintro ⟨hu | hu, -, hnadj⟩
            · exact hu
            · exact absurd ((hXmem u).mp (hT hu)).1 hnadj
          · intro hu
            exact ⟨Or.inl hu, hS' u hu⟩
  have hnotin : insert v S ∉ X.powerset.image fun T => S ∪ T := by
    intro h
    obtain ⟨T, hT, hTeq⟩ := mem_image.mp h
    rw [mem_powerset] at hT
    have hv : v ∈ S ∪ T := hTeq ▸ mem_insert_self v S
    rcases mem_union.mp hv with hv | hv
    · exact hvS hv
    · exact G.irrefl ((hXmem v).mp (hT hv)).1
  have hinj : Set.InjOn (fun T => S ∪ T) (X.powerset : Set (Finset V)) := by
    intro T hT T' hT' h
    rw [mem_coe, mem_powerset] at hT hT'
    have h' : (S ∪ T).filter (G.Adj v) = (S ∪ T').filter (G.Adj v) := by
      simpa using congrArg (fun W : Finset V => W.filter (G.Adj v)) h
    rwa [hfilt T hT, hfilt T' hT'] at h'
  have hwt1 : wt G d v (insert v S) = d := by
    have hempty : (insert v S).filter (G.Adj v) = ∅ := by
      refine filter_eq_empty_iff.mpr fun u hu => ?_
      rcases mem_insert.mp hu with rfl | hu
      · exact G.irrefl
      · exact (hS' u hu).2
    simp [wt, hempty]
  have hwt2 : ∀ T ∈ X.powerset, wt G d v (S ∪ T) = T.card := by
    intro T hT
    rw [mem_powerset] at hT
    have hv : v ∉ S ∪ T := by
      intro hv
      rcases mem_union.mp hv with hv | hv
      · exact hvS hv
      · exact G.irrefl ((hXmem v).mp (hT hv)).1
    simp [wt, hv, hfilt T hT]
  rw [hfib, card_insert_of_notMem hnotin, sum_insert hnotin, card_image_of_injOn hinj,
    sum_image hinj, card_powerset, hwt1, sum_congr rfl hwt2]
  have h1 := two_mul_sum_card_powerset X
  have h2 := log_mul_le d X.card
  have h3 : 2 * (d + ∑ T ∈ X.powerset, T.card) = 2 * d + X.card * 2 ^ X.card := by
    rw [mul_add, h1]
  exact h2.trans h3.symm.le

/-- The local estimate: the average weight at `v` over all independent sets is at least
`log₂ d / 2`. -/
theorem local_bound (hG : G.CliqueFree 3) (d : ℕ) (v : V) :
    Nat.log 2 d * (indepSets G).card ≤ 2 * ∑ W ∈ indepSets G, wt G d v W := by
  have hmaps : ∀ W ∈ indepSets G, trace G v W ∈ indepSets G :=
    fun W hW => trace_mem_indepSets G v hW
  calc Nat.log 2 d * (indepSets G).card
      = ∑ S ∈ indepSets G,
          Nat.log 2 d * ((indepSets G).filter fun W => trace G v W = S).card := by
        rw [card_eq_sum_card_fiberwise hmaps, mul_sum]
    _ ≤ ∑ S ∈ indepSets G,
          2 * ∑ W ∈ (indepSets G).filter (fun W => trace G v W = S), wt G d v W :=
        sum_le_sum fun S hS => fiber_bound G hG d v S hS
    _ = 2 * ∑ W ∈ indepSets G, wt G d v W := by
        rw [← mul_sum, sum_fiberwise_of_maps_to hmaps]

/-- The total weight of an independent set is at most `2 d |W|`. -/
theorem sum_wt_le (d : ℕ) (hd : ∀ v, G.degree v ≤ d) (W : Finset V) :
    ∑ v, wt G d v W ≤ 2 * d * W.card := by
  have h1 : ∑ v : V, d * (if v ∈ W then 1 else 0) = d * W.card := by
    rw [← mul_sum]; simp
  have h2 : ∑ v : V, (W.filter (G.Adj v)).card ≤ d * W.card := by
    calc ∑ v : V, (W.filter (G.Adj v)).card
        = ∑ v : V, ∑ w ∈ W, if G.Adj v w then 1 else 0 := by
          refine sum_congr rfl fun v _ => ?_
          rw [card_filter]
      _ = ∑ w ∈ W, ∑ v : V, if G.Adj v w then 1 else 0 := sum_comm
      _ = ∑ w ∈ W, G.degree w := by
          refine sum_congr rfl fun w _ => ?_
          rw [← card_filter, ← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1
          ext u
          simp [SimpleGraph.adj_comm]
      _ ≤ ∑ w ∈ W, d := sum_le_sum fun w _ => hd w
      _ = d * W.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have h3 : 2 * d * W.card = d * W.card + d * W.card := by ring
  unfold wt
  rw [sum_add_distrib, h1, h3]
  omega

/-- **Shearer-type bound.** A triangle-free graph with all degrees at most `d` has an independent
set `W` with `|V| * log₂ d ≤ 4 d |W|`. -/
theorem exists_indepSet_of_cliqueFree (hG : G.CliqueFree 3) (d : ℕ)
    (hd : ∀ v, G.degree v ≤ d) :
    ∃ W : Finset V, (∀ a ∈ W, ∀ b ∈ W, ¬ G.Adj a b) ∧
      Fintype.card V * Nat.log 2 d ≤ 4 * d * W.card := by
  have hne : (indepSets G).Nonempty := ⟨∅, by simp [indepSets]⟩
  obtain ⟨W₀, hW₀, hmax⟩ := exists_max_image (indepSets G) card hne
  refine ⟨W₀, (mem_indepSets G).mp hW₀, ?_⟩
  have h1 : Fintype.card V * (Nat.log 2 d * (indepSets G).card)
      ≤ 2 * ∑ v : V, ∑ W ∈ indepSets G, wt G d v W := by
    rw [mul_sum, ← card_univ, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun v _ => local_bound G hG d v
  have h2 : ∑ v : V, ∑ W ∈ indepSets G, wt G d v W
      ≤ (indepSets G).card * (2 * d * W₀.card) := by
    rw [sum_comm]
    calc ∑ W ∈ indepSets G, ∑ v : V, wt G d v W
        ≤ ∑ W ∈ indepSets G, 2 * d * W.card := sum_le_sum fun W _ => sum_wt_le G d hd W
      _ ≤ ∑ W ∈ indepSets G, 2 * d * W₀.card :=
          sum_le_sum fun W hW => Nat.mul_le_mul_left _ (hmax W hW)
      _ = (indepSets G).card * (2 * d * W₀.card) := by rw [sum_const, smul_eq_mul]
  have hpos : 0 < (indepSets G).card := card_pos.mpr hne
  have h3 : (Fintype.card V * Nat.log 2 d) * (indepSets G).card
      ≤ (4 * d * W₀.card) * (indepSets G).card := by
    calc (Fintype.card V * Nat.log 2 d) * (indepSets G).card
        = Fintype.card V * (Nat.log 2 d * (indepSets G).card) := by ring
      _ ≤ 2 * ∑ v : V, ∑ W ∈ indepSets G, wt G d v W := h1
      _ ≤ 2 * ((indepSets G).card * (2 * d * W₀.card)) := Nat.mul_le_mul_left _ h2
      _ = (4 * d * W₀.card) * (indepSets G).card := by ring
  exact Nat.le_of_mul_le_mul_right h3 hpos

end Counting

/-- **Ramsey form.** Let `C` be a triangle-free graph and `M` a set of vertices with
`4 k² ≤ |M| * log₂ k`. Then `M` contains an independent set of size exactly `k`.
In particular `R(3, k) ≤ ⌈4k² / log₂ k⌉`. -/
theorem exists_indep_subset {V : Type*} [Fintype V] (C : SimpleGraph V) (hC : C.CliqueFree 3)
    (k : ℕ) (hk : 1 ≤ k) (M : Finset V) (hM : 4 * k ^ 2 ≤ M.card * Nat.log 2 k) :
    ∃ I ⊆ M, I.card = k ∧ ∀ a ∈ I, ∀ b ∈ I, ¬ C.Adj a b := by
  classical
  let H : SimpleGraph M := C.comap Subtype.val
  have hH : H.CliqueFree 3 :=
    hC.comap ⟨(SimpleGraph.Embedding.comap (Function.Embedding.subtype _) C).toCopy⟩
  -- it suffices to find an independent set of size at least `k` in `H`
  suffices hsuff : ∃ W : Finset M, k ≤ W.card ∧ ∀ a ∈ W, ∀ b ∈ W, ¬ H.Adj a b by
    obtain ⟨W, hWk, hW⟩ := hsuff
    obtain ⟨T, hT, hTk⟩ := exists_subset_card_eq hWk
    refine ⟨T.map (Function.Embedding.subtype _), ?_, by simpa using hTk, ?_⟩
    · intro x hx
      obtain ⟨a, -, rfl⟩ := mem_map.mp hx
      exact a.2
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
      exact hW a (hT ha) b (hT hb)
  by_cases hdeg : ∃ v : M, k ≤ H.degree v
  · obtain ⟨v, hv⟩ := hdeg
    refine ⟨H.neighborFinset v, by simpa using hv, ?_⟩
    intro a ha b hb hab
    rw [SimpleGraph.mem_neighborFinset] at ha hb
    exact CliqueFree3.false hH ha hb hab
  · push Not at hdeg
    obtain ⟨W, hW, hWcard⟩ := exists_indepSet_of_cliqueFree H hH k (fun v => (hdeg v).le)
    refine ⟨W, ?_, hW⟩
    rw [Fintype.card_coe] at hWcard
    have h4 : 4 * k * k ≤ 4 * k * W.card := by
      calc 4 * k * k = 4 * k ^ 2 := by ring
        _ ≤ M.card * Nat.log 2 k := hM
        _ ≤ 4 * k * W.card := hWcard
    exact Nat.le_of_mul_le_mul_left h4 (by omega)

end E1182

end ShearerPart

section LowerPart

/-
# The lower bound `f(n) ≫ n^{3/2} (log n)^{1/2}`

This is the lower half of [BEFRS80, Theorem 2]. The witness is the graph
`K_1 + (t K_k ∪ s K_1)`: a centre joined to `t` disjoint cliques of size `k` and to `s` further
vertices (`starOfCliques t k s`, on `n = tk + s + 1` vertices).

If every triangle-free graph on `N₀ ≤ s` vertices has an independent set of size `k`
(`Ramsey3 N₀ k`, i.e. `R(3,k) ≤ N₀`), this graph embeds in the complement of every triangle-free
graph on `2n - 1` vertices, so it is `K_3`-good and `f n ≥ t k (k-1) / 2`.

Main results:
* `star_embeds`: the embedding.
* `two_mul_f_ge_of_ramsey3`: `Ramsey3 N₀ k → N₀ ≤ s → t * (k * (k - 1)) ≤ 2 * f (t * k + s + 1)`.
* `not_ramsey3_of_f_lt`: the contrapositive, an upper bound for `f` gives a lower bound for
  `R(3,k)`.
* `f_lower`: `∃ A > 0, ∀ᶠ n, A * n^(3/2) * √(log n) < f n`.
-/

open Finset SimpleGraph

namespace E1182

/-- `Ramsey3 N k`: every triangle-free graph on `N` vertices has an independent set of size `k`,
i.e. `R(3, k) ≤ N`. -/
def Ramsey3 (N k : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), C.CliqueFree 3 →
    ∃ I : Finset (Fin N), I.card = k ∧ ∀ a ∈ I, ∀ b ∈ I, ¬ C.Adj a b

/-- The Shearer-type bound gives `R(3, k) ≤ N` as soon as `4 k² ≤ N log₂ k`. -/
theorem ramsey3_of_log {N k : ℕ} (hk : 1 ≤ k) (hN : 4 * k ^ 2 ≤ N * Nat.log 2 k) :
    Ramsey3 N k := by
  intro C hC
  obtain ⟨I, -, hIk, hI⟩ := exists_indep_subset C hC k hk univ (by simpa using hN)
  exact ⟨I, hIk, hI⟩

/-- `Ramsey3 N k` applies to any vertex set of size at least `N` in any triangle-free graph. -/
theorem Ramsey3.exists_subset {N k : ℕ} (hR : Ramsey3 N k) {W : Type*} [DecidableEq W]
    (C : SimpleGraph W) (hC : C.CliqueFree 3) (M : Finset W) (hM : N ≤ M.card) :
    ∃ I ⊆ M, I.card = k ∧ ∀ a ∈ I, ∀ b ∈ I, ¬ C.Adj a b := by
  obtain ⟨M₀, hM₀, hM₀card⟩ := exists_subset_card_eq hM
  let e : M₀ ≃ Fin N := Finset.equivFinOfCardEq hM₀card
  let ι : Fin N ↪ W := ⟨fun i => (e.symm i : W), fun i j h => e.symm.injective (Subtype.ext h)⟩
  obtain ⟨I, hIk, hI⟩ := hR (C.comap ι) (hC.comap ⟨(Embedding.comap ι C).toCopy⟩)
  refine ⟨I.map ι, ?_, by simpa using hIk, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := mem_map.mp hx
    exact hM₀ (e.symm i).2
  · intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
    exact hI i hi j hj

/-- The vertex type of `K_1 + (t K_k ∪ s K_1)`: `none` is the centre, `some (inl (c, a))` is the
`a`-th vertex of the `c`-th clique, `some (inr j)` is the `j`-th leaf. -/
abbrev StarV (t k s : ℕ) := Option ((Fin t × Fin k) ⊕ Fin s)

/-- The graph `K_1 + (t K_k ∪ s K_1)`. -/
def starOfCliques (t k s : ℕ) : SimpleGraph (StarV t k s) where
  Adj x y := x ≠ y ∧ (x = none ∨ y = none ∨
    ∃ c a b, x = some (Sum.inl (c, a)) ∧ y = some (Sum.inl (c, b)))
  symm := ⟨by
    rintro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | ⟨c, a, b, h1, h2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨c, b, a, h2, h1⟩)⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem card_starV (t k s : ℕ) : Fintype.card (StarV t k s) = t * k + s + 1 := by
  simp [StarV]

theorem starOfCliques_connected (t k s : ℕ) : (starOfCliques t k s).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨none, fun w => ?_⟩
  by_cases hw : w = none
  · subst hw
    exact Reachable.refl _
  · exact (show (starOfCliques t k s).Adj none w from
      ⟨fun h => hw h.symm, Or.inl rfl⟩).reachable

/-- `K_1 + (t K_k ∪ s K_1)` has at least `t k (k-1) / 2` edges. -/
theorem starOfCliques_edges (t k s : ℕ) :
    t * (k * (k - 1)) ≤ 2 * (starOfCliques t k s).edgeSet.ncard := by
  classical
  have hdeg : ∀ p : Fin t × Fin k,
      k - 1 ≤ (starOfCliques t k s).degree (some (Sum.inl p)) := by
    rintro ⟨c, a⟩
    rw [← card_neighborFinset_eq_degree]
    have hsub : ((univ : Finset (Fin k)).erase a).image
        (fun b => (some (Sum.inl (c, b)) : StarV t k s))
          ⊆ (starOfCliques t k s).neighborFinset (some (Sum.inl (c, a))) := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
      rw [mem_neighborFinset]
      refine ⟨fun h => ?_, Or.inr (Or.inr ⟨c, a, b, rfl, rfl⟩)⟩
      have hab : a = b := by simpa using h
      exact (mem_erase.mp hb).1 hab.symm
    have hinj : Function.Injective (fun b : Fin k => (some (Sum.inl (c, b)) : StarV t k s)) := by
      intro b b' h
      simpa using h
    calc k - 1 = (((univ : Finset (Fin k)).erase a).image
          (fun b => (some (Sum.inl (c, b)) : StarV t k s))).card := by
          rw [card_image_of_injective _ hinj, card_erase_of_mem (mem_univ a), card_univ,
            Fintype.card_fin]
      _ ≤ _ := card_le_card hsub
  have hsum := (starOfCliques t k s).sum_degrees_eq_twice_card_edges
  have h1 : t * (k * (k - 1)) ≤ ∑ v, (starOfCliques t k s).degree v := by
    calc t * (k * (k - 1)) = ∑ _p : Fin t × Fin k, (k - 1) := by
          simp [mul_assoc]
      _ ≤ ∑ p : Fin t × Fin k, (starOfCliques t k s).degree (some (Sum.inl p)) :=
          sum_le_sum fun p _ => hdeg p
      _ ≤ ∑ v, (starOfCliques t k s).degree v := by
          rw [Fintype.sum_option, Fintype.sum_sum_type]
          omega
  rw [hsum] at h1
  rwa [← Set.ncard_coe_finset, coe_edgeFinset] at h1

/-- In a triangle-free graph, a set `M` of at least `t k + N₀` vertices contains `t` pairwise
disjoint independent sets of size `k`, provided `R(3, k) ≤ N₀`. -/
theorem exists_blocks {W : Type*} [DecidableEq W] (C : SimpleGraph W)
    (hC : C.CliqueFree 3) {k N₀ : ℕ} (hR : Ramsey3 N₀ k) :
    ∀ (t : ℕ) (M : Finset W), t * k + N₀ ≤ M.card →
      ∃ I : Fin t → Finset W, (∀ c, I c ⊆ M) ∧ (∀ c, (I c).card = k) ∧
        (∀ c, ∀ a ∈ I c, ∀ b ∈ I c, ¬ C.Adj a b) ∧ (∀ c c', c ≠ c' → Disjoint (I c) (I c')) := by
  intro t
  induction t with
  | zero =>
    intro M _
    exact ⟨fun c => c.elim0, fun c => c.elim0, fun c => c.elim0, fun c => c.elim0,
      fun c => c.elim0⟩
  | succ t ih =>
    intro M hM
    have hM' : N₀ ≤ M.card := le_trans (Nat.le_add_left _ _) hM
    obtain ⟨I₀, hI₀M, hI₀k, hI₀⟩ := hR.exists_subset C hC M hM'
    have hcard : t * k + N₀ ≤ (M \ I₀).card := by
      have h1 := le_card_sdiff I₀ M
      have h2 : (t + 1) * k = t * k + k := by ring
      omega
    obtain ⟨I, hIM, hIk, hI, hdisj⟩ := ih (M \ I₀) hcard
    refine ⟨Fin.cons I₀ I, ?_, ?_, ?_, ?_⟩
    · intro c
      refine Fin.cases ?_ (fun c' => ?_) c
      · simpa using hI₀M
      · simpa using (hIM c').trans sdiff_subset
    · intro c
      refine Fin.cases ?_ (fun c' => ?_) c
      · simpa using hI₀k
      · simpa using hIk c'
    · intro c
      refine Fin.cases ?_ (fun c' => ?_) c
      · simpa using hI₀
      · simpa using hI c'
    · intro c c'
      refine Fin.cases ?_ (fun d => ?_) c <;> refine Fin.cases ?_ (fun d' => ?_) c'
      · intro h
        exact absurd rfl h
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact disjoint_sdiff.mono_right (hIM d')
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact sdiff_disjoint.mono_left (hIM d)
      · intro h
        simp only [Fin.cons_succ]
        exact hdisj d d' (fun e => h (congrArg Fin.succ e))

/-- **The embedding.** If `R(3, k) ≤ N₀ ≤ s`, then `K_1 + (t K_k ∪ s K_1)` (on `n = tk + s + 1`
vertices) embeds in the complement of every triangle-free graph on `2n - 1` vertices. -/
theorem star_embeds {W : Type*} [Fintype W] (C : SimpleGraph W) (hC : C.CliqueFree 3)
    (t k s N₀ : ℕ) (hR : Ramsey3 N₀ k) (hs : N₀ ≤ s)
    (hW : Fintype.card W = 2 * (t * k + s + 1) - 1) :
    ∃ φ : StarV t k s → W, Function.Injective φ ∧
      ∀ x y, (starOfCliques t k s).Adj x y → ¬ C.Adj (φ x) (φ y) := by
  classical
  have hWpos : 0 < Fintype.card W := by omega
  obtain ⟨x₀⟩ : Nonempty W := Fintype.card_pos_iff.mp hWpos
  by_cases hdeg : t * k + s + 1 ≤ C.degree x₀
  · -- the neighbourhood of `x₀` is an independent set of size at least `n`
    have hcard : Fintype.card (StarV t k s) ≤ Fintype.card (C.neighborFinset x₀) := by
      rw [card_starV, Fintype.card_coe, card_neighborFinset_eq_degree]
      exact hdeg
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine ⟨fun x => (g x : W), fun x y h => g.injective (Subtype.ext h), fun x y _ hadj => ?_⟩
    have hx := (mem_neighborFinset _ _ _).mp (g x).2
    have hy := (mem_neighborFinset _ _ _).mp (g y).2
    exact CliqueFree3.false hC hx hy hadj
  · push Not at hdeg
    -- `M`: the non-neighbours of `x₀`
    let M : Finset W := univ.filter fun y => y ≠ x₀ ∧ ¬ C.Adj x₀ y
    have hMmem : ∀ y, y ∈ M ↔ y ≠ x₀ ∧ ¬ C.Adj x₀ y := by
      intro y
      simp [M]
    have hMcard : t * k + s ≤ M.card := by
      have hM : M = univ \ insert x₀ (C.neighborFinset x₀) := by
        ext y
        simp [M, mem_neighborFinset]
      have h1 := le_card_sdiff (insert x₀ (C.neighborFinset x₀)) univ
      have h2 := card_insert_le x₀ (C.neighborFinset x₀)
      rw [card_neighborFinset_eq_degree] at h2
      rw [← hM, card_univ, hW] at h1
      omega
    obtain ⟨I, hIM, hIk, hI, hdisj⟩ := exists_blocks C hC hR t M (by omega)
    let U : Finset W := univ.biUnion I
    have hU : U.card ≤ t * k := by
      calc U.card ≤ ∑ c : Fin t, (I c).card := card_biUnion_le
        _ = t * k := by simp [hIk]
    let L : Finset W := M \ U
    have hL : s ≤ L.card := by
      have h1 : M.card - U.card ≤ L.card := le_card_sdiff U M
      omega
    obtain ⟨g⟩ : Nonempty (Fin s ↪ L) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hL)
    let e : ∀ c, Fin k ≃ I c := fun c => (Finset.equivFinOfCardEq (hIk c)).symm
    let φ : StarV t k s → W := fun x =>
      match x with
      | none => x₀
      | some (Sum.inl (c, a)) => (e c a : W)
      | some (Sum.inr j) => (g j : W)
    have hφblock : ∀ c a, φ (some (Sum.inl (c, a))) ∈ I c := fun c a => (e c a).2
    have hφU : ∀ c a, φ (some (Sum.inl (c, a))) ∈ U := fun c a =>
      mem_biUnion.mpr ⟨c, mem_univ _, hφblock c a⟩
    have hφleaf : ∀ j, φ (some (Sum.inr j)) ∈ L := fun j => (g j).2
    have hφM : ∀ x, x ≠ none → φ x ∈ M := by
      rintro (_ | (⟨c, a⟩ | j)) hx
      · exact absurd rfl hx
      · exact hIM c (hφblock c a)
      · exact (mem_sdiff.mp (hφleaf j)).1
    have hφne : ∀ x, x ≠ none → φ x ≠ x₀ := fun x hx => ((hMmem _).mp (hφM x hx)).1
    have hφ0 : φ none = x₀ := rfl
    refine ⟨φ, ?_, ?_⟩
    · -- injectivity
      rintro (_ | (⟨c, a⟩ | j)) (_ | (⟨c', a'⟩ | j')) h
      · rfl
      · exact absurd (h.symm.trans hφ0) (hφne (some (Sum.inl (c', a'))) (by simp))
      · exact absurd (h.symm.trans hφ0) (hφne (some (Sum.inr j')) (by simp))
      · exact absurd (h.trans hφ0) (hφne (some (Sum.inl (c, a))) (by simp))
      · have hcc : c = c' := by
          by_contra hne
          have h1 := hφblock c a
          have h2 := hφblock c' a'
          rw [h] at h1
          exact disjoint_left.mp (hdisj c c' hne) h1 h2
        subst hcc
        have h3 : e c a = e c a' := Subtype.ext h
        rw [(e c).injective h3]
      · have h1 := hφU c a
        rw [h] at h1
        exact absurd h1 (mem_sdiff.mp (hφleaf j')).2
      · exact absurd (h.trans hφ0) (hφne (some (Sum.inr j)) (by simp))
      · have h1 := hφU c' a'
        rw [← h] at h1
        exact absurd h1 (mem_sdiff.mp (hφleaf j)).2
      · have h3 : g j = g j' := Subtype.ext h
        rw [g.injective h3]
    · -- edges go to non-edges
      rintro x y ⟨hne, hxy⟩
      rcases hxy with rfl | rfl | ⟨c, a, b, rfl, rfl⟩
      · exact ((hMmem _).mp (hφM y (fun h => hne h.symm))).2
      · exact fun h => ((hMmem _).mp (hφM x hne)).2 h.symm
      · exact hI c _ (hφblock c a) _ (hφblock c b)

/-- **Explicit lower bound.** If `R(3, k) ≤ N₀ ≤ s` then `f (t k + s + 1) ≥ t k (k-1) / 2`. -/
theorem two_mul_f_ge_of_ramsey3 (t k s N₀ : ℕ) (hR : Ramsey3 N₀ k) (hs : N₀ ≤ s) :
    t * (k * (k - 1)) ≤ 2 * f (t * k + s + 1) := by
  have h := le_f_of_embeds (card_starV t k s) (starOfCliques t k s)
    (starOfCliques_connected t k s)
    (fun C hC => star_embeds C hC t k s N₀ hR hs (by simp))
  have h2 := starOfCliques_edges t k s
  omega

/-- **Upper bounds for `f` give lower bounds for `R(3, k)`.** If `2 f(tk + s + 1) < t k (k-1)`,
then `R(3, k) > s`: some triangle-free graph on `s` vertices has no independent set of size `k`.
In particular any proof of `f(n) ≪ n^{3/2} (log n)^{1/2}` contains Kim's theorem
`R(3,k) ≫ k² / log k`. -/
theorem not_ramsey3_of_f_lt (t k s : ℕ) (h : 2 * f (t * k + s + 1) < t * (k * (k - 1))) :
    ¬ Ramsey3 s k :=
  fun hR => absurd (two_mul_f_ge_of_ramsey3 t k s s hR le_rfl) (not_le.mpr h)

/-- Explicit lower bound in terms of `n` only. -/
theorem two_mul_f_ge (n k N₀ : ℕ) (hk : 1 ≤ k) (hR : Ramsey3 N₀ k) :
    (n - 1 - N₀ - k) * (k - 1) ≤ 2 * f n := by
  rcases Nat.lt_or_ge (n - 1) (N₀ + k) with h | h
  · have h0 : n - 1 - N₀ - k = 0 := by omega
    simp [h0]
  · have h1 : (n - 1 - N₀) / k * k ≤ n - 1 - N₀ := Nat.div_mul_le_self _ _
    have h2 : n - 1 - N₀ < (n - 1 - N₀) / k * k + k := Nat.lt_div_mul_add hk
    generalize (n - 1 - N₀) / k = t at h1 h2
    have hn : t * k + (n - 1 - t * k) + 1 = n := by omega
    have h3 := two_mul_f_ge_of_ramsey3 t k (n - 1 - t * k) N₀ hR (by omega)
    rw [hn] at h3
    calc (n - 1 - N₀ - k) * (k - 1) ≤ (t * k) * (k - 1) := Nat.mul_le_mul_right _ (by omega)
      _ = t * (k * (k - 1)) := by ring
      _ ≤ 2 * f n := h3

/-- `log k - 1 ≤ ⌊log₂ k⌋`. -/
theorem log_sub_one_le_natLog (k : ℕ) (hk : 1 ≤ k) : Real.log k - 1 ≤ (Nat.log 2 k : ℝ) := by
  have h1 : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have h2 : (k : ℝ) < 2 ^ (Nat.log 2 k + 1) := by exact_mod_cast h1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : Real.log k < Real.log ((2 : ℝ) ^ (Nat.log 2 k + 1)) := Real.log_lt_log hkpos h2
  rw [Real.log_pow] at h3
  have h4 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h5 : (0 : ℝ) ≤ ((Nat.log 2 k + 1 : ℕ) : ℝ) := by positivity
  have h6 : ((Nat.log 2 k + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((Nat.log 2 k + 1 : ℕ) : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left h4 h5
  push_cast at h3 h6 ⊢
  linarith

/-- **[BEFRS80, Theorem 2], lower bound.** There is `A > 0` with
`A n^{3/2} (log n)^{1/2} < f(n)` for all large `n`. (Here `A = 1/257`, `n ≥ 2^24`.) -/
theorem f_lower : ∃ A > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    A * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) < (f n : ℝ) := by
  refine ⟨1 / 257, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 24)] with n hn
  have hnR : (2 : ℝ) ^ 24 ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hL16 : 16 ≤ Real.log n := by
    have h1 : Real.log ((2 : ℝ) ^ 24) ≤ Real.log n := Real.log_le_log (by positivity) hnR
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have hLn : Real.log n ≤ n := by
    have h1 := Real.log_le_sub_one_of_pos hnpos
    linarith
  generalize hL : Real.log (n : ℝ) = L at hL16 hLn ⊢
  have hnL : 0 ≤ (n : ℝ) * L := by positivity
  obtain ⟨y, hy⟩ : ∃ y, y = Real.sqrt (n * L) := ⟨_, rfl⟩
  have hy2 : y ^ 2 = n * L := by rw [hy]; exact Real.sq_sqrt hnL
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hy_ge : 2 ^ 14 ≤ y := by
    have h28 : ((2 : ℝ) ^ 14) ^ 2 ≤ n * L := by
      calc ((2 : ℝ) ^ 14) ^ 2 = 2 ^ 24 * 16 := by norm_num
        _ ≤ n * L := mul_le_mul hnR hL16 (by norm_num) hnpos.le
    rw [hy]
    calc (2 : ℝ) ^ 14 = Real.sqrt (((2 : ℝ) ^ 14) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (n * L) := Real.sqrt_le_sqrt h28
  have hy_le : y ≤ n := by
    rw [hy]
    calc Real.sqrt (n * L) ≤ Real.sqrt (n * n) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLn hnpos.le)
      _ = n := Real.sqrt_mul_self hnpos.le
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊y / 8⌋₊ := ⟨_, rfl⟩
  have hk_le : (k : ℝ) ≤ y / 8 := by rw [hk]; exact Nat.floor_le (by positivity)
  have hk_ge : y / 16 ≤ (k : ℝ) := by
    have h1 := Nat.lt_floor_add_one (y / 8)
    rw [← hk] at h1
    linarith
  have hk2 : 2 ≤ k := by
    have h1 : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast h1
  have hkpos : (0 : ℝ) < k := by linarith
  have hlogk : L / 2 - 3 ≤ Real.log k := by
    have h1 : Real.log (y / 16) ≤ Real.log k := Real.log_le_log (by positivity) hk_ge
    have h2 : Real.log (y / 16) = Real.log y - Real.log 16 :=
      Real.log_div (by positivity) (by norm_num)
    have h3 : Real.log y = (Real.log n + Real.log L) / 2 := by
      rw [hy, Real.log_sqrt hnL, Real.log_mul hnpos.ne' (by positivity)]
    have h4 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have h5 : Real.log 16 ≤ 3 := by
      have h6 : (16 : ℝ) = 2 ^ 4 := by norm_num
      rw [h6, Real.log_pow]
      have h7 := Real.log_two_lt_d9
      push_cast
      linarith
    rw [hL] at h3
    linarith
  have hnatlog : L / 4 ≤ (Nat.log 2 k : ℝ) := by
    have h1 := log_sub_one_le_natLog k (by omega)
    linarith
  have hN₀R : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have h1 : n ≤ 2 * (n / 2) + 1 := by omega
    have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hcond : 4 * k ^ 2 ≤ n / 2 * Nat.log 2 k := by
    have h0 : (4 * (k : ℝ) ^ 2) ≤ ((n / 2 : ℕ) : ℝ) * (Nat.log 2 k : ℝ) := by
      have h1 : 4 * (k : ℝ) ^ 2 ≤ n * L / 16 := by nlinarith
      have h2 : (n : ℝ) * L / 16 ≤ ((n : ℝ) / 2 - 1 / 2) * (L / 4) := by nlinarith
      have h3 : ((n : ℝ) / 2 - 1 / 2) * (L / 4) ≤ ((n / 2 : ℕ) : ℝ) * (Nat.log 2 k : ℝ) :=
        mul_le_mul hN₀R hnatlog (by positivity) (by positivity)
      linarith
    exact_mod_cast h0
  have hmain := two_mul_f_ge n k (n / 2) (by omega) (ramsey3_of_log (by omega) hcond)
  have h4k : 4 * k + 4 ≤ n := by
    have h1 : (4 * (k : ℝ) + 4) ≤ n := by linarith
    exact_mod_cast h1
  have hnk : n * k ≤ 16 * f n := by
    have h1 : n ≤ 4 * (n - 1 - n / 2 - k) := by omega
    have h2 : k ≤ 2 * (k - 1) := by omega
    calc n * k ≤ (4 * (n - 1 - n / 2 - k)) * (2 * (k - 1)) := Nat.mul_le_mul h1 h2
      _ = 8 * ((n - 1 - n / 2 - k) * (k - 1)) := by ring
      _ ≤ 8 * (2 * f n) := Nat.mul_le_mul_left _ hmain
      _ = 16 * f n := by ring
  have hnkR : (n : ℝ) * k ≤ 16 * f n := by exact_mod_cast hnk
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt L = n * y := by
    have h1 : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [h1, hy, Real.sqrt_mul hnpos.le, mul_assoc]
  have hny : 0 < (n : ℝ) * y := by nlinarith
  calc 1 / 257 * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt L = (n * y) / 257 := by
        rw [mul_assoc, hpow]; ring
    _ < (n * y) / 256 := by linarith
    _ ≤ (n * k) / 16 := by nlinarith
    _ ≤ f n := by linarith

end E1182

end LowerPart

section UpperPart

/-
# The upper bound `f(n) ≪ n^{3/2} log n`

This formalizes the `s = 3` case of Sudakov's theorem
[B. Sudakov, *Ramsey numbers and the size of graphs*, SIAM J. Discrete Math. 21 (2007),
Theorem 1.1]: a graph with `m` edges satisfies `R(K_3, G) ≥ c (m / log m)^{2/3}`. In the form
needed here: if `G` has `n` vertices and at least `B n^{3/2} log n` edges, there is a triangle-free
graph on `2n - 1` vertices whose complement contains no copy of `G`.

The proof follows Sudakov's (after Krivelevich): colour the pairs of `[N]` red with probability
`1/q`, `q ≈ √N`; with positive probability every copy of `G` has more than `3k` red edges
(a Chernoff-type bound) and meets fewer than `k` pairwise edge-disjoint red triangles (the
Erdős–Tetali bound); deleting the edges of a maximal family of edge-disjoint red triangles leaves a
triangle-free graph that still meets every copy of `G`.

Probability is replaced by counting colourings `Sym2 (Fin N) → Fin q` (red is the colour `0`).

Main results:
* `exists_triangleFree_hitting`: the explicit statement.
* `f_upper_sudakov`: `∃ B > 0, ∀ᶠ n, f n < B * n^(3/2) * log n`.
-/

open Finset

namespace E1182

section Colourings

variable {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}

/-- The basic product formula: summing a product of weights over all colourings. -/
theorem sum_prod_weights (S : Finset E) (w : Fin q → ℕ) :
    (∑ c : E → Fin q, ∏ e ∈ S, w (c e)) * q ^ S.card
      = (∑ j, w j) ^ S.card * q ^ Fintype.card E := by
  have h1 : ∀ c : E → Fin q, ∏ e ∈ S, w (c e) = ∏ e, (if e ∈ S then w (c e) else 1) := by
    intro c
    rw [Fintype.prod_ite_mem]
  have h2 : ∑ c : E → Fin q, ∏ e, (if e ∈ S then w (c e) else 1)
      = ∏ e : E, ∑ j : Fin q, (if e ∈ S then w j else 1) := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
  have h3 : ∀ e : E, ∑ j : Fin q, (if e ∈ S then w j else 1)
      = if e ∈ S then ∑ j, w j else q := by
    intro e
    split_ifs <;> simp
  have h4 : ∏ e : E, (if e ∈ S then ∑ j, w j else q) = (∑ j, w j) ^ S.card * q ^ Sᶜ.card := by
    rw [prod_ite, prod_const, prod_const]
    congr 2
    · congr 1
      ext e
      simp
    · congr 1
      ext e
      simp
  simp_rw [h1]
  rw [h2]
  simp_rw [h3]
  rw [h4, mul_assoc, ← pow_add, card_compl, Nat.sub_add_cancel (card_le_univ S)]

/-- The number of colourings in which all pairs of `U` are red is at most `q^(|E| - |U|)`. -/
theorem card_allRed_mul_le [NeZero q] (U : Finset E) (B : Finset (E → Fin q))
    (hB : ∀ c ∈ B, ∀ e ∈ U, c e = 0) :
    B.card * q ^ U.card ≤ q ^ Fintype.card E := by
  have h := sum_prod_weights U (fun j : Fin q => if j = 0 then 1 else 0)
  have h1 : ∀ c ∈ B, ∏ e ∈ U, (if c e = 0 then 1 else 0) = 1 := by
    intro c hc
    exact prod_eq_one fun e he => by rw [if_pos (hB c hc e he)]
  have h2 : B.card ≤ ∑ c : E → Fin q, ∏ e ∈ U, (if c e = 0 then 1 else 0) := by
    calc B.card = ∑ c ∈ B, ∏ e ∈ U, (if c e = 0 then 1 else 0) := by
          rw [sum_congr rfl h1, sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ c : E → Fin q, ∏ e ∈ U, (if c e = 0 then 1 else 0) :=
          sum_le_sum_of_subset (subset_univ B)
  have h3 : ∑ j : Fin q, (if j = 0 then 1 else 0 : ℕ) = 1 := by simp
  calc B.card * q ^ U.card
      ≤ (∑ c : E → Fin q, ∏ e ∈ U, (if c e = 0 then 1 else 0)) * q ^ U.card :=
        Nat.mul_le_mul_right _ h2
    _ = q ^ Fintype.card E := by rw [h, h3, one_pow, one_mul]

/-- A Chernoff-type bound by counting: the number of colourings with at most `r` red pairs in
`F`. -/
theorem card_fewRed_mul_le [NeZero q] (F : Finset E) (r : ℕ) (B : Finset (E → Fin q))
    (hB : ∀ c ∈ B, (F.filter fun e => c e = 0).card ≤ r) :
    B.card * 2 ^ F.card * q ^ F.card
      ≤ 2 ^ r * (2 * q - 1) ^ F.card * q ^ Fintype.card E := by
  have h := sum_prod_weights F (fun j : Fin q => if j = 0 then 1 else 2)
  have hsum : ∑ j : Fin q, (if j = 0 then 1 else 2) = 2 * q - 1 := by
    have h2 : ∑ j : Fin q, ((if j = 0 then 1 else 2) + (if j = 0 then 1 else 0)) = 2 * q := by
      have h3 : ∀ j : Fin q, ((if j = 0 then 1 else 2) + (if j = 0 then 1 else 0) : ℕ) = 2 := by
        intro j
        split_ifs <;> rfl
      simp [h3, mul_comm]
    rw [sum_add_distrib] at h2
    have h4 : ∑ j : Fin q, (if j = 0 then 1 else 0 : ℕ) = 1 := by simp
    omega
  have hprod : ∀ c : E → Fin q, ∏ e ∈ F, (if c e = 0 then 1 else 2)
      = 2 ^ (F.filter fun e => ¬ c e = 0).card := by
    intro c
    rw [prod_ite, prod_const_one, prod_const, one_mul]
  have hind : ∀ c : E → Fin q,
      (if (F.filter fun e => c e = 0).card ≤ r then 1 else 0) * 2 ^ F.card
        ≤ 2 ^ r * ∏ e ∈ F, (if c e = 0 then 1 else 2) := by
    intro c
    rw [hprod]
    have hsplit := card_filter_add_card_filter_not (s := F) (fun e => c e = 0)
    split_ifs with hc
    · rw [one_mul, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · simp
  have hBsub : B ⊆ univ.filter fun c : E → Fin q => (F.filter fun e => c e = 0).card ≤ r :=
    fun c hc => mem_filter.mpr ⟨mem_univ _, hB c hc⟩
  calc B.card * 2 ^ F.card * q ^ F.card
      ≤ (univ.filter fun c : E → Fin q => (F.filter fun e => c e = 0).card ≤ r).card
          * 2 ^ F.card * q ^ F.card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (card_le_card hBsub))
    _ = (∑ c : E → Fin q, (if (F.filter fun e => c e = 0).card ≤ r then 1 else 0) * 2 ^ F.card)
          * q ^ F.card := by
        rw [card_filter, sum_mul]
    _ ≤ (∑ c : E → Fin q, 2 ^ r * ∏ e ∈ F, (if c e = 0 then 1 else 2)) * q ^ F.card :=
        Nat.mul_le_mul_right _ (sum_le_sum fun c _ => hind c)
    _ = 2 ^ r * ((∑ c : E → Fin q, ∏ e ∈ F, (if c e = 0 then 1 else 2)) * q ^ F.card) := by
        rw [← mul_sum, mul_assoc]
    _ = 2 ^ r * (2 * q - 1) ^ F.card * q ^ Fintype.card E := by
        rw [h, hsum, mul_assoc]

end Colourings

section Triangles

variable {V : Type*} [DecidableEq V] {q : ℕ} [NeZero q]

/-- The pairs inside a vertex set (for a triangle: its three edges). -/
def triEdges (T : Finset V) : Finset (Sym2 V) := T.offDiag.image Sym2.mk.uncurry

theorem mem_triEdges {T : Finset V} {e : Sym2 V} :
    e ∈ triEdges T ↔ ∃ a b, a ∈ T ∧ b ∈ T ∧ a ≠ b ∧ s(a, b) = e := by
  unfold triEdges
  rw [mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hp, rfl⟩
    rw [mem_offDiag] at hp
    exact ⟨a, b, hp.1, hp.2.1, hp.2.2, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩

theorem card_triEdges {T : Finset V} (hT : T.card = 3) : (triEdges T).card = 3 := by
  rw [triEdges, Sym2.card_image_offDiag, hT]
  rfl

theorem mem_triEdges_triple {a b d : V} {e : Sym2 V}
    (he : e ∈ triEdges ({a, b, d} : Finset V)) :
    e = s(a, b) ∨ e = s(a, d) ∨ e = s(b, d) := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := mem_triEdges.mp he
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | exact Or.inl rfl
      | exact Or.inl Sym2.eq_swap
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inl Sym2.eq_swap)
      | exact Or.inr (Or.inr rfl)
      | exact Or.inr (Or.inr Sym2.eq_swap)

/-- `T` is a red triangle of the colouring `c`. -/
def IsRedTri (c : Sym2 V → Fin q) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ e ∈ triEdges T, c e = 0

/-- `P` is a family of pairwise edge-disjoint red triangles. -/
def IsPacking (c : Sym2 V → Fin q) (P : Finset (Finset V)) : Prop :=
  (∀ T ∈ P, IsRedTri c T) ∧
    ∀ T ∈ P, ∀ T' ∈ P, T ≠ T' → Disjoint (triEdges T) (triEdges T')

/-- The red graph with the edges of all triangles of `P` removed. -/
def cleaned (c : Sym2 V → Fin q) (P : Finset (Finset V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ c s(a, b) = 0 ∧ s(a, b) ∉ P.biUnion triEdges
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2.1,
    by rw [Sym2.eq_swap]; exact h.2.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- There is a packing `P` such that every red triangle has an edge in a triangle of `P`. -/
theorem exists_max_packing [Fintype V] (c : Sym2 V → Fin q) :
    ∃ P : Finset (Finset V), IsPacking c P ∧
      ∀ T, IsRedTri c T → ∃ e ∈ triEdges T, e ∈ P.biUnion triEdges := by
  classical
  let cand : Finset (Finset (Finset V)) := univ.filter (IsPacking c)
  have hne : cand.Nonempty := ⟨∅, by simp [cand, IsPacking]⟩
  obtain ⟨P, hP, hmax⟩ := exists_max_image cand card hne
  have hPp : IsPacking c P := (mem_filter.mp hP).2
  refine ⟨P, hPp, fun T hT => ?_⟩
  by_contra hcon
  push Not at hcon
  have hTP : T ∉ P := by
    intro hTP
    have hcard := card_triEdges hT.1
    obtain ⟨e, he⟩ : (triEdges T).Nonempty := card_pos.mp (by omega)
    exact hcon e he (mem_biUnion.mpr ⟨T, hTP, he⟩)
  have hins : IsPacking c (insert T P) := by
    refine ⟨?_, ?_⟩
    · intro T' hT'
      rcases mem_insert.mp hT' with rfl | hT'
      · exact hT
      · exact hPp.1 T' hT'
    · intro T₁ h₁ T₂ h₂ hne
      rcases mem_insert.mp h₁ with e₁ | m₁ <;> rcases mem_insert.mp h₂ with e₂ | m₂
      · exact absurd (e₁.trans e₂.symm) hne
      · rw [e₁, disjoint_left]
        intro e he he'
        exact hcon e he (mem_biUnion.mpr ⟨T₂, m₂, he'⟩)
      · rw [e₂, disjoint_right]
        intro e he he'
        exact hcon e he (mem_biUnion.mpr ⟨T₁, m₁, he'⟩)
      · exact hPp.2 T₁ m₁ T₂ m₂ hne
  have h := hmax (insert T P) (mem_filter.mpr ⟨mem_univ _, hins⟩)
  rw [card_insert_of_notMem hTP] at h
  omega

/-- The cleaned graph is triangle-free. -/
theorem cleaned_cliqueFree (c : Sym2 V → Fin q) (P : Finset (Finset V))
    (hmax : ∀ T, IsRedTri c T → ∃ e ∈ triEdges T, e ∈ P.biUnion triEdges) :
    (cleaned c P).CliqueFree 3 := by
  refine cliqueFree3_of_forall fun a b d hab had hbd => ?_
  have hT : IsRedTri c ({a, b, d} : Finset V) := by
    refine ⟨card_eq_three.mpr ⟨a, b, d, hab.1, had.1, hbd.1, rfl⟩, fun e he => ?_⟩
    rcases mem_triEdges_triple he with rfl | rfl | rfl
    · exact hab.2.1
    · exact had.2.1
    · exact hbd.2.1
  obtain ⟨e, he, heP⟩ := hmax _ hT
  rcases mem_triEdges_triple he with rfl | rfl | rfl
  · exact hab.2.2 heP
  · exact had.2.2 heP
  · exact hbd.2.2 heP

/-- Bad event: the edge set `F` has at most `r` red pairs. -/
def FewRed (c : Sym2 V → Fin q) (F : Finset (Sym2 V)) (r : ℕ) : Prop :=
  (F.filter fun e => c e = 0).card ≤ r

/-- Bad event: there are `k` pairwise edge-disjoint red triangles, each sharing an edge
with `F`. -/
def ManyTri (c : Sym2 V → Fin q) (F : Finset (Sym2 V)) (k : ℕ) : Prop :=
  ∃ S : Finset (Finset V), S.card = k ∧ IsPacking c S ∧ ∀ T ∈ S, ∃ e ∈ F, e ∈ triEdges T

/-- If neither bad event holds for `F`, then after removing the edges of any packing, `F` still
contains a red pair. -/
theorem exists_red_edge (c : Sym2 V → Fin q) (P : Finset (Finset V)) (hP : IsPacking c P)
    (F : Finset (Sym2 V)) (k : ℕ) (h1 : ¬ FewRed c F (3 * k)) (h2 : ¬ ManyTri c F k) :
    ∃ e ∈ F, c e = 0 ∧ e ∉ P.biUnion triEdges := by
  classical
  have hPF : (P.filter fun T => ∃ e ∈ F, e ∈ triEdges T).card < k := by
    by_contra hge
    push Not at hge
    obtain ⟨S, hS, hSk⟩ := exists_subset_card_eq hge
    exact h2 ⟨S, hSk, ⟨fun T hT => hP.1 T (mem_filter.mp (hS hT)).1,
      fun T hT T' hT' hne => hP.2 T (mem_filter.mp (hS hT)).1 T' (mem_filter.mp (hS hT')).1 hne⟩,
      fun T hT => (mem_filter.mp (hS hT)).2⟩
  by_contra hcon
  push Not at hcon
  apply h1
  have hsub : F.filter (fun e => c e = 0)
      ⊆ (P.filter fun T => ∃ e ∈ F, e ∈ triEdges T).biUnion triEdges := by
    intro e he
    rw [mem_filter] at he
    obtain ⟨T, hT, heT⟩ := mem_biUnion.mp (hcon e he.1 he.2)
    exact mem_biUnion.mpr ⟨T, mem_filter.mpr ⟨hT, e, he.1, heT⟩, heT⟩
  calc (F.filter fun e => c e = 0).card
      ≤ ((P.filter fun T => ∃ e ∈ F, e ∈ triEdges T).biUnion triEdges).card := card_le_card hsub
    _ ≤ ∑ T ∈ P.filter (fun T => ∃ e ∈ F, e ∈ triEdges T), (triEdges T).card :=
        card_biUnion_le
    _ = ∑ T ∈ P.filter (fun T => ∃ e ∈ F, e ∈ triEdges T), 3 :=
        sum_congr rfl fun T hT => card_triEdges (hP.1 T (mem_filter.mp hT).1).1
    _ = 3 * (P.filter fun T => ∃ e ∈ F, e ∈ triEdges T).card := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 * k := by omega

/-- The number of triangles sharing an edge with `F` is at most `|F| * |V|`. -/
theorem card_triangles_meeting_le [Fintype V] (F : Finset (Sym2 V)) :
    ((powersetCard 3 (univ : Finset V)).filter fun T => ∃ e ∈ F, e ∈ triEdges T).card
      ≤ F.card * Fintype.card V := by
  classical
  have hsub : ((powersetCard 3 (univ : Finset V)).filter fun T => ∃ e ∈ F, e ∈ triEdges T)
      ⊆ (F ×ˢ (univ : Finset V)).image fun p => insert p.2 p.1.toFinset := by
    intro T hT
    obtain ⟨hT3, e, heF, heT⟩ := mem_filter.mp hT
    have hcard : T.card = 3 := (mem_powersetCard.mp hT3).2
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_triEdges.mp heT
    have hfin : (s(a, b) : Sym2 V).toFinset = {a, b} := by
      ext x
      simp [Sym2.mem_toFinset]
    have hpair : ({a, b} : Finset V) ⊆ T := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [mem_singleton] at hx
        exact hx ▸ hb
    have hcard2 : ({a, b} : Finset V).card = 2 := card_pair hab
    obtain ⟨w, hwT, hw⟩ : ∃ w ∈ T, w ∉ ({a, b} : Finset V) :=
      exists_mem_notMem_of_card_lt_card (by omega)
    refine mem_image.mpr ⟨(s(a, b), w), mem_product.mpr ⟨heF, mem_univ _⟩, ?_⟩
    simp only [hfin]
    refine eq_of_subset_of_card_le (insert_subset hwT hpair) ?_
    rw [card_insert_of_notMem hw, hcard2, hcard]
  calc _ ≤ ((F ×ˢ (univ : Finset V)).image fun p => insert p.2 p.1.toFinset).card :=
        card_le_card hsub
    _ ≤ (F ×ˢ (univ : Finset V)).card := card_image_le
    _ = F.card * Fintype.card V := by rw [card_product, card_univ]

/-- The Erdős–Tetali bound by counting: the number of colourings with `k` pairwise edge-disjoint
red triangles, each sharing an edge with `F`. -/
theorem card_manyTri_mul_le [Fintype V] (F : Finset (Sym2 V)) (k : ℕ)
    (B : Finset (Sym2 V → Fin q))
    (hB : ∀ c ∈ B, ManyTri c F k) :
    B.card * q ^ (3 * k)
      ≤ (F.card * Fintype.card V).choose k * q ^ Fintype.card (Sym2 V) := by
  classical
  let TF : Finset (Finset V) :=
    (powersetCard 3 (univ : Finset V)).filter fun T => ∃ e ∈ F, e ∈ triEdges T
  let cand : Finset (Finset (Finset V)) := (powersetCard k TF).filter fun S =>
    ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → Disjoint (triEdges T) (triEdges T')
  let Bof : Finset (Finset V) → Finset (Sym2 V → Fin q) := fun S =>
    B.filter fun c => ∀ e ∈ S.biUnion triEdges, c e = 0
  have hcover : B ⊆ cand.biUnion Bof := by
    intro c hc
    obtain ⟨S, hSk, hSp, hSF⟩ := hB c hc
    refine mem_biUnion.mpr ⟨S, ?_, mem_filter.mpr ⟨hc, ?_⟩⟩
    · refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨fun T hT => ?_, hSk⟩, hSp.2⟩
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, (hSp.1 T hT).1⟩, hSF T hT⟩
    · intro e he
      obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
      exact (hSp.1 T hT).2 e heT
  have hone : ∀ S ∈ cand, (Bof S).card * q ^ (3 * k) ≤ q ^ Fintype.card (Sym2 V) := by
    intro S hS
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    obtain ⟨hS3, hSk⟩ := mem_powersetCard.mp hS1
    have hU : (S.biUnion triEdges).card = 3 * k := by
      rw [card_biUnion (fun T hT T' hT' hne => hS2 T hT T' hT' hne),
        sum_congr rfl (fun T hT =>
          card_triEdges (mem_powersetCard.mp (mem_filter.mp (hS3 hT)).1).2),
        sum_const, smul_eq_mul, hSk, mul_comm]
    rw [← hU]
    exact card_allRed_mul_le _ _ (fun c hc => (mem_filter.mp hc).2)
  have hcand : cand.card ≤ (F.card * Fintype.card V).choose k := by
    calc cand.card ≤ (powersetCard k TF).card := card_filter_le _ _
      _ = TF.card.choose k := card_powersetCard k TF
      _ ≤ (F.card * Fintype.card V).choose k :=
          Nat.choose_le_choose k (card_triangles_meeting_le F)
  calc B.card * q ^ (3 * k)
      ≤ (cand.biUnion Bof).card * q ^ (3 * k) := Nat.mul_le_mul_right _ (card_le_card hcover)
    _ ≤ (∑ S ∈ cand, (Bof S).card) * q ^ (3 * k) := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ S ∈ cand, (Bof S).card * q ^ (3 * k) := sum_mul _ _ _
    _ ≤ ∑ S ∈ cand, q ^ Fintype.card (Sym2 V) := sum_le_sum hone
    _ = cand.card * q ^ Fintype.card (Sym2 V) := by rw [sum_const, smul_eq_mul]
    _ ≤ (F.card * Fintype.card V).choose k * q ^ Fintype.card (Sym2 V) :=
        Nat.mul_le_mul_right _ hcand

end Triangles

section Main

open SimpleGraph

/-- `(1 - 1/(2q))^m ≤ 32^{-k}` when `m ≥ 10 q k`, in integers. -/
theorem numA (q k m : ℕ) (hq : 1 ≤ q) (h1 : 10 * q * k ≤ m) :
    32 ^ k * (2 * q - 1) ^ m ≤ (2 * q) ^ m := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have key : (32 : ℝ) ^ k * ((2 * q - 1 : ℕ) : ℝ) ^ m ≤ ((2 * q : ℕ) : ℝ) ^ m := by
    have hcast : ((2 * q - 1 : ℕ) : ℝ) = 2 * q - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    push_cast
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (2 * q) := ⟨_, rfl⟩
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hqx : (2 : ℝ) * q * x = 1 := by
      rw [hx]
      exact mul_one_div_cancel (mul_ne_zero two_ne_zero hq0)
    have hx1 : (2 : ℝ) * q - 1 = 2 * q * (1 - x) := by
      rw [mul_sub, mul_one, hqx]
    have hx2 : x ≤ 1 := by
      rw [hx, div_le_one (by positivity)]
      linarith
    have h2 : 1 - x ≤ Real.exp (-x) := by
      have h := Real.add_one_le_exp (-x)
      linarith
    have h4 : (1 - x) ^ m ≤ Real.exp (-x) ^ m := pow_le_pow_left₀ (by linarith) h2 m
    have h5 : Real.exp (-x) ^ m = Real.exp (-(m * x)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have h6 : (5 * k : ℝ) ≤ m * x := by
      have h7 : (10 * q * k : ℝ) ≤ m := by exact_mod_cast h1
      have h8 : m * x = m / (2 * q) := by rw [hx]; ring
      rw [h8, le_div_iff₀ (by positivity)]
      linarith
    have h7 : Real.exp (-(m * x)) ≤ Real.exp (-(5 * k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h8 : Real.exp (-(5 * k : ℝ)) = (Real.exp (-1)) ^ (5 * k) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf
    have h9 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      have h := Real.add_one_le_exp 1
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h10 : (Real.exp (-1)) ^ (5 * k) ≤ (1 / 2 : ℝ) ^ (5 * k) :=
      pow_le_pow_left₀ (Real.exp_pos _).le h9 _
    have h11 : (32 : ℝ) ^ k * (1 / 2 : ℝ) ^ (5 * k) = 1 := by
      rw [pow_mul, ← mul_pow]
      norm_num
    have h12 : (1 - x) ^ m ≤ (1 / 2 : ℝ) ^ (5 * k) := by
      calc (1 - x) ^ m ≤ Real.exp (-x) ^ m := h4
        _ = Real.exp (-(m * x)) := h5
        _ ≤ Real.exp (-(5 * k : ℝ)) := h7
        _ = (Real.exp (-1)) ^ (5 * k) := h8
        _ ≤ (1 / 2 : ℝ) ^ (5 * k) := h10
    calc (32 : ℝ) ^ k * (2 * q - 1) ^ m = (32 : ℝ) ^ k * (1 - x) ^ m * (2 * q) ^ m := by
          rw [hx1, mul_pow]
          ring
      _ ≤ (32 : ℝ) ^ k * (1 / 2 : ℝ) ^ (5 * k) * (2 * q) ^ m := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h12 (by positivity)
      _ = (2 * q) ^ m := by rw [h11, one_mul]
  exact_mod_cast key

/-- `k^k ≤ k! * 3^k`. -/
theorem pow_self_le_factorial_mul (k : ℕ) : k ^ k ≤ k.factorial * 3 ^ k := by
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
  have h3 : Real.exp (k : ℝ) ≤ 3 ^ k := by
    have h5 : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [h5]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  have hfact : (0 : ℝ) < k.factorial := by positivity
  have h4 : (k : ℝ) ^ k ≤ k.factorial * 3 ^ k := by
    rw [div_le_iff₀ hfact] at h
    calc (k : ℝ) ^ k ≤ Real.exp k * k.factorial := h
      _ ≤ 3 ^ k * k.factorial := mul_le_mul_of_nonneg_right h3 hfact.le
      _ = k.factorial * 3 ^ k := mul_comm _ _
  exact_mod_cast h4

/-- `4^k * C(a, k) ≤ q^{3k}` when `12 a ≤ k q³`. -/
theorem numB (a q k : ℕ) (h2 : 12 * a ≤ k * q ^ 3) : 4 ^ k * a.choose k ≤ q ^ (3 * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h1 : k.factorial * a.choose k ≤ a ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a k
  have h3 := pow_self_le_factorial_mul k
  have h4 : (4 ^ k * a.choose k) * k ^ k ≤ q ^ (3 * k) * k ^ k := by
    calc (4 ^ k * a.choose k) * k ^ k
        ≤ (4 ^ k * a.choose k) * (k.factorial * 3 ^ k) := Nat.mul_le_mul_left _ h3
      _ = 12 ^ k * (k.factorial * a.choose k) := by
          rw [show (12 : ℕ) = 4 * 3 by norm_num, mul_pow]
          ring
      _ ≤ 12 ^ k * a ^ k := Nat.mul_le_mul_left _ h1
      _ = (12 * a) ^ k := (mul_pow _ _ _).symm
      _ ≤ (k * q ^ 3) ^ k := Nat.pow_le_pow_left h2 k
      _ = q ^ (3 * k) * k ^ k := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

/-- **Sudakov's theorem for `K_3`, explicit form.** Let `G` be a graph on `n` vertices with `m`
edges. If `10 q k ≤ m`, `12 m N ≤ k q³` and `2 N^n < 4^k`, then there is a triangle-free graph on
`N` vertices such that every injection of `V(G)` sends some edge of `G` to one of its edges;
that is, its complement contains no copy of `G`, so `R(K_3, G) > N`. -/
theorem exists_triangleFree_hitting {n N q k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hq : 1 ≤ q) (h1 : 10 * q * k ≤ G.edgeFinset.card)
    (h2 : 12 * (G.edgeFinset.card * N) ≤ k * q ^ 3) (h3 : 2 * N ^ n < 4 ^ k) :
    ∃ C : SimpleGraph (Fin N), C.CliqueFree 3 ∧
      ∀ φ : Fin n → Fin N, Function.Injective φ → ∃ a b, G.Adj a b ∧ C.Adj (φ a) (φ b) := by
  classical
  have : NeZero q := ⟨by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, m = G.edgeFinset.card := ⟨_, rfl⟩
  rw [← hm] at h1 h2
  let F : (Fin n ↪ Fin N) → Finset (Sym2 (Fin N)) := fun φ => G.edgeFinset.map φ.sym2Map
  have hF : ∀ φ, (F φ).card = m := fun φ => by rw [hm]; exact card_map _
  let badA : (Fin n ↪ Fin N) → Finset (Sym2 (Fin N) → Fin q) := fun φ =>
    univ.filter fun c => FewRed c (F φ) (3 * k)
  let badB : (Fin n ↪ Fin N) → Finset (Sym2 (Fin N) → Fin q) := fun φ =>
    univ.filter fun c => ManyTri c (F φ) k
  obtain ⟨D, hD⟩ : ∃ D, D = Fintype.card (Sym2 (Fin N)) := ⟨_, rfl⟩
  have hA : ∀ φ, 4 ^ k * (badA φ).card ≤ q ^ D := by
    intro φ
    have h := card_fewRed_mul_le (F φ) (3 * k) (badA φ) (fun c hc => (mem_filter.mp hc).2)
    rw [hF, ← hD] at h
    have hnum := numA q k m hq h1
    have h5 : (4 ^ k * (badA φ).card) * (2 * q) ^ m ≤ q ^ D * (2 * q) ^ m := by
      have h32 : (32 : ℕ) ^ k = 4 ^ k * 2 ^ (3 * k) := by
        rw [pow_mul, ← mul_pow]
        norm_num
      calc (4 ^ k * (badA φ).card) * (2 * q) ^ m
          = 4 ^ k * ((badA φ).card * 2 ^ m * q ^ m) := by ring
        _ ≤ 4 ^ k * (2 ^ (3 * k) * (2 * q - 1) ^ m * q ^ D) := Nat.mul_le_mul_left _ h
        _ = (32 ^ k * (2 * q - 1) ^ m) * q ^ D := by
            rw [h32]
            ring
        _ ≤ (2 * q) ^ m * q ^ D := Nat.mul_le_mul_right _ hnum
        _ = q ^ D * (2 * q) ^ m := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h5 (by positivity)
  have hB : ∀ φ, 4 ^ k * (badB φ).card ≤ q ^ D := by
    intro φ
    have h := card_manyTri_mul_le (F φ) k (badB φ) (fun c hc => (mem_filter.mp hc).2)
    rw [hF, Fintype.card_fin, ← hD] at h
    have hnum := numB (m * N) q k h2
    have h5 : (4 ^ k * (badB φ).card) * q ^ (3 * k) ≤ q ^ D * q ^ (3 * k) := by
      calc (4 ^ k * (badB φ).card) * q ^ (3 * k)
          = 4 ^ k * ((badB φ).card * q ^ (3 * k)) := by ring
        _ ≤ 4 ^ k * ((m * N).choose k * q ^ D) := Nat.mul_le_mul_left _ h
        _ = (4 ^ k * (m * N).choose k) * q ^ D := by ring
        _ ≤ q ^ (3 * k) * q ^ D := Nat.mul_le_mul_right _ hnum
        _ = q ^ D * q ^ (3 * k) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h5 (by positivity)
  -- union bound over all embeddings
  let bad : Finset (Sym2 (Fin N) → Fin q) := univ.biUnion fun φ => badA φ ∪ badB φ
  have hbad : bad.card < (univ : Finset (Sym2 (Fin N) → Fin q)).card := by
    have hemb : Fintype.card (Fin n ↪ Fin N) ≤ N ^ n := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
      exact Nat.descFactorial_le_pow N n
    have h6 : 4 ^ k * bad.card ≤ (2 * N ^ n) * q ^ D := by
      calc 4 ^ k * bad.card
          ≤ 4 ^ k * ∑ φ : Fin n ↪ Fin N, (badA φ ∪ badB φ).card :=
            Nat.mul_le_mul_left _ card_biUnion_le
        _ ≤ 4 ^ k * ∑ φ : Fin n ↪ Fin N, ((badA φ).card + (badB φ).card) :=
            Nat.mul_le_mul_left _ (sum_le_sum fun φ _ => card_union_le _ _)
        _ = ∑ φ : Fin n ↪ Fin N, (4 ^ k * (badA φ).card + 4 ^ k * (badB φ).card) := by
            rw [mul_sum]
            exact sum_congr rfl fun φ _ => mul_add _ _ _
        _ ≤ ∑ φ : Fin n ↪ Fin N, (q ^ D + q ^ D) :=
            sum_le_sum fun φ _ => Nat.add_le_add (hA φ) (hB φ)
        _ = Fintype.card (Fin n ↪ Fin N) * (2 * q ^ D) := by
            rw [sum_const, card_univ, smul_eq_mul, two_mul]
        _ ≤ N ^ n * (2 * q ^ D) := Nat.mul_le_mul_right _ hemb
        _ = (2 * N ^ n) * q ^ D := by ring
    have hcardU : (univ : Finset (Sym2 (Fin N) → Fin q)).card = q ^ D := by
      rw [card_univ, Fintype.card_fun, Fintype.card_fin, hD]
    rw [hcardU]
    have hqD : 0 < q ^ D := by positivity
    have h7 : 4 ^ k * bad.card < 4 ^ k * q ^ D :=
      lt_of_le_of_lt h6 (mul_lt_mul_of_pos_right h3 hqD)
    exact Nat.lt_of_mul_lt_mul_left h7
  obtain ⟨c, -, hc⟩ := exists_mem_notMem_of_card_lt_card hbad
  obtain ⟨P, hP, hPmax⟩ := exists_max_packing c
  refine ⟨cleaned c P, cleaned_cliqueFree c P hPmax, fun φ hφ => ?_⟩
  let φ' : Fin n ↪ Fin N := ⟨φ, hφ⟩
  have hnotA : ¬ FewRed c (F φ') (3 * k) := fun h =>
    hc (mem_biUnion.mpr ⟨φ', mem_univ _, mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)⟩)
  have hnotB : ¬ ManyTri c (F φ') k := fun h =>
    hc (mem_biUnion.mpr ⟨φ', mem_univ _, mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)⟩)
  obtain ⟨e, heF, hred, heP⟩ := exists_red_edge c P hP (F φ') k hnotA hnotB
  obtain ⟨e₀, he₀, rfl⟩ := mem_map.mp heF
  revert he₀ hred heP
  refine Sym2.ind (fun u v => ?_) e₀
  intro he₀ hred heP
  rw [mem_edgeFinset, mem_edgeSet] at he₀
  have hmap : φ'.sym2Map s(u, v) = s(φ u, φ v) := rfl
  rw [hmap] at hred heP
  refine ⟨u, v, he₀, ?_⟩
  change φ u ≠ φ v ∧ c s(φ u, φ v) = 0 ∧ s(φ u, φ v) ∉ P.biUnion triEdges
  exact ⟨fun h => he₀.ne (hφ h), hred, heP⟩

/-- **Sudakov's upper bound for `f`.** `f(n) < 341 n^{3/2} log n` for all `n ≥ 2^10`.
Together with `f_lower` this determines `f(n)` up to a factor `O(√log n)`. -/
theorem f_upper_sudakov : ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    (f n : ℝ) < B * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n := by
  refine ⟨341, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 10)] with n hn
  classical
  have hnR : (2 : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hL5 : 5 ≤ Real.log n := by
    have h1 : Real.log ((2 : ℝ) ^ 10) ≤ Real.log n := Real.log_le_log (by positivity) hnR
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_gt_d9
    push_cast at h1
    linarith
  generalize hL : Real.log (n : ℝ) = L at hL5 ⊢
  obtain ⟨w, hw⟩ : ∃ w, w = Real.sqrt n := ⟨_, rfl⟩
  have hw2 : w ^ 2 = n := by rw [hw]; exact Real.sq_sqrt hnpos.le
  have hw32 : 32 ≤ w := by
    rw [hw]
    calc (32 : ℝ) = Real.sqrt ((32 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by norm_num at hnR ⊢; linarith)
  have hwpos : 0 < w := by linarith
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * w := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow, hw]
  have hnwL : 0 ≤ 340 * ((n : ℝ) * w) * L := by positivity
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, M₀ = ⌊340 * ((n : ℝ) * w) * L⌋₊ := ⟨_, rfl⟩
  have hM₀le : (M₀ : ℝ) ≤ 340 * ((n : ℝ) * w) * L := by rw [hM₀]; exact Nat.floor_le hnwL
  have hM₀lt : 340 * ((n : ℝ) * w) * L < M₀ + 1 := by rw [hM₀]; exact Nat.lt_floor_add_one _
  have hf : f n ≤ M₀ := by
    refine f_le_of_forall_exists hn1 fun G hG hGm => ?_
    have hmcard : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← Set.ncard_coe_finset, coe_edgeFinset]
    rw [hmcard] at hGm
    obtain ⟨m, hm⟩ : ∃ m, m = G.edgeFinset.card := ⟨_, rfl⟩
    rw [← hm] at hGm
    have hmR : 340 * ((n : ℝ) * w) * L < m := by
      have h1 : (M₀ : ℝ) + 1 ≤ m := by exact_mod_cast hGm
      linarith
    -- `q = r + 1` with `q² > 240 n + 120`
    obtain ⟨r, hr1, hr2⟩ : ∃ r : ℕ, r ^ 2 ≤ 240 * n + 120 ∧ 240 * n + 120 < (r + 1) ^ 2 :=
      ⟨Nat.sqrt (240 * n + 120), Nat.sqrt_le' _, Nat.lt_succ_sqrt' _⟩
    have hr1R : (r : ℝ) ^ 2 ≤ 240 * n + 120 := by exact_mod_cast hr1
    have hr2R : 240 * (n : ℝ) + 121 ≤ ((r : ℝ) + 1) ^ 2 := by
      have h1 : 240 * n + 121 ≤ (r + 1) ^ 2 := hr2
      exact_mod_cast h1
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hn1024 : (1024 : ℝ) ≤ n := le_trans (by norm_num) hnR
    have hrw : (r : ℝ) + 1 ≤ 17 * w := by
      have h1 : (r : ℝ) ≤ 16 * w := by
        by_contra hcon
        push Not at hcon
        have h2 : 0 < ((r : ℝ) - 16 * w) * ((r : ℝ) + 16 * w) :=
          mul_pos (by linarith) (by linarith)
        have h3 : ((r : ℝ) - 16 * w) * ((r : ℝ) + 16 * w) = (r : ℝ) ^ 2 - 256 * w ^ 2 := by
          ring
        rw [h3, hw2] at h2
        linarith
      linarith
    -- `k = ⌊m / (10 q)⌋`
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, 10 * (r + 1) * k ≤ m ∧ m < 10 * (r + 1) * (k + 1) :=
      ⟨m / (10 * (r + 1)), Nat.mul_div_le _ _, Nat.lt_mul_div_succ _ (by positivity)⟩
    have hk2R : (m : ℝ) < 10 * ((r : ℝ) + 1) * ((k : ℝ) + 1) := by exact_mod_cast hk2
    have hmpos : (0 : ℝ) ≤ m := by positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    -- `q³ ≤ 12 m`
    have hq3 : ((r : ℝ) + 1) ^ 3 ≤ 12 * m := by
      have h1 : ((r : ℝ) + 1) ^ 3 ≤ (17 * w) ^ 3 := pow_le_pow_left₀ (by positivity) hrw 3
      have h2 : (17 * w) ^ 3 = 4913 * (n * w) := by rw [← hw2]; ring
      have h3 : 0 < (n : ℝ) * w := by positivity
      have h4 : (n : ℝ) * w * 5 ≤ n * w * L := mul_le_mul_of_nonneg_left hL5 h3.le
      rw [h2] at h1
      linarith
    -- `2 n L - 1 < k`
    have hkL : 2 * (n : ℝ) * L - 1 < k := by
      have h1 : 340 * ((n : ℝ) * w) * L < 10 * (17 * w) * ((k : ℝ) + 1) := by
        calc 340 * ((n : ℝ) * w) * L < m := hmR
          _ < 10 * ((r : ℝ) + 1) * ((k : ℝ) + 1) := hk2R
          _ ≤ 10 * (17 * w) * ((k : ℝ) + 1) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith
      have h2 : 170 * w * (2 * (n : ℝ) * L) < 170 * w * ((k : ℝ) + 1) := by linarith
      have h3 := lt_of_mul_lt_mul_left h2 (by linarith : (0 : ℝ) ≤ 170 * w)
      linarith
    have h2 : 12 * (m * (2 * n - 1)) ≤ k * (r + 1) ^ 3 := by
      have h4 : (12 * ((m : ℝ) * (2 * n)) : ℝ) ≤ k * ((r : ℝ) + 1) ^ 3 := by
        have e1 : (m : ℝ) * ((r : ℝ) + 1) ^ 2
            < 10 * ((r : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) := by
          have hpos : (0 : ℝ) < ((r : ℝ) + 1) ^ 2 := by positivity
          have h5 := mul_lt_mul_of_pos_right hk2R hpos
          calc (m : ℝ) * ((r : ℝ) + 1) ^ 2
              < 10 * ((r : ℝ) + 1) * ((k : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 := h5
            _ = 10 * ((r : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) := by ring
        have e2 : (m : ℝ) * (240 * n + 121) ≤ m * ((r : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hr2R hmpos
        linarith
      have h5 : 12 * (m * (2 * n)) ≤ k * (r + 1) ^ 3 := by exact_mod_cast h4
      calc 12 * (m * (2 * n - 1)) ≤ 12 * (m * (2 * n)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
        _ ≤ k * (r + 1) ^ 3 := h5
    have h3 : 2 * (2 * n - 1) ^ n < 4 ^ k := by
      obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = ((2 * n - 1 : ℕ) : ℝ) := ⟨_, rfl⟩
      have hN1 : (1 : ℝ) ≤ Nr := by
        have h4 : 1 ≤ 2 * n - 1 := by omega
        rw [hNr]
        exact_mod_cast h4
      have hN2 : Nr ≤ 2 * n := by
        have h4 : 2 * n - 1 ≤ 2 * n := Nat.sub_le _ _
        rw [hNr]
        exact_mod_cast h4
      have hlogN : Real.log Nr ≤ 1 + L := by
        have h4 : Real.log Nr ≤ Real.log (2 * n) := Real.log_le_log (by linarith) hN2
        rw [Real.log_mul (by norm_num) hnpos.ne', hL] at h4
        have h5 := Real.log_two_lt_d9
        linarith
      have key : (2 : ℝ) * Nr ^ n < 4 ^ k := by
        have hNrpos : (0 : ℝ) < Nr := by linarith
        have hpos1 : (0 : ℝ) < 2 * Nr ^ n := by positivity
        have hpos2 : (0 : ℝ) < 4 ^ k := by positivity
        have hlog4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [← Real.log_lt_log_iff hpos1 hpos2, Real.log_mul (by norm_num) (by positivity),
          Real.log_pow, Real.log_pow, hlog4]
        have h5 := Real.log_two_gt_d9
        have h6 := Real.log_two_lt_d9
        have h7 : (n : ℝ) * Real.log Nr ≤ n * (1 + L) :=
          mul_le_mul_of_nonneg_left hlogN hnpos.le
        have h8 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have h9 : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
          mul_le_mul_of_nonneg_left h5.le hk0
        have h10 : (n : ℝ) * 5 ≤ n * L := mul_le_mul_of_nonneg_left hL5 hnpos.le
        linarith
      rw [hNr] at key
      exact_mod_cast key
    have hk1' : 10 * (r + 1) * k ≤ G.edgeFinset.card := by rw [← hm]; exact hk1
    have h2' : 12 * (G.edgeFinset.card * (2 * n - 1)) ≤ k * (r + 1) ^ 3 := by
      rw [← hm]; exact h2
    exact exists_triangleFree_hitting G (by omega) hk1' h2' h3
  calc (f n : ℝ) ≤ M₀ := by exact_mod_cast hf
    _ ≤ 340 * ((n : ℝ) * w) * L := hM₀le
    _ < 341 * (n : ℝ) ^ (3 / 2 : ℝ) * L := by
        rw [hpow]
        have h1 : 0 < (n : ℝ) * w * L := by positivity
        linarith

end Main

end E1182

end UpperPart

section SummaryPart

/-
# Erdős Problem 1182, part (i): what is proved here

This part contains the bounds that follow from the literature; the sharp upper bound, and with it
part (i), is proved in the later parts of the file (`erdos_1182_i` in `FinalPart`).

* `f_bounds`: `A n^{3/2} √(log n) < f(n) < B n^{3/2} log n` for all large `n`
  (lower bound: [BEFRS80, Theorem 2]; upper bound: Sudakov 2007, Theorem 1.1 with `s = 3`).
* `ramsey_ge`: the Chvátal–Harary bound `R(K_3, G) ≥ 2n - 1` for connected `G`
  (this is `erdos_1182.variants.ramsey_ge` of Formal Conjectures).
* `f_isTheta_of_sudakovConjecture`: **conditional** on Sudakov's conjecture
  `R(K_3, G) ≥ c m^{2/3} / (log m)^{1/3}`, one gets `f(n) = Θ(n^{3/2} √(log n))`.
* `not_ramsey3_of_f_lt` (in the lower-bound part): any upper bound for `f` gives a lower bound
  for the Ramsey numbers `R(3, k)`; the upper bound `f(n) ≪ n^{3/2} √(log n)` contains Kim's
  theorem `R(3,k) ≫ k² / log k` (`kim_of_f_upper`, `ramsey3_lower_kim`).
-/

open Filter Asymptotics

namespace E1182

/-- `x^{3/2} = x √x` for `x > 0`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `(x^{2/3})³ = x²` for `x ≥ 0`. -/
theorem rpow_two_thirds_pow {x : ℝ} (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  have h : (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, h, Real.rpow_natCast]

/-- `(x^{1/3})³ = x` for `x ≥ 0`. -/
theorem rpow_one_third_pow {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  have h : (1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 1 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, h, Real.rpow_one]

/-- The set defining `R(K_3, G)` is nonempty (Ramsey's theorem, here from the Shearer-type
bound with `N = 4 max(n,2)²`). -/
theorem ramseySet_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) : (RamseySet G).Nonempty := by
  obtain ⟨k, hk⟩ : ∃ k, k = max n 2 := ⟨_, rfl⟩
  have hk2 : 2 ≤ k := by rw [hk]; exact le_max_right _ _
  have hkn : n ≤ k := by rw [hk]; exact le_max_left _ _
  have hlog : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num) hk2
  have hR : Ramsey3 (4 * k ^ 2) k :=
    ramsey3_of_log (by omega) (Nat.le_mul_of_pos_right _ hlog)
  refine ⟨4 * k ^ 2, ?_⟩
  rw [mem_ramseySet_iff]
  intro C hC
  obtain ⟨I, hIk, hI⟩ := hR C hC
  have hcard : Fintype.card (Fin n) ≤ Fintype.card I := by
    rw [Fintype.card_fin, Fintype.card_coe, hIk]
    exact hkn
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun a => (g a : Fin (4 * k ^ 2)), fun a b h => g.injective (Subtype.ext h),
    fun a b _ => hI _ (g a).2 _ (g b).2⟩

/-- **Chvátal–Harary.** `R(K_3, G) ≥ 2n - 1` for every connected graph `G` on `n` vertices.
This is the statement `erdos_1182.variants.ramsey_ge` of Formal Conjectures. -/
theorem ramsey_ge {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    2 * n - 1 ≤ SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) G := by
  rw [graphRamsey_eq_sInf]
  by_contra hlt
  push Not at hlt
  have hmem : sInf (RamseySet G) ∈ RamseySet G := Nat.sInf_mem (ramseySet_nonempty G)
  exact two_mul_sub_two_notMem G hG (ramseySet_mono G (by omega) hmem)

/-- **The two proved bounds.** There are constants `A, B > 0` with
`A n^{3/2} (log n)^{1/2} < f(n) < B n^{3/2} log n` for all large `n`. -/
theorem f_bounds : ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    A * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) < (f n : ℝ) ∧
      (f n : ℝ) < B * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n := by
  obtain ⟨A, hA, hA'⟩ := f_lower
  obtain ⟨B, hB, hB'⟩ := f_upper_sudakov
  exact ⟨A, hA, B, hB, hA'.and hB'⟩

/-- `n^{3/2} (log n)^{1/2} = O(f(n))`. -/
theorem isBigO_f_lower :
    (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) =O[atTop]
      fun n : ℕ => (f n : ℝ) := by
  obtain ⟨A, hA, hA'⟩ := f_lower
  refine IsBigO.of_bound (1 / A) ?_
  filter_upwards [hA'] with n hn
  have h0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (Nat.cast_nonneg _), div_mul_eq_mul_div,
    one_mul, le_div_iff₀ hA]
  linarith

/-- `f(n) = O(n^{3/2} log n)`. -/
theorem isBigO_f_upper :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n := by
  obtain ⟨B, hB, hB'⟩ := f_upper_sudakov
  refine IsBigO.of_bound B ?_
  filter_upwards [hB', eventually_ge_atTop 1] with n hn hn1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.log_nonneg hn1R)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg h0]
  linarith

/-- **[BEFRS80, Theorem 2], upper bound**, in the form stated in Formal Conjectures
(`erdos_1182.variants.f_upper`): `f(n) < B n^{5/3} (log n)^{2/3}` for all large `n`.
It is weaker than `f_upper_sudakov` and is deduced from it. -/
theorem f_upper_befrs : ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (f n : ℝ) < B * (n : ℝ) ^ (5 / 3 : ℝ) * Real.log n ^ (2 / 3 : ℝ) := by
  obtain ⟨B, hB, hB'⟩ := f_upper_sudakov
  refine ⟨2 * B, by positivity, ?_⟩
  filter_upwards [hB', eventually_ge_atTop 3] with n hn hn3
  have hnR3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    have h1 : Real.exp 1 ≤ n := le_trans Real.exp_one_lt_three.le hnR3
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) h1
  have hL2' : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hnpos)
    rw [Real.log_sqrt hnpos.le] at h1
    rw [← Real.sqrt_eq_rpow]
    linarith
  generalize hL : Real.log (n : ℝ) = L at hn hlog1 hL2' ⊢
  have hLpos : 0 < L := by linarith
  have h16 : L ^ (1 / 3 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 6 : ℝ) := by
    calc L ^ (1 / 3 : ℝ) ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hLpos.le hL2' (by norm_num)
      _ = (2 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le _),
            ← Real.rpow_mul hnpos.le]
          norm_num
      _ ≤ 2 * (n : ℝ) ^ (1 / 6 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnpos.le _)
          calc (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hsplitL : L = L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hsplitn : (n : ℝ) ^ (5 / 3 : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have h32 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hnpos.le _
  have h23 : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLpos.le _
  calc (f n : ℝ) < B * (n : ℝ) ^ (3 / 2 : ℝ) * L := hn
    _ = B * (n : ℝ) ^ (3 / 2 : ℝ) * (L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ)) := by
        rw [← hsplitL]
    _ ≤ B * (n : ℝ) ^ (3 / 2 : ℝ) * (L ^ (2 / 3 : ℝ) * (2 * (n : ℝ) ^ (1 / 6 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h16 h23) (mul_nonneg hB.le h32)
    _ = 2 * B * (n : ℝ) ^ (5 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
        rw [hsplitn]
        ring

/-- **The exponent is settled:** `f(n) = n^{3/2 + o(1)}`, that is,
`log f(n) / log n → 3/2`. (In [BEFRS80] the exponent was only known to lie in `[3/2, 5/3]`.) -/
theorem tendsto_log_f_div_log :
    Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (nhds (3 / 2)) := by
  obtain ⟨A, hA, hA'⟩ := f_lower
  obtain ⟨B, hB, hB'⟩ := f_upper_sudakov
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hL
  have hlow : Tendsto (fun n : ℕ => 3 / 2 + Real.log A / Real.log n) atTop (nhds (3 / 2)) := by
    have h1 := (tendsto_const_nhds (x := Real.log A)).div_atTop hL
    have h2 := (tendsto_const_nhds (x := (3 / 2 : ℝ))).add h1
    simpa using h2
  have hup : Tendsto (fun n : ℕ =>
      3 / 2 + (Real.log B / Real.log n + Real.log (Real.log n) / Real.log n))
        atTop (nhds (3 / 2)) := by
    have h1 := (tendsto_const_nhds (x := Real.log B)).div_atTop hL
    have h2 := (tendsto_const_nhds (x := (3 / 2 : ℝ))).add (h1.add hloglog)
    simpa using h2
  have hfacts : ∀ n : ℕ, 3 ≤ n → (0 : ℝ) < n ∧ 1 ≤ Real.log n := by
    intro n hn3
    have hnR3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    refine ⟨by linarith, ?_⟩
    have h1 : Real.exp 1 ≤ n := le_trans Real.exp_one_lt_three.le hnR3
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) h1
  have hlowf : ∀ n : ℕ, 3 ≤ n →
      A * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) < (f n : ℝ) →
        A * (n : ℝ) ^ (3 / 2 : ℝ) ≤ (f n : ℝ) := by
    intro n hn3 hn
    obtain ⟨hnpos, hlog1⟩ := hfacts n hn3
    have hsqrtL : 1 ≤ Real.sqrt (Real.log n) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hlog1
    have hpos : 0 ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) :=
      mul_nonneg hA.le (Real.rpow_nonneg hnpos.le _)
    have h1 : A * (n : ℝ) ^ (3 / 2 : ℝ) * 1 ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
      mul_le_mul_of_nonneg_left hsqrtL hpos
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hA', eventually_ge_atTop 3] with n hn hn3
    obtain ⟨hnpos, hlog1⟩ := hfacts n hn3
    have hLpos : 0 < Real.log n := by linarith
    have hrpow : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have h1 : Real.log (A * (n : ℝ) ^ (3 / 2 : ℝ)) ≤ Real.log (f n) :=
      Real.log_le_log (mul_pos hA hrpow) (hlowf n hn3 hn)
    rw [Real.log_mul hA.ne' hrpow.ne', Real.log_rpow hnpos] at h1
    rw [le_div_iff₀ hLpos]
    have h2 : (3 / 2 + Real.log A / Real.log n) * Real.log n
        = 3 / 2 * Real.log n + Real.log A := by
      field_simp
    rw [h2]
    linarith
  · filter_upwards [hB', hA', eventually_ge_atTop 3] with n hn hnA hn3
    obtain ⟨hnpos, hlog1⟩ := hfacts n hn3
    have hLpos : 0 < Real.log n := by linarith
    have hrpow : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have hfpos : (0 : ℝ) < f n := lt_of_lt_of_le (mul_pos hA hrpow) (hlowf n hn3 hnA)
    have h1 : Real.log (f n) ≤ Real.log (B * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n) :=
      Real.log_le_log hfpos hn.le
    rw [Real.log_mul (mul_pos hB hrpow).ne' hLpos.ne', Real.log_mul hB.ne' hrpow.ne',
      Real.log_rpow hnpos] at h1
    rw [div_le_iff₀ hLpos]
    have h2 : (3 / 2 + (Real.log B / Real.log n + Real.log (Real.log n) / Real.log n))
        * Real.log n = 3 / 2 * Real.log n + Real.log B + Real.log (Real.log n) := by
      field_simp
      ring
    rw [h2]
    linarith

/-- **Sudakov's conjecture** (Sudakov 2007, concluding remarks): there is `c > 0` such that every
graph `G` with `m` edges, `m` large, satisfies `R(K_3, G) ≥ c m^{2/3} / (log m)^{1/3}`.
A proof is claimed in the unrefereed preprint Zenodo 10.5281/zenodo.22697303 (2026); it is
**not** proved in this development. -/
def SudakovConjecture : Prop :=
  ∃ c > (0 : ℝ), ∃ m₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), m₀ ≤ G.edgeSet.ncard →
    c * (G.edgeSet.ncard : ℝ) ^ (2 / 3 : ℝ) / (Real.log G.edgeSet.ncard) ^ (1 / 3 : ℝ)
      ≤ (SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) G : ℝ)

/-- Under Sudakov's conjecture, `f(n) = O(n^{3/2} (log n)^{1/2})`. -/
theorem isBigO_f_of_sudakovConjecture (h : SudakovConjecture) :
    (fun n : ℕ => (f n : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by
  obtain ⟨c, hc, m₀, hconj⟩ := h
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 / c ^ 2 + 4 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hK2 : 16 ≤ K ^ 2 * c ^ 3 := by
    have h1 : K * c ^ 2 = 4 + 4 * c ^ 2 := by
      rw [hK]
      field_simp
    have h2 : K ^ 2 * c ^ 4 = (4 + 4 * c ^ 2) ^ 2 := by
      rw [← h1]
      ring
    have h3 : 16 * c ≤ K ^ 2 * c ^ 4 := by
      rw [h2]
      nlinarith [sq_nonneg (c - 1), sq_nonneg (c ^ 2 - 1), sq_nonneg c]
    have h4 : K ^ 2 * c ^ 4 = (K ^ 2 * c ^ 3) * c := by ring
    rw [h4] at h3
    exact le_of_mul_le_mul_right h3 hc
  refine IsBigO.of_bound (K + 1) ?_
  filter_upwards [eventually_ge_atTop (m₀ + 3)] with n hn
  have hn3 : 3 ≤ n := by omega
  have hnR3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    have h1 : Real.exp 1 ≤ n := le_trans Real.exp_one_lt_three.le hnR3
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) h1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := ⟨_, rfl⟩
  have hsqrtn : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrtL : 1 ≤ Real.sqrt (Real.log n) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hlog1
  have hXn : (n : ℝ) ≤ X := by
    rw [hX, rpow_three_halves hnpos]
    have h1 : (n : ℝ) * 1 ≤ n * Real.sqrt n := mul_le_mul_of_nonneg_left hsqrtn hnpos.le
    have h2 : (n : ℝ) * Real.sqrt n * 1 ≤ n * Real.sqrt n * Real.sqrt (Real.log n) :=
      mul_le_mul_of_nonneg_left hsqrtL (by positivity)
    linarith
  have hX0 : 0 ≤ X := by linarith
  have hX2 : X ^ 2 = (n : ℝ) ^ 3 * Real.log n := by
    rw [hX, rpow_three_halves hnpos, mul_pow, mul_pow, Real.sq_sqrt hnpos.le,
      Real.sq_sqrt (by linarith)]
    ring
  -- every connected good graph has at most `m₀ + 2 + K X` edges
  have hedges : ∀ G : SimpleGraph (Fin n), G.Connected → IsTriangleGood G →
      (G.edgeSet.ncard : ℝ) ≤ m₀ + 2 + K * X := by
    intro G hG hgood
    obtain ⟨m, hm⟩ : ∃ m, m = G.edgeSet.ncard := ⟨_, rfl⟩
    rw [← hm]
    rcases Nat.lt_or_ge m (m₀ + 2) with hsmall | hbig
    · have h1 : (m : ℝ) ≤ m₀ + 2 := by exact_mod_cast hsmall.le
      have h2 : 0 ≤ K * X := mul_nonneg hK0.le hX0
      linarith
    · have hm2 : (2 : ℝ) ≤ m := by
        have h1 : 2 ≤ m := by omega
        exact_mod_cast h1
      have hmpos : (0 : ℝ) < m := by linarith
      have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
      have hconj' := hconj n G (by omega)
      rw [← hm] at hconj'
      unfold IsTriangleGood at hgood
      rw [hgood] at hconj'
      -- `c m^{2/3} ≤ 2n (log m)^{1/3}`
      have hb : 0 < (Real.log m) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hlogm _
      have ha : 0 ≤ (m : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hmpos.le _
      have hR : ((2 * n - 1 : ℕ) : ℝ) ≤ 2 * n := by
        have h1 : 2 * n - 1 ≤ 2 * n := Nat.sub_le _ _
        exact_mod_cast h1
      have h1 : c * (m : ℝ) ^ (2 / 3 : ℝ) ≤ 2 * n * (Real.log m) ^ (1 / 3 : ℝ) := by
        rw [div_le_iff₀ hb] at hconj'
        calc c * (m : ℝ) ^ (2 / 3 : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) * (Real.log m) ^ (1 / 3 : ℝ) :=
              hconj'
          _ ≤ 2 * n * (Real.log m) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right hR hb.le
      -- cube it: `c³ m² ≤ 8 n³ log m`
      have h2 : c ^ 3 * (m : ℝ) ^ 2 ≤ 8 * (n : ℝ) ^ 3 * Real.log m := by
        have h3 := pow_le_pow_left₀ (mul_nonneg hc.le ha) h1 3
        rw [mul_pow, rpow_two_thirds_pow hmpos.le, mul_pow, rpow_one_third_pow hlogm.le] at h3
        calc c ^ 3 * (m : ℝ) ^ 2 ≤ (2 * (n : ℝ)) ^ 3 * Real.log m := h3
          _ = 8 * (n : ℝ) ^ 3 * Real.log m := by ring
      -- `log m ≤ 2 log n`
      have hmle : (m : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h3 : m ≤ n.choose 2 := hm ▸ ncard_edgeSet_le G
        have h4 : n.choose 2 ≤ n ^ 2 := by
          rw [Nat.choose_two_right]
          calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
            _ ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            _ = n ^ 2 := (sq n).symm
        exact_mod_cast h3.trans h4
      have hlogle : Real.log m ≤ 2 * Real.log n := by
        calc Real.log m ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hmpos hmle
          _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
      -- `m² ≤ (K X)²`
      have h4 : c ^ 3 * (m : ℝ) ^ 2 ≤ c ^ 3 * (K * X) ^ 2 := by
        have h5 : 8 * (n : ℝ) ^ 3 * Real.log m ≤ 16 * ((n : ℝ) ^ 3 * Real.log n) := by
          have h6 : (0 : ℝ) ≤ 8 * (n : ℝ) ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hlogle h6]
        have h7 : 16 * ((n : ℝ) ^ 3 * Real.log n) ≤ (K ^ 2 * c ^ 3) * ((n : ℝ) ^ 3 * Real.log n) :=
          mul_le_mul_of_nonneg_right hK2 (by rw [← hX2]; positivity)
        calc c ^ 3 * (m : ℝ) ^ 2 ≤ 8 * (n : ℝ) ^ 3 * Real.log m := h2
          _ ≤ 16 * ((n : ℝ) ^ 3 * Real.log n) := h5
          _ ≤ (K ^ 2 * c ^ 3) * ((n : ℝ) ^ 3 * Real.log n) := h7
          _ = c ^ 3 * (K * X) ^ 2 := by rw [mul_pow, hX2]; ring
      have h5 : (m : ℝ) ^ 2 ≤ (K * X) ^ 2 := le_of_mul_le_mul_left h4 (by positivity)
      have h6 : (m : ℝ) ≤ K * X :=
        (pow_le_pow_iff_left₀ hmpos.le (mul_nonneg hK0.le hX0) (by norm_num)).mp h5
      have h7 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
      linarith
  have hf : (f n : ℝ) ≤ m₀ + 2 + K * X := by
    have hnat : f n ≤ ⌊(m₀ : ℝ) + 2 + K * X⌋₊ := by
      refine f_le_of_forall fun G hG hgood => ?_
      exact Nat.le_floor (hedges G hG hgood)
    have h0 : (0 : ℝ) ≤ (m₀ : ℝ) + 2 + K * X := by
      have h1 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
      have h2 : 0 ≤ K * X := mul_nonneg hK0.le hX0
      linarith
    calc (f n : ℝ) ≤ (⌊(m₀ : ℝ) + 2 + K * X⌋₊ : ℝ) := by exact_mod_cast hnat
      _ ≤ (m₀ : ℝ) + 2 + K * X := Nat.floor_le h0
  have hm₀X : (m₀ : ℝ) + 2 ≤ X := by
    have h1 : (m₀ : ℝ) + 3 ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), ← hX, Real.norm_of_nonneg hX0]
  linarith

/-- **Conditional answer to part (i).** If Sudakov's conjecture holds, then
`f(n) = Θ(n^{3/2} (log n)^{1/2})`. The hypothesis is *not* proved in this file; the unconditional
statement is `erdos_1182_i`. -/
theorem f_isTheta_of_sudakovConjecture (h : SudakovConjecture) :
    (fun n : ℕ => (f n : ℝ)) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
  ⟨isBigO_f_of_sudakovConjecture h, isBigO_f_lower⟩

/-- `Ramsey3 N k` is monotone in `N`. -/
theorem Ramsey3.mono {N N' k : ℕ} (hR : Ramsey3 N k) (h : N ≤ N') : Ramsey3 N' k := by
  classical
  intro C hC
  obtain ⟨I, -, hIk, hI⟩ := hR.exists_subset C hC Finset.univ (by simpa using h)
  exact ⟨I, hIk, hI⟩

/-- **The sharp upper bound contains Kim's theorem.** If `f(n) ≤ B n^{3/2} (log n)^{1/2}` for
all large `n`, then `R(3, k) > c k² / log k` for all large `k`: there is a triangle-free graph on
`⌈c k² / log k⌉` vertices with no independent set of size `k`. (So any proof of the upper bound
for `f` must reprove Kim's theorem; with the upper bound proved below this gives
`ramsey3_lower_kim`.) -/
theorem kim_of_f_upper
    (h : ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) ≤ B * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop, ¬ Ramsey3 ⌈c * (k : ℝ) ^ 2 / Real.log k⌉₊ k := by
  obtain ⟨B₀, hB₀, hf₀⟩ := h
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max B₀ 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by rw [hB]; exact le_max_right _ _
  have hBB₀ : B₀ ≤ B := by rw [hB]; exact le_max_left _ _
  have hBpos : 0 < B := by linarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hf₀
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 128 * B ^ 2 := ⟨_, rfl⟩
  have hD128 : 128 ≤ D := by rw [hD]; nlinarith
  have hDpos : 0 < D := by linarith
  have hn0R : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨1 / (8 * D), by positivity, ?_⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (D * (10 + n₀)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hlogsmall : ∀ᶠ k : ℕ in atTop, Real.log (k : ℝ) ≤ ε * k := by
    have h1 := Real.isLittleO_log_id_atTop.def hεpos
    have h2 := tendsto_natCast_atTop_atTop.eventually h1
    filter_upwards [h2] with k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg hk0] at hk
    exact le_trans (le_abs_self _) hk
  filter_upwards [hlogsmall, eventually_ge_atTop 4] with k hksmall hk4
  have hk4R : (4 : ℝ) ≤ k := by exact_mod_cast hk4
  have hkpos : (0 : ℝ) < k := by linarith
  have hL1 : 1 ≤ Real.log k := by
    have h1 : Real.exp 1 ≤ k := le_trans Real.exp_one_lt_three.le (by linarith)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log k := Real.log_le_log (Real.exp_pos 1) h1
  generalize hL : Real.log (k : ℝ) = L at hksmall hL1 ⊢
  have hLpos : 0 < L := by linarith
  have hDL : 0 < D * L := mul_pos hDpos hLpos
  have hDL1 : 1 ≤ D * L := by nlinarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (k : ℝ) ^ 2 / (D * L) := ⟨_, rfl⟩
  have hu_ge : (k : ℝ) * (10 + n₀) ≤ u := by
    rw [hu, le_div_iff₀ hDL]
    have h2 : D * (10 + (n₀ : ℝ)) * (ε * k) = k := by
      rw [hε]
      field_simp
    have h3 : D * (10 + (n₀ : ℝ)) * L ≤ D * (10 + (n₀ : ℝ)) * (ε * k) :=
      mul_le_mul_of_nonneg_left hksmall (by positivity)
    have h4 : D * (10 + (n₀ : ℝ)) * L ≤ k := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hkpos.le
    nlinarith
  have hu_le : u ≤ (k : ℝ) ^ 2 := by
    rw [hu]
    exact div_le_self (by positivity) hDL1
  have hupos : 0 ≤ u := by rw [hu]; positivity
  have hu40 : (40 : ℝ) ≤ u := by
    have h1 : (0 : ℝ) ≤ k * n₀ := mul_nonneg hkpos.le hn0R
    nlinarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊u⌋₊ := ⟨_, rfl⟩
  have hn_le : (n : ℝ) ≤ u := by rw [hn]; exact Nat.floor_le hupos
  have hn_gt : u < n + 1 := by rw [hn]; exact Nat.lt_floor_add_one u
  have hn_big : (8 * k + 4 : ℝ) + n₀ ≤ n := by
    have h1 : (0 : ℝ) ≤ ((k : ℝ) - 1) * n₀ := mul_nonneg (by linarith) hn0R
    nlinarith
  have hnn₀ : n₀ ≤ n := by
    have h1 : (n₀ : ℝ) ≤ n := by linarith
    exact_mod_cast h1
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  -- `f(n) ≤ n k / 8`
  have hfn : (f n : ℝ) ≤ n * k / 8 := by
    have h1 := hn₀ n hnn₀
    have hlogn : Real.log n ≤ 2 * L := by
      have h2 : (n : ℝ) ≤ (k : ℝ) ^ 2 := le_trans hn_le hu_le
      calc Real.log n ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log hnpos h2
        _ = 2 * L := by rw [Real.log_pow, hL]; norm_num
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hB0 : B ≠ 0 := ne_of_gt hBpos
    have hL0 : L ≠ 0 := ne_of_gt hLpos
    have hsq : Real.sqrt n * Real.sqrt (Real.log n) ≤ k / (8 * B) := by
      rw [← Real.sqrt_mul hnpos.le, Real.sqrt_le_left (by positivity)]
      have h3 : (n : ℝ) * Real.log n ≤ u * (2 * L) := mul_le_mul hn_le hlogn hlogn0 hupos
      have h4 : u * (2 * L) = (k / (8 * B)) ^ 2 := by
        rw [hu, hD]
        field_simp
        try ring
      linarith
    have hrp : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := rpow_three_halves hnpos
    have hnn : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hnpos.le _
    calc (f n : ℝ) ≤ B₀ * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := h1
      _ ≤ B * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBB₀ hnn) (Real.sqrt_nonneg _)
      _ = B * n * (Real.sqrt n * Real.sqrt (Real.log n)) := by rw [hrp]; ring
      _ ≤ B * n * (k / (8 * B)) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = n * k / 8 := by
          field_simp
  -- the number of cliques
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, 2 * k * t ≤ n - 1 ∧ n - 1 < 2 * k * (t + 1) :=
    ⟨(n - 1) / (2 * k), Nat.mul_div_le _ _, Nat.lt_mul_div_succ _ (by omega)⟩
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  have h2kt : 2 * k * t = 2 * (t * k) := by ring
  have hsum : t * k + (n - 1 - t * k) + 1 = n := by omega
  have hkey : 2 * f (t * k + (n - 1 - t * k) + 1) < t * (k * (k - 1)) := by
    rw [hsum]
    have ht2R : (n : ℝ) - 1 < 2 * k * ((t : ℝ) + 1) := by
      have h1 : n < 2 * k * (t + 1) + 1 := by omega
      have h2 : (n : ℝ) < 2 * k * ((t : ℝ) + 1) + 1 := by exact_mod_cast h1
      linarith
    have hR : 2 * (f n : ℝ) < (t : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) := by
      have p1 : 0 < ((k : ℝ) - 1) * (2 * k * ((t : ℝ) + 1) - ((n : ℝ) - 1)) :=
        mul_pos (by linarith) (by linarith)
      have p2 : 0 ≤ ((n : ℝ) - (8 * k + 4)) * ((k : ℝ) - 2) :=
        mul_nonneg (by linarith) (by linarith)
      have p3 : 0 ≤ (k : ℝ) * ((k : ℝ) - 4) := mul_nonneg hkpos.le (by linarith)
      nlinarith
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have hR' : 2 * (f n : ℝ) < (t : ℝ) * ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
      rw [hcast]
      exact hR
    exact_mod_cast hR'
  have hnot := not_ramsey3_of_f_lt t k (n - 1 - t * k) hkey
  intro hR
  apply hnot
  refine hR.mono ?_
  rw [Nat.ceil_le]
  have hs : ((n : ℝ) - 1) / 2 ≤ ((n - 1 - t * k : ℕ) : ℝ) := by
    have h1 : n ≤ 2 * (n - 1 - t * k) + 1 := by omega
    have h2 : (n : ℝ) ≤ 2 * ((n - 1 - t * k : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hcu : 1 / (8 * D) * (k : ℝ) ^ 2 / L = u / 8 := by
    rw [hu]
    field_simp
  rw [hcu]
  linarith

end E1182


/- ## Comparison with the statements in Formal Conjectures

`statement_of% c` is the statement (type) of the constant `c`; only the statement is read, the
placeholder proof of the Formal Conjectures stub is not used. The three examples below check that the
theorems proved here have *exactly* the types of the corresponding Formal Conjectures variants. -/


end SummaryPart

section ProcPart

/-
# The triangle-free process: states, open pairs, the mass recursion, the master lemma

Histories are lists of pairs (newest first); the state is the set of chosen pairs.
`massFrom r F s` is the expected value of `F` after `r` further uniformly random open choices.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

/-- The pair `uv` is open in the state `J`: distinct, not chosen, no common neighbour. -/
def Op (J : Finset (Sym2 (Fin N))) (u v : Fin N) : Prop :=
  u ≠ v ∧ s(u, v) ∉ J ∧ ∀ w, ¬ (s(u, w) ∈ J ∧ s(v, w) ∈ J)

theorem Op.symm {J : Finset (Sym2 (Fin N))} {u v : Fin N} (h : Op J u v) : Op J v u :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2.1, fun w hw => h.2.2 w ⟨hw.2, hw.1⟩⟩

theorem op_comm {J : Finset (Sym2 (Fin N))} {u v : Fin N} : Op J u v ↔ Op J v u :=
  ⟨Op.symm, Op.symm⟩

open Classical in
/-- The set of open pairs. -/
noncomputable def openSet (J : Finset (Sym2 (Fin N))) : Finset (Sym2 (Fin N)) :=
  univ.filter fun e => ∃ u v, e = s(u, v) ∧ Op J u v

theorem mk_mem_openSet {J : Finset (Sym2 (Fin N))} {u v : Fin N} :
    s(u, v) ∈ openSet J ↔ Op J u v := by
  classical
  simp only [openSet, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u', v', heq, hop⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hop
    · exact hop.symm
  · intro h
    exact ⟨u, v, rfl, h⟩

theorem exists_of_mem_openSet {J : Finset (Sym2 (Fin N))} {e : Sym2 (Fin N)}
    (he : e ∈ openSet J) : ∃ u v, e = s(u, v) ∧ Op J u v := by
  classical
  simpa [openSet] using he

/-- Expected value of `F` after `r` more steps of the process, started from the history `s`. -/
noncomputable def massFrom :
    ℕ → (List (Sym2 (Fin N)) → ℝ) → List (Sym2 (Fin N)) → ℝ
  | 0, F, s => F s
  | r + 1, F, s =>
    (∑ e ∈ openSet s.toFinset, massFrom r F (e :: s)) / (openSet s.toFinset).card

theorem massFrom_zero (F : List (Sym2 (Fin N)) → ℝ) (s : List (Sym2 (Fin N))) :
    massFrom 0 F s = F s := rfl

theorem massFrom_succ (r : ℕ) (F : List (Sym2 (Fin N)) → ℝ) (s : List (Sym2 (Fin N))) :
    massFrom (r + 1) F s =
      (∑ e ∈ openSet s.toFinset, massFrom r F (e :: s)) / (openSet s.toFinset).card := rfl

theorem massFrom_nonneg {F : List (Sym2 (Fin N)) → ℝ} (hF : ∀ t, 0 ≤ F t) :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))), 0 ≤ massFrom r F s := by
  intro r
  induction r with
  | zero => intro s; exact hF s
  | succ r ih =>
    intro s
    rw [massFrom_succ]
    exact div_nonneg (sum_nonneg fun e _ => ih (e :: s)) (Nat.cast_nonneg _)

theorem massFrom_mono {F F' : List (Sym2 (Fin N)) → ℝ} (h : ∀ t, F t ≤ F' t) :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))), massFrom r F s ≤ massFrom r F' s := by
  intro r
  induction r with
  | zero => intro s; exact h s
  | succ r ih =>
    intro s
    rw [massFrom_succ, massFrom_succ]
    exact div_le_div_of_nonneg_right (sum_le_sum fun e _ => ih (e :: s)) (Nat.cast_nonneg _)

theorem massFrom_sub (F F' : List (Sym2 (Fin N)) → ℝ) :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))),
      massFrom r (fun t => F t - F' t) s = massFrom r F s - massFrom r F' s := by
  intro r
  induction r with
  | zero => intro s; rfl
  | succ r ih =>
    intro s
    rw [massFrom_succ, massFrom_succ, massFrom_succ, ← sub_div, ← sum_sub_distrib]
    congr 1
    exact sum_congr rfl fun e _ => ih (e :: s)

theorem massFrom_sum {ι : Type*} (T : Finset ι) (F : ι → List (Sym2 (Fin N)) → ℝ) :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))),
      massFrom r (fun t => ∑ c ∈ T, F c t) s = ∑ c ∈ T, massFrom r (F c) s := by
  intro r
  induction r with
  | zero => intro s; rfl
  | succ r ih =>
    intro s
    simp only [massFrom_succ]
    rw [← sum_div, sum_comm]
    congr 1
    exact sum_congr rfl fun e _ => ih (e :: s)

/-- If the mass of a nonnegative `F` is positive, some history of the right length has
`F > 0`. -/
theorem exists_of_massFrom_pos {F : List (Sym2 (Fin N)) → ℝ} :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))), 0 < massFrom r F s →
      ∃ t, t.length = s.length + r ∧ 0 < F t := by
  intro r
  induction r with
  | zero => intro s h; exact ⟨s, rfl, h⟩
  | succ r ih =>
    intro s h
    rw [massFrom_succ] at h
    have hsum : 0 < ∑ e ∈ openSet s.toFinset, massFrom r F (e :: s) := by
      by_contra hcon
      push Not at hcon
      exact absurd h (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hcon (Nat.cast_nonneg _)))
    obtain ⟨e, -, he⟩ := exists_lt_of_sum_lt (s := openSet s.toFinset)
      (f := fun _ => (0 : ℝ)) (g := fun e => massFrom r F (e :: s)) (by simpa using hsum)
    obtain ⟨t, ht, hFt⟩ := ih (e :: s) he
    exact ⟨t, by rw [ht, List.length_cons]; omega, hFt⟩

open Classical in
/-- Indicator of a proposition, as a real number. -/
noncomputable def ind (P : Prop) : ℝ := if P then 1 else 0

theorem ind_of {P : Prop} (h : P) : ind P = 1 := by
  classical
  simp [ind, h]

theorem ind_of_not {P : Prop} (h : ¬ P) : ind P = 0 := by
  classical
  simp [ind, h]

theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  by_cases h : P
  · rw [ind_of h]; norm_num
  · rw [ind_of_not h]

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_of h]
  · rw [ind_of_not h]; norm_num

/-- All earlier histories (suffixes) satisfy `G`. -/
def GoodAll (G : List (Sym2 (Fin N)) → Prop) (s : List (Sym2 (Fin N))) : Prop :=
  ∀ t, t <:+ s → G t

theorem goodAll_cons {G : List (Sym2 (Fin N)) → Prop} {e : Sym2 (Fin N)}
    {s : List (Sym2 (Fin N))} : GoodAll G (e :: s) ↔ G (e :: s) ∧ GoodAll G s := by
  constructor
  · intro h
    exact ⟨h _ List.suffix_rfl, fun t ht => h t (ht.trans (List.suffix_cons e s))⟩
  · rintro ⟨h1, h2⟩ t ht
    rcases List.suffix_cons_iff.mp ht with rfl | ht
    · exact h1
    · exact h2 t ht

theorem GoodAll.self {G : List (Sym2 (Fin N)) → Prop} {s : List (Sym2 (Fin N))}
    (h : GoodAll G s) : G s := h s List.suffix_rfl

/-- **Master lemma (first-failure union bound).** Let `Ψ c` be nonnegative functions that are
supermartingales along good histories and that are at least `Λ c` whenever the cause `c` makes a
history bad for the first time. Then the mass of histories that stay good for `I` steps is at
least `1 - ∑ c, Ψ c s / Λ c`. -/
theorem massFrom_goodAll_ge {ι : Type*} [Fintype ι] (G : List (Sym2 (Fin N)) → Prop) (I : ℕ)
    (Ψ : ι → List (Sym2 (Fin N)) → ℝ) (Λ : ι → ℝ)
    (hΨ0 : ∀ c s, 0 ≤ Ψ c s) (hΛ : ∀ c, 0 < Λ c)
    (hQ : ∀ s, GoodAll G s → s.length < I → (openSet s.toFinset).Nonempty)
    (hsuper : ∀ c s, GoodAll G s → s.length < I →
      ∑ e ∈ openSet s.toFinset, Ψ c (e :: s) ≤ (openSet s.toFinset).card * Ψ c s)
    (hbad : ∀ s e, GoodAll G s → s.length < I → e ∈ openSet s.toFinset → ¬ G (e :: s) →
      ∃ c, Λ c ≤ Ψ c (e :: s)) :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))), GoodAll G s → s.length + r = I →
      1 - ∑ c, Ψ c s / Λ c ≤ massFrom r (fun t => ind (GoodAll G t)) s := by
  have hF0 : ∀ t : List (Sym2 (Fin N)), (0 : ℝ) ≤ ind (GoodAll G t) := fun t => ind_nonneg _
  have hterm : ∀ c s, 0 ≤ Ψ c s / Λ c := fun c s => div_nonneg (hΨ0 c s) (hΛ c).le
  intro r
  induction r with
  | zero =>
    intro s hs _
    rw [massFrom_zero, ind_of hs]
    have h0 : 0 ≤ ∑ c, Ψ c s / Λ c := sum_nonneg fun c _ => hterm c s
    linarith
  | succ r ih =>
    intro s hs hlen
    have hlt : s.length < I := by omega
    have hne := hQ s hs hlt
    have hQpos : (0 : ℝ) < (openSet s.toFinset).card := by exact_mod_cast card_pos.mpr hne
    have hstep : ∀ e ∈ openSet s.toFinset,
        1 - ∑ c, Ψ c (e :: s) / Λ c
          ≤ massFrom r (fun t => ind (GoodAll G t)) (e :: s) := by
      intro e he
      by_cases hG : G (e :: s)
      · exact ih (e :: s) (goodAll_cons.mpr ⟨hG, hs⟩) (by rw [List.length_cons]; omega)
      · obtain ⟨c₀, hc₀⟩ := hbad s e hs hlt he hG
        have h1 : 1 ≤ Ψ c₀ (e :: s) / Λ c₀ := by
          rw [le_div_iff₀ (hΛ c₀), one_mul]
          exact hc₀
        have h2 : Ψ c₀ (e :: s) / Λ c₀ ≤ ∑ c, Ψ c (e :: s) / Λ c :=
          single_le_sum (f := fun c => Ψ c (e :: s) / Λ c) (fun c _ => hterm c (e :: s))
            (mem_univ c₀)
        have h3 := massFrom_nonneg hF0 r (e :: s)
        linarith
    rw [massFrom_succ, le_div_iff₀ hQpos]
    calc (1 - ∑ c, Ψ c s / Λ c) * (openSet s.toFinset).card
        = (openSet s.toFinset).card - ∑ c, ((openSet s.toFinset).card * Ψ c s) / Λ c := by
          rw [sub_mul, one_mul, sum_mul]
          refine congrArg _ (sum_congr rfl fun c _ => ?_)
          ring
      _ ≤ (openSet s.toFinset).card - ∑ c, (∑ e ∈ openSet s.toFinset, Ψ c (e :: s)) / Λ c := by
          apply sub_le_sub_left
          exact sum_le_sum fun c _ =>
            div_le_div_of_nonneg_right (hsuper c s hs hlt) (hΛ c).le
      _ = ∑ e ∈ openSet s.toFinset, (1 - ∑ c, Ψ c (e :: s) / Λ c) := by
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_comm]
          refine congrArg _ (sum_congr rfl fun c _ => ?_)
          exact sum_div _ _ _
      _ ≤ ∑ e ∈ openSet s.toFinset,
            massFrom r (fun t => ind (GoodAll G t)) (e :: s) := sum_le_sum hstep

end TFP
end E1182

end ProcPart

section StepPart

/-
# One step of the triangle-free process: exact counting identities

`J` is the set of chosen pairs, `e = s(a, b)` an open pair, `insert e J` the next state.
For a pair `uv`: `Xset J u v` are the vertices `w` with `uw`, `vw` both open; `Yset J u v` the
vertices `w` with one of `uw`, `vw` chosen and the other open (the "closing partners" of `uv`).
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

open Classical in
/-- Neighbours of `u`. -/
noncomputable def nb (J : Finset (Sym2 (Fin N))) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun w => s(u, w) ∈ J

open Classical in
/-- Common neighbours of `u` and `v`. -/
noncomputable def cod (J : Finset (Sym2 (Fin N))) (u v : Fin N) : Finset (Fin N) :=
  univ.filter fun w => s(u, w) ∈ J ∧ s(v, w) ∈ J

open Classical in
/-- Vertices `w` with `uw` and `vw` both open. -/
noncomputable def Xset (J : Finset (Sym2 (Fin N))) (u v : Fin N) : Finset (Fin N) :=
  univ.filter fun w => Op J u w ∧ Op J v w

open Classical in
/-- Vertices `w` with one of `uw`, `vw` chosen and the other open. -/
noncomputable def Yset (J : Finset (Sym2 (Fin N))) (u v : Fin N) : Finset (Fin N) :=
  univ.filter fun w => (s(u, w) ∈ J ∧ Op J v w) ∨ (Op J u w ∧ s(v, w) ∈ J)

theorem Yset_comm (J : Finset (Sym2 (Fin N))) (u v : Fin N) : Yset J u v = Yset J v u := by
  classical
  ext w
  simp only [Yset, mem_filter, mem_univ, true_and]
  tauto

open Classical in
/-- The open pair at `w ∈ Yset J u v`. -/
noncomputable def partner (J : Finset (Sym2 (Fin N))) (u v w : Fin N) : Sym2 (Fin N) :=
  if s(u, w) ∈ J then s(v, w) else s(u, w)

/-- The closing count as a function of the pair. -/
noncomputable def Ys (J : Finset (Sym2 (Fin N))) (e : Sym2 (Fin N)) : ℕ :=
  Sym2.lift ⟨fun u v => (Yset J u v).card, fun u v => congrArg Finset.card (Yset_comm J u v)⟩ e

theorem Ys_mk (J : Finset (Sym2 (Fin N))) (u v : Fin N) : Ys J s(u, v) = (Yset J u v).card := rfl

/-- A history is valid if every chosen pair was open when chosen. -/
def Valid : List (Sym2 (Fin N)) → Prop
  | [] => True
  | e :: s => e ∈ openSet s.toFinset ∧ Valid s

/-- No loops and no triangles. -/
def TF (J : Finset (Sym2 (Fin N))) : Prop :=
  (∀ e ∈ J, ¬ e.IsDiag) ∧ ∀ a b c, s(a, b) ∈ J → s(a, c) ∈ J → s(b, c) ∈ J → False

/-- Adding the open pair `ab` closes `uv` (through a chosen pair at the other end). -/
def Closes (J : Finset (Sym2 (Fin N))) (a b u v : Fin N) : Prop :=
  (u = a ∧ s(v, b) ∈ J) ∨ (u = b ∧ s(v, a) ∈ J) ∨ (v = a ∧ s(u, b) ∈ J) ∨ (v = b ∧ s(u, a) ∈ J)

/- ## Helper lemmas

Proof infrastructure for the statements below. Everything is kept in the namespace `StepAux`, so
that the names cannot clash with declarations of later parts. -/

namespace StepAux

theorem sym2_mem_swap {J : Finset (Sym2 (Fin N))} {x y : Fin N} (h : s(x, y) ∈ J) :
    s(y, x) ∈ J := by
  rw [Sym2.eq_swap]
  exact h

theorem mem_nb {J : Finset (Sym2 (Fin N))} {u w : Fin N} : w ∈ nb J u ↔ s(u, w) ∈ J := by
  classical
  simp only [nb, mem_filter, mem_univ, true_and]

theorem mem_cod {J : Finset (Sym2 (Fin N))} {u v w : Fin N} :
    w ∈ cod J u v ↔ s(u, w) ∈ J ∧ s(v, w) ∈ J := by
  classical
  simp only [cod, mem_filter, mem_univ, true_and]

theorem mem_Xset {J : Finset (Sym2 (Fin N))} {u v w : Fin N} :
    w ∈ Xset J u v ↔ Op J u w ∧ Op J v w := by
  classical
  simp only [Xset, mem_filter, mem_univ, true_and]

theorem mem_Yset {J : Finset (Sym2 (Fin N))} {u v w : Fin N} :
    w ∈ Yset J u v ↔ (s(u, w) ∈ J ∧ Op J v w) ∨ (Op J u w ∧ s(v, w) ∈ J) := by
  classical
  simp only [Yset, mem_filter, mem_univ, true_and]

theorem op_mono {J J' : Finset (Sym2 (Fin N))} (h : J ⊆ J') {u v : Fin N} (huv : Op J' u v) :
    Op J u v :=
  ⟨huv.1, fun hm => huv.2.1 (h hm), fun w hw => huv.2.2 w ⟨h hw.1, h hw.2⟩⟩

theorem op_of_insert {J : Finset (Sym2 (Fin N))} {e : Sym2 (Fin N)} {u v : Fin N}
    (huv : Op (insert e J) u v) : Op J u v :=
  op_mono (subset_insert e J) huv

theorem tf_not_loop {J : Finset (Sym2 (Fin N))} (hJ : TF J) (x : Fin N) : s(x, x) ∉ J :=
  fun hx => hJ.1 _ hx (Sym2.mk_isDiag_iff.mpr rfl)

/-- A chosen pair is not open. -/
theorem not_mem_openSet_of_mem {J : Finset (Sym2 (Fin N))} {e : Sym2 (Fin N)} (h : e ∈ J) :
    e ∉ openSet J := by
  intro he
  obtain ⟨u, v, rfl, huv⟩ := exists_of_mem_openSet he
  exact huv.2.1 h

theorem openSet_insert_subset_aux (J : Finset (Sym2 (Fin N))) (e : Sym2 (Fin N)) :
    openSet (insert e J) ⊆ openSet J := by
  intro f hf
  obtain ⟨u, v, rfl, huv⟩ := exists_of_mem_openSet hf
  exact mk_mem_openSet.mpr (op_of_insert huv)

/-- The two possible shapes of a vertex of `Yset J u v`, with the value of `partner`. -/
theorem partner_spec {J : Finset (Sym2 (Fin N))} {u v w : Fin N} (hw : w ∈ Yset J u v) :
    (s(u, w) ∈ J ∧ Op J v w ∧ partner J u v w = s(v, w)) ∨
      (Op J u w ∧ s(v, w) ∈ J ∧ partner J u v w = s(u, w)) := by
  rcases mem_Yset.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    unfold partner
    exact if_pos h1
  · refine Or.inr ⟨h1, h2, ?_⟩
    unfold partner
    exact if_neg h1.2.1

theorem partner_mem_openSet_aux {J : Finset (Sym2 (Fin N))} {u v w : Fin N}
    (hw : w ∈ Yset J u v) : partner J u v w ∈ openSet J := by
  rcases partner_spec hw with ⟨-, h2, h3⟩ | ⟨h1, -, h3⟩
  · rw [h3]
    exact mk_mem_openSet.mpr h2
  · rw [h3]
    exact mk_mem_openSet.mpr h1

/-- For an open pair `uw`: the pairs `e` whose insertion makes `uw` non-open. -/
theorem not_op_insert_iff {J : Finset (Sym2 (Fin N))} {e : Sym2 (Fin N)} {u w : Fin N}
    (huw : Op J u w) :
    ¬ Op (insert e J) u w ↔
      e = s(u, w) ∨ ∃ z, (e = s(u, z) ∧ s(w, z) ∈ J) ∨ (e = s(w, z) ∧ s(u, z) ∈ J) := by
  constructor
  · intro h
    by_contra hcon
    obtain ⟨c1, c2⟩ := not_or.mp hcon
    apply h
    refine ⟨huw.1, ?_, ?_⟩
    · intro hm
      rcases mem_insert.mp hm with hm | hm
      · exact c1 hm.symm
      · exact huw.2.1 hm
    · rintro z ⟨hz1, hz2⟩
      rcases mem_insert.mp hz1 with hz1 | hz1 <;> rcases mem_insert.mp hz2 with hz2 | hz2
      · rcases Sym2.eq_iff.mp (hz1.trans hz2.symm) with ⟨h', -⟩ | ⟨h', h''⟩
        · exact huw.1 h'
        · exact huw.1 (h'.trans h'')
      · exact c2 ⟨z, Or.inl ⟨hz1.symm, hz2⟩⟩
      · exact c2 ⟨z, Or.inr ⟨hz2.symm, hz1⟩⟩
      · exact huw.2.2 z ⟨hz1, hz2⟩
  · rintro (rfl | ⟨z, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩) hop
    · exact hop.2.1 (mem_insert_self _ _)
    · exact hop.2.2 z ⟨mem_insert_self _ _, mem_insert_of_mem h2⟩
    · exact hop.2.2 z ⟨mem_insert_of_mem h2, mem_insert_self _ _⟩

/-- "Killing" is symmetric: if inserting `e` makes the open pair `f` non-open, then inserting `f`
makes `e` non-open. -/
theorem not_mem_openSet_insert_symm {J : Finset (Sym2 (Fin N))} {e f : Sym2 (Fin N)}
    (hf : f ∈ openSet J) (h : f ∉ openSet (insert e J)) : e ∉ openSet (insert f J) := by
  obtain ⟨u, w, rfl, huw⟩ := exists_of_mem_openSet hf
  have h' : ¬ Op (insert e J) u w := fun hop => h (mk_mem_openSet.mpr hop)
  rcases (not_op_insert_iff huw).mp h' with rfl | ⟨z, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩
  · exact not_mem_openSet_of_mem (mem_insert_self _ _)
  · intro hmem
    have hop := mk_mem_openSet.mp hmem
    exact hop.2.2 w ⟨mem_insert_self _ _, mem_insert_of_mem (sym2_mem_swap h2)⟩
  · intro hmem
    have hop := mk_mem_openSet.mp hmem
    exact hop.2.2 u ⟨mem_insert.mpr (Or.inl Sym2.eq_swap), mem_insert_of_mem (sym2_mem_swap h2)⟩

/-- The open pairs destroyed by inserting the open pair `ab`. -/
theorem not_mem_openSet_insert_iff {J : Finset (Sym2 (Fin N))} {a b : Fin N} (hab : Op J a b)
    {f : Sym2 (Fin N)} (hf : f ∈ openSet J) :
    f ∉ openSet (insert s(a, b) J) ↔
      f = s(a, b) ∨ ∃ z, (f = s(a, z) ∧ s(b, z) ∈ J) ∨ (f = s(b, z) ∧ s(a, z) ∈ J) := by
  constructor
  · intro h
    exact (not_op_insert_iff hab).mp fun hop =>
      not_mem_openSet_insert_symm hf h (mk_mem_openSet.mpr hop)
  · intro h
    exact not_mem_openSet_insert_symm (mk_mem_openSet.mpr hab)
      (fun h' => (not_op_insert_iff hab).mpr h (mk_mem_openSet.mp h'))

theorem openSet_sdiff_insert {J : Finset (Sym2 (Fin N))} {a b : Fin N} (hab : Op J a b) :
    openSet J \ openSet (insert s(a, b) J)
      = insert s(a, b) ((Yset J a b).image (partner J a b)) := by
  classical
  ext f
  simp only [mem_sdiff, mem_insert, mem_image]
  constructor
  · rintro ⟨hf, hnf⟩
    rcases (not_mem_openSet_insert_iff hab hf).mp hnf with h | ⟨z, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩
    · exact Or.inl h
    · have haz : Op J a z := mk_mem_openSet.mp hf
      refine Or.inr ⟨z, mem_Yset.mpr (Or.inr ⟨haz, h2⟩), ?_⟩
      unfold partner
      exact if_neg haz.2.1
    · have hbz : Op J b z := mk_mem_openSet.mp hf
      refine Or.inr ⟨z, mem_Yset.mpr (Or.inl ⟨h2, hbz⟩), ?_⟩
      unfold partner
      exact if_pos h2
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact ⟨mk_mem_openSet.mpr hab, not_mem_openSet_of_mem (mem_insert_self _ _)⟩
    · refine ⟨partner_mem_openSet_aux hz, ?_⟩
      rcases partner_spec hz with ⟨h1, -, h3⟩ | ⟨-, h2, h3⟩
      · rw [h3]
        intro hmem
        have hop := mk_mem_openSet.mp hmem
        exact hop.2.2 a
          ⟨mem_insert.mpr (Or.inl Sym2.eq_swap), mem_insert_of_mem (sym2_mem_swap h1)⟩
      · rw [h3]
        intro hmem
        have hop := mk_mem_openSet.mp hmem
        exact hop.2.2 b ⟨mem_insert_self _ _, mem_insert_of_mem (sym2_mem_swap h2)⟩

theorem card_openSet_sdiff_insert {J : Finset (Sym2 (Fin N))} (hJ : TF J) {a b : Fin N}
    (hab : Op J a b) :
    (openSet J \ openSet (insert s(a, b) J)).card = 1 + (Yset J a b).card := by
  classical
  have hloop := tf_not_loop hJ
  have hinj : Set.InjOn (partner J a b) (Yset J a b : Set (Fin N)) := by
    intro x hx y hy hxy
    rcases partner_spec (mem_coe.mp hx) with ⟨hx1, hx2, hx3⟩ | ⟨hx1, hx2, hx3⟩ <;>
      rcases partner_spec (mem_coe.mp hy) with ⟨hy1, hy2, hy3⟩ | ⟨hy1, hy2, hy3⟩
    · rw [hx3, hy3] at hxy
      rcases Sym2.eq_iff.mp hxy with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hy2.1
    · rw [hx3, hy3] at hxy
      rcases Sym2.eq_iff.mp hxy with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm hab.1
      · exfalso
        rw [h] at hx1
        exact hloop _ hx1
    · rw [hx3, hy3] at hxy
      rcases Sym2.eq_iff.mp hxy with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hab.1
      · exfalso
        rw [h] at hx2
        exact hloop _ hx2
    · rw [hx3, hy3] at hxy
      rcases Sym2.eq_iff.mp hxy with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hy1.1
  have hnot : s(a, b) ∉ (Yset J a b).image (partner J a b) := by
    intro hmem
    obtain ⟨z, hz, hzeq⟩ := mem_image.mp hmem
    rcases partner_spec hz with ⟨h1, -, h3⟩ | ⟨-, h2, h3⟩
    · rw [h3] at hzeq
      rcases Sym2.eq_iff.mp hzeq with ⟨h, -⟩ | ⟨-, h⟩
      · exact hab.1 h.symm
      · rw [h] at h1
        exact hloop _ h1
    · rw [h3] at hzeq
      rcases Sym2.eq_iff.mp hzeq with ⟨-, h⟩ | ⟨h, -⟩
      · rw [h] at h2
        exact hloop _ h2
      · exact hab.1 h
  rw [openSet_sdiff_insert hab, card_insert_of_notMem hnot, card_image_of_injOn hinj]
  omega

/-- The number of open pairs whose insertion destroys the open pair `f`. -/
theorem card_filter_killers {J : Finset (Sym2 (Fin N))} (hJ : TF J) {f : Sym2 (Fin N)}
    (hf : f ∈ openSet J) :
    ((openSet J).filter fun e => f ∉ openSet (insert e J)).card = 1 + Ys J f := by
  classical
  obtain ⟨u, w, rfl, huw⟩ := exists_of_mem_openSet hf
  have hset : ((openSet J).filter fun e => s(u, w) ∉ openSet (insert e J))
      = openSet J \ openSet (insert s(u, w) J) := by
    ext e
    rw [mem_filter, mem_sdiff]
    exact ⟨fun h => ⟨h.1, not_mem_openSet_insert_symm hf h.2⟩,
      fun h => ⟨h.1, not_mem_openSet_insert_symm h.1 h.2⟩⟩
  rw [hset, card_openSet_sdiff_insert hJ huw, Ys_mk]

/-- If `uv`, `uw`, `vw` are all open, no single insertion destroys both `uw` and `vw`. -/
theorem not_both_killed {J : Finset (Sym2 (Fin N))} {e : Sym2 (Fin N)} {u v w : Fin N}
    (huv : Op J u v) (huw : Op J u w) (hvw : Op J v w)
    (n1 : ¬ Op (insert e J) u w) (n2 : ¬ Op (insert e J) v w) : False := by
  rcases (not_op_insert_iff huw).mp n1 with h1 | ⟨z, ⟨h1, k1⟩ | ⟨h1, k1⟩⟩ <;>
    rcases (not_op_insert_iff hvw).mp n2 with h2 | ⟨y, ⟨h2, k2⟩ | ⟨h2, k2⟩⟩
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact huv.1 h
    · exact huw.1 h
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨-, h⟩
    · exact huv.1 h
    · exact hvw.1 h.symm
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact huw.1 h
    · rw [← h] at k2
      exact huv.2.1 (sym2_mem_swap k2)
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact huv.1 h
    · exact huw.1 h
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨-, h⟩
    · exact huv.1 h
    · rw [h] at k1
      exact hvw.2.1 (sym2_mem_swap k1)
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact huw.1 h
    · rw [← h] at k2
      exact huv.2.1 (sym2_mem_swap k2)
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨-, h⟩
    · exact hvw.1 h.symm
    · rw [h] at k1
      exact huv.2.1 k1
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨h, -⟩ | ⟨-, h⟩
    · exact hvw.1 h.symm
    · rw [h] at k1
      exact huv.2.1 k1
  · rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨-, h⟩ | ⟨-, h⟩
    · rw [← h] at k2
      exact huv.2.2 z ⟨k1, k2⟩
    · rw [h] at k1
      exact huw.2.1 k1

/-- A vertex of `Yset J u v` survives an insertion iff its open pair survives. -/
theorem mem_Yset_insert_iff {J : Finset (Sym2 (Fin N))} {e : Sym2 (Fin N)} {u v w : Fin N}
    (hw : w ∈ Yset J u v) :
    w ∈ Yset (insert e J) u v ↔ partner J u v w ∈ openSet (insert e J) := by
  rcases partner_spec hw with ⟨h1, -, h3⟩ | ⟨-, h2, h3⟩
  · rw [h3, mk_mem_openSet, mem_Yset]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd (mem_insert_of_mem h1) h.2.1
    · intro h
      exact Or.inl ⟨mem_insert_of_mem h1, h⟩
  · rw [h3, mk_mem_openSet, mem_Yset]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd (mem_insert_of_mem h2) h.2.1
      · exact h
    · intro h
      exact Or.inr ⟨h, mem_insert_of_mem h2⟩

/-- Where a pair `xw` destroyed by the insertion of `ab` can sit. -/
theorem not_op_insert_cases {J : Finset (Sym2 (Fin N))} {a b x w : Fin N} (hxw : Op J x w)
    (hn : ¬ Op (insert s(a, b) J) x w) :
    w = a ∨ w = b ∨ (x = a ∧ s(b, w) ∈ J) ∨ (x = b ∧ s(a, w) ∈ J) := by
  rcases (not_op_insert_iff hxw).mp hn with h | ⟨z, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · rcases Sym2.eq_iff.mp h with ⟨-, hb⟩ | ⟨ha, -⟩
    · exact Or.inr (Or.inl hb.symm)
    · exact Or.inl ha.symm
  · rcases Sym2.eq_iff.mp h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine Or.inr (Or.inr (Or.inl ⟨ha.symm, ?_⟩))
      rw [hb]
      exact sym2_mem_swap h2
    · refine Or.inr (Or.inr (Or.inr ⟨hb.symm, ?_⟩))
      rw [ha]
      exact sym2_mem_swap h2
  · rcases Sym2.eq_iff.mp h1 with ⟨ha, -⟩ | ⟨-, hb⟩
    · exact Or.inl ha.symm
    · exact Or.inr (Or.inl hb.symm)

theorem Yset_lost_cases {J : Finset (Sym2 (Fin N))} {a b u v w : Fin N}
    (hw : w ∈ Yset J u v \ Yset (insert s(a, b) J) u v) :
    w = a ∨ w = b ∨ (v = a ∧ w ∈ cod J u b) ∨ (v = b ∧ w ∈ cod J u a) ∨
      (u = a ∧ w ∈ cod J v b) ∨ (u = b ∧ w ∈ cod J v a) := by
  classical
  obtain ⟨hw1, hw2⟩ := mem_sdiff.mp hw
  rcases partner_spec hw1 with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · have hn : ¬ Op (insert s(a, b) J) v w := fun h =>
      hw2 (mem_Yset.mpr (Or.inl ⟨mem_insert_of_mem h1, h⟩))
    rcases not_op_insert_cases h2 hn with h | h | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h, mem_cod.mpr ⟨h1, h'⟩⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, mem_cod.mpr ⟨h1, h'⟩⟩)))
  · have hn : ¬ Op (insert s(a, b) J) u w := fun h =>
      hw2 (mem_Yset.mpr (Or.inr ⟨h, mem_insert_of_mem h2⟩))
    rcases not_op_insert_cases h1 hn with h | h | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, mem_cod.mpr ⟨h2, h'⟩⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, mem_cod.mpr ⟨h2, h'⟩⟩))))

/-- Double counting for a relation between two finsets. -/
theorem sum_card_filter_comm {α β : Type*} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a ∈ s, (t.filter fun b => r a b).card = ∑ b ∈ t, (s.filter fun a => r a b).card := by
  simp_rw [card_filter]
  exact sum_comm

end StepAux

open StepAux

/- ## Basic facts -/

theorem Op.mono {J J' : Finset (Sym2 (Fin N))} (h : J ⊆ J') {u v : Fin N} (huv : Op J' u v) :
    Op J u v := by
  exact op_mono h huv

theorem tf_empty : TF (∅ : Finset (Sym2 (Fin N))) := by
  exact ⟨fun e he => absurd he (notMem_empty e), fun a b c h _ _ => absurd h (notMem_empty _)⟩

theorem tf_insert {J : Finset (Sym2 (Fin N))} (hJ : TF J) {a b : Fin N} (hab : Op J a b) :
    TF (insert s(a, b) J) := by
  have hloop := tf_not_loop hJ
  have key : ∀ z, ¬ (s(a, z) ∈ insert s(a, b) J ∧ s(b, z) ∈ insert s(a, b) J) := by
    rintro z ⟨h1, h2⟩
    rcases mem_insert.mp h1 with h1 | h1
    · rcases Sym2.eq_iff.mp h1 with ⟨-, hz⟩ | ⟨h, -⟩
      · rw [hz] at h2
        rcases mem_insert.mp h2 with h2 | h2
        · rcases Sym2.eq_iff.mp h2 with ⟨h, -⟩ | ⟨-, h⟩
          · exact hab.1 h.symm
          · exact hab.1 h.symm
        · exact hloop _ h2
      · exact hab.1 h
    · rcases mem_insert.mp h2 with h2 | h2
      · rcases Sym2.eq_iff.mp h2 with ⟨h, -⟩ | ⟨-, hz⟩
        · exact hab.1 h.symm
        · rw [hz] at h1
          exact hloop _ h1
      · exact hab.2.2 z ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · rw [Sym2.mk_isDiag_iff]
      exact hab.1
    · exact hJ.1 e he
  · intro x y z h1 h2 h3
    rcases mem_insert.mp h1 with e1 | h1'
    · rcases Sym2.eq_iff.mp e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact key z ⟨h2, h3⟩
      · exact key z ⟨h3, h2⟩
    · rcases mem_insert.mp h2 with e2 | h2'
      · rcases Sym2.eq_iff.mp e2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact key y ⟨h1, sym2_mem_swap h3⟩
        · exact key y ⟨sym2_mem_swap h3, h1⟩
      · rcases mem_insert.mp h3 with e3 | h3'
        · rcases Sym2.eq_iff.mp e3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact key x ⟨sym2_mem_swap h1, sym2_mem_swap h2⟩
          · exact key x ⟨sym2_mem_swap h2, sym2_mem_swap h1⟩
        · exact hJ.2 x y z h1' h2' h3'

theorem Valid.tf {s : List (Sym2 (Fin N))} (h : Valid s) : TF s.toFinset := by
  induction s with
  | nil =>
    rw [List.toFinset_nil]
    exact tf_empty
  | cons e s ih =>
    have h' : e ∈ openSet s.toFinset ∧ Valid s := h
    obtain ⟨he, hs⟩ := h'
    obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_openSet he
    rw [List.toFinset_cons]
    exact tf_insert (ih hs) hab

theorem op_insert_iff {J : Finset (Sym2 (Fin N))} {a b : Fin N} (_hab : Op J a b) {u v : Fin N} :
    Op (insert s(a, b) J) u v ↔ Op J u v ∧ s(u, v) ≠ s(a, b) ∧ ¬ Closes J a b u v := by
  constructor
  · intro h
    have huv : Op J u v := op_of_insert h
    have hn : ¬ (s(a, b) = s(u, v) ∨
        ∃ z, (s(a, b) = s(u, z) ∧ s(v, z) ∈ J) ∨ (s(a, b) = s(v, z) ∧ s(u, z) ∈ J)) :=
      fun hx => (not_op_insert_iff huv).mpr hx h
    refine ⟨huv, fun heq => hn (Or.inl heq.symm), fun hc => hn (Or.inr ?_)⟩
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨b, Or.inl ⟨by rw [h1], h2⟩⟩
    · exact ⟨a, Or.inl ⟨by rw [h1]; exact Sym2.eq_swap, h2⟩⟩
    · exact ⟨b, Or.inr ⟨by rw [h1], h2⟩⟩
    · exact ⟨a, Or.inr ⟨by rw [h1]; exact Sym2.eq_swap, h2⟩⟩
  · rintro ⟨huv, hne, hc⟩
    by_contra hn
    rcases (not_op_insert_iff huv).mp hn with h | ⟨z, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact hne h.symm
    · rcases Sym2.eq_iff.mp h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hc (Or.inl ⟨ha.symm, by rw [hb]; exact h2⟩)
      · exact hc (Or.inr (Or.inl ⟨hb.symm, by rw [ha]; exact h2⟩))
    · rcases Sym2.eq_iff.mp h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hc (Or.inr (Or.inr (Or.inl ⟨ha.symm, by rw [hb]; exact h2⟩)))
      · exact hc (Or.inr (Or.inr (Or.inr ⟨hb.symm, by rw [ha]; exact h2⟩)))

theorem card_openSet_empty : (openSet (∅ : Finset (Sym2 (Fin N)))).card = N.choose 2 := by
  classical
  have h := Sym2.card_subtype_not_diag (α := Fin N)
  rw [Fintype.card_subtype, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext e
  refine Sym2.ind (fun u v => ?_) e
  rw [mk_mem_openSet, mem_filter, Sym2.mk_isDiag_iff]
  constructor
  · intro h'
    exact ⟨mem_univ _, h'.1⟩
  · rintro ⟨-, h'⟩
    exact ⟨h', notMem_empty _, fun w hw => notMem_empty _ hw.1⟩

theorem card_Xset_empty {u v : Fin N} (h : u ≠ v) :
    (Xset (∅ : Finset (Sym2 (Fin N))) u v).card = N - 2 := by
  classical
  have hX : Xset (∅ : Finset (Sym2 (Fin N))) u v = univ \ {u, v} := by
    ext w
    rw [mem_Xset, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨mem_univ _, ?_⟩
      rintro (hw | hw)
      · exact h1.1 hw.symm
      · exact h2.1 hw.symm
    · rintro ⟨-, hw⟩
      have hop : ∀ x : Fin N, x ≠ w → Op (∅ : Finset (Sym2 (Fin N))) x w := fun x hx =>
        ⟨hx, notMem_empty _, fun z hz => notMem_empty _ hz.1⟩
      exact ⟨hop u (fun e => hw (Or.inl e.symm)), hop v (fun e => hw (Or.inr e.symm))⟩
  have h1 := card_sdiff_add_card_eq_card (subset_univ ({u, v} : Finset (Fin N)))
  rw [card_univ, Fintype.card_fin, card_pair h] at h1
  rw [hX]
  omega

theorem Yset_empty (u v : Fin N) : Yset (∅ : Finset (Sym2 (Fin N))) u v = ∅ := by
  classical
  ext w
  rw [mem_Yset]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h (notMem_empty _)
    · exact absurd h (notMem_empty _)
  · intro h
    exact absurd h (notMem_empty _)

theorem nb_empty (u : Fin N) : nb (∅ : Finset (Sym2 (Fin N))) u = ∅ := by
  classical
  ext w
  rw [mem_nb]
  constructor
  · intro h
    exact absurd h (notMem_empty _)
  · intro h
    exact absurd h (notMem_empty _)

theorem cod_empty (u v : Fin N) : cod (∅ : Finset (Sym2 (Fin N))) u v = ∅ := by
  classical
  ext w
  rw [mem_cod]
  constructor
  · rintro ⟨h, -⟩
    exact absurd h (notMem_empty _)
  · intro h
    exact absurd h (notMem_empty _)

theorem Yset_subset_nb (J : Finset (Sym2 (Fin N))) (u v : Fin N) :
    Yset J u v ⊆ nb J u ∪ nb J v := by
  classical
  intro w hw
  rw [mem_union, mem_nb, mem_nb]
  rcases mem_Yset.mp hw with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

open Classical in
/-- Sums over open pairs as sums over ordered open pairs. -/
theorem two_mul_sum_openSet (J : Finset (Sym2 (Fin N))) (F : Sym2 (Fin N) → ℝ) :
    2 * ∑ e ∈ openSet J, F e
      = ∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, F s(p.1, p.2) := by
  have hmaps : ∀ p ∈ (univ : Finset (Fin N × Fin N)).filter (fun p => Op J p.1 p.2),
      s(p.1, p.2) ∈ openSet J := by
    intro p hp
    exact mk_mem_openSet.mpr (mem_filter.mp hp).2
  rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
  refine sum_congr rfl fun e he => ?_
  obtain ⟨u, v, rfl, huv⟩ := exists_of_mem_openSet he
  have hfib : ((univ : Finset (Fin N × Fin N)).filter (fun p => Op J p.1 p.2)).filter
      (fun p => s(p.1, p.2) = s(u, v)) = {(u, v), (v, u)} := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)
    · rintro (rfl | rfl)
      · exact ⟨huv, rfl⟩
      · exact ⟨huv.symm, Sym2.eq_swap⟩
  have hne : (u, v) ≠ (v, u) := fun h => huv.1 (congrArg Prod.fst h)
  rw [hfib, sum_pair hne]
  show 2 * F s(u, v) = F s(u, v) + F s(v, u)
  rw [Sym2.eq_swap (a := v) (b := u)]
  ring

/- ## The number of open pairs -/

theorem card_openSet_insert {J : Finset (Sym2 (Fin N))} (hJ : TF J) {a b : Fin N}
    (hab : Op J a b) :
    (openSet (insert s(a, b) J)).card + 1 + (Yset J a b).card = (openSet J).card := by
  classical
  have h1 := card_openSet_sdiff_insert hJ hab
  have h2 := card_sdiff_add_card_eq_card (openSet_insert_subset_aux J s(a, b))
  omega

/- ## `Xset` -/

theorem Xset_insert_subset (J : Finset (Sym2 (Fin N))) (e : Sym2 (Fin N)) (u v : Fin N) :
    Xset (insert e J) u v ⊆ Xset J u v := by
  intro w hw
  obtain ⟨h1, h2⟩ := mem_Xset.mp hw
  exact mem_Xset.mpr ⟨op_of_insert h1, op_of_insert h2⟩

theorem Xset_removed_subset {J : Finset (Sym2 (Fin N))} {a b : Fin N} (_hab : Op J a b)
    (u v : Fin N) :
    Xset J u v \ Xset (insert s(a, b) J) u v ⊆ insert a (insert b (nb J a ∪ nb J b)) := by
  classical
  intro w hw
  obtain ⟨hw1, hw2⟩ := mem_sdiff.mp hw
  obtain ⟨huw, hvw⟩ := mem_Xset.mp hw1
  have hcases : ∃ x, w = a ∨ w = b ∨ (x = a ∧ s(b, w) ∈ J) ∨ (x = b ∧ s(a, w) ∈ J) := by
    by_cases h1 : Op (insert s(a, b) J) u w
    · have h2 : ¬ Op (insert s(a, b) J) v w := fun h2 => hw2 (mem_Xset.mpr ⟨h1, h2⟩)
      exact ⟨v, not_op_insert_cases hvw h2⟩
    · exact ⟨u, not_op_insert_cases huw h1⟩
  obtain ⟨x, hx⟩ := hcases
  simp only [mem_insert, mem_union, mem_nb]
  rcases hx with h | h | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Exact drift of `X`: every `w ∈ Xset J u v` is removed by exactly
`2 + Y(uw) + Y(vw)` open choices. -/
theorem sum_Xset_removed {J : Finset (Sym2 (Fin N))} (hJ : TF J) {u v : Fin N}
    (huv : Op J u v) :
    ∑ e ∈ openSet J, (Xset J u v \ Xset (insert e J) u v).card
      = ∑ w ∈ Xset J u v, (2 + (Yset J u w).card + (Yset J v w).card) := by
  classical
  have h1 : ∀ e, Xset J u v \ Xset (insert e J) u v
      = (Xset J u v).filter
          (fun w => s(u, w) ∉ openSet (insert e J) ∨ s(v, w) ∉ openSet (insert e J)) := by
    intro e
    ext w
    rw [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨hw, hn⟩
      refine ⟨hw, ?_⟩
      by_contra hcon
      obtain ⟨c1, c2⟩ := not_or.mp hcon
      exact hn (mem_Xset.mpr
        ⟨mk_mem_openSet.mp (not_not.mp c1), mk_mem_openSet.mp (not_not.mp c2)⟩)
    · rintro ⟨hw, hn⟩
      refine ⟨hw, fun hmem => ?_⟩
      obtain ⟨c1, c2⟩ := mem_Xset.mp hmem
      rcases hn with hn | hn
      · exact hn (mk_mem_openSet.mpr c1)
      · exact hn (mk_mem_openSet.mpr c2)
  have h2 : ∀ w ∈ Xset J u v,
      ((openSet J).filter
        (fun e => s(u, w) ∉ openSet (insert e J) ∨ s(v, w) ∉ openSet (insert e J))).card
        = 2 + (Yset J u w).card + (Yset J v w).card := by
    intro w hw
    obtain ⟨huw, hvw⟩ := mem_Xset.mp hw
    have hdisj : Disjoint ((openSet J).filter (fun e => s(u, w) ∉ openSet (insert e J)))
        ((openSet J).filter (fun e => s(v, w) ∉ openSet (insert e J))) := by
      rw [disjoint_left]
      intro e he1 he2
      exact not_both_killed huv huw hvw
        (fun h => (mem_filter.mp he1).2 (mk_mem_openSet.mpr h))
        (fun h => (mem_filter.mp he2).2 (mk_mem_openSet.mpr h))
    have hunion : (openSet J).filter
        (fun e => s(u, w) ∉ openSet (insert e J) ∨ s(v, w) ∉ openSet (insert e J))
        = (openSet J).filter (fun e => s(u, w) ∉ openSet (insert e J)) ∪
          (openSet J).filter (fun e => s(v, w) ∉ openSet (insert e J)) := by
      ext e
      simp only [mem_filter, mem_union]
      tauto
    rw [hunion, card_union_of_disjoint hdisj, card_filter_killers hJ (mk_mem_openSet.mpr huw),
      card_filter_killers hJ (mk_mem_openSet.mpr hvw), Ys_mk, Ys_mk]
    omega
  calc ∑ e ∈ openSet J, (Xset J u v \ Xset (insert e J) u v).card
      = ∑ e ∈ openSet J, ((Xset J u v).filter
          (fun w => s(u, w) ∉ openSet (insert e J) ∨ s(v, w) ∉ openSet (insert e J))).card :=
        sum_congr rfl fun e _ => by rw [h1 e]
    _ = ∑ w ∈ Xset J u v, ((openSet J).filter
          (fun e => s(u, w) ∉ openSet (insert e J) ∨ s(v, w) ∉ openSet (insert e J))).card :=
        sum_card_filter_comm (openSet J) (Xset J u v)
          (fun e w => s(u, w) ∉ openSet (insert e J) ∨ s(v, w) ∉ openSet (insert e J))
    _ = ∑ w ∈ Xset J u v, (2 + (Yset J u w).card + (Yset J v w).card) := sum_congr rfl h2

/- ## `Yset` -/

/-- Exact gain of `Y`: `w` enters `Yset J u v` exactly when `uw` or `vw` is chosen and
`w ∈ Xset J u v`. -/
theorem sum_Yset_gained {J : Finset (Sym2 (Fin N))} (_hJ : TF J) {u v : Fin N}
    (huv : Op J u v) :
    ∑ e ∈ openSet J, (Yset (insert e J) u v \ Yset J u v).card = 2 * (Xset J u v).card := by
  classical
  have h1 : ∀ e ∈ openSet J, Yset (insert e J) u v \ Yset J u v
      = (Xset J u v).filter (fun w => e = s(u, w) ∨ e = s(v, w)) := by
    intro e he
    ext w
    simp only [mem_sdiff, mem_filter, mem_Xset, mem_Yset]
    constructor
    · rintro ⟨h | h, hn⟩
      · obtain ⟨hm, hop⟩ := h
        have hvw : Op J v w := op_of_insert hop
        rcases mem_insert.mp hm with heq | hin
        · subst heq
          exact ⟨⟨mk_mem_openSet.mp he, hvw⟩, Or.inl rfl⟩
        · exact absurd (Or.inl ⟨hin, hvw⟩) hn
      · obtain ⟨hop, hm⟩ := h
        have huw : Op J u w := op_of_insert hop
        rcases mem_insert.mp hm with heq | hin
        · subst heq
          exact ⟨⟨huw, mk_mem_openSet.mp he⟩, Or.inr rfl⟩
        · exact absurd (Or.inr ⟨huw, hin⟩) hn
    · rintro ⟨⟨huw, hvw⟩, h | h⟩
      · subst h
        refine ⟨Or.inl ⟨mem_insert_self _ _, ?_⟩, ?_⟩
        · by_contra hn
          exact not_both_killed huv huw hvw (fun h => h.2.1 (mem_insert_self _ _)) hn
        · rintro (⟨k1, -⟩ | ⟨-, k2⟩)
          · exact huw.2.1 k1
          · exact hvw.2.1 k2
      · subst h
        refine ⟨Or.inr ⟨?_, mem_insert_self _ _⟩, ?_⟩
        · by_contra hn
          exact not_both_killed huv huw hvw hn (fun h => h.2.1 (mem_insert_self _ _))
        · rintro (⟨k1, -⟩ | ⟨-, k2⟩)
          · exact huw.2.1 k1
          · exact hvw.2.1 k2
  have h2 : ∀ w ∈ Xset J u v,
      ((openSet J).filter (fun e => e = s(u, w) ∨ e = s(v, w))).card = 2 := by
    intro w hw
    obtain ⟨huw, hvw⟩ := mem_Xset.mp hw
    have hpair : (openSet J).filter (fun e => e = s(u, w) ∨ e = s(v, w))
        = {s(u, w), s(v, w)} := by
      ext e
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨mk_mem_openSet.mpr huw, Or.inl rfl⟩
        · exact ⟨mk_mem_openSet.mpr hvw, Or.inr rfl⟩
    have hne : s(u, w) ≠ s(v, w) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
      · exact huv.1 h'
      · exact huw.1 h'
    rw [hpair, card_pair hne]
  calc ∑ e ∈ openSet J, (Yset (insert e J) u v \ Yset J u v).card
      = ∑ e ∈ openSet J, ((Xset J u v).filter (fun w => e = s(u, w) ∨ e = s(v, w))).card :=
        sum_congr rfl fun e he => by rw [h1 e he]
    _ = ∑ w ∈ Xset J u v, ((openSet J).filter (fun e => e = s(u, w) ∨ e = s(v, w))).card :=
        sum_card_filter_comm (openSet J) (Xset J u v) (fun e w => e = s(u, w) ∨ e = s(v, w))
    _ = ∑ w ∈ Xset J u v, 2 := sum_congr rfl h2
    _ = 2 * (Xset J u v).card := by
        rw [sum_const, smul_eq_mul]
        omega

theorem Yset_gained_card_le {J : Finset (Sym2 (Fin N))} {a b : Fin N} (_hab : Op J a b)
    (u v : Fin N) : (Yset (insert s(a, b) J) u v \ Yset J u v).card ≤ 2 := by
  classical
  have hsub : Yset (insert s(a, b) J) u v \ Yset J u v ⊆ {a, b} := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_sdiff.mp hw
    have key : ∀ x : Fin N, s(x, w) ∈ insert s(a, b) J → s(x, w) ∉ J →
        w ∈ ({a, b} : Finset (Fin N)) := by
      intro x hx hxn
      rw [mem_insert, mem_singleton]
      rcases mem_insert.mp hx with h | h
      · rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact Or.inr h'
        · exact Or.inl h'
      · exact absurd h hxn
    rcases mem_Yset.mp hw1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key u h1 (fun h => hw2 (mem_Yset.mpr (Or.inl ⟨h, op_of_insert h2⟩)))
    · exact key v h2 (fun h => hw2 (mem_Yset.mpr (Or.inr ⟨op_of_insert h1, h⟩)))
  exact (card_le_card hsub).trans card_le_two

/-- Exact loss of `Y`: `w ∈ Yset J u v` leaves exactly when its open pair is chosen or closed. -/
theorem sum_Yset_lost {J : Finset (Sym2 (Fin N))} (hJ : TF J) {u v : Fin N}
    (_huv : Op J u v) :
    ∑ e ∈ openSet J, (Yset J u v \ Yset (insert e J) u v).card
      = ∑ w ∈ Yset J u v, (1 + Ys J (partner J u v w)) := by
  classical
  have h1 : ∀ e, Yset J u v \ Yset (insert e J) u v
      = (Yset J u v).filter (fun w => partner J u v w ∉ openSet (insert e J)) := by
    intro e
    ext w
    rw [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨hw, hnw⟩
      exact ⟨hw, fun h => hnw ((mem_Yset_insert_iff hw).mpr h)⟩
    · rintro ⟨hw, hnw⟩
      exact ⟨hw, fun h => hnw ((mem_Yset_insert_iff hw).mp h)⟩
  calc ∑ e ∈ openSet J, (Yset J u v \ Yset (insert e J) u v).card
      = ∑ e ∈ openSet J,
          ((Yset J u v).filter (fun w => partner J u v w ∉ openSet (insert e J))).card :=
        sum_congr rfl fun e _ => by rw [h1 e]
    _ = ∑ w ∈ Yset J u v,
          ((openSet J).filter (fun e => partner J u v w ∉ openSet (insert e J))).card :=
        sum_card_filter_comm (openSet J) (Yset J u v)
          (fun e w => partner J u v w ∉ openSet (insert e J))
    _ = ∑ w ∈ Yset J u v, (1 + Ys J (partner J u v w)) :=
        sum_congr rfl fun w hw => card_filter_killers hJ (partner_mem_openSet_aux hw)

theorem Yset_lost_card_le {J : Finset (Sym2 (Fin N))} (_hJ : TF J) {a b : Fin N}
    (hab : Op J a b) {u v : Fin N} (huv : Op J u v) (hne : s(a, b) ≠ s(u, v)) {Z : ℕ}
    (hZ : ∀ x y : Fin N, x ≠ y → (cod J x y).card ≤ Z) :
    (Yset J u v \ Yset (insert s(a, b) J) u v).card ≤ 2 + Z := by
  classical
  have hbound : ∀ S : Finset (Fin N), S.card ≤ Z →
      Yset J u v \ Yset (insert s(a, b) J) u v ⊆ insert a (insert b S) →
      (Yset J u v \ Yset (insert s(a, b) J) u v).card ≤ 2 + Z := by
    intro S hS hsub
    have h1 := card_le_card hsub
    have h2 := card_insert_le a (insert b S)
    have h3 := card_insert_le b S
    omega
  have hne1 : ¬ (a = u ∧ b = v) := fun h => hne (by rw [h.1, h.2])
  have hne2 : ¬ (a = v ∧ b = u) := fun h => hne (by rw [h.1, h.2]; exact Sym2.eq_swap)
  have hA : ∀ w : Fin N, w = a → ∀ S : Finset (Fin N), w ∈ insert a (insert b S) :=
    fun w h S => mem_insert.mpr (Or.inl h)
  have hB : ∀ w : Fin N, w = b → ∀ S : Finset (Fin N), w ∈ insert a (insert b S) :=
    fun w h S => mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl h)))
  have hS : ∀ (w : Fin N) (S : Finset (Fin N)), w ∈ S → w ∈ insert a (insert b S) :=
    fun w S h => mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr h)))
  by_cases c1 : v = a
  · refine hbound (cod J u b) (hZ u b ?_) ?_
    · intro hub
      exact hne2 ⟨c1.symm, hub.symm⟩
    · intro w hw
      rcases Yset_lost_cases hw with h | h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
      · exact hA w h _
      · exact hB w h _
      · exact hS w _ hc
      · exact absurd (c1.symm.trans h) hab.1
      · exact absurd (h.trans c1.symm) huv.1
      · exact absurd ⟨c1.symm, h.symm⟩ hne2
  · by_cases c2 : v = b
    · refine hbound (cod J u a) (hZ u a ?_) ?_
      · intro hua
        exact hne1 ⟨hua.symm, c2.symm⟩
      · intro w hw
        rcases Yset_lost_cases hw with h | h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
        · exact hA w h _
        · exact hB w h _
        · exact absurd h c1
        · exact hS w _ hc
        · exact absurd ⟨h.symm, c2.symm⟩ hne1
        · exact absurd (h.trans c2.symm) huv.1
    · by_cases c3 : u = a
      · refine hbound (cod J v b) (hZ v b c2) ?_
        intro w hw
        rcases Yset_lost_cases hw with h | h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
        · exact hA w h _
        · exact hB w h _
        · exact absurd h c1
        · exact absurd h c2
        · exact hS w _ hc
        · exact absurd (c3.symm.trans h) hab.1
      · by_cases c4 : u = b
        · refine hbound (cod J v a) (hZ v a c1) ?_
          intro w hw
          rcases Yset_lost_cases hw with h | h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
          · exact hA w h _
          · exact hB w h _
          · exact absurd h c1
          · exact absurd h c2
          · exact absurd h c3
          · exact hS w _ hc
        · refine hbound ∅ (by simp) ?_
          intro w hw
          rcases Yset_lost_cases hw with h | h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
          · exact hA w h _
          · exact hB w h _
          · exact absurd h c1
          · exact absurd h c2
          · exact absurd h c3
          · exact absurd h c4

/-- The open pair at `w ∈ Yset J u v` is open. -/
theorem partner_mem_openSet {J : Finset (Sym2 (Fin N))} {u v w : Fin N}
    (hw : w ∈ Yset J u v) : partner J u v w ∈ openSet J := by
  exact partner_mem_openSet_aux hw

/- ## Degrees and codegrees -/

theorem card_nb_insert_le (J : Finset (Sym2 (Fin N))) (e : Sym2 (Fin N)) (u : Fin N) :
    (nb (insert e J) u).card ≤ (nb J u).card + 1 := by
  classical
  by_cases h : ∃ w0, s(u, w0) = e
  · obtain ⟨w0, rfl⟩ := h
    have hsub : nb (insert s(u, w0) J) u ⊆ insert w0 (nb J u) := by
      intro w hw
      rw [mem_insert, mem_nb]
      rcases mem_insert.mp (mem_nb.mp hw) with hw' | hw'
      · left
        rcases Sym2.eq_iff.mp hw' with ⟨-, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact h2.trans h1
      · exact Or.inr hw'
    exact (card_le_card hsub).trans (card_insert_le _ _)
  · have hsub : nb (insert e J) u ⊆ nb J u := by
      intro w hw
      rw [mem_nb]
      rcases mem_insert.mp (mem_nb.mp hw) with hw' | hw'
      · exact absurd ⟨w, hw'⟩ h
      · exact hw'
    exact (card_le_card hsub).trans (Nat.le_succ _)

open Classical in
theorem card_filter_nb_ne_le (J : Finset (Sym2 (Fin N))) (u : Fin N) :
    ((openSet J).filter fun e => (nb (insert e J) u).card ≠ (nb J u).card).card ≤ N := by
  have hsub : ((openSet J).filter fun e => (nb (insert e J) u).card ≠ (nb J u).card) ⊆
      (univ : Finset (Fin N)).image (fun w => s(u, w)) := by
    intro e he
    by_contra hcon
    apply (mem_filter.mp he).2
    congr 1
    ext w
    simp only [mem_nb, mem_insert]
    constructor
    · rintro (h | h)
      · exact absurd (mem_image.mpr ⟨w, mem_univ _, h⟩) hcon
      · exact h
    · exact fun h => Or.inr h
  calc ((openSet J).filter fun e => (nb (insert e J) u).card ≠ (nb J u).card).card
      ≤ ((univ : Finset (Fin N)).image (fun w => s(u, w))).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin N)).card := card_image_le
    _ = N := by rw [card_univ, Fintype.card_fin]

theorem card_cod_insert_le {J : Finset (Sym2 (Fin N))} (hJ : TF J) {e : Sym2 (Fin N)}
    (_he : e ∈ openSet J) {u v : Fin N} (huv : u ≠ v) :
    (cod (insert e J) u v).card ≤ (cod J u v).card + 1 := by
  classical
  have hloop := tf_not_loop hJ
  have hnew : ∀ w ∈ cod (insert e J) u v \ cod J u v,
      (s(u, w) = e ∧ s(v, w) ∈ J) ∨ (s(u, w) ∈ J ∧ s(v, w) = e) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_sdiff.mp hw
    obtain ⟨h1, h2⟩ := mem_cod.mp hw1
    rcases mem_insert.mp h1 with h1 | h1 <;> rcases mem_insert.mp h2 with h2 | h2
    · exfalso
      rcases Sym2.eq_iff.mp (h1.trans h2.symm) with ⟨h, -⟩ | ⟨h, h'⟩
      · exact huv h
      · exact huv (h.trans h')
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (mem_cod.mpr ⟨h1, h2⟩) hw2
  have hone : (cod (insert e J) u v \ cod J u v).card ≤ 1 := by
    rw [card_le_one]
    intro w1 hw1 w2 hw2
    rcases hnew w1 hw1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases hnew w2 hw2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · rcases Sym2.eq_iff.mp (a1.trans a2.symm) with ⟨-, h⟩ | ⟨h, h'⟩
      · exact h
      · exact h'.trans h
    · exfalso
      rcases Sym2.eq_iff.mp (a1.trans b2.symm) with ⟨h, -⟩ | ⟨-, h⟩
      · exact huv h
      · rw [h] at b1
        exact hloop _ b1
    · exfalso
      rcases Sym2.eq_iff.mp (b1.trans a2.symm) with ⟨h, -⟩ | ⟨-, h⟩
      · exact huv h.symm
      · rw [h] at a1
        exact hloop _ a1
    · rcases Sym2.eq_iff.mp (b1.trans b2.symm) with ⟨-, h⟩ | ⟨h, h'⟩
      · exact h
      · exact h'.trans h
  have h3 := card_le_card_sdiff_add_card (s := cod (insert e J) u v) (t := cod J u v)
  omega

open Classical in
theorem card_filter_cod_ne_le {J : Finset (Sym2 (Fin N))} (_hJ : TF J) {u v : Fin N}
    (huv : u ≠ v) :
    ((openSet J).filter fun e => (cod (insert e J) u v).card ≠ (cod J u v).card).card
      ≤ (nb J u).card + (nb J v).card := by
  have hsub : ((openSet J).filter fun e => (cod (insert e J) u v).card ≠ (cod J u v).card) ⊆
      (nb J u).image (fun w => s(v, w)) ∪ (nb J v).image (fun w => s(u, w)) := by
    intro e he
    by_contra hcon
    apply (mem_filter.mp he).2
    congr 1
    ext w
    simp only [mem_cod, mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exfalso
        rcases Sym2.eq_iff.mp (h1.trans h2.symm) with ⟨h, -⟩ | ⟨h, h'⟩
        · exact huv h
        · exact huv (h.trans h')
      · exfalso
        exact hcon (mem_union_right _ (mem_image.mpr ⟨w, mem_nb.mpr h2, h1⟩))
      · exfalso
        exact hcon (mem_union_left _ (mem_image.mpr ⟨w, mem_nb.mpr h1, h2⟩))
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, Or.inr h2⟩
  exact (card_le_card hsub).trans
    ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))

/- ## A fixed set `W` of pairs -/

/-- Exact loss of open pairs of `W`. -/
theorem sum_W_lost {J : Finset (Sym2 (Fin N))} (hJ : TF J) (W : Finset (Sym2 (Fin N))) :
    ∑ e ∈ openSet J, ((W ∩ openSet J) \ (W ∩ openSet (insert e J))).card
      = ∑ f ∈ W ∩ openSet J, (1 + Ys J f) := by
  classical
  have h1 : ∀ e, (W ∩ openSet J) \ (W ∩ openSet (insert e J))
      = (W ∩ openSet J).filter (fun f => f ∉ openSet (insert e J)) := by
    intro e
    ext f
    simp only [mem_sdiff, mem_inter, mem_filter]
    tauto
  calc ∑ e ∈ openSet J, ((W ∩ openSet J) \ (W ∩ openSet (insert e J))).card
      = ∑ e ∈ openSet J, ((W ∩ openSet J).filter (fun f => f ∉ openSet (insert e J))).card :=
        sum_congr rfl fun e _ => by rw [h1 e]
    _ = ∑ f ∈ W ∩ openSet J, ((openSet J).filter (fun e => f ∉ openSet (insert e J))).card :=
        sum_card_filter_comm (openSet J) (W ∩ openSet J)
          (fun e f => f ∉ openSet (insert e J))
    _ = ∑ f ∈ W ∩ openSet J, (1 + Ys J f) :=
        sum_congr rfl fun f hf => card_filter_killers hJ (mem_inter.mp hf).2

theorem W_lost_card_le_Ys {J : Finset (Sym2 (Fin N))} (hJ : TF J) {a b : Fin N}
    (hab : Op J a b) (W : Finset (Sym2 (Fin N))) :
    ((W ∩ openSet J) \ (W ∩ openSet (insert s(a, b) J))).card ≤ 1 + (Yset J a b).card := by
  classical
  rw [← card_openSet_sdiff_insert hJ hab]
  apply card_le_card
  intro f hf
  simp only [mem_sdiff, mem_inter] at hf ⊢
  exact ⟨hf.1.2, fun h => hf.2 ⟨hf.1.1, h⟩⟩

open Classical in
theorem W_lost_card_le {J : Finset (Sym2 (Fin N))} (_hJ : TF J) {a b : Fin N}
    (hab : Op J a b) (W : Finset (Sym2 (Fin N))) :
    ((W ∩ openSet J) \ (W ∩ openSet (insert s(a, b) J))).card
      ≤ (if s(a, b) ∈ W then 1 else 0)
        + (univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card
        + (univ.filter fun x : Fin N => s(b, x) ∈ W ∧ s(x, a) ∈ J).card := by
  have hsub : (W ∩ openSet J) \ (W ∩ openSet (insert s(a, b) J)) ⊆
      ((if s(a, b) ∈ W then ({s(a, b)} : Finset (Sym2 (Fin N))) else ∅) ∪
        (univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).image (fun x => s(a, x))) ∪
        (univ.filter fun x : Fin N => s(b, x) ∈ W ∧ s(x, a) ∈ J).image (fun x => s(b, x)) := by
    intro f hf
    simp only [mem_sdiff, mem_inter] at hf
    obtain ⟨⟨hfW, hfO⟩, hfn⟩ := hf
    have hfn' : f ∉ openSet (insert s(a, b) J) := fun h => hfn ⟨hfW, h⟩
    rcases (not_mem_openSet_insert_iff hab hfO).mp hfn' with rfl | ⟨z, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩
    · apply mem_union_left
      apply mem_union_left
      rw [if_pos hfW]
      exact mem_singleton_self _
    · apply mem_union_left
      apply mem_union_right
      exact mem_image.mpr ⟨z, mem_filter.mpr ⟨mem_univ _, hfW, sym2_mem_swap h2⟩, rfl⟩
    · apply mem_union_right
      exact mem_image.mpr ⟨z, mem_filter.mpr ⟨mem_univ _, hfW, sym2_mem_swap h2⟩, rfl⟩
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  refine add_le_add ((card_union_le _ _).trans (add_le_add ?_ card_image_le)) card_image_le
  split_ifs <;> simp

theorem openSet_insert_subset {J : Finset (Sym2 (Fin N))} (e : Sym2 (Fin N)) :
    openSet (insert e J) ⊆ openSet J := by
  exact openSet_insert_subset_aux J e

end TFP
end E1182

end StepPart

section MartRealPart

/-
# Real-number lemmas for the supermartingale estimates

* `sum_exp_le`: the basic exponential-moment inequality.
* `xdrift_up`, `xdrift_down`, `ydrift_up`, `ydrift_down`: the drift of `X` and `Y` at a state whose
  counts are within the allowed errors is within `DX`, `DY` of the drift of the trajectory.
-/

open Finset

namespace E1182
namespace TFP

/-- `exp z ≤ 1 + z + z²` for `z ≤ 1`. -/
theorem exp_le_quad {z : ℝ} (hz : z ≤ 1) : Real.exp z ≤ 1 + z + z ^ 2 := by
  by_cases h : -1 ≤ z
  · have h1 : |z| ≤ 1 := abs_le.mpr ⟨h, hz⟩
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 := (abs_le.mp h2).2
    linarith
  · push Not at h
    have h1 : Real.exp z ≤ Real.exp (-1) := Real.exp_le_exp.mpr h.le
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      have h3 := Real.add_one_le_exp 1
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    nlinarith [sq_nonneg (z + 1 / 2)]

/-- Exponential-moment inequality: if the increments `z e` (over a set `O` of equally likely
outcomes) have nonpositive sum and second moment at most `V`, then the average of `exp (z e)`
over any subset `T` on which `z ≤ 1` is at most `exp V`. -/
theorem sum_exp_le {ι : Type*} (O T : Finset ι) (z : ι → ℝ) (V : ℝ) (hT : T ⊆ O)
    (hz : ∀ e ∈ T, z e ≤ 1) (hdrift : ∑ e ∈ O, z e ≤ 0)
    (hvar : ∑ e ∈ O, z e ^ 2 ≤ O.card * V) :
    ∑ e ∈ T, Real.exp (z e) ≤ O.card * Real.exp V := by
  have h1 : ∑ e ∈ T, Real.exp (z e) ≤ ∑ e ∈ T, (1 + z e + z e ^ 2) :=
    sum_le_sum fun e he => exp_le_quad (hz e he)
  have h2 : ∑ e ∈ T, (1 + z e + z e ^ 2) ≤ ∑ e ∈ O, (1 + z e + z e ^ 2) := by
    refine sum_le_sum_of_subset_of_nonneg hT fun e _ _ => ?_
    nlinarith [sq_nonneg (z e + 1 / 2)]
  have h3 : ∑ e ∈ O, (1 + z e + z e ^ 2) = O.card + ∑ e ∈ O, z e + ∑ e ∈ O, z e ^ 2 := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
  have h4 : (O.card : ℝ) * (1 + V) ≤ O.card * Real.exp V := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have := Real.add_one_le_exp V
    linarith
  calc ∑ e ∈ T, Real.exp (z e) ≤ O.card + ∑ e ∈ O, z e + ∑ e ∈ O, z e ^ 2 := by
        rw [← h3]; exact h1.trans h2
    _ ≤ O.card * (1 + V) := by linarith
    _ ≤ O.card * Real.exp V := h4

/-- `exp z ≤ 1 + z + z² exp B` for `z ≤ B`, `0 ≤ B`. -/
theorem exp_le_quad' {z B : ℝ} (hB : 0 ≤ B) (hz : z ≤ B) :
    Real.exp z ≤ 1 + z + z ^ 2 * Real.exp B := by
  have hB1 : 1 ≤ Real.exp B := Real.one_le_exp hB
  by_cases h1 : z ≤ 1
  · have h2 := exp_le_quad h1
    have h3 : z ^ 2 * 1 ≤ z ^ 2 * Real.exp B := mul_le_mul_of_nonneg_left hB1 (sq_nonneg z)
    linarith
  · push Not at h1
    have h2 : Real.exp z ≤ Real.exp B := Real.exp_le_exp.mpr hz
    have h3 : 1 * Real.exp B ≤ z ^ 2 * Real.exp B :=
      mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos B).le
    linarith

/-- Exponential-moment inequality with a large upper bound `B` on the increments. -/
theorem sum_exp_le' {ι : Type*} (O T : Finset ι) (z : ι → ℝ) (V B : ℝ) (hT : T ⊆ O)
    (hB : 0 ≤ B) (hz : ∀ e ∈ T, z e ≤ B) (hdrift : ∑ e ∈ O, z e ≤ 0)
    (hvar : ∑ e ∈ O, z e ^ 2 ≤ O.card * V) :
    ∑ e ∈ T, Real.exp (z e) ≤ O.card * Real.exp (Real.exp B * V) := by
  have hB1 : 1 ≤ Real.exp B := Real.one_le_exp hB
  have h1 : ∑ e ∈ T, Real.exp (z e) ≤ ∑ e ∈ T, (1 + z e + z e ^ 2 * Real.exp B) :=
    sum_le_sum fun e he => exp_le_quad' hB (hz e he)
  have h2 : ∑ e ∈ T, (1 + z e + z e ^ 2 * Real.exp B)
      ≤ ∑ e ∈ O, (1 + z e + z e ^ 2 * Real.exp B) := by
    refine sum_le_sum_of_subset_of_nonneg hT fun e _ _ => ?_
    have h3 : z e ^ 2 * 1 ≤ z e ^ 2 * Real.exp B :=
      mul_le_mul_of_nonneg_left hB1 (sq_nonneg (z e))
    nlinarith [sq_nonneg (z e + 1 / 2)]
  have h3 : ∑ e ∈ O, (1 + z e + z e ^ 2 * Real.exp B)
      = O.card + ∑ e ∈ O, z e + (∑ e ∈ O, z e ^ 2) * Real.exp B := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, sum_mul]
  have h4 : (∑ e ∈ O, z e ^ 2) * Real.exp B ≤ O.card * V * Real.exp B :=
    mul_le_mul_of_nonneg_right hvar (Real.exp_pos B).le
  have h5 : (O.card : ℝ) * (1 + Real.exp B * V) ≤ O.card * Real.exp (Real.exp B * V) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have := Real.add_one_le_exp (Real.exp B * V)
    linarith
  calc ∑ e ∈ T, Real.exp (z e)
      ≤ O.card + ∑ e ∈ O, z e + (∑ e ∈ O, z e ^ 2) * Real.exp B := by
        rw [← h3]; exact h1.trans h2
    _ ≤ O.card * (1 + Real.exp B * V) := by nlinarith
    _ ≤ O.card * Real.exp (Real.exp B * V) := h5

/-- **Bennett-type step for a decreasing count.** `loss e ≥ 0` is the loss of the count `X` under
the outcome `e`; the mean loss is between `alow * X` and `abar * X`; `gp > 0` is the next
normalisation. -/
theorem bennett_step {ι : Type*} (O : Finset ι) (loss : ι → ℝ) {X abar alow gp lam B S2 V : ℝ}
    (hX : 0 ≤ X) (halow : 0 ≤ alow) (hab : alow ≤ abar) (hgp : 0 < gp) (hlam : 0 ≤ lam)
    (hB : 0 ≤ B)
    (hlo : O.card * alow * X ≤ ∑ e ∈ O, loss e) (hhi : ∑ e ∈ O, loss e ≤ O.card * abar * X)
    (hS2 : ∑ e ∈ O, loss e ^ 2 ≤ S2)
    (hb : ∀ e ∈ O, lam * (loss e / gp) ≤ B)
    (hV : (S2 + O.card * abar * (abar - alow) * X ^ 2) / gp ^ 2 ≤ O.card * V) :
    ∑ e ∈ O, Real.exp (lam * ((loss e - abar * X) / gp))
      ≤ O.card * Real.exp (Real.exp B * (lam ^ 2 * V)) := by
  have habar : 0 ≤ abar := le_trans halow hab
  refine sum_exp_le' O O (fun e => lam * ((loss e - abar * X) / gp)) (lam ^ 2 * V) B
    (Subset.refl _) hB ?_ ?_ ?_
  · intro e he
    have h1 : (loss e - abar * X) / gp ≤ loss e / gp := by
      apply div_le_div_of_nonneg_right _ hgp.le
      have := mul_nonneg habar hX
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left h1 hlam) (hb e he)
  · rw [← mul_sum, ← sum_div, sum_sub_distrib, sum_const, nsmul_eq_mul]
    apply mul_nonpos_of_nonneg_of_nonpos hlam
    apply div_nonpos_of_nonpos_of_nonneg _ hgp.le
    linarith
  · have h1 : ∑ e ∈ O, (lam * ((loss e - abar * X) / gp)) ^ 2
        = lam ^ 2 / gp ^ 2 * ∑ e ∈ O, (loss e - abar * X) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun e _ => ?_
      field_simp
    have h2 : ∑ e ∈ O, (loss e - abar * X) ^ 2
        = ∑ e ∈ O, loss e ^ 2 - 2 * (abar * X) * ∑ e ∈ O, loss e + O.card * (abar * X) ^ 2 := by
      have h3 : ∀ e ∈ O, (loss e - abar * X) ^ 2
          = loss e ^ 2 - 2 * (abar * X) * loss e + (abar * X) ^ 2 := fun e _ => by ring
      rw [sum_congr rfl h3, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    have h3 : ∑ e ∈ O, (loss e - abar * X) ^ 2
        ≤ S2 + O.card * abar * (abar - alow) * X ^ 2 := by
      rw [h2]
      have h4 : 2 * (abar * X) * (O.card * alow * X) ≤ 2 * (abar * X) * ∑ e ∈ O, loss e :=
        mul_le_mul_of_nonneg_left hlo (by have := mul_nonneg habar hX; linarith)
      have h5 : 0 ≤ (O.card : ℝ) * abar * alow * X ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) habar) halow) (sq_nonneg X)
      nlinarith
    have h4 : 0 ≤ lam ^ 2 / gp ^ 2 := div_nonneg (sq_nonneg lam) (sq_nonneg gp)
    calc ∑ e ∈ O, (lam * ((loss e - abar * X) / gp)) ^ 2
        = lam ^ 2 / gp ^ 2 * ∑ e ∈ O, (loss e - abar * X) ^ 2 := h1
      _ ≤ lam ^ 2 / gp ^ 2 * (S2 + O.card * abar * (abar - alow) * X ^ 2) :=
          mul_le_mul_of_nonneg_left h3 h4
      _ = lam ^ 2 * ((S2 + O.card * abar * (abar - alow) * X ^ 2) / gp ^ 2) := by
          field_simp
      _ ≤ lam ^ 2 * (O.card * V) := mul_le_mul_of_nonneg_left hV (sq_nonneg lam)
      _ = O.card * (lam ^ 2 * V) := by ring

/-- The drift allowance for `X`. -/
noncomputable def DXr (Qh xh yh eX eY eQ : ℝ) : ℝ :=
  (2 * (2 + 2 * yh) * eX + 8 * xh * eY + 8 * xh * (2 + 2 * yh) * (eQ / Qh)) / Qh

/-- The drift allowance for `Y`. -/
noncomputable def DYr (Qh xh yh eX eY eQ : ℝ) : ℝ :=
  (2 * eX + 8 * (eQ / Qh) * xh + eY * (1 + 2 * yh + eY)
    + 2 * (eQ / Qh) * (yh + eY) * (1 + yh + eY)) / Qh

section Drift

variable {Q Qh xh yh eX eY eQ : ℝ}

/-- Upper drift of `X`: `S` is the expected number of removed vertices times `Q`. -/
theorem xdrift_up (hQh : 0 < Qh) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Qh + eQ) (heQ : 0 ≤ eQ)
    (heX : 0 ≤ eX) (heXx : eX ≤ xh) (heY : 0 ≤ eY) (hyh : 0 ≤ yh)
    {S ym : ℝ} (hym0 : 0 ≤ ym) (hym : yh - eY ≤ ym) (hS : (xh - eX) * (2 + 2 * ym) ≤ S) :
    Q * (xh * (2 + 2 * yh) / Qh) - S ≤ Q * DXr Qh xh yh eX eY eQ := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = eQ / Qh := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg heQ hQh.le
  have heQκ : eQ = κ * Qh := by rw [hκ]; field_simp
  obtain ⟨A, hA⟩ : ∃ A, A = 2 + 2 * yh := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hxh : 0 ≤ xh := le_trans heX heXx
  -- `S ≥ S₁ ≥ 0` and `S₁ ≥ xh A - 2 xh eY - eX A`
  have hS1 : 0 ≤ (xh - eX) * (2 + 2 * ym) := mul_nonneg (by linarith) (by linarith)
  have hS2 : xh * A - 2 * xh * eY - eX * A ≤ (xh - eX) * (2 + 2 * ym) := by
    have h1 : (xh - eX) * (A - 2 * eY) ≤ (xh - eX) * (2 + 2 * ym) :=
      mul_le_mul_of_nonneg_left (by rw [hA]; linarith) (by linarith)
    nlinarith [mul_nonneg heX heY]
  -- `P = xh A - Qh DX`
  have hDX : Qh * DXr Qh xh yh eX eY eQ = 2 * A * eX + 8 * xh * eY + 8 * xh * A * κ := by
    rw [DXr, ← hκ, ← hA]
    field_simp
  obtain ⟨P, hP⟩ : ∃ P, P = xh * A - (2 * A * eX + 8 * xh * eY + 8 * xh * A * κ) := ⟨_, rfl⟩
  have hgoal : Q * P ≤ Qh * S := by
    by_cases hP0 : P ≤ 0
    · have h1 : Q * P ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ0 hP0
      have h2 : 0 ≤ Qh * S := mul_nonneg hQh.le (le_trans hS1 hS)
      linarith
    · push Not at hP0
      have h1 : Q * P ≤ (Qh + eQ) * P := mul_le_mul_of_nonneg_right hQ hP0.le
      have h2 : (Qh + eQ) * P = Qh * ((1 + κ) * P) := by rw [heQκ]; ring
      have h3 : (1 + κ) * P ≤ xh * A - 2 * xh * eY - eX * A := by
        have h4 : κ * P ≤ κ * (xh * A) := by
          apply mul_le_mul_of_nonneg_left _ hκ0
          rw [hP]
          have := mul_nonneg hA0 heX
          have := mul_nonneg hxh heY
          have := mul_nonneg (mul_nonneg hxh hA0) hκ0
          linarith
        have h5 := mul_nonneg hA0 heX
        have h6 := mul_nonneg hxh heY
        have h7 := mul_nonneg (mul_nonneg hxh hA0) hκ0
        rw [hP] at h4 ⊢
        nlinarith
      have h4 : Qh * ((1 + κ) * P) ≤ Qh * S :=
        mul_le_mul_of_nonneg_left (h3.trans (hS2.trans hS)) hQh.le
      linarith
  -- translate back
  have h1 : Q * (xh * (2 + 2 * yh) / Qh) - Q * DXr Qh xh yh eX eY eQ = Q * P / Qh := by
    have h2 : DXr Qh xh yh eX eY eQ = (2 * A * eX + 8 * xh * eY + 8 * xh * A * κ) / Qh := by
      rw [← hDX]; field_simp
    rw [h2, hP, ← hA]
    field_simp
  have h2 : Q * P / Qh ≤ S := by
    rw [div_le_iff₀ hQh]
    linarith
  linarith

/-- Lower drift of `X`. -/
theorem xdrift_down (hQh : 0 < Qh) (hQ : Qh - eQ ≤ Q) (heQ : 0 ≤ eQ) (heQ2 : 2 * eQ ≤ Qh)
    (heX : 0 ≤ eX) (heXx : eX ≤ xh) (heY : 0 ≤ eY) (hyh : 0 ≤ yh)
    {S : ℝ} (hS : S ≤ (xh + eX) * (2 + 2 * (yh + eY))) :
    S - Q * (xh * (2 + 2 * yh) / Qh) ≤ Q * DXr Qh xh yh eX eY eQ := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = eQ / Qh := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg heQ hQh.le
  have hκ2 : κ ≤ 1 / 2 := by rw [hκ, div_le_iff₀ hQh]; linarith
  have heQκ : eQ = κ * Qh := by rw [hκ]; field_simp
  obtain ⟨A, hA⟩ : ∃ A, A = 2 + 2 * yh := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hxh : 0 ≤ xh := le_trans heX heXx
  have hDX : Qh * DXr Qh xh yh eX eY eQ = 2 * A * eX + 8 * xh * eY + 8 * xh * A * κ := by
    rw [DXr, ← hκ, ← hA]
    field_simp
  obtain ⟨T, hT⟩ : ∃ T, T = xh * A + (2 * A * eX + 8 * xh * eY + 8 * xh * A * κ) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    have := mul_nonneg hxh hA0
    have := mul_nonneg hA0 heX
    have := mul_nonneg hxh heY
    have := mul_nonneg (mul_nonneg hxh hA0) hκ0
    linarith
  -- `S ≤ xh A + eX A + 4 xh eY ≤ (1 - κ) T`
  have hS' : S ≤ xh * A + eX * A + 4 * xh * eY := by
    have h1 : (xh + eX) * (2 + 2 * (yh + eY)) = xh * A + eX * A + 2 * xh * eY + 2 * eX * eY := by
      rw [hA]; ring
    have h2 : 2 * eX * eY ≤ 2 * xh * eY := by
      have := mul_le_mul_of_nonneg_right heXx heY
      linarith
    linarith
  have hκT : κ * T ≤ A * eX + 4 * xh * eY + 5 * (xh * A * κ) := by
    have h5 := mul_nonneg hA0 heX
    have h6 := mul_nonneg hxh heY
    have h7 := mul_nonneg (mul_nonneg hxh hA0) hκ0
    have h8 : κ * (2 * A * eX) ≤ A * eX := by nlinarith
    have h9 : κ * (8 * xh * eY) ≤ 4 * xh * eY := by nlinarith
    have h10 : κ * (8 * xh * A * κ) ≤ 4 * (xh * A * κ) := by nlinarith
    rw [hT]
    nlinarith
  have hgoal : Qh * S ≤ Q * T := by
    have h1 : (Qh - eQ) * T ≤ Q * T := mul_le_mul_of_nonneg_right hQ hT0
    have h2 : (Qh - eQ) * T = Qh * (T - κ * T) := by rw [heQκ]; ring
    have h3 : S ≤ T - κ * T := by
      have h7 := mul_nonneg (mul_nonneg hxh hA0) hκ0
      rw [hT] at hκT ⊢
      linarith
    have h4 : Qh * S ≤ Qh * (T - κ * T) := mul_le_mul_of_nonneg_left h3 hQh.le
    linarith
  have h1 : Q * (xh * (2 + 2 * yh) / Qh) + Q * DXr Qh xh yh eX eY eQ = Q * T / Qh := by
    have h2 : DXr Qh xh yh eX eY eQ = (2 * A * eX + 8 * xh * eY + 8 * xh * A * κ) / Qh := by
      rw [← hDX]; field_simp
    rw [h2, hT, ← hA]
    field_simp
  have h2 : S ≤ Q * T / Qh := by
    rw [le_div_iff₀ hQh]
    linarith
  linarith

/-- `ym (1 + ym) ≥ yh (1 + yh) - eY (1 + 2 yh)` when `ym ≥ max (yh - eY) 0`. -/
theorem ylow_aux (heY : 0 ≤ eY) (hyh : 0 ≤ yh) {ym : ℝ} (hym0 : 0 ≤ ym) (hym : yh - eY ≤ ym) :
    yh * (1 + yh) - eY * (1 + 2 * yh) ≤ ym * (1 + ym) := by
  by_cases h : eY ≤ yh
  · have h1 : (yh - eY) * (1 + (yh - eY)) ≤ ym * (1 + ym) := by
      have h2 : 0 ≤ yh - eY := by linarith
      nlinarith
    nlinarith [sq_nonneg eY]
  · push Not at h
    have h1 : 0 ≤ ym * (1 + ym) := mul_nonneg hym0 (by linarith)
    nlinarith

/-- Upper drift of `Y`: `G` is the expected gain times `Q`, `Lo` the expected loss times `Q`. -/
theorem ydrift_up (hQh : 0 < Qh) (hQlo : Qh - eQ ≤ Q) (hQ : Q ≤ Qh + eQ) (heQ : 0 ≤ eQ)
    (heQ2 : 2 * eQ ≤ Qh) (heX : 0 ≤ eX) (heXx : eX ≤ xh) (heY : 0 ≤ eY) (hyh : 0 ≤ yh)
    {G Lo ym : ℝ} (hG : G ≤ 2 * (xh + eX)) (hym0 : 0 ≤ ym) (hym : yh - eY ≤ ym)
    (hLo : ym * (1 + ym) ≤ Lo) :
    (G - Lo) - Q * ((2 * xh - yh * (1 + yh)) / Qh) ≤ Q * DYr Qh xh yh eX eY eQ := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = eQ / Qh := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg heQ hQh.le
  have hκ2 : κ ≤ 1 / 2 := by rw [hκ, div_le_iff₀ hQh]; linarith
  have heQκ : eQ = κ * Qh := by rw [hκ]; field_simp
  have hxh : 0 ≤ xh := le_trans heX heXx
  have hQ0 : 0 ≤ Q := by linarith
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = (yh + eY) * (1 + yh + eY) := ⟨_, rfl⟩
  have hL00 : 0 ≤ L0 := by rw [hL0]; exact mul_nonneg (by linarith) (by linarith)
  have hL0y : yh * (1 + yh) ≤ L0 := by
    rw [hL0]; nlinarith [mul_nonneg heY hyh, sq_nonneg eY]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = 2 * xh + 2 * eX + 8 * κ * xh := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ Rm, Rm = yh * (1 + yh) - eY * (1 + 2 * yh + eY) - 2 * κ * L0 := ⟨_, rfl⟩
  have hLo0 : 0 ≤ Lo := le_trans (mul_nonneg hym0 (by linarith)) hLo
  have hLo' : yh * (1 + yh) - eY * (1 + 2 * yh) ≤ Lo := (ylow_aux heY hyh hym0 hym).trans hLo
  have hDY : Qh * DYr Qh xh yh eX eY eQ
      = 2 * eX + 8 * κ * xh + eY * (1 + 2 * yh + eY) + 2 * κ * L0 := by
    rw [DYr, ← hκ, hL0]
    field_simp
  -- step 1: `Qh G ≤ Q Rp`
  have hRp0 : 0 ≤ Rp := by
    rw [hRp]
    have := mul_nonneg hκ0 hxh
    linarith
  have h1 : Qh * G ≤ Q * Rp := by
    have h2 : (Qh - eQ) * Rp ≤ Q * Rp := mul_le_mul_of_nonneg_right hQlo hRp0
    have h3 : (Qh - eQ) * Rp = Qh * ((1 - κ) * Rp) := by rw [heQκ]; ring
    have h4 : 2 * xh + 2 * eX ≤ (1 - κ) * Rp := by
      rw [hRp]
      have h5 := mul_nonneg hκ0 hxh
      have h6 : κ * eX ≤ κ * xh := mul_le_mul_of_nonneg_left heXx hκ0
      have h7 : κ * (κ * xh) ≤ 1 / 2 * (κ * xh) := mul_le_mul_of_nonneg_right hκ2 h5
      nlinarith
    have h5 : Qh * G ≤ Qh * ((1 - κ) * Rp) := mul_le_mul_of_nonneg_left (hG.trans (by linarith)) hQh.le
    linarith
  -- step 2: `Q Rm ≤ Qh Lo`
  have h2 : Q * Rm ≤ Qh * Lo := by
    by_cases hRm0 : Rm ≤ 0
    · have := mul_nonpos_of_nonneg_of_nonpos hQ0 hRm0
      have := mul_nonneg hQh.le hLo0
      linarith
    · push Not at hRm0
      have h3 : Q * Rm ≤ (Qh + eQ) * Rm := mul_le_mul_of_nonneg_right hQ hRm0.le
      have h4 : (Qh + eQ) * Rm = Qh * ((1 + κ) * Rm) := by rw [heQκ]; ring
      have h5 : (1 + κ) * Rm ≤ yh * (1 + yh) - eY * (1 + 2 * yh) := by
        have h6 : κ * Rm ≤ κ * L0 := by
          apply mul_le_mul_of_nonneg_left _ hκ0
          rw [hRm]
          have := mul_nonneg hκ0 hL00
          have := mul_nonneg heY (by linarith : 0 ≤ 1 + 2 * yh + eY)
          linarith
        have h7 := mul_nonneg hκ0 hL00
        have h8 : 0 ≤ eY * eY := mul_nonneg heY heY
        rw [hRm] at h6 ⊢
        nlinarith
      have h6 : Qh * ((1 + κ) * Rm) ≤ Qh * Lo := mul_le_mul_of_nonneg_left (h5.trans hLo') hQh.le
      linarith
  have h3 : Q * ((2 * xh - yh * (1 + yh)) / Qh) + Q * DYr Qh xh yh eX eY eQ = Q * (Rp - Rm) / Qh := by
    have h4 : DYr Qh xh yh eX eY eQ
        = (2 * eX + 8 * κ * xh + eY * (1 + 2 * yh + eY) + 2 * κ * L0) / Qh := by
      rw [← hDY]; field_simp
    rw [h4, hRp, hRm]
    field_simp
    ring
  have h4 : G - Lo ≤ Q * (Rp - Rm) / Qh := by
    rw [le_div_iff₀ hQh]
    nlinarith
  linarith

/-- Lower drift of `Y`. -/
theorem ydrift_down (hQh : 0 < Qh) (hQlo : Qh - eQ ≤ Q) (hQ : Q ≤ Qh + eQ) (heQ : 0 ≤ eQ)
    (heQ2 : 2 * eQ ≤ Qh) (heX : 0 ≤ eX) (heXx : eX ≤ xh) (heY : 0 ≤ eY) (hyh : 0 ≤ yh)
    {G Lo : ℝ} (hG : 2 * (xh - eX) ≤ G) (hLo : Lo ≤ (yh + eY) * (1 + yh + eY)) :
    Q * ((2 * xh - yh * (1 + yh)) / Qh) - (G - Lo) ≤ Q * DYr Qh xh yh eX eY eQ := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = eQ / Qh := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg heQ hQh.le
  have hκ2 : κ ≤ 1 / 2 := by rw [hκ, div_le_iff₀ hQh]; linarith
  have heQκ : eQ = κ * Qh := by rw [hκ]; field_simp
  have hxh : 0 ≤ xh := le_trans heX heXx
  have hQ0 : 0 ≤ Q := by linarith
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = (yh + eY) * (1 + yh + eY) := ⟨_, rfl⟩
  have hL00 : 0 ≤ L0 := by rw [hL0]; exact mul_nonneg (by linarith) (by linarith)
  have hG0 : 0 ≤ G := le_trans (by linarith) hG
  rw [← hL0] at hLo
  have hDY : Qh * DYr Qh xh yh eX eY eQ
      = 2 * eX + 8 * κ * xh + eY * (1 + 2 * yh + eY) + 2 * κ * L0 := by
    rw [DYr, ← hκ, hL0]
    field_simp
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = 2 * xh - 2 * eX - 8 * κ * xh := ⟨_, rfl⟩
  -- step 1: `Q Rp ≤ Qh G`
  have h1 : Q * Rp ≤ Qh * G := by
    by_cases hRp0 : Rp ≤ 0
    · have := mul_nonpos_of_nonneg_of_nonpos hQ0 hRp0
      have := mul_nonneg hQh.le hG0
      linarith
    · push Not at hRp0
      have h3 : Q * Rp ≤ (Qh + eQ) * Rp := mul_le_mul_of_nonneg_right hQ hRp0.le
      have h4 : (Qh + eQ) * Rp = Qh * ((1 + κ) * Rp) := by rw [heQκ]; ring
      have h5 : (1 + κ) * Rp ≤ 2 * (xh - eX) := by
        have h6 := mul_nonneg hκ0 hxh
        have h7 := mul_nonneg hκ0 heX
        have h8 : 0 ≤ κ * (κ * xh) := mul_nonneg hκ0 h6
        rw [hRp]
        nlinarith
      have h6 : Qh * ((1 + κ) * Rp) ≤ Qh * G := mul_le_mul_of_nonneg_left (h5.trans hG) hQh.le
      linarith
  -- step 2: `Qh Lo ≤ Q (L0 + 2 κ L0)`
  have h2 : Qh * Lo ≤ Q * (L0 + 2 * κ * L0) := by
    have hR0 : 0 ≤ L0 + 2 * κ * L0 := by
      have := mul_nonneg hκ0 hL00
      linarith
    have h3 : (Qh - eQ) * (L0 + 2 * κ * L0) ≤ Q * (L0 + 2 * κ * L0) :=
      mul_le_mul_of_nonneg_right hQlo hR0
    have h4 : (Qh - eQ) * (L0 + 2 * κ * L0) = Qh * ((1 - κ) * (1 + 2 * κ) * L0) := by
      rw [heQκ]; ring
    have h5 : L0 ≤ (1 - κ) * (1 + 2 * κ) * L0 := by
      have h6 : 1 ≤ (1 - κ) * (1 + 2 * κ) := by nlinarith
      nlinarith
    have h6 : Qh * Lo ≤ Qh * ((1 - κ) * (1 + 2 * κ) * L0) :=
      mul_le_mul_of_nonneg_left (hLo.trans h5) hQh.le
    linarith
  have h3 : Q * ((2 * xh - yh * (1 + yh)) / Qh) - Q * DYr Qh xh yh eX eY eQ
      = Q * (Rp - (L0 + 2 * κ * L0)) / Qh := by
    have h4 : DYr Qh xh yh eX eY eQ
        = (2 * eX + 8 * κ * xh + eY * (1 + 2 * yh + eY) + 2 * κ * L0) / Qh := by
      rw [← hDY]; field_simp
    rw [h4, hRp, hL0]
    field_simp
    ring
  have h4 : Q * (Rp - (L0 + 2 * κ * L0)) / Qh ≤ G - Lo := by
    rw [div_le_iff₀ hQh]
    nlinarith
  linarith

end Drift

end TFP
end E1182

end MartRealPart

section MartPart

/-
# One-step exponential supermartingale inequalities for `X` and `Y`

`GoodAt J …` bundles the bounds satisfied by a good state. For an open pair `uv` we bound the
exponential moments of the one-step change of `X(u,v)` and `Y(u,v)` (minus the change of the
trajectory and the drift allowance), in both directions.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

/-- The bounds satisfied by a good state `J` at a step where the trajectory is `(Qh, xh, yh)` and
the allowed errors are `(eX, eY, eQ)`. -/
structure GoodAt (J : Finset (Sym2 (Fin N))) (Qh xh yh eX eY eQ Dm Zm : ℝ) : Prop where
  tf : TF J
  hQ : |((openSet J).card : ℝ) - Qh| ≤ eQ
  hX : ∀ a b, Op J a b → |((Xset J a b).card : ℝ) - xh| ≤ eX
  hY : ∀ a b, Op J a b → |((Yset J a b).card : ℝ) - yh| ≤ eY
  hD : ∀ a, ((nb J a).card : ℝ) ≤ Dm
  hZ : ∀ a b, a ≠ b → ((cod J a b).card : ℝ) ≤ Zm
  Qh_pos : 0 < Qh
  eQ0 : 0 ≤ eQ
  eQ2 : 2 * eQ ≤ Qh
  eX0 : 0 ≤ eX
  eXx : eX ≤ xh
  eY0 : 0 ≤ eY
  yh0 : 0 ≤ yh

theorem mXset_iff {J : Finset (Sym2 (Fin N))} {u v w : Fin N} :
    w ∈ Xset J u v ↔ Op J u w ∧ Op J v w := by
  classical
  simp [Xset]

theorem mYset_iff {J : Finset (Sym2 (Fin N))} {u v w : Fin N} :
    w ∈ Yset J u v ↔ (s(u, w) ∈ J ∧ Op J v w) ∨ (Op J u w ∧ s(v, w) ∈ J) := by
  classical
  simp [Yset]

section

variable {J : Finset (Sym2 (Fin N))} {Qh xh yh eX eY eQ Dm Zm : ℝ}

theorem GoodAt.Q_lower (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    Qh - eQ ≤ ((openSet J).card : ℝ) := by
  have := (abs_le.mp h.hQ).1
  linarith

theorem GoodAt.Q_upper (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    ((openSet J).card : ℝ) ≤ Qh + eQ := by
  have := (abs_le.mp h.hQ).2
  linarith

theorem GoodAt.Q_pos (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    0 < ((openSet J).card : ℝ) := by
  have h1 := h.Q_lower
  have h2 := h.eQ2
  have h3 := h.Qh_pos
  have h4 := h.eQ0
  linarith

theorem GoodAt.Q_ge_half (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    Qh / 2 ≤ ((openSet J).card : ℝ) := by
  have h1 := h.Q_lower
  have h2 := h.eQ2
  linarith

theorem GoodAt.Y_lower (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {a b : Fin N} (hab : Op J a b) :
    max (yh - eY) 0 ≤ ((Yset J a b).card : ℝ) := by
  have := (abs_le.mp (h.hY a b hab)).1
  exact max_le (by linarith) (Nat.cast_nonneg _)

theorem GoodAt.Y_upper (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {a b : Fin N} (hab : Op J a b) :
    ((Yset J a b).card : ℝ) ≤ yh + eY := by
  have := (abs_le.mp (h.hY a b hab)).2
  linarith

theorem GoodAt.X_lower (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {a b : Fin N} (hab : Op J a b) :
    xh - eX ≤ ((Xset J a b).card : ℝ) := by
  have := (abs_le.mp (h.hX a b hab)).1
  linarith

theorem GoodAt.X_upper (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {a b : Fin N} (hab : Op J a b) :
    ((Xset J a b).card : ℝ) ≤ xh + eX := by
  have := (abs_le.mp (h.hX a b hab)).2
  linarith

/-- The total number of removals `S = ∑_e r_e` (as a real number). -/
noncomputable def sumR (J : Finset (Sym2 (Fin N))) (u v : Fin N) : ℝ :=
  ∑ e ∈ openSet J, ((Xset J u v \ Xset (insert e J) u v).card : ℝ)

theorem GoodAt.sumR_eq (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    sumR J u v = ∑ w ∈ Xset J u v, (2 + ((Yset J u w).card : ℝ) + (Yset J v w).card) := by
  have h1 := sum_Xset_removed h.tf huv
  unfold sumR
  exact_mod_cast h1

theorem GoodAt.sumR_ge (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    (xh - eX) * (2 + 2 * max (yh - eY) 0) ≤ sumR J u v := by
  rw [h.sumR_eq huv]
  have h1 : ∑ _w ∈ Xset J u v, (2 + 2 * max (yh - eY) 0)
      ≤ ∑ w ∈ Xset J u v, (2 + ((Yset J u w).card : ℝ) + (Yset J v w).card) := by
    refine sum_le_sum fun w hw => ?_
    obtain ⟨h1, h2⟩ := mXset_iff.mp hw
    have := h.Y_lower h1
    have := h.Y_lower h2
    linarith
  rw [sum_const, nsmul_eq_mul] at h1
  have h2 : (0 : ℝ) ≤ 2 + 2 * max (yh - eY) 0 := by
    have := le_max_right (yh - eY) 0
    linarith
  have h3 := mul_le_mul_of_nonneg_right (h.X_lower huv) h2
  linarith

theorem GoodAt.sumR_le (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    sumR J u v ≤ (xh + eX) * (2 + 2 * (yh + eY)) := by
  rw [h.sumR_eq huv]
  have h1 : ∑ w ∈ Xset J u v, (2 + ((Yset J u w).card : ℝ) + (Yset J v w).card)
      ≤ ∑ _w ∈ Xset J u v, (2 + 2 * (yh + eY)) := by
    refine sum_le_sum fun w hw => ?_
    obtain ⟨h1, h2⟩ := mXset_iff.mp hw
    have := h.Y_upper h1
    have := h.Y_upper h2
    linarith
  rw [sum_const, nsmul_eq_mul] at h1
  have h2 : (0 : ℝ) ≤ 2 + 2 * (yh + eY) := by
    have := h.yh0
    have := h.eY0
    linarith
  have h3 := mul_le_mul_of_nonneg_right (h.X_upper huv) h2
  linarith

/-- One removal count is at most `2 + 2 Dm`. -/
theorem GoodAt.removed_le (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) (u v : Fin N)
    {e : Sym2 (Fin N)} (he : e ∈ openSet J) :
    ((Xset J u v \ Xset (insert e J) u v).card : ℝ) ≤ 2 + 2 * Dm := by
  classical
  obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_openSet he
  have h1 := card_le_card (Xset_removed_subset hab u v)
  have h2 : (insert a (insert b (nb J a ∪ nb J b))).card ≤ 2 + ((nb J a).card + (nb J b).card) := by
    calc (insert a (insert b (nb J a ∪ nb J b))).card
        ≤ (insert b (nb J a ∪ nb J b)).card + 1 := card_insert_le _ _
      _ ≤ ((nb J a ∪ nb J b).card + 1) + 1 := Nat.add_le_add_right (card_insert_le _ _) 1
      _ ≤ (((nb J a).card + (nb J b).card) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) 1) 1
      _ = 2 + ((nb J a).card + (nb J b).card) := by ring
  have h3 : ((Xset J u v \ Xset (insert s(a, b) J) u v).card : ℝ)
      ≤ 2 + (((nb J a).card : ℝ) + (nb J b).card) := by exact_mod_cast h1.trans h2
  have := h.hD a
  have := h.hD b
  linarith

theorem GoodAt.Dm_nonneg (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) (a : Fin N) : 0 ≤ Dm :=
  le_trans (Nat.cast_nonneg _) (h.hD a)

/-- Second moment of the removal counts. -/
theorem GoodAt.sum_removed_sq_le (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N}
    (huv : Op J u v) :
    ∑ e ∈ openSet J, ((Xset J u v \ Xset (insert e J) u v).card : ℝ) ^ 2
      ≤ (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) := by
  have h1 : ∑ e ∈ openSet J, ((Xset J u v \ Xset (insert e J) u v).card : ℝ) ^ 2
      ≤ ∑ e ∈ openSet J, (2 + 2 * Dm) * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) := by
    refine sum_le_sum fun e he => ?_
    have h2 := h.removed_le u v he
    have h3 : (0 : ℝ) ≤ ((Xset J u v \ Xset (insert e J) u v).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [← mul_sum] at h1
  have h2 : (0 : ℝ) ≤ 2 + 2 * Dm := by
    have := h.Dm_nonneg u
    linarith
  have h3 := mul_le_mul_of_nonneg_left (h.sumR_le huv) h2
  unfold sumR at h3
  linarith

/-- The change of `X` in one step. -/
theorem card_Xset_insert (J : Finset (Sym2 (Fin N))) (e : Sym2 (Fin N)) (u v : Fin N) :
    ((Xset (insert e J) u v).card : ℝ) - (Xset J u v).card
      = -((Xset J u v \ Xset (insert e J) u v).card : ℝ) := by
  have h1 := card_sdiff_add_card_eq_card (Xset_insert_subset J e u v)
  have h2 : (((Xset J u v \ Xset (insert e J) u v).card : ℝ)) + (Xset (insert e J) u v).card
      = (Xset J u v).card := by exact_mod_cast h1
  linarith

theorem GoodAt.xh_nonneg (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) : 0 ≤ xh :=
  le_trans h.eX0 h.eXx

theorem GoodAt.DXr_nonneg (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    0 ≤ DXr Qh xh yh eX eY eQ := by
  unfold DXr
  have h1 := h.xh_nonneg
  have h2 := h.yh0
  have h3 := h.eX0
  have h4 := h.eY0
  have h5 : 0 ≤ eQ / Qh := div_nonneg h.eQ0 h.Qh_pos.le
  apply div_nonneg _ h.Qh_pos.le
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (2 + 2 * yh)) h3
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) h1) h4
  have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) h1)
    (by linarith : (0 : ℝ) ≤ 2 + 2 * yh)) h5
  linarith

theorem GoodAt.c0_nonneg (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    0 ≤ xh * (2 + 2 * yh) / Qh := by
  have h1 := h.xh_nonneg
  have h2 := h.yh0
  exact div_nonneg (mul_nonneg h1 (by linarith)) h.Qh_pos.le

/-- Common bound for the second moment of the `X`-increments. -/
theorem GoodAt.X_var (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v)
    {vX c : ℝ} (hc : |c| ≤ xh * (2 + 2 * yh) / Qh + DXr Qh xh yh eX eY eQ)
    (hv : 4 * (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) / Qh
          + 2 * (xh * (2 + 2 * yh) / Qh + DXr Qh xh yh eX eY eQ) ^ 2 ≤ vX)
    (sgn : ℝ) (hsgn : sgn ^ 2 = 1) :
    ∑ e ∈ openSet J, (sgn * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) + c) ^ 2
      ≤ (openSet J).card * vX := by
  obtain ⟨B, hB⟩ : ∃ B, B = xh * (2 + 2 * yh) / Qh + DXr Qh xh yh eX eY eQ := ⟨_, rfl⟩
  rw [← hB] at hc hv
  have hB0 : 0 ≤ B := le_trans (abs_nonneg c) hc
  have hc2 : c ^ 2 ≤ B ^ 2 := by
    have := abs_le.mp hc
    nlinarith
  have h1 : ∑ e ∈ openSet J, (sgn * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) + c) ^ 2
      ≤ ∑ e ∈ openSet J, (2 * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) ^ 2 + 2 * B ^ 2) := by
    refine sum_le_sum fun e _ => ?_
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ((Xset J u v \ Xset (insert e J) u v).card : ℝ) := ⟨_, rfl⟩
    rw [← hr]
    have h2 : (sgn * r) ^ 2 = r ^ 2 := by rw [mul_pow, hsgn, one_mul]
    nlinarith [sq_nonneg (sgn * r - c)]
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h1
  have h2 := h.sum_removed_sq_le huv
  have hW0 : 0 ≤ (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) := by
    have := h.Dm_nonneg u
    have := h.xh_nonneg
    have := h.eX0
    have := h.yh0
    have := h.eY0
    exact mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  obtain ⟨Wv, hWv⟩ : ∃ Wv, Wv = (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) := ⟨_, rfl⟩
  rw [← hWv] at h2 hW0
  have hv' : 4 * Wv / Qh + 2 * B ^ 2 ≤ vX := by
    rw [hWv]
    have h3 : 4 * ((2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))))
        = 4 * (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) := by ring
    rw [h3]
    exact hv
  have hQ := h.Q_ge_half
  have hQh := h.Qh_pos
  -- `2 Wv ≤ Q * (4 Wv / Qh)`
  have h3 : 2 * Wv ≤ (openSet J).card * (4 * Wv / Qh) := by
    have h4 : (openSet J).card * (4 * Wv / Qh) = ((openSet J).card / Qh) * (4 * Wv) := by
      field_simp
    rw [h4]
    have h5 : (1 : ℝ) / 2 ≤ (openSet J).card / Qh := by
      rw [le_div_iff₀ hQh]
      linarith
    nlinarith
  have hQ0 : (0 : ℝ) ≤ (openSet J).card := Nat.cast_nonneg _
  calc ∑ e ∈ openSet J, (sgn * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) + c) ^ 2
      ≤ 2 * ∑ e ∈ openSet J, ((Xset J u v \ Xset (insert e J) u v).card : ℝ) ^ 2
          + (openSet J).card * (2 * B ^ 2) := h1
    _ ≤ 2 * Wv + (openSet J).card * (2 * B ^ 2) := by linarith
    _ ≤ (openSet J).card * (4 * Wv / Qh) + (openSet J).card * (2 * B ^ 2) := by linarith
    _ = (openSet J).card * (4 * Wv / Qh + 2 * B ^ 2) := by ring
    _ ≤ (openSet J).card * vX := mul_le_mul_of_nonneg_left hv' hQ0

/-- **Upper deviation of `X`**, one step. -/
theorem GoodAt.exp_X_up (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v)
    {lam vX : ℝ} (hlam : 0 ≤ lam) (hc : lam * (xh * (2 + 2 * yh) / Qh) ≤ 1)
    (hv : 4 * (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) / Qh
          + 2 * (xh * (2 + 2 * yh) / Qh + DXr Qh xh yh eX eY eQ) ^ 2 ≤ vX) :
    ∑ e ∈ openSet J, Real.exp (lam * ((((Xset (insert e J) u v).card : ℝ) - (Xset J u v).card)
        + xh * (2 + 2 * yh) / Qh - DXr Qh xh yh eX eY eQ))
      ≤ (openSet J).card * Real.exp (lam ^ 2 * vX) := by
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = xh * (2 + 2 * yh) / Qh := ⟨_, rfl⟩
  obtain ⟨DX, hDX⟩ : ∃ DX, DX = DXr Qh xh yh eX eY eQ := ⟨_, rfl⟩
  have hc00 : 0 ≤ c0 := by rw [hc0]; exact h.c0_nonneg
  have hDX0 : 0 ≤ DX := by rw [hDX]; exact h.DXr_nonneg
  rw [← hc0] at hc hv ⊢
  rw [← hDX] at hv ⊢
  have key := sum_exp_le (openSet J) (openSet J)
    (fun e => lam * (-((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (c0 - DX)))
    (lam ^ 2 * vX) (Subset.refl _) ?_ ?_ ?_
  · refine le_trans (le_of_eq (sum_congr rfl fun e _ => ?_)) key
    rw [card_Xset_insert]
    ring_nf
  · intro e _
    have h1 : (0 : ℝ) ≤ ((Xset J u v \ Xset (insert e J) u v).card : ℝ) := Nat.cast_nonneg _
    have h2 : -((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (c0 - DX) ≤ c0 := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hlam) hc
  · rw [← mul_sum, sum_add_distrib, sum_neg_distrib, sum_const, nsmul_eq_mul]
    have h1 := xdrift_up h.Qh_pos (Nat.cast_nonneg _) h.Q_upper h.eQ0 h.eX0 h.eXx h.eY0 h.yh0
      (le_max_right (yh - eY) 0) (le_max_left (yh - eY) 0) (h.sumR_ge huv)
    rw [← hc0, ← hDX] at h1
    unfold sumR at h1
    apply mul_nonpos_of_nonneg_of_nonpos hlam
    linarith
  · have h1 := h.X_var huv (c := c0 - DX) (vX := vX) (by
      rw [← hc0, ← hDX, abs_le]
      constructor <;> linarith) (by rw [← hc0, ← hDX]; exact hv) (-1) (by norm_num)
    calc ∑ e ∈ openSet J,
          (lam * (-((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (c0 - DX))) ^ 2
        = lam ^ 2 * ∑ e ∈ openSet J,
            (-1 * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (c0 - DX)) ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun e _ => by ring
      _ ≤ lam ^ 2 * ((openSet J).card * vX) := mul_le_mul_of_nonneg_left h1 (sq_nonneg lam)
      _ = (openSet J).card * (lam ^ 2 * vX) := by ring

/-- **Lower deviation of `X`**, one step. -/
theorem GoodAt.exp_X_down (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N}
    (huv : Op J u v) {lam vX : ℝ} (hlam : 0 ≤ lam) (hc : lam * (2 + 2 * Dm) ≤ 1)
    (hv : 4 * (2 + 2 * Dm) * ((xh + eX) * (2 + 2 * (yh + eY))) / Qh
          + 2 * (xh * (2 + 2 * yh) / Qh + DXr Qh xh yh eX eY eQ) ^ 2 ≤ vX) :
    ∑ e ∈ openSet J, Real.exp (lam * (-(((Xset (insert e J) u v).card : ℝ) - (Xset J u v).card)
        - xh * (2 + 2 * yh) / Qh - DXr Qh xh yh eX eY eQ))
      ≤ (openSet J).card * Real.exp (lam ^ 2 * vX) := by
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = xh * (2 + 2 * yh) / Qh := ⟨_, rfl⟩
  obtain ⟨DX, hDX⟩ : ∃ DX, DX = DXr Qh xh yh eX eY eQ := ⟨_, rfl⟩
  have hc00 : 0 ≤ c0 := by rw [hc0]; exact h.c0_nonneg
  have hDX0 : 0 ≤ DX := by rw [hDX]; exact h.DXr_nonneg
  rw [← hc0] at hv ⊢
  rw [← hDX] at hv ⊢
  have key := sum_exp_le (openSet J) (openSet J)
    (fun e => lam * (((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (-c0 - DX)))
    (lam ^ 2 * vX) (Subset.refl _) ?_ ?_ ?_
  · refine le_trans (le_of_eq (sum_congr rfl fun e _ => ?_)) key
    rw [card_Xset_insert]
    ring_nf
  · intro e he
    have h1 := h.removed_le u v he
    have h2 : ((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (-c0 - DX) ≤ 2 + 2 * Dm := by
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hlam) hc
  · rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
    have h1 := xdrift_down h.Qh_pos h.Q_lower h.eQ0 h.eQ2 h.eX0 h.eXx h.eY0 h.yh0
      (h.sumR_le huv)
    rw [← hc0, ← hDX] at h1
    unfold sumR at h1
    apply mul_nonpos_of_nonneg_of_nonpos hlam
    linarith
  · have h1 := h.X_var huv (c := -c0 - DX) (vX := vX) (by
      rw [← hc0, ← hDX, abs_le]
      constructor <;> linarith) (by rw [← hc0, ← hDX]; exact hv) 1 (by norm_num)
    calc ∑ e ∈ openSet J,
          (lam * (((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (-c0 - DX))) ^ 2
        = lam ^ 2 * ∑ e ∈ openSet J,
            (1 * ((Xset J u v \ Xset (insert e J) u v).card : ℝ) + (-c0 - DX)) ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun e _ => by ring
      _ ≤ lam ^ 2 * ((openSet J).card * vX) := mul_le_mul_of_nonneg_left h1 (sq_nonneg lam)
      _ = (openSet J).card * (lam ^ 2 * vX) := by ring

/- ## `Y` -/

theorem card_sub_card' {α : Type*} [DecidableEq α] (A B : Finset α) :
    (B.card : ℝ) - A.card = ((B \ A).card : ℝ) - (A \ B).card := by
  have h1 := card_sdiff_add_card_inter B A
  have h2 := card_sdiff_add_card_inter A B
  rw [inter_comm] at h2
  have h1' : (((B \ A).card : ℝ)) + (B ∩ A).card = B.card := by exact_mod_cast h1
  have h2' : (((A \ B).card : ℝ)) + (B ∩ A).card = A.card := by exact_mod_cast h2
  linarith

theorem GoodAt.DYr_nonneg (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) :
    0 ≤ DYr Qh xh yh eX eY eQ := by
  unfold DYr
  have h1 := h.xh_nonneg
  have h2 := h.yh0
  have h3 := h.eX0
  have h4 := h.eY0
  have h5 : 0 ≤ eQ / Qh := div_nonneg h.eQ0 h.Qh_pos.le
  apply div_nonneg _ h.Qh_pos.le
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) h5) h1
  have := mul_nonneg h4 (by linarith : (0 : ℝ) ≤ 1 + 2 * yh + eY)
  have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h5)
    (by linarith : (0 : ℝ) ≤ yh + eY)) (by linarith : (0 : ℝ) ≤ 1 + yh + eY)
  linarith

/-- Total gains and losses of `Y(u,v)` over all open choices (as real numbers). -/
noncomputable def sumG (J : Finset (Sym2 (Fin N))) (u v : Fin N) : ℝ :=
  ∑ e ∈ openSet J, ((Yset (insert e J) u v \ Yset J u v).card : ℝ)

noncomputable def sumL (J : Finset (Sym2 (Fin N))) (u v : Fin N) : ℝ :=
  ∑ e ∈ openSet J, ((Yset J u v \ Yset (insert e J) u v).card : ℝ)

theorem GoodAt.sumG_eq (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    sumG J u v = 2 * ((Xset J u v).card : ℝ) := by
  have h1 := sum_Yset_gained h.tf huv
  unfold sumG
  exact_mod_cast h1

theorem GoodAt.sumL_eq (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    sumL J u v = ∑ w ∈ Yset J u v, (1 + (Ys J (partner J u v w) : ℝ)) := by
  have h1 := sum_Yset_lost h.tf huv
  unfold sumL
  exact_mod_cast h1

theorem GoodAt.Ys_partner_bounds (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v w : Fin N}
    (hw : w ∈ Yset J u v) :
    max (yh - eY) 0 ≤ (Ys J (partner J u v w) : ℝ) ∧ (Ys J (partner J u v w) : ℝ) ≤ yh + eY := by
  obtain ⟨a, b, hab, hop⟩ := exists_of_mem_openSet (partner_mem_openSet hw)
  rw [hab, Ys_mk]
  exact ⟨h.Y_lower hop, h.Y_upper hop⟩

theorem GoodAt.sumL_ge (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    max (yh - eY) 0 * (1 + max (yh - eY) 0) ≤ sumL J u v := by
  rw [h.sumL_eq huv]
  have hm0 : (0 : ℝ) ≤ max (yh - eY) 0 := le_max_right _ _
  have h1 : ∑ _w ∈ Yset J u v, (1 + max (yh - eY) 0)
      ≤ ∑ w ∈ Yset J u v, (1 + (Ys J (partner J u v w) : ℝ)) := by
    refine sum_le_sum fun w hw => ?_
    have := (h.Ys_partner_bounds hw).1
    linarith
  rw [sum_const, nsmul_eq_mul] at h1
  have h3 := mul_le_mul_of_nonneg_right (h.Y_lower huv) (by linarith : (0 : ℝ) ≤ 1 + max (yh - eY) 0)
  linarith

theorem GoodAt.sumL_le (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    sumL J u v ≤ (yh + eY) * (1 + yh + eY) := by
  rw [h.sumL_eq huv]
  have h1 : ∑ w ∈ Yset J u v, (1 + (Ys J (partner J u v w) : ℝ))
      ≤ ∑ _w ∈ Yset J u v, (1 + (yh + eY)) := by
    refine sum_le_sum fun w hw => ?_
    have := (h.Ys_partner_bounds hw).2
    linarith
  rw [sum_const, nsmul_eq_mul] at h1
  have h2 : (0 : ℝ) ≤ 1 + (yh + eY) := by
    have := h.yh0
    have := h.eY0
    linarith
  have h3 := mul_le_mul_of_nonneg_right (h.Y_upper huv) h2
  nlinarith

theorem GoodAt.gained_le (_h : GoodAt J Qh xh yh eX eY eQ Dm Zm) (u v : Fin N)
    {e : Sym2 (Fin N)} (he : e ∈ openSet J) :
    ((Yset (insert e J) u v \ Yset J u v).card : ℝ) ≤ 2 := by
  obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_openSet he
  exact_mod_cast Yset_gained_card_le hab u v

theorem GoodAt.Zm_nonneg (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v) :
    0 ≤ Zm :=
  le_trans (Nat.cast_nonneg _) (h.hZ u v huv.1)

theorem GoodAt.lost_le (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v)
    {e : Sym2 (Fin N)} (he : e ∈ openSet J) (hne : e ≠ s(u, v)) :
    ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ≤ 2 + Zm := by
  obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_openSet he
  have hZ0 := h.Zm_nonneg huv
  have hZ : ∀ x y : Fin N, x ≠ y → (cod J x y).card ≤ ⌊Zm⌋₊ :=
    fun x y hxy => Nat.le_floor (h.hZ x y hxy)
  have h1 := Yset_lost_card_le h.tf hab huv hne hZ
  have h2 : ((Yset J u v \ Yset (insert s(a, b) J) u v).card : ℝ) ≤ 2 + (⌊Zm⌋₊ : ℝ) := by
    exact_mod_cast h1
  have h3 := Nat.floor_le hZ0
  linarith

theorem GoodAt.lost_le_Y (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v)
    (e : Sym2 (Fin N)) :
    ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ≤ yh + eY := by
  have h1 : ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ≤ (Yset J u v).card := by
    exact_mod_cast card_le_card sdiff_subset
  exact h1.trans (h.Y_upper huv)

/-- Second moment of the losses. -/
theorem GoodAt.sum_lost_sq_le (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N}
    (huv : Op J u v) :
    ∑ e ∈ openSet J, ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ^ 2
      ≤ (2 + Zm) * ((yh + eY) * (1 + yh + eY)) + (yh + eY) ^ 2 := by
  classical
  have hZ0 := h.Zm_nonneg huv
  have hmem : s(u, v) ∈ openSet J := mk_mem_openSet.mpr huv
  have hY0 : (0 : ℝ) ≤ yh + eY := by
    have := h.yh0
    have := h.eY0
    linarith
  have h1 : ∀ e ∈ openSet J, ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ^ 2
      ≤ (2 + Zm) * ((Yset J u v \ Yset (insert e J) u v).card : ℝ)
        + (if e = s(u, v) then (yh + eY) ^ 2 else 0) := by
    intro e he
    have h0 : (0 : ℝ) ≤ ((Yset J u v \ Yset (insert e J) u v).card : ℝ) := Nat.cast_nonneg _
    by_cases hne : e = s(u, v)
    · rw [if_pos hne]
      have h2 := h.lost_le_Y huv e
      have h3 : (0 : ℝ) ≤ (2 + Zm) * ((Yset J u v \ Yset (insert e J) u v).card : ℝ) :=
        mul_nonneg (by linarith) h0
      nlinarith
    · rw [if_neg hne, add_zero]
      have h2 := h.lost_le huv he hne
      nlinarith
  have h2 := sum_le_sum h1
  rw [sum_add_distrib, ← mul_sum, sum_ite_eq' (openSet J) s(u, v), if_pos hmem] at h2
  have h3 := mul_le_mul_of_nonneg_left (h.sumL_le huv) (by linarith : (0 : ℝ) ≤ 2 + Zm)
  unfold sumL at h3
  linarith

/-- Common bound for the second moment of the `Y`-increments. -/
theorem GoodAt.Y_var (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v)
    {vY c B : ℝ} (hc : |c| ≤ B)
    (hv : 2 * (12 * (xh + eX) + 3 * ((2 + Zm) * ((yh + eY) * (1 + yh + eY)) + (yh + eY) ^ 2)) / Qh
          + 3 * B ^ 2 ≤ vY)
    (sgn : ℝ) (hsgn : sgn ^ 2 = 1) :
    ∑ e ∈ openSet J, (sgn * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + c) ^ 2
      ≤ (openSet J).card * vY := by
  have hc2 : c ^ 2 ≤ B ^ 2 := by
    have := abs_le.mp hc
    have hB0 : 0 ≤ B := le_trans (abs_nonneg c) hc
    nlinarith
  have h1 : ∑ e ∈ openSet J, (sgn * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + c) ^ 2
      ≤ ∑ e ∈ openSet J, (6 * ((Yset (insert e J) u v \ Yset J u v).card : ℝ)
          + 3 * ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ^ 2 + 3 * B ^ 2) := by
    refine sum_le_sum fun e he => ?_
    obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ((Yset (insert e J) u v \ Yset J u v).card : ℝ) := ⟨_, rfl⟩
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = ((Yset J u v \ Yset (insert e J) u v).card : ℝ) := ⟨_, rfl⟩
    have hg2 : g ≤ 2 := by rw [hg]; exact h.gained_le u v he
    have hg0 : 0 ≤ g := by rw [hg]; exact Nat.cast_nonneg _
    rw [← hg, ← hl]
    have h2 : (sgn * (g - l) + c) ^ 2 ≤ 3 * g ^ 2 + 3 * l ^ 2 + 3 * c ^ 2 := by
      have h3 : (sgn * (g - l)) ^ 2 = (g - l) ^ 2 := by rw [mul_pow, hsgn, one_mul]
      nlinarith [sq_nonneg (sgn * (g - l) - c), sq_nonneg (g + l), sq_nonneg (sgn * g - c),
        sq_nonneg (sgn * l + c), sq_nonneg (g - l)]
    have h4 : g ^ 2 ≤ 2 * g := by nlinarith
    linarith
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul] at h1
  have hG : ∑ e ∈ openSet J, ((Yset (insert e J) u v \ Yset J u v).card : ℝ)
      ≤ 2 * (xh + eX) := by
    have h2 := h.sumG_eq huv
    unfold sumG at h2
    rw [h2]
    have := h.X_upper huv
    linarith
  have hL := h.sum_lost_sq_le huv
  obtain ⟨Wv, hWv⟩ : ∃ Wv, Wv = 12 * (xh + eX)
      + 3 * ((2 + Zm) * ((yh + eY) * (1 + yh + eY)) + (yh + eY) ^ 2) := ⟨_, rfl⟩
  rw [← hWv] at hv
  have hW0 : 0 ≤ Wv := by
    rw [hWv]
    have := h.xh_nonneg
    have := h.eX0
    have := h.yh0
    have := h.eY0
    have := h.Zm_nonneg huv
    have h5 : 0 ≤ (2 + Zm) * ((yh + eY) * (1 + yh + eY)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have h6 : 0 ≤ (yh + eY) ^ 2 := sq_nonneg _
    linarith
  have hQ := h.Q_ge_half
  have hQh := h.Qh_pos
  have h3 : Wv ≤ (openSet J).card * (2 * Wv / Qh) := by
    have h4 : (openSet J).card * (2 * Wv / Qh) = ((openSet J).card / Qh) * (2 * Wv) := by
      field_simp
    rw [h4]
    have h5 : (1 : ℝ) / 2 ≤ (openSet J).card / Qh := by
      rw [le_div_iff₀ hQh]
      linarith
    nlinarith
  have hQ0 : (0 : ℝ) ≤ (openSet J).card := Nat.cast_nonneg _
  calc ∑ e ∈ openSet J, (sgn * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + c) ^ 2
      ≤ 6 * ∑ e ∈ openSet J, ((Yset (insert e J) u v \ Yset J u v).card : ℝ)
          + 3 * ∑ e ∈ openSet J, ((Yset J u v \ Yset (insert e J) u v).card : ℝ) ^ 2
          + (openSet J).card * (3 * B ^ 2) := h1
    _ ≤ Wv + (openSet J).card * (3 * B ^ 2) := by rw [hWv]; linarith
    _ ≤ (openSet J).card * (2 * Wv / Qh) + (openSet J).card * (3 * B ^ 2) := by linarith
    _ = (openSet J).card * (2 * Wv / Qh + 3 * B ^ 2) := by ring
    _ ≤ (openSet J).card * vY := mul_le_mul_of_nonneg_left hv hQ0

/-- **Upper deviation of `Y`**, one step. -/
theorem GoodAt.exp_Y_up (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N} (huv : Op J u v)
    {lam vY : ℝ} (hlam : 0 ≤ lam)
    (hc : lam * (2 + |(2 * xh - yh * (1 + yh)) / Qh|) ≤ 1)
    (hv : 2 * (12 * (xh + eX) + 3 * ((2 + Zm) * ((yh + eY) * (1 + yh + eY)) + (yh + eY) ^ 2)) / Qh
          + 3 * (|(2 * xh - yh * (1 + yh)) / Qh| + DYr Qh xh yh eX eY eQ) ^ 2 ≤ vY) :
    ∑ e ∈ openSet J, Real.exp (lam * ((((Yset (insert e J) u v).card : ℝ) - (Yset J u v).card)
        - (2 * xh - yh * (1 + yh)) / Qh - DYr Qh xh yh eX eY eQ))
      ≤ (openSet J).card * Real.exp (lam ^ 2 * vY) := by
  classical
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = (2 * xh - yh * (1 + yh)) / Qh := ⟨_, rfl⟩
  obtain ⟨DY, hDY⟩ : ∃ DY, DY = DYr Qh xh yh eX eY eQ := ⟨_, rfl⟩
  have hDY0 : 0 ≤ DY := by rw [hDY]; exact h.DYr_nonneg
  rw [← hd0] at hc hv ⊢
  rw [← hDY] at hv ⊢
  have habs := abs_le.mp (le_refl |d0|)
  have key := sum_exp_le (openSet J) (openSet J)
    (fun e => lam * (1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + (-d0 - DY)))
    (lam ^ 2 * vY) (Subset.refl _) ?_ ?_ ?_
  · refine le_trans (le_of_eq (sum_congr rfl fun e _ => ?_)) key
    rw [card_sub_card' (Yset J u v) (Yset (insert e J) u v)]
    ring_nf
  · intro e he
    have h1 := h.gained_le u v he
    have h0 : (0 : ℝ) ≤ ((Yset J u v \ Yset (insert e J) u v).card : ℝ) := Nat.cast_nonneg _
    have h2 : 1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + (-d0 - DY) ≤ 2 + |d0| := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hlam) hc
  · rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    have hG : sumG J u v ≤ 2 * (xh + eX) := by
      rw [h.sumG_eq huv]
      have := h.X_upper huv
      linarith
    have h1 := ydrift_up h.Qh_pos h.Q_lower h.Q_upper h.eQ0 h.eQ2 h.eX0 h.eXx h.eY0 h.yh0 hG
      (le_max_right (yh - eY) 0) (le_max_left (yh - eY) 0) (h.sumL_ge huv)
    rw [← hd0, ← hDY] at h1
    unfold sumG sumL at h1
    apply mul_nonpos_of_nonneg_of_nonpos hlam
    linarith
  · have h1 := h.Y_var huv (c := -d0 - DY) (B := |d0| + DY) (vY := vY) (by
      rw [abs_le]
      constructor <;> linarith) hv 1 (by norm_num)
    calc ∑ e ∈ openSet J,
          (lam * (1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
            - (Yset J u v \ Yset (insert e J) u v).card) + (-d0 - DY))) ^ 2
        = lam ^ 2 * ∑ e ∈ openSet J,
            (1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
              - (Yset J u v \ Yset (insert e J) u v).card) + (-d0 - DY)) ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun e _ => by ring
      _ ≤ lam ^ 2 * ((openSet J).card * vY) := mul_le_mul_of_nonneg_left h1 (sq_nonneg lam)
      _ = (openSet J).card * (lam ^ 2 * vY) := by ring

/-- **Lower deviation of `Y`**, one step (the choice `e = uv` is excluded). -/
theorem GoodAt.exp_Y_down (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {u v : Fin N}
    (huv : Op J u v) {lam vY : ℝ} (hlam : 0 ≤ lam)
    (hc : lam * (2 + Zm + |(2 * xh - yh * (1 + yh)) / Qh|) ≤ 1)
    (hv : 2 * (12 * (xh + eX) + 3 * ((2 + Zm) * ((yh + eY) * (1 + yh + eY)) + (yh + eY) ^ 2)) / Qh
          + 3 * (|(2 * xh - yh * (1 + yh)) / Qh| + DYr Qh xh yh eX eY eQ) ^ 2 ≤ vY) :
    ∑ e ∈ (openSet J).erase s(u, v),
        Real.exp (lam * (-(((Yset (insert e J) u v).card : ℝ) - (Yset J u v).card)
          + (2 * xh - yh * (1 + yh)) / Qh - DYr Qh xh yh eX eY eQ))
      ≤ (openSet J).card * Real.exp (lam ^ 2 * vY) := by
  classical
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = (2 * xh - yh * (1 + yh)) / Qh := ⟨_, rfl⟩
  obtain ⟨DY, hDY⟩ : ∃ DY, DY = DYr Qh xh yh eX eY eQ := ⟨_, rfl⟩
  have hDY0 : 0 ≤ DY := by rw [hDY]; exact h.DYr_nonneg
  rw [← hd0] at hc hv ⊢
  rw [← hDY] at hv ⊢
  have habs := abs_le.mp (le_refl |d0|)
  have key := sum_exp_le (openSet J) ((openSet J).erase s(u, v))
    (fun e => lam * (-1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + (d0 - DY)))
    (lam ^ 2 * vY) (erase_subset _ _) ?_ ?_ ?_
  · refine le_trans (le_of_eq (sum_congr rfl fun e _ => ?_)) key
    rw [card_sub_card' (Yset J u v) (Yset (insert e J) u v)]
    ring_nf
  · intro e he
    obtain ⟨hne, he'⟩ := mem_erase.mp he
    have h1 := h.lost_le huv he' hne
    have h0 : (0 : ℝ) ≤ ((Yset (insert e J) u v \ Yset J u v).card : ℝ) := Nat.cast_nonneg _
    have h2 : -1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
        - (Yset J u v \ Yset (insert e J) u v).card) + (d0 - DY) ≤ 2 + Zm + |d0| := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hlam) hc
  · rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    have hG : 2 * (xh - eX) ≤ sumG J u v := by
      rw [h.sumG_eq huv]
      have := h.X_lower huv
      linarith
    have h1 := ydrift_down h.Qh_pos h.Q_lower h.Q_upper h.eQ0 h.eQ2 h.eX0 h.eXx h.eY0 h.yh0 hG
      (h.sumL_le huv)
    rw [← hd0, ← hDY] at h1
    unfold sumG sumL at h1
    apply mul_nonpos_of_nonneg_of_nonpos hlam
    linarith
  · have h1 := h.Y_var huv (c := d0 - DY) (B := |d0| + DY) (vY := vY) (by
      rw [abs_le]
      constructor <;> linarith) hv (-1) (by norm_num)
    calc ∑ e ∈ openSet J,
          (lam * (-1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
            - (Yset J u v \ Yset (insert e J) u v).card) + (d0 - DY))) ^ 2
        = lam ^ 2 * ∑ e ∈ openSet J,
            (-1 * (((Yset (insert e J) u v \ Yset J u v).card : ℝ)
              - (Yset J u v \ Yset (insert e J) u v).card) + (d0 - DY)) ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun e _ => by ring
      _ ≤ lam ^ 2 * ((openSet J).card * vY) := mul_le_mul_of_nonneg_left h1 (sq_nonneg lam)
      _ = (openSet J).card * (lam ^ 2 * vY) := by ring

/- ## The number of open pairs, degrees, codegrees -/

/-- The number of open pairs follows the trajectory deterministically. -/
theorem GoodAt.Q_step (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) {e : Sym2 (Fin N)}
    (he : e ∈ openSet J) :
    |((openSet (insert e J)).card : ℝ) - (Qh - 1 - yh)| ≤ eQ + eY := by
  obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_openSet he
  have h1 := card_openSet_insert h.tf hab
  have h1' : ((openSet (insert s(a, b) J)).card : ℝ) + 1 + (Yset J a b).card
      = (openSet J).card := by exact_mod_cast h1
  have h2 := abs_le.mp h.hQ
  have h3 := abs_le.mp (h.hY a b hab)
  rw [abs_le]
  constructor <;> linarith

/-- Counting lemma behind the exponential bounds for degrees and codegrees. -/
theorem sum_two_pow_le {ι : Type*} [DecidableEq ι] (O : Finset ι) (d' : ι → ℕ) (d K : ℕ)
    (hle : ∀ e ∈ O, d' e ≤ d + 1) (hK : (O.filter fun e => d' e ≠ d).card ≤ K) :
    ∑ e ∈ O, (2 : ℝ) ^ d' e ≤ 2 ^ d * (O.card + K) := by
  have h1 : ∀ e ∈ O, (2 : ℝ) ^ d' e ≤ 2 ^ d + 2 ^ d * (if d' e ≠ d then 1 else 0) := by
    intro e he
    by_cases hd : d' e = d
    · simp [hd]
    · rw [if_pos hd, mul_one]
      have h2 : (2 : ℝ) ^ d' e ≤ 2 ^ (d + 1) :=
        pow_le_pow_right₀ (by norm_num) (hle e he)
      rw [pow_succ] at h2
      linarith
  have h2 := sum_le_sum h1
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum] at h2
  have h3 : ∑ e ∈ O, (if d' e ≠ d then (1 : ℝ) else 0) = (O.filter fun e => d' e ≠ d).card := by
    rw [card_filter]
    push_cast
    rfl
  rw [h3] at h2
  have h4 : ((O.filter fun e => d' e ≠ d).card : ℝ) ≤ K := by exact_mod_cast hK
  have h5 : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

theorem sum_two_pow_nb_le (J : Finset (Sym2 (Fin N))) (u : Fin N) :
    ∑ e ∈ openSet J, (2 : ℝ) ^ (nb (insert e J) u).card
      ≤ 2 ^ (nb J u).card * ((openSet J).card + N) := by
  classical
  exact sum_two_pow_le (openSet J) (fun e => (nb (insert e J) u).card) (nb J u).card N
    (fun e _ => card_nb_insert_le J e u) (card_filter_nb_ne_le J u)

theorem sum_two_pow_cod_le {J : Finset (Sym2 (Fin N))} (hJ : TF J) {u v : Fin N} (huv : u ≠ v) :
    ∑ e ∈ openSet J, (2 : ℝ) ^ (cod (insert e J) u v).card
      ≤ 2 ^ (cod J u v).card * ((openSet J).card + ((nb J u).card + (nb J v).card : ℕ)) := by
  classical
  exact sum_two_pow_le (openSet J) (fun e => (cod (insert e J) u v).card) (cod J u v).card
    ((nb J u).card + (nb J v).card) (fun e he => card_cod_insert_le hJ he huv)
    (card_filter_cod_ne_le hJ huv)

end

end TFP
end E1182

end MartPart

section TrajPart

/-
# Erdős Problem 1182: reference trajectory and error sequences

Pure real analysis on two recursively defined sequences, used for the analysis of the early
triangle-free process on `K_N`.

* `traj N i = (Q̂_i, x̂_i, ŷ_i)` is the reference trajectory (`Qh`, `xh`, `yh`), defined by the same
  one-step recursion as the expected changes of the process;
* `err N i = (eX_i, eY_i, eQ_i)` are the error sequences;
* `horizon γ N = ⌊(√γ / 3) N^{3/2} √(log N)⌋` is the number of steps.

Main results:

* `traj_facts`: for `0 < γ ≤ 1/100` and all large `N`, up to the horizon the trajectory satisfies
  `M N^{-γ} ≤ Q̂ ≤ M` (`M = N.choose 2`), `0 ≤ ŷ ≤ 9 i Q̂ / N³`, `0 < x̂ ≤ (N - 2) (Q̂ / M)²`,
  `(1 + ŷ) / Q̂ ≤ 1 / N` and `∑_{j < i} (1 + ŷ_j) / Q̂_j ≤ γ log N`;
* `err_facts`: for `γ = 1/2000` and all large `N`, up to the horizon
  `N^{17/20} ≤ eX ≤ N^{-1/20} x̂`, `N^{7/20} ≤ eY ≤ N^{-1/20} (ŷ + N^{9/20})`,
  `0 ≤ eQ ≤ N^{-1/20} Q̂`.

Structure of the proofs: one-step algebraic lemmas (`traj_step`, `err_step_X`, `err_step_Y`,
`err_step_Q`), inductions with abstract constants (`traj_inv`, `err_inv`), and the estimates for
large `N` (`traj_core`, `err_core`), which only need a lower bound for `N` and for `log N`.
-/

namespace E1182
namespace TFP

/- ## Definitions -/

/-- Reference trajectory `(Q̂, x̂, ŷ)`. -/
noncomputable def traj (N : ℕ) : ℕ → ℝ × ℝ × ℝ
  | 0 => ((N.choose 2 : ℝ), (N : ℝ) - 2, 0)
  | i + 1 =>
    ((traj N i).1 - 1 - (traj N i).2.2,
     (traj N i).2.1 - (traj N i).2.1 * (2 + 2 * (traj N i).2.2) / (traj N i).1,
     (traj N i).2.2 + (2 * (traj N i).2.1 - (traj N i).2.2 * (1 + (traj N i).2.2)) / (traj N i).1)

/-- The trajectory of the number of open pairs. -/
noncomputable def Qh (N i : ℕ) : ℝ := (traj N i).1
/-- The trajectory of the open-open counts. -/
noncomputable def xh (N i : ℕ) : ℝ := (traj N i).2.1
/-- The trajectory of the closing counts. -/
noncomputable def yh (N i : ℕ) : ℝ := (traj N i).2.2

/-- The number of steps of the process that is analysed. -/
noncomputable def horizon (γ : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.sqrt γ / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N)⌋₊

/-- Error sequences `(eX, eY, eQ)`. -/
noncomputable def err (N : ℕ) : ℕ → ℝ × ℝ × ℝ
  | 0 => ((N : ℝ) ^ (17 / 20 : ℝ), (N : ℝ) ^ (7 / 20 : ℝ), 0)
  | i + 1 =>
    ((err N i).1 + (2 * (2 + 2 * yh N i) * (err N i).1 + 8 * xh N i * (err N i).2.1
        + 8 * xh N i * (2 + 2 * yh N i) * ((err N i).2.2 / Qh N i)) / Qh N i,
     (err N i).2.1 + (2 * (err N i).1 + 8 * ((err N i).2.2 / Qh N i) * xh N i
        + (err N i).2.1 * (1 + 2 * yh N i + (err N i).2.1)
        + 2 * ((err N i).2.2 / Qh N i) * (yh N i + (err N i).2.1) * (1 + yh N i + (err N i).2.1)) / Qh N i,
     (err N i).2.2 + (err N i).2.1)

/-- The error allowed for the open-open counts. -/
noncomputable def eX (N i : ℕ) : ℝ := (err N i).1
/-- The error allowed for the closing counts. -/
noncomputable def eY (N i : ℕ) : ℝ := (err N i).2.1
/-- The error allowed for the number of open pairs. -/
noncomputable def eQ (N i : ℕ) : ℝ := (err N i).2.2

/- ## Unfolding lemmas -/

theorem Qh_zero (N : ℕ) : Qh N 0 = (N.choose 2 : ℝ) := rfl
theorem xh_zero (N : ℕ) : xh N 0 = (N : ℝ) - 2 := rfl
theorem yh_zero (N : ℕ) : yh N 0 = 0 := rfl

theorem Qh_succ (N i : ℕ) : Qh N (i + 1) = Qh N i - 1 - yh N i := rfl

theorem xh_succ (N i : ℕ) :
    xh N (i + 1) = xh N i - xh N i * (2 + 2 * yh N i) / Qh N i := rfl

theorem yh_succ (N i : ℕ) :
    yh N (i + 1) = yh N i + (2 * xh N i - yh N i * (1 + yh N i)) / Qh N i := rfl

theorem eX_zero (N : ℕ) : eX N 0 = (N : ℝ) ^ (17 / 20 : ℝ) := rfl
theorem eY_zero (N : ℕ) : eY N 0 = (N : ℝ) ^ (7 / 20 : ℝ) := rfl
theorem eQ_zero (N : ℕ) : eQ N 0 = 0 := rfl

theorem eX_succ (N i : ℕ) :
    eX N (i + 1) = eX N i + (2 * (2 + 2 * yh N i) * eX N i + 8 * xh N i * eY N i
        + 8 * xh N i * (2 + 2 * yh N i) * (eQ N i / Qh N i)) / Qh N i := rfl

theorem eY_succ (N i : ℕ) :
    eY N (i + 1) = eY N i + (2 * eX N i + 8 * (eQ N i / Qh N i) * xh N i
        + eY N i * (1 + 2 * yh N i + eY N i)
        + 2 * (eQ N i / Qh N i) * (yh N i + eY N i) * (1 + yh N i + eY N i)) / Qh N i := rfl

theorem eQ_succ (N i : ℕ) : eQ N (i + 1) = eQ N i + eY N i := rfl

/-- Partial sums of `a_j = (1 + ŷ_j) / Q̂_j`. -/
noncomputable def aSum (N i : ℕ) : ℝ := ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j

theorem aSum_zero (N : ℕ) : aSum N 0 = 0 := by
  unfold aSum
  exact Finset.sum_range_zero _

theorem aSum_succ (N i : ℕ) : aSum N (i + 1) = aSum N i + (1 + yh N i) / Qh N i := by
  unfold aSum
  exact Finset.sum_range_succ _ i

/- ## One step of the trajectory -/

/-- `exp (-(4/3) a) ≤ 1 - a` for `0 ≤ a ≤ 1/4`. -/
theorem exp_neg_le_one_sub {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) :
    Real.exp (-(4 / 3 * a)) ≤ 1 - a := by
  have h1 : 4 / 3 * a + 1 ≤ Real.exp (4 / 3 * a) := Real.add_one_le_exp _
  have h3 : (1 - a) * (4 / 3 * a + 1) ≤ (1 - a) * Real.exp (4 / 3 * a) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h4 : 0 ≤ a * (1 / 4 - a) := mul_nonneg ha0 (sub_nonneg.mpr ha)
  have h2 : 1 ≤ (1 - a) * Real.exp (4 / 3 * a) := by nlinarith
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  exact h2

/-- One step of the trajectory recursion. Here `u = N - 2`, `t = 9 i / N³`, `k = 9 / N³`. -/
theorem traj_step {Q x y M u t k : ℝ} (hQ : 0 < Q) (hM : 0 < M) (hx : 0 < x) (hy : 0 ≤ y)
    (hk : 0 ≤ k) (ha : (1 + y) / Q ≤ 1 / 9)
    (hxu : x ≤ u * (Q / M) ^ 2) (huk : 2 * u ≤ 8 / 9 * k * M ^ 2) (hyt : y ≤ t * Q) :
    0 < Q - 1 - y ∧ Q - 1 - y ≤ Q ∧
    0 < x - x * (2 + 2 * y) / Q ∧
    x - x * (2 + 2 * y) / Q ≤ u * ((Q - 1 - y) / M) ^ 2 ∧
    0 ≤ y + (2 * x - y * (1 + y)) / Q ∧
    y + (2 * x - y * (1 + y)) / Q ≤ (t + k) * (Q - 1 - y) := by
  have hQ0 : Q ≠ 0 := hQ.ne'
  have hM0 : M ≠ 0 := hM.ne'
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (1 + y) / Q := ⟨_, rfl⟩
  rw [← hadef] at ha
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hy' : 1 + y = a * Q := by rw [hadef]; field_simp
  have eQ' : Q - 1 - y = Q * (1 - a) := by linarith
  have eX' : x - x * (2 + 2 * y) / Q = x * (1 - 2 * a) := by rw [hadef]; ring
  have eY' : y + (2 * x - y * (1 + y)) / Q = y * (1 - a) + 2 * x / Q := by rw [hadef]; ring
  have h2x : 2 * x / Q ≤ 8 / 9 * k * Q := by
    have h1 : 2 * x ≤ 2 * u * (Q / M) ^ 2 := by linarith
    have h2 : 2 * u * (Q / M) ^ 2 ≤ 8 / 9 * k * M ^ 2 * (Q / M) ^ 2 :=
      mul_le_mul_of_nonneg_right huk (sq_nonneg _)
    have h3 : 8 / 9 * k * M ^ 2 * (Q / M) ^ 2 = 8 / 9 * k * Q * Q := by field_simp
    rw [div_le_iff₀ hQ]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eQ']; exact mul_pos hQ (by linarith)
  · linarith
  · rw [eX']; exact mul_pos hx (by linarith)
  · rw [eX', eQ']
    have h1 : x * (1 - 2 * a) ≤ x * (1 - a) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a]) hx.le
    have h2 : x * (1 - a) ^ 2 ≤ u * (Q / M) ^ 2 * (1 - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hxu (sq_nonneg _)
    have h3 : u * (Q / M) ^ 2 * (1 - a) ^ 2 = u * (Q * (1 - a) / M) ^ 2 := by ring
    linarith
  · rw [eY']
    have h1 : 0 ≤ y * (1 - a) := mul_nonneg hy (by linarith)
    have h2 : 0 ≤ 2 * x / Q := by positivity
    linarith
  · rw [eY', eQ']
    have h1 : y * (1 - a) ≤ t * Q * (1 - a) := mul_le_mul_of_nonneg_right hyt (by linarith)
    have h2 : 8 / 9 * (k * Q) ≤ (1 - a) * (k * Q) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith

/-- The bound for `a = (1 + ŷ) / Q̂` that follows from the invariant. -/
theorem a_le_of_inv {Q y A m c : ℝ} (hQ : 0 < Q) (hA : 0 ≤ A) (h2 : 1 ≤ A * m) (hm : m ≤ Q)
    (hy : y ≤ c * Q) : (1 + y) / Q ≤ A + c := by
  rw [div_le_iff₀ hQ]
  have h : A * m ≤ A * Q := mul_le_mul_of_nonneg_left hm hA
  linarith

/- ## One step of the error sequences -/

theorem gron_poly_x {a s : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 10) (hs : 0 ≤ s) :
    1 + 40 * a + 32 * s ≤ (1 + 60 * a + 40 * s) * (1 - 2 * a) := by
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha), mul_nonneg hs (sub_nonneg.mpr ha)]

theorem gron_poly_q {a s : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 10) (hs : 0 ≤ s) :
    1 + 16 * a + 16 * s ≤ (1 + 60 * a + 40 * s) * (1 - a) := by
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha), mul_nonneg hs (sub_nonneg.mpr ha)]

/-- The errors `eX` do not decrease. -/
theorem err_mono_X {Q x y eX eY eQ : ℝ} (hQ : 0 < Q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hX0 : 0 ≤ eX) (hY0 : 0 ≤ eY) (hQ0 : 0 ≤ eQ) :
    eX ≤ eX + (2 * (2 + 2 * y) * eX + 8 * x * eY + 8 * x * (2 + 2 * y) * (eQ / Q)) / Q :=
  le_add_of_nonneg_right (by positivity)

/-- The errors `eY` do not decrease. -/
theorem err_mono_Y {Q x y eX eY eQ : ℝ} (hQ : 0 < Q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hX0 : 0 ≤ eX) (hY0 : 0 ≤ eY) (hQ0 : 0 ≤ eQ) :
    eY ≤ eY + (2 * eX + 8 * (eQ / Q) * x + eY * (1 + 2 * y + eY)
        + 2 * (eQ / Q) * (y + eY) * (1 + y + eY)) / Q :=
  le_add_of_nonneg_right (by positivity)

/-- One step of the Gronwall invariant for `eX`. -/
theorem err_step_X {Q x y eX eY eQ Φ Φ' S₀ : ℝ} (hQ : 0 < Q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hS : 0 ≤ S₀) (ha : (1 + y) / Q ≤ 1 / 10) (hΦ : 0 ≤ Φ)
    (hX : eX ≤ Φ / 4 * x) (hY : eY ≤ Φ * (y + S₀)) (hQe : eQ ≤ Φ / 16 * Q)
    (hΦ' : Φ * (1 + 60 * ((1 + y) / Q) + 40 * (S₀ / Q)) ≤ Φ') :
    eX + (2 * (2 + 2 * y) * eX + 8 * x * eY + 8 * x * (2 + 2 * y) * (eQ / Q)) / Q
      ≤ Φ' / 4 * (x - x * (2 + 2 * y) / Q) := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (1 + y) / Q := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = S₀ / Q := ⟨_, rfl⟩
  rw [← hadef] at ha hΦ'
  rw [← hsdef] at hΦ'
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hyq : y / Q ≤ a := by
    rw [hadef]; exact div_le_div_of_nonneg_right (by linarith) hQ.le
  have hk : eQ / Q ≤ Φ / 16 := by rw [div_le_iff₀ hQ]; exact hQe
  have e1 : eX + (2 * (2 + 2 * y) * eX + 8 * x * eY + 8 * x * (2 + 2 * y) * (eQ / Q)) / Q
      = eX * (1 + 4 * a) + 8 * (x / Q) * eY + 16 * (x * a) * (eQ / Q) := by
    rw [hadef]; ring
  have e2 : x - x * (2 + 2 * y) / Q = x * (1 - 2 * a) := by rw [hadef]; ring
  rw [e1, e2]
  have t1 : eX * (1 + 4 * a) ≤ Φ / 4 * x * (1 + 4 * a) :=
    mul_le_mul_of_nonneg_right hX (by linarith)
  have t2 : 8 * (x / Q) * eY ≤ 8 * (x / Q) * (Φ * (y + S₀)) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have t2' : 8 * (x / Q) * (Φ * (y + S₀)) ≤ 8 * (Φ * x) * (a + s) := by
    have e : 8 * (x / Q) * (Φ * (y + S₀)) = 8 * (Φ * x) * (y / Q + s) := by
      rw [hsdef]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t3 : 16 * (x * a) * (eQ / Q) ≤ 16 * (x * a) * (Φ / 16) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  have t4 : Φ / 4 * x * (1 + 40 * a + 32 * s)
      ≤ Φ / 4 * x * ((1 + 60 * a + 40 * s) * (1 - 2 * a)) :=
    mul_le_mul_of_nonneg_left (gron_poly_x ha0 ha hs0) (by positivity)
  have t5 : Φ * (1 + 60 * a + 40 * s) / 4 * (x * (1 - 2 * a)) ≤ Φ' / 4 * (x * (1 - 2 * a)) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hx (by linarith))
  have e3 : Φ / 4 * x * (1 + 4 * a) + 8 * (Φ * x) * (a + s) + 16 * (x * a) * (Φ / 16)
      = Φ / 4 * x * (1 + 40 * a + 32 * s) := by ring
  have e4 : Φ / 4 * x * ((1 + 60 * a + 40 * s) * (1 - 2 * a))
      = Φ * (1 + 60 * a + 40 * s) / 4 * (x * (1 - 2 * a)) := by ring
  linarith

/-- One step of the Gronwall invariant for `eQ`. -/
theorem err_step_Q {Q y eY eQ Φ Φ' S₀ : ℝ} (hQ : 0 < Q) (hy : 0 ≤ y)
    (hS : 0 ≤ S₀) (ha : (1 + y) / Q ≤ 1 / 10) (hΦ : 0 ≤ Φ)
    (hY : eY ≤ Φ * (y + S₀)) (hQe : eQ ≤ Φ / 16 * Q)
    (hΦ' : Φ * (1 + 60 * ((1 + y) / Q) + 40 * (S₀ / Q)) ≤ Φ') :
    eQ + eY ≤ Φ' / 16 * (Q - 1 - y) := by
  have hQne : Q ≠ 0 := hQ.ne'
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (1 + y) / Q := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = S₀ / Q := ⟨_, rfl⟩
  rw [← hadef] at ha hΦ'
  rw [← hsdef] at hΦ'
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hy' : 1 + y = a * Q := by rw [hadef]; field_simp
  have hS' : S₀ = s * Q := by rw [hsdef]; field_simp
  have t1 : Φ * (y + S₀) ≤ Φ * ((a + s) * Q) :=
    mul_le_mul_of_nonneg_left (by linarith) hΦ
  have t2 : Φ / 16 * Q * (1 + 16 * a + 16 * s)
      ≤ Φ / 16 * Q * ((1 + 60 * a + 40 * s) * (1 - a)) :=
    mul_le_mul_of_nonneg_left (gron_poly_q ha0 ha hs0) (by positivity)
  have t3 : Φ * (1 + 60 * a + 40 * s) / 16 * (Q * (1 - a)) ≤ Φ' / 16 * (Q * (1 - a)) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hQ.le (by linarith))
  have e1 : Q - 1 - y = Q * (1 - a) := by linarith
  rw [e1]
  have e2 : Φ / 16 * Q + Φ * ((a + s) * Q) = Φ / 16 * Q * (1 + 16 * a + 16 * s) := by ring
  have e3 : Φ / 16 * Q * ((1 + 60 * a + 40 * s) * (1 - a))
      = Φ * (1 + 60 * a + 40 * s) / 16 * (Q * (1 - a)) := by ring
  linarith

/-- One step of the Gronwall invariant for `eY`. -/
theorem err_step_Y {Q x y eX eY eQ Φ Φ' S₀ : ℝ} (hQ : 0 < Q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hS : 0 ≤ S₀) (ha : (1 + y) / Q ≤ 1 / 10) (hΦ : 0 ≤ Φ) (hΦ1 : Φ ≤ 1)
    (hY0 : 0 ≤ eY) (hQ0 : 0 ≤ eQ)
    (hX : eX ≤ Φ / 4 * x) (hY : eY ≤ Φ * (y + S₀)) (hQe : eQ ≤ Φ / 16 * Q)
    (hΦ' : Φ * (1 + 60 * ((1 + y) / Q) + 40 * (S₀ / Q)) ≤ Φ') :
    eY + (2 * eX + 8 * (eQ / Q) * x + eY * (1 + 2 * y + eY)
        + 2 * (eQ / Q) * (y + eY) * (1 + y + eY)) / Q
      ≤ Φ' * (y + (2 * x - y * (1 + y)) / Q + S₀) := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (1 + y) / Q := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = S₀ / Q := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = eQ / Q := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = x / Q := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = eY / Q := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = y + S₀ := ⟨_, rfl⟩
  rw [← hadef] at ha hΦ'
  rw [← hsdef] at hΦ'
  rw [← hwdef] at hY
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hk0 : 0 ≤ k := by rw [hkdef]; positivity
  have hp0 : 0 ≤ p := by rw [hpdef]; positivity
  have hz0 : 0 ≤ z := by rw [hzdef]; positivity
  have hw0 : 0 ≤ w := by rw [hwdef]; positivity
  have hyw : y ≤ w := by rw [hwdef]; linarith
  have hk : k ≤ Φ / 16 := by rw [hkdef, div_le_iff₀ hQ]; exact hQe
  have hyq0 : 0 ≤ y / Q := by positivity
  have hyq : y / Q ≤ a := by
    rw [hadef]; exact div_le_div_of_nonneg_right (by linarith) hQ.le
  have hz : z ≤ a + s := by
    have h1 : z ≤ Φ * w / Q := by
      rw [hzdef]; exact div_le_div_of_nonneg_right hY hQ.le
    have h2 : Φ * w / Q = Φ * (y / Q + s) := by rw [hwdef, hsdef]; ring
    have h3 : Φ * (y / Q + s) ≤ 1 * (a + s) :=
      mul_le_mul hΦ1 (by linarith) (by positivity) (by norm_num)
    linarith
  have e1 : eY + (2 * eX + 8 * (eQ / Q) * x + eY * (1 + 2 * y + eY)
        + 2 * (eQ / Q) * (y + eY) * (1 + y + eY)) / Q
      = eY + 2 * (eX / Q) + 8 * k * p + eY * (a + y / Q + z)
        + 2 * k * (y + eY) * (a + z) := by
    rw [hadef, hkdef, hpdef, hzdef]; ring
  have e2 : y + (2 * x - y * (1 + y)) / Q + S₀ = w + 2 * p - y * a := by
    rw [hwdef, hpdef, hadef]; ring
  rw [e1, e2]
  have t1 : 2 * (eX / Q) ≤ Φ / 2 * p := by
    have h1 : eX / Q ≤ Φ / 4 * x / Q := div_le_div_of_nonneg_right hX hQ.le
    have h2 : Φ / 4 * x / Q = Φ / 4 * p := by rw [hpdef]; ring
    linarith
  have t2 : 8 * k * p ≤ Φ / 2 * p := by
    have h1 : k * p ≤ Φ / 16 * p := mul_le_mul_of_nonneg_right hk hp0
    linarith
  have t3 : eY * (a + y / Q + z) ≤ Φ * w * (3 * a + s) :=
    mul_le_mul hY (by linarith) (by positivity) (by positivity)
  have t4 : 2 * k * (y + eY) * (a + z) ≤ 2 * (Φ / 16) * (2 * w) * (2 * a + s) := by
    have hye : y + eY ≤ 2 * w := by
      have h1 : Φ * w ≤ 1 * w := mul_le_mul_of_nonneg_right hΦ1 hw0
      linarith
    have h1 : 2 * k * (y + eY) ≤ 2 * (Φ / 16) * (2 * w) :=
      mul_le_mul (by linarith) hye (by positivity) (by positivity)
    exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)
  have hya : y * a ≤ w * a := mul_le_mul_of_nonneg_right hyw ha0
  have hwa : w * a ≤ w * (1 / 10) := mul_le_mul_of_nonneg_left ha hw0
  have r0 : 0 ≤ w + 2 * p - y * a := by linarith
  have r1 : Φ * (1 + 60 * a + 40 * s) * (w + 2 * p - y * a) ≤ Φ' * (w + 2 * p - y * a) :=
    mul_le_mul_of_nonneg_right hΦ' r0
  have r2 : Φ * (1 + 60 * a + 40 * s) * (w * (1 - a) + 2 * p)
      ≤ Φ * (1 + 60 * a + 40 * s) * (w + 2 * p - y * a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have r3 : Φ * w * (1 + 16 * a + 16 * s) ≤ Φ * w * ((1 + 60 * a + 40 * s) * (1 - a)) :=
    mul_le_mul_of_nonneg_left (gron_poly_q ha0 ha hs0) (by positivity)
  have r4 : Φ * 1 * (2 * p) ≤ Φ * (1 + 60 * a + 40 * s) * (2 * p) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hΦ) (by positivity)
  have n1 : 0 ≤ Φ * w * a := by positivity
  have n2 : 0 ≤ Φ * w * s := by positivity
  have n3 : 0 ≤ Φ * p := by positivity
  linarith

/- ## The induction for the trajectory -/

/-- Consequences of the invariant at one index. -/
theorem traj_inv_a {N : ℕ} {A T : ℝ} {i : ℕ} (hA : 0 ≤ A) (hM : 0 < (N.choose 2 : ℝ))
    (h2 : 1 ≤ A * ((N.choose 2 : ℝ) * Real.exp (-(4 / 3 * T))))
    (hQ : 0 < Qh N i) (hyt : yh N i ≤ 9 * (i : ℝ) / (N : ℝ) ^ 3 * Qh N i)
    (hST : aSum N i ≤ T)
    (hE : (N.choose 2 : ℝ) * Real.exp (-(4 / 3 * aSum N i)) ≤ Qh N i) :
    (N.choose 2 : ℝ) * Real.exp (-(4 / 3 * T)) ≤ Qh N i ∧
      (1 + yh N i) / Qh N i ≤ A + 9 * (i : ℝ) / (N : ℝ) ^ 3 := by
  have hmQ : (N.choose 2 : ℝ) * Real.exp (-(4 / 3 * T)) ≤ Qh N i :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hM.le) hE
  exact ⟨hmQ, a_le_of_inv hQ hA h2 hmQ hyt⟩

/-- The invariant of the trajectory, with abstract constants `A` (a bound for `1 / Q̂`) and
`T` (a bound for the partial sums of `a_j`). -/
theorem traj_inv {N : ℕ} (hN : (9 : ℝ) ≤ N) {A T : ℝ} {I : ℕ} (hA : 0 ≤ A)
    (h1 : ∀ i : ℕ, i ≤ I → (i : ℝ) * A + 9 / 2 * (i : ℝ) ^ 2 / (N : ℝ) ^ 3 ≤ T)
    (h2 : 1 ≤ A * ((N.choose 2 : ℝ) * Real.exp (-(4 / 3 * T))))
    (h3 : ∀ i : ℕ, i ≤ I → A + 9 * (i : ℝ) / (N : ℝ) ^ 3 ≤ 1 / 9) :
    ∀ i : ℕ, i ≤ I →
      0 < Qh N i ∧ Qh N i ≤ (N.choose 2 : ℝ) ∧ 0 ≤ yh N i ∧
      yh N i ≤ 9 * (i : ℝ) / (N : ℝ) ^ 3 * Qh N i ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / (N.choose 2 : ℝ)) ^ 2 ∧
      aSum N i ≤ (i : ℝ) * A + 9 / 2 * (i : ℝ) ^ 2 / (N : ℝ) ^ 3 ∧
      (N.choose 2 : ℝ) * Real.exp (-(4 / 3 * aSum N i)) ≤ Qh N i := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hM1 : (N.choose 2 : ℝ) = N * (N - 1) / 2 := Nat.cast_choose_two ℝ N
  have hMpos : (0 : ℝ) < (N.choose 2 : ℝ) := by
    rw [hM1]; exact div_pos (mul_pos hNpos (by linarith)) (by norm_num)
  have h4M : 4 * (N.choose 2 : ℝ) ^ 2 = ((N : ℝ) - 2) * (N : ℝ) ^ 3 + (N : ℝ) ^ 2 := by
    rw [hM1]; ring
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have huk : 2 * ((N : ℝ) - 2) ≤ 8 / 9 * (9 / (N : ℝ) ^ 3) * (N.choose 2 : ℝ) ^ 2 := by
    have e : 8 / 9 * (9 / (N : ℝ) ^ 3) * (N.choose 2 : ℝ) ^ 2
        = 8 * (N.choose 2 : ℝ) ^ 2 / (N : ℝ) ^ 3 := by ring
    rw [e, le_div_iff₀ hN3]
    nlinarith [sq_nonneg (N : ℝ)]
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Qh_zero]; exact hMpos
    · rw [Qh_zero]
    · rw [yh_zero]
    · rw [yh_zero]; simp
    · rw [xh_zero]; linarith
    · rw [xh_zero, Qh_zero, div_self hMpos.ne']; simp
    · rw [aSum_zero]; simp
    · rw [aSum_zero, Qh_zero]; simp
  | succ i ih =>
    intro hi
    have hi' : i ≤ I := Nat.le_of_succ_le hi
    obtain ⟨hQ, hQM, hy0, hyt, hx0, hxu, hS, hE⟩ := ih hi'
    have hQne : Qh N i ≠ 0 := hQ.ne'
    have hST : aSum N i ≤ T := le_trans hS (h1 i hi')
    obtain ⟨hmQ, ha⟩ := traj_inv_a hA hMpos h2 hQ hyt hST hE
    have ha9 : (1 + yh N i) / Qh N i ≤ 1 / 9 := le_trans ha (h3 i hi')
    have ha0 : 0 ≤ (1 + yh N i) / Qh N i := by positivity
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ :=
      traj_step (u := (N : ℝ) - 2) (t := 9 * (i : ℝ) / (N : ℝ) ^ 3) (k := 9 / (N : ℝ) ^ 3)
        hQ hMpos hx0 hy0 (by positivity) ha9 hxu huk hyt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Qh_succ]; exact s1
    · rw [Qh_succ]; linarith
    · rw [yh_succ]; exact s5
    · rw [yh_succ, Qh_succ]
      have e : 9 * ((i + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3
          = 9 * (i : ℝ) / (N : ℝ) ^ 3 + 9 / (N : ℝ) ^ 3 := by
        push_cast; ring
      rw [e]; exact s6
    · rw [xh_succ]; exact s3
    · rw [xh_succ, Qh_succ]; exact s4
    · rw [aSum_succ]
      have e : ((i + 1 : ℕ) : ℝ) * A + 9 / 2 * ((i + 1 : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 3
          = (i : ℝ) * A + 9 / 2 * (i : ℝ) ^ 2 / (N : ℝ) ^ 3
            + (A + 9 * (i : ℝ) / (N : ℝ) ^ 3) + 9 / 2 / (N : ℝ) ^ 3 := by
        push_cast; ring
      have h : 0 ≤ 9 / 2 / (N : ℝ) ^ 3 := by positivity
      rw [e]; linarith
    · rw [aSum_succ, Qh_succ]
      have e1 : Qh N i - 1 - yh N i = Qh N i * (1 - (1 + yh N i) / Qh N i) := by
        field_simp
        ring
      have e2 : Real.exp (-(4 / 3 * (aSum N i + (1 + yh N i) / Qh N i)))
          = Real.exp (-(4 / 3 * aSum N i)) * Real.exp (-(4 / 3 * ((1 + yh N i) / Qh N i))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e1, e2, ← mul_assoc]
      exact mul_le_mul hE (exp_neg_le_one_sub ha0 (by linarith)) (Real.exp_pos _).le hQ.le

/- ## The trajectory for large `N` -/

theorem horizon_sq_le {γ : ℝ} (hγ : 0 ≤ γ) (N : ℕ) :
    ((horizon γ N : ℕ) : ℝ) ^ 2 ≤ γ / 9 * (N : ℝ) ^ 3 * Real.log N := by
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hr : 0 ≤ Real.sqrt γ / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N) := by
    positivity
  have h1 : ((horizon γ N : ℕ) : ℝ)
      ≤ Real.sqrt γ / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N) := Nat.floor_le hr
  have h2 : ((N : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (N : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul (Nat.cast_nonneg N),
      ← Real.rpow_natCast (N : ℝ) 3]
    congr 1; norm_num
  calc ((horizon γ N : ℕ) : ℝ) ^ 2
      ≤ (Real.sqrt γ / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
    _ = Real.sqrt γ ^ 2 / 9 * ((N : ℝ) ^ (3 / 2 : ℝ)) ^ 2 * Real.sqrt (Real.log N) ^ 2 := by
        ring
    _ = γ / 9 * (N : ℝ) ^ 3 * Real.log N := by rw [Real.sq_sqrt hγ, Real.sq_sqrt hL, h2]

/-- The trajectory facts for one `N`, with explicit lower bounds for `N` and `log N`. -/
theorem traj_core {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1 / 100) {N : ℕ}
    (hN : (64 : ℝ) ≤ N) (hL : 30 / γ ≤ Real.log N) :
    ∀ i ≤ horizon γ N,
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-γ) ≤ Qh N i ∧ Qh N i ≤ N.choose 2 ∧
      0 ≤ yh N i ∧ yh N i ≤ 9 * i * Qh N i / (N : ℝ) ^ 3 ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / N.choose 2) ^ 2 ∧
      (1 + yh N i) / Qh N i ≤ 1 / N ∧
      ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j ≤ γ * Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hLN : Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos hNpos]
  have hγL : 30 ≤ γ * Real.log N := by
    have h := (div_le_iff₀ hγ).mp hL
    linarith
  have hM1 : (N.choose 2 : ℝ) = N * (N - 1) / 2 := Nat.cast_choose_two ℝ N
  have hMlow : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ) := by
    rw [hM1]; nlinarith [mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]
  have hMpos : (0 : ℝ) < (N.choose 2 : ℝ) := lt_of_lt_of_le (by positivity) hMlow
  have hM0 : (N.choose 2 : ℝ) ≠ 0 := hMpos.ne'
  have hN3pos : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hI2 := horizon_sq_le hγ.le N
  have hg0 : 0 < (N : ℝ) ^ γ := Real.rpow_pos_of_pos hNpos γ
  have hg0' : (N : ℝ) ^ γ ≠ 0 := hg0.ne'
  -- `r = √N`
  obtain ⟨r, hr0, hr2, hr8, hrγ⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = N ∧ 8 ≤ r ∧ (N : ℝ) ^ γ ≤ r := by
    refine ⟨Real.sqrt N, Real.sqrt_pos.mpr hNpos, Real.sq_sqrt hNpos.le, ?_, ?_⟩
    · refine (Real.le_sqrt' (by norm_num)).mpr ?_
      rw [show (8 : ℝ) ^ 2 = 64 by norm_num]; exact hN
    · rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hr0' : r ≠ 0 := hr0.ne'
  have hN3 : (N : ℝ) ^ 3 = r ^ 6 := by rw [← hr2]; ring
  have hinvN : 1 / (N : ℝ) = 1 / r ^ 2 := by rw [hr2]
  -- the bound `A` for `1 / Q̂`
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (N : ℝ) ^ γ / (N.choose 2 : ℝ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hA : A ≤ 4 / r ^ 3 := by
    rw [hAdef, div_le_iff₀ hMpos]
    have t1 : 4 / r ^ 3 * ((N : ℝ) ^ 2 / 4) ≤ 4 / r ^ 3 * (N.choose 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hMlow (by positivity)
    have t2 : 4 / r ^ 3 * ((N : ℝ) ^ 2 / 4) = r := by
      rw [← hr2]; field_simp
    linarith
  have hA2 : A ≤ 1 / 2 * (1 / (N : ℝ)) := by
    refine le_trans hA ?_
    rw [hinvN]
    have e : 4 / r ^ 3 = 4 / r * (1 / r ^ 2) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [div_le_iff₀ hr0]; linarith
  -- the horizon is at most `N² / 30`
  have hI30 : ((horizon γ N : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / 30 := by
    have t1 : γ / 9 * (N : ℝ) ^ 3 ≤ 1 / 100 / 9 * (N : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hN3pos.le
    have t2 : γ / 9 * (N : ℝ) ^ 3 * Real.log N ≤ 1 / 100 / 9 * (N : ℝ) ^ 3 * N :=
      mul_le_mul t1 hLN hL0 (by positivity)
    have t3 : ((horizon γ N : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) ^ 2 / 30) ^ 2 := by
      have e : ((N : ℝ) ^ 2 / 30) ^ 2 = 1 / 100 / 9 * (N : ℝ) ^ 3 * N := by ring
      rw [e]; linarith
    exact (abs_le_of_sq_le_sq' t3 (by positivity)).2
  have hAi : ∀ i : ℕ, i ≤ horizon γ N → A + 9 * (i : ℝ) / (N : ℝ) ^ 3 ≤ 1 / (N : ℝ) := by
    intro i hi
    have hi' : (i : ℝ) ≤ (N : ℝ) ^ 2 / 30 := le_trans (Nat.cast_le.mpr hi) hI30
    have t1 : 9 * (i : ℝ) / (N : ℝ) ^ 3 ≤ 3 / 10 * (1 / (N : ℝ)) := by
      rw [div_le_iff₀ hN3pos]
      have e : 3 / 10 * (1 / (N : ℝ)) * (N : ℝ) ^ 3 = 9 * ((N : ℝ) ^ 2 / 30) := by
        field_simp
        norm_num
      rw [e]; linarith
    have t2 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith
  -- the two parts of the bound for the partial sums
  have hR1 : ((horizon γ N : ℕ) : ℝ) * A ≤ γ / 4 * Real.log N := by
    have hAsq : A ^ 2 ≤ 16 / r ^ 6 := by
      have t := pow_le_pow_left₀ hA0 hA 2
      have e : (4 / r ^ 3) ^ 2 = 16 / r ^ 6 := by ring
      rw [e] at t; exact t
    have t1 : (((horizon γ N : ℕ) : ℝ) * A) ^ 2
        ≤ (γ / 9 * (N : ℝ) ^ 3 * Real.log N) * (16 / r ^ 6) := by
      rw [mul_pow]; exact mul_le_mul hI2 hAsq (sq_nonneg _) (by positivity)
    have t2 : (γ / 9 * (N : ℝ) ^ 3 * Real.log N) * (16 / r ^ 6) = 16 / 9 * (γ * Real.log N) := by
      rw [hN3]; field_simp
    have t3 : 16 / 9 * (γ * Real.log N) ≤ (γ / 4 * Real.log N) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ γ * Real.log N)
        (by linarith : (0 : ℝ) ≤ γ * Real.log N - 30)]
    have t4 : (((horizon γ N : ℕ) : ℝ) * A) ^ 2 ≤ (γ / 4 * Real.log N) ^ 2 := by linarith
    exact (abs_le_of_sq_le_sq' t4 (by positivity)).2
  have hR5 : 9 / 2 * ((horizon γ N : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 3 ≤ γ / 2 * Real.log N := by
    rw [div_le_iff₀ hN3pos]; nlinarith
  have h1 : ∀ i : ℕ, i ≤ horizon γ N →
      (i : ℝ) * A + 9 / 2 * (i : ℝ) ^ 2 / (N : ℝ) ^ 3 ≤ 3 * γ / 4 * Real.log N := by
    intro i hi
    have hi' : (i : ℝ) ≤ ((horizon γ N : ℕ) : ℝ) := Nat.cast_le.mpr hi
    have t1 : (i : ℝ) * A ≤ ((horizon γ N : ℕ) : ℝ) * A := mul_le_mul_of_nonneg_right hi' hA0
    have t2 : 9 / 2 * (i : ℝ) ^ 2 / (N : ℝ) ^ 3
        ≤ 9 / 2 * ((horizon γ N : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 3 := by
      refine div_le_div_of_nonneg_right ?_ hN3pos.le
      have t := pow_le_pow_left₀ (Nat.cast_nonneg i) hi' 2
      linarith
    linarith
  have hexpT : Real.exp (-(4 / 3 * (3 * γ / 4 * Real.log N))) = ((N : ℝ) ^ γ)⁻¹ := by
    rw [Real.rpow_def_of_pos hNpos, ← Real.exp_neg]; congr 1; ring
  have h2 : 1 ≤ A * ((N.choose 2 : ℝ) * Real.exp (-(4 / 3 * (3 * γ / 4 * Real.log N)))) := by
    rw [hexpT, hAdef]; apply le_of_eq; field_simp
  have h3 : ∀ i : ℕ, i ≤ horizon γ N → A + 9 * (i : ℝ) / (N : ℝ) ^ 3 ≤ 1 / 9 := by
    intro i hi
    have t1 := hAi i hi
    have t2 : 1 / (N : ℝ) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  intro i hi
  obtain ⟨hQ, hQM, hy0, hyt, hx0, hxu, hS, hE⟩ :=
    traj_inv (by linarith : (9 : ℝ) ≤ N) hA0 h1 h2 h3 i hi
  have hST : aSum N i ≤ 3 * γ / 4 * Real.log N := le_trans hS (h1 i hi)
  obtain ⟨hmQ, ha⟩ := traj_inv_a hA0 hMpos h2 hQ hyt hST hE
  refine ⟨?_, hQM, hy0, ?_, hx0, hxu, le_trans ha (hAi i hi), ?_⟩
  · rw [Real.rpow_neg hNpos.le, ← hexpT]; exact hmQ
  · have e : 9 * (i : ℝ) * Qh N i / (N : ℝ) ^ 3 = 9 * (i : ℝ) / (N : ℝ) ^ 3 * Qh N i := by ring
    rw [e]; exact hyt
  · have t : aSum N i ≤ γ * Real.log N := by linarith
    exact t

theorem traj_facts {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1 / 100) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i ≤ horizon γ N,
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-γ) ≤ Qh N i ∧ Qh N i ≤ N.choose 2 ∧
      0 ≤ yh N i ∧ yh N i ≤ 9 * i * Qh N i / (N : ℝ) ^ 3 ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / N.choose 2) ^ 2 ∧
      (1 + yh N i) / Qh N i ≤ 1 / N ∧
      ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j ≤ γ * Real.log N := by
  have e1 : ∀ᶠ N : ℕ in Filter.atTop, (64 : ℝ) ≤ N :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 64
  have e2 : ∀ᶠ N : ℕ in Filter.atTop, 30 / γ ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (30 / γ)
  filter_upwards [e1, e2] with N h1 h2
  exact traj_core hγ hγ' h1 h2

/- ## The induction for the errors -/

/-- The Gronwall factor: `N^{-1/10} exp (60 ∑_{j<i} a_j + c i)`. -/
noncomputable def gron (N : ℕ) (c : ℝ) (i : ℕ) : ℝ :=
  (N : ℝ) ^ (-(1 / 10 : ℝ)) * Real.exp (60 * aSum N i + c * (i : ℝ))

theorem gron_nonneg (N : ℕ) (c : ℝ) (i : ℕ) : 0 ≤ gron N c i :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.exp_pos _).le

theorem gron_zero (N : ℕ) (c : ℝ) : gron N c 0 = (N : ℝ) ^ (-(1 / 10 : ℝ)) := by
  simp [gron, aSum_zero]

theorem gron_succ_ge (N : ℕ) (c : ℝ) (i : ℕ) :
    gron N c i * (1 + 60 * ((1 + yh N i) / Qh N i) + c) ≤ gron N c (i + 1) := by
  have e : 60 * aSum N (i + 1) + c * ((i + 1 : ℕ) : ℝ)
      = (60 * aSum N i + c * (i : ℝ)) + (60 * ((1 + yh N i) / Qh N i) + c) := by
    rw [aSum_succ]; push_cast; ring
  have h := Real.add_one_le_exp (60 * ((1 + yh N i) / Qh N i) + c)
  have hB : 0 ≤ (N : ℝ) ^ (-(1 / 10 : ℝ)) * Real.exp (60 * aSum N i + c * (i : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.exp_pos _).le
  unfold gron
  rw [e, Real.exp_add (60 * aSum N i + c * (i : ℝ)) (60 * ((1 + yh N i) / Qh N i) + c),
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hB

/-- The Gronwall invariant of the error sequences, with an abstract constant `c`
(a bound for `40 N^{9/20} / Q̂`). -/
theorem err_inv {N : ℕ} {c : ℝ} {I : ℕ}
    (hT : ∀ i : ℕ, i ≤ I → 0 < Qh N i ∧ 0 ≤ xh N i ∧ 0 ≤ yh N i ∧
        (1 + yh N i) / Qh N i ≤ 1 / 10 ∧ 40 * ((N : ℝ) ^ (9 / 20 : ℝ) / Qh N i) ≤ c ∧
        gron N c i ≤ 1)
    (h0 : (N : ℝ) ^ (17 / 20 : ℝ) ≤ (N : ℝ) ^ (-(1 / 10 : ℝ)) / 4 * ((N : ℝ) - 2))
    (h0' : (N : ℝ) ^ (7 / 20 : ℝ) ≤ (N : ℝ) ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ (9 / 20 : ℝ)) :
    ∀ i : ℕ, i ≤ I →
      (N : ℝ) ^ (17 / 20 : ℝ) ≤ eX N i ∧ eX N i ≤ gron N c i / 4 * xh N i ∧
      (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i ∧
      eY N i ≤ gron N c i * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) ∧
      0 ≤ eQ N i ∧ eQ N i ≤ gron N c i / 16 * Qh N i := by
  intro i
  induction i with
  | zero =>
    intro hi
    obtain ⟨hQ, -, -, -, -, -⟩ := hT 0 hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eX_zero]
    · rw [eX_zero, gron_zero, xh_zero]; exact h0
    · rw [eY_zero]
    · rw [eY_zero, gron_zero, yh_zero, zero_add]; exact h0'
    · rw [eQ_zero]
    · rw [eQ_zero]
      exact mul_nonneg (div_nonneg (gron_nonneg N c 0) (by norm_num)) hQ.le
  | succ i ih =>
    intro hi
    have hi' : i ≤ I := Nat.le_of_succ_le hi
    obtain ⟨hQ, hx, hy, ha, hc, hΦ1⟩ := hT i hi'
    obtain ⟨hX0, hX, hY0, hY, hQ0, hQe⟩ := ih hi'
    have hS : (0 : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hX0' : 0 ≤ eX N i := le_trans (Real.rpow_nonneg (Nat.cast_nonneg N) _) hX0
    have hY0' : 0 ≤ eY N i := le_trans (Real.rpow_nonneg (Nat.cast_nonneg N) _) hY0
    have hΦ : 0 ≤ gron N c i := gron_nonneg N c i
    have hΦ' : gron N c i * (1 + 60 * ((1 + yh N i) / Qh N i)
        + 40 * ((N : ℝ) ^ (9 / 20 : ℝ) / Qh N i)) ≤ gron N c (i + 1) :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) hΦ) (gron_succ_ge N c i)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eX_succ]; exact le_trans hX0 (err_mono_X hQ hx hy hX0' hY0' hQ0)
    · rw [eX_succ, xh_succ]; exact err_step_X hQ hx hy hS ha hΦ hX hY hQe hΦ'
    · rw [eY_succ]; exact le_trans hY0 (err_mono_Y hQ hx hy hX0' hY0' hQ0)
    · rw [eY_succ, yh_succ]
      exact err_step_Y hQ hx hy hS ha hΦ hΦ1 hY0' hQ0 hX hY hQe hΦ'
    · rw [eQ_succ]; linarith
    · rw [eQ_succ, Qh_succ]; exact err_step_Q hQ hy hS ha hΦ hY hQe hΦ'

/- ## The errors for large `N` -/

/-- The elementary estimate behind `40 N^{9/20} N^{1/2000} I / M ≤ 1`. -/
theorem exp_bound_c0 {L t : ℝ} (hL : 600 ≤ L)
    (ht : t ^ 2 ≤ 1 / 2000 / 9 * Real.exp L ^ 3 * L) :
    160 * Real.exp (L * (9 / 20)) * Real.exp (L * (1 / 2000)) * t ≤ Real.exp L ^ 2 := by
  have hu : 64 / 45 * L ≤ Real.exp (99 / 1000 * L) := by
    have h := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 99 / 1000 * L)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by linarith : (0 : ℝ) ≤ L - 600)]
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Real.exp (L * (9 / 20)) ^ 2 * Real.exp (L * (1 / 2000)) ^ 2
      * Real.exp L ^ 3 := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hP : Real.exp (99 / 1000 * L) * P = (Real.exp L ^ 2) ^ 2 := by
    rw [hPdef]
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have hb : 0 ≤ Real.exp L ^ 2 := by positivity
  have hsq : (160 * Real.exp (L * (9 / 20)) * Real.exp (L * (1 / 2000)) * t) ^ 2
      ≤ (Real.exp L ^ 2) ^ 2 :=
    calc (160 * Real.exp (L * (9 / 20)) * Real.exp (L * (1 / 2000)) * t) ^ 2
        = 25600 * (Real.exp (L * (9 / 20)) ^ 2 * Real.exp (L * (1 / 2000)) ^ 2) * t ^ 2 := by
          ring
      _ ≤ 25600 * (Real.exp (L * (9 / 20)) ^ 2 * Real.exp (L * (1 / 2000)) ^ 2)
            * (1 / 2000 / 9 * Real.exp L ^ 3 * L) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 64 / 45 * L * P := by rw [hPdef]; ring
      _ ≤ Real.exp (99 / 1000 * L) * P := mul_le_mul_of_nonneg_right hu hP0
      _ = (Real.exp L ^ 2) ^ 2 := hP
  exact (abs_le_of_sq_le_sq' hsq hb).2

/-- The constant `c = 40 N^{9/20} N^{1/2000} / M` satisfies `c I ≤ 1`. -/
theorem err_c0 {N : ℕ} (hN : (64 : ℝ) ≤ N) (hL : 600 ≤ Real.log N) :
    40 * (N : ℝ) ^ (9 / 20 : ℝ) * ((N : ℝ) ^ (1 / 2000 : ℝ) / (N.choose 2 : ℝ))
      * ((horizon (1 / 2000) N : ℕ) : ℝ) ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hM1 : (N.choose 2 : ℝ) = N * (N - 1) / 2 := Nat.cast_choose_two ℝ N
  have hMlow : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ) := by
    rw [hM1]; nlinarith [mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]
  have hMpos : (0 : ℝ) < (N.choose 2 : ℝ) := lt_of_lt_of_le (by positivity) hMlow
  have hI2 := horizon_sq_le (by norm_num : (0 : ℝ) ≤ 1 / 2000) N
  have hNL : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  have key : 160 * Real.exp (Real.log N * (9 / 20)) * Real.exp (Real.log N * (1 / 2000))
      * ((horizon (1 / 2000) N : ℕ) : ℝ) ≤ Real.exp (Real.log N) ^ 2 := by
    refine exp_bound_c0 hL ?_
    rw [← hNL]; exact hI2
  rw [← hNL] at key
  rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hNpos]
  have e : 40 * Real.exp (Real.log N * (9 / 20))
        * (Real.exp (Real.log N * (1 / 2000)) / (N.choose 2 : ℝ))
        * ((horizon (1 / 2000) N : ℕ) : ℝ)
      = 40 * Real.exp (Real.log N * (9 / 20)) * Real.exp (Real.log N * (1 / 2000))
        * ((horizon (1 / 2000) N : ℕ) : ℝ) / (N.choose 2 : ℝ) := by ring
  rw [e, div_le_one hMpos]
  linarith

/-- The initial error `eX_0 = N^{17/20}` is below `(N^{-1/10} / 4) x̂_0`. -/
theorem err_base {N : ℕ} (hN : (64 : ℝ) ≤ N) (hL : 600 ≤ Real.log N) :
    (N : ℝ) ^ (17 / 20 : ℝ) ≤ (N : ℝ) ^ (-(1 / 10 : ℝ)) / 4 * ((N : ℝ) - 2) := by
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hNpos]
  have h8 : 8 ≤ Real.exp (Real.log N * (1 / 20)) := by
    linarith [Real.add_one_le_exp (Real.log N * (1 / 20))]
  have hsplit : Real.exp (Real.log N * -(1 / 10)) * (N : ℝ)
      = Real.exp (Real.log N * (17 / 20)) * Real.exp (Real.log N * (1 / 20)) := by
    calc Real.exp (Real.log N * -(1 / 10)) * (N : ℝ)
        = Real.exp (Real.log N * -(1 / 10)) * Real.exp (Real.log N) := by
          rw [Real.exp_log hNpos]
      _ = Real.exp (Real.log N * (17 / 20)) * Real.exp (Real.log N * (1 / 20)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have t1 : Real.exp (Real.log N * -(1 / 10)) / 4 * ((N : ℝ) / 2)
      ≤ Real.exp (Real.log N * -(1 / 10)) / 4 * ((N : ℝ) - 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t2 : Real.exp (Real.log N * (17 / 20)) * 8
      ≤ Real.exp (Real.log N * (17 / 20)) * Real.exp (Real.log N * (1 / 20)) :=
    mul_le_mul_of_nonneg_left h8 (Real.exp_pos _).le
  linarith

/-- The error facts for one `N`, given the trajectory facts and lower bounds for `N`, `log N`. -/
theorem err_core {N : ℕ} (hN : (64 : ℝ) ≤ N) (hL : 600 ≤ Real.log N)
    (hT : ∀ i ≤ horizon (1 / 2000) N,
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ Qh N i ∧ Qh N i ≤ N.choose 2 ∧
      0 ≤ yh N i ∧ yh N i ≤ 9 * i * Qh N i / (N : ℝ) ^ 3 ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / N.choose 2) ^ 2 ∧
      (1 + yh N i) / Qh N i ≤ 1 / N ∧
      ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j ≤ 1 / 2000 * Real.log N) :
    ∀ i ≤ horizon (1 / 2000) N,
      (N : ℝ) ^ (17 / 20 : ℝ) ≤ eX N i ∧ eX N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * xh N i ∧
      (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i ∧
      eY N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) ∧
      0 ≤ eQ N i ∧ eQ N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hexp : ∀ p : ℝ, (N : ℝ) ^ p = Real.exp (Real.log N * p) :=
    fun p => Real.rpow_def_of_pos hNpos p
  have hM1 : (N.choose 2 : ℝ) = N * (N - 1) / 2 := Nat.cast_choose_two ℝ N
  have hMlow : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ) := by
    rw [hM1]; nlinarith [mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]
  have hMpos : (0 : ℝ) < (N.choose 2 : ℝ) := lt_of_lt_of_le (by positivity) hMlow
  have hM0 : (N.choose 2 : ℝ) ≠ 0 := hMpos.ne'
  have hg : 0 < (N : ℝ) ^ (1 / 2000 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hg0 : (N : ℝ) ^ (1 / 2000 : ℝ) ≠ 0 := hg.ne'
  have hS : 0 < (N : ℝ) ^ (9 / 20 : ℝ) := Real.rpow_pos_of_pos hNpos _
  -- the constant `c`
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 40 * (N : ℝ) ^ (9 / 20 : ℝ)
      * ((N : ℝ) ^ (1 / 2000 : ℝ) / (N.choose 2 : ℝ)) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hcI : c * ((horizon (1 / 2000) N : ℕ) : ℝ) ≤ 1 := by
    rw [hcdef]; exact err_c0 hN hL
  -- the Gronwall factor is at most `N^{-1/20}`
  have hgron : ∀ i : ℕ, i ≤ horizon (1 / 2000) N → gron N c i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
    intro i hi
    obtain ⟨-, -, -, -, -, -, -, hSi⟩ := hT i hi
    have hci : c * (i : ℝ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi) hc0) hcI
    have hSi' : aSum N i ≤ 1 / 2000 * Real.log N := hSi
    unfold gron
    rw [hexp, hexp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hle1 : (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 := by
    rw [hexp]
    calc Real.exp (Real.log N * -(1 / 20)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hT' : ∀ i : ℕ, i ≤ horizon (1 / 2000) N → 0 < Qh N i ∧ 0 ≤ xh N i ∧ 0 ≤ yh N i ∧
      (1 + yh N i) / Qh N i ≤ 1 / 10 ∧ 40 * ((N : ℝ) ^ (9 / 20 : ℝ) / Qh N i) ≤ c ∧
      gron N c i ≤ 1 := by
    intro i hi
    obtain ⟨hQlow, -, hy, -, hx, -, ha, -⟩ := hT i hi
    have hQ : 0 < Qh N i :=
      lt_of_lt_of_le (mul_pos hMpos (Real.rpow_pos_of_pos hNpos _)) hQlow
    refine ⟨hQ, hx.le, hy, ?_, ?_, le_trans (hgron i hi) hle1⟩
    · exact le_trans ha (one_div_le_one_div_of_le (by norm_num) (by linarith))
    · rw [Real.rpow_neg hNpos.le] at hQlow
      have hgQ : (N.choose 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2000 : ℝ) * Qh N i := by
        have t := mul_le_mul_of_nonneg_left hQlow hg.le
        have e : (N : ℝ) ^ (1 / 2000 : ℝ)
            * ((N.choose 2 : ℝ) * ((N : ℝ) ^ (1 / 2000 : ℝ))⁻¹) = (N.choose 2 : ℝ) := by
          field_simp
        linarith
      have t1 : 1 ≤ (N : ℝ) ^ (1 / 2000 : ℝ) / (N.choose 2 : ℝ) * Qh N i := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hMpos]; linarith
      have t2 : (N : ℝ) ^ (9 / 20 : ℝ) / Qh N i
          ≤ (N : ℝ) ^ (9 / 20 : ℝ) * ((N : ℝ) ^ (1 / 2000 : ℝ) / (N.choose 2 : ℝ)) := by
        rw [div_le_iff₀ hQ]
        have t3 := mul_le_mul_of_nonneg_left t1 hS.le
        linarith
      rw [hcdef]; linarith
  have h0 : (N : ℝ) ^ (17 / 20 : ℝ) ≤ (N : ℝ) ^ (-(1 / 10 : ℝ)) / 4 * ((N : ℝ) - 2) :=
    err_base hN hL
  have h0' : (N : ℝ) ^ (7 / 20 : ℝ) ≤ (N : ℝ) ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ (9 / 20 : ℝ) := by
    rw [← Real.rpow_add hNpos]; apply le_of_eq; congr 1; norm_num
  intro i hi
  obtain ⟨hX0, hX, hY0, hY, hQ0, hQe⟩ := err_inv hT' h0 h0' i hi
  obtain ⟨hQ, hx, hy, -, -, -⟩ := hT' i hi
  have hG := hgron i hi
  have hG0 := gron_nonneg N c i
  refine ⟨hX0, ?_, hY0, ?_, hQ0, ?_⟩
  · exact le_trans hX (mul_le_mul_of_nonneg_right (by linarith) hx)
  · exact le_trans hY (mul_le_mul_of_nonneg_right hG (by positivity))
  · exact le_trans hQe (mul_le_mul_of_nonneg_right (by linarith) hQ.le)

theorem err_facts :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i ≤ horizon (1 / 2000) N,
      (N : ℝ) ^ (17 / 20 : ℝ) ≤ eX N i ∧ eX N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * xh N i ∧
      (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i ∧
      eY N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) ∧
      0 ≤ eQ N i ∧ eQ N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i := by
  have e1 : ∀ᶠ N : ℕ in Filter.atTop, (64 : ℝ) ≤ N :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 64
  have e2 : ∀ᶠ N : ℕ in Filter.atTop, (600 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 600
  have e3 := traj_facts (γ := 1 / 2000) (by norm_num) (by norm_num)
  filter_upwards [e1, e2, e3] with N h1 h2 h3
  exact err_core h1 h2 h3

end TFP
end E1182

end TrajPart

section WCountPart

/-
# Second moment of the loss of open pairs of a fixed edge set

For a fixed set `W` of pairs, choosing the open pair `ab` removes from `W ∩ openSet J` the pair
`ab` itself (if it is in `W`) and the pairs of `W` closed by it. The sum over all open choices of
the squares of these losses is bounded in terms of the degrees and codegrees of `J` and the
maximum degree of `W`.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

open Classical in
/-- The degree of the vertex `a` in the edge set `W`. -/
noncomputable def degW (W : Finset (Sym2 (Fin N))) (a : Fin N) : ℕ :=
  (univ.filter fun x : Fin N => s(a, x) ∈ W).card

/-- Every pair of `W` has at most two ordered representatives, so the degrees of `W` sum to at
most `2 |W|`. -/
theorem sum_degW_le (W : Finset (Sym2 (Fin N))) : ∑ a : Fin N, degW W a ≤ 2 * W.card := by
  classical
  have h1 : ∑ a : Fin N, degW W a
      = ((univ : Finset (Fin N × Fin N)).filter fun p => s(p.1, p.2) ∈ W).card := by
    simp only [degW, card_filter, Fintype.sum_prod_type]
  rw [h1]
  refine card_le_mul_card_image_of_maps_to (f := fun p : Fin N × Fin N => s(p.1, p.2))
    (fun p hp => (mem_filter.mp hp).2) 2 (fun e _ => ?_)
  induction e using Sym2.ind with
  | h u v =>
    refine (card_le_card (t := {(u, v), (v, u)}) fun p hp => ?_).trans card_le_two
    have hp2 : s(p.1, p.2) = s(u, v) := (mem_filter.mp hp).2
    rcases (Sym2.mk_eq_mk_iff (q := (u, v))).mp hp2 with rfl | rfl
    · simp
    · simp

open Classical in
/-- For a vertex set `S`, the second moment over `b` of the number of neighbours of `b` in `S`:
a pair `x, x'` of vertices of `S` is counted once for every common neighbour. -/
theorem GoodAt.sum_sq_card_filter_le {J : Finset (Sym2 (Fin N))} {Qh xh yh eX eY eQ Dm Zm : ℝ}
    (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) (hZ0 : 0 ≤ Zm) (S : Finset (Fin N)) :
    ∑ b : Fin N, ((S.filter fun x => s(x, b) ∈ J).card : ℝ) ^ 2
      ≤ (S.card : ℝ) * (Dm + (S.card : ℝ) * Zm) := by
  have hT : ∀ x x' : Fin N,
      ∑ b : Fin N, (if s(x, b) ∈ J then (1 : ℝ) else 0) * (if s(x', b) ∈ J then (1 : ℝ) else 0)
        ≤ (if x = x' then Dm else 0) + Zm := by
    intro x x'
    have hcod : ∑ b : Fin N,
        (if s(x, b) ∈ J then (1 : ℝ) else 0) * (if s(x', b) ∈ J then (1 : ℝ) else 0)
          = ((cod J x x').card : ℝ) := by
      rw [cod, natCast_card_filter]
      refine sum_congr rfl fun b _ => ?_
      by_cases h1 : s(x, b) ∈ J <;> by_cases h2 : s(x', b) ∈ J <;> simp [h1, h2]
    rw [hcod]
    by_cases hxx : x = x'
    · subst hxx
      rw [if_pos rfl]
      have hnb : cod J x x = nb J x := by
        ext w
        simp [cod, nb]
      rw [hnb]
      have := h.hD x
      linarith
    · rw [if_neg hxx]
      have := h.hZ x x' hxx
      linarith
  calc ∑ b : Fin N, ((S.filter fun x => s(x, b) ∈ J).card : ℝ) ^ 2
      = ∑ b : Fin N, ∑ x ∈ S, ∑ x' ∈ S,
          (if s(x, b) ∈ J then (1 : ℝ) else 0) * (if s(x', b) ∈ J then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun b _ => ?_
        rw [natCast_card_filter, sq, sum_mul_sum]
    _ = ∑ x ∈ S, ∑ x' ∈ S, ∑ b : Fin N,
          (if s(x, b) ∈ J then (1 : ℝ) else 0) * (if s(x', b) ∈ J then (1 : ℝ) else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        exact sum_comm
    _ ≤ ∑ x ∈ S, ∑ x' ∈ S, ((if x = x' then Dm else 0) + Zm) :=
        sum_le_sum fun x _ => sum_le_sum fun x' _ => hT x x'
    _ = ∑ x ∈ S, (Dm + (S.card : ℝ) * Zm) := by
        refine sum_congr rfl fun x hx => ?_
        rw [sum_add_distrib, sum_ite_eq, if_pos hx, sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ) * (Dm + (S.card : ℝ) * Zm) := by
        rw [sum_const, nsmul_eq_mul]

/-- Double counting over the open pairs: if the loss `L` at the open pair `ab` is at most
`ι(ab) + A a b + A b a` with `ι` an indicator, then the second moment of `L` over the open pairs
is controlled by the sum of `ι` over the open pairs and the second moment of `A` over all ordered
pairs. -/
theorem two_mul_sum_openSet_sq_le (J : Finset (Sym2 (Fin N))) (L ι : Sym2 (Fin N) → ℝ)
    (A : Fin N → Fin N → ℝ) (hL0 : ∀ e, 0 ≤ L e) (hι : ∀ e, ι e ^ 2 = ι e)
    (hL : ∀ a b, Op J a b → L s(a, b) ≤ ι s(a, b) + A a b + A b a) :
    2 * ∑ e ∈ openSet J, L e ^ 2
      ≤ 3 * (2 * ∑ e ∈ openSet J, ι e + 2 * ∑ a : Fin N, ∑ b : Fin N, A a b ^ 2) := by
  classical
  have hpt : ∀ a b, Op J a b →
      L s(a, b) ^ 2 ≤ 3 * (ι s(a, b) + A a b ^ 2 + A b a ^ 2) := by
    intro a b hab
    have h1 : L s(a, b) ^ 2 ≤ (ι s(a, b) + A a b + A b a) ^ 2 :=
      pow_le_pow_left₀ (hL0 s(a, b)) (hL a b hab) 2
    have h2 := hι s(a, b)
    nlinarith [sq_nonneg (ι s(a, b) - A a b), sq_nonneg (ι s(a, b) - A b a),
      sq_nonneg (A a b - A b a)]
  have hι_sum : (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, ι s(p.1, p.2))
      = 2 * ∑ e ∈ openSet J, ι e := (two_mul_sum_openSet J ι).symm
  have hA1 : (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, A p.1 p.2 ^ 2)
      ≤ ∑ a : Fin N, ∑ b : Fin N, A a b ^ 2 := by
    calc (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, A p.1 p.2 ^ 2)
        ≤ ∑ p : Fin N × Fin N, A p.1 p.2 ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => sq_nonneg _
      _ = ∑ a : Fin N, ∑ b : Fin N, A a b ^ 2 :=
          Fintype.sum_prod_type' fun a b => A a b ^ 2
  have hA2 : (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, A p.2 p.1 ^ 2)
      ≤ ∑ a : Fin N, ∑ b : Fin N, A a b ^ 2 := by
    calc (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, A p.2 p.1 ^ 2)
        ≤ ∑ p : Fin N × Fin N, A p.2 p.1 ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => sq_nonneg _
      _ = ∑ a : Fin N, ∑ b : Fin N, A a b ^ 2 :=
          Fintype.sum_prod_type_right' fun b a => A a b ^ 2
  calc 2 * ∑ e ∈ openSet J, L e ^ 2
      = ∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, L s(p.1, p.2) ^ 2 :=
        two_mul_sum_openSet J fun e => L e ^ 2
    _ ≤ ∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2,
          3 * (ι s(p.1, p.2) + A p.1 p.2 ^ 2 + A p.2 p.1 ^ 2) :=
        sum_le_sum fun p hp => hpt p.1 p.2 (mem_filter.mp hp).2
    _ = 3 * ((∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, ι s(p.1, p.2))
          + (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, A p.1 p.2 ^ 2)
          + (∑ p ∈ (univ : Finset (Fin N × Fin N)) with Op J p.1 p.2, A p.2 p.1 ^ 2)) := by
        rw [← mul_sum, sum_add_distrib, sum_add_distrib]
    _ ≤ 3 * (2 * ∑ e ∈ openSet J, ι e + 2 * ∑ a : Fin N, ∑ b : Fin N, A a b ^ 2) := by
        linarith

/-- Second moment of the losses. -/
theorem GoodAt.sum_W_lost_sq_le {J : Finset (Sym2 (Fin N))} {Qh xh yh eX eY eQ Dm Zm : ℝ}
    (h : GoodAt J Qh xh yh eX eY eQ Dm Zm) (hD0 : 0 ≤ Dm) (hZ0 : 0 ≤ Zm)
    (W : Finset (Sym2 (Fin N))) {ΔW : ℝ} (hΔ : ∀ a : Fin N, (degW W a : ℝ) ≤ ΔW) :
    ∑ e ∈ openSet J, (((W ∩ openSet J) \ (W ∩ openSet (insert e J))).card : ℝ) ^ 2
      ≤ 3 * W.card * (1 + 2 * Dm + 2 * ΔW * Zm) := by
  classical
  -- without vertices there are no pairs at all
  rcases isEmpty_or_nonempty (Fin N) with hN | ⟨⟨a₀⟩⟩
  · have hW : W = ∅ := eq_empty_of_isEmpty W
    subst hW
    simp
  have hΔ0 : 0 ≤ ΔW := le_trans (Nat.cast_nonneg _) (hΔ a₀)
  have hF0 : 0 ≤ Dm + ΔW * Zm := add_nonneg hD0 (mul_nonneg hΔ0 hZ0)
  -- the loss at an open pair
  have hL : ∀ a b : Fin N, Op J a b →
      (((W ∩ openSet J) \ (W ∩ openSet (insert s(a, b) J))).card : ℝ)
        ≤ (if s(a, b) ∈ W then (1 : ℝ) else 0)
          + ((univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card : ℝ)
          + ((univ.filter fun x : Fin N => s(b, x) ∈ W ∧ s(x, a) ∈ J).card : ℝ) := by
    intro a b hab
    exact_mod_cast W_lost_card_le h.tf hab W
  have hι2 : ∀ e : Sym2 (Fin N),
      (if e ∈ W then (1 : ℝ) else 0) ^ 2 = (if e ∈ W then (1 : ℝ) else 0) := by
    intro e
    by_cases he : e ∈ W <;> simp [he]
  have key : 2 * ∑ e ∈ openSet J,
        (((W ∩ openSet J) \ (W ∩ openSet (insert e J))).card : ℝ) ^ 2
      ≤ 3 * (2 * ∑ e ∈ openSet J, (if e ∈ W then (1 : ℝ) else 0)
        + 2 * ∑ a : Fin N, ∑ b : Fin N,
          ((univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card : ℝ) ^ 2) :=
    two_mul_sum_openSet_sq_le J
      (fun e => (((W ∩ openSet J) \ (W ∩ openSet (insert e J))).card : ℝ))
      (fun e => if e ∈ W then (1 : ℝ) else 0)
      (fun a b => ((univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card : ℝ))
      (fun e => Nat.cast_nonneg _) hι2 hL
  -- the pairs of `W` among the open pairs
  have hι : ∑ e ∈ openSet J, (if e ∈ W then (1 : ℝ) else 0) ≤ W.card := by
    rw [sum_boole]
    exact_mod_cast card_le_card fun e he => (mem_filter.mp he).2
  -- the second moment for a fixed first vertex
  have hC : ∀ a : Fin N,
      ∑ b : Fin N, ((univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card : ℝ) ^ 2
        ≤ (degW W a : ℝ) * (Dm + ΔW * Zm) := by
    intro a
    have h1 := h.sum_sq_card_filter_le hZ0 (univ.filter fun x : Fin N => s(a, x) ∈ W)
    simp only [filter_filter] at h1
    have h2 : (degW W a : ℝ) ≤ ΔW := hΔ a
    have h3 : (0 : ℝ) ≤ (degW W a : ℝ) := Nat.cast_nonneg _
    have h4 : (degW W a : ℝ) * (Dm + (degW W a : ℝ) * Zm)
        ≤ (degW W a : ℝ) * (Dm + ΔW * Zm) := by
      have h5 : (degW W a : ℝ) * Zm ≤ ΔW * Zm := mul_le_mul_of_nonneg_right h2 hZ0
      exact mul_le_mul_of_nonneg_left (by linarith) h3
    exact le_trans h1 h4
  have hsum : ∑ a : Fin N, ∑ b : Fin N,
        ((univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card : ℝ) ^ 2
      ≤ 2 * W.card * (Dm + ΔW * Zm) := by
    have h1 : (∑ a : Fin N, (degW W a : ℝ)) ≤ 2 * W.card := by
      exact_mod_cast sum_degW_le W
    calc ∑ a : Fin N, ∑ b : Fin N,
          ((univ.filter fun x : Fin N => s(a, x) ∈ W ∧ s(x, b) ∈ J).card : ℝ) ^ 2
        ≤ ∑ a : Fin N, (degW W a : ℝ) * (Dm + ΔW * Zm) := sum_le_sum fun a _ => hC a
      _ = (∑ a : Fin N, (degW W a : ℝ)) * (Dm + ΔW * Zm) := (sum_mul _ _ _).symm
      _ ≤ 2 * W.card * (Dm + ΔW * Zm) := mul_le_mul_of_nonneg_right h1 hF0
  linarith [key, hι, hsum]

/-- The image of a graph under an embedding of its vertices has the same maximum degree. -/
theorem degW_map_le {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    [DecidableRel H.Adj] (φ : α ↪ Fin N) {D : ℕ} (hD : ∀ a, H.degree a ≤ D) (b : Fin N) :
    degW (H.edgeFinset.map φ.sym2Map) b ≤ D := by
  classical
  unfold degW
  by_cases hb : ∃ a₀, φ a₀ = b
  · obtain ⟨a₀, rfl⟩ := hb
    refine le_trans (card_le_card (t := (H.neighborFinset a₀).map φ) fun x hx => ?_) ?_
    · obtain ⟨e, he, hex⟩ := mem_map.mp (mem_filter.mp hx).2
      induction e using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        rw [Function.Embedding.sym2Map_apply, Sym2.map_mk] at hex
        rcases Sym2.eq_iff.mp hex with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain rfl := φ.injective h1
          exact mem_map.mpr ⟨v, (H.mem_neighborFinset _ _).mpr he, h2⟩
        · obtain rfl := φ.injective h2
          exact mem_map.mpr ⟨u, (H.mem_neighborFinset _ _).mpr he.symm, h1⟩
    · rw [card_map]
      exact hD a₀
  · refine le_trans (le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun x _ hx => ?_)))
      (Nat.zero_le _)
    obtain ⟨e, -, hex⟩ := mem_map.mp hx
    induction e using Sym2.ind with
    | h u v =>
      rw [Function.Embedding.sym2Map_apply, Sym2.map_mk] at hex
      rcases Sym2.eq_iff.mp hex with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hb ⟨u, h1⟩
      · exact hb ⟨v, h2⟩

end TFP
end E1182

end WCountPart

section GlobalPart

/-
# Good histories of the triangle-free process

`Good N W m s`: the history `s` is valid, all open pairs have `X`, `Y` within the allowed errors
of the trajectory, degrees and codegrees are bounded, and every edge set `W c` still has at
least `(m/2) g` open pairs. The number of open pairs then follows the trajectory
deterministically (`Good.Q_bound`).
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

/-- The horizon of the process (`γ = 1/2000`). -/
noncomputable def hor (N : ℕ) : ℕ := horizon (1 / 2000) N

/-- Degree bound. -/
noncomputable def Dmx (N : ℕ) : ℝ := (N : ℝ) ^ (51 / 100 : ℝ)

/-- Codegree bound. -/
noncomputable def Zmx (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 40 : ℝ)

/-- Upper bound for the closing rate of an open pair at step `i`. -/
noncomputable def abar (N i : ℕ) : ℝ := (1 + yh N i + eY N i) / (Qh N i - eQ N i)

/-- Normalisation of the number of open pairs of a fixed edge set. -/
noncomputable def gW (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => gW N i * (1 - abar N i)

theorem gW_zero (N : ℕ) : gW N 0 = 1 := rfl

theorem gW_succ (N i : ℕ) : gW N (i + 1) = gW N i * (1 - abar N i) := rfl

/-- Good histories. -/
def Good (N : ℕ) {ι : Type*} (W : ι → Finset (Sym2 (Fin N))) (m : ℝ)
    (s : List (Sym2 (Fin N))) : Prop :=
  Valid s ∧
  (∀ u v, Op s.toFinset u v →
      |((Xset s.toFinset u v).card : ℝ) - xh N s.length| ≤ eX N s.length ∧
      |((Yset s.toFinset u v).card : ℝ) - yh N s.length| ≤ eY N s.length) ∧
  (∀ u, ((nb s.toFinset u).card : ℝ) ≤ Dmx N) ∧
  (∀ u v, u ≠ v → ((cod s.toFinset u v).card : ℝ) ≤ Zmx N) ∧
  (∀ c, m / 2 * gW N s.length ≤ ((W c ∩ openSet s.toFinset).card : ℝ))

/-- Numerical facts about the trajectory and the errors up to the horizon. -/
def NumA (N : ℕ) : Prop :=
  ∀ i ≤ hor N, 0 < Qh N i ∧ 0 ≤ eQ N i ∧ 2 * eQ N i ≤ Qh N i ∧ 0 ≤ eX N i ∧
    eX N i ≤ xh N i ∧ 0 ≤ eY N i ∧ 0 ≤ yh N i

section

variable {ι : Type*} {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

theorem goodAt_of (hnum : NumA N) {s : List (Sym2 (Fin N))} (hG : Good N W m s)
    (hQ : |((openSet s.toFinset).card : ℝ) - Qh N s.length| ≤ eQ N s.length)
    (hlen : s.length ≤ hor N) :
    GoodAt s.toFinset (Qh N s.length) (xh N s.length) (yh N s.length) (eX N s.length)
      (eY N s.length) (eQ N s.length) (Dmx N) (Zmx N) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnum s.length hlen
  exact
    { tf := hG.1.tf
      hQ := hQ
      hX := fun a b hab => (hG.2.1 a b hab).1
      hY := fun a b hab => (hG.2.1 a b hab).2
      hD := hG.2.2.1
      hZ := hG.2.2.2.1
      Qh_pos := h1
      eQ0 := h2
      eQ2 := h3
      eX0 := h4
      eXx := h5
      eY0 := h6
      yh0 := h7 }

/-- Along good histories the number of open pairs stays within `eQ` of the trajectory. -/
theorem Good.Q_bound (hnum : NumA N) :
    ∀ s : List (Sym2 (Fin N)), GoodAll (Good N W m) s → s.length ≤ hor N →
      |((openSet s.toFinset).card : ℝ) - Qh N s.length| ≤ eQ N s.length := by
  intro s
  induction s with
  | nil =>
    intro _ _
    simp only [List.toFinset_nil, List.length_nil]
    rw [card_openSet_empty, Qh_zero, eQ_zero]
    simp
  | cons e t ih =>
    intro hs hlen
    obtain ⟨hG, ht⟩ := goodAll_cons.mp hs
    have hlen' : t.length ≤ hor N := by
      rw [List.length_cons] at hlen
      omega
    have hQt := ih ht hlen'
    have hgood := goodAt_of hnum ht.self hQt hlen'
    have he : e ∈ openSet t.toFinset := hG.1.1
    have h1 := hgood.Q_step he
    rw [List.toFinset_cons, List.length_cons, Qh_succ, eQ_succ]
    exact h1

theorem GoodAll.goodAt (hnum : NumA N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length ≤ hor N) :
    GoodAt s.toFinset (Qh N s.length) (xh N s.length) (yh N s.length) (eX N s.length)
      (eY N s.length) (eQ N s.length) (Dmx N) (Zmx N) :=
  goodAt_of hnum hs.self (Good.Q_bound hnum s hs hlen) hlen

theorem GoodAll.openSet_nonempty (hnum : NumA N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length ≤ hor N) :
    (openSet s.toFinset).Nonempty := by
  have h := (hs.goodAt hnum hlen).Q_pos
  exact card_pos.mp (by exact_mod_cast h)

end

end TFP
end E1182

end GlobalPart

section CausesPart

/-
# The potentials for `X` and `Y`

For each ordered pair `uv` and each direction, `pairPot` is an exponential potential that is a
supermartingale along good histories and is large when the corresponding bound fails first.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

noncomputable def lamX (N : ℕ) : ℝ := (N : ℝ) ^ (-(4 / 5 : ℝ))
noncomputable def vX (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 20 : ℝ)
noncomputable def lamY (N : ℕ) : ℝ := (N : ℝ) ^ (-(3 / 10 : ℝ))
noncomputable def vY (N : ℕ) : ℝ := (N : ℝ) ^ (-(19 / 20 : ℝ))

theorem lamX_nonneg (N : ℕ) : 0 ≤ lamX N := Real.rpow_nonneg (Nat.cast_nonneg N) _
theorem vX_nonneg (N : ℕ) : 0 ≤ vX N := Real.rpow_nonneg (Nat.cast_nonneg N) _
theorem lamY_nonneg (N : ℕ) : 0 ≤ lamY N := Real.rpow_nonneg (Nat.cast_nonneg N) _
theorem vY_nonneg (N : ℕ) : 0 ≤ vY N := Real.rpow_nonneg (Nat.cast_nonneg N) _

/-- Numerical facts for the `X` and `Y` supermartingales. -/
def NumB (N : ℕ) : Prop :=
  ∀ i < hor N,
    lamX N * (xh N i * (2 + 2 * yh N i) / Qh N i) ≤ 1 ∧
    lamX N * (2 + 2 * Dmx N) ≤ 1 ∧
    4 * (2 + 2 * Dmx N) * ((xh N i + eX N i) * (2 + 2 * (yh N i + eY N i))) / Qh N i
      + 2 * (xh N i * (2 + 2 * yh N i) / Qh N i
          + DXr (Qh N i) (xh N i) (yh N i) (eX N i) (eY N i) (eQ N i)) ^ 2 ≤ vX N ∧
    lamY N * (2 + Zmx N + |(2 * xh N i - yh N i * (1 + yh N i)) / Qh N i|) ≤ 1 ∧
    2 * (12 * (xh N i + eX N i) + 3 * ((2 + Zmx N) * ((yh N i + eY N i)
        * (1 + yh N i + eY N i)) + (yh N i + eY N i) ^ 2)) / Qh N i
      + 3 * (|(2 * xh N i - yh N i * (1 + yh N i)) / Qh N i|
          + DYr (Qh N i) (xh N i) (yh N i) (eX N i) (eY N i) (eQ N i)) ^ 2 ≤ vY N

/-- A weighted exponential sum is controlled by the unweighted one on the support. -/
theorem pot_super {κ : Type*} (O T : Finset κ) (w δ : κ → ℝ) (E lam v : ℝ)
    (_hw0 : ∀ e ∈ O, 0 ≤ w e) (hw1 : ∀ e ∈ O, w e ≤ 1) (hwT : ∀ e ∈ O, e ∉ T → w e = 0)
    (hT : T ⊆ O)
    (hsum : ∑ e ∈ T, Real.exp (lam * δ e) ≤ O.card * Real.exp (lam ^ 2 * v)) :
    ∑ e ∈ O, w e * Real.exp (E + lam * δ e - lam ^ 2 * v) ≤ O.card * Real.exp E := by
  classical
  have h1 : ∑ e ∈ O, w e * Real.exp (E + lam * δ e - lam ^ 2 * v)
      ≤ ∑ e ∈ T, Real.exp (E + lam * δ e - lam ^ 2 * v) := by
    rw [← sum_subset hT (f := fun e => w e * Real.exp (E + lam * δ e - lam ^ 2 * v))
      (fun e he heT => by rw [hwT e he heT, zero_mul])]
    refine sum_le_sum fun e he => ?_
    have h2 := hw1 e (hT he)
    have h3 := (Real.exp_pos (E + lam * δ e - lam ^ 2 * v)).le
    nlinarith
  have h2 : ∑ e ∈ T, Real.exp (E + lam * δ e - lam ^ 2 * v)
      = Real.exp (E - lam ^ 2 * v) * ∑ e ∈ T, Real.exp (lam * δ e) := by
    rw [mul_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (E - lam ^ 2 * v) * (O.card * Real.exp (lam ^ 2 * v))
      = O.card * Real.exp E := by
    rw [mul_comm (O.card : ℝ), ← mul_assoc, ← Real.exp_add]
    rw [mul_comm]
    congr 2
    ring
  calc ∑ e ∈ O, w e * Real.exp (E + lam * δ e - lam ^ 2 * v)
      ≤ Real.exp (E - lam ^ 2 * v) * ∑ e ∈ T, Real.exp (lam * δ e) := h1.trans (le_of_eq h2)
    _ ≤ Real.exp (E - lam ^ 2 * v) * (O.card * Real.exp (lam ^ 2 * v)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = O.card * Real.exp E := h3

/-- Exponential potential attached to an ordered pair; it vanishes once the pair is not open. -/
noncomputable def pairPot (lam v : ℝ) (U : List (Sym2 (Fin N)) → ℝ) (u w : Fin N)
    (s : List (Sym2 (Fin N))) : ℝ :=
  ind (Op s.toFinset u w) * Real.exp (lam * U s - lam ^ 2 * v * s.length)

theorem pairPot_nonneg (lam v : ℝ) (U : List (Sym2 (Fin N)) → ℝ) (u w : Fin N)
    (s : List (Sym2 (Fin N))) : 0 ≤ pairPot lam v U u w s :=
  mul_nonneg (ind_nonneg _) (Real.exp_pos _).le

theorem pairPot_super {lam v : ℝ} {U : List (Sym2 (Fin N)) → ℝ} {u w : Fin N}
    {s : List (Sym2 (Fin N))} (T : Finset (Sym2 (Fin N))) (hT : T ⊆ openSet s.toFinset)
    (hTmem : ∀ e ∈ openSet s.toFinset, Op (insert e s.toFinset) u w → e ∈ T)
    (hsum : Op s.toFinset u w → ∑ e ∈ T, Real.exp (lam * (U (e :: s) - U s))
      ≤ (openSet s.toFinset).card * Real.exp (lam ^ 2 * v)) :
    ∑ e ∈ openSet s.toFinset, pairPot lam v U u w (e :: s)
      ≤ (openSet s.toFinset).card * pairPot lam v U u w s := by
  by_cases hop : Op s.toFinset u w
  · have h1 := pot_super (openSet s.toFinset) T
      (fun e => ind (Op (insert e s.toFinset) u w)) (fun e => U (e :: s) - U s)
      (lam * U s - lam ^ 2 * v * s.length) lam v (fun e _ => ind_nonneg _)
      (fun e _ => ind_le_one _)
      (fun e he heT => ind_of_not fun hop' => heT (hTmem e he hop')) hT (hsum hop)
    have h2 : pairPot lam v U u w s = Real.exp (lam * U s - lam ^ 2 * v * s.length) := by
      rw [pairPot, ind_of hop, one_mul]
    rw [h2]
    refine le_trans (le_of_eq (sum_congr rfl fun e _ => ?_)) h1
    rw [pairPot, List.toFinset_cons, List.length_cons]
    congr 2
    push_cast
    ring
  · have h1 : ∀ e ∈ openSet s.toFinset, pairPot lam v U u w (e :: s) = 0 := by
      intro e _
      rw [pairPot, List.toFinset_cons,
        ind_of_not fun hop' => hop (Op.mono (subset_insert _ _) hop'), zero_mul]
    rw [sum_congr rfl h1, sum_const_zero, pairPot, ind_of_not hop, zero_mul, mul_zero]

theorem pairPot_ge {lam v : ℝ} (hlam : 0 ≤ lam) (hv : 0 ≤ v) {U : List (Sym2 (Fin N)) → ℝ}
    {u w : Fin N} {t : List (Sym2 (Fin N))} {σ : ℝ} {I : ℕ} (hop : Op t.toFinset u w)
    (hU : σ ≤ U t) (hlen : t.length ≤ I) :
    Real.exp (lam * σ - lam ^ 2 * v * I) ≤ pairPot lam v U u w t := by
  rw [pairPot, ind_of hop, one_mul]
  apply Real.exp_le_exp.mpr
  have h1 : lam * σ ≤ lam * U t := mul_le_mul_of_nonneg_left hU hlam
  have h2 : (t.length : ℝ) ≤ I := by exact_mod_cast hlen
  have h3 : lam ^ 2 * v * t.length ≤ lam ^ 2 * v * I :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg lam) hv)
  linarith

/- ## The four deviation functions -/

noncomputable def UXu (N : ℕ) (u v : Fin N) (s : List (Sym2 (Fin N))) : ℝ :=
  ((Xset s.toFinset u v).card : ℝ) - xh N s.length - (eX N s.length - eX N 0)

noncomputable def UXd (N : ℕ) (u v : Fin N) (s : List (Sym2 (Fin N))) : ℝ :=
  xh N s.length - ((Xset s.toFinset u v).card : ℝ) - (eX N s.length - eX N 0)

noncomputable def UYu (N : ℕ) (u v : Fin N) (s : List (Sym2 (Fin N))) : ℝ :=
  ((Yset s.toFinset u v).card : ℝ) - yh N s.length - (eY N s.length - eY N 0)

noncomputable def UYd (N : ℕ) (u v : Fin N) (s : List (Sym2 (Fin N))) : ℝ :=
  yh N s.length - ((Yset s.toFinset u v).card : ℝ) - (eY N s.length - eY N 0)

theorem eX_step (N i : ℕ) :
    eX N (i + 1) = eX N i + DXr (Qh N i) (xh N i) (yh N i) (eX N i) (eY N i) (eQ N i) := rfl

theorem eY_step (N i : ℕ) :
    eY N (i + 1) = eY N i + DYr (Qh N i) (xh N i) (yh N i) (eX N i) (eY N i) (eQ N i) := rfl

theorem xh_step (N i : ℕ) : xh N (i + 1) = xh N i - xh N i * (2 + 2 * yh N i) / Qh N i := rfl

theorem yh_step (N i : ℕ) :
    yh N (i + 1) = yh N i + (2 * xh N i - yh N i * (1 + yh N i)) / Qh N i := rfl

theorem UXu_step (u v : Fin N) (e : Sym2 (Fin N)) (s : List (Sym2 (Fin N))) :
    UXu N u v (e :: s) - UXu N u v s
      = (((Xset (insert e s.toFinset) u v).card : ℝ) - (Xset s.toFinset u v).card)
        + xh N s.length * (2 + 2 * yh N s.length) / Qh N s.length
        - DXr (Qh N s.length) (xh N s.length) (yh N s.length) (eX N s.length)
            (eY N s.length) (eQ N s.length) := by
  simp only [UXu, List.toFinset_cons, List.length_cons, xh_step, eX_step]
  ring

theorem UXd_step (u v : Fin N) (e : Sym2 (Fin N)) (s : List (Sym2 (Fin N))) :
    UXd N u v (e :: s) - UXd N u v s
      = -(((Xset (insert e s.toFinset) u v).card : ℝ) - (Xset s.toFinset u v).card)
        - xh N s.length * (2 + 2 * yh N s.length) / Qh N s.length
        - DXr (Qh N s.length) (xh N s.length) (yh N s.length) (eX N s.length)
            (eY N s.length) (eQ N s.length) := by
  simp only [UXd, List.toFinset_cons, List.length_cons, xh_step, eX_step]
  ring

theorem UYu_step (u v : Fin N) (e : Sym2 (Fin N)) (s : List (Sym2 (Fin N))) :
    UYu N u v (e :: s) - UYu N u v s
      = (((Yset (insert e s.toFinset) u v).card : ℝ) - (Yset s.toFinset u v).card)
        - (2 * xh N s.length - yh N s.length * (1 + yh N s.length)) / Qh N s.length
        - DYr (Qh N s.length) (xh N s.length) (yh N s.length) (eX N s.length)
            (eY N s.length) (eQ N s.length) := by
  simp only [UYu, List.toFinset_cons, List.length_cons, yh_step, eY_step]
  ring

theorem UYd_step (u v : Fin N) (e : Sym2 (Fin N)) (s : List (Sym2 (Fin N))) :
    UYd N u v (e :: s) - UYd N u v s
      = -(((Yset (insert e s.toFinset) u v).card : ℝ) - (Yset s.toFinset u v).card)
        + (2 * xh N s.length - yh N s.length * (1 + yh N s.length)) / Qh N s.length
        - DYr (Qh N s.length) (xh N s.length) (yh N s.length) (eX N s.length)
            (eY N s.length) (eQ N s.length) := by
  simp only [UYd, List.toFinset_cons, List.length_cons, yh_step, eY_step]
  ring

section

variable {ι : Type*} {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

theorem super_Xu (hA : NumA N) (hB : NumB N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (u v : Fin N) :
    ∑ e ∈ openSet s.toFinset, pairPot (lamX N) (vX N) (UXu N u v) u v (e :: s)
      ≤ (openSet s.toFinset).card * pairPot (lamX N) (vX N) (UXu N u v) u v s := by
  refine pairPot_super (openSet s.toFinset) (Subset.refl _) (fun e he _ => he) (fun huv => ?_)
  have hg := hs.goodAt hA hlen.le
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB s.length hlen
  have h1 := hg.exp_X_up huv (lamX_nonneg N) b1 b3
  simp_rw [UXu_step]
  exact h1

theorem super_Xd (hA : NumA N) (hB : NumB N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (u v : Fin N) :
    ∑ e ∈ openSet s.toFinset, pairPot (lamX N) (vX N) (UXd N u v) u v (e :: s)
      ≤ (openSet s.toFinset).card * pairPot (lamX N) (vX N) (UXd N u v) u v s := by
  refine pairPot_super (openSet s.toFinset) (Subset.refl _) (fun e he _ => he) (fun huv => ?_)
  have hg := hs.goodAt hA hlen.le
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB s.length hlen
  have h1 := hg.exp_X_down huv (lamX_nonneg N) b2 b3
  simp_rw [UXd_step]
  exact h1

theorem super_Yu (hA : NumA N) (hB : NumB N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (u v : Fin N) :
    ∑ e ∈ openSet s.toFinset, pairPot (lamY N) (vY N) (UYu N u v) u v (e :: s)
      ≤ (openSet s.toFinset).card * pairPot (lamY N) (vY N) (UYu N u v) u v s := by
  refine pairPot_super (openSet s.toFinset) (Subset.refl _) (fun e he _ => he) (fun huv => ?_)
  have hg := hs.goodAt hA hlen.le
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB s.length hlen
  have hZ0 := hg.Zm_nonneg huv
  have hc : lamY N * (2 + |(2 * xh N s.length - yh N s.length * (1 + yh N s.length))
      / Qh N s.length|) ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (lamY_nonneg N)) b4
    linarith
  have h1 := hg.exp_Y_up huv (lamY_nonneg N) hc b5
  simp_rw [UYu_step]
  exact h1

theorem super_Yd (hA : NumA N) (hB : NumB N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (u v : Fin N) :
    ∑ e ∈ openSet s.toFinset, pairPot (lamY N) (vY N) (UYd N u v) u v (e :: s)
      ≤ (openSet s.toFinset).card * pairPot (lamY N) (vY N) (UYd N u v) u v s := by
  classical
  refine pairPot_super ((openSet s.toFinset).erase s(u, v)) (erase_subset _ _)
    (fun e he hop => mem_erase.mpr ⟨fun h => hop.2.1 (h ▸ mem_insert_self _ _), he⟩)
    (fun huv => ?_)
  have hg := hs.goodAt hA hlen.le
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB s.length hlen
  have h1 := hg.exp_Y_down huv (lamY_nonneg N) b4 b5
  simp_rw [UYd_step]
  exact h1

end

end TFP
end E1182

end CausesPart

section Causes2Part

/-
# The potentials for degrees, codegrees and fixed edge sets
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

/-- Lower bound for the number of open pairs along good histories. -/
noncomputable def Qmin (N : ℕ) : ℝ := (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) / 2

noncomputable def rhoD (N : ℕ) : ℝ := 1 + N / Qmin N

noncomputable def rhoZ (N : ℕ) : ℝ := 1 + 2 * Dmx N / Qmin N

/-- Numerical facts: the number of open pairs stays above `Qmin`. -/
def NumC (N : ℕ) : Prop :=
  0 < Qmin N ∧ ∀ i ≤ hor N, Qmin N ≤ Qh N i - eQ N i

theorem Dmx_nonneg (N : ℕ) : 0 ≤ Dmx N := Real.rpow_nonneg (Nat.cast_nonneg N) _

theorem Zmx_nonneg (N : ℕ) : 0 ≤ Zmx N := Real.rpow_nonneg (Nat.cast_nonneg N) _

/-- Degree potential. -/
noncomputable def PsiD (N : ℕ) (u : Fin N) (s : List (Sym2 (Fin N))) : ℝ :=
  2 ^ (nb s.toFinset u).card / rhoD N ^ s.length

open Classical in
/-- Codegree potential. -/
noncomputable def PsiZ (N : ℕ) (u v : Fin N) (s : List (Sym2 (Fin N))) : ℝ :=
  if u = v then 0 else 2 ^ (cod s.toFinset u v).card / rhoZ N ^ s.length

theorem rhoD_ge_one (hC : NumC N) : 1 ≤ rhoD N := by
  unfold rhoD
  have := div_nonneg (Nat.cast_nonneg (α := ℝ) N) hC.1.le
  linarith

theorem rhoZ_ge_one (hC : NumC N) : 1 ≤ rhoZ N := by
  unfold rhoZ
  have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Dmx_nonneg N)) hC.1.le
  linarith

theorem PsiD_nonneg (hC : NumC N) (u : Fin N) (s : List (Sym2 (Fin N))) : 0 ≤ PsiD N u s := by
  have := rhoD_ge_one hC
  unfold PsiD
  positivity

theorem PsiZ_nonneg (hC : NumC N) (u v : Fin N) (s : List (Sym2 (Fin N))) :
    0 ≤ PsiZ N u v s := by
  have := rhoZ_ge_one hC
  unfold PsiZ
  split_ifs
  · exact le_refl _
  · positivity

/-- A common step: `S ≤ P (Q + K)` and `K ≤ Q K'/Qmin`-type bound give the supermartingale
inequality for a potential `P / ρ^i`. -/
theorem pow_pot_step {S P Q K ρ : ℝ} {i : ℕ} (hρ : 0 < ρ) (hP : 0 ≤ P)
    (hS : S ≤ P * (Q + K)) (hK : Q + K ≤ Q * ρ) :
    S / ρ ^ (i + 1) ≤ Q * (P / ρ ^ i) := by
  have hpow : 0 < ρ ^ i := pow_pos hρ i
  rw [div_le_iff₀ (pow_pos hρ (i + 1))]
  have h1 : Q * (P / ρ ^ i) * ρ ^ (i + 1) = P * (Q * ρ) := by
    rw [pow_succ]
    field_simp
  rw [h1]
  exact hS.trans (mul_le_mul_of_nonneg_left hK hP)

section

variable {ι : Type*} {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

theorem super_D (hA : NumA N) (hC : NumC N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (u : Fin N) :
    ∑ e ∈ openSet s.toFinset, PsiD N u (e :: s)
      ≤ (openSet s.toFinset).card * PsiD N u s := by
  have hg := hs.goodAt hA hlen.le
  have hQ : Qmin N ≤ ((openSet s.toFinset).card : ℝ) := le_trans (hC.2 _ hlen.le) hg.Q_lower
  have hρ : 0 < rhoD N := lt_of_lt_of_le one_pos (rhoD_ge_one hC)
  have h1 := sum_two_pow_nb_le s.toFinset u
  have h2 : ((openSet s.toFinset).card : ℝ) + N ≤ (openSet s.toFinset).card * rhoD N := by
    unfold rhoD
    rw [mul_add, mul_one, mul_div_assoc']
    have h3 : (N : ℝ) ≤ (openSet s.toFinset).card * N / Qmin N := by
      rw [le_div_iff₀ hC.1]
      have := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α := ℝ) N)
      linarith
    linarith
  have h3 := pow_pot_step (i := s.length) hρ (by positivity) h1 h2
  simp only [PsiD, List.toFinset_cons, List.length_cons]
  rw [← sum_div]
  exact h3

theorem super_Z (hA : NumA N) (hC : NumC N) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (u v : Fin N) :
    ∑ e ∈ openSet s.toFinset, PsiZ N u v (e :: s)
      ≤ (openSet s.toFinset).card * PsiZ N u v s := by
  by_cases huv : u = v
  · simp [PsiZ, huv]
  have hg := hs.goodAt hA hlen.le
  have hQ : Qmin N ≤ ((openSet s.toFinset).card : ℝ) := le_trans (hC.2 _ hlen.le) hg.Q_lower
  have hρ : 0 < rhoZ N := lt_of_lt_of_le one_pos (rhoZ_ge_one hC)
  have h1 := sum_two_pow_cod_le hg.tf huv
  have hdeg : (((nb s.toFinset u).card + (nb s.toFinset v).card : ℕ) : ℝ) ≤ 2 * Dmx N := by
    push_cast
    have := hg.hD u
    have := hg.hD v
    linarith
  have h1' : ∑ e ∈ openSet s.toFinset, (2 : ℝ) ^ (cod (insert e s.toFinset) u v).card
      ≤ 2 ^ (cod s.toFinset u v).card * ((openSet s.toFinset).card + 2 * Dmx N) := by
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have h2 : ((openSet s.toFinset).card : ℝ) + 2 * Dmx N
      ≤ (openSet s.toFinset).card * rhoZ N := by
    unfold rhoZ
    rw [mul_add, mul_one, mul_div_assoc']
    have h3 : 2 * Dmx N ≤ (openSet s.toFinset).card * (2 * Dmx N) / Qmin N := by
      rw [le_div_iff₀ hC.1]
      have := mul_le_mul_of_nonneg_right hQ
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Dmx_nonneg N))
      linarith
    linarith
  have h3 := pow_pot_step (i := s.length) hρ (by positivity) h1' h2
  simp only [PsiZ, if_neg huv, List.toFinset_cons, List.length_cons]
  rw [← sum_div]
  exact h3

/-- A large degree makes the degree potential large. -/
theorem PsiD_ge (hC : NumC N) {u : Fin N} {t : List (Sym2 (Fin N))}
    (hdeg : Dmx N ≤ ((nb t.toFinset u).card : ℝ)) (hlen : t.length ≤ hor N) :
    (2 : ℝ) ^ (Dmx N) / rhoD N ^ hor N ≤ PsiD N u t := by
  have hρ1 := rhoD_ge_one hC
  have hρ : 0 < rhoD N := lt_of_lt_of_le one_pos hρ1
  unfold PsiD
  have h1 : (2 : ℝ) ^ (Dmx N) ≤ (2 : ℝ) ^ (nb t.toFinset u).card := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hdeg
  have h2 : rhoD N ^ t.length ≤ rhoD N ^ hor N := pow_le_pow_right₀ hρ1 hlen
  calc (2 : ℝ) ^ (Dmx N) / rhoD N ^ hor N
      ≤ (2 : ℝ) ^ (nb t.toFinset u).card / rhoD N ^ hor N :=
        div_le_div_of_nonneg_right h1 (pow_pos hρ _).le
    _ ≤ (2 : ℝ) ^ (nb t.toFinset u).card / rhoD N ^ t.length :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hρ _) h2

/-- A large codegree makes the codegree potential large. -/
theorem PsiZ_ge (hC : NumC N) {u v : Fin N} (huv : u ≠ v) {t : List (Sym2 (Fin N))}
    (hcod : Zmx N ≤ ((cod t.toFinset u v).card : ℝ)) (hlen : t.length ≤ hor N) :
    (2 : ℝ) ^ (Zmx N) / rhoZ N ^ hor N ≤ PsiZ N u v t := by
  have hρ1 := rhoZ_ge_one hC
  have hρ : 0 < rhoZ N := lt_of_lt_of_le one_pos hρ1
  simp only [PsiZ, if_neg huv]
  have h1 : (2 : ℝ) ^ (Zmx N) ≤ (2 : ℝ) ^ (cod t.toFinset u v).card := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcod
  have h2 : rhoZ N ^ t.length ≤ rhoZ N ^ hor N := pow_le_pow_right₀ hρ1 hlen
  calc (2 : ℝ) ^ (Zmx N) / rhoZ N ^ hor N
      ≤ (2 : ℝ) ^ (cod t.toFinset u v).card / rhoZ N ^ hor N :=
        div_le_div_of_nonneg_right h1 (pow_pos hρ _).le
    _ ≤ (2 : ℝ) ^ (cod t.toFinset u v).card / rhoZ N ^ t.length :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hρ _) h2

end

end TFP
end E1182

end Causes2Part

section CausesWPart

/-
# The potential for a fixed edge set

`PsiW` controls the lower deviation of the number of open pairs of a fixed edge set `Wc`
(normalised by `gW`), with a Bennett-type exponential supermartingale.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

/-- Lower bound for the closing rate of an open pair at step `i`. -/
noncomputable def alow (N i : ℕ) : ℝ := (1 + max (yh N i - eY N i) 0) / (Qh N i + eQ N i)

/-- Potential for the edge set `Wc`. -/
noncomputable def PsiW (N : ℕ) (Wc : Finset (Sym2 (Fin N))) (m lamW CW : ℝ)
    (s : List (Sym2 (Fin N))) : ℝ :=
  Real.exp (lamW * (m - ((Wc ∩ openSet s.toFinset).card : ℝ) / gW N s.length) - CW * s.length)

/-- Numerical facts for edge sets of size `m` and maximum degree `ΔW`. -/
def NumW (N : ℕ) (m ΔW lamW B₀ vW : ℝ) : Prop :=
  0 ≤ lamW ∧ 0 ≤ B₀ ∧ ∀ i < hor N,
    0 < gW N i ∧ 0 < gW N (i + 1) ∧
    lamW * ((1 + yh N i + eY N i) / gW N (i + 1)) ≤ B₀ ∧
    (3 * m * (1 + 2 * Dmx N + 2 * ΔW * Zmx N)) / (Qmin N * gW N (i + 1) ^ 2)
      + abar N i * (abar N i - alow N i) * m ^ 2 / gW N (i + 1) ^ 2 ≤ vW

section

variable {ι : Type*} {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

set_option maxHeartbeats 1600000 in
theorem super_W (hA : NumA N) (hC : NumC N) {ΔW lamW B₀ vW : ℝ}
    (hWn : NumW N m ΔW lamW B₀ vW) {s : List (Sym2 (Fin N))}
    (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) (Wc : Finset (Sym2 (Fin N)))
    (hcard : (Wc.card : ℝ) = m) (hΔ : ∀ a, (degW Wc a : ℝ) ≤ ΔW) :
    ∑ e ∈ openSet s.toFinset, PsiW N Wc m lamW (Real.exp B₀ * (lamW ^ 2 * vW)) (e :: s)
      ≤ (openSet s.toFinset).card * PsiW N Wc m lamW (Real.exp B₀ * (lamW ^ 2 * vW)) s := by
  classical
  have hg := hs.goodAt hA hlen.le
  obtain ⟨hlam, hB0, hW⟩ := hWn
  obtain ⟨hgi, hgi1, hb, hv⟩ := hW s.length hlen
  set J := s.toFinset with hJ
  set i := s.length with hi
  obtain ⟨CW, hCW⟩ : ∃ CW, CW = Real.exp B₀ * (lamW ^ 2 * vW) := ⟨_, rfl⟩
  rw [← hCW]
  obtain ⟨XW, hXW⟩ : ∃ XW : ℝ, XW = ((Wc ∩ openSet J).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨loss, hloss⟩ : ∃ loss : Sym2 (Fin N) → ℝ, loss = fun e =>
      (((Wc ∩ openSet J) \ (Wc ∩ openSet (insert e J))).card : ℝ) := ⟨_, rfl⟩
  have hlossdef : ∀ e, loss e
      = (((Wc ∩ openSet J) \ (Wc ∩ openSet (insert e J))).card : ℝ) := fun e => by rw [hloss]
  have hXW0 : 0 ≤ XW := by rw [hXW]; exact Nat.cast_nonneg _
  have hXWm : XW ≤ m := by
    rw [hXW, ← hcard]
    exact_mod_cast card_le_card inter_subset_left
  have hQh := hg.Qh_pos
  have hQpos := hg.Q_pos
  have hQlo := hg.Q_lower
  have hQhi := hg.Q_upper
  have heQ0 := hg.eQ0
  have heQ2 := hg.eQ2
  have heY0 := hg.eY0
  have hyh0 := hg.yh0
  have hden1 : 0 < Qh N i - eQ N i := by linarith
  have hden2 : 0 < Qh N i + eQ N i := by linarith
  have hym0 : (0 : ℝ) ≤ max (yh N i - eY N i) 0 := le_max_right _ _
  have hymle : max (yh N i - eY N i) 0 ≤ yh N i + eY N i := max_le (by linarith) (by linarith)
  have hQmin : Qmin N ≤ ((openSet J).card : ℝ) := by
    exact le_trans (hC.2 _ hlen.le) hQlo
  -- `1 - abar > 0`
  have h1a : 0 < 1 - abar N i := by
    have h1 : gW N (i + 1) = gW N i * (1 - abar N i) := gW_succ N i
    rw [h1] at hgi1
    exact (mul_pos_iff_of_pos_left hgi).mp hgi1
  -- the open pairs of `Wc` after one step
  have hcardstep : ∀ e, ((Wc ∩ openSet (insert e J)).card : ℝ) = XW - loss e := by
    intro e
    have h1 : Wc ∩ openSet (insert e J) ⊆ Wc ∩ openSet J :=
      inter_subset_inter (Subset.refl _) (openSet_insert_subset e)
    have h2 := card_sdiff_add_card_eq_card h1
    have h3 : (((Wc ∩ openSet J) \ (Wc ∩ openSet (insert e J))).card : ℝ)
        + (Wc ∩ openSet (insert e J)).card = (Wc ∩ openSet J).card := by exact_mod_cast h2
    rw [hXW, hlossdef]
    linarith
  have hstep : ∀ e ∈ openSet J, PsiW N Wc m lamW CW (e :: s)
      = PsiW N Wc m lamW CW s * Real.exp (-CW)
        * Real.exp (lamW * ((loss e - abar N i * XW) / gW N (i + 1))) := by
    intro e _
    have hkey : (XW - loss e) / gW N (i + 1)
        = XW / gW N i - (loss e - abar N i * XW) / gW N (i + 1) := by
      rw [gW_succ]
      field_simp
      ring
    rw [PsiW, PsiW, List.toFinset_cons, List.length_cons, ← hJ, ← hi, hcardstep, ← hXW,
      ← Real.exp_add, ← Real.exp_add, hkey]
    congr 1
    push_cast
    ring
  -- bounds on the total loss
  have hsumloss : ∑ e ∈ openSet J, loss e = ∑ f ∈ Wc ∩ openSet J, (1 + (Ys J f : ℝ)) := by
    have h1 := sum_W_lost hg.tf Wc
    simp only [hlossdef]
    exact_mod_cast h1
  have hYs : ∀ f ∈ Wc ∩ openSet J,
      max (yh N i - eY N i) 0 ≤ (Ys J f : ℝ) ∧ (Ys J f : ℝ) ≤ yh N i + eY N i := by
    intro f hf
    obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_openSet (mem_inter.mp hf).2
    rw [Ys_mk]
    exact ⟨hg.Y_lower hab, hg.Y_upper hab⟩
  have hlo : ((openSet J).card : ℝ) * alow N i * XW ≤ ∑ e ∈ openSet J, loss e := by
    rw [hsumloss]
    have h1 : ∑ _f ∈ Wc ∩ openSet J, (1 + max (yh N i - eY N i) 0)
        ≤ ∑ f ∈ Wc ∩ openSet J, (1 + (Ys J f : ℝ)) :=
      sum_le_sum fun f hf => by have := (hYs f hf).1; linarith
    rw [sum_const, nsmul_eq_mul, ← hXW] at h1
    have h2 : ((openSet J).card : ℝ) * alow N i ≤ 1 + max (yh N i - eY N i) 0 := by
      unfold alow
      rw [mul_div_assoc', div_le_iff₀ hden2]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hXW0
    linarith
  have hhi : ∑ e ∈ openSet J, loss e ≤ ((openSet J).card : ℝ) * abar N i * XW := by
    rw [hsumloss]
    have h1 : ∑ f ∈ Wc ∩ openSet J, (1 + (Ys J f : ℝ))
        ≤ ∑ _f ∈ Wc ∩ openSet J, (1 + (yh N i + eY N i)) :=
      sum_le_sum fun f hf => by have := (hYs f hf).2; linarith
    rw [sum_const, nsmul_eq_mul, ← hXW] at h1
    have h2 : 1 + (yh N i + eY N i) ≤ ((openSet J).card : ℝ) * abar N i := by
      unfold abar
      rw [mul_div_assoc', le_div_iff₀ hden1]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hXW0
    linarith
  have halow0 : 0 ≤ alow N i := by
    unfold alow
    exact div_nonneg (by linarith) hden2.le
  have hab : alow N i ≤ abar N i := by
    unfold alow abar
    rw [div_le_div_iff₀ hden2 hden1]
    have h1 : 1 + max (yh N i - eY N i) 0 ≤ 1 + yh N i + eY N i := by linarith
    have h2 : Qh N i - eQ N i ≤ Qh N i + eQ N i := by linarith
    exact mul_le_mul h1 h2 hden1.le (by linarith)
  have habar0 : 0 ≤ abar N i := le_trans halow0 hab
  -- second moment
  obtain ⟨S2, hS2def⟩ : ∃ S2, S2 = 3 * m * (1 + 2 * Dmx N + 2 * ΔW * Zmx N) := ⟨_, rfl⟩
  have hS2 : ∑ e ∈ openSet J, loss e ^ 2 ≤ S2 := by
    have h1 := hg.sum_W_lost_sq_le (Dmx_nonneg N) (Zmx_nonneg N) Wc hΔ
    rw [hcard] at h1
    simp only [hlossdef]
    rw [hS2def]
    exact h1
  have hS20 : 0 ≤ S2 := le_trans (sum_nonneg fun e _ => sq_nonneg _) hS2
  -- increments
  have hbb : ∀ e ∈ openSet J, lamW * (loss e / gW N (i + 1)) ≤ B₀ := by
    intro e he
    obtain ⟨a, b, rfl, hab'⟩ := exists_of_mem_openSet he
    have h1 := W_lost_card_le_Ys hg.tf hab' Wc
    have h2 : loss s(a, b) ≤ 1 + ((Yset J a b).card : ℝ) := by
      rw [hlossdef]
      exact_mod_cast h1
    have h3 := hg.Y_upper hab'
    have h4 : loss s(a, b) / gW N (i + 1) ≤ (1 + yh N i + eY N i) / gW N (i + 1) :=
      div_le_div_of_nonneg_right (by linarith) hgi1.le
    exact le_trans (mul_le_mul_of_nonneg_left h4 hlam) hb
  -- variance hypothesis
  rw [← hS2def] at hv
  have hV : (S2 + ((openSet J).card : ℝ) * abar N i * (abar N i - alow N i) * XW ^ 2)
      / gW N (i + 1) ^ 2 ≤ ((openSet J).card : ℝ) * vW := by
    have hg2 : 0 < gW N (i + 1) ^ 2 := pow_pos hgi1 2
    obtain ⟨x1, hx1⟩ : ∃ x1, x1 = S2 / gW N (i + 1) ^ 2 := ⟨_, rfl⟩
    have hx10 : 0 ≤ x1 := by rw [hx1]; exact div_nonneg hS20 hg2.le
    have t1 : x1 ≤ ((openSet J).card : ℝ) * (S2 / (Qmin N * gW N (i + 1) ^ 2)) := by
      have h1 : S2 / (Qmin N * gW N (i + 1) ^ 2) = x1 / Qmin N := by
        rw [hx1]
        field_simp
      rw [h1, mul_div_assoc', le_div_iff₀ hC.1]
      have h2 := mul_le_mul_of_nonneg_left hQmin hx10
      linarith
    obtain ⟨kk, hkk⟩ : ∃ kk, kk = abar N i * (abar N i - alow N i) / gW N (i + 1) ^ 2 :=
      ⟨_, rfl⟩
    have hkk0 : 0 ≤ kk := by
      rw [hkk]
      exact div_nonneg (mul_nonneg habar0 (by linarith)) hg2.le
    have hsq : XW ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hXW0 hXWm 2
    have t2 : ((openSet J).card : ℝ) * abar N i * (abar N i - alow N i) * XW ^ 2
          / gW N (i + 1) ^ 2 ≤ ((openSet J).card : ℝ) * (kk * m ^ 2) := by
      have h1 : ((openSet J).card : ℝ) * abar N i * (abar N i - alow N i) * XW ^ 2
          / gW N (i + 1) ^ 2 = ((openSet J).card : ℝ) * (kk * XW ^ 2) := by
        rw [hkk]
        field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hkk0) hQpos.le
    have h3 : abar N i * (abar N i - alow N i) * m ^ 2 / gW N (i + 1) ^ 2 = kk * m ^ 2 := by
      rw [hkk]
      field_simp
    rw [h3] at hv
    have t3 := mul_le_mul_of_nonneg_left hv hQpos.le
    rw [mul_add] at t3
    rw [add_div, ← hx1]
    linarith
  have hben := bennett_step (openSet J) loss hXW0 halow0 hab hgi1 hlam hB0 hlo hhi hS2 hbb hV
  rw [← hCW] at hben
  have hPsi0 : 0 ≤ PsiW N Wc m lamW CW s * Real.exp (-CW) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc ∑ e ∈ openSet J, PsiW N Wc m lamW CW (e :: s)
      = PsiW N Wc m lamW CW s * Real.exp (-CW)
          * ∑ e ∈ openSet J, Real.exp (lamW * ((loss e - abar N i * XW) / gW N (i + 1))) := by
        rw [mul_sum]
        exact sum_congr rfl hstep
    _ ≤ PsiW N Wc m lamW CW s * Real.exp (-CW) * (((openSet J).card : ℝ) * Real.exp CW) :=
        mul_le_mul_of_nonneg_left hben hPsi0
    _ = ((openSet J).card : ℝ) * PsiW N Wc m lamW CW s := by
        have h1 : Real.exp (-CW) * Real.exp CW = 1 := by
          rw [← Real.exp_add]
          simp
        calc PsiW N Wc m lamW CW s * Real.exp (-CW) * (((openSet J).card : ℝ) * Real.exp CW)
            = ((openSet J).card : ℝ) * PsiW N Wc m lamW CW s
                * (Real.exp (-CW) * Real.exp CW) := by ring
          _ = ((openSet J).card : ℝ) * PsiW N Wc m lamW CW s := by rw [h1, mul_one]

/-- If the edge set has too few open pairs, its potential is large. -/
theorem PsiW_ge {Wc : Finset (Sym2 (Fin N))} {m lamW CW : ℝ} (hlam : 0 ≤ lamW) (hCW : 0 ≤ CW)
    {t : List (Sym2 (Fin N))} (hg : 0 < gW N t.length)
    (hfail : ((Wc ∩ openSet t.toFinset).card : ℝ) < m / 2 * gW N t.length)
    (hlen : t.length ≤ hor N) :
    Real.exp (lamW * (m / 2) - CW * hor N) ≤ PsiW N Wc m lamW CW t := by
  unfold PsiW
  apply Real.exp_le_exp.mpr
  have h1 : ((Wc ∩ openSet t.toFinset).card : ℝ) / gW N t.length < m / 2 := by
    rw [div_lt_iff₀ hg]
    exact hfail
  have h2 : lamW * (m / 2)
      ≤ lamW * (m - ((Wc ∩ openSet t.toFinset).card : ℝ) / gW N t.length) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam
  have h3 : (t.length : ℝ) ≤ hor N := by exact_mod_cast hlen
  have h4 : CW * t.length ≤ CW * hor N := mul_le_mul_of_nonneg_left h3 hCW
  linarith

end

end TFP
end E1182

end CausesWPart

section NumDefsPart

/-
# Parameters of the final union bound and the list of numerical facts

`NumAll A N` collects every numerical inequality (about the trajectory, the error sequences and
the chosen parameters) that the combinatorial argument uses at the scale `N`.
-/

open Finset

namespace E1182
namespace TFP

/-- Bound for the exponent in the Bennett step. -/
noncomputable def B0 (N : ℕ) : ℝ := Real.log N / 100

/-- Exponential parameter for the edge-set potentials. -/
noncomputable def lamWn (N : ℕ) : ℝ := B0 N / (11 * hor N / N)

/-- Per-step second-moment allowance for an edge set with `m` pairs. -/
noncomputable def vWn (N : ℕ) (m : ℝ) : ℝ :=
  144 * m * (N : ℝ) ^ (-(107 / 100 : ℝ)) + 800 * m ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ))

/-- Per-step compensation in the edge-set potential. -/
noncomputable def CWn (N : ℕ) (m : ℝ) : ℝ := Real.exp (B0 N) * (lamWn N ^ 2 * vWn N m)

/-- Thresholds of the potentials. -/
noncomputable def LamX (N : ℕ) : ℝ := Real.exp (lamX N * eX N 0 - lamX N ^ 2 * vX N * hor N)

noncomputable def LamY (N : ℕ) : ℝ := Real.exp (lamY N * eY N 0 - lamY N ^ 2 * vY N * hor N)

noncomputable def LamD (N : ℕ) : ℝ := (2 : ℝ) ^ (Dmx N) / rhoD N ^ hor N

noncomputable def LamZ (N : ℕ) : ℝ := (2 : ℝ) ^ (Zmx N) / rhoZ N ^ hor N

noncomputable def LamW (N : ℕ) (m : ℝ) : ℝ :=
  Real.exp (lamWn N * (m / 2) - CWn N m * hor N)

/-- The numerical facts not involving edge sets. -/
structure NumGlobal (N : ℕ) : Prop where
  hN : 2 ≤ N
  nA : NumA N
  nB : NumB N
  nC : NumC N
  fX : 40 * (N : ℝ) ^ 2 ≤ LamX N
  fY : 40 * (N : ℝ) ^ 2 ≤ LamY N
  fD : 40 * (N : ℝ) ^ 2 ≤ LamD N
  fZ : 40 * (N : ℝ) ^ 2 ≤ LamZ N

/-- The numerical facts about edge sets (`A` is the density constant). -/
structure NumEdge (A : ℝ) (N : ℕ) : Prop where
  gpos : ∀ i ≤ hor N, 0 < gW N i
  nS : ∀ i < hor N, 2 * (Qh N i + eQ N i) ≤ 5 * (N.choose 2 : ℝ) * gW N i
  nW : ∀ m : ℝ, 0 ≤ m → m ≤ (N.choose 2 : ℝ) →
    NumW N m ((N : ℝ) ^ (9 / 10 : ℝ)) (lamWn N) (B0 N) (vWn N m)
  cW0 : ∀ m : ℝ, 0 ≤ m → 0 ≤ CWn N m
  f2 : ∀ (k : ℕ) (m : ℝ), 1 ≤ k → k ≤ N → A * k * Real.sqrt (N * Real.log N) ≤ m →
    m ≤ (N.choose 2 : ℝ) →
      8 * (N : ℝ) ^ k ≤ LamW N m ∧
      (N : ℝ) ^ k * (1 - m / (5 * (N.choose 2 : ℝ))) ^ hor N ≤ 1 / 8

end TFP
end E1182

end NumDefsPart

section ReductionPart

/-
# Erdős Problem 1182 (i): reduction of the upper bound to a blocker statement

This part proves no upper bound by itself. It reduces

  `f(n) = O(n^{3/2} √(log n))`

to `BlockerStatement`: for all large `N`, every graph `H` on at least one and at most `N` vertices
with maximum degree at most `N^{9/10}` and at least `A · v(H) · √(N log N)` edges is *blocked* by
some triangle-free graph `C` on `N` vertices (every injection of `V(H)` into `V(C)` sends an edge of
`H` to an edge of `C`).

* `f_isBigO_of_blocker : BlockerStatement → f(n) = O(n^{3/2} √(log n))`;
* `f_isTheta_of_blocker : BlockerStatement → f(n) = Θ(n^{3/2} √(log n))`
  (with `isBigO_f_lower` from the summary part).

`BlockerStatement` is a hypothesis in this part; it is proved in `FinalPart`
(`blockerStatement`).

The hypothesis `0 < Fintype.card α` in `BlockerAt` cannot be dropped: the graph with no vertices
satisfies the other three hypotheses (`0 ≤ N`, no vertex, `A · 0 · √(N log N) ≤ 0`), but it has no
edge, so it is blocked by nothing.

## The reduction

It is the degree-splitting argument (Lemma 3 of the Zenodo preprint cited in `NOTES.md`), in the
following form. Put `N = 2n - 1`, `d = ⌊N^{9/10}⌋`, `k = ⌈A √(N log N)⌉`.
A graph `G` on `n` vertices with at least `8kn` edges has a subgraph `G₀` with exactly `8kn` edges.
Let `U` be the set of vertices of `G₀`-degree `> d` and `h = |U|`; then `h (d+1) ≤ 16kn`, so
`2h ≤ d` and `2h ≤ n` for large `n`. Counting ordered adjacent pairs,

  `2 e(G₀) = Q + P + 2R`,

with `Q`, `P`, `R` the numbers of such pairs inside `U`, inside `Uᶜ`, and from `Uᶜ` to `U`. One of
`2P`, `2Q`, `2R` is at least `e(G₀)`, and correspondingly one takes

* the edges of `G₀` inside `Uᶜ` (degrees `≤ d` by the definition of `U`), `S = Uᶜ`;
* the edges of `G₀` inside `U` (degrees `≤ h`), `S = U`;
* the edges of `G₀` joining `U` to `T`, where `T ⊆ Uᶜ` consists of `h` vertices with the most
  neighbours in `U` (degrees `≤ 2h`), `S = T ∪ U`.

In each case the chosen graph `H` has all its edges inside the nonempty set `S`, maximum degree
`≤ d` and at least `k |S|` edges, so `BlockerAt A N` applies to `H` restricted to `S`.
The resulting bound is `f(n) ≤ 8kn ≤ (16A + 8) n^{3/2} √(log n)` for all large `n`.
-/

namespace E1182

/-- At scale `N` with constant `A`: every graph `H` on at least one and at most `N` vertices with
maximum degree at most `N^(9/10)` and at least `A · v(H) · √(N log N)` edges is blocked by a
triangle-free graph on `N` vertices. -/
def BlockerAt (A : ℝ) (N : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (H : SimpleGraph α) [DecidableRel H.Adj],
    0 < Fintype.card α → Fintype.card α ≤ N →
    (∀ a, (H.degree a : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ)) →
    A * Fintype.card α * Real.sqrt (N * Real.log N) ≤ H.edgeFinset.card →
    ∃ C : SimpleGraph (Fin N), C.CliqueFree 3 ∧
      ∀ φ : α → Fin N, Function.Injective φ → ∃ a b, H.Adj a b ∧ C.Adj (φ a) (φ b)

def BlockerStatement : Prop := ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ N : ℕ in Filter.atTop, BlockerAt A N

section Combinatorics

open Finset SimpleGraph

/-- **Selecting the heaviest elements.** If `s` has `k + c` elements, some `k`-subset `T` of `s`
carries at least the fraction `k / |s|` of the total weight. -/
theorem exists_subset_card_eq_mul_sum_le {ι : Type*} [DecidableEq ι] (w : ι → ℕ) (k c : ℕ) :
    ∀ s : Finset ι, s.card = k + c →
      ∃ T ⊆ s, T.card = k ∧ k * ∑ i ∈ s, w i ≤ s.card * ∑ i ∈ T, w i := by
  induction c with
  | zero =>
    intro s hs
    have hk : s.card = k := hs
    exact ⟨s, Subset.refl s, hk, by rw [hk]⟩
  | succ c ih =>
    intro s hs
    have hne : s.Nonempty := by
      rw [← Finset.card_pos]
      omega
    -- remove an element of least weight and use induction
    obtain ⟨x, hx, hmin⟩ := s.exists_min_image w hne
    have hcard : (s.erase x).card = k + c := by
      rw [Finset.card_erase_of_mem hx]
      omega
    obtain ⟨T, hT, hTk, hle⟩ := ih (s.erase x) hcard
    refine ⟨T, hT.trans (Finset.erase_subset _ _), hTk, ?_⟩
    have hsum : ∑ i ∈ s, w i = w x + ∑ i ∈ s.erase x, w i := (Finset.add_sum_erase s w hx).symm
    have hTw : k * w x ≤ ∑ i ∈ T, w i := by
      have h1 := Finset.card_nsmul_le_sum T w (w x)
        (fun i hi => hmin i (Finset.mem_of_mem_erase (hT hi)))
      rwa [hTk, smul_eq_mul] at h1
    rw [hcard] at hle
    rw [hsum, hs]
    calc k * (w x + ∑ i ∈ s.erase x, w i)
        = k * w x + k * ∑ i ∈ s.erase x, w i := by ring
      _ ≤ ∑ i ∈ T, w i + (k + c) * ∑ i ∈ T, w i := Nat.add_le_add hTw hle
      _ = (k + (c + 1)) * ∑ i ∈ T, w i := by ring

section Graph

variable {V : Type*}

/-- The graph of all edges of `G` with one end in `X` and the other end in `Y`. -/
def betweenGraph (G : SimpleGraph V) (X Y : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ((a ∈ X ∧ b ∈ Y) ∨ (a ∈ Y ∧ b ∈ X))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm.imp And.symm And.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem betweenGraph_le (G : SimpleGraph V) (X Y : Finset V) : betweenGraph G X Y ≤ G :=
  fun _ _ h => h.1

theorem betweenGraph_adj_of {G : SimpleGraph V} {X Y : Finset V} {a b : V} (h : G.Adj a b)
    (ha : a ∈ X) (hb : b ∈ Y) : (betweenGraph G X Y).Adj a b :=
  ⟨h, Or.inl ⟨ha, hb⟩⟩

theorem betweenGraph_adj_mem [DecidableEq V] {G : SimpleGraph V} {X Y : Finset V} {a b : V}
    (h : (betweenGraph G X Y).Adj a b) : a ∈ X ∪ Y ∧ b ∈ X ∪ Y := by
  rcases h.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨Finset.mem_union_left _ ha, Finset.mem_union_right _ hb⟩
  · exact ⟨Finset.mem_union_right _ ha, Finset.mem_union_left _ hb⟩

/-- A vertex all of whose neighbours lie in `S` has degree at most `|S|`. -/
theorem degree_le_card_of_adj_mem (H : SimpleGraph V) (v : V) [Fintype (H.neighborSet v)]
    (S : Finset V) (hS : ∀ b, H.Adj v b → b ∈ S) : H.degree v ≤ S.card := by
  rw [← H.card_neighborFinset_eq_degree]
  exact Finset.card_le_card fun b hb => hS b ((H.mem_neighborFinset v b).mp hb)

/-- Double counting: the number of adjacent pairs in `X × Y` equals that in `Y × X`. -/
theorem sum_card_filter_adj_comm (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    ∑ x ∈ X, (Y.filter fun y => G.Adj x y).card = ∑ y ∈ Y, (X.filter fun x => G.Adj y x).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
    if_congr (G.adj_comm x y) rfl rfl

variable [Fintype V]

/-- If `H` contains every edge of `G` from `X` to `Y`, then `H` has at least half as many edges as
there are `G`-adjacent pairs in `X × Y`. -/
theorem sum_card_filter_le_two_mul_card_edgeFinset (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (X Y : Finset V)
    (hH : ∀ a b, G.Adj a b → a ∈ X → b ∈ Y → H.Adj a b) :
    ∑ x ∈ X, (Y.filter fun y => G.Adj x y).card ≤ 2 * H.edgeFinset.card := by
  rw [← H.sum_degrees_eq_twice_card_edges]
  calc ∑ x ∈ X, (Y.filter fun y => G.Adj x y).card
      ≤ ∑ x ∈ X, H.degree x := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [← H.card_neighborFinset_eq_degree]
        refine Finset.card_le_card fun y hy => ?_
        rw [Finset.mem_filter] at hy
        rw [SimpleGraph.mem_neighborFinset]
        exact hH x y hy.2 hx hy.1
    _ ≤ ∑ x, H.degree x := Finset.sum_le_sum_of_subset (Finset.subset_univ X)

variable [DecidableEq V]

/-- The neighbours of `v` split into those in `U` and those outside `U`. -/
theorem degree_eq_card_filter_add (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V) :
    G.degree v = (U.filter fun y => G.Adj v y).card + (Uᶜ.filter fun y => G.Adj v y).card := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  simp_rw [Finset.card_filter]
  exact (Finset.sum_add_sum_compl U _).symm

/-- **Degree splitting.** Let `G` be a graph with `m ≥ 1` edges on `n` vertices such that
`4m < (d+1)²`, `4m ≤ n(d+1)` and `8kn ≤ m`. Then there are a nonempty vertex set `S` and a subgraph
`H` of `G`, all of whose edges lie inside `S`, with maximum degree at most `d` and at least `k |S|`
edges. -/
theorem exists_bounded_degree_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] (d k : ℕ)
    (h0 : 0 < G.edgeFinset.card)
    (h1 : 4 * G.edgeFinset.card < (d + 1) ^ 2)
    (h2 : 4 * G.edgeFinset.card ≤ Fintype.card V * (d + 1))
    (h3 : 8 * k * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (S : Finset V) (H : SimpleGraph V), H ≤ G ∧ (∀ a b, H.Adj a b → a ∈ S ∧ b ∈ S) ∧
      S.Nonempty ∧
      ∀ [DecidableRel H.Adj], (∀ v, H.degree v ≤ d) ∧ k * S.card ≤ H.edgeFinset.card := by
  obtain ⟨m, hm⟩ : ∃ m, m = G.edgeFinset.card := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card V := ⟨_, rfl⟩
  rw [← hm] at h0 h1 h2 h3
  rw [← hn] at h2 h3
  have hnpos : 0 < n := Nat.pos_of_ne_zero fun hn0 => by
    rw [hn0, zero_mul] at h2
    omega
  -- the set `U` of vertices of degree `> d`
  obtain ⟨U, hU⟩ : ∃ U : Finset V, U = univ.filter fun v => d < G.degree v := ⟨_, rfl⟩
  have hUmem : ∀ v, v ∈ U ↔ d < G.degree v := fun v => by rw [hU]; simp
  obtain ⟨h, hh⟩ : ∃ h, h = U.card := ⟨_, rfl⟩
  have hdeg : ∑ v, G.degree v = 2 * m := by rw [hm]; exact G.sum_degrees_eq_twice_card_edges
  have hhd : h * (d + 1) ≤ 2 * m := by
    calc h * (d + 1) = U.card • (d + 1) := by rw [hh, smul_eq_mul]
      _ ≤ ∑ v ∈ U, G.degree v := Finset.card_nsmul_le_sum U _ _ fun v hv => (hUmem v).mp hv
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ U)
      _ = 2 * m := hdeg
  have hhd' : 2 * h ≤ d := by
    have e1 : 2 * h * (d + 1) < (d + 1) * (d + 1) := by nlinarith
    have e2 := lt_of_mul_lt_mul_right e1 (Nat.zero_le _)
    omega
  have hhn : 2 * h ≤ n := by
    have e1 : 2 * h * (d + 1) ≤ n * (d + 1) := by nlinarith
    exact Nat.le_of_mul_le_mul_right e1 (Nat.succ_pos d)
  have hUc : Uᶜ.card = h + (n - 2 * h) := by
    rw [Finset.card_compl, ← hn, ← hh]
    omega
  have hUcn : Uᶜ.card ≤ n := by omega
  -- if some vertex has a neighbour in `U`, then `U` is not empty
  have hUne : ∀ X : Finset V, 0 < ∑ x ∈ X, (U.filter fun y => G.Adj x y).card → U.Nonempty := by
    intro X hX
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hX
    simp at hX
  -- ordered adjacent pairs inside `U`, inside `Uᶜ`, and from `Uᶜ` to `U`
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ x ∈ U, (U.filter fun y => G.Adj x y).card := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ x ∈ Uᶜ, (Uᶜ.filter fun y => G.Adj x y).card := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ x ∈ Uᶜ, (U.filter fun y => G.Adj x y).card := ⟨_, rfl⟩
  have hsplit : 2 * m = Q + P + 2 * R := by
    have e0 : ∑ x ∈ U, (Uᶜ.filter fun y => G.Adj x y).card = R := by
      rw [hR]
      exact sum_card_filter_adj_comm G U Uᶜ
    have e1 : ∑ v ∈ U, G.degree v = Q + R := by
      rw [hQ, ← e0, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => degree_eq_card_filter_add G U v
    have e2 : ∑ v ∈ Uᶜ, G.degree v = R + P := by
      rw [hR, hP, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => degree_eq_card_filter_add G U v
    rw [← hdeg, ← Finset.sum_add_sum_compl U, e1, e2]
    ring
  have hcases : m ≤ 2 * P ∨ m ≤ 2 * Q ∨ m ≤ 2 * R := by omega
  have h3' : 8 * (k * n) ≤ m := by rw [← mul_assoc]; exact h3
  rcases hcases with hcase | hcase | hcase
  · -- most edges inside `Uᶜ`
    refine ⟨Uᶜ, betweenGraph G Uᶜ Uᶜ, betweenGraph_le G _ _, fun a b hab => ?_,
      Finset.card_pos.mp (by omega), ?_⟩
    · have hmem := betweenGraph_adj_mem hab
      rwa [Finset.union_self] at hmem
    · intro inst
      refine ⟨fun v => ?_, ?_⟩
      · by_cases hv : v ∈ U
        · refine (degree_le_card_of_adj_mem _ v ∅ fun b hb => ?_).trans (Nat.zero_le d)
          have hmem := (betweenGraph_adj_mem hb).1
          rw [Finset.union_self, Finset.mem_compl] at hmem
          exact absurd hv hmem
        · rw [hUmem] at hv
          exact (degree_le_of_le (betweenGraph_le G _ _)).trans (by omega)
      · have hE := sum_card_filter_le_two_mul_card_edgeFinset G (betweenGraph G Uᶜ Uᶜ) Uᶜ Uᶜ
          (fun a b hab ha hb => betweenGraph_adj_of hab ha hb)
        rw [← hP] at hE
        have e1 : k * Uᶜ.card ≤ k * n := Nat.mul_le_mul_left _ hUcn
        omega
  · -- most edges inside `U`
    refine ⟨U, betweenGraph G U U, betweenGraph_le G _ _, fun a b hab => ?_,
      hUne U (by rw [← hQ]; omega), ?_⟩
    · have hmem := betweenGraph_adj_mem hab
      rwa [Finset.union_self] at hmem
    · intro inst
      refine ⟨fun v => ?_, ?_⟩
      · refine (degree_le_card_of_adj_mem _ v U fun b hb => ?_).trans (by omega)
        have hmem := (betweenGraph_adj_mem hb).2
        rwa [Finset.union_self] at hmem
      · have hE := sum_card_filter_le_two_mul_card_edgeFinset G (betweenGraph G U U) U U
          (fun a b hab ha hb => betweenGraph_adj_of hab ha hb)
        rw [← hQ] at hE
        have e1 : k * U.card ≤ k * n := Nat.mul_le_mul_left _ (by omega)
        omega
  · -- most edges join `U` to `Uᶜ`: keep the `h` vertices of `Uᶜ` with most neighbours in `U`
    obtain ⟨T, -, hTcard, hTsum⟩ := exists_subset_card_eq_mul_sum_le
      (fun x => (U.filter fun y => G.Adj x y).card) h (n - 2 * h) Uᶜ hUc
    rw [← hR] at hTsum
    obtain ⟨RT, hRT⟩ : ∃ RT, RT = ∑ x ∈ T, (U.filter fun y => G.Adj x y).card := ⟨_, rfl⟩
    rw [← hRT] at hTsum
    have hScard : (T ∪ U).card ≤ 2 * h := by
      have e1 := Finset.card_union_le T U
      omega
    refine ⟨T ∪ U, betweenGraph G T U, betweenGraph_le G _ _,
      fun a b hab => betweenGraph_adj_mem hab,
      (hUne Uᶜ (by rw [← hR]; omega)).mono Finset.subset_union_right, ?_⟩
    intro inst
    refine ⟨fun v => ?_, ?_⟩
    · refine (degree_le_card_of_adj_mem _ v (T ∪ U) fun b hb =>
        (betweenGraph_adj_mem hb).2).trans ?_
      omega
    · have hE := sum_card_filter_le_two_mul_card_edgeFinset G (betweenGraph G T U) T U
        (fun a b hab ha hb => betweenGraph_adj_of hab ha hb)
      rw [← hRT] at hE
      obtain ⟨e, he⟩ : ∃ e, e = (betweenGraph G T U).edgeFinset.card := ⟨_, rfl⟩
      rw [← he] at hE ⊢
      have e1 : k * (T ∪ U).card ≤ k * (2 * h) := Nat.mul_le_mul_left _ hScard
      have a1 : h * (8 * (k * n)) ≤ h * m := Nat.mul_le_mul_left _ h3'
      have a2 : h * m ≤ h * (2 * R) := Nat.mul_le_mul_left _ hcase
      have a3 : h * R ≤ n * RT := hTsum.trans (Nat.mul_le_mul_right _ hUcn)
      have a4 : n * RT ≤ n * (2 * e) := Nat.mul_le_mul_left _ hE
      have a5 : n * (k * (2 * h)) ≤ n * e := by nlinarith
      exact e1.trans (Nat.le_of_mul_le_mul_left a5 hnpos)

end Graph

end Combinatorics

section Transfer

open Finset SimpleGraph

/-- **Using a blocker for a subgraph.** If `H ≤ G` has all its edges inside the nonempty set `S`,
and `H` satisfies the hypotheses of `BlockerAt A N` with `|S|` as the number of vertices, then `G`
is blocked by a triangle-free graph on `N` vertices. -/
theorem exists_blocker_of_subgraph {V : Type} [Fintype V] [DecidableEq V] {A : ℝ} {N : ℕ}
    (hB : BlockerAt A N) (G H : SimpleGraph V) [DecidableRel H.Adj] (hHG : H ≤ G)
    (S : Finset V) (hS : ∀ a b, H.Adj a b → a ∈ S ∧ b ∈ S) (hSne : S.Nonempty)
    (hcard : S.card ≤ N) (hdeg : ∀ v, (H.degree v : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ))
    (hedges : A * S.card * Real.sqrt (N * Real.log N) ≤ H.edgeFinset.card) :
    ∃ C : SimpleGraph (Fin N), C.CliqueFree 3 ∧
      ∀ φ : V → Fin N, Function.Injective φ → ∃ a b, G.Adj a b ∧ C.Adj (φ a) (φ b) := by
  -- restrict `H` to `S`: degrees do not increase and no edge is lost
  have hdeg' : ∀ a : {x // x ∈ S},
      (H.comap (Subtype.val : {x // x ∈ S} → V)).degree a ≤ H.degree a.1 := by
    intro a
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    refine Finset.card_le_card_of_injOn Subtype.val (fun x hx => ?_) Subtype.val_injective.injOn
    rw [Finset.mem_coe, mem_neighborFinset] at hx ⊢
    exact hx
  have hedge' : H.edgeFinset.card ≤
      (H.comap (Subtype.val : {x // x ∈ S} → V)).edgeFinset.card := by
    have hsub : H.edgeFinset ⊆ (H.comap (Subtype.val : {x // x ∈ S} → V)).edgeFinset.map
        (Function.Embedding.subtype (· ∈ S)).sym2Map := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [mem_edgeFinset, mem_edgeSet] at he
      obtain ⟨ha, hb⟩ := hS a b he
      refine Finset.mem_map.mpr ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
      rw [mem_edgeFinset, mem_edgeSet]
      exact he
    exact (Finset.card_le_card hsub).trans (Finset.card_map _).le
  obtain ⟨C, hC, hCφ⟩ := hB {x // x ∈ S} (H.comap (Subtype.val : {x // x ∈ S} → V))
    (by rw [Fintype.card_coe]; exact hSne.card_pos)
    (by rw [Fintype.card_coe]; exact hcard)
    (fun a => le_trans (by exact_mod_cast hdeg' a) (hdeg a.1))
    (by rw [Fintype.card_coe]; exact hedges.trans (by exact_mod_cast hedge'))
  refine ⟨C, hC, fun φ hφ => ?_⟩
  obtain ⟨a, b, hab, hCab⟩ := hCφ (fun x => φ x.1) (fun x y hxy => Subtype.ext (hφ hxy))
  exact ⟨a.1, b.1, hHG hab, hCab⟩

/-- **The finite step.** Let `d ≤ N^{9/10}` and `k ≥ A √(N log N)`, `k ≥ 1`. If `32kn < (d+1)²` and
`32kn ≤ n(d+1)`, then every graph on `1 ≤ n ≤ N` vertices with at least `8kn` edges is blocked by a
triangle-free graph on `N` vertices, provided `BlockerAt A N` holds. -/
theorem exists_blocker_of_card_edges {n N : ℕ} {A : ℝ} (hB : BlockerAt A N)
    (hn0 : 0 < n) (hnN : n ≤ N) (d k : ℕ) (hk0 : 0 < k)
    (hd : (d : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ))
    (hk : A * Real.sqrt (N * Real.log N) ≤ k)
    (h1 : 4 * (8 * k * n) < (d + 1) ^ 2) (h2 : 4 * (8 * k * n) ≤ n * (d + 1))
    (G : SimpleGraph (Fin n)) (hG : 8 * k * n ≤ G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin N), C.CliqueFree 3 ∧
      ∀ φ : Fin n → Fin N, Function.Injective φ → ∃ a b, G.Adj a b ∧ C.Adj (φ a) (φ b) := by
  classical
  have hmcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [hmcard] at hG
  -- keep exactly `8kn` edges
  obtain ⟨E₀, hE₀, hE₀card⟩ := Finset.exists_subset_card_eq hG
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : SimpleGraph (Fin n),
      G₀ = SimpleGraph.fromEdgeSet (E₀ : Set (Sym2 (Fin n))) := ⟨_, rfl⟩
  have hG₀G : G₀ ≤ G := by
    intro a b hab
    rw [hG₀, fromEdgeSet_adj] at hab
    have hmem := hE₀ (Finset.mem_coe.mp hab.1)
    rwa [mem_edgeFinset, mem_edgeSet] at hmem
  have hG₀E : G₀.edgeFinset = E₀ := by
    ext e
    rw [mem_edgeFinset, hG₀, edgeSet_fromEdgeSet]
    constructor
    · intro he
      exact Finset.mem_coe.mp he.1
    · intro he
      refine ⟨Finset.mem_coe.mpr he, ?_⟩
      have hmem := hE₀ he
      rw [mem_edgeFinset] at hmem
      rw [Sym2.mem_diagSet]
      exact G.not_isDiag_of_mem_edgeSet hmem
  have hcardG₀ : G₀.edgeFinset.card = 8 * k * n := by rw [hG₀E, hE₀card]
  have hpos : 0 < 8 * k * n := Nat.mul_pos (Nat.mul_pos (by norm_num) hk0) hn0
  obtain ⟨S, H, hHG₀, hS, hSne, hH⟩ := exists_bounded_degree_subgraph G₀ d k
    (by rw [hcardG₀]; exact hpos) (by rw [hcardG₀]; exact h1)
    (by rw [hcardG₀, Fintype.card_fin]; exact h2) (by rw [hcardG₀, Fintype.card_fin])
  obtain ⟨hdegH, hedgeH⟩ := hH
  refine exists_blocker_of_subgraph hB G H (hHG₀.trans hG₀G) S hS hSne ?_ ?_ ?_
  · exact (Finset.card_le_univ S).trans (by rw [Fintype.card_fin]; exact hnN)
  · intro v
    exact le_trans (by exact_mod_cast hdegH v) hd
  · calc A * S.card * Real.sqrt (N * Real.log N)
        = (A * Real.sqrt (N * Real.log N)) * S.card := by ring
      _ ≤ k * S.card := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)
      _ ≤ H.edgeFinset.card := by exact_mod_cast hedgeH

end Transfer

section Asymptotics

open Filter Asymptotics

/-- **Conditional upper bound.** If `BlockerStatement` holds, then `f(n) = O(n^{3/2} √(log n))`;
in fact `f(n) ≤ (16A + 8) n^{3/2} √(log n)` for all large `n`. The hypothesis is proved in
`FinalPart` (`blockerStatement`). -/
theorem f_isBigO_of_blocker (h : BlockerStatement) :
    (fun n : ℕ => (f n : ℝ)) =O[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by
  obtain ⟨A, hA, hev⟩ := h
  have hA0 : (0 : ℝ) < A := by linarith
  have htend : Tendsto (fun n : ℕ => 2 * n - 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by show n ≤ 2 * n - 1; omega) tendsto_id
  have hbig : ∀ᶠ N : ℕ in atTop, 128 * A + 32 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  refine IsBigO.of_bound (16 * A + 8) ?_
  filter_upwards [htend.eventually (hev.and hbig), eventually_ge_atTop 3] with n hn hn3
  have hBl : BlockerAt A (2 * n - 1) := hn.1
  have hbigN : 128 * A + 32 ≤ ((2 * n - 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := hn.2
  have hnN : n ≤ 2 * n - 1 := by omega
  have hnR3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  -- `x = N = 2n - 1` as a real number
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((2 * n - 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hx] at hbigN
  have hx1 : 1 < x := by
    have h1 : 1 < 2 * n - 1 := by omega
    rw [hx]
    exact_mod_cast h1
  have hx0 : 0 < x := by linarith
  have hnx : (n : ℝ) ≤ x := by
    rw [hx]
    exact_mod_cast hnN
  have hx2n : x ≤ 2 * n := by
    have h1 : 2 * n - 1 ≤ 2 * n := Nat.sub_le _ _
    rw [hx]
    exact_mod_cast h1
  have hlogx0 : 0 < Real.log x := Real.log_pos hx1
  -- `L = √(N log N)`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.sqrt (x * Real.log x) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; exact Real.sqrt_pos.mpr (mul_pos hx0 hlogx0)
  -- powers of `x`
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = x ^ (1 / 10 : ℝ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = x ^ (11 / 20 : ℝ) := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; exact Real.rpow_nonneg hx0.le _
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_rpow hx1.le (by norm_num)
  have hq2 : q ^ 2 = p * x := by
    rw [hq, hp, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add_one hx0.ne']
    norm_num
  have hlogp : Real.log x ≤ 10 * p := by
    have h1 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 10)
    have h2 : x ^ (1 / 10 : ℝ) / (1 / 10) = 10 * x ^ (1 / 10 : ℝ) := by ring
    rw [h2, ← hp] at h1
    exact h1
  have hLq : L ≤ 4 * q := by
    rw [hL, Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have h1 : x * Real.log x ≤ x * (10 * p) := mul_le_mul_of_nonneg_left hlogp hx0.le
    have h2 : 0 ≤ p * x := mul_nonneg hp0 hx0.le
    calc x * Real.log x ≤ x * (10 * p) := h1
      _ ≤ 16 * (p * x) := by linarith
      _ = (4 * q) ^ 2 := by rw [mul_pow, hq2]; norm_num
  -- the one place where `n` must be large: `32 (A L + 1) ≤ N^{4/5}`
  have hkey : 32 * (A * L + 1) ≤ x ^ (4 / 5 : ℝ) := by
    have h1 : x ^ (4 / 5 : ℝ) = x ^ (1 / 4 : ℝ) * q := by
      rw [hq, ← Real.rpow_add hx0]
      norm_num
    have h2 : A * L ≤ A * (4 * q) := mul_le_mul_of_nonneg_left hLq hA0.le
    have h3 : (128 * A + 32) * q ≤ x ^ (1 / 4 : ℝ) * q :=
      mul_le_mul_of_nonneg_right hbigN (by linarith)
    rw [h1]
    nlinarith
  -- the integers `k = ⌈A L⌉` and `d = ⌊N^{9/10}⌋`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈A * L⌉₊ := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact Nat.ceil_pos.mpr (mul_pos hA0 hL0)
  have hk1 : A * L ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hk2 : (k : ℝ) < A * L + 1 := by
    rw [hk]
    exact Nat.ceil_lt_add_one (mul_nonneg hA0.le hL0.le)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊x ^ (9 / 10 : ℝ)⌋₊ := ⟨_, rfl⟩
  have hD0 : 0 ≤ x ^ (9 / 10 : ℝ) := Real.rpow_nonneg hx0.le _
  have hd1 : (d : ℝ) ≤ x ^ (9 / 10 : ℝ) := by rw [hd]; exact Nat.floor_le hD0
  have hd2 : x ^ (9 / 10 : ℝ) < (d : ℝ) + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
  have h32k : (32 : ℝ) * k ≤ x ^ (4 / 5 : ℝ) := by linarith
  have h2' : 4 * (8 * k * n) ≤ n * (d + 1) := by
    have e1 : (32 : ℝ) * k < (d : ℝ) + 1 :=
      calc (32 : ℝ) * k ≤ x ^ (4 / 5 : ℝ) := h32k
        _ ≤ x ^ (9 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
        _ < (d : ℝ) + 1 := hd2
    have e2 : 32 * k < d + 1 := by exact_mod_cast e1
    nlinarith
  have h1' : 4 * (8 * k * n) < (d + 1) ^ 2 := by
    have e1 : x ^ (4 / 5 : ℝ) * x = (x ^ (9 / 10 : ℝ)) ^ 2 := by
      rw [← Real.rpow_add_one hx0.ne', ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have e2 : (32 : ℝ) * k * n < ((d : ℝ) + 1) ^ 2 :=
      calc (32 : ℝ) * k * n ≤ x ^ (4 / 5 : ℝ) * x :=
            mul_le_mul h32k hnx hnpos.le (Real.rpow_nonneg hx0.le _)
        _ = (x ^ (9 / 10 : ℝ)) ^ 2 := e1
        _ < ((d : ℝ) + 1) ^ 2 := pow_lt_pow_left₀ hd2 hD0 (by norm_num)
    have e3 : 32 * k * n < (d + 1) ^ 2 := by exact_mod_cast e2
    calc 4 * (8 * k * n) = 32 * k * n := by ring
      _ < (d + 1) ^ 2 := e3
  -- hence `f n ≤ 8kn`
  have hf : f n ≤ 8 * k * n := by
    refine f_le_of_forall_exists (by omega) fun G _ hGm => ?_
    exact exists_blocker_of_card_edges hBl (by omega) hnN d k hk0 (by rw [← hx]; exact hd1)
      (by rw [← hx, ← hL]; exact hk1) h1' h2' G hGm.le
  -- comparison with `n^{3/2} √(log n)`
  have hlogn : 1 ≤ Real.log n := by
    have h1 : Real.exp 1 ≤ n := le_trans Real.exp_one_lt_three.le hnR3
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) h1
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.sqrt (n * Real.log n) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact Real.sqrt_nonneg _
  have hnlog : 1 ≤ (n : ℝ) * Real.log n := by nlinarith
  have hY2 : Y ^ 2 = n * Real.log n := by rw [hY]; exact Real.sq_sqrt (by linarith)
  have hY1 : 1 ≤ Y := by
    rw [hY, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnlog
  have hLY : L ≤ 2 * Y := by
    rw [hL, Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have h1 : Real.log x ≤ 2 * Real.log n := by
      have h2 : Real.log x ≤ Real.log (2 * n) := Real.log_le_log hx0 hx2n
      rw [Real.log_mul (by norm_num) hnpos.ne'] at h2
      have h3 := Real.log_two_lt_d9
      linarith
    calc x * Real.log x ≤ (2 * n) * (2 * Real.log n) :=
          mul_le_mul hx2n h1 hlogx0.le (by linarith)
      _ = (2 * Y) ^ 2 := by rw [mul_pow, hY2]; ring
  have htarget : (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) = n * Y := by
    rw [rpow_three_halves hnpos, hY, Real.sqrt_mul hnpos.le]
    ring
  have hnY : 0 ≤ (n : ℝ) * Y := mul_nonneg hnpos.le hY0
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), htarget, Real.norm_of_nonneg hnY]
  have hfR : (f n : ℝ) ≤ 8 * k * n := by exact_mod_cast hf
  have h4 : (k : ℝ) ≤ A * (2 * Y) + 1 := by
    have h5 : A * L ≤ A * (2 * Y) := mul_le_mul_of_nonneg_left hLY hA0.le
    linarith
  have h6 : (8 : ℝ) * k * n ≤ 8 * (A * (2 * Y) + 1) * n := by
    have h7 : (8 : ℝ) * k ≤ 8 * (A * (2 * Y) + 1) := by linarith
    exact mul_le_mul_of_nonneg_right h7 hnpos.le
  have h8 : (n : ℝ) ≤ n * Y := by
    have h9 : (n : ℝ) * 1 ≤ n * Y := mul_le_mul_of_nonneg_left hY1 hnpos.le
    linarith
  calc (f n : ℝ) ≤ 8 * k * n := hfR
    _ ≤ 8 * (A * (2 * Y) + 1) * n := h6
    _ = 16 * A * (n * Y) + 8 * n := by ring
    _ ≤ 16 * A * (n * Y) + 8 * (n * Y) := by linarith
    _ = (16 * A + 8) * (n * Y) := by ring

/-- **Conditional answer to part (i).** If `BlockerStatement` holds, then
`f(n) = Θ(n^{3/2} √(log n))`. The hypothesis is proved in `FinalPart` (`blockerStatement`), which
gives `erdos_1182_i`. -/
theorem f_isTheta_of_blocker (h : BlockerStatement) :
    (fun n : ℕ => (f n : ℝ)) =Θ[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
  ⟨f_isBigO_of_blocker h, isBigO_f_lower⟩

end Asymptotics

end E1182

end ReductionPart

section AssemblePart

/-
# Assembling the union bound

With all potentials at hand, the master lemma shows that most histories stay good up to the
horizon; along good histories every edge set of the family keeps many open pairs, so it is hit
with high probability. Hence some valid history hits every edge set.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

/-- The hypotheses on the family of edge sets. -/
structure EdgeHyp (N : ℕ) {ι : Type} (W : ι → Finset (Sym2 (Fin N))) (m : ℝ) : Prop where
  m0 : 0 ≤ m
  card : ∀ c, ((W c).card : ℝ) = m
  deg : ∀ c a, (degW (W c) a : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ)
  sub : ∀ c, W c ⊆ openSet (∅ : Finset (Sym2 (Fin N)))
  gpos : ∀ i ≤ hor N, 0 < gW N i
  nS : ∀ i < hor N, 2 * (Qh N i + eQ N i) ≤ 5 * (N.choose 2 : ℝ) * gW N i
  nW : NumW N m ((N : ℝ) ^ (9 / 10 : ℝ)) (lamWn N) (B0 N) (vWn N m)
  cW0 : 0 ≤ CWn N m

/- ## Values of the potentials at the empty history -/

theorem valid_cons {e : Sym2 (Fin N)} {s : List (Sym2 (Fin N))} :
    Valid (e :: s) ↔ e ∈ openSet s.toFinset ∧ Valid s := Iff.rfl

theorem valid_nil : Valid ([] : List (Sym2 (Fin N))) := by
  show True
  trivial

theorem pairPot_nil_le {lam v : ℝ} (hlam : 0 ≤ lam) {U : List (Sym2 (Fin N)) → ℝ}
    {u w : Fin N} (hU : Op (∅ : Finset (Sym2 (Fin N))) u w → U [] ≤ 0) :
    pairPot lam v U u w [] ≤ 1 := by
  unfold pairPot
  rw [List.toFinset_nil]
  by_cases hop : Op (∅ : Finset (Sym2 (Fin N))) u w
  · rw [ind_of hop, one_mul]
    apply Real.exp_le_one_iff.mpr
    have h1 := hU hop
    have h2 : lam * U [] ≤ 0 := by nlinarith [mul_nonneg hlam (neg_nonneg.mpr h1)]
    simp only [List.length_nil, Nat.cast_zero, mul_zero, sub_zero]
    exact h2
  · rw [ind_of_not hop, zero_mul]
    exact zero_le_one

theorem card_Xset_empty_real (hN : 2 ≤ N) {u v : Fin N} (huv : u ≠ v) :
    ((Xset (∅ : Finset (Sym2 (Fin N))) u v).card : ℝ) = (N : ℝ) - 2 := by
  rw [card_Xset_empty huv, Nat.cast_sub hN, Nat.cast_ofNat]

theorem UXu_nil (hN : 2 ≤ N) {u v : Fin N} (huv : u ≠ v) : UXu N u v [] = 0 := by
  simp only [UXu, List.toFinset_nil, List.length_nil]
  rw [card_Xset_empty_real hN huv, xh_zero]
  ring

theorem UXd_nil (hN : 2 ≤ N) {u v : Fin N} (huv : u ≠ v) : UXd N u v [] = 0 := by
  simp only [UXd, List.toFinset_nil, List.length_nil]
  rw [card_Xset_empty_real hN huv, xh_zero]
  ring

theorem UYu_nil (u v : Fin N) : UYu N u v [] = 0 := by
  simp only [UYu, List.toFinset_nil, List.length_nil]
  rw [Yset_empty, card_empty, yh_zero, Nat.cast_zero]
  ring

theorem UYd_nil (u v : Fin N) : UYd N u v [] = 0 := by
  simp only [UYd, List.toFinset_nil, List.length_nil]
  rw [Yset_empty, card_empty, yh_zero, Nat.cast_zero]
  ring

theorem PsiD_nil (u : Fin N) : PsiD N u [] = 1 := by
  simp only [PsiD, List.toFinset_nil, List.length_nil]
  rw [nb_empty, card_empty, pow_zero, pow_zero, div_one]

theorem PsiZ_nil_le (u v : Fin N) : PsiZ N u v [] ≤ 1 := by
  unfold PsiZ
  split_ifs
  · exact zero_le_one
  · simp only [List.toFinset_nil, List.length_nil]
    rw [cod_empty, card_empty, pow_zero, pow_zero, div_one]

theorem PsiW_nil {Wc : Finset (Sym2 (Fin N))} {m : ℝ} (lamW CW : ℝ)
    (hsub : Wc ⊆ openSet (∅ : Finset (Sym2 (Fin N)))) (hcard : (Wc.card : ℝ) = m) :
    PsiW N Wc m lamW CW [] = 1 := by
  simp only [PsiW, List.toFinset_nil, List.length_nil]
  rw [inter_eq_left.mpr hsub, hcard, gW_zero, div_one, sub_self, Nat.cast_zero, mul_zero,
    mul_zero, sub_zero, Real.exp_zero]

/- ## The family of all potentials -/

/-- The index type of the potentials: four deviation directions for every ordered pair, the
degrees, the codegrees and the edge sets. -/
abbrev Cause (ι : Type) (N : ℕ) : Type :=
  (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ Fin N ⊕
    (Fin N × Fin N) ⊕ ι

/-- All potentials. -/
noncomputable def PsiAll (N : ℕ) {ι : Type} (W : ι → Finset (Sym2 (Fin N))) (m : ℝ) :
    Cause ι N → List (Sym2 (Fin N)) → ℝ :=
  Sum.elim (fun p => pairPot (lamX N) (vX N) (UXu N p.1 p.2) p.1 p.2) <|
  Sum.elim (fun p => pairPot (lamX N) (vX N) (UXd N p.1 p.2) p.1 p.2) <|
  Sum.elim (fun p => pairPot (lamY N) (vY N) (UYu N p.1 p.2) p.1 p.2) <|
  Sum.elim (fun p => pairPot (lamY N) (vY N) (UYd N p.1 p.2) p.1 p.2) <|
  Sum.elim (fun u => PsiD N u) <|
  Sum.elim (fun p => PsiZ N p.1 p.2) (fun c => PsiW N (W c) m (lamWn N) (CWn N m))

/-- All thresholds. -/
noncomputable def LamAll (ι : Type) (N : ℕ) (m : ℝ) : Cause ι N → ℝ :=
  Sum.elim (fun _ => LamX N) <|
  Sum.elim (fun _ => LamX N) <|
  Sum.elim (fun _ => LamY N) <|
  Sum.elim (fun _ => LamY N) <|
  Sum.elim (fun _ => LamD N) <|
  Sum.elim (fun _ => LamZ N) (fun _ => LamW N m)

section

variable {ι : Type} {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

theorem PsiAll_nonneg (hC : NumC N) (W : ι → Finset (Sym2 (Fin N))) (m : ℝ) :
    ∀ (c : Cause ι N) (s : List (Sym2 (Fin N))), 0 ≤ PsiAll N W m c s := by
  rintro (p | p | p | p | u | p | c) s
  · exact pairPot_nonneg _ _ _ _ _ s
  · exact pairPot_nonneg _ _ _ _ _ s
  · exact pairPot_nonneg _ _ _ _ _ s
  · exact pairPot_nonneg _ _ _ _ _ s
  · exact PsiD_nonneg hC u s
  · exact PsiZ_nonneg hC p.1 p.2 s
  · show 0 ≤ PsiW N (W c) m (lamWn N) (CWn N m) s
    unfold PsiW
    exact (Real.exp_pos _).le

theorem pos_of_num {Λ : ℝ} (hN : 2 ≤ N) (h : 40 * (N : ℝ) ^ 2 ≤ Λ) : 0 < Λ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h40 : (0 : ℝ) < 40 * (N : ℝ) ^ 2 := by positivity
  exact lt_of_lt_of_le h40 h

theorem LamAll_pos (hG : NumGlobal N) (ι : Type) (m : ℝ) :
    ∀ c : Cause ι N, 0 < LamAll ι N m c := by
  rintro (p | p | p | p | u | p | c)
  · exact pos_of_num hG.hN hG.fX
  · exact pos_of_num hG.hN hG.fX
  · exact pos_of_num hG.hN hG.fY
  · exact pos_of_num hG.hN hG.fY
  · exact pos_of_num hG.hN hG.fD
  · exact pos_of_num hG.hN hG.fZ
  · show 0 < LamW N m
    unfold LamW
    exact Real.exp_pos _

theorem PsiAll_super (hG : NumGlobal N) (hE : EdgeHyp N W m) (c : Cause ι N)
    (s : List (Sym2 (Fin N))) (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N) :
    ∑ e ∈ openSet s.toFinset, PsiAll N W m c (e :: s)
      ≤ (openSet s.toFinset).card * PsiAll N W m c s := by
  rcases c with p | p | p | p | u | p | c
  · exact super_Xu hG.nA hG.nB hs hlen p.1 p.2
  · exact super_Xd hG.nA hG.nB hs hlen p.1 p.2
  · exact super_Yu hG.nA hG.nB hs hlen p.1 p.2
  · exact super_Yd hG.nA hG.nB hs hlen p.1 p.2
  · exact super_D hG.nA hG.nC hs hlen u
  · exact super_Z hG.nA hG.nC hs hlen p.1 p.2
  · exact super_W hG.nA hG.nC hE.nW hs hlen (W c) (hE.card c) (hE.deg c)

/-- If the next history is not good, one of the potentials has crossed its threshold. -/
theorem PsiAll_bad (hG : NumGlobal N) (hE : EdgeHyp N W m) (s : List (Sym2 (Fin N)))
    (e : Sym2 (Fin N)) (hs : GoodAll (Good N W m) s) (hlen : s.length < hor N)
    (he : e ∈ openSet s.toFinset) (hbad : ¬ Good N W m (e :: s)) :
    ∃ c : Cause ι N, LamAll ι N m c ≤ PsiAll N W m c (e :: s) := by
  by_contra hno
  push Not at hno
  apply hbad
  have hlen' : (e :: s).length ≤ hor N := by
    rw [List.length_cons]
    omega
  refine ⟨valid_cons.mpr ⟨he, hs.self.1⟩, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    have h1 : pairPot (lamX N) (vX N) (UXu N u v) u v (e :: s) < LamX N :=
      hno (Sum.inl (u, v))
    have h2 : pairPot (lamX N) (vX N) (UXd N u v) u v (e :: s) < LamX N :=
      hno (Sum.inr (Sum.inl (u, v)))
    have h3 : pairPot (lamY N) (vY N) (UYu N u v) u v (e :: s) < LamY N :=
      hno (Sum.inr (Sum.inr (Sum.inl (u, v))))
    have h4 : pairPot (lamY N) (vY N) (UYd N u v) u v (e :: s) < LamY N :=
      hno (Sum.inr (Sum.inr (Sum.inr (Sum.inl (u, v)))))
    have k1 : UXu N u v (e :: s) < eX N 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd (pairPot_ge (U := UXu N u v) (lamX_nonneg N) (vX_nonneg N) huv hcon hlen')
        (not_le.mpr h1)
    have k2 : UXd N u v (e :: s) < eX N 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd (pairPot_ge (U := UXd N u v) (lamX_nonneg N) (vX_nonneg N) huv hcon hlen')
        (not_le.mpr h2)
    have k3 : UYu N u v (e :: s) < eY N 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd (pairPot_ge (U := UYu N u v) (lamY_nonneg N) (vY_nonneg N) huv hcon hlen')
        (not_le.mpr h3)
    have k4 : UYd N u v (e :: s) < eY N 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd (pairPot_ge (U := UYd N u v) (lamY_nonneg N) (vY_nonneg N) huv hcon hlen')
        (not_le.mpr h4)
    unfold UXu at k1
    unfold UXd at k2
    unfold UYu at k3
    unfold UYd at k4
    constructor
    · rw [abs_le]
      constructor <;> linarith
    · rw [abs_le]
      constructor <;> linarith
  · intro u
    have h5 : PsiD N u (e :: s) < LamD N :=
      hno (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))))
    by_contra hcon
    push Not at hcon
    exact absurd (PsiD_ge hG.nC hcon.le hlen') (not_le.mpr h5)
  · intro u v huv
    have h6 : PsiZ N u v (e :: s) < LamZ N :=
      hno (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (u, v)))))))
    by_contra hcon
    push Not at hcon
    exact absurd (PsiZ_ge hG.nC huv hcon.le hlen') (not_le.mpr h6)
  · intro c
    have h7 : PsiW N (W c) m (lamWn N) (CWn N m) (e :: s) < LamW N m :=
      hno (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c))))))
    by_contra hcon
    push Not at hcon
    exact absurd (PsiW_ge hE.nW.1 hE.cW0 (hE.gpos _ hlen') hcon hlen') (not_le.mpr h7)

theorem goodAll_nil (hG : NumGlobal N) (hE : EdgeHyp N W m) :
    GoodAll (Good N W m) [] := by
  intro t ht
  obtain rfl : t = [] := List.suffix_nil.mp ht
  have hN2 := hG.hN
  refine ⟨valid_nil, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    simp only [List.toFinset_nil, List.length_nil] at huv ⊢
    constructor
    · rw [card_Xset_empty_real hN2 huv.1, xh_zero, sub_self, abs_zero, eX_zero]
      positivity
    · rw [Yset_empty, card_empty, yh_zero, Nat.cast_zero, sub_self, abs_zero, eY_zero]
      positivity
  · intro u
    simp only [List.toFinset_nil]
    rw [nb_empty, card_empty, Nat.cast_zero]
    exact Dmx_nonneg N
  · intro u v _
    simp only [List.toFinset_nil]
    rw [cod_empty, card_empty, Nat.cast_zero]
    exact Zmx_nonneg N
  · intro c
    simp only [List.toFinset_nil, List.length_nil]
    rw [inter_eq_left.mpr (hE.sub c), hE.card c, gW_zero, mul_one]
    linarith [hE.m0]

end

/- ## The initial value of the union bound -/

theorem sum_div_le_card {κ : Type*} [Fintype κ] (F : κ → ℝ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hF : ∀ x, F x ≤ 1) : ∑ x, F x / Λ ≤ (Fintype.card κ : ℝ) / Λ := by
  calc ∑ x, F x / Λ ≤ ∑ _x : κ, 1 / Λ :=
        sum_le_sum fun x _ => div_le_div_of_nonneg_right (hF x) hΛ.le
    _ = (Fintype.card κ : ℝ) / Λ := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_one_div]

theorem card_pair_div_le (hN : 2 ≤ N) {Λ : ℝ} (h : 40 * (N : ℝ) ^ 2 ≤ Λ) :
    (Fintype.card (Fin N × Fin N) : ℝ) / Λ ≤ 1 / 40 := by
  have hΛ := pos_of_num hN h
  rw [Fintype.card_prod, Fintype.card_fin, div_le_div_iff₀ hΛ (by norm_num)]
  push_cast
  nlinarith

theorem card_fin_div_le (hN : 2 ≤ N) {Λ : ℝ} (h : 40 * (N : ℝ) ^ 2 ≤ Λ) :
    (Fintype.card (Fin N) : ℝ) / Λ ≤ 1 / 40 := by
  have hΛ := pos_of_num hN h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rw [Fintype.card_fin, div_le_div_iff₀ hΛ (by norm_num)]
  nlinarith

section

variable {ι : Type} [Fintype ι] {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

theorem init_sum_le (hG : NumGlobal N) (hE : EdgeHyp N W m)
    (hι : 8 * (Fintype.card ι : ℝ) ≤ LamW N m) :
    ∑ c : Cause ι N, PsiAll N W m c [] / LamAll ι N m c ≤ 11 / 40 := by
  have hN2 : 2 ≤ N := hG.hN
  have hW : 0 < LamW N m := by
    unfold LamW
    exact Real.exp_pos _
  have s1 : ∑ p : Fin N × Fin N,
      pairPot (lamX N) (vX N) (UXu N p.1 p.2) p.1 p.2 [] / LamX N ≤ 1 / 40 :=
    le_trans (sum_div_le_card _ (pos_of_num hN2 hG.fX) fun p =>
      pairPot_nil_le (lamX_nonneg N) fun hop => (UXu_nil hN2 hop.1).le)
      (card_pair_div_le hN2 hG.fX)
  have s2 : ∑ p : Fin N × Fin N,
      pairPot (lamX N) (vX N) (UXd N p.1 p.2) p.1 p.2 [] / LamX N ≤ 1 / 40 :=
    le_trans (sum_div_le_card _ (pos_of_num hN2 hG.fX) fun p =>
      pairPot_nil_le (lamX_nonneg N) fun hop => (UXd_nil hN2 hop.1).le)
      (card_pair_div_le hN2 hG.fX)
  have s3 : ∑ p : Fin N × Fin N,
      pairPot (lamY N) (vY N) (UYu N p.1 p.2) p.1 p.2 [] / LamY N ≤ 1 / 40 :=
    le_trans (sum_div_le_card _ (pos_of_num hN2 hG.fY) fun p =>
      pairPot_nil_le (lamY_nonneg N) fun _ => (UYu_nil p.1 p.2).le)
      (card_pair_div_le hN2 hG.fY)
  have s4 : ∑ p : Fin N × Fin N,
      pairPot (lamY N) (vY N) (UYd N p.1 p.2) p.1 p.2 [] / LamY N ≤ 1 / 40 :=
    le_trans (sum_div_le_card _ (pos_of_num hN2 hG.fY) fun p =>
      pairPot_nil_le (lamY_nonneg N) fun _ => (UYd_nil p.1 p.2).le)
      (card_pair_div_le hN2 hG.fY)
  have s5 : ∑ u : Fin N, PsiD N u [] / LamD N ≤ 1 / 40 :=
    le_trans (sum_div_le_card _ (pos_of_num hN2 hG.fD) fun u => (PsiD_nil u).le)
      (card_fin_div_le hN2 hG.fD)
  have s6 : ∑ p : Fin N × Fin N, PsiZ N p.1 p.2 [] / LamZ N ≤ 1 / 40 :=
    le_trans (sum_div_le_card _ (pos_of_num hN2 hG.fZ) fun p => PsiZ_nil_le p.1 p.2)
      (card_pair_div_le hN2 hG.fZ)
  have s7 : ∑ c : ι, PsiW N (W c) m (lamWn N) (CWn N m) [] / LamW N m ≤ 1 / 8 := by
    refine le_trans (sum_div_le_card _ hW fun c =>
      (PsiW_nil (lamWn N) (CWn N m) (hE.sub c) (hE.card c)).le) ?_
    rw [div_le_div_iff₀ hW (by norm_num)]
    linarith
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  calc _ ≤ 1 / 40 + (1 / 40 + (1 / 40 + (1 / 40 + (1 / 40 + (1 / 40 + 1 / 8))))) :=
        add_le_add s1 (add_le_add s2 (add_le_add s3 (add_le_add s4 (add_le_add s5
          (add_le_add s6 s7)))))
    _ ≤ 11 / 40 := by norm_num

/-- Most histories stay good up to the horizon. -/
theorem good_mass (hG : NumGlobal N) (hE : EdgeHyp N W m)
    (hι : 8 * (Fintype.card ι : ℝ) ≤ LamW N m) :
    29 / 40 ≤ massFrom (hor N) (fun t => ind (GoodAll (Good N W m) t)) [] := by
  have h := massFrom_goodAll_ge (Good N W m) (hor N) (PsiAll N W m) (LamAll ι N m)
    (PsiAll_nonneg hG.nC W m) (LamAll_pos hG ι m)
    (fun s hs hlen => hs.openSet_nonempty hG.nA hlen.le)
    (fun c s hs hlen => PsiAll_super hG hE c s hs hlen)
    (fun s e hs hlen he hbad => PsiAll_bad hG hE s e hs hlen he hbad)
    (hor N) [] (goodAll_nil hG hE) (by simp)
  have h' := init_sum_le hG hE hι
  linarith

end

/- ## Survival of an edge set along good histories -/

theorem rho_nonneg (hN : 2 ≤ N) {m : ℝ} (hmM : m ≤ (N.choose 2 : ℝ)) :
    0 ≤ 1 - m / (5 * (N.choose 2 : ℝ)) := by
  have hM : (0 : ℝ) < (N.choose 2 : ℝ) := by
    have : 0 < N.choose 2 := Nat.choose_pos hN
    exact_mod_cast this
  have h1 : m / (5 * (N.choose 2 : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  linarith

theorem survive_real {m M g Q WO QQ : ℝ} (hm : 0 ≤ m) (hM : 0 < M) (hQ : Q ≤ QQ)
    (hS : 2 * QQ ≤ 5 * M * g) (hW : m / 2 * g ≤ WO) :
    Q - WO ≤ (1 - m / (5 * M)) * Q := by
  have h1 : m / (5 * M) * Q ≤ m / (5 * M) * (5 * M * g / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hm (by positivity))
  have h2 : m / (5 * M) * (5 * M * g / 2) = m / 2 * g := by
    field_simp
  have h3 : (1 - m / (5 * M)) * Q = Q - m / (5 * M) * Q := by ring
  rw [h3]
  linarith

section

variable {ι : Type} {W : ι → Finset (Sym2 (Fin N))} {m : ℝ}

/-- The mass of the good histories that avoid the edge set `W c` decays geometrically. -/
theorem survive (hG : NumGlobal N) (hE : EdgeHyp N W m) (hmM : m ≤ (N.choose 2 : ℝ)) (c : ι) :
    ∀ (r : ℕ) (s : List (Sym2 (Fin N))), s.length + r ≤ hor N →
      massFrom r (fun t => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) s
        ≤ (1 - m / (5 * (N.choose 2 : ℝ))) ^ r
          * ind (GoodAll (Good N W m) s ∧ W c ∩ s.toFinset = ∅) := by
  have hM : (0 : ℝ) < (N.choose 2 : ℝ) := by
    have : 0 < N.choose 2 := Nat.choose_pos hG.hN
    exact_mod_cast this
  have hρ0 : 0 ≤ 1 - m / (5 * (N.choose 2 : ℝ)) := rho_nonneg hG.hN hmM
  intro r
  induction r with
  | zero =>
    intro s _
    rw [massFrom_zero, pow_zero, one_mul]
  | succ r ih =>
    intro s hlen
    rw [massFrom_succ]
    by_cases hs : GoodAll (Good N W m) s ∧ W c ∩ s.toFinset = ∅
    · obtain ⟨hgood, hemp⟩ := hs
      have hlt : s.length < hor N := by omega
      have hgat := hgood.goodAt hG.nA hlt.le
      have hQpos := hgat.Q_pos
      have hQup := hgat.Q_upper
      have hWlow := hgood.self.2.2.2.2 c
      have hnS := hE.nS s.length hlt
      rw [ind_of ⟨hgood, hemp⟩, mul_one, div_le_iff₀ hQpos]
      have hterm : ∀ e ∈ openSet s.toFinset,
          massFrom r (fun t => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) (e :: s)
            ≤ (1 - m / (5 * (N.choose 2 : ℝ))) ^ r
              * (1 - (if e ∈ W c then (1 : ℝ) else 0)) := by
        intro e he
        refine le_trans (ih (e :: s) (by rw [List.length_cons]; omega)) ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ0 r)
        by_cases heW : e ∈ W c
        · rw [if_pos heW, sub_self, ind_of_not]
          rintro ⟨-, h⟩
          have hmem : e ∈ W c ∩ (e :: s).toFinset :=
            mem_inter.mpr ⟨heW, by rw [List.toFinset_cons]; exact mem_insert_self _ _⟩
          rw [h] at hmem
          exact absurd hmem (notMem_empty e)
        · rw [if_neg heW, sub_zero]
          exact ind_le_one _
      have hcount : ∑ e ∈ openSet s.toFinset, (1 - (if e ∈ W c then (1 : ℝ) else 0))
          = ((openSet s.toFinset).card : ℝ) - ((W c ∩ openSet s.toFinset).card : ℝ) := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_boole, filter_mem_eq_inter,
          inter_comm]
      calc ∑ e ∈ openSet s.toFinset,
            massFrom r (fun t => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) (e :: s)
          ≤ ∑ e ∈ openSet s.toFinset, (1 - m / (5 * (N.choose 2 : ℝ))) ^ r
              * (1 - (if e ∈ W c then (1 : ℝ) else 0)) := sum_le_sum hterm
        _ = (1 - m / (5 * (N.choose 2 : ℝ))) ^ r
              * (((openSet s.toFinset).card : ℝ) - ((W c ∩ openSet s.toFinset).card : ℝ)) := by
            rw [← mul_sum, hcount]
        _ ≤ (1 - m / (5 * (N.choose 2 : ℝ))) ^ r
              * ((1 - m / (5 * (N.choose 2 : ℝ))) * ((openSet s.toFinset).card : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (survive_real hE.m0 hM hQup hnS hWlow) (pow_nonneg hρ0 r)
        _ = (1 - m / (5 * (N.choose 2 : ℝ))) ^ (r + 1) * ((openSet s.toFinset).card : ℝ) := by
            rw [pow_succ, mul_assoc]
    · rw [ind_of_not hs, mul_zero]
      refine div_nonpos_of_nonpos_of_nonneg (sum_nonpos fun e he => ?_) (Nat.cast_nonneg _)
      refine le_trans (ih (e :: s) (by rw [List.length_cons]; omega)) ?_
      rw [ind_of_not, mul_zero]
      rintro ⟨hg, hemp⟩
      apply hs
      refine ⟨(goodAll_cons.mp hg).2, ?_⟩
      rw [List.toFinset_cons] at hemp
      refine subset_empty.mp ?_
      rw [← hemp]
      exact inter_subset_inter_left (subset_insert _ _)

end

/- ## A valid history hitting every edge set -/

theorem exists_history (hG : NumGlobal N) {ι : Type} [Fintype ι]
    {W : ι → Finset (Sym2 (Fin N))} {m : ℝ} (hE : EdgeHyp N W m)
    (hmM : m ≤ (N.choose 2 : ℝ)) (h1 : 8 * (Fintype.card ι : ℝ) ≤ LamW N m)
    (h2 : (Fintype.card ι : ℝ) * (1 - m / (5 * (N.choose 2 : ℝ))) ^ hor N ≤ 1 / 8) :
    ∃ t : List (Sym2 (Fin N)), Valid t ∧ ∀ c, (W c ∩ t.toFinset).Nonempty := by
  have hgood := good_mass hG hE h1
  have hρ0 : 0 ≤ 1 - m / (5 * (N.choose 2 : ℝ)) := rho_nonneg hG.hN hmM
  have hsurv : ∀ c,
      massFrom (hor N) (fun t => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) []
        ≤ (1 - m / (5 * (N.choose 2 : ℝ))) ^ hor N := by
    intro c
    refine le_trans (survive hG hE hmM c (hor N) [] (by simp)) ?_
    exact mul_le_of_le_one_right (pow_nonneg hρ0 _) (ind_le_one _)
  have hsum : ∑ c,
      massFrom (hor N) (fun t => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) []
        ≤ 1 / 8 := by
    refine le_trans (sum_le_sum fun c _ => hsurv c) ?_
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact h2
  have e1 := massFrom_sub (fun t => ind (GoodAll (Good N W m) t))
    (fun t => ∑ c, ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) (hor N) []
  have e2 := massFrom_sum (univ : Finset ι)
    (fun c t => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) (hor N) []
  have hpos : 0 < massFrom (hor N) (fun t => ind (GoodAll (Good N W m) t)
      - ∑ c, ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)) [] := by
    rw [e1, e2]
    linarith
  obtain ⟨t, -, ht⟩ := exists_of_massFrom_pos (hor N) [] hpos
  have htG : GoodAll (Good N W m) t := by
    by_contra hcon
    have h0 : ∑ c, ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅) = 0 :=
      sum_eq_zero fun c _ => ind_of_not fun h => hcon h.1
    rw [ind_of_not hcon, h0] at ht
    exact absurd ht (by norm_num)
  refine ⟨t, htG.self.1, fun c => ?_⟩
  rw [nonempty_iff_ne_empty]
  intro hemp
  have h3 : ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅)
      ≤ ∑ c, ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅) :=
    single_le_sum (f := fun c => ind (GoodAll (Good N W m) t ∧ W c ∩ t.toFinset = ∅))
      (fun c _ => ind_nonneg _) (mem_univ c)
  rw [ind_of ⟨htG, hemp⟩] at h3
  rw [ind_of htG] at ht
  linarith

end TFP
end E1182

end AssemblePart

section BlockerPart

/-
# From the process to the blocker statement

The edge sets are the images of the edges of `H` under all embeddings of its vertex set into
`Fin N`; a valid history hitting all of them is a triangle-free graph meeting every copy of `H`.
-/

open Finset

namespace E1182
namespace TFP

variable {N : ℕ}

theorem blockerAt_of_num {A : ℝ} (hG : NumGlobal N) (hE : NumEdge A N) : BlockerAt A N := by
  intro α _ _ H _ hα hαN hdeg hedges
  have hm0 : (0 : ℝ) ≤ (H.edgeFinset.card : ℝ) := Nat.cast_nonneg _
  have hmM : (H.edgeFinset.card : ℝ) ≤ (N.choose 2 : ℝ) := by
    have h1 := H.card_edgeFinset_le_card_choose_two
    have h2 := Nat.choose_le_choose 2 hαN
    exact_mod_cast h1.trans h2
  have hEH : EdgeHyp N (fun c : α ↪ Fin N => H.edgeFinset.map c.sym2Map)
      (H.edgeFinset.card : ℝ) :=
    { m0 := hm0
      card := fun c => by rw [card_map]
      deg := fun c a => by
        have hD : ∀ x, H.degree x ≤ ⌊(N : ℝ) ^ (9 / 10 : ℝ)⌋₊ := fun x => Nat.le_floor (hdeg x)
        have h1 := degW_map_le H c hD a
        have h2 : ((⌊(N : ℝ) ^ (9 / 10 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) :=
          Nat.floor_le (by positivity)
        exact le_trans (by exact_mod_cast h1) h2
      sub := fun c e he => by
        obtain ⟨e₀, he₀, rfl⟩ := mem_map.mp he
        induction e₀ using Sym2.ind with
        | h a b =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he₀
          rw [Function.Embedding.sym2Map_apply, Sym2.map_mk]
          exact mk_mem_openSet.mpr ⟨fun h => he₀.ne (c.injective h), notMem_empty _,
            fun w hw => notMem_empty _ hw.1⟩
      gpos := hE.gpos
      nS := hE.nS
      nW := hE.nW _ hm0 hmM
      cW0 := hE.cW0 _ hm0 }
  obtain ⟨f1, f2⟩ := hE.f2 (Fintype.card α) (H.edgeFinset.card : ℝ) hα hαN hedges hmM
  have hcard : (Fintype.card (α ↪ Fin N) : ℝ) ≤ (N : ℝ) ^ Fintype.card α := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    exact_mod_cast Nat.descFactorial_le_pow N (Fintype.card α)
  have hρ0 := rho_nonneg hG.hN hmM
  obtain ⟨t, htv, htW⟩ := exists_history hG hEH hmM (by linarith)
    (le_trans (mul_le_mul_of_nonneg_right hcard (pow_nonneg hρ0 _)) f2)
  refine ⟨SimpleGraph.fromEdgeSet (t.toFinset : Set (Sym2 (Fin N))), ?_, ?_⟩
  · apply cliqueFree3_of_forall
    intro a b c hab hac hbc
    rw [SimpleGraph.fromEdgeSet_adj] at hab hac hbc
    exact (Valid.tf htv).2 a b c (mem_coe.mp hab.1) (mem_coe.mp hac.1) (mem_coe.mp hbc.1)
  · intro φ hφ
    obtain ⟨e, he⟩ := htW ⟨φ, hφ⟩
    obtain ⟨heW, het⟩ := mem_inter.mp he
    obtain ⟨e₀, he₀, rfl⟩ := mem_map.mp heW
    induction e₀ using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he₀
      rw [Function.Embedding.sym2Map_apply, Sym2.map_mk] at het
      refine ⟨a, b, he₀, ?_⟩
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨mem_coe.mpr het, fun h => he₀.ne (hφ h)⟩

end TFP
end E1182

end BlockerPart

section NumGlobalProofPart

/-
# The numerical facts not involving edge sets hold for all large `N`

`numGlobal_eventually : ∀ᶠ N in atTop, NumGlobal N`.

All auxiliary declarations are kept in the namespace `NumGlobalAux`, so that their names cannot
clash with declarations of other parts. Structure of the proof:

* `rp_*`: products and comparisons of real powers of a number `n` with `10⁴ ≤ n^{1/200}`;
* `num_*`: the explicit inequalities between powers of `n` that are needed;
* `Pt`: the facts about one index of the trajectory and of the error sequences, in a form with
  three abstract bounds (`A` for `(1 + ŷ + eY) / Q̂`, `Y` for `ŷ + eY`, `J` for `x̂ / Q̂`), and the
  estimates for the five conditions of `NumB` in terms of these bounds (`Pt.numB`);
* `pt_of`: `Pt` follows from the conclusions of `traj_facts` and `err_facts`;
* `numGlobal_of`: all fields of `NumGlobal N` for one `N` with `10⁴ ≤ N` and `10⁴ ≤ N^{1/200}`.

The bounds used are `A = N^{-299/200}`, `Y = N^{101/200}`, `J = 2 / N` and
`hor N ≤ N^{301/200} / 100` (from `√(log N) ≤ N^{1/200}`).
-/

namespace E1182
namespace TFP

namespace NumGlobalAux

/- ## Powers of a large real number -/

section Powers

variable {n : ℝ}

theorem rp_mul (hn : 0 < n) {a b c : ℝ} (h : a + b = c) : n ^ a * n ^ b = n ^ c := by
  rw [← Real.rpow_add hn, h]

theorem rp_self_mul (hn : 0 < n) {b c : ℝ} (h : 1 + b = c) : n * n ^ b = n ^ c := by
  rw [← h, Real.rpow_add hn, Real.rpow_one]

theorem rp_mul_self (hn : 0 < n) {a c : ℝ} (h : a + 1 = c) : n ^ a * n = n ^ c := by
  rw [← h, Real.rpow_add hn, Real.rpow_one]

theorem rp_mul_nat (hn : 0 < n) (k : ℕ) {a c : ℝ} (h : a + (k : ℝ) = c) :
    n ^ a * n ^ k = n ^ c := by
  rw [← h, Real.rpow_add hn, Real.rpow_natCast]

theorem rp_le (hn : 1 ≤ n) {a b : ℝ} (h : a ≤ b) : n ^ a ≤ n ^ b :=
  Real.rpow_le_rpow_of_exponent_le hn h

/-- `c n^a ≤ n^b` when `c ≤ 10⁴ ≤ n^{1/200}` and `a + 1/200 ≤ b`. -/
theorem rp_cle (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) {c a b : ℝ}
    (hc : c ≤ 10000) (hab : a + 1 / 200 ≤ b) : c * n ^ a ≤ n ^ b := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  calc c * n ^ a ≤ n ^ (1 / 200 : ℝ) * n ^ a :=
        mul_le_mul_of_nonneg_right (hc.trans hK) (Real.rpow_nonneg hn0.le a)
    _ = n ^ (1 / 200 + a) := (Real.rpow_add hn0 _ _).symm
    _ ≤ n ^ b := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

end Powers

/- ## Explicit inequalities between powers -/

section Numeric

variable {n : ℝ}

/-- The inequalities used to derive the bounds `A`, `Y` at one index. -/
theorem num_pt (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    n ^ (-(1 / 20) : ℝ) ≤ 1 / 2 ∧ 1 ≤ n ^ (9 / 20 : ℝ) ∧
    2 * n ^ (9 / 20 : ℝ)
      ≤ 82 / 100 * (n ^ (-(299 / 200) : ℝ) * (n ^ 2 / 4 * n ^ (-(1 / 2000) : ℝ))) ∧
    n ^ (-(299 / 200) : ℝ) * n ^ 2 ≤ n ^ (101 / 200 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have e1 : n ^ (-(299 / 200) : ℝ) * n ^ 2 = n ^ (101 / 200 : ℝ) :=
    rp_mul_nat hn0 2 (by norm_num)
  have e2 : n ^ (101 / 200 : ℝ) * n ^ (-(1 / 2000) : ℝ) = n ^ (1009 / 2000 : ℝ) :=
    rp_mul hn0 (by norm_num)
  have a1 := rp_cle hn hK (c := 2) (a := -(1 / 20)) (b := 0) (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at a1
  have a2 := rp_cle hn hK (c := 10) (a := 9 / 20) (b := 1009 / 2000) (by norm_num) (by norm_num)
  have hpos : 0 ≤ n ^ (1009 / 2000 : ℝ) := Real.rpow_nonneg hn0.le _
  refine ⟨by linarith, Real.one_le_rpow hn (by norm_num), ?_, e1.le⟩
  have e3 : n ^ (-(299 / 200) : ℝ) * (n ^ 2 / 4 * n ^ (-(1 / 2000) : ℝ))
      = n ^ (1009 / 2000 : ℝ) / 4 := by
    rw [← e2, ← e1]; ring
  rw [e3]
  linarith

/-- `√(log n) ≤ n^{1/200}`. -/
theorem num_sqrt_log (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    Real.sqrt (Real.log n) ≤ n ^ (1 / 200 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  rw [Real.sqrt_le_iff]
  refine ⟨Real.rpow_nonneg hn0.le _, ?_⟩
  have h1 : Real.log n ≤ n ^ (1 / 200 : ℝ) / (1 / 200) :=
    Real.log_le_rpow_div hn0.le (by norm_num)
  have h4 : n ^ (1 / 200 : ℝ) / (1 / 200) = 200 * n ^ (1 / 200 : ℝ) := by ring
  rw [h4] at h1
  have h2 := rp_cle hn hK (c := 200) (a := 1 / 200) (b := 1 / 100) (by norm_num) (by norm_num)
  have h3 : (n ^ (1 / 200 : ℝ)) ^ 2 = n ^ (1 / 100 : ℝ) := by
    rw [sq]; exact rp_mul hn0 (by norm_num)
  rw [h3]
  linarith

/-- First condition of `NumB`: `lamX * 2 n A ≤ 1`. -/
theorem num_B1 (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    n ^ (-(4 / 5) : ℝ) * (2 * (n * n ^ (-(299 / 200) : ℝ))) ≤ 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have eP : n * n ^ (-(299 / 200) : ℝ) = n ^ (-(99 / 200) : ℝ) :=
    rp_self_mul hn0 (by norm_num)
  have e1 : n ^ (-(4 / 5) : ℝ) * n ^ (-(99 / 200) : ℝ) = n ^ (-(259 / 200) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have a1 := rp_cle hn hK (c := 2) (a := -(259 / 200)) (b := 0) (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at a1
  rw [eP]
  linarith

/-- Second condition of `NumB`: `lamX * (2 + 2 Dmx) ≤ 1`. -/
theorem num_B2 (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    n ^ (-(4 / 5) : ℝ) * (2 + 2 * n ^ (51 / 100 : ℝ)) ≤ 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have e1 : n ^ (-(4 / 5) : ℝ) * n ^ (51 / 100 : ℝ) = n ^ (-(29 / 100) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have a1 := rp_cle hn hK (c := 4) (a := -(4 / 5)) (b := 0) (by norm_num) (by norm_num)
  have a2 := rp_cle hn hK (c := 4) (a := -(29 / 100)) (b := 0) (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at a1 a2
  linarith

/-- Third condition of `NumB`: the bound for the second moment of `X` is at most `vX`. -/
theorem num_B3 (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    16 * (2 + 2 * n ^ (51 / 100 : ℝ)) * (n * n ^ (-(299 / 200) : ℝ))
      + 2 * (30 * (n * n ^ (-(299 / 200) : ℝ))) ^ 2 ≤ n ^ (1 / 20 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have eP : n * n ^ (-(299 / 200) : ℝ) = n ^ (-(99 / 200) : ℝ) :=
    rp_self_mul hn0 (by norm_num)
  have e1 : n ^ (51 / 100 : ℝ) * n ^ (-(99 / 200) : ℝ) = n ^ (3 / 200 : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e2 : n ^ (-(99 / 200) : ℝ) * n ^ (-(99 / 200) : ℝ) = n ^ (-(99 / 100) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have a1 := rp_cle hn hK (c := 96) (a := -(99 / 200)) (b := 1 / 20) (by norm_num) (by norm_num)
  have a2 := rp_cle hn hK (c := 96) (a := 3 / 200) (b := 1 / 20) (by norm_num) (by norm_num)
  have a3 := rp_cle hn hK (c := 5400) (a := -(99 / 100)) (b := 1 / 20) (by norm_num)
    (by norm_num)
  rw [eP]
  linarith

/-- Fourth condition of `NumB`: `lamY * (2 + Zmx + 2 J + Y A) ≤ 1`. -/
theorem num_B4 (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    n ^ (-(3 / 10) : ℝ) * (2 + n ^ (1 / 40 : ℝ)
      + (2 * (2 / n) + n ^ (101 / 200 : ℝ) * n ^ (-(299 / 200) : ℝ))) ≤ 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have eR : n ^ (101 / 200 : ℝ) * n ^ (-(299 / 200) : ℝ) = n ^ (-(99 / 100) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have eJ : 2 / n = 2 * n ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have e1 : n ^ (-(3 / 10) : ℝ) * n ^ (1 / 40 : ℝ) = n ^ (-(11 / 40) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e2 : n ^ (-(3 / 10) : ℝ) * n ^ (-1 : ℝ) = n ^ (-(13 / 10) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e3 : n ^ (-(3 / 10) : ℝ) * n ^ (-(99 / 100) : ℝ) = n ^ (-(129 / 100) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have a0 := rp_cle hn hK (c := 8) (a := -(3 / 10)) (b := 0) (by norm_num) (by norm_num)
  have a1 := rp_cle hn hK (c := 4) (a := -(11 / 40)) (b := 0) (by norm_num) (by norm_num)
  have a2 := rp_cle hn hK (c := 16) (a := -(13 / 10)) (b := 0) (by norm_num) (by norm_num)
  have a3 := rp_cle hn hK (c := 4) (a := -(129 / 100)) (b := 0) (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at a0 a1 a2 a3
  rw [eR, eJ]
  linarith

/-- Fifth condition of `NumB`: the bound for the second moment of `Y` is at most `vY`. -/
theorem num_B5 (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    48 * (2 / n) + 6 * (3 + n ^ (1 / 40 : ℝ)) * (n ^ (101 / 200 : ℝ) * n ^ (-(299 / 200) : ℝ))
      + 3 * (12 * (2 / n) + 5 * (n ^ (101 / 200 : ℝ) * n ^ (-(299 / 200) : ℝ))) ^ 2
      ≤ n ^ (-(19 / 20) : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have eR : n ^ (101 / 200 : ℝ) * n ^ (-(299 / 200) : ℝ) = n ^ (-(99 / 100) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have eJ : 2 / n = 2 * n ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hI0 : 0 ≤ n ^ (-1 : ℝ) := Real.rpow_nonneg hn0.le _
  have hR0 : 0 ≤ n ^ (-(99 / 100) : ℝ) := Real.rpow_nonneg hn0.le _
  have hIR : n ^ (-1 : ℝ) ≤ n ^ (-(99 / 100) : ℝ) := rp_le hn (by norm_num)
  have e1 : n ^ (1 / 40 : ℝ) * n ^ (-(99 / 100) : ℝ) = n ^ (-(193 / 200) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e2 : n ^ (-(99 / 100) : ℝ) * n ^ (-(99 / 100) : ℝ) = n ^ (-(99 / 50) : ℝ) :=
    rp_mul hn0 (by norm_num)
  have a1 := rp_cle hn hK (c := 342) (a := -(99 / 100)) (b := -(19 / 20)) (by norm_num)
    (by norm_num)
  have a2 := rp_cle hn hK (c := 18) (a := -(193 / 200)) (b := -(19 / 20)) (by norm_num)
    (by norm_num)
  have a3 := rp_cle hn hK (c := 7569) (a := -(99 / 50)) (b := -(19 / 20)) (by norm_num)
    (by norm_num)
  rw [eR, eJ]
  have hsq : (12 * (2 * n ^ (-1 : ℝ)) + 5 * n ^ (-(99 / 100) : ℝ)) ^ 2
      ≤ (29 * n ^ (-(99 / 100) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith

/-- The exponents of the potentials for `X` and `Y`. -/
theorem num_XY (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    n ^ (-(4 / 5) : ℝ) * n ^ (17 / 20 : ℝ) = n ^ (1 / 20 : ℝ) ∧
    (n ^ (-(4 / 5) : ℝ)) ^ 2 * n ^ (1 / 20 : ℝ) = n ^ (-(31 / 20) : ℝ) ∧
    n ^ (-(3 / 10) : ℝ) * n ^ (7 / 20 : ℝ) = n ^ (1 / 20 : ℝ) ∧
    (n ^ (-(3 / 10) : ℝ)) ^ 2 * n ^ (-(19 / 20) : ℝ) = n ^ (-(31 / 20) : ℝ) ∧
    n ^ (-(31 / 20) : ℝ) * (n ^ (301 / 200 : ℝ) / 100) ≤ 1 ∧
    n ^ (1 / 40 : ℝ) / 4 + 1 ≤ n ^ (1 / 20 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  refine ⟨rp_mul hn0 (by norm_num), ?_, rp_mul hn0 (by norm_num), ?_, ?_, ?_⟩
  · rw [sq, rp_mul hn0 (by norm_num : (-(4 / 5) : ℝ) + -(4 / 5) = -(8 / 5))]
    exact rp_mul hn0 (by norm_num)
  · rw [sq, rp_mul hn0 (by norm_num : (-(3 / 10) : ℝ) + -(3 / 10) = -(3 / 5))]
    exact rp_mul hn0 (by norm_num)
  · have e : n ^ (-(31 / 20) : ℝ) * n ^ (301 / 200 : ℝ) = n ^ (-(9 / 200) : ℝ) :=
      rp_mul hn0 (by norm_num)
    have h1 : n ^ (-(9 / 200) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
    linarith
  · have a := rp_cle hn hK (c := 2) (a := 0) (b := 1 / 40) (by norm_num) (by norm_num)
    rw [Real.rpow_zero] at a
    have b : n ^ (1 / 40 : ℝ) ≤ n ^ (1 / 20 : ℝ) := rp_le hn (by norm_num)
    linarith

/-- `40 n² ≤ exp (n^{1/40} / 4)`. -/
theorem num_exp (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    40 * n ^ 2 ≤ Real.exp (n ^ (1 / 40 : ℝ) / 4) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have h1 : Real.log n ≤ n ^ (1 / 200 : ℝ) / (1 / 200) :=
    Real.log_le_rpow_div hn0.le (by norm_num)
  have h4 : n ^ (1 / 200 : ℝ) / (1 / 200) = 200 * n ^ (1 / 200 : ℝ) := by ring
  rw [h4] at h1
  have h2 : n ^ 2 = Real.exp (Real.log n + Real.log n) := by
    rw [Real.exp_add, Real.exp_log hn0]; ring
  have h3 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have a1 := rp_cle hn hK (c := 320) (a := 0) (b := 1 / 40) (by norm_num) (by norm_num)
  rw [Real.rpow_zero] at a1
  have a2 := rp_cle hn hK (c := 3200) (a := 1 / 200) (b := 1 / 40) (by norm_num) (by norm_num)
  calc 40 * n ^ 2 ≤ Real.exp 40 * Real.exp (Real.log n + Real.log n) := by
        rw [h2]; exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.exp (40 + (Real.log n + Real.log n)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (n ^ (1 / 40 : ℝ) / 4) := Real.exp_le_exp.mpr (by linarith)

/-- The exponent comparison for the degree potential. -/
theorem num_D (hn : 1 ≤ n) :
    n ^ (301 / 200 : ℝ) * n ≤ n ^ (51 / 100 : ℝ) * (n ^ 2 * n ^ (-(1 / 2000) : ℝ)) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have e1 : n ^ (301 / 200 : ℝ) * n = n ^ (501 / 200 : ℝ) := rp_mul_self hn0 (by norm_num)
  have e2 : n ^ (51 / 100 : ℝ) * n ^ 2 = n ^ (251 / 100 : ℝ) := rp_mul_nat hn0 2 (by norm_num)
  have e3 : n ^ (251 / 100 : ℝ) * n ^ (-(1 / 2000) : ℝ) = n ^ (5019 / 2000 : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e4 : n ^ (51 / 100 : ℝ) * (n ^ 2 * n ^ (-(1 / 2000) : ℝ)) = n ^ (5019 / 2000 : ℝ) := by
    rw [← e3, ← e2]; ring
  rw [e1, e4]
  exact rp_le hn (by norm_num)

/-- The exponent comparison for the codegree potential. -/
theorem num_Z (hn : 1 ≤ n) (hK : (10000 : ℝ) ≤ n ^ (1 / 200 : ℝ)) :
    n ^ (301 / 200 : ℝ) * (2 * n ^ (51 / 100 : ℝ))
      ≤ n ^ (1 / 40 : ℝ) * (n ^ 2 * n ^ (-(1 / 2000) : ℝ)) := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have e1 : n ^ (301 / 200 : ℝ) * n ^ (51 / 100 : ℝ) = n ^ (403 / 200 : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e2 : n ^ (1 / 40 : ℝ) * n ^ 2 = n ^ (81 / 40 : ℝ) := rp_mul_nat hn0 2 (by norm_num)
  have e3 : n ^ (81 / 40 : ℝ) * n ^ (-(1 / 2000) : ℝ) = n ^ (4049 / 2000 : ℝ) :=
    rp_mul hn0 (by norm_num)
  have e4 : n ^ (1 / 40 : ℝ) * (n ^ 2 * n ^ (-(1 / 2000) : ℝ)) = n ^ (4049 / 2000 : ℝ) := by
    rw [← e3, ← e2]; ring
  have a1 := rp_cle hn hK (c := 2) (a := 403 / 200) (b := 4049 / 2000) (by norm_num)
    (by norm_num)
  rw [e4]
  linarith

end Numeric

/- ## One index: abstract estimates -/

/-- The facts about one index of the trajectory (`Q`, `x`, `y`) and of the error sequences
(`dx`, `dy`, `dq`) that are used for the supermartingale conditions: `A` bounds
`(1 + y + dy) / Q`, `Y` bounds `y + dy` and `J` bounds `x / Q`. -/
structure Pt (n Q x y dx dy dq A Y J : ℝ) : Prop where
  Q0 : 0 < Q
  x0 : 0 ≤ x
  xn : x ≤ n
  xJ : x ≤ J * Q
  y0 : 0 ≤ y
  dx0 : 0 ≤ dx
  dxx : dx ≤ x
  dy0 : 0 ≤ dy
  dq0 : 0 ≤ dq
  dqQ : dq ≤ Q
  yY : y + dy ≤ Y
  aA : 1 + y + dy ≤ A * Q

namespace Pt

variable {n Q x y dx dy dq A Y J : ℝ}

/-- The drift of the trajectory `x`. -/
theorem drift_x (h : Pt n Q x y dx dy dq A Y J) :
    0 ≤ x * (2 + 2 * y) / Q ∧ x * (2 + 2 * y) / Q ≤ 2 * (n * A) := by
  obtain ⟨hQ, hx0, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, hdqQ, hyY, haA⟩ := h
  have hn0 : 0 ≤ n := hx0.trans hxn
  have hAQ : 0 ≤ A * Q := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hQ]
  have t : x * (2 + 2 * y) ≤ n * (2 * (A * Q)) :=
    mul_le_mul hxn (by linarith) (by linarith) hn0
  linarith

/-- The main term of the second moment of `X`. -/
theorem term_x (h : Pt n Q x y dx dy dq A Y J) {D : ℝ} (hD : 0 ≤ D) :
    4 * (2 + 2 * D) * ((x + dx) * (2 + 2 * (y + dy))) / Q ≤ 16 * (2 + 2 * D) * (n * A) := by
  obtain ⟨hQ, hx0, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, hdqQ, hyY, haA⟩ := h
  have hn0 : 0 ≤ n := hx0.trans hxn
  have hAQ : 0 ≤ A * Q := by linarith
  rw [div_le_iff₀ hQ]
  have t : (x + dx) * (2 + 2 * (y + dy)) ≤ (2 * n) * (2 * (A * Q)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have t2 := mul_le_mul_of_nonneg_left t (by linarith : (0 : ℝ) ≤ 4 * (2 + 2 * D))
  linarith

/-- The drift allowance for `X`. -/
theorem DXr_le (h : Pt n Q x y dx dy dq A Y J) :
    0 ≤ DXr Q x y dx dy dq ∧ DXr Q x y dx dy dq ≤ 28 * (n * A) := by
  obtain ⟨hQ, hx0, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, hdqQ, hyY, haA⟩ := h
  have hn0 : 0 ≤ n := hx0.trans hxn
  have hAQ : 0 ≤ A * Q := by linarith
  have hk0 : 0 ≤ dq / Q := div_nonneg hdq0 hQ.le
  have hk1 : dq / Q ≤ 1 := (div_le_one hQ).mpr hdqQ
  unfold DXr
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hQ]
  have t1 : (2 + 2 * y) * dx ≤ (2 * (A * Q)) * n :=
    mul_le_mul (by linarith) (hdxx.trans hxn) hdx0 (by linarith)
  have t2 : x * dy ≤ n * (A * Q) := mul_le_mul hxn (by linarith) hdy0 hn0
  have t3 : x * (2 + 2 * y) ≤ n * (2 * (A * Q)) :=
    mul_le_mul hxn (by linarith) (by linarith) hn0
  have t4 : x * (2 + 2 * y) * (dq / Q) ≤ n * (2 * (A * Q)) * 1 :=
    mul_le_mul t3 hk1 hk0 (mul_nonneg hn0 (by linarith))
  linarith

/-- The drift of the trajectory `y`. -/
theorem absY_le (h : Pt n Q x y dx dy dq A Y J) :
    |(2 * x - y * (1 + y)) / Q| ≤ 2 * J + Y * A := by
  obtain ⟨hQ, hx0, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, hdqQ, hyY, haA⟩ := h
  have hAQ : 0 ≤ A * Q := by linarith
  have hY0 : 0 ≤ Y := by linarith
  rw [abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
  have t1 : y * (1 + y) ≤ Y * (A * Q) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hY0
  have t0 : 0 ≤ y * (1 + y) := mul_nonneg hy0 (by linarith)
  have t2 : |2 * x - y * (1 + y)| ≤ 2 * x + y * (1 + y) := by
    rw [_root_.abs_le]; constructor <;> linarith
  linarith

/-- The main term of the second moment of `Y`. -/
theorem term_y (h : Pt n Q x y dx dy dq A Y J) {Z : ℝ} (hZ : 0 ≤ Z) :
    2 * (12 * (x + dx) + 3 * ((2 + Z) * ((y + dy) * (1 + y + dy)) + (y + dy) ^ 2)) / Q
      ≤ 48 * J + 6 * (3 + Z) * (Y * A) := by
  obtain ⟨hQ, hx0, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, hdqQ, hyY, haA⟩ := h
  have hY0 : 0 ≤ Y := by linarith
  rw [div_le_iff₀ hQ]
  have t1 : (y + dy) * (1 + y + dy) ≤ Y * (A * Q) :=
    mul_le_mul hyY haA (by linarith) hY0
  have t2 : (y + dy) ^ 2 ≤ (y + dy) * (1 + y + dy) := by nlinarith
  have t3 : (2 + Z) * ((y + dy) * (1 + y + dy)) ≤ (2 + Z) * (Y * (A * Q)) :=
    mul_le_mul_of_nonneg_left t1 (by linarith)
  linarith

/-- The drift allowance for `Y`. -/
theorem DYr_le (h : Pt n Q x y dx dy dq A Y J) :
    0 ≤ DYr Q x y dx dy dq ∧ DYr Q x y dx dy dq ≤ 10 * J + 4 * (Y * A) := by
  obtain ⟨hQ, hx0, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, hdqQ, hyY, haA⟩ := h
  have hY0 : 0 ≤ Y := by linarith
  have hk0 : 0 ≤ dq / Q := div_nonneg hdq0 hQ.le
  have hk1 : dq / Q ≤ 1 := (div_le_one hQ).mpr hdqQ
  unfold DYr
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hQ]
  have t0 : 0 ≤ (y + dy) * (1 + y + dy) := mul_nonneg (by linarith) (by linarith)
  have t1 : (y + dy) * (1 + y + dy) ≤ Y * (A * Q) :=
    mul_le_mul hyY haA (by linarith) hY0
  have t2 : dq / Q * x ≤ 1 * x := mul_le_mul_of_nonneg_right hk1 hx0
  have t3 : dy * (1 + 2 * y + dy) ≤ 2 * ((y + dy) * (1 + y + dy)) := by
    nlinarith [mul_nonneg hy0 hy0, mul_nonneg hy0 hdy0, mul_nonneg hdy0 hdy0]
  have t4 : dq / Q * ((y + dy) * (1 + y + dy)) ≤ 1 * ((y + dy) * (1 + y + dy)) :=
    mul_le_mul_of_nonneg_right hk1 t0
  linarith

/-- The five conditions of `NumB` at one index, from inequalities between the bounds. -/
theorem numB (h : Pt n Q x y dx dy dq A Y J) {D Z lX vX' lY vY' : ℝ}
    (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hlX : 0 ≤ lX) (hlY : 0 ≤ lY)
    (n1 : lX * (2 * (n * A)) ≤ 1)
    (n2 : lX * (2 + 2 * D) ≤ 1)
    (n3 : 16 * (2 + 2 * D) * (n * A) + 2 * (30 * (n * A)) ^ 2 ≤ vX')
    (n4 : lY * (2 + Z + (2 * J + Y * A)) ≤ 1)
    (n5 : 48 * J + 6 * (3 + Z) * (Y * A) + 3 * (12 * J + 5 * (Y * A)) ^ 2 ≤ vY') :
    lX * (x * (2 + 2 * y) / Q) ≤ 1 ∧
    lX * (2 + 2 * D) ≤ 1 ∧
    4 * (2 + 2 * D) * ((x + dx) * (2 + 2 * (y + dy))) / Q
      + 2 * (x * (2 + 2 * y) / Q + DXr Q x y dx dy dq) ^ 2 ≤ vX' ∧
    lY * (2 + Z + |(2 * x - y * (1 + y)) / Q|) ≤ 1 ∧
    2 * (12 * (x + dx) + 3 * ((2 + Z) * ((y + dy) * (1 + y + dy)) + (y + dy) ^ 2)) / Q
      + 3 * (|(2 * x - y * (1 + y)) / Q| + DYr Q x y dx dy dq) ^ 2 ≤ vY' := by
  obtain ⟨a0, a1⟩ := h.drift_x
  have a2 := h.term_x hD
  obtain ⟨a3, a4⟩ := h.DXr_le
  have a5 := h.absY_le
  have a6 := h.term_y hZ
  obtain ⟨a7, a8⟩ := h.DYr_le
  have a9 := abs_nonneg ((2 * x - y * (1 + y)) / Q)
  refine ⟨le_trans (mul_le_mul_of_nonneg_left a1 hlX) n1, n2, ?_, ?_, ?_⟩
  · have hsq : (x * (2 + 2 * y) / Q + DXr Q x y dx dy dq) ^ 2 ≤ (30 * (n * A)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ hlY) n4
    linarith
  · have hsq : (|(2 * x - y * (1 + y)) / Q| + DYr Q x y dx dy dq) ^ 2
        ≤ (12 * J + 5 * (Y * A)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith

end Pt

/-- The facts about one index follow from the conclusions of `traj_facts` and `err_facts`
(`M = N.choose 2`, `g = N^{-1/2000}`, `ε = N^{-1/20}`, `S = N^{9/20}`). -/
theorem pt_of {n M g Q x y dx dy dq i ε S A Y : ℝ}
    (hn : 2 ≤ n) (hM : M = n * (n - 1) / 2) (hg : 0 < g)
    (hQlow : M * g ≤ Q) (hQM : Q ≤ M)
    (hy0 : 0 ≤ y) (hy : y ≤ 9 * i * Q / n ^ 3)
    (hx0 : 0 < x) (hx : x ≤ (n - 2) * (Q / M) ^ 2)
    (hdx0 : 0 ≤ dx) (hdx : dx ≤ ε * x)
    (hdy0 : 0 ≤ dy) (hdy : dy ≤ ε * (y + S))
    (hdq0 : 0 ≤ dq) (hdq : dq ≤ ε * Q)
    (hε : ε ≤ 1 / 2)
    (hA : 0 ≤ A) (hi : i ≤ A * n ^ 3 / 100)
    (hS1 : 1 ≤ S)
    (h2 : 2 * S ≤ 82 / 100 * (A * (n ^ 2 / 4 * g)))
    (hY : A * n ^ 2 ≤ Y) :
    Pt n Q x y dx dy dq A Y (2 / n) ∧ 2 * dq ≤ Q := by
  have hn0 : 0 < n := by linarith
  have hM0 : 0 < M := by
    rw [hM]; exact div_pos (mul_pos hn0 (by linarith)) (by norm_num)
  have hMlow : n ^ 2 / 4 ≤ M := by
    rw [hM]; nlinarith [mul_nonneg hn0.le (by linarith : (0 : ℝ) ≤ n - 2)]
  have hMup : M ≤ n ^ 2 / 2 := by
    rw [hM]; nlinarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (mul_pos hM0 hg) hQlow
  -- bounds for `x`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Q / M := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos hQ0 hM0
  have hr1 : r ≤ 1 := by rw [hr]; exact (div_le_one hM0).mpr hQM
  have hQr : Q = r * M := by rw [hr]; field_simp
  rw [← hr] at hx
  have hx1 : x ≤ (n - 2) * r := by
    have hr2 : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hr1)]
    exact hx.trans (mul_le_mul_of_nonneg_left hr2 (by linarith))
  have hxn : x ≤ n := by
    have h5 : (n - 2) * r ≤ (n - 2) * 1 := mul_le_mul_of_nonneg_left hr1 (by linarith)
    linarith
  have hxJ : x ≤ 2 / n * Q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hn0]
    have h5 : x * n ≤ (n - 2) * r * n := mul_le_mul_of_nonneg_right hx1 hn0.le
    have h6 : 0 ≤ r * n := mul_nonneg hr0.le hn0.le
    rw [hQr, hM]
    linarith
  -- the errors
  have hε1 : ε ≤ 1 := by linarith
  have hdxx : dx ≤ x := by
    have h5 : ε * x ≤ 1 * x := mul_le_mul_of_nonneg_right hε1 hx0.le
    linarith
  have hdq2 : 2 * dq ≤ Q := by
    have h5 : ε * Q ≤ 1 / 2 * Q := mul_le_mul_of_nonneg_right hε hQ0.le
    linarith
  have hdyS : dy ≤ y + S := by
    have h5 : ε * (y + S) ≤ 1 * (y + S) := mul_le_mul_of_nonneg_right hε1 (by linarith)
    linarith
  -- the bounds `A` and `Y`
  have hn3 : (0 : ℝ) < n ^ 3 := pow_pos hn0 3
  have hy1 : y ≤ 9 / 100 * (A * Q) := by
    refine hy.trans ?_
    rw [div_le_iff₀ hn3]
    have h5 : i * Q ≤ A * n ^ 3 / 100 * Q := mul_le_mul_of_nonneg_right hi hQ0.le
    linarith
  have hAQ : A * Q ≤ Y / 2 := by
    have h5 : A * Q ≤ A * (n ^ 2 / 2) := mul_le_mul_of_nonneg_left (hQM.trans hMup) hA
    linarith
  have h2' : 2 * S ≤ 82 / 100 * (A * Q) := by
    have h5 : n ^ 2 / 4 * g ≤ M * g := mul_le_mul_of_nonneg_right hMlow hg.le
    have h6 : A * (n ^ 2 / 4 * g) ≤ A * Q := mul_le_mul_of_nonneg_left (h5.trans hQlow) hA
    linarith
  have haA : 1 + y + dy ≤ A * Q := by linarith
  have hyY : y + dy ≤ Y := by linarith
  exact ⟨⟨hQ0, hx0.le, hxn, hxJ, hy0, hdx0, hdxx, hdy0, hdq0, by linarith, hyY, haA⟩, hdq2⟩

/- ## The potentials at the horizon -/

/-- Lower bound for the threshold of an exponential potential. -/
theorem exp_pot_ge {G lam e0 v H T W Hb : ℝ} (h1 : lam * e0 = T) (h2 : lam ^ 2 * v = W)
    (hW : 0 ≤ W) (hH : H ≤ Hb) (h3 : W * Hb ≤ 1) (h4 : G ≤ Real.exp (T - 1)) :
    G ≤ Real.exp (lam * e0 - lam ^ 2 * v * H) := by
  refine h4.trans (Real.exp_le_exp.mpr ?_)
  rw [h1, h2]
  have h5 := mul_le_mul_of_nonneg_left hH hW
  linarith

/-- Lower bound for the threshold of a potential `2^B / (1 + c)^H`. -/
theorem two_rpow_div_pow_ge {G B c : ℝ} {H : ℕ} (hc : 0 ≤ c) (h1 : (H : ℝ) * c ≤ B / 4)
    (h3 : G ≤ Real.exp (B / 4)) : G ≤ (2 : ℝ) ^ B / (1 + c) ^ H := by
  have hB : 0 ≤ B := by
    have h5 : 0 ≤ (H : ℝ) * c := mul_nonneg (Nat.cast_nonneg H) hc
    linarith
  have hρ : 0 < 1 + c := by linarith
  have hpow : (1 + c) ^ H ≤ Real.exp ((H : ℝ) * c) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hρ.le (by linarith [Real.add_one_le_exp c]) H
  have hl : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (lt_trans (by norm_num : (1 : ℝ) / 2 < 0.6931471803) Real.log_two_gt_d9).le
  have h2 : Real.exp (B / 2) ≤ (2 : ℝ) ^ B := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have h5 := mul_nonneg (sub_nonneg.mpr hl) hB
    linarith
  calc G ≤ Real.exp (B / 4) := h3
    _ ≤ Real.exp (B / 2 - (H : ℝ) * c) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (B / 2) / Real.exp ((H : ℝ) * c) := Real.exp_sub _ _
    _ ≤ (2 : ℝ) ^ B / Real.exp ((H : ℝ) * c) :=
        div_le_div_of_nonneg_right h2 (Real.exp_pos _).le
    _ ≤ (2 : ℝ) ^ B / (1 + c) ^ H :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg (by norm_num) B) (pow_pos hρ H) hpow

/-- The exponent of the compensating factor at the horizon. -/
theorem hor_mul_le {H Hb c B W Qm : ℝ} (hHb : 0 ≤ Hb) (hH : H ≤ Hb / 100) (hc0 : 0 ≤ c)
    (hB : 0 ≤ B) (hQm : 0 < Qm) (hW : W / 8 ≤ Qm) (h : Hb * c ≤ B * W) :
    H * (c / Qm) ≤ B / 4 := by
  rw [← mul_div_assoc, div_le_iff₀ hQm]
  have h1 : H * c ≤ Hb / 100 * c := mul_le_mul_of_nonneg_right hH hc0
  have h2 : B / 4 * (W / 8) ≤ B / 4 * Qm := mul_le_mul_of_nonneg_left hW (by linarith)
  have h3 : 0 ≤ Hb * c := mul_nonneg hHb hc0
  linarith

/- ## The facts for one large `N` -/

/-- The horizon is at most `N^{301/200} / 100`. -/
theorem hor_le {N : ℕ} (hn : (1 : ℝ) ≤ N) (hK : (10000 : ℝ) ≤ (N : ℝ) ^ (1 / 200 : ℝ)) :
    ((hor N : ℕ) : ℝ) ≤ (N : ℝ) ^ (301 / 200 : ℝ) / 100 := by
  have hn0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hn
  have hr : 0 ≤ Real.sqrt (1 / 2000) / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N) := by
    positivity
  have h1 : ((hor N : ℕ) : ℝ)
      ≤ Real.sqrt (1 / 2000) / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N) :=
    Nat.floor_le hr
  have h2 : Real.sqrt (1 / 2000) / 3 ≤ 1 / 100 := by
    have h5 : Real.sqrt (1 / 2000) ≤ 3 / 100 := by
      rw [Real.sqrt_le_iff]; constructor <;> norm_num
    linarith
  have h3 := num_sqrt_log hn hK
  have h4 : (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) ^ (1 / 200 : ℝ) = (N : ℝ) ^ (301 / 200 : ℝ) :=
    rp_mul hn0 (by norm_num)
  calc ((hor N : ℕ) : ℝ)
      ≤ Real.sqrt (1 / 2000) / 3 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log N) := h1
    _ ≤ 1 / 100 * (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) ^ (1 / 200 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hn0.le _)) h3
          (Real.sqrt_nonneg _) (by positivity)
    _ = (N : ℝ) ^ (301 / 200 : ℝ) / 100 := by rw [← h4]; ring

/-- The facts about every index up to the horizon. -/
theorem pt_idx {N : ℕ} (hN : (10000 : ℝ) ≤ N)
    (hK : (10000 : ℝ) ≤ (N : ℝ) ^ (1 / 200 : ℝ))
    (hT : ∀ i ≤ horizon (1 / 2000) N,
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ Qh N i ∧ Qh N i ≤ N.choose 2 ∧
      0 ≤ yh N i ∧ yh N i ≤ 9 * i * Qh N i / (N : ℝ) ^ 3 ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / N.choose 2) ^ 2 ∧
      (1 + yh N i) / Qh N i ≤ 1 / N ∧
      ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j ≤ 1 / 2000 * Real.log N)
    (hE : ∀ i ≤ horizon (1 / 2000) N,
      (N : ℝ) ^ (17 / 20 : ℝ) ≤ eX N i ∧ eX N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * xh N i ∧
      (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i ∧
      eY N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) ∧
      0 ≤ eQ N i ∧ eQ N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i) :
    ∀ i ≤ hor N,
      Pt (N : ℝ) (Qh N i) (xh N i) (yh N i) (eX N i) (eY N i) (eQ N i)
        ((N : ℝ) ^ (-(299 / 200) : ℝ)) ((N : ℝ) ^ (101 / 200 : ℝ)) (2 / (N : ℝ)) ∧
      2 * eQ N i ≤ Qh N i ∧
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ Qh N i := by
  intro i hi
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  obtain ⟨t1, t2, t3, t4, t5, t6, -, -⟩ := hT i hi
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hE i hi
  obtain ⟨p1, p2, p3, p4⟩ := num_pt hn1 hK
  have hH := hor_le hn1 hK
  have hi' : (i : ℝ) ≤ (N : ℝ) ^ (-(299 / 200) : ℝ) * (N : ℝ) ^ 3 / 100 := by
    have e : (N : ℝ) ^ (-(299 / 200) : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) ^ (301 / 200 : ℝ) :=
      rp_mul_nat hn0 3 (by norm_num)
    rw [e]
    exact le_trans (Nat.cast_le.mpr hi) hH
  have hpt := pt_of (n := (N : ℝ)) (M := (N.choose 2 : ℝ)) (g := (N : ℝ) ^ (-(1 / 2000 : ℝ)))
    (ε := (N : ℝ) ^ (-(1 / 20 : ℝ))) (S := (N : ℝ) ^ (9 / 20 : ℝ))
    (A := (N : ℝ) ^ (-(299 / 200) : ℝ)) (Y := (N : ℝ) ^ (101 / 200 : ℝ))
    (by linarith) (Nat.cast_choose_two ℝ N) (Real.rpow_pos_of_pos hn0 _) t1 t2 t3 t4 t5 t6
    ((Real.rpow_nonneg hn0.le _).trans u1) u2 ((Real.rpow_nonneg hn0.le _).trans u3) u4 u5 u6
    p1 (Real.rpow_nonneg hn0.le _) hi' p2 p3 p4
  exact ⟨hpt.1, hpt.2, t1⟩

/-- All fields of `NumGlobal N` for one large `N`. -/
theorem numGlobal_of {N : ℕ} (hN : (10000 : ℝ) ≤ N)
    (hK : (10000 : ℝ) ≤ (N : ℝ) ^ (1 / 200 : ℝ))
    (hT : ∀ i ≤ horizon (1 / 2000) N,
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ Qh N i ∧ Qh N i ≤ N.choose 2 ∧
      0 ≤ yh N i ∧ yh N i ≤ 9 * i * Qh N i / (N : ℝ) ^ 3 ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / N.choose 2) ^ 2 ∧
      (1 + yh N i) / Qh N i ≤ 1 / N ∧
      ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j ≤ 1 / 2000 * Real.log N)
    (hE : ∀ i ≤ horizon (1 / 2000) N,
      (N : ℝ) ^ (17 / 20 : ℝ) ≤ eX N i ∧ eX N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * xh N i ∧
      (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i ∧
      eY N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) ∧
      0 ≤ eQ N i ∧ eQ N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i) :
    NumGlobal N := by
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hpt := pt_idx hN hK hT hE
  have hH := hor_le hn1 hK
  have hM : (N.choose 2 : ℝ) = N * (N - 1) / 2 := Nat.cast_choose_two ℝ N
  have hMlow : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ) := by
    rw [hM]; nlinarith [mul_nonneg hn0.le (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]
  have hg : 0 < (N : ℝ) ^ (-(1 / 2000 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hQmin : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2000 : ℝ)) / 8 ≤ Qmin N := by
    unfold Qmin
    have h5 := mul_le_mul_of_nonneg_right hMlow hg.le
    linarith
  have hQmin0 : 0 < Qmin N := by
    have h5 := mul_pos (pow_pos hn0 2) hg
    linarith
  have hexp := num_exp hn1 hK
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := num_XY hn1 hK
  have hW0 : 0 ≤ (N : ℝ) ^ (-(31 / 20) : ℝ) := Real.rpow_nonneg hn0.le _
  have hHb0 : 0 ≤ (N : ℝ) ^ (301 / 200 : ℝ) := Real.rpow_nonneg hn0.le _
  have hexp' : 40 * (N : ℝ) ^ 2 ≤ Real.exp ((N : ℝ) ^ (1 / 20 : ℝ) - 1) :=
    hexp.trans (Real.exp_le_exp.mpr (by linarith))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hN`
    exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  · -- `nA`
    intro i hi
    obtain ⟨h, h2, -⟩ := hpt i hi
    exact ⟨h.Q0, h.dq0, h2, h.dx0, h.dxx, h.dy0, h.y0⟩
  · -- `nB`
    intro i hi
    obtain ⟨h, -, -⟩ := hpt i hi.le
    exact h.numB (Dmx_nonneg N) (Zmx_nonneg N) (lamX_nonneg N) (lamY_nonneg N)
      (num_B1 hn1 hK) (num_B2 hn1 hK) (num_B3 hn1 hK) (num_B4 hn1 hK) (num_B5 hn1 hK)
  · -- `nC`
    refine ⟨hQmin0, fun i hi => ?_⟩
    obtain ⟨h, h2, h3⟩ := hpt i hi
    show (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) / 2 ≤ Qh N i - eQ N i
    linarith
  · -- `fX`
    have q1' : lamX N * eX N 0 = (N : ℝ) ^ (1 / 20 : ℝ) := by
      rw [eX_zero]; exact q1
    exact exp_pot_ge q1' q2 hW0 hH q5 hexp'
  · -- `fY`
    have q3' : lamY N * eY N 0 = (N : ℝ) ^ (1 / 20 : ℝ) := by
      rw [eY_zero]; exact q3
    exact exp_pot_ge q3' q4 hW0 hH q5 hexp'
  · -- `fD`
    unfold LamD rhoD
    refine two_rpow_div_pow_ge (div_nonneg hn0.le hQmin0.le) ?_ ?_
    · exact hor_mul_le hHb0 hH hn0.le (Dmx_nonneg N) hQmin0 hQmin (num_D hn1)
    · refine hexp.trans (Real.exp_le_exp.mpr ?_)
      have h5 : (N : ℝ) ^ (1 / 40 : ℝ) ≤ (N : ℝ) ^ (51 / 100 : ℝ) := rp_le hn1 (by norm_num)
      unfold Dmx
      linarith
  · -- `fZ`
    unfold LamZ rhoZ
    refine two_rpow_div_pow_ge
      (div_nonneg (mul_nonneg (by norm_num) (Dmx_nonneg N)) hQmin0.le) ?_ ?_
    · exact hor_mul_le hHb0 hH (mul_nonneg (by norm_num) (Dmx_nonneg N)) (Zmx_nonneg N)
        hQmin0 hQmin (num_Z hn1 hK)
    · exact hexp

end NumGlobalAux

/-- **The numerical facts not involving edge sets hold for all large `N`.** -/
theorem numGlobal_eventually : ∀ᶠ N : ℕ in Filter.atTop, NumGlobal N := by
  have e1 : ∀ᶠ N : ℕ in Filter.atTop, (10000 : ℝ) ≤ N :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 10000
  have e2 : ∀ᶠ N : ℕ in Filter.atTop, (10000 : ℝ) ≤ (N : ℝ) ^ (1 / 200 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 10000
  have e3 := traj_facts (γ := 1 / 2000) (by norm_num) (by norm_num)
  have e4 := err_facts
  filter_upwards [e1, e2, e3, e4] with N h1 h2 h3 h4
  exact NumGlobalAux.numGlobal_of h1 h2 h3 h4

end TFP
end E1182

end NumGlobalProofPart

section NumEdgeProofPart

/-
# The numerical facts about edge sets hold for all large `N`

`numEdge_eventually : ∃ A, 1 ≤ A ∧ ∀ᶠ N in atTop, NumEdge A N` (with `A = 1000`).

All auxiliary declarations are kept in the namespace `NumEdgeAux`, so that their names cannot
clash with declarations of other parts. Structure of the proof:

* `sc_*`: explicit inequalities between powers of a real number `n` with `log n ≥ 10000`
  (every power is written as an exponential of `log n`);
* `Scale N`: the elementary facts about the scale `N` that are used (`scale_of_log`);
* `IdxFacts N i`: the facts about the trajectory and the error sequences at the index `i`;
* one-step inequalities with abstract real variables (`abar_*`, `gW_step`, `bstep_le`,
  `var_first`, `eps_u_sq_le`);
* comparison of the normalisation `gW` with the trajectory, `(9/10) Q̂_i ≤ M gW_i ≤ Q̂_i` for
  `i ≤ hor N` (`gW_bounds`), by induction with the partial sums `dSum` of `abar - a`;
* one lemma per field of `NumEdge` (`gW_pos`, `numEdge_nS`, `numEdge_nW`, `CWn_nonneg`,
  `numEdge_f2a`, `numEdge_f2b`), collected in `numEdge_core`.
-/

namespace E1182
namespace TFP

namespace NumEdgeAux

/- ## Explicit inequalities for large `n` -/

/-- `K * exp a ≤ exp b` when `K ≤ (b - a) + 1`. -/
theorem mul_exp_le_exp {a b K : ℝ} (hK : K ≤ b - a + 1) : K * Real.exp a ≤ Real.exp b := by
  have h1 := Real.add_one_le_exp (b - a)
  have h2 : Real.exp b = Real.exp (b - a) * Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem sc_eps {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    n ^ (-(1 / 20 : ℝ)) ≤ 1 / 100 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL
  rw [← Real.exp_mul]
  have h := mul_exp_le_exp (a := L * -(1 / 20)) (b := 0) (K := 100) (by linarith)
  rw [Real.exp_zero] at h
  linarith

theorem sc_epsL {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    n ^ (-(1 / 20 : ℝ)) * (Real.log n / 25 + 1) ≤ 1 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL ⊢
  rw [← Real.exp_mul]
  have h := mul_exp_le_exp (a := L * -(1 / 20)) (b := 0) (K := L / 25 + 1) (by linarith)
  rw [Real.exp_zero] at h
  linarith

theorem sc_K {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    1 + 2 * n ^ (51 / 100 : ℝ) + 2 * n ^ (9 / 10 : ℝ) * n ^ (1 / 40 : ℝ)
      ≤ 3 * n ^ (37 / 40 : ℝ) := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL
  simp only [← Real.exp_mul]
  have h1 : Real.exp (L * (9 / 10)) * Real.exp (L * (1 / 40)) = Real.exp (L * (37 / 40)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : (1 : ℝ) ≤ Real.exp (L * (51 / 100)) := Real.one_le_exp (by linarith)
  have h3 := mul_exp_le_exp (a := L * (51 / 100)) (b := L * (37 / 40)) (K := 3) (by linarith)
  have h4 : 2 * Real.exp (L * (9 / 10)) * Real.exp (L * (1 / 40))
      = 2 * Real.exp (L * (37 / 40)) := by
    rw [mul_assoc, h1]
  linarith

theorem sc_V1 {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    n ^ (37 / 40 : ℝ) ≤ n ^ (-(107 / 100 : ℝ)) * n ^ 2 * (n ^ (-(1 / 2000 : ℝ))) ^ 3 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL
  simp only [← Real.exp_mul]
  have e : Real.exp (L * -(107 / 100)) * Real.exp L ^ 2 * Real.exp (L * -(1 / 2000)) ^ 3
      = Real.exp (L * (1857 / 2000)) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

theorem sc_V2a {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    8 * (n ^ (-(1 / 20 : ℝ)) * (n ^ (9 / 20 : ℝ)) ^ 2)
      ≤ (n ^ (-(1 / 2000 : ℝ))) ^ 4 * n ^ (-(304 / 100 : ℝ)) * n ^ 4 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL
  simp only [← Real.exp_mul]
  have e1 : Real.exp (L * -(1 / 20)) * Real.exp (L * (9 / 20)) ^ 2
      = Real.exp (L * (17 / 20)) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e2 : Real.exp (L * -(1 / 2000)) ^ 4 * Real.exp (L * -(304 / 100)) * Real.exp L ^ 4
      = Real.exp (L * (479 / 500)) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  rw [e1, e2]
  exact mul_exp_le_exp (by linarith)

theorem sc_V2b {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    9 / 1000 * Real.log n * n ^ (-(1 / 20 : ℝ))
      ≤ (n ^ (-(1 / 2000 : ℝ))) ^ 2 * n ^ (-(304 / 100 : ℝ)) * n ^ 3 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL ⊢
  simp only [← Real.exp_mul]
  have e2 : Real.exp (L * -(1 / 2000)) ^ 2 * Real.exp (L * -(304 / 100)) * Real.exp L ^ 3
      = Real.exp (L * -(41 / 1000)) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  rw [e2]
  exact mul_exp_le_exp (by linarith)

theorem sc_F2 {n : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n) :
    Real.exp (Real.log n / 100)
        * (144 * n ^ (-(107 / 100 : ℝ)) + 400 * n ^ 2 * n ^ (-(304 / 100 : ℝ)))
        * (n * Real.log n / 1100) ≤ 1 / 4 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [Real.log_exp] at hL ⊢
  simp only [← Real.exp_mul]
  have e1 : Real.exp (L / 100) * Real.exp (L * -(107 / 100)) * Real.exp L
      = Real.exp (L * -(6 / 100)) := by
    simp only [← Real.exp_add]
    congr 1; ring
  have e2 : Real.exp (L / 100) * (Real.exp L ^ 2 * Real.exp (L * -(304 / 100))) * Real.exp L
      = Real.exp (L * -(3 / 100)) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have h1 : Real.exp (L * -(6 / 100)) ≤ Real.exp (L * -(3 / 100)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : 2 * L * Real.exp (L * -(3 / 100)) ≤ 1 := by
    have q := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ L * (3 / 100))
    have q2 : 2 * L ≤ Real.exp (L * (3 / 100)) := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by linarith : (0 : ℝ) ≤ L - 10000)]
    have q3 : Real.exp (L * (3 / 100)) * Real.exp (L * -(3 / 100)) = 1 := by
      rw [← Real.exp_add]
      have e0 : L * (3 / 100) + L * -(3 / 100) = 0 := by ring
      rw [e0, Real.exp_zero]
    have q4 := mul_le_mul_of_nonneg_right q2 (Real.exp_pos (L * -(3 / 100))).le
    linarith
  have e3 : Real.exp (L / 100)
        * (144 * Real.exp (L * -(107 / 100)) + 400 * Real.exp L ^ 2 * Real.exp (L * -(304 / 100)))
        * (Real.exp L * L / 1100)
      = L / 1100 * (144 * (Real.exp (L / 100) * Real.exp (L * -(107 / 100)) * Real.exp L)
        + 400 * (Real.exp (L / 100) * (Real.exp L ^ 2 * Real.exp (L * -(304 / 100)))
          * Real.exp L)) := by ring
  rw [e3, e1, e2]
  have h3 : L / 1100 * (144 * Real.exp (L * -(6 / 100)) + 400 * Real.exp (L * -(3 / 100)))
      ≤ L / 1100 * (544 * Real.exp (L * -(3 / 100))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- The facts about `T = (√γ / 3) n^{3/2} √(log n)`, the real number whose floor is the
horizon. -/
theorem sc_T {n T : ℝ} (hn : 0 < n) (hL : 10000 ≤ Real.log n)
    (hT : T = Real.sqrt (1 / 2000) / 3 * n ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) :
    4 ≤ T ∧
    n ^ (9 / 20 : ℝ) * n ≤ 3 / 4 * T * n ^ (-(1 / 2000 : ℝ)) ∧
    (∀ k m : ℝ, 0 ≤ k → 1000 * k * Real.sqrt (n * Real.log n) ≤ m → 8800 * k * T ≤ n * m) ∧
    (∀ k m : ℝ, 0 ≤ k → 1000 * k * Real.sqrt (n * Real.log n) ≤ m →
      5 * k * n ^ 2 * Real.log n ≤ 3 / 4 * T * m) := by
  obtain ⟨L, rfl⟩ : ∃ L, n = Real.exp L := ⟨Real.log n, (Real.exp_log hn).symm⟩
  simp only [Real.log_exp, ← Real.exp_mul] at hL hT ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 / 2000) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt L := ⟨_, rfl⟩
  rw [← hs, ← hr] at hT
  have hL0 : 0 ≤ L := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = L := by rw [hr]; exact Real.sq_sqrt hL0
  have hslo : 1 / 50 ≤ s := by
    rw [hs]; exact (Real.le_sqrt' (by norm_num)).mpr (by norm_num)
  have hshi : s ≤ 1 / 40 := by
    rw [hs, Real.sqrt_le_iff]; constructor <;> norm_num
  have hr1 : 1 ≤ r := by
    rw [hr]; exact (Real.le_sqrt' one_pos).mpr (by rw [one_pow]; linarith)
  have hsqrt : Real.sqrt (Real.exp L * L) = Real.exp (L * (1 / 2)) * r := by
    rw [Real.sqrt_mul (Real.exp_pos L).le, Real.sqrt_eq_rpow (Real.exp L), ← Real.exp_mul, hr]
  have hW : Real.exp (L * (3 / 2)) = Real.exp L * Real.exp (L * (1 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hW2 : Real.exp (L * (1 / 2)) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE : 15001 ≤ Real.exp (L * (3 / 2)) := by
    linarith [Real.add_one_le_exp (L * (3 / 2))]
  have hT4 : 4 ≤ T := by
    have h1 : 1 / 50 / 3 * 15001 * 1 ≤ s / 3 * Real.exp (L * (3 / 2)) * r := by
      refine mul_le_mul ?_ hr1 (by norm_num)
        (mul_nonneg (div_nonneg hs0 (by norm_num)) (Real.exp_pos _).le)
      refine mul_le_mul ?_ hE (by norm_num) (div_nonneg hs0 (by norm_num))
      linarith
    rw [hT]; linarith
  refine ⟨hT4, ?_, ?_, ?_⟩
  · have e1 : Real.exp (L * (9 / 20)) * Real.exp L = Real.exp (L * (29 / 20)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (L * (3 / 2)) * Real.exp (L * -(1 / 2000))
        = Real.exp (L * (2999 / 2000)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 := mul_exp_le_exp (a := L * (29 / 20)) (b := L * (2999 / 2000)) (K := 200)
      (by linarith)
    have hsr : 1 / 200 ≤ 3 / 4 * (s / 3) * r := by
      linarith [mul_le_mul hslo hr1 (by norm_num) hs0]
    have h3 : 1 / 200 * Real.exp (L * (2999 / 2000))
        ≤ 3 / 4 * (s / 3) * r * Real.exp (L * (2999 / 2000)) :=
      mul_le_mul_of_nonneg_right hsr (Real.exp_pos _).le
    have e3 : 3 / 4 * (s / 3 * Real.exp (L * (3 / 2)) * r) * Real.exp (L * -(1 / 2000))
        = 3 / 4 * (s / 3) * r * (Real.exp (L * (3 / 2)) * Real.exp (L * -(1 / 2000))) := by
      ring
    rw [e1, hT, e3, e2]
    linarith
  · intro k m hk hm
    rw [hsqrt] at hm
    have h1 : Real.exp L * (1000 * k * (Real.exp (L * (1 / 2)) * r)) ≤ Real.exp L * m :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos L).le
    have h2 : 0 ≤ Real.exp L * (k * (Real.exp (L * (1 / 2)) * r)) :=
      mul_nonneg (Real.exp_pos L).le (mul_nonneg hk (mul_nonneg (Real.exp_pos _).le hr0))
    have h3 : 8800 * (s / 3) * (Real.exp L * (k * (Real.exp (L * (1 / 2)) * r)))
        ≤ 1000 * (Real.exp L * (k * (Real.exp (L * (1 / 2)) * r))) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    rw [hT, hW]
    linarith
  · intro k m hk hm
    rw [hsqrt] at hm
    have hT0 : 0 ≤ 3 / 4 * T := by linarith
    have h1 : 3 / 4 * T * (1000 * k * (Real.exp (L * (1 / 2)) * r)) ≤ 3 / 4 * T * m :=
      mul_le_mul_of_nonneg_left hm hT0
    have e : 3 / 4 * T * (1000 * k * (Real.exp (L * (1 / 2)) * r))
        = 250 * s * (k * Real.exp L * Real.exp (L * (1 / 2)) ^ 2 * r ^ 2) := by
      rw [hT, hW]; ring
    rw [e, hW2, hr2] at h1
    have h2 : 0 ≤ k * Real.exp L * Real.exp L * L :=
      mul_nonneg (mul_nonneg (mul_nonneg hk (Real.exp_pos L).le) (Real.exp_pos L).le) hL0
    have h3 : 5 * (k * Real.exp L * Real.exp L * L)
        ≤ 250 * s * (k * Real.exp L * Real.exp L * L) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    linarith

/- ## The scale -/

/-- Elementary facts about the scale `N` (they hold when `log N ≥ 10000`). -/
structure Scale (N : ℕ) : Prop where
  n64 : (64 : ℝ) ≤ N
  L0 : 10000 ≤ Real.log N
  Mlo : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ)
  Mhi : (N.choose 2 : ℝ) ≤ (N : ℝ) ^ 2 / 2
  eps0 : 0 < (N : ℝ) ^ (-(1 / 20 : ℝ))
  eps : (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 / 100
  epsL : (N : ℝ) ^ (-(1 / 20 : ℝ)) * (Real.log N / 25 + 1) ≤ 1
  S1 : 1 ≤ (N : ℝ) ^ (9 / 20 : ℝ)
  gi0 : 0 < (N : ℝ) ^ (-(1 / 2000 : ℝ))
  H1 : 1 ≤ (hor N : ℝ)
  cH : 40 * (N : ℝ) ^ (9 / 20 : ℝ) * (hor N : ℝ)
    ≤ (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ))
  Hsq : (hor N : ℝ) ^ 2 ≤ 1 / 2000 / 9 * (N : ℝ) ^ 3 * Real.log N
  SgH : (N : ℝ) ^ (9 / 20 : ℝ) * N ≤ (hor N : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ))
  K : 1 + 2 * Dmx N + 2 * (N : ℝ) ^ (9 / 10 : ℝ) * Zmx N ≤ 3 * (N : ℝ) ^ (37 / 40 : ℝ)
  V1 : (N : ℝ) ^ (37 / 40 : ℝ)
    ≤ (N : ℝ) ^ (-(107 / 100 : ℝ)) * (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 3
  V2a : 8 * ((N : ℝ) ^ (-(1 / 20 : ℝ)) * ((N : ℝ) ^ (9 / 20 : ℝ)) ^ 2)
    ≤ ((N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 4 * (N : ℝ) ^ (-(304 / 100 : ℝ)) * (N : ℝ) ^ 4
  V2b : 9 / 1000 * Real.log N * (N : ℝ) ^ (-(1 / 20 : ℝ))
    ≤ ((N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)) * (N : ℝ) ^ 3
  F2 : Real.exp (B0 N)
      * (144 * (N : ℝ) ^ (-(107 / 100 : ℝ)) + 400 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)))
      * ((N : ℝ) * Real.log N / 1100) ≤ 1 / 4
  f2a : ∀ (k : ℕ) (m : ℝ), 1000 * (k : ℝ) * Real.sqrt (N * Real.log N) ≤ m →
    8800 * (k : ℝ) * (hor N : ℝ) ≤ N * m
  f2b : ∀ (k : ℕ) (m : ℝ), 1000 * (k : ℝ) * Real.sqrt (N * Real.log N) ≤ m →
    5 * (k : ℝ) * (N : ℝ) ^ 2 * Real.log N ≤ (hor N : ℝ) * m

theorem scale_of_log {N : ℕ} (hL : 10000 ≤ Real.log N) : Scale N := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, Real.log_zero] at hL
    norm_num at hL
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hn1 : (10001 : ℝ) ≤ N := by
    have h := Real.add_one_le_exp (Real.log N)
    rw [Real.exp_log hn] at h
    linarith
  have hM1 : (N.choose 2 : ℝ) = N * (N - 1) / 2 := Nat.cast_choose_two ℝ N
  have hMlo : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ) := by
    rw [hM1]; linarith [mul_nonneg hn.le (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]
  have hMhi : (N.choose 2 : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by
    rw [hM1]; linarith
  have hMpos : (0 : ℝ) < (N.choose 2 : ℝ) := lt_of_lt_of_le (by positivity) hMlo
  obtain ⟨T, hT⟩ : ∃ T, T = Real.sqrt (1 / 2000) / 3 * (N : ℝ) ^ (3 / 2 : ℝ)
      * Real.sqrt (Real.log N) := ⟨_, rfl⟩
  obtain ⟨hT4, hTS, hTa, hTb⟩ := sc_T hn hL hT
  have hHle : (hor N : ℝ) ≤ T := by
    rw [hT]
    unfold hor horizon
    exact Nat.floor_le (by positivity)
  have hHgt : T < (hor N : ℝ) + 1 := by
    rw [hT]
    unfold hor horizon
    exact Nat.lt_floor_add_one _
  have hH34 : 3 / 4 * T ≤ (hor N : ℝ) := by linarith
  have hgi0 : 0 < (N : ℝ) ^ (-(1 / 2000 : ℝ)) := Real.rpow_pos_of_pos hn _
  have hg : 0 < (N : ℝ) ^ (1 / 2000 : ℝ) := Real.rpow_pos_of_pos hn _
  have hcH : 40 * (N : ℝ) ^ (9 / 20 : ℝ) * (hor N : ℝ)
      ≤ (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) := by
    have h := err_c0 (N := N) (by linarith) (by linarith)
    have e : 40 * (N : ℝ) ^ (9 / 20 : ℝ) * ((N : ℝ) ^ (1 / 2000 : ℝ) / (N.choose 2 : ℝ))
          * (hor N : ℝ)
        = 40 * (N : ℝ) ^ (9 / 20 : ℝ) * (hor N : ℝ) * (N : ℝ) ^ (1 / 2000 : ℝ)
          / (N.choose 2 : ℝ) := by ring
    have h' : 40 * (N : ℝ) ^ (9 / 20 : ℝ) * (hor N : ℝ) * (N : ℝ) ^ (1 / 2000 : ℝ)
        / (N.choose 2 : ℝ) ≤ 1 := by
      rw [← e]; exact h
    rw [div_le_one hMpos] at h'
    rw [Real.rpow_neg hn.le, ← div_eq_mul_inv, le_div_iff₀ hg]
    exact h'
  exact
    { n64 := by linarith
      L0 := hL
      Mlo := hMlo
      Mhi := hMhi
      eps0 := Real.rpow_pos_of_pos hn _
      eps := sc_eps hn hL
      epsL := sc_epsL hn hL
      S1 := Real.one_le_rpow (by linarith) (by norm_num)
      gi0 := hgi0
      H1 := by linarith
      cH := hcH
      Hsq := horizon_sq_le (γ := 1 / 2000) (by norm_num) N
      SgH := le_trans hTS (mul_le_mul_of_nonneg_right hH34 hgi0.le)
      K := sc_K hn hL
      V1 := sc_V1 hn hL
      V2a := sc_V2a hn hL
      V2b := sc_V2b hn hL
      F2 := sc_F2 hn hL
      f2a := by
        intro k m hm
        have h1 := hTa (k : ℝ) m (Nat.cast_nonneg k) hm
        have h2 : 8800 * (k : ℝ) * (hor N : ℝ) ≤ 8800 * (k : ℝ) * T :=
          mul_le_mul_of_nonneg_left hHle (by positivity)
        linarith
      f2b := by
        intro k m hm
        have h1 := hTb (k : ℝ) m (Nat.cast_nonneg k) hm
        have hm0 : 0 ≤ m := le_trans (by positivity) hm
        have h2 : 3 / 4 * T * m ≤ (hor N : ℝ) * m := mul_le_mul_of_nonneg_right hH34 hm0
        linarith }

/- ## One-step inequalities with abstract variables -/

/-- `a ≤ abar`. -/
theorem abar_ge_a {Q y eY eQ ε : ℝ} (hQ : 0 < Q) (hy : 0 ≤ y) (hY0 : 0 ≤ eY)
    (hQ0 : 0 ≤ eQ) (hQe : eQ ≤ ε * Q) (hε : ε ≤ 1 / 2) :
    (1 + y) / Q ≤ (1 + y + eY) / (Q - eQ) := by
  have hεQ : ε * Q ≤ 1 / 2 * Q := mul_le_mul_of_nonneg_right hε hQ.le
  have hd : 0 < Q - eQ := by linarith
  rw [div_le_div_iff₀ hQ hd]
  have h1 : 0 ≤ (1 + y) * eQ := mul_nonneg (by linarith) hQ0
  have h2 : 0 ≤ eY * Q := mul_nonneg hY0 hQ.le
  linarith

/-- `abar ≤ 1`. -/
theorem abar_le_one {Q y eY eQ ε S : ℝ} (hQ : 0 < Q) (hy : 0 ≤ y)
    (hY : eY ≤ ε * (y + S)) (hQe : eQ ≤ ε * Q) (hε : ε ≤ 1 / 100) (hS : 0 ≤ S)
    (hyQ : 1 + y ≤ Q / 64) (hSQ : S ≤ Q / 40) :
    (1 + y + eY) / (Q - eQ) ≤ 1 := by
  have h1 : ε * (y + S) ≤ 1 / 100 * (y + S) := mul_le_mul_of_nonneg_right hε (by linarith)
  have h2 : ε * Q ≤ 1 / 100 * Q := mul_le_mul_of_nonneg_right hε hQ.le
  have hd : 0 < Q - eQ := by linarith
  rw [div_le_one hd]
  linarith

/-- `abar - a ≤ ε (4 a + 2 S / Q)`. -/
theorem abar_sub_a_le {Q y eY eQ ε S : ℝ} (hQ : 0 < Q) (hy : 0 ≤ y)
    (hY : eY ≤ ε * (y + S)) (hQe : eQ ≤ ε * Q) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hS : 0 ≤ S) :
    (1 + y + eY) / (Q - eQ) - (1 + y) / Q ≤ ε * (4 * ((1 + y) / Q) + 2 * (S / Q)) := by
  have hεQ : ε * Q ≤ 1 / 2 * Q := mul_le_mul_of_nonneg_right hε hQ.le
  have hd : 0 < Q - eQ := by linarith
  have hW0 : 0 ≤ 4 * (1 + y) + 2 * S := by linarith
  obtain ⟨X, hX⟩ : ∃ X, X = (1 + y) + ε * (4 * (1 + y) + 2 * S) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    have h := mul_nonneg hε0 hW0
    rw [hX]; linarith
  have e : (1 + y) / Q + ε * (4 * ((1 + y) / Q) + 2 * (S / Q)) = X / Q := by
    rw [hX]; ring
  have key : (1 + y + eY) / (Q - eQ) ≤ X / Q := by
    rw [div_le_div_iff₀ hd hQ]
    have h1 : X * (Q * (1 - ε)) ≤ X * (Q - eQ) :=
      mul_le_mul_of_nonneg_left (by linarith) hX0
    have h4 : ε * (1 / 2 * (4 * (1 + y) + 2 * S)) ≤ ε * ((1 - ε) * (4 * (1 + y) + 2 * S)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hW0) hε0
    have h2 : 1 + y + eY ≤ X * (1 - ε) := by
      rw [hX]; linarith
    have h3 : (1 + y + eY) * Q ≤ X * (1 - ε) * Q := mul_le_mul_of_nonneg_right h2 hQ.le
    linarith
  linarith

/-- One step of the comparison of `gW` with the trajectory. Here `G = M gW_i`, `a = a_i`,
`b = abar_i` and `D = ∑_{j<i} (abar_j - a_j)`. -/
theorem gW_step {G Q a b D : ℝ} (hlo : Q * (1 - 2 * D) ≤ G) (hhi : G ≤ Q) (hQ : 0 ≤ Q)
    (hD : 0 ≤ D) (hab : a ≤ b) (hb : b ≤ 1) (ha : a ≤ 1 / 2) :
    Q * (1 - a) * (1 - 2 * (D + (b - a))) ≤ G * (1 - b) ∧ G * (1 - b) ≤ Q * (1 - a) := by
  have hb' : 0 ≤ 1 - b := by linarith
  constructor
  · have h1 : Q * (1 - 2 * D) * (1 - b) ≤ G * (1 - b) := mul_le_mul_of_nonneg_right hlo hb'
    have h2 : 0 ≤ Q * ((b - a) * (1 + 2 * D - 2 * a)) :=
      mul_nonneg hQ (mul_nonneg (by linarith) (by linarith))
    linarith
  · have h1 : G * (1 - b) ≤ Q * (1 - b) := mul_le_mul_of_nonneg_right hhi hb'
    have h2 : Q * (1 - b) ≤ Q * (1 - a) := mul_le_mul_of_nonneg_left (by linarith) hQ
    linarith

/-- `abar (abar - alow) ≤ 18 ε u²` with `u = (1 + ŷ + S) / Q̂`. -/
theorem abar_alow_le {Q y eY eQ ε S : ℝ} (hQ : 0 < Q) (hy : 0 ≤ y) (hY0 : 0 ≤ eY)
    (hY : eY ≤ ε * (y + S)) (hQ0 : 0 ≤ eQ) (hQe : eQ ≤ ε * Q) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hS : 0 ≤ S) :
    (1 + y + eY) / (Q - eQ)
        * ((1 + y + eY) / (Q - eQ) - (1 + max (y - eY) 0) / (Q + eQ))
      ≤ 18 * ε * ((1 + y + S) / Q) ^ 2 := by
  have hεQ : ε * Q ≤ 1 / 2 * Q := mul_le_mul_of_nonneg_right hε hQ.le
  have hd1 : 0 < Q - eQ := by linarith
  have hd2 : 0 < Q + eQ := by linarith
  have hw : 0 ≤ 1 + y + S := by linarith
  have hεw : ε * (y + S) ≤ 1 / 2 * (y + S) := mul_le_mul_of_nonneg_right hε (by linarith)
  obtain ⟨u, hu⟩ : ∃ u, u = (1 + y + S) / Q := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg hw hQ.le
  rw [← hu]
  -- `abar ≤ 3 u`
  have h1 : (1 + y + eY) / (Q - eQ) ≤ 3 * u := by
    rw [hu, ← mul_div_assoc, div_le_div_iff₀ hd1 hQ]
    have a1 : (1 + y + eY) * Q ≤ 3 / 2 * (1 + y + S) * Q :=
      mul_le_mul_of_nonneg_right (by linarith) hQ.le
    have a2 : 3 * (1 + y + S) * (Q / 2) ≤ 3 * (1 + y + S) * (Q - eQ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have h0 : 0 ≤ (1 + y + eY) / (Q - eQ) := div_nonneg (by linarith) hd1.le
  -- `alow` from below
  have h2 : (1 + y - eY) / (Q + eQ) ≤ (1 + max (y - eY) 0) / (Q + eQ) :=
    div_le_div_of_nonneg_right (by linarith [le_max_left (y - eY) 0]) hd2.le
  -- `abar - alow ≤ 6 ε u`
  have h3 : (1 + y + eY) / (Q - eQ) - (1 + y - eY) / (Q + eQ) ≤ 6 * ε * u := by
    rw [div_sub_div _ _ hd1.ne' hd2.ne', hu, ← mul_div_assoc,
      div_le_div_iff₀ (mul_pos hd1 hd2) hQ]
    have b1 : (1 + y + eY) * (Q + eQ) - (Q - eQ) * (1 + y - eY)
        = 2 * eY * Q + 2 * (1 + y) * eQ := by ring
    have b2 : eY * Q ≤ ε * (y + S) * Q := mul_le_mul_of_nonneg_right hY hQ.le
    have b3 : (1 + y) * eQ ≤ (1 + y) * (ε * Q) := mul_le_mul_of_nonneg_left hQe (by linarith)
    have b0 : 0 ≤ ε * Q * (1 + S) := mul_nonneg (mul_nonneg hε0 hQ.le) (by linarith)
    have b4 : 2 * eY * Q + 2 * (1 + y) * eQ ≤ 4 * (ε * Q) * (1 + y + S) := by linarith
    have b5 : 3 / 4 * Q ^ 2 ≤ (Q - eQ) * (Q + eQ) := by
      linarith [mul_nonneg hQ0 (by linarith : 0 ≤ 1 / 2 * Q - eQ),
        mul_nonneg hQ.le (by linarith : 0 ≤ 1 / 2 * Q - eQ)]
    have b6 : (2 * eY * Q + 2 * (1 + y) * eQ) * Q ≤ 4 * (ε * Q) * (1 + y + S) * Q :=
      mul_le_mul_of_nonneg_right b4 hQ.le
    have b7 : 6 * ε * (1 + y + S) * (3 / 4 * Q ^ 2)
        ≤ 6 * ε * (1 + y + S) * ((Q - eQ) * (Q + eQ)) :=
      mul_le_mul_of_nonneg_left b5 (mul_nonneg (mul_nonneg (by norm_num) hε0) hw)
    have b8 : 0 ≤ ε * (1 + y + S) * Q ^ 2 := mul_nonneg (mul_nonneg hε0 hw) (sq_nonneg Q)
    rw [b1]
    linarith
  have h4 : (1 + y + eY) / (Q - eQ) - (1 + max (y - eY) 0) / (Q + eQ) ≤ 6 * ε * u := by
    linarith
  calc (1 + y + eY) / (Q - eQ)
        * ((1 + y + eY) / (Q - eQ) - (1 + max (y - eY) 0) / (Q + eQ))
      ≤ (1 + y + eY) / (Q - eQ) * (6 * ε * u) := mul_le_mul_of_nonneg_left h4 h0
    _ ≤ 3 * u * (6 * ε * u) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg (by norm_num) hε0) hu0)
    _ = 18 * ε * u ^ 2 := by ring

/-- The bound for the largest increment in the Bennett step:
`(1 + ŷ + eY) / gW_{i+1} ≤ 11 H / n`. -/
theorem bstep_le {Q y eY G n M H ε S gi : ℝ} (hQ : 0 < Q) (hM : 0 < M) (hn : 0 < n)
    (hH : 0 < H) (hG0 : 0 < G) (hG : 4 / 5 * Q ≤ G * M) (hy0 : 0 ≤ y)
    (hy : y ≤ 9 * H * Q / n ^ 3) (hY : eY ≤ ε * (y + S)) (hε : ε ≤ 1 / 100) (hS1 : 1 ≤ S)
    (hM2 : M ≤ n ^ 2 / 2) (hQlo : M * gi ≤ Q) (hsc : S * n ≤ H * gi) :
    (1 + y + eY) / G ≤ 11 * H / n := by
  rw [div_le_div_iff₀ hG0 hn]
  have h1 : eY ≤ 1 / 100 * (y + S) :=
    le_trans hY (mul_le_mul_of_nonneg_right hε (by linarith))
  have h2 : S * n * M ≤ H * Q := by
    calc S * n * M ≤ H * gi * M := mul_le_mul_of_nonneg_right hsc hM.le
      _ = H * (M * gi) := by ring
      _ ≤ H * Q := mul_le_mul_of_nonneg_left hQlo hH.le
  have h3 : y * n ^ 3 ≤ 9 * H * Q := by
    rwa [le_div_iff₀ (pow_pos hn 3)] at hy
  have h4 : y * n * M ≤ y * n * (n ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hM2 (mul_nonneg hy0 hn.le)
  have h5 : 0 ≤ H * Q := mul_nonneg hH.le hQ.le
  have h6 : 11 * H * (4 / 5 * Q) ≤ 11 * H * (G * M) :=
    mul_le_mul_of_nonneg_left hG (by linarith)
  have h7 : (1 + y + eY) * n * M ≤ (2 * S + 101 / 100 * y) * n * M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hn.le) hM.le
  have key : (1 + y + eY) * n * M ≤ 11 * H * G * M := by linarith
  exact le_of_mul_le_mul_right key hM

/-- The first term of the variance bound. Here `K = 1 + 2 Dmx + 2 ΔW Zmx`, `p1 = n^{37/40}`,
`p2 = n^{-107/100}` and `gi = n^{-1/2000}`. -/
theorem var_first {m K G M n gi p1 p2 : ℝ} (hm : 0 ≤ m) (hK : K ≤ 3 * p1) (hp1 : 0 ≤ p1)
    (hG : 4 / 5 * gi ≤ G) (hgi : 0 < gi) (hMlo : n ^ 2 / 4 ≤ M) (hn : 0 < n)
    (hV1 : p1 ≤ p2 * n ^ 2 * gi ^ 3) (hp2 : 0 ≤ p2) :
    3 * m * K / (M * gi / 2 * G ^ 2) ≤ 144 * m * p2 := by
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hMlo
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hG
  have hG2 : (4 / 5 * gi) ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (by positivity) hG 2
  have hden : 0 < M * gi / 2 * G ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have h0 : n ^ 2 / 4 * gi / 2 ≤ M * gi / 2 := by
    have h := mul_le_mul_of_nonneg_right hMlo hgi.le
    linarith
  have h1 : n ^ 2 / 4 * gi / 2 * (4 / 5 * gi) ^ 2 ≤ M * gi / 2 * G ^ 2 :=
    mul_le_mul h0 hG2 (by positivity) (by positivity)
  have h2 : m * K ≤ m * (3 * p1) := mul_le_mul_of_nonneg_left hK hm
  have h3 : m * p1 ≤ m * (p2 * n ^ 2 * gi ^ 3) := mul_le_mul_of_nonneg_left hV1 hm
  have h4 : 144 * m * p2 * (n ^ 2 / 4 * gi / 2 * (4 / 5 * gi) ^ 2)
      ≤ 144 * m * p2 * (M * gi / 2 * G ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (by norm_num) hm) hp2)
  have h5 : 0 ≤ m * p1 := mul_nonneg hm hp1
  linarith

/-- `ε u² ≤ 17 gi² p₃` for `u = (1 + ŷ + S) / Q̂`, where `t1 = 8 S / (n² gi)` and
`t2 = 9 H / n³`. -/
theorem eps_u_sq_le {u t1 t2 Q y S M n H gi ε p3 L : ℝ}
    (hQ : 0 < Q) (hu0 : 0 ≤ u) (ht10 : 0 ≤ t1)
    (hu : u * Q = 1 + y + S) (hy : y * n ^ 3 ≤ 9 * H * Q) (hS1 : 1 ≤ S)
    (hQlo : M * gi ≤ Q) (hgi : 0 < gi) (hMlo : n ^ 2 / 4 ≤ M) (hn : 0 < n)
    (hε0 : 0 ≤ ε) (ht1 : t1 * (n ^ 2 * gi) = 8 * S) (ht2 : t2 * n ^ 3 = 9 * H)
    (hHsq : H ^ 2 ≤ 1 / 2000 / 9 * n ^ 3 * L)
    (hV2a : 8 * (ε * S ^ 2) ≤ gi ^ 4 * p3 * n ^ 4)
    (hV2b : 9 / 1000 * L * ε ≤ gi ^ 2 * p3 * n ^ 3) :
    ε * u ^ 2 ≤ 17 * gi ^ 2 * p3 := by
  have hn3 : 0 < n ^ 3 := pow_pos hn 3
  -- `u ≤ t1 + t2`
  have h1 : y ≤ t2 * Q := by
    have h : y * n ^ 3 ≤ t2 * Q * n ^ 3 := by
      have e : t2 * Q * n ^ 3 = t2 * n ^ 3 * Q := by ring
      rw [e, ht2]; exact hy
    exact le_of_mul_le_mul_right h hn3
  have h2 : 2 * S ≤ t1 * Q := by
    have a1 : n ^ 2 / 4 * gi ≤ Q := le_trans (mul_le_mul_of_nonneg_right hMlo hgi.le) hQlo
    have a2 : t1 * (n ^ 2 / 4 * gi) ≤ t1 * Q := mul_le_mul_of_nonneg_left a1 ht10
    have a3 : t1 * (n ^ 2 / 4 * gi) = 2 * S := by
      have e : t1 * (n ^ 2 / 4 * gi) = t1 * (n ^ 2 * gi) / 4 := by ring
      rw [e, ht1]; ring
    linarith
  have h3 : u ≤ t1 + t2 := by
    have h : u * Q ≤ (t1 + t2) * Q := by rw [hu]; linarith
    exact le_of_mul_le_mul_right h hQ
  -- squares
  have h4 : u ^ 2 ≤ 2 * t1 ^ 2 + 2 * t2 ^ 2 := by
    have h := pow_le_pow_left₀ hu0 h3 2
    linarith [sq_nonneg (t1 - t2)]
  have h5 : ε * t1 ^ 2 ≤ 8 * gi ^ 2 * p3 := by
    have a : ε * t1 ^ 2 * (n ^ 4 * gi ^ 2) ≤ 8 * gi ^ 2 * p3 * (n ^ 4 * gi ^ 2) := by
      have e : ε * t1 ^ 2 * (n ^ 4 * gi ^ 2) = ε * (t1 * (n ^ 2 * gi)) ^ 2 := by ring
      rw [e, ht1]
      linarith
    exact le_of_mul_le_mul_right a (by positivity)
  have h6 : ε * t2 ^ 2 ≤ 1 / 2 * (gi ^ 2 * p3) := by
    have a : ε * t2 ^ 2 * n ^ 6 ≤ 1 / 2 * (gi ^ 2 * p3) * n ^ 6 := by
      have e : ε * t2 ^ 2 * n ^ 6 = ε * (t2 * n ^ 3) ^ 2 := by ring
      rw [e, ht2]
      have a1 : ε * H ^ 2 ≤ ε * (1 / 2000 / 9 * n ^ 3 * L) :=
        mul_le_mul_of_nonneg_left hHsq hε0
      have a2 : 9 / 1000 * L * ε * n ^ 3 ≤ gi ^ 2 * p3 * n ^ 3 * n ^ 3 :=
        mul_le_mul_of_nonneg_right hV2b hn3.le
      linarith
    exact le_of_mul_le_mul_right a (by positivity)
  calc ε * u ^ 2 ≤ ε * (2 * t1 ^ 2 + 2 * t2 ^ 2) := mul_le_mul_of_nonneg_left h4 hε0
    _ = 2 * (ε * t1 ^ 2) + 2 * (ε * t2 ^ 2) := by ring
    _ ≤ 17 * gi ^ 2 * p3 := by linarith

/- ## The facts about the trajectory and the errors -/

/-- The facts about the trajectory and the error sequences at the index `i`. -/
structure IdxFacts (N i : ℕ) : Prop where
  Qlo : (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ Qh N i
  Qhi : Qh N i ≤ (N.choose 2 : ℝ)
  y0 : 0 ≤ yh N i
  yhi : yh N i ≤ 9 * (i : ℝ) * Qh N i / (N : ℝ) ^ 3
  ale : (1 + yh N i) / Qh N i ≤ 1 / (N : ℝ)
  asum : aSum N i ≤ 1 / 2000 * Real.log N
  eYlo : (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i
  eYhi : eY N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ))
  eQ0 : 0 ≤ eQ N i
  eQhi : eQ N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i

section Compare

variable {N : ℕ}

theorem Scale.npos (sc : Scale N) : (0 : ℝ) < N := by linarith [sc.n64]

theorem Scale.Mpos (sc : Scale N) : (0 : ℝ) < (N.choose 2 : ℝ) := by
  have hn := sc.npos
  exact lt_of_lt_of_le (by positivity) sc.Mlo

theorem Scale.Hpos (sc : Scale N) : (0 : ℝ) < (hor N : ℝ) := by linarith [sc.H1]

theorem Scale.Lnonneg (sc : Scale N) : 0 ≤ Real.log N := by linarith [sc.L0]

theorem Scale.eps_half (sc : Scale N) : (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 / 2 := by
  linarith [sc.eps]

theorem Scale.S0 (sc : Scale N) : (0 : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := by linarith [sc.S1]

theorem IdxFacts.Qpos (sc : Scale N) {i : ℕ} (h : IdxFacts N i) : 0 < Qh N i :=
  lt_of_lt_of_le (mul_pos sc.Mpos sc.gi0) h.Qlo

theorem IdxFacts.eY0 {i : ℕ} (h : IdxFacts N i) : 0 ≤ eY N i :=
  le_trans (Real.rpow_nonneg (Nat.cast_nonneg N) _) h.eYlo

/-- `1 + ŷ ≤ Q̂ / 64`. -/
theorem IdxFacts.one_add_y_le (sc : Scale N) {i : ℕ} (h : IdxFacts N i) :
    1 + yh N i ≤ Qh N i / 64 := by
  have hQ := h.Qpos sc
  have h1 := h.ale
  rw [div_le_iff₀ hQ] at h1
  have h2 : 1 / (N : ℝ) ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) sc.n64
  have h3 : 1 / (N : ℝ) * Qh N i ≤ 1 / 64 * Qh N i := mul_le_mul_of_nonneg_right h2 hQ.le
  linarith

/-- `S₀ ≤ Q̂ / 40`. -/
theorem IdxFacts.S_le (sc : Scale N) {i : ℕ} (h : IdxFacts N i) :
    (N : ℝ) ^ (9 / 20 : ℝ) ≤ Qh N i / 40 := by
  have h1 := sc.cH
  have h2 := h.Qlo
  have h3 : 40 * (N : ℝ) ^ (9 / 20 : ℝ) * 1 ≤ 40 * (N : ℝ) ^ (9 / 20 : ℝ) * (hor N : ℝ) :=
    mul_le_mul_of_nonneg_left sc.H1 (mul_nonneg (by norm_num) sc.S0)
  linarith

/-- `ŷ ≤ 9 H Q̂ / N³`. -/
theorem IdxFacts.y_le (sc : Scale N) {i : ℕ} (hi : i ≤ hor N) (h : IdxFacts N i) :
    yh N i ≤ 9 * (hor N : ℝ) * Qh N i / (N : ℝ) ^ 3 := by
  have hQ := h.Qpos sc
  have hn := sc.npos
  have hi' : (i : ℝ) ≤ (hor N : ℝ) := Nat.cast_le.mpr hi
  refine le_trans h.yhi ?_
  refine div_le_div_of_nonneg_right ?_ (pow_pos hn 3).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi' (by norm_num)) hQ.le

/-- At one index: `a ≤ abar ≤ 1`, and `abar - a` is small. -/
theorem delta_bounds (sc : Scale N) {i : ℕ} (h : IdxFacts N i) :
    (1 + yh N i) / Qh N i ≤ abar N i ∧ abar N i ≤ 1 ∧
    abar N i - (1 + yh N i) / Qh N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ))
      * (4 * ((1 + yh N i) / Qh N i) + 2 * ((N : ℝ) ^ (9 / 20 : ℝ)
        / ((N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ))))) := by
  have hQ := h.Qpos sc
  have hε0 := sc.eps0.le
  have hMg : 0 < (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) := mul_pos sc.Mpos sc.gi0
  refine ⟨?_, ?_, ?_⟩
  · exact abar_ge_a hQ h.y0 h.eY0 h.eQ0 h.eQhi sc.eps_half
  · exact abar_le_one hQ h.y0 h.eYhi h.eQhi sc.eps sc.S0 (h.one_add_y_le sc) (h.S_le sc)
  · have h1 : abar N i - (1 + yh N i) / Qh N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ))
        * (4 * ((1 + yh N i) / Qh N i) + 2 * ((N : ℝ) ^ (9 / 20 : ℝ) / Qh N i)) :=
      abar_sub_a_le hQ h.y0 h.eYhi h.eQhi hε0 sc.eps_half sc.S0
    have h2 : (N : ℝ) ^ (9 / 20 : ℝ) / Qh N i
        ≤ (N : ℝ) ^ (9 / 20 : ℝ) / ((N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ))) :=
      div_le_div_of_nonneg_left sc.S0 hMg h.Qlo
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hε0)
    linarith

/-- Partial sums of `abar_j - a_j`. -/
noncomputable def dSum (N i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, (abar N j - (1 + yh N j) / Qh N j)

theorem dSum_zero (N : ℕ) : dSum N 0 = 0 := by
  unfold dSum
  exact Finset.sum_range_zero _

theorem dSum_succ (N i : ℕ) :
    dSum N (i + 1) = dSum N i + (abar N i - (1 + yh N i) / Qh N i) := by
  unfold dSum
  exact Finset.sum_range_succ _ i

/-- The partial sums `dSum` are bounded by the partial sums of `a_j`. -/
theorem dSum_bounds {ε c : ℝ} {I : ℕ}
    (hδ : ∀ i < I, 0 ≤ abar N i - (1 + yh N i) / Qh N i ∧
      abar N i - (1 + yh N i) / Qh N i ≤ ε * (4 * ((1 + yh N i) / Qh N i) + c)) :
    ∀ i ≤ I, 0 ≤ dSum N i ∧ dSum N i ≤ ε * (4 * aSum N i + c * (i : ℝ)) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [dSum_zero, aSum_zero]
    constructor
    · exact le_refl _
    · simp
  | succ i ih =>
    intro hi
    obtain ⟨h0, h1⟩ := ih (Nat.le_of_succ_le hi)
    obtain ⟨d0, d1⟩ := hδ i hi
    rw [dSum_succ, aSum_succ]
    refine ⟨by linarith, ?_⟩
    have e : ε * (4 * (aSum N i + (1 + yh N i) / Qh N i) + c * ((i + 1 : ℕ) : ℝ))
        = ε * (4 * aSum N i + c * (i : ℝ)) + ε * (4 * ((1 + yh N i) / Qh N i) + c) := by
      push_cast; ring
    rw [e]
    linarith

/-- `0 ≤ dSum ≤ 1/20` up to the horizon. -/
theorem dSum_le (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) :
    ∀ i ≤ hor N, 0 ≤ dSum N i ∧ dSum N i ≤ 1 / 20 := by
  intro i hi
  have hε0 := sc.eps0.le
  have hMg : 0 < (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) := mul_pos sc.Mpos sc.gi0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * ((N : ℝ) ^ (9 / 20 : ℝ)
      / ((N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)))) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]; exact mul_nonneg (by norm_num) (div_nonneg sc.S0 hMg.le)
  have hcH : c * (hor N : ℝ) ≤ 1 / 20 := by
    have h1 : (N : ℝ) ^ (9 / 20 : ℝ) / ((N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)))
        * (hor N : ℝ) ≤ 1 / 40 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hMg]
      linarith [sc.cH]
    rw [hc]; linarith
  have hδ : ∀ j < hor N, 0 ≤ abar N j - (1 + yh N j) / Qh N j ∧
      abar N j - (1 + yh N j) / Qh N j
        ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (4 * ((1 + yh N j) / Qh N j) + c) := by
    intro j hj
    obtain ⟨d0, -, d1⟩ := delta_bounds sc (hF j hj.le)
    rw [hc]
    exact ⟨by linarith, d1⟩
  obtain ⟨h0, h1⟩ := dSum_bounds hδ i hi
  refine ⟨h0, le_trans h1 ?_⟩
  have ha : aSum N i ≤ 1 / 2000 * Real.log N := (hF i hi).asum
  have hci : c * (i : ℝ) ≤ 1 / 20 :=
    le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi) hc0) hcH
  have h2 : (N : ℝ) ^ (-(1 / 20 : ℝ)) * (4 * aSum N i + c * (i : ℝ))
      ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (4 * (1 / 2000 * Real.log N) + 1 / 20) :=
    mul_le_mul_of_nonneg_left (by linarith) hε0
  have h3 := sc.epsL
  linarith

/-- The invariant of the comparison of `gW` with the trajectory. -/
theorem gW_inv (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) :
    ∀ i ≤ hor N, Qh N i * (1 - 2 * dSum N i) ≤ gW N i * (N.choose 2 : ℝ) ∧
      gW N i * (N.choose 2 : ℝ) ≤ Qh N i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [gW_zero, Qh_zero, dSum_zero]
    constructor <;> simp
  | succ i ih =>
    intro hi
    have hi' : i ≤ hor N := Nat.le_of_succ_le hi
    obtain ⟨h1, h2⟩ := ih hi'
    have hf := hF i hi'
    have hQ := hf.Qpos sc
    have hQne : Qh N i ≠ 0 := hQ.ne'
    obtain ⟨d0, d1, -⟩ := delta_bounds sc hf
    obtain ⟨D0, -⟩ := dSum_le sc hF i hi'
    have ha : (1 + yh N i) / Qh N i ≤ 1 / 2 := by
      have h3 := hf.one_add_y_le sc
      rw [div_le_iff₀ hQ]
      linarith
    have hQs : Qh N (i + 1) = Qh N i * (1 - (1 + yh N i) / Qh N i) := by
      rw [Qh_succ]
      field_simp
      ring
    obtain ⟨s1, s2⟩ := gW_step h1 h2 hQ.le D0 d0 d1 ha
    rw [gW_succ, dSum_succ, hQs]
    constructor
    · calc Qh N i * (1 - (1 + yh N i) / Qh N i)
            * (1 - 2 * (dSum N i + (abar N i - (1 + yh N i) / Qh N i)))
          ≤ gW N i * (N.choose 2 : ℝ) * (1 - abar N i) := s1
        _ = gW N i * (1 - abar N i) * (N.choose 2 : ℝ) := by ring
    · calc gW N i * (1 - abar N i) * (N.choose 2 : ℝ)
          = gW N i * (N.choose 2 : ℝ) * (1 - abar N i) := by ring
        _ ≤ Qh N i * (1 - (1 + yh N i) / Qh N i) := s2

/-- `(9/10) Q̂_i ≤ M gW_i ≤ Q̂_i` up to the horizon. -/
theorem gW_bounds (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) :
    ∀ i ≤ hor N, 9 / 10 * Qh N i ≤ gW N i * (N.choose 2 : ℝ) ∧
      gW N i * (N.choose 2 : ℝ) ≤ Qh N i := by
  intro i hi
  obtain ⟨h1, h2⟩ := gW_inv sc hF i hi
  obtain ⟨-, D1⟩ := dSum_le sc hF i hi
  have hQ := (hF i hi).Qpos sc
  refine ⟨?_, h2⟩
  have h3 : Qh N i * (9 / 10) ≤ Qh N i * (1 - 2 * dSum N i) :=
    mul_le_mul_of_nonneg_left (by linarith) hQ.le
  linarith

theorem gW_pos (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) :
    ∀ i ≤ hor N, 0 < gW N i := by
  intro i hi
  obtain ⟨h1, -⟩ := gW_bounds sc hF i hi
  have hQ := (hF i hi).Qpos sc
  have h2 : 0 < gW N i * (N.choose 2 : ℝ) := by linarith
  exact (mul_pos_iff_of_pos_right sc.Mpos).mp h2

/-- `(4/5) Q̂_i ≤ M gW_{i+1}` before the horizon. -/
theorem gW_succ_lower (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) :
    ∀ i < hor N, 4 / 5 * Qh N i ≤ gW N (i + 1) * (N.choose 2 : ℝ) := by
  intro i hi
  obtain ⟨h1, -⟩ := gW_bounds sc hF (i + 1) hi
  have hf := hF i hi.le
  have hQ := hf.Qpos sc
  have h2 := hf.one_add_y_le sc
  rw [Qh_succ] at h1
  linarith

/- ## The fields of `NumEdge` -/

theorem numEdge_nS (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) {i : ℕ} (hi : i < hor N) :
    2 * (Qh N i + eQ N i) ≤ 5 * (N.choose 2 : ℝ) * gW N i := by
  have hf := hF i hi.le
  have hQ := hf.Qpos sc
  obtain ⟨h1, -⟩ := gW_bounds sc hF i hi.le
  have h2 : (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i ≤ 1 / 100 * Qh N i :=
    mul_le_mul_of_nonneg_right sc.eps hQ.le
  have h3 := hf.eQhi
  linarith

theorem lamWn_nonneg (sc : Scale N) : 0 ≤ lamWn N := by
  unfold lamWn B0
  exact div_nonneg (div_nonneg sc.Lnonneg (by norm_num))
    (div_nonneg (mul_nonneg (by norm_num) sc.Hpos.le) sc.npos.le)

theorem B0_nonneg (sc : Scale N) : 0 ≤ B0 N := by
  unfold B0
  exact div_nonneg sc.Lnonneg (by norm_num)

/-- The increments in the Bennett step are bounded by `B0 / lamWn`. -/
theorem bennett_bound (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) {i : ℕ}
    (hi : i < hor N) :
    lamWn N * ((1 + yh N i + eY N i) / gW N (i + 1)) ≤ B0 N := by
  have hf := hF i hi.le
  have hQ := hf.Qpos sc
  have hn := sc.npos
  have hH := sc.Hpos
  have hG := gW_succ_lower sc hF i hi
  have hG0 := gW_pos sc hF (i + 1) hi
  have hX : (1 + yh N i + eY N i) / gW N (i + 1) ≤ 11 * (hor N : ℝ) / N :=
    bstep_le hQ sc.Mpos hn hH hG0 hG hf.y0 (hf.y_le sc hi.le) hf.eYhi sc.eps sc.S1 sc.Mhi
      hf.Qlo sc.SgH
  have hd : 0 < 11 * (hor N : ℝ) / N := div_pos (mul_pos (by norm_num) hH) hn
  have e : lamWn N * (11 * (hor N : ℝ) / N) = B0 N := by
    unfold lamWn
    exact div_mul_cancel₀ _ hd.ne'
  calc lamWn N * ((1 + yh N i + eY N i) / gW N (i + 1))
      ≤ lamWn N * (11 * (hor N : ℝ) / N) := mul_le_mul_of_nonneg_left hX (lamWn_nonneg sc)
    _ = B0 N := e

/-- The variance condition of `NumW`. -/
theorem var_bound (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) {i : ℕ} (hi : i < hor N)
    {m : ℝ} (hm : 0 ≤ m) :
    (3 * m * (1 + 2 * Dmx N + 2 * (N : ℝ) ^ (9 / 10 : ℝ) * Zmx N))
        / (Qmin N * gW N (i + 1) ^ 2)
      + abar N i * (abar N i - alow N i) * m ^ 2 / gW N (i + 1) ^ 2 ≤ vWn N m := by
  have hf := hF i hi.le
  have hQ := hf.Qpos sc
  have hn := sc.npos
  have hM := sc.Mpos
  have hgi := sc.gi0
  have hε0 := sc.eps0.le
  have hG := gW_succ_lower sc hF i hi
  have hG0 := gW_pos sc hF (i + 1) hi
  have hp1 : 0 ≤ (N : ℝ) ^ (37 / 40 : ℝ) := Real.rpow_nonneg hn.le _
  have hp2 : 0 ≤ (N : ℝ) ^ (-(107 / 100 : ℝ)) := Real.rpow_nonneg hn.le _
  have hp3 : 0 ≤ (N : ℝ) ^ (-(304 / 100 : ℝ)) := Real.rpow_nonneg hn.le _
  -- `gW ≥ (4/5) N^{-γ}`
  have hGgi : 4 / 5 * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ gW N (i + 1) := by
    have h1 : 4 / 5 * (N : ℝ) ^ (-(1 / 2000 : ℝ)) * (N.choose 2 : ℝ)
        ≤ gW N (i + 1) * (N.choose 2 : ℝ) := by
      have h := hf.Qlo
      linarith
    exact le_of_mul_le_mul_right h1 hM
  have hG2 : (4 / 5 * (N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 2 ≤ gW N (i + 1) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hgi.le) hGgi 2
  -- first term
  have hfirst : (3 * m * (1 + 2 * Dmx N + 2 * (N : ℝ) ^ (9 / 10 : ℝ) * Zmx N))
      / (Qmin N * gW N (i + 1) ^ 2) ≤ 144 * m * (N : ℝ) ^ (-(107 / 100 : ℝ)) := by
    unfold Qmin
    exact var_first hm sc.K hp1 hGgi hgi sc.Mlo hn sc.V1 hp2
  -- second term
  have h1 : abar N i * (abar N i - alow N i) ≤ 18 * (N : ℝ) ^ (-(1 / 20 : ℝ))
      * ((1 + yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) / Qh N i) ^ 2 :=
    abar_alow_le hQ hf.y0 hf.eY0 hf.eYhi hf.eQ0 hf.eQhi hε0 sc.eps_half sc.S0
  have h2 : (N : ℝ) ^ (-(1 / 20 : ℝ)) * ((1 + yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) / Qh N i) ^ 2
      ≤ 17 * ((N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)) := by
    have hy := hf.y_le sc hi.le
    rw [le_div_iff₀ (pow_pos hn 3)] at hy
    have hng : 0 < (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2000 : ℝ)) := mul_pos (pow_pos hn 2) hgi
    have hw : 0 ≤ 1 + yh N i + (N : ℝ) ^ (9 / 20 : ℝ) := by
      linarith [hf.y0, sc.S0]
    exact eps_u_sq_le (u := (1 + yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) / Qh N i)
      (t1 := 8 * (N : ℝ) ^ (9 / 20 : ℝ) / ((N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2000 : ℝ))))
      (t2 := 9 * (hor N : ℝ) / (N : ℝ) ^ 3) (L := Real.log N)
      hQ (div_nonneg hw hQ.le)
      (div_nonneg (mul_nonneg (by norm_num) sc.S0) hng.le)
      (div_mul_cancel₀ _ hQ.ne') hy sc.S1 hf.Qlo hgi sc.Mlo hn hε0
      (div_mul_cancel₀ _ hng.ne') (div_mul_cancel₀ _ (pow_pos hn 3).ne')
      sc.Hsq sc.V2a sc.V2b
  have hsecond : abar N i * (abar N i - alow N i) * m ^ 2 / gW N (i + 1) ^ 2
      ≤ 800 * m ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)) := by
    rw [div_le_iff₀ (pow_pos hG0 2)]
    have h3 : abar N i * (abar N i - alow N i) * m ^ 2
        ≤ 18 * (17 * ((N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)))
          * m ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg m)
    have h4 : 800 * m ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ))
          * (4 / 5 * (N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 2
        ≤ 800 * m ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)) * gW N (i + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hG2
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg m)) hp3)
    have h5 : 0 ≤ ((N : ℝ) ^ (-(1 / 2000 : ℝ))) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)) * m ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hp3) (sq_nonneg m)
    linarith
  unfold vWn
  linarith

theorem numEdge_nW (sc : Scale N) (hF : ∀ i ≤ hor N, IdxFacts N i) {m : ℝ} (hm : 0 ≤ m) :
    NumW N m ((N : ℝ) ^ (9 / 10 : ℝ)) (lamWn N) (B0 N) (vWn N m) := by
  unfold NumW
  refine ⟨lamWn_nonneg sc, B0_nonneg sc, fun i hi => ?_⟩
  exact ⟨gW_pos sc hF i hi.le, gW_pos sc hF (i + 1) hi, bennett_bound sc hF hi,
    var_bound sc hF hi hm⟩

theorem CWn_nonneg (N : ℕ) {m : ℝ} (hm : 0 ≤ m) : 0 ≤ CWn N m := by
  unfold CWn vWn
  have h1 : 0 ≤ (N : ℝ) ^ (-(107 / 100 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : 0 ≤ (N : ℝ) ^ (-(304 / 100 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h3 : 0 ≤ 144 * m * (N : ℝ) ^ (-(107 / 100 : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hm) h1
  have h4 : 0 ≤ 800 * m ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg m)) h2
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) (by linarith))

/-- The potential threshold for an edge set with at least `1000 k √(N log N)` pairs. -/
theorem numEdge_f2a (sc : Scale N) {k : ℕ} {m : ℝ} (hk : 1 ≤ k)
    (hm : 1000 * (k : ℝ) * Real.sqrt (N * Real.log N) ≤ m) (hmM : m ≤ (N.choose 2 : ℝ)) :
    8 * (N : ℝ) ^ k ≤ LamW N m := by
  have hn := sc.npos
  have hH := sc.Hpos
  have hL0 := sc.Lnonneg
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hlam := lamWn_nonneg sc
  have hp3 : 0 ≤ (N : ℝ) ^ (-(304 / 100 : ℝ)) := Real.rpow_nonneg hn.le _
  -- `lamWn * hor = N log N / 1100`
  have hd : 0 < 11 * (hor N : ℝ) / N := div_pos (mul_pos (by norm_num) hH) hn
  have e0 : 11 * (hor N : ℝ) / N * N = 11 * (hor N : ℝ) := div_mul_cancel₀ _ hn.ne'
  have e1 : lamWn N * (11 * (hor N : ℝ) / N) = B0 N := by
    unfold lamWn
    exact div_mul_cancel₀ _ hd.ne'
  have hlamH : lamWn N * (hor N : ℝ) = N * Real.log N / 1100 := by
    have e2 : lamWn N * (11 * (hor N : ℝ)) = B0 N * N := by
      calc lamWn N * (11 * (hor N : ℝ)) = lamWn N * (11 * (hor N : ℝ) / N * N) := by rw [e0]
        _ = lamWn N * (11 * (hor N : ℝ) / N) * N := by ring
        _ = B0 N * N := by rw [e1]
    unfold B0 at e2
    linarith
  -- the allowance `vWn`
  have h2m : 2 * m ≤ (N : ℝ) ^ 2 := by linarith [sc.Mhi]
  have hv : vWn N m ≤ m * (144 * (N : ℝ) ^ (-(107 / 100 : ℝ))
      + 400 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ))) := by
    unfold vWn
    have h := mul_le_mul_of_nonneg_left h2m (mul_nonneg hm0 hp3)
    linarith
  -- `CWn * hor ≤ lamWn * (m / 4)`
  have hC : CWn N m * (hor N : ℝ) ≤ lamWn N * (m / 4) := by
    have e : CWn N m * (hor N : ℝ)
        = lamWn N * (Real.exp (B0 N) * vWn N m * (lamWn N * (hor N : ℝ))) := by
      unfold CWn; ring
    rw [e, hlamH]
    refine mul_le_mul_of_nonneg_left ?_ hlam
    have h2 := mul_le_mul_of_nonneg_left sc.F2 hm0
    calc Real.exp (B0 N) * vWn N m * ((N : ℝ) * Real.log N / 1100)
        ≤ Real.exp (B0 N) * (m * (144 * (N : ℝ) ^ (-(107 / 100 : ℝ))
          + 400 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ))))
            * ((N : ℝ) * Real.log N / 1100) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le)
            (div_nonneg (mul_nonneg hn.le hL0) (by norm_num))
      _ = m * (Real.exp (B0 N) * (144 * (N : ℝ) ^ (-(107 / 100 : ℝ))
          + 400 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(304 / 100 : ℝ)))
            * ((N : ℝ) * Real.log N / 1100)) := by ring
      _ ≤ m * (1 / 4) := h2
      _ = m / 4 := by ring
  -- `2 k log N ≤ lamWn * (m / 4)`
  have hlamm : 2 * (k : ℝ) * Real.log N ≤ lamWn N * (m / 4) := by
    have h1 := sc.f2a k m hm
    have h2 := mul_le_mul_of_nonneg_left h1 hL0
    have h3 : 2 * (k : ℝ) * Real.log N * (hor N : ℝ) ≤ lamWn N * (m / 4) * (hor N : ℝ) := by
      have e : lamWn N * (m / 4) * (hor N : ℝ) = lamWn N * (hor N : ℝ) * (m / 4) := by ring
      rw [e, hlamH]
      linarith
    exact le_of_mul_le_mul_right h3 hH
  -- conclusion
  unfold LamW
  have hpow : (N : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hn]
  have h8 : (8 : ℝ) ≤ Real.exp (Real.log N) := by
    rw [Real.exp_log hn]; linarith [sc.n64]
  have h9 : 8 * (N : ℝ) ^ k ≤ Real.exp (Real.log N + (k : ℝ) * Real.log N) := by
    rw [Real.exp_add, hpow]
    exact mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
  refine le_trans h9 (Real.exp_le_exp.mpr ?_)
  have h10 : Real.log N ≤ (k : ℝ) * Real.log N := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1) hL0]
  have e : lamWn N * (m / 2) = 2 * (lamWn N * (m / 4)) := by ring
  rw [e]
  linarith

/-- The survival probability of an edge set with at least `1000 k √(N log N)` pairs. -/
theorem numEdge_f2b (sc : Scale N) {k : ℕ} {m : ℝ} (hk : 1 ≤ k)
    (hm : 1000 * (k : ℝ) * Real.sqrt (N * Real.log N) ≤ m) (hmM : m ≤ (N.choose 2 : ℝ)) :
    (N : ℝ) ^ k * (1 - m / (5 * (N.choose 2 : ℝ))) ^ hor N ≤ 1 / 8 := by
  have hn := sc.npos
  have hM := sc.Mpos
  have hL0 := sc.Lnonneg
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h5M : 0 < 5 * (N.choose 2 : ℝ) := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = m / (5 * (N.choose 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hx]
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one h5M]; linarith
  have hHx : 2 * (k : ℝ) * Real.log N ≤ (hor N : ℝ) * x := by
    rw [hx, mul_div_assoc', le_div_iff₀ h5M]
    have h1 := sc.f2b k m hm
    have h2 : 2 * (k : ℝ) * Real.log N * (N.choose 2 : ℝ)
        ≤ 2 * (k : ℝ) * Real.log N * ((N : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left sc.Mhi (mul_nonneg (by linarith) hL0)
    linarith
  have h1 : (1 - x) ^ hor N ≤ Real.exp (-((hor N : ℝ) * x)) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - x) (Real.one_sub_le_exp_neg x) (hor N)
    rw [← Real.exp_nat_mul] at h
    have e : (hor N : ℝ) * -x = -((hor N : ℝ) * x) := by ring
    rw [e] at h
    exact h
  have hpow : (N : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hn]
  have h8 : (8 : ℝ) ≤ Real.exp (Real.log N) := by
    rw [Real.exp_log hn]; linarith [sc.n64]
  have h2 : (N : ℝ) ^ k * (1 - x) ^ hor N
      ≤ Real.exp ((k : ℝ) * Real.log N) * Real.exp (-((hor N : ℝ) * x)) := by
    rw [hpow]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have h3 : Real.exp ((k : ℝ) * Real.log N) * Real.exp (-((hor N : ℝ) * x))
      ≤ Real.exp (-Real.log N) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h10 : Real.log N ≤ (k : ℝ) * Real.log N := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1) hL0]
    linarith
  have h4 : Real.exp (-Real.log N) * 8 ≤ 1 := by
    have h5 : Real.exp (-Real.log N) * Real.exp (Real.log N) = 1 := by
      rw [← Real.exp_add]; simp
    have h6 := mul_le_mul_of_nonneg_left h8 (Real.exp_pos (-Real.log N)).le
    linarith
  linarith

end Compare

/-- All fields of `NumEdge 1000 N` for one `N` with `log N ≥ 10000`, from the conclusions of
`traj_facts` and `err_facts`. -/
theorem numEdge_core {N : ℕ} (hL : 10000 ≤ Real.log N)
    (hT : ∀ i ≤ horizon (1 / 2000) N,
      (N.choose 2 : ℝ) * (N : ℝ) ^ (-(1 / 2000 : ℝ)) ≤ Qh N i ∧ Qh N i ≤ N.choose 2 ∧
      0 ≤ yh N i ∧ yh N i ≤ 9 * i * Qh N i / (N : ℝ) ^ 3 ∧
      0 < xh N i ∧ xh N i ≤ ((N : ℝ) - 2) * (Qh N i / N.choose 2) ^ 2 ∧
      (1 + yh N i) / Qh N i ≤ 1 / N ∧
      ∑ j ∈ Finset.range i, (1 + yh N j) / Qh N j ≤ 1 / 2000 * Real.log N)
    (hE : ∀ i ≤ horizon (1 / 2000) N,
      (N : ℝ) ^ (17 / 20 : ℝ) ≤ eX N i ∧ eX N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * xh N i ∧
      (N : ℝ) ^ (7 / 20 : ℝ) ≤ eY N i ∧
      eY N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * (yh N i + (N : ℝ) ^ (9 / 20 : ℝ)) ∧
      0 ≤ eQ N i ∧ eQ N i ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) * Qh N i) :
    NumEdge 1000 N := by
  have sc := scale_of_log hL
  have hF : ∀ i ≤ hor N, IdxFacts N i := by
    intro i hi
    obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := hT i hi
    obtain ⟨-, -, e3, e4, e5, e6⟩ := hE i hi
    exact ⟨h1, h2, h3, h4, h7, h8, e3, e4, e5, e6⟩
  exact
    { gpos := fun i hi => gW_pos sc hF i hi
      nS := fun i hi => numEdge_nS sc hF hi
      nW := fun m hm0 _ => numEdge_nW sc hF hm0
      cW0 := fun m hm0 => CWn_nonneg N hm0
      f2 := fun k m hk _ hm hmM => ⟨numEdge_f2a sc hk hm hmM, numEdge_f2b sc hk hm hmM⟩ }

end NumEdgeAux

/-- **The numerical facts about edge sets hold for all large `N`** (with the density constant
`A = 1000`). -/
theorem numEdge_eventually : ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ N : ℕ in Filter.atTop, NumEdge A N := by
  refine ⟨1000, by norm_num, ?_⟩
  have e2 : ∀ᶠ N : ℕ in Filter.atTop, (10000 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      10000
  have e3 := traj_facts (γ := 1 / 2000) (by norm_num) (by norm_num)
  have e4 := err_facts
  filter_upwards [e2, e3, e4] with N h2 h3 h4
  exact NumEdgeAux.numEdge_core h2 h3 h4

end TFP
end E1182

end NumEdgeProofPart

section FinalPart

/-
# Erdős Problem 1182, part (i): the order of magnitude of `f`
-/

namespace E1182

open TFP in
/-- For every large `N`, every not too dense graph with few vertices and many edges is blocked by
a triangle-free graph on `N` vertices (a history of the triangle-free process). -/
theorem blockerStatement : BlockerStatement := by
  obtain ⟨A, hA, hE⟩ := numEdge_eventually
  refine ⟨A, hA, ?_⟩
  filter_upwards [numGlobal_eventually, hE] with N hG hE'
  exact blockerAt_of_num hG hE'

/-- The upper bound `f(n) = O(n^{3/2} √(log n))`. -/
theorem f_isBigO_upper :
    (fun n : ℕ => (f n : ℝ)) =O[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
  f_isBigO_of_blocker blockerStatement

/-- **Erdős Problem 1182, part (i).** The largest number `f(n)` of edges of a connected graph `G`
on `n` vertices with `R(K_3, G) = 2n - 1` has order of magnitude `n^{3/2} √(log n)`. -/
theorem erdos_1182_i :
    (fun n : ℕ => (f n : ℝ)) =Θ[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
  f_isTheta_of_blocker blockerStatement

/-- The upper bound in explicit form: `f(n) ≤ B n^{3/2} √(log n)` for all large `n`. -/
theorem f_upper_sharp :
    ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
      (f n : ℝ) ≤ B * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by
  obtain ⟨C, hC⟩ := f_isBigO_upper.bound
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  filter_upwards [hC] with n hn
  have h0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg h0] at hn
  calc (f n : ℝ) ≤ C * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) := hn
    _ ≤ max C 1 * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ = max C 1 * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by ring

/-- **Kim's theorem** `R(3, k) > c k² / log k` for all large `k`, as a corollary of the upper
bound for `f` (see `kim_of_f_upper`). -/
theorem ramsey3_lower_kim :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in Filter.atTop, ¬ Ramsey3 ⌈c * (k : ℝ) ^ 2 / Real.log k⌉₊ k :=
  kim_of_f_upper f_upper_sharp

end E1182

end FinalPart

noncomputable def OMA.answer : ℕ → ℝ := fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)

theorem OMA.solution : Erdos1182.erdos_1182.parts.i.answer = OMA.answer →
    type_of% @Erdos1182.erdos_1182.parts.i := by
  intro h
  rw [h]
  exact E1182.erdos_1182_i
