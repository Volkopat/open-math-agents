import OMAReductions.R_Erdos1029_erdos_1029_R1
import Mathlib.Data.Set.Card

-- Reduction Erdos1029.erdos_1029.R1.H1.R1 of Erdos1029.erdos_1029.R1.H1
-- Credit: @sanchan
-- Combines the General Lovasz Local Lemma (H1, true standalone theorem) with the
-- deterministic monochromatic-clique alteration theorem (proved below) to reduce
-- Ramsey graph existence for k = 4s to finding LLL-admissible weighted graph
-- distributions with at most m surviving monochromatic k-cliques on n + m vertices (H2).

open SimpleGraph

namespace OMA.R_Erdos1029_erdos_1029_R1_H1_R1

/-- General Lovasz Local Lemma on finite weighted sample spaces: if nonnegative weights `w`
have strictly positive total weight and bad events `E i` (`i ∈ I`) satisfy the asymmetric
conditional LLL bounds with dependency neighborhoods `Γ i ⊆ I` and parameters `x i ∈ [0, 1)`,
then some sample avoids all bad events. -/
def H1 : Prop :=
  ∀ (M K : ℕ) (w : Fin M → ℝ) (I : Finset (Fin K)) (E : Fin K → Finset (Fin M))
    (Γ : Fin K → Finset (Fin K)) (p x : Fin K → ℝ),
    (∀ ω, 0 ≤ w ω) → (0 < ∑ ω, w ω) →
    (∀ i ∈ I, Γ i ⊆ I) →
    (∀ i ∈ I, 0 ≤ x i ∧ x i < 1) →
    (∀ i ∈ I, p i ≤ x i * ∏ j ∈ Γ i, (1 - x j)) →
    (∀ i ∈ I, ∀ S ⊆ I, i ∉ S → Disjoint S (Γ i) →
      (∑ ω ∈ (E i).filter (fun ω => ∀ j ∈ S, ω ∉ E j), w ω) ≤
        p i * (∑ ω ∈ (Finset.univ : Finset (Fin M)).filter (fun ω => ∀ j ∈ S, ω ∉ E j), w ω)) →
    ∃ ω : Fin M, ∀ i ∈ I, ω ∉ E i

/-- LLL-admissible weighted Ramsey coloring distributions with alteration budget `m`:
for every `a` and all sufficiently large `s`, letting `k = 4s` and `n = a * k * 2^(2s)`,
there exist an alteration budget `m` and a weighted finite family of graphs on `Fin (n + m)`
together with LLL-admissible bad events whose avoidance leaves at most `m` monochromatic
`k`-cliques. Lossless: any Ramsey graph on `Fin n` satisfies this with `m = 0, M = 1, K = 0`. -/
def H2 : Prop :=
  ∀ a : ℕ, ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
    let k := 2 * (2 * s)
    let n := a * (k * 2 ^ (2 * s))
    ∃ (m M K : ℕ) (g : Fin M → SimpleGraph (Fin (n + m))) (w : Fin M → ℝ)
      (I : Finset (Fin K)) (E : Fin K → Finset (Fin M))
      (Γ : Fin K → Finset (Fin K)) (p x : Fin K → ℝ),
      (∀ ω, 0 ≤ w ω) ∧ (0 < ∑ ω, w ω) ∧
      (∀ i ∈ I, Γ i ⊆ I) ∧
      (∀ i ∈ I, 0 ≤ x i ∧ x i < 1) ∧
      (∀ i ∈ I, p i ≤ x i * ∏ j ∈ Γ i, (1 - x j)) ∧
      (∀ i ∈ I, ∀ S ⊆ I, i ∉ S → Disjoint S (Γ i) →
        (∑ ω ∈ (E i).filter (fun ω => ∀ j ∈ S, ω ∉ E j), w ω) ≤
          p i * (∑ ω ∈ (Finset.univ : Finset (Fin M)).filter (fun ω => ∀ j ∈ S, ω ∉ E j), w ω)) ∧
      (∀ ω : Fin M, (∀ i ∈ I, ω ∉ E i) →
        {S : Finset (Fin (n + m)) | (g ω).IsNClique k S ∨ (g ω)ᶜ.IsNClique k S}.ncard ≤ m)

/-- Pulling back a graph along an injection preserves `k`-cliques under `Finset.map`. -/
theorem isNClique_map_of_comap {α β : Type*} {G : SimpleGraph β} {k : ℕ}
    (ι : α ↪ β) {T : Finset α} (hT : (G.comap ι).IsNClique k T) :
    G.IsNClique k (T.map ι) := by
  refine ⟨?_, by rw [Finset.card_map, hT.2]⟩
  intro a ha b hb hab
  rcases Finset.mem_map.mp (Finset.mem_coe.mp ha) with ⟨x, hx, rfl⟩
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hb) with ⟨y, hy, rfl⟩
  have hxy : x ≠ y := fun h => hab (congrArg ι h)
  exact hT.1 hx hy hxy

/-- Pulling back a graph along an injection preserves complement `k`-cliques under `Finset.map`. -/
theorem isNClique_compl_map_of_comap {α β : Type*} {G : SimpleGraph β} {k : ℕ}
    (ι : α ↪ β) {T : Finset α} (hT : (G.comap ι)ᶜ.IsNClique k T) :
    Gᶜ.IsNClique k (T.map ι) := by
  refine ⟨?_, by rw [Finset.card_map, hT.2]⟩
  intro a ha b hb hab
  rcases Finset.mem_map.mp (Finset.mem_coe.mp ha) with ⟨x, hx, rfl⟩
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hb) with ⟨y, hy, rfl⟩
  have hxy : x ≠ y := fun h => hab (congrArg ι h)
  have hadj : (G.comap ι)ᶜ.Adj x y := hT.1 hx hy hxy
  exact (G.compl_adj (ι x) (ι y)).2 ⟨hab, ((G.comap ι).compl_adj x y).1 hadj |>.2⟩

/-- Deterministic monochromatic-clique alteration theorem: deleting one vertex from each
monochromatic `k`-clique (`k ≥ 1`) in a graph on `n + m` vertices with at most `m`
monochromatic `k`-cliques leaves an induced subgraph on `n` vertices that is both
`k`-clique-free and co-`k`-clique-free. -/
theorem alteration_cliqueFree {n m k : ℕ} (hk : 1 ≤ k) (G : SimpleGraph (Fin (n + m)))
    (hcard : {S : Finset (Fin (n + m)) | G.IsNClique k S ∨ Gᶜ.IsNClique k S}.ncard ≤ m) :
    ∃ G' : SimpleGraph (Fin n), G'.CliqueFree k ∧ G'ᶜ.CliqueFree k := by
  classical
  let C : Finset (Finset (Fin (n + m))) :=
    Finset.univ.filter fun S => G.IsNClique k S ∨ Gᶜ.IsNClique k S
  have hCcard : C.card ≤ m := by
    have hset : (C : Set (Finset (Fin (n + m)))) =
        {S : Finset (Fin (n + m)) | G.IsNClique k S ∨ Gᶜ.IsNClique k S} := by
      ext S
      simp [C]
    rwa [← Set.ncard_coe_finset, hset]
  have hne : ∀ S ∈ C, S.Nonempty := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with h1 | h2
    · exact Finset.card_pos.mp (by rw [h1.2]; omega)
    · exact Finset.card_pos.mp (by rw [h2.2]; omega)
  let U : Finset (Fin (n + m)) := C.attach.image fun S => (hne S.1 S.2).choose
  have hUcard : U.card ≤ m :=
    Finset.card_image_le.trans (by rw [Finset.card_attach]; exact hCcard)
  let V : Finset (Fin (n + m)) := Finset.univ \ U
  have hVcard : n ≤ V.card := by
    have hsum : V.card + U.card = (Finset.univ : Finset (Fin (n + m))).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  obtain ⟨W, hWV, hWcard⟩ := Finset.exists_subset_card_eq hVcard
  let e : Fin n ≃ W := (Fintype.equivFinOfCardEq (by simp [hWcard])).symm
  let ι : Fin n ↪ Fin (n + m) := ⟨fun x => (e x).1, fun x y hxy => e.injective (Subtype.ext hxy)⟩
  have hnotU : ∀ x : Fin n, ι x ∉ U := fun x =>
    (Finset.mem_sdiff.mp (hWV (e x).2)).2
  have hhit : ∀ S ∈ C, ∃ u ∈ S, u ∈ U := by
    intro S hS
    refine ⟨(hne S hS).choose, (hne S hS).choose_spec, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨S, hS⟩, Finset.mem_attach C ⟨S, hS⟩, rfl⟩
  refine ⟨G.comap ι, ?_, ?_⟩
  · intro T hT
    have hSC : T.map ι ∈ C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (isNClique_map_of_comap ι hT)⟩
    obtain ⟨u, huS, huU⟩ := hhit (T.map ι) hSC
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp huS
    exact hnotU x huU
  · intro T hT
    have hSC : T.map ι ∈ C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (isNClique_compl_map_of_comap ι hT)⟩
    obtain ⟨u, huS, huU⟩ := hhit (T.map ι) hSC
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp huS
    exact hnotU x huU

theorem main : H1 → H2 → OMA.R_Erdos1029_erdos_1029_R1.H1 := by
  intro hLLL hDist a
  obtain ⟨N, hN⟩ := hDist a
  refine ⟨max N 1, fun s hs => ?_⟩
  have hsN : N ≤ s := le_trans (le_max_left N 1) hs
  have hs1 : 1 ≤ s := le_trans (le_max_right N 1) hs
  obtain ⟨m, M, K, g, w, I, E, Γ, p, x, hw0, hwpos, hΓ, hx, hp, hcond, havoid⟩ := hN s hsN
  obtain ⟨ω, hω⟩ := hLLL M K w I E Γ p x hw0 hwpos hΓ hx hp hcond
  have hcard := havoid ω hω
  exact alteration_cliqueFree (by omega) (g ω) hcard

end OMA.R_Erdos1029_erdos_1029_R1_H1_R1
