import FormalConjectures.ErdosProblems.«743»

-- Reduction Erdos743.erdos_743.variants.bounded_degree.R2 of Erdős Problem 743 — bounded degree
-- Credit: @hackoria
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos743_erdos_743_variants_bounded_degree_R2

open Filter Finset SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ η : ℝ, 0 < η → η ≤ 1 / 1000 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (S : Finset ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)),
        S ⊆ Finset.Icc 2 n →
        7 * n / 8 ≤ S.card →
        (∀ k ∈ S, (T k).IsTree ∧ (T k).maxDegree ≤ d) →
        let p : ℝ := ((n.choose 2 - ∑ k ∈ S, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ)
        let q : ℝ := 1 - p + (3 / 2 : ℝ) * η
        (1 / 40 : ℝ) ≤ p → p ≤ (1 / 10 : ℝ) →
        (∀ v : Fin n, |(G.degree v : ℝ) - q * n| ≤ η ^ 2 * n) →
        (∀ u v : Fin n, u ≠ v →
          |((Finset.univ.filter (fun w : Fin n => G.Adj u w ∧ G.Adj v w)).card : ℝ) - q ^ 2 * n| ≤
            η ^ 2 * n) →
        ∃ f : (k : S) → Fin k → Fin n,
          (∀ k : S, Function.Injective (f k)) ∧
          (∀ k l : S, (k : ℕ) < (l : ℕ) →
            Disjoint ((T k).map (f k)).edgeSet ((T l).map (f l)).edgeSet) ∧
          let P : SimpleGraph (Fin n) := ⨆ k : S, (T k).map (f k)
          P ≤ G ∧
          (∀ v : Fin n, ((G \ P).degree v : ℝ) ≤ 8 * η * n) ∧
          (∀ v : Fin n, Even (Pᶜ.degree v))

def H2 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (R : SimpleGraph (Fin n)) (I : Finset ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)),
      I ⊆ Finset.Icc ((n + 3) / 4) (n / 2) →
      n / 20 ≤ I.card →
      ∑ k ∈ I, (k - 1) = R.edgeFinset.card →
      (∀ v : Fin n, Even (R.degree v)) →
      let p : ℝ := (R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)
      (1 / 40 : ℝ) ≤ p → p ≤ (1 / 10 : ℝ) →
      (∀ v : Fin n, |(R.degree v : ℝ) - p * n| ≤ δ * n) →
      (∀ u v : Fin n, u ≠ v →
        |((Finset.univ.filter (fun w : Fin n => R.Adj u w ∧ R.Adj v w)).card : ℝ) - p ^ 2 * n| ≤
          δ * n) →
      (∀ k ∈ I, (T k).IsTree ∧ (T k).maxDegree ≤ d ∧
        n / 210 ≤ (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card) →
      ∃ f : (k : I) → Fin k → Fin n,
        (∀ k : I, Function.Injective (f k)) ∧
        (∀ k : I, (T k).map (f k) ≤ R) ∧
        (∀ k l : I, (k : ℕ) < (l : ℕ) →
          Disjoint ((T k).map (f k)).edgeSet ((T l).map (f l)).edgeSet)

def H3 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (R : SimpleGraph (Fin n)) (I : Finset ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)),
      I ⊆ Finset.Icc ((n + 3) / 4) (n / 2) →
      n / 20 ≤ I.card →
      ∑ k ∈ I, (k - 1) = R.edgeFinset.card →
      (∀ v : Fin n, Even (R.degree v)) →
      let p : ℝ := (R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)
      (1 / 40 : ℝ) ≤ p → p ≤ (1 / 10 : ℝ) →
      (∀ v : Fin n, |(R.degree v : ℝ) - p * n| ≤ δ * n) →
      (∀ u v : Fin n, u ≠ v →
        |((Finset.univ.filter (fun w : Fin n => R.Adj u w ∧ R.Adj v w)).card : ℝ) - p ^ 2 * n| ≤
          δ * n) →
      (∀ k ∈ I, (T k).IsTree ∧ (T k).maxDegree ≤ d ∧
        (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card < k / 52 ∧
        ∃ g : Fin (n / 100) × Fin 12 → Fin k, Function.Injective g ∧
          (∀ i (j : Fin 11), (T k).Adj (g (i, j.castSucc)) (g (i, j.succ))) ∧
          (∀ i j, (T k).degree (g (i, j)) = 2)) →
      ∃ f : (k : I) → Fin k → Fin n,
        (∀ k : I, Function.Injective (f k)) ∧
        (∀ k : I, (T k).map (f k) ≤ R) ∧
        (∀ k l : I, (k : ℕ) < (l : ℕ) →
          Disjoint ((T k).map (f k)).edgeSet ((T l).map (f l)).edgeSet)

section Helpers

-- ============================================================================
-- MODULE 1: Unconditional proof for d ≤ 2 (all n)
-- ============================================================================

/-!
Self-contained, def-free proof of the `d ≤ 2` case of
`Erdos743.erdos_743.variants.bounded_degree` for inclusion in `R2.lean`.
-/


private lemma r2_fin_covBy_iff {k : ℕ} {a b : Fin k} : a ⋖ b ↔ a.val + 1 = b.val := by
  constructor
  · rintro ⟨hab, hno⟩
    have hab' : a.val < b.val := hab
    by_contra hne
    exact hno (c := ⟨a.val + 1, by omega⟩) (show a.val < a.val + 1 by omega)
      (show a.val + 1 < b.val by omega)
  · intro h
    refine ⟨show a.val < b.val by omega, fun c hac hcb => ?_⟩
    have hac' : a.val < c.val := hac
    have hcb' : c.val < b.val := hcb
    omega

private lemma r2_pathGraph_adj_iff {k : ℕ} {a b : Fin k} :
    (pathGraph k).Adj a b ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val := by
  simp only [pathGraph, SimpleGraph.hasse_adj, r2_fin_covBy_iff]

private lemma r2_tree_deg_le_two_iso_path_from_end :
    ∀ (m : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V),
      G.IsTree → Fintype.card V = m + 1 → (∀ v : V, G.degree v ≤ 2) →
      ∀ u : V, G.degree u ≤ 1 →
      ∃ φ : G ≃g pathGraph (m + 1), φ u = 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ G _ hcard _ u _
    have hss : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    refine ⟨⟨⟨fun _ => 0, fun _ => u, fun v => Subsingleton.elim u v,
      fun i => by fin_cases i; rfl⟩, ?_⟩, rfl⟩
    intro a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simp
  | succ m ih =>
    intro V _ G hG hcard hdeg u hu
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hwu⟩ := exists_ne u
    obtain ⟨p⟩ := hG.connected.preconnected u w
    have hu_deg1 : G.degree u = 1 := by
      rcases p with _ | ⟨hadj, _⟩
      · exact False.elim (hwu rfl)
      · have hpos : 0 < G.degree u := by
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset u _).mpr hadj⟩
        omega
    obtain ⟨u', huu', hu'_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu_deg1
    let V' := ({u}ᶜ : Set V)
    let G' := G.induce V'
    have hV' : Fintype.card V' = m + 1 := by
      have eV' : V' ≃ ↥(Finset.univ.erase u) :=
        ⟨fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩,
         fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
         fun _ => rfl, fun _ => rfl⟩
      rw [Fintype.card_congr eV', Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, hcard]
      omega
    have hG' : G'.IsTree :=
      ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hu_deg1, hG.isAcyclic.induce V'⟩
    have hsub (x : V') :
        (G'.neighborFinset x).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ G.neighborFinset x.1 := by
      intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [SimpleGraph.mem_neighborFinset] at hz ⊢
      exact hz
    have hdeg' (x : V') : G'.degree x ≤ 2 := by
      have hc : G'.degree x ≤ G.degree x.1 := by
        rw [← G'.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree,
          ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
        exact Finset.card_le_card (hsub x)
      exact hc.trans (hdeg x.1)
    let x₀ : V' := ⟨u', huu'.ne.symm⟩
    have hx₀_deg : G'.degree x₀ ≤ 1 := by
      have hunot : u ∉ (G'.neighborFinset x₀).map ⟨Subtype.val, Subtype.val_injective⟩ := by
        intro h
        rw [Finset.mem_map] at h
        obtain ⟨z, _, hzu⟩ := h
        exact z.2 hzu
      have hins :
          insert u ((G'.neighborFinset x₀).map ⟨Subtype.val, Subtype.val_injective⟩) ⊆
            G.neighborFinset u' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with hyu | hy'
        · rw [hyu]
          exact (G.mem_neighborFinset u' u).mpr huu'.symm
        · exact hsub x₀ hy'
      have hc := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem hunot, Finset.card_map,
        G'.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hc
      have := hdeg u'
      omega
    obtain ⟨φ', hφ0⟩ := ih G' hG' hV' hdeg' x₀ hx₀_deg
    let toF : V → Fin (m + 2) := fun v => if hv : v = u then 0 else (φ' ⟨v, hv⟩).succ
    let invF : Fin (m + 2) → V := Fin.cases u (fun j => (φ'.symm j).val)
    have hleft : Function.LeftInverse invF toF := by
      intro v
      dsimp only [toF, invF]
      by_cases hv : v = u
      · subst hv; simp only [↓reduceDIte, Fin.cases_zero]
      · rw [dif_neg hv]; simp only [Fin.cases_succ, RelIso.symm_apply_apply]
    have hright : Function.RightInverse invF toF := by
      intro i
      dsimp only [toF, invF]
      induction i using Fin.cases with
      | zero => simp only [Fin.cases_zero, ↓reduceDIte]
      | succ j =>
        have hne : (φ'.symm j).val ≠ u := (φ'.symm j).2
        simp only [Fin.cases_succ, dif_neg hne, Subtype.coe_eta, RelIso.apply_symm_apply]
    refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩, ?_⟩
    · intro a b
      dsimp only [Equiv.coe_fn_mk, toF]
      by_cases ha : a = u <;> by_cases hb : b = u
      · subst ha; subst hb; simp only [SimpleGraph.irrefl]
      · subst ha
        rw [dif_pos rfl, dif_neg hb, r2_pathGraph_adj_iff]
        constructor
        · intro hadj
          have h0 : φ' ⟨b, hb⟩ = 0 := by
            simp only [Fin.val_zero, Fin.val_succ] at hadj
            apply Fin.ext
            simp only [Fin.val_zero]
            omega
          have hbu : b = u' := congrArg Subtype.val (φ'.injective (h0.trans hφ0.symm))
          subst hbu; exact huu'
        · intro hadj
          have hbu : b = u' := hu'_uniq b hadj
          have h0 : φ' ⟨b, hb⟩ = 0 := (congrArg φ' (Subtype.ext hbu)).trans hφ0
          rw [h0]; left; simp only [Fin.val_zero, Fin.val_succ, zero_add]
      · subst hb
        rw [dif_neg ha, dif_pos rfl, r2_pathGraph_adj_iff]
        constructor
        · intro hadj
          have h0 : φ' ⟨a, ha⟩ = 0 := by
            simp only [Fin.val_zero, Fin.val_succ] at hadj
            apply Fin.ext
            simp only [Fin.val_zero]
            omega
          have hau : a = u' := congrArg Subtype.val (φ'.injective (h0.trans hφ0.symm))
          subst hau; exact huu'.symm
        · intro hadj
          have hau : a = u' := hu'_uniq a hadj.symm
          have h0 : φ' ⟨a, ha⟩ = 0 := (congrArg φ' (Subtype.ext hau)).trans hφ0
          rw [h0]; right; simp only [Fin.val_zero, Fin.val_succ, zero_add]
      · rw [dif_neg ha, dif_neg hb]
        have hstep : (pathGraph (m + 2)).Adj (φ' ⟨a, ha⟩).succ (φ' ⟨b, hb⟩).succ ↔
            (pathGraph (m + 1)).Adj (φ' ⟨a, ha⟩) (φ' ⟨b, hb⟩) := by
          simp only [r2_pathGraph_adj_iff, Fin.val_succ]
          omega
        exact hstep.trans (φ'.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩))
    · dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk, toF]
      exact dif_pos rfl

private lemma r2_tree_deg_le_two_iso_path {k : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin k))
    (hG : G.IsTree) (hdeg : G.maxDegree ≤ 2) :
    Nonempty (G ≃g pathGraph k) := by
  have hnt : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨u, hu⟩ := hG.exists_vert_degree_one_of_nontrivial
  have hdeg' : ∀ v : Fin k, G.degree v ≤ 2 := fun v => (G.degree_le_maxDegree v).trans hdeg
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨φ, _⟩ := r2_tree_deg_le_two_iso_path_from_end m G hG (Fintype.card_fin _) hdeg' u (by omega)
  exact ⟨φ⟩

private lemma bounded_degree_le_two (d : ℕ) (hd : d ≤ 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ (T k).maxDegree ≤ d) →
        Erdos743.IsPacking n (Set.Icc 2 n) T := by
  refine ⟨0, fun n _ T hT => ?_⟩
  let zig : (k : Set.Icc 2 n) → Fin k → Fin n := fun k t =>
    have hkn : (k : ℕ) ≤ n := k.2.2
    if t.val % 2 = 0 then ⟨(k.1 - 1) - t.val / 2, by omega⟩
    else ⟨t.val / 2, by omega⟩
  have hzig_inj : ∀ k : Set.Icc 2 n, Function.Injective (zig k) := by
    intro k x y h
    simp only [zig] at h
    split_ifs at h with hx hy
    · exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
    · exfalso; have := congrArg Fin.val h; dsimp at this; omega
    · exfalso; have := congrArg Fin.val h; dsimp at this; omega
    · exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
  have hzig_sum : ∀ (k : Set.Icc 2 n) (u v : Fin n),
      ((pathGraph k).map (zig k)).Adj u v →
        u.val + v.val = k.1 - 2 ∨ u.val + v.val = k.1 - 1 := by
    rintro k u v ⟨_, a, b, hab, rfl, rfl⟩
    rw [r2_pathGraph_adj_iff] at hab
    have hk2 : 2 ≤ (k : ℕ) := k.2.1
    rcases hab with h1 | h1 <;>
    · simp only [zig]
      split_ifs with ha hb <;> dsimp <;> omega
  have hiso : ∀ k : Set.Icc 2 n, Nonempty (T k ≃g pathGraph k) := fun k =>
    r2_tree_deg_le_two_iso_path k.2.1 (T k) (hT k k.2).1 ((hT k k.2).2.trans hd)
  let f : (k : Set.Icc 2 n) → Fin k → Fin n := fun k =>
    if (k : ℕ) % 2 = 0 then
      zig k ∘ (hiso k).some
    else
      Fin.rev ∘ zig k ∘ (hiso k).some
  refine ⟨f, ?_, ?_⟩
  · intro k
    dsimp only [f]
    split_ifs
    · exact (hzig_inj k).comp (hiso k).some.injective
    · exact Fin.rev_injective.comp ((hzig_inj k).comp (hiso k).some.injective)
  · intro k l hkl
    rw [Set.disjoint_left]
    intro e hek hel
    induction e using Sym2.ind with
    | _ u v =>
      change ((T k).map (f k)).Adj u v at hek
      change ((T l).map (f l)).Adj u v at hel
      have hsum : ∀ (m : Set.Icc 2 n) (u v : Fin n), ((T m).map (f m)).Adj u v →
          if (m : ℕ) % 2 = 0 then
            u.val + v.val = m.1 - 2 ∨ u.val + v.val = m.1 - 1
          else
            u.val + v.val = 2 * n - 1 - m.1 ∨ u.val + v.val = 2 * n - m.1 := by
        rintro m u v ⟨huv, a, b, hab, rfl, rfl⟩
        dsimp only [f]
        split_ifs with hm
        · have hadj : ((pathGraph m).map (zig m)).Adj (zig m ((hiso m).some a))
              (zig m ((hiso m).some b)) :=
            ⟨by simpa [f, hm] using huv, (hiso m).some a, (hiso m).some b,
              (hiso m).some.map_rel_iff.mpr hab, rfl, rfl⟩
          simpa [f, hm] using hzig_sum m _ _ hadj
        · have huv' : zig m ((hiso m).some a) ≠ zig m ((hiso m).some b) := by
            intro heq
            exact huv (by simpa [f, hm] using congrArg Fin.rev heq)
          have hadj : ((pathGraph m).map (zig m)).Adj (zig m ((hiso m).some a))
              (zig m ((hiso m).some b)) :=
            ⟨huv', (hiso m).some a, (hiso m).some b,
              (hiso m).some.map_rel_iff.mpr hab, rfl, rfl⟩
          have hs := hzig_sum m _ _ hadj
          have hm2 : 2 ≤ (m : ℕ) := m.2.1
          have hmn : (m : ℕ) ≤ n := m.2.2
          simp only [Function.comp_apply, Fin.val_rev]
          omega
      have hk_sum := hsum k u v hek
      have hl_sum := hsum l u v hel
      have hk2 : 2 ≤ (k : ℕ) := k.2.1
      have hkn : (k : ℕ) ≤ n := k.2.2
      have hl2 : 2 ≤ (l : ℕ) := l.2.1
      have hln : (l : ℕ) ≤ n := l.2.2
      split_ifs at hk_sum hl_sum with hke hle <;> omega

-- ============================================================================
-- MODULE 2: Krivelevich leaf-vs-bare-path dichotomy on middle band [n/4, n/2]
-- ============================================================================

/-!
# Krivelevich Leaf-vs-Bare-Path Dichotomy and Middle-Band Density

Self-contained lemmas for `Erdos743.erdos_743.variants.bounded_degree.R2`:
1. Tree degree accounting (`|B| ≤ 2 * L` and `∑ v ∈ B, deg v ≤ 4 * L`).
2. Bare-path extraction (`12 * r + 24 * L ≤ k → ∃ r` vertex-disjoint 12-bare-paths).
3. Middle-band dichotomy and density bounds on `M = Finset.Icc ((n + 3) / 4) (n / 2)`.
-/

/-- Part 1: Degree accounting for a tree on `Fin k` (`k ≥ 2`).
Let `L` be the number of leaves and `B` the set of vertices of degree `≠ 2`.
Then `B.card ≤ 2 * L` and `∑ v ∈ B, G.degree v ≤ 4 * L`. -/
private lemma tree_degree_accounting {k : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin k))
    (hT : G.IsTree) :
    let L := (Finset.univ.filter (fun v : Fin k => G.degree v = 1)).card
    let B := Finset.univ.filter (fun v : Fin k => G.degree v ≠ 2)
    B.card ≤ 2 * L ∧ ∑ v ∈ B, G.degree v ≤ 4 * L := by
  intro L B
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  have hmin : G.minDegree = 1 := hT.minDegree_eq_one_of_nontrivial
  have hdeg_pos : ∀ v : Fin k, 1 ≤ G.degree v := fun v => by
    rw [← hmin]
    exact G.minDegree_le_degree v
  have hedge : G.edgeFinset.card + 1 = k := by
    simpa only [Fintype.card_fin] using hT.card_edgeFinset
  have hsum_all : ∑ v : Fin k, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hsum_tot : ∑ v : Fin k, G.degree v + 2 = 2 * k := by omega
  let D2 := Finset.univ.filter (fun v : Fin k => G.degree v = 2)
  have hdisj_BD2 : Disjoint B D2 := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    exact h1 h2
  have hunion_BD2 : B ∪ D2 = Finset.univ := by
    ext v
    simp only [B, D2, mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact em' _
  have hcard_BD2 : B.card + D2.card = k := by
    rw [← Finset.card_union_of_disjoint hdisj_BD2, hunion_BD2, Finset.card_univ, Fintype.card_fin]
  have hsum_D2 : ∑ v ∈ D2, G.degree v = 2 * D2.card := by
    calc
      ∑ v ∈ D2, G.degree v = ∑ _v ∈ D2, 2 :=
        Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = 2 * D2.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum_split : ∑ v ∈ B, G.degree v + ∑ v ∈ D2, G.degree v = ∑ v : Fin k, G.degree v := by
    rw [← Finset.sum_union hdisj_BD2, hunion_BD2]
  have hsum_B_eq : ∑ v ∈ B, G.degree v + 2 = 2 * B.card := by omega
  let B1 := Finset.univ.filter (fun v : Fin k => G.degree v = 1)
  let B3 := Finset.univ.filter (fun v : Fin k => 3 ≤ G.degree v)
  have hdisj_13 : Disjoint B1 B3 := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h3
    omega
  have hunion_13 : B1 ∪ B3 = B := by
    ext v
    simp only [B, B1, B3, mem_union, mem_filter, mem_univ, true_and]
    have := hdeg_pos v
    omega
  have hcard_B : B.card = L + B3.card := by
    rw [← hunion_13, Finset.card_union_of_disjoint hdisj_13]
  have hsum_B1 : ∑ v ∈ B1, G.degree v = L := by
    calc
      ∑ v ∈ B1, G.degree v = ∑ _v ∈ B1, 1 :=
        Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = L := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hsum_B3 : 3 * B3.card ≤ ∑ v ∈ B3, G.degree v := by
    calc
      3 * B3.card = ∑ _v ∈ B3, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ B3, G.degree v :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
  have hsum_B_split : ∑ v ∈ B, G.degree v = L + ∑ v ∈ B3, G.degree v := by
    rw [← hunion_13, Finset.sum_union hdisj_13, hsum_B1]
  have hB3_le : B3.card + 2 ≤ L := by omega
  constructor <;> omega

/-- Part 2: Bare-path extraction for a tree on `Fin k` (`k ≥ 2`).
If `12 * r + 24 * L ≤ k`, then `G` contains `r` vertex-disjoint paths of `12` vertices
all having degree `2` in `G`. -/
private lemma tree_extract_bare_paths {k r : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin k))
    (hT : G.IsTree)
    (hbound : 12 * r + 24 * (Finset.univ.filter (fun v : Fin k => G.degree v = 1)).card ≤ k) :
    ∃ f : Fin r × Fin 12 → Fin k,
      Function.Injective f ∧
      (∀ i (j : Fin 11), G.Adj (f (i, j.castSucc)) (f (i, j.succ))) ∧
      (∀ i j, G.degree (f (i, j)) = 2) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨root, hroot_deg⟩ := hT.exists_vert_degree_one_of_nontrivial
  let B := Finset.univ.filter (fun v : Fin k => G.degree v ≠ 2)
  let D2 := Finset.univ.filter (fun v : Fin k => G.degree v = 2)
  have hB_le : B.card ≤ 2 * (Finset.univ.filter (fun v : Fin k => G.degree v = 1)).card :=
    (tree_degree_accounting hk G hT).1
  choose p hp hp_uniq using (fun v : Fin k => hT.existsUnique_path v root)
  let par : Fin k → Fin k := fun v => (p v).snd
  have hp_root : p root = Walk.nil := (hp_uniq root Walk.nil Walk.IsPath.nil).symm
  have hpar_adj : ∀ v : Fin k, v ≠ root → G.Adj v (par v) := fun v hv =>
    (p v).adj_snd (Walk.not_nil_of_ne hv)
  have hp_cons : ∀ (v : Fin k) (hv : v ≠ root),
      p v = Walk.cons (hpar_adj v hv) (p (par v)) := by
    intro v hv
    have hnil : ¬ (p v).Nil := Walk.not_nil_of_ne hv
    have htail_eq : Walk.cons ((p v).adj_snd hnil) (p v).tail = p v :=
      (p v).cons_tail_eq hnil
    have htail_path : (p v).tail.IsPath := by
      have h1 : (Walk.cons ((p v).adj_snd hnil) (p v).tail).IsPath := by
        rw [htail_eq]
        exact hp v
      exact (Walk.cons_isPath_iff _ _).mp h1 |>.1
    have htail_p : (p v).tail = p (par v) := hp_uniq (par v) (p v).tail htail_path
    rw [← htail_eq, htail_p]
  have hpar_len : ∀ v : Fin k, v ≠ root → (p v).length = (p (par v)).length + 1 := by
    intro v hv
    conv_lhs => rw [hp_cons v hv]
    simp only [Walk.length_cons]
  have hadj_other : ∀ {v u : Fin k}, G.Adj v u → u ≠ par v →
      u ≠ root ∧ par u = v ∧ (p u).length = (p v).length + 1 := by
    intro v u hadj hne
    have hu_not : u ∉ (p v).support := by
      intro hmem
      exact hne (hT.isAcyclic.eq_snd_of_adj_start (hp v) hadj hmem)
    have hq_path : (Walk.cons hadj.symm (p v)).IsPath :=
      (Walk.cons_isPath_iff hadj.symm (p v)).mpr ⟨hp v, hu_not⟩
    have hpu : p u = Walk.cons hadj.symm (p v) :=
      (hp_uniq u (Walk.cons hadj.symm (p v)) hq_path).symm
    have hu_ne : u ≠ root := by
      intro hEq
      have hlen : (p u).length = 0 := by rw [hEq, hp_root]; rfl
      rw [hpu] at hlen
      simp only [Walk.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hlen
    refine ⟨hu_ne, ?_, ?_⟩
    · simp only [par, hpu, Walk.snd_cons]
    · simp only [hpu, Walk.length_cons]
  -- Define child function on D2 (the unique neighbor of v other than par v)
  have hex_ch : ∀ v : Fin k, v ∈ D2 → ∃ u : Fin k, G.Adj v u ∧ u ≠ par v := by
    intro v hv
    have hv_deg : G.degree v = 2 := (Finset.mem_filter.mp hv).2
    have hv_ne : v ≠ root := by
      intro h; rw [h] at hv_deg; omega
    have hpar_mem : par v ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hpar_adj v hv_ne
    have hcard_erase : ((G.neighborFinset v).erase (par v)).card = 1 := by
      rw [Finset.card_erase_of_mem hpar_mem, SimpleGraph.card_neighborFinset_eq_degree, hv_deg]
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset v).erase (par v)).card)
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hu
    exact ⟨u, hu.2, hu.1⟩
  let ch : Fin k → Fin k := fun v =>
    if hv : v ∈ D2 then Classical.choose (hex_ch v hv) else root
  have hch_spec : ∀ {v : Fin k}, v ∈ D2 → G.Adj v (ch v) ∧ ch v ≠ par v := by
    intro v hv
    simp only [ch, dif_pos hv]
    exact Classical.choose_spec (hex_ch v hv)
  have hch_par : ∀ {v : Fin k}, v ∈ D2 → ch v ≠ root ∧ par (ch v) = v := by
    intro v hv
    have hs := hch_spec hv
    have ho := hadj_other hs.1 hs.2
    exact ⟨ho.1, ho.2.1⟩
  have hch_inj : ∀ {v₁ v₂ : Fin k}, v₁ ∈ D2 → v₂ ∈ D2 → ch v₁ = ch v₂ → v₁ = v₂ := by
    intro v₁ v₂ hv₁ hv₂ heq
    have h1 := (hch_par hv₁).2
    have h2 := (hch_par hv₂).2
    rw [← h1, heq, h2]
  have hpar_inj_D2 : ∀ {w₁ w₂ : Fin k}, w₁ ≠ root → w₂ ≠ root →
      par w₁ = par w₂ → par w₁ ∈ D2 → w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₂ heq hyD2
    let y := par w₁
    have hy_deg : G.degree y = 2 := (Finset.mem_filter.mp hyD2).2
    have hy_ne : y ≠ root := by
      intro h
      rw [h] at hy_deg
      omega
    have hadj1 : G.Adj y w₁ := (hpar_adj w₁ hw₁).symm
    have hadj2 : G.Adj y w₂ := by
      have h2 := (hpar_adj w₂ hw₂).symm
      rwa [← heq] at h2
    have hne1 : w₁ ≠ par y := by
      intro h
      have hl1 : (p w₁).length = (p y).length + 1 := hpar_len w₁ hw₁
      have hl2 : (p y).length = (p (par y)).length + 1 := hpar_len y hy_ne
      rw [h] at hl1
      omega
    have hne2 : w₂ ≠ par y := by
      intro h
      have hl1 : (p w₂).length = (p y).length + 1 := by
        have h2 := hpar_len w₂ hw₂
        rwa [← heq] at h2
      have hl2 : (p y).length = (p (par y)).length + 1 := hpar_len y hy_ne
      rw [h] at hl1
      omega
    have hmem1 : w₁ ∈ (G.neighborFinset y).erase (par y) := by
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hne1, hadj1⟩
    have hmem2 : w₂ ∈ (G.neighborFinset y).erase (par y) := by
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hne2, hadj2⟩
    have hpar_mem : par y ∈ G.neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hpar_adj y hy_ne
    have hcard_one : ((G.neighborFinset y).erase (par y)).card = 1 := by
      rw [Finset.card_erase_of_mem hpar_mem, SimpleGraph.card_neighborFinset_eq_degree, hy_deg]
    exact Finset.card_le_one.mp (le_of_eq hcard_one) w₁ hmem1 w₂ hmem2
  -- Define upward D2-chain length `d v` using `List.takeWhile` on `(p v).support.tail`
  let d : Fin k → ℕ := fun v =>
    ((p v).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length
  have hsupp_cons : ∀ {a b : Fin k} (w : G.Walk a b), w.support = a :: w.support.tail := by
    intro a b w
    cases w <;> rfl
  have hd_step : ∀ {v : Fin k}, v ∈ D2 →
      (par v ∈ D2 → d v = d (par v) + 1) ∧ (par v ∉ D2 → d v = 0) := by
    intro v hv
    have hv_ne : v ≠ root := by
      intro h
      have hdeg := (Finset.mem_filter.mp hv).2
      rw [h] at hdeg
      omega
    have hsupp : (p v).support.tail = (p (par v)).support := by
      conv_lhs => rw [hp_cons v hv_ne]
      simp only [Walk.support_cons, List.tail_cons]
    constructor
    · intro hparD2
      have hdeg : G.degree (par v) = 2 := (Finset.mem_filter.mp hparD2).2
      change ((p v).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length =
        ((p (par v)).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length + 1
      rw [hsupp, hsupp_cons (p (par v)), List.takeWhile_cons]
      simp only [hdeg, decide_true, ↓reduceIte, List.length_cons, List.tail_cons]
    · intro hparND2
      have hdeg : G.degree (par v) ≠ 2 := fun h =>
        hparND2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      change ((p v).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length = 0
      rw [hsupp, hsupp_cons (p (par v)), List.takeWhile_cons]
      simp only [hdeg, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_nil]
  -- Define Bot := {v ∈ D2 | ch v ∈ B}
  let Bot := D2.filter (fun v => ch v ∈ B)
  have hBot_le : Bot.card ≤ B.card := by
    have hmaps : ∀ v ∈ Bot, ch v ∈ B := fun v hv => (Finset.mem_filter.mp hv).2
    have hinj : Set.InjOn ch (Bot : Set (Fin k)) := by
      intro v₁ hv₁ v₂ hv₂ heq
      rw [Finset.mem_coe] at hv₁ hv₂
      exact hch_inj (Finset.mem_filter.mp hv₁).1 (Finset.mem_filter.mp hv₂).1 heq
    exact Finset.card_le_card_of_injOn ch hmaps hinj
  -- Residue classes C t := {v ∈ D2 | d v % 12 = t}
  let C : ℕ → Finset (Fin k) := fun t => D2.filter (fun v => d v % 12 = t)
  have hC_step : ∀ t < 11, (C t).card ≤ (C (t + 1)).card + (C t ∩ Bot).card := by
    intro t ht
    have hsplit : (C t).card = (C t \ Bot).card + (C t ∩ Bot).card := by
      rw [add_comm, Finset.card_inter_add_card_sdiff]
    rw [hsplit]
    have hle : (C t \ Bot).card ≤ (C (t + 1)).card := by
      refine Finset.card_le_card_of_injOn ch ?_ ?_
      · intro v hv
        rw [Finset.mem_coe, Finset.mem_sdiff] at hv
        rw [Finset.mem_coe]
        have hvD2 : v ∈ D2 := (Finset.mem_filter.mp hv.1).1
        have hmod : d v % 12 = t := (Finset.mem_filter.mp hv.1).2
        have hch_notB : ch v ∉ B := by
          intro hB
          exact hv.2 (Finset.mem_filter.mpr ⟨hvD2, hB⟩)
        have hchD2 : ch v ∈ D2 := by
          simp only [B, mem_filter, mem_univ, true_and, not_not] at hch_notB
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hch_notB⟩
        have hpar_ch : par (ch v) = v := (hch_par hvD2).2
        have hd_ch : d (ch v) = d v + 1 := by
          have := (hd_step hchD2).1
          rw [hpar_ch] at this
          exact this hvD2
        refine Finset.mem_filter.mpr ⟨hchD2, ?_⟩
        rw [hd_ch]
        omega
      · intro v₁ hv₁ v₂ hv₂ heq
        rw [Finset.mem_coe, Finset.mem_sdiff] at hv₁ hv₂
        exact hch_inj (Finset.mem_filter.mp hv₁.1).1 (Finset.mem_filter.mp hv₂.1).1 heq
    omega
  have hC_chain : ∀ t ≤ 11, (C t).card ≤ (C 11).card + ∑ s ∈ Finset.Ico t 11, (C s ∩ Bot).card := by
    intro t ht
    have haux : ∀ m, m ≤ 11 →
        (C (11 - m)).card ≤ (C 11).card + ∑ s ∈ Finset.Ico (11 - m) 11, (C s ∩ Bot).card := by
      intro m
      induction m with
      | zero =>
        intro _
        simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty, add_zero, le_refl]
      | succ m ih =>
        intro hm
        have hm1 : 11 - (m + 1) < 11 := by omega
        have hm2 : 11 - (m + 1) + 1 = 11 - m := by omega
        have hstep := hC_step (11 - (m + 1)) hm1
        rw [hm2] at hstep
        have hih := ih (by omega)
        have hico : Finset.Ico (11 - (m + 1)) 11 =
            insert (11 - (m + 1)) (Finset.Ico (11 - m) 11) := by
          ext x
          simp only [mem_Ico, mem_insert]
          omega
        have hsum_ico :
            ∑ s ∈ Finset.Ico (11 - (m + 1)) 11, (C s ∩ Bot).card =
            (C (11 - (m + 1)) ∩ Bot).card + ∑ s ∈ Finset.Ico (11 - m) 11, (C s ∩ Bot).card := by
          rw [hico, Finset.sum_insert (by simp only [mem_Ico]; omega)]
        omega
    have := haux (11 - t) (by omega)
    have hsub : 11 - (11 - t) = t := by omega
    rwa [hsub] at this
  have hsum_Bot : ∑ s ∈ Finset.range 12, (C s ∩ Bot).card = Bot.card := by
    have hdisj : Set.PairwiseDisjoint (Finset.range 12 : Set ℕ) (fun s => C s ∩ Bot) := by
      intro s₁ _ s₂ _ hne
      show Disjoint (C s₁ ∩ Bot) (C s₂ ∩ Bot)
      rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      rw [Finset.mem_inter] at hv₁ hv₂
      have h1 := (Finset.mem_filter.mp hv₁.1).2
      have h2 := (Finset.mem_filter.mp hv₂.1).2
      omega
    rw [← Finset.card_biUnion hdisj]
    apply congrArg Finset.card
    ext v
    simp only [mem_biUnion, mem_range, mem_inter, C, mem_filter]
    constructor
    · rintro ⟨_, _, _, hv⟩; exact hv
    · intro hv
      exact ⟨d v % 12, Nat.mod_lt _ (by omega), ⟨(Finset.mem_filter.mp hv).1, rfl⟩, hv⟩
  have hC_le_11 : ∀ t ∈ Finset.range 11, (C t).card ≤ (C 11).card + Bot.card := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 := hC_chain t (by omega)
    have hsub : Finset.Ico t 11 ⊆ Finset.range 12 := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      rw [Finset.mem_range]
      omega
    have h2 : ∑ s ∈ Finset.Ico t 11, (C s ∩ Bot).card ≤ ∑ s ∈ Finset.range 12, (C s ∩ Bot).card :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hD2_sum : D2.card = ∑ t ∈ Finset.range 12, (C t).card := by
    have hdisj : Set.PairwiseDisjoint (Finset.range 12 : Set ℕ) C := by
      intro s₁ _ s₂ _ hne
      show Disjoint (C s₁) (C s₂)
      rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      have h1 := (Finset.mem_filter.mp hv₁).2
      have h2 := (Finset.mem_filter.mp hv₂).2
      omega
    rw [← Finset.card_biUnion hdisj]
    apply congrArg Finset.card
    ext v
    simp only [mem_biUnion, mem_range, C, mem_filter]
    constructor
    · intro hv; exact ⟨d v % 12, Nat.mod_lt _ (by omega), hv, rfl⟩
    · rintro ⟨_, _, hv, _⟩; exact hv
  have hD2_bound : D2.card ≤ 12 * (C 11).card + 11 * Bot.card := by
    rw [hD2_sum, Finset.sum_range_succ]
    have hsum11 : ∑ t ∈ Finset.range 11, (C t).card ≤ ∑ _t ∈ Finset.range 11, ((C 11).card + Bot.card) :=
      Finset.sum_le_sum hC_le_11
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum11
    omega
  have hcard_BD2 : B.card + D2.card = k := by
    have hdisj : Disjoint B D2 := by
      rw [Finset.disjoint_filter]
      intro v _ h1 h2; exact h1 h2
    have hunion : B ∪ D2 = Finset.univ := by
      ext v
      simp only [B, D2, mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact em' _
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hr_le : r ≤ (C 11).card := by omega
  -- Construct the r disjoint 12-bare-paths by walking UP from elements of C 11 via `par`
  have hiter_props : ∀ (v : Fin k), v ∈ D2 → ∀ j ≤ d v,
      par^[j] v ∈ D2 ∧ d (par^[j] v) = d v - j := by
    intro v hv j
    induction j with
    | zero =>
      intro _
      simp only [Function.iterate_zero, id_eq, Nat.sub_zero, hv, and_self]
    | succ j ih =>
      intro hj
      obtain ⟨hxD2, hdx⟩ := ih (by omega)
      have hparD2 : par (par^[j] v) ∈ D2 := by
        by_contra hnot
        have h0 := (hd_step hxD2).2 hnot
        omega
      have hdp := (hd_step hxD2).1 hparD2
      rw [Function.iterate_succ_apply']
      exact ⟨hparD2, by omega⟩
  have hiter_inj : ∀ (m : ℕ) (x₁ x₂ : Fin k), x₁ ∈ D2 → x₂ ∈ D2 →
      m ≤ d x₁ → m ≤ d x₂ → par^[m] x₁ = par^[m] x₂ → x₁ = x₂ := by
    intro m
    induction m with
    | zero =>
      intro x₁ x₂ _ _ _ _ h
      simpa only [Function.iterate_zero, id_eq] using h
    | succ m ih =>
      intro x₁ x₂ hx₁ hx₂ hm₁ hm₂ h
      have hpx₁_D2 : par x₁ ∈ D2 := by
        by_contra hnot
        have h0 := (hd_step hx₁).2 hnot
        omega
      have hpx₂_D2 : par x₂ ∈ D2 := by
        by_contra hnot
        have h0 := (hd_step hx₂).2 hnot
        omega
      have hdx₁ := (hd_step hx₁).1 hpx₁_D2
      have hdx₂ := (hd_step hx₂).1 hpx₂_D2
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      have hpar_eq : par x₁ = par x₂ := ih (par x₁) (par x₂) hpx₁_D2 hpx₂_D2 (by omega) (by omega) h
      have hx₁_ne : x₁ ≠ root := by
        intro heq; have hdeg := (Finset.mem_filter.mp hx₁).2; rw [heq] at hdeg; omega
      have hx₂_ne : x₂ ≠ root := by
        intro heq; have hdeg := (Finset.mem_filter.mp hx₂).2; rw [heq] at hdeg; omega
      exact hpar_inj_D2 hx₁_ne hx₂_ne hpar_eq hpx₁_D2
  -- Pick an injection e : Fin r → Fin k with image in C 11
  let e_equiv := (C 11).equivFin.symm
  let e : Fin r → Fin k := fun i => (e_equiv ⟨i.val, lt_of_lt_of_le i.isLt hr_le⟩).val
  have he_mem : ∀ i : Fin r, e i ∈ C 11 := fun i =>
    (e_equiv ⟨i.val, lt_of_lt_of_le i.isLt hr_le⟩).property
  have he_inj : Function.Injective e := by
    intro i₁ i₂ h
    have hsub : e_equiv ⟨i₁.val, lt_of_lt_of_le i₁.isLt hr_le⟩ =
        e_equiv ⟨i₂.val, lt_of_lt_of_le i₂.isLt hr_le⟩ := Subtype.ext h
    have hfin := e_equiv.injective hsub
    exact Fin.ext (congrArg (fun x : Fin (C 11).card => x.val) hfin)
  refine ⟨fun p => par^[p.2.val] (e p.1), ?_, ?_, ?_⟩
  · -- Injectivity
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    dsimp only at h
    have h1D2 : e i₁ ∈ D2 := (Finset.mem_filter.mp (he_mem i₁)).1
    have h2D2 : e i₂ ∈ D2 := (Finset.mem_filter.mp (he_mem i₂)).1
    have h1mod : d (e i₁) % 12 = 11 := (Finset.mem_filter.mp (he_mem i₁)).2
    have h2mod : d (e i₂) % 12 = 11 := (Finset.mem_filter.mp (he_mem i₂)).2
    have h1ge : 11 ≤ d (e i₁) := by omega
    have h2ge : 11 ≤ d (e i₂) := by omega
    have hd1 := (hiter_props (e i₁) h1D2 j₁.val (by omega)).2
    have hd2 := (hiter_props (e i₂) h2D2 j₂.val (by omega)).2
    have hdeq : d (e i₁) - j₁.val = d (e i₂) - j₂.val := by
      rw [← hd1, h, hd2]
    have hj_eq : j₁ = j₂ := by
      apply Fin.ext
      have hj1 : j₁.val < 12 := j₁.isLt
      have hj2 : j₂.val < 12 := j₂.isLt
      omega
    subst hj_eq
    have hi_eq : e i₁ = e i₂ :=
      hiter_inj j₁.val (e i₁) (e i₂) h1D2 h2D2 (by omega) (by omega) h
    exact Prod.ext (he_inj hi_eq) rfl
  · -- Adjacency
    intro i j
    have hiD2 : e i ∈ D2 := (Finset.mem_filter.mp (he_mem i)).1
    have himod : d (e i) % 12 = 11 := (Finset.mem_filter.mp (he_mem i)).2
    have hjD2 : par^[j.val] (e i) ∈ D2 :=
      (hiter_props (e i) hiD2 j.val (by omega)).1
    have hj_ne : par^[j.val] (e i) ≠ root := by
      intro heq
      have hdeg := (Finset.mem_filter.mp hjD2).2
      rw [heq] at hdeg
      omega
    change G.Adj (par^[j.val] (e i)) (par^[j.val + 1] (e i))
    rw [Function.iterate_succ_apply']
    exact hpar_adj (par^[j.val] (e i)) hj_ne
  · -- Degree 2
    intro i j
    have hiD2 : e i ∈ D2 := (Finset.mem_filter.mp (he_mem i)).1
    have himod : d (e i) % 12 = 11 := (Finset.mem_filter.mp (he_mem i)).2
    have hjD2 : par^[j.val] (e i) ∈ D2 :=
      (hiter_props (e i) hiD2 j.val (by omega)).1
    exact (Finset.mem_filter.mp hjD2).2

/-- Part 3: Middle-band dichotomy and density bounds.
For all `n ≥ 10000` and any family of trees `T k` (`2 ≤ k ≤ n`), there exists a subset `I`
of the middle band `M = Finset.Icc ((n + 3) / 4) (n / 2)` of cardinality `n / 16` whose
edge count `eI = ∑ k ∈ I, (k - 1)` satisfies `p := eI / C(n, 2) ∈ [1/40, 1/10]`, such that
either every tree in `I` has at least `n / 210` leaves, or every tree in `I` has fewer than
`k / 52` leaves and admits `n / 100` vertex-disjoint 12-bare-paths. -/
private lemma middle_band_dichotomy {n : ℕ} (hn : 10000 ≤ n)
    (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree) :
    ∃ I : Finset ℕ,
      I ⊆ Finset.Icc ((n + 3) / 4) (n / 2) ∧
      I.card = n / 16 ∧
      n / 20 ≤ I.card ∧
      7 * n / 8 ≤ (Finset.Icc 2 n \ I).card ∧
      (1 / 40 : ℝ) ≤ ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ) ∧
      ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ) ≤ (1 / 10 : ℝ) ∧
      ((∀ k ∈ I, n / 210 ≤ (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card) ∨
       (∀ k ∈ I,
          (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card < k / 52 ∧
          ∃ g : Fin (n / 100) × Fin 12 → Fin k,
            Function.Injective g ∧
            (∀ i (j : Fin 11), (T k).Adj (g (i, j.castSucc)) (g (i, j.succ))) ∧
            (∀ i j, (T k).degree (g (i, j)) = 2))) := by
  let M := Finset.Icc ((n + 3) / 4) (n / 2)
  have hM_card : 2 * (n / 16) ≤ M.card := by
    simp only [M, Nat.card_Icc]
    omega
  let M_leaf := M.filter (fun k => k / 52 ≤ (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card)
  let M_bare := M.filter (fun k => (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card < k / 52)
  have hpart : M_leaf.card + M_bare.card = M.card := by
    have hdisj : Disjoint M_leaf M_bare := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2; omega
    have hunion : M_leaf ∪ M_bare = M := by
      ext k
      simp only [M_leaf, M_bare, mem_union, mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hk : k / 52 ≤ (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card
        · exact Or.inl ⟨h, hk⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- Helper proving the common cardinality and density bounds for any `I ⊆ M` with `I.card = n / 16`
  have hcommon : ∀ I : Finset ℕ, I ⊆ M → I.card = n / 16 →
      n / 20 ≤ I.card ∧
      7 * n / 8 ≤ (Finset.Icc 2 n \ I).card ∧
      (1 / 40 : ℝ) ≤ ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ) ∧
      ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ) ≤ (1 / 10 : ℝ) := by
    intro I hIM hIcard
    have hI_Icc : I ⊆ Finset.Icc 2 n := by
      intro k hk
      have hkM := Finset.mem_Icc.mp (hIM hk)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hsdiff : 7 * n / 8 ≤ (Finset.Icc 2 n \ I).card := by
      rw [Finset.card_sdiff_of_subset hI_Icc, Nat.card_Icc, hIcard]
      omega
    have hsum_lo : I.card * ((n + 3) / 4 - 1) ≤ ∑ k ∈ I, (k - 1) := by
      calc
        I.card * ((n + 3) / 4 - 1) = ∑ _k ∈ I, ((n + 3) / 4 - 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ k ∈ I, (k - 1) := Finset.sum_le_sum (fun k hk => by
            have hkM := Finset.mem_Icc.mp (hIM hk); omega)
    have hsum_hi : ∑ k ∈ I, (k - 1) ≤ I.card * (n / 2) := by
      calc
        ∑ k ∈ I, (k - 1) ≤ ∑ _k ∈ I, (n / 2) := Finset.sum_le_sum (fun k hk => by
            have hkM := Finset.mem_Icc.mp (hIM hk); omega)
        _ = I.card * (n / 2) := by rw [Finset.sum_const, smul_eq_mul]
    have hch2 : 2 * n.choose 2 = n * (n - 1) := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    have hsq : 2 * n.choose 2 + n = n * n := by
      have hn1 : (n - 1) + 1 = n := by omega
      calc
        2 * n.choose 2 + n = n * (n - 1) + n * 1 := by rw [hch2, mul_one]
        _ = n * ((n - 1) + 1) := by rw [← Nat.mul_add]
        _ = n * n := by rw [hn1]
    have hnat_lo : n.choose 2 ≤ 40 * ∑ k ∈ I, (k - 1) := by
      set a := n / 16
      set b := (n + 3) / 4 - 1
      have ha1 : n ≤ 16 * a + 15 := by omega
      have ha2 : 16 * a ≤ n := by omega
      have hb1 : n ≤ 4 * b + 4 := by omega
      have hb2 : 4 * b ≤ n := by omega
      have h3 : a * b ≤ ∑ k ∈ I, (k - 1) := by rwa [hIcard] at hsum_lo
      have hprod : n * n ≤ (16 * a + 15) * (4 * b + 4) := Nat.mul_le_mul ha1 hb1
      nlinarith
    have hnat_hi : 10 * ∑ k ∈ I, (k - 1) ≤ n.choose 2 := by
      set a := n / 16
      set c := n / 2
      have ha : 16 * a ≤ n := by omega
      have hc : 2 * c ≤ n := by omega
      have h3 : ∑ k ∈ I, (k - 1) ≤ a * c := by rwa [hIcard] at hsum_hi
      have hprod : (16 * a) * (2 * c) ≤ n * n := Nat.mul_le_mul ha hc
      nlinarith
    have hch_pos : (0 : ℝ) < (n.choose 2 : ℝ) := by
      have hpos : 0 < n.choose 2 := by nlinarith
      exact_mod_cast hpos
    have hreal_lo : (1 / 40 : ℝ) ≤ ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hch_pos]
      have : (n.choose 2 : ℝ) ≤ 40 * ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) := by exact_mod_cast hnat_lo
      linarith
    have hreal_hi : ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ) ≤ (1 / 10 : ℝ) := by
      rw [div_le_div_iff₀ hch_pos (by norm_num)]
      have : 10 * ((∑ k ∈ I, (k - 1) : ℕ) : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast hnat_hi
      linarith
    exact ⟨by omega, hsdiff, hreal_lo, hreal_hi⟩
  rcases le_or_gt (n / 16) M_leaf.card with hleaf | hbare
  · -- Leaf-rich case
    obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hleaf
    have hIM : I ⊆ M := Finset.Subset.trans hIsub (Finset.filter_subset _ _)
    obtain ⟨h1, h2, h3, h4⟩ := hcommon I hIM hIcard
    refine ⟨I, hIM, hIcard, h1, h2, h3, h4, Or.inl ?_⟩
    intro k hk
    have hk_leaf := Finset.mem_filter.mp (hIsub hk)
    have hkM := Finset.mem_Icc.mp hk_leaf.1
    have hdiv : n / 210 ≤ k / 52 := by omega
    exact le_trans hdiv hk_leaf.2
  · -- Bare-path-rich case
    have hbare_ge : n / 16 ≤ M_bare.card := by omega
    obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hbare_ge
    have hIM : I ⊆ M := Finset.Subset.trans hIsub (Finset.filter_subset _ _)
    obtain ⟨h1, h2, h3, h4⟩ := hcommon I hIM hIcard
    refine ⟨I, hIM, hIcard, h1, h2, h3, h4, Or.inr ?_⟩
    intro k hk
    have hk_bare := Finset.mem_filter.mp (hIsub hk)
    have hkM := Finset.mem_Icc.mp hk_bare.1
    have hk2 : 2 ≤ k := by omega
    have hkIcc : k ∈ Set.Icc 2 n := ⟨hk2, by omega⟩
    have hTk : (T k).IsTree := hT k hkIcc
    have hL_lt : (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card < k / 52 := hk_bare.2
    have hbound :
        12 * (n / 100) + 24 * (Finset.univ.filter (fun v : Fin k => (T k).degree v = 1)).card ≤ k := by
      omega
    exact ⟨hL_lt, tree_extract_bare_paths hk2 (T k) hTk hbound⟩

-- ============================================================================
-- MODULE 3: Probabilistic quasirandom edge-split & deterministic transfer
-- ============================================================================

/-!
# Probabilistic Quasirandom Edge-Split & Deterministic Quasirandomness Transfer

Purely finite-sum proof of:
1. `exists_quasirandom_graph`: Uniform-in-`q` existence of `(q, ε)`-quasirandom graphs on `Fin n`.
2. `compl_quasirandom`: Complement quasirandomness transfer from `G` to `Gᶜ`.
3. `quasirandom_transfer_general` & `quasirandom_transfer`: Deterministic quasirandomness transfer
   from `G₁` and `P ≤ G₁` with bounded leftover degree `G₁ \ P` to `R = Pᶜ`.
-/

/-- Finite union bound for sums of nonnegative functions. -/
private lemma sum_union_le_of_nonneg {ι : Type*} [DecidableEq ι] {s t : Finset ι} {f : ι → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg (fun x _ => hf x)
  linarith

/-- Finite `biUnion` bound for sums of nonnegative functions. -/
private lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset α) (S : α → Finset ι) {f : ι → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ I.biUnion S, f x ≤ ∑ i ∈ I, ∑ x ∈ S i, f x := by
  induction I using Finset.induction_on with
  | empty => simp only [Finset.biUnion_empty, Finset.sum_empty, le_refl]
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (sum_union_le_of_nonneg hf) (add_le_add le_rfl ih)

/-- Elementary Bernoulli MGF bound: for `p ∈ [0, 1]` and `|t| ≤ 1 / 2`,
`(1 - p) * exp (-t * p) + p * exp (t * (1 - p)) ≤ exp (t ^ 2)`. -/
private lemma bernoulli_mgf_le (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1 / 2) :
    (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) ≤ Real.exp (t ^ 2) := by
  have hexp : ∀ x : ℝ, x ≤ 1 / 2 → Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
    intro x hx
    have h1mx : 0 < 1 - x := by linarith
    have hadd : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have hmul : Real.exp x * (1 - x) ≤ 1 := by
      have hle := mul_le_mul_of_nonneg_left hadd (le_of_lt (Real.exp_pos x))
      have heq : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linarith
    have hpoly : 1 ≤ (1 + x + 2 * x ^ 2) * (1 - x) := by
      have : (1 + x + 2 * x ^ 2) * (1 - x) - 1 = x ^ 2 * (1 - 2 * x) := by ring
      have : 0 ≤ x ^ 2 * (1 - 2 * x) := mul_nonneg (sq_nonneg x) (by linarith)
      linarith
    nlinarith
  have h1 : -t * p ≤ 1 / 2 := by
    have : |-t * p| ≤ 1 / 2 := by
      rw [abs_mul, abs_neg, abs_of_nonneg hp0]
      nlinarith
    exact (abs_le.mp this).2
  have h2 : t * (1 - p) ≤ 1 / 2 := by
    have : |t * (1 - p)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - p)]
      nlinarith
    exact (abs_le.mp this).2
  have e1 := hexp (-t * p) h1
  have e2 := hexp (t * (1 - p)) h2
  have hcomb : (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) ≤
      1 + 2 * t ^ 2 * p * (1 - p) := by
    have ha := mul_le_mul_of_nonneg_left e1 (by linarith : 0 ≤ 1 - p)
    have hb := mul_le_mul_of_nonneg_left e2 hp0
    linarith
  have hle : 1 + 2 * t ^ 2 * p * (1 - p) ≤ 1 + t ^ 2 := by
    have hprod : 2 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (p - 1 / 2)]
    nlinarith [sq_nonneg t]
  linarith [Real.add_one_le_exp (t ^ 2)]

/-- Total weight of the Bernoulli(`q`) product measure on `E → Bool` is `1`. -/
private lemma sum_bernoulli_weight {E : Type*} [Fintype E] [DecidableEq E] (q : ℝ) :
    ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : E) (b : Bool) => if b then q else 1 - q)]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_sub_cancel, Finset.prod_const_one]

/-- Nonnegativity of Bernoulli(`q`) weights for `q ∈ [0, 1]`. -/
private lemma bernoulli_weight_nonneg {E : Type*} [Fintype E] (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ω : E → Bool) :
    0 ≤ ∏ e : E, if ω e then q else 1 - q := by
  apply Finset.prod_nonneg
  intro e _
  split_ifs <;> linarith

/-- Exact MGF for the number of true coordinates in a subset `A : Finset E`. -/
private lemma mgf_subset {E : Type*} [Fintype E] [DecidableEq E] (q t : ℝ) (A : Finset E) :
    ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) *
      Real.exp (t * (((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ))) =
    ((1 - q) * Real.exp (-t * q) + q * Real.exp (t * (1 - q))) ^ A.card := by
  have hterm : ∀ ω : E → Bool,
      (∏ e : E, if ω e then q else 1 - q) *
        Real.exp (t * (((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ))) =
      ∏ e : E, ((if ω e then q else 1 - q) *
        if e ∈ A then Real.exp (t * ((if ω e then (1 : ℝ) else 0) - q)) else 1) := by
    intro ω
    have hcard : ((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ) =
        ∑ e ∈ A, ((if ω e then (1 : ℝ) else 0) - q) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
      simp only [mul_comm]
    rw [hcard, Finset.mul_sum, Real.exp_sum]
    have hf : Finset.univ.filter (fun e : E => e ∈ A) = A := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (∏ e ∈ Finset.univ.filter (fun e => e ∈ A),
        ((if ω e then q else 1 - q) *
          if e ∈ A then Real.exp (t * ((if ω e then (1 : ℝ) else 0) - q)) else 1)) =
        (∏ e ∈ A, if ω e then q else 1 - q) *
        (∏ e ∈ A, Real.exp (t * ((if ω e then (1 : ℝ) else 0) - q))) := by
      rw [hf, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e he
      simp only [he, ↓reduceIte]
    have h2 : (∏ e ∈ Finset.univ.filter (fun e => e ∉ A),
        ((if ω e then q else 1 - q) *
          if e ∈ A then Real.exp (t * ((if ω e then (1 : ℝ) else 0) - q)) else 1)) =
        ∏ e ∈ Finset.univ.filter (fun e => e ∉ A), if ω e then q else 1 - q := by
      apply Finset.prod_congr rfl
      intro e he
      have hne : e ∉ A := (Finset.mem_filter.mp he).2
      simp only [hne, ↓reduceIte, mul_one]
    have hrhs : (∏ e : E, ((if ω e then q else 1 - q) *
        if e ∈ A then Real.exp (t * ((if ω e then (1 : ℝ) else 0) - q)) else 1)) =
        (∏ e ∈ A, if ω e then q else 1 - q) *
        (∏ e ∈ A, Real.exp (t * ((if ω e then (1 : ℝ) else 0) - q))) *
        (∏ e ∈ Finset.univ.filter (fun e => e ∉ A), if ω e then q else 1 - q) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e => e ∈ A), h1, h2]
    have hsplit : (∏ e : E, if ω e then q else 1 - q) =
        (∏ e ∈ A, if ω e then q else 1 - q) *
        (∏ e ∈ Finset.univ.filter (fun e => e ∉ A), if ω e then q else 1 - q) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e => e ∈ A), hf]
    rw [hrhs, hsplit]
    ring
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (e : E) (b : Bool) =>
    (if b then q else 1 - q) *
      if e ∈ A then Real.exp (t * ((if b then (1 : ℝ) else 0) - q)) else 1)]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e => e ∈ A)]
  have hf : Finset.univ.filter (fun e : E => e ∈ A) = A := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hf]
  have hA : (∏ e ∈ A, ∑ b : Bool, (if b then q else 1 - q) *
      if e ∈ A then Real.exp (t * ((if b then (1 : ℝ) else 0) - q)) else 1) =
      ((1 - q) * Real.exp (-t * q) + q * Real.exp (t * (1 - q))) ^ A.card := by
    calc (∏ e ∈ A, ∑ b : Bool, (if b then q else 1 - q) *
            if e ∈ A then Real.exp (t * ((if b then (1 : ℝ) else 0) - q)) else 1)
        = ∏ _e ∈ A, ((1 - q) * Real.exp (-t * q) + q * Real.exp (t * (1 - q))) := by
          apply Finset.prod_congr rfl
          intro e he
          simp only [Fintype.sum_bool, he, ↓reduceIte, Bool.false_eq_true]
          ring_nf
      _ = ((1 - q) * Real.exp (-t * q) + q * Real.exp (t * (1 - q))) ^ A.card := by
          rw [Finset.prod_const]
  have hAc : (∏ e ∈ Finset.univ.filter (fun e => e ∉ A), ∑ b : Bool, (if b then q else 1 - q) *
      if e ∈ A then Real.exp (t * ((if b then (1 : ℝ) else 0) - q)) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro e he
    have hne : e ∉ A := (Finset.mem_filter.mp he).2
    simp only [Fintype.sum_bool, hne, ↓reduceIte, Bool.false_eq_true, mul_one, add_sub_cancel]
  rw [hA, hAc, mul_one]

/-- Exact MGF for the number of indices `w : α` where BOTH `ω (e₁ w) = true` and `ω (e₂ w) = true`,
given pairwise disjoint pairs `(e₁ w, e₂ w)` in `E`. -/
private lemma mgf_disjoint_pairs {E α : Type*} [Fintype E] [DecidableEq E] [Fintype α] [DecidableEq α]
    (q t : ℝ) (e₁ e₂ : α → E)
    (hinj1 : Function.Injective e₁) (hinj2 : Function.Injective e₂)
    (hcross : ∀ w₁ w₂ : α, e₁ w₁ ≠ e₂ w₂) :
    ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) *
      Real.exp (t * (((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
        - q ^ 2 * (Fintype.card α : ℝ))) =
    ((1 - q ^ 2) * Real.exp (-t * q ^ 2) + q ^ 2 * Real.exp (t * (1 - q ^ 2))) ^ Fintype.card α := by
  let U : Finset E := Finset.univ.image e₁ ∪ Finset.univ.image e₂
  let toE : (α × Bool) ⊕ {e : E // e ∉ U} → E := fun x =>
    match x with
    | Sum.inl (w, true) => e₁ w
    | Sum.inl (w, false) => e₂ w
    | Sum.inr e => e.1
  have hbij : Function.Bijective toE := by
    constructor
    · intro x y hxy
      rcases x with ⟨w₁, b₁⟩ | ⟨ex, hex⟩ <;> rcases y with ⟨w₂, b₂⟩ | ⟨ey, hey⟩
      · cases b₁ <;> cases b₂
        · exact congrArg (fun w => Sum.inl (w, false)) (hinj2 hxy)
        · exact absurd hxy.symm (hcross w₂ w₁)
        · exact absurd hxy (hcross w₁ w₂)
        · exact congrArg (fun w => Sum.inl (w, true)) (hinj1 hxy)
      · cases b₁
        · dsimp [toE] at hxy
          exfalso; apply hey; rw [← hxy]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem e₂ (Finset.mem_univ w₁))
        · dsimp [toE] at hxy
          exfalso; apply hey; rw [← hxy]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem e₁ (Finset.mem_univ w₁))
      · cases b₂
        · dsimp [toE] at hxy
          exfalso; apply hex; rw [hxy]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem e₂ (Finset.mem_univ w₂))
        · dsimp [toE] at hxy
          exfalso; apply hex; rw [hxy]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem e₁ (Finset.mem_univ w₂))
      · exact congrArg Sum.inr (Subtype.ext hxy)
    · intro e
      by_cases h1 : e ∈ Finset.univ.image e₁
      · rcases Finset.mem_image.mp h1 with ⟨w, _, rfl⟩
        exact ⟨Sum.inl (w, true), rfl⟩
      · by_cases h2 : e ∈ Finset.univ.image e₂
        · rcases Finset.mem_image.mp h2 with ⟨w, _, rfl⟩
          exact ⟨Sum.inl (w, false), rfl⟩
        · have hU : e ∉ U := by
            simp only [U, Finset.mem_union, h1, h2, or_self, not_false_eq_true]
          exact ⟨Sum.inr ⟨e, hU⟩, rfl⟩
  let φ : (α × Bool) ⊕ {e : E // e ∉ U} ≃ E := Equiv.ofBijective toE hbij
  let ψ : (E → Bool) ≃ ((α → Bool → Bool) × ({e : E // e ∉ U} → Bool)) :=
    (Equiv.arrowCongr φ (Equiv.refl Bool)).symm.trans
      ((Equiv.sumArrowEquivProdArrow (α × Bool) {e : E // e ∉ U} Bool).trans
        (Equiv.prodCongr (Equiv.curry α Bool Bool) (Equiv.refl _)))
  have hprod_ω : ∀ ω : E → Bool,
      (∏ e : E, if ω e then q else 1 - q) *
        Real.exp (t * (((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
          - q ^ 2 * (Fintype.card α : ℝ))) =
      (∏ w : α, (if (ψ ω).1 w true then q else 1 - q) * (if (ψ ω).1 w false then q else 1 - q) *
        Real.exp (t * ((if (ψ ω).1 w true = true ∧ (ψ ω).1 w false = true then (1 : ℝ) else 0) - q ^ 2))) *
      (∏ r : {e : E // e ∉ U}, if (ψ ω).2 r then q else 1 - q) := by
    intro ω
    have hψ1t : ∀ w : α, (ψ ω).1 w true = ω (e₁ w) := fun _ => rfl
    have hψ1f : ∀ w : α, (ψ ω).1 w false = ω (e₂ w) := fun _ => rfl
    have hψ2 : ∀ r : {e : E // e ∉ U}, (ψ ω).2 r = ω r.1 := fun _ => rfl
    have hW : (∏ e : E, if ω e then q else 1 - q) =
        (∏ w : α, (if ω (e₁ w) then q else 1 - q) * (if ω (e₂ w) then q else 1 - q)) *
        (∏ r : {e : E // e ∉ U}, if ω r.1 then q else 1 - q) := by
      rw [← Fintype.prod_equiv φ (fun x => if ω (φ x) then q else 1 - q)
        (fun e => if ω e then q else 1 - q) (fun _ => rfl)]
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
      congr 1
      apply Finset.prod_congr rfl
      intro w _
      simp only [Fintype.prod_bool, φ, Equiv.ofBijective_apply, toE]
    have hE : Real.exp (t * (((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
          - q ^ 2 * (Fintype.card α : ℝ))) =
        ∏ w : α, Real.exp (t * ((if ω (e₁ w) = true ∧ ω (e₂ w) = true then (1 : ℝ) else 0) - q ^ 2)) := by
      rw [← Real.exp_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Finset.sum_boole]
      congr 2
      ring
    rw [hW, hE]
    simp_rw [hψ1t, hψ1f, hψ2]
    rw [mul_right_comm, ← Finset.prod_mul_distrib]
  simp_rw [hprod_ω]
  rw [Fintype.sum_equiv ψ _ (fun p : (α → Bool → Bool) × ({e : E // e ∉ U} → Bool) =>
    (∏ w : α, (if p.1 w true then q else 1 - q) * (if p.1 w false then q else 1 - q) *
      Real.exp (t * ((if p.1 w true = true ∧ p.1 w false = true then (1 : ℝ) else 0) - q ^ 2))) *
    (∏ r : {e : E // e ∉ U}, if p.2 r then q else 1 - q)) (fun _ => rfl)]
  have hsep : (∑ p : (α → Bool → Bool) × ({e : E // e ∉ U} → Bool),
      (∏ w : α, (if p.1 w true then q else 1 - q) * (if p.1 w false then q else 1 - q) *
        Real.exp (t * ((if p.1 w true = true ∧ p.1 w false = true then (1 : ℝ) else 0) - q ^ 2))) *
      (∏ r : {e : E // e ∉ U}, if p.2 r then q else 1 - q)) =
    (∑ f : α → Bool → Bool, ∏ w : α, (if f w true then q else 1 - q) * (if f w false then q else 1 - q) *
        Real.exp (t * ((if f w true = true ∧ f w false = true then (1 : ℝ) else 0) - q ^ 2))) *
    (∑ g : {e : E // e ∉ U} → Bool, ∏ r : {e : E // e ∉ U}, if g r then q else 1 - q) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.mul_sum]
  rw [hsep, sum_bernoulli_weight q, mul_one]
  rw [← Fintype.prod_sum (fun (_w : α) (b : Bool → Bool) =>
    (if b true then q else 1 - q) * (if b false then q else 1 - q) *
      Real.exp (t * ((if b true = true ∧ b false = true then (1 : ℝ) else 0) - q ^ 2)))]
  have hinner :
      (∑ b : Bool → Bool,
        (if b true then q else 1 - q) * (if b false then q else 1 - q) *
        Real.exp (t * ((if b true = true ∧ b false = true then (1 : ℝ) else 0) - q ^ 2))) =
      (1 - q ^ 2) * Real.exp (-t * q ^ 2) + q ^ 2 * Real.exp (t * (1 - q ^ 2)) := by
    let eb : (Bool → Bool) ≃ Bool × Bool :=
      { toFun := fun b => (b true, b false)
        invFun := fun p b => if b then p.1 else p.2
        left_inv := fun b => by funext x; cases x <;> rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [Fintype.sum_equiv eb
      (fun b : Bool → Bool =>
        (if b true then q else 1 - q) * (if b false then q else 1 - q) *
        Real.exp (t * ((if b true = true ∧ b false = true then (1 : ℝ) else 0) - q ^ 2)))
      (fun p : Bool × Bool =>
        (if p.1 then q else 1 - q) * (if p.2 then q else 1 - q) *
        Real.exp (t * ((if p.1 = true ∧ p.2 = true then (1 : ℝ) else 0) - q ^ 2)))
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    dsimp only
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, and_true, and_false]
    ring_nf
  simp_rw [hinner]
  rw [Finset.prod_const, Finset.card_univ]

/-- Generic Markov tail bound on the finite Bernoulli(`q`) space. -/
private lemma markov_upper_tail {E : Type*} [Fintype E] [DecidableEq E] (q t c : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t)
    (X : (E → Bool) → ℝ) (M : ℝ)
    (hmgf : ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (t * X ω) ≤ M) :
    ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
      (∏ e : E, if ω e then q else 1 - q) ≤ Real.exp (-t * c) * M := by
  have h1 : Real.exp (t * c) *
      ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
        (∏ e : E, if ω e then q else 1 - q) ≤
      ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (t * X ω) := by
    rw [Finset.mul_sum]
    calc ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
            Real.exp (t * c) * (∏ e : E, if ω e then q else 1 - q)
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
            (∏ e : E, if ω e then q else 1 - q) * Real.exp (t * X ω) := by
          apply Finset.sum_le_sum
          intro ω hω
          have hc : c < X ω := (Finset.mem_filter.mp hω).2
          have hw : 0 ≤ ∏ e : E, if ω e then q else 1 - q := bernoulli_weight_nonneg q hq0 hq1 ω
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hc) ht)) hw
      _ ≤ ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (t * X ω) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro ω
          exact mul_nonneg (bernoulli_weight_nonneg q hq0 hq1 ω) (le_of_lt (Real.exp_pos _))
  have h2 : Real.exp (t * c) *
      ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
        (∏ e : E, if ω e then q else 1 - q) ≤ M := le_trans h1 hmgf
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-t * c)))
  have hexp_mul : Real.exp (-t * c) * Real.exp (t * c) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
          (∏ e : E, if ω e then q else 1 - q)
      = Real.exp (-t * c) * (Real.exp (t * c) *
          ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => c < X ω),
            (∏ e : E, if ω e then q else 1 - q)) := by
        rw [← mul_assoc, hexp_mul, one_mul]
    _ ≤ Real.exp (-t * c) * M := h3

/-- Two-sided tail bound for a single subset `A` of size `m ≤ n`. -/
private lemma tail_subset_bound {E : Type*} [Fintype E] [DecidableEq E]
    (q ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 < ε)
    (n : ℕ) (A : Finset E) (hAn : A.card ≤ n) :
    let t := min (1 / 2) (ε / 4)
    ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool =>
        (ε / 2) * (n : ℝ) < |((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ)|),
      (∏ e : E, if ω e then q else 1 - q) ≤ 2 * Real.exp (-(t * (ε / 4)) * (n : ℝ)) := by
  intro t
  have ht0 : 0 ≤ t := le_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htε : t ≤ ε / 4 := min_le_right _ _
  have habs_t : |t| ≤ 1 / 2 := by rwa [abs_of_nonneg ht0]
  have habs_nt : |-t| ≤ 1 / 2 := by rw [abs_neg]; exact habs_t
  let X : (E → Bool) → ℝ := fun ω =>
    ((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ)
  have hM : ∀ s : ℝ, |s| ≤ 1 / 2 →
      ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (s * X ω) ≤
        Real.exp (s ^ 2 * (n : ℝ)) := by
    intro s hs
    have h1 := mgf_subset q s A
    have h2 : ((1 - q) * Real.exp (-s * q) + q * Real.exp (s * (1 - q))) ^ A.card ≤
        (Real.exp (s ^ 2)) ^ A.card := by
      apply pow_le_pow_left₀
      · have : 0 ≤ 1 - q := by linarith
        positivity
      · exact bernoulli_mgf_le q s hq0 hq1 hs
    have h3 : (Real.exp (s ^ 2)) ^ A.card = Real.exp (s ^ 2 * (A.card : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h4 : Real.exp (s ^ 2 * (A.card : ℝ)) ≤ Real.exp (s ^ 2 * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hAn) (sq_nonneg s)
    linarith
  have hup := markov_upper_tail q t ((ε / 2) * (n : ℝ)) hq0 hq1 ht0 X
    (Real.exp (t ^ 2 * (n : ℝ))) (hM t habs_t)
  have hdn_mgf : ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (t * (-X ω)) ≤
      Real.exp (t ^ 2 * (n : ℝ)) := by
    have h := hM (-t) habs_nt
    have heq1 : ∀ ω : E → Bool, t * (-X ω) = (-t) * X ω := fun _ => by ring
    have heq2 : (-t) ^ 2 * (n : ℝ) = t ^ 2 * (n : ℝ) := by ring
    simp_rw [heq1]
    rwa [heq2] at h
  have hdn := markov_upper_tail q t ((ε / 2) * (n : ℝ)) hq0 hq1 ht0 (fun ω => -X ω)
    (Real.exp (t ^ 2 * (n : ℝ))) hdn_mgf
  have hexp_le : Real.exp (-t * ((ε / 2) * (n : ℝ))) * Real.exp (t ^ 2 * (n : ℝ)) ≤
      Real.exp (-(t * (ε / 4)) * (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg ht0 hn0]
  have hsub : Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < |X ω|) ⊆
      Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < X ω) ∪
      Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < -X ω) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
    rcases lt_abs.mp hω with h | h
    · left; exact h
    · right; exact h
  calc ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < |X ω|),
          (∏ e : E, if ω e then q else 1 - q)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < X ω) ∪
          Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < -X ω),
          (∏ e : E, if ω e then q else 1 - q) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ω _ _ => bernoulli_weight_nonneg q hq0 hq1 ω)
    _ ≤ (∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < X ω),
          (∏ e : E, if ω e then q else 1 - q)) +
        (∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < -X ω),
          (∏ e : E, if ω e then q else 1 - q)) :=
        sum_union_le_of_nonneg (fun ω => bernoulli_weight_nonneg q hq0 hq1 ω)
    _ ≤ Real.exp (-t * ((ε / 2) * (n : ℝ))) * Real.exp (t ^ 2 * (n : ℝ)) +
        Real.exp (-t * ((ε / 2) * (n : ℝ))) * Real.exp (t ^ 2 * (n : ℝ)) := add_le_add hup hdn
    _ ≤ 2 * Real.exp (-(t * (ε / 4)) * (n : ℝ)) := by linarith

/-- Two-sided tail bound for disjoint edge-pairs `(e₁ w, e₂ w)` indexed by `α` with `|α| ≤ n`. -/
private lemma tail_pairs_bound {E α : Type*} [Fintype E] [DecidableEq E] [Fintype α] [DecidableEq α]
    (q ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 < ε)
    (n : ℕ) (hαn : Fintype.card α ≤ n)
    (e₁ e₂ : α → E) (hinj1 : Function.Injective e₁) (hinj2 : Function.Injective e₂)
    (hcross : ∀ w₁ w₂ : α, e₁ w₁ ≠ e₂ w₂) :
    let t := min (1 / 2) (ε / 4)
    ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool =>
        (ε / 2) * (n : ℝ) <
          |((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
            - q ^ 2 * (Fintype.card α : ℝ)|),
      (∏ e : E, if ω e then q else 1 - q) ≤ 2 * Real.exp (-(t * (ε / 4)) * (n : ℝ)) := by
  intro t
  have ht0 : 0 ≤ t := le_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htε : t ≤ ε / 4 := min_le_right _ _
  have habs_t : |t| ≤ 1 / 2 := by rwa [abs_of_nonneg ht0]
  have habs_nt : |-t| ≤ 1 / 2 := by rw [abs_neg]; exact habs_t
  have hq2_0 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2_1 : q ^ 2 ≤ 1 := by nlinarith
  let X : (E → Bool) → ℝ := fun ω =>
    ((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
      - q ^ 2 * (Fintype.card α : ℝ)
  have hM : ∀ s : ℝ, |s| ≤ 1 / 2 →
      ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (s * X ω) ≤
        Real.exp (s ^ 2 * (n : ℝ)) := by
    intro s hs
    have h1 := mgf_disjoint_pairs q s e₁ e₂ hinj1 hinj2 hcross
    have h2 : ((1 - q ^ 2) * Real.exp (-s * q ^ 2) + q ^ 2 * Real.exp (s * (1 - q ^ 2))) ^ Fintype.card α ≤
        (Real.exp (s ^ 2)) ^ Fintype.card α := by
      apply pow_le_pow_left₀
      · have : 0 ≤ 1 - q ^ 2 := by linarith
        positivity
      · exact bernoulli_mgf_le (q ^ 2) s hq2_0 hq2_1 hs
    have h3 : (Real.exp (s ^ 2)) ^ Fintype.card α = Real.exp (s ^ 2 * (Fintype.card α : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h4 : Real.exp (s ^ 2 * (Fintype.card α : ℝ)) ≤ Real.exp (s ^ 2 * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hαn) (sq_nonneg s)
    linarith
  have hup := markov_upper_tail q t ((ε / 2) * (n : ℝ)) hq0 hq1 ht0 X
    (Real.exp (t ^ 2 * (n : ℝ))) (hM t habs_t)
  have hdn_mgf : ∑ ω : E → Bool, (∏ e : E, if ω e then q else 1 - q) * Real.exp (t * (-X ω)) ≤
      Real.exp (t ^ 2 * (n : ℝ)) := by
    have h := hM (-t) habs_nt
    have heq1 : ∀ ω : E → Bool, t * (-X ω) = (-t) * X ω := fun _ => by ring
    have heq2 : (-t) ^ 2 * (n : ℝ) = t ^ 2 * (n : ℝ) := by ring
    simp_rw [heq1]
    rwa [heq2] at h
  have hdn := markov_upper_tail q t ((ε / 2) * (n : ℝ)) hq0 hq1 ht0 (fun ω => -X ω)
    (Real.exp (t ^ 2 * (n : ℝ))) hdn_mgf
  have hexp_le : Real.exp (-t * ((ε / 2) * (n : ℝ))) * Real.exp (t ^ 2 * (n : ℝ)) ≤
      Real.exp (-(t * (ε / 4)) * (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg ht0 hn0]
  have hsub : Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < |X ω|) ⊆
      Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < X ω) ∪
      Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < -X ω) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
    rcases lt_abs.mp hω with h | h
    · left; exact h
    · right; exact h
  calc ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < |X ω|),
          (∏ e : E, if ω e then q else 1 - q)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < X ω) ∪
          Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < -X ω),
          (∏ e : E, if ω e then q else 1 - q) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ω _ _ => bernoulli_weight_nonneg q hq0 hq1 ω)
    _ ≤ (∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < X ω),
          (∏ e : E, if ω e then q else 1 - q)) +
        (∑ ω ∈ Finset.univ.filter (fun ω : E → Bool => (ε / 2) * (n : ℝ) < -X ω),
          (∏ e : E, if ω e then q else 1 - q)) :=
        sum_union_le_of_nonneg (fun ω => bernoulli_weight_nonneg q hq0 hq1 ω)
    _ ≤ Real.exp (-t * ((ε / 2) * (n : ℝ))) * Real.exp (t ^ 2 * (n : ℝ)) +
        Real.exp (-t * ((ε / 2) * (n : ℝ))) * Real.exp (t ^ 2 * (n : ℝ)) := add_le_add hup hdn
    _ ≤ 2 * Real.exp (-(t * (ε / 4)) * (n : ℝ)) := by linarith

/-- Probabilistic existence of a `(q, ε)`-quasirandom graph on `Fin n` for all sufficiently large `n`,
uniformly in `q ∈ (0, 1)`. -/
private lemma exists_quasirandom_graph (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 < q → q < 1 → ∃ G : SimpleGraph (Fin n),
      (∀ v : Fin n, |(G.degree v : ℝ) - q * (n : ℝ)| ≤ ε * (n : ℝ)) ∧
      (∀ u v : Fin n, u ≠ v →
        |((Finset.univ.filter (fun w : Fin n => G.Adj u w ∧ G.Adj v w)).card : ℝ)
          - q ^ 2 * (n : ℝ)| ≤ ε * (n : ℝ)) := by
  let t : ℝ := min (1 / 2) (ε / 4)
  have ht_pos : 0 < t := lt_min (by norm_num) (by linarith)
  let c : ℝ := t * (ε / 4)
  have hc_pos : 0 < c := mul_pos ht_pos (by linarith)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 / ε)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (108 / c ^ 3)
  refine ⟨max 2 (max N₁ N₂), fun n hn q hq0 hq1 => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnN2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn_eps : 4 ≤ ε * (n : ℝ) := by
    have h1 : 4 / ε < (n : ℝ) := lt_of_lt_of_le hN₁ (by exact_mod_cast hnN1)
    have := (div_lt_iff₀ hε).mp h1
    linarith
  have hn_exp : (2 * (n : ℝ) + 2 * (n : ℝ) ^ 2) * Real.exp (-c * (n : ℝ)) < 1 := by
    have h1 : 108 / c ^ 3 < (n : ℝ) := lt_of_lt_of_le hN₂ (by exact_mod_cast hnN2)
    have hc3_pos : 0 < c ^ 3 := pow_pos hc_pos 3
    have h2 : 108 < c ^ 3 * (n : ℝ) := by
      have := (div_lt_iff₀ hc3_pos).mp h1
      linarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have h3 : (4 : ℝ) * (n : ℝ) ^ 2 < (c * (n : ℝ) / 3) ^ 3 := by
      have : (c * (n : ℝ) / 3) ^ 3 = (c ^ 3 * (n : ℝ) / 27) * (n : ℝ) ^ 2 := by ring
      rw [this]
      have : (4 : ℝ) < c ^ 3 * (n : ℝ) / 27 := by linarith
      nlinarith [sq_pos_of_pos hn_pos]
    have h4 : (c * (n : ℝ) / 3) ^ 3 ≤ Real.exp (c * (n : ℝ)) := by
      have hy : 0 ≤ c * (n : ℝ) / 3 := by positivity
      have hlin : c * (n : ℝ) / 3 ≤ Real.exp (c * (n : ℝ) / 3) := by
        linarith [Real.add_one_le_exp (c * (n : ℝ) / 3)]
      calc (c * (n : ℝ) / 3) ^ 3
          ≤ (Real.exp (c * (n : ℝ) / 3)) ^ 3 := pow_le_pow_left₀ hy hlin 3
        _ = Real.exp (3 * (c * (n : ℝ) / 3)) := by rw [← Real.exp_nat_mul]; norm_num
        _ = Real.exp (c * (n : ℝ)) := by ring_nf
    have h5 : 2 * (n : ℝ) + 2 * (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      nlinarith
    have h6 : 2 * (n : ℝ) + 2 * (n : ℝ) ^ 2 < Real.exp (c * (n : ℝ)) :=
      lt_of_le_of_lt h5 (lt_of_lt_of_le h3 h4)
    have hexp_pos : 0 < Real.exp (c * (n : ℝ)) := Real.exp_pos _
    rw [neg_mul, Real.exp_neg]
    have := mul_lt_mul_of_pos_right h6 (inv_pos.mpr hexp_pos)
    simpa only [mul_inv_cancel₀ (ne_of_gt hexp_pos)] using this
  let E := {e : Sym2 (Fin n) // ¬e.IsDiag}
  let mkG : (E → Bool) → SimpleGraph (Fin n) := fun ω =>
    { Adj := fun u v => ∃ h : u ≠ v, ω ⟨s(u, v), by simp only [Sym2.mk_isDiag_iff]; exact h⟩ = true
      symm := ⟨by
        rintro u v ⟨h, hω⟩
        refine ⟨h.symm, ?_⟩
        have heq : (⟨s(v, u), by simp only [Sym2.mk_isDiag_iff]; exact h.symm⟩ : E) =
            ⟨s(u, v), by simp only [Sym2.mk_isDiag_iff]; exact h⟩ := Subtype.ext Sym2.eq_swap
        rwa [heq]⟩
      loopless := ⟨by rintro v ⟨h, _⟩; exact h rfl⟩ }
  let W : (E → Bool) → ℝ := fun ω => ∏ e : E, if ω e then q else 1 - q
  have hW_nonneg : ∀ ω, 0 ≤ W ω := bernoulli_weight_nonneg q (le_of_lt hq0) (le_of_lt hq1)
  let badDeg : Fin n → Finset (E → Bool) := fun v =>
    Finset.univ.filter (fun ω : E → Bool => ε * (n : ℝ) < |((mkG ω).degree v : ℝ) - q * (n : ℝ)|)
  let badCod : Fin n × Fin n → Finset (E → Bool) := fun p =>
    if p.1 = p.2 then ∅ else
    Finset.univ.filter (fun ω : E → Bool =>
      ε * (n : ℝ) < |((Finset.univ.filter (fun w : Fin n => (mkG ω).Adj p.1 w ∧ (mkG ω).Adj p.2 w)).card : ℝ)
        - q ^ 2 * (n : ℝ)|)
  have hbadDeg_le : ∀ v : Fin n, ∑ ω ∈ badDeg v, W ω ≤ 2 * Real.exp (-c * (n : ℝ)) := by
    intro v
    let A : Finset E := Finset.univ.image (fun w : {w : Fin n // w ≠ v} =>
      ⟨s(v, w.1), by simp only [Sym2.mk_isDiag_iff]; exact w.2.symm⟩)
    have hA_inj : Function.Injective (fun w : {w : Fin n // w ≠ v} =>
        (⟨s(v, w.1), by simp only [Sym2.mk_isDiag_iff]; exact w.2.symm⟩ : E)) := by
      intro w₁ w₂ h
      have hs : s(v, w₁.1) = s(v, w₂.1) := congrArg Subtype.val h
      rw [Sym2.eq_iff] at hs
      rcases hs with ⟨_, hw⟩ | ⟨hw, _⟩
      · exact Subtype.ext hw
      · exact absurd hw.symm w₂.2
    have hA_card : A.card = n - 1 := by
      rw [Finset.card_image_of_injective _ hA_inj, Finset.card_univ, Fintype.card_subtype_compl,
        Fintype.card_fin, Fintype.card_unique]
    have hdeg_eq : ∀ ω : E → Bool, (mkG ω).degree v = (A.filter (fun e => ω e = true)).card := by
      intro ω
      have hnb : (mkG ω).neighborFinset v = Finset.univ.filter (fun w : Fin n => (mkG ω).Adj v w) := by
        ext w; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [SimpleGraph.degree, hnb]
      have h1 : (Finset.univ.filter (fun w : Fin n => (mkG ω).Adj v w)).card =
          (Finset.univ.filter (fun w : {w : Fin n // w ≠ v} =>
            ω ⟨s(v, w.1), by simp only [Sym2.mk_isDiag_iff]; exact w.2.symm⟩ = true)).card := by
        apply Finset.card_bij (fun w hw => ⟨w, fun h => by
          rcases (Finset.mem_filter.mp hw).2 with ⟨hne, _⟩
          exact hne h.symm⟩)
        · intro w hw
          rcases (Finset.mem_filter.mp hw).2 with ⟨_, hω⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hω
        · intro w₁ _ w₂ _ h
          exact congrArg Subtype.val h
        · intro w hw
          refine ⟨w.1, ?_, Subtype.eta w w.2⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact ⟨w.2.symm, hw⟩
      have h2 : (A.filter (fun e => ω e = true)).card =
          (Finset.univ.filter (fun w : {w : Fin n // w ≠ v} =>
            ω ⟨s(v, w.1), by simp only [Sym2.mk_isDiag_iff]; exact w.2.symm⟩ = true)).card := by
        rw [Finset.filter_image, Finset.card_image_of_injective _ hA_inj]
      rw [h1, ← h2]
    have hsub : badDeg v ⊆ Finset.univ.filter (fun ω : E → Bool =>
        (ε / 2) * (n : ℝ) < |((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ)|) := by
      intro ω hω
      simp only [badDeg, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [hdeg_eq ω] at hω
      have hAc : (A.card : ℝ) = (n : ℝ) - 1 := by
        rw [hA_card, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [hAc]
      have htri : |((A.filter (fun e => ω e = true)).card : ℝ) - q * (n : ℝ)| ≤
          |((A.filter (fun e => ω e = true)).card : ℝ) - q * ((n : ℝ) - 1)| + |q| := by
        have : ((A.filter (fun e => ω e = true)).card : ℝ) - q * (n : ℝ) =
            (((A.filter (fun e => ω e = true)).card : ℝ) - q * ((n : ℝ) - 1)) - q := by ring
        rw [this]
        exact abs_sub _ _
      have hqabs : |q| ≤ 1 := by rw [abs_of_pos hq0]; exact le_of_lt hq1
      linarith
    calc ∑ ω ∈ badDeg v, W ω
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool =>
            (ε / 2) * (n : ℝ) < |((A.filter (fun e => ω e = true)).card : ℝ) - q * (A.card : ℝ)|), W ω :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => hW_nonneg ω)
      _ ≤ 2 * Real.exp (-c * (n : ℝ)) :=
          tail_subset_bound q ε (le_of_lt hq0) (le_of_lt hq1) hε n A (by omega)
  have hbadCod_le : ∀ p : Fin n × Fin n, ∑ ω ∈ badCod p, W ω ≤ 2 * Real.exp (-c * (n : ℝ)) := by
    rintro ⟨u, v⟩
    by_cases huv : u = v
    · simp only [badCod, huv, ↓reduceIte, Finset.sum_empty]
      positivity
    · simp only [badCod, huv, ↓reduceIte]
      let α := {w : Fin n // w ≠ u ∧ w ≠ v}
      let e₁ : α → E := fun w => ⟨s(u, w.1), by simp only [Sym2.mk_isDiag_iff]; exact w.2.1.symm⟩
      let e₂ : α → E := fun w => ⟨s(v, w.1), by simp only [Sym2.mk_isDiag_iff]; exact w.2.2.symm⟩
      have hinj1 : Function.Injective e₁ := by
        intro w₁ w₂ h
        have hs : s(u, w₁.1) = s(u, w₂.1) := congrArg Subtype.val h
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨_, hw⟩ | ⟨hw, _⟩
        · exact Subtype.ext hw
        · exact absurd hw.symm w₂.2.1
      have hinj2 : Function.Injective e₂ := by
        intro w₁ w₂ h
        have hs : s(v, w₁.1) = s(v, w₂.1) := congrArg Subtype.val h
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨_, hw⟩ | ⟨hw, _⟩
        · exact Subtype.ext hw
        · exact absurd hw.symm w₂.2.2
      have hcross : ∀ w₁ w₂ : α, e₁ w₁ ≠ e₂ w₂ := by
        intro w₁ w₂ h
        have hs : s(u, w₁.1) = s(v, w₂.1) := congrArg Subtype.val h
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨huv', _⟩ | ⟨huw, _⟩
        · exact huv huv'
        · exact w₂.2.1 huw.symm
      have hα_card : Fintype.card α = n - 2 := by
        have hset : (Finset.univ.filter (fun w : Fin n => w ≠ u ∧ w ≠ v)) =
            (Finset.univ.erase u).erase v := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_comm]
        rw [Fintype.card_subtype, hset, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ u),
          Finset.card_univ, Fintype.card_fin]
        · omega
        · exact Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩
      have hcod_eq : ∀ ω : E → Bool,
          (Finset.univ.filter (fun w : Fin n => (mkG ω).Adj u w ∧ (mkG ω).Adj v w)).card =
          (Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card := by
        intro ω
        apply Finset.card_bij (fun w hw => ⟨w, ⟨fun h => by
            rcases (Finset.mem_filter.mp hw).2.1 with ⟨hne, _⟩
            exact hne h.symm,
          fun h => by
            rcases (Finset.mem_filter.mp hw).2.2 with ⟨hne, _⟩
            exact hne h.symm⟩⟩)
        · intro w hw
          rcases (Finset.mem_filter.mp hw).2 with ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, e₁, e₂]
          exact ⟨h1, h2⟩
        · intro w₁ _ w₂ _ h
          exact congrArg Subtype.val h
        · intro w hw
          refine ⟨w.1, ?_, Subtype.eta w w.2⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, e₁, e₂] at hw ⊢
          exact ⟨⟨w.2.1.symm, hw.1⟩, ⟨w.2.2.symm, hw.2⟩⟩
      have hsub : Finset.univ.filter (fun ω : E → Bool =>
          ε * (n : ℝ) < |((Finset.univ.filter (fun w : Fin n => (mkG ω).Adj u w ∧ (mkG ω).Adj v w)).card : ℝ)
            - q ^ 2 * (n : ℝ)|) ⊆
        Finset.univ.filter (fun ω : E → Bool =>
          (ε / 2) * (n : ℝ) < |((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
            - q ^ 2 * (Fintype.card α : ℝ)|) := by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        rw [hcod_eq ω] at hω
        have hαc : (Fintype.card α : ℝ) = (n : ℝ) - 2 := by
          rw [hα_card, Nat.cast_sub hn2]; norm_num
        rw [hαc]
        have htri : |((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ) - q ^ 2 * (n : ℝ)| ≤
            |((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ) - q ^ 2 * ((n : ℝ) - 2)| +
            |2 * q ^ 2| := by
          have : ((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ) - q ^ 2 * (n : ℝ) =
              (((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ) - q ^ 2 * ((n : ℝ) - 2)) - 2 * q ^ 2 := by
            ring
          rw [this]
          exact abs_sub _ _
        have h2q : |2 * q ^ 2| ≤ 2 := by
          rw [abs_of_nonneg (by positivity)]
          nlinarith
        linarith
      calc ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool =>
            ε * (n : ℝ) < |((Finset.univ.filter (fun w : Fin n => (mkG ω).Adj u w ∧ (mkG ω).Adj v w)).card : ℝ)
              - q ^ 2 * (n : ℝ)|), W ω
          ≤ ∑ ω ∈ Finset.univ.filter (fun ω : E → Bool =>
            (ε / 2) * (n : ℝ) < |((Finset.univ.filter (fun w : α => ω (e₁ w) = true ∧ ω (e₂ w) = true)).card : ℝ)
              - q ^ 2 * (Fintype.card α : ℝ)|), W ω :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => hW_nonneg ω)
        _ ≤ 2 * Real.exp (-c * (n : ℝ)) :=
            tail_pairs_bound q ε (le_of_lt hq0) (le_of_lt hq1) hε n (by omega) e₁ e₂ hinj1 hinj2 hcross
  let badAll : Finset (E → Bool) :=
    (Finset.univ.biUnion badDeg) ∪ (Finset.univ.biUnion badCod)
  have hbadAll_lt : ∑ ω ∈ badAll, W ω < 1 := by
    have h1 : ∑ ω ∈ badAll, W ω ≤
        (∑ ω ∈ Finset.univ.biUnion badDeg, W ω) + (∑ ω ∈ Finset.univ.biUnion badCod, W ω) :=
      sum_union_le_of_nonneg hW_nonneg
    have h2 : ∑ ω ∈ Finset.univ.biUnion badDeg, W ω ≤ ∑ v : Fin n, ∑ ω ∈ badDeg v, W ω :=
      sum_biUnion_le_of_nonneg Finset.univ badDeg hW_nonneg
    have h3 : ∑ ω ∈ Finset.univ.biUnion badCod, W ω ≤ ∑ p : Fin n × Fin n, ∑ ω ∈ badCod p, W ω :=
      sum_biUnion_le_of_nonneg Finset.univ badCod hW_nonneg
    have h4 : ∑ v : Fin n, ∑ ω ∈ badDeg v, W ω ≤ (n : ℝ) * (2 * Real.exp (-c * (n : ℝ))) := by
      calc ∑ v : Fin n, ∑ ω ∈ badDeg v, W ω
          ≤ ∑ _v : Fin n, (2 * Real.exp (-c * (n : ℝ))) :=
            Finset.sum_le_sum (fun v _ => hbadDeg_le v)
        _ = (n : ℝ) * (2 * Real.exp (-c * (n : ℝ))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h5 : ∑ p : Fin n × Fin n, ∑ ω ∈ badCod p, W ω ≤ ((n : ℝ) ^ 2) * (2 * Real.exp (-c * (n : ℝ))) := by
      calc ∑ p : Fin n × Fin n, ∑ ω ∈ badCod p, W ω
          ≤ ∑ _p : Fin n × Fin n, (2 * Real.exp (-c * (n : ℝ))) :=
            Finset.sum_le_sum (fun p _ => hbadCod_le p)
        _ = ((n : ℝ) ^ 2) * (2 * Real.exp (-c * (n : ℝ))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have h6 : (n : ℝ) * (2 * Real.exp (-c * (n : ℝ))) + ((n : ℝ) ^ 2) * (2 * Real.exp (-c * (n : ℝ))) =
        (2 * (n : ℝ) + 2 * (n : ℝ) ^ 2) * Real.exp (-c * (n : ℝ)) := by ring
    linarith
  have hex : ∃ ω : E → Bool, ω ∉ badAll := by
    by_contra h
    push Not at h
    have hall : badAll = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [hall] at hbadAll_lt
    dsimp only [W] at hbadAll_lt
    rw [sum_bernoulli_weight q] at hbadAll_lt
    exact lt_irrefl 1 hbadAll_lt
  rcases hex with ⟨ω, hω⟩
  refine ⟨mkG ω, ?_, ?_⟩
  · intro v
    by_contra hlt
    push Not at hlt
    apply hω
    apply Finset.mem_union_left
    refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, ?_⟩
    simp only [badDeg, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdeg_eq : ∀ inst₁ inst₂,
        @SimpleGraph.degree (Fin n) (mkG ω) v inst₁ = @SimpleGraph.degree (Fin n) (mkG ω) v inst₂ := by
      intro inst₁ inst₂
      simp only [SimpleGraph.degree]
      exact congrArg Finset.card (by ext w; simp only [SimpleGraph.mem_neighborFinset])
    exact lt_of_lt_of_eq hlt (congrArg (fun m : ℕ => |(m : ℝ) - q * (n : ℝ)|) (hdeg_eq _ _))
  · intro u v huv
    by_contra hlt
    push Not at hlt
    apply hω
    apply Finset.mem_union_right
    refine Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_univ (u, v), ?_⟩
    simp only [badCod, huv, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcod_eq : ∀ inst₁ inst₂,
        (@Finset.filter (Fin n) (fun w : Fin n => (mkG ω).Adj u w ∧ (mkG ω).Adj v w) inst₁ Finset.univ).card =
        (@Finset.filter (Fin n) (fun w : Fin n => (mkG ω).Adj u w ∧ (mkG ω).Adj v w) inst₂ Finset.univ).card :=
      fun inst₁ inst₂ => congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
    exact lt_of_lt_of_eq hlt (congrArg (fun m : ℕ => |(m : ℝ) - q ^ 2 * (n : ℝ)|) (hcod_eq _ _))

/-- Complement quasirandomness: if `G` has degrees within `q * n ± ε * n` and 2-codegrees
within `q^2 * n ± ε * n`, then `Gᶜ` has degrees within `(1 - q) * n ± (ε * n + 1)` and
2-codegrees within `(1 - q)^2 * n ± (3 * ε * n + 2)`. -/
private lemma compl_quasirandom {n : ℕ} (G : SimpleGraph (Fin n)) (q ε : ℝ)
    (hdeg : ∀ v : Fin n, |(G.degree v : ℝ) - q * (n : ℝ)| ≤ ε * (n : ℝ))
    (hcod : ∀ u v : Fin n, u ≠ v →
      |((Finset.univ.filter (fun w : Fin n => G.Adj u w ∧ G.Adj v w)).card : ℝ)
        - q ^ 2 * (n : ℝ)| ≤ ε * (n : ℝ)) :
    (∀ v : Fin n, |(Gᶜ.degree v : ℝ) - (1 - q) * (n : ℝ)| ≤ ε * (n : ℝ) + 1) ∧
    (∀ u v : Fin n, u ≠ v →
      |((Finset.univ.filter (fun w : Fin n => Gᶜ.Adj u w ∧ Gᶜ.Adj v w)).card : ℝ)
        - (1 - q) ^ 2 * (n : ℝ)| ≤ 3 * ε * (n : ℝ) + 2) := by
  constructor
  · intro v
    have hdisj : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj] at hw1 hw2
      exact hw2.2 hw1
    have hunion : G.neighborFinset v ∪ Gᶜ.neighborFinset v = Finset.univ.erase v := by
      ext w
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj,
        Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro (h | ⟨hne, _⟩)
        · exact (G.ne_of_adj h).symm
        · exact hne.symm
      · intro hne
        by_cases hadj : G.Adj v w
        · left; exact hadj
        · right; exact ⟨hne.symm, hadj⟩
    have hsum : G.degree v + Gᶜ.degree v = n - 1 := by
      rw [SimpleGraph.degree, SimpleGraph.degree, ← Finset.card_union_of_disjoint hdisj, hunion,
        Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (Fin.pos v).ne'
    have hsumR : (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) = (n : ℝ) - 1 := by
      have : ((G.degree v + Gᶜ.degree v : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hsum
      rw [Nat.cast_add, Nat.cast_sub hn1, Nat.cast_one] at this
      exact this
    have heq : (Gᶜ.degree v : ℝ) - (1 - q) * (n : ℝ) = -((G.degree v : ℝ) - q * (n : ℝ)) - 1 := by
      linarith
    rw [heq]
    have htri := abs_sub (-((G.degree v : ℝ) - q * (n : ℝ))) 1
    rw [abs_neg, abs_one] at htri
    linarith [hdeg v]
  · intro u v huv
    let I : Finset (Fin n) := (Finset.univ.erase u).erase v
    let A : Finset (Fin n) := I.filter (fun w => G.Adj u w)
    let B : Finset (Fin n) := I.filter (fun w => G.Adj v w)
    have hI_card : I.card = n - 2 := by
      rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, Fintype.card_fin]
      · omega
      · exact Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩
    have hC_eq : Finset.univ.filter (fun w : Fin n => Gᶜ.Adj u w ∧ Gᶜ.Adj v w) = I \ (A ∪ B) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.compl_adj,
        Finset.mem_sdiff, Finset.mem_union, I, A, B, Finset.mem_erase, and_true]
      constructor
      · rintro ⟨⟨huw, hnu⟩, ⟨hvw, hnv⟩⟩
        exact ⟨⟨hvw.symm, huw.symm⟩, fun h => h.elim (fun h1 => hnu h1.2) (fun h2 => hnv h2.2)⟩
      · rintro ⟨⟨hwv, hwu⟩, hnot⟩
        exact ⟨⟨hwu.symm, fun hu => hnot (Or.inl ⟨⟨hwv, hwu⟩, hu⟩)⟩,
               ⟨hwv.symm, fun hv => hnot (Or.inr ⟨⟨hwv, hwu⟩, hv⟩)⟩⟩
    have hAB_sub : A ∪ B ⊆ I := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hAB_inter : A ∩ B = Finset.univ.filter (fun w : Fin n => G.Adj u w ∧ G.Adj v w) := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, I, A, B,
        Finset.mem_erase, and_true]
      constructor
      · rintro ⟨⟨_, hu⟩, ⟨_, hv⟩⟩; exact ⟨hu, hv⟩
      · rintro ⟨hu, hv⟩
        exact ⟨⟨⟨(G.ne_of_adj hv).symm, (G.ne_of_adj hu).symm⟩, hu⟩,
               ⟨⟨(G.ne_of_adj hv).symm, (G.ne_of_adj hu).symm⟩, hv⟩⟩
    have hA_eq : A = (G.neighborFinset u).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        SimpleGraph.mem_neighborFinset, I, A]
      constructor
      · rintro ⟨⟨hwv, _⟩, huw⟩; exact ⟨hwv, huw⟩
      · rintro ⟨hwv, huw⟩; exact ⟨⟨hwv, (G.ne_of_adj huw).symm⟩, huw⟩
    have hB_eq : B = (G.neighborFinset v).erase u := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        SimpleGraph.mem_neighborFinset, I, B]
      constructor
      · rintro ⟨⟨_, hwu⟩, hvw⟩; exact ⟨hwu, hvw⟩
      · rintro ⟨hwu, hvw⟩; exact ⟨⟨(G.ne_of_adj hvw).symm, hwu⟩, hvw⟩
    have hA_card : (A.card : ℝ) = (G.degree u : ℝ) - if G.Adj u v then 1 else 0 := by
      rw [hA_eq]
      by_cases hadj : G.Adj u v
      · have hv_mem : v ∈ G.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
        have hpos : 1 ≤ G.degree u := by
          rw [SimpleGraph.degree]
          exact Finset.one_le_card.mpr ⟨v, hv_mem⟩
        rw [Finset.card_erase_of_mem hv_mem, ← SimpleGraph.degree, Nat.cast_sub hpos]
        simp only [hadj, ↓reduceIte, Nat.cast_one]
      · have hv_nmem : v ∉ G.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
        rw [Finset.erase_eq_of_notMem hv_nmem, ← SimpleGraph.degree]
        simp only [hadj, ↓reduceIte, sub_zero]
    have hB_card : (B.card : ℝ) = (G.degree v : ℝ) - if G.Adj u v then 1 else 0 := by
      rw [hB_eq]
      by_cases hadj : G.Adj u v
      · have hu_mem : u ∈ G.neighborFinset v := by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm
        have hpos : 1 ≤ G.degree v := by
          rw [SimpleGraph.degree]
          exact Finset.one_le_card.mpr ⟨u, hu_mem⟩
        rw [Finset.card_erase_of_mem hu_mem, ← SimpleGraph.degree, Nat.cast_sub hpos]
        simp only [hadj, ↓reduceIte, Nat.cast_one]
      · have hu_nmem : u ∉ G.neighborFinset v := by
          rw [SimpleGraph.mem_neighborFinset]
          exact fun h => hadj h.symm
        rw [Finset.erase_eq_of_notMem hu_nmem, ← SimpleGraph.degree]
        simp only [hadj, ↓reduceIte, sub_zero]
    have hn2 : 2 ≤ n := by
      have hcard := Fintype.card_fin n
      have h2 : 2 ≤ Fintype.card (Fin n) := Fintype.one_lt_card_iff.mpr ⟨u, v, huv⟩
      omega
    have hsdiff : (I \ (A ∪ B)).card + (A ∪ B).card = I.card := Finset.card_sdiff_add_card_eq_card hAB_sub
    have hunion_inter : (A ∪ B).card + (A ∩ B).card = A.card + B.card := Finset.card_union_add_card_inter A B
    have hC_R : ((Finset.univ.filter (fun w : Fin n => Gᶜ.Adj u w ∧ Gᶜ.Adj v w)).card : ℝ) =
        (n : ℝ) - (G.degree u : ℝ) - (G.degree v : ℝ) +
        ((Finset.univ.filter (fun w : Fin n => G.Adj u w ∧ G.Adj v w)).card : ℝ) -
        2 + 2 * (if G.Adj u v then (1 : ℝ) else 0) := by
      rw [hC_eq, ← hAB_inter]
      have h1 : ((I \ (A ∪ B)).card : ℝ) + ((A ∪ B).card : ℝ) = (I.card : ℝ) := by exact_mod_cast hsdiff
      have h2 : ((A ∪ B).card : ℝ) + ((A ∩ B).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hunion_inter
      have hI_R : (I.card : ℝ) = (n : ℝ) - 2 := by
        rw [hI_card, Nat.cast_sub hn2]; norm_num
      linarith
    have hdiff : ((Finset.univ.filter (fun w : Fin n => Gᶜ.Adj u w ∧ Gᶜ.Adj v w)).card : ℝ) - (1 - q) ^ 2 * (n : ℝ) =
        -((G.degree u : ℝ) - q * (n : ℝ)) - ((G.degree v : ℝ) - q * (n : ℝ)) +
        (((Finset.univ.filter (fun w : Fin n => G.Adj u w ∧ G.Adj v w)).card : ℝ) - q ^ 2 * (n : ℝ)) +
        (-2 + 2 * (if G.Adj u v then (1 : ℝ) else 0)) := by
      rw [hC_R]; ring
    rw [hdiff]
    have hrem : |-2 + 2 * (if G.Adj u v then (1 : ℝ) else 0)| ≤ 2 := by
      split_ifs <;> norm_num
    have h1 := hdeg u
    have h2 := hdeg v
    have h3 := hcod u v huv
    rw [abs_le] at h1 h2 h3 hrem ⊢
    constructor <;> linarith

/-- General deterministic quasirandomness transfer from `G₁` and `P ≤ G₁` with bounded
leftover degree `(G₁ \ P).degree v ≤ c * n` to `R = Pᶜ`. -/
private lemma quasirandom_transfer_general {n : ℕ} (G₁ P : SimpleGraph (Fin n)) (hPG : P ≤ G₁)
    (p q ε c : ℝ)
    (hdeg : ∀ v : Fin n, |(G₁.degree v : ℝ) - q * (n : ℝ)| ≤ ε * (n : ℝ))
    (hcod : ∀ u v : Fin n, u ≠ v →
      |((Finset.univ.filter (fun w : Fin n => G₁.Adj u w ∧ G₁.Adj v w)).card : ℝ)
        - q ^ 2 * (n : ℝ)| ≤ ε * (n : ℝ))
    (hrem : ∀ v : Fin n, ((G₁ \ P).degree v : ℝ) ≤ c * (n : ℝ)) :
    (∀ v : Fin n, |(Pᶜ.degree v : ℝ) - p * (n : ℝ)| ≤ (ε + |(1 - q) - p| + c) * (n : ℝ) + 1) ∧
    (∀ u v : Fin n, u ≠ v →
      |((Finset.univ.filter (fun w : Fin n => Pᶜ.Adj u w ∧ Pᶜ.Adj v w)).card : ℝ)
        - p ^ 2 * (n : ℝ)| ≤ (3 * ε + |(1 - q) ^ 2 - p ^ 2| + 2 * c) * (n : ℝ) + 2) := by
  have hcpl := compl_quasirandom G₁ q ε hdeg hcod
  have hR_adj : ∀ u v : Fin n, Pᶜ.Adj u v ↔ G₁ᶜ.Adj u v ∨ (G₁ \ P).Adj u v := by
    intro u v
    simp only [SimpleGraph.compl_adj, SimpleGraph.sdiff_adj]
    constructor
    · rintro ⟨hne, hnp⟩
      by_cases hg : G₁.Adj u v
      · right; exact ⟨hg, hnp⟩
      · left; exact ⟨hne, hg⟩
    · rintro (⟨hne, hng⟩ | ⟨hg, hnp⟩)
      · exact ⟨hne, fun hp => hng (hPG hp)⟩
      · exact ⟨G₁.ne_of_adj hg, hnp⟩
  constructor
  · intro v
    have hdisj : Disjoint (G₁ᶜ.neighborFinset v) ((G₁ \ P).neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj, SimpleGraph.sdiff_adj] at hw1 hw2
      exact hw1.2 hw2.1
    have hunion : G₁ᶜ.neighborFinset v ∪ (G₁ \ P).neighborFinset v = Pᶜ.neighborFinset v := by
      ext w
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, hR_adj]
    have hdeg_eq : (Pᶜ.degree v : ℝ) = (G₁ᶜ.degree v : ℝ) + ((G₁ \ P).degree v : ℝ) := by
      have : Pᶜ.degree v = G₁ᶜ.degree v + (G₁ \ P).degree v := by
        rw [SimpleGraph.degree, SimpleGraph.degree, SimpleGraph.degree, ← hunion,
          Finset.card_union_of_disjoint hdisj]
      exact_mod_cast this
    have h1 := hcpl.1 v
    have h2 := hrem v
    have h3 : (0 : ℝ) ≤ ((G₁ \ P).degree v : ℝ) := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdiff : (Pᶜ.degree v : ℝ) - p * (n : ℝ) =
        ((G₁ᶜ.degree v : ℝ) - (1 - q) * (n : ℝ)) + ((1 - q) - p) * (n : ℝ) + ((G₁ \ P).degree v : ℝ) := by
      rw [hdeg_eq]; ring
    rw [hdiff]
    have hqp : |((1 - q) - p) * (n : ℝ)| = |(1 - q) - p| * (n : ℝ) := by
      rw [abs_mul, abs_of_nonneg hn0]
    rw [abs_le] at h1 ⊢
    have hqp' := abs_le.mp (le_of_eq hqp)
    constructor <;> linarith
  · intro u v huv
    let S_c : Finset (Fin n) := Finset.univ.filter (fun w : Fin n => G₁ᶜ.Adj u w ∧ G₁ᶜ.Adj v w)
    let S_R : Finset (Fin n) := Finset.univ.filter (fun w : Fin n => Pᶜ.Adj u w ∧ Pᶜ.Adj v w)
    have hsub1 : S_c ⊆ S_R := by
      intro w hw
      simp only [S_c, S_R, Finset.mem_filter, Finset.mem_univ, true_and, hR_adj] at hw ⊢
      exact ⟨Or.inl hw.1, Or.inl hw.2⟩
    have hsub2 : S_R \ S_c ⊆ (G₁ \ P).neighborFinset u ∪ (G₁ \ P).neighborFinset v := by
      intro w hw
      simp only [S_c, S_R, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, SimpleGraph.mem_neighborFinset, hR_adj] at hw ⊢
      rcases hw with ⟨⟨hu | hu, hv | hv⟩, hnot⟩
      · exact absurd ⟨hu, hv⟩ hnot
      · exact Or.inr hv
      · exact Or.inl hu
      · exact Or.inl hu
    have hcard_lo : (S_c.card : ℝ) ≤ (S_R.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub1
    have hcard_hi : (S_R.card : ℝ) ≤ (S_c.card : ℝ) + ((G₁ \ P).degree u : ℝ) + ((G₁ \ P).degree v : ℝ) := by
      have h1 : (S_R \ S_c).card + S_c.card = S_R.card := Finset.card_sdiff_add_card_eq_card hsub1
      have h2 : (S_R \ S_c).card ≤ ((G₁ \ P).neighborFinset u ∪ (G₁ \ P).neighborFinset v).card :=
        Finset.card_le_card hsub2
      have h3 : ((G₁ \ P).neighborFinset u ∪ (G₁ \ P).neighborFinset v).card ≤
          (G₁ \ P).degree u + (G₁ \ P).degree v := by
        rw [SimpleGraph.degree, SimpleGraph.degree]
        exact Finset.card_union_le _ _
      have : S_R.card ≤ S_c.card + (G₁ \ P).degree u + (G₁ \ P).degree v := by omega
      exact_mod_cast this
    have h1 := hcpl.2 u v huv
    have hru := hrem u
    have hrv := hrem v
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hqp : |((1 - q) ^ 2 - p ^ 2) * (n : ℝ)| = |(1 - q) ^ 2 - p ^ 2| * (n : ℝ) := by
      rw [abs_mul, abs_of_nonneg hn0]
    have hqp' := abs_le.mp (le_of_eq hqp)
    rw [abs_le] at h1 ⊢
    constructor <;> linarith

/-- Specialized deterministic quasirandomness transfer lemma for `q = 1 - p + (3/2) * η`,
`ε = η^2`, leftover max degree `≤ 8 * η * n`, and `η ≤ min (δ / 25) (1 / 1000)`. -/
private lemma quasirandom_transfer {n : ℕ} (G₁ P : SimpleGraph (Fin n)) (hPG : P ≤ G₁)
    (p η δ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hη0 : 0 < η) (hηδ : η ≤ δ / 25) (hη1 : η ≤ 1 / 1000) (hn : 2 ≤ η * (n : ℝ))
    (hdeg : ∀ v : Fin n, |(G₁.degree v : ℝ) - (1 - p + (3 / 2) * η) * (n : ℝ)| ≤ η ^ 2 * (n : ℝ))
    (hcod : ∀ u v : Fin n, u ≠ v →
      |((Finset.univ.filter (fun w : Fin n => G₁.Adj u w ∧ G₁.Adj v w)).card : ℝ)
        - (1 - p + (3 / 2) * η) ^ 2 * (n : ℝ)| ≤ η ^ 2 * (n : ℝ))
    (hrem : ∀ v : Fin n, ((G₁ \ P).degree v : ℝ) ≤ 8 * η * (n : ℝ)) :
    (∀ v : Fin n, |(Pᶜ.degree v : ℝ) - p * (n : ℝ)| ≤ δ * (n : ℝ)) ∧
    (∀ u v : Fin n, u ≠ v →
      |((Finset.univ.filter (fun w : Fin n => Pᶜ.Adj u w ∧ Pᶜ.Adj v w)).card : ℝ)
        - p ^ 2 * (n : ℝ)| ≤ δ * (n : ℝ)) := by
  let q : ℝ := 1 - p + (3 / 2) * η
  have hgen := quasirandom_transfer_general G₁ P hPG p q (η ^ 2) (8 * η) hdeg hcod hrem
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1q : |(1 - q) - p| = (3 / 2) * η := by
    have : (1 - q) - p = -((3 / 2) * η) := by dsimp [q]; ring
    rw [this, abs_neg, abs_of_pos (by linarith)]
  have h1q2 : |(1 - q) ^ 2 - p ^ 2| ≤ 3 * η + (9 / 4) * η ^ 2 := by
    have : (1 - q) ^ 2 - p ^ 2 = -3 * p * η + (9 / 4) * η ^ 2 := by dsimp [q]; ring
    rw [this]
    have htri := abs_add_le (-3 * p * η) ((9 / 4) * η ^ 2)
    have ha : |-3 * p * η| ≤ 3 * η := by
      rw [show -3 * p * η = -(3 * p * η) by ring, abs_neg, abs_of_nonneg (by positivity)]
      have : 3 * p * η ≤ 3 * 1 * η := mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hη0)
      linarith
    have hb : |(9 / 4) * η ^ 2| = (9 / 4) * η ^ 2 := abs_of_nonneg (by positivity)
    linarith
  have hη2_le : η ^ 2 * (n : ℝ) ≤ (1 / 1000) * (η * (n : ℝ)) := by
    have : η ^ 2 * (n : ℝ) = η * (η * (n : ℝ)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hη1 (by linarith)
  have hηn_le : η * (n : ℝ) ≤ (δ / 25) * (n : ℝ) := mul_le_mul_of_nonneg_right hηδ hn0
  constructor
  · intro v
    have hv := hgen.1 v
    rw [h1q] at hv
    linarith
  · intro u v huv
    have huv' := hgen.2 u v huv
    have hmul : (3 * η ^ 2 + |(1 - q) ^ 2 - p ^ 2| + 2 * (8 * η)) * (n : ℝ) + 2 ≤
        (3 * η ^ 2 + (3 * η + (9 / 4) * η ^ 2) + 16 * η) * (n : ℝ) + 2 := by
      have := mul_le_mul_of_nonneg_right h1q2 hn0
      linarith
    linarith

-- ============================================================================
-- MODULE 4: Edge-count accounting & packing glue
-- ============================================================================

-- === MAIN GLUING LEMMAS (0 sorry, 0 helper defs) ===

private lemma r2_card_edgeFinset_map_tree {k n : ℕ} (G : SimpleGraph (Fin k))
    (hG : G.IsTree) {f : Fin k → Fin n} (hf : Function.Injective f) :
    (G.map f).edgeFinset.card = k - 1 := by
  have htree : G.edgeFinset.card + 1 = k := by
    simpa only [Fintype.card_fin] using hG.card_edgeFinset
  have hmap : (G.map f).edgeFinset = G.edgeFinset.image (Sym2.map f) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_image]
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨_, a, b, hab, rfl, rfl⟩
        exact ⟨s(a, b), hab, rfl⟩
      · rintro ⟨e', he', heq⟩
        induction e' using Sym2.ind with
        | _ a b =>
          simp only [SimpleGraph.mem_edgeSet] at he'
          rw [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hf.ne he'.ne, a, b, he', rfl, rfl⟩
          · exact ⟨hf.ne he'.symm.ne, b, a, he'.symm, rfl, rfl⟩
  rw [hmap, Finset.card_image_of_injective _ (Sym2.map.injective hf)]
  omega

private lemma r2_card_edgeFinset_iSup {n : ℕ} (S : Finset ℕ)
    (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k ∈ S, (T k).IsTree)
    (f : (k : S) → Fin k → Fin n)
    (hinj : ∀ k : S, Function.Injective (f k))
    (hdisj : ∀ k l : S, (k : ℕ) < (l : ℕ) →
      Disjoint ((T k).map (f k)).edgeSet ((T l).map (f l)).edgeSet) :
    (⨆ k : S, (T k).map (f k)).edgeFinset.card = ∑ k ∈ S, (k - 1) := by
  have hunion : (⨆ k : S, (T k).map (f k)).edgeFinset =
      S.attach.biUnion (fun k => ((T k).map (f k)).edgeFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_biUnion, Finset.mem_attach, true_and]
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.iSup_adj]
  rw [hunion, Finset.card_biUnion]
  · calc
      ∑ k ∈ S.attach, ((T k).map (f k)).edgeFinset.card
          = ∑ k ∈ S.attach, ((k : ℕ) - 1) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact r2_card_edgeFinset_map_tree (T k) (hT k k.2) (hinj k)
      _ = ∑ k ∈ S, (k - 1) := Finset.sum_attach S (fun k => k - 1)
  · intro k _ l _ hkl
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e hek hel
    rw [SimpleGraph.mem_edgeFinset] at hek hel
    rcases lt_or_gt_of_ne (fun h => hkl (Subtype.ext h)) with hlt | hgt
    · exact Set.disjoint_left.mp (hdisj k l hlt) hek hel
    · exact Set.disjoint_left.mp (hdisj l k hgt) hel hek

private lemma r2_card_edgeFinset_compl {n : ℕ} (P : SimpleGraph (Fin n)) :
    Pᶜ.edgeFinset.card = n.choose 2 - P.edgeFinset.card := by
  have hdisj : Disjoint P.edgeFinset Pᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [SimpleGraph.mem_edgeFinset] at he1 he2
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at he1 he2
      exact he2.2 he1
  have hunion : P.edgeFinset ∪ Pᶜ.edgeFinset = (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
      constructor
      · rintro (h | h)
        · exact h.ne
        · exact h.1
      · intro huv
        by_cases h : P.Adj u v
        · exact Or.inl h
        · exact Or.inr ⟨huv, h⟩
  have htot : (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
    simpa only [Fintype.card_fin] using (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))
  have hadd : P.edgeFinset.card + Pᶜ.edgeFinset.card = n.choose 2 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, htot]
  omega

private lemma r2_glue_packing {n : ℕ} (I S : Finset ℕ)
    (hS : S = Finset.Icc 2 n \ I)
    (T : (k : ℕ) → SimpleGraph (Fin k))
    (f₁ : (k : S) → Fin k → Fin n)
    (hf₁_inj : ∀ k, Function.Injective (f₁ k))
    (hf₁_disj : ∀ k l : S, (k : ℕ) < (l : ℕ) →
      Disjoint ((T k).map (f₁ k)).edgeSet ((T l).map (f₁ l)).edgeSet)
    (f₂ : (k : I) → Fin k → Fin n)
    (hf₂_inj : ∀ k, Function.Injective (f₂ k))
    (hf₂_le : ∀ k : I, (T k).map (f₂ k) ≤ (⨆ j : S, (T j).map (f₁ j))ᶜ)
    (hf₂_disj : ∀ k l : I, (k : ℕ) < (l : ℕ) →
      Disjoint ((T k).map (f₂ k)).edgeSet ((T l).map (f₂ l)).edgeSet) :
    Erdos743.IsPacking n (Set.Icc 2 n) T := by
  let P : SimpleGraph (Fin n) := ⨆ j : S, (T j).map (f₁ j)
  have hmemS : ∀ (k : Set.Icc 2 n), (k : ℕ) ∉ I → (k : ℕ) ∈ S := by
    intro k hk
    rw [hS]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr k.2, hk⟩
  let f : (k : Set.Icc 2 n) → Fin k → Fin n := fun k =>
    if hk : (k : ℕ) ∈ I then
      f₂ ⟨k, hk⟩
    else
      f₁ ⟨k, hmemS k hk⟩
  refine ⟨f, ?_, ?_⟩
  · intro k
    dsimp only [f]
    split_ifs with hk
    · exact hf₂_inj ⟨k, hk⟩
    · exact hf₁_inj ⟨k, hmemS k hk⟩
  · intro k l hkl
    have hcross : ∀ (a : I) (b : S),
        Disjoint ((T a).map (f₂ a)).edgeSet ((T b).map (f₁ b)).edgeSet := by
      intro a b
      rw [Set.disjoint_left]
      intro e hea heb
      induction e using Sym2.ind with
      | _ u v =>
        change ((T a).map (f₂ a)).Adj u v at hea
        change ((T b).map (f₁ b)).Adj u v at heb
        have h1 : Pᶜ.Adj u v := hf₂_le a hea
        have h2 : P.Adj u v := SimpleGraph.iSup_adj.mpr ⟨b, heb⟩
        exact h1.2 h2
    dsimp only [f]
    by_cases hk : (k : ℕ) ∈ I <;> by_cases hl : (l : ℕ) ∈ I
    · simp only [hk, hl, ↓reduceDIte]
      exact hf₂_disj ⟨k, hk⟩ ⟨l, hl⟩ hkl
    · simp only [hk, hl, ↓reduceDIte]
      exact hcross ⟨k, hk⟩ ⟨l, hmemS l hl⟩
    · simp only [hk, hl, ↓reduceDIte]
      exact (hcross ⟨l, hl⟩ ⟨k, hmemS k hk⟩).symm
    · simp only [hk, hl, ↓reduceDIte]
      exact hf₁_disj ⟨k, hmemS k hk⟩ ⟨l, hmemS l hl⟩ hkl

end Helpers

theorem main : H1 → H2 → H3 → type_of% @Erdos743.erdos_743.variants.bounded_degree := by
  intro hH1 hH2 hH3 d
  by_cases hd : d ≤ 2
  · exact bounded_degree_le_two d hd
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨δ₂, hδ₂_pos, N₂, hN₂⟩ := hH2 d hd3
    obtain ⟨δ₃, hδ₃_pos, N₃, hN₃⟩ := hH3 d hd3
    let δ : ℝ := min δ₂ δ₃
    have hδ_pos : 0 < δ := lt_min hδ₂_pos hδ₃_pos
    let η : ℝ := min (δ / 25) (1 / 1000)
    have hη_pos : 0 < η := lt_min (by linarith) (by norm_num)
    have hη_le_δ : η ≤ δ / 25 := min_le_left _ _
    have hη_le_1000 : η ≤ 1 / 1000 := min_le_right _ _
    obtain ⟨N₁, hN₁⟩ := hH1 d hd3 η hη_pos hη_le_1000
    obtain ⟨N_qr, hN_qr⟩ := exists_quasirandom_graph (η ^ 2) (sq_pos_of_pos hη_pos)
    obtain ⟨N_eta, hN_eta⟩ := exists_nat_gt (2 / η)
    refine ⟨max 10000 (max N₁ (max N₂ (max N₃ (max N_qr N_eta)))), fun n hn T hT => ?_⟩
    have hn10000 : 10000 ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
    have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
    have hn_qr : N_qr ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) hn
    have hn_eta : N_eta ≤ n := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) hn
    obtain ⟨I, hI_mid, _, hI_20, hS_card, heI_lo, heI_hi, hcase⟩ :=
      middle_band_dichotomy hn10000 T (fun k hk => (hT k hk).1)
    have hI_sub : I ⊆ Finset.Icc 2 n := by
      intro k hk
      have hkM := Finset.mem_Icc.mp (hI_mid hk)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    let S : Finset ℕ := Finset.Icc 2 n \ I
    have hS_sub : S ⊆ Finset.Icc 2 n := Finset.sdiff_subset
    have hsum_split : ∑ k ∈ S, (k - 1) + ∑ k ∈ I, (k - 1) = n.choose 2 := by
      have hdisj_SI : Disjoint S I := disjoint_sdiff_self_left
      have hunion_SI : S ∪ I = Finset.Icc 2 n := Finset.sdiff_union_of_subset hI_sub
      rw [← Finset.sum_union hdisj_SI, hunion_SI, Erdos743.sum_Icc_two_sub_one]
    have heI_eq : n.choose 2 - ∑ k ∈ S, (k - 1) = ∑ k ∈ I, (k - 1) := by omega
    let p : ℝ := ((n.choose 2 - ∑ k ∈ S, (k - 1) : ℕ) : ℝ) / (n.choose 2 : ℝ)
    have hp_lo : (1 / 40 : ℝ) ≤ p := by
      dsimp only [p]
      rw [heI_eq]
      exact heI_lo
    have hp_hi : p ≤ (1 / 10 : ℝ) := by
      dsimp only [p]
      rw [heI_eq]
      exact heI_hi
    let q : ℝ := 1 - p + (3 / 2 : ℝ) * η
    have hq0 : 0 < q := by dsimp only [q]; linarith
    have hq1 : q < 1 := by dsimp only [q]; linarith
    obtain ⟨G₁, hG₁_deg, hG₁_cod⟩ := hN_qr n hn_qr q hq0 hq1
    have hT_S : ∀ k ∈ S, (T k).IsTree ∧ (T k).maxDegree ≤ d := fun k hk =>
      hT k (Finset.mem_Icc.mp (hS_sub hk))
    obtain ⟨f₁, hf₁_inj, hf₁_disj, hP_le, hrem_deg, hR_even⟩ :=
      hN₁ n hn1 G₁ S T hS_sub hS_card hT_S hp_lo hp_hi hG₁_deg hG₁_cod
    let P : SimpleGraph (Fin n) := ⨆ k : S, (T k).map (f₁ k)
    obtain ⟨R, hReq⟩ : ∃ R : SimpleGraph (Fin n), R = Pᶜ := ⟨Pᶜ, rfl⟩
    have hR_edges : ∑ k ∈ I, (k - 1) = R.edgeFinset.card := by
      have h1 : Pᶜ.edgeFinset.card = n.choose 2 - ∑ k ∈ S, (k - 1) := by
        rw [r2_card_edgeFinset_compl,
          r2_card_edgeFinset_iSup S T (fun k hk => (hT_S k hk).1) f₁ hf₁_inj hf₁_disj]
      have h2 : R.edgeFinset.card = Pᶜ.edgeFinset.card := by
        subst hReq; convert rfl
      omega
    have hR_even' : ∀ v : Fin n, Even (R.degree v) := by
      intro v
      have hdv : R.degree v = Pᶜ.degree v := by subst hReq; convert rfl
      rw [hdv]
      exact hR_even v
    have hp_eq_R : (R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) = p := by
      dsimp only [p]
      rw [← hR_edges, heI_eq]
    have hn_eta_mul : 2 ≤ η * (n : ℝ) := by
      have h1 : 2 / η < (n : ℝ) := lt_of_lt_of_le hN_eta (by exact_mod_cast hn_eta)
      have h2 := (div_lt_iff₀ hη_pos).mp h1
      linarith
    obtain ⟨hR_deg_Pc, hR_cod_Pc⟩ :=
      quasirandom_transfer G₁ P hP_le p η δ (by linarith) (by linarith)
        hη_pos hη_le_δ hη_le_1000 hn_eta_mul hG₁_deg hG₁_cod hrem_deg
    have hR_deg : ∀ v : Fin n, |(R.degree v : ℝ) - p * (n : ℝ)| ≤ δ * (n : ℝ) := by
      intro v
      have hdv : R.degree v = Pᶜ.degree v := by subst hReq; convert rfl
      rw [hdv]
      exact hR_deg_Pc v
    have hR_cod : ∀ u v : Fin n, u ≠ v →
        |((Finset.univ.filter (fun w : Fin n => R.Adj u w ∧ R.Adj v w)).card : ℝ) - p ^ 2 * (n : ℝ)| ≤
          δ * (n : ℝ) := by
      intro u v huv
      have hcv : (Finset.univ.filter (fun w : Fin n => R.Adj u w ∧ R.Adj v w)).card =
          (Finset.univ.filter (fun w : Fin n => Pᶜ.Adj u w ∧ Pᶜ.Adj v w)).card := by
        subst hReq; convert rfl
      rw [hcv]
      exact hR_cod_Pc u v huv
    rcases hcase with hleaf | hbare
    · have hR_deg₂ : ∀ v : Fin n, |(R.degree v : ℝ) - ((R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) * n| ≤ δ₂ * n := by
        intro v
        rw [hp_eq_R]
        exact le_trans (hR_deg v) (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
      have hR_cod₂ : ∀ u v : Fin n, u ≠ v →
          |((Finset.univ.filter (fun w : Fin n => R.Adj u w ∧ R.Adj v w)).card : ℝ) -
            ((R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ 2 * n| ≤ δ₂ * n := by
        intro u v huv
        rw [hp_eq_R]
        exact le_trans (hR_cod u v huv) (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
      obtain ⟨f₂, hf₂_inj, hf₂_le, hf₂_disj⟩ :=
        hN₂ n hn2 R I T hI_mid hI_20 hR_edges hR_even'
          (by rw [hp_eq_R]; exact hp_lo) (by rw [hp_eq_R]; exact hp_hi)
          hR_deg₂ hR_cod₂
          (fun k hk => ⟨(hT k (Finset.mem_Icc.mp (hI_sub hk))).1,
            (hT k (Finset.mem_Icc.mp (hI_sub hk))).2, hleaf k hk⟩)
      exact r2_glue_packing I S rfl T f₁ hf₁_inj hf₁_disj f₂ hf₂_inj (fun k => by rw [← hReq]; exact hf₂_le k) hf₂_disj
    · have hR_deg₃ : ∀ v : Fin n, |(R.degree v : ℝ) - ((R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) * n| ≤ δ₃ * n := by
        intro v
        rw [hp_eq_R]
        exact le_trans (hR_deg v) (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
      have hR_cod₃ : ∀ u v : Fin n, u ≠ v →
          |((Finset.univ.filter (fun w : Fin n => R.Adj u w ∧ R.Adj v w)).card : ℝ) -
            ((R.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ 2 * n| ≤ δ₃ * n := by
        intro u v huv
        rw [hp_eq_R]
        exact le_trans (hR_cod u v huv) (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
      obtain ⟨f₂, hf₂_inj, hf₂_le, hf₂_disj⟩ :=
        hN₃ n hn3 R I T hI_mid hI_20 hR_edges hR_even'
          (by rw [hp_eq_R]; exact hp_lo) (by rw [hp_eq_R]; exact hp_hi)
          hR_deg₃ hR_cod₃
          (fun k hk => ⟨(hT k (Finset.mem_Icc.mp (hI_sub hk))).1,
            (hT k (Finset.mem_Icc.mp (hI_sub hk))).2, (hbare k hk).1, (hbare k hk).2⟩)
      exact r2_glue_packing I S rfl T f₁ hf₁_inj hf₁_disj f₂ hf₂_inj (fun k => by rw [← hReq]; exact hf₂_le k) hf₂_disj

end OMA.R_Erdos743_erdos_743_variants_bounded_degree_R2
