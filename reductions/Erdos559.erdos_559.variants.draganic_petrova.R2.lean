import FormalConjectures.ErdosProblems.«559»

/-!
Reduction Erdos559.erdos_559.variants.draganic_petrova.R2
Credit: @Progren
Fixes the inconsistent upper-uniformity clause in R1 (where bounding by `4 * U'.card * X'.card * p`
for arbitrary `X'` of size `≤ c * N` allowed singletons `X' = {u}`, forcing `1 ≤ 4 * p` and
`4 * c^2 * N^2 ≤ |E(Γ)|`, making `R1.H2` provably false).
Matches Draganić–Petrova (2022, arXiv:2207.05048):
  - allows passing to a monochromatic subgraph `F₀ ≤ R ∨ F₀ ≤ Γ \ R` (supporting subsampling `G₀ ⊆ Γ`),
  - bounds `e_{F₀}(U', X') ≤ 4 * U'.card * (c * N) * p` for `|U'| ≥ K₀ / p`, `|X'| ≤ c * N`, `Disjoint X' V₂₁`.
Splits into:
  H1: 1-degenerate decomposition into a bounded-treewidth tree-blowup subgraph and long induced cycles
  H2: Draganić–Petrova host graph construction with tree-blowup embedding, degree, upper-uniformity, and cycle embedding
  H3: two-layer (`bit ∈ {0, 1}`) inductive 1-degenerate embedding of the cycle sequence into the 20 regular parts
-/

namespace OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R2

open Filter Real SimpleGraph

def H1 : Prop :=
  open scoped Classical in
  ∀ (ℓ : ℕ), 5 ≤ ℓ → ∀ (n : ℕ), 1 ≤ n → ∀ (G : SimpleGraph (Fin n)), G.maxDegree ≤ 3 →
    ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (V₀ : Finset (Fin n)) (parts : List (Finset (Fin n))),
      1 ≤ m ∧ m ≤ n ∧ T.IsTree ∧ T.maxDegree ≤ 400 * ℓ ∧
      (∀ x : Fin n, x ∈ V₀ ∨ ∃ C ∈ parts, x ∈ C) ∧
      (∀ C ∈ parts, Disjoint V₀ C) ∧ parts.Pairwise Disjoint ∧
      (∃ φ : V₀ ↪ Fin m × Fin (400 * ℓ),
        ∀ u v : V₀, G.Adj u.1 v.1 → (φ u).1 = (φ v).1 ∨ T.Adj (φ u).1 (φ v).1) ∧
      (∀ C ∈ parts, ℓ ≤ C.card ∧ ∃ e : C ≃ Fin C.card,
        ∀ u v : C, G.Adj u.1 v.1 ↔
          (((e u : ℕ) + 1) % C.card = (e v : ℕ) ∨ ((e v : ℕ) + 1) % C.card = (e u : ℕ))) ∧
      (∀ (i : ℕ) (hi : i < parts.length), ∀ v ∈ parts[i],
        (Finset.univ.filter (fun u => G.Adj v u ∧
          (u ∈ V₀ ∨ ∃ (j : ℕ) (hj : j < i), u ∈ parts[j]'(lt_trans hj hi)))).card ≤ 1)

def H2 : Prop :=
  open scoped Classical in
  ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 100 → ∀ (ℓ : ℕ), 5 ≤ ℓ → 1 < δ * (4 * (ℓ : ℝ) - 6) →
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∃ (Γ : SimpleGraph (Fin N)), (Γ.edgeSet.ncard : ℝ) ≤ (N : ℝ) ^ (3 / 2 + 2 * δ) ∧
        ∀ (R : SimpleGraph (Fin N)), R ≤ Γ →
          ∃ (F₀ : SimpleGraph (Fin N)) (V : Fin 10 → Fin 2 → Finset (Fin N)) (V₂₁ : Finset (Fin N))
            (nt : ℕ) (p d K₀ : ℝ),
            (F₀ ≤ R ∨ F₀ ≤ Γ \ R) ∧ 0 < p ∧ 0 < d ∧ 0 < K₀ ∧
            16 * c * N * p < nt * d ∧ 3 * K₀ / p ≤ nt * d / 4 ∧ 1 ≤ nt * d / 20 ∧
            2 * c * N ≤ V₂₁.card ∧ (∀ a b, (V a b).card = nt ∧ Disjoint (V a b) V₂₁) ∧
            (∀ a₁ b₁ a₂ b₂, (a₁, b₁) ≠ (a₂, b₂) → Disjoint (V a₁ b₁) (V a₂ b₂)) ∧
            (∀ (m : ℕ) (T : SimpleGraph (Fin m)), 1 ≤ m → (m : ℝ) ≤ c * N →
              T.IsTree → T.maxDegree ≤ 400 * ℓ →
              ∃ ψ : Fin m × Fin (400 * ℓ) ↪ V₂₁,
                ∀ x y, ((x.1 = y.1 ∧ x.2 ≠ y.2) ∨ T.Adj x.1 y.1) → F₀.Adj (ψ x).1 (ψ y).1) ∧
            (∀ u a b, (u ∈ V₂₁ ∨ ∃ a' b', a' ≠ a ∧ u ∈ V a' b') →
              nt * d / 2 ≤ ((V a b).filter (F₀.Adj u)).card) ∧
            (∀ U' X' : Finset (Fin N), K₀ / p ≤ U'.card → (X'.card : ℝ) ≤ c * N →
              Disjoint X' V₂₁ →
              ((U' ×ˢ X').filter (fun e => F₀.Adj e.1 e.2)).card ≤ 4 * U'.card * (c * N) * p) ∧
            (∀ (L : ℕ) [NeZero L], ℓ ≤ L → (L : ℝ) ≤ c * N →
              ∀ (col : Fin L → Fin 10) (bit : Fin L → Fin 2) (u : Fin L → Fin N)
                (S : Fin L → Finset (Fin N)),
                (∀ r, col r ≠ col (r + 1)) →
                (∀ x, (Finset.univ.filter (u · = x)).card ≤ 3) →
                (∀ r, u r ∈ V₂₁ ∨ ∃ a' b', a' ≠ col r ∧ a' ≠ col (r + 1) ∧ a' ≠ col (r - 1) ∧ u r ∈ V a' b') →
                (∀ r, S r ⊆ (V (col r) (bit r)).filter (F₀.Adj (u r)) ∧ nt * d / 20 ≤ (S r).card) →
                ∃ f : Fin L ↪ Fin N, (∀ r, f r ∈ S r) ∧ ∀ r, F₀.Adj (f r) (f (r + 1)))

def H3 : Prop :=
  open scoped Classical in
  ∀ (N n ℓ : ℕ) (c p d K₀ : ℝ) (nt : ℕ) (F₀ : SimpleGraph (Fin N))
    (V : Fin 10 → Fin 2 → Finset (Fin N)) (V₂₁ : Finset (Fin N))
    (G : SimpleGraph (Fin n)) (V₀ : Finset (Fin n)) (parts : List (Finset (Fin n)))
    (emb₀ : V₀ ↪ V₂₁),
    5 ≤ ℓ → 1 ≤ n → (n : ℝ) ≤ c * N → G.maxDegree ≤ 3 →
    0 < c → 0 < p → 0 < d → 0 < K₀ →
    16 * c * N * p < nt * d → 3 * K₀ / p ≤ nt * d / 4 → 1 ≤ nt * d / 20 →
    2 * c * N ≤ V₂₁.card → (∀ a b, (V a b).card = nt ∧ Disjoint (V a b) V₂₁) →
    (∀ a₁ b₁ a₂ b₂, (a₁, b₁) ≠ (a₂, b₂) → Disjoint (V a₁ b₁) (V a₂ b₂)) →
    (∀ u a b, (u ∈ V₂₁ ∨ ∃ a' b', a' ≠ a ∧ u ∈ V a' b') →
      nt * d / 2 ≤ ((V a b).filter (F₀.Adj u)).card) →
    (∀ U' X' : Finset (Fin N), K₀ / p ≤ U'.card → (X'.card : ℝ) ≤ c * N →
      Disjoint X' V₂₁ →
      ((U' ×ˢ X').filter (fun e => F₀.Adj e.1 e.2)).card ≤ 4 * U'.card * (c * N) * p) →
    (∀ (L : ℕ) [NeZero L], ℓ ≤ L → (L : ℝ) ≤ c * N →
      ∀ (col : Fin L → Fin 10) (bit : Fin L → Fin 2) (u : Fin L → Fin N)
        (S : Fin L → Finset (Fin N)),
        (∀ r, col r ≠ col (r + 1)) →
        (∀ x, (Finset.univ.filter (u · = x)).card ≤ 3) →
        (∀ r, u r ∈ V₂₁ ∨ ∃ a' b', a' ≠ col r ∧ a' ≠ col (r + 1) ∧ a' ≠ col (r - 1) ∧ u r ∈ V a' b') →
        (∀ r, S r ⊆ (V (col r) (bit r)).filter (F₀.Adj (u r)) ∧ nt * d / 20 ≤ (S r).card) →
        ∃ f : Fin L ↪ Fin N, (∀ r, f r ∈ S r) ∧ ∀ r, F₀.Adj (f r) (f (r + 1))) →
    (∀ x, x ∈ V₀ ∨ ∃ C ∈ parts, x ∈ C) →
    (∀ C ∈ parts, Disjoint V₀ C) → parts.Pairwise Disjoint →
    (∀ u v : V₀, G.Adj u.1 v.1 → F₀.Adj (emb₀ u).1 (emb₀ v).1) →
    (∀ C ∈ parts, ℓ ≤ C.card ∧ ∃ e : C ≃ Fin C.card,
      ∀ u v : C, G.Adj u.1 v.1 ↔
        (((e u : ℕ) + 1) % C.card = (e v : ℕ) ∨ ((e v : ℕ) + 1) % C.card = (e u : ℕ))) →
    (∀ (i : ℕ) (hi : i < parts.length), ∀ v ∈ parts[i],
      (Finset.univ.filter (fun u => G.Adj v u ∧
        (u ∈ V₀ ∨ ∃ (j : ℕ) (hj : j < i), u ∈ parts[j]'(lt_trans hj hi)))).card ≤ 1) →
    G.IsContained F₀

theorem main : H1 → H2 → H3 → type_of% @Erdos559.erdos_559.variants.draganic_petrova := by
  classical
  intro h1 h2 h3 ε hε
  set δ : ℝ := min (ε / 4) (1 / 100)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 100 := min_le_right _ _
  have h2δ : 2 * δ ≤ ε / 2 := by
    have : δ ≤ ε / 4 := min_le_left _ _
    linarith
  set ℓ : ℕ := Nat.ceil (1 / δ) + 5
  have hℓ5 : 5 ≤ ℓ := by omega
  have hδℓ : 1 < δ * (4 * (ℓ : ℝ) - 6) := by
    have hceil : 1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil (1 / δ)
    have hℓ_r : 1 / δ + 5 ≤ (ℓ : ℝ) := by
      dsimp only [ℓ]
      push_cast
      linarith
    have h4 : 4 / δ + 14 ≤ 4 * (ℓ : ℝ) - 6 := by
      have : 4 * (1 / δ) = 4 / δ := by ring
      linarith
    calc (1 : ℝ) < 4 + 14 * δ := by linarith
      _ = δ * (4 / δ + 14) := by field_simp [hδ0.ne']
      _ ≤ δ * (4 * (ℓ : ℝ) - 6) := mul_le_mul_of_nonneg_left h4 hδ0.le
  obtain ⟨c, N₀, hc0, hΓ⟩ := h2 δ hδ0 hδ1 ℓ hℓ5 hδℓ
  set M_pow : ℝ := ((2 / c) ^ (3 / 2 + 2 * δ)) ^ (2 / ε)
  set N_min : ℕ := max 1 (max N₀ (max (Nat.ceil (c * (N₀ : ℝ) + 1)) (max (Nat.ceil c) (Nat.ceil M_pow))))
  refine eventually_atTop.mpr ⟨N_min, fun n hn G hGdeg => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hcn0 : c * (N₀ : ℝ) + 1 ≤ (n : ℝ) := by
    have h1 : Nat.ceil (c * (N₀ : ℝ) + 1) ≤ n :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hc_le_n : c ≤ (n : ℝ) := by
    have h1 : Nat.ceil c ≤ n :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hM_le_n : M_pow ≤ (n : ℝ) := by
    have h1 : Nat.ceil M_pow ≤ n :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  set N : ℕ := max N₀ (Nat.ceil ((n : ℝ) / c))
  have hN_ge_N0 : N₀ ≤ N := le_max_left _ _
  have hn_le_cN : (n : ℝ) ≤ c * (N : ℝ) := by
    have h1 : (n : ℝ) / c ≤ (Nat.ceil ((n : ℝ) / c) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil ((n : ℝ) / c) : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right N₀ _
    exact (div_le_iff₀' hc0).mp (h1.trans h2)
  have hN_le : (N : ℝ) ≤ (2 / c) * (n : ℝ) := by
    have hN0_le : (N₀ : ℝ) ≤ (n : ℝ) / c := by
      rw [le_div_iff₀ hc0]
      linarith
    have hceil_le : (Nat.ceil ((n : ℝ) / c) : ℝ) < (n : ℝ) / c + 1 := Nat.ceil_lt_add_one (by positivity)
    have hceil_le2 : (Nat.ceil ((n : ℝ) / c) : ℝ) ≤ (2 / c) * (n : ℝ) := by
      have h1 : 1 ≤ (n : ℝ) / c := (le_div_iff₀ hc0).mpr (by linarith)
      have : (n : ℝ) / c + 1 ≤ (2 / c) * (n : ℝ) := by
        have : (n : ℝ) / c + (n : ℝ) / c = (2 / c) * (n : ℝ) := by ring
        linarith
      linarith
    have hN0_le2 : (N₀ : ℝ) ≤ (2 / c) * (n : ℝ) := by
      have : (n : ℝ) / c ≤ (2 / c) * (n : ℝ) := by
        have : 0 ≤ (n : ℝ) / c := by positivity
        have : (2 / c) * (n : ℝ) = 2 * ((n : ℝ) / c) := by ring
        linarith
      exact hN0_le.trans this
    dsimp only [N]
    rw [Nat.cast_max]
    exact max_le hN0_le2 hceil_le2
  obtain ⟨Γ, hΓ_edges, hΓ_ramsey⟩ := hΓ N hN_ge_N0
  obtain ⟨m, T, V₀, parts, hm1, hmn, hTtree, hTdeg, hcov, hdisjV, hdisjP, ⟨φ, hφ⟩, hcyc, hdeg1⟩ :=
    h1 ℓ hℓ5 n hn1 G hGdeg
  have hm_le_cN : (m : ℝ) ≤ c * (N : ℝ) := le_trans (by exact_mod_cast hmn) hn_le_cN
  have hramsey : ∀ R : SimpleGraph (Fin N), R ≤ Γ → G.IsContained R ∨ G.IsContained (Γ \ R) := by
    intro R hR
    obtain ⟨F₀, V, V₂₁, nt, p, d, K₀, hF₀, hp0, hd0, hK0, h16c, h3K, hnd20,
      h2cN, hVcard, hVdisj, htree_emb, hdeg_lb, hupper, hcyc_emb⟩ := hΓ_ramsey R hR
    obtain ⟨ψ, hψ⟩ := htree_emb m T hm1 hm_le_cN hTtree hTdeg
    let emb₀ : V₀ ↪ V₂₁ := φ.trans ψ
    have hemb₀ : ∀ u v : V₀, G.Adj u.1 v.1 → F₀.Adj (emb₀ u).1 (emb₀ v).1 := by
      intro u v huv
      refine hψ (φ u) (φ v) ?_
      rcases hφ u v huv with heq | hadj
      · left
        refine ⟨heq, fun heq2 => ?_⟩
        have hne_uv : u ≠ v := fun h => G.ne_of_adj huv (congrArg Subtype.val h)
        have hne_phi : φ u ≠ φ v := fun h => hne_uv (φ.injective h)
        exact hne_phi (Prod.ext heq heq2)
      · exact Or.inr hadj
    have hcont : G.IsContained F₀ :=
      h3 N n ℓ c p d K₀ nt F₀ V V₂₁ G V₀ parts emb₀ hℓ5 hn1 hn_le_cN hGdeg hc0
        hp0 hd0 hK0 h16c h3K hnd20 h2cN hVcard hVdisj hdeg_lb hupper hcyc_emb
        hcov hdisjV hdisjP hemb₀ hcyc hdeg1
    obtain ⟨e, he⟩ := SimpleGraph.isContained_iff_exists_le_comap.mp hcont
    rcases hF₀ with hle | hle
    · exact Or.inl (SimpleGraph.isContained_iff_exists_le_comap.mpr ⟨e, fun {_ _} hab => hle (he hab)⟩)
    · exact Or.inr (SimpleGraph.isContained_iff_exists_le_comap.mpr ⟨e, fun {_ _} hab => hle (he hab)⟩)
  have hSR_le : SimpleGraph.sizeRamsey G G ≤ Γ.edgeSet.ncard := by
    rw [SimpleGraph.sizeRamsey]
    exact Nat.sInf_le ⟨N, Γ, rfl, hramsey⟩
  have hSR_real : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (Γ.edgeSet.ncard : ℝ) := by exact_mod_cast hSR_le
  have hN_pow : (N : ℝ) ^ (3 / 2 + 2 * δ) ≤ (n : ℝ) ^ (3 / 2 + ε) := by
    have hN0_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2c_pos : 0 < 2 / c := by positivity
    have hbase1 : (N : ℝ) ^ (3 / 2 + 2 * δ) ≤ ((2 / c) * (n : ℝ)) ^ (3 / 2 + 2 * δ) :=
      Real.rpow_le_rpow hN0_nn hN_le (by positivity)
    have hsplit : ((2 / c) * (n : ℝ)) ^ (3 / 2 + 2 * δ) =
        (2 / c) ^ (3 / 2 + 2 * δ) * (n : ℝ) ^ (3 / 2 + 2 * δ) :=
      Real.mul_rpow h2c_pos.le (Nat.cast_nonneg n)
    have hc_pow : (2 / c) ^ (3 / 2 + 2 * δ) ≤ (n : ℝ) ^ (ε / 2) := by
      have h1 : M_pow ^ (ε / 2) = (2 / c) ^ (3 / 2 + 2 * δ) := by
        dsimp only [M_pow]
        rw [← Real.rpow_mul (by positivity), show (2 / ε) * (ε / 2) = 1 by field_simp,
          Real.rpow_one]
      rw [← h1]
      exact Real.rpow_le_rpow (by positivity) hM_le_n (by positivity)
    have hn_pow_le : (n : ℝ) ^ (3 / 2 + 2 * δ) ≤ (n : ℝ) ^ (3 / 2 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
    have hprod_eq : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (3 / 2 + ε / 2) = (n : ℝ) ^ (3 / 2 + ε) := by
      rw [← Real.rpow_add hn_pos]
      congr 1
      ring
    calc (N : ℝ) ^ (3 / 2 + 2 * δ)
        ≤ (2 / c) ^ (3 / 2 + 2 * δ) * (n : ℝ) ^ (3 / 2 + 2 * δ) := hbase1.trans_eq hsplit
      _ ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (3 / 2 + ε / 2) :=
          mul_le_mul hc_pow hn_pow_le (by positivity) (by positivity)
      _ = (n : ℝ) ^ (3 / 2 + ε) := hprod_eq
  exact hSR_real.trans (hΓ_edges.trans hN_pow)

end OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R2
