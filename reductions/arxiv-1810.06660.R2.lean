import OMAStatements.S_arxiv_1810_06660

/-!
# Round 2 Reduction for Cioabă–Guo–Haemers Conjecture 1.2 (`arxiv-1810.06660`)

Building on the complete multipartite (`μ = k`) and low-degree (`k ≤ 3`, Petersen uniqueness)
classifications, this second-stage reduction (`R2`) proves unconditionally:
1. **Class-1 Edge-Coloring of `SRG(10, 6, 3, 4)` (`srg_10_6_3_4_colorable`):**
   Every `SRG(10, 6, 3, 4)` has complement `SRG(10, 3, 0, 1) ≃g petersen` (`G ≃g L(K_5)`), and we
   transfer a kernel-verified 6-edge-coloring across the canonical labeling to prove `Colorable 6`.
2. **Even-Order SRG Eigenvalue Integrality & Multiplicity Theorem (`even_srg_integral_conditions`):**
   Using the Hermitian spectrum of `G.adjMatrix ℝ`, every non-principal eigenvalue on `1^⊥`
   satisfies `λ^2 - (ℓ - μ) λ - (k - μ) = 0`. Since `Even n` forces `f + g = n - 1` to be odd,
   the multiplicities `f ≠ g` cannot be equal, forcing `Δ = (ℓ - μ)^2 + 4 * (k - μ) = d^2` (`d > 0`)
   and `2 * k + (n - 1) * (ℓ - μ) + (f - g) * d = 0`.
3. **Complete Elimination of All Even Orders `n ≤ 14` (`srg_even_order_le_14_colorable`):**
   Combining spectral integrality with the SRG parameter equation eliminates every primitive
   parameter tuple with `Even n` and `n ≤ 14` except `(10, 3, 0, 1)` (Petersen) and `(10, 6, 3, 4)`
   (`petersenᶜ`, proved Class 1), establishing `16 ≤ n` and `4 ≤ k` for all remaining cases.

We then reduce the remaining problem (`16 ≤ n`, `4 ≤ k`) into:
- `H1`: **Chetwynd–Hilton 1-Factorization / Overfull Regular Graph Conjecture** for `16 ≤ n`
  (`n ≤ 2 * k`, a pure regular-graph statement independent of SRGs), and
- `H2`: **Sparse Integral Primitive Even-Order SRGs** (`16 ≤ n`, `4 ≤ k`, `2 * k < n`, `1 ≤ μ < k`)
  equipped with explicit eigenvalue integrality witnesses `(d, f, g)`.
-/

namespace OMA.R_arxiv_1810_06660_R2

/-! ## Section 1: Line-Graph Clique Lower Bound and `k`-Colorable Equivalence -/

theorem lineGraph_colorable_of_symm_fn {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → V → Fin k)
    (hsym : ∀ u v, c u v = c v u)
    (hinj : ∀ u v w, G.Adj u v → G.Adj u w → v ≠ w → c u v ≠ c u w) :
    G.lineGraph.Colorable k := by
  let f : Sym2 V → Fin k := Sym2.lift ⟨c, hsym⟩
  refine ⟨SimpleGraph.Coloring.mk (fun e => f e.1) ?_⟩
  intro e₁ e₂ hadj
  obtain ⟨hne, u, hu₁, hu₂⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
  rcases e₁ with ⟨e₁, he₁⟩
  rcases e₂ with ⟨e₂, he₂⟩
  induction e₁ using Sym2.ind with
  | _ a₁ b₁ =>
    induction e₂ using Sym2.ind with
    | _ a₂ b₂ =>
      have hadj₁ : G.Adj a₁ b₁ := G.mem_edgeSet.mp he₁
      have hadj₂ : G.Adj a₂ b₂ := G.mem_edgeSet.mp he₂
      have hne_sym : s(a₁, b₁) ≠ s(a₂, b₂) := fun h => hne (Subtype.ext h)
      change c a₁ b₁ ≠ c a₂ b₂
      rcases Sym2.mem_iff.mp hu₁ with rfl | rfl <;>
        rcases Sym2.mem_iff.mp hu₂ with rfl | rfl
      · exact hinj u b₁ b₂ hadj₁ hadj₂ (fun h => hne_sym (h ▸ rfl))
      · rw [hsym a₂ u]
        exact hinj u b₁ a₂ hadj₁ hadj₂.symm (fun h => hne_sym (h ▸ Sym2.eq_swap))
      · rw [hsym a₁ u]
        exact hinj u a₁ b₂ hadj₁.symm hadj₂ (fun h => hne_sym (h ▸ Sym2.eq_swap))
      · rw [hsym a₁ u, hsym a₂ u]
        exact hinj u a₁ a₂ hadj₁.symm hadj₂.symm (fun h => hne_sym (h ▸ rfl))

theorem lineGraph_exists_isNClique_of_regular {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree k) (hn : 0 < n) :
    ∃ s : Finset G.edgeSet, G.lineGraph.IsNClique k s := by
  let v₀ : Fin n := ⟨0, hn⟩
  let emb : {w : Fin n // w ∈ G.neighborFinset v₀} ↪ G.edgeSet :=
    { toFun := fun w => ⟨s(v₀, w.1), G.mem_edgeSet.mpr ((G.mem_neighborFinset v₀ w.1).mp w.2)⟩
      inj' := by
        intro w₁ w₂ h
        have hs : s(v₀, w₁.1) = s(v₀, w₂.1) := Subtype.mk.inj h
        rcases Sym2.eq_iff.mp hs with ⟨-, hw⟩ | ⟨hv, -⟩
        · exact Subtype.ext hw
        · exact absurd hv (G.ne_of_adj ((G.mem_neighborFinset v₀ w₂.1).mp w₂.2)) }
  refine ⟨(G.neighborFinset v₀).attach.map emb, ?_, ?_⟩
  · intro e₁ he₁ e₂ he₂ hne
    rw [Finset.mem_coe, Finset.mem_map] at he₁ he₂
    rcases he₁ with ⟨w₁, -, rfl⟩
    rcases he₂ with ⟨w₂, -, rfl⟩
    refine SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v₀, ?_, ?_⟩
    · show v₀ ∈ s(v₀, w₁.1)
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    · show v₀ ∈ s(v₀, w₂.1)
      exact Sym2.mem_iff.mpr (Or.inl rfl)
  · rw [Finset.card_map, Finset.card_attach, G.card_neighborFinset_eq_degree, hreg v₀]

theorem le_lineGraph_chromaticNumber_of_regular {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree k) (hn : 0 < n) :
    (k : ℕ∞) ≤ G.lineGraph.chromaticNumber := by
  obtain ⟨s, hs⟩ := lineGraph_exists_isNClique_of_regular G hreg hn
  exact hs.card_eq ▸ hs.isClique.card_le_chromaticNumber

theorem lineGraph_chromaticNumber_eq_iff_colorable {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree k) (hn : 0 < n) :
    G.lineGraph.chromaticNumber = (k : ℕ∞) ↔ G.lineGraph.Colorable k := by
  constructor
  · intro h
    exact SimpleGraph.chromaticNumber_le_iff_colorable.mp h.le
  · intro hcol
    exact le_antisymm hcol.chromaticNumber_le (le_lineGraph_chromaticNumber_of_regular G hreg hn)

theorem lineGraph_chromaticNumber_eq_of_colorable {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree k) (hn : 0 < n)
    (hcol : G.lineGraph.Colorable k) :
    G.lineGraph.chromaticNumber = (k : ℕ∞) :=
  (lineGraph_chromaticNumber_eq_iff_colorable G hreg hn).mpr hcol

/-! ## Section 2: SRG Parameter Bounds and Complete Multipartite SRGs (`μ = k`) -/

theorem srg_four_le_n {n k : ℕ} (hk : 0 < k) (hkn : k < n - 1) (heven : Even n) :
    4 ≤ n := by
  rcases heven with ⟨r, rfl⟩
  omega

theorem srg_regular_exists_not_adj {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree k) (hkn : k < n - 1) (v : Fin n) :
    ∃ w : Fin n, v ≠ w ∧ ¬ G.Adj v w := by
  by_contra! hall
  have huniv : insert v (G.neighborFinset v) = Finset.univ := by
    ext w
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, Finset.mem_univ, iff_true]
    by_cases hvw : w = v
    · exact Or.inl hvw
    · exact Or.inr (hall w (Ne.symm hvw))
  have hcard : (insert v (G.neighborFinset v)).card ≤ 1 + k := by
    calc (insert v (G.neighborFinset v)).card
      _ ≤ (G.neighborFinset v).card + 1 := Finset.card_insert_le v (G.neighborFinset v)
      _ = k + 1 := by rw [G.card_neighborFinset_eq_degree, hreg v]
      _ = 1 + k := Nat.add_comm k 1
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem srg_mu_le_k {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hn : 0 < n) (hkn : k < n - 1) :
    μ ≤ k := by
  let v₀ : Fin n := ⟨0, hn⟩
  obtain ⟨w, hne, hna⟩ := srg_regular_exists_not_adj G hSRG.regular hkn v₀
  calc μ = Fintype.card (G.commonNeighbors v₀ w) := (hSRG.of_not_adj hne hna).symm
    _ ≤ G.degree v₀ := G.card_commonNeighbors_le_degree_left v₀ w
    _ = k := hSRG.regular v₀

theorem srg_one_le_mu {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1) (hconn : G.Connected) :
    1 ≤ μ := by
  have hn : 0 < n := by omega
  let v₀ : Fin n := ⟨0, hn⟩
  by_contra hμ0
  have hμ : μ = 0 := by omega
  have hwalk : ∀ x y : Fin n, G.Walk x y → (x = v₀ ∨ G.Adj v₀ x) → (y = v₀ ∨ G.Adj v₀ y) := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons a b c hab _ ih =>
      intro ha
      apply ih
      rcases ha with rfl | hadj
      · exact Or.inr hab
      · by_cases hbv : b = v₀
        · exact Or.inl hbv
        · refine Or.inr ?_
          by_contra hnab
          have hmem : a ∈ G.commonNeighbors v₀ b := ⟨hadj, hab.symm⟩
          have hpos : 0 < Fintype.card (G.commonNeighbors v₀ b) :=
            Fintype.card_pos_iff.mpr ⟨⟨a, hmem⟩⟩
          have heq := hSRG.of_not_adj (Ne.symm hbv) hnab
          omega
  obtain ⟨w, hne, hna⟩ := srg_regular_exists_not_adj G hSRG.regular hkn v₀
  rcases (hconn v₀ w).elim (fun p => hwalk v₀ w p (Or.inl rfl)) with rfl | hadj
  · exact hne rfl
  · exact hna hadj

theorem srg_mul_add_inj_of_lt {a₁ a₂ b₁ b₂ s : ℕ} (hb₁ : b₁ < s) (hb₂ : b₂ < s)
    (heq : a₁ * s + b₁ = a₂ * s + b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ha : a₁ = a₂ := by
    rcases lt_trichotomy a₁ a₂ with hlt | rfl | hgt
    · exfalso
      have h1 : (a₁ + 1) * s ≤ a₂ * s := Nat.mul_le_mul_right s hlt
      have h2 : a₁ * s + b₁ < (a₁ + 1) * s := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      omega
    · rfl
    · exfalso
      have h1 : (a₂ + 1) * s ≤ a₁ * s := Nat.mul_le_mul_right s hgt
      have h2 : a₂ * s + b₂ < (a₂ + 1) * s := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      omega
  subst ha
  exact ⟨rfl, by omega⟩

theorem srg_exists_kirkman_factorization (r : ℕ) (hr : 1 ≤ r) :
    ∃ kcol : ℕ → ℕ → ℕ,
      (∀ u v, u < 2 * r → v < 2 * r → kcol u v < 2 * r - 1) ∧
      (∀ u v, kcol u v = kcol v u) ∧
      (∀ u v₁ v₂, u < 2 * r → v₁ < 2 * r → v₂ < 2 * r →
        u ≠ v₁ → u ≠ v₂ → kcol u v₁ = kcol u v₂ → v₁ = v₂) ∧
      (∀ u v, u < 2 * r → v < 2 * r → u ≠ v →
        (kcol u v = 0 ↔
          (u = 0 ∧ v = 2 * r - 1) ∨ (u = 2 * r - 1 ∧ v = 0) ∨
          (0 < u ∧ u < 2 * r - 1 ∧ v = 2 * r - 1 - u))) := by
  refine ⟨fun u v =>
    if u = v then 0
    else if u = 2 * r - 1 then
      if 2 * v < 2 * r - 1 then 2 * v else 2 * v - (2 * r - 1)
    else if v = 2 * r - 1 then
      if 2 * u < 2 * r - 1 then 2 * u else 2 * u - (2 * r - 1)
    else
      if u + v < 2 * r - 1 then u + v else u + v - (2 * r - 1),
    ?_, ?_, ?_, ?_⟩
  · intro u v hu hv
    dsimp only
    split_ifs <;> omega
  · intro u v
    dsimp only
    split_ifs <;> omega
  · intro u v₁ v₂ hu hv₁ hv₂ hne₁ hne₂ heq
    dsimp only at heq
    split_ifs at heq <;> omega
  · intro u v hu hv hne
    dsimp only
    split_ifs <;> constructor <;> intro h <;> omega

theorem completeEquipartiteGraph_lineGraph_colorable (m t : ℕ)
    (hm : 2 ≤ m) (ht : 1 ≤ t) (heven : Even (m * t)) :
    (SimpleGraph.completeEquipartiteGraph m t).lineGraph.Colorable ((m - 1) * t) := by
  rcases Nat.even_mul.mp heven with hm_even | ht_even
  · rcases hm_even with ⟨r, hr⟩
    have hr1 : 1 ≤ r := by omega
    obtain ⟨kcol, hk_lt, hk_sym, hk_inj, -⟩ := srg_exists_kirkman_factorization r hr1
    let shift : ℕ → ℕ → ℕ := fun x y => if x + y < t then x + y else x + y - t
    have hshift_lt : ∀ x y, x < t → y < t → shift x y < t := by
      intro x y hx hy
      dsimp only [shift]
      split_ifs <;> omega
    have hshift_sym : ∀ x y, shift x y = shift y x := by
      intro x y
      dsimp only [shift]
      split_ifs <;> omega
    have hshift_inj : ∀ x y₁ y₂, x < t → y₁ < t → y₂ < t → shift x y₁ = shift x y₂ → y₁ = y₂ := by
      intro x y₁ y₂ hx hy₁ hy₂ heq
      dsimp only [shift] at heq
      split_ifs at heq <;> omega
    have hbound : ∀ p q : Fin m × Fin t, kcol p.1.1 q.1.1 * t + shift p.2.1 q.2.1 < (m - 1) * t := by
      intro p q
      have hp1 := p.1.2
      have hq1 := q.1.2
      have ha : kcol p.1.1 q.1.1 < m - 1 := by
        have := hk_lt p.1.1 q.1.1 (by omega) (by omega)
        omega
      have hb : shift p.2.1 q.2.1 < t := hshift_lt p.2.1 q.2.1 p.2.2 q.2.2
      have h1 : (kcol p.1.1 q.1.1 + 1) * t ≤ (m - 1) * t := Nat.mul_le_mul_right t ha
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    refine lineGraph_colorable_of_symm_fn _ _
      (fun p q => ⟨kcol p.1.1 q.1.1 * t + shift p.2.1 q.2.1, hbound p q⟩) ?_ ?_
    · intro p q
      apply Fin.ext
      dsimp only
      rw [hk_sym p.1.1 q.1.1, hshift_sym p.2.1 q.2.1]
    · intro p q₁ q₂ hadj₁ hadj₂ hne heq
      apply hne
      have hval : kcol p.1.1 q₁.1.1 * t + shift p.2.1 q₁.2.1 =
          kcol p.1.1 q₂.1.1 * t + shift p.2.1 q₂.2.1 := Fin.mk.inj heq
      have hb₁ : shift p.2.1 q₁.2.1 < t := hshift_lt p.2.1 q₁.2.1 p.2.2 q₁.2.2
      have hb₂ : shift p.2.1 q₂.2.1 < t := hshift_lt p.2.1 q₂.2.1 p.2.2 q₂.2.2
      obtain ⟨ha_eq, hb_eq⟩ := srg_mul_add_inj_of_lt hb₁ hb₂ hval
      have hpq₁ : p.1.1 ≠ q₁.1.1 := Fin.val_ne_of_ne hadj₁
      have hpq₂ : p.1.1 ≠ q₂.1.1 := Fin.val_ne_of_ne hadj₂
      have hp1 := p.1.2; have hq₁1 := q₁.1.2; have hq₂1 := q₂.1.2
      have hj : q₁.1.1 = q₂.1.1 :=
        hk_inj p.1.1 q₁.1.1 q₂.1.1 (by omega) (by omega) (by omega) hpq₁ hpq₂ ha_eq
      have hy : q₁.2.1 = q₂.2.1 := hshift_inj p.2.1 q₁.2.1 q₂.2.1 p.2.2 q₁.2.2 q₂.2.2 hb_eq
      exact Prod.ext (Fin.ext hj) (Fin.ext hy)
  · rcases ht_even with ⟨s, hs⟩
    have hs1 : 1 ≤ s := by omega
    obtain ⟨kcol, hk_lt, hk_sym, hk_inj, hk_zero⟩ := srg_exists_kirkman_factorization m (by omega)
    let emb : ℕ → ℕ → ℕ := fun i bit =>
      if i = 0 then (if bit = 0 then 0 else 2 * m - 1)
      else (if bit = 0 then i else 2 * m - 1 - i)
    let shift : ℕ → ℕ → ℕ := fun zx zy => if zx + zy < s then zx + zy else zx + zy - s
    have hshift_lt : ∀ x y, x < s → y < s → shift x y < s := by
      intro x y hx hy
      dsimp only [shift]
      split_ifs <;> omega
    have hshift_sym : ∀ x y, shift x y = shift y x := by
      intro x y
      dsimp only [shift]
      split_ifs <;> omega
    have hshift_inj : ∀ x y₁ y₂, x < s → y₁ < s → y₂ < s → shift x y₁ = shift x y₂ → y₁ = y₂ := by
      intro x y₁ y₂ hx hy₁ hy₂ heq
      dsimp only [shift] at heq
      split_ifs at heq <;> omega
    have hemb_lt : ∀ i bit, i < m → bit < 2 → emb i bit < 2 * m := by
      intro i bit hi hbit
      dsimp only [emb]
      split_ifs <;> omega
    have hemb_inj : ∀ i₁ b₁ i₂ b₂, i₁ < m → b₁ < 2 → i₂ < m → b₂ < 2 →
        emb i₁ b₁ = emb i₂ b₂ → i₁ = i₂ ∧ b₁ = b₂ := by
      intro i₁ b₁ i₂ b₂ hi₁ hb₁ hi₂ hb₂ heq
      dsimp only [emb] at heq
      split_ifs at heq <;> omega
    have hk_pos : ∀ p q : Fin m × Fin t, p.1 ≠ q.1 →
        1 ≤ kcol (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)) := by
      intro p q hne_fst
      have hi_ne : p.1.1 ≠ q.1.1 := Fin.val_ne_of_ne hne_fst
      have hu_lt : emb p.1.1 (p.2.1 % 2) < 2 * m := hemb_lt p.1.1 (p.2.1 % 2) p.1.2 (by omega)
      have hv_lt : emb q.1.1 (q.2.1 % 2) < 2 * m := hemb_lt q.1.1 (q.2.1 % 2) q.1.2 (by omega)
      have huv_ne : emb p.1.1 (p.2.1 % 2) ≠ emb q.1.1 (q.2.1 % 2) := by
        intro heq
        exact hi_ne (hemb_inj p.1.1 (p.2.1 % 2) q.1.1 (q.2.1 % 2)
          p.1.2 (by omega) q.1.2 (by omega) heq).1
      by_contra hle0
      have hz : kcol (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)) = 0 := by omega
      have hz' := (hk_zero _ _ hu_lt hv_lt huv_ne).mp hz
      have hp1 := p.1.2
      have hq1 := q.1.2
      dsimp only [emb] at hz'
      split_ifs at hz' <;> omega
    let raw : (Fin m × Fin t) → (Fin m × Fin t) → ℕ := fun p q =>
      (kcol (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)) - 1) * s +
        shift (p.2.1 / 2) (q.2.1 / 2)
    have hbound : ∀ p q : Fin m × Fin t, raw p q < (m - 1) * t := by
      intro p q
      have hu_lt : emb p.1.1 (p.2.1 % 2) < 2 * m := hemb_lt p.1.1 (p.2.1 % 2) p.1.2 (by omega)
      have hv_lt : emb q.1.1 (q.2.1 % 2) < 2 * m := hemb_lt q.1.1 (q.2.1 % 2) q.1.2 (by omega)
      have hk_ub : kcol (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)) < 2 * m - 1 :=
        hk_lt _ _ hu_lt hv_lt
      have ha : kcol (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)) - 1 < 2 * (m - 1) := by omega
      have hp2 := p.2.2; have hq2 := q.2.2
      have hb : shift (p.2.1 / 2) (q.2.1 / 2) < s :=
        hshift_lt (p.2.1 / 2) (q.2.1 / 2) (by omega) (by omega)
      have h1 : (kcol (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)) - 1 + 1) * s ≤
          (2 * (m - 1)) * s := Nat.mul_le_mul_right s ha
      have hmt : (2 * (m - 1)) * s = (m - 1) * t := by
        have ht2 : t = 2 * s := by omega
        rw [ht2]
        ring
      rw [Nat.add_mul, Nat.one_mul, hmt] at h1
      dsimp only [raw]
      omega
    refine lineGraph_colorable_of_symm_fn _ _ (fun p q => ⟨raw p q, hbound p q⟩) ?_ ?_
    · intro p q
      apply Fin.ext
      dsimp only [raw]
      rw [hk_sym (emb p.1.1 (p.2.1 % 2)) (emb q.1.1 (q.2.1 % 2)),
        hshift_sym (p.2.1 / 2) (q.2.1 / 2)]
    · intro p q₁ q₂ hadj₁ hadj₂ hne heq
      apply hne
      have hval : raw p q₁ = raw p q₂ := Fin.mk.inj heq
      have hp2 := p.2.2; have hq₁2 := q₁.2.2; have hq₂2 := q₂.2.2
      have hb₁ : shift (p.2.1 / 2) (q₁.2.1 / 2) < s :=
        hshift_lt (p.2.1 / 2) (q₁.2.1 / 2) (by omega) (by omega)
      have hb₂ : shift (p.2.1 / 2) (q₂.2.1 / 2) < s :=
        hshift_lt (p.2.1 / 2) (q₂.2.1 / 2) (by omega) (by omega)
      obtain ⟨ha_eq, hb_eq⟩ := srg_mul_add_inj_of_lt hb₁ hb₂ hval
      have hpos₁ : 1 ≤ kcol (emb p.1.1 (p.2.1 % 2)) (emb q₁.1.1 (q₁.2.1 % 2)) := hk_pos p q₁ hadj₁
      have hpos₂ : 1 ≤ kcol (emb p.1.1 (p.2.1 % 2)) (emb q₂.1.1 (q₂.2.1 % 2)) := hk_pos p q₂ hadj₂
      have hk_eq : kcol (emb p.1.1 (p.2.1 % 2)) (emb q₁.1.1 (q₁.2.1 % 2)) =
          kcol (emb p.1.1 (p.2.1 % 2)) (emb q₂.1.1 (q₂.2.1 % 2)) := by omega
      have hu_lt := hemb_lt p.1.1 (p.2.1 % 2) p.1.2 (by omega)
      have hv₁_lt := hemb_lt q₁.1.1 (q₁.2.1 % 2) q₁.1.2 (by omega)
      have hv₂_lt := hemb_lt q₂.1.1 (q₂.2.1 % 2) q₂.1.2 (by omega)
      have huv₁ : emb p.1.1 (p.2.1 % 2) ≠ emb q₁.1.1 (q₁.2.1 % 2) := fun h =>
        Fin.val_ne_of_ne hadj₁
          (hemb_inj p.1.1 (p.2.1 % 2) q₁.1.1 (q₁.2.1 % 2) p.1.2 (by omega) q₁.1.2 (by omega) h).1
      have huv₂ : emb p.1.1 (p.2.1 % 2) ≠ emb q₂.1.1 (q₂.2.1 % 2) := fun h =>
        Fin.val_ne_of_ne hadj₂
          (hemb_inj p.1.1 (p.2.1 % 2) q₂.1.1 (q₂.2.1 % 2) p.1.2 (by omega) q₂.1.2 (by omega) h).1
      have hv_eq := hk_inj _ _ _ hu_lt hv₁_lt hv₂_lt huv₁ huv₂ hk_eq
      obtain ⟨hj_eq, hmod_eq⟩ := hemb_inj q₁.1.1 (q₁.2.1 % 2) q₂.1.1 (q₂.2.1 % 2)
        q₁.1.2 (by omega) q₂.1.2 (by omega) hv_eq
      have hdiv_eq : q₁.2.1 / 2 = q₂.2.1 / 2 :=
        hshift_inj (p.2.1 / 2) (q₁.2.1 / 2) (q₂.2.1 / 2) (by omega) (by omega) (by omega) hb_eq
      have hy_eq : q₁.2.1 = q₂.2.1 := by omega
      exact Prod.ext (Fin.ext hj_eq) (Fin.ext hy_eq)

theorem srg_not_adj_iff_neighborFinset_eq {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hSRG : G.IsSRGWith n k ℓ μ) (hμ : μ = k) (u v : Fin n) :
    ¬ G.Adj u v ↔ G.neighborFinset u = G.neighborFinset v := by
  constructor
  · intro hna
    by_cases huv : u = v
    · subst huv; rfl
    · have hcard_union : (G.neighborFinset u ∪ G.neighborFinset v).card = k := by
        have hc := hSRG.card_neighborFinset_union_of_not_adj huv hna
        omega
      have hcard_u : (G.neighborFinset u).card = k := by
        rw [G.card_neighborFinset_eq_degree, hSRG.regular u]
      have hcard_v : (G.neighborFinset v).card = k := by
        rw [G.card_neighborFinset_eq_degree, hSRG.regular v]
      have h1 : G.neighborFinset u = G.neighborFinset u ∪ G.neighborFinset v :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
      have h2 : G.neighborFinset v = G.neighborFinset u ∪ G.neighborFinset v :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
      exact h1.trans h2.symm
  · intro heq hadj
    have hv : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
    rw [heq] at hv
    exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp hv)

theorem srg_mu_eq_k_iso_completeEquipartite {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1)
    (hμ : μ = k) :
    ∃ m t : ℕ, 2 ≤ m ∧ 2 ≤ t ∧ n = m * t ∧ k = (m - 1) * t ∧
      Nonempty (G ≃g SimpleGraph.completeEquipartiteGraph m t) := by
  let t : ℕ := n - k
  have ht2 : 2 ≤ t := by omega
  let S : Finset (Finset (Fin n)) := Finset.univ.image (fun u : Fin n => G.neighborFinset u)
  let m : ℕ := S.card
  let fib : Finset (Fin n) → Finset (Fin n) :=
    fun s => Finset.univ.filter (fun v : Fin n => G.neighborFinset v = s)
  have hfib_card : ∀ s ∈ S, (fib s).card = t := by
    intro s hs
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hs
    have hfib_eq : fib (G.neighborFinset u) = (G.neighborFinset u)ᶜ := by
      ext v
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
        SimpleGraph.mem_neighborFinset]
      rw [← srg_not_adj_iff_neighborFinset_eq G hSRG hμ v u, G.adj_comm]
    rw [hfib_eq, Finset.card_compl, Fintype.card_fin, G.card_neighborFinset_eq_degree,
      hSRG.regular u]
  have hdisj : (S : Set (Finset (Fin n))).PairwiseDisjoint fib := by
    intro s₁ _ s₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    intro v hv₁ hv₂
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    exact hne (hv₁.symm.trans hv₂)
  have hbiUnion : S.biUnion fib = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    exact ⟨G.neighborFinset v, Finset.mem_image_of_mem _ (Finset.mem_univ v),
      by simp [fib]⟩
  have hn_eq : n = m * t := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = (S.biUnion fib).card := by rw [hbiUnion]
      _ = ∑ s ∈ S, (fib s).card := Finset.card_biUnion hdisj
      _ = ∑ _s ∈ S, t := Finset.sum_congr rfl hfib_card
      _ = m * t := by simp [m]
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m'
    · simp at hn_eq; omega
    · simp at hn_eq; omega
    · omega
  have hk_eq : k = (m - 1) * t := by
    have h1 : (m - 1) * t = m * t - t := Nat.sub_one_mul m t
    omega
  let eS : S ≃ Fin m := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let eFib : ∀ i : Fin m, fib (eS.symm i).1 ≃ Fin t := fun i =>
    Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans (hfib_card (eS.symm i).1 (eS.symm i).2))
  let ψ : Fin m × Fin t → Fin n := fun p => ((eFib p.1).symm p.2).1
  have hψ_nei : ∀ p : Fin m × Fin t, G.neighborFinset (ψ p) = (eS.symm p.1).1 := by
    intro p
    exact (Finset.mem_filter.mp ((eFib p.1).symm p.2).2).2
  have hψ_inj : Function.Injective ψ := by
    intro p₁ p₂ heq
    have hs_eq : (eS.symm p₁.1).1 = (eS.symm p₂.1).1 := by
      rw [← hψ_nei p₁, ← hψ_nei p₂, heq]
    have hi_eq : p₁.1 = p₂.1 := eS.symm.injective (Subtype.ext hs_eq)
    rcases p₁ with ⟨i₁, j₁⟩
    rcases p₂ with ⟨i₂, j₂⟩
    dsimp at hi_eq
    subst hi_eq
    have hj_eq : j₁ = j₂ := (eFib i₁).symm.injective (Subtype.ext heq)
    exact Prod.ext rfl hj_eq
  have hψ_bij : Function.Bijective ψ :=
    (Fintype.bijective_iff_injective_and_card ψ).mpr ⟨hψ_inj, by simp [hn_eq]⟩
  let eV : Fin m × Fin t ≃ Fin n := Equiv.ofBijective ψ hψ_bij
  let iso : SimpleGraph.completeEquipartiteGraph m t ≃g G :=
    { toEquiv := eV
      map_rel_iff' := by
        intro p q
        change G.Adj (ψ p) (ψ q) ↔ p.1 ≠ q.1
        rw [← not_iff_not, not_ne_iff, srg_not_adj_iff_neighborFinset_eq G hSRG hμ,
          hψ_nei p, hψ_nei q]
        exact ⟨fun h => eS.symm.injective (Subtype.ext h), fun h => by rw [h]⟩ }
  exact ⟨m, t, hm2, ht2, hn_eq, hk_eq, ⟨iso.symm⟩⟩

theorem srg_multipartite_colorable {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1)
    (heven : Even n) (hμ : μ = k) :
    G.lineGraph.Colorable k := by
  obtain ⟨m, t, hm2, ht2, hn_eq, hk_eq, ⟨iso⟩⟩ :=
    srg_mu_eq_k_iso_completeEquipartite G hSRG hk hkn hμ
  rw [hk_eq]
  have heven_mt : Even (m * t) := hn_eq ▸ heven
  have hcol := completeEquipartiteGraph_lineGraph_colorable m t hm2 (by omega) heven_mt
  exact (SimpleGraph.colorable_congr iso.lineGraph).mpr hcol

/-! ## Section 3: Petersen Graph Uniqueness, `k ≤ 3`, and `SRG(10, 6, 3, 4)` Class-1 Proof -/

theorem pet_canonical_labeling
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (h : G.IsSRGWith 10 3 0 1) :
    ∃ e : Fin 10 ≃ Fin 10, ∀ i j : Fin 10,
      G.Adj (e i) (e j) ↔
        (109142149470260270904923702286 >>> (10 * i.val + j.val)) % 2 = 1 := by
  have hdeg : ∀ v : Fin 10, (G.neighborFinset v).card = 3 :=
    fun v => (G.card_neighborFinset_eq_degree v).trans (h.regular v)
  have hno3 : ∀ {a b c : Fin 10}, G.Adj a b → G.Adj b c → ¬ G.Adj a c := by
    intro a b c hab hbc hac
    have h0 : Fintype.card (G.commonNeighbors a c) = 0 := h.of_adj a c hac
    have hmem : b ∈ G.commonNeighbors a c := ⟨hab, hbc.symm⟩
    have hpos : 0 < Fintype.card (G.commonNeighbors a c) :=
      Fintype.card_pos_iff.mpr ⟨⟨b, hmem⟩⟩
    omega
  have hno4 : ∀ {a b c d : Fin 10},
      a ≠ b → G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → c = d := by
    intro a b c d hab hac hbc had hbd
    have hnab : ¬ G.Adj a b := hno3 hac hbc.symm
    have h1 : Fintype.card (G.commonNeighbors a b) = 1 := h.of_not_adj hab hnab
    have hsub : Subsingleton (G.commonNeighbors a b) :=
      Fintype.card_le_one_iff_subsingleton.mp h1.le
    exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨c, hac, hbc⟩ ⟨d, had, hbd⟩)
  have hex_common : ∀ {a b : Fin 10},
      a ≠ b → ¬ G.Adj a b → ∃ c : Fin 10, G.Adj a c ∧ G.Adj b c := by
    intro a b hab hnab
    have h1 : Fintype.card (G.commonNeighbors a b) = 1 := h.of_not_adj hab hnab
    obtain ⟨⟨c, hc1, hc2⟩⟩ :=
      Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (G.commonNeighbors a b))
    exact ⟨c, hc1, hc2⟩
  have nbrs_eq : ∀ {v a b c : Fin 10},
      G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
      G.neighborFinset v = {a, b, c} := by
    intro v a b c hva hvb hvc hab hac hbc
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with rfl | rfl | rfl <;> assumption
    · have hcard3 : ({a, b, c} : Finset (Fin 10)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hbc]
        · simp [hab, hac]
      rw [hdeg v, hcard3]
  let r : Fin 10 := 0
  obtain ⟨u₀, u₁, u₂, hu01, hu02, hu12, hr_nbrs⟩ := Finset.card_eq_three.mp (hdeg r)
  have hru0 : G.Adj r u₀ := (G.mem_neighborFinset r u₀).mp (hr_nbrs ▸ by simp)
  have hru1 : G.Adj r u₁ := (G.mem_neighborFinset r u₁).mp (hr_nbrs ▸ by simp)
  have hru2 : G.Adj r u₂ := (G.mem_neighborFinset r u₂).mp (hr_nbrs ▸ by simp)
  have hu0r : u₀ ≠ r := (G.ne_of_adj hru0).symm
  have hu1r : u₁ ≠ r := (G.ne_of_adj hru1).symm
  have hu2r : u₂ ≠ r := (G.ne_of_adj hru2).symm
  have hnu01 : ¬ G.Adj u₀ u₁ := hno3 hru0.symm hru1
  have hnu02 : ¬ G.Adj u₀ u₂ := hno3 hru0.symm hru2
  have hnu12 : ¬ G.Adj u₁ u₂ := hno3 hru1.symm hru2
  have hcard_u0_sdiff : (G.neighborFinset u₀ \ {r}).card = 2 := by
    rw [Finset.card_sdiff_of_subset
      (Finset.singleton_subset_iff.mpr ((G.mem_neighborFinset u₀ r).mpr hru0.symm)),
      hdeg u₀, Finset.card_singleton]
  obtain ⟨x₀, x₁, hx01, hu0_sdiff⟩ := Finset.card_eq_two.mp hcard_u0_sdiff
  have hx0_mem : x₀ ∈ G.neighborFinset u₀ \ {r} := hu0_sdiff ▸ by simp
  have hx1_mem : x₁ ∈ G.neighborFinset u₀ \ {r} := hu0_sdiff ▸ by simp
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_singleton] at hx0_mem hx1_mem
  rcases hx0_mem with ⟨hu0x0, hx0r_raw⟩
  rcases hx1_mem with ⟨hu0x1, hx1r_raw⟩
  have hx0r : x₀ ≠ r := hx0r_raw
  have hx1r : x₁ ≠ r := hx1r_raw
  have hu0_nbrs : G.neighborFinset u₀ = {r, x₀, x₁} :=
    nbrs_eq hru0.symm hu0x0 hu0x1 hx0r.symm hx1r.symm hx01
  have hnrx0 : ¬ G.Adj r x₀ := hno3 hru0 hu0x0
  have hnrx1 : ¬ G.Adj r x₁ := hno3 hru0 hu0x1
  have hdisj_u : ∀ {i j w : Fin 10},
      i ≠ j → G.Adj r i → G.Adj r j → w ≠ r → G.Adj i w → ¬ G.Adj j w :=
    fun hij hri hrj hwr hiw hjw => hwr (hno4 hij hri.symm hrj.symm hiw hjw).symm
  have hnu1x0 : ¬ G.Adj u₁ x₀ := hdisj_u hu01 hru0 hru1 hx0r hu0x0
  have hnu1x1 : ¬ G.Adj u₁ x₁ := hdisj_u hu01 hru0 hru1 hx1r hu0x1
  have hnu2x0 : ¬ G.Adj u₂ x₀ := hdisj_u hu02 hru0 hru2 hx0r hu0x0
  have hnu2x1 : ¬ G.Adj u₂ x₁ := hdisj_u hu02 hru0 hru2 hx1r hu0x1
  have hu1x0 : u₁ ≠ x₀ := fun heq => hnrx0 (heq ▸ hru1)
  have hu1x1 : u₁ ≠ x₁ := fun heq => hnrx1 (heq ▸ hru1)
  have hu2x0 : u₂ ≠ x₀ := fun heq => hnrx0 (heq ▸ hru2)
  have hu2x1 : u₂ ≠ x₁ := fun heq => hnrx1 (heq ▸ hru2)
  obtain ⟨y₀, hu1y0, hx1y0⟩ := hex_common hu1x1 hnu1x1
  obtain ⟨y₁, hu1y1, hx0y1⟩ := hex_common hu1x0 hnu1x0
  obtain ⟨z₀, hu2z0, hx1z0⟩ := hex_common hu2x1 hnu2x1
  obtain ⟨z₁, hu2z1, hx0z1⟩ := hex_common hu2x0 hnu2x0
  have hnry0 : ¬ G.Adj r y₀ := hno3 hru1 hu1y0
  have hnry1 : ¬ G.Adj r y₁ := hno3 hru1 hu1y1
  have hnrz0 : ¬ G.Adj r z₀ := hno3 hru2 hu2z0
  have hnrz1 : ¬ G.Adj r z₁ := hno3 hru2 hu2z1
  have hy0r : y₀ ≠ r := fun heq => hnrx1 (heq ▸ hx1y0).symm
  have hy1r : y₁ ≠ r := fun heq => hnrx0 (heq ▸ hx0y1).symm
  have hz0r : z₀ ≠ r := fun heq => hnrx1 (heq ▸ hx1z0).symm
  have hz1r : z₁ ≠ r := fun heq => hnrx0 (heq ▸ hx0z1).symm
  have hnu0y0 : ¬ G.Adj u₀ y₀ := hdisj_u hu01.symm hru1 hru0 hy0r hu1y0
  have hnu0y1 : ¬ G.Adj u₀ y₁ := hdisj_u hu01.symm hru1 hru0 hy1r hu1y1
  have hnu2y0 : ¬ G.Adj u₂ y₀ := hdisj_u hu12 hru1 hru2 hy0r hu1y0
  have hnu2y1 : ¬ G.Adj u₂ y₁ := hdisj_u hu12 hru1 hru2 hy1r hu1y1
  have hnu0z0 : ¬ G.Adj u₀ z₀ := hdisj_u hu02.symm hru2 hru0 hz0r hu2z0
  have hnu0z1 : ¬ G.Adj u₀ z₁ := hdisj_u hu02.symm hru2 hru0 hz1r hu2z1
  have hnu1z0 : ¬ G.Adj u₁ z₀ := hdisj_u hu12.symm hru2 hru1 hz0r hu2z0
  have hnu1z1 : ¬ G.Adj u₁ z₁ := hdisj_u hu12.symm hru2 hru1 hz1r hu2z1
  have hy01 : y₀ ≠ y₁ := fun heq =>
    hnu01 ((hno4 hx01 hu0x0.symm hu0x1.symm (heq ▸ hx0y1) hx1y0) ▸ hu1y0).symm
  have hz01 : z₀ ≠ z₁ := fun heq =>
    hnu02 ((hno4 hx01 hu0x0.symm hu0x1.symm (heq ▸ hx0z1) hx1z0) ▸ hu2z0).symm
  have hy0z0 : y₀ ≠ z₀ := fun heq =>
    hy0r (hno4 hu12 hru1.symm hru2.symm hu1y0 (heq ▸ hu2z0)).symm
  have hy1z1 : y₁ ≠ z₁ := fun heq =>
    hy1r (hno4 hu12 hru1.symm hru2.symm hu1y1 (heq ▸ hu2z1)).symm
  have hu0y0 : u₀ ≠ y₀ := fun heq => hnu01 (heq ▸ hu1y0).symm
  have hu0y1 : u₀ ≠ y₁ := fun heq => hnu01 (heq ▸ hu1y1).symm
  have hu0z0 : u₀ ≠ z₀ := fun heq => hnu02 (heq ▸ hu2z0).symm
  have hu0z1 : u₀ ≠ z₁ := fun heq => hnu02 (heq ▸ hu2z1).symm
  have hu1_nbrs : G.neighborFinset u₁ = {r, y₀, y₁} :=
    nbrs_eq hru1.symm hu1y0 hu1y1 hy0r.symm hy1r.symm hy01
  have hu2_nbrs : G.neighborFinset u₂ = {r, z₀, z₁} :=
    nbrs_eq hru2.symm hu2z0 hu2z1 hz0r.symm hz1r.symm hz01
  have hx0_nbrs : G.neighborFinset x₀ = {u₀, y₁, z₁} :=
    nbrs_eq hu0x0.symm hx0y1 hx0z1 hu0y1 hu0z1 hy1z1
  have hx1_nbrs : G.neighborFinset x₁ = {u₀, y₀, z₀} :=
    nbrs_eq hu0x1.symm hx1y0 hx1z0 hu0y0 hu0z0 hy0z0
  let f : Fin 10 → Fin 10 := fun i =>
    match i.val with
    | 0 => r | 1 => u₀ | 2 => u₁ | 3 => u₂
    | 4 => x₀ | 5 => x₁ | 6 => y₀ | 7 => y₁
    | 8 => z₀ | _ => z₁
  let tag : Fin 10 → ℕ := fun w =>
    if w = r then 0
    else if G.Adj r w then 1
    else if G.Adj u₀ w then 2
    else if G.Adj u₁ w then 3
    else 4
  have htag : ∀ i : Fin 10, tag (f i) =
      match i.val with
      | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2
      | 5 => 2 | 6 => 3 | 7 => 3 | 8 => 4 | _ => 4 := by
    intro i
    fin_cases i
    · simp [f, tag]
    · simp [f, tag, hu0r, hru0]
    · simp [f, tag, hu1r, hru1]
    · simp [f, tag, hu2r, hru2]
    · simp [f, tag, hx0r, hnrx0, hu0x0]
    · simp [f, tag, hx1r, hnrx1, hu0x1]
    · simp [f, tag, hy0r, hnry0, hnu0y0, hu1y0]
    · simp [f, tag, hy1r, hnry1, hnu0y1, hu1y1]
    · simp [f, tag, hz0r, hnrz0, hnu0z0, hnu1z0]
    · simp [f, tag, hz1r, hnrz1, hnu0z1, hnu1z1]
  have hf_inj : Function.Injective f := by
    intro i j hij
    have ht : tag (f i) = tag (f j) := congrArg tag hij
    rw [htag i, htag j] at ht
    fin_cases i <;> fin_cases j
    all_goals
      first
      | rfl
      | exact absurd ht (by decide)
      | exact absurd hij hu01
      | exact absurd hij.symm hu01
      | exact absurd hij hu02
      | exact absurd hij.symm hu02
      | exact absurd hij hu12
      | exact absurd hij.symm hu12
      | exact absurd hij hx01
      | exact absurd hij.symm hx01
      | exact absurd hij hy01
      | exact absurd hij.symm hy01
      | exact absurd hij hz01
      | exact absurd hij.symm hz01
  let e : Fin 10 ≃ Fin 10 :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, rfl⟩)
  have he_apply : ∀ i : Fin 10, e i = f i := fun _ => rfl
  have hy0_z1 : G.Adj y₀ z₁ := by
    have hsub : ({u₁, x₁} : Finset (Fin 10)) ⊆ G.neighborFinset y₀ := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact hu1y0.symm
      · exact hx1y0.symm
    have hcard1 : (G.neighborFinset y₀ \ {u₁, x₁}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hdeg y₀,
        Finset.card_insert_of_notMem (by simp [hu1x1]), Finset.card_singleton]
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset y₀ \ {u₁, x₁}).card)
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with ⟨hy0w, hnot⟩
    have hwe : w = e (e.symm w) := (e.apply_symm_apply w).symm
    rw [hwe, he_apply] at hy0w hnot
    generalize e.symm w = k at hy0w hnot
    fin_cases k
    · exact False.elim (hnry0 hy0w.symm)
    · exact False.elim (hnu0y0 hy0w.symm)
    · exact False.elim (hnot (Or.inl rfl))
    · exact False.elim (hnu2y0 hy0w.symm)
    · have hmem : y₀ ∈ G.neighborFinset x₀ := (G.mem_neighborFinset x₀ y₀).mpr hy0w.symm
      rw [hx0_nbrs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h2 | h3
      · exact False.elim (hu0y0 h1.symm)
      · exact False.elim (hy01 h2)
      · exact False.elim (hy0r (hno4 hu12 hru1.symm hru2.symm hu1y0 (h3 ▸ hu2z1)).symm)
    · exact False.elim (hnot (Or.inr rfl))
    · exact False.elim (G.irrefl hy0w)
    · exact False.elim (hno3 hu1y0.symm hu1y1 hy0w)
    · exact False.elim (hno3 hx1y0.symm hx1z0 hy0w)
    · exact hy0w
  have hy1_z0 : G.Adj y₁ z₀ := by
    have hsub : ({u₁, x₀} : Finset (Fin 10)) ⊆ G.neighborFinset y₁ := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact hu1y1.symm
      · exact hx0y1.symm
    have hcard1 : (G.neighborFinset y₁ \ {u₁, x₀}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hdeg y₁,
        Finset.card_insert_of_notMem (by simp [hu1x0]), Finset.card_singleton]
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset y₁ \ {u₁, x₀}).card)
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with ⟨hy1w, hnot⟩
    have hwe : w = e (e.symm w) := (e.apply_symm_apply w).symm
    rw [hwe, he_apply] at hy1w hnot
    generalize e.symm w = k at hy1w hnot
    fin_cases k
    · exact False.elim (hnry1 hy1w.symm)
    · exact False.elim (hnu0y1 hy1w.symm)
    · exact False.elim (hnot (Or.inl rfl))
    · exact False.elim (hnu2y1 hy1w.symm)
    · exact False.elim (hnot (Or.inr rfl))
    · have hmem : y₁ ∈ G.neighborFinset x₁ := (G.mem_neighborFinset x₁ y₁).mpr hy1w.symm
      rw [hx1_nbrs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h2 | h3
      · exact False.elim (hu0y1 h1.symm)
      · exact False.elim (hy01 h2.symm)
      · exact False.elim (hy1r (hno4 hu12 hru1.symm hru2.symm hu1y1 (h3 ▸ hu2z0)).symm)
    · exact False.elim (hno3 hu1y1.symm hu1y0 hy1w)
    · exact False.elim (G.irrefl hy1w)
    · exact hy1w
    · exact False.elim (hno3 hx0y1.symm hx0z1 hy1w)
  have hu1z1 : u₁ ≠ z₁ := fun heq => hnu12 (heq ▸ hu2z1).symm
  have hx1z1 : x₁ ≠ z₁ := fun heq => hnu0z1 (heq ▸ hu0x1)
  have hu1z0 : u₁ ≠ z₀ := fun heq => hnu12 (heq ▸ hu2z0).symm
  have hx0z0 : x₀ ≠ z₀ := fun heq => hnu0z0 (heq ▸ hu0x0)
  have hu2y1 : u₂ ≠ y₁ := fun heq => hnu12 (heq ▸ hu1y1)
  have hx1y1 : x₁ ≠ y₁ := fun heq => hnu0y1 (heq ▸ hu0x1)
  have hu2y0 : u₂ ≠ y₀ := fun heq => hnu12 (heq ▸ hu1y0)
  have hx0y0 : x₀ ≠ y₀ := fun heq => hnu0y0 (heq ▸ hu0x0)
  have hy0_nbrs : G.neighborFinset y₀ = {u₁, x₁, z₁} :=
    nbrs_eq hu1y0.symm hx1y0.symm hy0_z1 hu1x1 hu1z1 hx1z1
  have hy1_nbrs : G.neighborFinset y₁ = {u₁, x₀, z₀} :=
    nbrs_eq hu1y1.symm hx0y1.symm hy1_z0 hu1x0 hu1z0 hx0z0
  have hz0_nbrs : G.neighborFinset z₀ = {u₂, x₁, y₁} :=
    nbrs_eq hu2z0.symm hx1z0.symm hy1_z0.symm hu2x1 hu2y1 hx1y1
  have hz1_nbrs : G.neighborFinset z₁ = {u₂, x₀, y₀} :=
    nbrs_eq hu2z1.symm hx0z1.symm hy0_z1.symm hu2x0 hu2y0 hx0y0
  refine ⟨e, fun i j => ?_⟩
  rw [← SimpleGraph.mem_neighborFinset]
  have hmem_iff : ∀ a b c : Fin 10,
      e j ∈ ({e a, e b, e c} : Finset (Fin 10)) ↔ (j = a ∨ j = b ∨ j = c) := by
    intro a b c
    simp only [Finset.mem_insert, Finset.mem_singleton, e.injective.eq_iff]
  fin_cases i
  · change e j ∈ G.neighborFinset r ↔ _; rw [hr_nbrs]
    exact (hmem_iff 1 2 3).trans ((show ∀ j : Fin 10,
      (j = 1 ∨ j = 2 ∨ j = 3) ↔ (109142149470260270904923702286 >>> (10 * 0 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset u₀ ↔ _; rw [hu0_nbrs]
    exact (hmem_iff 0 4 5).trans ((show ∀ j : Fin 10,
      (j = 0 ∨ j = 4 ∨ j = 5) ↔ (109142149470260270904923702286 >>> (10 * 1 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset u₁ ↔ _; rw [hu1_nbrs]
    exact (hmem_iff 0 6 7).trans ((show ∀ j : Fin 10,
      (j = 0 ∨ j = 6 ∨ j = 7) ↔ (109142149470260270904923702286 >>> (10 * 2 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset u₂ ↔ _; rw [hu2_nbrs]
    exact (hmem_iff 0 8 9).trans ((show ∀ j : Fin 10,
      (j = 0 ∨ j = 8 ∨ j = 9) ↔ (109142149470260270904923702286 >>> (10 * 3 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset x₀ ↔ _; rw [hx0_nbrs]
    exact (hmem_iff 1 7 9).trans ((show ∀ j : Fin 10,
      (j = 1 ∨ j = 7 ∨ j = 9) ↔ (109142149470260270904923702286 >>> (10 * 4 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset x₁ ↔ _; rw [hx1_nbrs]
    exact (hmem_iff 1 6 8).trans ((show ∀ j : Fin 10,
      (j = 1 ∨ j = 6 ∨ j = 8) ↔ (109142149470260270904923702286 >>> (10 * 5 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset y₀ ↔ _; rw [hy0_nbrs]
    exact (hmem_iff 2 5 9).trans ((show ∀ j : Fin 10,
      (j = 2 ∨ j = 5 ∨ j = 9) ↔ (109142149470260270904923702286 >>> (10 * 6 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset y₁ ↔ _; rw [hy1_nbrs]
    exact (hmem_iff 2 4 8).trans ((show ∀ j : Fin 10,
      (j = 2 ∨ j = 4 ∨ j = 8) ↔ (109142149470260270904923702286 >>> (10 * 7 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset z₀ ↔ _; rw [hz0_nbrs]
    exact (hmem_iff 3 5 7).trans ((show ∀ j : Fin 10,
      (j = 3 ∨ j = 5 ∨ j = 7) ↔ (109142149470260270904923702286 >>> (10 * 8 + j.val)) % 2 = 1
      by decide +kernel) j)
  · change e j ∈ G.neighborFinset z₁ ↔ _; rw [hz1_nbrs]
    exact (hmem_iff 3 4 6).trans ((show ∀ j : Fin 10,
      (j = 3 ∨ j = 4 ∨ j = 6) ↔ (109142149470260270904923702286 >>> (10 * 9 + j.val)) % 2 = 1
      by decide +kernel) j)

theorem pet_kneser_equiv :
    ∃ k : Fin 10 ≃ {s : Finset (Fin 5) // s.card = 2},
      ∀ i j : Fin 10,
        OMA.S_arxiv_1810_06660.petersen.Adj (k i) (k j) ↔
          (109142149470260270904923702286 >>> (10 * i.val + j.val)) % 2 = 1 := by
  let toK : Fin 10 → {s : Finset (Fin 5) // s.card = 2} := fun i =>
    if i = 0 then ⟨{3, 4}, by decide⟩
    else if i = 1 then ⟨{1, 2}, by decide⟩
    else if i = 2 then ⟨{0, 2}, by decide⟩
    else if i = 3 then ⟨{0, 1}, by decide⟩
    else if i = 4 then ⟨{0, 3}, by decide⟩
    else if i = 5 then ⟨{0, 4}, by decide⟩
    else if i = 6 then ⟨{1, 3}, by decide⟩
    else if i = 7 then ⟨{1, 4}, by decide⟩
    else if i = 8 then ⟨{2, 3}, by decide⟩
    else ⟨{2, 4}, by decide⟩
  let ofK : {s : Finset (Fin 5) // s.card = 2} → Fin 10 := fun s =>
    if (0 : Fin 5) ∈ s.1 then
      if (1 : Fin 5) ∈ s.1 then 3
      else if (2 : Fin 5) ∈ s.1 then 2
      else if (3 : Fin 5) ∈ s.1 then 4
      else 5
    else if (1 : Fin 5) ∈ s.1 then
      if (2 : Fin 5) ∈ s.1 then 1
      else if (3 : Fin 5) ∈ s.1 then 6
      else 7
    else if (2 : Fin 5) ∈ s.1 then
      if (3 : Fin 5) ∈ s.1 then 8
      else 9
    else 0
  have hleft : Function.LeftInverse ofK toK := by decide +kernel
  have hright : Function.RightInverse ofK toK := by decide +kernel
  have hadj : ∀ i j : Fin 10,
      OMA.S_arxiv_1810_06660.petersen.Adj (toK i) (toK j) ↔
        (109142149470260270904923702286 >>> (10 * i.val + j.val)) % 2 = 1 := by
    intro i j
    rw [OMA.S_arxiv_1810_06660.petersen, SimpleGraph.fromRel_adj]
    revert i j
    decide +kernel
  exact ⟨⟨toK, ofK, hleft, hright⟩, hadj⟩

theorem srg_10_3_0_1_iso_petersen
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (h : G.IsSRGWith 10 3 0 1) :
    Nonempty (G ≃g OMA.S_arxiv_1810_06660.petersen) := by
  obtain ⟨e, he⟩ := pet_canonical_labeling G h
  obtain ⟨k, hk⟩ := pet_kneser_equiv
  refine ⟨{
    toEquiv := e.symm.trans k
    map_rel_iff' := ?_
  }⟩
  intro a b
  simp only [Equiv.trans_apply]
  rw [hk (e.symm a) (e.symm b), ← he (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply]

theorem srg_even_deg_le_three_params
    {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hk0 : 0 < k) (hk3 : k ≤ 3) (hkn : k < n - 1)
    (hμ1 : 1 ≤ μ) (hμk : μ < k) (heven : Even n) :
    n = 10 ∧ k = 3 ∧ ℓ = 0 ∧ μ = 1 := by
  have hn0 : 0 < n := by omega
  have hparam : k * (k - ℓ - 1) = (n - k - 1) * μ := SimpleGraph.IsSRGWith.param_eq G h hn0
  obtain ⟨m, rfl⟩ := heven
  have hk_cases : k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl
  · have hμ_eq : μ = 1 := by omega
    subst hμ_eq
    have hℓ_cases : ℓ = 0 ∨ 1 ≤ ℓ := by omega
    rcases hℓ_cases with rfl | hℓ1 <;> omega
  · have hμ_cases : μ = 1 ∨ μ = 2 := by omega
    rcases hμ_cases with rfl | rfl
    · have hℓ_cases : ℓ = 0 ∨ ℓ = 1 ∨ 2 ≤ ℓ := by omega
      rcases hℓ_cases with rfl | rfl | hℓ2 <;> omega
    · have hℓ_cases : ℓ = 0 ∨ ℓ = 1 ∨ 2 ≤ ℓ := by omega
      rcases hℓ_cases with rfl | rfl | hℓ2 <;> omega

theorem srg_even_deg_le_three_of_mu_lt
    {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hk0 : 0 < k) (hk3 : k ≤ 3) (hkn : k < n - 1)
    (hμ1 : 1 ≤ μ) (hμk : μ < k) (heven : Even n)
    (hpet : IsEmpty (G ≃g OMA.S_arxiv_1810_06660.petersen)) :
    False := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := srg_even_deg_le_three_params G h hk0 hk3 hkn hμ1 hμk heven
  obtain ⟨iso⟩ := srg_10_3_0_1_iso_petersen G h
  exact hpet.false iso

theorem pet_compl_color_table :
    ∃ c : Fin 10 → Fin 10 → Fin 6,
      (∀ i j : Fin 10, c i j = c j i) ∧
      (∀ i j k : Fin 10,
        i ≠ j →
        (109142149470260270904923702286 >>> (10 * i.val + j.val)) % 2 ≠ 1 →
        i ≠ k →
        (109142149470260270904923702286 >>> (10 * i.val + k.val)) % 2 ≠ 1 →
        j ≠ k →
        c i j ≠ c i k) :=
  ⟨fun i j =>
    ⟨((67636395070545407607799497470963835516362850706761532238993527579667065647721014220062720 >>>
        (3 * (10 * i.val + j.val))) % 8) % 6,
      Nat.mod_lt _ (by decide)⟩,
   by decide +kernel⟩

/-- Every `SRG(10, 6, 3, 4)` (`L(K_5) = petersenᶜ`) is 6-edge-colorable (Class 1). -/
theorem srg_10_6_3_4_colorable
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (h : G.IsSRGWith 10 6 3 4) :
    G.lineGraph.Colorable 6 := by
  have hc : Gᶜ.IsSRGWith 10 3 0 1 := h.compl
  obtain ⟨e, he⟩ := pet_canonical_labeling Gᶜ hc
  obtain ⟨c, hsymm, hvalid⟩ := pet_compl_color_table
  let f : Fin 10 → Fin 10 → Fin 6 := fun u v => c (e.symm u) (e.symm v)
  have hfsymm : ∀ u v : Fin 10, f u v = f v u := fun u v => hsymm (e.symm u) (e.symm v)
  let edgeColor : G.edgeSet → Fin 6 := fun edge => Sym2.lift ⟨f, hfsymm⟩ edge.1
  refine ⟨SimpleGraph.Coloring.mk edgeColor ?_⟩
  intro e₁ e₂ hadj
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨hne, v, hv1, hv2⟩
  obtain ⟨w₁, hw1⟩ := Sym2.mem_iff_exists.mp hv1
  obtain ⟨w₂, hw2⟩ := Sym2.mem_iff_exists.mp hv2
  have he1_adj : G.Adj v w₁ := by
    have hmem : e₁.1 ∈ G.edgeSet := e₁.2
    rw [hw1, SimpleGraph.mem_edgeSet] at hmem
    exact hmem
  have he2_adj : G.Adj v w₂ := by
    have hmem : e₂.1 ∈ G.edgeSet := e₂.2
    rw [hw2, SimpleGraph.mem_edgeSet] at hmem
    exact hmem
  have hw_ne : w₁ ≠ w₂ := by
    intro hweq
    apply hne
    apply Subtype.ext
    rw [hw1, hw2, hweq]
  have hvw1 : v ≠ w₁ := G.ne_of_adj he1_adj
  have hvw2 : v ≠ w₂ := G.ne_of_adj he2_adj
  have hnc1 : ¬ Gᶜ.Adj v w₁ := by
    rw [SimpleGraph.compl_adj]
    intro h1
    exact h1.2 he1_adj
  have hnc2 : ¬ Gᶜ.Adj v w₂ := by
    rw [SimpleGraph.compl_adj]
    intro h2
    exact h2.2 he2_adj
  have hnpet1 : (109142149470260270904923702286 >>> (10 * (e.symm v).val + (e.symm w₁).val)) % 2 ≠ 1 := by
    have htmp := he (e.symm v) (e.symm w₁)
    rw [e.apply_symm_apply, e.apply_symm_apply] at htmp
    exact hnc1 ∘ htmp.mpr
  have hnpet2 : (109142149470260270904923702286 >>> (10 * (e.symm v).val + (e.symm w₂).val)) % 2 ≠ 1 := by
    have htmp := he (e.symm v) (e.symm w₂)
    rw [e.apply_symm_apply, e.apply_symm_apply] at htmp
    exact hnc2 ∘ htmp.mpr
  have hcol1 : edgeColor e₁ = f v w₁ := by
    change Sym2.lift ⟨f, hfsymm⟩ e₁.1 = f v w₁
    rw [hw1]
    rfl
  have hcol2 : edgeColor e₂ = f v w₂ := by
    change Sym2.lift ⟨f, hfsymm⟩ e₂.1 = f v w₂
    rw [hw2]
    rfl
  rw [hcol1, hcol2]
  exact hvalid (e.symm v) (e.symm w₁) (e.symm w₂)
    (e.symm.injective.ne hvw1) hnpet1
    (e.symm.injective.ne hvw2) hnpet2
    (e.symm.injective.ne hw_ne)

/-! ## Section 4: Spectral Integrality and Elimination of Even Orders `n ≤ 14` -/

theorem srg_spec_basic_param_bounds {n k ℓ μ : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1) :
    ℓ + 1 ≤ k ∧ μ ≤ k ∧ 3 ≤ n := by
  have hn3 : 3 ≤ n := by omega
  have u0_lt : 0 < n := by omega
  let u : Fin n := ⟨0, u0_lt⟩
  have hdeg_u : G.degree u = k := hSRG.regular u
  have hne_nb : (G.neighborFinset u).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hc : (G.neighborFinset u).card = 0 := by simp [hemp]
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg_u] at hc
    omega
  obtain ⟨v, hv_mem⟩ := hne_nb
  have hv : G.Adj u v := (G.mem_neighborFinset u v).mp hv_mem
  have hℓ : Fintype.card (G.commonNeighbors u v) = ℓ := hSRG.of_adj u v hv
  have hsub : (G.commonNeighbors u v).toFinset ⊆ (G.neighborFinset u).erase v := by
    intro w hw
    rw [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors] at hw
    rw [Finset.mem_erase, G.mem_neighborFinset]
    exact ⟨hw.2.ne', hw.1⟩
  have hcard_le := Finset.card_le_card hsub
  rw [Set.toFinset_card, hℓ, Finset.card_erase_of_mem hv_mem,
    SimpleGraph.card_neighborFinset_eq_degree, hdeg_u] at hcard_le
  have hℓ_bound : ℓ + 1 ≤ k := by omega
  have hdeg_compl : Gᶜ.degree u = n - k - 1 := hSRG.compl_is_regular u
  have hne_cnb : (Gᶜ.neighborFinset u).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hc : (Gᶜ.neighborFinset u).card = 0 := by simp [hemp]
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg_compl] at hc
    omega
  obtain ⟨w, hw_mem⟩ := hne_cnb
  have hw : Gᶜ.Adj u w := (Gᶜ.mem_neighborFinset u w).mp hw_mem
  rw [SimpleGraph.compl_adj] at hw
  have hμ_eq : Fintype.card (G.commonNeighbors u w) = μ := hSRG.of_not_adj hw.1 hw.2
  have hμ_le : μ ≤ k := by
    have hle := G.card_commonNeighbors_le_degree_left u w
    rw [hμ_eq, hdeg_u] at hle
    exact hle
  exact ⟨hℓ_bound, hμ_le, hn3⟩

theorem srg_spec_mulVec_sq_of_sum_zero {n k ℓ μ : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hSRG : G.IsSRGWith n k ℓ μ) (w : Fin n → ℝ)
    (hw : ∑ x : Fin n, w x = 0) :
    Matrix.mulVec (G.adjMatrix ℝ) (Matrix.mulVec (G.adjMatrix ℝ) w) =
      ((ℓ : ℝ) - μ) • Matrix.mulVec (G.adjMatrix ℝ) w + ((k : ℝ) - μ) • w := by
  have hsum_compl : ∀ i : Fin n,
      w i + Matrix.mulVec (G.adjMatrix ℝ) w i + Matrix.mulVec (Gᶜ.adjMatrix ℝ) w i = 0 := by
    intro i
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.adjMatrix_mulVec_apply, ← hw]
    have hpart : ∀ j : Fin n,
        (if i = j then w j else 0) + (if G.Adj i j then w j else 0) +
          (if Gᶜ.Adj i j then w j else 0) = w j := by
      intro j
      by_cases hij : i = j
      · subst hij; simp
      · by_cases hadj : G.Adj i j <;> simp [hij, hadj, SimpleGraph.compl_adj]
    have h1 : w i = ∑ j : Fin n, if i = j then w j else 0 := by simp
    have h2 : (∑ u ∈ G.neighborFinset i, w u) = ∑ j : Fin n, if G.Adj i j then w j else 0 := by
      simp [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    have h3 : (∑ u ∈ Gᶜ.neighborFinset i, w u) = ∑ j : Fin n, if Gᶜ.Adj i j then w j else 0 := by
      simp [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpart j
  ext i
  have hi := congr_fun (congr_arg (fun M => Matrix.mulVec M w) (hSRG.matrix_eq (α := ℝ))) i
  simp only [sq, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hi
  simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hci : Matrix.mulVec (Gᶜ.adjMatrix ℝ) w i = -w i - Matrix.mulVec (G.adjMatrix ℝ) w i := by
    linarith [hsum_compl i]
  rw [hci] at hi
  linarith

theorem even_srg_integral_conditions (n k ℓ μ : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1) (hμ : 1 ≤ μ) (hn : Even n) :
    ∃ d f g : ℕ, 0 < d ∧
      ((ℓ : ℤ) - μ) ^ 2 + 4 * ((k : ℤ) - μ) = (d : ℤ) ^ 2 ∧
      f + g = n - 1 ∧
      2 * (k : ℤ) + ((n : ℤ) - 1) * ((ℓ : ℤ) - μ) + ((f : ℤ) - g) * (d : ℤ) = 0 := by
  obtain ⟨hℓ_le, hμ_le_k, hn3⟩ := srg_spec_basic_param_bounds hSRG hk hkn
  have hn_pos : 0 < n := by omega
  let A : Matrix (Fin n) (Fin n) ℝ := G.adjMatrix ℝ
  have hA : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  let ev : Fin n → ℝ := hA.eigenvalues
  let v : Fin n → Fin n → ℝ := fun j => ⇑(hA.eigenvectorBasis j)
  let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hv_eig : ∀ j : Fin n, Matrix.mulVec A (v j) = (ev j) • v j :=
    fun j => hA.mulVec_eigenvectorBasis j
  have hv_ortho : ∀ j : Fin n, Matrix.mulVec (star U) (v j) = Pi.single j 1 :=
    fun j => hA.star_eigenvectorUnitary_mulVec j
  have hv_ne_zero : ∀ j : Fin n, v j ≠ 0 := by
    intro j hj
    have h0 := congr_fun (hv_ortho j) j
    rw [hj, Matrix.mulVec_zero, Pi.zero_apply, Pi.single_eq_same] at h0
    exact zero_ne_one h0
  have hQk_pos : 0 < (k : ℝ) ^ 2 - ((ℓ : ℝ) - μ) * (k : ℝ) - ((k : ℝ) - μ) := by
    have hℓR : (ℓ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hℓ_le
    have hμR : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hquad_of_sum_zero : ∀ (w : Fin n → ℝ) (t : ℝ),
      w ≠ 0 → (∑ x : Fin n, w x = 0) → Matrix.mulVec A w = t • w →
      t ^ 2 - ((ℓ : ℝ) - μ) * t - ((k : ℝ) - μ) = 0 := by
    intro w t hw_ne hw_sum hw_eig
    have hsq := srg_spec_mulVec_sq_of_sum_zero hSRG w hw_sum
    change Matrix.mulVec A (Matrix.mulVec A w) =
      ((ℓ : ℝ) - μ) • Matrix.mulVec A w + ((k : ℝ) - μ) • w at hsq
    rw [hw_eig, Matrix.mulVec_smul, hw_eig, smul_smul] at hsq
    obtain ⟨x, hx⟩ : ∃ x : Fin n, w x ≠ 0 := Function.ne_iff.mp hw_ne
    have hx_eq := congr_fun hsq x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx_eq
    have hsub : (t ^ 2 - ((ℓ : ℝ) - μ) * t - ((k : ℝ) - μ)) * w x = 0 := by linarith
    exact (mul_eq_zero.mp hsub).resolve_right hx
  have hev_eq_k_of_sum_ne : ∀ j : Fin n, (∑ x : Fin n, v j x) ≠ 0 → ev j = (k : ℝ) := by
    intro j hsum
    have h1 : ∑ x : Fin n, Matrix.mulVec A (v j) x = ev j * ∑ x : Fin n, v j x := by
      rw [hv_eig j]
      simp [Finset.mul_sum]
    have h2 : ∑ x : Fin n, Matrix.mulVec A (v j) x = (k : ℝ) * ∑ x : Fin n, v j x := by
      have hd1 : dotProduct (1 : Fin n → ℝ) (Matrix.mulVec A (v j)) =
          ∑ x : Fin n, Matrix.mulVec A (v j) x :=
        one_dotProduct (Matrix.mulVec A (v j))
      have hd2 : dotProduct (1 : Fin n → ℝ) (Matrix.mulVec A (v j)) =
          dotProduct (Matrix.vecMul (1 : Fin n → ℝ) A) (v j) :=
        Matrix.dotProduct_mulVec 1 A (v j)
      have hd3 : Matrix.vecMul (1 : Fin n → ℝ) A = Function.const (Fin n) (k : ℝ) := by
        ext x
        change Matrix.vecMul (1 : Fin n → ℝ) (G.adjMatrix ℝ) x = (k : ℝ)
        rw [SimpleGraph.adjMatrix_vecMul_apply]
        simp [hSRG.regular.degree_eq]
      rw [← hd1, hd2, hd3]
      simp [dotProduct, Finset.mul_sum]
    exact mul_right_cancel₀ hsum (h1.symm.trans h2)
  have hex_i0 : ∃ i₀ : Fin n, (∑ x : Fin n, v i₀ x) ≠ 0 := by
    by_contra h_all
    simp only [not_exists, not_not] at h_all
    have hstar1 : Matrix.mulVec (star U) (1 : Fin n → ℝ) = 0 := by
      ext j
      simp only [Matrix.mulVec, dotProduct_one, Pi.zero_apply]
      have hUj : ∀ x : Fin n, (star U) j x = v j x := by
        intro x
        change Matrix.conjTranspose U j x = v j x
        simp [U, v, Matrix.conjTranspose_apply]
      simp_rw [hUj]
      exact h_all j
    have hU1 : Matrix.mulVec U (Matrix.mulVec (star U) (1 : Fin n → ℝ)) = (1 : Fin n → ℝ) := by
      rw [Matrix.mulVec_mulVec]
      have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
      rw [hUU, Matrix.one_mulVec]
    rw [hstar1, Matrix.mulVec_zero] at hU1
    have h01 := congr_fun hU1 ⟨0, hn_pos⟩
    exact zero_ne_one h01
  obtain ⟨i₀, hi₀_sum⟩ := hex_i0
  have hi₀_ev : ev i₀ = (k : ℝ) := hev_eq_k_of_sum_ne i₀ hi₀_sum
  have hj_sum_zero : ∀ j : Fin n, j ≠ i₀ → ∑ x : Fin n, v j x = 0 := by
    intro j hne
    by_contra hj_sum
    have hj_ev : ev j = (k : ℝ) := hev_eq_k_of_sum_ne j hj_sum
    let cj : ℝ := ∑ x : Fin n, v j x
    let ci : ℝ := ∑ x : Fin n, v i₀ x
    let w : Fin n → ℝ := cj • v i₀ - ci • v j
    have hw_sum : ∑ x : Fin n, w x = 0 := by
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring
    have hw_eig : Matrix.mulVec A w = (k : ℝ) • w := by
      simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hv_eig i₀, hv_eig j, hi₀_ev, hj_ev]
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hproj := congr_fun (congr_arg (fun z => Matrix.mulVec (star U) z) hw0) i₀
      simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hv_ortho i₀, hv_ortho j,
        Matrix.mulVec_zero, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne hne.symm, mul_one, mul_zero, sub_zero] at hproj
      exact hj_sum hproj
    have hq := hquad_of_sum_zero w (k : ℝ) hw_ne hw_sum hw_eig
    linarith
  let Δ : ℤ := ((ℓ : ℤ) - μ) ^ 2 + 4 * ((k : ℤ) - μ)
  have hΔ_pos : 0 < Δ := by
    by_cases hμk : μ < k
    · have : (4 : ℤ) ≤ 4 * ((k : ℤ) - μ) := by omega
      have : (0 : ℤ) ≤ ((ℓ : ℤ) - μ) ^ 2 := sq_nonneg _
      omega
    · have hℓ_lt_μ : ℓ < μ := by omega
      have : (1 : ℤ) ≤ ((ℓ : ℤ) - μ) ^ 2 := by
        have hne : (ℓ : ℤ) - μ ≠ 0 := by omega
        nlinarith
      have : 4 * ((k : ℤ) - μ) = 0 := by omega
      omega
  have hΔR_pos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ_pos
  let s_real : ℝ := Real.sqrt (Δ : ℝ)
  have hs_pos : 0 < s_real := Real.sqrt_pos.mpr hΔR_pos
  have hs_sq : s_real ^ 2 = (Δ : ℝ) := Real.sq_sqrt (le_of_lt hΔR_pos)
  let r : ℝ := (((ℓ : ℝ) - μ) + s_real) / 2
  let s : ℝ := (((ℓ : ℝ) - μ) - s_real) / 2
  have hrs_ne : r ≠ s := by
    intro heq
    have : s_real = 0 := by simp only [r, s] at heq; linarith
    linarith
  have hj_roots : ∀ j : Fin n, j ≠ i₀ → ev j = r ∨ ev j = s := by
    intro j hne
    have hq := hquad_of_sum_zero (v j) (ev j) (hv_ne_zero j) (hj_sum_zero j hne) (hv_eig j)
    have hΔ_cast : (Δ : ℝ) = ((ℓ : ℝ) - μ) ^ 2 + 4 * ((k : ℝ) - μ) := by
      simp [Δ]
    have hfac : (ev j - r) * (ev j - s) = 0 := by
      have : (ev j - r) * (ev j - s) =
          ev j ^ 2 - ((ℓ : ℝ) - μ) * ev j + (((ℓ : ℝ) - μ) ^ 2 - s_real ^ 2) / 4 := by
        simp only [r, s]; ring
      rw [this, hs_sq, hΔ_cast]
      linarith
    rcases mul_eq_zero.mp hfac with hr | hs_eq
    · exact Or.inl (sub_eq_zero.mp hr)
    · exact Or.inr (sub_eq_zero.mp hs_eq)
  let S : Finset (Fin n) := Finset.univ.erase i₀
  let Fr : Finset (Fin n) := S.filter (fun j => ev j = r)
  let Fs : Finset (Fin n) := S.filter (fun j => ev j = s)
  have hFrFs_disj : Disjoint Fr Fs := by
    rw [Finset.disjoint_filter]
    intro j _ hr hs_eq
    exact hrs_ne (hr.symm.trans hs_eq)
  have hFrFs_union : Fr ∪ Fs = S := by
    ext j
    simp only [Fr, Fs, Finset.mem_union, Finset.mem_filter]
    refine ⟨fun h => h.elim (·.1) (·.1), fun hjS => ?_⟩
    have hne : j ≠ i₀ := (Finset.mem_erase.mp hjS).1
    rcases hj_roots j hne with hr | hs_eq
    · exact Or.inl ⟨hjS, hr⟩
    · exact Or.inr ⟨hjS, hs_eq⟩
  let f : ℕ := Fr.card
  let g : ℕ := Fs.card
  have hS_card : S.card = n - 1 := by
    simp [S, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
  have hfg_sum : f + g = n - 1 := by
    have hcard := Finset.card_union_of_disjoint hFrFs_disj
    rw [hFrFs_union, hS_card] at hcard
    exact hcard.symm
  have htrace : (k : ℝ) + (f : ℝ) * r + (g : ℝ) * s = 0 := by
    have htr0 : A.trace = 0 := SimpleGraph.trace_adjMatrix ℝ G
    have htr_sum : A.trace = ∑ j : Fin n, ev j := hA.trace_eq_sum_eigenvalues
    rw [htr0] at htr_sum
    have huniv : ∑ j : Fin n, ev j = ev i₀ + ∑ j ∈ S, ev j := by
      symm
      exact Finset.add_sum_erase Finset.univ ev (Finset.mem_univ i₀)
    have hS_sum : ∑ j ∈ S, ev j = (f : ℝ) * r + (g : ℝ) * s := by
      rw [← hFrFs_union, Finset.sum_union hFrFs_disj]
      have hsum_r : ∑ j ∈ Fr, ev j = (f : ℝ) * r := by
        have : ∑ j ∈ Fr, ev j = ∑ _j ∈ Fr, r :=
          Finset.sum_congr rfl fun j hj => (Finset.mem_filter.mp hj).2
        rw [this, Finset.sum_const, nsmul_eq_mul]
      have hsum_s : ∑ j ∈ Fs, ev j = (g : ℝ) * s := by
        have : ∑ j ∈ Fs, ev j = ∑ _j ∈ Fs, s :=
          Finset.sum_congr rfl fun j hj => (Finset.mem_filter.mp hj).2
        rw [this, Finset.sum_const, nsmul_eq_mul]
      rw [hsum_r, hsum_s]
    linarith [htr_sum, huniv, hi₀_ev, hS_sum]
  have hrel_real :
      2 * (k : ℝ) + ((n : ℝ) - 1) * ((ℓ : ℝ) - μ) + ((f : ℝ) - g) * s_real = 0 := by
    have hfgR : (f : ℝ) + (g : ℝ) = (n : ℝ) - 1 := by
      have : (f + g : ℕ) = n - 1 := hfg_sum
      have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      calc (f : ℝ) + (g : ℝ) = ((f + g : ℕ) : ℝ) := (Nat.cast_add f g).symm
        _ = ((n - 1 : ℕ) : ℝ) := by rw [this]
        _ = (n : ℝ) - 1 := hn1
    have hlin : 2 * ((k : ℝ) + (f : ℝ) * r + (g : ℝ) * s) =
        2 * (k : ℝ) + ((f : ℝ) + g) * ((ℓ : ℝ) - μ) + ((f : ℝ) - g) * s_real := by
      simp only [r, s]; ring
    rw [htrace, mul_zero, hfgR] at hlin
    exact hlin.symm
  have hfg_ne : (f : ℤ) - (g : ℤ) ≠ 0 := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hsq_real : ((f : ℝ) - g) ^ 2 * (Δ : ℝ) =
      (2 * (k : ℝ) + ((n : ℝ) - 1) * ((ℓ : ℝ) - μ)) ^ 2 := by
    have h1 : ((f : ℝ) - g) * s_real = -(2 * (k : ℝ) + ((n : ℝ) - 1) * ((ℓ : ℝ) - μ)) := by
      linarith
    calc ((f : ℝ) - g) ^ 2 * (Δ : ℝ)
        = (((f : ℝ) - g) * s_real) ^ 2 := by rw [mul_pow, hs_sq]
      _ = (2 * (k : ℝ) + ((n : ℝ) - 1) * ((ℓ : ℝ) - μ)) ^ 2 := by rw [h1]; ring
  have hsq_int : ((f : ℤ) - g) ^ 2 * Δ =
      (2 * (k : ℤ) + ((n : ℤ) - 1) * ((ℓ : ℤ) - μ)) ^ 2 := by
    exact_mod_cast hsq_real
  have hisSq_rat : IsSquare (Δ : ℚ) := by
    have hsq_rat : ((f : ℚ) - g) ^ 2 * (Δ : ℚ) =
        (2 * (k : ℚ) + ((n : ℚ) - 1) * ((ℓ : ℚ) - μ)) ^ 2 := by
      exact_mod_cast hsq_int
    have hfg_rat_ne : (f : ℚ) - (g : ℚ) ≠ 0 := by exact_mod_cast hfg_ne
    let q : ℚ := (2 * (k : ℚ) + ((n : ℚ) - 1) * ((ℓ : ℚ) - μ)) / ((f : ℚ) - g)
    refine ⟨q, ?_⟩
    have hq_sq : q * q = (Δ : ℚ) := by
      simp only [q]
      field_simp [hfg_rat_ne]
      linarith
    exact hq_sq.symm
  have hisSq_int : IsSquare Δ := Rat.isSquare_intCast_iff.mp hisSq_rat
  obtain ⟨z, hz⟩ := hisSq_int
  let d : ℕ := z.natAbs
  have hd_sq : (d : ℤ) ^ 2 = Δ := by
    have : (d : ℤ) ^ 2 = z ^ 2 := Int.natAbs_pow_two z
    rw [this, sq, ← hz]
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd_zero : d = 0 := by omega
    rw [hd_zero] at hd_sq
    omega
  have hs_eq_d : s_real = (d : ℝ) := by
    have hΔ_eq_dR : (Δ : ℝ) = (d : ℝ) ^ 2 := by exact_mod_cast hd_sq.symm
    simp only [s_real, hΔ_eq_dR, Real.sqrt_sq (Nat.cast_nonneg d)]
  have hrel_int :
      2 * (k : ℤ) + ((n : ℤ) - 1) * ((ℓ : ℤ) - μ) + ((f : ℤ) - g) * (d : ℤ) = 0 := by
    rw [hs_eq_d] at hrel_real
    exact_mod_cast hrel_real
  exact ⟨d, f, g, hd_pos, hd_sq.symm, hfg_sum, hrel_int⟩

theorem srg_spec_params_le_14_bool :
    ((List.range 15).all fun n =>
      !(Nat.beq (n % 2) 0) ||
      (List.range 15).all fun k =>
        !(Nat.ble 1 k && Nat.ble (k + 2) n) ||
        (List.range 15).all fun ℓ =>
          !(Nat.ble (ℓ + 1) k) ||
          (List.range 15).all fun μ =>
            !(Nat.ble 1 μ && Nat.ble (μ + 1) k &&
              Nat.beq (k * (k - ℓ - 1)) ((n - k - 1) * μ)) ||
            (List.range 15).all fun d =>
              !(Nat.ble 1 d &&
                Nat.beq (((ℓ - μ) + (μ - ℓ)) * ((ℓ - μ) + (μ - ℓ)) + 4 * (k - μ)) (d * d)) ||
              (List.range 15).all fun f =>
                !(Nat.ble f (n - 1) &&
                  Nat.beq (2 * k + (n - 1) * ℓ + f * d) ((n - 1) * μ + (n - 1 - f) * d)) ||
                (Nat.beq n 10 && Nat.beq k 3 && Nat.beq ℓ 0 && Nat.beq μ 1) ||
                (Nat.beq n 10 && Nat.beq k 6 && Nat.beq ℓ 3 && Nat.beq μ 4)) = true := by
  decide +kernel

theorem even_srg_order_le_14 (n k ℓ μ : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1) (hμ : 1 ≤ μ) (hμk : μ < k)
    (hn : Even n) (hle : n ≤ 14) :
    (n = 10 ∧ k = 3 ∧ ℓ = 0 ∧ μ = 1) ∨ (n = 10 ∧ k = 6 ∧ ℓ = 3 ∧ μ = 4) := by
  obtain ⟨hℓ_le, _, _⟩ := srg_spec_basic_param_bounds hSRG hk hkn
  have hn_pos : 0 < n := by omega
  have hparam : k * (k - ℓ - 1) = (n - k - 1) * μ := hSRG.param_eq G hn_pos
  obtain ⟨d, f, g, hd_pos, hd_sq, hfg, hmult⟩ :=
    even_srg_integral_conditions n k ℓ μ G hSRG hk hkn hμ hn
  have hd_nat : ((ℓ - μ) + (μ - ℓ)) * ((ℓ - μ) + (μ - ℓ)) + 4 * (k - μ) = d * d := by
    have h1 : (((ℓ - μ) + (μ - ℓ) : ℕ) : ℤ) ^ 2 = ((ℓ : ℤ) - μ) ^ 2 := by
      by_cases hℓμ : ℓ ≤ μ
      · have hsub1 : ℓ - μ = 0 := by omega
        have hsub2 : ((μ - ℓ : ℕ) : ℤ) = (μ : ℤ) - ℓ := by omega
        rw [hsub1, zero_add, hsub2]; ring
      · have hsub1 : μ - ℓ = 0 := by omega
        have hsub2 : ((ℓ - μ : ℕ) : ℤ) = (ℓ : ℤ) - μ := by omega
        rw [hsub1, add_zero, hsub2]
    have hkm : ((k - μ : ℕ) : ℤ) = (k : ℤ) - μ := by omega
    have hZ : ((((ℓ - μ) + (μ - ℓ)) * ((ℓ - μ) + (μ - ℓ)) + 4 * (k - μ) : ℕ) : ℤ) =
        ((d * d : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
        ← sq, ← sq, h1, hkm, hd_sq]
    exact Nat.cast_injective hZ
  have hd_lt : d < 15 := by
    have ha_le : (ℓ - μ) + (μ - ℓ) ≤ 12 := by omega
    have ha_sq : ((ℓ - μ) + (μ - ℓ)) * ((ℓ - μ) + (μ - ℓ)) ≤ 12 * 12 :=
      Nat.mul_le_mul ha_le ha_le
    have hdd_le : d * d ≤ 192 := by omega
    by_contra hd_ge
    have h15 : 15 ≤ d := by omega
    have h225 : 15 * 15 ≤ d * d := Nat.mul_le_mul h15 h15
    omega
  have hg_eq : g = n - 1 - f := by omega
  have hmult_nat : 2 * k + (n - 1) * ℓ + f * d = (n - 1) * μ + (n - 1 - f) * d := by
    have hn1Z : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hZ : ((2 * k + (n - 1) * ℓ + f * d : ℕ) : ℤ) = (((n - 1) * μ + g * d : ℕ) : ℤ) := by
      push_cast
      rw [hn1Z]
      have hr1 : ((n : ℤ) - 1) * (ℓ : ℤ) - ((n : ℤ) - 1) * (μ : ℤ) =
          ((n : ℤ) - 1) * ((ℓ : ℤ) - μ) := by ring
      have hr2 : (f : ℤ) * (d : ℤ) - (g : ℤ) * (d : ℤ) = ((f : ℤ) - g) * (d : ℤ) := by ring
      linarith [hr1, hr2, hmult]
    have hN : 2 * k + (n - 1) * ℓ + f * d = (n - 1) * μ + g * d := by exact_mod_cast hZ
    rw [hg_eq] at hN
    exact hN
  have hb := srg_spec_params_le_14_bool
  rw [List.all_eq_true] at hb
  have hb1 := hb n (List.mem_range.mpr (by omega))
  have hev : Nat.beq (n % 2) 0 = true := by simp [Nat.even_iff.mp hn]
  simp only [hev, Bool.not_true, Bool.false_or, List.all_eq_true] at hb1
  have hb2 := hb1 k (List.mem_range.mpr (by omega))
  have hk_b : (Nat.ble 1 k && Nat.ble (k + 2) n) = true := by
    simp [Nat.ble_eq]; omega
  simp only [hk_b, Bool.not_true, Bool.false_or, List.all_eq_true] at hb2
  have hb3 := hb2 ℓ (List.mem_range.mpr (by omega))
  have hℓ_b : Nat.ble (ℓ + 1) k = true := by simp [Nat.ble_eq, hℓ_le]
  simp only [hℓ_b, Bool.not_true, Bool.false_or, List.all_eq_true] at hb3
  have hb4 := hb3 μ (List.mem_range.mpr (by omega))
  have hμ_b : (Nat.ble 1 μ && Nat.ble (μ + 1) k &&
      Nat.beq (k * (k - ℓ - 1)) ((n - k - 1) * μ)) = true := by
    simp [Nat.ble_eq, hμ, hparam]; omega
  simp only [hμ_b, Bool.not_true, Bool.false_or, List.all_eq_true] at hb4
  have hb5 := hb4 d (List.mem_range.mpr hd_lt)
  have hd_b : (Nat.ble 1 d &&
      Nat.beq (((ℓ - μ) + (μ - ℓ)) * ((ℓ - μ) + (μ - ℓ)) + 4 * (k - μ)) (d * d)) = true := by
    simp [Nat.ble_eq, hd_nat]; omega
  simp only [hd_b, Bool.not_true, Bool.false_or, List.all_eq_true] at hb5
  have hb6 := hb5 f (List.mem_range.mpr (by omega))
  have hf_b : (Nat.ble f (n - 1) &&
      Nat.beq (2 * k + (n - 1) * ℓ + f * d) ((n - 1) * μ + (n - 1 - f) * d)) = true := by
    simp [Nat.ble_eq, hmult_nat]; omega
  simp only [hf_b, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    Nat.beq_eq] at hb6
  rcases hb6 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ | ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

/-- Every connected even-order SRG on `n ≤ 14` vertices not isomorphic to the Petersen graph
is `k`-edge-colorable (Class 1). -/
theorem srg_even_order_le_14_colorable
    {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1)
    (hconn : G.Connected) (heven : Even n) (hle : n ≤ 14)
    (hpet : IsEmpty (G ≃g OMA.S_arxiv_1810_06660.petersen)) :
    G.lineGraph.Colorable k := by
  have hn : 0 < n := by omega
  have hμ1 : 1 ≤ μ := srg_one_le_mu G hSRG hk hkn hconn
  have hμ_le : μ ≤ k := srg_mu_le_k G hSRG hn hkn
  rcases Nat.eq_or_lt_of_le hμ_le with hμ_eq | hμ_lt
  · exact srg_multipartite_colorable G hSRG hk hkn heven hμ_eq
  · rcases even_srg_order_le_14 n k ℓ μ G hSRG hk hkn hμ1 hμ_lt heven hle with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨iso⟩ := srg_10_3_0_1_iso_petersen G hSRG
      exact False.elim (hpet.false iso)
    · exact srg_10_6_3_4_colorable G hSRG

/-! ## Section 5: Stage 2 Hypotheses and Main Reduction -/

/-- Chetwynd–Hilton 1-Factorization / Overfull Regular Graph Conjecture for `16 ≤ n`:
every `k`-regular simple graph on an even number `n ≥ 16` of vertices with `n ≤ 2 * k`
is `k`-edge-colorable (1-factorizable). -/
def H1 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsRegularOfDegree k → 16 ≤ n → n ≤ 2 * k → Even n → G.lineGraph.Colorable k

/-- Sparse integral primitive even-order strongly regular graphs (`16 ≤ n`, `4 ≤ k`, `2 * k < n`,
`1 ≤ μ < k`, with integer eigenvalue discriminant `d ^ 2` and multiplicities `f, g`)
are `k`-edge-colorable (Class 1). -/
def H2 : Prop :=
  ∀ (n k ℓ μ d f g : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsSRGWith n k ℓ μ → 16 ≤ n → 4 ≤ k → 2 * k < n → 1 ≤ μ → μ < k →
    0 < d → ((ℓ : ℤ) - μ) ^ 2 + 4 * ((k : ℤ) - μ) = (d : ℤ) ^ 2 →
    f + g = n - 1 →
    2 * (k : ℤ) + ((n : ℤ) - 1) * ((ℓ : ℤ) - μ) + ((f : ℤ) - g) * (d : ℤ) = 0 →
    G.Connected → Even n → G.lineGraph.Colorable k

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1810_06660.main := by
  intro hOverfull hSparseInt n k ℓ μ G _inst hSRG hk hkn hconn heven hpet
  have hn : 0 < n := by omega
  apply lineGraph_chromaticNumber_eq_of_colorable G hSRG.regular hn
  by_cases hle14 : n ≤ 14
  · exact srg_even_order_le_14_colorable G hSRG hk hkn hconn heven hle14 hpet
  · have hn16 : 16 ≤ n := by
      rcases heven with ⟨r, hr⟩
      omega
    have hμ1 : 1 ≤ μ := srg_one_le_mu G hSRG hk hkn hconn
    have hμ_le : μ ≤ k := srg_mu_le_k G hSRG hn hkn
    rcases Nat.eq_or_lt_of_le hμ_le with hμ_eq | hμ_lt
    · exact srg_multipartite_colorable G hSRG hk hkn heven hμ_eq
    · by_cases hk3 : k ≤ 3
      · exact False.elim (srg_even_deg_le_three_of_mu_lt G hSRG hk hk3 hkn hμ1 hμ_lt heven hpet)
      · have hk4 : 4 ≤ k := by omega
        by_cases hnk : n ≤ 2 * k
        · exact hOverfull n k G hSRG.regular hn16 hnk heven
        · obtain ⟨d, f, g, hd_pos, hd_sq, hfg, hmult⟩ :=
            even_srg_integral_conditions n k ℓ μ G hSRG hk hkn hμ1 heven
          exact hSparseInt n k ℓ μ d f g G hSRG hn16 hk4 (by omega) hμ1 hμ_lt
            hd_pos hd_sq hfg hmult hconn heven

end OMA.R_arxiv_1810_06660_R2
