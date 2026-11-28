import OMAStatements.S_arxiv_1810_06660

/-!
# Round 1 Reduction for Cioabă–Guo–Haemers Conjecture 1.2 (`arxiv-1810.06660`)

Every connected strongly regular graph `G` of even order `n` except the Petersen graph has
chromatic index equal to its degree `k` (`G.lineGraph.chromaticNumber = k`).

In this first-stage reduction (`R1`), we prove unconditionally:
1. **Line-Graph Clique Lower Bound (`lineGraph_chromaticNumber_eq_iff_colorable`):**
   For any `k`-regular graph `G` on `Fin n` (`n > 0`), the `k` edges incident to vertex `0` form a
   `k`-clique in `G.lineGraph`, so `G.lineGraph.chromaticNumber = k ↔ G.lineGraph.Colorable k`.
2. **SRG Connectivity & Parameter Bounds (`srg_four_le_n`, `srg_two_le_k`, `srg_one_le_mu`, `srg_mu_le_k`):**
   Every connected non-complete non-empty even-order `SRG(n, k, ℓ, μ)` satisfies `4 ≤ n`, `2 ≤ k`,
   `1 ≤ μ ≤ k`, and `k * (k - ℓ - 1) = μ * (n - k - 1)`.
3. **All Complete Multipartite (Imprimitive `μ = k`) Even-Order SRGs (`srg_multipartite_colorable`):**
   When `μ = k`, non-adjacency is an equivalence relation partitioning `Fin n` into `m ≥ 2` parts of
   equal size `t = n - k ≥ 2` (`G ≃g completeEquipartiteGraph m t`), and for `Even (m * t)` we
   explicitly `((m - 1) * t)`-edge-color `K_{m × t}` via Kirkman 1-factorizations of `K_{2r}`
   (when `m` is even) and parity-bit blowup factorizations on `K_{2m}` (when `m` is odd, `t` even).
4. **Uniqueness of the Petersen Graph & All `k ≤ 3` Even-Order SRGs (`srg_10_3_0_1_iso_petersen`,
   `srg_even_deg_le_three`):**
   Every `SRG(10, 3, 0, 1)` on `Fin 10` is isomorphic to `OMA.S_arxiv_1810_06660.petersen`, and no
   other primitive (`1 ≤ μ < k`) even-order SRG parameter set exists with `k ≤ 3`.

This eliminates the Petersen graph exception completely and splits the remaining primitive
(`1 ≤ μ < k`, `4 ≤ k < n - 1`) even-order SRGs into the **dense** (`n ≤ 2 * k`, `H1`) and
**sparse** (`2 * k < n`, `H2`) regimes.
-/

namespace OMA.R_arxiv_1810_06660_R1

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

/-! ## Section 2: SRG Parameter and Connectivity Lemmas -/

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

theorem srg_two_le_k {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1)
    (hconn : G.Connected) (heven : Even n) :
    2 ≤ k := by
  have hn4 : 4 ≤ n := srg_four_le_n hk hkn heven
  by_contra hk2
  have hk1 : k = 1 := by omega
  obtain ⟨v₀, -⟩ : ∃ v₀ : Fin n, True := ⟨⟨0, by omega⟩, trivial⟩
  have hdeg₀ : (G.neighborFinset v₀).card = 1 := by
    rw [G.card_neighborFinset_eq_degree, hSRG.regular v₀, hk1]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdeg₀
  have hadj₀ : G.Adj v₀ u := by
    have hmem : u ∈ G.neighborFinset v₀ := by simp [hu]
    exact (G.mem_neighborFinset v₀ u).mp hmem
  have hdeg_u : (G.neighborFinset u).card = 1 := by
    rw [G.card_neighborFinset_eq_degree, hSRG.regular u, hk1]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdeg_u
  have hv₀_mem : v₀ ∈ G.neighborFinset u := (G.mem_neighborFinset u v₀).mpr hadj₀.symm
  rw [hz, Finset.mem_singleton] at hv₀_mem
  rw [← hv₀_mem] at hz
  have hwalk : ∀ x y : Fin n, G.Walk x y → (x = v₀ ∨ x = u) → (y = v₀ ∨ y = u) := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons a b c hab _ ih =>
      intro ha
      apply ih
      rcases ha with ha | ha
      · rw [ha] at hab
        have hb : b ∈ G.neighborFinset v₀ := (G.mem_neighborFinset v₀ b).mpr hab
        rw [hu, Finset.mem_singleton] at hb
        exact Or.inr hb
      · rw [ha] at hab
        have hb : b ∈ G.neighborFinset u := (G.mem_neighborFinset u b).mpr hab
        rw [hz, Finset.mem_singleton] at hb
        exact Or.inl hb
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {v₀, u} := by
    intro y _
    rcases (hconn v₀ y).elim (fun p => hwalk v₀ y p (Or.inl rfl)) with rfl | rfl <;> simp
  have hle : n ≤ 2 := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ ({v₀, u} : Finset (Fin n)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
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

theorem srg_param_eq {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hSRG : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = μ * (n - k - 1) := by
  rw [hSRG.param_eq G hn, mul_comm]

/-! ## Section 3: Unconditional Class-1 Proof for Complete Multipartite SRGs (`μ = k`) -/

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

theorem srg_not_adj_equivalence {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hSRG : G.IsSRGWith n k ℓ μ) (hμ : μ = k) :
    Equivalence (fun u v : Fin n => ¬ G.Adj u v) := by
  refine ⟨fun u => G.loopless.irrefl u, fun h => fun hadj => h hadj.symm, ?_⟩
  intro u v w huv hvw
  rw [srg_not_adj_iff_neighborFinset_eq G hSRG hμ] at huv hvw ⊢
  exact huv.trans hvw

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

theorem srg_multipartite_chromaticNumber {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hSRG : G.IsSRGWith n k ℓ μ) (hk : 0 < k) (hkn : k < n - 1)
    (heven : Even n) (hμ : μ = k) :
    G.lineGraph.chromaticNumber = (k : ℕ∞) := by
  have hn : 0 < n := by omega
  exact lineGraph_chromaticNumber_eq_of_colorable G hSRG.regular hn
    (srg_multipartite_colorable G hSRG hk hkn heven hμ)

/-! ## Section 4: Uniqueness of the Petersen Graph and Low-Degree (`k ≤ 3`) Classification -/

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

/-- Every `SRG(10, 3, 0, 1)` on `Fin 10` is isomorphic to the Petersen graph `K(5, 2)`. -/
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

/-- For an even-order primitive (`1 ≤ μ < k`) SRG with `0 < k ≤ 3` and `k < n - 1`,
the only feasible parameter tuple is `(10, 3, 0, 1)`. -/
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

/-- No even-order SRG with `0 < k ≤ 3`, `k < n - 1`, and `1 ≤ μ < k` can avoid being
isomorphic to the Petersen graph. -/
theorem srg_even_deg_le_three_of_mu_lt
    {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hk0 : 0 < k) (hk3 : k ≤ 3) (hkn : k < n - 1)
    (hμ1 : 1 ≤ μ) (hμk : μ < k) (heven : Even n)
    (hpet : IsEmpty (G ≃g OMA.S_arxiv_1810_06660.petersen)) :
    False := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := srg_even_deg_le_three_params G h hk0 hk3 hkn hμ1 hμk heven
  obtain ⟨iso⟩ := srg_10_3_0_1_iso_petersen G h
  exact hpet.false iso

/-- Low-degree (`0 < k ≤ 3`) theorem for connected even-order SRGs:
every such graph not isomorphic to the Petersen graph has `μ = k` and is Class 1. -/
theorem srg_even_deg_le_three
    {n k ℓ μ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hk0 : 0 < k) (hk3 : k ≤ 3) (hkn : k < n - 1)
    (hconn : G.Connected) (heven : Even n)
    (hpet : IsEmpty (G ≃g OMA.S_arxiv_1810_06660.petersen)) :
    G.lineGraph.Colorable k := by
  have hn : 0 < n := by omega
  have hμ1 : 1 ≤ μ := srg_one_le_mu G h hk0 hkn hconn
  have hμ_le : μ ≤ k := srg_mu_le_k G h hn hkn
  rcases Nat.eq_or_lt_of_le hμ_le with h_eq | h_lt
  · exact srg_multipartite_colorable G h hk0 hkn heven h_eq
  · exact False.elim (srg_even_deg_le_three_of_mu_lt G h hk0 hk3 hkn hμ1 h_lt heven hpet)

/-! ## Section 5: Stage 1 Hypotheses and Main Reduction -/

/-- Dense primitive strongly regular graphs of even order (`n ≤ 2 * k`, `4 ≤ k < n - 1`, `1 ≤ μ < k`)
are `k`-edge-colorable (Class 1). -/
def H1 : Prop :=
  ∀ (n k ℓ μ : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsSRGWith n k ℓ μ → 4 ≤ k → k < n - 1 → 1 ≤ μ → μ < k →
    n ≤ 2 * k → G.Connected → Even n → G.lineGraph.Colorable k

/-- Sparse primitive strongly regular graphs of even order (`2 * k < n`, `4 ≤ k < n - 1`, `1 ≤ μ < k`)
are `k`-edge-colorable (Class 1). -/
def H2 : Prop :=
  ∀ (n k ℓ μ : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsSRGWith n k ℓ μ → 4 ≤ k → k < n - 1 → 1 ≤ μ → μ < k →
    2 * k < n → G.Connected → Even n → G.lineGraph.Colorable k

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1810_06660.main := by
  intro hDense hSparse n k ℓ μ G _inst hSRG hk hkn hconn heven hpet
  have hn : 0 < n := by omega
  apply lineGraph_chromaticNumber_eq_of_colorable G hSRG.regular hn
  have hμ1 : 1 ≤ μ := srg_one_le_mu G hSRG hk hkn hconn
  have hμ_le : μ ≤ k := srg_mu_le_k G hSRG hn hkn
  rcases Nat.eq_or_lt_of_le hμ_le with hμ_eq | hμ_lt
  · exact srg_multipartite_colorable G hSRG hk hkn heven hμ_eq
  · by_cases hk3 : k ≤ 3
    · exact False.elim (srg_even_deg_le_three_of_mu_lt G hSRG hk hk3 hkn hμ1 hμ_lt heven hpet)
    · have hk4 : 4 ≤ k := by omega
      by_cases hnk : n ≤ 2 * k
      · exact hDense n k ℓ μ G hSRG hk4 hkn hμ1 hμ_lt hnk hconn heven
      · exact hSparse n k ℓ μ G hSRG hk4 hkn hμ1 hμ_lt (by omega) hconn heven

end OMA.R_arxiv_1810_06660_R1
