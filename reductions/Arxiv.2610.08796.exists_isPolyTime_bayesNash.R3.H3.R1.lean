import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R3.H3.R1 of step R3.H3
-- Credit: @paynebrowning (formalizing Section 2 & Lemmas 3-6 of Shiva Kintali, SecurityGames-short.pdf, Nov 24, 2026)
-- Each H becomes its own step once this file is accepted. Proving all of them closes R3.H3.

/-!
Modular 3-part reduction of `R3.H3` (Shiva Kintali's Section 2 & Lemmas 3–6: Grouped Baïou–Balinski
Quota-Sweep & Fixed-Witness Blocker Oracle):

* `H1` (Generic Polynomial-Time Ordinal-Transportation Quota Sweep — Kintali Lemma 3):
  Pure algorithmic / `FinTM2` core with zero game theory. Given a finite bipartite
  ordinal-transportation market `(nR, buys, sites, bids, T)` where `buys` are positive buyer masses,
  `sites` are positive site injection rates, `bids` is a list of `(buyer, site, bRank)` ordered
  best-first per site with strict per-buyer ranks and exclusive private buyers `nR ≤ buyer`, and
  `0 < T < ∑_{nR ≤ b} buys[b]` is the target total private purchase, computes in `IsPolyTime` a
  pressure `t ≥ 0` and a feasible stable allocation achieving total private purchase `T`.
* `H2` (Security-Game Market Reduction, Blocker Extraction & Fixed Witness — Kintali §2 & Lemmas 4–6):
  Constructs `IsPolyTime` maps `grid`, `build`, and `extract` (closed-form arithmetic and list
  operations, with no quota-sweep loop) together with the fixed sparse witness `W` of size at most
  `g.numTypes + g.numTargets`. For every valid `(g, η)` and quote selection `Q`, `build ((g, η), Q)`
  is a valid ordinal-transportation market, and for any feasible stable contact allocation `(t, a)`
  of that market, `extract (((g, η), Q), (t, a))` returns `(x, B)` where either `x` admits an
  `η`-relaxed equilibrium (Lemma 4) or `B` is `Q`-disjoint and captures a witness in `W`
  (Lemmas 5–6).
* `H3` (`IsPolyTime` Composition): Closure of `IsPolyTime` under the pipeline
  `z ↦ extract (z, otSweep (build z))`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3_H3_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Generic polynomial-time ordinal-transportation quota sweep (Kintali, Lemma 3): given positive
buyer masses `buys`, positive site injection rates `sites`, bids `(buyer, site, bRank)` listed
best-first per site with strict per-buyer rankings and exclusive private buyers `nR ≤ buyer`, and
target private purchase `0 < T < ∑_{nR ≤ b} buys[b]`, compute in `IsPolyTime` a pressure `t ≥ 0`
and a feasible stable allocation achieving total private purchase `T`. -/
def H1 : Prop :=
  ∃ otSweep : (ℕ × List ℚ × List ℚ × List (ℕ × ℕ × ℕ) × ℚ) → ℚ × List ℚ,
    IsPolyTime otSweep ∧
    ∀ (nR : ℕ) (buys sites : List ℚ) (bids : List (ℕ × ℕ × ℕ)) (T : ℚ),
      let E := Fin bids.length
      let b (i : E) := (bids.get i).1; let s (i : E) := (bids.get i).2.1
      let br (i : E) := (bids.get i).2.2
      (∀ v ∈ buys, 0 < v) → (∀ r ∈ sites, 0 < r) →
      (∀ i : E, b i < buys.length ∧ s i < sites.length) →
      (∀ i j : E, i ≠ j → b i = b j → br i ≠ br j ∧ b i < nR) →
      0 < T → T < (∑ i : E, if nR ≤ b i then buys[b i]?.getD 0 else 0) →
      let (t, a) := otSweep (nR, buys, sites, bids, T)
      let f (i : E) := a[i.val]?.getD 0
      let bs u := ∑ i : E, if b i = u then f i else 0
      let ss v := ∑ i : E, if s i = v then f i else 0
      0 ≤ t ∧ (∀ i, 0 ≤ f i) ∧
      (∀ u, bs u ≤ buys[u]?.getD 0) ∧ (∀ v, ss v ≤ t * sites[v]?.getD 0) ∧
      (∑ i : E, if nR ≤ b i then f i else 0) = T ∧
      ∀ i : E,
        (bs (b i) = buys[b i]?.getD 0 ∧ ∀ j, b j = b i → br i < br j → f j = 0) ∨
        (ss (s i) = t * sites[s i]?.getD 0 ∧ ∀ j, s j = s i → i < j → f j = 0)

/-- Security-game grouped market builder, blocker extractor, and fixed-witness correctness
(Kintali, §2 & Lemmas 4–6): polynomial-time `grid`, `build`, and `extract` maps such that every
quote selection compiles to a valid ordinal-transportation market whose stable contact allocations
extract to either an `η`-relaxed equilibrium coverage or `Q`-disjoint blocker intervals capturing
a fixed sparse witness `W` of size at most `g.numTypes + g.numTargets`. -/
def H2 : Prop :=
  let I := (GameInput × ℚ) × List (List (List ℕ))
  ∃ (gr : GameInput × ℚ → ℕ) (bd : I → ℕ × List ℚ × List ℚ × List (ℕ × ℕ × ℕ) × ℚ)
    (ex : I × (ℚ × List ℚ) → List ℚ × List (List (ℕ × ℕ))),
  IsPolyTime gr ∧ IsPolyTime bd ∧ IsPolyTime ex ∧
  ∀ g η, g.Valid → 0 < η →
  let G := gr (g, η); let k := g.numTypes; let m := g.numTargets
  1 ≤ G ∧ ∃ W : List (ℕ × ℕ × ℕ), W.length ≤ k + m ∧
  (∀ w ∈ W, w.1 < k ∧ w.2.1 < m ∧ w.2.2 < G) ∧ ∀ Q,
  let (nR, bu, si, es, T) := bd ((g, η), Q)
  let b (i : Fin es.length) := (es.get i).1; let s i := (es.get i).2.1; let r i := (es.get i).2.2
  let bv u := bu[u]?.getD 0; let sv v := si[v]?.getD 0
  (∀ v ∈ bu, 0 < v) ∧ (∀ v ∈ si, 0 < v) ∧ (∀ i, b i < bu.length ∧ s i < si.length) ∧
  (∀ i j, i ≠ j → b i = b j → r i ≠ r j ∧ b i < nR) ∧
  0 < T ∧ T < (∑ i, if nR ≤ b i then bv (b i) else 0) ∧
  ∀ t a, let f (i : Fin es.length) := a[i.val]?.getD 0
  let bs u := ∑ i, if b i = u then f i else 0; let ss v := ∑ i, if s i = v then f i else 0
  0 ≤ t → (∀ i, 0 ≤ f i) → (∀ u, bs u ≤ bv u) → (∀ v, ss v ≤ t * sv v) →
  (∑ i, if nR ≤ b i then f i else 0) = T →
  (∀ i, (bs (b i) = bv (b i) ∧ ∀ j, b j = b i → r i < r j → f j = 0) ∨
    (ss (s i) = t * sv (s i) ∧ ∀ j, s j = s i → i < j → f j = 0)) →
  let (x, B) := ex (((g, η), Q), t, a); let bp i j := (B[i]?.getD [])[j]?.getD (0, 0)
  (∃ (q : Fin k → Fin m → ℚ) (lam : ℚ), let c (j : Fin m) := x[j.val]?.getD 0
    let u i j := (1 - c j) * (g.attackerPayoff i j).1 + c j * (g.attackerPayoff i j).2
    let p j := (∑ i, q i j) * ((g.defenderPayoff j).2 - (g.defenderPayoff j).1)
    x.length = m ∧ (∑ j, c j) = g.1 ∧ (∀ j, 0 ≤ c j ∧ c j ≤ 1) ∧ 0 ≤ lam ∧
    (∀ i, (∑ j, q i j) = g.prior i ∧ ∀ j, 0 ≤ q i j) ∧ (∀ i j l, 0 < q i j → u i l ≤ u i j + η) ∧
    ∀ j, (0 < c j → lam ≤ p j + η) ∧ (c j < 1 → p j ≤ lam + η)) ∨
  ((∀ i < k, ∀ j < m, let v := bp i j; v.1 ≤ v.2 ∧ v.2 ≤ G ∧
    ∀ z ∈ (Q[i]?.getD [])[j]?.getD [], ¬(v.1 ≤ z ∧ z < v.2)) ∧
  ∃ w ∈ W, let v := bp w.1 w.2.1; v.1 ≤ w.2.2 ∧ w.2.2 < v.2)

/-- Polynomial-time closure under the pipeline `z ↦ extract (z, otSweep (build z))`. -/
def H3 : Prop :=
  ∀ (build : (GameInput × ℚ) × List (List (List ℕ)) → ℕ × List ℚ × List ℚ × List (ℕ × ℕ × ℕ) × ℚ)
    (otSweep : (ℕ × List ℚ × List ℚ × List (ℕ × ℕ × ℕ) × ℚ) → ℚ × List ℚ)
    (extract : ((GameInput × ℚ) × List (List (List ℕ))) × (ℚ × List ℚ) → List ℚ × List (List (ℕ × ℕ))),
    IsPolyTime build → IsPolyTime otSweep → IsPolyTime extract →
    IsPolyTime (fun z : (GameInput × ℚ) × List (List (List ℕ)) => extract (z, otSweep (build z)))

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3.H3 := by
  intro h1 h2 h3
  obtain ⟨otSweep, hot_pt, hot_spec⟩ := h1
  obtain ⟨grid, build, extract, hgrid_pt, hbuild_pt, hextract_pt, h2_spec⟩ := h2
  refine ⟨grid, fun z => extract (z, otSweep (build z)), hgrid_pt,
    h3 build otSweep extract hbuild_pt hot_pt hextract_pt, ?_⟩
  intro g η hg hη
  obtain ⟨hG, W, hW_len, hW_bnd, hW_spec⟩ := h2_spec g η hg hη
  refine ⟨hG, W, hW_len, hW_bnd, fun Q => ?_⟩
  obtain ⟨hbuys, hsites, hbnd, huniq, hT0, hTcap, hres⟩ := hW_spec Q
  dsimp only
  rcases hM : build ((g, η), Q) with ⟨nR, buys, sites, bids, T⟩
  rw [hM] at hbuys hsites hbnd huniq hT0 hTcap hres
  obtain ⟨ht0, ha0, hbs, hss, hT, hstab⟩ :=
    hot_spec nR buys sites bids T hbuys hsites hbnd huniq hT0 hTcap
  rcases hO : otSweep (nR, buys, sites, bids, T) with ⟨t, a⟩
  rw [hO] at ht0 ha0 hbs hss hT hstab
  rcases hres t a ht0 ha0 hbs hss hT hstab with ⟨q, lam, hlen, hsum, hcb, hlam, hq, hu, hp⟩ | hblk
  · exact Or.inl ⟨q, lam, hlen, hsum, hcb, hlam, hq, hu, fun j => (hp j).1, fun j => (hp j).2⟩
  · exact Or.inr hblk

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3_H3_R1
