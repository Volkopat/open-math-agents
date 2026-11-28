import FormalConjectures.ErdosProblems.«1165»
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Reduction of `Erdos1165.erdos_1165.variants.hao_li_okada_zheng`

Following C. Hao, X. Li, I. Okada, and Y. Zheng (*Favorite sites for simple random walk in two and
more dimensions*, arXiv:2409.00995, 2024, Theorem 1.1) and G. Pólya (1921), we transfer the
universe-polymorphic random walk `{Ω : Type*}` to the canonical `Type 0` path space `ℕ → ℤ × ℤ`
equipped with `Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count steps)` and
reduce `limsup #F(n) = 3` a.s. to three independent pillars on the canonical space:
1. `H1`: **Pólya's recurrence / unbounded local time at the origin** — almost surely, the local time
   `localTime coord n s (0, 0)` takes arbitrarily large values.
2. `H2`: **Summability of 4-way favourite-site ties by local-time height** (HLOZ24, Prop. 4.7) —
   the probabilities of the height-`m` 4-way tie events `tieAtLevel 4 m` are summable over `m : ℕ`.
3. `H3`: **Infinitely many 3-way favourite-site ties across local-time heights** (HLOZ24, lower
   bound) — almost surely, `tieAtLevel 3 m` occurs for infinitely many local-time heights `m`.

Inside `main`, we prove from scratch:
- Equality of the pushforward law `ℙ.map (fun ω k => X k ω)` with the canonical infinite product
  measure via `ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map` and `hX.isUniform`.
- Measurability of finite-horizon path functionals via finite truncation `Fin n → ℤ × ℤ`
  (`DiscreteMeasurableSpace`), giving measurability of the `limsup = 3` event.
- Deterministic local-time monotonicity, peak existence, and the `peak ≤ n + 1` bound.
- First Borel–Cantelli (`MeasureTheory.ae_eventually_notMem`) applied to `H2` together with `H1`
  to yield `∀ᶠ n, (favouriteSites coord n s).encard ≤ 3` a.s.
- Level-to-time transfer from `H3` to yield `∃ᶠ n, 3 ≤ (favouriteSites coord n s).encard` a.s.,
  assembly of `limsup = 3` in `ℕ∞`, and pullback from `ℙ.map Φ` to `ℙ`.

Thanks to @MechaNuggan for the local-time height indexing `tieAtLevel`, `peak ≤ n + 1` transfer,
and Borel–Cantelli decomposition.
Credit: @tkaiman
-/

namespace OMA.R_Erdos1165_erdos_1165_variants_hao_li_okada_zheng_R1

open MeasureTheory Filter Erdos1165
open scoped ProbabilityTheory ENNReal

private abbrev Path := ℕ → ℤ × ℤ

private abbrev coord : ℕ → Path → ℤ × ℤ := fun k s => s k

private noncomputable def srwMeasure : Measure Path :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)

private def truncPath (n : ℕ) (v : Fin n → ℤ × ℤ) : Path :=
  fun j => if h : j < n then v ⟨j, h⟩ else (0, 0)

private lemma position_truncPath {n k : ℕ} (hk : k ≤ n) (s : Path) :
    position coord k (truncPath n (fun j : Fin n => s j)) = position coord k s := by
  unfold position
  refine Finset.sum_congr rfl fun j hj => ?_
  have hlt : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  simp [coord, truncPath, hlt]

private lemma localTime_truncPath (n : ℕ) (s : Path) (x : ℤ × ℤ) :
    localTime coord n (truncPath n (fun j : Fin n => s j)) x = localTime coord n s x := by
  unfold localTime
  congr 1
  refine Finset.filter_congr fun k hk => ?_
  have hle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [position_truncPath hle s]

private lemma favouriteSites_truncPath (n : ℕ) (s : Path) :
    favouriteSites coord n (truncPath n (fun j : Fin n => s j)) = favouriteSites coord n s := by
  ext x
  simp only [favouriteSites, Set.mem_ofPred_eq]
  simp_rw [localTime_truncPath]

private lemma measurable_encard_favouriteSites (n : ℕ) :
    Measurable (fun s : Path => (favouriteSites coord n s).encard) := by
  have hfac : (fun s : Path => (favouriteSites coord n s).encard) =
      (fun v : Fin n → ℤ × ℤ => (favouriteSites coord n (truncPath n v)).encard) ∘
        (fun s (j : Fin n) => s j) := by
    ext s
    exact (congrArg Set.encard (favouriteSites_truncPath n s)).symm
  rw [hfac]
  exact Measurable.of_discrete.comp (measurable_pi_lambda _ fun j => measurable_pi_apply j.1)

private lemma localTime_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (x : ℤ × ℤ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    localTime X n₁ ω x ≤ localTime X n₂ ω x := by
  unfold localTime
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ h)))

private lemma localTime_le_succ {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) (x : ℤ × ℤ) :
    localTime X n ω x ≤ n + 1 := by
  unfold localTime
  calc ((Finset.range (n + 1)).filter fun k => position X k ω = x).card
      ≤ (Finset.range (n + 1)).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.card_range (n + 1)

private lemma exists_max_localTime {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) :
    ∃ m : ℕ, (∀ x, localTime X n ω x ≤ m) ∧ (∃ x, localTime X n ω x = m) := by
  let S : Finset (ℤ × ℤ) := (Finset.range (n + 1)).image (fun k => position X k ω)
  have hS : S.Nonempty :=
    ⟨position X 0 ω, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), rfl⟩⟩
  obtain ⟨x₀, _, hmax⟩ := S.exists_max_image (fun x => localTime X n ω x) hS
  refine ⟨localTime X n ω x₀, fun x => ?_, ⟨x₀, rfl⟩⟩
  by_cases hx : x ∈ S
  · exact hmax x hx
  · have hzero : localTime X n ω x = 0 := by
      unfold localTime
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk heq
      exact hx (Finset.mem_image.mpr ⟨k, hk, heq⟩)
    omega

private lemma limsup_eq_three_of_bounds {a : ℕ → ℕ∞}
    (hle : ∀ᶠ n in Filter.atTop, a n ≤ 3) (hge : ∃ᶠ n in Filter.atTop, (3 : ℕ∞) ≤ a n) :
    Filter.limsup a Filter.atTop = 3 := by
  refine le_antisymm ?_ ?_
  · exact Filter.limsup_le_of_le (by isBoundedDefault) hle
  · refine Filter.le_limsup_of_frequently_le hge (by isBoundedDefault)

private lemma measurableSet_limsup_eq_three :
    MeasurableSet {s : Path | Filter.limsup (fun n => (favouriteSites coord n s).encard) Filter.atTop = 3} := by
  have heq : {s : Path | Filter.limsup (fun n => (favouriteSites coord n s).encard) Filter.atTop = 3} =
      (⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {s : Path | (favouriteSites coord n s).encard ≤ 3}) ∩
      (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {s : Path | (3 : ℕ∞) ≤ (favouriteSites coord n s).encard}) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hlim
      constructor
      · have hlt : Filter.limsup (fun n => (favouriteSites coord n s).encard) Filter.atTop < (4 : ℕ∞) := by
          rw [hlim]; decide
        have hev := Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)
        rw [Filter.eventually_atTop] at hev
        obtain ⟨N, hN⟩ := hev
        refine ⟨N, fun n hn => ?_⟩
        have h4 : (favouriteSites coord n s).encard < 4 := hN n hn
        cases hval : (favouriteSites coord n s).encard with
        | top => simp [hval] at h4
        | coe k =>
          rw [hval] at h4
          have hk : k < 4 := (ENat.natCast_lt_natCast (n := k) (m := 4)).mp h4
          exact (ENat.natCast_le_natCast (n := k) (m := 3)).mpr (by omega)
      · intro N
        have hgt : (2 : ℕ∞) < Filter.limsup (fun n => (favouriteSites coord n s).encard) Filter.atTop := by
          rw [hlim]; decide
        have hfr := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hgt
        rw [Filter.frequently_atTop] at hfr
        obtain ⟨n, hn, h2⟩ := hfr N
        refine ⟨n, hn, ?_⟩
        cases hval : (favouriteSites coord n s).encard with
        | top => exact le_top
        | coe k =>
          rw [hval] at h2
          have hk : 2 < k := (ENat.natCast_lt_natCast (n := 2) (m := k)).mp h2
          exact (ENat.natCast_le_natCast (n := 3) (m := k)).mpr (by omega)
    · rintro ⟨⟨N, hle⟩, hge⟩
      refine limsup_eq_three_of_bounds ?_ ?_
      · rw [Filter.eventually_atTop]
        exact ⟨N, hle⟩
      · rw [Filter.frequently_atTop]
        intro N
        obtain ⟨n, hn, h3⟩ := hge N
        exact ⟨n, hn, h3⟩
  rw [heq]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
    exact (measurable_encard_favouriteSites n) (MeasurableSet.of_discrete (s := {y : ℕ∞ | y ≤ 3}))
  · refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => ?_
    exact (measurable_encard_favouriteSites n) (MeasurableSet.of_discrete (s := {y : ℕ∞ | (3 : ℕ∞) ≤ y}))

/-- **Pólya's recurrence / unbounded origin local time for the canonical 2D simple random walk**:
almost surely under the product SRW law on `ℕ → ℤ × ℤ`, the local time at `(0, 0)` is unbounded. -/
def H1 : Prop :=
  ∀ᵐ s ∂(Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)),
    ∀ M : ℕ, ∃ n : ℕ, M ≤ Erdos1165.localTime (fun k (s : ℕ → ℤ × ℤ) => s k) n s (0, 0)

/-- **Summability of 4-way favourite-site ties by local-time height** (Hao–Li–Okada–Zheng 2024,
Prop. 4.7): under the canonical 2D SRW law on `ℕ → ℤ × ℤ`, the sum over heights `m : ℕ` of the
probabilities that some time `n` has maximal local time `m` and at least `4` favourite sites is
finite. -/
def H2 : Prop :=
  (∑' m : ℕ,
    Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)
      {s : ℕ → ℤ × ℤ | ∃ n : ℕ,
        (∀ x, Erdos1165.localTime (fun k (s : ℕ → ℤ × ℤ) => s k) n s x ≤ m) ∧
        (∃ x, Erdos1165.localTime (fun k (s : ℕ → ℤ × ℤ) => s k) n s x = m) ∧
        (4 : ℕ∞) ≤ (Erdos1165.favouriteSites (fun k (s : ℕ → ℤ × ℤ) => s k) n s).encard}) ≠ ∞

/-- **Infinitely many 3-way favourite-site ties across local-time heights** (Hao–Li–Okada–Zheng
2024, lower bound): almost surely under the canonical 2D SRW law on `ℕ → ℤ × ℤ`, for every `M`
there exist a height `m ≥ M` and a time `n` with maximal local time `m` and at least `3` favourite
sites. -/
def H3 : Prop :=
  ∀ᵐ s ∂(Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)),
    ∀ M : ℕ, ∃ m ≥ M, ∃ n : ℕ,
      (∀ x, Erdos1165.localTime (fun k (s : ℕ → ℤ × ℤ) => s k) n s x ≤ m) ∧
      (∃ x, Erdos1165.localTime (fun k (s : ℕ → ℤ × ℤ) => s k) n s x = m) ∧
      (3 : ℕ∞) ≤ (Erdos1165.favouriteSites (fun k (s : ℕ → ℤ × ℤ) => s k) n s).encard

theorem main : H1 → H2 → H3 → type_of% @Erdos1165.erdos_1165.variants.hao_li_okada_zheng := by
  intro h1 h2 h3 Ω _ _ X hX
  -- Step 1: Canonical space almost-sure `limsup = 3` via First Borel–Cantelli + level-to-time transfer
  have hbc : ∀ᵐ s ∂srwMeasure, ∀ᶠ m in Filter.atTop,
      s ∉ {s : Path | ∃ n : ℕ,
        (∀ x, localTime coord n s x ≤ m) ∧
        (∃ x, localTime coord n s x = m) ∧
        (4 : ℕ∞) ≤ (favouriteSites coord n s).encard} :=
    MeasureTheory.ae_eventually_notMem h2
  have hcanon : ∀ᵐ s ∂srwMeasure,
      Filter.limsup (fun n => (favouriteSites coord n s).encard) Filter.atTop = 3 := by
    filter_upwards [h1, hbc, h3] with s hs_rec hs_bc hs_three
    refine limsup_eq_three_of_bounds ?_ ?_
    · rw [Filter.eventually_atTop] at hs_bc ⊢
      obtain ⟨M₀, hM₀⟩ := hs_bc
      obtain ⟨N₀, hN₀⟩ := hs_rec M₀
      refine ⟨N₀, fun n hn => ?_⟩
      obtain ⟨m, hm_le, hm_eq⟩ := exists_max_localTime coord n s
      have hm_ge : M₀ ≤ m := by
        calc M₀ ≤ localTime coord N₀ s (0, 0) := hN₀
          _ ≤ localTime coord n s (0, 0) := localTime_mono coord s (0, 0) hn
          _ ≤ m := hm_le (0, 0)
      have hnot4 : ¬ ((4 : ℕ∞) ≤ (favouriteSites coord n s).encard) := fun h4 =>
        hM₀ m hm_ge ⟨n, hm_le, hm_eq, h4⟩
      cases hval : (favouriteSites coord n s).encard with
      | top =>
        exfalso
        exact hnot4 (by simp [hval])
      | coe k =>
        rw [hval] at hnot4
        have hk : ¬ (4 ≤ k) := fun hk4 => hnot4 ((ENat.natCast_le_natCast (n := 4) (m := k)).mpr hk4)
        exact (ENat.natCast_le_natCast (n := k) (m := 3)).mpr (by omega)
    · rw [Filter.frequently_atTop]
      intro N
      obtain ⟨m, hm_ge, n, _, ⟨x, hx⟩, h3n⟩ := hs_three (N + 1)
      have hle : m ≤ n + 1 := hx ▸ localTime_le_succ coord n s x
      exact ⟨n, by omega, h3n⟩
  -- Step 2: Push forward `ℙ` along `Φ ω := fun k => X k ω` to `srwMeasure`
  let Φ : Ω → Path := fun ω k => X k ω
  have hΦ_meas : Measurable Φ := measurable_pi_lambda _ hX.measurable
  have hmap : Measure.map Φ (ℙ : Measure Ω) = srwMeasure := by
    rw [hX.indep.map_fun_eq_infinitePi_map hX.measurable]
    unfold srwMeasure
    congr 1
    ext k : 1
    exact hX.isUniform k
  rw [← hmap] at hcanon
  have hpull : ∀ᵐ ω ∂(ℙ : Measure Ω),
      Filter.limsup (fun n => (favouriteSites coord n (Φ ω)).encard) Filter.atTop = 3 :=
    (ae_map_iff hΦ_meas.aemeasurable measurableSet_limsup_eq_three).mp hcanon
  filter_upwards [hpull] with ω hω
  exact hω

end OMA.R_Erdos1165_erdos_1165_variants_hao_li_okada_zheng_R1
