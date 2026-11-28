import FormalConjectures.ErdosProblems.«165»

/-!
Reduction `Erdos165.erdos_165.variants.lower.R1` of the Hefty-Horn-King-Pfender [HHKP25]
lower bound `R(3, k) >= (1/2 - eps) k^2 / log k` (USD 250 Erdős prize problem #165).
Credit: @B221393 (incorporating the deterministic scale conversion noted by @PanPapag in desk notes).

- `H1`: Ramsey finiteness for `R(3, k)`: for every `k`, the guaranteeing vertex-count set
  for `K_3` vs `K_k` is nonempty.
- `H2`: Hefty-Horn-King-Pfender [HHKP25, Theorem 1.3] triangle-free graph existence:
  for every `delta > 0`, for all sufficiently large `n`, there exists a triangle-free graph
  on `Fin n` whose complement contains no `K_k` whenever `(1 + delta) * sqrt(n * log n) < k`.
- `main`: Unconditionally proves `witness_lt_classicalRamsey` (any triangle-free `G` on `Fin n`
  with no independent `k`-set satisfies `n < classicalRamsey 3 k` via `Fin.castLE` restriction)
  and executes the quantitative scale conversion from `n = ceil((1/2 - eps) k^2 / log k)` to
  `(1 + delta) sqrt(n log n) < k` for `delta = eps / 2`.
-/

namespace OMA.R_Erdos165_erdos_165_variants_lower_R1

open Filter SimpleGraph

/-- Ramsey finiteness for `R(3, k)`: for every `k`, there exists `n` such that every graph on
`Fin n` contains a triangle or its complement contains `K_k`. -/
def H1 : Prop :=
  ∀ k : ℕ, { n : ℕ | ∀ C : SimpleGraph (Fin n),
    (completeGraph (Fin 3)).IsContained C ∨ (completeGraph (Fin k)).IsContained Cᶜ }.Nonempty

/-- Hefty-Horn-King-Pfender [HHKP25, Theorem 1.3]: for every `delta > 0`, for all sufficiently
large `n`, there exists a triangle-free graph on `Fin n` whose complement avoids `K_k` for
every `k > (1 + delta) * sqrt(n * log n)`. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∃ G : SimpleGraph (Fin n),
      ¬ (completeGraph (Fin 3)).IsContained G ∧
      ∀ k : ℕ, (1 + δ) * Real.sqrt ((n : ℝ) * Real.log n) < (k : ℝ) →
        ¬ (completeGraph (Fin k)).IsContained Gᶜ

lemma witness_lt_classicalRamsey {n k : ℕ}
    (hne : { m : ℕ | ∀ C : SimpleGraph (Fin m),
      (completeGraph (Fin 3)).IsContained C ∨ (completeGraph (Fin k)).IsContained Cᶜ }.Nonempty)
    (G : SimpleGraph (Fin n))
    (h3 : ¬ (completeGraph (Fin 3)).IsContained G)
    (hk : ¬ (completeGraph (Fin k)).IsContained Gᶜ) :
    n < SimpleGraph.classicalRamsey 3 k := by
  by_contra hle
  push Not at hle
  have hmem := Nat.sInf_mem hne
  let N : ℕ := SimpleGraph.classicalRamsey 3 k
  let f : Fin N ↪ Fin n := Fin.castLEEmb hle
  let G' : SimpleGraph (Fin N) := G.comap f
  have hG' : (completeGraph (Fin 3)).IsContained G' ∨ (completeGraph (Fin k)).IsContained G'ᶜ :=
    hmem G'
  rcases hG' with ⟨⟨φ, hφ⟩⟩ | ⟨⟨φ, hφ⟩⟩
  · apply h3
    let e := (SimpleGraph.Hom.comap f G).comp φ
    exact ⟨⟨e, by rw [SimpleGraph.Hom.coe_comp]; exact Function.Injective.comp f.injective hφ⟩⟩
  · apply hk
    let e : completeGraph (Fin k) →g Gᶜ := ⟨f ∘ φ, by
      intro a b hab
      have h1 := φ.map_rel' hab
      simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at h1
      exact ⟨f.injective.ne h1.1, h1.2⟩⟩
    exact ⟨⟨e, by intro a b h; apply hφ; exact f.injective h⟩⟩

theorem main : H1 → H2 → type_of% @Erdos165.erdos_165.variants.lower := by
  intro h1 h2 ε hε
  by_cases hhalf : 1 / 2 ≤ ε
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
    have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hnum_nonpos : (1 / 2 - ε) * (k : ℝ) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    have hlhs_nonpos : (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum_nonpos (le_of_lt hlog_pos)
    exact le_trans hlhs_nonpos (Nat.cast_nonneg _)
  · push Not at hhalf
    let c : ℝ := 1 / 2 - ε
    have hc_pos : 0 < c := by dsimp only [c]; linarith
    let δ : ℝ := ε / 2
    have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
    have hcoeff_lt : (1 + δ) ^ 2 * (2 * c) < 1 := by
      have hdiff : 1 - (1 + δ) ^ 2 * (2 * c) = ε + 7 / 4 * ε ^ 2 + 1 / 2 * ε ^ 3 := by
        dsimp only [c, δ]
        ring
      have hpos : 0 < ε + 7 / 4 * ε ^ 2 + 1 / 2 * ε ^ 3 := by positivity
      linarith
    have hgap_pos : 0 < 1 - (1 + δ) ^ 2 * (2 * c) := by linarith
    rcases Filter.eventually_atTop.mp (h2 δ hδ_pos) with ⟨N₀, hN₀⟩
    have hev_N₀ : ∀ᶠ k : ℕ in atTop,
        (N₀ : ℝ) ≤ c * (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
      have h1' : Tendsto (fun k : ℕ => (k : ℝ) / Real.log (k : ℝ)) atTop atTop := by
        have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
        have hinv : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
          simpa using h
        have hpos_ev : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
          filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
          exact div_pos (Real.log_pos hx) (lt_trans zero_lt_one hx)
        have hrec : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop :=
          Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinv hpos_ev)
        have hcomp := hrec.comp tendsto_natCast_atTop_atTop
        refine hcomp.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k _
        simp [inv_div]
      have h2' : Tendsto (fun k : ℕ => c * ((k : ℝ) * ((k : ℝ) / Real.log (k : ℝ)))) atTop atTop := by
        have hmul := Filter.Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop h1'
        exact Filter.Tendsto.const_mul_atTop hc_pos hmul
      have h3' := Filter.tendsto_atTop.mp h2' (N₀ : ℝ)
      filter_upwards [h3'] with k hk
      have heq : c * ((k : ℝ) * ((k : ℝ) / Real.log (k : ℝ))) = c * (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
        ring
      rwa [heq] at hk
    have hev_log_small : ∀ᶠ k : ℕ in atTop,
        (1 + δ) ^ 2 * (2 * Real.log (k : ℝ)) < (1 - (1 + δ) ^ 2 * (2 * c)) * (k : ℝ) ^ 2 := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have hinv : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (nhds 0) := by
        have := h.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def] using this
      let η : ℝ := (1 - (1 + δ) ^ 2 * (2 * c)) / (2 * (1 + δ) ^ 2)
      have hη_pos : 0 < η := by positivity
      have hsmall := (Metric.tendsto_atTop.mp hinv) η hη_pos
      rcases hsmall with ⟨K₁, hK₁⟩
      filter_upwards [Filter.eventually_ge_atTop (max K₁ 3)] with k hk
      have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
      have hlog_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
      have hdist := hK₁ k (le_trans (le_max_left _ _) hk)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hlog_nn (le_of_lt hk_pos))] at hdist
      have hlt1 : Real.log (k : ℝ) < η * (k : ℝ) := (div_lt_iff₀ hk_pos).mp hdist
      have hk_le_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      have hlt2 : Real.log (k : ℝ) < η * (k : ℝ) ^ 2 :=
        lt_of_lt_of_le hlt1 (mul_le_mul_of_nonneg_left hk_le_sq (le_of_lt hη_pos))
      have hmul := mul_lt_mul_of_pos_left hlt2 (show 0 < 2 * (1 + δ) ^ 2 by positivity)
      have hsimp : 2 * (1 + δ) ^ 2 * (η * (k : ℝ) ^ 2) =
          (1 - (1 + δ) ^ 2 * (2 * c)) * (k : ℝ) ^ 2 := by
        dsimp only [η]
        field_simp
      linarith
    filter_upwards [hev_N₀, hev_log_small, Filter.eventually_ge_atTop (3 : ℕ)] with k hkN hklog hk3
    have hk_ge3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    have hlogk_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by
      have hexp : Real.exp 1 ≤ (k : ℝ) := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have hle := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at hle
    have hlogk_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le zero_lt_one hlogk_ge1
    let target : ℝ := c * (k : ℝ) ^ 2 / Real.log (k : ℝ)
    let n : ℕ := Nat.ceil target
    have htarget_nn : 0 ≤ target := by positivity
    have htarget_le_n : target ≤ (n : ℝ) := Nat.le_ceil target
    have hn_lt : (n : ℝ) < target + 1 := Nat.ceil_lt_add_one htarget_nn
    have hn_ge_N₀ : N₀ ≤ n := by exact_mod_cast le_trans hkN htarget_le_n
    have hn_le_ksq : (n : ℝ) ≤ (k : ℝ) ^ 2 := by
      have h1' : target ≤ c * (k : ℝ) ^ 2 :=
        div_le_self (by positivity) hlogk_ge1
      have h2' : c * (k : ℝ) ^ 2 + 1 ≤ (k : ℝ) ^ 2 := by
        dsimp only [c]
        nlinarith
      linarith
    have hlogn_le : Real.log (n : ℝ) ≤ 2 * Real.log (k : ℝ) := by
      by_cases hn0 : n = 0
      · rw [hn0, Nat.cast_zero, Real.log_zero]
        linarith
      · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have h1' := Real.log_le_log hn_pos hn_le_ksq
        rw [Real.log_pow] at h1'
        simpa using h1'
    have hprod_lt : (1 + δ) ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) < (k : ℝ) ^ 2 := by
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hstep1 : (n : ℝ) * Real.log (n : ℝ) ≤ (target + 1) * (2 * Real.log (k : ℝ)) := by
        have ha : (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) * (2 * Real.log (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogn_le hn_nn
        have hb : (n : ℝ) * (2 * Real.log (k : ℝ)) ≤ (target + 1) * (2 * Real.log (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hn_lt) (by linarith)
        exact le_trans ha hb
      have hexpand : (target + 1) * (2 * Real.log (k : ℝ)) =
          2 * c * (k : ℝ) ^ 2 + 2 * Real.log (k : ℝ) := by
        dsimp only [target]
        field_simp [ne_of_gt hlogk_pos]
      have hstep2 : (1 + δ) ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) ≤
          (1 + δ) ^ 2 * (2 * c * (k : ℝ) ^ 2 + 2 * Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (hexpand ▸ hstep1) (sq_nonneg _)
      linarith
    have hsqrt_lt : (1 + δ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) < (k : ℝ) := by
      by_contra hge
      push Not at hge
      have hsq : (k : ℝ) ^ 2 ≤ ((1 + δ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hge 2
      have hnlog_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
        by_cases hn0 : n = 0
        · simp [hn0]
        · exact mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn0))
      rw [mul_pow, Real.sq_sqrt hnlog_nn] at hsq
      linarith
    rcases hN₀ n hn_ge_N₀ with ⟨G, hG3, hGk⟩
    have hlt_R : n < SimpleGraph.classicalRamsey 3 k :=
      witness_lt_classicalRamsey (h1 k) G hG3 (hGk k hsqrt_lt)
    have hn_le_R : (n : ℝ) ≤ (SimpleGraph.classicalRamsey 3 k : ℝ) := by
      exact_mod_cast le_of_lt hlt_R
    exact le_trans htarget_le_n hn_le_R

end OMA.R_Erdos165_erdos_165_variants_lower_R1
