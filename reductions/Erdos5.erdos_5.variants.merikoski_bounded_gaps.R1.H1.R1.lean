import OMAReductions.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

-- Reduction Erdos5.erdos_5.variants.merikoski_bounded_gaps.R1.H1.R1 of step Erdos5.erdos_5.variants.merikoski_bounded_gaps.R1.H1
-- Credit: @KevinBigham

/-!
# Reduction of Banks–Freiberg–Maynard (2016) limit points of normalized prime gaps

Following Banks, Freiberg, and Maynard (*On limit points of the sequence of normalized prime gaps*,
Proc. Lond. Math. Soc. 2016), we reduce `Erdos5.erdos_5.variants.merikoski_bounded_gaps.R1.H1` to
two independent hypotheses:
- `H1`: Uniform Maynard–Tao bounded prime gaps in admissible `k`-tuples along residue classes
  modulo a squarefree `W ≤ X^(1/100)` avoiding at most one exceptional prime `p₀`.
- `H2`: Elementary Erdős–Rankin / Westzynthius residue covering with `k` prescribed approximate
  holes near `β_i * log X` (avoiding any single prime `p₀`).
-/

namespace OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1_H1_R1

/-- Uniform Maynard–Tao theorem for admissible `k`-tuples in residue classes modulo a squarefree
`W ≤ X^(1/100)` avoiding at most one exceptional prime `p₀`. -/
def H1 : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ ∀ᶠ X : ℕ in Filter.atTop, ∃ p₀ : ℕ,
    ∀ (W b : ℕ) (h : Fin k → ℕ),
      1 ≤ W → Squarefree W → (W : ℝ) ≤ (X : ℝ) ^ (1 / 100 : ℝ) →
      (p₀.Prime → ¬ p₀ ∣ W) →
      StrictMono h → (∀ i, (h i : ℝ) ≤ (X : ℝ) ^ (1 / 100 : ℝ)) →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ i : Fin k, h i % p ≠ r % p) →
      (∀ i : Fin k, Nat.Coprime (b + h i) W) →
      ∃ n : ℕ, X ≤ n ∧ n ≤ 2 * X ∧ n % W = b % W ∧
        2 ≤ (Finset.univ.filter (fun i : Fin k => (n + h i).Prime)).card

/-- Elementary Erdős–Rankin / Westzynthius covering of `[h 0, h (k - 1)] \ {h 0, ..., h (k - 1)}`
by primes dividing a squarefree `W ≤ X^(1/100)` avoiding any single prime `p₀`, with `h i`
approximating `β i * log X`. -/
def H2 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (β : Fin k → ℝ), (∀ i, 0 ≤ β i) → StrictMono β →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, ∀ p₀ : ℕ,
      ∃ (W b : ℕ) (h : Fin k → ℕ),
        1 ≤ W ∧ Squarefree W ∧ (W : ℝ) ≤ (X : ℝ) ^ (1 / 100 : ℝ) ∧
        (p₀.Prime → ¬ p₀ ∣ W) ∧
        StrictMono h ∧ (∀ i, (h i : ℝ) ≤ (X : ℝ) ^ (1 / 100 : ℝ)) ∧
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ i : Fin k, h i % p ≠ r % p) ∧
        (∀ i : Fin k, Nat.Coprime (b + h i) W) ∧
        (∀ i : Fin k, |(h i : ℝ) - β i * Real.log (X : ℝ)| ≤ ε * Real.log (X : ℝ)) ∧
        (∀ i j : Fin k, ∀ t : ℕ, h i ≤ t → t ≤ h j →
          (∀ r : Fin k, t ≠ h r) → ∃ p : ℕ, p.Prime ∧ p ∣ W ∧ p ∣ b + t)

section Helpers

open Filter Real Erdos5
open scoped Topology Classical

private lemma consecutive_primes_nth {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hno : ∀ u : ℕ, p < u → u < q → ¬ u.Prime) :
    let idx := Nat.count Nat.Prime p
    Nat.nth Nat.Prime idx = p ∧ Nat.nth Nat.Prime (idx + 1) = q ∧ primeGap idx = q - p := by
  dsimp only
  set idx := Nat.count Nat.Prime p
  have hnth_p : Nat.nth Nat.Prime idx = p := Nat.nth_count hp
  have hnth_gt : p < Nat.nth Nat.Prime (idx + 1) := by
    rw [← hnth_p]
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self idx)
  have hnth_prime : (Nat.nth Nat.Prime (idx + 1)).Prime := Nat.prime_nth_prime (idx + 1)
  have hcnt_lt : idx < Nat.count Nat.Prime q := by
    dsimp only [idx]
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset_filter _ (Finset.range_mono hpq.le), fun heq => ?_⟩
    have hp_in : p ∈ (Finset.range q).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpq, hp⟩
    rw [← heq] at hp_in
    exact (lt_irrefl p) (Finset.mem_range.mp (Finset.mem_filter.mp hp_in).1)
  have hnth_le : Nat.nth Nat.Prime (idx + 1) ≤ q := by
    have h1 : idx + 1 ≤ Nat.count Nat.Prime q := hcnt_lt
    have h2 : Nat.nth Nat.Prime (idx + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone h1
    rwa [Nat.nth_count hq] at h2
  have hnth_q : Nat.nth Nat.Prime (idx + 1) = q := by
    by_contra hne
    exact hno (Nat.nth Nat.Prime (idx + 1)) hnth_gt (lt_of_le_of_ne hnth_le hne) hnth_prime
  refine ⟨hnth_p, hnth_q, ?_⟩
  rw [primeGap, hnth_p, hnth_q]

private lemma exists_consecutive_prime_indices {k : ℕ} {h : Fin k → ℕ} {n : ℕ}
    (hcard : 2 ≤ (Finset.univ.filter (fun i : Fin k => (n + h i).Prime)).card) :
    ∃ i j : Fin k, i < j ∧ (n + h i).Prime ∧ (n + h j).Prime ∧
      ∀ r : Fin k, i < r → r < j → ¬ (n + h r).Prime := by
  set S := Finset.univ.filter (fun i : Fin k => (n + h i).Prime)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  set i := S.min' hSne
  have hiS : i ∈ S := Finset.min'_mem S hSne
  have hiP : (n + h i).Prime := (Finset.mem_filter.mp hiS).2
  set S' := S.erase i
  have hS'card : S'.card = S.card - 1 := Finset.card_erase_of_mem hiS
  have hS'ne : S'.Nonempty := Finset.card_pos.mp (by omega)
  set j := S'.min' hS'ne
  have hjS' : j ∈ S' := Finset.min'_mem S' hS'ne
  have hjS : j ∈ S := Finset.mem_of_mem_erase hjS'
  have hji : j ≠ i := Finset.ne_of_mem_erase hjS'
  have hjP : (n + h j).Prime := (Finset.mem_filter.mp hjS).2
  have hij : i < j := lt_of_le_of_ne (Finset.min'_le S j hjS) hji.symm
  refine ⟨i, j, hij, hiP, hjP, fun r hir hrj hrP => ?_⟩
  have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hrP⟩
  have hrS' : r ∈ S' := Finset.mem_erase.mpr ⟨ne_of_gt hir, hrS⟩
  exact (not_le_of_gt hrj) (Finset.min'_le S' r hrS')

private lemma rpow_one_hundredth_lt_self {X : ℕ} (hX : 2 ≤ X) :
    (X : ℝ) ^ (1 / 100 : ℝ) < (X : ℝ) := by
  have hX1 : (1 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  calc (X : ℝ) ^ (1 / 100 : ℝ) < (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
    _ = (X : ℝ) := Real.rpow_one (X : ℝ)

private lemma log_ratio_close {X n hi hj : ℕ} {βi βj ε : ℝ}
    (hX : 16 ≤ X) (hβ_nn : 0 ≤ βj - βi) (hε : 0 < ε)
    (hn_lo : X ≤ n) (hn_hi : n ≤ 2 * X) (hhi_le : (hi : ℝ) ≤ (X : ℝ))
    (hdiff : |((hj - hi : ℕ) : ℝ) - (βj - βi) * Real.log (X : ℝ)| ≤ (ε / 2) * Real.log (X : ℝ))
    (hlogX : 4 * (βj - βi + 1) * Real.log 3 / ε ≤ Real.log (X : ℝ)) :
    |((hj - hi : ℕ) : ℝ) / Real.log ((n + hi : ℕ) : ℝ) - (βj - βi)| ≤ ε := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hnhi_lo : (X : ℝ) ≤ ((n + hi : ℕ) : ℝ) := by
    have : X ≤ n + hi := by omega
    exact_mod_cast this
  have hnhi_hi : ((n + hi : ℕ) : ℝ) ≤ 3 * (X : ℝ) := by
    have hn_r : (n : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hn_hi
    push_cast
    linarith
  have hlog_lo : Real.log (X : ℝ) ≤ Real.log ((n + hi : ℕ) : ℝ) :=
    Real.log_le_log hXpos hnhi_lo
  have hlog_hi : Real.log ((n + hi : ℕ) : ℝ) ≤ Real.log (X : ℝ) + Real.log 3 := by
    calc Real.log ((n + hi : ℕ) : ℝ) ≤ Real.log (3 * (X : ℝ)) :=
          Real.log_le_log (lt_of_lt_of_le hXpos hnhi_lo) hnhi_hi
      _ = Real.log 3 + Real.log (X : ℝ) := Real.log_mul (by norm_num) hXpos.ne'
      _ = Real.log (X : ℝ) + Real.log 3 := add_comm _ _
  have hlog_nhi_pos : 0 < Real.log ((n + hi : ℕ) : ℝ) := lt_of_lt_of_le hlogX_pos hlog_lo
  set L := Real.log (X : ℝ)
  set L' := Real.log ((n + hi : ℕ) : ℝ)
  set D := ((hj - hi : ℕ) : ℝ)
  set Δ := βj - βi
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hsplit : D / L' - Δ = (D - Δ * L) / L' - Δ * (L' - L) / L' := by
    field_simp
    ring
  rw [hsplit]
  have h1 : |(D - Δ * L) / L'| ≤ ε / 2 := by
    rw [abs_div, abs_of_pos hlog_nhi_pos, div_le_iff₀ hlog_nhi_pos]
    calc |D - Δ * L| ≤ (ε / 2) * L := hdiff
      _ ≤ (ε / 2) * L' := by nlinarith
  have h2 : |Δ * (L' - L) / L'| ≤ ε / 2 := by
    have hL'sub : 0 ≤ L' - L := by linarith
    have hL'sub_le : L' - L ≤ Real.log 3 := by linarith
    have hnn : 0 ≤ Δ * (L' - L) / L' := by positivity
    rw [abs_of_nonneg hnn, div_le_iff₀ hlog_nhi_pos]
    have hεL : 4 * (Δ + 1) * Real.log 3 ≤ ε * L := by
      have := (div_le_iff₀ hε).mp hlogX
      linarith
    have hΔ_le : Δ * (L' - L) ≤ (Δ + 1) * Real.log 3 := by nlinarith
    nlinarith
  calc |(D - Δ * L) / L' - Δ * (L' - L) / L'|
      ≤ |(D - Δ * L) / L'| + |Δ * (L' - L) / L'| := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

end Helpers

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1.H1 := by
  classical
  intro hMT hER
  obtain ⟨k, hk2, hMT_ev⟩ := hMT
  refine ⟨k - 1, ?_⟩
  have hk_eq : k - 1 + 1 = k := by omega
  intro β hβ_nn hβ_mono
  -- Transport β from Fin (k - 1 + 1) to Fin k via Fin.cast
  let eFin : Fin (k - 1 + 1) ≃o Fin k := Fin.castOrderIso hk_eq
  let β' : Fin k → ℝ := fun i => β (eFin.symm i)
  have hβ'_nn : ∀ i, 0 ≤ β' i := fun i => hβ_nn (eFin.symm i)
  have hβ'_mono : StrictMono β' := fun i j hij => hβ_mono (eFin.symm.strictMono hij)
  -- For every s : ℕ and lower bound M : ℕ, find (i, j, idx) with idx > M and error ≤ 1/(s+1)
  have hstep : ∀ (s M : ℕ), ∃ (i j : Fin k) (idx : ℕ),
      i < j ∧ M < idx ∧
      |(primeGap idx : ℝ) / Real.log (Nat.nth Nat.Prime idx) - (β' j - β' i)| ≤
        1 / ((s + 1 : ℕ) : ℝ) := by
    intro s M
    set ε : ℝ := 1 / ((s + 1 : ℕ) : ℝ)
    have hε_pos : 0 < ε := by positivity
    have hER_ev := hER k hk2 β' hβ'_nn hβ'_mono (ε / 4) (by positivity)
    set Bmax : ℝ := β' ⟨k - 1, by omega⟩ + 1
    have hBmax_pos : 0 < Bmax := by
      have := hβ'_nn ⟨k - 1, by omega⟩; linarith
    have hlog_ev : ∀ᶠ X : ℕ in Filter.atTop,
        4 * Bmax * Real.log 3 / ε ≤ Real.log (X : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop _)
    have hbig_ev : ∀ᶠ X : ℕ in Filter.atTop,
        max 16 (Nat.nth Nat.Prime M + 1) ≤ X :=
      Filter.eventually_ge_atTop _
    have hall := (hMT_ev.and (hER_ev.and (hlog_ev.and hbig_ev))).exists
    obtain ⟨X, hMT_X, hER_X, hlog_X, hbig_X⟩ := hall
    obtain ⟨p₀, hp₀⟩ := hMT_X
    obtain ⟨W, b, h, hW1, hWsq, hW_le, hp₀_ndvd, hh_mono, hh_le, hh_adm, hh_cop, hh_approx, hcov⟩ :=
      hER_X p₀
    obtain ⟨n, hn_lo, hn_hi, hn_mod, hprimes⟩ :=
      hp₀ W b h hW1 hWsq hW_le hp₀_ndvd hh_mono hh_le hh_adm hh_cop
    obtain ⟨i, j, hij, hiP, hjP, hno_mid⟩ := exists_consecutive_prime_indices hprimes
    have hX16 : 16 ≤ X := le_trans (le_max_left _ _) hbig_X
    have hX_gt_pM : Nat.nth Nat.Prime M < X := by
      have := le_trans (le_max_right _ _) hbig_X; omega
    have hW_lt_X : W < X := by
      have h1 : (W : ℝ) < (X : ℝ) := hW_le.trans_lt (rpow_one_hundredth_lt_self (by omega))
      exact_mod_cast h1
    have hhi_lt_hj : h i < h j := hh_mono hij
    -- No prime strictly between n + h i and n + h j
    have hno_prime : ∀ u : ℕ, n + h i < u → u < n + h j → ¬ u.Prime := by
      intro u hu1 hu2 huP
      set t := u - n
      have hu_eq : u = n + t := by omega
      by_cases hex : ∃ r : Fin k, t = h r
      · obtain ⟨r, hr⟩ := hex
        have hir : i < r := by
          by_contra hle; push Not at hle
          have := hh_mono.monotone hle; omega
        have hrj : r < j := by
          by_contra hle; push Not at hle
          have := hh_mono.monotone hle; omega
        exact hno_mid r hir hrj (by rwa [← hr, ← hu_eq])
      · push Not at hex
        obtain ⟨p, hpP, hpW, hpbt⟩ := hcov i j t (by omega) (by omega) hex
        have hpu : p ∣ u := by
          rw [hu_eq]
          have h1 : (n + t) % W = (b + t) % W := by
            rw [Nat.add_mod, hn_mod, ← Nat.add_mod]
          have h2 : p ∣ (n + t) % W := by
            rw [h1]
            exact Nat.dvd_mod_iff hpW |>.mpr hpbt
          exact (Nat.dvd_mod_iff hpW).mp h2
        have hp_le_W : p ≤ W := Nat.le_of_dvd (by omega) hpW
        have hp_lt_u : p < u := by omega
        rcases (Nat.dvd_prime huP).mp hpu with hp1 | hpeq
        · exact hpP.ne_one hp1
        · omega
    obtain ⟨hnth_p, _, hgap⟩ := consecutive_primes_nth hiP hjP (by omega) hno_prime
    set idx := Nat.count Nat.Prime (n + h i)
    have hM_lt_idx : M < idx := by
      by_contra hle; push Not at hle
      have h1 : Nat.nth Nat.Prime idx ≤ Nat.nth Nat.Prime M :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hle
      rw [hnth_p] at h1
      omega
    have hdiff_approx : |((h j - h i : ℕ) : ℝ) - (β' j - β' i) * Real.log (X : ℝ)| ≤
        (ε / 2) * Real.log (X : ℝ) := by
      have hsub_cast : ((h j - h i : ℕ) : ℝ) = (h j : ℝ) - (h i : ℝ) :=
        Nat.cast_sub hhi_lt_hj.le
      rw [hsub_cast]
      have hrew : (h j : ℝ) - (h i : ℝ) - (β' j - β' i) * Real.log (X : ℝ) =
          ((h j : ℝ) - β' j * Real.log (X : ℝ)) - ((h i : ℝ) - β' i * Real.log (X : ℝ)) := by ring
      rw [hrew]
      calc |((h j : ℝ) - β' j * Real.log (X : ℝ)) - ((h i : ℝ) - β' i * Real.log (X : ℝ))|
          ≤ |(h j : ℝ) - β' j * Real.log (X : ℝ)| + |(h i : ℝ) - β' i * Real.log (X : ℝ)| :=
            abs_sub _ _
        _ ≤ (ε / 4) * Real.log (X : ℝ) + (ε / 4) * Real.log (X : ℝ) :=
            add_le_add (hh_approx j) (hh_approx i)
        _ = (ε / 2) * Real.log (X : ℝ) := by ring
    have hΔ_le : β' j - β' i + 1 ≤ Bmax := by
      have h1 : β' j ≤ β' ⟨k - 1, by omega⟩ :=
        hβ'_mono.monotone (Nat.le_sub_one_of_lt j.2)
      have h2 : 0 ≤ β' i := hβ'_nn i
      dsimp only [Bmax]; linarith
    have hlog_bound : 4 * (β' j - β' i + 1) * Real.log 3 / ε ≤ Real.log (X : ℝ) := by
      have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have h1 : 4 * (β' j - β' i + 1) * Real.log 3 / ε ≤ 4 * Bmax * Real.log 3 / ε := by
        gcongr
      exact h1.trans hlog_X
    have hclose := log_ratio_close hX16 (sub_nonneg.mpr (hβ'_mono hij).le) hε_pos
      hn_lo hn_hi ((hh_le i).trans (rpow_one_hundredth_lt_self (by omega)).le)
      hdiff_approx hlog_bound
    have hgap_eq : primeGap idx = h j - h i := by
      rw [hgap]; omega
    refine ⟨i, j, idx, hij, hM_lt_idx, ?_⟩
    rw [hgap_eq, hnth_p]
    exact hclose
  -- Build a strictly increasing sequence of indices with vanishing error
  choose fi fj fidx hfij hfM hferr using hstep
  let seq : ℕ → ℕ := Nat.rec (fidx 0 0) (fun s prev => fidx (s + 1) prev)
  have hseq_strict : StrictMono seq := strictMono_nat_of_lt_succ fun s => hfM (s + 1) (seq s)
  let pairAt : ℕ → Fin k × Fin k := fun s =>
    match s with
    | 0 => (fi 0 0, fj 0 0)
    | s + 1 => (fi (s + 1) (seq s), fj (s + 1) (seq s))
  have hpair_lt : ∀ s : ℕ, (pairAt s).1 < (pairAt s).2 := by
    intro s; cases s with
    | zero => exact hfij 0 0
    | succ s => exact hfij (s + 1) (seq s)
  have hpair_err : ∀ s : ℕ,
      |(primeGap (seq s) : ℝ) / Real.log (Nat.nth Nat.Prime (seq s)) -
          (β' (pairAt s).2 - β' (pairAt s).1)| ≤ 1 / ((s + 1 : ℕ) : ℝ) := by
    intro s; cases s with
    | zero => exact hferr 0 0
    | succ s => exact hferr (s + 1) (seq s)
  -- Infinite pigeonhole on Fin k × Fin k
  obtain ⟨⟨i0, j0⟩, hinf⟩ := Finite.exists_infinite_fiber pairAt
  have hset_inf : {s : ℕ | pairAt s = (i0, j0)}.Infinite := Set.infinite_coe_iff.mp hinf
  let sub : ℕ → ℕ := Nat.nth (fun s => pairAt s = (i0, j0))
  have hsub_mono : StrictMono sub := Nat.nth_strictMono hset_inf
  have hsub_mem : ∀ r : ℕ, pairAt (sub r) = (i0, j0) := fun r => Nat.nth_mem_of_infinite hset_inf r
  have hij0 : i0 < j0 := by
    have h0 := hpair_lt (sub 0)
    rw [hsub_mem 0] at h0
    exact h0
  refine ⟨eFin.symm i0, eFin.symm j0, eFin.symm.strictMono hij0, fun r => seq (sub r),
    hseq_strict.comp hsub_mono, ?_⟩
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨R, hR⟩ := exists_nat_one_div_lt hδ
  refine ⟨R, fun r hr => ?_⟩
  rw [Real.dist_eq]
  have herr := hpair_err (sub r)
  rw [hsub_mem r] at herr
  have hr_le : r ≤ sub r := hsub_mono.id_le r
  have hR_le : (R + 1 : ℝ) ≤ ((sub r + 1 : ℕ) : ℝ) := by
    push_cast
    have : R ≤ sub r := hr.trans hr_le
    exact_mod_cast (by omega : R + 1 ≤ sub r + 1)
  have hinv_le : 1 / ((sub r + 1 : ℕ) : ℝ) ≤ 1 / ((R : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hR_le
  exact (herr.trans hinv_le).trans_lt hR

end OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1_H1_R1
