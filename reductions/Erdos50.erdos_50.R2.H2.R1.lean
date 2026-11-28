import OMAReductions.R_Erdos50_erdos_50_R2

/-!
# Reduction `Erdos50.erdos_50.R2.H2.R1` — Prime-cutoff sifting for rational non-totient-ratios

Splits hypothesis `H2` of `Erdos50.erdos_50.R2` (rational interior points `x ∈ (0, 1)` that
are not totient ratios `φ(d)/d`) around `x = 1 / 2 = φ(2) / 2` into two distinct arithmetic
regimes:

* `H1` (`x ∈ (0, 1 / 2)`): rational non-totient-ratios in the lower half, where even integers
  actively participate in `f(x + h) - f(x - h)` through the dilation `n ↦ 2n`.
* `H2` (`x ∈ (1 / 2, 1)`): rational non-totient-ratios in the upper half, **reduced completely
  to the sifted totient distribution** on integers coprime to the primorial
  `M = ∏_{p < 1/(1-x)} p` (which is divisible by `2` and by every prime with `(p - 1)/p < x`).

Inside this file we prove:
1. `coprime_density`: exact natural density `φ(M) / M` of `{n : ℕ | Nat.Coprime n M}` for any
   `M > 0`, and `1 - φ(M) / M` for `{n : ℕ | 0 < n ∧ ¬ Nat.Coprime n M}`.
2. `phi_div_le_of_prime_dvd`: if a prime `p` divides `n > 0`, then `φ(n) / n ≤ (p - 1) / p`.
3. `four_dvd_den_not_totient_ratio`: `2`-adic denominator obstruction showing that no rational
   `q` with `4 ∣ q.den` (such as `1/4, 3/4, 1/8, 3/8, ...`) is a totient ratio `φ(d)/d`.
4. Exact sifted density and derivative transfer `g(c) = f(c) - (1 - φ(M) / M)` on a neighborhood
   `[x - δ₀, x + δ₀]` for every non-totient-ratio `x ∈ (1 / 2, 1)`.
-/

-- Credit: @sanchan

namespace OMA.R_Erdos50_erdos_50_R2_H2_R1

open Filter Set Topology
open scoped BigOperators

/-- Lower half (`0 < x < 1/2`): rational interior non-totient-ratios, where even integers
contribute to the local increment of Schoenberg's distribution function `f`. -/
def H1 : Prop :=
  ∀ f : ℝ → ℝ, (∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) →
    ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → ¬ Irrational x →
      (∃ C > (0 : ℝ), ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ D : Finset ℕ,
        (∀ d ∈ D, 0 < d) → (∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d) →
        (∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1) →
        (∀ d ∈ D, |(d.totient : ℝ) / d - x| ≤ h) →
        (∑ d ∈ D, (d : ℝ)⁻¹) ≤ C * h * (1 + Real.log h⁻¹)) →
      ¬∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x

/-- Upper half (`1/2 < x < 1`): rational interior non-totient-ratios, sifted by the primorial
`M` of all primes `p` with `(p - 1)/p < x` (in particular `2 ∣ M`). On a neighborhood
`[x - δ₀, x + δ₀]`, the sifted distribution `g` on integers coprime to `M` cannot have a
positive derivative at `x`. -/
def H2 : Prop :=
  ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 1, (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → ¬ Irrational x →
    ∀ M : ℕ, 0 < M → 2 ∣ M →
      (∀ p : ℕ, p.Prime → ((p : ℝ) - 1) / p < x → p ∣ M) →
      ∀ δ₀ > (0 : ℝ), Set.Icc (x - δ₀) (x + δ₀) ⊆ Set.Ioo (0 : ℝ) 1 →
        ∀ g : ℝ → ℝ,
          (∀ c ∈ Set.Icc (x - δ₀) (x + δ₀),
            {n : ℕ | Nat.Coprime n M ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (g c)) →
          (∃ C > (0 : ℝ), ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ D : Finset ℕ,
            (∀ d ∈ D, 0 < d) → (∀ d ∈ D, Nat.Coprime d M) →
            (∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d) →
            (∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1) →
            (∀ d ∈ D, |(d.totient : ℝ) / d - x| ≤ h) →
            (∑ d ∈ D, (d : ℝ)⁻¹) ≤ C * h * (1 + Real.log h⁻¹)) →
          ¬∃ y > 0, HasDerivWithinAt g y (Set.Icc (x - δ₀) (x + δ₀)) x

/-- Partial density expressed as a `Finset.range` count divided by `b`. -/
theorem partialDensity_eq_card_div (A : Set ℕ) [DecidablePred (· ∈ A)] (b : ℕ) :
    A.partialDensity Set.univ b =
      (((Finset.range b).filter (fun n => n ∈ A)).card : ℝ) / b := by
  classical
  have hs : A ∩ Set.Iio b = ((Finset.range b).filter (fun n => n ∈ A) : Set ℕ) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hs,
    Set.ncard_coe_finset, Nat.ncard_Iio]

/-- Each full block `[k * M, (k + 1) * M)` contains exactly `φ(M)` integers coprime to `M`. -/
theorem coprime_count_block (M k : ℕ) :
    ((Finset.Ico (k * M) ((k + 1) * M)).filter (fun n => Nat.Coprime n M)).card = M.totient := by
  have hbij :
      ((Finset.Ico (k * M) ((k + 1) * M)).filter (fun n => Nat.Coprime n M)).card =
      ((Finset.range M).filter (fun r => Nat.Coprime r M)).card := by
    refine Finset.card_bij (fun n _ => n - k * M) ?_ ?_ ?_
    · intro n hn
      obtain ⟨hIco, hcop⟩ := Finset.mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hIco
      have hkm : (k + 1) * M = k * M + M := by ring
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have heq : n = (n - k * M) + k * M := (Nat.sub_add_cancel hlo).symm
      rw [heq] at hcop
      exact (Nat.coprime_add_mul_right_left (n - k * M) M k).mp hcop
    · intro n₁ hn₁ n₂ hn₂ hsub
      have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).1).1
      have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).1).1
      omega
    · intro r hr
      obtain ⟨hrM, hcop⟩ := Finset.mem_filter.mp hr
      have hrlt : r < M := Finset.mem_range.mp hrM
      have hkm : (k + 1) * M = k * M + M := by ring
      refine ⟨r + k * M, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
        (Nat.coprime_add_mul_right_left r M k).mpr hcop⟩, by omega⟩
  rw [hbij, Nat.totient]
  congr 1
  ext r
  simp [Nat.coprime_comm]

/-- On `[0, q * M)` there are exactly `q * φ(M)` integers coprime to `M`. -/
theorem coprime_count_mul (M q : ℕ) :
    ((Finset.range (q * M)).filter (fun n => Nat.Coprime n M)).card = q * M.totient := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Finset.range ((q + 1) * M) =
        Finset.range (q * M) ∪ Finset.Ico (q * M) ((q + 1) * M) := by
      have hqm : (q + 1) * M = q * M + M := by ring
      ext n
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range (q * M)) (Finset.Ico (q * M) ((q + 1) * M)) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      have := Finset.mem_range.mp h1
      have := (Finset.mem_Ico.mp h2).1
      omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      ih, coprime_count_block]
    ring

/-- The set of natural numbers coprime to `M > 0` has exact natural density `φ(M) / M`. -/
theorem coprime_density {M : ℕ} (hM : 0 < M) :
    {n : ℕ | Nat.Coprime n M}.HasDensity ((M.totient : ℝ) / M) := by
  classical
  unfold Set.HasDensity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hlo : Tendsto (fun b : ℕ => (M.totient : ℝ) / M - (M.totient : ℝ) / b) atTop
      (𝓝 ((M.totient : ℝ) / M)) := by
    have h0 : Tendsto (fun b : ℕ => (M.totient : ℝ) / b) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (M.totient : ℝ)
    simpa using tendsto_const_nhds.sub h0
  have hhi : Tendsto (fun b : ℕ => (M.totient : ℝ) / M + (M.totient : ℝ) / b) atTop
      (𝓝 ((M.totient : ℝ) / M)) := by
    have h0 : Tendsto (fun b : ℕ => (M.totient : ℝ) / b) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (M.totient : ℝ)
    simpa using tendsto_const_nhds.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
    rw [partialDensity_eq_card_div]
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    set q := b / M
    have hqm : q * M ≤ b := Nat.div_mul_le_self b M
    have hqhi : b < (q + 1) * M := by
      have h1 : q * M + b % M = b := by rw [mul_comm]; exact Nat.div_add_mod b M
      have h2 := Nat.mod_lt b hM
      have h3 : (q + 1) * M = q * M + M := by ring
      omega
    have hsub : (Finset.range (q * M)).filter (fun n => Nat.Coprime n M) ⊆
        (Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M}) := by
      intro n hn
      obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) hqm), hc⟩
    have hcard : (q * M.totient : ℕ) ≤
        ((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card := by
      rw [← coprime_count_mul M q]
      exact Finset.card_le_card hsub
    have hcardR : (q : ℝ) * M.totient ≤
        (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) := by
      exact_mod_cast hcard
    have hqR : ((b : ℝ) - M) / M ≤ q := by
      rw [div_le_iff₀ hMpos]
      have hqhiR : (b : ℝ) ≤ ((q : ℝ) + 1) * M := by exact_mod_cast hqhi.le
      linarith
    have hphi0 : (0 : ℝ) ≤ M.totient := Nat.cast_nonneg _
    have h1 : ((b : ℝ) - M) / M * M.totient ≤ (q : ℝ) * M.totient :=
      mul_le_mul_of_nonneg_right hqR hphi0
    have h2 : (M.totient : ℝ) / M - (M.totient : ℝ) / b =
        ((b : ℝ) - M) / M * M.totient / b := by
      field_simp
    rw [h2]
    exact div_le_div_of_nonneg_right (h1.trans hcardR) hbpos.le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
    rw [partialDensity_eq_card_div]
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    set q := b / M
    have hqm : q * M ≤ b := Nat.div_mul_le_self b M
    have hqhi : b ≤ (q + 1) * M := by
      have h1 : q * M + b % M = b := by rw [mul_comm]; exact Nat.div_add_mod b M
      have h2 := Nat.mod_lt b hM
      have h3 : (q + 1) * M = q * M + M := by ring
      omega
    have hsub : (Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M}) ⊆
        (Finset.range ((q + 1) * M)).filter (fun n => Nat.Coprime n M) := by
      intro n hn
      obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) hqhi), hc⟩
    have hcard : ((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card ≤
        (q + 1) * M.totient := by
      rw [← coprime_count_mul M (q + 1)]
      exact Finset.card_le_card hsub
    have hcardR : (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) ≤
        ((q : ℝ) + 1) * M.totient := by
      exact_mod_cast hcard
    have hqR : (q : ℝ) ≤ (b : ℝ) / M := by
      rw [le_div_iff₀ hMpos]
      exact_mod_cast hqm
    have hphi0 : (0 : ℝ) ≤ M.totient := Nat.cast_nonneg _
    have h1 : ((q : ℝ) + 1) * M.totient ≤ ((b : ℝ) / M + 1) * M.totient :=
      mul_le_mul_of_nonneg_right (by linarith) hphi0
    have h2 : (M.totient : ℝ) / M + (M.totient : ℝ) / b =
        ((b : ℝ) / M + 1) * M.totient / b := by
      field_simp
    rw [h2]
    exact div_le_div_of_nonneg_right (hcardR.trans h1) hbpos.le

/-- The set `{n : ℕ | 0 < n ∧ ¬ Nat.Coprime n M}` has exact natural density `1 - φ(M) / M`. -/
theorem not_coprime_pos_density {M : ℕ} (hM : 0 < M) :
    {n : ℕ | 0 < n ∧ ¬ Nat.Coprime n M}.HasDensity (1 - (M.totient : ℝ) / M) := by
  classical
  have hcop := coprime_density hM
  unfold Set.HasDensity at hcop ⊢
  have hdiff : Tendsto (fun b : ℕ => (1 : ℝ) - {n : ℕ | Nat.Coprime n M}.partialDensity Set.univ b)
      atTop (𝓝 (1 - (M.totient : ℝ) / M)) := tendsto_const_nhds.sub hcop
  have hlo : Tendsto (fun b : ℕ =>
      (1 : ℝ) - {n : ℕ | Nat.Coprime n M}.partialDensity Set.univ b - 1 / (b : ℝ))
      atTop (𝓝 (1 - (M.totient : ℝ) / M)) := by
    simpa using hdiff.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hdiff ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
    rw [partialDensity_eq_card_div, partialDensity_eq_card_div]
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hpart := Finset.card_filter_add_card_filter_not (s := Finset.range b)
      (p := fun n => Nat.Coprime n M)
    rw [Finset.card_range] at hpart
    have hsub : ((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)) ⊆
        insert 0 ((Finset.range b).filter (fun n => n ∈ {k : ℕ | 0 < k ∧ ¬ Nat.Coprime k M})) := by
      intro n hn
      obtain ⟨hr, hnc⟩ := Finset.mem_filter.mp hn
      by_cases hn0 : n = 0
      · subst hn0; exact Finset.mem_insert_self 0 _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hr, Nat.pos_of_ne_zero hn0, hnc⟩)
    have hcle : ((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)).card ≤
        ((Finset.range b).filter (fun n => n ∈ {k : ℕ | 0 < k ∧ ¬ Nat.Coprime k M})).card + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hcleR : (((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)).card : ℝ) ≤
        (((Finset.range b).filter (fun n => n ∈ {k : ℕ | 0 < k ∧ ¬ Nat.Coprime k M})).card : ℝ) + 1 := by
      exact_mod_cast hcle
    have hpartR : (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) +
        (((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)).card : ℝ) = b := by
      have : ((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})) =
          (Finset.range b).filter (fun n => Nat.Coprime n M) := rfl
      rw [this]
      exact_mod_cast hpart
    rw [le_div_iff₀ hbpos]
    have hbne : (b : ℝ) ≠ 0 := hbpos.ne'
    have hlhs : (1 - (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) / b -
        1 / b) * b =
        (b : ℝ) - (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) - 1 := by
      field_simp
    rw [hlhs]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
    rw [partialDensity_eq_card_div, partialDensity_eq_card_div]
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hpart := Finset.card_filter_add_card_filter_not (s := Finset.range b)
      (p := fun n => Nat.Coprime n M)
    rw [Finset.card_range] at hpart
    have hsub : (Finset.range b).filter (fun n => n ∈ {k : ℕ | 0 < k ∧ ¬ Nat.Coprime k M}) ⊆
        (Finset.range b).filter (fun n => ¬ Nat.Coprime n M) := by
      intro n hn
      obtain ⟨hr, _, hnc⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hr, hnc⟩
    have hcle : ((Finset.range b).filter (fun n => n ∈ {k : ℕ | 0 < k ∧ ¬ Nat.Coprime k M})).card ≤
        ((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)).card :=
      Finset.card_le_card hsub
    have hcleR : (((Finset.range b).filter (fun n => n ∈ {k : ℕ | 0 < k ∧ ¬ Nat.Coprime k M})).card : ℝ) ≤
        (((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)).card : ℝ) := by
      exact_mod_cast hcle
    have hpartR : (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) +
        (((Finset.range b).filter (fun n => ¬ Nat.Coprime n M)).card : ℝ) = b := by
      have : ((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})) =
          (Finset.range b).filter (fun n => Nat.Coprime n M) := rfl
      rw [this]
      exact_mod_cast hpart
    rw [div_le_iff₀ hbpos]
    have hbne : (b : ℝ) ≠ 0 := hbpos.ne'
    have hrhs : (1 - (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) / b) * b =
        (b : ℝ) - (((Finset.range b).filter (fun n => n ∈ {k : ℕ | Nat.Coprime k M})).card : ℝ) := by
      field_simp
    rw [hrhs]
    linarith

/-- Density of a set difference `B \ A` when `A ⊆ B`. -/
theorem hasDensity_sdiff {A B : Set ℕ} {a b : ℝ} (hs : A ⊆ B)
    (ha : A.HasDensity a) (hb : B.HasDensity b) : (B \ A).HasDensity (b - a) := by
  classical
  unfold Set.HasDensity at ha hb ⊢
  refine (hb.sub ha).congr fun N => ?_
  simp only [partialDensity_eq_card_div]
  have hsub : (Finset.range N).filter (fun n => n ∈ A) ⊆
      (Finset.range N).filter (fun n => n ∈ B) := by
    intro n hn
    obtain ⟨hN, hA⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hN, hs hA⟩
  have heq : (Finset.range N).filter (fun n => n ∈ B \ A) =
      ((Finset.range N).filter (fun n => n ∈ B)) \
        ((Finset.range N).filter (fun n => n ∈ A)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), sub_div]

/-- If a prime `p` divides `n > 0`, then `φ(n) / n ≤ (p - 1) / p`. -/
theorem phi_div_le_of_prime_dvd {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hdvd : p ∣ n) :
    (n.totient : ℝ) / n ≤ ((p : ℝ) - 1) / p := by
  have hprod : (n.totient : ℝ) = (n : ℝ) * ∏ q ∈ n.primeFactors, (1 - (q : ℝ)⁻¹) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hprod, mul_div_cancel_left₀ _ hn']
  have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn.ne'⟩
  rw [← Finset.mul_prod_erase _ _ hpmem]
  have h1sub : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [h1sub]
  have hle1 : ∏ q ∈ n.primeFactors.erase p, (1 - (q : ℝ)⁻¹) ≤ 1 := by
    refine Finset.prod_le_one (fun q _ => ?_) (fun q _ => ?_)
    · by_cases hq : q = 0
      · subst hq; simp
      · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero hq
        have : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
        linarith
    · have : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
      linarith
  have hnonneg : (0 : ℝ) ≤ ((p : ℝ) - 1) / p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    exact div_nonneg (by linarith) (by positivity)
  simpa using mul_le_mul_of_nonneg_left hle1 hnonneg

/-- `2`-adic denominator obstruction: no rational `q` with `4 ∣ q.den` is a totient ratio
`φ(d) / d` (covering `1/4, 3/4, 1/8, 3/8, 5/8, 7/8, ...`). -/
theorem four_dvd_den_not_totient_ratio (q : ℚ) (h4 : 4 ∣ q.den) :
    ¬ ∃ d : ℕ, 0 < d ∧ (q : ℝ) = (d.totient : ℝ) / d := by
  rintro ⟨d, hd, hqR⟩
  have hqQ : q = (d.totient : ℚ) / d := by
    apply Rat.cast_injective (α := ℝ)
    simpa using hqR
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcross : q.num * (d : ℤ) = (q.den : ℤ) * (d.totient : ℤ) := by
    have h1 : (q.num : ℚ) / q.den = (d.totient : ℚ) / d := by
      rw [Rat.num_div_den, hqQ]
    have hden0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have h2 := (div_eq_div_iff hden0 hdQ).mp h1
    have h3 : (q.num : ℚ) * (d : ℚ) = (q.den : ℚ) * (d.totient : ℚ) := by linarith
    exact_mod_cast h3
  set k := d.factorization 2
  set m := d / 2 ^ k
  have h2k_dvd : 2 ^ k ∣ d := Nat.ordProj_dvd d 2
  have hd_eq : 2 ^ k * m = d := Nat.mul_div_cancel' h2k_dvd
  have hm_odd : ¬ 2 ∣ m := by
    intro h2m
    have hpow : 2 ^ (k + 1) ∣ d := by
      rw [← hd_eq, pow_succ]
      obtain ⟨r, hr⟩ := h2m
      exact ⟨r, by rw [hr]; ring⟩
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hd.ne').mp hpow
    omega
  have hcop : Nat.Coprime (2 ^ k) m := by
    refine Nat.Coprime.pow_left k ?_
    exact Nat.prime_two.coprime_iff_not_dvd.mpr hm_odd
  have hphi_mul : d.totient = (2 ^ k).totient * m.totient := by
    rw [← hd_eq, Nat.totient_mul hcop]
  have h2_num : (2 : ℤ) ∣ q.num := by
    by_cases hk : k = 0
    · have hd_odd : ¬ 2 ∣ d := by
        have hdm : d = m := by simpa [hk] using hd_eq.symm
        rwa [hdm]
      obtain ⟨u, hu⟩ := h4
      have h2dvd : (2 : ℤ) ∣ q.num * (d : ℤ) := by
        rw [hcross, hu]
        exact ⟨2 * (u : ℤ) * (d.totient : ℤ), by push_cast; ring⟩
      rcases Int.prime_two.dvd_or_dvd h2dvd with h2n | h2d
      · exact h2n
      · exfalso
        exact hd_odd (Int.ofNat_dvd.mp h2d)
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hphi2 : (2 ^ k).totient = 2 ^ (k - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two hkpos]
        simp
      have hpow_eq : (2 : ℤ) ^ k = (2 : ℤ) ^ (k - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hkpos]
      have hcross2 : (2 : ℤ) ^ (k - 1) * (q.num * (2 * (m : ℤ))) =
          (2 : ℤ) ^ (k - 1) * ((q.den : ℤ) * (m.totient : ℤ)) := by
        have hdZ : (d : ℤ) = (2 : ℤ) ^ k * (m : ℤ) := by exact_mod_cast hd_eq.symm
        have hphiZ : (d.totient : ℤ) = (2 : ℤ) ^ (k - 1) * (m.totient : ℤ) := by
          rw [hphi_mul, hphi2]; push_cast; rfl
        rw [hdZ, hphiZ, hpow_eq] at hcross
        linarith
      have hcancel : q.num * (2 * (m : ℤ)) = (q.den : ℤ) * (m.totient : ℤ) :=
        mul_left_cancel₀ (by positivity : (2 : ℤ) ^ (k - 1) ≠ 0) hcross2
      obtain ⟨u, hu⟩ := h4
      have h2m : (2 : ℤ) * (q.num * (m : ℤ)) = (2 : ℤ) * (2 * (u : ℤ) * (m.totient : ℤ)) := by
        rw [hu] at hcancel
        push_cast at hcancel
        linarith
      have h2dvd : (2 : ℤ) ∣ q.num * (m : ℤ) := by
        have hq' := mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2m
        exact ⟨(u : ℤ) * (m.totient : ℤ), by linarith⟩
      rcases Int.prime_two.dvd_or_dvd h2dvd with h2n | h2m'
      · exact h2n
      · exfalso
        exact hm_odd (Int.ofNat_dvd.mp h2m')
  have h2numNat : 2 ∣ q.num.natAbs := Int.ofNat_dvd_left.mp h2_num
  have h2denNat : 2 ∣ q.den := dvd_trans (by norm_num : 2 ∣ 4) h4
  have h2gcd : 2 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h2numNat h2denNat
  rw [q.reduced] at h2gcd
  omega

theorem main : H1 → H2 → OMA.R_Erdos50_erdos_50_R2.H2 := by
  intro h1 h2 f hf x hx hratio hirr hpat hderiv
  have hne_half : x ≠ 1 / 2 := by
    intro hhalf
    apply hratio
    refine ⟨2, by norm_num, ?_⟩
    rw [hhalf]
    norm_num [Nat.totient_two]
  rcases lt_or_gt_of_ne hne_half with hlt | hgt
  · exact h1 f hf x ⟨hx.1, hlt⟩ hratio hirr hpat hderiv
  · classical
    let N : ℕ := ⌊1 / (1 - x)⌋₊ + 1
    let P : Finset ℕ := (Finset.range N).filter (fun p => p.Prime ∧ ((p : ℝ) - 1) / p < x)
    let M : ℕ := ∏ p ∈ P, p
    have h1mx : 0 < 1 - x := by linarith [hx.2]
    have hP_mem : ∀ p : ℕ, p.Prime → ((p : ℝ) - 1) / p < x → p ∈ P := by
      intro p hp hpx
      have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hplt : (p : ℝ) < 1 / (1 - x) := by
        rw [div_lt_iff₀ hppos] at hpx
        rw [lt_div_iff₀ h1mx]
        nlinarith
      have hple : p ≤ ⌊1 / (1 - x)⌋₊ := Nat.le_floor hplt.le
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hpx⟩
    have h2P : 2 ∈ P := hP_mem 2 Nat.prime_two (by norm_num; linarith)
    have hMpos : 0 < M := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.1.pos
    have h2M : 2 ∣ M := Finset.dvd_prod_of_mem _ h2P
    have hallM : ∀ p : ℕ, p.Prime → ((p : ℝ) - 1) / p < x → p ∣ M :=
      fun p hp hpx => Finset.dvd_prod_of_mem _ (hP_mem p hp hpx)
    have hgap_ex : ∃ δ₁ > (0 : ℝ), ∀ p ∈ P, ((p : ℝ) - 1) / p < x - δ₁ := by
      have hPne : P.Nonempty := ⟨2, h2P⟩
      obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image P (fun p => x - ((p : ℝ) - 1) / p) hPne
      have hm_pos : 0 < x - ((p₀ : ℝ) - 1) / p₀ := by
        have hpx := (Finset.mem_filter.mp hp₀).2.2
        linarith
      refine ⟨(x - ((p₀ : ℝ) - 1) / p₀) / 2, by linarith, fun p hp => ?_⟩
      have hle := hmin p hp
      linarith
    obtain ⟨δ₁, hδ₁, hPgap⟩ := hgap_ex
    set δ₀ : ℝ := min (min (x / 2) ((1 - x) / 2)) δ₁
    have hδ₀ : 0 < δ₀ := lt_min (lt_min (by linarith [hx.1]) (by linarith [hx.2])) hδ₁
    have hIcc_sub : Set.Icc (x - δ₀) (x + δ₀) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro c ⟨hc1, hc2⟩
      have hd1 : δ₀ ≤ x / 2 := (min_le_left _ _).trans (min_le_left _ _)
      have hd2 : δ₀ ≤ (1 - x) / 2 := (min_le_left _ _).trans (min_le_right _ _)
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hδ₀_le : δ₀ ≤ δ₁ := min_le_right _ _
    let g : ℝ → ℝ := fun c => f c - (1 - (M.totient : ℝ) / M)
    have hg_dens : ∀ c ∈ Set.Icc (x - δ₀) (x + δ₀),
        {n : ℕ | Nat.Coprime n M ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (g c) := by
      intro c hc
      have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hIcc_sub hc)
      have hsub : {n : ℕ | 0 < n ∧ ¬ Nat.Coprime n M} ⊆ {n : ℕ | (Nat.totient n : ℝ) < c * n} := by
        intro n ⟨hnpos, hncop⟩
        have hgcd : 1 < Nat.gcd n M := by
          have hne1 : Nat.gcd n M ≠ 1 := hncop
          have hpos : 0 < Nat.gcd n M := Nat.gcd_pos_of_pos_left M hnpos
          omega
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd.ne'
        have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_left n M)
        have hpM : p ∣ M := hpdvd.trans (Nat.gcd_dvd_right n M)
        have hpP : p ∈ P := by
          have := (hp.prime.dvd_finset_prod_iff id).mp hpM
          obtain ⟨q, hqP, hpq⟩ := this
          have hqprime := (Finset.mem_filter.mp hqP).2.1
          have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
          exact heq ▸ hqP
        have hle := phi_div_le_of_prime_dvd hnpos hp hpn
        have hlt1 : ((p : ℝ) - 1) / p < x - δ₁ := hPgap p hpP
        have hlt2 : (n.totient : ℝ) / n < c := lt_of_le_of_lt hle (lt_of_lt_of_le hlt1 (by linarith [hc.1]))
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        exact (div_lt_iff₀ hnR).mp hlt2
      have hset : {n : ℕ | Nat.Coprime n M ∧ (Nat.totient n : ℝ) < c * n} =
          {n : ℕ | (Nat.totient n : ℝ) < c * n} \ {n : ℕ | 0 < n ∧ ¬ Nat.Coprime n M} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_diff]
        constructor
        · rintro ⟨hcop, hlt⟩
          exact ⟨hlt, fun h => h.2 hcop⟩
        · rintro ⟨hlt, hnot⟩
          have hnpos : 0 < n := by
            by_contra h0
            have hn0 : n = 0 := by omega
            subst hn0
            simp at hlt
          exact ⟨by by_contra hnc; exact hnot ⟨hnpos, hnc⟩, hlt⟩
      rw [hset]
      exact hasDensity_sdiff hsub (not_coprime_pos_density hMpos) (hf c hc01)
    have hg_pat : ∃ C > (0 : ℝ), ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ D : Finset ℕ,
        (∀ d ∈ D, 0 < d) → (∀ d ∈ D, Nat.Coprime d M) →
        (∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d) →
        (∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1) →
        (∀ d ∈ D, |(d.totient : ℝ) / d - x| ≤ h) →
        (∑ d ∈ D, (d : ℝ)⁻¹) ≤ C * h * (1 + Real.log h⁻¹) := by
      obtain ⟨C, hC, δ, hδ, hbound⟩ := hpat
      exact ⟨C, hC, δ, hδ, fun h hh hhδ D hDpos _ hDsq hDp hDgap =>
        hbound h hh hhδ D hDpos hDsq hDp hDgap⟩
    obtain ⟨y, hy, hfy⟩ := hderiv
    have hgy : HasDerivWithinAt g y (Set.Icc (x - δ₀) (x + δ₀)) x := by
      have h1 : HasDerivWithinAt g y (Set.Icc 0 1) x := hfy.sub_const _
      exact h1.mono (hIcc_sub.trans Ioo_subset_Icc_self)
    exact h2 x ⟨hgt, hx.2⟩ hratio hirr M hMpos h2M hallM δ₀ hδ₀ hIcc_sub g hg_dens hg_pat ⟨y, hy, hgy⟩

end OMA.R_Erdos50_erdos_50_R2_H2_R1
