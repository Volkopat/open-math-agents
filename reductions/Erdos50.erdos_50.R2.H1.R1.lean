import OMAReductions.R_Erdos50_erdos_50_R2

/-!
# Reduction `Erdos50.erdos_50.R2.H1.R1` — Exact 2-adic functional equation & primorial sifting for irrational points

Splits hypothesis `H1` of `Erdos50.erdos_50.R2` (irrational interior points `x ∈ (0, 1)`) at
`x = 1 / 2` (impossible for irrational `x`) into two strictly strengthened regimes:

* `H1` (`x ∈ (0, 1 / 2)`): irrational interior points in the lower half, equipped with the
  **exact global 2-adic odd-integer totient distribution** `g2 : ℝ → ℝ` proved unconditionally:
  - `g2 c` is the natural density of `{n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}` for all `c ∈ (0, 1]`;
  - `g2 c = f c - 1 / 2` for all `c ∈ (1 / 2, 1]`;
  - `f c = g2 c + g2 (2 * c)` for all `c ∈ (0, 1 / 2]` (exact 2-adic functional equation);
  - `g2` is monotone non-decreasing on `(0, 1]`.
* `H2` (`x ∈ (1 / 2, 1)`): irrational interior points in the upper half, **reduced completely
  to the sifted totient distribution** `g c = f c - (1 - φ(M) / M)` on integers coprime to the
  primorial `M = ∏_{p < 1/(1-x)} p` (`2 ∣ M`), transferring both the logarithmic ratio divergence
  and the local pattern weight bound to integers coprime to `M`.
-/

-- Credit: @sanchan

namespace OMA.R_Erdos50_erdos_50_R2_H1_R1

open Filter Set Topology
open scoped BigOperators

/-- Lower half (`0 < x < 1/2`): irrational interior points equipped with the global 2-adic
odd-integer totient distribution `g2` satisfying `g2 c = f c - 1/2` on `(1/2, 1]`,
`f c = g2 c + g2 (2 * c)` on `(0, 1/2]`, and monotonicity on `(0, 1]`. -/
def H1 : Prop :=
  ∀ f : ℝ → ℝ, (∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) →
    ∀ g2 : ℝ → ℝ,
      (∀ c ∈ Set.Ioc (0 : ℝ) 1, {n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (g2 c)) →
      (∀ c ∈ Set.Ioc (1 / 2 : ℝ) 1, g2 c = f c - 1 / 2) →
      (∀ c ∈ Set.Ioc (0 : ℝ) (1 / 2), f c = g2 c + g2 (2 * c)) →
      MonotoneOn g2 (Set.Ioc (0 : ℝ) 1) →
      ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → Irrational x →
        (∀ B > (0 : ℝ), ∃ δ > 0, ∀ d : ℕ, 0 < d → 0 < |(d.totient : ℝ) / d - x| →
          |(d.totient : ℝ) / d - x| < δ →
          B ≤ (d : ℝ) * |(d.totient : ℝ) / d - x| * (1 + Real.log |(d.totient : ℝ) / d - x|⁻¹)) →
        (∃ C > (0 : ℝ), ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ D : Finset ℕ,
          (∀ d ∈ D, 0 < d) → (∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d) →
          (∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1) →
          (∀ d ∈ D, |(d.totient : ℝ) / d - x| ≤ h) →
          (∑ d ∈ D, (d : ℝ)⁻¹) ≤ C * h * (1 + Real.log h⁻¹)) →
        ¬∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x

/-- Upper half (`1/2 < x < 1`): irrational interior points sifted by the primorial `M` of all
primes `p` with `(p - 1)/p < x` (`2 ∣ M`). On `[x - δ₀, x + δ₀]`, the sifted distribution `g`
on integers coprime to `M` inherits both the logarithmic ratio divergence and the local pattern
weight bound restricted to `Nat.Coprime d M`, and cannot have a positive derivative at `x`. -/
def H2 : Prop :=
  ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 1, (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → Irrational x →
    ∀ M : ℕ, 0 < M → 2 ∣ M →
      (∀ p : ℕ, p.Prime → ((p : ℝ) - 1) / p < x → p ∣ M) →
      ∀ δ₀ > (0 : ℝ), Set.Icc (x - δ₀) (x + δ₀) ⊆ Set.Ioo (0 : ℝ) 1 →
        ∀ g : ℝ → ℝ,
          (∀ c ∈ Set.Icc (x - δ₀) (x + δ₀),
            {n : ℕ | Nat.Coprime n M ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (g c)) →
          (∀ B > (0 : ℝ), ∃ δ > 0, ∀ d : ℕ, 0 < d → Nat.Coprime d M →
            0 < |(d.totient : ℝ) / d - x| → |(d.totient : ℝ) / d - x| < δ →
            B ≤ (d : ℝ) * |(d.totient : ℝ) / d - x| * (1 + Real.log |(d.totient : ℝ) / d - x|⁻¹)) →
          (∃ C > (0 : ℝ), ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ D : Finset ℕ,
            (∀ d ∈ D, 0 < d) → (∀ d ∈ D, Nat.Coprime d M) →
            (∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d) →
            (∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1) →
            (∀ d ∈ D, |(d.totient : ℝ) / d - x| ≤ h) →
            (∑ d ∈ D, (d : ℝ)⁻¹) ≤ C * h * (1 + Real.log h⁻¹)) →
          ¬∃ y > 0, HasDerivWithinAt g y (Set.Icc (x - δ₀) (x + δ₀)) x

-- ### Part 1: Basic natural density calculus

theorem partialDensity_eq_card_div (A : Set ℕ) [DecidablePred (· ∈ A)] (b : ℕ) :
    A.partialDensity Set.univ b =
      (((Finset.range b).filter (fun n => n ∈ A)).card : ℝ) / b := by
  classical
  have hs : A ∩ Set.Iio b = ((Finset.range b).filter (fun n => n ∈ A) : Set ℕ) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hs,
    Set.ncard_coe_finset, Nat.ncard_Iio]

theorem hasDensity_unique {A : Set ℕ} {a b : ℝ}
    (ha : A.HasDensity a) (hb : A.HasDensity b) : a = b :=
  tendsto_nhds_unique ha hb

theorem hasDensity_nonneg {A : Set ℕ} {a : ℝ} (ha : A.HasDensity a) : 0 ≤ a := by
  classical
  unfold Set.HasDensity at ha
  refine ge_of_tendsto' ha fun b => ?_
  rw [partialDensity_eq_card_div]
  positivity

theorem hasDensity_le_one {A : Set ℕ} {a : ℝ} (ha : A.HasDensity a) : a ≤ 1 := by
  classical
  unfold Set.HasDensity at ha
  refine le_of_tendsto' ha fun b => ?_
  rw [partialDensity_eq_card_div]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · rw [div_le_one (by exact_mod_cast hb)]
    have hcard := Finset.card_filter_le (Finset.range b) (fun n => n ∈ A)
    rw [Finset.card_range] at hcard
    exact_mod_cast hcard

theorem hasDensity_mono {A B : Set ℕ} {a b : ℝ} (hsub : A ⊆ B)
    (ha : A.HasDensity a) (hb : B.HasDensity b) : a ≤ b := by
  classical
  unfold Set.HasDensity at ha hb
  refine le_of_tendsto_of_tendsto ha hb (Eventually.of_forall fun N => ?_)
  dsimp only
  rw [partialDensity_eq_card_div, partialDensity_eq_card_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hfs : (Finset.range N).filter (fun n => n ∈ A) ⊆
      (Finset.range N).filter (fun n => n ∈ B) := by
    intro n hn
    obtain ⟨hN, hA⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hN, hsub hA⟩
  exact_mod_cast Finset.card_le_card hfs

theorem hasDensity_empty : (∅ : Set ℕ).HasDensity 0 := by
  classical
  unfold Set.HasDensity
  refine tendsto_const_nhds.congr fun N => ?_
  rw [partialDensity_eq_card_div]
  simp

theorem hasDensity_union_disjoint {A B : Set ℕ} {a b : ℝ} (hdisj : Disjoint A B)
    (ha : A.HasDensity a) (hb : B.HasDensity b) : (A ∪ B).HasDensity (a + b) := by
  classical
  unfold Set.HasDensity at ha hb ⊢
  refine (ha.add hb).congr fun N => ?_
  simp only [partialDensity_eq_card_div]
  have hd : Disjoint ((Finset.range N).filter (fun n => n ∈ A))
      ((Finset.range N).filter (fun n => n ∈ B)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    exact Set.disjoint_left.mp hdisj (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have heq : (Finset.range N).filter (fun n => n ∈ A ∪ B) =
      ((Finset.range N).filter (fun n => n ∈ A)) ∪
        ((Finset.range N).filter (fun n => n ∈ B)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]
    tauto
  rw [heq, Finset.card_union_of_disjoint hd, Nat.cast_add, add_div]

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

-- ### Part 2: Exact coprime and non-coprime densities + prime divisor bound

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

-- ### Part 3: Exact 2-adic scaling and odd-integer totient distribution `g2`

theorem hasDensity_scale_mul {S : Set ℕ} {α : ℝ} (hS : S.HasDensity α) {D : ℕ} (hD : 0 < D) :
    {n : ℕ | ∃ m ∈ S, n = D * m}.HasDensity (α / (D : ℝ)) := by
  classical
  let L : Set ℕ := {n : ℕ | ∃ m ∈ S, n = D * m}
  let q : ℕ → ℕ := fun b => (b + D - 1) / D
  have hDposR : (0 : ℝ) < D := by exact_mod_cast hD
  have hcard_eq : ∀ b : ℕ,
      ((Finset.range b).filter (fun n => n ∈ L)).card =
      ((Finset.range (q b)).filter (fun m => m ∈ S)).card := by
    intro b
    symm
    refine Finset.card_bij (fun m _ => D * m) ?_ ?_ ?_
    · intro m hm
      obtain ⟨hmq, hmS⟩ := Finset.mem_filter.mp hm
      have hmlt : m + 1 ≤ (b + D - 1) / D := Finset.mem_range.mp hmq
      have hmul : (m + 1) * D ≤ b + D - 1 := (Nat.le_div_iff_mul_le hD).mp hmlt
      have hdm : D * m < b := by
        have : (m + 1) * D = D * m + D := by ring
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdm, ⟨m, hmS, rfl⟩⟩
    · intro m₁ _ m₂ _ hEq
      exact Nat.eq_of_mul_eq_mul_left hD hEq
    · intro n hn
      obtain ⟨hnb, m, hmS, rfl⟩ := Finset.mem_filter.mp hn
      have hdm : D * m < b := Finset.mem_range.mp hnb
      have hmul : (m + 1) * D ≤ b + D - 1 := by
        have : (m + 1) * D = D * m + D := by ring
        omega
      have hmq : m < q b := (Nat.le_div_iff_mul_le hD).mpr hmul
      exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmq, hmS⟩, rfl⟩
  have hq_top : Tendsto q atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun M => ⟨M * D, fun b hb => ?_⟩
    exact (Nat.le_div_iff_mul_le hD).mpr (by omega)
  have hq_ratio : Tendsto (fun b : ℕ => (q b : ℝ) / b) atTop (𝓝 (1 / (D : ℝ))) := by
    have hhi : Tendsto (fun b : ℕ => 1 / (D : ℝ) + 1 / (b : ℝ)) atTop (𝓝 (1 / (D : ℝ))) := by
      simpa using (tendsto_const_nhds (x := 1 / (D : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
      have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      have hlb : b ≤ q b * D := by
        have h1 := Nat.div_add_mod (b + D - 1) D
        have h2 := Nat.mod_lt (b + D - 1) hD
        have h3 : q b * D = D * ((b + D - 1) / D) := by dsimp [q]; ring
        omega
      have hlbR : (b : ℝ) ≤ (q b : ℝ) * D := by exact_mod_cast hlb
      rw [div_le_div_iff₀ hDposR hbpos]
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
      have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      have hub : q b * D ≤ b + D := by
        have h1 : q b * D ≤ b + D - 1 := Nat.div_mul_le_self (b + D - 1) D
        omega
      have hubR : (q b : ℝ) * D ≤ (b : ℝ) + D := by exact_mod_cast hub
      have hdiv : (q b : ℝ) ≤ ((b : ℝ) + D) / D := (le_div_iff₀ hDposR).mpr hubR
      have hrhs : (1 / (D : ℝ) + 1 / (b : ℝ)) * b = ((b : ℝ) + D) / D := by
        field_simp
      rw [div_le_iff₀ hbpos, hrhs]
      exact hdiv
  have hprod : Tendsto (fun b : ℕ => S.partialDensity Set.univ (q b) * ((q b : ℝ) / b))
      atTop (𝓝 (α * (1 / (D : ℝ)))) := (hS.comp hq_top).mul hq_ratio
  rw [mul_one_div] at hprod
  unfold Set.HasDensity
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
  have hqpos : 0 < q b := (Nat.le_div_iff_mul_le hD).mpr (by omega)
  have hqne : (q b : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  rw [partialDensity_eq_card_div, partialDensity_eq_card_div, hcard_eq b]
  field_simp

theorem pow_two_mul_odd_unique {k₁ k₂ m₁ m₂ : ℕ}
    (h1 : Odd m₁) (h2 : Odd m₂) (heq : 2 ^ k₁ * m₁ = 2 ^ k₂ * m₂) :
    k₁ = k₂ ∧ m₁ = m₂ := by
  have hnd1 : ¬ 2 ∣ m₁ := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact h1
  have hnd2 : ¬ 2 ∣ m₂ := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact h2
  have hk : k₁ = k₂ := by
    rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
    · exfalso
      have hsub : 2 ^ k₁ * m₁ = 2 ^ k₁ * (2 ^ (k₂ - k₁) * m₂) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, heq]
      have hm : m₁ = 2 ^ (k₂ - k₁) * m₂ := Nat.eq_of_mul_eq_mul_left (by positivity) hsub
      have h2dvd : 2 ∣ m₁ := by
        rw [hm]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m₂
      exact hnd1 h2dvd
    · rfl
    · exfalso
      have hsub : 2 ^ k₂ * m₂ = 2 ^ k₂ * (2 ^ (k₁ - k₂) * m₁) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hgt.le, heq.symm]
      have hm : m₂ = 2 ^ (k₁ - k₂) * m₁ := Nat.eq_of_mul_eq_mul_left (by positivity) hsub
      have h2dvd : 2 ∣ m₂ := by
        rw [hm]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m₁
      exact hnd2 h2dvd
  subst hk
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) heq⟩

theorem hasDensity_dyadic_even {S : Set ℕ} {α : ℝ} (hodd : ∀ m ∈ S, Odd m)
    (hS : S.HasDensity α) :
    {n : ℕ | ∃ k ≥ 1, ∃ m ∈ S, n = 2 ^ k * m}.HasDensity α := by
  classical
  let E : Set ℕ := {n : ℕ | ∃ k ≥ 1, ∃ m ∈ S, n = 2 ^ k * m}
  let Ecap : ℕ → Set ℕ := fun K => {n : ℕ | ∃ k ∈ Finset.Icc 1 K, ∃ m ∈ S, n = 2 ^ k * m}
  have hEcap_dens : ∀ K : ℕ, (Ecap K).HasDensity (α * (1 - 1 / (2 : ℝ) ^ K)) := by
    intro K
    induction K with
    | zero =>
      have hempty : Ecap 0 = ∅ := by
        ext n
        simp [Ecap]
      rw [hempty]
      simp [hasDensity_empty]
    | succ K ih =>
      let L : Set ℕ := {n : ℕ | ∃ m ∈ S, n = 2 ^ (K + 1) * m}
      have hL_dens : L.HasDensity (α / (2 : ℝ) ^ (K + 1)) := by
        simpa [L, Nat.cast_pow] using hasDensity_scale_mul hS (by positivity : 0 < 2 ^ (K + 1))
      have hdisj : Disjoint (Ecap K) L := by
        rw [Set.disjoint_left]
        rintro n ⟨k, hk, m₁, hm₁, rfl⟩ ⟨m₂, hm₂, heq⟩
        have hkeq := (pow_two_mul_odd_unique (hodd m₁ hm₁) (hodd m₂ hm₂) heq).1
        have hkle := (Finset.mem_Icc.mp hk).2
        omega
      have hunion : Ecap (K + 1) = Ecap K ∪ L := by
        ext n
        simp only [Ecap, L, Set.mem_ofPred_eq, Set.mem_union, Finset.mem_Icc]
        constructor
        · rintro ⟨k, ⟨hk1, hk2⟩, m, hm, rfl⟩
          by_cases hk : k ≤ K
          · exact Or.inl ⟨k, ⟨hk1, hk⟩, m, hm, rfl⟩
          · have hke : k = K + 1 := by omega
            subst hke
            exact Or.inr ⟨m, hm, rfl⟩
        · rintro (⟨k, ⟨hk1, hk2⟩, m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
          · exact ⟨k, ⟨hk1, by omega⟩, m, hm, rfl⟩
          · exact ⟨K + 1, ⟨by omega, le_rfl⟩, m, hm, rfl⟩
      rw [hunion]
      have hsum : α * (1 - 1 / (2 : ℝ) ^ K) + α / (2 : ℝ) ^ (K + 1) =
          α * (1 - 1 / (2 : ℝ) ^ (K + 1)) := by
        rw [pow_succ]
        field_simp
        ring
      rw [← hsum]
      exact hasDensity_union_disjoint hdisj ih hL_dens
  have hα0 : 0 ≤ α := hasDensity_nonneg hS
  have hα1 : α ≤ 1 := hasDensity_le_one hS
  unfold Set.HasDensity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 4 by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hKinv : 1 / (2 : ℝ) ^ K < ε / 4 := by
    simpa [one_div, inv_pow] using hK
  have hEK := Metric.tendsto_atTop.mp (hEcap_dens K) (ε / 4) (by linarith)
  obtain ⟨N₁, hN₁⟩ := hEK
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 / ε)
  refine ⟨max (max N₁ N₂) 1, fun b hb => ?_⟩
  have hb1 : N₁ ≤ b := (le_max_left N₁ N₂).trans ((le_max_left _ 1).trans hb)
  have hb2 : N₂ ≤ b := (le_max_right N₁ N₂).trans ((le_max_left _ 1).trans hb)
  have hbpos_nat : 0 < b := (le_max_right _ 1).trans hb
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hbpos_nat
  have hinv_b : 1 / (b : ℝ) < ε / 4 := by
    have h4 : 4 / ε < (b : ℝ) := lt_of_lt_of_le hN₂ (by exact_mod_cast hb2)
    rw [div_lt_iff₀ hε] at h4
    rw [div_lt_div_iff₀ hbpos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hEK_near := Real.dist_eq _ _ ▸ hN₁ b hb1
  have hEK_abs : |(Ecap K).partialDensity Set.univ b - α * (1 - 1 / (2 : ℝ) ^ K)| < ε / 4 := hEK_near
  have hsub : Ecap K ⊆ E := by
    rintro n ⟨k, hk, m, hm, rfl⟩
    exact ⟨k, (Finset.mem_Icc.mp hk).1, m, hm, rfl⟩
  have hlo_pd : (Ecap K).partialDensity Set.univ b ≤ E.partialDensity Set.univ b := by
    rw [partialDensity_eq_card_div, partialDensity_eq_card_div]
    apply div_le_div_of_nonneg_right _ hbpos.le
    have hfs : (Finset.range b).filter (fun n => n ∈ Ecap K) ⊆
        (Finset.range b).filter (fun n => n ∈ E) := by
      intro n hn
      obtain ⟨hr, hmem⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hr, hsub hmem⟩
    exact_mod_cast Finset.card_le_card hfs
  have htail_card :
      ((Finset.range b).filter (fun n => n ∈ E)).card ≤
      ((Finset.range b).filter (fun n => n ∈ Ecap K)).card + (b / 2 ^ (K + 1) + 1) := by
    let tail := (Finset.range b).filter (fun n => 2 ^ (K + 1) ∣ n)
    have hcov : (Finset.range b).filter (fun n => n ∈ E) ⊆
        (Finset.range b).filter (fun n => n ∈ Ecap K) ∪ tail := by
      intro n hn
      obtain ⟨hr, k, hk1, m, hm, rfl⟩ := Finset.mem_filter.mp hn
      by_cases hk : k ≤ K
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨hr, k, Finset.mem_Icc.mpr ⟨hk1, hk⟩, m, hm, rfl⟩)
      · apply Finset.mem_union_right
        refine Finset.mem_filter.mpr ⟨hr, ?_⟩
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega)) m
    have htail_le : tail.card ≤ b / 2 ^ (K + 1) + 1 := by
      have hinj : tail.card ≤ (Finset.range (b / 2 ^ (K + 1) + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun n => n / 2 ^ (K + 1)) ?_ ?_
        · intro n hn
          obtain ⟨hr, _⟩ := Finset.mem_filter.mp hn
          have hlt : n < b := Finset.mem_range.mp hr
          have hle : n / 2 ^ (K + 1) ≤ b / 2 ^ (K + 1) := Nat.div_le_div_right hlt.le
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by dsimp only; omega))
        · intro n₁ hn₁ n₂ hn₂ hdiv
          dsimp only at hdiv
          have h1 := (Finset.mem_filter.mp hn₁).2
          have h2 := (Finset.mem_filter.mp hn₂).2
          have e1 := Nat.mul_div_cancel' h1
          have e2 := Nat.mul_div_cancel' h2
          rw [← e1, ← e2, hdiv]
      simpa using hinj
    calc ((Finset.range b).filter (fun n => n ∈ E)).card
        ≤ ((Finset.range b).filter (fun n => n ∈ Ecap K) ∪ tail).card := Finset.card_le_card hcov
      _ ≤ ((Finset.range b).filter (fun n => n ∈ Ecap K)).card + tail.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left htail_le _
  have hhi_pd : E.partialDensity Set.univ b ≤
      (Ecap K).partialDensity Set.univ b + 1 / (2 : ℝ) ^ (K + 1) + 1 / (b : ℝ) := by
    rw [partialDensity_eq_card_div, partialDensity_eq_card_div]
    have hcardR : (((Finset.range b).filter (fun n => n ∈ E)).card : ℝ) ≤
        (((Finset.range b).filter (fun n => n ∈ Ecap K)).card : ℝ) +
        ((b / 2 ^ (K + 1) : ℕ) : ℝ) + 1 := by
      have h1 : (((Finset.range b).filter (fun n => n ∈ E)).card : ℝ) ≤
          (((Finset.range b).filter (fun n => n ∈ Ecap K)).card + (b / 2 ^ (K + 1) + 1) : ℕ) := by
        exact_mod_cast htail_card
      push_cast at h1
      linarith
    have hdiv_le : ((b / 2 ^ (K + 1) : ℕ) : ℝ) ≤ (b : ℝ) / (2 : ℝ) ^ (K + 1) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (K + 1))]
      exact_mod_cast Nat.div_mul_le_self b (2 ^ (K + 1))
    have hnum : (((Finset.range b).filter (fun n => n ∈ E)).card : ℝ) ≤
        (((Finset.range b).filter (fun n => n ∈ Ecap K)).card : ℝ) +
        (b : ℝ) / (2 : ℝ) ^ (K + 1) + 1 := by linarith
    have hstep := div_le_div_of_nonneg_right hnum hbpos.le
    have hrhs : ((((Finset.range b).filter (fun n => n ∈ Ecap K)).card : ℝ) +
        (b : ℝ) / (2 : ℝ) ^ (K + 1) + 1) / b =
        (((Finset.range b).filter (fun n => n ∈ Ecap K)).card : ℝ) / b +
        1 / (2 : ℝ) ^ (K + 1) + 1 / b := by
      field_simp
    linarith
  have hpow_half : 1 / (2 : ℝ) ^ (K + 1) ≤ 1 / (2 : ℝ) ^ K := by
    rw [pow_succ]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    have : 1 / ((2 : ℝ) ^ K * 2) = (1 / (2 : ℝ) ^ K) / 2 := by field_simp
    linarith [div_pos one_pos hpos]
  have hα_term : 0 ≤ α / (2 : ℝ) ^ K ∧ α / (2 : ℝ) ^ K ≤ 1 / (2 : ℝ) ^ K := by
    refine ⟨by positivity, ?_⟩
    exact div_le_div_of_nonneg_right hα1 (by positivity)
  have hEK_lo : α * (1 - 1 / (2 : ℝ) ^ K) - ε / 4 < (Ecap K).partialDensity Set.univ b :=
    by linarith [(abs_lt.mp hEK_abs).1]
  have hEK_hi : (Ecap K).partialDensity Set.univ b < α * (1 - 1 / (2 : ℝ) ^ K) + ε / 4 :=
    by linarith [(abs_lt.mp hEK_abs).2]
  have hα_expand : α * (1 - 1 / (2 : ℝ) ^ K) = α - α / (2 : ℝ) ^ K := by ring
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem phi_ratio_even_decomp {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) :
    ∃ k ≥ 1, ∃ m : ℕ, Odd m ∧ n = 2 ^ k * m ∧
      (n.totient : ℝ) / n = (1 / 2) * ((m.totient : ℝ) / m) := by
  set k := n.factorization 2
  set m := n / 2 ^ k
  have h2k_dvd : 2 ^ k ∣ n := Nat.ordProj_dvd n 2
  have hn_eq : 2 ^ k * m = n := Nat.mul_div_cancel' h2k_dvd
  have hk_pos : 1 ≤ k := by
    have h1 : 2 ^ 1 ∣ n := by simpa using heven
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp h1
  have hm_not_even : ¬ 2 ∣ m := by
    intro h2m
    have hpow : 2 ^ (k + 1) ∣ n := by
      rw [← hn_eq, pow_succ]
      obtain ⟨r, hr⟩ := h2m
      exact ⟨r, by rw [hr]; ring⟩
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp hpow
    omega
  have hm_odd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hm_not_even
  have hm_pos : 0 < m := by
    rcases hm_odd with ⟨r, hr⟩; omega
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr hm_not_even)
  have hphi_mul : n.totient = (2 ^ k).totient * m.totient := by
    rw [← hn_eq, Nat.totient_mul hcop]
  have hphi2 : (2 ^ k).totient = 2 ^ (k - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k)]
    simp
  have hpow_eq : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hk_pos]
  refine ⟨k, hk_pos, m, hm_odd, hn_eq.symm, ?_⟩
  have hnR : (n : ℝ) = (2 : ℝ) ^ k * m := by exact_mod_cast hn_eq.symm
  have hphiR : (n.totient : ℝ) = (2 : ℝ) ^ (k - 1) * m.totient := by
    rw [hphi_mul, hphi2]; push_cast; rfl
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have h2R : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
  rw [hnR, hphiR, hpow_eq]
  field_simp

theorem odd_totient_set_eq_sdiff_high (c : ℝ) :
    {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n} =
    {n : ℕ | (n.totient : ℝ) < c * n} \ {n : ℕ | 0 < n ∧ ¬ Nat.Coprime n 2} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  have hcop2 : Nat.Coprime n 2 ↔ Odd n := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  constructor
  · rintro ⟨hodd, hlt⟩
    exact ⟨hlt, fun h => h.2 (hcop2.mpr hodd)⟩
  · rintro ⟨hlt, hnot⟩
    have hnpos : 0 < n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      simp at hlt
    refine ⟨hcop2.mp ?_, hlt⟩
    by_contra hnc
    exact hnot ⟨hnpos, hnc⟩

theorem even_totient_subset_high {c : ℝ} (hc : 1 / 2 < c) :
    {n : ℕ | 0 < n ∧ ¬ Nat.Coprime n 2} ⊆ {n : ℕ | (n.totient : ℝ) < c * n} := by
  intro n ⟨hnpos, hnc⟩
  have h2n : 2 ∣ n := by
    by_contra hnd
    exact hnc (Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr hnd))
  have hle := phi_div_le_of_prime_dvd hnpos Nat.prime_two h2n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlt : (n.totient : ℝ) / n < c := by linarith [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num]
  exact (div_lt_iff₀ hnR).mp hlt

theorem totient_even_part_eq_dyadic (c : ℝ) :
    {n : ℕ | (n.totient : ℝ) < c * n} \ {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n} =
    {n : ℕ | ∃ k ≥ 1, ∃ m ∈ {m : ℕ | Odd m ∧ (m.totient : ℝ) < (2 * c) * m}, n = 2 ^ k * m} := by
  ext n
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hlt, hnotodd⟩
    have hnpos : 0 < n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      simp at hlt
    have heven : 2 ∣ n := by
      rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
      intro hodd
      exact hnotodd ⟨hodd, hlt⟩
    obtain ⟨k, hk, m, hmodd, rfl, hratio⟩ := phi_ratio_even_decomp hnpos heven
    have hmpos : 0 < m := by rcases hmodd with ⟨r, rfl⟩; omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hnR : (0 : ℝ) < (2 ^ k * m : ℕ) := by exact_mod_cast hnpos
    have hlt1 : ((2 ^ k * m).totient : ℝ) / (2 ^ k * m : ℕ) < c := (div_lt_iff₀ hnR).mpr hlt
    rw [hratio] at hlt1
    have hlt2 : (m.totient : ℝ) / m < 2 * c := by linarith
    exact ⟨k, hk, m, ⟨hmodd, (div_lt_iff₀ hmR).mp hlt2⟩, rfl⟩
  · rintro ⟨k, hk, m, ⟨hmodd, hmlt⟩, rfl⟩
    have hmpos : 0 < m := by rcases hmodd with ⟨r, rfl⟩; omega
    have hnpos : 0 < 2 ^ k * m := by positivity
    have h2dvd : 2 ∣ 2 ^ k * m := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m
    have hnotodd : ¬ Odd (2 ^ k * m) := by
      rw [Nat.not_odd_iff_even, even_iff_two_dvd]
      exact h2dvd
    obtain ⟨k', hk', m', hm'odd, heq, hratio⟩ := phi_ratio_even_decomp hnpos h2dvd
    obtain ⟨rfl, rfl⟩ := pow_two_mul_odd_unique hmodd hm'odd heq
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hnR : (0 : ℝ) < (2 ^ k * m : ℕ) := by exact_mod_cast hnpos
    have hmlt' : (m.totient : ℝ) / m < 2 * c := (div_lt_iff₀ hmR).mpr hmlt
    have hlt' : ((2 ^ k * m).totient : ℝ) / (2 ^ k * m : ℕ) < c := by rw [hratio]; linarith
    exact ⟨(div_lt_iff₀ hnR).mp hlt', fun h => hnotodd h.1⟩

theorem exists_odd_totient_distribution {f : ℝ → ℝ}
    (hf : ∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) :
    ∃ g2 : ℝ → ℝ,
      (∀ c ∈ Set.Ioc (0 : ℝ) 1, {n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (g2 c)) ∧
      (∀ c ∈ Set.Ioc (1 / 2 : ℝ) 1, g2 c = f c - 1 / 2) ∧
      (∀ c ∈ Set.Ioc (0 : ℝ) (1 / 2), f c = g2 c + g2 (2 * c)) ∧
      MonotoneOn g2 (Set.Ioc (0 : ℝ) 1) := by
  classical
  have hhigh : ∀ c ∈ Set.Ioc (1 / 2 : ℝ) 1,
      {n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (f c - 1 / 2) := by
    intro c hc
    rw [odd_totient_set_eq_sdiff_high c]
    have h2dens : {n : ℕ | 0 < n ∧ ¬ Nat.Coprime n 2}.HasDensity (1 / 2 : ℝ) := by
      have h := not_coprime_pos_density (show 0 < 2 by norm_num)
      have hval : (1 : ℝ) - ((2 : ℕ).totient : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 := by
        rw [Nat.totient_two]; norm_num
      rwa [hval] at h
    have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], hc.2⟩
    exact hasDensity_sdiff (even_totient_subset_high hc.1) h2dens (hf c hc01)
  have hind : ∀ j : ℕ, ∀ c ∈ Set.Ioc (1 / (2 : ℝ) ^ (j + 1)) 1,
      ∃ α : ℝ, {n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}.HasDensity α := by
    intro j
    induction j with
    | zero =>
      intro c hc
      have hc' : c ∈ Set.Ioc (1 / 2 : ℝ) 1 := by simpa using hc
      exact ⟨f c - 1 / 2, hhigh c hc'⟩
    | succ j ih =>
      intro c hc
      by_cases hgt : 1 / 2 < c
      · exact ⟨f c - 1 / 2, hhigh c ⟨hgt, hc.2⟩⟩
      · have hle : c ≤ 1 / 2 := le_of_not_gt hgt
        have h2c : 2 * c ∈ Set.Ioc (1 / (2 : ℝ) ^ (j + 1)) 1 := by
          refine ⟨?_, by linarith⟩
          have h1 : 1 / (2 : ℝ) ^ (j + 2) < c := hc.1
          have hpow : (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ (j + 1) * 2 := by rw [pow_succ]
          rw [hpow] at h1
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
          rw [div_lt_iff₀ hpos]
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1) * 2)] at h1
          linarith
        obtain ⟨α, hα⟩ := ih (2 * c) h2c
        have heven_dens :
            {n : ℕ | ∃ k ≥ 1, ∃ m ∈ {m : ℕ | Odd m ∧ (m.totient : ℝ) < (2 * c) * m},
              n = 2 ^ k * m}.HasDensity α :=
          hasDensity_dyadic_even (fun m hm => hm.1) hα
        rw [← totient_even_part_eq_dyadic c] at heven_dens
        have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := by
          have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ (j + 2) := by positivity
          exact ⟨by linarith [hc.1], hc.2⟩
        have hodd_eq : {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n} =
            {n : ℕ | (n.totient : ℝ) < c * n} \
              ({n : ℕ | (n.totient : ℝ) < c * n} \ {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n}) := by
          ext n
          simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
          tauto
        rw [hodd_eq]
        exact ⟨f c - α, hasDensity_sdiff Set.sdiff_subset heven_dens (hf c hc01)⟩
  have hex : ∀ c ∈ Set.Ioc (0 : ℝ) 1,
      ∃ α : ℝ, {n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}.HasDensity α := by
    intro c hc
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hc.1 (show (1 / 2 : ℝ) < 1 by norm_num)
    have hj' : 1 / (2 : ℝ) ^ (j + 1) < c := by
      have h1 : 1 / (2 : ℝ) ^ j < c := by simpa [one_div, inv_pow] using hj
      have h2 : 1 / (2 : ℝ) ^ (j + 1) ≤ 1 / (2 : ℝ) ^ j := by
        rw [pow_succ]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
        have : 1 / ((2 : ℝ) ^ j * 2) = (1 / (2 : ℝ) ^ j) / 2 := by field_simp
        linarith [div_pos one_pos hpos]
      linarith
    exact hind j c ⟨hj', hc.2⟩
  let g2 : ℝ → ℝ := fun c => if hc : c ∈ Set.Ioc (0 : ℝ) 1 then Classical.choose (hex c hc) else 0
  have hg2_dens : ∀ c ∈ Set.Ioc (0 : ℝ) 1,
      {n : ℕ | Odd n ∧ (Nat.totient n : ℝ) < c * n}.HasDensity (g2 c) := by
    intro c hc
    simp only [g2, dif_pos hc]
    exact Classical.choose_spec (hex c hc)
  refine ⟨g2, hg2_dens, ?_, ?_, ?_⟩
  · intro c hc
    have hc01 : c ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith [hc.1], hc.2⟩
    exact hasDensity_unique (hg2_dens c hc01) (hhigh c hc)
  · intro c hc
    have hc01 : c ∈ Set.Ioc (0 : ℝ) 1 := ⟨hc.1, by linarith [hc.2]⟩
    have h2c01 : 2 * c ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hodd_d := hg2_dens c hc01
    have heven_d :
        ({n : ℕ | (n.totient : ℝ) < c * n} \ {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n}).HasDensity
          (g2 (2 * c)) := by
      rw [totient_even_part_eq_dyadic c]
      exact hasDensity_dyadic_even (fun m hm => hm.1) (hg2_dens (2 * c) h2c01)
    have hdisj : Disjoint {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n}
        ({n : ℕ | (n.totient : ℝ) < c * n} \ {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n}) :=
      disjoint_sdiff_self_right
    have hunion : {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n} ∪
        ({n : ℕ | (n.totient : ℝ) < c * n} \ {n : ℕ | Odd n ∧ (n.totient : ℝ) < c * n}) =
        {n : ℕ | (n.totient : ℝ) < c * n} := by
      ext n
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq]
      tauto
    have hsum_d := hasDensity_union_disjoint hdisj hodd_d heven_d
    rw [hunion] at hsum_d
    exact hasDensity_unique (hf c ⟨hc.1.le, by linarith [hc.2]⟩) hsum_d
  · intro u hu v hv huv
    have hsub : {n : ℕ | Odd n ∧ (n.totient : ℝ) < u * n} ⊆
        {n : ℕ | Odd n ∧ (n.totient : ℝ) < v * n} := by
      intro n ⟨hodd, hlt⟩
      exact ⟨hodd, lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_right huv (Nat.cast_nonneg n))⟩
    exact hasDensity_mono hsub (hg2_dens u hu) (hg2_dens v hv)

-- ### Part 4: Main reduction proof

theorem main : H1 → H2 → OMA.R_Erdos50_erdos_50_R2.H1 := by
  intro h1 h2 f hf x hx hratio hirr hsep hpat hderiv
  have hne_half : x ≠ 1 / 2 := by
    intro hhalf
    apply hratio
    refine ⟨2, by norm_num, ?_⟩
    rw [hhalf]
    norm_num [Nat.totient_two]
  rcases lt_or_gt_of_ne hne_half with hlt | hgt
  · obtain ⟨g2, hg2_dens, hg2_high, hg2_eq, hg2_mono⟩ := exists_odd_totient_distribution hf
    exact h1 f hf g2 hg2_dens hg2_high hg2_eq hg2_mono x ⟨hx.1, hlt⟩ hratio hirr hsep hpat hderiv
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
          have := (hp.prime.dvd_finsetProd_iff id).mp hpM
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
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
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
    have hg_sep : ∀ B > (0 : ℝ), ∃ δ > 0, ∀ d : ℕ, 0 < d → Nat.Coprime d M →
        0 < |(d.totient : ℝ) / d - x| → |(d.totient : ℝ) / d - x| < δ →
        B ≤ (d : ℝ) * |(d.totient : ℝ) / d - x| * (1 + Real.log |(d.totient : ℝ) / d - x|⁻¹) := by
      intro B hB
      obtain ⟨δ, hδ, hb⟩ := hsep B hB
      exact ⟨δ, hδ, fun d hd _ hpos hlt => hb d hd hpos hlt⟩
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
    exact h2 x ⟨hgt, hx.2⟩ hratio hirr M hMpos h2M hallM δ₀ hδ₀ hIcc_sub g hg_dens hg_sep hg_pat
      ⟨y, hy, hgy⟩

end OMA.R_Erdos50_erdos_50_R2_H1_R1
