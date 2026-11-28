import OMAReductions.R_Erdos39_erdos_39_R1

/-!
# Reduction `Erdos39.erdos_39.R1.H1.R1` — Dyadic coded-block Sidon construction

Reduces hypothesis `H1` of `Erdos39.erdos_39.R1` (finite Sidon prefixes achieving an envelope
`f(n) = Ω_ε(n^{1/2 - ε})` for all `ε > 0`) into two completely independent components:

* `H1` (open combinatorial core): finite dyadic Sidon blocks `B_j ⊆ [2^j, 2^{j+1})` achieving
  a dyadic growth envelope `g(j) = Ω_ε(2^{(1/2 - ε) j})` for all `ε > 0`, whose positive
  differences avoid those of nearby blocks (`j / 3 < i < j`).
* `H2` (known arithmetic encoding): a dyadic Sidon tag encoder `E : ℕ → ℕ` whose pair sums
  `E a + E b` determine both `a + b` and the unordered pair `{Nat.log 2 a, Nat.log 2 b}`,
  stretching each dyadic block `[2^j, 2^{j+1})` by at most a polynomial factor `(j + 2)^e`.

Inside this file we prove:
1. `sidon_thin_small_diffs`: deleting at most `D` elements from any finite Sidon set enforces
   minimum pairwise difference `> D`, unconditionally eliminating cross-scale collisions with
   distant blocks `i ≤ j / 3`.
2. `coded_blocks_isSidon`: combining thinned dyadic Sidon blocks through any encoder `E`
   satisfying `H2` produces a genuine Sidon set.
3. Full dyadic-to-all-`n` asymptotic transfer (`main`), absorbing both the polynomial overhead
   `(j + 3)^e` and the thinning loss `2^{j / 3 + 1}` into `ε`.
-/

-- Credit: @sanchan

namespace OMA.R_Erdos39_erdos_39_R1_H1_R1

open Filter Asymptotics Finset
open scoped Topology

/-- Open combinatorial core: finite dyadic Sidon blocks `B_j ⊆ [2^j, 2^{j+1})` with dyadic
size envelope `g(j) = Ω_ε(2^{(1/2 - ε) j})` for every `ε > 0`, avoiding shared positive
differences across nearby scales `j / 3 < i < j`. -/
def H1 : Prop :=
  ∃ (g : ℕ → ℕ) (J : ℕ),
    (∀ ε > (0 : ℝ),
      (fun j : ℕ => (2 : ℝ) ^ ((1 / 2 - ε) * (j : ℝ))) =O[atTop] fun j => (g j : ℝ)) ∧
    ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon ((B j : Finset ℕ) : Set ℕ)) ∧
      (∀ j, J ≤ j → j ≤ N → g j ≤ (B j).card) ∧
      ∀ i j, j / 3 < i → i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v

/-- Known arithmetic encoding: an integer code `E` whose pair sums recover both the original
sum and the unordered pair of dyadic scales `Nat.log 2`, with polynomial overhead `(j + 2)^e`. -/
def H2 : Prop :=
  ∃ (E : ℕ → ℕ) (e : ℕ),
    (∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
    ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * (j + 2) ^ e

/-- In a Sidon set, positive differences uniquely determine the larger endpoint. -/
theorem sidon_diff_inj {A : Set ℕ} (hA : IsSidon A)
    {u₁ v₁ u₂ v₂ : ℕ} (hu₁ : u₁ ∈ A) (hv₁ : v₁ ∈ A) (hu₂ : u₂ ∈ A) (hv₂ : v₂ ∈ A)
    (hlt₁ : v₁ < u₁) (hlt₂ : v₂ < u₂) (hdiff : u₁ - v₁ = u₂ - v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have hsum : u₁ + v₂ = u₂ + v₁ := by omega
  rcases hA u₁ hu₁ u₂ hu₂ v₂ hv₂ v₁ hv₁ hsum with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact ⟨h1, h2.symm⟩
  · omega

/-- Thinning lemma: from any finite Sidon set `A` and threshold `D`, removing at most `D`
elements leaves a subset `A' ⊆ A` with minimum pairwise difference strictly above `D`. -/
theorem sidon_thin_small_diffs (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (D : ℕ) :
    ∃ A' ⊆ A, A.card ≤ A'.card + D ∧ ∀ u ∈ A', ∀ v ∈ A', v < u → D < u - v := by
  classical
  let Bad := A.filter (fun u => ∃ v ∈ A, v < u ∧ u - v ≤ D)
  have hBad_card : Bad.card ≤ D := by
    have hv_ex : ∀ u : ℕ, u ∈ Bad → ∃ v ∈ A, v < u ∧ u - v ≤ D :=
      fun u hu => (Finset.mem_filter.mp hu).2
    let f : ℕ → ℕ := fun u =>
      if h : u ∈ Bad then u - Classical.choose (hv_ex u h) else 0
    have hmaps : Set.MapsTo f (Bad : Set ℕ) (Finset.Icc 1 D : Set ℕ) := by
      intro u hu
      have hu' : u ∈ Bad := hu
      have hspec := Classical.choose_spec (hv_ex u hu')
      simp only [f, dif_pos hu', Finset.mem_coe, Finset.mem_Icc]
      omega
    have hinj : Set.InjOn f (Bad : Set ℕ) := by
      intro u₁ hu₁ u₂ hu₂ heq
      have hu₁' : u₁ ∈ Bad := hu₁
      have hu₂' : u₂ ∈ Bad := hu₂
      have hs₁ := Classical.choose_spec (hv_ex u₁ hu₁')
      have hs₂ := Classical.choose_spec (hv_ex u₂ hu₂')
      simp only [f, dif_pos hu₁', dif_pos hu₂'] at heq
      exact (sidon_diff_inj hA (Finset.mem_filter.mp hu₁').1 hs₁.1
        (Finset.mem_filter.mp hu₂').1 hs₂.1 hs₁.2.1 hs₂.2.1 heq).1
    have hle := Finset.card_le_card_of_injOn f hmaps hinj
    simpa [Nat.card_Icc] using hle
  refine ⟨A \ Bad, Finset.sdiff_subset, ?_, ?_⟩
  · have hsub : Bad ⊆ A := Finset.filter_subset _ _
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    omega
  · intro u hu v hv hvu
    have huA : u ∈ A := (Finset.mem_sdiff.mp hu).1
    have huNB : u ∉ Bad := (Finset.mem_sdiff.mp hu).2
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    by_contra hle
    exact huNB (Finset.mem_filter.mpr ⟨huA, v, hvA, hvu, by omega⟩)

/-- Every `a ∈ [2^j, 2^(j+1))` satisfies `Nat.log 2 a = j`. -/
theorem nat_log_two_of_mem_Ico {j a : ℕ} (ha : a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))) :
    Nat.log 2 a = j := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp ha
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

/-- A dyadic Sidon encoder `E` is automatically injective. -/
theorem encoder_injective {E : ℕ → ℕ}
    (hE : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) :
    Function.Injective E := by
  intro a b hab
  have h := (hE a a b b (by omega)).1
  omega

/-- Combining thinned dyadic Sidon blocks via a dyadic Sidon encoder `E` gives a Sidon set. -/
theorem coded_blocks_isSidon {N : ℕ} {B' : ℕ → Finset ℕ} {E : ℕ → ℕ}
    (hIco : ∀ j, B' j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hSid : ∀ j, IsSidon ((B' j : Finset ℕ) : Set ℕ))
    (hGap : ∀ j, ∀ u ∈ B' j, ∀ v ∈ B' j, v < u → 2 ^ (j / 3 + 1) < u - v)
    (hCross : ∀ i j, j / 3 < i → i < j → ∀ a ∈ B' i, ∀ b ∈ B' i, ∀ u ∈ B' j, ∀ v ∈ B' j,
      b < a → v < u → a - b ≠ u - v)
    (hE : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) :
    IsSidon (((Finset.range (N + 1)).biUnion (fun j => (B' j).image E) : Finset ℕ) : Set ℕ) := by
  intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hsum
  simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hx₁ hy₁ hx₂ hy₂
  obtain ⟨i₁, _, a, ha, rfl⟩ := hx₁
  obtain ⟨j₁, _, u, hu, rfl⟩ := hy₁
  obtain ⟨i₂, _, b, hb, rfl⟩ := hx₂
  obtain ⟨j₂, _, v, hv, rfl⟩ := hy₂
  have ⟨hab, hlogs⟩ := hE a b u v hsum
  have hli₁ : Nat.log 2 a = i₁ := nat_log_two_of_mem_Ico (hIco i₁ ha)
  have hli₂ : Nat.log 2 b = i₂ := nat_log_two_of_mem_Ico (hIco i₂ hb)
  have hlj₁ : Nat.log 2 u = j₁ := nat_log_two_of_mem_Ico (hIco j₁ hu)
  have hlj₂ : Nat.log 2 v = j₂ := nat_log_two_of_mem_Ico (hIco j₂ hv)
  rw [hli₁, hli₂, hlj₁, hlj₂] at hlogs
  have hcase : ∀ (r s : ℕ) (p q p' q' : ℕ),
      p ∈ B' r → p' ∈ B' r → q ∈ B' s → q' ∈ B' s → p + q = p' + q' →
      (E p = E p' ∧ E q = E q') ∨ (E p = E q' ∧ E q = E p') := by
    intro r s p q p' q' hp hp' hq hq' hpq
    by_cases hrs : r = s
    · subst hrs
      rcases hSid r p hp p' hp' q hq q' hq' hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg E h1, congrArg E h2⟩
      · exact Or.inr ⟨congrArg E h1, congrArg E h2⟩
    · have hp_eq : p = p' := by
        by_contra hne
        rcases lt_or_gt_of_ne hrs with hlt | hgt
        · rcases lt_or_gt_of_ne hne with hpp | hpp
          · have hqq : q' < q := by omega
            have hdiff : p' - p = q - q' := by omega
            by_cases hnear : s / 3 < r
            · exact hCross r s hnear hlt p' hp' p hp q hq q' hq' hpp hqq hdiff
            · have hle : r + 1 ≤ s / 3 + 1 := by omega
              have hp'lt : p' < 2 ^ (r + 1) := (Finset.mem_Ico.mp (hIco r hp')).2
              have hpow : 2 ^ (r + 1) ≤ 2 ^ (s / 3 + 1) := Nat.pow_le_pow_right (by norm_num) hle
              have hgap := hGap s q hq q' hq' hqq
              omega
          · have hqq : q < q' := by omega
            have hdiff : p - p' = q' - q := by omega
            by_cases hnear : s / 3 < r
            · exact hCross r s hnear hlt p hp p' hp' q' hq' q hq hpp hqq hdiff
            · have hle : r + 1 ≤ s / 3 + 1 := by omega
              have hplt : p < 2 ^ (r + 1) := (Finset.mem_Ico.mp (hIco r hp)).2
              have hpow : 2 ^ (r + 1) ≤ 2 ^ (s / 3 + 1) := Nat.pow_le_pow_right (by norm_num) hle
              have hgap := hGap s q' hq' q hq hqq
              omega
        · rcases lt_or_gt_of_ne hne with hpp | hpp
          · have hqq : q' < q := by omega
            have hdiff : q - q' = p' - p := by omega
            by_cases hnear : r / 3 < s
            · exact hCross s r hnear hgt q hq q' hq' p' hp' p hp hqq hpp hdiff
            · have hle : s + 1 ≤ r / 3 + 1 := by omega
              have hqlt : q < 2 ^ (s + 1) := (Finset.mem_Ico.mp (hIco s hq)).2
              have hpow : 2 ^ (s + 1) ≤ 2 ^ (r / 3 + 1) := Nat.pow_le_pow_right (by norm_num) hle
              have hgap := hGap r p' hp' p hp hpp
              omega
          · have hqq : q < q' := by omega
            have hdiff : q' - q = p - p' := by omega
            by_cases hnear : r / 3 < s
            · exact hCross s r hnear hgt q' hq' q hq p hp p' hp' hqq hpp hdiff
            · have hle : s + 1 ≤ r / 3 + 1 := by omega
              have hq'lt : q' < 2 ^ (s + 1) := (Finset.mem_Ico.mp (hIco s hq')).2
              have hpow : 2 ^ (s + 1) ≤ 2 ^ (r / 3 + 1) := Nat.pow_le_pow_right (by norm_num) hle
              have hgap := hGap r p hp p' hp' hpp
              omega
      have hq_eq : q = q' := by omega
      exact Or.inl ⟨congrArg E hp_eq, congrArg E hq_eq⟩
  rcases hlogs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcase i₁ i₂ a b u v ha hu hb hv hab
  · rcases hcase i₁ i₂ a b v u ha hv hb hu (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

/-- Polynomial growth `(j + 3) ^ e` is eventually dominated by `2 ^ (δ * j)` for any `δ > 0`. -/
theorem poly_le_rpow_two (e : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j : ℕ in atTop, ((j + 3 : ℕ) : ℝ) ^ e ≤ (2 : ℝ) ^ (δ * (j : ℝ)) := by
  have hr : (1 : ℝ) < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have ht := tendsto_pow_const_div_const_pow_of_one_lt e hr
  have ht3 : Tendsto (fun j : ℕ => ((j + 3 : ℕ) : ℝ) ^ e / ((2 : ℝ) ^ δ) ^ (j + 3)) atTop (𝓝 0) :=
    ht.comp (tendsto_add_atTop_nat 3)
  have hmul : Tendsto (fun j : ℕ => ((2 : ℝ) ^ δ) ^ 3 *
      (((j + 3 : ℕ) : ℝ) ^ e / ((2 : ℝ) ^ δ) ^ (j + 3))) atTop (𝓝 0) := by
    simpa using ht3.const_mul (((2 : ℝ) ^ δ) ^ 3)
  filter_upwards [(tendsto_order.mp hmul).2 1 zero_lt_one] with j hj
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ δ) ^ j := by positivity
  have hpow3 : ((2 : ℝ) ^ δ) ^ (j + 3) = ((2 : ℝ) ^ δ) ^ j * ((2 : ℝ) ^ δ) ^ 3 := pow_add _ j 3
  have hsimp : ((2 : ℝ) ^ δ) ^ 3 * (((j + 3 : ℕ) : ℝ) ^ e / ((2 : ℝ) ^ δ) ^ (j + 3)) =
      ((j + 3 : ℕ) : ℝ) ^ e / ((2 : ℝ) ^ δ) ^ j := by
    rw [hpow3]
    field_simp
  rw [hsimp, div_lt_one hpos] at hj
  have hEq : ((2 : ℝ) ^ δ) ^ j = (2 : ℝ) ^ (δ * (j : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ δ) j, ← Real.rpow_mul (by norm_num)]
  rw [← hEq]
  exact hj.le

theorem main : H1 → H2 → OMA.R_Erdos39_erdos_39_R1.H1 := by
  rintro ⟨g, J, hgO, hB⟩ ⟨E, e, hE, hEbound⟩
  classical
  let T : ℕ → ℕ := fun j => 2 ^ j * (j + 2) ^ e
  have hT_ge : ∀ j : ℕ, j < T j := by
    intro j
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 1 ≤ (j + 2) ^ e := Nat.one_le_pow _ _ (by omega)
    dsimp only [T]
    nlinarith
  let jn : ℕ → ℕ := fun n => ((Finset.range (n + 1)).filter (fun j => T j ≤ n)).sup id
  have hjn_spec : ∀ n : ℕ, T J ≤ n → J ≤ jn n ∧ T (jn n) ≤ n ∧ n < T (jn n + 1) := by
    intro n hn
    let S := (Finset.range (n + 1)).filter (fun j => T j ≤ n)
    have hJS : J ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hT_ge J; omega), hn⟩
    have hSne : S.Nonempty := ⟨J, hJS⟩
    have hmax_mem : S.max' hSne ∈ S := Finset.max'_mem S hSne
    have hsup_eq : jn n = S.max' hSne := by
      apply le_antisymm
      · exact Finset.sup_le fun j hj => Finset.le_max' S j hj
      · exact Finset.le_sup (f := id) hmax_mem
    refine ⟨?_, ?_, ?_⟩
    · rw [hsup_eq]; exact Finset.le_max' S J hJS
    · rw [hsup_eq]; exact (Finset.mem_filter.mp hmax_mem).2
    · by_contra hle
      push Not at hle
      have hmem1 : jn n + 1 ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hT_ge (jn n + 1); omega), hle⟩
      have hle_max : jn n + 1 ≤ S.max' hSne := Finset.le_max' S (jn n + 1) hmem1
      omega
  have hjn_tendsto : Tendsto jn atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    refine ⟨T (max J M), fun n hn => ?_⟩
    have hmem : max J M ∈ (Finset.range (n + 1)).filter (fun j => T j ≤ n) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hT_ge (max J M); omega), hn⟩
    exact (le_max_right J M).trans (Finset.le_sup (f := id) hmem)
  let f : ℕ → ℕ := fun n => if T J ≤ n then g (jn n) - 2 ^ (jn n / 3 + 1) else 0
  have hlow : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 12 →
      ∃ C > (0 : ℝ), ∀ᶠ j : ℕ in atTop,
        (2 : ℝ) ^ ((1 / 2 - δ) * (j : ℝ)) ≤ C * ((g j - 2 ^ (j / 3 + 1) : ℕ) : ℝ) := by
    intro δ hδ hδ12
    obtain ⟨C0, hC0⟩ := (hgO δ hδ).bound
    set C1 := max C0 1
    have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hC1ge : C0 ≤ C1 := le_max_left _ _
    have hr : (1 : ℝ) < (2 : ℝ) ^ ((1 / 12 : ℝ)) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have hpow_top : Tendsto (fun j : ℕ => ((2 : ℝ) ^ ((1 / 12 : ℝ))) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hr
    have hbig : ∀ᶠ j : ℕ in atTop, 4 * C1 ≤ ((2 : ℝ) ^ ((1 / 12 : ℝ))) ^ j :=
      hpow_top.eventually (eventually_ge_atTop (4 * C1))
    refine ⟨2 * C1, by positivity, ?_⟩
    filter_upwards [hC0, hbig] with j hj h4C
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hj
    have hgj : (2 : ℝ) ^ ((1 / 2 - δ) * (j : ℝ)) ≤ C1 * (g j : ℝ) :=
      hj.trans (mul_le_mul_of_nonneg_right hC1ge (Nat.cast_nonneg _))
    have hsub_le : ((2 ^ (j / 3 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) * (2 : ℝ) ^ ((1 / 3 : ℝ) * (j : ℝ)) := by
      have hdiv3 : ((j / 3 : ℕ) : ℝ) ≤ (1 / 3 : ℝ) * (j : ℝ) := by
        have : 3 * (j / 3) ≤ j := Nat.mul_div_le j 3
        have hR : (3 : ℝ) * ((j / 3 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
        linarith
      rw [pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm,
        ← Real.rpow_natCast (2 : ℝ) (j / 3)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv3) (by norm_num)
    have h12_eq : ((2 : ℝ) ^ ((1 / 12 : ℝ))) ^ j = (2 : ℝ) ^ ((1 / 12 : ℝ) * (j : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 / 12 : ℝ))) j, ← Real.rpow_mul (by norm_num)]
    rw [h12_eq] at h4C
    have hexp : (1 / 3 : ℝ) * (j : ℝ) + (1 / 12 : ℝ) * (j : ℝ) ≤ (1 / 2 - δ) * (j : ℝ) := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have h2sub : 2 * C1 * ((2 ^ (j / 3 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 - δ) * (j : ℝ)) := by
      calc 2 * C1 * ((2 ^ (j / 3 + 1) : ℕ) : ℝ)
          ≤ 2 * C1 * ((2 : ℝ) * (2 : ℝ) ^ ((1 / 3 : ℝ) * (j : ℝ))) :=
            mul_le_mul_of_nonneg_left hsub_le (by positivity)
        _ = (4 * C1) * (2 : ℝ) ^ ((1 / 3 : ℝ) * (j : ℝ)) := by ring
        _ ≤ (2 : ℝ) ^ ((1 / 12 : ℝ) * (j : ℝ)) * (2 : ℝ) ^ ((1 / 3 : ℝ) * (j : ℝ)) :=
            mul_le_mul_of_nonneg_right h4C (by positivity)
        _ = (2 : ℝ) ^ ((1 / 3 : ℝ) * (j : ℝ) + (1 / 12 : ℝ) * (j : ℝ)) := by
            rw [mul_comm, ← Real.rpow_add (by norm_num)]
        _ ≤ (2 : ℝ) ^ ((1 / 2 - δ) * (j : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hle_nat : 2 ^ (j / 3 + 1) ≤ g j := by
      by_contra hlt
      push Not at hlt
      have hltR : (g j : ℝ) < ((2 ^ (j / 3 + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
      have : C1 * (g j : ℝ) < C1 * ((2 ^ (j / 3 + 1) : ℕ) : ℝ) :=
        mul_lt_mul_of_pos_left hltR hC1pos
      have hnonneg : (0 : ℝ) ≤ C1 * ((2 ^ (j / 3 + 1) : ℕ) : ℝ) := by positivity
      linarith
    rw [Nat.cast_sub hle_nat]
    linarith
  refine ⟨f, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨C, hC, hEv⟩ := hlow (1 / 12) (by norm_num) le_rfl
    have hr : (1 : ℝ) < (2 : ℝ) ^ ((5 / 12 : ℝ)) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have hpow_top : Tendsto (fun j : ℕ => ((2 : ℝ) ^ ((5 / 12 : ℝ))) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hr
    have hbig : ∀ᶠ j : ℕ in atTop, C * (k : ℝ) ≤ ((2 : ℝ) ^ ((5 / 12 : ℝ))) ^ j :=
      hpow_top.eventually (eventually_ge_atTop (C * (k : ℝ)))
    have hcomb : ∀ᶠ n : ℕ in atTop,
        T J ≤ n ∧ (2 : ℝ) ^ ((1 / 2 - (1 / 12 : ℝ)) * (jn n : ℝ)) ≤ C * ((g (jn n) - 2 ^ (jn n / 3 + 1) : ℕ) : ℝ) ∧
        C * (k : ℝ) ≤ ((2 : ℝ) ^ ((5 / 12 : ℝ))) ^ (jn n) := by
      filter_upwards [eventually_ge_atTop (T J), hjn_tendsto.eventually hEv,
        hjn_tendsto.eventually hbig] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨n, hTJ, h1, h2⟩ := hcomb.exists
    refine ⟨n, ?_⟩
    have h512 : ((2 : ℝ) ^ ((5 / 12 : ℝ))) ^ (jn n) = (2 : ℝ) ^ ((1 / 2 - (1 / 12 : ℝ)) * (jn n : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((5 / 12 : ℝ))) (jn n), ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h512] at h2
    have hfk : (k : ℝ) ≤ (f n : ℝ) := by
      have hf_eq : f n = g (jn n) - 2 ^ (jn n / 3 + 1) := if_pos hTJ
      rw [hf_eq]
      nlinarith
    exact_mod_cast hfk
  · intro ε hε
    set δ := min (ε / 2) (1 / 12 : ℝ)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ12 : δ ≤ 1 / 12 := min_le_right _ _
    have h2δ : 2 * δ ≤ ε := by have := min_le_left (ε / 2) (1 / 12 : ℝ); linarith
    obtain ⟨C, hC, hEv⟩ := hlow δ hδ hδ12
    have hpoly := poly_le_rpow_two e hδ
    refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    filter_upwards [eventually_ge_atTop (max 1 (T J)), hjn_tendsto.eventually hEv,
      hjn_tendsto.eventually hpoly] with n hn hfl hpl
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hTJ : T J ≤ n := le_trans (le_max_right _ _) hn
    have hf_eq : f n = g (jn n) - 2 ^ (jn n / 3 + 1) := if_pos hTJ
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
      Real.norm_of_nonneg (Nat.cast_nonneg _), hf_eq]
    by_cases hneg : 1 / 2 - ε ≤ 0
    · have h1 : (n : ℝ) ^ (1 / 2 - ε) ≤ 1 := by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        exact Real.rpow_le_one_of_one_le_of_nonpos hnR hneg
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 - δ) * (jn n : ℝ)) :=
        Real.one_le_rpow (by norm_num) (mul_nonneg (by linarith) (Nat.cast_nonneg _))
      nlinarith
    · push Not at hneg
      have hspec := hjn_spec n hTJ
      have hn_lt : (n : ℝ) ≤ 2 * (2 : ℝ) ^ ((1 + δ) * (jn n : ℝ)) := by
        have hlt : (n : ℝ) ≤ ((T (jn n + 1) : ℕ) : ℝ) := by exact_mod_cast hspec.2.2.le
        have hTcast : ((T (jn n + 1) : ℕ) : ℝ) =
            2 * (2 : ℝ) ^ (jn n : ℝ) * ((jn n + 3 : ℕ) : ℝ) ^ e := by
          dsimp only [T]
          rw [pow_succ, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
            ← Real.rpow_natCast (2 : ℝ) (jn n)]
          have hadd : jn n + 1 + 2 = jn n + 3 := by omega
          rw [hadd]
          ring
        rw [hTcast] at hlt
        calc (n : ℝ) ≤ 2 * (2 : ℝ) ^ (jn n : ℝ) * ((jn n + 3 : ℕ) : ℝ) ^ e := hlt
          _ ≤ 2 * (2 : ℝ) ^ (jn n : ℝ) * (2 : ℝ) ^ (δ * (jn n : ℝ)) :=
              mul_le_mul_of_nonneg_left hpl (by positivity)
          _ = 2 * ((2 : ℝ) ^ (jn n : ℝ) * (2 : ℝ) ^ (δ * (jn n : ℝ))) := by ring
          _ = 2 * (2 : ℝ) ^ ((1 + δ) * (jn n : ℝ)) := by
              rw [← Real.rpow_add (by norm_num)]
              congr 2; ring
      have hrpow1 : (n : ℝ) ^ (1 / 2 - ε) ≤ (2 * (2 : ℝ) ^ ((1 + δ) * (jn n : ℝ))) ^ (1 / 2 - ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn_lt hneg.le
      have h2le : (2 : ℝ) ^ (1 / 2 - ε) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 2 - ε) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hexp : (1 + δ) * (jn n : ℝ) * (1 / 2 - ε) ≤ (1 / 2 - δ) * (jn n : ℝ) := by
        have hcoeff : (1 + δ) * (1 / 2 - ε) ≤ 1 / 2 - δ := by nlinarith
        have hj0 : (0 : ℝ) ≤ jn n := Nat.cast_nonneg _
        nlinarith
      have hstep : (2 * (2 : ℝ) ^ ((1 + δ) * (jn n : ℝ))) ^ (1 / 2 - ε) ≤
          2 * (2 : ℝ) ^ ((1 / 2 - δ) * (jn n : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num)]
        exact mul_le_mul h2le (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
          (by positivity) (by norm_num)
      calc (n : ℝ) ^ (1 / 2 - ε) ≤ 2 * (2 : ℝ) ^ ((1 / 2 - δ) * (jn n : ℝ)) := hrpow1.trans hstep
        _ ≤ 2 * (C * ((g (jn n) - 2 ^ (jn n / 3 + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hfl (by norm_num)
        _ = 2 * C * ((g (jn n) - 2 ^ (jn n / 3 + 1) : ℕ) : ℝ) := by ring
  · intro K
    obtain ⟨B_raw, hBIco, hBSid, hBcard, hBCross⟩ := hB K
    have hthin : ∀ j : ℕ, ∃ A' ⊆ B_raw j,
        (B_raw j).card ≤ A'.card + 2 ^ (j / 3 + 1) ∧
        ∀ u ∈ A', ∀ v ∈ A', v < u → 2 ^ (j / 3 + 1) < u - v :=
      fun j => sidon_thin_small_diffs (B_raw j) (hBSid j) (2 ^ (j / 3 + 1))
    let B' : ℕ → Finset ℕ := fun j => Classical.choose (hthin j)
    have hB'sub : ∀ j, B' j ⊆ B_raw j := fun j => (Classical.choose_spec (hthin j)).1
    have hB'card : ∀ j, (B_raw j).card ≤ (B' j).card + 2 ^ (j / 3 + 1) :=
      fun j => (Classical.choose_spec (hthin j)).2.1
    have hB'gap : ∀ j, ∀ u ∈ B' j, ∀ v ∈ B' j, v < u → 2 ^ (j / 3 + 1) < u - v :=
      fun j => (Classical.choose_spec (hthin j)).2.2
    let B : Finset ℕ := (Finset.range (K + 1)).biUnion (fun j => (B' j).image E)
    refine ⟨B, ?_, ?_⟩
    · exact coded_blocks_isSidon
        (fun j => (hB'sub j).trans (hBIco j))
        (fun j => fun a ha b hb c hc d hd h =>
          hBSid j a (hB'sub j ha) b (hB'sub j hb) c (hB'sub j hc) d (hB'sub j hd) h)
        hB'gap
        (fun i j h1 h2 a ha b hb u hu v hv =>
          hBCross i j h1 h2 a (hB'sub i ha) b (hB'sub i hb) u (hB'sub j hu) v (hB'sub j hv))
        hE
    · intro n hnK
      by_cases hTJ : T J ≤ n
      · have hf_eq : f n = g (jn n) - 2 ^ (jn n / 3 + 1) := if_pos hTJ
        rw [hf_eq]
        obtain ⟨hJle, hTle, _⟩ := hjn_spec n hTJ
        have hjnK : jn n ≤ K := by have := hT_ge (jn n); omega
        have hsub : (((B' (jn n)).image E : Finset ℕ) : Set ℕ) ⊆ (Set.Icc 1 n) ∩ (B : Set ℕ) := by
          intro x hx
          simp only [Finset.mem_coe, Finset.mem_image] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          have haIco := hBIco (jn n) (hB'sub (jn n) ha)
          have hEb := hEbound (jn n) a haIco
          refine ⟨⟨hEb.1, hEb.2.trans hTle⟩, ?_⟩
          simp only [B, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
          exact ⟨jn n, by omega, a, ha, rfl⟩
        have hcard_le : ((B' (jn n)).image E).card ≤ ((Set.Icc 1 n) ∩ (B : Set ℕ)).ncard := by
          have hfin : ((Set.Icc 1 n) ∩ (B : Set ℕ)).Finite :=
            (Finset.finite_toSet B).subset Set.inter_subset_right
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hsub hfin
        have himg_eq : ((B' (jn n)).image E).card = (B' (jn n)).card :=
          Finset.card_image_of_injective _ (encoder_injective hE)
        have hraw := hBcard (jn n) hJle hjnK
        have hth := hB'card (jn n)
        omega
      · simp only [f, if_neg hTJ]
        exact Nat.zero_le _

end OMA.R_Erdos39_erdos_39_R1_H1_R1
