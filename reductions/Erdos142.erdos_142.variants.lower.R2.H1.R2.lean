import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R2 of step Erdos142.erdos_142.variants.lower.R2.H1
-- Credit: @stochastic-parrot-ftw

/-!
# Reciprocal progressions on 4-adic blocks via shift covering and monochromatic progressions

The target is step `H1` of reduction `R2` of Erdős 142: every set `A` supported on the blocks
`(4 * 4 ^ j, 5 * 4 ^ j]` with divergent reciprocal sum contains `k`-term progressions of positive
step for every `k ≥ 3`.

Whereas reduction `R2.H1.R1` routes through summability of the extremal numbers `r_k(4 ^ j) / 4 ^ j`,
this reduction takes the direct Ramsey / shift-covering route (cf. Fox–Hunter 2026; OpenAI 2026,
*Quasipolynomial Bounds for Arithmetic Progressions*, Section 1.4, Eq. 1.3), avoiding `Erdos142.r`
altogether in the hypotheses:

- `H1` (elementary combinatorics + p-series comparison): if `A` is supported on the 4-adic blocks
  and has divergent reciprocal sum, then for infinitely many scales `4 ^ j`, polylogarithmically
  many shifts `q_j = (⌈log (4 ^ j)⌉₊ + 1) ^ 4` of the shifted block slice
  `{b ∈ [1, 4 ^ j] | 4 * 4 ^ j + b ∈ A}` cover `[4 ^ j + 1, 2 * 4 ^ j]`.
- `H2` (known three-term case): eventually every `q_j`-coloring of `[1, 4 ^ j]` contains a
  monochromatic 3-term progression (follows from Kelley–Meka via the pigeonhole lemma
  `monochromatic_ap_of_r_lt` proved below).
- `H3` (long-progression Ramsey core): for each `k ≥ 4`, eventually every `q_j`-coloring of
  `[1, 4 ^ j]` contains a monochromatic `k`-term progression.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2

open Erdos142 Filter

/-- Divergent reciprocal sum on the 4-adic blocks produces arbitrarily large scales `4 ^ j`
where polylogarithmically many shifts of the block slice cover `[4 ^ j + 1, 2 * 4 ^ j]`. -/
def H1 : Prop :=
  ∀ A : Set ℕ, (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    ¬ Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) →
    ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧
      ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
        ∀ x ∈ Finset.Icc 1 (4 ^ j),
          ∃ t : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
            ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b

/-- Three-term monochromatic progressions on `[1, 4 ^ j]` with polylogarithmically many colors. -/
def H2 : Prop :=
  ∀ᶠ j : ℕ in Filter.atTop,
    ∀ c : ℕ → Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
      ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ Finset.Icc 1 (4 ^ j) ∧ c (a + i * d) = c a

/-- Monochromatic progressions of each fixed length `k ≥ 4` on `[1, 4 ^ j]` with
polylogarithmically many colors. -/
def H3 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ j : ℕ in Filter.atTop,
    ∀ c : ℕ → Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 (4 ^ j) ∧ c (a + i * d) = c a

lemma isAPOfLengthFree_iff {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (show 1 < k by omega)
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

/-- Pigeonhole bridge from extremal progression-free bounds (`r k N`) to monochromatic
progressions (`H2`/`H3`): whenever `q * r k N < N`, every `q`-coloring of `[1, N]`
contains a monochromatic `k`-term progression. -/
theorem monochromatic_ap_of_r_lt {k N q : ℕ} (hk : 2 ≤ k) (hr : q * r k N < N)
    (c : ℕ → Fin q) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
  by_contra hno
  let F : Fin q → Finset ℕ := fun t => (Finset.Icc 1 N).filter (fun x => c x = t)
  have hF_le : ∀ t : Fin q, (F t).card ≤ r k N := by
    intro t
    apply OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard (Finset.filter_subset _ _)
    rw [isAPOfLengthFree_iff hk]
    rintro ⟨a, d, hd, hmem⟩
    have ha0 := Finset.mem_filter.mp (hmem 0 (by omega))
    simp only [zero_mul, add_zero] at ha0
    refine hno ⟨a, d, hd, fun i hi => ?_⟩
    have hiF := Finset.mem_filter.mp (hmem i hi)
    exact ⟨hiF.1, hiF.2.trans ha0.2.symm⟩
  have hpart : (Finset.Icc 1 N).card = ∑ t : Fin q, (F t).card := by
    simpa [F] using
      (Finset.card_eq_sum_card_fiberwise
        (f := c) (s := Finset.Icc 1 N) (t := Finset.univ)
        (fun x _ => Finset.mem_univ (c x)))
  have hsum : ∑ t : Fin q, (F t).card ≤ q * r k N := by
    calc
      ∑ t : Fin q, (F t).card ≤ ∑ _t : Fin q, r k N := Finset.sum_le_sum fun t _ => hF_le t
      _ = q * r k N := by simp
  have hcard : (Finset.Icc 1 N).card = N := Nat.card_Icc 1 N
  omega

/-- Extracting a `k`-term progression in `A` from a shift cover of `[4 ^ j + 1, 2 * 4 ^ j]`
by the `j`-th block slice of `A` and a monochromatic `k`-term progression on `[1, 4 ^ j]`. -/
lemma ap_in_block_of_shift_cover {A : Set ℕ} {k j q : ℕ} (hk : 3 ≤ k) (hq : 0 < q)
    (hmono : ∀ c : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧
      ∀ i < k, a + i * d ∈ Finset.Icc 1 (4 ^ j) ∧ c (a + i * d) = c a)
    (shifts : Fin q → ℕ)
    (hcover : ∀ x ∈ Finset.Icc 1 (4 ^ j),
      ∃ t : Fin q, ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  classical
  let color (x : ℕ) : Fin q :=
    if hx : x ∈ Finset.Icc 1 (4 ^ j) then (hcover x hx).choose else ⟨0, hq⟩
  have color_spec (x : ℕ) (hx : x ∈ Finset.Icc 1 (4 ^ j)) :
      ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts (color x) + b := by
    simpa only [color, dif_pos hx] using (hcover x hx).choose_spec
  obtain ⟨a, d, hd, hap⟩ := hmono color
  have ha : a ∈ Finset.Icc 1 (4 ^ j) := by simpa using (hap 0 (by omega)).1
  obtain ⟨b₀, -, _, hbase⟩ := color_spec a ha
  refine ⟨4 * 4 ^ j + b₀, d, hd, fun i hi => ?_⟩
  obtain ⟨bi, -, hbiA, hshift⟩ := color_spec (a + i * d) (hap i hi).1
  rw [(hap i hi).2] at hshift
  have hbi : b₀ + i * d = bi := by omega
  have hterm : 4 * 4 ^ j + b₀ + i * d = 4 * 4 ^ j + bi := by omega
  rwa [hterm]

theorem main : H1 → H2 → H3 → OMA.R_Erdos142_erdos_142_variants_lower_R2.H1 := by
  intro h1 h2 h3 A hA hns k hk
  have hramsey : ∀ᶠ j : ℕ in Filter.atTop,
      ∀ c : ℕ → Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
        ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 (4 ^ j) ∧ c (a + i * d) = c a := by
    rcases eq_or_lt_of_le hk with rfl | hk4
    · exact h2
    · exact h3 k hk4
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hramsey
  obtain ⟨j, hjJ, shifts, hcover⟩ := h1 A hA hns J
  have hq : 0 < (⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4 := by positivity
  exact ap_in_block_of_shift_cover hk hq (hJ j hjJ) shifts hcover

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
