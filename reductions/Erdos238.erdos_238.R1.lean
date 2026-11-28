import FormalConjectures.ErdosProblems.«238»

-- Reduction Erdos238.erdos_238.R1 of Erdős Problem 238
-- Credit: @jared-jasinski
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos238_erdos_238_R1

def H1 : Prop :=
  ∀ A > (0 : ℝ), ∀ c > (0 : ℝ), c < A → ∀ δ > (0 : ℝ),
    ∀ᶠ (x : ℝ) in Filter.atTop,
      let N := ⌊x⌋₊
      let T := ⌊A * (Real.log x) ^ 2⌋₊
      let U := Finset.Ico (N / 2) (N - T)
      (((U.filter (fun u =>
        ((Finset.Icc u (u + T)).filter Nat.Prime).card ≤ ⌊c * Real.log x⌋₊)).card : ℝ)
        < δ * (U.card : ℝ))

def H2 : Prop :=
  ∀ A > (0 : ℝ), ∀ c₂ : ℕ, 0 < c₂ → ∃ δ > (0 : ℝ),
    ∀ᶠ (x : ℝ) in Filter.atTop,
      let N := ⌊x⌋₊
      let T := ⌊A * (Real.log x) ^ 2⌋₊
      let U := Finset.Ico (N / 2) (N - T)
      δ * (U.card : ℝ) ≤
        ((U.filter (fun u =>
          ∀ p ∈ Finset.Icc u (u + T), ∀ q ∈ Finset.Icc u (u + T),
            p.Prime → q.Prime → p < q → c₂ < q - p)).card : ℝ)

lemma nth_mem_primes_in_Icc (u T : ℕ)
    (hP : ((Finset.Icc u (u + T)).filter Nat.Prime).Nonempty) :
    let P := (Finset.Icc u (u + T)).filter Nat.Prime
    let m := Nat.count Nat.Prime (P.min' hP)
    ∀ i < P.card, Nat.nth Nat.Prime (m + i) ∈ P := by
  intro P m i hi
  set p₀ := P.min' hP
  set p₁ := P.max' hP
  set M := Nat.count Nat.Prime p₁
  have hp₀_mem : p₀ ∈ P := Finset.min'_mem P hP
  have hp₁_mem : p₁ ∈ P := Finset.max'_mem P hP
  have hp₀_prime : p₀.Prime := (Finset.mem_filter.mp hp₀_mem).2
  have hp₁_prime : p₁.Prime := (Finset.mem_filter.mp hp₁_mem).2
  have hp₀_Icc : u ≤ p₀ ∧ p₀ ≤ u + T := Finset.mem_Icc.mp (Finset.mem_filter.mp hp₀_mem).1
  have hp₁_Icc : u ≤ p₁ ∧ p₁ ≤ u + T := Finset.mem_Icc.mp (Finset.mem_filter.mp hp₁_mem).1
  have hnth_m : Nat.nth Nat.Prime m = p₀ := Nat.nth_count hp₀_prime
  have hnth_M : Nat.nth Nat.Prime M = p₁ := Nat.nth_count hp₁_prime
  have hP_eq : P = (Finset.Icc m M).image (Nat.nth Nat.Prime) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hq
      have hq_prime : q.Prime := (Finset.mem_filter.mp hq).2
      have hq_ge : p₀ ≤ q := Finset.min'_le P q hq
      have hq_le : q ≤ p₁ := Finset.le_max' P q hq
      refine ⟨Nat.count Nat.Prime q, ⟨?_, ?_⟩, Nat.nth_count hq_prime⟩
      · exact Nat.count_monotone Nat.Prime hq_ge
      · exact Nat.count_monotone Nat.Prime hq_le
    · rintro ⟨j, ⟨hmj, hjM⟩, rfl⟩
      have hmono := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone
      have h1 : p₀ ≤ Nat.nth Nat.Prime j := by rw [← hnth_m]; exact hmono hmj
      have h2 : Nat.nth Nat.Prime j ≤ p₁ := by rw [← hnth_M]; exact hmono hjM
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j
  have hcard : P.card = M + 1 - m := by
    rw [hP_eq, Finset.card_image_of_injective _ (Nat.nth_strictMono Nat.infinite_setOf_prime).injective,
      Nat.card_Icc]
  have hm_le_M : m ≤ M := Nat.count_monotone Nat.Prime (Finset.min'_le P p₁ hp₁_mem)
  rw [hP_eq]
  exact Finset.mem_image.mpr ⟨m + i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩

theorem main : H1 → H2 → type_of% @Erdos238.erdos_238 := by
  intro hH1 hH2 c₁ hc₁ c₂ hc₂
  set A : ℝ := 2 * c₁
  have hA_pos : 0 < A := by positivity
  have hc₁_lt_A : c₁ < A := by linarith
  obtain ⟨δ, hδ_pos, h2⟩ := hH2 A hA_pos c₂ hc₂
  have h1 := hH1 A hA_pos c₁ hc₁ hc₁_lt_A δ hδ_pos
  filter_upwards [h1, h2, Filter.eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx_ge1
  set N := ⌊x⌋₊
  set T := ⌊A * (Real.log x) ^ 2⌋₊
  set U := Finset.Ico (N / 2) (N - T)
  set bad := U.filter (fun u =>
    ((Finset.Icc u (u + T)).filter Nat.Prime).card ≤ ⌊c₁ * Real.log x⌋₊)
  set good := U.filter (fun u =>
    ∀ p ∈ Finset.Icc u (u + T), ∀ q ∈ Finset.Icc u (u + T),
      p.Prime → q.Prime → p < q → c₂ < q - p)
  have hcard_lt : bad.card < good.card := by
    have hreal : (bad.card : ℝ) < (good.card : ℝ) := lt_of_lt_of_le hx1 hx2
    exact_mod_cast hreal
  have hex : ∃ u ∈ good, u ∉ bad := by
    by_contra hall
    push_neg at hall
    have hsub : good ⊆ bad := fun u hu => hall u hu
    have hle : good.card ≤ bad.card := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu_good, hu_not_bad⟩ := hex
  have hu_U : u ∈ U := (Finset.mem_filter.mp hu_good).1
  have hu_gap : ∀ p ∈ Finset.Icc u (u + T), ∀ q ∈ Finset.Icc u (u + T),
      p.Prime → q.Prime → p < q → c₂ < q - p := (Finset.mem_filter.mp hu_good).2
  set P := (Finset.Icc u (u + T)).filter Nat.Prime
  have hP_gt_floor : ⌊c₁ * Real.log x⌋₊ < P.card := by
    by_contra hle
    push_neg at hle
    exact hu_not_bad (Finset.mem_filter.mpr ⟨hu_U, hle⟩)
  have hP_gt : c₁ * Real.log x < (P.card : ℝ) := by
    have hlt := Nat.lt_floor_add_one (c₁ * Real.log x)
    have hsucc : (⌊c₁ * Real.log x⌋₊ : ℝ) + 1 ≤ (P.card : ℝ) := by exact_mod_cast hP_gt_floor
    linarith
  have hP_ne : P.Nonempty := Finset.card_pos.mp (by omega)
  set m := Nat.count Nat.Prime (P.min' hP_ne)
  have hmem := nth_mem_primes_in_Icc u T hP_ne
  refine ⟨P.card, hP_gt, fun i => Nat.nth Nat.Prime (m + i.1), m, ?_, ?_⟩
  · intro i
    refine ⟨?_, rfl⟩
    have hi_mem : Nat.nth Nat.Prime (m + i.1) ∈ P := hmem i.1 i.2
    have hi_le : Nat.nth Nat.Prime (m + i.1) ≤ u + T :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hi_mem).1).2
    have hu_lt : u < N - T := (Finset.mem_Ico.mp hu_U).2
    have hle_N : Nat.nth Nat.Prime (m + i.1) ≤ N := by omega
    have hN_le_x : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    exact le_trans (by exact_mod_cast hle_N) hN_le_x
  · intro i
    have hi1 : i.1 < P.card := by omega
    have hi2 : i.1 + 1 < P.card := by omega
    have hp_mem : Nat.nth Nat.Prime (m + i.1) ∈ P := hmem i.1 hi1
    have hq_mem : Nat.nth Nat.Prime (m + (i.1 + 1)) ∈ P := hmem (i.1 + 1) hi2
    have hp_Icc : Nat.nth Nat.Prime (m + i.1) ∈ Finset.Icc u (u + T) :=
      (Finset.mem_filter.mp hp_mem).1
    have hp_prime : (Nat.nth Nat.Prime (m + i.1)).Prime :=
      (Finset.mem_filter.mp hp_mem).2
    have hq_Icc : Nat.nth Nat.Prime (m + i.1 + 1) ∈ Finset.Icc u (u + T) := by
      simpa [Nat.add_assoc] using (Finset.mem_filter.mp hq_mem).1
    have hq_prime : (Nat.nth Nat.Prime (m + i.1 + 1)).Prime := by
      simpa [Nat.add_assoc] using (Finset.mem_filter.mp hq_mem).2
    have hlt : Nat.nth Nat.Prime (m + i.1) < Nat.nth Nat.Prime (m + i.1 + 1) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
    exact hu_gap _ hp_Icc _ hq_Icc hp_prime hq_prime hlt

end OMA.R_Erdos238_erdos_238_R1
