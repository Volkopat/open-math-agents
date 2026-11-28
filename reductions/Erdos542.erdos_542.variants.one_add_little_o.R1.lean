import FormalConjectures.ErdosProblems.«542»

-- Reduction Erdos542.erdos_542.variants.one_add_little_o.R1 of Erdős Problem 542 — one plus little o
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The `1 + o(1)` bound, split by the smallest member

Let `A ⊆ {1, …, n}` with `lcm(a, b) > n` for distinct `a, b ∈ A`. The target says that
`∑ 1/a ≤ 1 + o(1)` as `n → ∞`, uniformly in `A`.

Two members `a, b ≤ √n` would have `lcm(a, b) ≤ a * b ≤ n`, so `A` has at most one member
`s ≤ √n`. `main` splits by this member.

* `1 ∈ A`: then `A = {1}`. Proved here.
* `2 ∈ A`, `n ≥ 6`: `∑ 1/a ≤ 1`. Proved here.
* `3 ∈ A`, `n ≥ 12`: `∑ 1/a ≤ 1`, from the numerical inequality `H1`.
* `s ∈ A` for a fixed `s ≥ 4`: this is `H2`, with an error term that may depend on `s`.
* `s ∈ A` with `s` large: remove `s`. The rest has no member up to `√n`, so `H3` bounds it, and
  `1 / s` is small. This step is why `H2` needs no uniformity in `s`.
* no member up to `√n`: this is `H3`.

`H1` is word for word `H1` of the merged reduction `Erdos542.erdos_542.variants.only_two.R1`,
which is proved upstream. The lemmas `odd_half_small` to `three_mem_bound` are taken from that
reduction (credit: @ivillar). `H2` and `H3` are special cases of the target. Both are open.
-/

namespace OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R1

/-- The numerical inequality behind the case `3 ∈ A`: for `n ≥ 12`, the reciprocals of the
non-multiples of `3` in `(n / 2, n]`, plus half the reciprocals of the non-multiples of `3` in
`(n / 3, n / 2]`, sum to at most `2 / 3`. Elementary. It is `H1` of
`Erdos542.erdos_542.variants.only_two.R1`, proved upstream. -/
def H1 : Prop :=
  ∀ n : ℕ, 12 ≤ n →
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) ≤ 2 / 3

/-- The target for sets with a fixed member `s ≥ 4`. The error term may depend on `s`. -/
def H2 : Prop :=
  ∀ s : ℕ, 4 ≤ s → ∃ o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (nhds 0) ∧
    ∀ (n : ℕ) (A : Finset ℕ), Erdos542.IsLcmFree n A → s ∈ A →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + o n

/-- The target for sets without a small member: every member of `A` exceeds `√n`. -/
def H3 : Prop :=
  ∃ o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (nhds 0) ∧
    ∀ (n : ℕ) (A : Finset ℕ), Erdos542.IsLcmFree n A → (∀ a ∈ A, n < a * a) →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + o n

/-- Kernel computation: the odd integers in `(n / 2, n]` have reciprocal sum at most `1 / 2`,
for `6 ≤ n ≤ 63`. -/
lemma odd_half_small : ∀ n ∈ Finset.Icc (6 : ℕ) 63,
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℚ) / (b : ℚ) ≤ 1 / 2 := by
  decide +kernel

/-- The same bound for `n ≥ 64`, splitting `(n / 2, n]` at `3 n / 4`. -/
lemma odd_half_large {n : ℕ} (hn : 64 ≤ n) :
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℝ) / b ≤ 1 / 2 := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b) :=
    ⟨_, rfl⟩
  rw [← hS]
  have hmem : ∀ b ∈ S, 1 ≤ b ∧ b ≤ n ∧ b % 2 = 1 ∧ n < 2 * b := by
    intro b hb
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hb
    exact ⟨hb.1.1, hb.1.2, hb.2.1, hb.2.2⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : ∑ b ∈ S.filter (fun b => 4 * b ≤ 3 * n), (1 : ℝ) / b ≤
      ((S.filter (fun b => 4 * b ≤ 3 * n)).card : ℝ) * (2 / n) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro b hb
    have hb' := hmem b (Finset.mem_filter.mp hb).1
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_le_div_iff₀ hbR hnR]
    have hle : (n : ℝ) ≤ 2 * b := by exact_mod_cast (by omega : n ≤ 2 * b)
    linarith
  have h2 : ∑ b ∈ S.filter (fun b => ¬ 4 * b ≤ 3 * n), (1 : ℝ) / b ≤
      ((S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card : ℝ) * (4 / (3 * n)) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro b hb
    have hb1 := Finset.mem_filter.mp hb
    have hb' := hmem b hb1.1
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_le_div_iff₀ hbR (by positivity)]
    have hle : (3 * n : ℝ) ≤ 4 * b := by exact_mod_cast (by omega : 3 * n ≤ 4 * b)
    linarith
  have c1 : 8 * (S.filter (fun b => 4 * b ≤ 3 * n)).card ≤ n + 14 := by
    have hc : (S.filter (fun b => 4 * b ≤ 3 * n)).card ≤ (Finset.Icc (n / 4) (3 * n / 8)).card := by
      apply Finset.card_le_card_of_injOn (fun b => b / 2)
      · intro b hb
        have hb1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have hb' := hmem b hb1.1
        have hb2 := hb1.2
        have hI : b / 2 ∈ Finset.Icc (n / 4) (3 * n / 8) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact Finset.mem_coe.mpr hI
      · intro b hb c hc hbc
        have hb1 := hmem b (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
        have hc1 := hmem c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).1
        have hbc' : b / 2 = c / 2 := hbc
        omega
    rw [Nat.card_Icc] at hc
    omega
  have c2 : 8 * (S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card ≤ n + 11 := by
    have hc : (S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card ≤
        (Finset.Icc (3 * n / 8) ((n - 1) / 2)).card := by
      apply Finset.card_le_card_of_injOn (fun b => b / 2)
      · intro b hb
        have hb1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have hb' := hmem b hb1.1
        have hb2 := hb1.2
        have hI : b / 2 ∈ Finset.Icc (3 * n / 8) ((n - 1) / 2) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact Finset.mem_coe.mpr hI
      · intro b hb c hc hbc
        have hb1 := hmem b (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
        have hc1 := hmem c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).1
        have hbc' : b / 2 = c / 2 := hbc
        omega
    rw [Nat.card_Icc] at hc
    omega
  have c1R : (8 : ℝ) * ((S.filter (fun b => 4 * b ≤ 3 * n)).card : ℝ) ≤ n + 14 := by
    exact_mod_cast c1
  have c2R : (8 : ℝ) * ((S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card : ℝ) ≤ n + 11 := by
    exact_mod_cast c2
  have hn64 : (64 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Finset.sum_filter_add_sum_filter_not S (fun b => 4 * b ≤ 3 * n)]
  have key : ∀ x y : ℝ, x * (2 / n) + y * (4 / (3 * n)) = (6 * x + 4 * y) / (3 * n) := by
    intro x y
    field_simp
    ring
  have hfin : ((S.filter (fun b => 4 * b ≤ 3 * n)).card : ℝ) * (2 / n) +
      ((S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card : ℝ) * (4 / (3 * n)) ≤ 1 / 2 := by
    rw [key, div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- The odd integers in `(n / 2, n]` have reciprocal sum at most `1 / 2`, for every `n ≥ 6`. -/
lemma odd_half {n : ℕ} (hn : 6 ≤ n) :
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℝ) / b ≤ 1 / 2 := by
  by_cases h : n ≤ 63
  · have hq := odd_half_small n (Finset.mem_Icc.mpr ⟨hn, h⟩)
    have hr : ((∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b),
        (1 : ℚ) / (b : ℚ) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    push_cast at hr
    exact hr
  · exact odd_half_large (by omega)

/-- The bound `∑ 1/a ≤ 1` for every `n ≥ 6` when `2 ∈ A`. -/
lemma two_mem {n : ℕ} {A : Finset ℕ} (hn : 6 ≤ n) (hA : Erdos542.IsLcmFree n A) (h2 : 2 ∈ A) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ 1 := by
  have hsub : A.erase 2 ⊆ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b) := by
    intro b hb
    obtain ⟨hb2, hbA⟩ := Finset.mem_erase.mp hb
    have hbI := Finset.mem_Icc.mp (hA.1 hbA)
    have hl : n < Nat.lcm 2 b := hA.2 h2 hbA (Ne.symm hb2)
    have hodd : b % 2 = 1 := by
      by_contra hne
      have hd : 2 ∣ b := by omega
      have hle : Nat.lcm 2 b ≤ b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd hd (dvd_refl b))
      omega
    have hle : Nat.lcm 2 b ≤ 2 * b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd_mul 2 b)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hbI, hodd, by omega⟩
  have h := odd_half hn
  have hmono : ∑ b ∈ A.erase 2, (1 : ℝ) / b ≤
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℝ) / b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
  rw [← Finset.add_sum_erase A _ h2]
  have e : (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [e]
  linarith

/-- The case `3 ∈ A`, reduced to a sum that does not depend on `A`. Every other member `b`
satisfies `3 ∤ b` and `b > n / 3`, and `A` contains no pair `b, 2 b`. Give weight `1 / m` to each
`m` in `(n / 2, n]` and `1 / (2 b)` to each `b` in `(n / 3, n / 2]`: a member `b > n / 2` is paid
by its own weight, a member `b ≤ n / 2` by its weight and that of `2 b`, and no integer pays
twice. -/
lemma three_mem_bound {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) (h3 : 3 ∈ A) :
    ∑ b ∈ A.erase 3, (1 : ℝ) / b ≤
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
        ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
          (1 : ℝ) / (2 * b) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B = A.erase 3 := ⟨_, rfl⟩
  rw [← hB]
  have hmem : ∀ b ∈ B, b ∈ A ∧ 1 ≤ b ∧ b ≤ n ∧ b % 3 ≠ 0 ∧ n < 3 * b := by
    intro b hb
    rw [hB] at hb
    obtain ⟨hb3, hbA⟩ := Finset.mem_erase.mp hb
    have hbI := Finset.mem_Icc.mp (hA.1 hbA)
    have hl : n < Nat.lcm 3 b := hA.2 h3 hbA (Ne.symm hb3)
    have hnd : b % 3 ≠ 0 := by
      intro h0
      have hd : 3 ∣ b := Nat.dvd_of_mod_eq_zero h0
      have hle : Nat.lcm 3 b ≤ b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd hd (dvd_refl b))
      omega
    have hle : Nat.lcm 3 b ≤ 3 * b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd_mul 3 b)
    exact ⟨hbA, hbI.1, hbI.2, hnd, by omega⟩
  have hnodouble : ∀ b ∈ B, 2 * b ∉ B := by
    intro b hb h2b
    have hb' := hmem b hb
    have h2b' := hmem (2 * b) h2b
    have hne : b ≠ 2 * b := by omega
    have hl : n < Nat.lcm b (2 * b) := hA.2 hb'.1 h2b'.1 hne
    have hle : Nat.lcm b (2 * b) ≤ 2 * b :=
      Nat.le_of_dvd (by omega) (Nat.lcm_dvd (Dvd.intro_left 2 rfl) (dvd_refl _))
    omega
  obtain ⟨Bh, hBh⟩ : ∃ Bh : Finset ℕ, Bh = B.filter (fun b => n < 2 * b) := ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl : Finset ℕ, Bl = B.filter (fun b => ¬ n < 2 * b) := ⟨_, rfl⟩
  have hsplit : ∑ b ∈ Bh, (1 : ℝ) / b + ∑ b ∈ Bl, (1 : ℝ) / b = ∑ b ∈ B, (1 : ℝ) / b := by
    rw [hBh, hBl]
    exact Finset.sum_filter_add_sum_filter_not B (fun b => n < 2 * b) (fun b => (1 : ℝ) / b)
  have hBlmem : ∀ b ∈ Bl, b ∈ B ∧ 2 * b ≤ n := by
    intro b hb
    rw [hBl, Finset.mem_filter] at hb
    exact ⟨hb.1, by omega⟩
  have hBhmem : ∀ b ∈ Bh, b ∈ B ∧ n < 2 * b := by
    intro b hb
    rw [hBh, Finset.mem_filter] at hb
    exact hb
  obtain ⟨D, hD⟩ : ∃ D : Finset ℕ, D = Bl.image (fun b : ℕ => 2 * b) := ⟨_, rfl⟩
  have hlow : ∑ b ∈ Bl, (1 : ℝ) / b =
      ∑ m ∈ D, (1 : ℝ) / (m : ℝ) + ∑ b ∈ Bl, (1 : ℝ) / (2 * b) := by
    rw [hD, Finset.sum_image (fun x _ y _ (h : 2 * x = 2 * y) => by omega),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' := hmem b (hBlmem b hb).1
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    push_cast
    field_simp
    ring
  have hDmem : ∀ m ∈ D, ∃ b ∈ Bl, m = 2 * b := by
    intro m hm
    rw [hD] at hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨b, hb, rfl⟩
  have hdisj : Disjoint Bh D := by
    rw [Finset.disjoint_left]
    intro m hm hm2
    obtain ⟨b, hb, rfl⟩ := hDmem m hm2
    exact hnodouble b (hBlmem b hb).1 (hBhmem _ hm).1
  have hsub1 : Bh ∪ D ⊆ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0) := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have h1 := hBhmem m hm
      have h2 := hmem m h1.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h2.2.1, h2.2.2.1⟩, h1.2, h2.2.2.2.1⟩
    · obtain ⟨b, hb, rfl⟩ := hDmem m hm
      have h1 := hBlmem b hb
      have h2 := hmem b h1.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, by omega, by omega⟩
  have hsub2 : Bl ⊆ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) := by
    intro b hb
    have h1 := hBlmem b hb
    have h2 := hmem b h1.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h2.2.1, h2.2.2.1⟩, h2.2.2.2.2, h1.2, h2.2.2.2.1⟩
  have hle1 : ∑ m ∈ Bh, (1 : ℝ) / (m : ℝ) + ∑ m ∈ D, (1 : ℝ) / (m : ℝ) ≤
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun m _ _ => by positivity)
  have hle2 : ∑ b ∈ Bl, (1 : ℝ) / (2 * b) ≤
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun b _ _ => by positivity)
  linarith

/-- If `1 ∈ A` then `A = {1}`. -/
lemma one_mem {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) (h1 : 1 ∈ A) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ 1 := by
  have hA1 : A = {1} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨h1, fun b hb => ?_⟩
    by_contra hne
    have hl : n < Nat.lcm 1 b := hA.2 h1 hb (Ne.symm hne)
    rw [Nat.lcm_one_left] at hl
    have := (Finset.mem_Icc.mp (hA.1 hb)).2
    omega
  rw [hA1]
  simp

/-- Removing a member keeps the lcm condition. -/
lemma erase_lcmFree {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) (s : ℕ) :
    Erdos542.IsLcmFree n (A.erase s) :=
  ⟨(Finset.erase_subset s A).trans hA.1,
    hA.2.mono (Finset.coe_subset.mpr (Finset.erase_subset s A))⟩

/-- A set has at most one member up to `√n`. -/
lemma small_unique {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) {s : ℕ} (hs : s ∈ A)
    (hss : s * s ≤ n) : ∀ b ∈ A.erase s, n < b * b := by
  intro b hb
  obtain ⟨hbs, hbA⟩ := Finset.mem_erase.mp hb
  by_contra hc
  have hbb : b * b ≤ n := by omega
  have hs1 := (Finset.mem_Icc.mp (hA.1 hs)).1
  have hb1 := (Finset.mem_Icc.mp (hA.1 hbA)).1
  have hl : n < Nat.lcm s b := hA.2 hs hbA (Ne.symm hbs)
  have hle : Nat.lcm s b ≤ s * b :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul s b)
  have hsb : s * b ≤ n := by
    rcases le_total s b with h | h
    · exact le_trans (Nat.mul_le_mul_right b h) hbb
    · exact le_trans (Nat.mul_le_mul_left s h) hss
  omega

/-- A crude bound for every `n`: the sum has at most `n` terms, each at most `1`. -/
lemma sum_le_nat {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ n := by
  have h1 : ∑ a ∈ A, (1 : ℝ) / a ≤ ∑ _a ∈ A, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp (hA.1 ha)).1
    rw [div_le_one (by linarith)]
    exact ha1
  have h2 : A.card ≤ n := by
    have := Finset.card_le_card hA.1
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  have h3 : ((A.card : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  linarith

/-- The target follows from its `ε`-`N` form: take `o n` to be the largest excess over `1`. -/
lemma exists_o (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ A : Finset ℕ,
    Erdos542.IsLcmFree n A → ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + ε) :
    type_of% @Erdos542.erdos_542.variants.one_add_little_o := by
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Set ℝ, S = fun n =>
      {x | ∃ A : Finset ℕ, Erdos542.IsLcmFree n A ∧ ∑ a ∈ A, (1 : ℝ) / a - 1 = x} := ⟨_, rfl⟩
  have hmem : ∀ n x, x ∈ S n ↔
      ∃ A : Finset ℕ, Erdos542.IsLcmFree n A ∧ ∑ a ∈ A, (1 : ℝ) / a - 1 = x := by
    intro n x
    rw [hS]
    rfl
  have hbdd : ∀ n, BddAbove (S n) := by
    intro n
    refine ⟨n, fun x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := (hmem n x).mp hx
    have := sum_le_nat hA
    linarith
  have hne : ∀ n, (S n).Nonempty := by
    intro n
    exact ⟨_, (hmem n _).mpr ⟨∅, ⟨Finset.empty_subset _, by simp⟩, rfl⟩⟩
  refine ⟨fun n => max 0 (sSup (S n)), ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hsup : sSup (S n) ≤ ε / 2 := by
      apply csSup_le (hne n)
      intro x hx
      obtain ⟨A, hA, rfl⟩ := (hmem n x).mp hx
      have := hN n hn A hA
      linarith
    have hmax : max 0 (sSup (S n)) ≤ ε / 2 := max_le (by positivity) hsup
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
    linarith
  · intro n A hA
    have h1 : ∑ a ∈ A, (1 : ℝ) / a - 1 ≤ sSup (S n) :=
      le_csSup (hbdd n) ((hmem n _).mpr ⟨A, hA, rfl⟩)
    have h2 : sSup (S n) ≤ max 0 (sSup (S n)) := le_max_right _ _
    linarith

/-- From `H2`: one threshold serves all fixed members `4 ≤ s < T`. -/
lemma fixed_small (h2 : H2) (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ A : Finset ℕ, Erdos542.IsLcmFree n A → ∀ s ∈ A, 4 ≤ s → s < T →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + ε := by
  induction T with
  | zero => exact ⟨0, fun n _ A _ s _ _ hs => absurd hs (Nat.not_lt_zero s)⟩
  | succ T ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hT : 4 ≤ T
    · obtain ⟨o, ho, hb⟩ := h2 T hT
      obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp (ho.eventually (gt_mem_nhds hε))
      refine ⟨max N N', fun n hn A hA s hs hs4 hsT => ?_⟩
      by_cases hsT' : s < T
      · exact hN n (le_trans (le_max_left _ _) hn) A hA s hs hs4 hsT'
      · have hsT'' : s = T := by omega
        rw [hsT''] at hs
        have hb1 := hb n A hA hs
        have hb2 := hN' n (le_trans (le_max_right _ _) hn)
        linarith
    · refine ⟨N, fun n hn A hA s hs hs4 hsT => ?_⟩
      exact hN n hn A hA s hs hs4 (by omega)

theorem main : H1 → H2 → H3 → type_of% @Erdos542.erdos_542.variants.one_add_little_o := by
  intro h1 h2 h3
  obtain ⟨o3, ho3, h3⟩ := h3
  apply exists_o
  intro ε hε
  obtain ⟨T, hT⟩ := exists_nat_gt (2 / ε)
  have hTpos : (0 : ℝ) < T := lt_trans (by positivity) hT
  have hTinv : 1 / (T : ℝ) < ε / 2 := by
    have hmul : 2 < (T : ℝ) * ε := (div_lt_iff₀ hε).mp hT
    rw [div_lt_iff₀ hTpos]
    linarith
  obtain ⟨N2, hN2⟩ := fixed_small h2 T ε hε
  obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.mp (ho3.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max 12 (max N2 N3), fun n hn A hA => ?_⟩
  have hn12 : 12 ≤ n := le_trans (le_max_left _ _) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnN3 : N3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have ho : o3 n < ε / 2 := hN3 n hnN3
  by_cases h2A : 2 ∈ A
  · have := two_mem (by omega) hA h2A
    linarith
  by_cases h3A : 3 ∈ A
  · have hb := three_mem_bound hA h3A
    have hnum := h1 n hn12
    have e : (1 : ℝ) / ((3 : ℕ) : ℝ) = 1 / 3 := by norm_num
    rw [← Finset.add_sum_erase A _ h3A, e]
    linarith
  by_cases hs : ∃ s ∈ A, s * s ≤ n
  · obtain ⟨s, hsA, hss⟩ := hs
    by_cases hsT : s < T
    · by_cases hs1 : s = 1
      · rw [hs1] at hsA
        have := one_mem hA hsA
        linarith
      · have hs0 := (Finset.mem_Icc.mp (hA.1 hsA)).1
        have hs2 : s ≠ 2 := fun h => h2A (h ▸ hsA)
        have hs3 : s ≠ 3 := fun h => h3A (h ▸ hsA)
        exact hN2 n hnN2 A hA s hsA (by omega) hsT
    · have hTs : (T : ℝ) ≤ s := by exact_mod_cast (by omega : T ≤ s)
      have hrest := h3 n (A.erase s) (erase_lcmFree hA s) (small_unique hA hsA hss)
      have hinv : 1 / (s : ℝ) ≤ 1 / (T : ℝ) := one_div_le_one_div_of_le hTpos hTs
      rw [← Finset.add_sum_erase A _ hsA]
      linarith
  · have hs' : ∀ a ∈ A, n < a * a := by
      intro a ha
      by_contra hc
      exact hs ⟨a, ha, by omega⟩
    have := h3 n A hA hs'
    linarith

end OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R1
