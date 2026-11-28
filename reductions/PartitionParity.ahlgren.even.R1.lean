import FormalConjectures.Paper.PartitionParity
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

/-!
# Reduction of `PartitionParity.ahlgren.even`

Following S. Ahlgren (*Distribution of parity of the partition function in arithmetic
progressions*, Indag. Math. 10 (1999), 173–181, Theorem 1(a) and Lemma 3.1(a)), K. Ono
(*Parity of the partition function in arithmetic progressions*, J. Reine Angew. Math. 472 (1996),
1–16, Proposition 1), and J.-P. Serre (1976, Theorem 4.7), we reduce the lower bound
$$\#\{n \le X : n \equiv r \pmod t,\; p(n) \text{ even}\} \gg \sqrt{X}$$
to two independent classical modular-form pillars:
1. `H1`: **Serre's sparsity theorem**: for any level `L > 0`, integer weight `k`, and cusp form
   `F` on `Γ₁(L)` whose `q`-expansion at `∞` has integer coefficients `b : ℕ → ℤ`, the set of
   indices `m` with `Odd (b m)` has natural density `0`.
2. `H2`: **Ono–Ahlgren eta-quotient cusp-form realization**: for every `r < t` (`0 < t`), there
   exist `d > 0`, `L > 0`, `k : ℤ`, and a cusp form `F` on `Γ₁(L)` with integer `q`-expansion `b`
   such that for all `n ≥ 1`, oddness of the odd-square convolution
   `∑_{d(2j+1)^2 ≤ n} p(r + t*(n - d(2j+1)^2))` implies `Odd (b (24 * (r + t * n) - 1))`.

Inside `main`, we prove Ahlgren's Lemma 3.1(a) completely from scratch:
- The disjoint odd-parity bands `Bands d K = ⋃_{q < K} [d(4q+1)^2, d(4q+3)^2)` have exact
  cardinality `8 * d * K^2`, lie in `[1, 16 * d * K^2)`, and each `n ∈ Bands d K` has an odd
  number `2q + 1` of shifts `j` with `d(2j+1)^2 ≤ n`.
- Whenever the convolution at `n ∈ Bands d K` is even, parity forces at least one summand
  `p(r%t + t*(n - d(2j+1)^2))` to be even.
- Subsequence transfer of `H1` via `H2` bounds odd-convolution indices in `Bands d K` by at most
  `4 * d * K^2` for large `K`, leaving at least `4 * d * K^2` even-convolution indices, which
  inject into `E_K × range (2 * K)` to give `2 * d * K ≤ E_K.card` and hence `≫ √X` even values.

Thanks to @MechaNuggan for the odd-square convolution band-counting and `Gamma1` cusp-form
interface notes.
Credit: @tkaiman
-/

namespace OMA.R_PartitionParity_ahlgren_even_R1

open PartitionParity Nat Real Filter Asymptotics Finset
open scoped BigOperators Classical Topology

/- ### Step 1: Odd-cardinality parity extraction and odd-square bands -/

private lemma exists_even_of_even_sum_odd_card {α : Type*} (s : Finset α) (f : α → ℕ)
    (hcard : Odd s.card) (heven : Even (∑ x ∈ s, f x)) : ∃ x ∈ s, Even (f x) := by
  by_contra h
  push Not at h
  have hall : ∀ x ∈ s, Odd (f x) := fun x hx => Nat.not_even_iff_odd.mp (h x hx)
  have hodd : Odd (∑ x ∈ s, f x) := by
    have hmod : (∑ x ∈ s, f x) % 2 = s.card % 2 := by
      have hsum_mod : (∑ x ∈ s, f x) % 2 = (∑ x ∈ s, (f x % 2)) % 2 :=
        Finset.sum_nat_mod s 2 f
      rw [hsum_mod]
      have hone : ∀ x ∈ s, f x % 2 = 1 := fun x hx => Nat.odd_iff.mp (hall x hx)
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
    exact Nat.odd_iff.mpr (hmod.trans (Nat.odd_iff.mp hcard))
  exact (Nat.not_odd_iff_even.mpr heven) hodd

private def bands (d K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion fun q => Finset.Ico (d * (4 * q + 1) ^ 2) (d * (4 * q + 3) ^ 2)

private lemma bands_card (d K : ℕ) : (bands d K).card = 8 * d * K ^ 2 := by
  unfold bands
  have hdisj : Set.PairwiseDisjoint (Finset.range K : Set ℕ)
      (fun q => Finset.Ico (d * (4 * q + 1) ^ 2) (d * (4 * q + 3) ^ 2)) := by
    intro q₁ _ q₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Ico] at hx1 hx2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsq : (4 * q₁ + 3) ^ 2 ≤ (4 * q₂ + 1) ^ 2 := by nlinarith
      have hmul : d * (4 * q₁ + 3) ^ 2 ≤ d * (4 * q₂ + 1) ^ 2 := Nat.mul_le_mul_left d hsq
      omega
    · have hsq : (4 * q₂ + 3) ^ 2 ≤ (4 * q₁ + 1) ^ 2 := by nlinarith
      have hmul : d * (4 * q₂ + 3) ^ 2 ≤ d * (4 * q₁ + 1) ^ 2 := Nat.mul_le_mul_left d hsq
      omega
  rw [Finset.card_biUnion hdisj]
  have hterm : ∀ q ∈ Finset.range K,
      (Finset.Ico (d * (4 * q + 1) ^ 2) (d * (4 * q + 3) ^ 2)).card = 8 * d * (2 * q + 1) := by
    intro q _
    rw [Nat.card_Ico]
    have hdiff : d * (4 * q + 3) ^ 2 - d * (4 * q + 1) ^ 2 = 8 * d * (2 * q + 1) := by
      have : d * (4 * q + 1) ^ 2 + 8 * d * (2 * q + 1) = d * (4 * q + 3) ^ 2 := by ring
      omega
    exact hdiff
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum_odd : ∑ q ∈ Finset.range K, (2 * q + 1) = K ^ 2 := by
    clear hdisj hterm
    induction K with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [hsum_odd]

private lemma mem_bands_bounds {d K n : ℕ} (hd : 0 < d) (hn : n ∈ bands d K) :
    1 ≤ n ∧ n < 16 * d * K ^ 2 := by
  obtain ⟨q, hqK, hqIco⟩ := Finset.mem_biUnion.mp hn
  have hq : q < K := Finset.mem_range.mp hqK
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hqIco
  constructor
  · have : 1 ≤ (4 * q + 1) ^ 2 := by nlinarith
    have : 1 * 1 ≤ d * (4 * q + 1) ^ 2 := Nat.mul_le_mul hd this
    omega
  · have hsq : (4 * q + 3) ^ 2 ≤ (4 * K) ^ 2 := by nlinarith
    have hmul : d * (4 * q + 3) ^ 2 ≤ d * (4 * K) ^ 2 := Nat.mul_le_mul_left d hsq
    have h16 : d * (4 * K) ^ 2 = 16 * d * K ^ 2 := by ring
    omega

private lemma bands_shift_filter_eq {d q n : ℕ} (hd : 0 < d)
    (hlo : d * (4 * q + 1) ^ 2 ≤ n) (hhi : n < d * (4 * q + 3) ^ 2) :
    (Finset.range (n + 1)).filter (fun j => d * (2 * j + 1) ^ 2 ≤ n) = Finset.range (2 * q + 1) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hjle⟩
    by_contra hge
    have hj : 2 * q + 1 ≤ j := by omega
    have hsq : (4 * q + 3) ^ 2 ≤ (2 * j + 1) ^ 2 := by nlinarith
    have hmul : d * (4 * q + 3) ^ 2 ≤ d * (2 * j + 1) ^ 2 := Nat.mul_le_mul_left d hsq
    omega
  · intro hj
    have hsq : (2 * j + 1) ^ 2 ≤ (4 * q + 1) ^ 2 := by nlinarith
    have hmul : d * (2 * j + 1) ^ 2 ≤ d * (4 * q + 1) ^ 2 := Nat.mul_le_mul_left d hsq
    have hj_le_sq : j ≤ (2 * j + 1) ^ 2 := by nlinarith
    have hj_le_d : (2 * j + 1) ^ 2 ≤ d * (2 * j + 1) ^ 2 := Nat.le_mul_of_pos_left _ hd
    exact ⟨by omega, by omega⟩

/- ### Hypotheses and main reduction theorem -/

/-- **Serre's sparsity theorem** (J.-P. Serre 1976, Theorem 4.7; Ahlgren 1999, Lemma 2.2):
for every positive level `L`, integer weight `k`, and cusp form `F` on `Γ₁(L)` whose
`q`-expansion at `∞` has integer coefficients `b : ℕ → ℤ`, the set of indices `n` with `Odd (b n)`
has natural density `0`. -/
def H1 : Prop :=
  ∀ (L : ℕ), 0 < L → ∀ (k : ℤ)
    (F : CuspForm (↑(CongruenceSubgroup.Gamma1 L) : Subgroup (GL (Fin 2) ℝ)) k)
    (b : ℕ → ℤ),
    (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff n = (b n : ℂ)) →
    Tendsto
      (fun N : ℕ => (((Finset.range (N + 1)).filter (fun n => Odd (b n))).card : ℝ) / (N : ℝ))
      atTop (𝓝 0)

/-- **Ono–Ahlgren eta-quotient cusp-form realization** (K. Ono 1996, Proposition 1; S. Ahlgren
1999, Lemma 4.2): for every `r < t` (`0 < t`), there exist `d > 0`, `L > 0`, integer weight `k`,
and a cusp form `F` on `Γ₁(L)` with integer `q`-expansion `b` such that for all `n ≥ 1`, whenever
the odd-square convolution `∑_{d(2j+1)^2 ≤ n} p(r + t*(n - d(2j+1)^2))` is odd, `b (24*(r+t*n)-1)`
is odd. -/
def H2 : Prop :=
  ∀ (r t : ℕ), 0 < t → r < t →
    ∃ (d L : ℕ) (k : ℤ)
      (F : CuspForm (↑(CongruenceSubgroup.Gamma1 L) : Subgroup (GL (Fin 2) ℝ)) k)
      (b : ℕ → ℤ),
      0 < d ∧ 0 < L ∧
      (∀ m : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff m = (b m : ℂ)) ∧
      (∀ n : ℕ, 1 ≤ n →
        Odd (∑ j ∈ (Finset.range (n + 1)).filter (fun j => d * (2 * j + 1) ^ 2 ≤ n),
          partitionNumber (r + t * (n - d * (2 * j + 1) ^ 2))) →
        Odd (b (24 * (r + t * n) - 1)))

theorem main : H1 → H2 → type_of% @PartitionParity.ahlgren.even := by
  intro h1 h2 r t ht
  let r₀ : ℕ := r % t
  have hr₀ : r₀ < t := Nat.mod_lt r ht
  obtain ⟨d, L, k, F, b, hd, hL, hqexp, hodd_impl⟩ := h2 r₀ t ht hr₀
  have hsparse := h1 L hL k F b hqexp
  -- Choose threshold N₀ so that for N ≥ N₀, #{m ≤ N | Odd (b m)} / N < 1 / (96 * t)
  have heps : (0 : ℝ) < 1 / (96 * (t : ℝ)) := by positivity
  have hev_b : ∀ᶠ N : ℕ in atTop,
      (((Finset.range (N + 1)).filter (fun m => Odd (b m))).card : ℝ) / (N : ℝ) <
        1 / (96 * (t : ℝ)) := by
    have hmem : Set.Iio (1 / (96 * (t : ℝ))) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds heps
    exact hsparse.eventually hmem
  rw [Filter.eventually_atTop] at hev_b
  obtain ⟨N₀, hN₀⟩ := hev_b
  -- Define convolution and even-count along progression r₀ + t * m
  let a : ℕ → ℕ := fun m => partitionNumber (r₀ + t * m)
  let conv : ℕ → ℕ := fun n =>
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => d * (2 * j + 1) ^ 2 ≤ n),
      a (n - d * (2 * j + 1) ^ 2)
  have hK_lower : ∀ K : ℕ, max 1 N₀ ≤ K →
      2 * d * K ≤ ((Finset.range (16 * d * K ^ 2)).filter (fun m => Even (a m))).card := by
    intro K hK
    have hK1 : 1 ≤ K := le_trans (le_max_left _ _) hK
    have hKN₀ : N₀ ≤ K := le_trans (le_max_right _ _) hK
    let M : ℕ := 384 * t * d * K ^ 2
    have hM_ge : N₀ ≤ M := by
      have h1 : 1 ≤ 384 * t * d := by nlinarith
      have h2 : K ≤ K ^ 2 := by nlinarith
      have h3 : K ^ 2 ≤ 384 * t * d * K ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hM_pos : (0 : ℝ) < (M : ℝ) := by dsimp [M]; positivity
    have hsparseM := hN₀ M hM_ge
    rw [div_lt_iff₀ hM_pos] at hsparseM
    have hodd_b_le : (((Finset.range (M + 1)).filter (fun m => Odd (b m))).card : ℝ) <
        4 * (d : ℝ) * (K : ℝ) ^ 2 := by
      have hRHS : 1 / (96 * (t : ℝ)) * (M : ℝ) = 4 * (d : ℝ) * (K : ℝ) ^ 2 := by
        dsimp [M]; push_cast; field_simp [show (t : ℝ) ≠ 0 by positivity]; ring
      linarith
    have hodd_b_nat : ((Finset.range (M + 1)).filter (fun m => Odd (b m))).card ≤ 4 * d * K ^ 2 := by
      have : (((Finset.range (M + 1)).filter (fun m => Odd (b m))).card : ℝ) ≤
          ((4 * d * K ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    -- Bound odd-convolution elements in bands d K via injection n ↦ 24*(r₀ + t*n) - 1
    let Bodd := (bands d K).filter fun n => Odd (conv n)
    let Beven := (bands d K).filter fun n => Even (conv n)
    have hBodd_le : Bodd.card ≤ ((Finset.range (M + 1)).filter (fun m => Odd (b m))).card := by
      refine Finset.card_le_card_of_injOn (fun n => 24 * (r₀ + t * n) - 1) ?_ ?_
      · intro n hn
        obtain ⟨hnB, hnOdd⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn1, hnlt⟩ := mem_bands_bounds hd hnB
        have hltM : 24 * (r₀ + t * n) - 1 < M + 1 := by
          have h1 : r₀ + t * n ≤ t * (16 * d * K ^ 2) := by
            have : t * n + t ≤ t * (16 * d * K ^ 2) := by
              have : n + 1 ≤ 16 * d * K ^ 2 := hnlt
              calc t * n + t = t * (n + 1) := by ring
                _ ≤ t * (16 * d * K ^ 2) := Nat.mul_le_mul_left t this
            omega
          have h2 : 24 * (r₀ + t * n) ≤ 384 * t * d * K ^ 2 := by
            calc 24 * (r₀ + t * n) ≤ 24 * (t * (16 * d * K ^ 2)) := Nat.mul_le_mul_left 24 h1
              _ = 384 * t * d * K ^ 2 := by ring
          dsimp [M]; omega
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hltM, hodd_impl n hn1 hnOdd⟩)
      · intro n₁ hn₁ n₂ hn₂ heq
        dsimp only at heq
        have h1 := (mem_bands_bounds hd (Finset.mem_filter.mp hn₁).1).1
        have h2 := (mem_bands_bounds hd (Finset.mem_filter.mp hn₂).1).1
        have hge1 : 1 ≤ 24 * (r₀ + t * n₁) := by nlinarith
        have hge2 : 1 ≤ 24 * (r₀ + t * n₂) := by nlinarith
        have hmul : 24 * (r₀ + t * n₁) = 24 * (r₀ + t * n₂) := by omega
        have htn : t * n₁ = t * n₂ := by omega
        exact Nat.eq_of_mul_eq_mul_left ht htn
    have hsplit : Beven.card + Bodd.card = (bands d K).card := by
      have hdisj : Disjoint Beven Bodd := by
        rw [Finset.disjoint_left]
        intro n hnE hnO
        exact (Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hnE).2) (Finset.mem_filter.mp hnO).2
      have hunion : Beven ∪ Bodd = bands d K := by
        ext n
        simp only [Beven, Bodd, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          rcases Nat.even_or_odd (conv n) with he | ho
          · exact Or.inl ⟨h, he⟩
          · exact Or.inr ⟨h, ho⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hBeven_ge : 4 * d * K ^ 2 ≤ Beven.card := by
      have hbc := bands_card d K
      have h8 : 8 * d * K ^ 2 = 2 * (4 * d * K ^ 2) := by ring
      omega
    -- Inject Beven into E_K × range (2 * K) via m + d * (2*j+1)^2 = n
    let EK := (Finset.range (16 * d * K ^ 2)).filter fun m => Even (a m)
    have hBeven_sub : Beven ⊆ (EK ×ˢ Finset.range (2 * K)).image
        (fun p => p.1 + d * (2 * p.2 + 1) ^ 2) := by
      intro n hn
      obtain ⟨hnB, hnEven⟩ := Finset.mem_filter.mp hn
      obtain ⟨q, hqK, hqIco⟩ := Finset.mem_biUnion.mp hnB
      have hq : q < K := Finset.mem_range.mp hqK
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hqIco
      have hfilt := bands_shift_filter_eq hd hlo hhi
      have hsum_even : Even (∑ j ∈ Finset.range (2 * q + 1), a (n - d * (2 * j + 1) ^ 2)) := by
        simpa only [conv, hfilt] using hnEven
      have hcard_odd : Odd (Finset.range (2 * q + 1)).card := by
        rw [Finset.card_range]; exact ⟨q, rfl⟩
      obtain ⟨j, hj_mem, hj_even⟩ := exists_even_of_even_sum_odd_card _ _ hcard_odd hsum_even
      have hj_lt : j < 2 * q + 1 := Finset.mem_range.mp hj_mem
      have hj_le : d * (2 * j + 1) ^ 2 ≤ n := by
        have hsq : (2 * j + 1) ^ 2 ≤ (4 * q + 1) ^ 2 := by nlinarith
        have hmul : d * (2 * j + 1) ^ 2 ≤ d * (4 * q + 1) ^ 2 := Nat.mul_le_mul_left d hsq
        omega
      let m := n - d * (2 * j + 1) ^ 2
      have hm_lt : m < 16 * d * K ^ 2 := by
        have := (mem_bands_bounds hd hnB).2
        omega
      refine Finset.mem_image.mpr ⟨(m, j), Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm_lt, hj_even⟩,
         Finset.mem_range.mpr (by omega)⟩, Nat.sub_add_cancel hj_le⟩
    have hBeven_le : Beven.card ≤ EK.card * (2 * K) := by
      calc Beven.card
          ≤ ((EK ×ˢ Finset.range (2 * K)).image (fun p => p.1 + d * (2 * p.2 + 1) ^ 2)).card :=
            Finset.card_le_card hBeven_sub
        _ ≤ (EK ×ˢ Finset.range (2 * K)).card := Finset.card_image_le
        _ = EK.card * (2 * K) := by rw [Finset.card_product, Finset.card_range]
    have hmul_le : (2 * d * K) * (2 * K) ≤ EK.card * (2 * K) := by
      have : (2 * d * K) * (2 * K) = 4 * d * K ^ 2 := by ring
      omega
    exact Nat.le_of_mul_le_mul_right hmul_le (by omega)
  -- Convert K-bound into Asymptotics.IsBigO
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := Real.sqrt (17 * (t : ℝ) * (d : ℝ)) / (d : ℝ)
  refine ⟨C, ?_⟩
  let X₀ : ℝ := 17 * (t : ℝ) * (d : ℝ) * ((max 1 N₀ + 1 : ℕ) : ℝ) ^ 2
  filter_upwards [eventually_ge_atTop (max 1 X₀)] with X hX
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXX₀ : X₀ ≤ X := le_trans (le_max_right _ _) hX
  have h17_pos : (0 : ℝ) < 17 * (t : ℝ) * (d : ℝ) := by positivity
  let K : ℕ := ⌊Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ)))⌋₊
  have hsqrt_ge : ((max 1 N₀ + 1 : ℕ) : ℝ) ≤ Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ))) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ h17_pos]
    dsimp [X₀] at hXX₀
    linarith
  have hK_ge1 : max 1 N₀ + 1 ≤ K := Nat.le_floor hsqrt_ge
  have hK_ge : max 1 N₀ ≤ K := by omega
  have hK_pos : 1 ≤ K := le_trans (le_max_left _ _) hK_ge
  have hK_sq_le : 17 * (t : ℝ) * (d : ℝ) * (K : ℝ) ^ 2 ≤ X := by
    have hfl : (K : ℝ) ≤ Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ))) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have hsq : (K : ℝ) ^ 2 ≤ X / (17 * (t : ℝ) * (d : ℝ)) := by
      have := sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) K]) hfl
      rwa [Real.sq_sqrt (div_nonneg (by linarith) h17_pos.le)] at this
    rwa [le_div_iff₀ h17_pos, mul_comm] at hsq
  -- Inject EK into S_even = {u : ℕ | (u : ℝ) ≤ X ∧ u ≡ r [MOD t] ∧ Even (partitionNumber u)}
  let EK := (Finset.range (16 * d * K ^ 2)).filter fun m => Even (a m)
  set S_even : Set ℕ := {u : ℕ | (u : ℝ) ≤ X ∧ u ≡ r [MOD t] ∧ Even (partitionNumber u)}
  have hS_fin : S_even.Finite :=
    (Set.finite_Iic ⌊X⌋₊).subset fun u hu => Nat.le_floor hu.1
  have hEK_le_S : EK.card ≤ S_even.ncard := by
    rw [Set.ncard_eq_toFinset_card S_even hS_fin]
    refine Finset.card_le_card_of_injOn (fun m => r₀ + t * m) ?_ ?_
    · intro m hm
      obtain ⟨hm_lt, hm_even⟩ := Finset.mem_filter.mp hm
      have hm_lt' : m < 16 * d * K ^ 2 := Finset.mem_range.mp hm_lt
      have hu_le : ((r₀ + t * m : ℕ) : ℝ) ≤ X := by
        have hnat : r₀ + t * m ≤ 17 * t * d * K ^ 2 := by
          have h1 : t * m + t ≤ t * (16 * d * K ^ 2) := by
            calc t * m + t = t * (m + 1) := by ring
              _ ≤ t * (16 * d * K ^ 2) := Nat.mul_le_mul_left t hm_lt'
          have h2 : t * (16 * d * K ^ 2) = 16 * t * d * K ^ 2 := by ring
          have h3 : 16 * t * d * K ^ 2 ≤ 17 * t * d * K ^ 2 := by nlinarith
          omega
        have hcast : ((r₀ + t * m : ℕ) : ℝ) ≤ 17 * (t : ℝ) * (d : ℝ) * (K : ℝ) ^ 2 := by
          exact_mod_cast hnat
        linarith
      have hu_mod : r₀ + t * m ≡ r [MOD t] := by
        have h1 : r₀ + t * m ≡ r₀ + 0 [MOD t] :=
          Nat.ModEq.add_left r₀ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right t m))
        rw [add_zero] at h1
        exact h1.trans (Nat.mod_modEq r t)
      exact Finset.mem_coe.mpr (hS_fin.mem_toFinset.mpr ⟨hu_le, hu_mod, hm_even⟩)
    · intro m₁ _ m₂ _ heq
      dsimp only at heq
      have htn : t * m₁ = t * m₂ := by omega
      exact Nat.eq_of_mul_eq_mul_left ht htn
  have h2dK : (2 * d * K : ℝ) ≤ (S_even.ncard : ℝ) := by
    have := (hK_lower K hK_ge).trans hEK_le_S
    exact_mod_cast this
  have hsqrt_le_2K : Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ))) ≤ 2 * (K : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ))))
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
    dsimp [K] at hlt ⊢
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg X),
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hsqrt_div : Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ))) =
      √X / Real.sqrt (17 * (t : ℝ) * (d : ℝ)) :=
    Real.sqrt_div (by linarith) _
  have hsqrt17_pos : 0 < Real.sqrt (17 * (t : ℝ) * (d : ℝ)) := Real.sqrt_pos.mpr h17_pos
  have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
  calc √X
      = Real.sqrt (17 * (t : ℝ) * (d : ℝ)) * Real.sqrt (X / (17 * (t : ℝ) * (d : ℝ))) := by
        rw [hsqrt_div, mul_div_cancel₀ _ hsqrt17_pos.ne']
    _ ≤ Real.sqrt (17 * (t : ℝ) * (d : ℝ)) * (2 * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrt_le_2K hsqrt17_pos.le
    _ = C * (2 * (d : ℝ) * (K : ℝ)) := by
        dsimp [C]; field_simp [hd_pos.ne']
    _ ≤ C * (S_even.ncard : ℝ) := by
        have hC_nn : 0 ≤ C := by dsimp [C]; positivity
        have h2dK' : 2 * (d : ℝ) * (K : ℝ) ≤ (S_even.ncard : ℝ) := by
          simpa [Nat.cast_mul] using h2dK
        exact mul_le_mul_of_nonneg_left h2dK' hC_nn

end OMA.R_PartitionParity_ahlgren_even_R1
