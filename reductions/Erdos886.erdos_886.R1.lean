import FormalConjectures.ErdosProblems.«886»
import Mathlib

-- Reduction Erdos886.erdos_886.R1 of Erdős Problem 886
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 886: divisors just above the square root

The target (Ruzsa's conjecture) says that for every `ε > 0` the number of divisors of `n` in
`(n^(1/2), n^(1/2) + n^(1/2 - ε))` is bounded for all large `n`.

Proved below, with no hypothesis:

* `card_le`, a counting bound in the spirit of Erdős and Rosenfeld: for every `n ≥ 1`, every real
  `ε` and every `C ≥ 0`, at most `C^2 n^(1/2 - 2ε) + 1` divisors of `n` lie in
  `(n^(1/2), n^(1/2) + C n^(1/2 - ε))`. Write `r = n^(1/2)` and send a divisor `d > r` to the
  integer `d + n / d`. Then `d + n / d - 2 r = (d - r)^2 / d`, which lies strictly between `0` and
  `C^2 n^(1 - 2ε) / r = C^2 n^(1/2 - 2ε)` (`fermat_gap`). The map is injective on divisors above
  `r`, because two of them have product larger than `n` (`eq_of_same_sum`). So the divisors in
  the window inject into the integers of an open interval of length `C^2 n^(1/2 - 2ε)`.
* `card_le_two`: hence for every `ε ≥ 1/4` and every `n ≥ 1` at most two divisors of `n` lie in
  the window. The target holds for every `ε ≥ 1/4` with `K = 2`.

For `ε < 1/4` the bound grows like `n^(1/2 - 2ε)`, and Erdős and Rosenfeld showed that four
divisors occur infinitely often in `(n^(1/2), n^(1/2) + 16 n^(1/4))`. What is left is the open
range `0 < ε < 1/4`, split by the parity of `n`. Both hypotheses are special cases of the target.

* `H1`: for every `0 < ε < 1/4`, odd `n` have a bounded number of divisors in the window.
* `H2`: for every `0 < ε < 1/4`, even `n` have a bounded number of divisors in the window.
-/

namespace OMA.R_Erdos886_erdos_886_R1

open Erdos886 Filter Finset

/-- Ruzsa's conjecture for odd `n` in the open range: for `0 < ε < 1/4`, all large odd `n` have
at most `K` divisors in `(n^(1/2), n^(1/2) + n^(1/2 - ε))`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1/4 →
    ∃ K : ℕ, ∀ᶠ n in atTop, Odd n → (Erdos886.Erdos886Divisors n ε 1).card ≤ K

/-- Ruzsa's conjecture for even `n` in the open range: for `0 < ε < 1/4`, all large even `n` have
at most `K` divisors in `(n^(1/2), n^(1/2) + n^(1/2 - ε))`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1/4 →
    ∃ K : ℕ, ∀ᶠ n in atTop, Even n → (Erdos886.Erdos886Divisors n ε 1).card ≤ K

/-- The identity behind the map `d ↦ d + n / d`, written with `n = r * r`. -/
lemma fermat_gap {r d : ℝ} (hd : 0 < d) : d + r * r / d - 2 * r = (d - r) ^ 2 / d := by
  field_simp
  ring

/-- Two numbers above `r` with the same value of `t + r^2 / t` are equal, since their product
exceeds `r^2`. -/
lemma eq_of_same_sum {r a b : ℝ} (hr : 0 < r) (ha : r < a) (hb : r < b)
    (h : a + r * r / a = b + r * r / b) : a = b := by
  have ha0 : 0 < a := hr.trans ha
  have hb0 : 0 < b := hr.trans hb
  have h' : (a - b) * (a * b - r * r) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · linarith
  · nlinarith

/-- The counting bound: at most `C^2 n^(1/2 - 2ε) + 1` divisors of `n` lie in
`(n^(1/2), n^(1/2) + C n^(1/2 - ε))`. -/
lemma card_le (n : ℕ) (hn : 0 < n) (ε C : ℝ) (hC : 0 ≤ C) :
    ((Erdos886Divisors n ε C).card : ℝ) ≤ C ^ 2 * (n : ℝ) ^ (1/2 - 2 * ε) + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := (n : ℝ) ^ (1/2 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hnR _
  have hrr : r * r = n := by
    rw [hr, ← Real.rpow_add hnR]
    norm_num
  set L : ℝ := C * (n : ℝ) ^ (1/2 - ε) with hL
  have hL0 : 0 ≤ L := by positivity
  set δ : ℝ := C ^ 2 * (n : ℝ) ^ (1/2 - 2 * ε) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hLr : L ^ 2 / r = δ := by
    rw [hL, hδ, hr, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1/2 - ε)) 2,
      ← Real.rpow_mul hnR.le, mul_div_assoc, ← Real.rpow_sub hnR]
    congr 2
    push_cast
    ring
  have hmem : ∀ d ∈ Erdos886Divisors n ε C, d ∣ n ∧ r < d ∧ (d : ℝ) < r + L := by
    intro d hd
    simp only [Erdos886Divisors, Finset.mem_filter, Nat.mem_divisors] at hd
    exact ⟨hd.1.1, hd.2.1, hd.2.2⟩
  let s : ℕ → ℕ := fun d => d + n / d
  have hs : ∀ d ∈ Erdos886Divisors n ε C, ((s d : ℕ) : ℝ) = d + r * r / d := by
    intro d hd
    obtain ⟨hdn, hrd, -⟩ := hmem d hd
    have hd0 : (d : ℝ) ≠ 0 := (hr0.trans hrd).ne'
    simp only [s]
    rw [Nat.cast_add, Nat.cast_div hdn hd0, hrr]
  have hlow : ∀ d ∈ Erdos886Divisors n ε C, 2 * r < ((s d : ℕ) : ℝ) := by
    intro d hd
    obtain ⟨-, hrd, -⟩ := hmem d hd
    have hd0 : (0 : ℝ) < d := hr0.trans hrd
    have hgap := fermat_gap (r := r) hd0
    have hpos : 0 < ((d : ℝ) - r) ^ 2 / d := by
      apply div_pos _ hd0
      have : (d : ℝ) - r ≠ 0 := by linarith
      positivity
    rw [hs d hd]
    linarith
  have hupp : ∀ d ∈ Erdos886Divisors n ε C, ((s d : ℕ) : ℝ) < 2 * r + δ := by
    intro d hd
    obtain ⟨-, hrd, hdL⟩ := hmem d hd
    have hd0 : (0 : ℝ) < d := hr0.trans hrd
    have hgap := fermat_gap (r := r) hd0
    have hsq : ((d : ℝ) - r) ^ 2 < L ^ 2 := by nlinarith
    have h1 : ((d : ℝ) - r) ^ 2 / d ≤ ((d : ℝ) - r) ^ 2 / r :=
      div_le_div_of_nonneg_left (sq_nonneg _) hr0 hrd.le
    have h2 : ((d : ℝ) - r) ^ 2 / r < L ^ 2 / r := div_lt_div_of_pos_right hsq hr0
    rw [hs d hd]
    linarith
  have hinj : Set.InjOn s (Erdos886Divisors n ε C : Set ℕ) := by
    intro a ha b hb hab
    have hab' : ((s a : ℕ) : ℝ) = ((s b : ℕ) : ℝ) := by rw [hab]
    rw [hs a ha, hs b hb] at hab'
    have := eq_of_same_sum hr0 (hmem a ha).2.1 (hmem b hb).2.1 hab'
    exact_mod_cast this
  have hsub : (Erdos886Divisors n ε C).image s ⊆
      Finset.Icc (⌊2 * r⌋₊ + 1) ⌊2 * r + δ⌋₊ := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_Icc]
    constructor
    · have := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ 2 * r)).2 (hlow d hd)
      omega
    · exact (Nat.le_floor_iff (by positivity)).2 (hupp d hd).le
  have hcard : (Erdos886Divisors n ε C).card ≤ ⌊2 * r + δ⌋₊ - ⌊2 * r⌋₊ := by
    rw [← Finset.card_image_of_injOn hinj]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Nat.card_Icc]
    omega
  have hmono : ⌊2 * r⌋₊ ≤ ⌊2 * r + δ⌋₊ := Nat.floor_le_floor (by linarith)
  have hcast : ((⌊2 * r + δ⌋₊ - ⌊2 * r⌋₊ : ℕ) : ℝ) = (⌊2 * r + δ⌋₊ : ℝ) - ⌊2 * r⌋₊ :=
    Nat.cast_sub hmono
  have hf1 : (⌊2 * r + δ⌋₊ : ℝ) ≤ 2 * r + δ := Nat.floor_le (by positivity)
  have hf2 : 2 * r - 1 < (⌊2 * r⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have : ((Erdos886Divisors n ε C).card : ℝ) ≤ ((⌊2 * r + δ⌋₊ - ⌊2 * r⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [hcast] at this
  linarith

/-- For `ε ≥ 1/4`, every `n ≥ 1` has at most two divisors in `(n^(1/2), n^(1/2) + n^(1/2 - ε))`. -/
lemma card_le_two {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 1/4 ≤ ε) :
    (Erdos886Divisors n ε 1).card ≤ 2 := by
  have h := card_le n hn ε 1 zero_le_one
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (1/2 - 2 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have : ((Erdos886Divisors n ε 1).card : ℝ) ≤ 2 := by nlinarith
  exact_mod_cast this

theorem main : H1 → H2 → type_of% @Erdos886.erdos_886 := by
  intro h1 h2 ε hε
  by_cases hlt : ε < 1/4
  · obtain ⟨K₁, hK₁⟩ := h1 ε hε hlt
    obtain ⟨K₂, hK₂⟩ := h2 ε hε hlt
    refine ⟨max K₁ K₂, ?_⟩
    filter_upwards [hK₁, hK₂] with n hn₁ hn₂
    rcases Nat.even_or_odd n with he | ho
    · exact (hn₂ he).trans (le_max_right _ _)
    · exact (hn₁ ho).trans (le_max_left _ _)
  · refine ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact card_le_two (by omega) (not_lt.1 hlt)

end OMA.R_Erdos886_erdos_886_R1
