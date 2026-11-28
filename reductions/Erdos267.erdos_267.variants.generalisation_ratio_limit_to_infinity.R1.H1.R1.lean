import OMAReductions.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1

-- Reduction Erdos267.erdos_267.variants.generalisation_ratio_limit_to_infinity.R1.H1.R1 of step Erdos267.erdos_267.variants.generalisation_ratio_limit_to_infinity.R1.H1
-- Credit: @rickmanelius

/-!
# Erdős 267, lacunary case: the Liouville argument reaches every ratio above `2`

The step is Badea's theorem in eventual form: if `n (k+1) ≥ c n k` for some `c > 1` and all large
`k`, then `S = ∑ 1 / F (n k)` is irrational. Write `s K = n 0 + ⋯ + n K` and `φ` for the golden
ratio.

Proved below with no hypothesis:
* `lacunary_jump`: if `n (K+1) - s K` is unbounded, `S` is irrational. If `S = p / q` and `L` is the
  product of the nonzero `F (n k)` with `k ≤ K`, then `q L (S - S_K)` is a positive integer, while
  `L ≤ φ ^ (s K)` (since `F m ≤ φ ^ m`, `fib_le_gold_pow`) and
  `S - S_K ≤ 3 / F (n (K+1)) ≤ 3 φ ^ (2 - n (K+1))` (the parent's tail bound and
  `F (m + 2) ≥ φ ^ m`, `gold_pow_le_fib`). This sharpens the parent's super-lacunary case, which
  needs `n (K+1) - 2 s K` unbounded because it uses `F m ≤ 2 ^ m` and `F m ≥ (3/2) ^ (m - 2)`.
* `jump_of_ratio`: if `n (k+1) ≥ c n k` for some `c > 2` and all large `k`, then
  `s K ≤ S₀ + c n K / (c - 1)`, so `n (K+1) - s K ≥ c (c - 2) / (c - 1) * n K - S₀` is unbounded.
So every sequence whose ratio is eventually at least some `c > 2` is settled.

What is left:
* `H1`: the doubling regime, `n (k+1) ≥ 2 n k` for all large `k` while for every `c > 2` the ratio
  falls below `c` infinitely often. It contains `n k = 2 ^ k`, for which the irrationality of
  `∑ 1 / F (2 ^ k)` is the result of Good and of Bicknell and Hoggatt cited in the source file.
* `H2`: ratios below `2` infinitely often: `n (k+1) ≥ c n k` eventually for some `c > 1`, and
  `n (k+1) < 2 n k` for infinitely many `k`.
-/

open Filter Finset Real
open OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1
  (summable_inv_fib tail_le)

namespace OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1_H1_R1

/-- The doubling regime: `n (k+1) ≥ 2 n k` eventually, and for every `c > 2` the ratio
`n (k+1) / n k` is below `c` infinitely often. -/
def H1 : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → (∀ᶠ k in atTop, 2 * n k ≤ n (k + 1)) →
    (∀ c : ℝ, 2 < c → ∃ᶠ k in atTop, (n (k + 1) : ℝ) < c * n k) →
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ))

/-- Ratios below `2` infinitely often: lacunary with some `c > 1`, and `n (k+1) < 2 n k`
for infinitely many `k`. -/
def H2 : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → (∃ c : ℝ, 1 < c ∧ ∀ᶠ k in atTop, c * n k ≤ n (k + 1)) →
    (∃ᶠ k in atTop, n (k + 1) < 2 * n k) →
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ))

/-- `F m ≤ φ ^ m`. -/
theorem fib_le_gold_pow : ∀ m : ℕ, (Nat.fib m : ℝ) ≤ goldenRatio ^ m
  | 0 => by simp
  | 1 => by simp [Real.one_lt_goldenRatio.le]
  | m + 2 => by
    have h1 := fib_le_gold_pow (m + 1)
    have h0 := fib_le_gold_pow m
    rw [Nat.fib_add_two, Nat.cast_add]
    have hg : goldenRatio ^ (m + 2) = goldenRatio ^ m + goldenRatio ^ (m + 1) := by
      rw [pow_add, Real.goldenRatio_sq]
      ring
    linarith

/-- `φ ^ m ≤ F (m + 2)`. -/
theorem gold_pow_le_fib : ∀ m : ℕ, goldenRatio ^ m ≤ (Nat.fib (m + 2) : ℝ)
  | 0 => by simp
  | 1 => by
    have h := Real.goldenRatio_sq
    have hpos := Real.goldenRatio_pos
    norm_num [Nat.fib_add_two]
    nlinarith
  | m + 2 => by
    have h1 := gold_pow_le_fib (m + 1)
    have h0 := gold_pow_le_fib m
    rw [show m + 2 + 2 = (m + 2) + 2 by ring, Nat.fib_add_two, Nat.cast_add]
    have hg : goldenRatio ^ (m + 2) = goldenRatio ^ m + goldenRatio ^ (m + 1) := by
      rw [pow_add, Real.goldenRatio_sq]
      ring
    rw [show m + 1 + 2 = m + 3 by ring] at h1
    linarith

/-- If `n (K+1)` exceeds `n 0 + ⋯ + n K` by an unbounded amount, `∑ 1 / F (n k)` is
irrational. -/
theorem lacunary_jump (n : ℕ → ℕ) (hn : StrictMono n)
    (hjump : ∀ C : ℕ, ∃ K, ∑ k ∈ range (K + 1), n k + C < n (K + 1)) :
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ)) := by
  rintro ⟨r, hr⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 * (r.den : ℝ)) Real.one_lt_goldenRatio
  obtain ⟨K, hK⟩ := hjump (m + 2)
  set s := ∑ k ∈ range (K + 1), n k with hs
  set L : ℕ := ∏ k ∈ range (K + 1), max 1 (Nat.fib (n k)) with hL
  have hL2 : (L : ℝ) ≤ goldenRatio ^ s := by
    rw [hL, hs, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun k _ => by positivity)
    intro k _
    rcases le_total 1 (Nat.fib (n k)) with h | h
    · rw [max_eq_right h]
      exact fib_le_gold_pow _
    · rw [max_eq_left h]
      push_cast
      exact one_le_pow₀ Real.one_lt_goldenRatio.le
  obtain ⟨z, hz⟩ : ∃ z : ℕ, (L : ℝ) * ∑ k ∈ range (K + 1), 1 / (Nat.fib (n k) : ℝ) = z := by
    refine ⟨∑ k ∈ range (K + 1), (if Nat.fib (n k) = 0 then 0 else L / Nat.fib (n k)), ?_⟩
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    by_cases h0 : Nat.fib (n k) = 0
    · simp [h0]
    · rw [if_neg h0]
      have hdvd : Nat.fib (n k) ∣ L := by
        have : max 1 (Nat.fib (n k)) = Nat.fib (n k) :=
          max_eq_right (Nat.one_le_iff_ne_zero.mpr h0)
        rw [← this]
        exact Finset.dvd_prod_of_mem _ hk
      rw [Nat.cast_div hdvd (by exact_mod_cast h0)]
      ring
  have hsum := (summable_inv_fib n hn).sum_add_tsum_nat_add (K + 1)
  set T := ∑' i, 1 / (Nat.fib (n (i + (K + 1))) : ℝ) with hT
  have hnK : 2 ≤ n (K + 1) := by omega
  have hF : goldenRatio ^ (n (K + 1) - 2) ≤ Nat.fib (n (K + 1)) := by
    have h := gold_pow_le_fib (n (K + 1) - 2)
    rwa [show n (K + 1) - 2 + 2 = n (K + 1) by omega] at h
  have hFpos : (0 : ℝ) < Nat.fib (n (K + 1)) := by
    have : (0 : ℝ) < goldenRatio ^ (n (K + 1) - 2) := by positivity
    linarith
  have hTpos : 0 < T := by
    have hs' := (summable_nat_add_iff (K + 1)).mpr (summable_inv_fib n hn)
    refine hs'.tsum_pos (fun _ => by positivity) 0 ?_
    simp only [zero_add]
    exact one_div_pos.mpr hFpos
  have hTle := tail_le n hn K hnK
  have hint : (r.den : ℝ) * L * T = ((r.num * L - r.den * z : ℤ) : ℝ) := by
    have hr' : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    have hS : ∑' k, 1 / (Nat.fib (n k) : ℝ) =
        ∑ k ∈ range (K + 1), 1 / (Nat.fib (n k) : ℝ) + T := hsum.symm
    have hT' : T = r - ∑ k ∈ range (K + 1), 1 / (Nat.fib (n k) : ℝ) := by
      rw [hr, hS]; ring
    push_cast
    rw [hT', mul_sub, ← hz, hr']
    field_simp
  have hL0 : (0 : ℝ) < L := by
    have : 1 ≤ L := Finset.one_le_prod' (fun k _ => le_max_left _ _)
    exact_mod_cast this
  have hwpos : (0 : ℝ) < (r.den : ℝ) * L * T := by positivity
  have hw1 : (1 : ℝ) ≤ (r.den : ℝ) * L * T := by
    rw [hint] at hwpos ⊢
    have : (0 : ℤ) < r.num * L - r.den * z := by exact_mod_cast hwpos
    exact_mod_cast this
  have hpow : goldenRatio ^ s * goldenRatio ^ m ≤ goldenRatio ^ (n (K + 1) - 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ Real.one_lt_goldenRatio.le (by omega)
  have hbound : (r.den : ℝ) * L * T ≤ 3 * r.den / goldenRatio ^ m := by
    have hm0 : (0 : ℝ) < goldenRatio ^ m := by positivity
    have hs0 : (0 : ℝ) < goldenRatio ^ s := by positivity
    calc (r.den : ℝ) * L * T ≤ r.den * goldenRatio ^ s * (3 / Nat.fib (n (K + 1))) := by
          gcongr
      _ ≤ r.den * goldenRatio ^ s * (3 / (goldenRatio ^ s * goldenRatio ^ m)) := by
          gcongr
          exact hpow.trans hF
      _ = 3 * r.den / goldenRatio ^ m := by
          field_simp
  have hlt : 3 * (r.den : ℝ) / goldenRatio ^ m < 1 := by
    rw [div_lt_one (by positivity)]
    exact hm
  linarith

/-- A ratio eventually at least `c > 2` gives unbounded jumps `n (K+1) - (n 0 + ⋯ + n K)`. -/
theorem jump_of_ratio (n : ℕ → ℕ) (hn : StrictMono n) {c : ℝ} (hc : 2 < c)
    (hev : ∀ᶠ k in atTop, c * n k ≤ n (k + 1)) :
    ∀ C : ℕ, ∃ K, ∑ k ∈ range (K + 1), n k + C < n (K + 1) := by
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hev
  have hgeo : ∀ K, k0 ≤ K →
      (c - 1) * ∑ k ∈ Finset.Ico k0 (K + 1), (n k : ℝ) ≤ c * n K := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base =>
      rw [Finset.sum_Ico_succ_top (le_refl k0), Finset.Ico_self, Finset.sum_empty, zero_add]
      have : (0 : ℝ) ≤ n k0 := by positivity
      linarith
    | succ K hK ih =>
      rw [Finset.sum_Ico_succ_top (by omega : k0 ≤ K + 1)]
      have hstep := hk0 K hK
      have : (0 : ℝ) ≤ n (K + 1) := by positivity
      nlinarith
  intro C
  set S0 : ℝ := ∑ k ∈ range k0, (n k : ℝ) with hS0
  obtain ⟨B, hB⟩ := exists_nat_gt ((S0 + C + 1) * (c - 1) / (c * (c - 2)))
  set K := max k0 B with hKdef
  refine ⟨K, ?_⟩
  have hKk0 : k0 ≤ K := le_max_left _ _
  have hKB : B ≤ K := le_max_right _ _
  have hnK : (B : ℝ) ≤ n K := by
    have : B ≤ n K := le_trans hKB (hn.id_le K)
    exact_mod_cast this
  have hsplit : ∑ k ∈ range (K + 1), (n k : ℝ) = S0 + ∑ k ∈ Finset.Ico k0 (K + 1), (n k : ℝ) := by
    rw [hS0, Finset.sum_range_add_sum_Ico _ (by omega : k0 ≤ K + 1)]
  have hg := hgeo K hKk0
  have hstep := hk0 K hKk0
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hc2 : (0 : ℝ) < c - 2 := by linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hBlarge : (S0 + C + 1) * (c - 1) < c * (c - 2) * n K := by
    have h1 : (S0 + C + 1) * (c - 1) / (c * (c - 2)) < n K := lt_of_lt_of_le hB hnK
    rw [div_lt_iff₀ (by positivity)] at h1
    calc (S0 + C + 1) * (c - 1) < (n K : ℝ) * (c * (c - 2)) := h1
      _ = c * (c - 2) * n K := by ring
  have hreal : ∑ k ∈ range (K + 1), (n k : ℝ) + C < n (K + 1) := by
    rw [hsplit]
    have hS0nn : (0 : ℝ) ≤ S0 := by positivity
    nlinarith
  have hcast : ((∑ k ∈ range (K + 1), n k + C : ℕ) : ℝ) < (n (K + 1) : ℝ) := by
    push_cast
    exact hreal
  exact_mod_cast hcast

theorem main : H1 → H2 →
    OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1.H1 := by
  intro h1 h2 n hn hlac
  by_cases hbig : ∃ c : ℝ, 2 < c ∧ ∀ᶠ k in atTop, c * n k ≤ n (k + 1)
  · obtain ⟨c, hc, hev⟩ := hbig
    exact lacunary_jump n hn (jump_of_ratio n hn hc hev)
  · have hsmall : ∀ c : ℝ, 2 < c → ∃ᶠ k in atTop, (n (k + 1) : ℝ) < c * n k := by
      intro c hc
      have hne : ¬ ∀ᶠ k in atTop, c * (n k : ℝ) ≤ n (k + 1) := fun h => hbig ⟨c, hc, h⟩
      rw [Filter.not_eventually] at hne
      simpa only [not_le] using hne
    by_cases hdouble : ∀ᶠ k in atTop, 2 * n k ≤ n (k + 1)
    · exact h1 n hn hdouble hsmall
    · have hf : ∃ᶠ k in atTop, n (k + 1) < 2 * n k := by
        rw [Filter.not_eventually] at hdouble
        simpa only [not_le] using hdouble
      exact h2 n hn hlac hf

end OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1_H1_R1
