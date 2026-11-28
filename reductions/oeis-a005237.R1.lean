import OMAStatements.S_oeis_a005237

-- Reduction oeis-a005237.R1 of A005237: Numbers k such that k and k+1 have the same number of divisors.
-- Credit: @Dolcruz
-- Splits superlinear growth of A005237 into infinitude (Heath-Brown 1984) and density zero (Erdos 1936).

namespace OMA.R_oeis_a005237_R1

def H1 : Prop :=
  Set.Infinite {k : ℕ | 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card}

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    (((Finset.Icc 1 N).filter (fun k => k.divisors.card = (k + 1).divisors.card)).card : ℝ) ≤ ε * N

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a005237.main := by
  classical
  intro hInf hDens
  rw [Filter.tendsto_atTop_atTop]
  intro M
  let M' : ℝ := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hε : 0 < (1 : ℝ) / M' := div_pos one_pos hM'
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hDens (1 / M') hε)
  have hstrict : StrictMono (Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card)) :=
    Nat.nth_strictMono hInf
  refine ⟨N0 + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have han_ge : N0 ≤ OMA.S_oeis_a005237.a n := by
    have hle : n - 1 ≤ OMA.S_oeis_a005237.a n := hstrict.id_le (n - 1)
    omega
  have hsub :
      (Finset.range n).image (Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card)) ⊆
      (Finset.Icc 1 (OMA.S_oeis_a005237.a n)).filter
        (fun k => k.divisors.card = (k + 1).divisors.card) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    have hi_le : i ≤ n - 1 := by
      have hi_lt : i < n := Finset.mem_range.mp hi
      omega
    have hmem : 1 ≤ Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card) i ∧
        (Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card) i).divisors.card =
        (Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card) i + 1).divisors.card :=
      Nat.nth_mem_of_infinite hInf i
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmem.1, ?_⟩, hmem.2⟩
    exact hstrict.monotone hi_le
  have hcard_nat :
      n ≤ ((Finset.Icc 1 (OMA.S_oeis_a005237.a n)).filter
        (fun k => k.divisors.card = (k + 1).divisors.card)).card := by
    calc
      n = (Finset.range n).card := (Finset.card_range n).symm
      _ = ((Finset.range n).image
            (Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card))).card :=
        (Finset.card_image_of_injective _ hstrict.injective).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcard_real : (n : ℝ) ≤ (1 / M') * (OMA.S_oeis_a005237.a n : ℝ) :=
    le_trans (by exact_mod_cast hcard_nat) (hN0 (OMA.S_oeis_a005237.a n) han_ge)
  have hmul : M' * (n : ℝ) ≤ (OMA.S_oeis_a005237.a n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hcard_real hM'.le
    have hsimp : M' * ((1 / M') * (OMA.S_oeis_a005237.a n : ℝ)) = (OMA.S_oeis_a005237.a n : ℝ) := by
      field_simp [hM'.ne']
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hdiv : M' ≤ (OMA.S_oeis_a005237.a n : ℝ) / (n : ℝ) := (le_div_iff₀ hn_pos).mpr hmul
  exact le_trans (le_max_left M 1) hdiv

end OMA.R_oeis_a005237_R1
