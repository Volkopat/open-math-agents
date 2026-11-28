import OMAStatements.S_oeis_a380392

/-!
# Proof of `oeis-a380392`

Proves John Tyler Rascoe's conjecture for the mean number of South-East paths of ones in a
uniform random `(m + 1) × (m + 1)` binary matrix.

1. Every South-East path `s ∈ paths m` visits `2 * m + 1` distinct cells inside `grid m`
   (since the coordinate sum `(cell s t).1 + (cell s t).2` equals `t`), so it is contained in
   exactly `2 ^ ((m + 1) ^ 2 - (2 * m + 1))` subsets of `grid m`.
2. Swapping the double sum yields mean `(m.centralBinom : ℚ) / 2 ^ (2 * m + 1)`.
3. By Legendre's formula `padicValNat 2 n! + (Nat.digits 2 n).sum = n`, we have
   `padicValNat 2 m.centralBinom = (Nat.digits 2 m).sum`, which identifies the reduced
   numerator and denominator with `A001790 m` and `A101926 m`.
-/

namespace OMA.A380392Proof

open OMA.S_oeis_a380392 Finset

private lemma cell_sum (s : Finset ℕ) (t : ℕ) :
    (cell s t).1 + (cell s t).2 = t := by
  unfold cell
  dsimp only
  rw [Finset.card_inter_add_card_sdiff, Finset.card_range]

private lemma cells_subset_grid {m : ℕ} {s : Finset ℕ} (hs : s ∈ paths m) :
    cells m s ⊆ grid m := by
  rw [paths, Finset.mem_powersetCard] at hs
  intro p hp
  rw [cells, Finset.mem_image] at hp
  rcases hp with ⟨t, ht, rfl⟩
  rw [Finset.mem_range] at ht
  rw [grid, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  dsimp only [cell]
  constructor
  · have h1 : (range t ∩ s).card ≤ s.card := Finset.card_le_card Finset.inter_subset_right
    omega
  · have hsub : range t \ s ⊆ range (2 * m) \ s :=
      Finset.sdiff_subset_sdiff (Finset.range_mono (by omega)) Subset.rfl
    have h1 : (range t \ s).card ≤ (range (2 * m) \ s).card := Finset.card_le_card hsub
    have h2 : (range (2 * m) \ s).card = (range (2 * m)).card - s.card :=
      Finset.card_sdiff_of_subset hs.1
    rw [Finset.card_range] at h2
    omega

private lemma cells_card (m : ℕ) (s : Finset ℕ) : (cells m s).card = 2 * m + 1 := by
  rw [cells, Finset.card_image_of_injOn, Finset.card_range]
  intro t₁ _ t₂ _ heq
  have h1 := cell_sum s t₁
  have h2 := cell_sum s t₂
  rw [heq] at h1
  omega

private lemma card_powerset_superset {α : Type*} [DecidableEq α] {G A : Finset α} (hAG : A ⊆ G) :
    (G.powerset.filter (fun M => A ⊆ M)).card = 2 ^ (G.card - A.card) := by
  have hbij : (G.powerset.filter (fun M => A ⊆ M)).card = (G \ A).powerset.card := by
    refine Finset.card_bij (fun M _ => M \ A) ?_ ?_ ?_
    · intro M hM
      rw [Finset.mem_filter, Finset.mem_powerset] at hM
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hM.1 Subset.rfl
    · intro M₁ hM₁ M₂ hM₂ heq
      rw [Finset.mem_filter] at hM₁ hM₂
      rw [← Finset.sdiff_union_of_subset hM₁.2, ← Finset.sdiff_union_of_subset hM₂.2, heq]
    · intro B hB
      rw [Finset.mem_powerset] at hB
      refine ⟨B ∪ A, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset (hB.trans Finset.sdiff_subset) hAG, Finset.subset_union_right⟩
      · have hdisj : Disjoint B A := Finset.disjoint_of_subset_left hB Finset.sdiff_disjoint
        exact Finset.union_sdiff_cancel_right hdisj
  rw [hbij, Finset.card_powerset, Finset.card_sdiff_of_subset hAG]

private lemma sum_pathCount (m : ℕ) :
    (∑ M ∈ (grid m).powerset, pathCount m M) = m.centralBinom * 2 ^ (m * m) := by
  have hswap : (∑ M ∈ (grid m).powerset, pathCount m M) =
      ∑ s ∈ paths m, ((grid m).powerset.filter (fun M => cells m s ⊆ M)).card := by
    simp only [pathCount, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hconst : ∀ s ∈ paths m,
      ((grid m).powerset.filter (fun M => cells m s ⊆ M)).card = 2 ^ (m * m) := by
    intro s hs
    rw [card_powerset_superset (cells_subset_grid hs), cells_card]
    have hgrid : (grid m).card = (m + 1) * (m + 1) := by
      rw [grid, Finset.card_product, Finset.card_range]
    rw [hgrid]
    congr 1
    have hsq : (m + 1) * (m + 1) = m * m + (2 * m + 1) := by ring
    omega
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, paths,
    Finset.card_powersetCard, Finset.card_range, Nat.centralBinom_eq_two_mul_choose]

private lemma digits_two_double (n : ℕ) : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Nat.digits_def' (by decide) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left n (by decide : 0 < 2)]

private lemma digits_two_succ_add_padicValNat (n : ℕ) :
    (Nat.digits 2 (n + 1)).sum + padicValNat 2 (n + 1) = (Nat.digits 2 n).sum + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · have hodd : ¬ 2 ∣ (r + r + 1) := by omega
      have hv : padicValNat 2 (r + r + 1) = 0 := padicValNat.eq_zero_of_not_dvd hodd
      have h1 : (Nat.digits 2 (r + r + 1)).sum = 1 + (Nat.digits 2 r).sum := by
        rw [Nat.digits_def' (by decide) (by omega)]
        have hm : (r + r + 1) % 2 = 1 := by omega
        have hd : (r + r + 1) / 2 = r := by omega
        rw [hm, hd]
        simp
      have h2 : (Nat.digits 2 (r + r)).sum = (Nat.digits 2 r).sum := by
        rw [show r + r = 2 * r by omega]
        exact digits_two_double r
      omega
    · have h2r : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
      rw [h2r, digits_two_double (r + 1)]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hv : padicValNat 2 (2 * (r + 1)) = 1 + padicValNat 2 (r + 1) := by
        rw [padicValNat.mul (by decide) (by omega), padicValNat.self (by decide)]
      have h1 : (Nat.digits 2 (2 * r + 1)).sum = 1 + (Nat.digits 2 r).sum := by
        rw [Nat.digits_def' (by decide) (by omega)]
        have hm : (2 * r + 1) % 2 = 1 := by omega
        have hd : (2 * r + 1) / 2 = r := by omega
        rw [hm, hd]
        simp
      have hih := ih r (by omega)
      omega

private lemma padicValNat_factorial_add_digits (n : ℕ) :
    padicValNat 2 n.factorial + (Nat.digits 2 n).sum = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
    have hstep := digits_two_succ_add_padicValNat n
    omega

private lemma padicValNat_centralBinom (m : ℕ) :
    padicValNat 2 m.centralBinom = (Nat.digits 2 m).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : m.centralBinom * (m.factorial * m.factorial) = (2 * m).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    simpa [show 2 * m - m = m by omega] using h
  have hv := congrArg (padicValNat 2) hfac
  rw [padicValNat.mul (Nat.centralBinom_ne_zero m) (mul_ne_zero (Nat.factorial_ne_zero m)
        (Nat.factorial_ne_zero m)),
      padicValNat.mul (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero m)] at hv
  have h1 := padicValNat_factorial_add_digits m
  have h2 := padicValNat_factorial_add_digits (2 * m)
  rw [digits_two_double m] at h2
  omega

private lemma digits_two_sum_le (m : ℕ) : (Nat.digits 2 m).sum ≤ m := by
  have := padicValNat_factorial_add_digits m
  omega

theorem result : type_of% @OMA.S_oeis_a380392.main := by
  intro m
  have hnum : (∑ M ∈ (grid m).powerset, (pathCount m M : ℚ)) =
      (m.centralBinom : ℚ) * (2 : ℚ) ^ (m * m) := by
    rw [← Nat.cast_sum, sum_pathCount]
    push_cast
    rfl
  have hden : ((grid m).powerset.card : ℚ) = (2 : ℚ) ^ (2 * m + 1) * (2 : ℚ) ^ (m * m) := by
    rw [Finset.card_powerset, grid, Finset.card_product, Finset.card_range]
    have hsq : (m + 1) * (m + 1) = (2 * m + 1) + m * m := by ring
    rw [hsq, pow_add]
    push_cast
    rfl
  have h2pow_ne : ((2 : ℚ) ^ (m * m)) ≠ 0 := by positivity
  rw [hnum, hden, mul_div_mul_right _ _ h2pow_ne]
  have hdvd : 2 ^ padicValNat 2 m.centralBinom ∣ m.centralBinom := pow_padicValNat_dvd
  have hA1 : (A001790 m : ℚ) * (2 : ℚ) ^ (Nat.digits 2 m).sum = (m.centralBinom : ℚ) := by
    unfold A001790
    rw [← padicValNat_centralBinom m]
    exact_mod_cast Nat.div_mul_cancel hdvd
  have hle : (Nat.digits 2 m).sum ≤ 2 * m := (digits_two_sum_le m).trans (by omega)
  have hA2 : (A101926 m : ℚ) * (2 : ℚ) ^ (Nat.digits 2 m).sum = (2 : ℚ) ^ (2 * m + 1) := by
    unfold A101926
    push_cast
    rw [← pow_add]
    congr 1
    omega
  have h2d_ne : ((2 : ℚ) ^ (Nat.digits 2 m).sum) ≠ 0 := by positivity
  rw [← hA1, ← hA2, mul_div_mul_right _ _ h2d_ne]

end OMA.A380392Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380392.main := OMA.A380392Proof.result
