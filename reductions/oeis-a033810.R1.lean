import OMAStatements.S_oeis_a033810

/-!
Reduction `oeis-a033810.R1` for A033810 (the birthday-problem threshold).

`a n` is the least `k` with `1 - pDistinct n k ≥ 1/2`, and the claim is `a n = ⌈F n⌉` for every
`n ≥ 1`, where `F` is the standard asymptotic formula. Two structural facts make the problem purely
statistical:

* `pDistinct n ·` is antitone in `k` (each new factor `(n - k)/n` is `≤ 1`), so
  `{k | 1/2 ≤ 1 - pDistinct n k}` is an upward-closed set of naturals;
* hence `a n` is exactly the least element of that set, and `a n = ⌈F n⌉` reduces to the two
  inequalities `1/2 ≤ 1 - pDistinct n ⌈F n⌉` and `1 - pDistinct n (⌈F n⌉ - 1) < 1/2`.

The difficulty then splits by regime, which is what `H1`..`H4` separate:

* `H1`, `H2`: the asymptotic regime `n ≥ 1000`. Here `⌈F n⌉ ≈ √(2 n log 2)` and the margins are
  `Θ(n^{-1/2})`, so one needs the expansion of `log ∏ (1 - i/n)` in powers of `k/n` with explicit
  control of the remainder (Faulhaber sums plus two-sided `log(1-x)` bounds suffice; Stirling is
  not needed), together with the exact expansion error of `F`.
* `H3`, `H4`: the finite regime `n < 1000`. Only 998 cases, but the ceiling of a transcendental
  expression must be decided exactly for each: rational interval arithmetic on `Real.log 2` and
  `Real.sqrt`, with the large margins available there.

Proving all four hypotheses closes the problem; the implication is pure order theory on `sInf`.
-/

namespace OMA.R_oeis_a033810_R1

open OMA.S_oeis_a033810

def H1 : Prop :=
  ∀ n : ℕ, 1000 ≤ n → (1:ℝ)/2 ≤ 1 - pDistinct n (Int.ceil (Real.sqrt (2 * n * Real.log 2) + (3 - 2 * Real.log 2) / 6 + (9 - 4 * Real.log 2 ^ 2) / (72 * Real.sqrt (2 * n * Real.log 2)) - 2 * Real.log 2 ^ 2 / (135 * n))).toNat

def H2 : Prop :=
  ∀ n : ℕ, 1000 ≤ n → 1 - pDistinct n ((Int.ceil (Real.sqrt (2 * n * Real.log 2) + (3 - 2 * Real.log 2) / 6 + (9 - 4 * Real.log 2 ^ 2) / (72 * Real.sqrt (2 * n * Real.log 2)) - 2 * Real.log 2 ^ 2 / (135 * n))).toNat - 1) < (1:ℝ)/2

def H3 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n < 1000 → (1:ℝ)/2 ≤ 1 - pDistinct n (Int.ceil (Real.sqrt (2 * n * Real.log 2) + (3 - 2 * Real.log 2) / 6 + (9 - 4 * Real.log 2 ^ 2) / (72 * Real.sqrt (2 * n * Real.log 2)) - 2 * Real.log 2 ^ 2 / (135 * n))).toNat

def H4 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n < 1000 → 1 - pDistinct n ((Int.ceil (Real.sqrt (2 * n * Real.log 2) + (3 - 2 * Real.log 2) / 6 + (9 - 4 * Real.log 2 ^ 2) / (72 * Real.sqrt (2 * n * Real.log 2)) - 2 * Real.log 2 ^ 2 / (135 * n))).toNat - 1) < (1:ℝ)/2

lemma pDistinct_zero (n : ℕ) : pDistinct n 0 = 1 := by
  simp [pDistinct]

lemma pDistinct_nonneg (n k : ℕ) : 0 ≤ pDistinct n k := by
  rw [pDistinct]
  by_cases hk : k ≤ n
  · refine Finset.prod_nonneg ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    have hin : i ≤ n := le_trans (le_of_lt hi) hk
    have h1 : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
    have h2 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    exact div_nonneg (by linarith) h2
  · push_neg at hk
    have hmem : n ∈ Finset.range k := Finset.mem_range.mpr hk
    have hzero : (((n : ℝ) - (n : ℝ)) / (n : ℝ)) = 0 := by simp
    exact le_of_eq (Finset.prod_eq_zero hmem hzero).symm

lemma pDistinct_succ_le (n k : ℕ) : pDistinct n (k + 1) ≤ pDistinct n k := by
  have hnonneg : 0 ≤ pDistinct n k := pDistinct_nonneg n k
  have hfac : (((n : ℝ) - (k : ℝ)) / (n : ℝ)) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsplit : (((n : ℝ) - (k : ℝ)) / (n : ℝ)) = 1 - (k : ℝ) / (n : ℝ) := by
        rw [sub_div, div_self (ne_of_gt hn')]
      have hk0 : 0 ≤ (k : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg k) (le_of_lt hn')
      linarith
  calc pDistinct n (k + 1) = pDistinct n k * (((n : ℝ) - (k : ℝ)) / (n : ℝ)) := by
        simp only [pDistinct, Finset.prod_range_succ]
    _ ≤ pDistinct n k * 1 := by exact mul_le_mul_of_nonneg_left hfac hnonneg
    _ = pDistinct n k := by ring

lemma pDistinct_le_of_le {n k m : ℕ} (h : k ≤ m) : pDistinct n m ≤ pDistinct n k := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact le_trans (pDistinct_succ_le n m) ih

lemma mem_of_le {n k m : ℕ} (hk : (1:ℝ)/2 ≤ 1 - pDistinct n k) (hkm : k ≤ m) :
    (1:ℝ)/2 ≤ 1 - pDistinct n m := by
  have hmono : pDistinct n m ≤ pDistinct n k := pDistinct_le_of_le (n := n) hkm
  linarith

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a033810.main := by
  intro h1 h2 h3 h4 n hn
  set E : ℝ := Real.sqrt (2 * n * Real.log 2) + (3 - 2 * Real.log 2) / 6 + (9 - 4 * Real.log 2 ^ 2) / (72 * Real.sqrt (2 * n * Real.log 2)) - 2 * Real.log 2 ^ 2 / (135 * n) with hE
  set K : ℕ := (Int.ceil E).toNat with hK
  set S : Set ℕ := {k : ℕ | (1:ℝ)/2 ≤ 1 - pDistinct n k} with hS
  have hmemK : K ∈ S := by
    by_cases hc : n < 1000
    · exact h3 n hn hc
    · push_neg at hc
      exact h1 n hc
  have hmemK' : K - 1 ∉ S := by
    by_cases hc : n < 1000
    · exact not_le.mpr (h4 n hn hc)
    · push_neg at hc
      exact not_le.mpr (h2 n hc)
  have hKne : K ≠ 0 := by
    intro h0
    have h : K ∈ S := hmemK
    rw [h0] at h
    have h1' : (1:ℝ)/2 ≤ 1 - pDistinct n 0 := h
    rw [pDistinct_zero] at h1'
    norm_num at h1'
  have hpos : 0 ≤ Int.ceil E := by
    by_contra hc
    have hle : Int.ceil E ≤ 0 := by omega
    have hcast : (((Int.ceil E).toNat : ℕ) : ℤ) = max (Int.ceil E) 0 := Int.ofNat_toNat (Int.ceil E)
    have hmax : max (Int.ceil E) 0 = 0 := le_antisymm (max_le hle le_rfl) (le_max_right _ _)
    have hz : (Int.ceil E).toNat = 0 := by
      have hz' : (((Int.ceil E).toNat : ℕ) : ℤ) = 0 := by rw [hcast, hmax]
      exact_mod_cast hz'
    exact hKne (by rw [hK]; exact hz)
  have hKcast : (K : ℤ) = Int.ceil E := by
    rw [hK]
    exact Int.toNat_of_nonneg hpos
  have hsInf_le : a n ≤ K := by
    show sInf S ≤ K
    exact Nat.sInf_le hmemK
  have hbound : ∀ k ∈ S, K ≤ k := by
    intro k hk
    by_contra hlt
    push_neg at hlt
    have hk' : k ≤ K - 1 := Nat.le_pred_of_lt hlt
    have hmem : (1:ℝ)/2 ≤ 1 - pDistinct n (K - 1) := mem_of_le (n := n) hk hk'
    exact hmemK' hmem
  have hK_le : K ≤ a n := by
    have hne : S.Nonempty := ⟨K, hmemK⟩
    have hmin : sInf S ∈ S := Nat.sInf_mem hne
    show K ≤ sInf S
    exact hbound (sInf S) hmin
  have hfin : a n = K := le_antisymm hsInf_le hK_le
  rw [hfin]
  exact hKcast

end OMA.R_oeis_a033810_R1
