import OMAStatements.S_oeis_a355872

/-!
Proof of all three conjectures (plus the stronger mod-16 theorem) on OEIS A355872.

1. Existence: since `(-X)^(n^2)` for `n ≥ 1` and `X^4` shift coefficients by at least `1`,
   the `r`-th coefficient of the RHS depends only on `A.coeff j` for `j < r`, so structural
   recursion on prefix lists builds `A : PowerSeries ℤ` satisfying `SatisfiesA355872 A`.
2. Parity (`2 ∣ A.coeff r` for all `r`): immediate by strong induction on `r`, since every
   term on the RHS is either `2`, `0`, or a sum of products involving `A.coeff j` (`j < r`).
3. Mod 16: since `2 ∣ A.coeff j` for all `j`, `A = 2 * B` for `B := PowerSeries.mk (fun j => A.coeff j / 2)`.
   Therefore for every `e ≥ 4`, `A ^ e = 2 ^ e * B ^ e` has all coefficients divisible by `16`.
   Since `(n - 1)^2 ≥ 4` for `n ≥ 3` and `(m + 1)^2 ≥ 4` for `m ≥ 1`, both tail sums vanish mod `16`,
   leaving `A.coeff r ≡ (if r = 1 then 2 else 0) - (X^4 * A).coeff r (mod 16)` for all `r`.
   By induction on `k`, `A.coeff (4 * k - 3) ≡ 2 * (-1)^(k - 1) (mod 16)`, which immediately
   implies `a(k) % 4 = 2`, `a(2k - 1) % 8 = 2`, and `a(2k) % 8 = 6`.
-/

namespace A355872Proof

open Finset PowerSeries OMA.S_oeis_a355872

private lemma coeff_mul_eq_of_prefix {A₁ A₂ B₁ B₂ : PowerSeries ℤ} {n : ℕ}
    (h1 : ∀ j ≤ n, A₁.coeff j = B₁.coeff j) (h2 : ∀ j ≤ n, A₂.coeff j = B₂.coeff j) :
    ∀ k ≤ n, (A₁ * A₂).coeff k = (B₁ * B₂).coeff k := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [h1 p.1 (by omega), h2 p.2 (by omega)]

private lemma coeff_pow_eq_of_prefix {A B : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j ≤ n, A.coeff j = B.coeff j) :
    ∀ e k : ℕ, k ≤ n → (A ^ e).coeff k = (B ^ e).coeff k := by
  intro e
  induction e with
  | zero => intro k _; simp
  | succ e ih =>
    intro k hk
    rw [pow_succ, pow_succ]
    exact coeff_mul_eq_of_prefix ih h k hk

private lemma coeff_negX_pow_mul {s : ℕ} (F : PowerSeries ℤ) (r : ℕ) :
    ((-PowerSeries.X) ^ s * F).coeff r =
      if s ≤ r then (-1 : ℤ) ^ s * F.coeff (r - s) else 0 := by
  have h1 : (-PowerSeries.X : PowerSeries ℤ) ^ s = PowerSeries.C ((-1 : ℤ) ^ s) * PowerSeries.X ^ s := by
    rw [neg_eq_neg_one_mul, mul_pow]
    have : (-1 : PowerSeries ℤ) ^ s = PowerSeries.C ((-1 : ℤ) ^ s) := by simp
    rw [this]
  rw [h1, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> ring

private lemma coeff_negX_pow_mul_eq_of_strict_prefix {A B : PowerSeries ℤ} {r s e : ℕ}
    (hs : 1 ≤ s) (h : ∀ j < r, A.coeff j = B.coeff j) :
    ((-PowerSeries.X) ^ s * A ^ e).coeff r = ((-PowerSeries.X) ^ s * B ^ e).coeff r := by
  rw [coeff_negX_pow_mul, coeff_negX_pow_mul]
  split_ifs with hle
  · congr 1
    exact coeff_pow_eq_of_prefix (fun j hj => h j (by omega)) e (r - s) le_rfl
  · rfl

private noncomputable def buildList : ℕ → List ℤ
  | 0 => []
  | r + 1 =>
    let L := buildList r
    let val : ℤ :=
      if r = 0 then 0
      else
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        (if r = 1 then (2 : ℤ) else 0) -
        (PowerSeries.X ^ 4 * Aprev).coeff r -
        (∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * Aprev ^ ((n - 1) ^ 2)).coeff r) -
        (∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * Aprev ^ ((m + 1) ^ 2)).coeff r)
    L ++ [val]

private lemma buildList_length (n : ℕ) : (buildList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildList, ih]

private lemma buildList_getD_of_lt : ∀ (n j : ℕ), j < n →
    (buildList n).getD j 0 = (buildList (j + 1)).getD j 0 := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
    · rfl
    · simp only [buildList, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [buildList_length]; exact hlt)]
      exact ih j hlt

private noncomputable def buildSeq (r : ℕ) : ℤ :=
  (buildList (r + 1)).getD r 0

private lemma exists_solution : ∃ A : PowerSeries ℤ, SatisfiesA355872 A := by
  let A : PowerSeries ℤ := PowerSeries.mk buildSeq
  have h0 : A.coeff 0 = 0 := by
    rw [PowerSeries.coeff_mk]
    unfold buildSeq
    simp [buildList]
  refine ⟨A, h0, fun r => ?_⟩
  cases r with
  | zero =>
    have h1 : Finset.Icc 3 0 = ∅ := by decide
    have h2 : Finset.Icc 1 0 = ∅ := by decide
    rw [h0, if_neg (by decide : (0 : ℕ) ≠ 1), PowerSeries.coeff_X_pow_mul',
      if_neg (by decide : ¬ 4 ≤ 0), h1, h2]
    simp
  | succ r' =>
    set r := r' + 1
    rw [PowerSeries.coeff_mk]
    unfold buildSeq
    have hlen : (buildList r).length = r := buildList_length r
    have hlast : (buildList (r + 1)).getD r 0 =
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList r).getD j 0
        (if r = 1 then (2 : ℤ) else 0) -
        (PowerSeries.X ^ 4 * Aprev).coeff r -
        (∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * Aprev ^ ((n - 1) ^ 2)).coeff r) -
        (∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * Aprev ^ ((m + 1) ^ 2)).coeff r) := by
      simp [buildList, List.getD_eq_getElem?_getD, hlen, show r ≠ 0 by omega]
    rw [hlast]
    let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList r).getD j 0
    have hpre : ∀ j < r, Aprev.coeff j = A.coeff j := by
      intro j hj
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      exact buildList_getD_of_lt r j hj
    have hx4 : (PowerSeries.X ^ 4 * Aprev).coeff r = (PowerSeries.X ^ 4 * A).coeff r := by
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      split_ifs with hle
      · exact hpre (r - 4) (by omega)
      · rfl
    have hsum1 : ∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * Aprev ^ ((n - 1) ^ 2)).coeff r =
        ∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * A ^ ((n - 1) ^ 2)).coeff r := by
      apply Finset.sum_congr rfl
      intro n hn; rw [Finset.mem_Icc] at hn
      exact coeff_negX_pow_mul_eq_of_strict_prefix (by nlinarith) hpre
    have hsum2 : ∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * Aprev ^ ((m + 1) ^ 2)).coeff r =
        ∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * A ^ ((m + 1) ^ 2)).coeff r := by
      apply Finset.sum_congr rfl
      intro m hm; rw [Finset.mem_Icc] at hm
      exact coeff_negX_pow_mul_eq_of_strict_prefix (by nlinarith) hpre
    change (if r = 1 then (2 : ℤ) else 0) - (PowerSeries.X ^ 4 * Aprev).coeff r - _ - _ = _
    rw [hx4, hsum1, hsum2]

private lemma two_dvd_pow_of_two_dvd_prefix {A : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j ≤ n, (2 : ℤ) ∣ A.coeff j) :
    ∀ e k : ℕ, 1 ≤ e → k ≤ n → (2 : ℤ) ∣ (A ^ e).coeff k := by
  intro e
  induction e with
  | zero => intro k he _; omega
  | succ e ih =>
    intro k _ hk
    cases e with
    | zero => simpa using h k hk
    | succ e' =>
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Finset.dvd_sum
      intro p hp
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact dvd_mul_of_dvd_right (h p.2 (by omega)) _

private lemma two_dvd_all {A : PowerSeries ℤ} (hA : SatisfiesA355872 A) :
    ∀ r : ℕ, (2 : ℤ) ∣ A.coeff r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [hA.2 r]
    have h1 : (2 : ℤ) ∣ (if r = 1 then (2 : ℤ) else 0) := by split_ifs <;> decide
    have h2 : (2 : ℤ) ∣ (PowerSeries.X ^ 4 * A).coeff r := by
      rw [PowerSeries.coeff_X_pow_mul']
      split_ifs with hle
      · exact ih (r - 4) (by omega)
      · exact dvd_zero 2
    have h3 : (2 : ℤ) ∣ ∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * A ^ ((n - 1) ^ 2)).coeff r := by
      apply Finset.dvd_sum
      intro n hn; rw [Finset.mem_Icc] at hn
      rw [coeff_negX_pow_mul]
      split_ifs with hle
      · have hpos : 1 ≤ n ^ 2 := by nlinarith
        have hnm1 : 1 ≤ n - 1 := by omega
        have he1 : 1 ≤ (n - 1) ^ 2 := by nlinarith
        exact dvd_mul_of_dvd_right
          (two_dvd_pow_of_two_dvd_prefix (fun j hj => ih j (by omega)) ((n - 1) ^ 2) (r - n ^ 2) he1 le_rfl) _
      · exact dvd_zero 2
    have h4 : (2 : ℤ) ∣ ∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * A ^ ((m + 1) ^ 2)).coeff r := by
      apply Finset.dvd_sum
      intro m hm; rw [Finset.mem_Icc] at hm
      rw [coeff_negX_pow_mul]
      split_ifs with hle
      · have hpos : 1 ≤ m ^ 2 := by nlinarith
        have he1 : 1 ≤ (m + 1) ^ 2 := by nlinarith
        exact dvd_mul_of_dvd_right
          (two_dvd_pow_of_two_dvd_prefix (fun j hj => ih j (by omega)) ((m + 1) ^ 2) (r - m ^ 2) he1 le_rfl) _
      · exact dvd_zero 2
    exact dvd_sub (dvd_sub (dvd_sub h1 h2) h3) h4

private lemma sixteen_dvd_pow {A : PowerSeries ℤ} (h2 : ∀ j : ℕ, (2 : ℤ) ∣ A.coeff j)
    {e : ℕ} (he : 4 ≤ e) (r : ℕ) : (16 : ℤ) ∣ (A ^ e).coeff r := by
  let B : PowerSeries ℤ := PowerSeries.mk fun j => A.coeff j / 2
  have hAB : A = PowerSeries.C (2 : ℤ) * B := by
    ext j
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (h2 j)]
  rw [hAB, mul_pow, ← map_pow, PowerSeries.coeff_C_mul]
  have h16 : (16 : ℤ) ∣ (2 : ℤ) ^ e := by
    rw [show e = 4 + (e - 4) by omega, pow_add]; exact dvd_mul_right 16 _
  exact dvd_mul_of_dvd_left h16 _

private lemma mod16_step {A : PowerSeries ℤ} (hA : SatisfiesA355872 A) (r : ℕ) :
    (16 : ℤ) ∣ (A.coeff r - ((if r = 1 then (2 : ℤ) else 0) - (PowerSeries.X ^ 4 * A).coeff r)) := by
  have h2 := two_dvd_all hA
  have hsum1 : (16 : ℤ) ∣ ∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * A ^ ((n - 1) ^ 2)).coeff r := by
    apply Finset.dvd_sum
    intro n hn; rw [Finset.mem_Icc] at hn
    rw [coeff_negX_pow_mul]
    split_ifs
    · have he4 : 4 ≤ (n - 1) ^ 2 := by
        have : 2 ≤ n - 1 := by omega
        nlinarith
      exact dvd_mul_of_dvd_right (sixteen_dvd_pow h2 he4 _) _
    · exact dvd_zero 16
  have hsum2 : (16 : ℤ) ∣ ∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * A ^ ((m + 1) ^ 2)).coeff r := by
    apply Finset.dvd_sum
    intro m hm; rw [Finset.mem_Icc] at hm
    rw [coeff_negX_pow_mul]
    split_ifs
    · have he4 : 4 ≤ (m + 1) ^ 2 := by nlinarith
      exact dvd_mul_of_dvd_right (sixteen_dvd_pow h2 he4 _) _
    · exact dvd_zero 16
  have hdiff : A.coeff r - ((if r = 1 then (2 : ℤ) else 0) - (PowerSeries.X ^ 4 * A).coeff r) =
      -((∑ n ∈ Finset.Icc 3 r, ((-PowerSeries.X) ^ (n ^ 2) * A ^ ((n - 1) ^ 2)).coeff r) +
        (∑ m ∈ Finset.Icc 1 r, ((-PowerSeries.X) ^ (m ^ 2) * A ^ ((m + 1) ^ 2)).coeff r)) := by
    have := hA.2 r; linarith
  rw [hdiff]
  exact (dvd_add hsum1 hsum2).neg_right

private lemma mod16_formula {A : PowerSeries ℤ} (hA : SatisfiesA355872 A) :
    ∀ k : ℕ, 1 ≤ k → A.coeff (4 * k - 3) ≡ 2 * (-1 : ℤ) ^ (k - 1) [ZMOD 16] := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h := mod16_step hA 1
    rw [if_pos rfl, PowerSeries.coeff_X_pow_mul', if_neg (by decide : ¬ 4 ≤ 1), sub_zero] at h
    exact Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using h.neg_right)
  | succ k hk ih =>
    have h := mod16_step hA (4 * (k + 1) - 3)
    rw [if_neg (by omega), zero_sub, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
      show 4 * (k + 1) - 3 - 4 = 4 * k - 3 by omega] at h
    have hstep : A.coeff (4 * (k + 1) - 3) ≡ -A.coeff (4 * k - 3) [ZMOD 16] := by
      rw [Int.modEq_iff_dvd]
      have : -A.coeff (4 * k - 3) - A.coeff (4 * (k + 1) - 3) =
          -(A.coeff (4 * (k + 1) - 3) - -A.coeff (4 * k - 3)) := by ring
      rw [this]
      exact h.neg_right
    have hneg : -A.coeff (4 * k - 3) ≡ -(2 * (-1 : ℤ) ^ (k - 1)) [ZMOD 16] := ih.neg
    have hsign : -(2 * (-1 : ℤ) ^ (k - 1)) = 2 * (-1 : ℤ) ^ (k + 1 - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    rw [hsign] at hneg
    exact hstep.trans hneg

theorem solve : type_of% @OMA.S_oeis_a355872.main := by
  refine ⟨exists_solution, fun A hA k hk => ?_⟩
  have h16 := mod16_formula hA k hk
  have h16_odd := mod16_formula hA (2 * k - 1) (by omega)
  have h16_even := mod16_formula hA (2 * k) (by omega)
  have hpow_k : (-1 : ℤ) ^ (k - 1) = 1 ∨ (-1 : ℤ) ^ (k - 1) = -1 := by
    rcases Nat.even_or_odd (k - 1) with hev | hodd
    · left; exact hev.neg_one_pow
    · right; exact hodd.neg_one_pow
  have hpow_odd : (-1 : ℤ) ^ (2 * k - 1 - 1) = 1 := by
    have : Even (2 * k - 1 - 1) := ⟨k - 1, by omega⟩
    exact this.neg_one_pow
  have hpow_even : (-1 : ℤ) ^ (2 * k - 1) = -1 := by
    have : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    exact this.neg_one_pow
  refine ⟨?_, ?_, ?_, h16⟩
  · obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp h16
    rcases hpow_k with h1 | hm1 <;> omega
  · rw [hpow_odd, mul_one] at h16_odd
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp h16_odd
    omega
  · rw [hpow_even] at h16_even
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp h16_even
    omega

end A355872Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a355872.main :=
  A355872Proof.solve
