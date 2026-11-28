import OMAStatements.S_oeis_a005309
import Mathlib.Tactic

namespace OMA.P_oeis_a005309

open OMA.S_oeis_a005309

private lemma coeff_X_mul_eq (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) * f) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  cases n with
  | zero => simp
  | succ m => simp

/-- Exact computable truncated polynomial multiplication on length-8 lists (`a[0..7]`). -/
private def mulL (a b : List ℤ) : List ℤ :=
  (List.range 8).map fun i =>
    ((List.range (i + 1)).map fun j => a.getD j 0 * b.getD (i - j) 0).sum

private lemma list_sum_range (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private lemma coeff_mulL_eq {f g : PowerSeries ℤ} {a b : List ℤ}
    (hf : ∀ i < 8, PowerSeries.coeff i f = a.getD i 0)
    (hg : ∀ i < 8, PowerSeries.coeff i g = b.getD i 0) :
    ∀ i < 8, PowerSeries.coeff i (f * g) = (mulL a b).getD i 0 := by
  intro i hi
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => PowerSeries.coeff x f * PowerSeries.coeff y g)]
  have hget : (mulL a b).getD i 0 =
      ((List.range (i + 1)).map fun j => a.getD j 0 * b.getD (i - j) 0).sum := by
    simp [mulL, List.getD_eq_getElem?_getD, hi]
  rw [hget, list_sum_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [hf j (by omega), hg (i - j) (by omega)]

private lemma coeff_f2 : ∀ i < 8, PowerSeries.coeff i (fermionicFactor 2) =
    ([1, 0, 2, 0, 2, 0, 2, 0] : List ℤ).getD i 0 := by
  intro i hi; interval_cases i <;> simp [fermionicFactor]

private lemma coeff_f3 : ∀ i < 8, PowerSeries.coeff i (fermionicFactor 3) =
    ([1, 0, 0, 2, 0, 0, 2, 0] : List ℤ).getD i 0 := by
  intro i hi; interval_cases i <;> simp [fermionicFactor]

private lemma coeff_f4 : ∀ i < 8, PowerSeries.coeff i (fermionicFactor 4) =
    ([1, 0, 0, 0, 2, 0, 0, 0] : List ℤ).getD i 0 := by
  intro i hi; interval_cases i <;> simp [fermionicFactor]

private lemma coeff_f5 : ∀ i < 8, PowerSeries.coeff i (fermionicFactor 5) =
    ([1, 0, 0, 0, 0, 2, 0, 0] : List ℤ).getD i 0 := by
  intro i hi; interval_cases i <;> simp [fermionicFactor]

private lemma coeff_f6 : ∀ i < 8, PowerSeries.coeff i (fermionicFactor 6) =
    ([1, 0, 0, 0, 0, 0, 2, 0] : List ℤ).getD i 0 := by
  intro i hi; interval_cases i <;> simp [fermionicFactor]

private lemma coeff_f7 : ∀ i < 8, PowerSeries.coeff i (fermionicFactor 7) =
    ([1, 0, 0, 0, 0, 0, 0, 2] : List ℤ).getD i 0 := by
  intro i hi; interval_cases i <;> simp [fermionicFactor]

private lemma coeff_step {f g : PowerSeries ℤ} {a b c : List ℤ}
    (hf : ∀ i < 8, PowerSeries.coeff i f = a.getD i 0)
    (hg : ∀ i < 8, PowerSeries.coeff i g = b.getD i 0)
    (hcalc : mulL a b = c) :
    ∀ i < 8, PowerSeries.coeff i (f * g) = c.getD i 0 := by
  intro i hi
  rw [coeff_mulL_eq hf hg i hi, hcalc]

private lemma A005309_7_eq_60 : A005309 7 = 60 := by
  unfold A005309
  have hIcc : (Finset.Icc 1 7 : Finset ℕ) = {1, 2, 3, 4, 5, 6, 7} := by decide
  rw [hIcc]
  have hprod : ∏ k ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ), (fermionicFactor k) ^ (k - 1) =
      fermionicFactor 2 * (fermionicFactor 3 * fermionicFactor 3) *
      (fermionicFactor 4 * fermionicFactor 4 * fermionicFactor 4) *
      (fermionicFactor 5 * fermionicFactor 5 * fermionicFactor 5 * fermionicFactor 5) *
      (fermionicFactor 6 * fermionicFactor 6 * fermionicFactor 6 * fermionicFactor 6 * fermionicFactor 6) *
      (fermionicFactor 7 * fermionicFactor 7 * fermionicFactor 7 * fermionicFactor 7 * fermionicFactor 7 * fermionicFactor 7) := by
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    ring
  rw [hprod]
  have hf3_2 := coeff_step coeff_f3 coeff_f3 (c := [1, 0, 0, 4, 0, 0, 8, 0]) (by decide)
  have hf4_2 := coeff_step coeff_f4 coeff_f4 (c := [1, 0, 0, 0, 4, 0, 0, 0]) (by decide)
  have hf4_3 := coeff_step hf4_2 coeff_f4 (c := [1, 0, 0, 0, 6, 0, 0, 0]) (by decide)
  have hf5_2 := coeff_step coeff_f5 coeff_f5 (c := [1, 0, 0, 0, 0, 4, 0, 0]) (by decide)
  have hf5_3 := coeff_step hf5_2 coeff_f5 (c := [1, 0, 0, 0, 0, 6, 0, 0]) (by decide)
  have hf5_4 := coeff_step hf5_3 coeff_f5 (c := [1, 0, 0, 0, 0, 8, 0, 0]) (by decide)
  have hf6_2 := coeff_step coeff_f6 coeff_f6 (c := [1, 0, 0, 0, 0, 0, 4, 0]) (by decide)
  have hf6_3 := coeff_step hf6_2 coeff_f6 (c := [1, 0, 0, 0, 0, 0, 6, 0]) (by decide)
  have hf6_4 := coeff_step hf6_3 coeff_f6 (c := [1, 0, 0, 0, 0, 0, 8, 0]) (by decide)
  have hf6_5 := coeff_step hf6_4 coeff_f6 (c := [1, 0, 0, 0, 0, 0, 10, 0]) (by decide)
  have hf7_2 := coeff_step coeff_f7 coeff_f7 (c := [1, 0, 0, 0, 0, 0, 0, 4]) (by decide)
  have hf7_3 := coeff_step hf7_2 coeff_f7 (c := [1, 0, 0, 0, 0, 0, 0, 6]) (by decide)
  have hf7_4 := coeff_step hf7_3 coeff_f7 (c := [1, 0, 0, 0, 0, 0, 0, 8]) (by decide)
  have hf7_5 := coeff_step hf7_4 coeff_f7 (c := [1, 0, 0, 0, 0, 0, 0, 10]) (by decide)
  have hf7_6 := coeff_step hf7_5 coeff_f7 (c := [1, 0, 0, 0, 0, 0, 0, 12]) (by decide)
  have hp23 := coeff_step coeff_f2 hf3_2 (c := [1, 0, 2, 4, 2, 8, 10, 8]) (by decide)
  have hp234 := coeff_step hp23 hf4_3 (c := [1, 0, 2, 4, 8, 8, 22, 32]) (by decide)
  have hp2345 := coeff_step hp234 hf5_4 (c := [1, 0, 2, 4, 8, 16, 22, 48]) (by decide)
  have hp23456 := coeff_step hp2345 hf6_5 (c := [1, 0, 2, 4, 8, 16, 32, 48]) (by decide)
  have hpall := coeff_step hp23456 hf7_6 (c := [1, 0, 2, 4, 8, 16, 32, 60]) (by decide)
  exact hpall 7 (by omega)

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a005309.main := by
  intro hEq
  set A : PowerSeries ℤ := PowerSeries.mk A005309
  have hstep : ∀ n : ℕ,
      -A005309 n + 2 * (if 1 ≤ n then A005309 (n - 1) else 0) =
      -(if n = 0 then 1 else 0) + 2 * (if n = 1 then 1 else 0) - 2 * (if n = 2 then 1 else 0) := by
    intro n
    have hId : (-1 + PowerSeries.C (2 : ℤ) * PowerSeries.X) * A =
        -1 + PowerSeries.C (2 : ℤ) * PowerSeries.X - PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 := by
      have hR : -(1 - PowerSeries.C (2 : ℤ) * (PowerSeries.X : PowerSeries ℤ) +
          PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2) =
          -1 + PowerSeries.C (2 : ℤ) * PowerSeries.X - PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 := by
        ring
      rw [← hR]
      exact hEq
    have hc := congrArg (PowerSeries.coeff n) hId
    rw [add_mul, neg_mul, one_mul, mul_assoc,
      map_add, map_neg, map_sub, map_add, map_neg,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      coeff_X_mul_eq, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow] at hc
    simp only [A, PowerSeries.coeff_mk] at hc
    exact hc
  have h0 : A005309 0 = 1 := by
    have h := hstep 0; norm_num at h; linarith
  have h1 : A005309 1 = 0 := by
    have h := hstep 1; norm_num [h0] at h; linarith
  have h2 : A005309 2 = 2 := by
    have h := hstep 2; norm_num [h1] at h; linarith
  have h3 : A005309 3 = 4 := by
    have h := hstep 3; norm_num [h2] at h; linarith
  have h4 : A005309 4 = 8 := by
    have h := hstep 4; norm_num [h3] at h; linarith
  have h5 : A005309 5 = 16 := by
    have h := hstep 5; norm_num [h4] at h; linarith
  have h6 : A005309 6 = 32 := by
    have h := hstep 6; norm_num [h5] at h; linarith
  have h7 : A005309 7 = 64 := by
    have h := hstep 7; norm_num [h6] at h; linarith
  linarith [A005309_7_eq_60]

end OMA.P_oeis_a005309

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005309.main) :=
  OMA.P_oeis_a005309.prove_disproof
