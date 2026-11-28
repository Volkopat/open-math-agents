import OMAStatements.S_oeis_a267234

-- Credit: @RiverMint78

namespace FirstRepeatProof

section
def repOK : List ℕ → Bool
  | a :: b :: t => if b = a then t.all (· < b) else repOK (b :: t)
  | _ => true

def repCount (m n : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Fin m → Fin (n+1) => repOK (List.ofFn (fun i => (v i : ℕ))))).card
end

-- Split on whether the first two letters agree.
section
private def repList {m n : ℕ} (w : Fin m → Fin (n+1)) : List ℕ :=
  List.ofFn fun i => (w i : ℕ)

private lemma repList_cons {m n : ℕ} (c : Fin (n+1)) (w : Fin m → Fin (n+1)) :
    repList (Fin.cons c w) = c.val :: repList w := by
  simp [repList, List.ofFn_succ]

private def repWeight {m n : ℕ} (w : Fin m → Fin (n+1)) : ℕ :=
  if repOK (repList w) then 1 else 0

private lemma repCount_sum (m n : ℕ) :
    repCount m n = ∑ w : Fin m → Fin (n+1), repWeight w := by
  simp only [repCount, Finset.card_filter, repWeight, repList]
  apply Finset.sum_congr rfl
  intro w _
  split <;> rename_i h
  · exact (if_pos h).symm
  · exact (if_neg h).symm

private lemma rep_heads {m n : ℕ} (f : (Fin (m+1) → Fin (n+1)) → ℕ) :
    (∑ w, f w) = ∑ w : Fin m → Fin (n+1), ∑ c : Fin (n+1), f (Fin.cons c w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Fin (n+1))).sum_comp f,
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl

private def repSmall {m n : ℕ} (b : Fin (n+1)) (w : Fin m → Fin (n+1)) : ℕ :=
  if ∀ i, w i < b then 1 else 0

private lemma rep_smaller_iff {m n : ℕ} (b : Fin (n+1)) (w : Fin m → Fin (n+1)) :
    (repList w).all (· < b.val) = true ↔ ∀ i, w i < b := by
  simp [repList, List.all_eq_true, List.mem_ofFn]

private lemma rep_two_weight {m n : ℕ} (b c : Fin (n+1)) (w : Fin m → Fin (n+1)) :
    repWeight (Fin.cons c (Fin.cons b w)) =
      if c = b then repSmall b w else repWeight (Fin.cons b w) := by
  by_cases h : c = b
  · subst c
    simp only [repWeight, repList_cons, repOK, ite_true, repSmall, rep_smaller_iff]
  · have hval : b.val ≠ c.val := fun hbc => h (Fin.ext hbc.symm)
    simp [repWeight, repList_cons, repOK, hval, h]

private lemma rep_prepend_count {m n : ℕ} (b : Fin (n+1)) (w : Fin m → Fin (n+1)) :
    (∑ c, repWeight (Fin.cons c (Fin.cons b w))) =
      n * repWeight (Fin.cons b w) + repSmall b w := by
  simp_rw [rep_two_weight]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), if_pos rfl]
  congr 1
  calc
    _ = ∑ _c ∈ Finset.univ.erase b, repWeight (Fin.cons b w) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact if_neg (Finset.mem_erase.mp hc).1
    _ = _ := by simp [Finset.card_erase_of_mem]

private lemma rep_small_sum {m n : ℕ} (b : Fin (n+1)) :
    (∑ w : Fin m → Fin (n+1), repSmall b w) = (b : ℕ)^m := by
  have boxes : (Finset.univ.filter fun w : Fin m → Fin (n+1) => ∀ i, w i < b) =
      Fintype.piFinset (fun _ : Fin m => Finset.Iio b) := by
    ext w
    simp
  change (∑ w : Fin m → Fin (n+1), if ∀ i, w i < b then 1 else 0) = _
  rw [← Finset.card_filter, boxes]
  simp

lemma rep_one (n : ℕ) : repCount 1 n = n + 1 := by
  simp [repCount, List.ofFn_succ, repOK]

lemma rep_succ (m n : ℕ) : repCount (m+2) n =
    n * repCount (m+1) n + ∑ b : Fin (n+1), (b : ℕ)^m := by
  rw [repCount_sum, repCount_sum]
  calc
    _ = ∑ w : Fin m → Fin (n+1), ∑ b : Fin (n+1), ∑ c : Fin (n+1),
        repWeight (Fin.cons c (Fin.cons b w)) :=
      (rep_heads repWeight).trans (rep_heads _)
    _ = ∑ w : Fin m → Fin (n+1), ∑ b : Fin (n+1),
        (n * repWeight (Fin.cons b w) + repSmall b w) := by
      simp_rw [rep_prepend_count]
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [rep_heads (m := m) repWeight]
      congr 1
      rw [Finset.sum_comm]
      simp_rw [rep_small_sum]
end

-- Identify the bounded words with the functions counted in the statement.
section
open OMA.S_oeis_a267234

lemma rep_matches5 (l : List ℕ) : ok l = repOK l := by
  fun_induction repOK l <;> simp_all [ok]

lemma rep_bridge5 (n : ℕ) : a n = repCount 5 n := by
  unfold a repCount
  refine Finset.card_bij'
    (fun f hf i => ⟨f i, Finset.mem_range.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 i)⟩)
    (fun f _ i => (f i : ℕ)) ?_ ?_ ?_ ?_
  · intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (rep_matches5 _).symm.trans (Finset.mem_filter.mp hf).2⟩
  · intro f hf
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (f i).isLt),
      (rep_matches5 _).trans (Finset.mem_filter.mp hf).2⟩
  · intro f _
    rfl
  · intro f _
    rfl
end

-- Evaluate the power sums from the word recurrence.
section
open Finset

private def repPowerPoly : ℕ → ℚ → ℚ
  | 0, x => x + 1
  | 1, x => x * (x+1) / 2
  | 2, x => x * (x+1) * (2*x+1) / 6
  | 3, x => x^2 * (x+1)^2 / 4
  | 4, x => x * (x+1) * (2*x+1) * (3*x^2+3*x-1) / 30
  | 5, x => x^2 * (x+1)^2 * (2*x^2+2*x-1) / 12
  | _, _ => 0

private lemma rep_sum_powers (m n : ℕ) (hm : m ≤ 5) :
    (∑ b : Fin (n+1), (b:ℚ)^m) = repPowerPoly m n := by
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => (b:ℚ)^m)]
  induction n with
  | zero => interval_cases m <;> norm_num [repPowerPoly]
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    interval_cases m <;> simp only [repPowerPoly] <;> ring

private lemma rep_rat_step {r : ℕ → ℕ → ℕ}
    (hs : ∀ m n, r (m+2) n = n*r (m+1) n + ∑ b : Fin (n+1), (b:ℕ)^m)
    (m n : ℕ) (hm : m ≤ 5) :
    (r (m+2) n : ℚ) = n * (r (m+1) n : ℚ) + repPowerPoly m n := by
  rw [hs]
  push_cast
  rw [rep_sum_powers m n hm]

lemma rep_poly5 {r : ℕ → ℕ → ℕ}
    (h1 : ∀ n, r 1 n = n+1)
    (hs : ∀ m n, r (m+2) n = n*r (m+1) n + ∑ b : Fin (n+1), (b:ℕ)^m)
    (n : ℕ) : (r 5 n : ℚ) = (n:ℚ)^2 * (12*n^3 + 37*n^2 + 30*n + 5)/12 := by
  rw [rep_rat_step hs 3 n (by decide), rep_rat_step hs 2 n (by decide),
    rep_rat_step hs 1 n (by decide), rep_rat_step hs 0 n (by decide), h1]
  push_cast
  simp only [repPowerPoly]
  ring
end

-- Take coefficients of the proposed generating function.
section
open OMA.S_oeis_a267234 PowerSeries

lemma repSeries5 (hp : ∀ n : ℕ, (a n : ℚ) = (n:ℚ)^2 * (12*n^3 + 37*n^2 + 30*n + 5) / 12) :
    type_of% @OMA.S_oeis_a267234.main := by
  let F := PowerSeries.mk fun n => (a n : ℚ)
  have hD : F * (1-X)^6 = F - 6 • (F*X^1) + 15 • (F*X^2) - 20 • (F*X^3) + 15 • (F*X^4) - 6 • (F*X^5) + F*X^6 := by
    simp only [nsmul_eq_mul]
    ring
  have hN : (X : ℚ⟦X⟧) * (7 + 61*X + 51*X^2 + X^3) = 7 • X^1 + 61 • X^2 + 51 • X^3 + X^4 := by
    simp only [nsmul_eq_mul]
    ring
  change F * _ = _
  rw [hD, hN]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  by_cases h : n ≤ 6
  · interval_cases n <;> norm_num [hp]
  · simp (disch := omega) only [if_pos, if_neg, hp, Nat.cast_sub, Nat.cast_ofNat,
      Nat.cast_one, nsmul_eq_mul]
    ring
end

end FirstRepeatProof

open FirstRepeatProof

theorem OMA.solution : type_of% @OMA.S_oeis_a267234.main := by
  apply repSeries5
  intro n
  rw [rep_bridge5]
  exact rep_poly5 rep_one rep_succ n
