import OMAStatements.S_oeis_a321580

/-!
# Proof of OEIS A321580

We prove that for all `n ≥ 1`, `a n = A014657 (n + 1) - 1`, where `a` enumerates deck sizes `k ≥ 1`
reversible by repeated perfect Faro shuffles with cut, and `A014657` enumerates numbers `m`
dividing `2^j + 1` for some `j ≥ 0`.

Proof outline:
1. Characterization `InSeq k ↔ 1 ≤ k ∧ DividesTwoPowAddOne (k + 1)`:
   - For `k = 1`: `shuffle 1` fixes position `0`, so `j = 1` reverses the 1-card deck, and
     `2 ∣ 2^0 + 1`.
   - For odd `k ≥ 3`: `k - 1 ≥ k / 2` and `2 * (k - 1 - k / 2) = k - 1`, so `shuffle k` fixes
     position `k - 1`. Thus the card at `k - 1` remains `k ≠ 1`, so `¬ InSeq k`. Also `k + 1` is
     even and `≥ 4`, so `¬ DividesTwoPowAddOne (k + 1)` (`2^j + 1` is odd for `j ≥ 1` and `2` for
     `j = 0`).
   - For even `k ≥ 2`: for every `i < k`, `(shuffle k d) i = d (pos k i)` where
     `pos k i + 1 ≡ 2 * (i + 1) [MOD k + 1]` and `pos k i < k`. By induction on `j`,
     `(shuffle k)^[j] (fun i => i + 1) i ≡ 2^j * (i + 1) [MOD k + 1]` and stays in `[1, k]`.
     Hence reversal `(shuffle k)^[j] (fun i => i + 1) i = k - i` for all `i < k` holds if and
     only if `2^j ≡ -1 [MOD k + 1]`, i.e., `k + 1 ∣ 2^j + 1` (which automatically forces `j ≥ 1`
     since `k + 1 ≥ 3`).
2. Since `DividesTwoPowAddOne 0` is false and `DividesTwoPowAddOne 1` holds (`1 ∣ 2^0 + 1`),
   `DividesTwoPowAddOne` is infinite (e.g. `2^t + 1` divides `2^t + 1`) and `Nat.nth InSeq m + 1 =
   Nat.nth DividesTwoPowAddOne (m + 1)` for all `m : ℕ` by induction on `m`, giving
   `a n = A014657 (n + 1) - 1` for `n ≥ 1`.
-/

namespace OMA.A321580Proof

open OMA.S_oeis_a321580 Classical

private def stepPos (k i : ℕ) : ℕ :=
  if i < k / 2 then 2 * i + 1 else 2 * (i - k / 2)

private lemma shuffle_eq (k : ℕ) (d : ℕ → ℕ) (i : ℕ) :
    shuffle k d i = d (stepPos k i) := by
  unfold shuffle stepPos
  split_ifs <;> rfl

private lemma shuffle_iter_apply (k j : ℕ) (d : ℕ → ℕ) (i : ℕ) :
    (shuffle k)^[j] d i = d ((stepPos k)^[j] i) := by
  induction j generalizing i with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, shuffle_eq, ih]

private lemma stepPos_lt_of_even (k i : ℕ) (heven : k % 2 = 0) (hi : i < k) :
    stepPos k i < k := by
  unfold stepPos
  split_ifs <;> omega

private lemma stepPos_mod_of_even (k i : ℕ) (heven : k % 2 = 0) (hi : i < k) :
    (stepPos k i + 1) % (k + 1) = (2 * (i + 1)) % (k + 1) := by
  unfold stepPos
  split_ifs with h
  · have : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [this]
  · have h1 : 2 * (i + 1) = (2 * (i - k / 2) + 1) + (k + 1) := by omega
    rw [h1, Nat.add_mod_right]

private lemma shuffle_iter_even (k : ℕ) (heven : k % 2 = 0) :
    ∀ j i : ℕ, i < k →
      (shuffle k)^[j] (fun t => t + 1) i ≤ k ∧
      1 ≤ (shuffle k)^[j] (fun t => t + 1) i ∧
      ((shuffle k)^[j] (fun t => t + 1) i) % (k + 1) = (2 ^ j * (i + 1)) % (k + 1) := by
  intro j
  induction j with
  | zero =>
    intro i hi
    refine ⟨by simp; omega, by simp, ?_⟩
    simp
  | succ j ih =>
    intro i hi
    have hlt : stepPos k i < k := stepPos_lt_of_even k i heven hi
    obtain ⟨hle, hge, hmod⟩ := ih (stepPos k i) hlt
    have hstep : (shuffle k)^[j + 1] (fun t => t + 1) i =
        (shuffle k)^[j] (fun t => t + 1) (stepPos k i) := by
      rw [shuffle_iter_apply, shuffle_iter_apply, Function.iterate_succ_apply]
    rw [hstep]
    refine ⟨hle, hge, ?_⟩
    rw [hmod]
    have hsm := stepPos_mod_of_even k i heven hi
    calc (2 ^ j * (stepPos k i + 1)) % (k + 1)
        = (2 ^ j * ((stepPos k i + 1) % (k + 1))) % (k + 1) := by rw [Nat.mul_mod_mod]
      _ = (2 ^ j * ((2 * (i + 1)) % (k + 1))) % (k + 1) := by rw [hsm]
      _ = (2 ^ j * (2 * (i + 1))) % (k + 1) := by rw [Nat.mul_mod_mod]
      _ = (2 ^ (j + 1) * (i + 1)) % (k + 1) := by congr 1; rw [pow_succ]; ring

private lemma shuffle_fix_last_odd (k : ℕ) (hodd : k % 2 = 1) (j : ℕ) :
    (shuffle k)^[j] (fun t => t + 1) (k - 1) = k := by
  induction j with
  | zero => simp; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply', shuffle_eq]
    have hstep : stepPos k (k - 1) = k - 1 := by
      unfold stepPos
      have hge : ¬ (k - 1 < k / 2) := by omega
      rw [if_neg hge]
      omega
    rw [hstep, ih]

private lemma inSeq_iff (k : ℕ) :
    InSeq k ↔ 1 ≤ k ∧ DividesTwoPowAddOne (k + 1) := by
  constructor
  · rintro ⟨hk1, j, hj1, hrev⟩
    refine ⟨hk1, ?_⟩
    by_cases hk1_eq : k = 1
    · subst hk1_eq
      exact ⟨0, by decide⟩
    · rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
      · have h0 := hrev 0 (by omega)
        obtain ⟨_, _, hmod⟩ := shuffle_iter_even k heven j 0 (by omega)
        rw [h0] at hmod
        refine ⟨j, ?_⟩
        have hsum : (2 ^ j + 1) % (k + 1) = 0 := by
          have : (2 ^ j * (0 + 1)) % (k + 1) = k % (k + 1) := hmod.symm
          simp only [zero_add, mul_one] at this
          rw [Nat.add_mod, this, ← Nat.add_mod, Nat.mod_self]
        exact Nat.dvd_of_mod_eq_zero hsum
      · have hfix := shuffle_fix_last_odd k hodd j
        have hlast := hrev (k - 1) (by omega)
        omega
  · rintro ⟨hk1, j, hdvd⟩
    refine ⟨hk1, ?_⟩
    by_cases hk1_eq : k = 1
    · subst hk1_eq
      refine ⟨1, le_rfl, ?_⟩
      intro i hi
      interval_cases i
      rfl
    · have heven : k % 2 = 0 := by
        by_contra h
        have hodd : k % 2 = 1 := by omega
        have h2 : 2 ∣ k + 1 := ⟨(k + 1) / 2, by omega⟩
        have h2d : 2 ∣ 2 ^ j + 1 := dvd_trans h2 hdvd
        cases j with
        | zero =>
          have : k + 1 ≤ 2 := Nat.le_of_dvd (by decide) hdvd
          omega
        | succ m =>
          have : (2 ^ (m + 1) + 1) % 2 = 1 := by rw [pow_succ]; omega
          have : (2 ^ (m + 1) + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2d
          omega
      have hj1 : 1 ≤ j := by
        cases j with
        | zero =>
          have : k + 1 ≤ 2 := Nat.le_of_dvd (by decide) hdvd
          omega
        | succ m => omega
      refine ⟨j, hj1, ?_⟩
      intro i hi
      obtain ⟨hle, hge, hmod⟩ := shuffle_iter_even k heven j i hi
      have h2j_mod : (2 ^ j + 1) % (k + 1) = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hsum_mod : ((shuffle k)^[j] (fun t => t + 1) i + (i + 1)) % (k + 1) = 0 := by
        rw [Nat.add_mod, hmod, ← Nat.add_mod]
        have hfac : 2 ^ j * (i + 1) + (i + 1) = (2 ^ j + 1) * (i + 1) := by ring
        rw [hfac, Nat.mul_mod, h2j_mod, zero_mul, Nat.zero_mod]
      have hsum_pos : 0 < (shuffle k)^[j] (fun t => t + 1) i + (i + 1) := by omega
      have hsum_lt : (shuffle k)^[j] (fun t => t + 1) i + (i + 1) < 2 * (k + 1) := by omega
      have hsum_dvd : k + 1 ∣ (shuffle k)^[j] (fun t => t + 1) i + (i + 1) :=
        Nat.dvd_of_mod_eq_zero hsum_mod
      rcases hsum_dvd with ⟨q, hq⟩
      have hq1 : q = 1 := by nlinarith
      rw [hq1, mul_one] at hq
      omega

private lemma div_infinite : {m : ℕ | DividesTwoPowAddOne m}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro b
  refine ⟨2 ^ (b + 1) + 1, ⟨b + 1, dvd_refl _⟩, ?_⟩
  have : b + 1 < 2 ^ (b + 1) := Nat.lt_two_pow_self
  omega

private lemma inSeq_infinite : {k : ℕ | InSeq k}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro b
  obtain ⟨m, hm, hgt⟩ := (Set.infinite_iff_exists_gt.mp div_infinite) (b + 1)
  refine ⟨m - 1, ?_, by omega⟩
  change InSeq (m - 1)
  rw [inSeq_iff]
  refine ⟨by omega, ?_⟩
  rwa [show m - 1 + 1 = m by omega]

private lemma count_div_succ (m : ℕ) (hm : 1 ≤ m) :
    Nat.count DividesTwoPowAddOne (m + 1) = Nat.count InSeq m + 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h0 : ¬ DividesTwoPowAddOne 0 := by
      rintro ⟨j, h⟩; exact Nat.succ_ne_zero _ (zero_dvd_iff.mp h)
    have h1 : DividesTwoPowAddOne 1 := ⟨0, one_dvd _⟩
    have h0i : ¬ InSeq 0 := by rintro ⟨h, _⟩; omega
    simp [Nat.count_succ, h0, h1, h0i]
  | succ m hm ih =>
    rw [Nat.count_succ, ih, Nat.count_succ]
    have heq : DividesTwoPowAddOne (m + 1) ↔ InSeq m := by
      rw [inSeq_iff]
      exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩
    simp only [heq]
    omega

private lemma nth_inSeq_add_one (m : ℕ) :
    Nat.nth InSeq m + 1 = Nat.nth DividesTwoPowAddOne (m + 1) := by
  have hmem : InSeq (Nat.nth InSeq m) := Nat.nth_mem_of_infinite inSeq_infinite m
  have hpos : 1 ≤ Nat.nth InSeq m := hmem.1
  have hdiv : DividesTwoPowAddOne (Nat.nth InSeq m + 1) := (inSeq_iff _).mp hmem |>.2
  have hcnt_in : Nat.count InSeq (Nat.nth InSeq m) = m :=
    Nat.count_nth_of_infinite inSeq_infinite m
  have hcnt_div : Nat.count DividesTwoPowAddOne (Nat.nth InSeq m + 1) = m + 1 := by
    rw [count_div_succ _ hpos, hcnt_in]
  rw [← hcnt_div, Nat.nth_count hdiv]

theorem result : type_of% @OMA.S_oeis_a321580.main := by
  intro n hn
  unfold a A014657
  have heq : n + 1 - 1 = (n - 1) + 1 := by omega
  rw [heq, ← nth_inSeq_add_one (n - 1)]
  omega

end OMA.A321580Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a321580.main := OMA.A321580Proof.result
