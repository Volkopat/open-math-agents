import OMAStatements.S_oeis_a002124
import Mathlib.Tactic

namespace OMA.P_oeis_a002124

open OMA.S_oeis_a002124

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℤ) (m n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) ^ m * f) =
      if m ≤ n then PowerSeries.coeff (n - m) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single (m, n - m)]
    · simp [PowerSeries.coeff_X_pow]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      have ham : a ≠ m := fun ha => hne (Prod.ext ha (by omega))
      dsimp only
      rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
  · refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    have ham : a ≠ m := by omega
    dsimp only
    rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]

private lemma finite_oddPrimeComp (n : ℕ) :
    Set.Finite { l : List ℕ | IsOddPrimeComp n l } := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      have hsub : { l : List ℕ | IsOddPrimeComp 0 l } ⊆ {[]} := by
        intro l hl
        cases l with
        | nil => rfl
        | cons a t =>
          have h1 := hl.2 a (by simp)
          have h3 : 3 ≤ a := by
            have := h1.1.two_le; omega
          have hsum := hl.1
          simp at hsum
          omega
      exact (Set.finite_singleton []).subset hsub
    | succ m =>
      have hsub : { l : List ℕ | IsOddPrimeComp (m + 1) l } ⊆
          ⋃ p ∈ (Finset.range (m + 2)).filter (fun p => Nat.Prime p ∧ p % 2 = 1),
            (List.cons p) '' { t : List ℕ | IsOddPrimeComp (m + 1 - p) t } := by
        intro l hl
        cases l with
        | nil => simp [IsOddPrimeComp] at hl
        | cons p t =>
          have hp := hl.2 p (by simp)
          have hsum : p + t.sum = m + 1 := by simpa using hl.1
          simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, Set.mem_image]
          exact ⟨p, ⟨by omega, hp⟩, t, ⟨by omega, fun q hq => hl.2 q (by simp [hq])⟩, rfl⟩
      refine Set.Finite.subset ?_ hsub
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => ?_
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp
      have hp_pos : 1 ≤ p := hp.2.1.pos
      exact (ih (m + 1 - p) (by omega)).image (List.cons p)

private lemma A002124_zero : A002124 0 = 1 := by
  have heq : { l : List ℕ | IsOddPrimeComp 0 l } = {[]} := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hl
      cases l with
      | nil => rfl
      | cons a t =>
        have h1 := hl.2 a (by simp)
        have h3 : 3 ≤ a := by have := h1.1.two_le; omega
        have hsum := hl.1; simp at hsum; omega
    · rintro rfl; exact ⟨rfl, fun _ h => by simp at h⟩
  unfold A002124
  rw [heq, Set.ncard_singleton]

private lemma A002124_succ (m : ℕ) :
    A002124 (m + 1) =
      ∑ p ∈ (Finset.range (m + 2)).filter (fun p => Nat.Prime p ∧ p % 2 = 1),
        A002124 (m + 1 - p) := by
  set P := (Finset.range (m + 2)).filter (fun p => Nat.Prime p ∧ p % 2 = 1)
  have hunion : { l : List ℕ | IsOddPrimeComp (m + 1) l } =
      ⋃ p ∈ (P : Set ℕ), (List.cons p) '' { t : List ℕ | IsOddPrimeComp (m + 1 - p) t } := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, P, Finset.mem_filter,
      Finset.mem_range, Set.mem_image]
    constructor
    · intro hl
      cases l with
      | nil => simp [IsOddPrimeComp] at hl
      | cons p t =>
        have hp := hl.2 p (by simp)
        have hsum : p + t.sum = m + 1 := by simpa using hl.1
        exact ⟨p, ⟨by omega, hp⟩, t, ⟨by omega, fun q hq => hl.2 q (by simp [hq])⟩, rfl⟩
    · rintro ⟨p, ⟨hplt, hp⟩, t, ⟨htsum, ht⟩, rfl⟩
      refine ⟨by simp; omega, fun q hq => ?_⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hqt
      · exact hp
      · exact ht q hqt
  have hcard_union : Set.ncard (⋃ p ∈ (P : Set ℕ),
      (List.cons p) '' { t : List ℕ | IsOddPrimeComp (m + 1 - p) t }) =
      ∑ p ∈ P, Set.ncard ((List.cons p) '' { t : List ℕ | IsOddPrimeComp (m + 1 - p) t }) := by
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p s hps ihs =>
      rw [Finset.coe_insert, Set.biUnion_insert, Finset.sum_insert hps]
      have hd : Disjoint ((List.cons p) '' { t : List ℕ | IsOddPrimeComp (m + 1 - p) t })
          (⋃ q ∈ (s : Set ℕ), (List.cons q) '' { t : List ℕ | IsOddPrimeComp (m + 1 - q) t }) := by
        rw [Set.disjoint_iUnion₂_right]
        intro q hq
        have hne : p ≠ q := fun h => hps (h ▸ hq)
        rw [Set.disjoint_left]
        rintro _ ⟨t1, _, rfl⟩ ⟨t2, _, hcons⟩
        exact hne (List.cons.inj hcons).1.symm
      have hfin1 : ((List.cons p) '' { t : List ℕ | IsOddPrimeComp (m + 1 - p) t }).Finite :=
        (finite_oddPrimeComp _).image _
      have hfin2 : (⋃ q ∈ (s : Set ℕ), (List.cons q) '' { t : List ℕ | IsOddPrimeComp (m + 1 - q) t }).Finite :=
        Set.Finite.biUnion (Finset.finite_toSet s) fun q _ => (finite_oddPrimeComp _).image _
      rw [Set.ncard_union_eq hd hfin1 hfin2, ihs]
  unfold A002124
  rw [hunion, hcard_union]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Set.ncard_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)]

private lemma oddPrimes_le25 :
    (Finset.range 26).filter (fun p => Nat.Prime p ∧ p % 2 = 1) =
      ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) := by
  decide

private lemma A002124_step_le25 (n : ℕ) (hn1 : 1 ≤ n) (hn25 : n ≤ 25) :
    A002124 n =
      (if 3 ≤ n then A002124 (n - 3) else 0) +
      (if 5 ≤ n then A002124 (n - 5) else 0) +
      (if 7 ≤ n then A002124 (n - 7) else 0) +
      (if 11 ≤ n then A002124 (n - 11) else 0) +
      (if 13 ≤ n then A002124 (n - 13) else 0) +
      (if 17 ≤ n then A002124 (n - 17) else 0) +
      (if 19 ≤ n then A002124 (n - 19) else 0) +
      (if 23 ≤ n then A002124 (n - 23) else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [A002124_succ]
  have hfilt : (Finset.range (m + 2)).filter (fun p => Nat.Prime p ∧ p % 2 = 1) =
      ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ).filter (fun p => p ≤ m + 1) := by
    rw [← oddPrimes_le25]
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hP⟩; exact ⟨⟨by omega, hP⟩, by omega⟩
    · rintro ⟨⟨_, hP⟩, hle⟩; exact ⟨by omega, hP⟩
  rw [hfilt, Finset.sum_filter]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private lemma A002124_val_25 : A002124 25 = 125 := by
  have h0 : A002124 0 = 1 := A002124_zero
  have h1 : A002124 1 = 0 := by rw [A002124_step_le25 1 (by omega) (by omega)]; norm_num
  have h2 : A002124 2 = 0 := by rw [A002124_step_le25 2 (by omega) (by omega)]; norm_num
  have h3 : A002124 3 = 1 := by rw [A002124_step_le25 3 (by omega) (by omega)]; norm_num [h0]
  have h4 : A002124 4 = 0 := by rw [A002124_step_le25 4 (by omega) (by omega)]; norm_num [h1]
  have h5 : A002124 5 = 1 := by rw [A002124_step_le25 5 (by omega) (by omega)]; norm_num [h0, h2]
  have h6 : A002124 6 = 1 := by rw [A002124_step_le25 6 (by omega) (by omega)]; norm_num [h1, h3]
  have h7 : A002124 7 = 1 := by rw [A002124_step_le25 7 (by omega) (by omega)]; norm_num [h0, h2, h4]
  have h8 : A002124 8 = 2 := by rw [A002124_step_le25 8 (by omega) (by omega)]; norm_num [h1, h3, h5]
  have h9 : A002124 9 = 1 := by rw [A002124_step_le25 9 (by omega) (by omega)]; norm_num [h2, h4, h6]
  have h10 : A002124 10 = 3 := by rw [A002124_step_le25 10 (by omega) (by omega)]; norm_num [h3, h5, h7]
  have h11 : A002124 11 = 4 := by rw [A002124_step_le25 11 (by omega) (by omega)]; norm_num [h0, h4, h6, h8]
  have h12 : A002124 12 = 3 := by rw [A002124_step_le25 12 (by omega) (by omega)]; norm_num [h1, h5, h7, h9]
  have h13 : A002124 13 = 7 := by rw [A002124_step_le25 13 (by omega) (by omega)]; norm_num [h0, h2, h6, h8, h10]
  have h14 : A002124 14 = 7 := by rw [A002124_step_le25 14 (by omega) (by omega)]; norm_num [h1, h3, h7, h9, h11]
  have h15 : A002124 15 = 8 := by rw [A002124_step_le25 15 (by omega) (by omega)]; norm_num [h2, h4, h8, h10, h12]
  have h16 : A002124 16 = 14 := by rw [A002124_step_le25 16 (by omega) (by omega)]; norm_num [h3, h5, h9, h11, h13]
  have h17 : A002124 17 = 15 := by rw [A002124_step_le25 17 (by omega) (by omega)]; norm_num [h0, h4, h6, h10, h12, h14]
  have h18 : A002124 18 = 21 := by rw [A002124_step_le25 18 (by omega) (by omega)]; norm_num [h1, h5, h7, h11, h13, h15]
  have h19 : A002124 19 = 28 := by rw [A002124_step_le25 19 (by omega) (by omega)]; norm_num [h0, h2, h6, h8, h12, h14, h16]
  have h20 : A002124 20 = 33 := by rw [A002124_step_le25 20 (by omega) (by omega)]; norm_num [h1, h3, h7, h9, h13, h15, h17]
  have h21 : A002124 21 = 47 := by rw [A002124_step_le25 21 (by omega) (by omega)]; norm_num [h2, h4, h8, h10, h14, h16, h18]
  have h22 : A002124 22 = 58 := by rw [A002124_step_le25 22 (by omega) (by omega)]; norm_num [h3, h5, h9, h11, h15, h17, h19]
  have h23 : A002124 23 = 76 := by rw [A002124_step_le25 23 (by omega) (by omega)]; norm_num [h0, h4, h6, h10, h12, h16, h18, h20]
  have h24 : A002124 24 = 103 := by rw [A002124_step_le25 24 (by omega) (by omega)]; norm_num [h1, h5, h7, h11, h13, h17, h19, h21]
  rw [A002124_step_le25 25 (by omega) (by omega)]
  norm_num [h2, h6, h8, h12, h14, h18, h20, h22]

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a002124.main := by
  intro hEq
  set A : PowerSeries ℤ := PowerSeries.mk fun n => (A002124 n : ℤ)
  have hId : (1 - (PowerSeries.X : PowerSeries ℤ) ^ 3 - PowerSeries.X ^ 5 -
      PowerSeries.X ^ 6 - PowerSeries.X ^ 7 + PowerSeries.X ^ 9) * A =
      1 - PowerSeries.X ^ 6 := by
    convert hEq using 1
    ring
  have hstep : ∀ n : ℕ,
      (A002124 n : ℤ) -
        (if 3 ≤ n then (A002124 (n - 3) : ℤ) else 0) -
        (if 5 ≤ n then (A002124 (n - 5) : ℤ) else 0) -
        (if 6 ≤ n then (A002124 (n - 6) : ℤ) else 0) -
        (if 7 ≤ n then (A002124 (n - 7) : ℤ) else 0) +
        (if 9 ≤ n then (A002124 (n - 9) : ℤ) else 0) =
      (if n = 0 then 1 else 0) - (if n = 6 then 1 else 0) := by
    intro n
    have hc := congrArg (PowerSeries.coeff n) hId
    rw [add_mul, sub_mul, sub_mul, sub_mul, sub_mul, one_mul,
      map_add, map_sub, map_sub, map_sub, map_sub, map_sub] at hc
    rw [coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq,
      coeff_X_pow_mul_eq, PowerSeries.coeff_one, PowerSeries.coeff_X_pow] at hc
    simp only [A, PowerSeries.coeff_mk] at hc
    exact hc
  have hrec : ∀ n : ℕ, 9 ≤ n →
      (A002124 n : ℤ) =
        (A002124 (n - 3) : ℤ) + (A002124 (n - 5) : ℤ) + (A002124 (n - 6) : ℤ) +
        (A002124 (n - 7) : ℤ) - (A002124 (n - 9) : ℤ) := by
    intro n hn
    have h := hstep n
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    linarith
  have h0 : (A002124 0 : ℤ) = 1 := by
    have h := hstep 0
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl, if_neg (by omega)] at h; linarith
  have h1 : (A002124 1 : ℤ) = 0 := by
    have h := hstep 1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; linarith
  have h2 : (A002124 2 : ℤ) = 0 := by
    have h := hstep 2
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; linarith
  have h3 : (A002124 3 : ℤ) = 1 := by
    have h := hstep 3
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; norm_num [h0] at h; linarith
  have h4 : (A002124 4 : ℤ) = 0 := by
    have h := hstep 4
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; norm_num [h1] at h; linarith
  have h5 : (A002124 5 : ℤ) = 1 := by
    have h := hstep 5
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; norm_num [h0, h2] at h; linarith
  have h6 : (A002124 6 : ℤ) = 1 := by
    have h := hstep 6
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl] at h; norm_num [h0, h1, h3] at h; linarith
  have h7 : (A002124 7 : ℤ) = 1 := by
    have h := hstep 7
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; norm_num [h0, h1, h2, h4] at h; linarith
  have h8 : (A002124 8 : ℤ) = 2 := by
    have h := hstep 8
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; norm_num [h1, h2, h3, h5] at h; linarith
  have h9 : (A002124 9 : ℤ) = 1 := by have h := hrec 9 (by omega); norm_num [h0, h2, h3, h4, h6] at h; exact_mod_cast h
  have h10 : (A002124 10 : ℤ) = 3 := by have h := hrec 10 (by omega); norm_num [h1, h3, h4, h5, h7] at h; exact h
  have h11 : (A002124 11 : ℤ) = 4 := by have h := hrec 11 (by omega); norm_num [h2, h4, h5, h6, h8] at h; exact h
  have h12 : (A002124 12 : ℤ) = 3 := by have h := hrec 12 (by omega); norm_num [h3, h5, h6, h7, h9] at h; exact h
  have h13 : (A002124 13 : ℤ) = 7 := by have h := hrec 13 (by omega); norm_num [h4, h6, h7, h8, h10] at h; exact h
  have h14 : (A002124 14 : ℤ) = 7 := by have h := hrec 14 (by omega); norm_num [h5, h7, h8, h9, h11] at h; exact h
  have h15 : (A002124 15 : ℤ) = 8 := by have h := hrec 15 (by omega); norm_num [h6, h8, h9, h10, h12] at h; exact h
  have h16 : (A002124 16 : ℤ) = 14 := by have h := hrec 16 (by omega); norm_num [h7, h9, h10, h11, h13] at h; exact h
  have h17 : (A002124 17 : ℤ) = 15 := by have h := hrec 17 (by omega); norm_num [h8, h10, h11, h12, h14] at h; exact h
  have h18 : (A002124 18 : ℤ) = 21 := by have h := hrec 18 (by omega); norm_num [h9, h11, h12, h13, h15] at h; exact h
  have h19 : (A002124 19 : ℤ) = 28 := by have h := hrec 19 (by omega); norm_num [h10, h12, h13, h14, h16] at h; exact h
  have h20 : (A002124 20 : ℤ) = 33 := by have h := hrec 20 (by omega); norm_num [h11, h13, h14, h15, h17] at h; exact h
  have h21 : (A002124 21 : ℤ) = 47 := by have h := hrec 21 (by omega); norm_num [h12, h14, h15, h16, h18] at h; exact h
  have h22 : (A002124 22 : ℤ) = 58 := by have h := hrec 22 (by omega); norm_num [h13, h15, h16, h17, h19] at h; exact h
  have h23 : (A002124 23 : ℤ) = 76 := by have h := hrec 23 (by omega); norm_num [h14, h16, h17, h18, h20] at h; exact h
  have h24 : (A002124 24 : ℤ) = 103 := by have h := hrec 24 (by omega); norm_num [h15, h17, h18, h19, h21] at h; exact h
  have h25 : (A002124 25 : ℤ) = 126 := by have h := hrec 25 (by omega); norm_num [h16, h18, h19, h20, h22] at h; exact h
  have htrue : (A002124 25 : ℤ) = 125 := by exact_mod_cast A002124_val_25
  linarith

end OMA.P_oeis_a002124

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002124.main) :=
  OMA.P_oeis_a002124.prove_disproof
