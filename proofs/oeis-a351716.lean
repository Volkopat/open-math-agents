import OMAStatements.S_oeis_a351716

-- Credit: @grp06
open OMA.S_oeis_a351716

private theorem lucasBound (j : ℕ) : j + 3 ≤ lucasTail j := by
  induction j using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more j h₀ h₁ => rw [lucasTail]; omega

private theorem lucasIncreasing : StrictMono lucasTail := by
  apply strictMono_nat_of_lt_succ
  intro j
  cases j with
  | zero => decide
  | succ k =>
    change lucasTail (k+1) < lucasTail (k+1) + lucasTail k
    have := lucasBound k
    omega

private theorem weightInBlock {j n : ℕ} (lo : lucasTail j ≤ n)
    (hi : n < lucasTail (j+1)) :
    greedyWeight n = 1 + greedyWeight (n - lucasTail j) := by
  have bound := lucasBound j
  have greatest : Nat.findGreatest (fun k => lucasTail k ≤ n) n = j := by
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨by omega, fun _ => lo, ?_⟩
    intro k hjk _ hk
    have := lucasIncreasing.monotone (show j+1 ≤ k by omega)
    omega
  rw [greedyWeight, dif_neg (by omega), largestLucas, if_neg (by omega), greatest]

private theorem blockAt {n : ℕ} (hn : 3 ≤ n) :
    ∃ j, lucasTail j ≤ n ∧ n < lucasTail (j+1) := by
  let j := Nat.findGreatest (fun k => lucasTail k ≤ n) n
  have lo : lucasTail j ≤ n :=
    Nat.findGreatest_spec (P := fun k => lucasTail k ≤ n) (m := 0) (Nat.zero_le n) (show lucasTail 0 ≤ n from hn)
  refine ⟨j, lo, ?_⟩
  by_contra! bad
  have := lucasBound (j+1)
  have hj : j+1 ≤ j := Nat.le_findGreatest (by omega : j+1 ≤ n) bad
  omega

private theorem w0 : greedyWeight 0 = 0 := by rw [greedyWeight]; rfl
private theorem w1 : greedyWeight 1 = 1 := by
  rw [greedyWeight]; change 1 + greedyWeight 0 = 1; rw [w0]
private theorem w2 : greedyWeight 2 = 1 := by
  rw [greedyWeight]; change 1 + greedyWeight 0 = 1; rw [w0]
private theorem w3 : greedyWeight 3 = 1 := by
  rw [greedyWeight]; change 1 + greedyWeight 0 = 1; rw [w0]
private theorem w4 : greedyWeight 4 = 1 := by
  rw [greedyWeight]; change 1 + greedyWeight 0 = 1; rw [w0]
private theorem w5 : greedyWeight 5 = 2 := by
  rw [greedyWeight]; change 1 + greedyWeight 1 = 2; rw [w1]

private theorem weightPos {n : ℕ} (h : 0 < n) : 0 < greedyWeight n := by
  rw [greedyWeight, dif_neg (by omega)]
  omega

-- The last two places before each Lucas boundary have the same weight.
private theorem beforeBoundary (j : ℕ) :
    greedyWeight (lucasTail j - 2) = greedyWeight (lucasTail j - 1) ∧
    (2 ≤ j → 2 ≤ greedyWeight (lucasTail j - 2)) := by
  induction j using Nat.twoStepInduction with
  | zero => change greedyWeight 1 = greedyWeight 2 ∧ _; exact ⟨w1.trans w2.symm, by omega⟩
  | one => change greedyWeight 2 = greedyWeight 3 ∧ _; exact ⟨w2.trans w3.symm, by omega⟩
  | more k hk _ =>
    have h := lucasBound k
    have b : lucasTail (k+2) = lucasTail (k+1) + lucasTail k := rfl
    have two := weightInBlock (j := k+1) (n := lucasTail (k+2)-2) (by omega) (by change _ < lucasTail (k+2); omega)
    have one := weightInBlock (j := k+1) (n := lucasTail (k+2)-1) (by omega) (by change _ < lucasTail (k+2); omega)
    rw [show lucasTail (k+2)-2-lucasTail (k+1) = lucasTail k-2 by omega] at two
    rw [show lucasTail (k+2)-1-lucasTail (k+1) = lucasTail k-1 by omega] at one
    have := weightPos (n := lucasTail k - 2) (by omega)
    exact ⟨by rw [two, one, hk.1], by omega⟩

private theorem adjacentWeights (n : ℕ) :
    ∃ t, n ≤ t ∧ t ≤ n+2 ∧ greedyWeight t = greedyWeight (t+1) ∧
      0 < greedyWeight t ∧ (5 ≤ n → 2 ≤ greedyWeight t) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 4
    · interval_cases n
      · exact ⟨1, by decide, by decide, w1.trans w2.symm, by rw [w1]; decide, by omega⟩
      · exact ⟨1, by decide, by decide, w1.trans w2.symm, by rw [w1]; decide, by omega⟩
      · exact ⟨2, by decide, by decide, w2.trans w3.symm, by rw [w2]; decide, by omega⟩
      · exact ⟨3, by decide, by decide, w3.trans w4.symm, by rw [w3]; decide, by omega⟩
    obtain ⟨j, lo, hi⟩ := blockAt (n := n) (by omega)
    have hL := lucasBound j
    by_cases inside : n+3 < lucasTail (j+1)
    · obtain ⟨t, tlo, thi, eq, pos, _⟩ := ih (n-lucasTail j) (by omega)
      have left := weightInBlock (j := j) (n := lucasTail j+t) (by omega) (by omega)
      have right := weightInBlock (j := j) (n := lucasTail j+t+1) (by omega) (by omega)
      rw [show lucasTail j+t-lucasTail j=t by omega] at left
      rw [show lucasTail j+t+1-lucasTail j=t+1 by omega] at right
      exact ⟨lucasTail j+t, by omega, by omega, by omega, by omega, by omega⟩
    · have jpos : 0 < j := by
        by_contra! hj
        have : j = 0 := by omega
        subst j
        change n < 4 at hi
        omega
      by_cases ends : n ≤ lucasTail (j+1)-2
      · obtain ⟨eq, strong⟩ := beforeBoundary (j+1)
        have lower := strong (by omega)
        have limit := lucasBound (j+1)
        refine ⟨lucasTail (j+1)-2, by omega, by omega, ?_, by omega, by omega⟩
        rwa [show lucasTail (j+1)-2+1 = lucasTail (j+1)-1 by omega]
      · have step : lucasTail (j+2) = lucasTail (j+1) + lucasTail j := rfl
        have left := weightInBlock (j := j+1) (n := lucasTail (j+1)+1) (by omega) (by change _ < lucasTail (j+2); omega)
        have right := weightInBlock (j := j+1) (n := lucasTail (j+1)+1+1) (by omega) (by change _ < lucasTail (j+2); omega)
        rw [show lucasTail (j+1)+1-lucasTail (j+1)=1 by omega, w1] at left
        rw [show lucasTail (j+1)+1+1-lucasTail (j+1)=2 by omega, w2] at right
        exact ⟨lucasTail (j+1)+1, by omega, by omega, by omega, by omega, by omega⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a351716.main := by
  intro n
  constructor
  · intro run
    by_cases big : 5 ≤ n
    · obtain ⟨t, lo, hi, eq, _, lower⟩ := adjacentWeights n
      have both (k : ℕ) (hk : n ≤ k) (hk' : k ≤ n+3) : greedyWeight k ∣ k := by
        have d := (run ⟨k-n, by omega⟩).2
        simpa [Nat.add_sub_of_le hk] using d
      have left := both t lo (by omega)
      have right := both (t+1) (by omega) (by omega)
      rw [← eq] at right
      have one : greedyWeight t ∣ 1 := by simpa using Nat.dvd_sub right left
      have := Nat.le_of_dvd (by decide : 0 < 1) one
      have := lower big
      omega
    · have empty : ¬ IsLucasNiven 0 := by simp [IsLucasNiven]
      have five : ¬ IsLucasNiven 5 := by simp [IsLucasNiven, w5]
      interval_cases n
      · exact (empty (run 0)).elim
      · rfl
      · exact (five (run 3)).elim
      · exact (five (run 2)).elim
      · exact (five (run 1)).elim
  · rintro rfl i
    fin_cases i <;> norm_num [IsLucasNiven, w1, w2, w3, w4]
