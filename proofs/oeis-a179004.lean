import OMAStatements.S_oeis_a179004
import Mathlib

/-!
# Proof of `oeis-a179004`

Proves that the maximum density `GridAnti.best n m / (n * m)` of ones in a binary `n × m` grid
where every cell has at least half its orthogonal neighbors of the opposite value converges to
`2 / 3` as `n, m → ∞`.

1. **Upper bound (`3 * best n m ≤ 2 * n * m + n + m`)**: double-counting directed edges from
   `true` cells to `false` cells gives `4 * ones c - 2 * (n + m) ≤ 2 * E ≤ 8 * (n * m - ones c)`.
2. **Lower bound (`3 * best n m ≥ 2 * (n - 2) * (m - 2) - 2 * (n - 2)`)**: an explicit `Happy`
   configuration based on `(i + j) % 3 ≠ 0` in the interior with a border/corner adjustment.
3. Combining both bounds yields `|best n m / (n * m) - 2 / 3| ≤ 2 / n + 2 / m`.
-/

namespace OMA.A179004Proof

open GridAnti Finset

private lemma adj_symm {n m : ℕ} {v w : Cell n m} (h : Adj v w) : Adj w v := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

private lemma card_neighbors_eq {n m : ℕ} (v : Cell n m) :
    (neighbors v).card =
      (if v.1.val + 1 < n then 1 else 0) + (if 0 < v.1.val then 1 else 0) +
      (if v.2.val + 1 < m then 1 else 0) + (if 0 < v.2.val then 1 else 0) := by
  let A : Finset (Cell n m) := if h : v.1.val + 1 < n then {(⟨v.1.val + 1, h⟩, v.2)} else ∅
  let B : Finset (Cell n m) := if h : 0 < v.1.val then {(⟨v.1.val - 1, by omega⟩, v.2)} else ∅
  let C : Finset (Cell n m) := if h : v.2.val + 1 < m then {(v.1, ⟨v.2.val + 1, h⟩)} else ∅
  let D : Finset (Cell n m) := if h : 0 < v.2.val then {(v.1, ⟨v.2.val - 1, by omega⟩)} else ∅
  have heq : neighbors v = A ∪ B ∪ C ∪ D := by
    ext w
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      A, B, C, D]
    constructor
    · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
      · left; right; rw [dif_pos (by omega), Finset.mem_singleton]
        exact Prod.ext h1.symm (Fin.ext h2.symm)
      · right; rw [dif_pos (by omega), Finset.mem_singleton]
        exact Prod.ext h1.symm (Fin.ext (by dsimp; omega))
      · left; left; left; rw [dif_pos (by omega), Finset.mem_singleton]
        exact Prod.ext (Fin.ext h2.symm) h1.symm
      · left; left; right; rw [dif_pos (by omega), Finset.mem_singleton]
        exact Prod.ext (Fin.ext (by dsimp; omega)) h1.symm
    · rintro (((hw | hw) | hw) | hw)
      · split_ifs at hw with h
        · rw [Finset.mem_singleton] at hw; subst hw; exact Or.inr ⟨rfl, Or.inl rfl⟩
        · simp at hw
      · split_ifs at hw with h
        · rw [Finset.mem_singleton] at hw; subst hw; exact Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩
        · simp at hw
      · split_ifs at hw with h
        · rw [Finset.mem_singleton] at hw; subst hw; exact Or.inl ⟨rfl, Or.inl rfl⟩
        · simp at hw
      · split_ifs at hw with h
        · rw [Finset.mem_singleton] at hw; subst hw; exact Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩
        · simp at hw
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]; intro w hA hB
    simp only [A, B] at hA hB
    split_ifs at hA with h1 <;> [skip; simp at hA]
    split_ifs at hB with h2 <;> [skip; simp at hB]
    rw [Finset.mem_singleton] at hA hB; subst hA
    have := congrArg (fun p : Cell n m => p.1.val) hB; dsimp at this; omega
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]; intro w h1 hC
    simp only [Finset.mem_union, A, B, C] at h1 hC
    split_ifs at hC with h3 <;> [skip; simp at hC]
    rw [Finset.mem_singleton] at hC; subst hC
    rcases h1 with hA | hB
    · split_ifs at hA with h1 <;> [skip; simp at hA]
      rw [Finset.mem_singleton] at hA
      have := congrArg (fun p : Cell n m => p.2.val) hA; dsimp at this; omega
    · split_ifs at hB with h2 <;> [skip; simp at hB]
      rw [Finset.mem_singleton] at hB
      have := congrArg (fun p : Cell n m => p.2.val) hB; dsimp at this; omega
  have hABCD : Disjoint (A ∪ B ∪ C) D := by
    rw [Finset.disjoint_left]; intro w h1 hD
    simp only [Finset.mem_union, A, B, C, D] at h1 hD
    split_ifs at hD with h4 <;> [skip; simp at hD]
    rw [Finset.mem_singleton] at hD; subst hD
    rcases h1 with (hA | hB) | hC
    · split_ifs at hA with h1 <;> [skip; simp at hA]
      rw [Finset.mem_singleton] at hA
      have := congrArg (fun p : Cell n m => p.2.val) hA; dsimp at this; omega
    · split_ifs at hB with h2 <;> [skip; simp at hB]
      rw [Finset.mem_singleton] at hB
      have := congrArg (fun p : Cell n m => p.2.val) hB; dsimp at this; omega
    · split_ifs at hC with h3 <;> [skip; simp at hC]
      rw [Finset.mem_singleton] at hC
      have := congrArg (fun p : Cell n m => p.2.val) hC; dsimp at this; omega
  rw [heq, Finset.card_union_of_disjoint hABCD, Finset.card_union_of_disjoint hABC,
    Finset.card_union_of_disjoint hAB]
  have cA : A.card = if v.1.val + 1 < n then 1 else 0 := by dsimp [A]; split_ifs <;> simp
  have cB : B.card = if 0 < v.1.val then 1 else 0 := by dsimp [B]; split_ifs <;> simp
  have cC : C.card = if v.2.val + 1 < m then 1 else 0 := by dsimp [C]; split_ifs <;> simp
  have cD : D.card = if 0 < v.2.val then 1 else 0 := by dsimp [D]; split_ifs <;> simp
  rw [cA, cB, cC, cD]

private lemma card_neighbors_le_four {n m : ℕ} (v : Cell n m) :
    (neighbors v).card ≤ 4 := by
  rw [card_neighbors_eq]
  split_ifs <;> omega

private lemma ones_upper {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {c : Cell n m → Bool}
    (hc : Happy c) : 3 * ones c ≤ 2 * n * m + n + m := by
  let T := (Finset.univ : Finset (Cell n m)).filter (fun v => c v = true)
  let F := (Finset.univ : Finset (Cell n m)).filter (fun v => c v = false)
  let E := (Finset.univ : Finset (Cell n m × Cell n m)).filter
    (fun p => Adj p.1 p.2 ∧ c p.1 = true ∧ c p.2 = false)
  have hET : E.card = ∑ v ∈ T, opp c v := by
    have h1 : E.card = ∑ v : Cell n m, ∑ w : Cell n m,
        if Adj v w ∧ c v = true ∧ c w = false then 1 else 0 := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
    rw [h1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : c v = true
    · rw [if_pos hv]
      simp only [opp, neighbors, Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hadj : Adj v w <;> cases hcw : c w <;> simp [hv, hadj]
    · rw [if_neg hv]
      apply Finset.sum_eq_zero
      intro w _
      simp [hv]
  have hEF : E.card = ∑ w ∈ F, opp c w := by
    have h1 : E.card = ∑ w : Cell n m, ∑ v : Cell n m,
        if Adj v w ∧ c v = true ∧ c w = false then 1 else 0 := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
    rw [h1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : c w = false
    · rw [if_pos hw]
      simp only [opp, neighbors, Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hadj : Adj w v
      · have hadj' : Adj v w := adj_symm hadj
        cases hcv : c v <;> simp [hw, hadj, hadj']
      · have hadj' : ¬ Adj v w := fun h => hadj (adj_symm h)
        simp [hw, hadj, hadj']
    · rw [if_neg hw]
      apply Finset.sum_eq_zero
      intro v _
      simp [hw]
  have hlow1 : ∑ v ∈ T, (neighbors v).card ≤ 2 * E.card := by
    rw [hET, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => hc v
  have hup1 : E.card ≤ 4 * F.card := by
    rw [hEF]
    calc ∑ w ∈ F, opp c w ≤ ∑ w ∈ F, (neighbors w).card :=
          Finset.sum_le_sum fun w _ => Finset.card_filter_le _ _
      _ ≤ ∑ _w ∈ F, 4 := Finset.sum_le_sum fun w _ => card_neighbors_le_four w
      _ = 4 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hTF : T.card + F.card = n * m := by
    have hdisj : Disjoint T F := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      rw [Finset.mem_filter] at h1 h2
      rw [h1.2] at h2; exact Bool.noConfusion h2.2
    have hunion : T ∪ F = Finset.univ := by
      ext v; simp only [T, F, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases c v <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  have hpen : ∀ v : Cell n m,
      4 ≤ (neighbors v).card +
        (if v.1.val = 0 then 1 else 0) + (if v.1.val + 1 = n then 1 else 0) +
        (if v.2.val = 0 then 1 else 0) + (if v.2.val + 1 = m then 1 else 0) := by
    intro v
    rw [card_neighbors_eq]
    have h1 := v.1.isLt; have h2 := v.2.isLt
    split_ifs <;> omega
  have hsum_pen : 4 * T.card ≤ (∑ v ∈ T, (neighbors v).card) + 2 * m + 2 * n := by
    have h1 : 4 * T.card ≤ ∑ v ∈ T, ((neighbors v).card +
        (if v.1.val = 0 then 1 else 0) + (if v.1.val + 1 = n then 1 else 0) +
        (if v.2.val = 0 then 1 else 0) + (if v.2.val + 1 = m then 1 else 0)) := by
      calc 4 * T.card = ∑ _v ∈ T, 4 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun v _ => hpen v
    simp only [Finset.sum_add_distrib] at h1
    have s1 : ∑ v ∈ T, (if v.1.val = 0 then 1 else 0) ≤ m := by
      calc ∑ v ∈ T, (if v.1.val = 0 then 1 else 0)
          ≤ ∑ v : Cell n m, (if v.1.val = 0 then 1 else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = ∑ i : Fin n, ∑ _j : Fin m, (if i.val = 0 then 1 else 0) := Fintype.sum_prod_type _
        _ = m := by
            have h0 : (⟨0, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
            rw [Finset.sum_eq_single ⟨0, by omega⟩]
            · simp
            · intro i _ hi
              have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
              simp [hne]
            · intro h; exact (h h0).elim
    have s2 : ∑ v ∈ T, (if v.1.val + 1 = n then 1 else 0) ≤ m := by
      calc ∑ v ∈ T, (if v.1.val + 1 = n then 1 else 0)
          ≤ ∑ v : Cell n m, (if v.1.val + 1 = n then 1 else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = ∑ i : Fin n, ∑ _j : Fin m, (if i.val + 1 = n then 1 else 0) := Fintype.sum_prod_type _
        _ = m := by
            have h0 : (⟨n - 1, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
            rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
            · simp [show n - 1 + 1 = n by omega]
            · intro i _ hi
              have hne : i.val + 1 ≠ n := fun h => hi (Fin.ext (by dsimp; omega))
              simp [hne]
            · intro h; exact (h h0).elim
    have s3 : ∑ v ∈ T, (if v.2.val = 0 then 1 else 0) ≤ n := by
      calc ∑ v ∈ T, (if v.2.val = 0 then 1 else 0)
          ≤ ∑ v : Cell n m, (if v.2.val = 0 then 1 else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = ∑ j : Fin m, ∑ _i : Fin n, (if j.val = 0 then 1 else 0) := Fintype.sum_prod_type_right _
        _ = n := by
            have h0 : (⟨0, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
            rw [Finset.sum_eq_single ⟨0, by omega⟩]
            · simp
            · intro j _ hj
              have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
              simp [hne]
            · intro h; exact (h h0).elim
    have s4 : ∑ v ∈ T, (if v.2.val + 1 = m then 1 else 0) ≤ n := by
      calc ∑ v ∈ T, (if v.2.val + 1 = m then 1 else 0)
          ≤ ∑ v : Cell n m, (if v.2.val + 1 = m then 1 else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = ∑ j : Fin m, ∑ _i : Fin n, (if j.val + 1 = m then 1 else 0) := Fintype.sum_prod_type_right _
        _ = n := by
            have h0 : (⟨m - 1, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
            rw [Finset.sum_eq_single ⟨m - 1, by omega⟩]
            · simp [show m - 1 + 1 = m by omega]
            · intro j _ hj
              have hne : j.val + 1 ≠ m := fun h => hj (Fin.ext (by dsimp; omega))
              simp [hne]
            · intro h; exact (h h0).elim
    omega
  have hT_eq : T.card = ones c := rfl
  have h2nm : 2 * n * m = 2 * (n * m) := by ring
  omega

private lemma best_upper {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    3 * best n m ≤ 2 * n * m + n + m := by
  classical
  unfold best
  have hle : ∀ c ∈ Finset.univ.filter (fun c : Cell n m → Bool => Happy c),
      ones c ≤ (2 * n * m + n + m) / 3 := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have := ones_upper hn hm hc.2
    omega
  have h1 := Finset.sup_le hle
  omega

private def goodCfg (n m : ℕ) (v : Cell n m) : Bool :=
  if v.1.val = 0 ∧ v.2.val = 0 then true
  else if v.1.val = 0 ∧ v.2.val + 1 = m then decide (m % 3 ≠ 1)
  else if v.1.val + 1 = n ∧ v.2.val = 0 then decide (n % 3 ≠ 1)
  else if v.1.val + 1 = n ∧ v.2.val + 1 = m then decide ((n + m) % 3 ≠ 1)
  else if v.1.val = 0 ∧ (v.1.val + v.2.val) % 3 = 1 then false
  else if v.2.val = 0 ∧ (v.1.val + v.2.val) % 3 = 1 then false
  else if v.1.val + 1 = n ∧ (v.1.val + v.2.val) % 3 = 2 then false
  else if v.2.val + 1 = m ∧ (v.1.val + v.2.val) % 3 = 2 then false
  else decide ((v.1.val + v.2.val) % 3 ≠ 0)

private lemma opp_ge_of_one {n m : ℕ} {c : Cell n m → Bool} {v w : Cell n m}
    (h1 : Adj v w) (h2 : c w ≠ c v) : 1 ≤ opp c v := by
  unfold opp
  refine Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩⟩

private lemma opp_ge_of_two {n m : ℕ} {c : Cell n m → Bool} {v w₁ w₂ : Cell n m}
    (hne : w₁ ≠ w₂) (ha1 : Adj v w₁) (ha2 : Adj v w₂) (hb1 : c w₁ ≠ c v) (hb2 : c w₂ ≠ c v) :
    2 ≤ opp c v := by
  unfold opp
  have hsub : ({w₁, w₂} : Finset (Cell n m)) ⊆ (neighbors v).filter (fun w => c w ≠ c v) := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha1⟩, hb1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2⟩, hb2⟩
  calc 2 = ({w₁, w₂} : Finset (Cell n m)).card := (Finset.card_pair hne).symm
    _ ≤ ((neighbors v).filter (fun w => c w ≠ c v)).card := Finset.card_le_card hsub

private lemma goodCfg_int {n m : ℕ} {i j : ℕ} (hi : i < n) (hj : j < m)
    (hi0 : 0 < i) (hin : i + 1 < n) (hj0 : 0 < j) (hjm : j + 1 < m) :
    goodCfg n m (⟨i, hi⟩, ⟨j, hj⟩) = decide ((i + j) % 3 ≠ 0) := by
  unfold goodCfg
  simp [show i ≠ 0 by omega, show j ≠ 0 by omega, show i + 1 ≠ n by omega, show j + 1 ≠ m by omega]

private lemma goodCfg_top {n m : ℕ} {j : ℕ} (hn : 4 ≤ n) (hj : j < m) (hj0 : 0 < j) (hjm : j + 1 < m) :
    goodCfg n m (⟨0, by omega⟩, ⟨j, hj⟩) = decide (j % 3 = 2) := by
  unfold goodCfg
  simp only [show j ≠ 0 by omega, show j + 1 ≠ m by omega, show (0 : ℕ) + 1 ≠ n by omega,
    and_false, false_and, ↓reduceIte, true_and, zero_add]
  rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with h | h | h <;> simp [h]

private lemma goodCfg_bot {n m : ℕ} {j : ℕ} (hn : 4 ≤ n) (hj : j < m) (hj0 : 0 < j) (hjm : j + 1 < m) :
    goodCfg n m (⟨n - 1, by omega⟩, ⟨j, hj⟩) = decide ((n - 1 + j) % 3 = 1) := by
  unfold goodCfg
  simp only [show n - 1 ≠ 0 by omega, show n - 1 + 1 = n by omega, show j ≠ 0 by omega,
    show j + 1 ≠ m by omega, and_false, false_and, ↓reduceIte, true_and]
  rcases (show (n - 1 + j) % 3 = 0 ∨ (n - 1 + j) % 3 = 1 ∨ (n - 1 + j) % 3 = 2 by omega) with h | h | h <;>
    simp [h]

private lemma goodCfg_left {n m : ℕ} {i : ℕ} (hm : 4 ≤ m) (hi : i < n) (hi0 : 0 < i) (hin : i + 1 < n) :
    goodCfg n m (⟨i, hi⟩, ⟨0, by omega⟩) = decide (i % 3 = 2) := by
  unfold goodCfg
  simp only [show i ≠ 0 by omega, show i + 1 ≠ n by omega, show (0 : ℕ) + 1 ≠ m by omega,
    and_false, false_and, ↓reduceIte, true_and, add_zero]
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h <;> simp [h]

private lemma goodCfg_right {n m : ℕ} {i : ℕ} (hm : 4 ≤ m) (hi : i < n) (hi0 : 0 < i) (hin : i + 1 < n) :
    goodCfg n m (⟨i, hi⟩, ⟨m - 1, by omega⟩) = decide ((i + (m - 1)) % 3 = 1) := by
  unfold goodCfg
  simp only [show i ≠ 0 by omega, show i + 1 ≠ n by omega, show m - 1 ≠ 0 by omega,
    show m - 1 + 1 = m by omega, and_false, false_and, ↓reduceIte, true_and]
  rcases (show (i + (m - 1)) % 3 = 0 ∨ (i + (m - 1)) % 3 = 1 ∨ (i + (m - 1)) % 3 = 2 by omega) with h | h | h <;>
    simp [h]

private lemma goodCfg_c00 {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    goodCfg n m (⟨0, by omega⟩, ⟨0, by omega⟩) = true := by
  unfold goodCfg; simp

private lemma goodCfg_c0m {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    goodCfg n m (⟨0, by omega⟩, ⟨m - 1, by omega⟩) = decide (m % 3 ≠ 1) := by
  unfold goodCfg
  simp [show m - 1 ≠ 0 by omega, show m - 1 + 1 = m by omega]

private lemma goodCfg_cn0 {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    goodCfg n m (⟨n - 1, by omega⟩, ⟨0, by omega⟩) = decide (n % 3 ≠ 1) := by
  unfold goodCfg
  simp [show n - 1 ≠ 0 by omega, show n - 1 + 1 = n by omega, show (0 : ℕ) + 1 ≠ m by omega]

private lemma goodCfg_cnm {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    goodCfg n m (⟨n - 1, by omega⟩, ⟨m - 1, by omega⟩) = decide ((n + m) % 3 ≠ 1) := by
  unfold goodCfg
  simp [show n - 1 ≠ 0 by omega, show n - 1 + 1 = n by omega,
    show m - 1 ≠ 0 by omega, show m - 1 + 1 = m by omega]

private lemma goodCfg_val_top_or_c {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) {j : ℕ} (hj : j < m) :
    goodCfg n m (⟨0, by omega⟩, ⟨j, hj⟩) =
      if j = 0 then true else if j + 1 = m then decide (m % 3 ≠ 1) else decide (j % 3 = 2) := by
  by_cases h0 : j = 0
  · subst h0; simp [goodCfg_c00 hn hm]
  · by_cases hm1 : j + 1 = m
    · have hj_eq : j = m - 1 := by omega
      subst hj_eq
      simp [h0, hm1, goodCfg_c0m hn hm]
    · simp [h0, hm1, goodCfg_top hn hj (by omega) (by omega)]

private lemma goodCfg_val_bot_or_c {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) {j : ℕ} (hj : j < m) :
    goodCfg n m (⟨n - 1, by omega⟩, ⟨j, hj⟩) =
      if j = 0 then decide (n % 3 ≠ 1)
      else if j + 1 = m then decide ((n + m) % 3 ≠ 1)
      else decide ((n - 1 + j) % 3 = 1) := by
  by_cases h0 : j = 0
  · subst h0; simp [goodCfg_cn0 hn hm]
  · by_cases hm1 : j + 1 = m
    · have hj_eq : j = m - 1 := by omega
      subst hj_eq
      simp [h0, hm1, goodCfg_cnm hn hm]
    · simp [h0, hm1, goodCfg_bot hn hj (by omega) (by omega)]

private lemma goodCfg_val_left_or_c {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) {i : ℕ} (hi : i < n) :
    goodCfg n m (⟨i, hi⟩, ⟨0, by omega⟩) =
      if i = 0 then true else if i + 1 = n then decide (n % 3 ≠ 1) else decide (i % 3 = 2) := by
  by_cases h0 : i = 0
  · subst h0; simp [goodCfg_c00 hn hm]
  · by_cases hn1 : i + 1 = n
    · have hi_eq : i = n - 1 := by omega
      subst hi_eq
      simp [h0, hn1, goodCfg_cn0 hn hm]
    · simp [h0, hn1, goodCfg_left hm hi (by omega) (by omega)]

private lemma goodCfg_val_right_or_c {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) {i : ℕ} (hi : i < n) :
    goodCfg n m (⟨i, hi⟩, ⟨m - 1, by omega⟩) =
      if i = 0 then decide (m % 3 ≠ 1)
      else if i + 1 = n then decide ((n + m) % 3 ≠ 1)
      else decide ((i + (m - 1)) % 3 = 1) := by
  by_cases h0 : i = 0
  · subst h0; simp [goodCfg_c0m hn hm]
  · by_cases hn1 : i + 1 = n
    · have hi_eq : i = n - 1 := by omega
      subst hi_eq
      simp [h0, hn1, goodCfg_cnm hn hm]
    · simp [h0, hn1, goodCfg_right hm hi (by omega) (by omega)]

private lemma goodCfg_happy {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) : Happy (goodCfg n m) := by
  intro v
  rcases v with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [card_neighbors_eq]
  dsimp only
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      have hdeg : (if 0 + 1 < n then 1 else 0) + (if 0 < 0 then 1 else 0) +
          (if 0 + 1 < m then 1 else 0) + (if 0 < 0 then 1 else 0) = 2 := by split_ifs <;> omega
      rw [hdeg]
      have h1 : 1 ≤ opp (goodCfg n m) (⟨0, hi⟩, ⟨0, hj⟩) := by
        refine opp_ge_of_one (w := (⟨0, hi⟩, ⟨1, by omega⟩)) (Or.inl ⟨rfl, Or.inl rfl⟩) ?_
        rw [goodCfg_c00 hn hm, goodCfg_top hn (by omega) (by omega) (by omega)]; decide
      omega
    · by_cases hjm : j + 1 = m
      · have hj_eq : j = m - 1 := by omega
        subst hj_eq
        have hdeg : (if 0 + 1 < n then 1 else 0) + (if 0 < 0 then 1 else 0) +
            (if m - 1 + 1 < m then 1 else 0) + (if 0 < m - 1 then 1 else 0) = 2 := by split_ifs <;> omega
        rw [hdeg]
        have h1 : 1 ≤ opp (goodCfg n m) (⟨0, hi⟩, ⟨m - 1, hj⟩) := by
          refine opp_ge_of_one (w := (⟨0, hi⟩, ⟨m - 2, by omega⟩))
            (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_
          rw [goodCfg_c0m hn hm, goodCfg_top hn (by omega) (by omega) (by omega)]
          rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with h | h | h
          · simp [h, show (m - 2) % 3 = 1 by omega]
          · simp [h, show (m - 2) % 3 = 2 by omega]
          · simp [h, show (m - 2) % 3 = 0 by omega]
        omega
      · have hdeg : (if 0 + 1 < n then 1 else 0) + (if 0 < 0 then 1 else 0) +
            (if j + 1 < m then 1 else 0) + (if 0 < j then 1 else 0) = 3 := by split_ifs <;> omega
        rw [hdeg]
        have h2 : 2 ≤ opp (goodCfg n m) (⟨0, hi⟩, ⟨j, hj⟩) := by
          rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with hmod | hmod | hmod
          · refine opp_ge_of_two (w₁ := (⟨0, hi⟩, ⟨j - 1, by omega⟩))
              (w₂ := (⟨1, by omega⟩, ⟨j, hj⟩)) ?_
              (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inr ⟨rfl, Or.inl rfl⟩) ?_ ?_
            · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
            · rw [goodCfg_top hn hj (by omega) (by omega), goodCfg_val_top_or_c hn hm (by omega)]
              by_cases h1 : j - 1 = 0
              · rw [if_pos h1]; simp [hmod]
              · rw [if_neg h1, if_neg (by omega)]; simp [hmod, show (j - 1) % 3 = 2 by omega]
            · rw [goodCfg_top hn hj (by omega) (by omega),
                goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
              simp [hmod, show (1 + j) % 3 = 1 by omega]
          · refine opp_ge_of_two (w₁ := (⟨0, hi⟩, ⟨j + 1, by omega⟩))
              (w₂ := (⟨1, by omega⟩, ⟨j, hj⟩)) ?_
              (Or.inl ⟨rfl, Or.inl rfl⟩) (Or.inr ⟨rfl, Or.inl rfl⟩) ?_ ?_
            · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
            · rw [goodCfg_top hn hj (by omega) (by omega), goodCfg_val_top_or_c hn hm (by omega),
                if_neg (by omega)]
              by_cases h2 : j + 1 + 1 = m
              · rw [if_pos h2]
                have hm3 : m % 3 = 0 := by omega
                simp [hmod, hm3]
              · rw [if_neg h2]; simp [hmod, show (j + 1) % 3 = 2 by omega]
            · rw [goodCfg_top hn hj (by omega) (by omega),
                goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
              simp [hmod, show (1 + j) % 3 = 2 by omega]
          · refine opp_ge_of_two (w₁ := (⟨0, hi⟩, ⟨j - 1, by omega⟩))
              (w₂ := (⟨1, by omega⟩, ⟨j, hj⟩)) ?_
              (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inr ⟨rfl, Or.inl rfl⟩) ?_ ?_
            · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
            · rw [goodCfg_top hn hj (by omega) (by omega), goodCfg_val_top_or_c hn hm (by omega),
                if_neg (by omega), if_neg (by omega)]
              simp [hmod, show (j - 1) % 3 = 1 by omega]
            · rw [goodCfg_top hn hj (by omega) (by omega),
                goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
              simp [hmod, show (1 + j) % 3 = 0 by omega]
        omega
  · by_cases hin : i + 1 = n
    · have hi_eq : i = n - 1 := by omega
      subst hi_eq
      by_cases hj0 : j = 0
      · subst hj0
        have hdeg : (if n - 1 + 1 < n then 1 else 0) + (if 0 < n - 1 then 1 else 0) +
            (if 0 + 1 < m then 1 else 0) + (if 0 < 0 then 1 else 0) = 2 := by split_ifs <;> omega
        rw [hdeg]
        have h1 : 1 ≤ opp (goodCfg n m) (⟨n - 1, hi⟩, ⟨0, hj⟩) := by
          refine opp_ge_of_one (w := (⟨n - 2, by omega⟩, ⟨0, hj⟩))
            (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_
          rw [goodCfg_cn0 hn hm, goodCfg_left hm (by omega) (by omega) (by omega)]
          rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
          · simp [h, show (n - 2) % 3 = 1 by omega]
          · simp [h, show (n - 2) % 3 = 2 by omega]
          · simp [h, show (n - 2) % 3 = 0 by omega]
        omega
      · by_cases hjm : j + 1 = m
        · have hj_eq : j = m - 1 := by omega
          subst hj_eq
          have hdeg : (if n - 1 + 1 < n then 1 else 0) + (if 0 < n - 1 then 1 else 0) +
              (if m - 1 + 1 < m then 1 else 0) + (if 0 < m - 1 then 1 else 0) = 2 := by split_ifs <;> omega
          rw [hdeg]
          have h1 : 1 ≤ opp (goodCfg n m) (⟨n - 1, hi⟩, ⟨m - 1, hj⟩) := by
            refine opp_ge_of_one (w := (⟨n - 1, hi⟩, ⟨m - 2, by omega⟩))
              (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_
            rw [goodCfg_cnm hn hm, goodCfg_bot hn (by omega) (by omega) (by omega)]
            rcases (show (n + m) % 3 = 0 ∨ (n + m) % 3 = 1 ∨ (n + m) % 3 = 2 by omega) with h | h | h
            · simp [h, show (n - 1 + (m - 2)) % 3 = 0 by omega]
            · simp [h, show (n - 1 + (m - 2)) % 3 = 1 by omega]
            · simp [h, show (n - 1 + (m - 2)) % 3 = 2 by omega]
          omega
        · have hdeg : (if n - 1 + 1 < n then 1 else 0) + (if 0 < n - 1 then 1 else 0) +
              (if j + 1 < m then 1 else 0) + (if 0 < j then 1 else 0) = 3 := by split_ifs <;> omega
          rw [hdeg]
          have h2 : 2 ≤ opp (goodCfg n m) (⟨n - 1, hi⟩, ⟨j, hj⟩) := by
            rcases (show (n - 1 + j) % 3 = 0 ∨ (n - 1 + j) % 3 = 1 ∨ (n - 1 + j) % 3 = 2 by omega) with hmod | hmod | hmod
            · refine opp_ge_of_two (w₁ := (⟨n - 1, hi⟩, ⟨j + 1, by omega⟩))
                (w₂ := (⟨n - 2, by omega⟩, ⟨j, hj⟩)) ?_
                (Or.inl ⟨rfl, Or.inl rfl⟩) (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
              · rw [goodCfg_bot hn hj (by omega) (by omega), goodCfg_val_bot_or_c hn hm (by omega),
                  if_neg (by omega)]
                by_cases h2 : j + 1 + 1 = m
                · rw [if_pos h2]
                  have hnm : (n + m) % 3 = 0 := by omega
                  simp [hmod, hnm]
                · rw [if_neg h2]; simp [hmod, show (n - 1 + (j + 1)) % 3 = 1 by omega]
              · rw [goodCfg_bot hn hj (by omega) (by omega),
                  goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
                simp [hmod, show (n - 2 + j) % 3 = 2 by omega]
            · refine opp_ge_of_two (w₁ := (⟨n - 1, hi⟩, ⟨j + 1, by omega⟩))
                (w₂ := (⟨n - 2, by omega⟩, ⟨j, hj⟩)) ?_
                (Or.inl ⟨rfl, Or.inl rfl⟩) (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
              · rw [goodCfg_bot hn hj (by omega) (by omega), goodCfg_val_bot_or_c hn hm (by omega),
                  if_neg (by omega)]
                by_cases h2 : j + 1 + 1 = m
                · rw [if_pos h2]
                  have hnm1 : (n + m) % 3 = 1 := by omega
                  simp [hmod, hnm1]
                · rw [if_neg h2]; simp [hmod, show (n - 1 + (j + 1)) % 3 = 2 by omega]
              · rw [goodCfg_bot hn hj (by omega) (by omega),
                  goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
                simp [hmod, show (n - 2 + j) % 3 = 0 by omega]
            · refine opp_ge_of_two (w₁ := (⟨n - 1, hi⟩, ⟨j - 1, by omega⟩))
                (w₂ := (⟨n - 2, by omega⟩, ⟨j, hj⟩)) ?_
                (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
              · rw [goodCfg_bot hn hj (by omega) (by omega), goodCfg_val_bot_or_c hn hm (by omega)]
                by_cases h1 : j - 1 = 0
                · rw [if_pos h1]
                  have hn3 : n % 3 = 2 := by omega
                  simp [hmod, hn3]
                · rw [if_neg h1, if_neg (by omega)]
                  simp [hmod, show (n - 1 + (j - 1)) % 3 = 1 by omega]
              · rw [goodCfg_bot hn hj (by omega) (by omega),
                  goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
                simp [hmod, show (n - 2 + j) % 3 = 1 by omega]
          omega
    · by_cases hj0 : j = 0
      · subst hj0
        have hdeg : (if i + 1 < n then 1 else 0) + (if 0 < i then 1 else 0) +
            (if 0 + 1 < m then 1 else 0) + (if 0 < 0 then 1 else 0) = 3 := by split_ifs <;> omega
        rw [hdeg]
        have h2 : 2 ≤ opp (goodCfg n m) (⟨i, hi⟩, ⟨0, hj⟩) := by
          rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with hmod | hmod | hmod
          · refine opp_ge_of_two (w₁ := (⟨i - 1, by omega⟩, ⟨0, hj⟩))
              (w₂ := (⟨i, hi⟩, ⟨1, by omega⟩)) ?_
              (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inl ⟨rfl, Or.inl rfl⟩) ?_ ?_
            · intro heq; have := congrArg (fun p : Cell n m => p.2.val) heq; dsimp at this; omega
            · rw [goodCfg_left hm hi (by omega) (by omega), goodCfg_val_left_or_c hn hm (by omega)]
              by_cases h1 : i - 1 = 0
              · rw [if_pos h1]; simp [hmod]
              · rw [if_neg h1, if_neg (by omega)]; simp [hmod, show (i - 1) % 3 = 2 by omega]
            · rw [goodCfg_left hm hi (by omega) (by omega),
                goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
              simp [hmod, show (i + 1) % 3 = 1 by omega]
          · refine opp_ge_of_two (w₁ := (⟨i + 1, by omega⟩, ⟨0, hj⟩))
              (w₂ := (⟨i, hi⟩, ⟨1, by omega⟩)) ?_
              (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨rfl, Or.inl rfl⟩) ?_ ?_
            · intro heq; have := congrArg (fun p : Cell n m => p.2.val) heq; dsimp at this; omega
            · rw [goodCfg_left hm hi (by omega) (by omega), goodCfg_val_left_or_c hn hm (by omega),
                if_neg (by omega)]
              by_cases h2 : i + 1 + 1 = n
              · rw [if_pos h2]
                have hn3 : n % 3 = 0 := by omega
                simp [hmod, hn3]
              · rw [if_neg h2]; simp [hmod, show (i + 1) % 3 = 2 by omega]
            · rw [goodCfg_left hm hi (by omega) (by omega),
                goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
              simp [hmod, show (i + 1) % 3 = 2 by omega]
          · refine opp_ge_of_two (w₁ := (⟨i - 1, by omega⟩, ⟨0, hj⟩))
              (w₂ := (⟨i, hi⟩, ⟨1, by omega⟩)) ?_
              (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inl ⟨rfl, Or.inl rfl⟩) ?_ ?_
            · intro heq; have := congrArg (fun p : Cell n m => p.2.val) heq; dsimp at this; omega
            · rw [goodCfg_left hm hi (by omega) (by omega), goodCfg_val_left_or_c hn hm (by omega),
                if_neg (by omega), if_neg (by omega)]
              simp [hmod, show (i - 1) % 3 = 1 by omega]
            · rw [goodCfg_left hm hi (by omega) (by omega),
                goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
              simp [hmod, show (i + 1) % 3 = 0 by omega]
        omega
      · by_cases hjm : j + 1 = m
        · have hj_eq : j = m - 1 := by omega
          subst hj_eq
          have hdeg : (if i + 1 < n then 1 else 0) + (if 0 < i then 1 else 0) +
              (if m - 1 + 1 < m then 1 else 0) + (if 0 < m - 1 then 1 else 0) = 3 := by split_ifs <;> omega
          rw [hdeg]
          have h2 : 2 ≤ opp (goodCfg n m) (⟨i, hi⟩, ⟨m - 1, hj⟩) := by
            rcases (show (i + (m - 1)) % 3 = 0 ∨ (i + (m - 1)) % 3 = 1 ∨ (i + (m - 1)) % 3 = 2 by omega) with hmod | hmod | hmod
            · refine opp_ge_of_two (w₁ := (⟨i + 1, by omega⟩, ⟨m - 1, hj⟩))
                (w₂ := (⟨i, hi⟩, ⟨m - 2, by omega⟩)) ?_
                (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.2.val) heq; dsimp at this; omega
              · rw [goodCfg_right hm hi (by omega) (by omega), goodCfg_val_right_or_c hn hm (by omega),
                  if_neg (by omega)]
                by_cases h2 : i + 1 + 1 = n
                · rw [if_pos h2]
                  have hnm : (n + m) % 3 = 0 := by omega
                  simp [hmod, hnm]
                · rw [if_neg h2]
                  simp [hmod, show (i + 1 + (m - 1)) % 3 = 1 by omega]
              · rw [goodCfg_right hm hi (by omega) (by omega),
                  goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
                simp [hmod, show (i + (m - 2)) % 3 = 2 by omega]
            · refine opp_ge_of_two (w₁ := (⟨i + 1, by omega⟩, ⟨m - 1, hj⟩))
                (w₂ := (⟨i, hi⟩, ⟨m - 2, by omega⟩)) ?_
                (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.2.val) heq; dsimp at this; omega
              · rw [goodCfg_right hm hi (by omega) (by omega), goodCfg_val_right_or_c hn hm (by omega),
                  if_neg (by omega)]
                by_cases h2 : i + 1 + 1 = n
                · rw [if_pos h2]
                  have hnm1 : (n + m) % 3 = 1 := by omega
                  simp [hmod, hnm1]
                · rw [if_neg h2]
                  simp [hmod, show (i + 1 + (m - 1)) % 3 = 2 by omega]
              · rw [goodCfg_right hm hi (by omega) (by omega),
                  goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
                simp [hmod, show (i + (m - 2)) % 3 = 0 by omega]
            · refine opp_ge_of_two (w₁ := (⟨i - 1, by omega⟩, ⟨m - 1, hj⟩))
                (w₂ := (⟨i, hi⟩, ⟨m - 2, by omega⟩)) ?_
                (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.2.val) heq; dsimp at this; omega
              · rw [goodCfg_right hm hi (by omega) (by omega), goodCfg_val_right_or_c hn hm (by omega)]
                by_cases h1 : i - 1 = 0
                · rw [if_pos h1]
                  have hm3 : m % 3 = 2 := by omega
                  simp [hmod, hm3]
                · rw [if_neg h1, if_neg (by omega)]
                  simp [hmod, show (i - 1 + (m - 1)) % 3 = 1 by omega]
              · rw [goodCfg_right hm hi (by omega) (by omega),
                  goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
                simp [hmod, show (i + (m - 2)) % 3 = 1 by omega]
          omega
        · -- Interior cell: 1 ≤ i ≤ n - 2, 1 ≤ j ≤ m - 2
          have hdeg : (if i + 1 < n then 1 else 0) + (if 0 < i then 1 else 0) +
              (if j + 1 < m then 1 else 0) + (if 0 < j then 1 else 0) = 4 := by split_ifs <;> omega
          rw [hdeg]
          have h2 : 2 ≤ opp (goodCfg n m) (⟨i, hi⟩, ⟨j, hj⟩) := by
            rcases (show (i + j) % 3 = 0 ∨ (i + j) % 3 = 1 ∨ (i + j) % 3 = 2 by omega) with hmod | hmod | hmod
            · refine opp_ge_of_two (w₁ := (⟨i - 1, by omega⟩, ⟨j, hj⟩))
                (w₂ := (⟨i, hi⟩, ⟨j - 1, by omega⟩)) ?_
                (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
              · rw [goodCfg_int hi hj (by omega) (by omega) (by omega) (by omega)]
                by_cases h1 : i - 1 = 0
                · have hi1 : i = 1 := by omega
                  subst hi1
                  have heq : (⟨1 - 1, by omega⟩ : Fin n) = ⟨0, by omega⟩ := Fin.ext rfl
                  rw [heq, goodCfg_top hn hj (by omega) (by omega)]
                  simp [hmod, show j % 3 = 2 by omega]
                · rw [goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
                  simp [hmod, show (i - 1 + j) % 3 = 2 by omega]
              · rw [goodCfg_int hi hj (by omega) (by omega) (by omega) (by omega)]
                by_cases h1 : j - 1 = 0
                · have hj1 : j = 1 := by omega
                  subst hj1
                  have heq : (⟨1 - 1, by omega⟩ : Fin m) = ⟨0, by omega⟩ := Fin.ext rfl
                  rw [heq, goodCfg_left hm hi (by omega) (by omega)]
                  simp [hmod, show i % 3 = 2 by omega]
                · rw [goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
                  simp [hmod, show (i + (j - 1)) % 3 = 2 by omega]
            · refine opp_ge_of_two (w₁ := (⟨i - 1, by omega⟩, ⟨j, hj⟩))
                (w₂ := (⟨i, hi⟩, ⟨j - 1, by omega⟩)) ?_
                (Or.inr ⟨rfl, Or.inr (by dsimp; omega)⟩) (Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
              · rw [goodCfg_int hi hj (by omega) (by omega) (by omega) (by omega)]
                by_cases h1 : i - 1 = 0
                · have hi1 : i = 1 := by omega
                  subst hi1
                  have heq : (⟨1 - 1, by omega⟩ : Fin n) = ⟨0, by omega⟩ := Fin.ext rfl
                  rw [heq, goodCfg_top hn hj (by omega) (by omega)]
                  simp [hmod, show j % 3 = 0 by omega]
                · rw [goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
                  simp [hmod, show (i - 1 + j) % 3 = 0 by omega]
              · rw [goodCfg_int hi hj (by omega) (by omega) (by omega) (by omega)]
                by_cases h1 : j - 1 = 0
                · have hj1 : j = 1 := by omega
                  subst hj1
                  have heq : (⟨1 - 1, by omega⟩ : Fin m) = ⟨0, by omega⟩ := Fin.ext rfl
                  rw [heq, goodCfg_left hm hi (by omega) (by omega)]
                  simp [hmod, show i % 3 = 0 by omega]
                · rw [goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
                  simp [hmod, show (i + (j - 1)) % 3 = 0 by omega]
            · refine opp_ge_of_two (w₁ := (⟨i + 1, by omega⟩, ⟨j, hj⟩))
                (w₂ := (⟨i, hi⟩, ⟨j + 1, by omega⟩)) ?_
                (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨rfl, Or.inl rfl⟩) ?_ ?_
              · intro heq; have := congrArg (fun p : Cell n m => p.1.val) heq; dsimp at this; omega
              · rw [goodCfg_int hi hj (by omega) (by omega) (by omega) (by omega)]
                by_cases h1 : i + 1 + 1 = n
                · have hi1 : i + 1 = n - 1 := by omega
                  have heq : (⟨i + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext hi1
                  rw [heq, goodCfg_bot hn hj (by omega) (by omega)]
                  simp [hmod, show (n - 1 + j) % 3 = 0 by omega]
                · rw [goodCfg_int (by omega) hj (by omega) (by omega) (by omega) (by omega)]
                  simp [hmod, show (i + 1 + j) % 3 = 0 by omega]
              · rw [goodCfg_int hi hj (by omega) (by omega) (by omega) (by omega)]
                by_cases h1 : j + 1 + 1 = m
                · have hj1 : j + 1 = m - 1 := by omega
                  have heq : (⟨j + 1, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := Fin.ext hj1
                  rw [heq, goodCfg_right hm hi (by omega) (by omega)]
                  simp [hmod, show (i + (m - 1)) % 3 = 0 by omega]
                · rw [goodCfg_int hi (by omega) (by omega) (by omega) (by omega) (by omega)]
                  simp [hmod, show (i + (j + 1)) % 3 = 0 by omega]
          omega

private lemma count_mod3_nonzero' (a L : ℕ) :
    2 * L ≤ 3 * (∑ j ∈ Finset.range L, if (a + j) % 3 ≠ 0 then 1 else 0) + 2 := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    by_cases hL : L < 3
    · interval_cases L
      · simp
      · simp
      · simp [Finset.sum_range_succ]; split_ifs <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, L = k + 3 := ⟨L - 3, by omega⟩
      have hih := ih k (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have h3 : (if (a + k) % 3 ≠ 0 then 1 else 0) +
          (if (a + (k + 1)) % 3 ≠ 0 then 1 else 0) +
          (if (a + (k + 2)) % 3 ≠ 0 then 1 else 0) = 2 := by
        rcases (show (a + k) % 3 = 0 ∨ (a + k) % 3 = 1 ∨ (a + k) % 3 = 2 by omega) with h | h | h
        · simp [h, show (a + (k + 1)) % 3 = 1 by omega, show (a + (k + 2)) % 3 = 2 by omega]
        · simp [h, show (a + (k + 1)) % 3 = 2 by omega, show (a + (k + 2)) % 3 = 0 by omega]
        · simp [h, show (a + (k + 1)) % 3 = 0 by omega, show (a + (k + 2)) % 3 = 1 by omega]
      omega

private lemma best_lower {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    2 * (n - 2) * (m - 2) ≤ 3 * best n m + 2 * (n - 2) := by
  classical
  have hmem : goodCfg n m ∈ Finset.univ.filter (fun c : Cell n m → Bool => Happy c) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, goodCfg_happy hn hm⟩
  have hle : ones (goodCfg n m) ≤ best n m := by
    unfold best
    exact Finset.le_sup (f := ones) hmem
  have hones : 2 * (n - 2) * (m - 2) ≤ 3 * ones (goodCfg n m) + 2 * (n - 2) := by
    unfold ones
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have hrow : ∀ i : Fin n, 1 ≤ i.val → i.val + 1 < n →
        2 * (m - 2) ≤ 3 * (∑ j : Fin m, if goodCfg n m (i, j) = true then 1 else 0) + 2 := by
      intro i hi1 hi2
      have hsub : (∑ j ∈ Finset.range (m - 2), if (i.val + 1 + j) % 3 ≠ 0 then 1 else 0) ≤
          ∑ j : Fin m, if goodCfg n m (i, j) = true then 1 else 0 := by
        let S : Finset (Fin m) := (Finset.range (m - 2)).attach.image
          (fun x => ⟨x.1 + 1, by have := Finset.mem_range.mp x.2; omega⟩)
        calc (∑ j ∈ Finset.range (m - 2), if (i.val + 1 + j) % 3 ≠ 0 then 1 else 0)
            = ∑ x ∈ (Finset.range (m - 2)).attach, if (i.val + 1 + x.1) % 3 ≠ 0 then 1 else 0 := by
              rw [Finset.sum_attach (Finset.range (m - 2))
                (fun j => if (i.val + 1 + j) % 3 ≠ 0 then 1 else 0)]
          _ = ∑ j ∈ S, if goodCfg n m (i, j) = true then 1 else 0 := by
              refine Finset.sum_bij
                (fun x _ => ⟨x.1 + 1, by have := Finset.mem_range.mp x.2; omega⟩) ?_ ?_ ?_ ?_
              · intro x hx; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
              · intro x₁ _ x₂ _ heq
                exact Subtype.ext (by have := congrArg Fin.val heq; dsimp at this; omega)
              · intro j hj
                rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
                exact ⟨x, hx, rfl⟩
              · intro x _
                have hx := Finset.mem_range.mp x.2
                unfold goodCfg
                have h1 : i.val ≠ 0 := by omega
                have h2 : i.val + 1 ≠ n := by omega
                have h3 : x.1 + 1 ≠ 0 := by omega
                have h4 : x.1 + 1 + 1 ≠ m := by omega
                simp only [h1, h2, h3, h4, false_and, and_false, ↓reduceIte, decide_eq_true_eq]
                rw [show i.val + (x.1 + 1) = i.val + 1 + x.1 by omega]
          _ ≤ ∑ j : Fin m, if goodCfg n m (i, j) = true then 1 else 0 :=
              Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      have hc := count_mod3_nonzero' (i.val + 1) (m - 2)
      omega
    let R : Finset (Fin n) := (Finset.range (n - 2)).attach.image
      (fun x => ⟨x.1 + 1, by have := Finset.mem_range.mp x.2; omega⟩)
    have hRcard : R.card = n - 2 := by
      rw [Finset.card_image_of_injective]
      · rw [Finset.card_attach, Finset.card_range]
      · intro x₁ x₂ heq
        exact Subtype.ext (by have := congrArg Fin.val heq; dsimp at this; omega)
    have hsumR : ∑ i ∈ R, (2 * (m - 2)) ≤
        ∑ i ∈ R, (3 * (∑ j : Fin m, if goodCfg n m (i, j) = true then 1 else 0) + 2) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rcases Finset.mem_image.mp hi with ⟨x, _, rfl⟩
      have hx := Finset.mem_range.mp x.2
      exact hrow ⟨x.1 + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    rw [Finset.sum_const, smul_eq_mul, hRcard, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, smul_eq_mul, hRcard] at hsumR
    have hsubR : (∑ i ∈ R, ∑ j : Fin m, if goodCfg n m (i, j) = true then 1 else 0) ≤
        ∑ i : Fin n, ∑ j : Fin m, if goodCfg n m (i, j) = true then 1 else 0 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    have hmul : (n - 2) * (2 * (m - 2)) = 2 * (n - 2) * (m - 2) := by ring
    omega
  omega

theorem result : type_of% @OMA.S_oeis_a179004.main := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (6 / ε)
  refine ⟨max 4 K, by omega, fun n m hn hm => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_max_left 4 K) hn
  have hm4 : 4 ≤ m := le_trans (le_max_left 4 K) hm
  have hnK : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right 4 K) hn
  have hmK : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (le_max_right 4 K) hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hnm_pos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hn_pos hm_pos
  have hup_nat := best_upper (show 2 ≤ n by omega) (show 2 ≤ m by omega)
  have hlo_nat := best_lower hn4 hm4
  have hup : (3 : ℝ) * (best n m : ℝ) ≤ 2 * (n : ℝ) * (m : ℝ) + (n : ℝ) + (m : ℝ) := by
    exact_mod_cast hup_nat
  have hlo : 2 * ((n : ℝ) - 2) * ((m : ℝ) - 2) ≤ 3 * (best n m : ℝ) + 2 * ((n : ℝ) - 2) := by
    have h1 : ((2 * (n - 2) * (m - 2) : ℕ) : ℝ) ≤ ((3 * best n m + 2 * (n - 2) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hlo_nat
    have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := Nat.cast_sub (by omega)
    have hm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub (by omega)
    push_cast at h1
    rw [hn2, hm2] at h1
    linarith
  have h6n : 6 / (n : ℝ) < ε := by
    rw [div_lt_iff₀ hn_pos]
    have : 6 < ε * (K : ℝ) := by rwa [div_lt_iff₀ hε, mul_comm] at hK
    nlinarith
  have h6m : 6 / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hm_pos]
    have : 6 < ε * (K : ℝ) := by rwa [div_lt_iff₀ hε, mul_comm] at hK
    nlinarith
  rw [abs_lt]
  constructor
  · have hdiff : (2 : ℝ) / 3 - (best n m : ℝ) / ((n : ℝ) * (m : ℝ)) ≤
        (6 * (n : ℝ) + 4 * (m : ℝ)) / (3 * ((n : ℝ) * (m : ℝ))) := by
      rw [sub_le_iff_le_add]
      have h3nm : (0 : ℝ) < 3 * ((n : ℝ) * (m : ℝ)) := by positivity
      rw [div_add_div _ _ (ne_of_gt h3nm) (ne_of_gt hnm_pos),
        div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) (mul_pos h3nm hnm_pos)]
      nlinarith
    have hbound : (6 * (n : ℝ) + 4 * (m : ℝ)) / (3 * ((n : ℝ) * (m : ℝ))) ≤
        2 / (m : ℝ) + 2 / (n : ℝ) := by
      have h3nm : (0 : ℝ) < 3 * ((n : ℝ) * (m : ℝ)) := by positivity
      rw [div_add_div _ _ (ne_of_gt hm_pos) (ne_of_gt hn_pos),
        div_le_div_iff₀ h3nm (mul_pos hm_pos hn_pos)]
      nlinarith
    linarith [show 2 / (m : ℝ) + 2 / (n : ℝ) = (6 / (m : ℝ) + 6 / (n : ℝ)) / 3 by ring]
  · have hdiff : (best n m : ℝ) / ((n : ℝ) * (m : ℝ)) - 2 / 3 ≤
        ((n : ℝ) + (m : ℝ)) / (3 * ((n : ℝ) * (m : ℝ))) := by
      have h3nm : (0 : ℝ) < 3 * ((n : ℝ) * (m : ℝ)) := by positivity
      rw [sub_le_iff_le_add, div_add_div _ _ (ne_of_gt h3nm) (by norm_num : (3 : ℝ) ≠ 0),
        div_le_div_iff₀ hnm_pos (mul_pos h3nm (by norm_num : (0 : ℝ) < 3))]
      nlinarith
    have hbound : ((n : ℝ) + (m : ℝ)) / (3 * ((n : ℝ) * (m : ℝ))) ≤
        1 / (m : ℝ) + 1 / (n : ℝ) := by
      have h3nm : (0 : ℝ) < 3 * ((n : ℝ) * (m : ℝ)) := by positivity
      rw [div_add_div _ _ (ne_of_gt hm_pos) (ne_of_gt hn_pos),
        div_le_div_iff₀ h3nm (mul_pos hm_pos hn_pos)]
      nlinarith
    linarith [show 1 / (m : ℝ) + 1 / (n : ℝ) = (6 / (m : ℝ) + 6 / (n : ℝ)) / 6 by ring]

end OMA.A179004Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a179004.main := OMA.A179004Proof.result
