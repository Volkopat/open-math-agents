import OMAStatements.S_oeis_a128103
import Mathlib

/-!
# Proof of OEIS A128103 Conjecture

We prove that the number `a(n)` of permutations of `Fin n` with an even number of rises equals
`Sum_{k = 0..n} Sum_{j = 0..k} (-1)^(n + j) * C(n, k - j) * j^n`:
1. Establish the Eulerian recurrence for `eulerian n k = #{σ ∈ S_n | rises σ = k}` via inserting
   the maximum element `Fin.last n` at position `p : Fin (n + 1)`.
2. Prove by induction that `eulerian n k = eulerFormula n k = B n (k + 1) - B n k`, where
   `B n k = ∑_{j=0..k} (-1)^(k - j) * C(n, k - j) * j^n`.
3. Telescope `∑_{k=0..n} (-1)^(n + k) * B n k`:
   - For odd `n`, it equals `∑_{k even} eulerian n k = a(n)`.
   - For even `n >= 2`, it equals `∑_{k odd} eulerian n k`, which equals `∑_{k even} eulerian n k`
     by permutation reversal `σ ↦ Fin.revPerm.trans σ` (`rises (Fin.revPerm.trans σ) = n - 1 - rises σ`).
-/

namespace OeisA128103Proof

open Finset

private def eulerian (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => OMA.S_oeis_a128103.rises σ = k).card

private def B (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (Nat.choose n (k - j) : ℤ) * (j : ℤ) ^ n

private def eulerFormula (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 2),
    (-1 : ℤ) ^ (k + 1 - j) * (Nat.choose (n + 1) (k + 1 - j) : ℤ) * (j : ℤ) ^ n

private lemma B_zero (n : ℕ) (hn : 1 ≤ n) : B n 0 = 0 := by
  unfold B
  rw [Finset.sum_range_one]
  simp [zero_pow (by omega : n ≠ 0)]

private lemma eulerFormula_eq_B_sub_B (n k : ℕ) :
    eulerFormula n k = B n (k + 1) - B n k := by
  unfold eulerFormula B
  rw [Finset.sum_range_succ (f := fun j => (-1 : ℤ) ^ (k + 1 - j) * (Nat.choose (n + 1) (k + 1 - j) : ℤ) * (j : ℤ) ^ n)]
  rw [Finset.sum_range_succ (f := fun j => (-1 : ℤ) ^ (k + 1 - j) * (Nat.choose n (k + 1 - j) : ℤ) * (j : ℤ) ^ n)]
  simp only [Nat.sub_self, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
  rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsub : k + 1 - j = (k - j) + 1 := by omega
  rw [hsub, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

private lemma eulerFormula_zero (n : ℕ) (hn : 1 ≤ n) : eulerFormula n 0 = 1 := by
  unfold eulerFormula
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [zero_pow (by omega : n ≠ 0)]

private lemma eulerFormula_one (k : ℕ) : eulerFormula 1 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => exact eulerFormula_zero 1 le_rfl
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    unfold eulerFormula
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hrest : ∑ j ∈ Finset.range k,
        (-1 : ℤ) ^ (k + 1 + 1 - j) * (Nat.choose 2 (k + 1 + 1 - j) : ℤ) * (j : ℤ) ^ 1 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : j < k := Finset.mem_range.mp hj
      have hgt : 2 < k + 1 + 1 - j := by omega
      rw [Nat.choose_eq_zero_of_lt hgt]
      simp
    rw [hrest, zero_add]
    have h1 : k + 1 + 1 - k = 2 := by omega
    have h2 : k + 1 + 1 - (k + 1) = 1 := by omega
    have h3 : k + 1 + 1 - (k + 1 + 1) = 0 := by omega
    rw [h1, h2, h3]
    norm_num
    ring

private lemma choose_mul_identity (n k r : ℕ) (hr : 1 ≤ r) :
    ((k + 2 : ℤ) - (r : ℤ)) * (Nat.choose (n + 2) r : ℤ) =
    (k + 2 : ℤ) * (Nat.choose (n + 1) r : ℤ) -
    ((n : ℤ) - (k : ℤ)) * (Nat.choose (n + 1) (r - 1) : ℤ) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0) with ⟨m, rfl⟩
  have h1 : Nat.choose (n + 2) (m + 1) = Nat.choose (n + 1) (m + 1) + Nat.choose (n + 1) m := by
    rw [Nat.choose_succ_succ, add_comm]
  have h2 : (m + 1) * Nat.choose (n + 1) (m + 1) = (n + 1 - m) * Nat.choose (n + 1) m := by
    by_cases hmn : m + 1 ≤ n + 1
    · have h3 := Nat.choose_succ_right_eq (n + 1) m
      linarith
    · have hlt1 : n + 1 < m + 1 := by omega
      rw [Nat.choose_eq_zero_of_lt hlt1, mul_zero]
      by_cases hmn2 : m ≤ n + 1
      · have : n + 1 - m = 0 := by omega
        rw [this, zero_mul]
      · rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  have h2z : ((m + 1 : ℕ) : ℤ) * (Nat.choose (n + 1) (m + 1) : ℤ) =
      ((n + 1 : ℤ) - (m : ℤ)) * (Nat.choose (n + 1) m : ℤ) := by
    by_cases hmn : m ≤ n + 1
    · have := congrArg (Nat.cast (R := ℤ)) h2
      push_cast [Nat.cast_sub hmn] at this
      exact this
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [h1]
  have hsub' : m + 1 - 1 = m := by omega
  rw [hsub']
  push_cast at h2z ⊢
  linarith

private lemma eulerFormula_succ (n k : ℕ) :
    eulerFormula (n + 1) (k + 1) =
    (k + 2 : ℤ) * eulerFormula n (k + 1) + ((n : ℤ) - (k : ℤ)) * eulerFormula n k := by
  unfold eulerFormula
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_range_succ (f := fun j => (-1 : ℤ) ^ (k + 1 + 1 - j) * (Nat.choose (n + 1 + 1) (k + 1 + 1 - j) : ℤ) * (j : ℤ) ^ (n + 1))]
  rw [Finset.sum_range_succ (f := fun j => (k + 2 : ℤ) * ((-1 : ℤ) ^ (k + 1 + 1 - j) * (Nat.choose (n + 1) (k + 1 + 1 - j) : ℤ) * (j : ℤ) ^ n))]
  have htop : (-1 : ℤ) ^ (k + 1 + 1 - (k + 2)) * (Nat.choose (n + 1 + 1) (k + 1 + 1 - (k + 2)) : ℤ) * ((k + 2 : ℕ) : ℤ) ^ (n + 1) =
      (k + 2 : ℤ) * ((-1 : ℤ) ^ (k + 1 + 1 - (k + 2)) * (Nat.choose (n + 1) (k + 1 + 1 - (k + 2)) : ℤ) * ((k + 2 : ℕ) : ℤ) ^ n) := by
    have hz : k + 1 + 1 - (k + 2) = 0 := by omega
    rw [hz, pow_zero, Nat.choose_zero_right, Nat.choose_zero_right, Nat.cast_one, one_mul, one_mul, pow_succ]
    push_cast
    ring
  rw [htop]
  conv_rhs => rw [add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k + 2 := Finset.mem_range.mp hj
  have hr1 : 1 ≤ k + 2 - j := by omega
  have hident := choose_mul_identity n k (k + 2 - j) hr1
  have hj_eq : (k + 2 : ℤ) - ((k + 2 - j : ℕ) : ℤ) = (j : ℤ) := by
    have : (k + 2 - j : ℕ) + j = k + 2 := by omega
    have hz := congrArg (Nat.cast (R := ℤ)) this
    push_cast at hz
    linarith
  rw [hj_eq] at hident
  have hr_eq1 : k + 1 + 1 - j = k + 2 - j := by omega
  have hr_eq2 : k + 2 - j - 1 = k + 1 - j := by omega
  rw [hr_eq2] at hident
  rw [hr_eq1, pow_succ (j : ℤ) n]
  have hsign : (-1 : ℤ) ^ (k + 2 - j) = -((-1 : ℤ) ^ (k + 1 - j)) := by
    have : k + 2 - j = (k + 1 - j) + 1 := by omega
    rw [this, pow_succ]
    ring
  calc (-1 : ℤ) ^ (k + 2 - j) * (Nat.choose (n + 1 + 1) (k + 2 - j) : ℤ) * ((j : ℤ) ^ n * (j : ℤ))
      = (-1 : ℤ) ^ (k + 2 - j) * ((j : ℤ) * (Nat.choose (n + 2) (k + 2 - j) : ℤ)) * (j : ℤ) ^ n := by ring
    _ = (-1 : ℤ) ^ (k + 2 - j) * ((k + 2 : ℤ) * (Nat.choose (n + 1) (k + 2 - j) : ℤ) -
          ((n : ℤ) - (k : ℤ)) * (Nat.choose (n + 1) (k + 1 - j) : ℤ)) * (j : ℤ) ^ n := by rw [hident]
    _ = (k + 2 : ℤ) * ((-1 : ℤ) ^ (k + 2 - j) * (Nat.choose (n + 1) (k + 2 - j) : ℤ) * (j : ℤ) ^ n) +
        ((n : ℤ) - (k : ℤ)) * ((-1 : ℤ) ^ (k + 1 - j) * (Nat.choose (n + 1) (k + 1 - j) : ℤ) * (j : ℤ) ^ n) := by
          rw [hsign]; ring

/-! ### Indicator form of `rises` and insertion bijection -/

private def isRise {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i + 1 < n then if σ ⟨i, by omega⟩ < σ ⟨i + 1, h⟩ then 1 else 0 else 0

private lemma rises_eq_sum_isRise {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a128103.rises σ = ∑ i ∈ Finset.range (n - 1), isRise σ i := by
  unfold OMA.S_oeis_a128103.rises
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  unfold isRise
  have hi : i.1 + 1 < n := by omega
  simp [hi]

private lemma rises_lt {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a128103.rises σ < n := by
  unfold OMA.S_oeis_a128103.rises
  calc (Finset.univ.filter fun i : Fin (n - 1) =>
        σ ⟨i.1, by omega⟩ < σ ⟨i.1 + 1, by omega⟩).card
      ≤ (Finset.univ : Finset (Fin (n - 1))).card := Finset.card_filter_le _ _
    _ = n - 1 := by simp
    _ < n := by omega

private lemma rises_le_pred {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a128103.rises σ ≤ n - 1 := by
  unfold OMA.S_oeis_a128103.rises
  calc (Finset.univ.filter fun i : Fin (n - 1) =>
        σ ⟨i.1, by omega⟩ < σ ⟨i.1 + 1, by omega⟩).card
      ≤ (Finset.univ : Finset (Fin (n - 1))).card := Finset.card_filter_le _ _
    _ = n - 1 := by simp

private def insertLastFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    Fin (n + 1) → Fin (n + 1) :=
  fun i =>
    if h : i = p then Fin.last n
    else if hlt : i.1 < p.1 then
      (σ ⟨i.1, by omega⟩).castSucc
    else
      (σ ⟨i.1 - 1, by omega⟩).castSucc

private def insertLastInvFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    Fin (n + 1) → Fin (n + 1) :=
  fun y =>
    if h : y = Fin.last n then p
    else p.succAbove (σ.symm ⟨y.1, by have := y.2; have : y.1 ≠ n := fun heq => h (Fin.ext heq); omega⟩)

private def insertPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := insertLastFun σ p
  invFun := insertLastInvFun σ p
  left_inv i := by
    unfold insertLastFun insertLastInvFun
    by_cases hip : i = p
    · simp [hip]
    · simp only [hip, ↓reduceDIte]
      by_cases hlt : i.1 < p.1
      · simp only [hlt, ↓reduceDIte]
        have hne : (σ ⟨i.1, by omega⟩).castSucc ≠ Fin.last n := Fin.castSucc_ne_last _
        simp only [hne, ↓reduceDIte, Fin.val_castSucc, Fin.eta, Equiv.symm_apply_apply]
        ext
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · exact Fin.lt_def.mpr hlt
      · simp only [hlt, ↓reduceDIte]
        have hne : (σ ⟨i.1 - 1, by omega⟩).castSucc ≠ Fin.last n := Fin.castSucc_ne_last _
        simp only [hne, ↓reduceDIte, Fin.val_castSucc, Fin.eta, Equiv.symm_apply_apply]
        have hgt : p.1 < i.1 := by
          have : i.1 ≠ p.1 := fun heq => hip (Fin.ext heq)
          omega
        ext
        rw [Fin.succAbove_of_le_castSucc]
        · simp; omega
        · exact Fin.le_def.mpr (by simp; omega)
  right_inv y := by
    unfold insertLastFun insertLastInvFun
    by_cases hyl : y = Fin.last n
    · simp [hyl]
    · simp only [hyl, ↓reduceDIte]
      generalize_proofs hy_lt
      set q : Fin n := σ.symm ⟨y.1, hy_lt⟩
      have hne : p.succAbove q ≠ p := Fin.succAbove_ne p q
      rw [dif_neg hne]
      by_cases hqp : q.castSucc < p
      · have hval : (p.succAbove q).1 = q.1 := by
          rw [Fin.succAbove_of_castSucc_lt p q hqp]; rfl
        have hlt : (p.succAbove q).1 < p.1 := by rw [hval]; exact hqp
        rw [dif_pos hlt]
        ext
        simp only [Fin.val_castSucc]
        have heq : (⟨(p.succAbove q).1, by omega⟩ : Fin n) = q := Fin.ext hval
        rw [heq]
        have hsq : σ q = ⟨y.1, hy_lt⟩ := Equiv.apply_symm_apply σ _
        exact congrArg Fin.val hsq
      · have hle : p ≤ q.castSucc := le_of_not_gt hqp
        have hval : (p.succAbove q).1 = q.1 + 1 := by
          rw [Fin.succAbove_of_le_castSucc p q hle]; rfl
        have hlt : ¬ (p.succAbove q).1 < p.1 := by
          rw [hval]; have : p.1 ≤ q.1 := hle; omega
        rw [dif_neg hlt]
        ext
        simp only [Fin.val_castSucc]
        have heq : (⟨(p.succAbove q).1 - 1, by omega⟩ : Fin n) = q := Fin.ext (by simp [hval])
        rw [heq]
        have hsq : σ q = ⟨y.1, hy_lt⟩ := Equiv.apply_symm_apply σ _
        exact congrArg Fin.val hsq

private lemma insertPerm_at_p {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    insertPerm σ p p = Fin.last n := by
  simp [insertPerm, insertLastFun]

private lemma insertPerm_of_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1))
    (i : Fin (n + 1)) (hlt : i.1 < p.1) :
    insertPerm σ p i = (σ ⟨i.1, by omega⟩).castSucc := by
  have hne : i ≠ p := fun h => by subst h; omega
  simp [insertPerm, insertLastFun, hne, hlt]

private lemma insertPerm_of_gt {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1))
    (i : Fin (n + 1)) (hgt : p.1 < i.1) :
    insertPerm σ p i = (σ ⟨i.1 - 1, by omega⟩).castSucc := by
  have hne : i ≠ p := fun h => by subst h; omega
  have hnlt : ¬ i.1 < p.1 := by omega
  simp [insertPerm, insertLastFun, hne, hnlt]

private lemma insertPerm_bijective (n : ℕ) :
    Function.Bijective (fun x : Equiv.Perm (Fin n) × Fin (n + 1) => insertPerm x.1 x.2) := by
  have hcard : Fintype.card (Equiv.Perm (Fin n) × Fin (n + 1)) =
      Fintype.card (Equiv.Perm (Fin (n + 1))) := by
    simp [Fintype.card_perm, Nat.factorial_succ, mul_comm]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro ⟨σ₁, p₁⟩ ⟨σ₂, p₂⟩ h
  dsimp only at h
  have hp : p₁ = p₂ := by
    have h1 : insertPerm σ₁ p₁ p₁ = Fin.last n := insertPerm_at_p σ₁ p₁
    rw [h] at h1
    have h2 : insertPerm σ₂ p₂ p₂ = Fin.last n := insertPerm_at_p σ₂ p₂
    exact (insertPerm σ₂ p₂).injective (h1.trans h2.symm)
  subst hp
  congr 1
  ext i
  have hval := congrArg (fun τ => τ (p₁.succAbove i)) h
  by_cases hlt : i.castSucc < p₁
  · have hi1 : (p₁.succAbove i).1 = i.1 := by rw [Fin.succAbove_of_castSucc_lt p₁ i hlt]; rfl
    have hlt' : (p₁.succAbove i).1 < p₁.1 := by rw [hi1]; exact hlt
    rw [insertPerm_of_lt σ₁ p₁ _ hlt', insertPerm_of_lt σ₂ p₁ _ hlt'] at hval
    have heq := Fin.castSucc_injective _ hval
    have : (⟨(p₁.succAbove i).1, by omega⟩ : Fin n) = i := Fin.ext hi1
    rw [this] at heq
    exact congrArg Fin.val heq
  · have hle : p₁ ≤ i.castSucc := le_of_not_gt hlt
    have hi1 : (p₁.succAbove i).1 = i.1 + 1 := by rw [Fin.succAbove_of_le_castSucc p₁ i hle]; rfl
    have hgt' : p₁.1 < (p₁.succAbove i).1 := by rw [hi1]; have : p₁.1 ≤ i.1 := hle; omega
    rw [insertPerm_of_gt σ₁ p₁ _ hgt', insertPerm_of_gt σ₂ p₁ _ hgt'] at hval
    have heq := Fin.castSucc_injective _ hval
    have : (⟨(p₁.succAbove i).1 - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp [hi1])
    rw [this] at heq
    exact congrArg Fin.val heq

private lemma rises_insertPerm_zero {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a128103.rises (insertPerm σ 0) = OMA.S_oeis_a128103.rises σ := by
  rw [rises_eq_sum_isRise, rises_eq_sum_isRise]
  have hsub : n + 1 - 1 = (n - 1) + 1 := by omega
  rw [hsub, Finset.sum_range_succ']
  have h0 : isRise (insertPerm σ 0) 0 = 0 := by
    unfold isRise
    have hlt : 0 + 1 < n + 1 := by omega
    simp only [hlt, ↓reduceDIte]
    have hval0 : insertPerm σ 0 ⟨0, by omega⟩ = Fin.last n := insertPerm_at_p σ 0
    rw [hval0]
    have hnot : ¬ Fin.last n < insertPerm σ 0 ⟨1, hlt⟩ := not_lt.mpr (Fin.le_last _)
    simp [hnot]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n - 1 := Finset.mem_range.mp hj
  unfold isRise
  have h1 : j + 1 + 1 < n + 1 := by omega
  have h2 : j + 1 < n := by omega
  simp only [h1, h2, ↓reduceDIte]
  rw [insertPerm_of_gt σ 0 ⟨j + 1, by omega⟩ (by simp),
      insertPerm_of_gt σ 0 ⟨j + 1 + 1, h1⟩ (by simp)]
  simp only [Nat.add_sub_cancel, Fin.castSucc_lt_castSucc_iff]

private lemma rises_insertPerm_last {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a128103.rises (insertPerm σ (Fin.last n)) = OMA.S_oeis_a128103.rises σ + 1 := by
  rw [rises_eq_sum_isRise, rises_eq_sum_isRise]
  have hsub : n + 1 - 1 = (n - 1) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n - 1 := Finset.mem_range.mp hj
    unfold isRise
    have h1 : j + 1 < n + 1 := by omega
    have h2 : j + 1 < n := by omega
    simp only [h1, h2, ↓reduceDIte]
    rw [insertPerm_of_lt σ (Fin.last n) ⟨j, by omega⟩ (by simp; omega),
        insertPerm_of_lt σ (Fin.last n) ⟨j + 1, h1⟩ (by simp; omega)]
    simp only [Fin.castSucc_lt_castSucc_iff]
  · unfold isRise
    have h1 : n - 1 + 1 < n + 1 := by omega
    simp only [h1, ↓reduceDIte]
    rw [insertPerm_of_lt σ (Fin.last n) ⟨n - 1, by omega⟩ (by simp; omega)]
    have hlast : (⟨n - 1 + 1, h1⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    rw [hlast, insertPerm_at_p]
    have hlt : (σ ⟨n - 1, by omega⟩).castSucc < Fin.last n := Fin.castSucc_lt_last _
    simp [hlt]

private lemma rises_insertPerm_mid {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) (hp0 : 0 < p.1) (hpn : p.1 < n) :
    OMA.S_oeis_a128103.rises (insertPerm σ p) + isRise σ (p.1 - 1) =
    OMA.S_oeis_a128103.rises σ + 1 := by
  rw [rises_eq_sum_isRise, rises_eq_sum_isRise]
  set j := p.1 - 1
  have hjlt : j < n - 1 := by omega
  have hsub1 : n + 1 - 1 = n := by omega
  rw [hsub1]
  -- Split range n at j + 2 and range (n - 1) at j + 1
  have hsumL : ∑ i ∈ Finset.range n, isRise (insertPerm σ p) i =
      (∑ i ∈ Finset.range j, isRise (insertPerm σ p) i) +
      isRise (insertPerm σ p) j +
      isRise (insertPerm σ p) (j + 1) +
      (∑ i ∈ Finset.range (n - 2 - j), isRise (insertPerm σ p) (j + 2 + i)) := by
    have hrange : Finset.range n = Finset.range ((j + 2) + (n - 2 - j)) := by congr 1; omega
    rw [hrange, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ]
  have hsumR : ∑ i ∈ Finset.range (n - 1), isRise σ i =
      (∑ i ∈ Finset.range j, isRise σ i) +
      isRise σ j +
      (∑ i ∈ Finset.range (n - 2 - j), isRise σ (j + 1 + i)) := by
    have hrange : Finset.range (n - 1) = Finset.range ((j + 1) + (n - 2 - j)) := by congr 1; omega
    rw [hrange, Finset.sum_range_add, Finset.sum_range_succ]
  rw [hsumL, hsumR]
  have hpre : ∑ i ∈ Finset.range j, isRise (insertPerm σ p) i = ∑ i ∈ Finset.range j, isRise σ i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    unfold isRise
    have h1 : i + 1 < n + 1 := by omega
    have h2 : i + 1 < n := by omega
    simp only [h1, h2, ↓reduceDIte]
    rw [insertPerm_of_lt σ p ⟨i, by omega⟩ (by simp; omega),
        insertPerm_of_lt σ p ⟨i + 1, h1⟩ (by simp; omega)]
    simp only [Fin.castSucc_lt_castSucc_iff]
  have hpost : ∑ i ∈ Finset.range (n - 2 - j), isRise (insertPerm σ p) (j + 2 + i) =
      ∑ i ∈ Finset.range (n - 2 - j), isRise σ (j + 1 + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < n - 2 - j := Finset.mem_range.mp hi
    unfold isRise
    have h1 : j + 2 + i + 1 < n + 1 := by omega
    have h2 : j + 1 + i + 1 < n := by omega
    simp only [h1, h2, ↓reduceDIte]
    rw [insertPerm_of_gt σ p ⟨j + 2 + i, by omega⟩ (by simp; omega),
        insertPerm_of_gt σ p ⟨j + 2 + i + 1, h1⟩ (by simp; omega)]
    have heq1 : (⟨j + 2 + i - 1, by omega⟩ : Fin n) = ⟨j + 1 + i, by omega⟩ := Fin.ext (by dsimp; omega)
    have heq2 : (⟨j + 2 + i + 1 - 1, by omega⟩ : Fin n) = ⟨j + 1 + i + 1, h2⟩ := Fin.ext (by dsimp; omega)
    rw [heq1, heq2]
    simp only [Fin.castSucc_lt_castSucc_iff]
  have hmid1 : isRise (insertPerm σ p) j = 1 := by
    unfold isRise
    have h1 : j + 1 < n + 1 := by omega
    simp only [h1, ↓reduceDIte]
    rw [insertPerm_of_lt σ p ⟨j, by omega⟩ (by simp; omega)]
    have hp_eq : (⟨j + 1, h1⟩ : Fin (n + 1)) = p := Fin.ext (by simp; omega)
    rw [hp_eq, insertPerm_at_p]
    have hlt : (σ ⟨j, by omega⟩).castSucc < Fin.last n := Fin.castSucc_lt_last _
    simp [hlt]
  have hmid2 : isRise (insertPerm σ p) (j + 1) = 0 := by
    unfold isRise
    have h1 : j + 1 + 1 < n + 1 := by omega
    simp only [h1, ↓reduceDIte]
    have hp_eq : (⟨j + 1, by omega⟩ : Fin (n + 1)) = p := Fin.ext (by simp; omega)
    rw [hp_eq, insertPerm_at_p]
    have hnot : ¬ Fin.last n < insertPerm σ p ⟨j + 1 + 1, h1⟩ := not_lt.mpr (Fin.le_last _)
    simp [hnot]
  rw [hpre, hpost, hmid1, hmid2]
  omega

private lemma rises_insertPerm_cases {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ ∨
    OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ + 1 := by
  by_cases hp0 : p.1 = 0
  · left; have : p = 0 := Fin.ext hp0; subst this; exact rises_insertPerm_zero hn σ
  · by_cases hpn : p.1 = n
    · right; have : p = Fin.last n := Fin.ext hpn; subst this; exact rises_insertPerm_last hn σ
    · have hm := rises_insertPerm_mid hn σ p (by omega) (by omega)
      have h01 : isRise σ (p.1 - 1) = 0 ∨ isRise σ (p.1 - 1) = 1 := by
        unfold isRise; split_ifs <;> simp
      rcases h01 with h | h <;> omega

private lemma card_pos_same_rises {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun p : Fin (n + 1) =>
      OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ).card =
    OMA.S_oeis_a128103.rises σ + 1 := by
  let g : ℕ → ℕ := fun p =>
    if h : p < n + 1 then
      if OMA.S_oeis_a128103.rises (insertPerm σ ⟨p, h⟩) = OMA.S_oeis_a128103.rises σ then 1 else 0
    else 0
  have hcard : (Finset.univ.filter fun p : Fin (n + 1) =>
      OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ).card =
      ∑ p ∈ Finset.range (n + 1), g p := by
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [g]
    rw [dif_pos p.2]
  rw [hcard, Finset.sum_range_succ']
  have hg0 : g 0 = 1 := by
    have h0 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
    simp [g, h0, rises_insertPerm_zero hn σ]
  rw [hg0]
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn_eq, Finset.sum_range_succ]
  have hgn : g (n - 1 + 1) = 0 := by
    have hlast : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    have hlt : n - 1 + 1 < n + 1 := by omega
    simp only [g, hlt, ↓reduceDIte, hlast, rises_insertPerm_last hn σ]
    simp
  rw [hgn, add_zero, rises_eq_sum_isRise]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n - 1 := Finset.mem_range.mp hj
  have hlt : j + 1 < n + 1 := by omega
  simp only [g, hlt, ↓reduceDIte]
  have hm := rises_insertPerm_mid hn σ ⟨j + 1, hlt⟩ (by simp) (by simp; omega)
  simp only [Nat.add_sub_cancel] at hm
  have h01 : isRise σ j = 0 ∨ isRise σ j = 1 := by unfold isRise; split_ifs <;> simp
  rcases h01 with h | h
  · rw [h] at hm ⊢
    have hne : OMA.S_oeis_a128103.rises (insertPerm σ ⟨j + 1, hlt⟩) ≠ OMA.S_oeis_a128103.rises σ := by omega
    simp [hne]
  · rw [h] at hm ⊢
    have heq : OMA.S_oeis_a128103.rises (insertPerm σ ⟨j + 1, hlt⟩) = OMA.S_oeis_a128103.rises σ := by omega
    simp [heq]

private lemma card_pos_inc_rises {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun p : Fin (n + 1) =>
      OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ + 1).card =
    n - OMA.S_oeis_a128103.rises σ := by
  have hcompl : (Finset.univ.filter fun p : Fin (n + 1) =>
      OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ + 1) =
      (Finset.univ.filter fun p : Fin (n + 1) =>
      ¬ (OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases rises_insertPerm_cases hn σ p with h | h <;> omega
  rw [hcompl]
  have htot : (Finset.univ.filter fun p : Fin (n + 1) =>
      OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ).card +
      (Finset.univ.filter fun p : Fin (n + 1) =>
      ¬ (OMA.S_oeis_a128103.rises (insertPerm σ p) = OMA.S_oeis_a128103.rises σ)).card =
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p; simp [em]
    · rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h2 h1
  rw [card_pos_same_rises hn σ, Finset.card_univ, Fintype.card_fin] at htot
  omega

private lemma eulerian_one (k : ℕ) : eulerian 1 k = if k = 0 then 1 else 0 := by
  unfold eulerian
  have hr : ∀ σ : Equiv.Perm (Fin 1), OMA.S_oeis_a128103.rises σ = 0 := by
    intro σ
    have := rises_lt le_rfl σ
    omega
  split_ifs with hk
  · subst hk
    simp [hr]
  · apply Finset.card_eq_zero.mpr
    ext σ
    simp [hr, Ne.symm hk]

private lemma eulerian_succ_zero {n : ℕ} (hn : 1 ≤ n) :
    eulerian (n + 1) 0 = eulerian n 0 := by
  unfold eulerian
  let e := Equiv.ofBijective _ (insertPerm_bijective n)
  have h1 : (Finset.univ.filter fun τ : Equiv.Perm (Fin (n + 1)) => OMA.S_oeis_a128103.rises τ = 0).card =
      (Finset.univ.filter fun x : Equiv.Perm (Fin n) × Fin (n + 1) =>
        OMA.S_oeis_a128103.rises (insertPerm x.1 x.2) = 0).card := by
    apply Finset.card_bij (fun τ _ => e.symm τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      have heq : insertPerm (e.symm τ).1 (e.symm τ).2 = τ := e.apply_symm_apply τ
      rw [heq]; exact hτ
    · intro a _ b _ h; exact e.symm.injective h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨e x, by simp [e, hx], e.symm_apply_apply x⟩
  rw [h1, Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ σ : Equiv.Perm (Fin n),
      (∑ p : Fin (n + 1), if OMA.S_oeis_a128103.rises (insertPerm σ p) = 0 then 1 else 0) =
      if OMA.S_oeis_a128103.rises σ = 0 then 1 else 0 := by
    intro σ
    rw [← Finset.card_filter]
    by_cases h0 : OMA.S_oeis_a128103.rises σ = 0
    · rw [if_pos h0]
      have := card_pos_same_rises hn σ
      rw [h0] at this
      exact this
    · rw [if_neg h0]
      apply Finset.card_eq_zero.mpr
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rcases rises_insertPerm_cases hn σ p with h | h <;> omega
  simp_rw [hinner, ← Finset.card_filter]

private lemma eulerian_succ_succ {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    eulerian (n + 1) (k + 1) = (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k := by
  unfold eulerian
  let e := Equiv.ofBijective _ (insertPerm_bijective n)
  have h1 : (Finset.univ.filter fun τ : Equiv.Perm (Fin (n + 1)) => OMA.S_oeis_a128103.rises τ = k + 1).card =
      (Finset.univ.filter fun x : Equiv.Perm (Fin n) × Fin (n + 1) =>
        OMA.S_oeis_a128103.rises (insertPerm x.1 x.2) = k + 1).card := by
    apply Finset.card_bij (fun τ _ => e.symm τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      have heq : insertPerm (e.symm τ).1 (e.symm τ).2 = τ := e.apply_symm_apply τ
      rw [heq]; exact hτ
    · intro a _ b _ h; exact e.symm.injective h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨e x, by simp [e, hx], e.symm_apply_apply x⟩
  rw [h1, Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ σ : Equiv.Perm (Fin n),
      (∑ p : Fin (n + 1), if OMA.S_oeis_a128103.rises (insertPerm σ p) = k + 1 then 1 else 0) =
      (if OMA.S_oeis_a128103.rises σ = k + 1 then k + 2 else 0) +
      (if OMA.S_oeis_a128103.rises σ = k then n - k else 0) := by
    intro σ
    rw [← Finset.card_filter]
    by_cases h1 : OMA.S_oeis_a128103.rises σ = k + 1
    · have h2 : OMA.S_oeis_a128103.rises σ ≠ k := by omega
      rw [if_pos h1, if_neg h2, add_zero]
      have := card_pos_same_rises hn σ
      rw [h1] at this
      exact this
    · by_cases h2 : OMA.S_oeis_a128103.rises σ = k
      · rw [if_neg h1, if_pos h2, zero_add]
        have := card_pos_inc_rises hn σ
        rw [h2] at this
        exact this
      · rw [if_neg h1, if_neg h2, add_zero]
        apply Finset.card_eq_zero.mpr
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rcases rises_insertPerm_cases hn σ p with h | h <;> omega
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

private lemma eulerian_eq_zero_of_ge {n k : ℕ} (hn : 1 ≤ n) (hkn : n ≤ k) :
    eulerian n k = 0 := by
  unfold eulerian
  apply Finset.card_eq_zero.mpr
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  have := rises_lt hn σ
  omega

private lemma eulerian_eq_eulerFormula (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, (eulerian n k : ℤ) = eulerFormula n k := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      intro k
      rw [eulerian_one, eulerFormula_one]
      split_ifs <;> simp
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      have ihm := ih hm
      intro k
      cases k with
      | zero =>
        rw [eulerian_succ_zero hm, ihm 0, eulerFormula_zero (m + 1) hm, eulerFormula_zero (m + 2) (by omega)]
      | succ k =>
        rw [eulerian_succ_succ hm k, eulerFormula_succ (m + 1) k]
        push_cast
        rw [ihm (k + 1), ihm k]
        by_cases hkm : k ≤ m + 1
        · rw [Nat.cast_sub hkm]
          push_cast
          ring
        · have hz : eulerian (m + 1) k = 0 := eulerian_eq_zero_of_ge hm (by omega)
          have hfz : eulerFormula (m + 1) k = 0 := by
            rw [← ihm k, hz, Nat.cast_zero]
          rw [hfz, mul_zero, mul_zero]

private lemma rises_revPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a128103.rises (Fin.revPerm.trans σ) + OMA.S_oeis_a128103.rises σ = n - 1 := by
  rw [rises_eq_sum_isRise, rises_eq_sum_isRise]
  rw [← Finset.sum_range_reflect (fun i => isRise (Fin.revPerm.trans σ) i) (n - 1)]
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ i ∈ Finset.range (n - 1),
      isRise (Fin.revPerm.trans σ) (n - 1 - 1 - i) + isRise σ i = 1 := by
    intro i hi
    have hin : i < n - 1 := Finset.mem_range.mp hi
    unfold isRise
    have hlt1 : n - 1 - 1 - i + 1 < n := by omega
    have hlt2 : i + 1 < n := by omega
    simp only [hlt1, hlt2, ↓reduceDIte]
    have heq1 : (Fin.revPerm.trans σ) ⟨n - 1 - 1 - i, by omega⟩ = σ ⟨i + 1, hlt2⟩ := by
      simp only [Equiv.trans_apply, Fin.revPerm_apply]
      congr 1; ext; simp [Fin.val_rev]; omega
    have heq2 : (Fin.revPerm.trans σ) ⟨n - 1 - 1 - i + 1, hlt1⟩ = σ ⟨i, by omega⟩ := by
      simp only [Equiv.trans_apply, Fin.revPerm_apply]
      congr 1; ext; simp [Fin.val_rev]; omega
    rw [heq1, heq2]
    have hne : σ ⟨i, by omega⟩ ≠ σ ⟨i + 1, hlt2⟩ := fun h => by
      have := σ.injective h
      have := congrArg Fin.val this
      simp at this
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hnot : ¬ σ ⟨i + 1, hlt2⟩ < σ ⟨i, by omega⟩ := not_lt.mpr (le_of_lt hlt)
      simp [hlt, hnot]
    · have hnot : ¬ σ ⟨i, by omega⟩ < σ ⟨i + 1, hlt2⟩ := not_lt.mpr (le_of_lt hgt)
      simp [hgt, hnot]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

private lemma a_eq_sum_even {n : ℕ} (hn : 1 ≤ n) :
    OMA.S_oeis_a128103.a n = ∑ k ∈ Finset.range n, if Even k then eulerian n k else 0 := by
  unfold OMA.S_oeis_a128103.a eulerian
  have hpart : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Even (OMA.S_oeis_a128103.rises σ)) =
      (Finset.range n).biUnion fun k =>
        if Even k then Finset.univ.filter fun σ : Equiv.Perm (Fin n) => OMA.S_oeis_a128103.rises σ = k
        else ∅ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hev
      refine ⟨OMA.S_oeis_a128103.rises σ, rises_lt hn σ, ?_⟩
      simp [hev]
    · rintro ⟨k, _, hk⟩
      split_ifs at hk with hev
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [hk]; exact hev
      · simp at hk
  rw [hpart, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro σ hσi hσj
    dsimp only at hσi hσj
    split_ifs at hσi hσj
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσi hσj
      exact hij (hσi.symm.trans hσj)
    all_goals simp at hσi hσj

private lemma a_eq_sum_odd_of_even {n : ℕ} (hn : 1 ≤ n) (hev : Even n) :
    OMA.S_oeis_a128103.a n = ∑ k ∈ Finset.range n, if Odd k then eulerian n k else 0 := by
  have hodd_card : OMA.S_oeis_a128103.a n =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Odd (OMA.S_oeis_a128103.rises σ)).card := by
    unfold OMA.S_oeis_a128103.a
    apply Finset.card_bij (fun σ _ => Fin.revPerm.trans σ)
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      have hsum := rises_revPerm σ
      rcases hev with ⟨m, hm⟩
      rcases hσ with ⟨r, hr⟩
      exact ⟨m - 1 - r, by omega⟩
    · intro a _ b _ h
      ext1 x
      have := congrArg (fun τ => τ (Fin.rev x)) h
      simpa using this
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      refine ⟨Fin.revPerm.trans τ, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hsum := rises_revPerm τ
        rcases hev with ⟨m, hm⟩
        rcases hτ with ⟨r, hr⟩
        exact ⟨m - 1 - r, by omega⟩
      · ext1 x; simp
  rw [hodd_card]
  have hpart : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Odd (OMA.S_oeis_a128103.rises σ)) =
      (Finset.range n).biUnion fun k =>
        if Odd k then Finset.univ.filter fun σ : Equiv.Perm (Fin n) => OMA.S_oeis_a128103.rises σ = k
        else ∅ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hodd
      refine ⟨OMA.S_oeis_a128103.rises σ, rises_lt hn σ, ?_⟩
      simp [hodd]
    · rintro ⟨k, _, hk⟩
      split_ifs at hk with hodd
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [hk]; exact hodd
      · simp at hk
  rw [hpart, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp [eulerian]
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro σ hσi hσj
    dsimp only at hσi hσj
    split_ifs at hσi hσj
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσi hσj
      exact hij (hσi.symm.trans hσj)
    all_goals simp at hσi hσj

private lemma rhs_eq_alt_B (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (n + j) * (Nat.choose n (k - j) : ℤ) * (j : ℤ) ^ n) =
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * B n k := by
  apply Finset.sum_congr rfl
  intro k _
  unfold B
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsign : (-1 : ℤ) ^ (n + k) * (-1 : ℤ) ^ (k - j) = (-1 : ℤ) ^ (n + j) := by
    rw [← pow_add]
    have heq : n + k + (k - j) = (n + j) + 2 * (k - j) := by omega
    rw [heq, pow_add, pow_mul]
    norm_num
  calc (-1 : ℤ) ^ (n + j) * (Nat.choose n (k - j) : ℤ) * (j : ℤ) ^ n
      = ((-1 : ℤ) ^ (n + k) * (-1 : ℤ) ^ (k - j)) * (Nat.choose n (k - j) : ℤ) * (j : ℤ) ^ n := by
        rw [hsign]
    _ = (-1 : ℤ) ^ (n + k) * ((-1 : ℤ) ^ (k - j) * (Nat.choose n (k - j) : ℤ) * (j : ℤ) ^ n) := by ring

private lemma alt_sum_odd (f : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m + 2), (-1 : ℤ) ^ (k + 1) * f k) =
    ∑ j ∈ Finset.range (m + 1), (f (2 * j + 1) - f (2 * j)) := by
  induction m with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_one]
    ring
  | succ m ih =>
    have h1 : 2 * (m + 1) + 2 = (2 * m + 2) + 2 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hp1 : (-1 : ℤ) ^ (2 * m + 2 + 1) = -1 := by
      rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by omega, pow_succ, pow_mul]; norm_num
    have hp2 : (-1 : ℤ) ^ (2 * m + 2 + 1 + 1) = 1 := by
      have : 2 * m + 2 + 1 + 1 = 2 * (m + 2) := by omega
      rw [this, pow_mul]; norm_num
    rw [hp1, hp2]
    have ha : 2 * m + 2 = 2 * (m + 1) := by omega
    have hb : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by omega
    rw [ha, hb]
    ring

private lemma alt_sum_even (f : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m + 1), (-1 : ℤ) ^ k * f k) =
    f 0 + ∑ j ∈ Finset.range m, (f (2 * j + 2) - f (2 * j + 1)) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hp1 : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    have hp2 : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := by
      have : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      rw [this, pow_mul]; norm_num
    rw [hp1, hp2]
    have ha : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    rw [ha]
    ring

private lemma sum_even_range_odd (g : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m + 1), if Even k then g k else 0) =
    ∑ j ∈ Finset.range (m + 1), g (2 * j) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hodd : ¬ Even (2 * m + 1) := by intro ⟨r, hr⟩; omega
    have hev : Even (2 * m + 1 + 1) := ⟨m + 1, by omega⟩
    rw [if_neg hodd, if_pos hev, add_zero]
    have ha : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [ha]

private lemma sum_odd_range_even (g : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m), if Odd k then g k else 0) =
    ∑ j ∈ Finset.range m, g (2 * j + 1) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h1 : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hev : ¬ Odd (2 * m) := by intro ⟨r, hr⟩; omega
    have hodd : Odd (2 * m + 1) := ⟨m, by omega⟩
    rw [if_neg hev, if_pos hodd, add_zero]

end OeisA128103Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a128103.main := by
  intro n
  rw [OeisA128103Proof.rhs_eq_alt_B]
  cases n with
  | zero =>
    simp only [OMA.S_oeis_a128103.a, OMA.S_oeis_a128103.rises, OeisA128103Proof.B]
    decide
  | succ n =>
    have hn : 1 ≤ n + 1 := by omega
    rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n + 1 = 2 * m (even)
      have h2m : n + 1 = 2 * m := by omega
      rw [OeisA128103Proof.a_eq_sum_odd_of_even hn ⟨m, hm⟩]
      push_cast
      rw [h2m, OeisA128103Proof.sum_odd_range_even]
      have hsign : ∀ k ∈ Finset.range (2 * m + 1),
          (-1 : ℤ) ^ (2 * m + k) * OeisA128103Proof.B (2 * m) k =
          (-1 : ℤ) ^ k * OeisA128103Proof.B (2 * m) k := by
        intro k _
        rw [pow_add, pow_mul]
        norm_num
      rw [Finset.sum_congr rfl hsign, OeisA128103Proof.alt_sum_even,
          OeisA128103Proof.B_zero (2 * m) (by omega), zero_add]
      apply Finset.sum_congr rfl
      intro j _
      rw [OeisA128103Proof.eulerian_eq_eulerFormula (2 * m) (by omega) (2 * j + 1),
          OeisA128103Proof.eulerFormula_eq_B_sub_B]
    · -- n + 1 = 2 * m + 1 (odd)
      rw [OeisA128103Proof.a_eq_sum_even hn]
      push_cast
      rw [hm, OeisA128103Proof.sum_even_range_odd]
      have hsign : ∀ k ∈ Finset.range (2 * m + 1 + 1),
          (-1 : ℤ) ^ (2 * m + 1 + k) * OeisA128103Proof.B (2 * m + 1) k =
          (-1 : ℤ) ^ (k + 1) * OeisA128103Proof.B (2 * m + 1) k := by
        intro k _
        rw [show 2 * m + 1 + k = 2 * m + (k + 1) by omega, pow_add, pow_mul]
        norm_num
      rw [Finset.sum_congr rfl hsign, show 2 * m + 1 + 1 = 2 * m + 2 by omega,
          OeisA128103Proof.alt_sum_odd]
      apply Finset.sum_congr rfl
      intro j _
      rw [OeisA128103Proof.eulerian_eq_eulerFormula (2 * m + 1) (by omega) (2 * j),
          OeisA128103Proof.eulerFormula_eq_B_sub_B]
