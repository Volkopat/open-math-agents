import OMAStatements.S_oeis_a250781

/-!
Proof of the conjectures of OEIS A250781 (statement by @ivillar).

Method: rows are states; consecutive rows must satisfy the row relation, so a(n) is the number
of walks with n steps in a graph on the 2^7 = 128 rows. Rows are encoded as Fin 128 by
finFunctionFinEquiv; the adjacency lists and the first 13 level vectors are checked by the
kernel. The vector sequence is annihilated by (x - 2)(x - 1)^10 from n = 1 on, which gives a
recurrence for a(n) and, by strong induction, the closed form; the recurrence of the entry
and the generating function follow from the closed form.
-/

namespace A250781Proof

open OMA.S_oeis_a250781 Finset


section Core

variable {S : Type*} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain {n : ℕ} (x : Fin (n + 1) → S) : Prop := ∀ i : Fin n, R (x i.castSucc) (x i.succ)

instance {n : ℕ} (x : Fin (n + 1) → S) : Decidable (Chain R x) := by unfold Chain; infer_instance

/-- The number of chains of n + 1 states starting at s. -/
def cnt : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then cnt n t else 0

theorem chain_cons {n : ℕ} (a : S) (y : Fin (n + 1) → S) :
    Chain R (Fin.cons a y : Fin (n + 2) → S) ↔ R a (y 0) ∧ Chain R y := by
  unfold Chain
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

theorem key (n : ℕ) (s : S) :
    (∑ y : Fin (n + 1) → S, if y 0 = s ∧ Chain R y then 1 else 0) = cnt R n s := by
  induction n generalizing s with
  | zero =>
    rw [cnt]
    rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    simp [Chain]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => S)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.cons_zero]
    rw [cnt, Finset.sum_eq_single s]
    · simp only [true_and]
      have h1 : ∀ t, (if R s t then cnt R n t else 0) =
          ∑ y : Fin (n + 1) → S, if R s t ∧ y 0 = t ∧ Chain R y then 1 else 0 := by
        intro t
        rw [← ih t]
        by_cases h : R s t <;> simp [h]
      simp only [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_eq_single (y 0)]
      · show (if Chain R (Fin.cons s y : Fin (n + 2) → S) then 1 else 0) = _
        simp only [chain_cons, true_and]
      · intro t _ ht
        have : ¬ y 0 = t := fun h => ht h.symm
        simp [this]
      · simp
    · intro b _ hb
      simp [hb]
    · simp

theorem card_chain (n : ℕ) :
    Fintype.card {x : Fin (n + 1) → S // Chain R x} = ∑ s, cnt R n s := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [← Finset.sum_congr rfl (fun s _ => key R n s)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single (y 0)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem cnt_equiv {T : Type*} [Fintype T] [DecidableEq T] (e : S ≃ T) (n : ℕ) (s : S) :
    cnt R n s = cnt (fun i j => R (e.symm i) (e.symm j)) n (e s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [cnt]
    refine Fintype.sum_equiv e _ _ (fun t => ?_)
    simp [ih]

theorem lin_step (L : ℕ) (w : ℕ → ℕ) (n : ℕ) (s : S) :
    (∑ k ∈ Finset.range L, w k * cnt R (n + 1 + k) s) =
      ∑ t, if R s t then (∑ k ∈ Finset.range L, w k * cnt R (n + k) t) else 0 := by
  have h : ∀ k, n + 1 + k = (n + k) + 1 := fun k => by omega
  simp only [h, cnt, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem sum_adj (l : S → List S) (hl : ∀ s t, R s t ↔ t ∈ l s) (hn : ∀ s, (l s).Nodup)
    (v : S → ℕ) (s : S) : (∑ t, if R s t then v t else 0) = ((l s).map v).sum := by
  rw [← Finset.sum_filter, ← List.sum_toFinset v (hn s)]
  congr 1
  ext t
  simp [hl]

theorem rec_solve (d : ℕ) (c : ℕ → ℚ) (hc : c d = 1) (T f : ℕ → ℚ)
    (hT : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (d + 1), c k * T (n + k) = 0)
    (hf : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (d + 1), c k * f (n + k) = 0)
    (h0 : ∀ n, 1 ≤ n → n ≤ d → T n = f n) : ∀ n, 1 ≤ n → T n = f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hd : n ≤ d
    · exact h0 n hn hd
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
      have hm : 1 ≤ m := by omega
      have e1 := hT m hm
      have e2 := hf m hm
      rw [Finset.sum_range_succ, hc, one_mul] at e1 e2
      have : ∑ k ∈ Finset.range d, c k * T (m + k) = ∑ k ∈ Finset.range d, c k * f (m + k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [ih (m + k) (by omega) (by omega)]
      linarith

end Core

abbrev K : ℕ := 7
abbrev N : ℕ := 2 ^ K

def Rel (u v : Fin K → Fin 2) : Prop := BlockOK u v

instance : DecidableRel Rel := fun u v => by unfold Rel BlockOK; infer_instance

def R' (i j : Fin N) : Prop := Rel (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)

instance : DecidableRel R' := fun i j => by unfold R'; infer_instance

def adjL : Fin N → List (Fin N) :=
  ![[0, 64, 96, 112, 120, 124, 126, 127],
    [1, 65, 97, 113, 121, 125, 126, 127],
    [2, 66, 98, 114, 122, 125, 126],
    [3, 67, 99, 115, 123, 127],
    [4, 68, 100, 116, 122, 123, 124],
    [5, 69, 101, 117, 122, 123, 125],
    [6, 70, 102, 118, 126],
    [7, 71, 103, 119, 127],
    [8, 72, 104, 116, 118, 119, 120],
    [9, 73, 105, 117, 118, 119, 121],
    [10, 74, 106, 117, 118, 122],
    [11, 75, 107, 119, 123],
    [12, 76, 108, 124],
    [13, 77, 109, 125],
    [14, 78, 110, 126],
    [15, 79, 111, 127],
    [16, 80, 104, 108, 110, 111, 112],
    [17, 81, 105, 109, 110, 111, 113],
    [18, 82, 106, 109, 110, 114],
    [19, 83, 107, 111, 115],
    [20, 84, 106, 107, 108, 116],
    [21, 85, 106, 107, 109, 117],
    [22, 86, 110, 118],
    [23, 87, 111, 119],
    [24, 88, 120],
    [25, 89, 121],
    [26, 90, 122],
    [27, 91, 123],
    [28, 92, 124],
    [29, 93, 125],
    [30, 94, 126],
    [31, 95, 127],
    [32, 80, 88, 92, 94, 95, 96],
    [33, 81, 89, 93, 94, 95, 97],
    [34, 82, 90, 93, 94, 98],
    [35, 83, 91, 95, 99],
    [36, 84, 90, 91, 92, 100],
    [37, 85, 90, 91, 93, 101],
    [38, 86, 94, 102],
    [39, 87, 95, 103],
    [40, 84, 86, 87, 88, 104],
    [41, 85, 86, 87, 89, 105],
    [42, 85, 86, 90, 106],
    [43, 87, 91, 107],
    [44, 92, 108],
    [45, 93, 109],
    [46, 94, 110],
    [47, 95, 111],
    [48, 112],
    [49, 113],
    [50, 114],
    [51, 115],
    [52, 116],
    [53, 117],
    [54, 118],
    [55, 119],
    [56, 120],
    [57, 121],
    [58, 122],
    [59, 123],
    [60, 124],
    [61, 125],
    [62, 126],
    [63, 127],
    [32, 48, 56, 60, 62, 63, 64],
    [33, 49, 57, 61, 62, 63, 65],
    [34, 50, 58, 61, 62, 66],
    [35, 51, 59, 63, 67],
    [36, 52, 58, 59, 60, 68],
    [37, 53, 58, 59, 61, 69],
    [38, 54, 62, 70],
    [39, 55, 63, 71],
    [40, 52, 54, 55, 56, 72],
    [41, 53, 54, 55, 57, 73],
    [42, 53, 54, 58, 74],
    [43, 55, 59, 75],
    [44, 60, 76],
    [45, 61, 77],
    [46, 62, 78],
    [47, 63, 79],
    [40, 44, 46, 47, 48, 80],
    [41, 45, 46, 47, 49, 81],
    [42, 45, 46, 50, 82],
    [43, 47, 51, 83],
    [42, 43, 44, 52, 84],
    [42, 43, 45, 53, 85],
    [46, 54, 86],
    [47, 55, 87],
    [56, 88],
    [57, 89],
    [58, 90],
    [59, 91],
    [60, 92],
    [61, 93],
    [62, 94],
    [63, 95],
    [96],
    [97],
    [98],
    [99],
    [100],
    [101],
    [102],
    [103],
    [104],
    [105],
    [106],
    [107],
    [108],
    [109],
    [110],
    [111],
    [112],
    [113],
    [114],
    [115],
    [116],
    [117],
    [118],
    [119],
    [120],
    [121],
    [122],
    [123],
    [124],
    [125],
    [126],
    [127]]

theorem adj_iff_0 : ∀ i : Fin N, 0 ≤ i.val → i.val < 16 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_16 : ∀ i : Fin N, 16 ≤ i.val → i.val < 32 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_32 : ∀ i : Fin N, 32 ≤ i.val → i.val < 48 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_48 : ∀ i : Fin N, 48 ≤ i.val → i.val < 64 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_64 : ∀ i : Fin N, 64 ≤ i.val → i.val < 80 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_80 : ∀ i : Fin N, 80 ≤ i.val → i.val < 96 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_96 : ∀ i : Fin N, 96 ≤ i.val → i.val < 112 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_112 : ∀ i : Fin N, 112 ≤ i.val → i.val < 128 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel

theorem adj_iff (i j : Fin N) : R' i j ↔ j ∈ adjL i :=
  if h0 : i.val < 16 then adj_iff_0 i (by omega) h0 j else if h16 : i.val < 32 then adj_iff_16 i (by omega) h16 j else if h32 : i.val < 48 then adj_iff_32 i (by omega) h32 j else if h48 : i.val < 64 then adj_iff_48 i (by omega) h48 j else if h64 : i.val < 80 then adj_iff_64 i (by omega) h64 j else if h80 : i.val < 96 then adj_iff_80 i (by omega) h80 j else if h96 : i.val < 112 then adj_iff_96 i (by omega) h96 j else adj_iff_112 i (by omega) (by have := i.isLt; simp only [N, K] at this; omega) j

theorem adj_nodup : ∀ i : Fin N, (adjL i).Nodup := by decide +kernel

def V : ℕ → Fin N → ℕ
  | 0 => ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 1 => ![8, 8, 7, 6, 7, 7, 5, 5, 7, 7, 6, 5, 4, 4, 4, 4, 7, 7, 6, 5, 6, 6, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 6, 5, 6, 6, 4, 4, 6, 6, 5, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 6, 5, 6, 6, 4, 4, 6, 6, 5, 4, 3, 3, 3, 3, 6, 6, 5, 4, 5, 5, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 2 => ![21, 21, 18, 15, 18, 18, 12, 12, 18, 18, 15, 12, 9, 9, 9, 9, 18, 18, 15, 12, 15, 15, 9, 9, 6, 6, 6, 6, 6, 6, 6, 6, 22, 22, 18, 14, 18, 18, 10, 10, 20, 20, 16, 10, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 24, 24, 20, 16, 20, 20, 12, 12, 20, 20, 16, 12, 8, 8, 8, 8, 23, 23, 18, 13, 19, 19, 8, 8, 4, 4, 4, 4, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 3 => ![51, 51, 43, 35, 43, 43, 27, 27, 43, 43, 35, 27, 19, 19, 19, 19, 46, 46, 37, 28, 38, 38, 19, 19, 11, 11, 11, 11, 11, 11, 11, 11, 62, 62, 49, 36, 50, 50, 23, 23, 60, 60, 48, 23, 11, 11, 11, 11, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 61, 61, 50, 39, 50, 50, 28, 28, 52, 52, 41, 28, 17, 17, 17, 17, 64, 64, 49, 32, 54, 54, 17, 17, 7, 7, 7, 7, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 4 => ![118, 118, 98, 78, 98, 98, 58, 58, 100, 100, 80, 58, 38, 38, 38, 38, 115, 115, 90, 63, 96, 96, 38, 38, 19, 19, 19, 19, 19, 19, 19, 19, 155, 155, 120, 83, 126, 126, 48, 48, 156, 156, 127, 48, 19, 19, 19, 19, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 143, 143, 115, 87, 116, 116, 59, 59, 128, 128, 101, 59, 32, 32, 32, 32, 161, 161, 123, 70, 140, 140, 32, 32, 11, 11, 11, 11, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 5 => ![267, 267, 218, 169, 219, 219, 120, 120, 233, 233, 185, 120, 72, 72, 72, 72, 281, 281, 217, 136, 240, 240, 72, 72, 31, 31, 31, 31, 31, 31, 31, 31, 361, 361, 277, 176, 300, 300, 92, 92, 372, 372, 311, 92, 31, 31, 31, 31, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 323, 323, 255, 185, 262, 262, 117, 117, 304, 304, 243, 117, 56, 56, 56, 56, 379, 379, 293, 142, 339, 339, 56, 56, 16, 16, 16, 16, 16, 16, 16, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 6 => ![596, 596, 478, 358, 486, 486, 240, 240, 542, 542, 432, 240, 130, 130, 130, 130, 665, 665, 514, 281, 583, 583, 130, 130, 48, 48, 48, 48, 48, 48, 48, 48, 805, 805, 619, 351, 688, 688, 165, 165, 840, 840, 723, 165, 48, 48, 48, 48, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 714, 714, 556, 379, 586, 586, 221, 221, 700, 700, 572, 221, 93, 93, 93, 93, 850, 850, 672, 271, 779, 779, 93, 93, 22, 22, 22, 22, 22, 22, 22, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 7 => ![1316, 1316, 1039, 741, 1077, 1077, 464, 464, 1247, 1247, 1008, 464, 225, 225, 225, 225, 1520, 1520, 1190, 555, 1366, 1366, 225, 225, 71, 71, 71, 71, 71, 71, 71, 71, 1744, 1744, 1358, 667, 1534, 1534, 281, 281, 1828, 1828, 1618, 281, 71, 71, 71, 71, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 1554, 1554, 1203, 751, 1302, 1302, 400, 400, 1568, 1568, 1316, 400, 148, 148, 148, 148, 1841, 1841, 1498, 491, 1722, 1722, 148, 148, 29, 29, 29, 29, 29, 29, 29, 29, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 8 => ![2876, 2876, 2247, 1496, 2384, 2384, 867, 867, 2820, 2820, 2328, 867, 375, 375, 375, 375, 3366, 3366, 2692, 1049, 3092, 3092, 375, 375, 101, 101, 101, 101, 101, 101, 101, 101, 3702, 3702, 2944, 1217, 3344, 3344, 459, 459, 3876, 3876, 3518, 459, 101, 101, 101, 101, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 3338, 3338, 2593, 1442, 2868, 2868, 697, 697, 3428, 3428, 2958, 697, 227, 227, 227, 227, 3890, 3890, 3266, 851, 3700, 3700, 227, 227, 37, 37, 37, 37, 37, 37, 37, 37, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 9 => ![6220, 6220, 4845, 2942, 5257, 5257, 1567, 1567, 6253, 6253, 5290, 1567, 604, 604, 604, 604, 7261, 7261, 5962, 1903, 6796, 6796, 604, 604, 139, 139, 139, 139, 139, 139, 139, 139, 7741, 7741, 6322, 2143, 7156, 7156, 724, 724, 8068, 8068, 7483, 724, 139, 139, 139, 139, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 7085, 7085, 5573, 2686, 6248, 6248, 1174, 1174, 7340, 7340, 6503, 1174, 337, 337, 337, 337, 8078, 8078, 6995, 1420, 7787, 7787, 337, 337, 46, 46, 46, 46, 46, 46, 46, 46, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 10 => ![13311, 13311, 10423, 5632, 11510, 11510, 2744, 2744, 13598, 13598, 11797, 2744, 943, 943, 943, 943, 15344, 15344, 12961, 3326, 14587, 14587, 943, 943, 186, 186, 186, 186, 186, 186, 186, 186, 16004, 16004, 13456, 3656, 15082, 15082, 1108, 1108, 16576, 16576, 15654, 1108, 186, 186, 186, 186, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 14876, 14876, 11935, 4859, 13444, 13444, 1918, 1918, 15448, 15448, 14016, 1918, 486, 486, 486, 486, 16573, 16573, 14766, 2293, 16143, 16143, 486, 486, 56, 56, 56, 56, 56, 56, 56, 56, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 11 => ![28193, 28193, 22363, 10495, 24959, 24959, 4665, 4665, 29051, 29051, 25817, 4665, 1431, 1431, 1431, 1431, 31922, 31922, 27731, 5622, 30734, 30734, 1431, 1431, 243, 243, 243, 243, 243, 243, 243, 243, 32802, 32802, 28391, 6062, 31394, 31394, 1651, 1651, 33748, 33748, 32340, 1651, 243, 243, 243, 243, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 30935, 30935, 25435, 8548, 28570, 28570, 3048, 3048, 32068, 32068, 29703, 3048, 683, 683, 683, 683, 33718, 33718, 30803, 3598, 33102, 33102, 683, 683, 67, 67, 67, 67, 67, 67, 67, 67, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 12 => ![59134, 59134, 47803, 19047, 53534, 53534, 7716, 7716, 61124, 61124, 55524, 7716, 2116, 2116, 2116, 2116, 65645, 65645, 58538, 9223, 63840, 63840, 2116, 2116, 311, 311, 311, 311, 311, 311, 311, 311, 66789, 66789, 59396, 9795, 64698, 64698, 2402, 2402, 68284, 68284, 66193, 2402, 311, 311, 311, 311, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 63797, 63797, 53874, 14646, 60012, 60012, 4723, 4723, 65864, 65864, 62079, 4723, 938, 938, 938, 938, 68207, 68207, 63641, 5504, 67348, 67348, 938, 938, 79, 79, 79, 79, 79, 79, 79, 79, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | _ => fun _ => 0

theorem V_zero : ∀ i : Fin N, V 0 i = 1 := by decide +kernel

theorem V_step : ∀ m : Fin 12, ∀ i : Fin N, ((adjL i).map (V m.val)).sum = V (m.val + 1) i := by
  decide +kernel

theorem cnt_eq_V (m : ℕ) (hm : m ≤ 12) (i : Fin N) : cnt R' m i = V m i := by
  induction m generalizing i with
  | zero => rw [V_zero]; rfl
  | succ m ih =>
    show (∑ t, if R' i t then cnt R' m t else 0) = _
    rw [sum_adj R' adjL adj_iff adj_nodup]
    have := V_step ⟨m, by omega⟩ i
    simp only at this
    rw [← this]
    congr 1
    apply List.map_congr_left
    intro t _
    exact ih (by omega) t

def qp : ℕ → ℕ
  | 0 => 0
  | 1 => 21
  | 2 => 0
  | 3 => 285
  | 4 => 0
  | 5 => 714
  | 6 => 0
  | 7 => 450
  | 8 => 0
  | 9 => 65
  | 10 => 0
  | 11 => 1
  | _ => 0

def qn : ℕ → ℕ
  | 0 => 2
  | 1 => 0
  | 2 => 100
  | 3 => 0
  | 4 => 540
  | 5 => 0
  | 6 => 672
  | 7 => 0
  | 8 => 210
  | 9 => 0
  | 10 => 12
  | 11 => 0
  | _ => 0

theorem vec_base : ∀ i : Fin N, (∑ k ∈ Finset.range 12, qp k * V (1 + k) i) =
    ∑ k ∈ Finset.range 12, qn k * V (1 + k) i := by decide +kernel

theorem vec_rec (n : ℕ) (hn : 1 ≤ n) : ∀ i : Fin N,
    (∑ k ∈ Finset.range 12, qp k * cnt R' (n + k) i) =
      ∑ k ∈ Finset.range 12, qn k * cnt R' (n + k) i := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro i
    have h : ∀ w : ℕ → ℕ, (∑ k ∈ Finset.range 12, w k * cnt R' (1 + k) i) =
        ∑ k ∈ Finset.range 12, w k * V (1 + k) i := by
      intro w
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [cnt_eq_V (1 + k) (by omega)]
    rw [h, h]
    exact vec_base i
  | succ n hn ih =>
    intro i
    rw [lin_step, lin_step]
    apply Finset.sum_congr rfl
    intro t _
    rw [ih t]

def Tot (n : ℕ) : ℕ := ∑ i, cnt R' n i

def c (k : ℕ) : ℚ := (qp k : ℚ) - (qn k : ℚ)

theorem Tot_rec (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range 12, c k * (Tot (n + k) : ℚ) = 0 := by
  have h := fun i => vec_rec n hn i
  have hs : (∑ k ∈ Finset.range 12, qp k * Tot (n + k)) =
      ∑ k ∈ Finset.range 12, qn k * Tot (n + k) := by
    simp only [Tot, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range 12)]
    exact Finset.sum_congr rfl (fun i _ => h i)
  simp only [c, sub_mul, Finset.sum_sub_distrib]
  have := congrArg (fun x : ℕ => (x : ℚ)) hs
  push_cast at this
  rw [this, sub_self]

def F (n : ℕ) : ℚ := (2520 * (289 * (2 : ℚ) ^ n - 209) - 314796 * (n : ℚ) - 41972 * (n : ℚ) ^ 2 - 23779 * (n : ℚ) ^ 3 + 385 * (n : ℚ) ^ 4 - 364 * (n : ℚ) ^ 5 + 7 * (n : ℚ) ^ 6 - (n : ℚ) ^ 7) / 1260

theorem F_rec (n : ℕ) (_hn : 1 ≤ n) : ∑ k ∈ Finset.range 12, c k * F (n + k) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c, qp, qn, F]
  push_cast
  ring

theorem Tot_eq_V (n : ℕ) (hn : n ≤ 12) : Tot n = ∑ i, V n i := by
  simp only [Tot]
  exact Finset.sum_congr rfl (fun i _ => cnt_eq_V n hn i)

theorem Tot_small : ∀ n : Fin 12, (∑ i, V n.val i) = ![128, 436, 1106, 2604, 5882, 12950, 27986, 59590, 125334, 260916, 538538, 1103752] n := by
  decide +kernel

theorem Tot_closed (n : ℕ) (hn : 1 ≤ n) : (Tot n : ℚ) = F n := by
  refine rec_solve 11 c (by norm_num [c, qp, qn]) (fun n => (Tot n : ℚ)) F Tot_rec F_rec ?_ n hn
  intro n h1 h2
  rw [Tot_eq_V n (by omega)]
  have := Tot_small ⟨n, by omega⟩
  simp only at this
  rw [this]
  interval_cases n <;> norm_num [F]

theorem good_iff {n : ℕ} (x : Fin (n + 1) → Fin 7 → Fin 2) : Good x ↔ Chain Rel x := by
  constructor
  · intro h i
    exact h i.castSucc i.succ (by simp)
  · intro h i j hij
    have hj := j.isLt
    have hi : i.val < n := by omega
    have := h ⟨i.val, hi⟩
    have e1 : (⟨i.val, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, hi⟩ : Fin n).succ = j := Fin.ext (by simp; omega)
    rw [e1, e2] at this
    exact this

theorem a_eq (n : ℕ) : a n = Tot n := by
  have h1 : a n = Nat.card {x : Fin (n + 1) → Fin K → Fin 2 // Chain Rel x} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => good_iff x))
  rw [h1, Nat.card_eq_fintype_card, card_chain, Tot]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ (fun s => cnt_equiv Rel finFunctionFinEquiv n s)

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = F n := by
  rw [a_eq]
  exact Tot_closed n hn

theorem v1 : (a 1 : ℚ) = 436 := by rw [closed 1 (by norm_num)]; norm_num [F]
theorem v2 : (a 2 : ℚ) = 1106 := by rw [closed 2 (by norm_num)]; norm_num [F]
theorem v3 : (a 3 : ℚ) = 2604 := by rw [closed 3 (by norm_num)]; norm_num [F]
theorem v4 : (a 4 : ℚ) = 5882 := by rw [closed 4 (by norm_num)]; norm_num [F]
theorem v5 : (a 5 : ℚ) = 12950 := by rw [closed 5 (by norm_num)]; norm_num [F]
theorem v6 : (a 6 : ℚ) = 27986 := by rw [closed 6 (by norm_num)]; norm_num [F]
theorem v7 : (a 7 : ℚ) = 59590 := by rw [closed 7 (by norm_num)]; norm_num [F]
theorem v8 : (a 8 : ℚ) = 125334 := by rw [closed 8 (by norm_num)]; norm_num [F]
theorem v9 : (a 9 : ℚ) = 260916 := by rw [closed 9 (by norm_num)]; norm_num [F]
theorem v10 : (a 10 : ℚ) = 538538 := by rw [closed 10 (by norm_num)]; norm_num [F]

theorem part_rec : ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 44 * (a (n - 2) : ℤ) + 112 * (a (n - 3) : ℤ) - 182 * (a (n - 4) : ℤ) + 196 * (a (n - 5) : ℤ) - 140 * (a (n - 6) : ℤ) + 64 * (a (n - 7) : ℤ) - 17 * (a (n - 8) : ℤ) + 2 * (a (n - 9) : ℤ) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega]
  rw [show m + 10 - 2 = m + 8 by omega]
  rw [show m + 10 - 3 = m + 7 by omega]
  rw [show m + 10 - 4 = m + 6 by omega]
  rw [show m + 10 - 5 = m + 5 by omega]
  rw [show m + 10 - 6 = m + 4 by omega]
  rw [show m + 10 - 7 = m + 3 by omega]
  rw [show m + 10 - 8 = m + 2 by omega]
  rw [show m + 10 - 9 = m + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [closed (m + 10) (by omega)]
  rw [closed (m + 9) (by omega)]
  rw [closed (m + 8) (by omega)]
  rw [closed (m + 7) (by omega)]
  rw [closed (m + 6) (by omega)]
  rw [closed (m + 5) (by omega)]
  rw [closed (m + 4) (by omega)]
  rw [closed (m + 3) (by omega)]
  rw [closed (m + 2) (by omega)]
  rw [closed (m + 1) (by omega)]
  simp only [F]
  push_cast
  ring


open PowerSeries in
theorem part_gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have hQ : ((1 - PowerSeries.X) ^ 8 * (1 - 2 * PowerSeries.X) : PowerSeries ℚ) = 1 - C 10 * X ^ 1 + C 44 * X ^ 2 - C 112 * X ^ 3 + C 182 * X ^ 4 - C 196 * X ^ 5 + C 140 * X ^ 6 - C 64 * X ^ 7 + C 17 * X ^ 8 - C 2 * X ^ 9 := by
    simp only [map_ofNat]
    ring
  have hP : (2 * PowerSeries.X * (218 - 1627 * PowerSeries.X + 5364 * PowerSeries.X ^ 2 - 10163 * PowerSeries.X ^ 3 + 12093 * PowerSeries.X ^ 4 - 9259 * PowerSeries.X ^ 5 + 4469 * PowerSeries.X ^ 6 - 1253 * PowerSeries.X ^ 7 + 160 * PowerSeries.X ^ 8) : PowerSeries ℚ) = C 436 * X ^ 1 - C 3254 * X ^ 2 + C 10728 * X ^ 3 - C 20326 * X ^ 4 + C 24186 * X ^ 5 - C 18518 * X ^ 6 + C 8938 * X ^ 7 - C 2506 * X ^ 8 + C 320 * X ^ 9 := by
    simp only [map_ofNat]
    ring
  rw [hQ, hP, mul_comm]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, map_neg, neg_mul,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
  by_cases hn : n < 10
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    simp only [if_pos (show 1 ≤ m + 10 by omega), if_pos (show 2 ≤ m + 10 by omega), if_pos (show 3 ≤ m + 10 by omega), if_pos (show 4 ≤ m + 10 by omega), if_pos (show 5 ≤ m + 10 by omega), if_pos (show 6 ≤ m + 10 by omega), if_pos (show 7 ≤ m + 10 by omega), if_pos (show 8 ≤ m + 10 by omega), if_pos (show 9 ≤ m + 10 by omega), if_neg (show m + 10 - 0 ≠ 0 by omega), if_neg (show m + 10 - 1 ≠ 0 by omega), if_neg (show m + 10 - 2 ≠ 0 by omega), if_neg (show m + 10 - 3 ≠ 0 by omega), if_neg (show m + 10 - 4 ≠ 0 by omega), if_neg (show m + 10 - 5 ≠ 0 by omega), if_neg (show m + 10 - 6 ≠ 0 by omega), if_neg (show m + 10 - 7 ≠ 0 by omega), if_neg (show m + 10 - 8 ≠ 0 by omega), if_neg (show m + 10 - 9 ≠ 0 by omega), if_neg (show m + 10 ≠ 0 by omega), if_neg (show m + 10 ≠ 1 by omega), if_neg (show m + 10 ≠ 2 by omega), if_neg (show m + 10 ≠ 3 by omega), if_neg (show m + 10 ≠ 4 by omega), if_neg (show m + 10 ≠ 5 by omega), if_neg (show m + 10 ≠ 6 by omega), if_neg (show m + 10 ≠ 7 by omega), if_neg (show m + 10 ≠ 8 by omega), if_neg (show m + 10 ≠ 9 by omega)]
    rw [show m + 10 - 1 = m + 9 by omega]
    rw [show m + 10 - 2 = m + 8 by omega]
    rw [show m + 10 - 3 = m + 7 by omega]
    rw [show m + 10 - 4 = m + 6 by omega]
    rw [show m + 10 - 5 = m + 5 by omega]
    rw [show m + 10 - 6 = m + 4 by omega]
    rw [show m + 10 - 7 = m + 3 by omega]
    rw [show m + 10 - 8 = m + 2 by omega]
    rw [show m + 10 - 9 = m + 1 by omega]
    rw [closed (m + 10) (by omega)]
    rw [closed (m + 9) (by omega)]
    rw [closed (m + 8) (by omega)]
    rw [closed (m + 7) (by omega)]
    rw [closed (m + 6) (by omega)]
    rw [closed (m + 5) (by omega)]
    rw [closed (m + 4) (by omega)]
    rw [closed (m + 3) (by omega)]
    rw [closed (m + 2) (by omega)]
    rw [closed (m + 1) (by omega)]
    simp only [F]
    push_cast
    ring

theorem main_proof : (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 44 * (a (n - 2) : ℤ) + 112 * (a (n - 3) : ℤ) - 182 * (a (n - 4) : ℤ) + 196 * (a (n - 5) : ℤ) - 140 * (a (n - 6) : ℤ) + 64 * (a (n - 7) : ℤ) - 17 * (a (n - 8) : ℤ) + 2 * (a (n - 9) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2520 * (289 * (2 : ℚ) ^ n - 209) - 314796 * (n : ℚ) - 41972 * (n : ℚ) ^ 2 - 23779 * (n : ℚ) ^ 3 + 385 * (n : ℚ) ^ 4 - 364 * (n : ℚ) ^ 5 + 7 * (n : ℚ) ^ 6 - (n : ℚ) ^ 7) / 1260) :=
  ⟨part_rec, part_gf, fun n hn => closed n hn⟩

end A250781Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a250781.main := A250781Proof.main_proof
