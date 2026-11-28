import OMAStatements.S_oeis_a250780

/-!
Proof of the conjectures of OEIS A250780 (statement by @ivillar).

Method: rows are states; consecutive rows must satisfy the row relation, so a(n) is the number
of walks with n steps in a graph on the 2^6 = 64 rows. Rows are encoded as Fin 64 by
finFunctionFinEquiv; the adjacency lists and the first 11 level vectors are checked by the
kernel. The vector sequence is annihilated by (x - 2)(x - 1)^8 from n = 1 on, which gives a
recurrence for a(n) and, by strong induction, the closed form; the recurrence of the entry
and the generating function follow from the closed form.
-/

namespace A250780Proof

open OMA.S_oeis_a250780 Finset


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

abbrev K : ℕ := 6
abbrev N : ℕ := 2 ^ K

def Rel (u v : Fin K → Fin 2) : Prop :=
  ∀ j : Fin 5, Blk (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

instance : DecidableRel Rel := fun u v => by unfold Rel Blk; infer_instance

def R' (i j : Fin N) : Prop := Rel (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)

instance : DecidableRel R' := fun i j => by unfold R'; infer_instance

def adjL : Fin N → List (Fin N) :=
  ![[0, 32, 48, 56, 60, 62, 63],
    [1, 33, 49, 57, 61, 62, 63],
    [2, 34, 50, 58, 61, 62],
    [3, 35, 51, 59, 63],
    [4, 36, 52, 58, 59, 60],
    [5, 37, 53, 58, 59, 61],
    [6, 38, 54, 62],
    [7, 39, 55, 63],
    [8, 40, 52, 54, 55, 56],
    [9, 41, 53, 54, 55, 57],
    [10, 42, 53, 54, 58],
    [11, 43, 55, 59],
    [12, 44, 60],
    [13, 45, 61],
    [14, 46, 62],
    [15, 47, 63],
    [16, 40, 44, 46, 47, 48],
    [17, 41, 45, 46, 47, 49],
    [18, 42, 45, 46, 50],
    [19, 43, 47, 51],
    [20, 42, 43, 44, 52],
    [21, 42, 43, 45, 53],
    [22, 46, 54],
    [23, 47, 55],
    [24, 56],
    [25, 57],
    [26, 58],
    [27, 59],
    [28, 60],
    [29, 61],
    [30, 62],
    [31, 63],
    [16, 24, 28, 30, 31, 32],
    [17, 25, 29, 30, 31, 33],
    [18, 26, 29, 30, 34],
    [19, 27, 31, 35],
    [20, 26, 27, 28, 36],
    [21, 26, 27, 29, 37],
    [22, 30, 38],
    [23, 31, 39],
    [20, 22, 23, 24, 40],
    [21, 22, 23, 25, 41],
    [21, 22, 26, 42],
    [23, 27, 43],
    [28, 44],
    [29, 45],
    [30, 46],
    [31, 47],
    [48],
    [49],
    [50],
    [51],
    [52],
    [53],
    [54],
    [55],
    [56],
    [57],
    [58],
    [59],
    [60],
    [61],
    [62],
    [63]]

theorem adj_iff_0 : ∀ i : Fin N, 0 ≤ i.val → i.val < 16 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_16 : ∀ i : Fin N, 16 ≤ i.val → i.val < 32 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_32 : ∀ i : Fin N, 32 ≤ i.val → i.val < 48 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel
theorem adj_iff_48 : ∀ i : Fin N, 48 ≤ i.val → i.val < 64 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel

theorem adj_iff (i j : Fin N) : R' i j ↔ j ∈ adjL i :=
  if h0 : i.val < 16 then adj_iff_0 i (by omega) h0 j else if h16 : i.val < 32 then adj_iff_16 i (by omega) h16 j else if h32 : i.val < 48 then adj_iff_32 i (by omega) h32 j else adj_iff_48 i (by omega) (by have := i.isLt; simp only [N, K] at this; omega) j

theorem adj_nodup : ∀ i : Fin N, (adjL i).Nodup := by decide +kernel

def V : ℕ → Fin N → ℕ
  | 0 => ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 1 => ![7, 7, 6, 5, 6, 6, 4, 4, 6, 6, 5, 4, 3, 3, 3, 3, 6, 6, 5, 4, 5, 5, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 6, 6, 5, 4, 5, 5, 3, 3, 5, 5, 4, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 2 => ![18, 18, 15, 12, 15, 15, 9, 9, 15, 15, 12, 9, 6, 6, 6, 6, 18, 18, 14, 10, 15, 15, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 20, 20, 16, 12, 16, 16, 8, 8, 18, 18, 14, 8, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 3 => ![43, 43, 35, 27, 35, 35, 19, 19, 37, 37, 29, 19, 11, 11, 11, 11, 49, 49, 37, 23, 42, 42, 11, 11, 4, 4, 4, 4, 4, 4, 4, 4, 50, 50, 39, 28, 40, 40, 17, 17, 48, 48, 38, 17, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 4 => ![98, 98, 78, 58, 79, 79, 38, 38, 89, 89, 70, 38, 19, 19, 19, 19, 119, 119, 90, 48, 105, 105, 19, 19, 5, 5, 5, 5, 5, 5, 5, 5, 115, 115, 88, 59, 94, 94, 32, 32, 116, 116, 95, 32, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 5 => ![218, 218, 170, 120, 177, 177, 72, 72, 209, 209, 168, 72, 31, 31, 31, 31, 269, 269, 208, 92, 244, 244, 31, 31, 6, 6, 6, 6, 6, 6, 6, 6, 254, 254, 193, 117, 214, 214, 56, 56, 264, 264, 224, 56, 16, 16, 16, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 6 => ![477, 477, 367, 240, 395, 395, 130, 130, 477, 477, 395, 130, 48, 48, 48, 48, 582, 582, 465, 165, 541, 541, 48, 48, 7, 7, 7, 7, 7, 7, 7, 7, 547, 547, 419, 221, 476, 476, 93, 93, 576, 576, 505, 93, 22, 22, 22, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 7 => ![1029, 1029, 790, 464, 875, 875, 225, 225, 1057, 1057, 903, 225, 71, 71, 71, 71, 1225, 1225, 1015, 281, 1162, 1162, 71, 71, 8, 8, 8, 8, 8, 8, 8, 8, 1157, 1157, 905, 400, 1038, 1038, 148, 148, 1220, 1220, 1101, 148, 29, 29, 29, 29, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 8 => ![2191, 2191, 1699, 867, 1917, 1917, 375, 375, 2281, 2281, 2007, 375, 101, 101, 101, 101, 2533, 2533, 2175, 459, 2441, 2441, 101, 101, 9, 9, 9, 9, 9, 9, 9, 9, 2414, 2414, 1944, 697, 2224, 2224, 227, 227, 2532, 2532, 2342, 227, 37, 37, 37, 37, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 9 => ![4610, 4610, 3647, 1567, 4145, 4145, 604, 604, 4817, 4817, 4352, 604, 139, 139, 139, 139, 5177, 5177, 4592, 724, 5048, 5048, 139, 139, 10, 10, 10, 10, 10, 10, 10, 10, 4983, 4983, 4146, 1174, 4692, 4692, 337, 337, 5184, 5184, 4893, 337, 46, 46, 46, 46, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 10 => ![9598, 9598, 7797, 2744, 8841, 8841, 943, 943, 10005, 10005, 9248, 943, 186, 186, 186, 186, 10500, 10500, 9578, 1108, 10325, 10325, 186, 186, 11, 11, 11, 11, 11, 11, 11, 11, 10200, 10200, 8768, 1918, 9770, 9770, 486, 486, 10520, 10520, 10090, 486, 56, 56, 56, 56, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | _ => fun _ => 0

theorem V_zero : ∀ i : Fin N, V 0 i = 1 := by decide +kernel

theorem V_step : ∀ m : Fin 10, ∀ i : Fin N, ((adjL i).map (V m.val)).sum = V (m.val + 1) i := by
  decide +kernel

theorem cnt_eq_V (m : ℕ) (hm : m ≤ 10) (i : Fin N) : cnt R' m i = V m i := by
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
  | 1 => 17
  | 2 => 0
  | 3 => 140
  | 4 => 0
  | 5 => 182
  | 6 => 0
  | 7 => 44
  | 8 => 0
  | 9 => 1
  | _ => 0

def qn : ℕ → ℕ
  | 0 => 2
  | 1 => 0
  | 2 => 64
  | 3 => 0
  | 4 => 196
  | 5 => 0
  | 6 => 112
  | 7 => 0
  | 8 => 10
  | 9 => 0
  | _ => 0

theorem vec_base : ∀ i : Fin N, (∑ k ∈ Finset.range 10, qp k * V (1 + k) i) =
    ∑ k ∈ Finset.range 10, qn k * V (1 + k) i := by decide +kernel

theorem vec_rec (n : ℕ) (hn : 1 ≤ n) : ∀ i : Fin N,
    (∑ k ∈ Finset.range 10, qp k * cnt R' (n + k) i) =
      ∑ k ∈ Finset.range 10, qn k * cnt R' (n + k) i := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro i
    have h : ∀ w : ℕ → ℕ, (∑ k ∈ Finset.range 10, w k * cnt R' (1 + k) i) =
        ∑ k ∈ Finset.range 10, w k * V (1 + k) i := by
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
    ∑ k ∈ Finset.range 10, c k * (Tot (n + k) : ℚ) = 0 := by
  have h := fun i => vec_rec n hn i
  have hs : (∑ k ∈ Finset.range 10, qp k * Tot (n + k)) =
      ∑ k ∈ Finset.range 10, qn k * Tot (n + k) := by
    simp only [Tot, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range 10)]
    exact Finset.sum_congr rfl (fun i _ => h i)
  simp only [c, sub_mul, Finset.sum_sub_distrib]
  have := congrArg (fun x : ℕ => (x : ℚ)) hs
  push_cast at this
  rw [this, sub_self]

def F (n : ℕ) : ℚ := 9 / 2 * (49 * 2 ^ n - 32) - 374 * (n : ℚ) / 5 - 9 * (n : ℚ) ^ 2 - 25 * (n : ℚ) ^ 3 / 6 - (n : ℚ) ^ 5 / 30

theorem F_rec (n : ℕ) (_hn : 1 ≤ n) : ∑ k ∈ Finset.range 10, c k * F (n + k) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c, qp, qn, F]
  push_cast
  ring

theorem Tot_eq_V (n : ℕ) (hn : n ≤ 10) : Tot n = ∑ i, V n i := by
  simp only [Tot]
  exact Finset.sum_congr rfl (fun i _ => cnt_eq_V n hn i)

theorem Tot_small : ∀ n : Fin 10, (∑ i, V n.val i) = ![64, 209, 518, 1194, 2640, 5688, 12036, 25126, 51904, 106344] n := by
  decide +kernel

theorem Tot_closed (n : ℕ) (hn : 1 ≤ n) : (Tot n : ℚ) = F n := by
  refine rec_solve 9 c (by norm_num [c, qp, qn]) (fun n => (Tot n : ℚ)) F Tot_rec F_rec ?_ n hn
  intro n h1 h2
  rw [Tot_eq_V n (by omega)]
  have := Tot_small ⟨n, by omega⟩
  simp only at this
  rw [this]
  interval_cases n <;> norm_num [F]


theorem a_eq (n : ℕ) : a n = Tot n := by
  have h1 : a n = Nat.card {x : Fin (n + 1) → Fin K → Fin 2 // Chain Rel x} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  rw [h1, Nat.card_eq_fintype_card, card_chain, Tot]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ (fun s => cnt_equiv Rel finFunctionFinEquiv n s)

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = F n := by
  rw [a_eq]
  exact Tot_closed n hn

theorem v1 : (a 1 : ℚ) = 209 := by rw [closed 1 (by norm_num)]; norm_num [F]
theorem v2 : (a 2 : ℚ) = 518 := by rw [closed 2 (by norm_num)]; norm_num [F]
theorem v3 : (a 3 : ℚ) = 1194 := by rw [closed 3 (by norm_num)]; norm_num [F]
theorem v4 : (a 4 : ℚ) = 2640 := by rw [closed 4 (by norm_num)]; norm_num [F]
theorem v5 : (a 5 : ℚ) = 5688 := by rw [closed 5 (by norm_num)]; norm_num [F]
theorem v6 : (a 6 : ℚ) = 12036 := by rw [closed 6 (by norm_num)]; norm_num [F]
theorem v7 : (a 7 : ℚ) = 25126 := by rw [closed 7 (by norm_num)]; norm_num [F]
theorem v8 : (a 8 : ℚ) = 51904 := by rw [closed 8 (by norm_num)]; norm_num [F]

theorem part_rec : ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega]
  rw [show m + 8 - 2 = m + 6 by omega]
  rw [show m + 8 - 3 = m + 5 by omega]
  rw [show m + 8 - 4 = m + 4 by omega]
  rw [show m + 8 - 5 = m + 3 by omega]
  rw [show m + 8 - 6 = m + 2 by omega]
  rw [show m + 8 - 7 = m + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
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
  have hQ : ((1 - PowerSeries.X) ^ 6 * (1 - 2 * PowerSeries.X) : PowerSeries ℚ) = 1 - C 8 * X ^ 1 + C 27 * X ^ 2 - C 50 * X ^ 3 + C 55 * X ^ 4 - C 36 * X ^ 5 + C 13 * X ^ 6 - C 2 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have hP : (PowerSeries.X * (209 - 1154 * PowerSeries.X + 2693 * PowerSeries.X ^ 2 - 3376 * PowerSeries.X ^ 3 + 2401 * PowerSeries.X ^ 4 - 922 * PowerSeries.X ^ 5 + 153 * PowerSeries.X ^ 6) : PowerSeries ℚ) = C 209 * X ^ 1 - C 1154 * X ^ 2 + C 2693 * X ^ 3 - C 3376 * X ^ 4 + C 2401 * X ^ 5 - C 922 * X ^ 6 + C 153 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [hQ, hP, mul_comm]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, map_neg, neg_mul,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
  by_cases hn : n < 8
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [if_pos (show 1 ≤ m + 8 by omega), if_pos (show 2 ≤ m + 8 by omega), if_pos (show 3 ≤ m + 8 by omega), if_pos (show 4 ≤ m + 8 by omega), if_pos (show 5 ≤ m + 8 by omega), if_pos (show 6 ≤ m + 8 by omega), if_pos (show 7 ≤ m + 8 by omega), if_neg (show m + 8 - 0 ≠ 0 by omega), if_neg (show m + 8 - 1 ≠ 0 by omega), if_neg (show m + 8 - 2 ≠ 0 by omega), if_neg (show m + 8 - 3 ≠ 0 by omega), if_neg (show m + 8 - 4 ≠ 0 by omega), if_neg (show m + 8 - 5 ≠ 0 by omega), if_neg (show m + 8 - 6 ≠ 0 by omega), if_neg (show m + 8 - 7 ≠ 0 by omega), if_neg (show m + 8 ≠ 0 by omega), if_neg (show m + 8 ≠ 1 by omega), if_neg (show m + 8 ≠ 2 by omega), if_neg (show m + 8 ≠ 3 by omega), if_neg (show m + 8 ≠ 4 by omega), if_neg (show m + 8 ≠ 5 by omega), if_neg (show m + 8 ≠ 6 by omega), if_neg (show m + 8 ≠ 7 by omega)]
    rw [show m + 8 - 1 = m + 7 by omega]
    rw [show m + 8 - 2 = m + 6 by omega]
    rw [show m + 8 - 3 = m + 5 by omega]
    rw [show m + 8 - 4 = m + 4 by omega]
    rw [show m + 8 - 5 = m + 3 by omega]
    rw [show m + 8 - 6 = m + 2 by omega]
    rw [show m + 8 - 7 = m + 1 by omega]
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

theorem main_proof : (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 9 / 2 * (49 * 2 ^ n - 32) - 374 * (n : ℚ) / 5 - 9 * (n : ℚ) ^ 2 - 25 * (n : ℚ) ^ 3 / 6 - (n : ℚ) ^ 5 / 30) :=
  ⟨part_rec, part_gf, fun n hn => closed n hn⟩

end A250780Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a250780.main := A250780Proof.main_proof
