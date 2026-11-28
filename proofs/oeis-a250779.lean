import OMAStatements.S_oeis_a250779

/-!
Proof of the conjectures of OEIS A250779 (statement by @ivillar).

Method: rows are states; consecutive rows must satisfy the row relation, so a(n) is the number
of walks with n steps in a graph on the 2^5 = 32 rows. Rows are encoded as Fin 32 by
finFunctionFinEquiv; the adjacency lists and the first 9 level vectors are checked by the
kernel. The vector sequence is annihilated by (x - 2)(x - 1)^6 from n = 1 on, which gives a
recurrence for a(n) and, by strong induction, the closed form; the recurrence of the entry
and the generating function follow from the closed form.
-/

namespace A250779Proof

open OMA.S_oeis_a250779 Finset


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

abbrev K : ℕ := 5
abbrev N : ℕ := 2 ^ K

def Rel (u v : Fin K → Fin 2) : Prop :=
  ∀ j : Fin 4, CellOK ((u j.castSucc : ℕ) : ℤ) ((u j.succ : ℕ) : ℤ) ((v j.castSucc : ℕ) : ℤ) ((v j.succ : ℕ) : ℤ)

instance : DecidableRel Rel := fun u v => by unfold Rel CellOK; infer_instance

def R' (i j : Fin N) : Prop := Rel (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)

instance : DecidableRel R' := fun i j => by unfold R'; infer_instance

def adjL : Fin N → List (Fin N) :=
  ![[0, 16, 24, 28, 30, 31],
    [1, 17, 25, 29, 30, 31],
    [2, 18, 26, 29, 30],
    [3, 19, 27, 31],
    [4, 20, 26, 27, 28],
    [5, 21, 26, 27, 29],
    [6, 22, 30],
    [7, 23, 31],
    [8, 20, 22, 23, 24],
    [9, 21, 22, 23, 25],
    [10, 21, 22, 26],
    [11, 23, 27],
    [12, 28],
    [13, 29],
    [14, 30],
    [15, 31],
    [8, 12, 14, 15, 16],
    [9, 13, 14, 15, 17],
    [10, 13, 14, 18],
    [11, 15, 19],
    [10, 11, 12, 20],
    [10, 11, 13, 21],
    [14, 22],
    [15, 23],
    [24],
    [25],
    [26],
    [27],
    [28],
    [29],
    [30],
    [31]]

theorem adj_iff_0 : ∀ i : Fin N, 0 ≤ i.val → i.val < 32 →
    ∀ j : Fin N, R' i j ↔ j ∈ adjL i := by decide +kernel

theorem adj_iff (i j : Fin N) : R' i j ↔ j ∈ adjL i :=
  adj_iff_0 i (by omega) (by have := i.isLt; simp only [N, K] at this; omega) j

theorem adj_nodup : ∀ i : Fin N, (adjL i).Nodup := by decide +kernel

def V : ℕ → Fin N → ℕ
  | 0 => ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | 1 => ![6, 6, 5, 4, 5, 5, 3, 3, 5, 5, 4, 3, 2, 2, 2, 2, 5, 5, 4, 3, 4, 4, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1]
  | 2 => ![15, 15, 12, 9, 12, 12, 6, 6, 14, 14, 11, 6, 3, 3, 3, 3, 16, 16, 12, 8, 13, 13, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1]
  | 3 => ![35, 35, 27, 19, 28, 28, 11, 11, 36, 36, 29, 11, 4, 4, 4, 4, 39, 39, 29, 17, 33, 33, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1]
  | 4 => ![78, 78, 59, 38, 64, 64, 19, 19, 84, 84, 70, 19, 5, 5, 5, 5, 87, 87, 66, 32, 77, 77, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1]
  | 5 => ![169, 169, 128, 72, 144, 144, 31, 31, 184, 184, 159, 31, 6, 6, 6, 6, 186, 186, 146, 56, 171, 171, 16, 16, 1, 1, 1, 1, 1, 1, 1, 1]
  | 6 => ![359, 359, 277, 130, 318, 318, 48, 48, 388, 388, 347, 48, 7, 7, 7, 7, 388, 388, 317, 93, 367, 367, 22, 22, 1, 1, 1, 1, 1, 1, 1, 1]
  | 7 => ![751, 751, 597, 225, 688, 688, 71, 71, 800, 800, 737, 71, 8, 8, 8, 8, 797, 797, 678, 148, 769, 769, 29, 29, 1, 1, 1, 1, 1, 1, 1, 1]
  | 8 => ![1552, 1552, 1278, 375, 1460, 1460, 101, 101, 1628, 1628, 1536, 101, 9, 9, 9, 9, 1621, 1621, 1431, 227, 1585, 1585, 37, 37, 1, 1, 1, 1, 1, 1, 1, 1]
  | _ => fun _ => 0

theorem V_zero : ∀ i : Fin N, V 0 i = 1 := by decide +kernel

theorem V_step : ∀ m : Fin 8, ∀ i : Fin N, ((adjL i).map (V m.val)).sum = V (m.val + 1) i := by
  decide +kernel

theorem cnt_eq_V (m : ℕ) (hm : m ≤ 8) (i : Fin N) : cnt R' m i = V m i := by
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
  | 1 => 13
  | 2 => 0
  | 3 => 55
  | 4 => 0
  | 5 => 27
  | 6 => 0
  | 7 => 1
  | _ => 0

def qn : ℕ → ℕ
  | 0 => 2
  | 1 => 0
  | 2 => 36
  | 3 => 0
  | 4 => 50
  | 5 => 0
  | 6 => 8
  | 7 => 0
  | _ => 0

theorem vec_base : ∀ i : Fin N, (∑ k ∈ Finset.range 8, qp k * V (1 + k) i) =
    ∑ k ∈ Finset.range 8, qn k * V (1 + k) i := by decide +kernel

theorem vec_rec (n : ℕ) (hn : 1 ≤ n) : ∀ i : Fin N,
    (∑ k ∈ Finset.range 8, qp k * cnt R' (n + k) i) =
      ∑ k ∈ Finset.range 8, qn k * cnt R' (n + k) i := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro i
    have h : ∀ w : ℕ → ℕ, (∑ k ∈ Finset.range 8, w k * cnt R' (1 + k) i) =
        ∑ k ∈ Finset.range 8, w k * V (1 + k) i := by
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
    ∑ k ∈ Finset.range 8, c k * (Tot (n + k) : ℚ) = 0 := by
  have h := fun i => vec_rec n hn i
  have hs : (∑ k ∈ Finset.range 8, qp k * Tot (n + k)) =
      ∑ k ∈ Finset.range 8, qn k * Tot (n + k) := by
    simp only [Tot, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range 8)]
    exact Finset.sum_congr rfl (fun i _ => h i)
  simp only [c, sub_mul, Finset.sum_sub_distrib]
  have := congrArg (fun x : ℕ => (x : ℚ)) hs
  push_cast at this
  rw [this, sub_self]

def F (n : ℕ) : ℚ := (-288 + 507 * 2 ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6

theorem F_rec (n : ℕ) (_hn : 1 ≤ n) : ∑ k ∈ Finset.range 8, c k * F (n + k) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c, qp, qn, F]
  push_cast
  ring

theorem Tot_eq_V (n : ℕ) (hn : n ≤ 8) : Tot n = ∑ i, V n i := by
  simp only [Tot]
  exact Finset.sum_congr rfl (fun i _ => cnt_eq_V n hn i)

theorem Tot_small : ∀ n : Fin 8, (∑ i, V n.val i) = ![32, 99, 238, 534, 1152, 2426, 5028, 10306] n := by
  decide +kernel

theorem Tot_closed (n : ℕ) (hn : 1 ≤ n) : (Tot n : ℚ) = F n := by
  refine rec_solve 7 c (by norm_num [c, qp, qn]) (fun n => (Tot n : ℚ)) F Tot_rec F_rec ?_ n hn
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

theorem v1 : (a 1 : ℚ) = 99 := by rw [closed 1 (by norm_num)]; norm_num [F]
theorem v2 : (a 2 : ℚ) = 238 := by rw [closed 2 (by norm_num)]; norm_num [F]
theorem v3 : (a 3 : ℚ) = 534 := by rw [closed 3 (by norm_num)]; norm_num [F]
theorem v4 : (a 4 : ℚ) = 1152 := by rw [closed 4 (by norm_num)]; norm_num [F]
theorem v5 : (a 5 : ℚ) = 2426 := by rw [closed 5 (by norm_num)]; norm_num [F]
theorem v6 : (a 6 : ℚ) = 5028 := by rw [closed 6 (by norm_num)]; norm_num [F]

theorem part_rec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) + 2 * a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega]
  rw [show m + 6 - 2 = m + 4 by omega]
  rw [show m + 6 - 3 = m + 3 by omega]
  rw [show m + 6 - 4 = m + 2 by omega]
  rw [show m + 6 - 5 = m + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
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
  have hQ : ((1 - PowerSeries.X) ^ 4 * (1 - 2 * PowerSeries.X) : PowerSeries ℚ) = 1 - C 6 * X ^ 1 + C 14 * X ^ 2 - C 16 * X ^ 3 + C 9 * X ^ 4 - C 2 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hP : (PowerSeries.X * (99 - 356 * PowerSeries.X + 492 * PowerSeries.X ^ 2 - 304 * PowerSeries.X ^ 3 + 73 * PowerSeries.X ^ 4) : PowerSeries ℚ) = C 99 * X ^ 1 - C 356 * X ^ 2 + C 492 * X ^ 3 - C 304 * X ^ 4 + C 73 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hQ, hP, mul_comm]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, map_neg, neg_mul,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
  by_cases hn : n < 6
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [if_pos (show 1 ≤ m + 6 by omega), if_pos (show 2 ≤ m + 6 by omega), if_pos (show 3 ≤ m + 6 by omega), if_pos (show 4 ≤ m + 6 by omega), if_pos (show 5 ≤ m + 6 by omega), if_neg (show m + 6 - 0 ≠ 0 by omega), if_neg (show m + 6 - 1 ≠ 0 by omega), if_neg (show m + 6 - 2 ≠ 0 by omega), if_neg (show m + 6 - 3 ≠ 0 by omega), if_neg (show m + 6 - 4 ≠ 0 by omega), if_neg (show m + 6 - 5 ≠ 0 by omega), if_neg (show m + 6 ≠ 0 by omega), if_neg (show m + 6 ≠ 1 by omega), if_neg (show m + 6 ≠ 2 by omega), if_neg (show m + 6 ≠ 3 by omega), if_neg (show m + 6 ≠ 4 by omega), if_neg (show m + 6 ≠ 5 by omega)]
    rw [show m + 6 - 1 = m + 5 by omega]
    rw [show m + 6 - 2 = m + 4 by omega]
    rw [show m + 6 - 3 = m + 3 by omega]
    rw [show m + 6 - 4 = m + 2 by omega]
    rw [show m + 6 - 5 = m + 1 by omega]
    rw [closed (m + 6) (by omega)]
    rw [closed (m + 5) (by omega)]
    rw [closed (m + 4) (by omega)]
    rw [closed (m + 3) (by omega)]
    rw [closed (m + 2) (by omega)]
    rw [closed (m + 1) (by omega)]
    simp only [F]
    push_cast
    ring

theorem main_proof : (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) + 2 * a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-288 + 507 * 2 ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6) :=
  ⟨part_rec, part_gf, fun n hn => closed n hn⟩

end A250779Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a250779.main := A250779Proof.main_proof
