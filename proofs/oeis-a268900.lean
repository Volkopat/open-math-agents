import OMAStatements.S_oeis_a268900

/-!
Proof of Barker's conjectures for A268900 by a transfer matrix over the rows: a row is one of the
3^4 = 81 maps Fin 4 → Fin 3, the pairs totalling two are counted per row (horizontal) and per
consecutive pair of rows (antidiagonal), and the counts of row sequences by total (0 or 1) satisfy
the recurrence on every starting row, by induction from computed tables.
-/

namespace OMA.S_oeis_a268900

open PowerSeries

section TMCore

/-- The total cost of a sequence of states: a cost per state and a cost per consecutive pair. -/
def pc {α : Type} (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (y : Fin (m + 1) → α) : ℕ :=
  (∑ i, h (y i)) + ∑ i : Fin m, d (y i.castSucc) (y i.succ)

theorem pc_cons {α : Type} (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (a : α) (z : Fin (m + 1) → α) :
    pc h d (m + 1) (Fin.cons a z) = h a + d a (z 0) + pc h d m z := by
  unfold pc
  rw [Fin.sum_univ_succ (f := fun i => h ((Fin.cons a z : Fin (m + 2) → α) i)),
    Fin.sum_univ_succ (f := fun i : Fin (m + 1) =>
      d ((Fin.cons a z : Fin (m + 2) → α) i.castSucc) ((Fin.cons a z : Fin (m + 2) → α) i.succ))]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]
  ring

/-- The number of sequences of m + 1 states starting at a with total cost c. -/
def cnt {α : Type} [Fintype α] [DecidableEq α] (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (a : α) (c : ℕ) :
    ℕ :=
  ∑ y : Fin (m + 1) → α, if y 0 = a ∧ pc h d m y = c then 1 else 0

theorem sum_cons_eq {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 2) → α) → ℕ) :
    ∑ y : Fin (m + 2) → α, f y = ∑ a : α, ∑ z : Fin (m + 1) → α, f (Fin.cons a z) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem cnt_zero {α : Type} [Fintype α] [DecidableEq α] (h : α → ℕ) (d : α → α → ℕ) (a : α) (c : ℕ) :
    cnt h d 0 a c = if h a = c then 1 else 0 := by
  unfold cnt pc
  rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem cnt_succ {α : Type} [Fintype α] [DecidableEq α] (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (a : α)
    (c : ℕ) : cnt h d (m + 1) a c =
      ∑ b : α, if h a + d a b ≤ c then cnt h d m b (c - (h a + d a b)) else 0 := by
  unfold cnt
  rw [sum_cons_eq]
  simp only [Fin.cons_zero, pc_cons]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp only [true_and]
  rw [← Finset.sum_fiberwise Finset.univ (fun z : Fin (m + 1) → α => z 0)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs with hc
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : z 0 = b
    · simp only [hz, true_and, if_true]
      congr 1
      apply propext
      omega
    · simp [hz]
  · apply Finset.sum_eq_zero
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [hz.2]
    simp only [ite_eq_right_iff]
    omega

theorem cnt_succ0 {α : Type} [Fintype α] [DecidableEq α] (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (a : α) :
    cnt h d (m + 1) a 0 = ∑ b : α, if h a + d a b = 0 then cnt h d m b 0 else 0 := by
  rw [cnt_succ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : h a + d a b = 0
  · rw [if_pos (by omega), if_pos hb, hb]
  · rw [if_neg (by omega), if_neg hb]

theorem cnt_succ1 {α : Type} [Fintype α] [DecidableEq α] (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (a : α) :
    cnt h d (m + 1) a 1 = ∑ b : α, ((if h a + d a b = 0 then cnt h d m b 1 else 0) +
      (if h a + d a b = 1 then cnt h d m b 0 else 0)) := by
  rw [cnt_succ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rcases Nat.lt_trichotomy (h a + d a b) 1 with hb | hb | hb
  · have : h a + d a b = 0 := by omega
    rw [if_pos (by omega), if_pos this, if_neg (by omega), this]
    simp
  · rw [if_pos (by omega), if_neg (by omega), if_pos hb, hb]
    simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Sequences of states by total cost: the sum over the first state. -/
theorem card_pc {α : Type} [Fintype α] [DecidableEq α] (h : α → ℕ) (d : α → α → ℕ) (m : ℕ) (c : ℕ) :
    (Finset.univ.filter fun y : Fin (m + 1) → α => pc h d m y = c).card = ∑ a : α, cnt h d m a c := by
  rw [Finset.card_filter]
  unfold cnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (y 0) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- Reindexing the states along an equivalence. -/
theorem card_reindex {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (m : ℕ)
    (P : (Fin (m + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun y : Fin (m + 1) → β => P (fun i => e.symm (y i))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  rw [← (Equiv.arrowCongr (Equiv.refl (Fin (m + 1))) e).symm.sum_comp]
  rfl

end TMCore

/-- The horizontal pairs of a row totalling two. -/
def hr (r : Fin 4 → Fin 3) : ℕ :=
  (Finset.univ.filter fun j : Fin 3 => (r j.castSucc : ℕ) + (r j.succ : ℕ) = 2).card

/-- The antidiagonal pairs of two consecutive rows totalling two. -/
def dr (r s : Fin 4 → Fin 3) : ℕ :=
  (Finset.univ.filter fun j : Fin 3 => (r j.succ : ℕ) + (s j.castSucc : ℕ) = 2).card

theorem pairs_eq (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 3) : pairsTotallingTwo m x = pc hr dr m x := by
  unfold pairsTotallingTwo pc hr dr
  simp only [Finset.card_filter, Fintype.sum_prod_type]

/-- The number of rows. -/
abbrev K : ℕ := 3 ^ 4

/-- Rows as numbers in base 3. -/
def E : (Fin 4 → Fin 3) ≃ Fin K := finFunctionFinEquiv

/-- The costs on row codes. -/
def h' (a : Fin K) : ℕ := hr (E.symm a)

/-- The costs on pairs of row codes. -/
def d' (a b : Fin K) : ℕ := dr (E.symm a) (E.symm b)

theorem a_succ (m : ℕ) : a (m + 1) = ∑ s : Fin K, cnt h' d' m s 1 := by
  show (Finset.univ.filter fun x : Fin (m + 1) → Fin 4 → Fin 3 => pairsTotallingTwo m x = 1).card = _
  simp only [pairs_eq]
  rw [card_reindex E, ← card_pc]
  rfl

/-- A table lookup. -/
def lk (t : List (ℕ × ℕ)) (s : Fin K) : (ℕ × ℕ) := t.getD s (0, 0)

/-- The counts from every state after 0 steps. -/
def t0 : List (ℕ × ℕ) :=
  [(1, 0), (1, 0), (0, 1), (1, 0), (0, 1), (1, 0), (0, 0), (0, 1), (0, 1), (1, 0), (1, 0), (0, 1), (0, 1), (0, 0), (0, 1), (0, 1), (1, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 0), (0, 1), (0, 0), (0, 1), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (0, 1), (1, 0), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 0), (1, 0), (0, 1), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (0, 1), (0, 0), (0, 1), (0, 0), (0, 1), (0, 0), (0, 0), (0, 0), (1, 0), (1, 0), (0, 1), (0, 1), (0, 0), (0, 1), (0, 1), (1, 0), (1, 0), (0, 1), (0, 1), (0, 0), (1, 0), (0, 1), (1, 0), (0, 1), (1, 0), (1, 0)]

/-- The counts from every state after 1 steps. -/
def t1 : List (ℕ × ℕ) :=
  [(10, 15), (10, 15), (0, 10), (8, 22), (0, 8), (8, 22), (0, 0), (0, 6), (0, 6), (10, 15), (10, 15), (0, 10), (0, 6), (0, 0), (0, 6), (0, 8), (8, 22), (8, 22), (0, 0), (0, 0), (0, 0), (0, 6), (0, 0), (0, 6), (0, 0), (0, 6), (0, 6), (8, 22), (8, 22), (0, 8), (10, 15), (0, 10), (10, 15), (0, 0), (0, 6), (0, 6), (0, 6), (0, 6), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 6), (0, 6), (0, 6), (0, 6), (0, 0), (10, 15), (0, 10), (10, 15), (0, 8), (8, 22), (8, 22), (0, 6), (0, 6), (0, 0), (0, 6), (0, 0), (0, 6), (0, 0), (0, 0), (0, 0), (8, 22), (8, 22), (0, 8), (0, 6), (0, 0), (0, 6), (0, 10), (10, 15), (10, 15), (0, 6), (0, 6), (0, 0), (8, 22), (0, 8), (8, 22), (0, 10), (10, 15), (10, 15)]

/-- The counts from every state after 2 steps. -/
def t2 : List (ℕ × ℕ) :=
  [(90, 299), (90, 299), (0, 90), (72, 322), (0, 72), (72, 322), (0, 0), (0, 54), (0, 54), (90, 299), (90, 299), (0, 90), (0, 54), (0, 0), (0, 54), (0, 72), (72, 322), (72, 322), (0, 0), (0, 0), (0, 0), (0, 54), (0, 0), (0, 54), (0, 0), (0, 54), (0, 54), (72, 322), (72, 322), (0, 72), (90, 299), (0, 90), (90, 299), (0, 0), (0, 54), (0, 54), (0, 54), (0, 54), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 54), (0, 54), (0, 54), (0, 54), (0, 0), (90, 299), (0, 90), (90, 299), (0, 72), (72, 322), (72, 322), (0, 54), (0, 54), (0, 0), (0, 54), (0, 0), (0, 54), (0, 0), (0, 0), (0, 0), (72, 322), (72, 322), (0, 72), (0, 54), (0, 0), (0, 54), (0, 90), (90, 299), (90, 299), (0, 54), (0, 54), (0, 0), (72, 322), (0, 72), (72, 322), (0, 90), (90, 299), (90, 299)]

/-- The counts from every state after 3 steps. -/
def t3 : List (ℕ × ℕ) :=
  [(810, 4131), (810, 4131), (0, 810), (648, 4050), (0, 648), (648, 4050), (0, 0), (0, 486), (0, 486), (810, 4131), (810, 4131), (0, 810), (0, 486), (0, 0), (0, 486), (0, 648), (648, 4050), (648, 4050), (0, 0), (0, 0), (0, 0), (0, 486), (0, 0), (0, 486), (0, 0), (0, 486), (0, 486), (648, 4050), (648, 4050), (0, 648), (810, 4131), (0, 810), (810, 4131), (0, 0), (0, 486), (0, 486), (0, 486), (0, 486), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 486), (0, 486), (0, 486), (0, 486), (0, 0), (810, 4131), (0, 810), (810, 4131), (0, 648), (648, 4050), (648, 4050), (0, 486), (0, 486), (0, 0), (0, 486), (0, 0), (0, 486), (0, 0), (0, 0), (0, 0), (648, 4050), (648, 4050), (0, 648), (0, 486), (0, 0), (0, 486), (0, 810), (810, 4131), (810, 4131), (0, 486), (0, 486), (0, 0), (648, 4050), (0, 648), (648, 4050), (0, 810), (810, 4131), (810, 4131)]

/-- The counts from every state after 4 steps. -/
def t4 : List (ℕ × ℕ) :=
  [(7290, 50139), (7290, 50139), (0, 7290), (5832, 46818), (0, 5832), (5832, 46818), (0, 0), (0, 4374), (0, 4374), (7290, 50139), (7290, 50139), (0, 7290), (0, 4374), (0, 0), (0, 4374), (0, 5832), (5832, 46818), (5832, 46818), (0, 0), (0, 0), (0, 0), (0, 4374), (0, 0), (0, 4374), (0, 0), (0, 4374), (0, 4374), (5832, 46818), (5832, 46818), (0, 5832), (7290, 50139), (0, 7290), (7290, 50139), (0, 0), (0, 4374), (0, 4374), (0, 4374), (0, 4374), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 4374), (0, 4374), (0, 4374), (0, 4374), (0, 0), (7290, 50139), (0, 7290), (7290, 50139), (0, 5832), (5832, 46818), (5832, 46818), (0, 4374), (0, 4374), (0, 0), (0, 4374), (0, 0), (0, 4374), (0, 0), (0, 0), (0, 0), (5832, 46818), (5832, 46818), (0, 5832), (0, 4374), (0, 0), (0, 4374), (0, 7290), (7290, 50139), (7290, 50139), (0, 4374), (0, 4374), (0, 0), (5832, 46818), (0, 5832), (5832, 46818), (0, 7290), (7290, 50139), (7290, 50139)]

/-- The counts from every state after 5 steps. -/
def t5 : List (ℕ × ℕ) :=
  [(65610, 567891), (65610, 567891), (0, 65610), (52488, 514674), (0, 52488), (52488, 514674), (0, 0), (0, 39366), (0, 39366), (65610, 567891), (65610, 567891), (0, 65610), (0, 39366), (0, 0), (0, 39366), (0, 52488), (52488, 514674), (52488, 514674), (0, 0), (0, 0), (0, 0), (0, 39366), (0, 0), (0, 39366), (0, 0), (0, 39366), (0, 39366), (52488, 514674), (52488, 514674), (0, 52488), (65610, 567891), (0, 65610), (65610, 567891), (0, 0), (0, 39366), (0, 39366), (0, 39366), (0, 39366), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 39366), (0, 39366), (0, 39366), (0, 39366), (0, 0), (65610, 567891), (0, 65610), (65610, 567891), (0, 52488), (52488, 514674), (52488, 514674), (0, 39366), (0, 39366), (0, 0), (0, 39366), (0, 0), (0, 39366), (0, 0), (0, 0), (0, 0), (52488, 514674), (52488, 514674), (0, 52488), (0, 39366), (0, 0), (0, 39366), (0, 65610), (65610, 567891), (65610, 567891), (0, 39366), (0, 39366), (0, 0), (52488, 514674), (0, 52488), (52488, 514674), (0, 65610), (65610, 567891), (65610, 567891)]

/-- The counts from every state after 6 steps. -/
def t6 : List (ℕ × ℕ) :=
  [(590490, 6160779), (590490, 6160779), (0, 590490), (472392, 5471874), (0, 472392), (472392, 5471874), (0, 0), (0, 354294), (0, 354294), (590490, 6160779), (590490, 6160779), (0, 590490), (0, 354294), (0, 0), (0, 354294), (0, 472392), (472392, 5471874), (472392, 5471874), (0, 0), (0, 0), (0, 0), (0, 354294), (0, 0), (0, 354294), (0, 0), (0, 354294), (0, 354294), (472392, 5471874), (472392, 5471874), (0, 472392), (590490, 6160779), (0, 590490), (590490, 6160779), (0, 0), (0, 354294), (0, 354294), (0, 354294), (0, 354294), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 354294), (0, 354294), (0, 354294), (0, 354294), (0, 0), (590490, 6160779), (0, 590490), (590490, 6160779), (0, 472392), (472392, 5471874), (472392, 5471874), (0, 354294), (0, 354294), (0, 0), (0, 354294), (0, 0), (0, 354294), (0, 0), (0, 0), (0, 0), (472392, 5471874), (472392, 5471874), (0, 472392), (0, 354294), (0, 0), (0, 354294), (0, 590490), (590490, 6160779), (590490, 6160779), (0, 354294), (0, 354294), (0, 0), (472392, 5471874), (0, 472392), (472392, 5471874), (0, 590490), (590490, 6160779), (590490, 6160779)]

lemma V0_0 (s : Fin K) : cnt h' d' 0 s 0 = (lk t0 s).1 := by
  rw [cnt_zero]
  revert s
  decide +kernel

lemma V0_1 (s : Fin K) : cnt h' d' 0 s 1 = (lk t0 s).2 := by
  rw [cnt_zero]
  revert s
  decide +kernel

lemma V1_0 (s : Fin K) : cnt h' d' 1 s 0 = (lk t1 s).1 := by
  rw [cnt_succ0]
  simp only [V0_0]
  revert s
  decide +kernel

lemma V1_1 (s : Fin K) : cnt h' d' 1 s 1 = (lk t1 s).2 := by
  rw [cnt_succ1]
  simp only [V0_0, V0_1]
  revert s
  decide +kernel

lemma V2_0 (s : Fin K) : cnt h' d' 2 s 0 = (lk t2 s).1 := by
  rw [cnt_succ0]
  simp only [V1_0]
  revert s
  decide +kernel

lemma V2_1 (s : Fin K) : cnt h' d' 2 s 1 = (lk t2 s).2 := by
  rw [cnt_succ1]
  simp only [V1_0, V1_1]
  revert s
  decide +kernel

lemma V3_0 (s : Fin K) : cnt h' d' 3 s 0 = (lk t3 s).1 := by
  rw [cnt_succ0]
  simp only [V2_0]
  revert s
  decide +kernel

lemma V3_1 (s : Fin K) : cnt h' d' 3 s 1 = (lk t3 s).2 := by
  rw [cnt_succ1]
  simp only [V2_0, V2_1]
  revert s
  decide +kernel

lemma V4_0 (s : Fin K) : cnt h' d' 4 s 0 = (lk t4 s).1 := by
  rw [cnt_succ0]
  simp only [V3_0]
  revert s
  decide +kernel

lemma V4_1 (s : Fin K) : cnt h' d' 4 s 1 = (lk t4 s).2 := by
  rw [cnt_succ1]
  simp only [V3_0, V3_1]
  revert s
  decide +kernel

lemma V5_0 (s : Fin K) : cnt h' d' 5 s 0 = (lk t5 s).1 := by
  rw [cnt_succ0]
  simp only [V4_0]
  revert s
  decide +kernel

lemma V5_1 (s : Fin K) : cnt h' d' 5 s 1 = (lk t5 s).2 := by
  rw [cnt_succ1]
  simp only [V4_0, V4_1]
  revert s
  decide +kernel

lemma V6_0 (s : Fin K) : cnt h' d' 6 s 0 = (lk t6 s).1 := by
  rw [cnt_succ0]
  simp only [V5_0]
  revert s
  decide +kernel

lemma V6_1 (s : Fin K) : cnt h' d' 6 s 1 = (lk t6 s).2 := by
  rw [cnt_succ1]
  simp only [V5_0, V5_1]
  revert s
  decide +kernel

/-- The recurrence on every state. -/
theorem rec_state (m : ℕ) (s : Fin K) :
      (cnt h' d' (m + 4) s 0 : ℤ) = 18 * (cnt h' d' (m + 3) s 0 : ℤ) - 81 * (cnt h' d' (m + 2) s 0 : ℤ) ∧
      (cnt h' d' (m + 4) s 1 : ℤ) = 18 * (cnt h' d' (m + 3) s 1 : ℤ) - 81 * (cnt h' d' (m + 2) s 1 : ℤ) := by
  induction m generalizing s with
  | zero =>
    simp only [Nat.zero_add, V2_0, V2_1, V3_0, V3_1, V4_0, V4_1]
    revert s
    decide +kernel
  | succ m ih =>
    rw [show m + 1 + 4 = m + 4 + 1 by omega, show m + 1 + 3 = m + 3 + 1 by omega, show m + 1 + 2 = m + 2 + 1 by omega]
    refine ⟨?_, ?_⟩
    · rw [cnt_succ0 h' d' (m + 4) s, cnt_succ0 h' d' (m + 3) s, cnt_succ0 h' d' (m + 2) s]
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs
      · exact (ih b).1
      · simp
    · rw [cnt_succ1 h' d' (m + 4) s, cnt_succ1 h' d' (m + 3) s, cnt_succ1 h' d' (m + 2) s]
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      have h0 := (ih b).1
      have h1 := (ih b).2
      split_ifs <;> linarith

lemma values : a 1 = 36 ∧ a 2 = 696 ∧ a 3 = 9720 ∧ a 4 = 118584 ∧ a 5 = 1347192 := by
  simp only [a_succ, V0_1, V1_1, V2_1, V3_1, V4_1]
  decide +kernel

theorem recurrence (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 18 * a (n - 1) - 81 * a (n - 2) := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := values
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    simp only [show 4 - 1 = 3 from rfl, show 4 - 2 = 2 from rfl, v4, v3, v2]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = (m + 3) + 1 by omega, show m + 5 - 2 = (m + 2) + 1 by omega,
      show m + 5 = (m + 4) + 1 by omega, a_succ, a_succ, a_succ]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    exact (rec_state m s).2

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 9 * X) ^ 2 = 12 * X * (3 + 4 * X + 9 * X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (1 - 9 * X) ^ 2 = A - C 18 * (A * X ^ 1) + C 81 * (A * X ^ 2) := by
    simp only [map_ofNat]; ring
  have e2 : (12 * X * (3 + 4 * X + 9 * X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C 36 + X ^ 2 * C 48 + X ^ 3 * C 108 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (a k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  obtain ⟨v1, v2, v3, v4, v5⟩ := values
  have v0 : a 0 = 0 := rfl
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3] <;> norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
    have h := recurrence (q + 4) (by omega)
    simp only [show q + 4 - 1 = q + 3 by omega, show q + 4 - 2 = q + 2 by omega] at h
    have h' : (a (q + 4) : ℚ) = 18 * a (q + 3) - 81 * a (q + 2) := by exact_mod_cast h
    simp only [show 1 ≤ q + 4 by omega, show 2 ≤ q + 4 by omega, show q + 4 - 1 = q + 3 by omega,
      show q + 4 - 2 = q + 2 by omega, show ¬ q + 4 = 1 by omega, show ¬ q + 4 = 2 by omega,
      show ¬ q + 4 = 3 by omega, if_true, if_false]
    rw [h']
    ring

theorem closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 8 * 3 ^ (2 * n - 3) * (16 * n - 3) := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := values
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · rw [v2]; norm_num
      · rw [v3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have h := recurrence (k + 4) (by omega)
      simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega] at h
      have h' : (a (k + 4) : ℚ) = 18 * a (k + 3) - 81 * a (k + 2) := by exact_mod_cast h
      rw [h', ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega)]
      rw [show 2 * (k + 4) - 3 = (2 * k + 1) + 4 by omega, show 2 * (k + 3) - 3 = (2 * k + 1) + 2 by omega,
        show 2 * (k + 2) - 3 = 2 * k + 1 by omega]
      push_cast
      ring

theorem conjecture :
    (∀ n : ℕ, 4 ≤ n →
      (a n : ℤ) = 18 * a (n - 1) - 81 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 9 * X) ^ 2 =
      12 * X * (3 + 4 * X + 9 * X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 8 * 3 ^ (2 * n - 3) * (16 * n - 3)) :=
  ⟨recurrence, gf, closed⟩

end OMA.S_oeis_a268900

theorem OMA.solution : type_of% @OMA.S_oeis_a268900.main :=
  OMA.S_oeis_a268900.conjecture
