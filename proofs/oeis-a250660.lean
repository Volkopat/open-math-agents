import OMAStatements.S_oeis_a250660
import Mathlib

-- Proof of the conjectures in OEIS A250660 (statement by @ivillar).
-- Idea: the conditions only involve 2 X 2 blocks, so the count is a walk count on the columns of the
-- array (transfer matrix). The 128 states are lumped into 12 classes with constant numbers of successors in
-- each class (checked by decide), which gives a linear system for the class counts W n c. The recurrence
-- of order 3 follows from explicit row vectors orthogonal to all W n (an invariant subspace of the
-- transposed class matrix), and the generating function and closed forms follow from the recurrence
-- and the first values.

namespace OMAA250660Helpers

open OMA.S_oeis_a250660

instance (p q r s : ℕ) : Decidable (Blk p q r s) := by
  unfold Blk; infer_instance

/-- The states of the transfer matrix: the columns of the array, encoded as numbers in base 2
(digit j of the code is entry j). -/
abbrev R := Fin (2 ^ 7)

/-- Digit j of the code a in base 2. -/
def dig (a j : ℕ) : ℕ := a / 2 ^ j % 2

/-- Consecutive columns u, v: all the 2 X 2 blocks they form satisfy the condition. -/
abbrev BlockOK (u v : Fin 7 → Fin 2) : Prop :=
  ∀ i : Fin 6, Blk (u i.castSucc) (v i.castSucc) (u i.succ) (v i.succ)

/-- The truth table of `Blk` on entries below 2: bit ((p * 2 + q) * 2 + r) * 2 + s. -/
def blkTab : ℕ := 45867

/-- `Blk` read off the truth table. -/
def blkB (p q r s : ℕ) : Bool := Nat.testBit blkTab (((p * 2 + q) * 2 + r) * 2 + s)

theorem blk_iff : ∀ p q r s : Fin 2, blkB p q r s = true ↔ Blk p q r s := by decide +kernel

/-- The same condition on codes. -/
def compatB (r s : ℕ) : Bool :=
  blkB (dig r 0) (dig s 0) (dig r 1) (dig s 1) &&
    (blkB (dig r 1) (dig s 1) (dig r 2) (dig s 2) &&
    (blkB (dig r 2) (dig s 2) (dig r 3) (dig s 3) &&
    (blkB (dig r 3) (dig s 3) (dig r 4) (dig s 4) &&
    (blkB (dig r 4) (dig s 4) (dig r 5) (dig s 5) &&
    (blkB (dig r 5) (dig s 5) (dig r 6) (dig s 6))))))

abbrev compatN (r s : ℕ) : Prop := compatB r s = true

/-- States are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Every state may start a walk. -/
abbrev init (_r : R) : Prop := True

/-- Compatibility of consecutive states. -/
abbrev compat (r s : R) : Prop := compatN r.val s.val

theorem dig_enc (u : Fin 7 → Fin 2) (i : Fin 7) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val i.val = (u i).val :=
  congrArg Fin.val (congrFun (Equiv.symm_apply_apply (finFunctionFinEquiv (m := 2) (n := 7)) u) i)

theorem dig_e0 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 0 = (u 0).val := dig_enc u 0

theorem dig_e1 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 1 = (u 1).val := dig_enc u 1

theorem dig_e2 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 2 = (u 2).val := dig_enc u 2

theorem dig_e3 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 3 = (u 3).val := dig_enc u 3

theorem dig_e4 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 4 = (u 4).val := dig_enc u 4

theorem dig_e5 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 5 = (u 5).val := dig_enc u 5

theorem dig_e6 (u : Fin 7 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 7)) u).val 6 = (u 6).val := dig_enc u 6


theorem blockOK_iff (u v : Fin 7 → Fin 2) :
    BlockOK u v ↔
      (Blk (u 0) (v 0) (u 1) (v 1) ∧
      (Blk (u 1) (v 1) (u 2) (v 2) ∧
      (Blk (u 2) (v 2) (u 3) (v 3) ∧
      (Blk (u 3) (v 3) (u 4) (v 4) ∧
      (Blk (u 4) (v 4) (u 5) (v 5) ∧
      (Blk (u 5) (v 5) (u 6) (v 6))))))) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ j
    fin_cases j <;>
      first
        | exact h0
        | exact h1
        | exact h2
        | exact h3
        | exact h4
        | exact h5

theorem compat_enc (u v : Fin 7 → Fin 2) :
    compat ((finFunctionFinEquiv (m := 2) (n := 7)) u) ((finFunctionFinEquiv (m := 2) (n := 7)) v) ↔ BlockOK u v := by
  rw [blockOK_iff]
  simp only [compat, compatN, compatB, Bool.and_eq_true, dig_e0, dig_e1, dig_e2, dig_e3, dig_e4, dig_e5, dig_e6, blk_iff]

/-- Arrays as sequences of encoded columns. -/
def enc (n : ℕ) : (Fin 7 → Fin (n + 1) → Fin 2) ≃ (Fin (n + 1) → R) where
  toFun := fun x j => (finFunctionFinEquiv (m := 2) (n := 7)) (fun i => x i j)
  invFun := fun y i j => (finFunctionFinEquiv (m := 2) (n := 7)).symm (y j) i
  left_inv := fun x => by funext i j; exact congrFun (Equiv.symm_apply_apply _ _) i
  right_inv := fun y => by funext j; exact Equiv.apply_symm_apply _ _

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The classes of the states, one byte per state. -/
def clsTab : ℕ := 704988415032080595798814705394284095005710515433032868200352691139921301251990366971918711964906956806238422103945740113554642481958632700846209791413506529013673517598141783673118858483819014566482129640844054611806021065232310559607073477385532987071720403748744365463422814913649114321921828602794870528

/-- The class of a code (states of one class have the same numbers of successors in each class). -/
def clsF (a : ℕ) : Fin 12 := ⟨(clsTab >>> (8 * a)) % 256 % 12, Nat.mod_lt _ (by norm_num)⟩

/-- The class of a state. -/
def cls (t : R) : Fin 12 := clsF t.val

/-- The codes of the states of each class. -/
def mem : Fin 12 → List ℕ :=
  ![[0], [64, 66, 67, 68, 70, 71, 72, 74, 75, 76, 78, 79, 80, 82, 83, 84, 86, 87, 88, 90, 91, 92, 94, 95, 96, 98, 99, 100, 102, 103, 104, 106, 107, 108, 110, 111, 112, 114, 115, 116, 118, 119, 120, 122, 123, 124, 126, 127], [32, 34, 35, 36, 38, 39, 40, 42, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 58, 59, 60, 62, 63, 65, 69, 73, 77, 81, 85, 89, 93, 97, 101, 105, 109, 113, 117, 121, 125], [16, 18, 19, 20, 22, 23, 24, 26, 27, 28, 30, 31], [8, 10, 11, 12, 14, 15], [4, 6, 7], [2, 3], [1], [33, 37, 41, 45, 49, 53, 57, 61], [17, 21, 25, 29], [9, 13], [5]]

/-- Mat c d: the number of successors of class d of a state of class c. -/
def Mat : Fin 12 → Fin 12 → ℤ :=
  ![![1, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 7, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 3, 3, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 4, 4, 0, 0, 1, 0, 0, 0, 0, 0, 1]]

/-- W n c: the number of walks with n steps starting at a given state of class c. -/
def W : ℕ → Fin 12 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun c => ∑ d, Mat c d * W n d

theorem hmem : ∀ c : Fin 12, mem c = (List.range (2 ^ 7)).filter (fun a => clsF a = c) := by decide +kernel

theorem cntN_0 : ∀ s : R, 0 ≤ s.val → s.val < 31 → ∀ c : Fin 12,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_1 : ∀ s : R, 31 ≤ s.val → s.val < 62 → ∀ c : Fin 12,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_2 : ∀ s : R, 62 ≤ s.val → s.val < 93 → ∀ c : Fin 12,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_3 : ∀ s : R, 93 ≤ s.val → s.val < 124 → ∀ c : Fin 12,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_4 : ∀ s : R, 124 ≤ s.val → s.val < 2 ^ 7 → ∀ c : Fin 12,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN : ∀ s : R, ∀ c : Fin 12,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := fun s c =>
  if h2 : s.val < 62 then
    if h1 : s.val < 31 then
      cntN_0 s (Nat.zero_le _) h1 c
    else
      cntN_1 s (Nat.le_of_not_lt h1) h2 c
  else
    if h3 : s.val < 93 then
      cntN_2 s (Nat.le_of_not_lt h2) h3 c
    else
      if h4 : s.val < 124 then
        cntN_3 s (Nat.le_of_not_lt h3) h4 c
      else
        cntN_4 s (Nat.le_of_not_lt h4) s.isLt c

/-- U i: the row vector (class sizes) * Mat^i. -/
def U : Fin 5 → Fin 12 → ℤ :=
  ![![1, 48, 40, 12, 6, 3, 2, 1, 8, 4, 2, 1],
    ![2, 192, 79, 16, 8, 4, 2, 1, 8, 4, 2, 1],
    ![3, 400, 118, 20, 10, 5, 2, 1, 8, 4, 2, 1],
    ![4, 672, 157, 24, 12, 6, 2, 1, 8, 4, 2, 1],
    ![5, 1008, 196, 28, 14, 7, 2, 1, 8, 4, 2, 1]]

theorem totN : ∀ c : Fin 12, ((mem c).length : ℤ) = U 0 c := by decide +kernel

theorem card_cls (c : Fin 12) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).card = ((mem c).filter (fun a => P a)).length := by
  have key : (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).map Fin.valEmbedding =
      ((mem c).filter (fun a => P a)).toFinset := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    rw [hmem c]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨t.isLt, h1⟩, h2⟩
    · rintro ⟨⟨ha, hc⟩, h2⟩
      exact ⟨⟨a, ha⟩, ⟨hc, h2⟩, rfl⟩
  have hnd : (mem c).Nodup := by
    rw [hmem c]
    exact List.Nodup.filter _ (by first | exact List.nodup_range | exact List.nodup_range _)
  rw [← Finset.card_map Fin.valEmbedding, key, List.toFinset_card_of_nodup (hnd.filter _)]

theorem cnt : ∀ s : R, ∀ c : Fin 12,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card : ℤ) = Mat (cls s) c := by
  intro s c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t)) =
      Finset.univ.filter (fun t : R => cls t = c ∧ compatN s.val t.val) :=
    Finset.filter_congr (fun t _ => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩)
  rw [h2, card_cls c (fun a => compatN s.val a)]
  have h3 : (mem c).filter (fun a => decide (compatN s.val a)) = (mem c).filter (fun a => compatB s.val a) :=
    List.filter_congr (fun a _ => by simp only [compatN, Bool.decide_eq_true])
  first
    | (rw [h3]; exact cntN s c)
    | (simpa [compatN] using cntN s c)

theorem tot : ∀ c : Fin 12,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ init t)).card : ℤ) = U 0 c := by
  intro c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ init t) =
      Finset.univ.filter (fun t : R => cls t = c ∧ (fun _ : ℕ => True) t.val) :=
    Finset.filter_congr (fun t _ => Iff.rfl)
  rw [h2, card_cls c (fun _ : ℕ => True)]
  simpa using totN c

theorem hU : ∀ (i : Fin 4) (d : Fin 12), ∑ c, U i.castSucc c * Mat c d = U i.succ d := by
  decide +kernel

/-- Coefficients of the recurrence. -/
def L : Fin 5 → ℤ := ![-1, 3, -3, 1, 0]

/-- Row vectors orthogonal to all the vectors W n. -/
def Rm : Fin 1 → Fin 12 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def Am : Fin 1 → Fin 1 → ℤ :=
  ![![0]]

theorem hRA : ∀ (l : Fin 1) (d : Fin 12), ∑ c, Rm l c * Mat c d = ∑ l', Am l l' * Rm l' d := by
  decide +kernel

theorem hR0 : ∀ l : Fin 1, ∑ c, Rm l c = 0 := by decide +kernel

theorem hL : ∀ c : Fin 12, ∑ i, L i * U i c = Rm 0 c := by decide +kernel

/-- The first values. -/
def vals : Fin 5 → ℤ := ![128, 319, 574, 893, 1276]

theorem hV : ∀ i : Fin 5, ∑ c, U i c = vals i := by decide +kernel

theorem sum_cls (g : Fin 12 → ℤ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c : Fin 12, ((Finset.univ.filter (fun t => cls t = c ∧ P t)).card : ℤ) * g c := by
  rw [← Finset.sum_fiberwise Finset.univ cls]
  apply Finset.sum_congr rfl
  intro c _
  have h : ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g (cls t) else 0) =
      ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g c else 0) :=
    Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])
  rw [h, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]

theorem F_eq (n : ℕ) : ∀ s : R, (F n s : ℤ) = W n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    simp [W, ok]
  | succ n ih =>
    intro s
    rw [F_succ]
    push_cast
    simp only [ih]
    rw [sum_cls (W n) (fun t => ok s ∧ compat s t)]
    simp only [cnt]
    rfl

theorem swap_sum (f : Fin 12 → ℤ) (n : ℕ) :
    ∑ c, f c * W (n + 1) c = ∑ d, (∑ c, f c * Mat c d) * W n d := by
  have h : ∀ c, f c * W (n + 1) c = ∑ d, f c * Mat c d * W n d := by
    intro c
    show f c * ∑ d, Mat c d * W n d = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp only [h, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem W_inv : ∀ (n : ℕ) (l : Fin 1), ∑ c, Rm l c * W n c = 0 := by
  intro n
  induction n with
  | zero =>
    intro l
    simpa [W] using hR0 l
  | succ n ih =>
    intro l
    rw [swap_sum]
    simp only [hRA, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h : ∀ l', ∑ d, Am l l' * Rm l' d * W n d = Am l l' * ∑ d, Rm l' d * W n d := by
      intro l'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    simp only [h, ih, mul_zero, Finset.sum_const_zero]

theorem W_shift : ∀ (i : Fin 5) (n : ℕ), ∑ c, U 0 c * W (n + i) c = ∑ c, U i c * W n c := by
  intro i
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    have h1 : n + ((i.succ : Fin 5) : ℕ) = (n + 1) + ((i.castSucc : Fin 5) : ℕ) := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [h1, ih (n + 1), swap_sum]
    simp only [hU]

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ c, U 0 c * W n c := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (enc n)
      (p := fun x : Fin 7 → Fin (n + 1) → Fin 2 => ∀ i : Fin 6, ∀ j : Fin n,
        Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, fun j => (compat_enc _ _).mpr (fun i => h i j)⟩,
        fun h i j => (compat_enc _ _).mp (h.2 j) i⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if init s then F n s else 0 := by
    unfold F
    simp only [init, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  push_cast
  simp only [F_eq]
  rw [sum_cls (W n) init]
  simp only [tot]

theorem a_shift (i : Fin 5) (n : ℕ) : (a (n + i) : ℤ) = ∑ c, U i c * W n c := by
  rw [a_eq, W_shift]

theorem a_rec (n : ℕ) : ∑ i : Fin 5, L i * (a (n + i) : ℤ) = 0 := by
  simp only [a_shift, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c, ∑ i, L i * (U i c * W n c) = Rm 0 c * W n c := by
    intro c
    rw [← hL c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [h]
  exact W_inv n 0

theorem a_val (i : Fin 5) : (a i : ℤ) = vals i := by
  have h := a_shift i 0
  rw [Nat.zero_add] at h
  rw [h, ← hV i]
  apply Finset.sum_congr rfl
  intro c _
  simp [W]

theorem rec0 (n : ℕ) : (a (n + 3) : ℤ) = 3 * (a (n + 2) : ℤ) - 3 * (a (n + 1) : ℤ) + (a (n) : ℤ) := by
  have h := a_rec n
  simp [Fin.sum_univ_succ, L] at h
  linarith

theorem v0 : a 0 = 128 := by
  have h := a_val 0
  simp [vals] at h
  exact_mod_cast h

theorem v1 : a 1 = 319 := by
  have h := a_val 1
  simp [vals] at h
  exact_mod_cast h

theorem v2 : a 2 = 574 := by
  have h := a_val 2
  simp [vals] at h
  exact_mod_cast h

theorem v3 : a 3 = 893 := by
  have h := a_val 3
  simp [vals] at h
  exact_mod_cast h

theorem v4 : a 4 = 1276 := by
  have h := a_val 4
  simp [vals] at h
  exact_mod_cast h

theorem conj1 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 32 * (n : ℚ) ^ 2 + 159 * (n : ℚ) + 128 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n < 4
    · interval_cases n <;> norm_num [v1, v2, v3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have g0 := ih (k + 1) (by omega) (by omega)
      have g1 := ih (k + 2) (by omega) (by omega)
      have g2 := ih (k + 3) (by omega) (by omega)
      have hr : (a (k + 4) : ℚ) = 3 * (a (k + 3) : ℚ) - 3 * (a (k + 2) : ℚ) + (a (k + 1) : ℚ) := by exact_mod_cast rec0 (k + 1)
      rw [hr, g2, g1, g0]
      push_cast
      ring

theorem conj2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 3) =
      F' - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.X ^ 3 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (319 - 383 * PowerSeries.X + 128 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
      PowerSeries.C (319 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (383 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (128 : ℚ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [v0, v1, v2, v3]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have h1 : (a (j + 4) : ℚ) = 3 * (a (j + 3) : ℚ) - 3 * (a (j + 2) : ℚ) + (a (j + 1) : ℚ) := by exact_mod_cast rec0 (j + 1)
    simp
    linear_combination h1

theorem conj3 : ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega]
  have h1 : (a (k + 4) : ℤ) = 3 * (a (k + 3) : ℤ) - 3 * (a (k + 2) : ℤ) + (a (k + 1) : ℤ) := rec0 (k + 1)
  linear_combination h1

end OMAA250660Helpers

open OMA.S_oeis_a250660 OMAA250660Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250660.main :=
  ⟨conj1, conj2, conj3⟩
