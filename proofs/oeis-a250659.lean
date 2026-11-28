import OMAStatements.S_oeis_a250659
import Mathlib

-- Proof of the conjectures in OEIS A250659 (statement by @ivillar).
-- Idea: the conditions involve only consecutive columns, so the count is a walk count on the
-- 64 possible columns (transfer matrix). The states fall into 10 classes such that the number of successors
-- of a state in each class depends only on its own class (checked by a kernel computation, with the
-- class counts of each state packed into one base-128 number). The class-count vectors V(0), V(1), ...
-- then satisfy a linear recurrence with a 11 X 11 matrix, whose first iterates are computed
-- explicitly; they satisfy the conjectured recurrence, and so do all later ones by linearity.
-- The g.f. and the closed form follow from the recurrence and the first values.

namespace OMAA250659Helpers

open OMA.S_oeis_a250659

abbrev R := Fin 6 → Fin 2

instance (p q r s : ℤ) : Decidable (CellOK p q r s) := by unfold CellOK; infer_instance

/-- No constraint on a single state. -/
def RowOK (_r : R) : Prop := True

instance : DecidablePred RowOK := fun r => by unfold RowOK; infer_instance

/-- Consecutive columns u, v: all the subblocks they form satisfy the condition. -/
def Compat (u v : R) : Prop := ∀ i : Fin 5, CellOK ((u i.castSucc : ℕ) : ℤ) ((v i.castSucc : ℕ) : ℤ) ((u i.succ : ℕ) : ℤ) ((v i.succ : ℕ) : ℤ)

instance (u v : R) : Decidable (Compat u v) := by unfold Compat; infer_instance

/-- No constraint on the first state. -/
def Init (_r : R) : Prop := True

instance : DecidablePred Init := fun r => by unfold Init; infer_instance

abbrev ok (r : R) : Prop := RowOK r

abbrev compat (r s : R) : Prop := Compat r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

/-- Number of walks with n+1 states starting at s. -/
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

/-- Decoding of a state from its index (base 2 digits). -/
def dec (i : ℕ) : R := fun k => ⟨i / 2 ^ (k : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Index of a state. -/
def enc (r : R) : ℕ := (r 0 : ℕ) + 2 * ((r 1 : ℕ) + 2 * ((r 2 : ℕ) + 2 * ((r 3 : ℕ) + 2 * ((r 4 : ℕ) + 2 * ((r 5 : ℕ))))))

theorem dec_enc : ∀ r : R, dec (enc r) = r := by decide +kernel

theorem enc_lt : ∀ r : R, enc r < 64 := by decide +kernel

theorem enc_dec : ∀ i < 64, enc (dec i) = i := by decide +kernel

theorem sum_R (g : R → ℕ) : ∑ t : R, g t = ∑ i ∈ Finset.range 64, g (dec i) := by
  refine Finset.sum_nbij' (fun t => enc t) (fun i => dec i) ?_ ?_ ?_ ?_ ?_
  · intro t _; exact Finset.mem_range.mpr (enc_lt t)
  · intro i _; exact Finset.mem_univ _
  · intro t _; exact dec_enc t
  · intro i hi; exact enc_dec i (Finset.mem_range.mp hi)
  · intro t _; rw [dec_enc]

/-- Class of the state with index i (a table in base 16): states of one class have the same numbers
of successors in every class. -/
def clsN (i : ℕ) : ℕ := 69418713573585351369446561837282966531535322709389016026529199742100607017488 / 16 ^ i % 16

def cls (r : R) : ℕ := clsN (enc r)

/-- Class transition counts; the last row (index 10) counts the admissible first states by class. -/
def MXL : List (List ℕ) := [[1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0],
  [1, 1, 0, 0, 0, 0, 0, 4, 0, 6, 0],
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0],
  [0, 0, 0, 1, 1, 0, 0, 3, 0, 3, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0],
  [0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 1, 2, 3, 1, 6, 2, 20, 4, 24, 0]]

def MX (k j : ℕ) : ℕ := (MXL.getD k []).getD j 0

theorem MX_lt : ∀ k < 11, ∀ j < 11, MX k j < 128 := by decide +kernel

theorem clsN_lt : ∀ i < 64, clsN i < 10 := by decide +kernel

theorem cls_lt (r : R) : cls r < 11 := by
  have := clsN_lt (enc r) (enc_lt r)
  unfold cls
  omega

/-- The successor classes of every state, encoded in base 128. -/
theorem hashS : ∀ i < 64,
    (∑ t ∈ Finset.range 64, if ok (dec i) ∧ compat (dec i) (dec t) then 128 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 11, MX (clsN i) j * 128 ^ j := by decide +kernel

theorem hashI :
    (∑ t ∈ Finset.range 64, if Init (dec t) then 128 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 11, MX 10 j * 128 ^ j := by decide +kernel

theorem digits_unique (B : ℕ) (hB : 0 < B) : ∀ (c : ℕ) (n m : ℕ → ℕ), (∀ j < c, n j < B) →
    (∀ j < c, m j < B) →
    ∑ j ∈ Finset.range c, n j * B ^ j = ∑ j ∈ Finset.range c, m j * B ^ j → ∀ j < c, n j = m j := by
  intro c
  induction c with
  | zero => intro n m _ _ _ j hj; omega
  | succ c ih =>
    intro n m hn hm h j hj
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one, pow_succ] at h
    have e1 : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range c, f (k + 1) * (B ^ k * B) =
        B * ∑ k ∈ Finset.range c, f (k + 1) * B ^ k := by
      intro f
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e1 n, e1 m] at h
    have h0 : n 0 = m 0 := by
      have h' := congrArg (fun z => z % B) h
      simp only [Nat.mul_add_mod] at h'
      rwa [Nat.mod_eq_of_lt (hn 0 (by omega)), Nat.mod_eq_of_lt (hm 0 (by omega))] at h'
    have h1 : ∑ k ∈ Finset.range c, n (k + 1) * B ^ k = ∑ k ∈ Finset.range c, m (k + 1) * B ^ k := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hB (Nat.add_right_cancel h)
    rcases j with _ | j
    · exact h0
    · exact ih (fun k => n (k + 1)) (fun k => m (k + 1)) (fun k hk => hn (k + 1) (by omega))
        (fun k hk => hm (k + 1) (by omega)) h1 j (by omega)

theorem sum_cls (P : R → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (∑ t : R, if P t then f (cls t) else 0) =
      ∑ j ∈ Finset.range 11, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * f j := by
  have h : ∀ j, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * f j =
      ∑ t : R, if P t ∧ cls t = j then f j else 0 := by
    intro j
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hP : P t
  · simp only [hP, true_and, if_true]
    rw [Finset.sum_ite_eq (Finset.range 11) (cls t) f, if_pos (Finset.mem_range.mpr (cls_lt t))]
  · simp [hP]

theorem card_lt (P : R → Prop) [DecidablePred P] : (Finset.univ.filter P).card < 128 := by
  have h1 : (Finset.univ.filter P).card ≤ (Finset.univ : Finset R).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset R).card = 64 := by
    rw [Finset.card_eq_sum_ones, sum_R]
    simp
  omega

/-- From the base 128 encoding to the class counts. -/
theorem counts_of_hash (P : R → Prop) [DecidablePred P] (k : ℕ)
    (h : (∑ t ∈ Finset.range 64, if P (dec t) then 128 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 11, MX k j * 128 ^ j)
    (hk : ∀ j < 11, MX k j < 128) :
    ∀ j < 11, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card = MX k j := by
  have e : (∑ t : R, if P t then 128 ^ cls t else 0) =
      ∑ j ∈ Finset.range 11, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * 128 ^ j :=
    sum_cls P (fun j => 128 ^ j)
  refine digits_unique 128 (by norm_num) 11
    (fun j => (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card) (fun j => MX k j)
    (fun j _ => card_lt _) hk ?_
  rw [← e, sum_R, ← h]
  apply Finset.sum_congr rfl
  intro t ht
  unfold cls
  rw [enc_dec t (Finset.mem_range.mp ht)]

/-- Initial class vector. -/
def L0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]

/-- Walk counts by class; coordinate 10 at time n+1 is the number of admissible walks with n+1 states. -/
def V : ℕ → ℕ → ℕ
  | 0, j => L0.getD j 0
  | n + 1, i => ∑ j ∈ Finset.range 11, MX i j * V n j

theorem V_succ (n i : ℕ) : V (n + 1) i = ∑ j ∈ Finset.range 11, MX i j * V n j := rfl

theorem base_ok : ∀ i < 64, (if ok (dec i) then 1 else 0) = L0.getD (clsN i) 0 := by decide +kernel

theorem hashS' (s : R) :
    (∑ t ∈ Finset.range 64, if ok s ∧ compat s (dec t) then 128 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 11, MX (cls s) j * 128 ^ j := by
  have h := hashS (enc s) (enc_lt s)
  rw [dec_enc] at h
  exact h

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    have h := base_ok (enc s) (enc_lt s)
    rw [dec_enc] at h
    exact h
  | succ n ih =>
    intro s
    rw [F_succ, V_succ]
    simp only [ih]
    rw [sum_cls (fun t => ok s ∧ compat s t) (V n)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [counts_of_hash (fun t => ok s ∧ compat s t) (cls s) (hashS' s) (MX_lt _ (cls_lt s)) j
      (Finset.mem_range.mp hj)]

theorem count_walks (n : ℕ) :
    Nat.card {y : Fin (n + 1) → R // Walk y ∧ Init (y 0)} = V (n + 1) 10 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ Init (x 0) then 1 else 0) =
      ∑ s : R, if Init s then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if Init s then
        (∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0) else 0) =
        ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ Init (y 0) then 1 else 0) else 0 := by
      intro s
      by_cases hs : Init s
      · rw [if_pos hs]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy
          rw [if_pos rfl]
          exact if_congr ⟨fun h => ⟨h.1, hs⟩, fun h => ⟨h.1, rfl⟩⟩ rfl rfl
        · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = s) from fun h => hy h.2)]
      · rw [if_neg hs]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy
          rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F_eq]
  rw [sum_cls Init (V n), V_succ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [counts_of_hash Init 10 hashI (MX_lt _ (by norm_num)) j (Finset.mem_range.mp hj)]

theorem V_step (n : ℕ) (L L' : List ℕ) (h : ∀ j < 11, V n j = L.getD j 0)
    (h' : ∀ i < 11, ∑ j ∈ Finset.range 11, MX i j * L.getD j 0 = L'.getD i 0) :
    ∀ i < 11, V (n + 1) i = L'.getD i 0 := by
  intro i hi
  rw [V_succ, ← h' i hi]
  exact Finset.sum_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])

theorem lit0 : ∀ j < 11, V 0 j = L0.getD j 0 := fun _ _ => rfl

def L1 : List ℕ := [7, 12, 5, 4, 8, 3, 6, 2, 4, 1, 64]
theorem lit1 : ∀ i < 11, V 1 i = L1.getD i 0 := V_step 0 L0 L1 lit0 (by decide +kernel)
def L2 : List ℕ := [13, 33, 9, 7, 21, 5, 15, 3, 9, 1, 159]
theorem lit2 : ∀ i < 11, V 2 i = L2.getD i 0 := V_step 1 L1 L2 lit1 (by decide +kernel)
def L3 : List ℕ := [19, 64, 13, 10, 40, 7, 28, 4, 16, 1, 286]
theorem lit3 : ∀ i < 11, V 3 i = L3.getD i 0 := V_step 2 L2 L3 lit2 (by decide +kernel)
def L4 : List ℕ := [25, 105, 17, 13, 65, 9, 45, 5, 25, 1, 445]
theorem lit4 : ∀ i < 11, V 4 i = L4.getD i 0 := V_step 3 L3 L4 lit3 (by decide +kernel)
def L5 : List ℕ := [31, 156, 21, 16, 96, 11, 66, 6, 36, 1, 636]
theorem lit5 : ∀ i < 11, V 5 i = L5.getD i 0 := V_step 4 L4 L5 lit4 (by decide +kernel)
def L6 : List ℕ := [37, 217, 25, 19, 133, 13, 91, 7, 49, 1, 859]
theorem lit6 : ∀ i < 11, V 6 i = L6.getD i 0 := V_step 5 L5 L6 lit5 (by decide +kernel)

theorem vbase : ∀ i < 11, ((L4.getD i 0 : ℕ) : ℤ) = (1 : ℤ) * ((L1.getD i 0 : ℕ) : ℤ) + (-3 : ℤ) * ((L2.getD i 0 : ℕ) : ℤ) + (3 : ℤ) * ((L3.getD i 0 : ℕ) : ℤ) := by decide +kernel

/-- The recurrence holds for the whole class vector (by linearity of the transfer step). -/
theorem vrec : ∀ n : ℕ, ∀ i < 11, (V (n + 4) i : ℤ) = (1 : ℤ) * (V (n + 1) i : ℤ) + (-3 : ℤ) * (V (n + 2) i : ℤ) + (3 : ℤ) * (V (n + 3) i : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    simp only [Nat.zero_add]
    rw [lit4 i hi, lit1 i hi, lit2 i hi, lit3 i hi]
    exact vbase i hi
  | succ n ih =>
    intro i hi
    have e : ∀ m, (V (n + 1 + m) i : ℤ) = ∑ j ∈ Finset.range 11, (MX i j : ℤ) * (V (n + m) j : ℤ) := by
      intro m
      rw [show n + 1 + m = (n + m) + 1 by omega, V_succ]
      push_cast
      rfl
    simp only [e, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_range.mp hj)]
    ring

theorem a_eq (n : ℕ) : a n = V (n + 1) 10 := by
  unfold a
  rw [← count_walks]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.piComm (fun _ _ => Fin 2))
    (fun x => ⟨fun h => ⟨⟨fun _ => trivial, fun j i => h i j⟩, trivial⟩, fun h i j => h.1.2 j i⟩))

theorem a_rec (m : ℕ) : (a (m + 3) : ℤ) = (3 : ℤ) * (a (m + 2) : ℤ) + (-3 : ℤ) * (a (m + 1) : ℤ) + (1 : ℤ) * (a (m) : ℤ) := by
  have h := vrec m 10 (by norm_num)
  rw [show V (m + 4) 10 = a (m + 3) from (a_eq (m + 3)).symm, show V (m + 3) 10 = a (m + 2) from (a_eq (m + 2)).symm, show V (m + 2) 10 = a (m + 1) from (a_eq (m + 1)).symm, show V (m + 1) 10 = a (m) from (a_eq (m)).symm] at h
  linear_combination h

theorem a_1 : a 1 = 159 := (a_eq 1).trans ((lit2 10 (by norm_num)).trans (by decide))
theorem a_2 : a 2 = 286 := (a_eq 2).trans ((lit3 10 (by norm_num)).trans (by decide))
theorem a_3 : a 3 = 445 := (a_eq 3).trans ((lit4 10 (by norm_num)).trans (by decide))
theorem a_4 : a 4 = 636 := (a_eq 4).trans ((lit5 10 (by norm_num)).trans (by decide))

end OMAA250659Helpers

open OMA.S_oeis_a250659 OMAA250659Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250659.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    have h := a_rec (m + 1)
    rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega] at h
    linear_combination h
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) ^ 3) = F' - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.X ^ 3 * F' := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (159 - 191 * PowerSeries.X + 64 * PowerSeries.X ^ 2) : PowerSeries ℚ) = PowerSeries.C (159 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (191 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (64 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a_1, a_2, a_3]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      have h := a_rec (j + 1)
      rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega, show j + 1 + 3 = j + 4 by omega] at h
      have q := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at q
      simp
      linear_combination q
  · intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    by_cases hb : n ≤ 3
    · interval_cases n <;> norm_num [a_1, a_2, a_3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h := a_rec (m + 1)
      rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega] at h
      have q := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at q
      have i1 := ih (m + 3) (by omega) (by omega)
      have i2 := ih (m + 2) (by omega) (by omega)
      have i3 := ih (m + 1) (by omega) (by omega)
      rw [q, i1, i2, i3]
      push_cast
      ring
