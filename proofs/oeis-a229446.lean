import OMAStatements.S_oeis_a229446
import Mathlib

/-!
# oeis-a229446: counting the 3 X n arrays

Split an array (a list of columns) into its leftmost column and the rest. The local conditions
are a chain condition, and each comparison (row i against row i + 1, nondecreasing)
is decided at the first position where the two differ, so it only adds a flag saying whether the
comparison is still pending. The numbers of valid arrays with a given leftmost column and given pending
flags satisfy a linear recursion over the next column; their explicit polynomial closed forms are
checked by induction over the 27 possible values of the leftmost column and 4 flag settings. Summing them gives
Hardin's polynomial, and the generating function and Barker's recurrence follow from it.

Source: OEIS A229446, https://oeis.org/A229446.
-/
namespace OMA.P_oeis_a229446

open OMA.S_oeis_a229446

abbrev R := Fin 3 → Fin 3

lemma lexle3 (r s : R) : toLex r ≤ toLex s ↔
    r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ r 2 ≤ s 2))) := by
  rw [le_iff_lt_or_eq]
  change (∃ i, (∀ j, j < i → r j = s j) ∧ r i < s i) ∨ r = s ↔ _
  rw [funext_iff]
  simp only [Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.exists_iff,
    IsEmpty.forall_iff]
  simp +decide only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, lt_self_iff_false,
    false_imp_iff, true_imp_iff, and_true, true_and, or_false]
  rw [le_iff_lt_or_eq (a := r 2)]
  tauto

lemma sum3 (g : R → ℚ) :
    ∑ s : R, g s = ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z] := by
  let e : Fin 3 × Fin 3 × Fin 3 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2], fun f => (f 0, f 1, f 2), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

def rowOK (r : R) : Prop := ∀ j : Fin 2, ((r j.succ : ℤ) - r j.castSucc) % 3 ≠ 2

def adj (r s : R) : Prop := (∀ j, ((s j : ℤ) - r j) % 3 ≠ 1) ∧ toLex r ≤ toLex s

/-- A decidable form of `adj`. -/
def adjE (r s : R) : Prop := (∀ j, ((s j : ℤ) - r j) % 3 ≠ 1) ∧
  (r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ r 2 ≤ s 2))))

lemma adj_iff (r s : R) : adj r s ↔ adjE r s := by unfold adj adjE; rw [lexle3]

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adjE r s) := by unfold adjE; infer_instance

open Classical

def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

def C0 (l : List R) : Prop := l.map (fun r => r 0) ≤ l.map (fun r => r 1)
def C1 (l : List R) : Prop := l.map (fun r => r 1) ≤ l.map (fun r => r 2)

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l ∧ C0 l ∧ C1 l := by
  unfold IsSolution Pall rowOK adj C0 C1
  simp only [Fin.forall_fin_two, Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_one_eq_two,
    Fin.castSucc_one]
  tauto

lemma pall_cons_nil (r : R) : Pall [r] ↔ rowOK r := by
  simp [Pall]

lemma pall_cons_cons (r s : R) (m : List R) :
    Pall (r :: s :: m) ↔ rowOK r ∧ adj r s ∧ Pall (s :: m) := by
  unfold Pall
  rw [List.isChain_cons]
  simp only [List.mem_cons, forall_eq_or_imp, List.head?_cons, Option.mem_def,
    Option.some.injEq, forall_eq']
  tauto

lemma lcons (a b : Fin 3) (l m : List (Fin 3)) : a :: l ≤ b :: m ↔ a < b ∨ (a = b ∧ l ≤ m) := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  change (List.Lex (· < ·) _ _ ∨ _) ↔ (_ ∨ _ ∧ (List.Lex (· < ·) _ _ ∨ _))
  rw [List.cons_lex_cons_iff, List.cons.injEq]
  tauto

lemma c0_cons (r : R) (l : List R) : C0 (r :: l) ↔ r 0 < r 1 ∨ (r 0 = r 1 ∧ C0 l) := by
  unfold C0; simp only [List.map_cons]; exact lcons _ _ _ _

lemma c1_cons (r : R) (l : List R) : C1 (r :: l) ↔ r 1 < r 2 ∨ (r 1 = r 2 ∧ C1 l) := by
  unfold C1; simp only [List.map_cons]; exact lcons _ _ _ _

lemma c_nil0 : C0 [] := by unfold C0; simp
lemma c_nil1 : C1 [] := by unfold C1; simp

def LL : ℕ → Finset (List R)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset R) ×ˢ LL n).image (fun p => p.1 :: p.2)

lemma mem_LL (n : ℕ) (l : List R) : l ∈ LL n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [LL]
  | succ n ih =>
    cases l with
    | nil => simp [LL]
    | cons x m => simp [LL, ih]

lemma card_cons (n : ℕ) (Q : List R → Prop) [DecidablePred Q] :
    ((LL (n + 1)).filter Q).card = ∑ s : R, ((LL n).filter (fun m => Q (s :: m))).card := by
  rw [LL, Finset.filter_image, Finset.card_image_of_injective _ (by
    intro p q h; simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2)]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

/-- The required column comparisons. -/
def Q (b0 b1 : Bool) (l : List R) : Prop := Pall l ∧ (b0 = true → C0 l) ∧ (b1 = true → C1 l)

/-- Condition on the top row. -/
def okT (b0 b1 : Bool) (r : R) : Prop :=
  rowOK r ∧ (b0 = true → r 0 ≤ r 1) ∧ (b1 = true → r 1 ≤ r 2)

instance (b0 b1 : Bool) (r : R) : Decidable (okT b0 b1 r) := by unfold okT; infer_instance

noncomputable def f (b0 b1 : Bool) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q b0 b1 (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f true true n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q true true)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, Q, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma q_single (b0 b1 : Bool) (r : R) : Q b0 b1 [r] ↔ okT b0 b1 r := by
  unfold Q okT
  rw [pall_cons_nil, c0_cons, c1_cons]
  have h0 := c_nil0; have h1 := c_nil1
  constructor
  · rintro ⟨h, h0', h1'⟩
    refine ⟨h, fun hb => ?_, fun hb => ?_⟩
    · rcases h0' hb with h' | h' <;> [exact h'.le; exact h'.1.le]
    · rcases h1' hb with h' | h' <;> [exact h'.le; exact h'.1.le]
  · rintro ⟨h, h0', h1'⟩
    refine ⟨h, fun hb => ?_, fun hb => ?_⟩
    · rcases lt_or_eq_of_le (h0' hb) with h' | h' <;> [exact Or.inl h'; exact Or.inr ⟨h', h0⟩]
    · rcases lt_or_eq_of_le (h1' hb) with h' | h' <;> [exact Or.inl h'; exact Or.inr ⟨h', h1⟩]

lemma aux (b : Bool) (x y : Fin 3) (C : Prop) :
    (b = true → (x < y ∨ (x = y ∧ C))) ↔ (b = true → x ≤ y) ∧ ((b && decide (x = y)) = true → C) := by
  cases b
  · simp
  · simp only [true_imp_iff, Bool.true_and, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h, hc⟩)
      · exact ⟨h.le, fun he => absurd he h.ne⟩
      · exact ⟨h.le, fun _ => hc⟩
    · rintro ⟨h, hc⟩
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', hc h'⟩

lemma q_cons (b0 b1 : Bool) (r s : R) (m : List R) :
    Q b0 b1 (r :: s :: m) ↔ (okT b0 b1 r ∧ adj r s) ∧
      Q (b0 && decide (r 0 = r 1)) (b1 && decide (r 1 = r 2)) (s :: m) := by
  unfold Q okT
  rw [pall_cons_cons, c0_cons, c1_cons, aux, aux]
  tauto

lemma f_zero (b0 b1 : Bool) (r : R) : f b0 b1 0 r = if okT b0 b1 r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT b0 b1 r
  · rw [if_pos ((q_single b0 b1 r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((q_single b0 b1 r).mp h')), if_neg h]; rfl

lemma f_succ (b0 b1 : Bool) (n : ℕ) (r : R) :
    f b0 b1 (n + 1) r = ∑ s : R, if okT b0 b1 r ∧ adjE r s then
      f (b0 && decide (r 0 = r 1)) (b1 && decide (r 1 = r 2)) n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [q_cons, adj_iff]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

/-- Closed forms. -/
def T00 : Fin 3 → Fin 3 → Fin 3 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 3) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((5 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 3) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((7 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((5 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((1 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T01 : Fin 3 → Fin 3 → Fin 3 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 3) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((5 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((5 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((1 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T10 : Fin 3 → Fin 3 → Fin 3 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((1 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 3) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((7 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((5 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T11 : Fin 3 → Fin 3 → Fin 3 → ℚ → ℚ :=
  ![![![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((1 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((5 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def PCv (b0 b1 : Bool) (i j k : Fin 3) (t : ℚ) : ℚ :=
  (if b0 then (if b1 then T11 else T10) else (if b1 then T01 else T00)) i j k t

set_option maxHeartbeats 8000000 in
theorem f_closed (n : ℕ) : ∀ b0 b1 (x y z : Fin 3), (f b0 b1 n ![x, y, z] : ℚ) = PCv b0 b1 x y z n := by
  induction n with
  | zero =>
    intro b0 b1 x y z; rw [f_zero]
    cases b0 <;> cases b1 <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp +decide [PCv, T00, T01, T10, T11, okT, rowOK]
  | succ n ih =>
    intro b0 b1 x y z; rw [f_succ]; push_cast
    rw [sum3]
    simp only [Fin.sum_univ_three]
    cases b0 <;> cases b1 <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T00, T01, T10, T11] <;> ring

theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + ((8 : ℚ) / 3) * (n : ℚ) ^ 1 + (5 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]; push_cast
  rw [sum3]
  simp only [Fin.sum_univ_three, f_closed]
  simp [PCv, T11]
  ring

lemma av (k : ℕ) : (a (k + 1) : ℚ) = ((1 : ℚ) / 3) * ((k : ℚ) + 1) ^ 3 + ((8 : ℚ) / 3) * ((k : ℚ) + 1) ^ 1 + (5 : ℚ) := by
  rw [a_closed (k + 1) (by omega)]; push_cast; ring

open PowerSeries in
theorem full :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 3) * n ^ 3 + (8 / 3) * n + 5) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 4 =
      8 - 19 * X + 18 * X ^ 2 - 5 * X ^ 3) ∧
    (∀ n > 4, (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - 1 * a (n - 4)) := by
  refine ⟨fun n hn => by rw [a_closed n hn]; ring, ?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 4 =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-4 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (6 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-4 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (8 - 19 * X + 18 * X ^ 2 - 5 * X ^ 3 : PowerSeries ℚ) = C (8 : ℚ) * X ^ 0 + C (-19 : ℚ) * X ^ 1 + C (18 : ℚ) * X ^ 2 + C (-5 : ℚ) * X ^ 3 by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul, pow_zero, mul_one]; ring]
    ext k
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge k 4 with h | h
    · interval_cases k <;> simp [av] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
      simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m + 0 by omega, show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega, if_true, show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega, if_false, av, coeff_C]
      try simp only [show ∀ i, m + 4 ≠ i → (if m + 4 = i then (1 : ℚ) else 0) = 0 from fun i h => if_neg h]
      first | (push_cast; ring) | (simp; push_cast; ring) | simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 3 + 1 by omega, show m + 5 - 2 = m + 2 + 1 by omega, show m + 5 - 3 = m + 1 + 1 by omega, show m + 5 - 4 = m + 0 + 1 by omega, show m + 5 = m + 4 + 1 by omega]
    have : ((a (m + 4 + 1) : ℤ) : ℚ) = 4 * (a (m + 3 + 1) : ℚ) - 6 * (a (m + 2 + 1) : ℚ) + 4 * (a (m + 1 + 1) : ℚ) - 1 * (a (m + 0 + 1) : ℚ) := by
      push_cast; rw [av, av, av, av, av]; push_cast; ring
    exact_mod_cast this

end OMA.P_oeis_a229446

theorem OMA.solution : type_of% @OMA.S_oeis_a229446.main := OMA.P_oeis_a229446.full
