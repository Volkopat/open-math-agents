import OMAStatements.S_oeis_a266429
import Mathlib

/-!
# oeis-a266429: counting the 3 X n arrays

Split an array (a list of columns) into its first column and the rest. The local conditions
are a chain condition, and each lexicographic comparison of consecutive rows is decided at the first position
where the two differ, so it only adds a flag saying whether the comparison is still pending. The
numbers of valid arrays with a given first column and given pending flags satisfy a linear
recursion over the next column; their explicit polynomial closed forms are checked by induction
over the 8 possible first columns and all flag settings. Summing them gives Hardin's
polynomial, and the generating function and Barker's recurrence follow from it.

Source: OEIS A266429, https://oeis.org/A266429.
-/
namespace OMA.P_oeis_a266429

open OMA.S_oeis_a266429

abbrev R := Fin 3 → Fin 2

lemma lexle (r s : R) : toLex r ≤ toLex s ↔ (r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ r 2 ≤ s 2)))) := by
  rw [le_iff_lt_or_eq]
  change (∃ i, (∀ j, j < i → r j = s j) ∧ r i < s i) ∨ r = s ↔ _
  rw [funext_iff]
  simp only [Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.exists_iff,
    IsEmpty.forall_iff]
  simp +decide only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, lt_self_iff_false, false_imp_iff, true_imp_iff, and_true, true_and, or_false]
  rw [le_iff_lt_or_eq (a := r 2)]
  tauto

lemma sumk (g : R → ℚ) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, g ![y0, y1, y2] := by
  let e : Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2], fun f => (f 0, f 1, f 2), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def rowOK (_r : R) : Prop := True

def adj (r s : R) : Prop := toLex r ≤ toLex s ∧ ∑ i, (r i : ℕ) ≤ ∑ i, (s i : ℕ)

/-- A decidable form of `adj`. -/
def adjE (r s : R) : Prop :=
  (r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ r 2 ≤ s 2)))) ∧ ∑ i, (r i : ℕ) ≤ ∑ i, (s i : ℕ)

lemma adj_iff (r s : R) : adj r s ↔ adjE r s := by unfold adj adjE; rw [lexle]

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adjE r s) := by unfold adjE; infer_instance

open Classical

def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

def C0 (l : List R) : Prop := l.map (fun r => r 0) ≤ l.map (fun r => r 1)
def C1 (l : List R) : Prop := l.map (fun r => r 1) ≤ l.map (fun r => r 2)

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l ∧ C0 l ∧ C1 l := by
  unfold IsSolution Pall rowOK adj C0 C1
  simp only [Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.forall_iff, Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_one_eq_two, Fin.castSucc_one, Fin.reduceSucc, Fin.reduceCastSucc, implies_true, true_and]
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

lemma lcons (a b : Fin 2) (l m : List (Fin 2)) : a :: l ≤ b :: m ↔ a < b ∨ (a = b ∧ l ≤ m) := by
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

/-- The pending track comparisons. -/
def Q (b0 b1 : Bool) (l : List R) : Prop := Pall l ∧ (b0 = true → C0 l) ∧ (b1 = true → C1 l)

/-- Condition on the first letter. -/
def okT (b0 b1 : Bool) (r : R) : Prop := rowOK r ∧ (b0 = true → r 0 ≤ r 1) ∧ (b1 = true → r 1 ≤ r 2)

instance (b0 b1 : Bool) (r : R) : Decidable (okT b0 b1 r) := by
  unfold okT; infer_instance

noncomputable def f (b0 b1 : Bool) (n : ℕ) (r : R) : ℕ :=
  ((LL n).filter (fun l => Q b0 b1 (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f true true n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q true true)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, Q, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma aux (b : Bool) (x y : Fin 2) (C : Prop) :
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

lemma aux1 (b : Bool) (x y : Fin 2) (C : Prop) (hC : C) :
    (b = true → (x < y ∨ (x = y ∧ C))) ↔ (b = true → x ≤ y) := by
  rw [aux]; constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun _ => hC⟩

lemma q_single (b0 b1 : Bool) (r : R) : Q b0 b1 [r] ↔ okT b0 b1 r := by
  unfold Q okT
  rw [pall_cons_nil, c0_cons, c1_cons]
  have h0 := c_nil0; have h1 := c_nil1
  simp only [aux1 _ _ _ _ h0, aux1 _ _ _ _ h1]

lemma q_cons (b0 b1 : Bool) (r s : R) (m : List R) :
    Q b0 b1 (r :: s :: m) ↔ (okT b0 b1 r ∧ adj r s) ∧ Q (b0 && decide (r 0 = r 1)) (b1 && decide (r 1 = r 2)) (s :: m) := by
  unfold Q okT
  rw [pall_cons_cons, c0_cons, c1_cons, aux, aux]
  tauto

lemma f_zero (b0 b1 : Bool) (r : R) :
    f b0 b1 0 r = if okT b0 b1 r then 1 else 0 := by
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

def T00 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 20) * x ^ 5 + ((13 : ℚ) / 36) * x ^ 4 + ((4 : ℚ) / 3) * x ^ 3 + ((949 : ℚ) / 360) * x ^ 2 + ((157 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((5 : ℚ) / 24) * x ^ 4 + (1 : ℚ) * x ^ 3 + ((55 : ℚ) / 24) * x ^ 2 + ((149 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 12) * x ^ 4 + ((2 : ℚ) / 3) * x ^ 3 + ((23 : ℚ) / 12) * x ^ 2 + ((7 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T01 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 30) * x ^ 5 + ((17 : ℚ) / 72) * x ^ 4 + ((2 : ℚ) / 3) * x ^ 3 + ((317 : ℚ) / 180) * x ^ 2 + ((23 : ℚ) / 10) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((5 : ℚ) / 24) * x ^ 4 + (1 : ℚ) * x ^ 3 + ((55 : ℚ) / 24) * x ^ 2 + ((149 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T10 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 24) * x ^ 5 + ((17 : ℚ) / 72) * x ^ 4 + ((19 : ℚ) / 24) * x ^ 3 + ((317 : ℚ) / 180) * x ^ 2 + ((13 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((1 : ℚ) / 6) * x ^ 4 + ((7 : ℚ) / 12) * x ^ 3 + ((4 : ℚ) / 3) * x ^ 2 + ((19 : ℚ) / 10) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 12) * x ^ 4 + ((2 : ℚ) / 3) * x ^ 3 + ((23 : ℚ) / 12) * x ^ 2 + ((7 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T11 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 40) * x ^ 5 + ((1 : ℚ) / 9) * x ^ 4 + ((7 : ℚ) / 24) * x ^ 3 + ((319 : ℚ) / 360) * x ^ 2 + ((101 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((1 : ℚ) / 6) * x ^ 4 + ((7 : ℚ) / 12) * x ^ 3 + ((4 : ℚ) / 3) * x ^ 2 + ((19 : ℚ) / 10) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def PCv (b0 b1 : Bool) (i0 i1 i2 : Fin 2) (t : ℚ) : ℚ :=
  (if b0 then (if b1 then T11 else T10) else (if b1 then T01 else T00)) i0 i1 i2 t

set_option maxHeartbeats 40000000 in
theorem f_closed (n : ℕ) : ∀ b0 b1 (i0 i1 i2 : Fin 2),
    (f b0 b1 n ![i0, i1, i2] : ℚ) = PCv b0 b1 i0 i1 i2 n := by
  induction n with
  | zero =>
    intro b0 b1 i0 i1 i2; rw [f_zero]
    cases b0 <;> cases b1 <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
      simp +decide [PCv, T00, T01, T10, T11, okT, rowOK]
  | succ n ih =>
    intro b0 b1 i0 i1 i2; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    cases b0 <;> cases b1 <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T00, T01, T10, T11] <;> ring

set_option maxHeartbeats 4000000 in
theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 360) * (n : ℚ) ^ 6 + ((1 : ℚ) / 40) * (n : ℚ) ^ 5 + ((1 : ℚ) / 9) * (n : ℚ) ^ 4 + ((7 : ℚ) / 24) * (n : ℚ) ^ 3 + ((319 : ℚ) / 360) * (n : ℚ) ^ 2 + ((101 : ℚ) / 60) * (n : ℚ) ^ 1 + (1 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]; push_cast
  rw [sumk]
  simp only [Fin.sum_univ_two, f_closed]
  simp [PCv, T11]
  ring

lemma av (k : ℕ) : (a (k + 1) : ℚ) = ((1 : ℚ) / 360) * ((k : ℚ) + 1) ^ 6 + ((1 : ℚ) / 40) * ((k : ℚ) + 1) ^ 5 + ((1 : ℚ) / 9) * ((k : ℚ) + 1) ^ 4 + ((7 : ℚ) / 24) * ((k : ℚ) + 1) ^ 3 + ((319 : ℚ) / 360) * ((k : ℚ) + 1) ^ 2 + ((101 : ℚ) / 60) * ((k : ℚ) + 1) ^ 1 + (1 : ℚ) := by
  rw [a_closed (k + 1) (by omega)]; push_cast; ring

open PowerSeries in
theorem full :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 360) * n ^ 6 + (1 / 40) * n ^ 5 + (1 / 9) * n ^ 4 + (7 / 24) * n ^ 3 + (319 / 360) * n ^ 2 + (101 / 60) * n + 1) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      4 - 15 * X + 32 * X ^ 2 - 34 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + 1 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7)) := by
  refine ⟨fun n hn => by rw [a_closed n hn]; ring, ?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (4 - 15 * X + 32 * X ^ 2 - 34 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + 1 * X ^ 6 : PowerSeries ℚ) = C (4 : ℚ) * X ^ 0 + C (-15 : ℚ) * X ^ 1 + C (32 : ℚ) * X ^ 2 + C (-34 : ℚ) * X ^ 3 + C (21 : ℚ) * X ^ 4 + C (-7 : ℚ) * X ^ 5 + C (1 : ℚ) * X ^ 6 by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul, pow_zero, mul_one]; ring]
    ext k
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge k 7 with h | h
    · interval_cases k <;> simp [av] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
      simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m + 0 by omega, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, show 7 ≤ m + 7 by omega, if_true, show m + 7 ≠ 0 by omega, show m + 7 ≠ 1 by omega, show m + 7 ≠ 2 by omega, show m + 7 ≠ 3 by omega, show m + 7 ≠ 4 by omega, show m + 7 ≠ 5 by omega, show m + 7 ≠ 6 by omega, if_false, av, coeff_C]
      first | (push_cast; ring) | (simp; push_cast; ring) | simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 6 + 1 by omega, show m + 8 - 2 = m + 5 + 1 by omega, show m + 8 - 3 = m + 4 + 1 by omega, show m + 8 - 4 = m + 3 + 1 by omega, show m + 8 - 5 = m + 2 + 1 by omega, show m + 8 - 6 = m + 1 + 1 by omega, show m + 8 - 7 = m + 0 + 1 by omega, show m + 8 = m + 7 + 1 by omega]
    have : ((a (m + 7 + 1) : ℤ) : ℚ) = 7 * (a (m + 6 + 1) : ℚ) - 21 * (a (m + 5 + 1) : ℚ) + 35 * (a (m + 4 + 1) : ℚ) - 35 * (a (m + 3 + 1) : ℚ) + 21 * (a (m + 2 + 1) : ℚ) - 7 * (a (m + 1 + 1) : ℚ) + 1 * (a (m + 0 + 1) : ℚ) := by
      push_cast; rw [av, av, av, av, av, av, av, av]; push_cast; ring
    exact_mod_cast this

end OMA.P_oeis_a266429

theorem OMA.solution : type_of% @OMA.S_oeis_a266429.main := OMA.P_oeis_a266429.full
