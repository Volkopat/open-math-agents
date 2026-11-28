import OMAStatements.S_oeis_a184138
import Mathlib

/-!
# oeis-a184138: counting the n X 3 arrays

Original Lean proof: @physbuzz.

Split an array (a list of rows) into its first row and the rest. The local conditions
are a chain condition, and each lexicographic comparison of consecutive columns is decided at the first position
where the two differ, so it only adds a flag saying whether the comparison is still pending. The
numbers of valid arrays with a given first row and given pending flags satisfy a linear
recursion over the next row; their explicit polynomial closed forms are checked by induction
over the 8 possible first rows and all flag settings. Summing them gives Hardin's
polynomial, and the generating function and Barker's recurrence follow from it.

Source: OEIS A184138, https://oeis.org/A184138.
-/
namespace OMA.P_oeis_a184138

open OMA.S_oeis_a184138

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

def adj (r s : R) : Prop := toLex r ≤ toLex s

/-- A decidable form of `adj`. -/
def adjE (r s : R) : Prop := (r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ r 2 ≤ s 2))))

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
  ![![![(fun x : ℚ => ((1 : ℚ) / 5040) * x ^ 7 + ((1 : ℚ) / 180) * x ^ 6 + ((23 : ℚ) / 360) * x ^ 5 + ((7 : ℚ) / 18) * x ^ 4 + ((967 : ℚ) / 720) * x ^ 3 + ((469 : ℚ) / 180) * x ^ 2 + ((363 : ℚ) / 140) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 720) * x ^ 6 + ((7 : ℚ) / 240) * x ^ 5 + ((35 : ℚ) / 144) * x ^ 4 + ((49 : ℚ) / 48) * x ^ 3 + ((203 : ℚ) / 90) * x ^ 2 + ((49 : ℚ) / 20) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 120) * x ^ 5 + ((1 : ℚ) / 8) * x ^ 4 + ((17 : ℚ) / 24) * x ^ 3 + ((15 : ℚ) / 8) * x ^ 2 + ((137 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((5 : ℚ) / 12) * x ^ 3 + ((35 : ℚ) / 24) * x ^ 2 + ((25 : ℚ) / 12) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T01 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 5040) * x ^ 7 + ((1 : ℚ) / 240) * x ^ 6 + ((31 : ℚ) / 720) * x ^ 5 + ((11 : ℚ) / 48) * x ^ 4 + ((281 : ℚ) / 360) * x ^ 3 + ((53 : ℚ) / 30) * x ^ 2 + ((457 : ℚ) / 210) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 720) * x ^ 6 + ((7 : ℚ) / 240) * x ^ 5 + ((35 : ℚ) / 144) * x ^ 4 + ((49 : ℚ) / 48) * x ^ 3 + ((203 : ℚ) / 90) * x ^ 2 + ((49 : ℚ) / 20) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 4) * x ^ 3 + ((23 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 4) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T10 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 5040) * x ^ 7 + ((1 : ℚ) / 180) * x ^ 6 + ((1 : ℚ) / 18) * x ^ 5 + ((19 : ℚ) / 72) * x ^ 4 + ((577 : ℚ) / 720) * x ^ 3 + ((623 : ℚ) / 360) * x ^ 2 + ((15 : ℚ) / 7) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 720) * x ^ 6 + ((7 : ℚ) / 240) * x ^ 5 + ((29 : ℚ) / 144) * x ^ 4 + ((29 : ℚ) / 48) * x ^ 3 + ((467 : ℚ) / 360) * x ^ 2 + ((28 : ℚ) / 15) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 120) * x ^ 5 + ((1 : ℚ) / 8) * x ^ 4 + ((17 : ℚ) / 24) * x ^ 3 + ((15 : ℚ) / 8) * x ^ 2 + ((137 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((5 : ℚ) / 12) * x ^ 3 + ((35 : ℚ) / 24) * x ^ 2 + ((25 : ℚ) / 12) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

def T11 : Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![(fun x : ℚ => ((1 : ℚ) / 5040) * x ^ 7 + ((1 : ℚ) / 240) * x ^ 6 + ((5 : ℚ) / 144) * x ^ 5 + ((5 : ℚ) / 48) * x ^ 4 + ((73 : ℚ) / 180) * x ^ 3 + ((107 : ℚ) / 120) * x ^ 2 + ((131 : ℚ) / 84) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 720) * x ^ 6 + ((7 : ℚ) / 240) * x ^ 5 + ((29 : ℚ) / 144) * x ^ 4 + ((29 : ℚ) / 48) * x ^ 3 + ((467 : ℚ) / 360) * x ^ 2 + ((28 : ℚ) / 15) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 4) * x ^ 3 + ((23 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 4) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]

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

private def P (x : ℚ) : ℚ :=
  (1 / 5040) * x ^ 7 + (1 / 240) * x ^ 6 + (5 / 144) * x ^ 5 + (5 / 48) * x ^ 4 +
    (73 / 180) * x ^ 3 + (107 / 120) * x ^ 2 + (131 / 84) * x + 1

set_option maxHeartbeats 4000000 in
theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = P n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]; push_cast
  rw [sumk]
  simp only [Fin.sum_univ_two, f_closed]
  simp [PCv, T11, P]
  ring

private lemma av (k : ℕ) : (a (k + 1) : ℚ) = P ((k : ℚ) + 1) := by
  simpa using a_closed (k + 1) (by omega)

open PowerSeries

private noncomputable def series : PowerSeries ℚ := mk fun n => (a (n + 1) : ℚ)

private noncomputable def numerator : PowerSeries ℚ :=
  C 4 + C (-18) * X ^ 1 + C 45 * X ^ 2 + C (-62) * X ^ 3 +
    C 52 * X ^ 4 + C (-27) * X ^ 5 + C 8 * X ^ 6 + C (-1) * X ^ 7

private lemma coeff_product (n : ℕ) :
    coeff n (series * (1 - X) ^ 8) =
      let t (i : ℕ) := if i ≤ n then (a (n - i + 1) : ℚ) else 0
      (a (n + 1) : ℚ) + (-8) * t 1 + 28 * t 2 + (-56) * t 3 + 70 * t 4 +
        (-56) * t 5 + 28 * t 6 + (-8) * t 7 + t 8 := by
  have h : series * (1 - X) ^ 8 = series +
      C (-8) * (series * X ^ 1) + C 28 * (series * X ^ 2) +
      C (-56) * (series * X ^ 3) + C 70 * (series * X ^ 4) +
      C (-56) * (series * X ^ 5) + C 28 * (series * X ^ 6) +
      C (-8) * (series * X ^ 7) + series * X ^ 8 := by
    simp only [map_neg, map_ofNat, neg_mul]
    ring
  rw [h]
  simp only [series, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

-- The same vanishing coefficients give the generating function and recurrence.
private lemma vanish (n : ℕ) (hn : 8 ≤ n) : coeff n (series * (1 - X) ^ 8) = 0 := by
  simp (disch := omega) only [coeff_product, if_pos, av, Nat.cast_sub]
  unfold P
  ring

private lemma gf : series * (1 - X) ^ 8 = numerator := by
  ext n
  rcases Nat.lt_or_ge n 8 with h | h
  · rw [coeff_product]
    interval_cases n <;> norm_num [numerator, coeff_C, coeff_C_mul_X_pow, av, P]
  · rw [vanish n h]
    simp (disch := omega) only [numerator, map_add, coeff_C, coeff_C_mul_X_pow, if_neg, add_zero]

theorem full : type_of% @OMA.S_oeis_a184138.main := by
  refine ⟨a_closed, ?_, ?_⟩
  · simpa only [series, numerator, pow_one, map_neg, map_ofNat, map_one, neg_mul, one_mul,
      sub_eq_add_neg] using gf
  · intro n hn
    have h := vanish (n - 1) (by omega)
    rw [coeff_product] at h
    have idx (j : ℕ) (hj : j + 1 ≤ n) : n - 1 - j + 1 = n - j := by omega
    simp (disch := omega) only [if_pos, idx, Nat.sub_add_cancel] at h
    qify
    linear_combination h

end OMA.P_oeis_a184138

theorem OMA.solution : type_of% @OMA.S_oeis_a184138.main := OMA.P_oeis_a184138.full
