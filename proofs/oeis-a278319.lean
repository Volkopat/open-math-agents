import OMAStatements.S_oeis_a278319

namespace OMA.S_oeis_a278319

open PowerSeries Finset



/-! ## Row and column mistakes, row by row -/

/-- The number of rows of y followed by a lexicographically smaller row. -/
def rowCnt {m : ℕ} (y : Fin m → Fin 2 → Fin 2) : ℕ :=
  ∑ i : Fin m, if ∃ i' : Fin m, i'.val = i.val + 1 ∧ List.ofFn (y i') < List.ofFn (y i) then 1 else 0

/-- Column 1 of y is lexicographically less than column 0. -/
def colLt {m : ℕ} (y : Fin m → Fin 2 → Fin 2) : Prop :=
  List.ofFn (fun i => y i 1) < List.ofFn (fun i => y i 0)

instance {m : ℕ} (y : Fin m → Fin 2 → Fin 2) : Decidable (colLt y) := by
  unfold colLt
  infer_instance

/-- The first row of y is lexicographically less than the row r. -/
def firstLt {m : ℕ} (r : Fin 2 → Fin 2) (y : Fin m → Fin 2 → Fin 2) : Prop :=
  ∃ i' : Fin m, i'.val = 0 ∧ List.ofFn (y i') < List.ofFn r

instance {m : ℕ} (r : Fin 2 → Fin 2) (y : Fin m → Fin 2 → Fin 2) : Decidable (firstLt r y) := by
  unfold firstLt
  infer_instance

theorem mistakes_eq (n : ℕ) (x : Fin n → Fin 2 → Fin 2) :
    mistakes n x = rowCnt x + (if colLt x then 1 else 0) := by
  unfold mistakes
  congr 1
  · rw [show {i : Fin n | ∃ i' : Fin n, i'.val = i.val + 1 ∧ List.ofFn (x i') < List.ofFn (x i)} =
        ↑(univ.filter fun i : Fin n => ∃ i' : Fin n, i'.val = i.val + 1 ∧
          List.ofFn (x i') < List.ofFn (x i)) by ext; simp,
      Set.ncard_coe_finset, card_filter]
    rfl
  · by_cases h : colLt x
    · rw [if_pos h]
      have : {j : Fin 2 | ∃ j' : Fin 2, j'.val = j.val + 1 ∧
          List.ofFn (fun i => x i j') < List.ofFn (fun i => x i j)} = {0} := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨j', hj', _⟩
          have := j'.isLt
          exact Fin.ext (by omega)
        · rintro rfl
          exact ⟨1, rfl, h⟩
      rw [this, Set.ncard_singleton]
    · rw [if_neg h]
      have : {j : Fin 2 | ∃ j' : Fin 2, j'.val = j.val + 1 ∧
          List.ofFn (fun i => x i j') < List.ofFn (fun i => x i j)} = ∅ := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨j', hj', hl⟩
        have h1 := j'.isLt
        have h2 := j.isLt
        have hj0 : j = 0 := Fin.ext (by omega)
        have hj1 : j' = 1 := Fin.ext (by simp [hj0] at hj'; omega)
        subst hj0 hj1
        exact h hl
      rw [this, Set.ncard_empty]

theorem rowCnt_cons {m : ℕ} (r : Fin 2 → Fin 2) (y : Fin m → Fin 2 → Fin 2) :
    rowCnt (Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) = (if firstLt r y then 1 else 0) + rowCnt y := by
  unfold rowCnt
  rw [Fin.sum_univ_succ]
  congr 1
  · have e : (∃ i' : Fin (m + 1), i'.val = (0 : Fin (m + 1)).val + 1 ∧
        List.ofFn ((Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) i') <
          List.ofFn ((Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) 0)) ↔ firstLt r y := by
      unfold firstLt
      rw [Fin.exists_fin_succ]
      simp
    by_cases h : firstLt r y
    · rw [if_pos (e.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e.1 h')), if_neg h]
  · refine sum_congr rfl (fun i _ => ?_)
    have e : (∃ i' : Fin (m + 1), i'.val = (Fin.succ i).val + 1 ∧
        List.ofFn ((Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) i') <
          List.ofFn ((Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) (Fin.succ i))) ↔
        (∃ i' : Fin m, i'.val = i.val + 1 ∧ List.ofFn (y i') < List.ofFn (y i)) := by
      rw [Fin.exists_fin_succ]
      simp
    by_cases h : ∃ i' : Fin m, i'.val = i.val + 1 ∧ List.ofFn (y i') < List.ofFn (y i)
    · rw [if_pos (e.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

theorem colLt_cons {m : ℕ} (r : Fin 2 → Fin 2) (y : Fin m → Fin 2 → Fin 2) :
    colLt (Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) ↔ r 1 < r 0 ∨ (r 1 = r 0 ∧ colLt y) := by
  unfold colLt
  rw [List.ofFn_succ, List.ofFn_succ, List.cons_lt_cons_iff]
  simp

theorem firstLt_cons {m : ℕ} (r q : Fin 2 → Fin 2) (y : Fin m → Fin 2 → Fin 2) :
    firstLt r (Fin.cons q y : Fin (m + 1) → Fin 2 → Fin 2) ↔ List.ofFn q < List.ofFn r := by
  unfold firstLt
  rw [Fin.exists_fin_succ]
  simp

/-- The column status after the row q: 0 while the columns are equal so far, 1 once column 1 is
below column 0 at the first difference, 2 once it is above. -/
def stNext (st : ℕ) (q : Fin 2 → Fin 2) : ℕ :=
  if st = 0 then (if q 1 < q 0 then 1 else if q 1 = q 0 then 0 else 2) else st

/-- The column mistake of y under the status st. -/
def colC {m : ℕ} (st : ℕ) (y : Fin m → Fin 2 → Fin 2) : ℕ :=
  if st = 0 then (if colLt y then 1 else 0) else if st = 1 then 1 else 0

theorem colC_cons {m : ℕ} (st : ℕ) (hst : st ≤ 2) (q : Fin 2 → Fin 2) (y : Fin m → Fin 2 → Fin 2) :
    colC st (Fin.cons q y : Fin (m + 1) → Fin 2 → Fin 2) = colC (stNext st q) y := by
  unfold colC stNext
  by_cases h0 : st = 0
  · subst h0
    simp only [if_true]
    by_cases h1 : q 1 < q 0
    · rw [if_pos ((colLt_cons q y).2 (Or.inl h1)), if_pos h1]
      simp
    · by_cases h2 : q 1 = q 0
      · rw [if_neg h1, if_pos h2]
        simp only [if_true]
        by_cases h3 : colLt y
        · rw [if_pos ((colLt_cons q y).2 (Or.inr ⟨h2, h3⟩)), if_pos h3]
        · rw [if_neg (fun h' => by rcases (colLt_cons q y).1 h' with h' | h'; exact h1 h'; exact h3 h'.2),
            if_neg h3]
      · rw [if_neg (fun h' => by rcases (colLt_cons q y).1 h' with h' | h'; exact h1 h'; exact h2 h'.1),
          if_neg h1, if_neg h2]
        simp
  · simp only [h0, if_false]

theorem colC_zero (st : ℕ) (y : Fin 0 → Fin 2 → Fin 2) : colC st y = if st = 1 then 1 else 0 := by
  have h : ¬ colLt y := by
    unfold colLt
    simp
  unfold colC
  by_cases h0 : st = 0
  · subst h0
    simp [h]
  · simp [h0]

/-- The ways to put m more rows below the row r, with the column status st and e mistakes so
far, so that there are exactly 2 mistakes in all. -/
noncomputable def N (r : Fin 2 → Fin 2) (st e m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 2 → Fin 2,
    if (if firstLt r y then 1 else 0) + rowCnt y + colC st y + e = 2 then 1 else 0

theorem sum_cons {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 1) → α) → ℕ) :
    ∑ y : Fin (m + 1) → α, f y = ∑ r : α, ∑ y : Fin m → α, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem N_zero (r : Fin 2 → Fin 2) (st e : ℕ) :
    N r st e 0 = if (if st = 1 then 1 else 0) + e = 2 then 1 else 0 := by
  have key : ∀ y : Fin 0 → Fin 2 → Fin 2,
      (if (if firstLt r y then 1 else 0) + rowCnt y + colC st y + e = 2 then 1 else 0) =
        if (if st = 1 then 1 else 0) + e = 2 then 1 else 0 := by
    intro y
    have h1 : ¬ firstLt r y := fun ⟨i, _⟩ => i.elim0
    have h2 : rowCnt y = 0 := by simp [rowCnt]
    rw [if_neg h1, h2, colC_zero, zero_add, zero_add]
  unfold N
  rw [Fintype.sum_unique]
  exact key _

theorem N_succ (r : Fin 2 → Fin 2) (st e m : ℕ) (hst : st ≤ 2) :
    N r st e (m + 1) = ∑ q : Fin 2 → Fin 2,
      N q (stNext st q) (e + if List.ofFn q < List.ofFn r then 1 else 0) m := by
  unfold N
  rw [sum_cons]
  refine sum_congr rfl (fun q _ => ?_)
  refine sum_congr rfl (fun y _ => ?_)
  rw [rowCnt_cons, colC_cons st hst]
  have hf : (if firstLt r (Fin.cons q y : Fin (m + 1) → Fin 2 → Fin 2) then 1 else 0) =
      if List.ofFn q < List.ofFn r then 1 else 0 := by
    by_cases h : List.ofFn q < List.ofFn r
    · rw [if_pos ((firstLt_cons r q y).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((firstLt_cons r q y).1 h')), if_neg h]
  rw [hf]
  have he : ((if List.ofFn q < List.ofFn r then 1 else 0) + ((if firstLt q y then 1 else 0) + rowCnt y) +
      colC (stNext st q) y + e = 2) ↔
      ((if firstLt q y then 1 else 0) + rowCnt y + colC (stNext st q) y +
        (e + if List.ofFn q < List.ofFn r then 1 else 0) = 2) := by omega
  simp only [he]

theorem N_over (r : Fin 2 → Fin 2) (st e m : ℕ) (h : 2 < e) : N r st e m = 0 := by
  unfold N
  refine sum_eq_zero (fun y _ => ?_)
  rw [if_neg (by omega)]

theorem stNext_le (st : ℕ) (hst : st ≤ 2) (q : Fin 2 → Fin 2) : stNext st q ≤ 2 := by
  unfold stNext
  split_ifs <;> omega

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 2, N r (stNext 0 r) 0 n := by
  have ha : a (n + 1) = ∑ x : Fin (n + 1) → Fin 2 → Fin 2,
      if rowCnt x + colC 0 x = 2 then 1 else 0 := by
    rw [← card_filter]
    unfold a
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mistakes_eq, colC, if_true]
  rw [ha, sum_cons]
  refine sum_congr rfl (fun r _ => ?_)
  unfold N
  refine sum_congr rfl (fun y _ => ?_)
  rw [rowCnt_cons, colC_cons 0 (by norm_num), add_zero, add_assoc]

/-! ## Codes -/

/-- The row with code c. -/
def dig (c : ℕ) : Fin 2 → Fin 2 := fun j => ⟨c / 2 ^ j.val % 2, Nat.mod_lt _ (by norm_num)⟩

def code (r : Fin 2 → Fin 2) : ℕ := (r 0).val + 2 * (r 1).val

theorem dig_code (r : Fin 2 → Fin 2) : dig (code r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  fin_cases j <;> simp [dig, code] <;> omega

theorem code_lt (r : Fin 2 → Fin 2) : code r < 4 := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  unfold code
  omega

theorem code_dig (c : ℕ) (h : c < 4) : code (dig c) = c := by
  simp [code, dig]
  omega

theorem sum_dig (g : (Fin 2 → Fin 2) → ℕ) : ∑ r, g r = ∑ c ∈ range 4, g (dig c) := by
  rw [← (finFunctionFinEquiv (m := 2) (n := 2)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun c => g (dig c)) _

/-- The lexicographic order of rows on codes: bit 4 * rc + qc says row qc is less than row rc. -/
def ltC (qc rc : ℕ) : ℕ := 29008 >>> (4 * rc + qc) % 2

/-- The column status on codes. -/
def stC (st qc : ℕ) : ℕ := if st = 0 then (if qc / 2 % 2 < qc % 2 then 1 else if qc / 2 % 2 = qc % 2 then 0 else 2) else st

def enc (rc st e : ℕ) : ℕ := (rc * 3 + st) * 3 + e

def rcOf (s : ℕ) : ℕ := s / (3 * 3)

def stOf (s : ℕ) : ℕ := s / 3 % 3

def eOf (s : ℕ) : ℕ := s % 3

def guardB (s qc : ℕ) : Bool := decide (eOf s + ltC qc (rcOf s) ≤ 2)

def succS (s qc : ℕ) : ℕ := enc qc (stC (stOf s) qc) (eOf s + ltC qc (rcOf s))

def Ncode : ℕ → ℕ → ℕ
  | s, 0 => if (if stOf s = 1 then 1 else 0) + eOf s = 2 then 1 else 0
  | s, m + 1 => ∑ qc ∈ range 4, if guardB s qc = true then Ncode (succS s qc) m else 0

theorem Ncode_succ (s m : ℕ) : Ncode s (m + 1) =
    ∑ qc ∈ range 4, if guardB s qc = true then Ncode (succS s qc) m else 0 := rfl

theorem dec_enc (rc st e : ℕ) (h1 : st ≤ 2) (h2 : e ≤ 2) :
    rcOf (enc rc st e) = rc ∧ stOf (enc rc st e) = st ∧ eOf (enc rc st e) = e := by
  unfold rcOf stOf eOf enc
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem stC_eq (st : ℕ) (q : Fin 2 → Fin 2) : stC st (code q) = stNext st q := by
  unfold stC stNext
  by_cases h : st = 0
  · subst h
    simp only [↓reduceIte]
    revert q
    decide
  · simp only [h, ↓reduceIte]

/-- The table of Ncode 0: entry s in the bits 1 * s.. of one number. -/
def tab0 (s : ℕ) : ℕ := 37115535636 >>> (1 * s) % 2 ^ 1

/-- The table of Ncode 1: entry s in the bits 3 * s.. of one number. -/
def tab1 (s : ℕ) : ℕ := 55790440541151672989405289660616 >>> (3 * s) % 2 ^ 3

/-- The table of Ncode 2: entry s in the bits 4 * s.. of one number. -/
def tab2 (s : ℕ) : ℕ := 2455514904457464123659508411556552499660643 >>> (4 * s) % 2 ^ 4

/-- The table of Ncode 3: entry s in the bits 6 * s.. of one number. -/
def tab3 (s : ℕ) : ℕ := 2454999742735692331964662052838034182719932403764092430710793940 >>> (6 * s) % 2 ^ 6

/-- The table of Ncode 4: entry s in the bits 8 * s.. of one number. -/
def tab4 (s : ℕ) : ℕ := 2440519296310520832637127098328692390789199668340475756717261712972352424547945373790 >>> (8 * s) % 2 ^ 8

/-- The table of Ncode 5: entry s in the bits 10 * s.. of one number. -/
def tab5 (s : ℕ) : ℕ := 2563462223949469912700403389355017770883624107418576532699851652436366675311724677449391235991561835931019 >>> (10 * s) % 2 ^ 10

/-- The table of Ncode 6: entry s in the bits 12 * s.. of one number. -/
def tab6 (s : ℕ) : ℕ := 2842130410848698014276211570140970860280037015730281573668875171862351437727726026473548367472289730776658827448986932288964052 >>> (12 * s) % 2 ^ 12

/-- The table of Ncode 7: entry s in the bits 13 * s.. of one number. -/
def tab7 (s : ℕ) : ℕ := 96697563999570287565989702129817202713206786156129080867287984117892145321124804145055724389673501490125490805843328143815189716959417215 >>> (13 * s) % 2 ^ 13

/-- The table of Ncode 8: entry s in the bits 15 * s.. of one number. -/
def tab8 (s : ℕ) : ℕ := 111466675707578635155706820459022135954523088563719317476040535299768268524246583418900574335285491346912865412923241637333831031071544105775497534620779428352 >>> (15 * s) % 2 ^ 15

/-- The table of Ncode 9: entry s in the bits 16 * s.. of one number. -/
def tab9 (s : ℕ) : ℕ := 3814575740835498202640763347992351322466763205533452796584075366677042296082047491766314139514239672413843913656860647222946551979214941758475150147707087480918961396632 >>> (16 * s) % 2 ^ 16

/-- The table of Ncode 10: entry s in the bits 17 * s.. of one number. -/
def tab10 (s : ℕ) : ℕ := 130652037504395441901233873661270063441632989713576895048071653889922301684785309455200644868689247814289307821284518277028186108946002520674036478452037560168294555857335864360491 >>> (17 * s) % 2 ^ 17

/-- The table of Ncode 11: entry s in the bits 18 * s.. of one number. -/
def tab11 (s : ℕ) : ℕ := 4478508408894431273364623559809804082531397364211664464798317654459932284854408026569788368565580831595595955190049492559474700444817061067573985134698956699255529744380357038956277760747303 >>> (18 * s) % 2 ^ 18

/-- The table of Ncode 12: entry s in the bits 19 * s.. of one number. -/
def tab12 (s : ℕ) : ℕ := 153617797614413180441237992858864111622653434954131646790843991779285070277485440994960991778316701240178186433905803153966570135761313492841692720647651174217161607666184220279126057516563465675163590 >>> (19 * s) % 2 ^ 19

/-- The states reachable from a first row. -/
def reach (s : ℕ) : Bool := 68715540919 >>> s % 2 == 1

/-- ltC is the lexicographic order of rows. -/
def lcheck : Bool := (List.range 4).all fun qc => (List.range 4).all fun rc =>
  ltC qc rc == if List.ofFn (dig qc) < List.ofFn (dig rc) then 1 else 0

def crec : Bool := (List.range 36).all fun s =>
  !(reach s) || ((tab12 s : ℤ) == (12 : ℤ) * (tab11 s : ℤ) + (-66 : ℤ) * (tab10 s : ℤ) + (220 : ℤ) * (tab9 s : ℤ) + (-495 : ℤ) * (tab8 s : ℤ) + (792 : ℤ) * (tab7 s : ℤ) + (-924 : ℤ) * (tab6 s : ℤ) + (792 : ℤ) * (tab5 s : ℤ) + (-495 : ℤ) * (tab4 s : ℤ) + (220 : ℤ) * (tab3 s : ℤ) + (-66 : ℤ) * (tab2 s : ℤ) + (12 : ℤ) * (tab1 s : ℤ) + (-1 : ℤ) * (tab0 s : ℤ))

def cclos : Bool := (List.range 36).all fun s => !(reach s) ||
  (List.range 4).all fun qc => !(guardB s qc) || (decide (succS s qc < 36) && reach (succS s qc))

def cinit : Bool := (List.range 4).all fun rc =>
  reach (enc rc (stC 0 rc) 0) && decide (enc rc (stC 0 rc) 0 < 36)

def c0 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab0 s == if (if stOf s = 1 then 1 else 0) + eOf s = 2 then 1 else 0)

def c1 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab1 s ==
    (if guardB s 0 = true then tab0 (succS s 0) else 0) +
    (if guardB s 1 = true then tab0 (succS s 1) else 0) +
    (if guardB s 2 = true then tab0 (succS s 2) else 0) +
    (if guardB s 3 = true then tab0 (succS s 3) else 0))

def c2 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab2 s ==
    (if guardB s 0 = true then tab1 (succS s 0) else 0) +
    (if guardB s 1 = true then tab1 (succS s 1) else 0) +
    (if guardB s 2 = true then tab1 (succS s 2) else 0) +
    (if guardB s 3 = true then tab1 (succS s 3) else 0))

def c3 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab3 s ==
    (if guardB s 0 = true then tab2 (succS s 0) else 0) +
    (if guardB s 1 = true then tab2 (succS s 1) else 0) +
    (if guardB s 2 = true then tab2 (succS s 2) else 0) +
    (if guardB s 3 = true then tab2 (succS s 3) else 0))

def c4 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab4 s ==
    (if guardB s 0 = true then tab3 (succS s 0) else 0) +
    (if guardB s 1 = true then tab3 (succS s 1) else 0) +
    (if guardB s 2 = true then tab3 (succS s 2) else 0) +
    (if guardB s 3 = true then tab3 (succS s 3) else 0))

def c5 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab5 s ==
    (if guardB s 0 = true then tab4 (succS s 0) else 0) +
    (if guardB s 1 = true then tab4 (succS s 1) else 0) +
    (if guardB s 2 = true then tab4 (succS s 2) else 0) +
    (if guardB s 3 = true then tab4 (succS s 3) else 0))

def c6 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab6 s ==
    (if guardB s 0 = true then tab5 (succS s 0) else 0) +
    (if guardB s 1 = true then tab5 (succS s 1) else 0) +
    (if guardB s 2 = true then tab5 (succS s 2) else 0) +
    (if guardB s 3 = true then tab5 (succS s 3) else 0))

def c7 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab7 s ==
    (if guardB s 0 = true then tab6 (succS s 0) else 0) +
    (if guardB s 1 = true then tab6 (succS s 1) else 0) +
    (if guardB s 2 = true then tab6 (succS s 2) else 0) +
    (if guardB s 3 = true then tab6 (succS s 3) else 0))

def c8 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab8 s ==
    (if guardB s 0 = true then tab7 (succS s 0) else 0) +
    (if guardB s 1 = true then tab7 (succS s 1) else 0) +
    (if guardB s 2 = true then tab7 (succS s 2) else 0) +
    (if guardB s 3 = true then tab7 (succS s 3) else 0))

def c9 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab9 s ==
    (if guardB s 0 = true then tab8 (succS s 0) else 0) +
    (if guardB s 1 = true then tab8 (succS s 1) else 0) +
    (if guardB s 2 = true then tab8 (succS s 2) else 0) +
    (if guardB s 3 = true then tab8 (succS s 3) else 0))

def c10 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab10 s ==
    (if guardB s 0 = true then tab9 (succS s 0) else 0) +
    (if guardB s 1 = true then tab9 (succS s 1) else 0) +
    (if guardB s 2 = true then tab9 (succS s 2) else 0) +
    (if guardB s 3 = true then tab9 (succS s 3) else 0))

def c11 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab11 s ==
    (if guardB s 0 = true then tab10 (succS s 0) else 0) +
    (if guardB s 1 = true then tab10 (succS s 1) else 0) +
    (if guardB s 2 = true then tab10 (succS s 2) else 0) +
    (if guardB s 3 = true then tab10 (succS s 3) else 0))

def c12 : Bool := (List.range 36).all fun s =>
  !(reach s) || (tab12 s ==
    (if guardB s 0 = true then tab11 (succS s 0) else 0) +
    (if guardB s 1 = true then tab11 (succS s 1) else 0) +
    (if guardB s 2 = true then tab11 (succS s 2) else 0) +
    (if guardB s 3 = true then tab11 (succS s 3) else 0))

def cval0 : Bool :=
    tab0 (enc 0 (stC 0 0) 0) +
    tab0 (enc 1 (stC 0 1) 0) +
    tab0 (enc 2 (stC 0 2) 0) +
    tab0 (enc 3 (stC 0 3) 0) == 0

def cval1 : Bool :=
    tab1 (enc 0 (stC 0 0) 0) +
    tab1 (enc 1 (stC 0 1) 0) +
    tab1 (enc 2 (stC 0 2) 0) +
    tab1 (enc 3 (stC 0 3) 0) == 3

def cval2 : Bool :=
    tab2 (enc 0 (stC 0 0) 0) +
    tab2 (enc 1 (stC 0 1) 0) +
    tab2 (enc 2 (stC 0 2) 0) +
    tab2 (enc 3 (stC 0 3) 0) == 20

def cval3 : Bool :=
    tab3 (enc 0 (stC 0 0) 0) +
    tab3 (enc 1 (stC 0 1) 0) +
    tab3 (enc 2 (stC 0 2) 0) +
    tab3 (enc 3 (stC 0 3) 0) == 94

def cval4 : Bool :=
    tab4 (enc 0 (stC 0 0) 0) +
    tab4 (enc 1 (stC 0 1) 0) +
    tab4 (enc 2 (stC 0 2) 0) +
    tab4 (enc 3 (stC 0 3) 0) == 395

def cval5 : Bool :=
    tab5 (enc 0 (stC 0 0) 0) +
    tab5 (enc 1 (stC 0 1) 0) +
    tab5 (enc 2 (stC 0 2) 0) +
    tab5 (enc 3 (stC 0 3) 0) == 1492

def cval6 : Bool :=
    tab6 (enc 0 (stC 0 0) 0) +
    tab6 (enc 1 (stC 0 1) 0) +
    tab6 (enc 2 (stC 0 2) 0) +
    tab6 (enc 3 (stC 0 3) 0) == 4991

def cval7 : Bool :=
    tab7 (enc 0 (stC 0 0) 0) +
    tab7 (enc 1 (stC 0 1) 0) +
    tab7 (enc 2 (stC 0 2) 0) +
    tab7 (enc 3 (stC 0 3) 0) == 14848

def cval8 : Bool :=
    tab8 (enc 0 (stC 0 0) 0) +
    tab8 (enc 1 (stC 0 1) 0) +
    tab8 (enc 2 (stC 0 2) 0) +
    tab8 (enc 3 (stC 0 3) 0) == 39832

def cval9 : Bool :=
    tab9 (enc 0 (stC 0 0) 0) +
    tab9 (enc 1 (stC 0 1) 0) +
    tab9 (enc 2 (stC 0 2) 0) +
    tab9 (enc 3 (stC 0 3) 0) == 97835

def cval10 : Bool :=
    tab10 (enc 0 (stC 0 0) 0) +
    tab10 (enc 1 (stC 0 1) 0) +
    tab10 (enc 2 (stC 0 2) 0) +
    tab10 (enc 3 (stC 0 3) 0) == 223015

def cval11 : Bool :=
    tab11 (enc 0 (stC 0 0) 0) +
    tab11 (enc 1 (stC 0 1) 0) +
    tab11 (enc 2 (stC 0 2) 0) +
    tab11 (enc 3 (stC 0 3) 0) == 477126

set_option maxRecDepth 100000 in
theorem tabs : (lcheck && (crec && (cclos && (cinit && (c0 && (c1 && (c2 && (c3 && (c4 && (c5 && (c6 && (c7 && (c8 && (c9 && (c10 && (c11 && (c12 && (cval0 && (cval1 && (cval2 && (cval3 && (cval4 && (cval5 && (cval6 && (cval7 && (cval8 && (cval9 && (cval10 && (cval11))))))))))))))))))))))))))))) = true := by
  decide +kernel

theorem tabs_split : lcheck = true ∧ crec = true ∧ cclos = true ∧ cinit = true ∧ c0 = true ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧ c5 = true ∧ c6 = true ∧ c7 = true ∧ c8 = true ∧ c9 = true ∧ c10 = true ∧ c11 = true ∧ c12 = true ∧ cval0 = true ∧ cval1 = true ∧ cval2 = true ∧ cval3 = true ∧ cval4 = true ∧ cval5 = true ∧ cval6 = true ∧ cval7 = true ∧ cval8 = true ∧ cval9 = true ∧ cval10 = true ∧ cval11 = true := by
  have h := tabs
  simp only [Bool.and_eq_true] at h
  exact h


theorem ltC_eq (q r : Fin 2 → Fin 2) :
    ltC (code q) (code r) = if List.ofFn q < List.ofFn r then 1 else 0 := by
  have h := tabs_split.1
  unfold lcheck at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (code q) (code_lt q) (code r) (code_lt r)
  rw [dig_code, dig_code] at this
  exact this

theorem N_code (m : ℕ) : ∀ (r : Fin 2 → Fin 2) (st e : ℕ), st ≤ 2 → e ≤ 2 →
    N r st e m = Ncode (enc (code r) st e) m := by
  induction m with
  | zero =>
    intro r st e h1 h2
    obtain ⟨d1, d2, d3⟩ := dec_enc (code r) st e h1 h2
    rw [N_zero, Ncode, d2, d3]
  | succ m ih =>
    intro r st e h1 h2
    obtain ⟨d1, d2, d3⟩ := dec_enc (code r) st e h1 h2
    rw [N_succ r st e m h1, sum_dig, Ncode_succ]
    refine sum_congr rfl (fun qc hqc => ?_)
    rw [mem_range] at hqc
    set b := (if List.ofFn (dig qc) < List.ofFn r then 1 else 0) with hb
    have hl : ltC qc (code r) = b := by rw [hb, ← ltC_eq, code_dig qc hqc]
    have hs : stC st qc = stNext st (dig qc) := by rw [← stC_eq, code_dig qc hqc]
    unfold guardB succS
    rw [d1, d2, d3, hl, hs]
    by_cases he : e + b ≤ 2
    · rw [if_pos (decide_eq_true he), ih (dig qc) _ _ (stNext_le st h1 _) he, code_dig qc hqc]
    · rw [if_neg (fun h => he (of_decide_eq_true h)), N_over _ _ _ _ (by omega)]

theorem succ_ok (s qc : ℕ) (hs : s < 36) (hqc : qc < 4) (hg : guardB s qc = true)
    (hr : reach s = true) : succS s qc < 36 ∧ reach (succS s qc) = true := by
  have h := tabs_split.2.2.1
  unfold cclos at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h s hs with h' | h'
  · rw [hr] at h'
    exact absurd h' (by decide)
  · rcases h' qc hqc with h'' | h''
    · rw [hg] at h''
      exact absurd h'' (by decide)
    · exact h''

theorem init_ok (rc : ℕ) (hrc : rc < 4) :
    enc rc (stC 0 rc) 0 < 36 ∧ reach (enc rc (stC 0 rc) 0) = true := by
  have h := tabs_split.2.2.2.1
  unfold cinit at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(h rc hrc).2, (h rc hrc).1⟩

theorem tab_eq0 (s : ℕ) (hs : s < 36) (hr : reach s = true) : Ncode s 0 = tab0 s := by
  have h := tabs_split.2.2.2.2.1
  unfold c0 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  rfl

theorem tab_eq1 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 1 = tab1 s := by
  have h := tabs_split.2.2.2.2.2.1
  unfold c1 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 0 else 0) =
      (if guardB s qc = true then tab0 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq0 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq2 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 2 = tab2 s := by
  have h := tabs_split.2.2.2.2.2.2.1
  unfold c2 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 1 else 0) =
      (if guardB s qc = true then tab1 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq1 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq3 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 3 = tab3 s := by
  have h := tabs_split.2.2.2.2.2.2.2.1
  unfold c3 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 2 else 0) =
      (if guardB s qc = true then tab2 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq2 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq4 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 4 = tab4 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.1
  unfold c4 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 3 else 0) =
      (if guardB s qc = true then tab3 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq3 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq5 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 5 = tab5 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.1
  unfold c5 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 4 else 0) =
      (if guardB s qc = true then tab4 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq4 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq6 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 6 = tab6 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.1
  unfold c6 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 5 else 0) =
      (if guardB s qc = true then tab5 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq5 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq7 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 7 = tab7 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.1
  unfold c7 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 6 else 0) =
      (if guardB s qc = true then tab6 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq6 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq8 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 8 = tab8 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold c8 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 7 else 0) =
      (if guardB s qc = true then tab7 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq7 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq9 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 9 = tab9 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold c9 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 8 else 0) =
      (if guardB s qc = true then tab8 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq8 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq10 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 10 = tab10 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold c10 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 9 else 0) =
      (if guardB s qc = true then tab9 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq9 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq11 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 11 = tab11 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold c11 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 10 else 0) =
      (if guardB s qc = true then tab10 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq10 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq12 (s : ℕ) (hs : s < 36) (hr : reach s = true) :
    Ncode s 12 = tab12 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold c12 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ qc ∈ range 4, (if guardB s qc = true then Ncode (succS s qc) 11 else 0) =
      (if guardB s qc = true then tab11 (succS s qc) else 0) := by
    intro qc hqc
    split_ifs with hg
    · exact tab_eq11 _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1
        (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The recurrence of order 12 of the continuation counts, on every reachable state, from
m = 0. -/
theorem Ncode_rec (m : ℕ) : ∀ s, s < 36 → reach s = true →
    (Ncode s (m + 12) : ℤ) = (12 : ℤ) * (Ncode s (m + 11) : ℤ) + (-66 : ℤ) * (Ncode s (m + 10) : ℤ) + (220 : ℤ) * (Ncode s (m + 9) : ℤ) + (-495 : ℤ) * (Ncode s (m + 8) : ℤ) + (792 : ℤ) * (Ncode s (m + 7) : ℤ) + (-924 : ℤ) * (Ncode s (m + 6) : ℤ) + (792 : ℤ) * (Ncode s (m + 5) : ℤ) + (-495 : ℤ) * (Ncode s (m + 4) : ℤ) + (220 : ℤ) * (Ncode s (m + 3) : ℤ) + (-66 : ℤ) * (Ncode s (m + 2) : ℤ) + (12 : ℤ) * (Ncode s (m + 1) : ℤ) + (-1 : ℤ) * (Ncode s m : ℤ) := by
  induction m with
  | zero =>
    intro s hs hr
    simp only [zero_add]
    rw [tab_eq12 s hs hr, tab_eq11 s hs hr, tab_eq10 s hs hr, tab_eq9 s hs hr, tab_eq8 s hs hr, tab_eq7 s hs hr, tab_eq6 s hs hr, tab_eq5 s hs hr, tab_eq4 s hs hr, tab_eq3 s hs hr, tab_eq2 s hs hr, tab_eq1 s hs hr, tab_eq0 s hs hr]
    have h := tabs_split.2.1
    unfold crec at h
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq] at h
    rcases h s hs with h' | h'
    · rw [hr] at h'
      exact absurd h' (by decide)
    · exact h'
  | succ m ih =>
    intro s hs hr
    show (Ncode s (m + 1 + 12) : ℤ) = (12 : ℤ) * (Ncode s (m + 1 + 11) : ℤ) + (-66 : ℤ) * (Ncode s (m + 1 + 10) : ℤ) + (220 : ℤ) * (Ncode s (m + 1 + 9) : ℤ) + (-495 : ℤ) * (Ncode s (m + 1 + 8) : ℤ) + (792 : ℤ) * (Ncode s (m + 1 + 7) : ℤ) + (-924 : ℤ) * (Ncode s (m + 1 + 6) : ℤ) + (792 : ℤ) * (Ncode s (m + 1 + 5) : ℤ) + (-495 : ℤ) * (Ncode s (m + 1 + 4) : ℤ) + (220 : ℤ) * (Ncode s (m + 1 + 3) : ℤ) + (-66 : ℤ) * (Ncode s (m + 1 + 2) : ℤ) + (12 : ℤ) * (Ncode s (m + 1 + 1) : ℤ) + (-1 : ℤ) * (Ncode s (m + 1) : ℤ)
    rw [Ncode_succ s (m + 12), Ncode_succ s (m + 11), Ncode_succ s (m + 10), Ncode_succ s (m + 9), Ncode_succ s (m + 8), Ncode_succ s (m + 7), Ncode_succ s (m + 6), Ncode_succ s (m + 5), Ncode_succ s (m + 4), Ncode_succ s (m + 3), Ncode_succ s (m + 2), Ncode_succ s (m + 1), Ncode_succ s m]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun qc hqc => ?_)
    split_ifs with hg
    · exact ih _ (succ_ok s qc hs (mem_range.mp hqc) hg hr).1 (succ_ok s qc hs (mem_range.mp hqc) hg hr).2
    · simp

theorem a_code (n : ℕ) : a (n + 1) = ∑ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) n := by
  rw [a_succ, sum_dig]
  refine sum_congr rfl (fun rc hrc => ?_)
  rw [mem_range] at hrc
  rw [N_code n (dig rc) _ 0 (stNext_le 0 (by norm_num) _) (by norm_num), code_dig rc hrc,
    ← stC_eq, code_dig rc hrc]

/-- The recurrence of order 12: a(n) for n >= 13. -/
theorem a_rec (m : ℕ) : (a (m + 13) : ℤ) = (12 : ℤ) * (a (m + 12) : ℤ) + (-66 : ℤ) * (a (m + 11) : ℤ) + (220 : ℤ) * (a (m + 10) : ℤ) + (-495 : ℤ) * (a (m + 9) : ℤ) + (792 : ℤ) * (a (m + 8) : ℤ) + (-924 : ℤ) * (a (m + 7) : ℤ) + (792 : ℤ) * (a (m + 6) : ℤ) + (-495 : ℤ) * (a (m + 5) : ℤ) + (220 : ℤ) * (a (m + 4) : ℤ) + (-66 : ℤ) * (a (m + 3) : ℤ) + (12 : ℤ) * (a (m + 2) : ℤ) + (-1 : ℤ) * (a (m + 1) : ℤ) := by
  rw [a_code (m + 12), a_code (m + 11), a_code (m + 10), a_code (m + 9), a_code (m + 8), a_code (m + 7), a_code (m + 6), a_code (m + 5), a_code (m + 4), a_code (m + 3), a_code (m + 2), a_code (m + 1), a_code m]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl (fun rc hrc => ?_)
  exact Ncode_rec m _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2

theorem v1 : a 1 = 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 0 = tab0 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq0 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval0 at h
  exact beq_iff_eq.mp h

theorem v2 : a 2 = 3 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 1 = tab1 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq1 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval1 at h
  exact beq_iff_eq.mp h

theorem v3 : a 3 = 20 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 2 = tab2 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq2 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval2 at h
  exact beq_iff_eq.mp h

theorem v4 : a 4 = 94 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 3 = tab3 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq3 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval3 at h
  exact beq_iff_eq.mp h

theorem v5 : a 5 = 395 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 4 = tab4 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq4 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval4 at h
  exact beq_iff_eq.mp h

theorem v6 : a 6 = 1492 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 5 = tab5 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq5 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval5 at h
  exact beq_iff_eq.mp h

theorem v7 : a 7 = 4991 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 6 = tab6 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq6 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval6 at h
  exact beq_iff_eq.mp h

theorem v8 : a 8 = 14848 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 7 = tab7 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq7 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval7 at h
  exact beq_iff_eq.mp h

theorem v9 : a 9 = 39832 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 8 = tab8 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq8 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval8 at h
  exact beq_iff_eq.mp h

theorem v10 : a 10 = 97835 := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 9 = tab9 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq9 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval9 at h
  exact beq_iff_eq.mp h

theorem v11 : a 11 = 223015 := by
  rw [show (11 : ℕ) = 10 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 10 = tab10 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq10 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval10 at h
  exact beq_iff_eq.mp h

theorem v12 : a 12 = 477126 := by
  rw [show (12 : ℕ) = 11 + 1 from rfl, a_code]
  have e : ∀ rc ∈ range 4, Ncode (enc rc (stC 0 rc) 0) 11 = tab11 (enc rc (stC 0 rc) 0) := by
    intro rc hrc
    exact tab_eq11 _ (init_ok rc (mem_range.mp hrc)).1 (init_ok rc (mem_range.mp hrc)).2
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  unfold cval11 at h
  exact beq_iff_eq.mp h

/-- Barker's g.f., as A(x) (1 - X) ^ 12 = X ^ 2 * (3 - 16 * X + 52 * X ^ 2 - 73 * X ^ 3 + 41 * X ^ 4 + X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) in Z[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 12 = X ^ 2 * (3 - 16 * X + 52 * X ^ 2 - 73 * X ^ 3 + 41 * X ^ 4 + X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 12 = A - C 12 * (A * X ^ 1) + C 66 * (A * X ^ 2) - C 220 * (A * X ^ 3) + C 495 * (A * X ^ 4) - C 792 * (A * X ^ 5) + C 924 * (A * X ^ 6) - C 792 * (A * X ^ 7) + C 495 * (A * X ^ 8) - C 220 * (A * X ^ 9) + C 66 * (A * X ^ 10) - C 12 * (A * X ^ 11) + A * X ^ 12 := by
    simp only [map_ofNat]; ring
  have e2 : (X ^ 2 * (3 - 16 * X + 52 * X ^ 2 - 73 * X ^ 3 + 41 * X ^ 4 + X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) : ℤ⟦X⟧) = X ^ 2 * C 3 - X ^ 3 * C 16 + X ^ 4 * C 52 - X ^ 5 * C 73 + X ^ 6 * C 41 + X ^ 7 - X ^ 8 * C 10 + X ^ 9 * C 3 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 13 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 13 := ⟨n - 13, by omega⟩
    have h := a_rec q
    simp only [show q + 13 - 1 = q + 12 by omega, 
      show 1 ≤ q + 13 by omega, 
      show ¬ q + 12 = 0 by omega, 
      show q + 13 - 2 = q + 11 by omega, 
      show 2 ≤ q + 13 by omega, 
      show ¬ q + 11 = 0 by omega, 
      show q + 13 - 3 = q + 10 by omega, 
      show 3 ≤ q + 13 by omega, 
      show ¬ q + 10 = 0 by omega, 
      show q + 13 - 4 = q + 9 by omega, 
      show 4 ≤ q + 13 by omega, 
      show ¬ q + 9 = 0 by omega, 
      show q + 13 - 5 = q + 8 by omega, 
      show 5 ≤ q + 13 by omega, 
      show ¬ q + 8 = 0 by omega, 
      show q + 13 - 6 = q + 7 by omega, 
      show 6 ≤ q + 13 by omega, 
      show ¬ q + 7 = 0 by omega, 
      show q + 13 - 7 = q + 6 by omega, 
      show 7 ≤ q + 13 by omega, 
      show ¬ q + 6 = 0 by omega, 
      show q + 13 - 8 = q + 5 by omega, 
      show 8 ≤ q + 13 by omega, 
      show ¬ q + 5 = 0 by omega, 
      show q + 13 - 9 = q + 4 by omega, 
      show 9 ≤ q + 13 by omega, 
      show ¬ q + 4 = 0 by omega, 
      show q + 13 - 10 = q + 3 by omega, 
      show 10 ≤ q + 13 by omega, 
      show ¬ q + 3 = 0 by omega, 
      show q + 13 - 11 = q + 2 by omega, 
      show 11 ≤ q + 13 by omega, 
      show ¬ q + 2 = 0 by omega, 
      show q + 13 - 12 = q + 1 by omega, 
      show 12 ≤ q + 13 by omega, 
      show ¬ q + 1 = 0 by omega, 
      show ¬ q + 13 = 0 by omega, 
      show ¬ q + 13 = 2 by omega, 
      show ¬ q + 13 = 3 by omega, 
      show ¬ q + 13 = 4 by omega, 
      show ¬ q + 13 = 5 by omega, 
      show ¬ q + 13 = 6 by omega, 
      show ¬ q + 13 = 7 by omega, 
      show ¬ q + 13 = 8 by omega, 
      show ¬ q + 13 = 9 by omega,
      if_true, if_false]
    rw [h]
    ring

/-- Barker's recurrence, for n > 12. -/
theorem recurrence (n : ℕ) (hn : 12 < n) : (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  simp only [show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega, show m + 13 - 3 = m + 10 by omega, show m + 13 - 4 = m + 9 by omega, show m + 13 - 5 = m + 8 by omega, show m + 13 - 6 = m + 7 by omega, show m + 13 - 7 = m + 6 by omega, show m + 13 - 8 = m + 5 by omega, show m + 13 - 9 = m + 4 by omega, show m + 13 - 10 = m + 3 by omega, show m + 13 - 11 = m + 2 by omega, show m + 13 - 12 = m + 1 by omega]
  linear_combination a_rec m

/-- Controls: the entry's data a(1..13). -/
theorem controls : a 1 = 0 ∧ a 2 = 3 ∧ a 3 = 20 ∧ a 4 = 94 ∧ a 5 = 395 ∧ a 6 = 1492 ∧ a 7 = 4991 ∧ a 8 = 14848 ∧ a 9 = 39832 ∧ a 10 = 97835 ∧ a 11 = 223015 ∧ a 12 = 477126 ∧ a 13 = 966849 := by
  have v13 : a 13 = 966849 := by
    have h : (a 13 : ℤ) = (12 : ℤ) * (a 12 : ℤ) + (-66 : ℤ) * (a 11 : ℤ) + (220 : ℤ) * (a 10 : ℤ) + (-495 : ℤ) * (a 9 : ℤ) + (792 : ℤ) * (a 8 : ℤ) + (-924 : ℤ) * (a 7 : ℤ) + (792 : ℤ) * (a 6 : ℤ) + (-495 : ℤ) * (a 5 : ℤ) + (220 : ℤ) * (a 4 : ℤ) + (-66 : ℤ) * (a 3 : ℤ) + (12 : ℤ) * (a 2 : ℤ) + (-1 : ℤ) * (a 1 : ℤ) := a_rec 0
    rw [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 12 = X ^ 2 * (3 - 16 * X + 52 * X ^ 2 - 73 * X ^ 3 + 41 * X ^ 4 + X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a278319

theorem OMA.solution : type_of% @OMA.S_oeis_a278319.main :=
  OMA.S_oeis_a278319.conjecture
