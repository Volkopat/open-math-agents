import OMAStatements.S_oeis_a268052

namespace OMA.S_oeis_a268052

open PowerSeries Finset




/-! ## The scan by rows -/

/-- Column j of y introduces its new values in order after L j values were introduced above y. -/
def colsL {m : ℕ} (L : Fin 4 → ℕ) (y : Fin m → Fin 4 → Fin 3) : Prop :=
  ∀ i j, y i j ≠ 0 → (y i j).val ≤ L j ∨ ∃ i', i' < i ∧ (y i' j).val + 1 = (y i j).val

instance {m : ℕ} (L : Fin 4 → ℕ) (y : Fin m → Fin 4 → Fin 3) : Decidable (colsL L y) := by
  unfold colsL
  infer_instance

instance (m : ℕ) (y : Fin m → Fin 4 → Fin 3) : Decidable (rowsNew m y) := by
  unfold rowsNew
  infer_instance

theorem colsNew_iff (n : ℕ) (x : Fin n → Fin 4 → Fin 3) : colsNew n x ↔ colsL (fun _ => 0) x := by
  unfold colsNew colsL
  refine forall_congr' (fun i => forall_congr' (fun j => imp_congr_right (fun h => ?_)))
  have hx : ¬ (x i j).val ≤ 0 := fun h' => h (Fin.ext (Nat.le_zero.mp h'))
  constructor
  · exact Or.inr
  · rintro (h' | h')
    · exact absurd h' hx
    · exact h'

/-- The row r introduces its new values in order. -/
def rowNew (r : Fin 4 → Fin 3) : Prop := ∀ j, r j ≠ 0 → ∃ j', j' < j ∧ (r j').val + 1 = (r j).val

instance (r : Fin 4 → Fin 3) : Decidable (rowNew r) := by
  unfold rowNew
  infer_instance

/-- The column limits after the row r. -/
def Lnext (L : Fin 4 → ℕ) (r : Fin 4 → Fin 3) : Fin 4 → ℕ := fun j => max (L j) ((r j).val + 1)

theorem rowsNew_cons (m : ℕ) (r : Fin 4 → Fin 3) (y : Fin m → Fin 4 → Fin 3) :
    rowsNew (m + 1) (Fin.cons r y : Fin (m + 1) → Fin 4 → Fin 3) ↔ rowNew r ∧ rowsNew m y := by
  unfold rowsNew rowNew
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem colsL_cons {m : ℕ} (L : Fin 4 → ℕ) (r : Fin 4 → Fin 3) (y : Fin m → Fin 4 → Fin 3) :
    colsL L (Fin.cons r y : Fin (m + 1) → Fin 4 → Fin 3) ↔
      (∀ j, (r j).val ≤ L j) ∧ colsL (Lnext L r) y := by
  unfold colsL Lnext
  constructor
  · intro H
    have hr : ∀ j, (r j).val ≤ L j := by
      intro j
      by_cases hz : r j = 0
      · rw [hz]
        exact Nat.zero_le _
      · rcases H 0 j (by simpa using hz) with h | ⟨i', hi', _⟩
        · simpa using h
        · exact absurd hi' (Fin.not_lt_zero _)
    refine ⟨hr, fun i j hne => ?_⟩
    rcases H i.succ j (by simpa using hne) with h | ⟨i', hi', hv⟩
    · left
      simp only [Fin.cons_succ] at h
      omega
    · cases i' using Fin.cases with
      | zero =>
        left
        simp only [Fin.cons_zero, Fin.cons_succ] at hv
        omega
      | succ i2 =>
        right
        exact ⟨i2, Fin.succ_lt_succ_iff.mp hi', by simpa using hv⟩
  · rintro ⟨hr, Hy⟩ i j hne
    cases i using Fin.cases with
    | zero =>
      left
      simpa using hr j
    | succ i1 =>
      simp only [Fin.cons_succ] at hne ⊢
      rcases Hy i1 j hne with h | ⟨i2, hi2, hv⟩
      · by_cases h1 : (y i1 j).val ≤ L j
        · exact Or.inl h1
        · right
          refine ⟨0, Fin.succ_pos i1, ?_⟩
          simp only [Fin.cons_zero]
          have := hr j
          omega
      · right
        exact ⟨i2.succ, Fin.succ_lt_succ_iff.mpr hi2, by simpa using hv⟩

/-- The ways to add m rows below column limits L. -/
noncomputable def N (L : Fin 4 → ℕ) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 4 → Fin 3, if rowsNew m y ∧ colsL L y then 1 else 0

theorem sum_cons {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 1) → α) → ℕ) :
    ∑ y : Fin (m + 1) → α, f y = ∑ r : α, ∑ y : Fin m → α, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem N_zero (L : Fin 4 → ℕ) : N L 0 = 1 := by
  have key : ∀ y : Fin 0 → Fin 4 → Fin 3, (if rowsNew 0 y ∧ colsL L y then 1 else 0) = 1 := by
    intro y
    have h1 : rowsNew 0 y := fun i => i.elim0
    have h2 : colsL L y := fun i => i.elim0
    simp [h1, h2]
  unfold N
  rw [Fintype.sum_unique]
  exact key _

theorem N_succ (L : Fin 4 → ℕ) (m : ℕ) : N L (m + 1) = ∑ r : Fin 4 → Fin 3,
    if rowNew r ∧ (∀ j, (r j).val ≤ L j) then N (Lnext L r) m else 0 := by
  unfold N
  rw [sum_cons]
  refine sum_congr rfl (fun r _ => ?_)
  by_cases hr : rowNew r ∧ (∀ j, (r j).val ≤ L j)
  · rw [if_pos hr]
    refine sum_congr rfl (fun y _ => ?_)
    simp only [rowsNew_cons, colsL_cons, hr.1, hr.2, true_and, implies_true]
  · rw [if_neg hr]
    refine sum_eq_zero (fun y _ => ?_)
    rw [if_neg]
    rw [rowsNew_cons, colsL_cons]
    exact fun h => hr ⟨h.1.1, h.2.1⟩

theorem a_eq (n : ℕ) : a n = N (fun _ => 0) n := by
  unfold a N
  rw [← card_filter, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, colsNew_iff]

/-! ## Codes -/

/-- The row with code c: column j holds the digit of 3 ^ j. -/
def dig (c : ℕ) : Fin 4 → Fin 3 := fun j => ⟨c / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The code of the row r. -/
def code (r : Fin 4 → Fin 3) : ℕ := (r 0).val + 3 * (r 1).val + 9 * (r 2).val + 27 * (r 3).val

theorem dig_code (r : Fin 4 → Fin 3) : dig (code r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  fin_cases j <;> simp [dig, code] <;> omega

theorem code_lt (r : Fin 4 → Fin 3) : code r < 81 := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  unfold code
  omega

theorem code_dig (c : ℕ) (h : c < 81) : code (dig c) = c := by
  simp [code, dig]
  omega

theorem sum_dig (g : (Fin 4 → Fin 3) → ℕ) : ∑ r, g r = ∑ c ∈ range 81, g (dig c) := by
  rw [← (finFunctionFinEquiv (m := 3) (n := 4)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun c => g (dig c)) _

/-- The code of column limits L in base 4. -/
def lcode (L : Fin 4 → ℕ) : ℕ := L 0 + 4 * L 1 + 16 * L 2 + 64 * L 3

/-- The codes of the rows that introduce their values in order. -/
def rowsL : List ℕ := [0, 3, 9, 12, 21, 27, 30, 36, 39, 48, 57, 63, 66, 75]

theorem rowsL_nodup : rowsL.Nodup := by
  decide

/-- The row with code rc fits under the limits with code s. -/
def fitC (s rc : ℕ) : Bool := decide (rc % 3 ≤ s % 4 ∧ rc / 3 % 3 ≤ s / 4 % 4 ∧ rc / 9 % 3 ≤ s / 16 % 4 ∧ rc / 27 % 3 ≤ s / 64 % 4)

/-- The limits after the row with code rc. -/
def succC (s rc : ℕ) : ℕ := max (s % 4) (rc % 3 + 1) + 4 * max (s / 4 % 4) (rc / 3 % 3 + 1) + 16 * max (s / 16 % 4) (rc / 9 % 3 + 1) + 64 * max (s / 64 % 4) (rc / 27 % 3 + 1)

def guardB (s rc : ℕ) : Bool := fitC s rc

/-- The counts on limit codes. -/
def Ncode : ℕ → ℕ → ℕ
  | _, 0 => 1
  | s, m + 1 => ∑ rc ∈ rowsL.toFinset, if guardB s rc = true then Ncode (succC s rc) m else 0

theorem Ncode_succ (s m : ℕ) : Ncode s (m + 1) =
    ∑ rc ∈ rowsL.toFinset, if guardB s rc = true then Ncode (succC s rc) m else 0 := rfl

theorem forall_fin (P : Fin 4 → Prop) : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j <;> assumption

theorem code_digits (r : Fin 4 → Fin 3) : code r % 3 = (r 0).val ∧ code r / 3 % 3 = (r 1).val ∧ code r / 9 % 3 = (r 2).val ∧ code r / 27 % 3 = (r 3).val := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  unfold code
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem lcode_digits (L : Fin 4 → ℕ) (hL : ∀ j, L j ≤ 3) : lcode L % 4 = L 0 ∧ lcode L / 4 % 4 = L 1 ∧ lcode L / 16 % 4 = L 2 ∧ lcode L / 64 % 4 = L 3 := by
  have := hL
  rw [forall_fin] at this
  unfold lcode
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem fit_eq (L : Fin 4 → ℕ) (hL : ∀ j, L j ≤ 3) (r : Fin 4 → Fin 3) :
    fitC (lcode L) (code r) = decide (∀ j, (r j).val ≤ L j) := by
  obtain ⟨d0, d1, d2, d3⟩ := code_digits r
  obtain ⟨l0, l1, l2, l3⟩ := lcode_digits L hL
  unfold fitC
  rw [d0, d1, d2, d3, l0, l1, l2, l3, decide_eq_decide, forall_fin]

theorem succ_eq (L : Fin 4 → ℕ) (hL : ∀ j, L j ≤ 3) (r : Fin 4 → Fin 3) :
    succC (lcode L) (code r) = lcode (Lnext L r) := by
  obtain ⟨d0, d1, d2, d3⟩ := code_digits r
  obtain ⟨l0, l1, l2, l3⟩ := lcode_digits L hL
  unfold succC
  rw [d0, d1, d2, d3, l0, l1, l2, l3]
  rfl

theorem Lnext_le (L : Fin 4 → ℕ) (hL : ∀ j, L j ≤ 3) (r : Fin 4 → Fin 3) : ∀ j, Lnext L r j ≤ 3 := by
  intro j
  have := hL j
  have := (r j).isLt
  unfold Lnext
  omega

/-- The table of Ncode 0: entry s in the bits 1 * s.. of one number. -/
def tab0 (s : ℕ) : ℕ := 904640363588144290080851645009148431019412844199375176856350994610360680449 >>> (1 * s) % 2 ^ 1

/-- The table of Ncode 1: entry s in the bits 4 * s.. of one number. -/
def tab1 (s : ℕ) : ℕ := 9375700312879839058806984667062411021784746203867612651552812135267822341908275739026041899509192727867051897227751480579936230617885427577763657843060161776527469283080869961704983300027186586195601561342922090062815193753918610378018225258042603794813123858550688648840760728333719702533528751177729 >>> (4 * s) % 2 ^ 4

/-- The table of Ncode 2: entry s in the bits 8 * s.. of one number. -/
def tab2 (s : ℕ) : ℕ := 87903756356935112011576291965166276901967024988759962397990764413355809266114010064892077454424863132029043205540969184703351407569598612090238294571526807535236484946499458275938000866701375418088014591026360054554026948911093460988023373923947951178429361044844661005048550917113674573014036148289951959769223468618083069816030103963333101725698094230135826764050512267270470498631861336313966061497509275361381886333316814230481822492448947774343657673442950803628270502817430131448906964054573470580489554777579564343550764920806522478459944942801924344516872193559003603404256539159705999428812808 >>> (8 * s) % 2 ^ 8

/-- The table of Ncode 3: entry s in the bits 12 * s.. of one number. -/
def tab3 (s : ℕ) : ℕ := 824159275979029671264696626863136938519072004370574149429386147713815964339256341251189866442464466256596201037811176584281959330311703236564138426860496603047312171953055262580648779827354796401534188582849018449969609990856623151500054064023126990407969870272423394725479159572744680719970143566981657803776432420459607760099474257348566426300309866883287413791471496707901383948994600989677820088766179897524893487560088271225744866011574777568997148442281153008511263374139543897528037100412885088365227654691225249530014227674407257140761502897808069840353588005668077861749187736264962303174466497858093751644305195668835642784440999899972248878927955492151698824361108741311703121446631491751814354645423051032737495271177088410186234443072427078962521567433745679513906485293356000034079450970032386949467548721659153932251207747643066496397070515375547310074012135795994501868784613904504324182 >>> (12 * s) % 2 ^ 12

/-- The table of Ncode 4: entry s in the bits 16 * s.. of one number. -/
def tab4 (s : ℕ) : ℕ := 7727070381659410115599217275297987946789135756310908004374563193433736290036481592424461303405992906886654534361930502567990142571100379277587859776118800138073851697239743193406464956662026744556689042891741252996128476629013032252532304804721381476557374158459728633339148633361384689849986260753894684439042765177018880570201970652667001512040919787351130043554977937013122177578734847933100421259035075868564019728351931199923501943813722638676992344175395686089032247487021112207952688383531488667313639730604080939411643027833554839724926469239317125297721604091572447867613337891573427480386250010230275294814817096598338754303322658839569413694425592227135431279310982129192632010905212929777609623988822343416602322542606603679933986472616981050384817013656758251155002051371821781958952927040306734116416917925038744212033656084036595618946625916804321605149881350699943855724503083345967830270059888798927863868252029022596736739734715205318505615660411958441593350069398994326022377708621013517540344594014670206377351521714390403894591784484939229116203101787960737703484218223872526298530798194626651855955258280802742682196940345189868146439795194060801362743546004399059747731134654448698 >>> (16 * s) % 2 ^ 16

/-- The limit codes reachable from the empty array. -/
def reach (s : ℕ) : Bool := 904640363588144290080851645009148431019412844199375176856350994610360680449 >>> s % 2 == 1

/-- rowsL lists exactly the row codes whose rows introduce their values in order. -/
def rcheck : Bool := (List.range 81).all fun rc => decide (rc ∈ rowsL) == decide (rowNew (dig rc))

def rbound : Bool := rowsL.all fun rc => decide (rc < 81)

def crec : Bool := (List.range 256).all fun s =>
  !(reach s) || ((tab4 s : ℤ) == (21 : ℤ) * (tab3 s : ℤ) + (-108 : ℤ) * (tab2 s : ℤ) + (140 : ℤ) * (tab1 s : ℤ))

def cclos : Bool := (List.range 256).all fun s => !(reach s) ||
  rowsL.all fun rc => !(guardB s rc) || (decide (succC s rc < 256) && reach (succC s rc))

def c0 : Bool := (List.range 256).all fun s => !(reach s) || tab0 s == 1

def c1 : Bool := (List.range 256).all fun s =>
  !(reach s) || (tab1 s ==
    (rowsL.map fun rc => if guardB s rc = true then tab0 (succC s rc) else 0).sum)

def c2 : Bool := (List.range 256).all fun s =>
  !(reach s) || (tab2 s ==
    (rowsL.map fun rc => if guardB s rc = true then tab1 (succC s rc) else 0).sum)

def c3 : Bool := (List.range 256).all fun s =>
  !(reach s) || (tab3 s ==
    (rowsL.map fun rc => if guardB s rc = true then tab2 (succC s rc) else 0).sum)

def c4 : Bool := (List.range 256).all fun s =>
  !(reach s) || (tab4 s ==
    (rowsL.map fun rc => if guardB s rc = true then tab3 (succC s rc) else 0).sum)

set_option maxRecDepth 100000 in
theorem tabs : (rcheck && (rbound && (crec && (cclos && (c0 && (c1 && (c2 && (c3 && (c4))))))))) = true := by
  decide +kernel

theorem tabs_split : rcheck = true ∧ rbound = true ∧ crec = true ∧ cclos = true ∧ c0 = true ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true := by
  have h := tabs
  simp only [Bool.and_eq_true] at h
  exact h


theorem rows_iff (rc : ℕ) (h : rc < 81) : rc ∈ rowsL ↔ rowNew (dig rc) := by
  have hc := tabs_split.1
  unfold rcheck at hc
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_decide] at hc
  exact hc rc h

theorem rows_lt (rc : ℕ) (h : rc ∈ rowsL) : rc < 81 := by
  have hc := tabs_split.2.1
  unfold rbound at hc
  rw [List.all_eq_true] at hc
  exact of_decide_eq_true (hc rc h)

theorem N_code (m : ℕ) : ∀ L : Fin 4 → ℕ, (∀ j, L j ≤ 3) → N L m = Ncode (lcode L) m := by
  induction m with
  | zero =>
    intro L _
    rw [N_zero]
    rfl
  | succ m ih =>
    intro L hL
    rw [N_succ, sum_dig, Ncode_succ]
    have hsub : ∑ rc ∈ rowsL.toFinset, (if rowNew (dig rc) ∧ (∀ j, (dig rc j).val ≤ L j) then
          N (Lnext L (dig rc)) m else 0) =
        ∑ rc ∈ range 81, (if rowNew (dig rc) ∧ (∀ j, (dig rc j).val ≤ L j) then
          N (Lnext L (dig rc)) m else 0) := by
      apply Finset.sum_subset
      · intro rc hrc
        exact mem_range.mpr (rows_lt rc (List.mem_toFinset.mp hrc))
      · intro rc hrc hn
        rw [mem_range] at hrc
        rw [if_neg]
        intro h
        exact hn (List.mem_toFinset.mpr ((rows_iff rc hrc).mpr h.1))
    rw [← hsub]
    refine sum_congr rfl (fun rc hrc => ?_)
    have hrow := (rows_iff rc (rows_lt rc (List.mem_toFinset.mp hrc))).mp (List.mem_toFinset.mp hrc)
    have hlt := rows_lt rc (List.mem_toFinset.mp hrc)
    have hg : guardB (lcode L) rc = decide (rowNew (dig rc) ∧ ∀ j, (dig rc j).val ≤ L j) := by
      unfold guardB
      rw [← code_dig rc hlt, fit_eq L hL, dig_code]
      simp [hrow]
    rw [hg]
    by_cases h : rowNew (dig rc) ∧ ∀ j, (dig rc j).val ≤ L j
    · rw [if_pos h, if_pos (decide_eq_true h), ih _ (Lnext_le L hL _)]
      rw [← succ_eq L hL, code_dig rc hlt]
    · rw [if_neg h, if_neg (by simpa using h)]

theorem succ_ok (s rc : ℕ) (hs : s < 256) (hrc : rc ∈ rowsL.toFinset) (hg : guardB s rc = true)
    (hr : reach s = true) : succC s rc < 256 ∧ reach (succC s rc) = true := by
  have h := tabs_split.2.2.2.1
  unfold cclos at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h s hs with h' | h'
  · rw [hr] at h'
    exact absurd h' (by decide)
  · rcases h' rc (List.mem_toFinset.mp hrc) with h'' | h''
    · rw [hg] at h''
      exact absurd h'' (by decide)
    · exact h''

theorem succ_lt (s rc : ℕ) (hs : s < 256) (hrc : rc ∈ rowsL.toFinset) (hg : guardB s rc = true)
    (hr : reach s = true) : succC s rc < 256 := (succ_ok s rc hs hrc hg hr).1

theorem reach_succ (s rc : ℕ) (hs : s < 256) (hrc : rc ∈ rowsL.toFinset) (hg : guardB s rc = true)
    (hr : reach s = true) : reach (succC s rc) = true := (succ_ok s rc hs hrc hg hr).2

theorem reach0 : reach 0 = true := by decide

theorem tab_eq0 (s : ℕ) (hs : s < 256) (hr : reach s = true) : Ncode s 0 = tab0 s := by
  have h := tabs_split.2.2.2.2.1
  unfold c0 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  rfl

theorem tab_eq1 (s : ℕ) (hs : s < 256) (hr : reach s = true) :
    Ncode s 1 = tab1 s := by
  have h := tabs_split.2.2.2.2.2.1
  unfold c1 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ, ← List.sum_toFinset _ rowsL_nodup]
  refine sum_congr rfl (fun rc hrc => ?_)
  split_ifs with hg
  · exact tab_eq0 _ (succ_lt s rc hs hrc hg hr) (reach_succ s rc hs hrc hg hr)
  · rfl

theorem tab_eq2 (s : ℕ) (hs : s < 256) (hr : reach s = true) :
    Ncode s 2 = tab2 s := by
  have h := tabs_split.2.2.2.2.2.2.1
  unfold c2 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ, ← List.sum_toFinset _ rowsL_nodup]
  refine sum_congr rfl (fun rc hrc => ?_)
  split_ifs with hg
  · exact tab_eq1 _ (succ_lt s rc hs hrc hg hr) (reach_succ s rc hs hrc hg hr)
  · rfl

theorem tab_eq3 (s : ℕ) (hs : s < 256) (hr : reach s = true) :
    Ncode s 3 = tab3 s := by
  have h := tabs_split.2.2.2.2.2.2.2.1
  unfold c3 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ, ← List.sum_toFinset _ rowsL_nodup]
  refine sum_congr rfl (fun rc hrc => ?_)
  split_ifs with hg
  · exact tab_eq2 _ (succ_lt s rc hs hrc hg hr) (reach_succ s rc hs hrc hg hr)
  · rfl

theorem tab_eq4 (s : ℕ) (hs : s < 256) (hr : reach s = true) :
    Ncode s 4 = tab4 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2
  unfold c4 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ, ← List.sum_toFinset _ rowsL_nodup]
  refine sum_congr rfl (fun rc hrc => ?_)
  split_ifs with hg
  · exact tab_eq3 _ (succ_lt s rc hs hrc hg hr) (reach_succ s rc hs hrc hg hr)
  · rfl

/-- The recurrence of order 3 of the counts, on every reachable state, from m = 1. -/
theorem Ncode_rec (m : ℕ) : ∀ s, s < 256 → reach s = true →
    (Ncode s (m + 4) : ℤ) = (21 : ℤ) * (Ncode s (m + 3) : ℤ) + (-108 : ℤ) * (Ncode s (m + 2) : ℤ) + (140 : ℤ) * (Ncode s (m + 1) : ℤ) := by
  induction m with
  | zero =>
    intro s hs hr
    simp only [zero_add]
    rw [tab_eq4 s hs hr, tab_eq3 s hs hr, tab_eq2 s hs hr, tab_eq1 s hs hr]
    have h := tabs_split.2.2.1
    unfold crec at h
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq] at h
    rcases h s hs with h' | h'
    · rw [hr] at h'
      exact absurd h' (by decide)
    · exact h'
  | succ m ih =>
    intro s hs hr
    show (Ncode s (m + 1 + 4) : ℤ) = (21 : ℤ) * (Ncode s (m + 1 + 3) : ℤ) + (-108 : ℤ) * (Ncode s (m + 1 + 2) : ℤ) + (140 : ℤ) * (Ncode s (m + 1 + 1) : ℤ)
    rw [Ncode_succ s (m + 4), Ncode_succ s (m + 3), Ncode_succ s (m + 2), Ncode_succ s (m + 1)]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun rc hrc => ?_)
    split_ifs with hg
    · exact ih _ (succ_lt s rc hs hrc hg hr) (reach_succ s rc hs hrc hg hr)
    · simp

theorem a_code (n : ℕ) : a n = Ncode 0 n := by
  rw [a_eq, N_code n _ (fun _ => by norm_num)]
  rfl

/-- The recurrence of order 3: a(n) for n >= 4. -/
theorem a_rec (m : ℕ) : (a (m + 4) : ℤ) = (21 : ℤ) * (a (m + 3) : ℤ) + (-108 : ℤ) * (a (m + 2) : ℤ) + (140 : ℤ) * (a (m + 1) : ℤ) := by
  simp only [a_code]
  exact Ncode_rec m 0 (by norm_num) reach0

theorem v1 : a 1 = 1 := by
  rw [a_code, tab_eq1 0 (by norm_num) reach0]
  rfl

theorem v2 : a 2 = 8 := by
  rw [a_code, tab_eq2 0 (by norm_num) reach0]
  rfl

theorem v3 : a 3 = 86 := by
  rw [a_code, tab_eq3 0 (by norm_num) reach0]
  rfl

/-- Barker's g.f., as A(x) ((1 - 2 * X) * (1 - 5 * X) * (1 - 14 * X)) = X * (1 - 13 * X + 26 * X ^ 2) in Z[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - 2 * X) * (1 - 5 * X) * (1 - 14 * X)) = X * (1 - 13 * X + 26 * X ^ 2) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((1 - 2 * X) * (1 - 5 * X) * (1 - 14 * X)) = A - C 21 * (A * X ^ 1) + C 108 * (A * X ^ 2) - C 140 * (A * X ^ 3) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (1 - 13 * X + 26 * X ^ 2) : ℤ⟦X⟧) = X ^ 1 - X ^ 2 * C 13 + X ^ 3 * C 26 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
    have h := a_rec q
    simp only [show q + 4 - 1 = q + 3 by omega, 
      show 1 ≤ q + 4 by omega, 
      show ¬ q + 3 = 0 by omega, 
      show q + 4 - 2 = q + 2 by omega, 
      show 2 ≤ q + 4 by omega, 
      show ¬ q + 2 = 0 by omega, 
      show q + 4 - 3 = q + 1 by omega, 
      show 3 ≤ q + 4 by omega, 
      show ¬ q + 1 = 0 by omega, 
      show ¬ q + 4 = 0 by omega, 
      show ¬ q + 4 = 1 by omega, 
      show ¬ q + 4 = 2 by omega, 
      show ¬ q + 4 = 3 by omega,
      if_true, if_false]
    rw [h]
    ring

/-- Barker's closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (105 * 2 ^ n + 196 * 5 ^ n + 25 * 2 ^ (1 + n) * 7 ^ n) / 1890 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · rw [v1]
        push_cast
        ring
      · rw [v2]
        push_cast
        ring
      · rw [v3]
        push_cast
        ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hR : (a (k + 4) : ℚ) = (21 : ℚ) * (a (k + 3) : ℚ) + (-108 : ℚ) * (a (k + 2) : ℚ) + (140 : ℚ) * (a (k + 1) : ℚ) := by exact_mod_cast a_rec k
      rw [hR, ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
      push_cast
      ring

/-- Controls: the entry's data a(1..10). -/
theorem controls : a 1 = 1 ∧ a 2 = 8 ∧ a 3 = 86 ∧ a 4 = 1082 ∧ a 5 = 14554 ∧ a 6 = 200818 ∧ a 7 = 2796826 ∧ a 8 = 39082562 ∧ a 9 = 546791114 ∧ a 10 = 7653252338 := by
  have v4 : a 4 = 1082 := by
    have h : (a 4 : ℤ) = (21 : ℤ) * (a 3 : ℤ) + (-108 : ℤ) * (a 2 : ℤ) + (140 : ℤ) * (a 1 : ℤ) := a_rec 0
    rw [v3, v2, v1] at h
    omega
  have v5 : a 5 = 14554 := by
    have h : (a 5 : ℤ) = (21 : ℤ) * (a 4 : ℤ) + (-108 : ℤ) * (a 3 : ℤ) + (140 : ℤ) * (a 2 : ℤ) := a_rec 1
    rw [v4, v3, v2] at h
    omega
  have v6 : a 6 = 200818 := by
    have h : (a 6 : ℤ) = (21 : ℤ) * (a 5 : ℤ) + (-108 : ℤ) * (a 4 : ℤ) + (140 : ℤ) * (a 3 : ℤ) := a_rec 2
    rw [v5, v4, v3] at h
    omega
  have v7 : a 7 = 2796826 := by
    have h : (a 7 : ℤ) = (21 : ℤ) * (a 6 : ℤ) + (-108 : ℤ) * (a 5 : ℤ) + (140 : ℤ) * (a 4 : ℤ) := a_rec 3
    rw [v6, v5, v4] at h
    omega
  have v8 : a 8 = 39082562 := by
    have h : (a 8 : ℤ) = (21 : ℤ) * (a 7 : ℤ) + (-108 : ℤ) * (a 6 : ℤ) + (140 : ℤ) * (a 5 : ℤ) := a_rec 4
    rw [v7, v6, v5] at h
    omega
  have v9 : a 9 = 546791114 := by
    have h : (a 9 : ℤ) = (21 : ℤ) * (a 8 : ℤ) + (-108 : ℤ) * (a 7 : ℤ) + (140 : ℤ) * (a 6 : ℤ) := a_rec 5
    rw [v8, v7, v6] at h
    omega
  have v10 : a 10 = 7653252338 := by
    have h : (a 10 : ℤ) = (21 : ℤ) * (a 9 : ℤ) + (-108 : ℤ) * (a 8 : ℤ) + (140 : ℤ) * (a 7 : ℤ) := a_rec 6
    rw [v9, v8, v7] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - 2 * X) * (1 - 5 * X) * (1 - 14 * X)) = X * (1 - 13 * X + 26 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (105 * 2 ^ n + 196 * 5 ^ n + 25 * 2 ^ (1 + n) * 7 ^ n) / 1890 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a268052

theorem OMA.solution : type_of% @OMA.S_oeis_a268052.main :=
  OMA.S_oeis_a268052.conjecture
