import OMAStatements.S_oeis_a282955
import Mathlib

/-!
The x-axis word of Rule 533 is read off a finite invariant of the whole automaton.
By the symmetries of the square every state is determined by the wedge x ≥ y ≥ 0, which I
index by u = x - y, v = y and e = t - x - y. A table over eventually periodic caps of
(u, v, e) gives each wedge cell a value 0, 1 or 2 (unknown). The kernel checks that the
table is closed under one step of the rule, where on the diagonal and the axis the reflected
neighbours carry one shared bit, and that the axis entries are all known. The axis digits are
then eventually periodic in position and in time, which forces a fixed recurrence of order
8; the conjectured recurrence follows from it and finitely many checked values.
The wedge folding with shared bits on the symmetry lines follows the method of
Aryan-Poonacha (pull request 29570, Rule 533 binary word); the certificate search, the
table and the recurrence argument here are my own.
-/

namespace CAR533right
open OMA.S_oeis_a282955

def cap (a P x : ℤ) : ℤ := if x ≤ a then x else a + 1 + (x - a - 1) % P
def scap (a b P d : ℤ) : ℤ := if d < a then a - 1 - (a - 1 - d) % P else cap b P d

def tbl (U V E : ℤ) : ℕ :=
  (56962336984305703796279970875481657706669909637013100070067285281376751307691551215765890467322123615950079064224579571027708753992202215960923503108561853435282360193201681500651277392244645888339159457504396911714905454156435070785642313668716491399048796074990632828954908484120929376783876489495715181561409846258724624228401801441454924884043891306148322535704926027355874392931309981929800565622060174916387986757952886772124629163349584578857492298125240724630067685469598575902649792655976391903473569465976856019135277564966247855340455145673714833174140509715959196042757190195737877461114729715970883210468133111989520881969406848636921404788506671177994532219430456930618014179649038651967555118371290948292515552245339570038601425663741453530428638812294005919743290992080444684743349902094483018017964184313841148911877893093169224443816633148668302231430712088074895877515413163726233588384087578886286411953039853661899961267161536916540357329899064757817948315902254353092921263924954628047882042107949015122493296342528971793777480129837349953756600254724641622640894664805633932984445635549672256471152411816178919667319446202970713519205380931815598421109310045921727144952839177166431821239789494263152743592348325416630107783590641622285436891992220212961775103636076674004141586457513914646529661479191742736985040936345931209501583423695166822906758701131262917827318921996418215472834635105408281847743002982169088751622070946099047804184485233828698712035244730828818415197882524270784971610668884886305618445535167370791993062936942780751396855716997729458538526927086963212808070467552609932693165837723489542399490370810340601948229732592511542674470157980967809800821610549421679523502938846387558288304388268489921823276573204253255844430738922782657788258216529765829717401570162648219462782614224097424299744633350648204634391564247098032015475441444380442655051572947693122487413448853249330395367069318513665974140053420234958645897134651183963200954609874748327838499773803180381598792880894492422802053878948337167282872704120158840048630740394448075047501258468081393550640648308721969273563638952463252128552556976249824335889330637878322151030260606814805228591063795314178145272494918941718500760777513244825734125431435279635641361180656000020235675186307511707542002030144296814718064872533838644415803254949475553384009574587731022782801776768091395688923390419990077057742892807106802348282827220072673331937721249634827727228606768740556940211434677646812336326250029578378419848252970409779451028613850468654257084324611026385018940214550030062901915800969941589433725582006989196776492565051075378788702754152098644109994 >>> (2 * ((U * 13 + V) * 31 + (E - (-6))).toNat)) % 4 % 3

def lab (u v e : ℤ) : ℕ := tbl (cap 6 4 u) (cap 8 4 v) (scap (-2) 20 4 e)

def allows (a : ℕ) (b : Bool) : Prop := a = 2 ∨ a = b.toNat

instance (a : ℕ) (b : Bool) : Decidable (allows a b) := inferInstanceAs (Decidable (_ ∨ _))

def out (c : Bool) (s : ℕ) : Bool := (533 : ℕ).testBit (c.toNat + 2 * s)

def tag (u v : ℤ) : ℕ := if u = 0 then (if v = 0 then 3 else 2) else if v = 0 then 1 else 0

def upd (z : ℕ) (c w r s n : Bool) : Bool :=
  if z = 3 then out c (4 * r.toNat) else if z = 2 then out c (2 * r.toNat + 2 * s.toNat)
  else if z = 1 then out c (w.toNat + r.toNat + 2 * n.toNat)
  else out c (w.toNat + r.toNat + s.toNat + n.toNat)

def transfer (z a b c d e : ℕ) : ℕ :=
  (1062234277643638983012316457440359379499532583592879685569074533997749901076668123549487704781842435115191080225168908764023370395984083890979870816402161391560244031749092361766151035814036891266626859490248902224081197317891255442377598312737728203424783282036487212860711508895479003102476984911786628175536944100525644655820205397782427027421461904444821490390951979618885677041665095885643514301288900875647631434802253127128044116779612467661917533884718842496565170586427431632810390570975262781476007172389086343464563635281971037170485734252641934473430470212304108244909555797 >>> (2 * (z + 4 * (a + 3 * (b + 3 * (c + 3 * (d + 3 * e))))))) % 4

def decForallBool (p : Bool → Prop) (hp : DecidablePred p) : Decidable (∀ b, p b) :=
  letI := hp
  decidable_of_iff (p false ∧ p true)
    ⟨fun h b => by cases b; exact h.1; exact h.2, fun h => ⟨h false, h true⟩⟩

def transferSpec (z : Fin 4) (a b c d e : Fin 3) : Prop :=
  ∀ p q r s w : Bool, allows a p → allows b q → allows c r → allows d s → allows e w →
    allows (transfer z a b c d e) (upd z p q r s w)

instance (z : Fin 4) (a b c d e : Fin 3) : Decidable (transferSpec z a b c d e) := by
  unfold transferSpec
  apply decForallBool; intro p
  apply decForallBool; intro q
  apply decForallBool; intro r
  apply decForallBool; intro s
  apply decForallBool; intro w
  infer_instance

set_option maxRecDepth 100000 in
theorem transfer_ok : ∀ z : Fin 4, ∀ a b c d e : Fin 3, transferSpec z a b c d e := by
  decide +kernel

def ok (u v e : ℤ) : Prop :=
  lab u v (e + 1) = 2 ∨ lab u v (e + 1) = transfer (tag u v) (lab u v e)
    (if u = 0 then 2 else lab (u - 1) v (e + 1)) (lab (u + 1) v (e - 1))
    (if v = 0 then 2 else lab (u + 1) (v - 1) (e + 1))
    (if u = 0 then 2 else lab (u - 1) (v + 1) (e - 1))

instance (u v e : ℤ) : Decidable (ok u v e) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 100000 in
theorem box_ok : ∀ U : Fin 12, ∀ V : Fin 14, ∀ E : Fin 33,
    ((7 : ℤ) < (U : ℕ) ∨ (9 : ℤ) < (V : ℕ) ∨ (1 : ℤ) ≤ (U : ℕ) + 2 * (V : ℕ) + ((E : ℕ) + (-7))) →
      ok (U : ℕ) (V : ℕ) ((E : ℕ) + (-7)) := by
  decide +kernel

theorem capU_step (x s : ℤ) (hs : -1 ≤ s ∧ s ≤ 1) :
    cap 6 4 (cap 7 4 x + s) = cap 6 4 (x + s) := by
  unfold cap; split_ifs <;> omega

theorem capV_step (x s : ℤ) (hs : -1 ≤ s ∧ s ≤ 1) :
    cap 8 4 (cap 9 4 x + s) = cap 8 4 (x + s) := by
  unfold cap; split_ifs <;> omega

theorem scapE_step (d s : ℤ) (hs : -1 ≤ s ∧ s ≤ 1) :
    scap (-2) 20 4 (scap (-3) 21 4 d + s) = scap (-2) 20 4 (d + s) := by
  unfold scap cap; split_ifs <;> omega

theorem loc (u v e i j k : ℤ) (hi : -1 ≤ i ∧ i ≤ 1) (hj : -1 ≤ j ∧ j ≤ 1) (hk : -1 ≤ k ∧ k ≤ 1) :
    lab (cap 7 4 u + i) (cap 9 4 v + j) (scap (-3) 21 4 e + k) =
      lab (u + i) (v + j) (e + k) := by
  unfold lab
  rw [capU_step u i hi, capV_step v j hj, scapE_step e k hk]

theorem local_ok (u v e : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 1 ≤ u + 2 * v + e) : ok u v e := by
  set U := cap 7 4 u with hUdef
  set V := cap 9 4 v with hVdef
  set E := scap (-3) 21 4 e with hEdef
  have hU : 0 ≤ U ∧ U < 12 := by rw [hUdef]; unfold cap; split_ifs <;> omega
  have hV : 0 ≤ V ∧ V < 14 := by rw [hVdef]; unfold cap; split_ifs <;> omega
  have hE : -7 ≤ E ∧ E < 26 := by rw [hEdef]; unfold scap cap; split_ifs <;> omega
  have hreal : 7 < U ∨ 9 < V ∨ 1 ≤ U + 2 * V + E := by
    rw [hUdef, hVdef, hEdef]; unfold scap cap; split_ifs <;> omega
  have hc := box_ok ⟨U.toNat, by omega⟩ ⟨V.toNat, by omega⟩ ⟨(E - (-7)).toNat, by omega⟩
  simp only [Fin.val_mk, Int.toNat_of_nonneg hU.1, Int.toNat_of_nonneg hV.1,
    Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ E - (-7)), sub_add_cancel] at hc
  replace hc := hc hreal
  have hu0 : U = 0 ↔ u = 0 := by rw [hUdef]; unfold cap; split_ifs <;> omega
  have hv0 : V = 0 ↔ v = 0 := by rw [hVdef]; unfold cap; split_ifs <;> omega
  have l (i j k : ℤ) (hi : -1 ≤ i ∧ i ≤ 1) (hj : -1 ≤ j ∧ j ≤ 1) (hk : -1 ≤ k ∧ k ≤ 1) :
      lab (U + i) (V + j) (E + k) = lab (u + i) (v + j) (e + k) := loc u v e i j k hi hj hk
  have c0 := l 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  have c1 := l 0 0 1 (by norm_num) (by norm_num) (by norm_num)
  have cw := l (-1) 0 1 (by norm_num) (by norm_num) (by norm_num)
  have cr := l 1 0 (-1) (by norm_num) (by norm_num) (by norm_num)
  have cs := l 1 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
  have cn := l (-1) 1 (-1) (by norm_num) (by norm_num) (by norm_num)
  simp only [add_zero, ← sub_eq_add_neg] at c0 c1 cw cr cs cn
  have htag : tag U V = tag u v := by
    unfold tag; simp only [hu0, hv0]
  unfold ok at hc ⊢
  simp only [htag, c0, c1, cw, cr, cs, cn, hu0, hv0] at hc
  exact hc

/-! Symmetries of the automaton. -/

theorem swap (t : ℕ) (i j : ℤ) : cell 533 t i j = cell 533 t j i := by
  induction t generalizing i j with
  | zero => simp only [cell, and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih i j, ih (i + 1) j, ih (i - 1) j, ih i (j + 1), ih i (j - 1)]
    congr 1; omega

theorem reflY (t : ℕ) (i j : ℤ) : cell 533 t i (-j) = cell 533 t i j := by
  induction t generalizing i j with
  | zero => simp only [cell, neg_eq_zero]
  | succ t ih =>
    simp only [cell]
    rw [show -j + 1 = -(j - 1) by ring, show -j - 1 = -(j + 1) by ring, ih i j, ih (i + 1) j,
      ih (i - 1) j, ih i (j - 1), ih i (j + 1)]
    congr 1; omega

theorem reflX (t : ℕ) (i j : ℤ) : cell 533 t (-i) j = cell 533 t i j := by
  rw [swap, reflY, swap]

theorem cell_succ (t : ℕ) (i j : ℤ) : cell 533 (t + 1) i j = out (cell 533 t i j)
    ((cell 533 t (i + 1) j).toNat + (cell 533 t (i - 1) j).toNat +
      (cell 533 t i (j + 1)).toNat + (cell 533 t i (j - 1)).toNat) := rfl

/-- One step in wedge coordinates: cell (u + v, v) from its folded neighbours. -/
theorem wstep (t : ℕ) (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    cell 533 (t + 1) (u + v) v = upd (tag u v) (cell 533 t (u + v) v)
      (if u = 0 then false else cell 533 t (u - 1 + v) v) (cell 533 t (u + 1 + v) v)
      (if v = 0 then false else cell 533 t (u + 1 + (v - 1)) (v - 1))
      (if u = 0 then false else cell 533 t (u - 1 + (v + 1)) (v + 1)) := by
  rw [cell_succ]
  have eR : cell 533 t (u + v + 1) v = cell 533 t (u + 1 + v) v := by
      all_goals (try congr 1)
      all_goals ring
  rw [eR]
  by_cases hu0 : u = 0 <;> by_cases hv0 : v = 0
  · subst hu0; subst hv0
    have e1 : cell 533 t (0 + 0 - 1) 0 = cell 533 t (0 + 1 + 0) 0 := by
      rw [show (0 : ℤ) + 0 - 1 = -1 by norm_num, reflX]; norm_num
    have e2 : cell 533 t (0 + 0) (0 + 1) = cell 533 t (0 + 1 + 0) 0 := by
      rw [swap]; norm_num
    have e3 : cell 533 t (0 + 0) (0 - 1) = cell 533 t (0 + 1 + 0) 0 := by
      rw [show (0 : ℤ) - 1 = -1 by norm_num, reflY, swap]; norm_num
    rw [e1, e2, e3]; simp only [tag, upd, if_true]; congr 1; omega
  · subst hu0
    have e1 : cell 533 t (0 + v - 1) v = cell 533 t (0 + 1 + (v - 1)) (v - 1) := by
      rw [swap]
      all_goals (try congr 1)
      all_goals ring
    have e2 : cell 533 t (0 + v) (v + 1) = cell 533 t (0 + 1 + v) v := by
      rw [swap]
      all_goals (try congr 1)
      all_goals ring
    have e3 : cell 533 t (0 + v) (v - 1) = cell 533 t (0 + 1 + (v - 1)) (v - 1) := by
      all_goals (try congr 1)
      all_goals ring
    rw [e1, e2, e3]; simp only [tag, upd, hv0, if_true, if_false]; congr 1; omega
  · subst hv0
    have e1 : cell 533 t (u + 0 - 1) 0 = cell 533 t (u - 1 + 0) 0 := by
      all_goals (try congr 1)
      all_goals ring
    have e2 : cell 533 t (u + 0) (0 + 1) = cell 533 t (u - 1 + (0 + 1)) (0 + 1) := by
      all_goals (try congr 1)
      all_goals ring
    have e3 : cell 533 t (u + 0) (0 - 1) = cell 533 t (u - 1 + (0 + 1)) (0 + 1) := by
      rw [show (0 : ℤ) - 1 = -(0 + 1) by norm_num, reflY]
      all_goals (try congr 1)
      all_goals ring
    rw [e1, e2, e3]; simp only [tag, upd, hu0, if_true, if_false]; congr 1; omega
  · have e1 : cell 533 t (u + v - 1) v = cell 533 t (u - 1 + v) v := by
      all_goals (try congr 1)
      all_goals ring
    have e2 : cell 533 t (u + v) (v + 1) = cell 533 t (u - 1 + (v + 1)) (v + 1) := by
      all_goals (try congr 1)
      all_goals ring
    have e3 : cell 533 t (u + v) (v - 1) = cell 533 t (u + 1 + (v - 1)) (v - 1) := by
      all_goals (try congr 1)
      all_goals ring
    rw [e1, e2, e3]; simp only [tag, upd, hu0, hv0, if_false]; congr 1; omega

/-! The invariant, from time 1 on. -/

set_option maxRecDepth 100000 in
theorem base_box : ∀ U : Fin 11, ∀ V : Fin 13, ∀ E : Fin 31,
    ((E : ℕ) : ℤ) + (-6) < 0 → (((U : ℕ) : ℤ) + 2 * (V : ℕ) + (((E : ℕ) : ℤ) + (-6)) - 1) % 4 = 0 →
      allows (tbl (U : ℕ) (V : ℕ) ((E : ℕ) + (-6))) true := by
  decide +kernel

theorem cell_one_bg (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (h0 : ¬ (u = 0 ∧ v = 0))
    (h1 : ¬ (u = 1 ∧ v = 0)) : cell 533 1 (u + v) v = true := by
  rw [cell_succ]
  simp only [cell]
  have e1 : decide (u + v = 0 ∧ v = 0) = false := by simp only [decide_eq_false_iff_not]; omega
  have e2 : decide (u + v + 1 = 0 ∧ v = 0) = false := by simp only [decide_eq_false_iff_not]; omega
  have e3 : decide (u + v - 1 = 0 ∧ v = 0) = false := by simp only [decide_eq_false_iff_not]; omega
  have e4 : decide (u + v = 0 ∧ v + 1 = 0) = false := by simp only [decide_eq_false_iff_not]; omega
  have e5 : decide (u + v = 0 ∧ v - 1 = 0) = false := by simp only [decide_eq_false_iff_not]; omega
  rw [e1, e2, e3, e4, e5]
  decide

theorem base (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    allows (lab u v (1 - u - 2 * v)) (cell 533 1 (u + v) v) := by
  by_cases h0 : u = 0 ∧ v = 0
  · obtain ⟨rfl, rfl⟩ := h0; decide +kernel
  by_cases h1 : u = 1 ∧ v = 0
  · obtain ⟨rfl, rfl⟩ := h1; decide +kernel
  rw [cell_one_bg u v hu hv h0 h1]
  set U := cap 6 4 u with hUdef
  set V := cap 8 4 v with hVdef
  set E := scap (-2) 20 4 (1 - u - 2 * v) with hEdef
  have hU : 0 ≤ U ∧ U < 11 := by rw [hUdef]; unfold cap; split_ifs <;> omega
  have hV : 0 ≤ V ∧ V < 13 := by rw [hVdef]; unfold cap; split_ifs <;> omega
  have hE : -6 ≤ E ∧ E < 25 := by rw [hEdef]; unfold scap cap; split_ifs <;> omega
  have hb := base_box ⟨U.toNat, by omega⟩ ⟨V.toNat, by omega⟩ ⟨(E - (-6)).toNat, by omega⟩
  simp only [Fin.val_mk, Int.toNat_of_nonneg hU.1, Int.toNat_of_nonneg hV.1,
    Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ E - (-6)), sub_add_cancel] at hb
  have hEn : E < 0 := by rw [hEdef]; unfold scap cap; split_ifs <;> omega
  have hmod : (U + 2 * V + E - 1) % 4 = 0 := by
    rw [hUdef, hVdef, hEdef]; unfold scap cap; split_ifs <;> omega
  exact hb hEn hmod

theorem invariant (t : ℕ) (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    allows (lab u v ((t + 1 : ℕ) - u - 2 * v)) (cell 533 (t + 1) (u + v) v) := by
  induction t generalizing u v with
  | zero => simpa using base u v hu hv
  | succ t ih =>
    rw [wstep (t + 1) u v hu hv]
    have hl := local_ok u v ((t + 1 : ℕ) - u - 2 * v) hu hv (by push_cast; omega)
    have hc := ih u v hu hv
    have hr := ih (u + 1) v (by omega) hv
    have hw : allows (if u = 0 then 2 else lab (u - 1) v ((t + 1 : ℕ) - u - 2 * v + 1))
        (if u = 0 then false else cell 533 (t + 1) (u - 1 + v) v) := by
      by_cases h : u = 0
      · simp only [h, if_true]; left; rfl
      · simp only [h, if_false]
        have := ih (u - 1) v (by omega) hv
        rwa [show ((t + 1 : ℕ) : ℤ) - (u - 1) - 2 * v = (t + 1 : ℕ) - u - 2 * v + 1 by ring] at this
    have hs : allows (if v = 0 then 2 else lab (u + 1) (v - 1) ((t + 1 : ℕ) - u - 2 * v + 1))
        (if v = 0 then false else cell 533 (t + 1) (u + 1 + (v - 1)) (v - 1)) := by
      by_cases h : v = 0
      · simp only [h, if_true]; left; rfl
      · simp only [h, if_false]
        have := ih (u + 1) (v - 1) (by omega) (by omega)
        rwa [show ((t + 1 : ℕ) : ℤ) - (u + 1) - 2 * (v - 1) = (t + 1 : ℕ) - u - 2 * v + 1 by ring] at this
    have hn : allows (if u = 0 then 2 else lab (u - 1) (v + 1) ((t + 1 : ℕ) - u - 2 * v - 1))
        (if u = 0 then false else cell 533 (t + 1) (u - 1 + (v + 1)) (v + 1)) := by
      by_cases h : u = 0
      · simp only [h, if_true]; left; rfl
      · simp only [h, if_false]
        have := ih (u - 1) (v + 1) (by omega) (by omega)
        rwa [show ((t + 1 : ℕ) : ℤ) - (u - 1) - 2 * (v + 1) = (t + 1 : ℕ) - u - 2 * v - 1 by ring] at this
    rw [show ((t + 1 : ℕ) : ℤ) - (u + 1) - 2 * v = (t + 1 : ℕ) - u - 2 * v - 1 by ring] at hr
    rw [show ((t + 1 + 1 : ℕ) : ℤ) - u - 2 * v = (t + 1 : ℕ) - u - 2 * v + 1 by push_cast; ring]
    have bnd (a b c : ℤ) : lab a b c < 3 := Nat.mod_lt _ (by norm_num)
    have bnd2 (p : Prop) [Decidable p] (a b c : ℤ) : (if p then 2 else lab a b c) < 3 := by
      split_ifs
      · norm_num
      · exact bnd a b c
    rcases hl with h2 | heq
    · left; exact h2
    · rw [heq]
      exact transfer_ok ⟨tag u v, by unfold tag; split_ifs <;> norm_num⟩ ⟨_, bnd _ _ _⟩
        ⟨_, bnd2 _ _ _ _⟩ ⟨_, bnd _ _ _⟩ ⟨_, bnd2 _ _ _ _⟩ ⟨_, bnd2 _ _ _ _⟩ _ _ _ _ _ hc hw hr hs hn

/-! Axis digits. -/

def digit (x d : ℕ) : ℕ := if x + d = 0 then 1 else lab x 0 d

set_option maxRecDepth 100000 in
theorem axis_box : ∀ U : Fin 11, ∀ D : Fin 25, ((1 : ℤ) ≤ (U : ℕ) + (D : ℕ) ∨ (6 : ℤ) < (U : ℕ)) →
    tbl (U : ℕ) 0 (D : ℕ) < 2 := by
  decide +kernel

theorem axis_known (x d : ℕ) (h : 1 ≤ x + d) : lab x 0 d < 2 := by
  have hU : 0 ≤ cap 6 4 (x : ℤ) ∧ cap 6 4 (x : ℤ) < 11 := by unfold cap; split_ifs <;> omega
  have hD : 0 ≤ scap (-2) 20 4 (d : ℤ) ∧ scap (-2) 20 4 (d : ℤ) < 25 := by
    unfold scap cap; split_ifs <;> omega
  have := axis_box ⟨(cap 6 4 (x : ℤ)).toNat, by omega⟩ ⟨(scap (-2) 20 4 (d : ℤ)).toNat, by omega⟩
  simp only [Fin.val_mk, Int.toNat_of_nonneg hU.1, Int.toNat_of_nonneg hD.1] at this
  show tbl (cap 6 4 (x : ℤ)) (cap 8 4 0) (scap (-2) 20 4 (d : ℤ)) < 2
  rw [show cap 8 4 (0 : ℤ) = 0 by unfold cap; norm_num]
  exact this (by unfold scap cap; split_ifs <;> omega)

theorem cell_digit (x d : ℕ) : (cell 533 (x + d) (x : ℤ) 0).toNat = digit x d := by
  unfold digit
  split_ifs with h
  · have hx : x = 0 := by omega
    have hd : d = 0 := by omega
    subst hx; subst hd; decide
  · obtain ⟨t, ht⟩ : ∃ t, x + d = t + 1 := ⟨x + d - 1, by omega⟩
    have hv := invariant t (x : ℤ) 0 (by omega) le_rfl
    rw [← ht] at hv
    simp only [add_zero, mul_zero, sub_zero] at hv
    rw [show ((x + d : ℕ) : ℤ) - x = d by push_cast; ring] at hv
    have hk := axis_known x d (by omega)
    rcases hv with h2 | h2
    · omega
    · omega

theorem digit_lt (x d : ℕ) : digit x d < 2 := by
  unfold digit; split_ifs with h
  · norm_num
  · exact axis_known x d (by omega)

theorem digit_px (x d : ℕ) (hx : 7 ≤ x) : digit (x + 4) d = digit x d := by
  unfold digit
  rw [if_neg (by omega), if_neg (by omega)]
  unfold lab
  rw [show cap 6 4 ((x + 4 : ℕ) : ℤ) = cap 6 4 (x : ℤ) by push_cast; unfold cap; split_ifs <;> omega]

theorem digit_pd (x d : ℕ) (hd : 21 ≤ d) : digit x (d + 4) = digit x d := by
  unfold digit
  rw [if_neg (by omega), if_neg (by omega)]
  unfold lab
  rw [show scap (-2) 20 4 ((d + 4 : ℕ) : ℤ) = scap (-2) 20 4 (d : ℤ) by
    push_cast; unfold scap cap; split_ifs <;> omega]

/-! Anti-diagonal sums. -/

def A (B : ℤ) (G : ℕ → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), G k (n - k) * B ^ (n - k)

theorem A_reflect (B : ℤ) (G : ℕ → ℕ → ℤ) (n : ℕ) :
    A B G n = ∑ v ∈ Finset.range (n + 1), G (n - v) v * B ^ v := by
  unfold A
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have : k < n + 1 := Finset.mem_range.mp hk
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]

/-- `A (n+P) - B^P A n` is a sum with a bounded number of terms. -/
theorem H_form (B : ℤ) (G : ℕ → ℕ → ℤ) (P V0 : ℕ)
    (hv : ∀ u v, V0 ≤ v → G u (v + P) = G u v) (n : ℕ) (hn : V0 ≤ n + 1) :
    A B G (n + P) - B ^ P * A B G n =
      (∑ v ∈ Finset.range P, G (n + P - v) v * B ^ v) +
      ∑ w ∈ Finset.range V0, (G (n - w) (w + P) - G (n - w) w) * B ^ (P + w) := by
  rw [A_reflect, A_reflect, show n + P + 1 = P + (n + 1) by omega, Finset.sum_range_add,
    Finset.mul_sum]
  have hsplit : ∀ f : ℕ → ℤ, (∑ w ∈ Finset.range (n + 1), f w) =
      (∑ w ∈ Finset.range V0, f w) + ∑ w ∈ Finset.range (n + 1 - V0), f (V0 + w) := by
    intro f
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hn]
  have e1 : ∀ w, G (n + P - (P + w)) (P + w) * B ^ (P + w) - B ^ P * (G (n - w) w * B ^ w)
      = (G (n - w) (w + P) - G (n - w) w) * B ^ (P + w) := by
    intro w
    rw [show n + P - (P + w) = n - w by omega, add_comm P w, pow_add]; ring
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  simp only [e1]
  rw [hsplit (fun w => (G (n - w) (w + P) - G (n - w) w) * B ^ (P + w))]
  have hz : ∑ w ∈ Finset.range (n + 1 - V0),
      (G (n - (V0 + w)) (V0 + w + P) - G (n - (V0 + w)) (V0 + w)) * B ^ (P + (V0 + w)) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [hv _ _ (by omega), sub_self, zero_mul]
  rw [hz, add_zero]

/-- The anti-diagonal sum of a doubly eventually periodic table satisfies a fixed recurrence. -/
theorem big_rec (B : ℤ) (G : ℕ → ℕ → ℤ) (P U0 V0 : ℕ)
    (hu : ∀ u v, U0 ≤ u → G (u + P) v = G u v)
    (hv : ∀ u v, V0 ≤ v → G u (v + P) = G u v) (n : ℕ) (hn : U0 + V0 ≤ n) :
    A B G (n + 2 * P) = (1 + B ^ P) * A B G (n + P) - B ^ P * A B G n := by
  have h1 := H_form B G P V0 hv (n + P) (by omega)
  have h0 := H_form B G P V0 hv n (by omega)
  have e : A B G (n + P + P) - B ^ P * A B G (n + P) = A B G (n + P) - B ^ P * A B G n := by
    rw [h1, h0]
    congr 1
    · apply Finset.sum_congr rfl
      intro v hv'
      have : v < P := Finset.mem_range.mp hv'
      rw [show n + P + P - v = (n + P - v) + P by omega, hu _ _ (by omega)]
    · apply Finset.sum_congr rfl
      intro w hw
      have : w < V0 := Finset.mem_range.mp hw
      rw [show n + P - w = (n - w) + P by omega, hu _ _ (by omega), hu _ _ (by omega)]
  rw [show n + 2 * P = n + P + P by ring]
  linarith

/-- Propagate a vanishing residual along the fixed recurrence. -/
theorem propagate (r : ℕ → ℤ) (c : ℤ) (P M : ℕ) (hP : 0 < P)
    (hr : ∀ n, M ≤ n → r (n + 2 * P) = (1 + c) * r (n + P) - c * r n)
    (h0 : ∀ n, M ≤ n → n < M + 2 * P → r n = 0) : ∀ n, M ≤ n → r n = 0 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hlt : n < M + 2 * P
    · exact h0 n hn hlt
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * P := ⟨n - 2 * P, by omega⟩
      rw [hr m (by omega), ih (m + P) (by omega) (by omega), ih m (by omega) (by omega)]
      ring

def G (k v : ℕ) : ℤ := digit k v

theorem G_u (u v : ℕ) (h : 7 ≤ u) : G (u + 4) v = G u v := by
  unfold G; rw [digit_px u v h]

theorem G_v (u v : ℕ) (h : 21 ≤ v) : G u (v + 4) = G u v := by
  unfold G; rw [digit_pd u v h]

theorem a_eq (n : ℕ) : a n = A 10 G n := by
  unfold a A
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h := cell_digit k (n - k)
  rw [show k + (n - k) = n by omega] at h
  
  unfold G
  rw [← h]
  cases cell 533 n (k : ℤ) 0 <;> simp

/-! The recurrence and the generating function. -/

def qz (i : ℕ) : ℤ := [1, 0, 0, 0, -10001, 0, 0, 0, 10000].getD i 0
def mz (i : ℕ) : ℤ := [1, 1, 1, 1001, -9000, -9000, 1091000, -10000, -8900000, 1090000000, -900000000, -90000000000, -11000000000, 110000000000, 0, 1000000000000, 1011000000000, -110111000000000, -10000000000000000, 90000000000000000, 99990000000000000, 110000000000000, 10000000000000000, -90100000000000000, -99000000000000000].getD i 0

def res (n : ℕ) : ℤ := ∑ i ∈ Finset.range 9, qz i * (if i ≤ n then A 10 G (n - i) else 0)

set_option maxRecDepth 100000 in
theorem res_small : ∀ n : Fin 45, res n = if (n : ℕ) < 25 then mz n else 0 := by
  decide +kernel

theorem res_rec (n : ℕ) (hn : 37 ≤ n) :
    res (n + 2 * 4) = (1 + 10 ^ 4) * res (n + 4) - 10 ^ 4 * res n := by
  unfold res
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 9 := Finset.mem_range.mp hi
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [show n + 2 * 4 - i = (n - i) + 2 * 4 by omega, show n + 4 - i = (n - i) + 4 by omega,
    big_rec 10 G 4 7 21 G_u G_v (n - i) (by omega)]
  ring

theorem res_all (n : ℕ) : res n = if n < 25 then mz n else 0 := by
  by_cases h : n < 45
  · exact res_small ⟨n, h⟩
  · rw [if_neg (by omega)]
    refine propagate res (10 ^ 4) 4 37 (by norm_num) (fun m hm => res_rec m hm) ?_ n (by omega)
    intro m hm hm'
    have h2 := res_small ⟨m, by omega⟩
    simp only [Fin.val_mk] at h2
    rw [h2, if_neg (by omega)]

theorem res_eq (n : ℕ) (hn : 8 ≤ n) :
    res n = ∑ i ∈ Finset.range 9, qz i * A 10 G (n - i) := by
  unfold res
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (by have := Finset.mem_range.mp hi; omega)]

theorem rec_int (n : ℕ) (hn : 25 ≤ n) : a n = 10001 * a (n - 4) - 10000 * a (n - 8) := by
  have h := res_all n
  rw [if_neg (by omega), res_eq n (by omega)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, qz] at h
  norm_num at h
  simp only [a_eq]
  linarith

open PowerSeries in
theorem coeff_mul_poly (S : PowerSeries ℚ) (q : ℕ → ℚ) (L n : ℕ) :
    coeff n (S * ∑ i ∈ Finset.range L, C (q i) * X ^ i) =
      ∑ i ∈ Finset.range L, q i * (if i ≤ n then coeff (n - i) S else 0) := by
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show S * (C (q i) * X ^ i) = C (q i) * (S * X ^ i) by ring, coeff_C_mul, coeff_mul_X_pow']

open PowerSeries in
theorem coeff_poly (m : ℕ → ℚ) (L n : ℕ) :
    coeff n (∑ i ∈ Finset.range L, C (m i) * X ^ i) = if n < L then m n else 0 := by
  rw [map_sum]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (10000 * X ^ 8 - 10001 * X ^ 4 + 1 : PowerSeries ℚ) = -99000000000000000 * X ^ 24 - 90100000000000000 * X ^ 23 + 10000000000000000 * X ^ 22 + 110000000000000 * X ^ 21 + 99990000000000000 * X ^ 20 + 90000000000000000 * X ^ 19 - 10000000000000000 * X ^ 18 - 110111000000000 * X ^ 17 + 1011000000000 * X ^ 16 + 1000000000000 * X ^ 15 + 110000000000 * X ^ 13 - 11000000000 * X ^ 12 - 90000000000 * X ^ 11 - 900000000 * X ^ 10 + 1090000000 * X ^ 9 - 8900000 * X ^ 8 - 10000 * X ^ 7 + 1091000 * X ^ 6 - 9000 * X ^ 5 - 9000 * X ^ 4 + 1001 * X ^ 3 + X ^ 2 + X + 1 := by
  have hQ : (10000 * X ^ 8 - 10001 * X ^ 4 + 1 : PowerSeries ℚ) = ∑ i ∈ Finset.range 9, C ((qz i : ℚ)) * X ^ i := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, qz]
    norm_num <;> (try simp only [map_ofNat]) <;> ring
  have hN : (-99000000000000000 * X ^ 24 - 90100000000000000 * X ^ 23 + 10000000000000000 * X ^ 22 + 110000000000000 * X ^ 21 + 99990000000000000 * X ^ 20 + 90000000000000000 * X ^ 19 - 10000000000000000 * X ^ 18 - 110111000000000 * X ^ 17 + 1011000000000 * X ^ 16 + 1000000000000 * X ^ 15 + 110000000000 * X ^ 13 - 11000000000 * X ^ 12 - 90000000000 * X ^ 11 - 900000000 * X ^ 10 + 1090000000 * X ^ 9 - 8900000 * X ^ 8 - 10000 * X ^ 7 + 1091000 * X ^ 6 - 9000 * X ^ 5 - 9000 * X ^ 4 + 1001 * X ^ 3 + X ^ 2 + X + 1 : PowerSeries ℚ) = ∑ i ∈ Finset.range 25, C ((mz i : ℚ)) * X ^ i := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, mz]
    norm_num <;> (try simp only [map_ofNat]) <;> ring
  rw [hQ, hN]
  ext n
  rw [coeff_mul_poly, coeff_poly]
  simp only [coeff_mk]
  have h := res_all n
  unfold res at h
  have hc := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_mul, apply_ite (fun z : ℤ => (z : ℚ)), Int.cast_zero] at hc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [a_eq]

end CAR533right

theorem OMA.solution : type_of% @OMA.S_oeis_a282955.main := by
  exact ⟨fun n hn => by exact_mod_cast CAR533right.rec_int n hn, CAR533right.gf⟩
