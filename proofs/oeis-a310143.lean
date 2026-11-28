import OMAStatements.S_oeis_a310143

namespace OMA.S_oeis_a310143






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 13

/-- Field k of the B-bit fields packed in the natural number T, as stored. The table accessors call
the kernel's natural number primitives directly: through the operators' type-class instances the
kernel decisions take more memory. -/
def tgetN (T B k : ℕ) : ℕ := Nat.mod (Nat.shiftRight T (Nat.mul B k)) (Nat.pow 2 B)

/-- Field k of the B-bit fields packed in T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := Int.subNatNat (tgetN T B k) off

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 728441059241
  | 1 => 655159298216
  | 2 => 650579188136
  | 3 => 714717506233
  | 4 => 440984643189
  | 5 => 513712756614
  | 6 => 586726082455
  | 7 => 660007843480
  | 8 => 641704180392
  | 9 => 577565862295
  | 10 => 509132646534
  | 11 => 436404533109
  | 12 => 641417853881
  | _ => 0

/-- The potential t is Ac t * x + Bc t * y + Cc s t at (x, y, s) (packed tables). -/
def Ac (i : Fin 10) : ℤ := tget 494819663272 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 312959664947 4 8 i.val

def Cc (s : Fin 13) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The potential t at v. -/
def pot (v : V) (i : Fin 10) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)) (pot v 8)) (pot v 9)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F8 (v : V) : pot v 8 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F9 (v : V) : pot v 9 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 10) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v, le_F8 v, le_F9 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) (h8 : pot v 8 ≤ t) (h9 : pot v 9 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩) ⟨8, rfl⟩) ⟨9, rfl⟩

/-- The level of class s beyond which the far argument runs (the near box of class s covers the rest). -/
def R0N (s : Fin 13) : ℕ := tgetN 13129628315374075373 5 s.val

def R0c (s : Fin 13) : ℤ := (R0N s : ℤ)

/-- The pairs (class s, potential t) and the classes whose rule, far, side and near checks are made;
here all of them. -/
def repB (s : Fin 13) (t : Fin 10) : Bool := decide (tgetN 1361129467683753853853498429727072845823 1 (s.val * 10 + t.val) = 1)

def repC (s : Fin 13) : Bool := decide (tgetN 8191 1 s.val = 1)

/-- The change of the potential j along the edge e. -/
def dl (e : Fin 13 × Fin 13 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

/-- Along an edge e the potential j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 13 × Fin 13 × ℤ × ℤ) (j : Fin 10) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 13) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
    (hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l0 ∧
      l1 * (Ac a1 - Ac b1) + l2 * (Ac a2 - Ac b2) + l3 * (Ac a3 - Ac b3) - l0 * Ac i0 = 0 ∧
      l1 * (Bc a1 - Bc b1) + l2 * (Bc a2 - Bc b2) + l3 * (Bc a3 - Bc b3) - l0 * Bc i0 = 0 ∧
      0 < l1 * (Cc s a1 - Cc s b1 - t1) + l2 * (Cc s a2 - Cc s b2 - t2) +
        l3 * (Cc s a3 - Cc s b3 - t3) + l0 * (r - Cc s i0))
    (h1 : pot (x, y, s) a1 ≤ pot (x, y, s) b1 + t1) (h2 : pot (x, y, s) a2 ≤ pot (x, y, s) b2 + t2)
    (h3 : pot (x, y, s) a3 ≤ pot (x, y, s) b3 + t3) (h0 : r ≤ pot (x, y, s) i0) : False := by
  obtain ⟨hl1, hl2, hl3, hl0, hx, hy, hk⟩ := hc
  have e1 := mul_le_mul_of_nonneg_left h1 hl1
  have e2 := mul_le_mul_of_nonneg_left h2 hl2
  have e3 := mul_le_mul_of_nonneg_left h3 hl3
  have e0 := mul_le_mul_of_nonneg_left h0 hl0
  have hx' : (l1 * (Ac a1 - Ac b1) + l2 * (Ac a2 - Ac b2) + l3 * (Ac a3 - Ac b3) - l0 * Ac i0) * x = 0 := by
    rw [hx, zero_mul]
  have hy' : (l1 * (Bc a1 - Bc b1) + l2 * (Bc a2 - Bc b2) + l3 * (Bc a3 - Bc b3) - l0 * Bc i0) * y = 0 := by
    rw [hy, zero_mul]
  simp only [pot] at e1 e2 e3 e0
  nlinarith [e1, e2, e3, e0, hx', hy', hk]

/-- The neighbor slots of potential t: slots 0 and 1 on the side of the previous potentials and
slots 2 and 3 on the side of the next ones, nearest first; unused slots hold t itself. -/
def nb (t : Fin 10) (k : Fin 4) : Fin 10 :=
  ⟨(tget 825485214377624614016408041292630399738576896265 4 0 (t.val * 4 + k.val)).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The slot k of t holds another potential. -/
def real (t : Fin 10) (k : Fin 4) : Bool := decide (nb t k ≠ t)

/-- The potential t is a facet: a slot on each side cannot both come within 1 of t beyond R0c. -/
def facetB (t : Fin 10) : Bool := decide (tget 428 1 0 t.val = 1)

/-- The potential j is neither t nor in a slot of t. -/
def nonadj (t j : Fin 10) : Bool :=
  decide (j ≠ t) && decide (j ≠ nb t 0) && decide (j ≠ nb t 1) && decide (j ≠ nb t 2) && decide (j ≠ nb t 3)

/-- Certificates of the far facts, the same for every class: for maximal potential t and a potential
j that is not a neighbor of t, the fields k1, k2, m1, m2, m0, mj of entry t * 10 + j give the facts
pot k1 ≤ pot t, pot k2 ≤ pot t, R0c s + 1 ≤ pot t and pot t ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (t j : Fin 10) (f : ℕ) : ℤ := tget 10674758086713020450945326324794231173867471688921456261407436055509694084513837020671443860830103653245686091737242555559345747711382747838417881537192086638262996746075254012540557086195530975195511531749347331245231078619923534512168967758321790575262813645712861654232221582591717428199336152395436411579139580600715028095283763324029726224531369918989908990082767700604670482099800432581447837530931902500999704268909374013963277674254396834359481698621596696521749928755209486814518723335748514100350184315620173036638301972317121055477151321007304248105387809830554722485010935932411750161009325566980324721451173733277082079695930647666608016828208027776094567198197605936578489800173643701926515956073737948309119149430963384234222594281659798921731446029772583626271712959545496252697342635476127189689862823400343332913575664899226929869145587846372792218834884239859951247548023491867225896898504572200152400923365407317276041941409757851684247271951085122108630012102279115814584013684467002645204763084689209089760885553384409546428077210056871215357889576610244086934297722785947034681144739349214977834289638514349750886918673701856966414434242161892766095433086417609007190965934714430430189823306388567936853421157818137760250802640378067319529536 7 64 ((t.val * 10 + j.val) * 6 + f)

def fk1 (t j : Fin 10) : Fin 10 := ⟨(fd t j 0).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (t j : Fin 10) : Fin 10 := ⟨(fd t j 1).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The x and y parts of the far certificate of (t, j) cancel. -/
def farXY (t j : Fin 10) : Bool :=
  decide (0 ≤ fd t j 2 ∧ 0 ≤ fd t j 3 ∧ 0 ≤ fd t j 5 ∧ 0 ≤ fd t j 4 ∧
    fd t j 2 * (Ac (fk1 t j) - Ac t) + fd t j 3 * (Ac (fk2 t j) - Ac t) + fd t j 5 * (Ac t - Ac j) -
      fd t j 4 * Ac t = 0 ∧
    fd t j 2 * (Bc (fk1 t j) - Bc t) + fd t j 3 * (Bc (fk2 t j) - Bc t) + fd t j 5 * (Bc t - Bc j) -
      fd t j 4 * Bc t = 0)

/-- The constants of the far certificate of (t, j) at class s add up to a positive number. -/
def farC (s : Fin 13) (t j : Fin 10) : Bool :=
  decide (0 < fd t j 2 * (Cc s (fk1 t j) - Cc s t - 0) + fd t j 3 * (Cc s (fk2 t j) - Cc s t - 0) +
    fd t j 5 * (Cc s t - Cc s j - 1) + fd t j 4 * (R0c s + 1 - Cc s t))

/-- The far certificates of the maximal potential t are valid. -/
def farsOK (t : Fin 10) : Bool :=
  (List.finRange 10).all fun j => !nonadj t j || (farXY t j && (List.finRange 13).all fun s => !repB s t || farC s t j)

/-- Beyond F = R0c s, a potential that is not a neighbor of a maximal potential t has slack at least 2. -/
theorem far (s : Fin 13) (t j : Fin 10) (hxy : farXY t j = true) (hc0 : farC s t j = true) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) t) (hF : R0c s < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) t + (-2) := by
  by_contra hc
  have q := of_decide_eq_true hxy
  exact farkas x y s (fk1 t j) t (fk2 t j) t t j t 0 0 1 (R0c s + 1) (fd t j 2) (fd t j 3) (fd t j 5) (fd t j 4)
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) (pair_of (le_F _ _) h) (not_pair2 hc) (bound_of hF h)

/-- Certificates of the side facts, the same for every class: for a facet t, entry i of t, for the
slots (0, 2), (0, 3), (1, 2), (1, 3), has fields k, mk, mL, mR, m0 for the facts pot k ≤ pot t,
pot t ≤ pot (left slot) + 1, pot t ≤ pot (right slot) + 1 and R0c s + 1 ≤ pot t. -/
def sd (t : Fin 10) (i f : ℕ) : ℤ := tget 8745894327053079679018350575772767229754882410386636155180191498767742169197063504094588713987234860706876663854705144077822096968920265844024219552853604864898657521283555814280039276481269222810740667507324932060554103551435156396366715399259588353723870208052933412825199708659273887133968375587911704943175148939790698559852327243098777189100623581478520864 6 32 ((t.val * 4 + i) * 5 + f)

def sk (t : Fin 10) (i : ℕ) : Fin 10 := ⟨(sd t i 0).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

def sideXY (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 ≤ sd t i 1 ∧ 0 ≤ sd t i 2 ∧ 0 ≤ sd t i 3 ∧ 0 ≤ sd t i 4 ∧
    sd t i 1 * (Ac (sk t i) - Ac t) + sd t i 2 * (Ac t - Ac (nb t kl)) + sd t i 3 * (Ac t - Ac (nb t kr)) -
      sd t i 4 * Ac t = 0 ∧
    sd t i 1 * (Bc (sk t i) - Bc t) + sd t i 2 * (Bc t - Bc (nb t kl)) + sd t i 3 * (Bc t - Bc (nb t kr)) -
      sd t i 4 * Bc t = 0)

def sideC (s : Fin 13) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 < sd t i 1 * (Cc s (sk t i) - Cc s t - 0) + sd t i 2 * (Cc s t - Cc s (nb t kl) - 1) +
    sd t i 3 * (Cc s t - Cc s (nb t kr) - 1) + sd t i 4 * (R0c s + 1 - Cc s t))

def sideOK (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  !(real t kl && real t kr) || (sideXY t kl kr i && (List.finRange 13).all fun s => !repB s t || sideC s t kl kr i)

/-- All side certificates are valid. -/
def sidesOK : Bool :=
  (List.finRange 10).all fun t =>
    !facetB t || (sideOK t 0 2 0 && sideOK t 0 3 1 && sideOK t 1 2 2 && sideOK t 1 3 3)

/-- Beyond F = R0c s, a facet t has no slot on each side within 1 of it. -/
theorem side (s : Fin 13) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) (hxy : sideXY t kl kr i = true)
    (hc0 : sideC s t kl kr i = true) (x y : ℤ) (hL : pot (x, y, s) t ≤ pot (x, y, s) (nb t kl) + 1)
    (hR : pot (x, y, s) t ≤ pot (x, y, s) (nb t kr) + 1) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) : False := by
  have q := of_decide_eq_true hxy
  exact farkas x y s (sk t i) t t (nb t kl) t (nb t kr) t 0 1 1 (R0c s + 1) (sd t i 1) (sd t i 2) (sd t i 3)
    (sd t i 4) ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) hL hR (bound_of hF h)

/-- The edges of E by position p: source and target class, cell offset, and the potential changes dl
(entry p * 10 + j). -/
def srcv (p : ℕ) : ℕ := tgetN 5021681363366002641627375980757563721310586828628643872768 4 p

def tgtv (p : ℕ) : ℕ := tgetN 4522795719505413688012191486292779948521073493255443762033 4 p

def tgtF (p : ℕ) : Fin 13 := ⟨tgtv p % 13, Nat.mod_lt _ (by norm_num)⟩

def dxv (p : ℕ) : ℤ := tget 3349320461897223777052833004354229345514785269471926318984 4 8 p

def dyv (p : ℕ) : ℤ := tget 2955372976162993262984307320854269844224429090795002824584 4 8 p

/-- dlv p j + 8, as a natural number (the rule checks compare naturals). -/
def dlvN (p : ℕ) (j : Fin 10) : ℕ := tgetN 56562247996179433317189680745598804989723831608992267330573844069209861807874309485615307075285297297029289795216460435284788820697940843289963218831683419474725247047211375047780581674112609886413055457115455283466882720412755495674006004063158862246048754825220468093459266398354926990246020178095578987210825024684012482347856802322752899184952291878839248802401112025083508119606661069799760170075177657581307791719866857375464161497497447214385045605167245397419217372463730358920750319835178320601628409349207356741104525426414348159997250530566440651720918628089686759815 4 (p * 10 + j.val)

def dlv (p : ℕ) (j : Fin 10) : ℤ := (dlvN p j : ℤ) - 8

/-- The edge tables agree with the edges of a list l from position p on, every edge moves, and every
potential changes by at most one along every edge. -/
def dlOKl : List (Fin 13 × Fin 13 × ℤ × ℤ) → ℕ → Bool
  | [], _ => true
  | e :: l, p => decide (srcv p = e.1.val ∧ tgtv p = e.2.1.val ∧ dxv p = e.2.2.1 ∧ dyv p = e.2.2.2 ∧
        (e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1)) &&
      ((List.finRange 10).all fun j => decide (dlv p j = dl e j ∧ dl e j ≤ 1 ∧ -dl e j ≤ 1)) && dlOKl l (p + 1)

/-- The edge tables agree with E. -/
def dlOK : Bool := dlOKl E 0

/-- The slack class of a slack d ≥ 0: 2 when d ≥ 2, else d. -/
def scl (d : ℤ) : Fin 3 := if 2 ≤ d then 2 else if d = 1 then 1 else 0

theorem scl_le (d : ℤ) (hd : 0 ≤ d) : ((scl d).val : ℤ) ≤ d := by
  have e2 : ((2 : Fin 3).val : ℤ) = 2 := rfl
  have e1 : ((1 : Fin 3).val : ℤ) = 1 := rfl
  have e0 : ((0 : Fin 3).val : ℤ) = 0 := rfl
  unfold scl
  split_ifs <;> omega

theorem scl_eq (d : ℤ) (hd : 0 ≤ d) (h1 : (scl d).val ≤ 1) : d = (scl d).val := by
  have e2 : (2 : Fin 3).val = 2 := rfl
  have e1 : (1 : Fin 3).val = 1 := rfl
  have e0 : (0 : Fin 3).val = 0 := rfl
  unfold scl at *
  split_ifs at * <;> omega

/-- The pattern (c0, c1, c2, c3) of slack classes of the slots of t can occur beyond R0c: unused
slots have class 0, and a facet has no slot on each side of class at most 1. -/
def padOK (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  (real t 0 || decide (c0 = 0)) && (real t 1 || decide (c1 = 0)) && (real t 2 || decide (c2 = 0)) &&
    (real t 3 || decide (c3 = 0))

def closeL (t : Fin 10) (c0 c1 : ℕ) : Bool := (real t 0 && decide (c0 ≤ 1)) || (real t 1 && decide (c1 ≤ 1))

def closeR (t : Fin 10) (c2 c3 : ℕ) : Bool := (real t 2 && decide (c2 ≤ 1)) || (real t 3 && decide (c3 ≤ 1))

def adm (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  padOK t c0 c1 c2 c3 && (!facetB t || !closeL t c0 c1 || !closeR t c2 c3)

/-- Descent rules beyond F = R0c s, one word of 32 bits per class s, potential t and admissible
pattern (c0, c1, c2, c3), at position POFF t + (the rank of the pattern among the admissible patterns
of t): kind 0 names an edge by its position in E; kind 1 is a Farkas certificate: multipliers m1, m2,
m3 of the slot facts of slots k1, k2, k3 (slack ≥ c for a multiplier ≥ 0, slack ≤ c for a negative
multiplier, where c ≤ 1) and l0 ≥ 0 of the bound R0c s + 1 ≤ pot t, whose x and y parts cancel and
whose constants add up to a positive number; kind 2 is a line of slot k1 without lattice points
(modulus l0). Fields from bit 0: kind (2 bits), edge position (6), k1, k2, k3 (2 each), m1, m2, m3
(5 each, stored as value + 16), l0 (3). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 515660268487346442300706151683239308166227757456876033877717815912371655058963728927267149117190703099531512107096382859842042661995155709884594892848075306110367833970467586675689030528284214776083826573430558735274428207825538252345576586935553315779084495021021793386071430787509762378453304540418453431273735957667661449145852349481455210102415572478105042178992303885380767755488727583029820809101559571564971772587631345115289298476729951231193942289799531786666350081345432657228416023409942780223834610502975740850115739148671824019089672763000004017492631315891455611636351504415925216499310401970137780616201048117460035659033506995064322638639607334554071221960093627133545728716125335191522077163218870268353699325163922237763537987649262795692766886467782315724053265770610692
  | 1 => 515660313151592032237733091715446033342073848783762845580224067874435974757443531189194864763334782888039055412779363610109121554772136386400358046344160679262559561055401303150913203136928331674774524270672196836712873477703764074116252685070145554950964620721373054275177339731481333177429286433817606739057723063025877277989422204094220113734837935089032163061115012999034646773211203163334451349714328229633691205015169607289190883495475184911873542191169001518430510937755875579317187654672570066258176451447385112280768774316542420635386182124359941766619923852188329699574703800005759341168631942985301605016361258582146819707350388159905903296090908831887409730418003021395784425961143978561797710586159840698073118609074242552406306019264710961458722814112250465822511994029473816
  | 2 => 515660335483714827205926417375501626024412506891244374749946359304330640059688059900442982472321900149365594404908924237772032470084369565821765151591294663906605794954997791317057260870542641677528731289140282795016834606188531314907933074994697903352827771389975396087641728868289472308465734966069250503911042514863534731729787312936186120062706250715808228289058933192735487036753701633017923947264462808129456806904824044375213474345770540447558674405819916391735552979532026089819354630934286364852559809280938970392964350987360256607423246311774148307790431206823792852992621630495232969765329573891544414220247118778693590995098048973791282728547652456702933075526663320010413411734049895169553917416948787980361494413802721977486735159850554938360172460783889155489885104967516196
  | 3 => 515660342927755762328463685458918430581220426167264283685970457199544959733558394305196715565993713976480969573080767475701357806998017315375144002609908239102700798619785573348040188604724527643263059289939967272214055324541889158778615072522004089373374947079461626532686751162020892401706346456965650360522156819899920861041589716248720887551602888687855644870296561218658376668557311594669820123125319892954366674309890724509889823509714710104952189079813551764706240557647348018181953717483849581218341012172715630727487087415484157409718065264016516379375710046921544416929930028473174942757702790492566051583965785279031316803404670162791925444288183712845698833323115800594366201549983530846264378711312448978155591573622433014575873539844613707609418898196389930726901753334464552
  | 4 => 515660395036042280455011097990845908565021173055127344414149508986071960060331909654377056565785158162202159640982989054033833441118654873628230733317556810687886896953330646787012929595373690218975588820362676456010038055232088028844790134363773219426717717197177331510792242327724810063386132238737783709030888787751661432190048446324337252034633501444200051094109431683052049929069059353993084892555988720472003074277213654076776722039348225296874134627032037844953240302866297034209107326246699692051734772373221284954882389427172868303931405094194983813254517327050759075039055487359009539528182480434152485663077921150420308131869042896204959802430466698640275239831428945101639576017272941221006136677569364686812390869647545379227226377594538312928355094944073695806832466590957636
  | 5 => 515660402480083212111146683067763943882597256325612715622174902696289625060412390873618815827483033628420754006345647778972711000228367820366583875287907507271441802169854493395532111612419611302479213898470633293531759318719846390358175006067078476281863369443908789063006354270136950303502483057392219123117880569109105720837459354748262232862478423306377024066457815158652432639426346710746505990774891831963697911334940025257788778003215663168307549769063079813473238386236412014396993393680300026948321018456210560861045893927518025960108950976654152794575892336766940422092732757362601718547115469925793121453396820111906151401498980674626539665771483996658899658296643118330376567968856324777887597663472774317118099516475326458157461942420803461680111568135738265415673667700129864
  | 6 => 515660432256246938735689023375436085152901589407554200454276477537160285060734315750585852874214662634832611046757693221075962847454426661255948911752633284997265260657535978623686578569805078994261731376009206919221152374503074262329836412900220299965402490866761405563927159666077412628135639019909758987075813661723345256337453745536560427369850827651442169815997506758583842626560577618151367368754142003576237527744569157302398188579090843906922276298423690594467858861596464320721336172546542608028066299355598004102285731845716220675000250881435981947092549697127802225266144558402710100787391866381389492559319701488168623213688925338838656222699315081869111159089710084375790333931204116267201818183054794563975475503815339353672512025835788700070662610920524239405350639060123736
  | 7 => 515660454588369733704095778606190191105629839219010314078352658667813280060975759408311130659263384389645778469827835410660761088443382968873865800404359322987637348001217890374524403701758994251291330067401136958270712636372342407767006571237216647561803554064986739400484983549095647172941350776632610937622172634740742875938620145032083679682028636515317109419708952369061221833269116575530865836560537087383971999999096144355812285845299633567499053390195328785959897034212463149091430207622247550922457911429838438695384510996192929936682775726218991457098611280964605146831894611260985020199638609474982021842172045688568671880205479405204768301599011318116716737312935063994372750198614466319124091336574060937812641306996728242361619238565454008808902853692990183777357658546866177
  | 8 => 515660484364533460328638118913862332375934172300951798910454233509869698439234870067052127315392248103406179311858140290709255886105073297868284612594398498827387420425815140493390087984369571248912510807031300777311833800519468058524702203083277925695033523167585726239912873367508385628799001141360865071841885951618203383698477033304532965946870526972703974461128820647043162453405728159718678188706030380993622971023205513480850421612599494314165332965109432003688378350383896364128599988272327997195067805692003115371937583925388360803379231345127154443212386926720375787768302696184903000002357452581304794983069358022711813014088040932715912510173107807296380501288485996812053583763365624465312427964864082252119760727234685149964537477547942785048193674845167633019438169210486904
  | 9 => 515660521584738118609529462569967534623359452347018937649369587581097524075258411933696902363303735010075634819114619585523387735532596850442786087561658211608531716692630861545919863136260255439490660844916794174310639458231428530904897180180907324005453062594329416398414635983457628657486504705688811012664126320517949269814916574115168343725156371090215515855444523955699138159129206638473900091983914214773292422825679467540435297835052854114628348662544743130586790940251863903093406913926923373886808109244528563591779408520252781994167571847106583058806287411509263021691817050136938817191069099806799727214194061924448559050491224424596474683071758976571491220483221336707235167351406325375706651860548530604843026719388728333888122312959439878395421665734155594667509439097208968
  | 10 => 515660543916860913577722799529206614916542838464834768574657383190425260061941534039212241799460610192305773792801442208649692932746987553712037617484340352565244543277457332204530348374760114693373806213751679715509076159606897389170050416949066745987623413838677526737208197191400346337916719201943640510629794742469930210613073807443867911071151431907213375171470384579827769878094106327158917267717004085112882854522693357372506303445893705893739181604832350700674512830774794618178871846392694321889850378752041002104583188153813635974747133702468723024296667941119537388882444683404820434514759821565207696860597654735549851899532599463543334495021630409180198829959129245059602159604757100538701207642355648286812339713883559561168010280136099974982529738401099208363682706810470548
  | 11 => 515660551360901845233858384606124650234118921735320139782682776900642925062022015258454001061141178660505741518892839996966808034157646961167146939645800871362197307354668254261590877378099563583052195207802478132797930438082709109866705718055498981527116144457272036329573045286479599666266350902158731732370977594798703449443695075315805700209844323327590435035459522546050816758776856716039894379975168455159467686719354677448304236922719034265601669311598052168789351672865392559522806465654181107228479318235742923573055981253365578141339504325467088010693175207837260270037748634227657866539506244611085500396948158639014106900982346211275888572233085078617937791135679152781806126967511248600906191810525301202383203287607012219931957949047179218222459135273033544441003165498998948
  | 12 => 515660603469188366826807480144550897457151504628717738238860532872166580062585383793146315892876624777916030781700652830220922577018078658958077396443011655792380339551676694121940238167918694030709316978867481485568259611725125755083173429252205796734367998555775874790655507630716534132119196688293152648006275255183224233922047727314232151198451250551331819339616815731629624177748314895709145677083061623078368360058213033481853689261598086468742533058196136594361477601498587193280030675904753485958937467460136989571523221027882402447943011995320267974228408591298047029622948040708281486117827612347764112478097770152432251484537963118089728697276427483510209718118055842792942705971043035258206111842851227325481158054212721419530236189920089602326369967888970069103469222161909761
  | _ => 0

def rword (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ :=
  tgetN (ruleT s.val) 32 (Nat.add (tgetN 677806030053202756736 7 t.val) (tgetN 650557212750267116677091687183999463197617251559131726911330484388181898161242152562005905889419962899261793440116003195209125234413442065886784661792087470815506039305757657872918701252164946943433378365045961033612816626227120943502207498844392609650556760067715708789319021952151741293789926521648288294792574797889037676896418338087124568061789690421709853162258849388557895226268572447435543071123883336016782926304794188431120714372040598611319229293193257877681956219965829432476466616593955743480415849170351973468006759967920734531800072048007232150760354738677437020876883242239549766056061370537359455831600633585343691381611815330686211118574454927715664246776523656955979889075783951248638781920489962773496164874808087118288641028935788300579765427173912229236507546232564969613983992227984998017608138660158829226523873315348515442216691486081775762307298178225239017061996911969888633360 4
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul t.val 81) c0) (Nat.mul 3 c1)) (Nat.mul 9 c2)) (Nat.mul 27 c3))))

/-- The field of B bits from bit o of the word w. -/
def fld (w o B : ℕ) : ℕ := Nat.mod (Nat.shiftRight w o) (Nat.pow 2 B)

def rk (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 0 2

def re (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 2 6

def rsl (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : Fin 4 :=
  ⟨fld (rword s t c0 c1 c2 c3) (Nat.add 8 (Nat.mul 2 i)) 2 % 4, Nat.mod_lt _ (by norm_num)⟩

def rm (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : ℤ := Int.subNatNat (fld (rword s t c0 c1 c2 c3) (Nat.add 14 (Nat.mul 5 i)) 5) 16

def rl0 (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℤ := Int.ofNat (fld (rword s t c0 c1 c2 c3) 29 3)

/-- The class of slot k in the pattern (c0, c1, c2, c3). -/
def cv (c0 c1 c2 c3 : ℕ) (k : Fin 4) : ℕ := if k.val = 0 then c0 else if k.val = 1 then c1 else if k.val = 2 then c2 else c3

/-- The slack of the slot k below t in x and y, and its constant: pot t - pot (nb t k) at (x, y, s)
is dA t k * x + dB t k * y + dC s t k. -/
def dA (t : Fin 10) (k : Fin 4) : ℤ := Ac t - Ac (nb t k)

def dB (t : Fin 10) (k : Fin 4) : ℤ := Bc t - Bc (nb t k)

def dC (s : Fin 13) (t : Fin 10) (k : Fin 4) : ℤ := Cc s t - Cc s (nb t k)

/-- Kind 0: the edge at position re descends from class s for this pattern. -/
def ok0 (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  Nat.blt (re s t c0 c1 c2 c3) 48 && Nat.beq (srcv (re s t c0 c1 c2 c3)) s.val && Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) t) 1) 8 &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 0)) 1) (Nat.add c0 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 1)) 1) (Nat.add c1 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 2)) 1) (Nat.add c2 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 3)) 1) (Nat.add c3 8)

/-- Kind 1: the Farkas certificate over the slot facts and the bound is valid. -/
def ok1 (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
    decide (0 ≤ rl0 s t c0 c1 c2 c3 ∧
      (rm s t c0 c1 c2 c3 0 < 0 → cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1) ∧ (rm s t c0 c1 c2 c3 1 < 0 → cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 1) ≤ 1) ∧
      (rm s t c0 c1 c2 c3 2 < 0 → cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 2) ≤ 1) ∧
      rm s t c0 c1 c2 c3 0 * dA t (rsl s t c0 c1 c2 c3 0) + rm s t c0 c1 c2 c3 1 * dA t (rsl s t c0 c1 c2 c3 1) + rm s t c0 c1 c2 c3 2 * dA t (rsl s t c0 c1 c2 c3 2) +
        rl0 s t c0 c1 c2 c3 * Ac t = 0 ∧
      rm s t c0 c1 c2 c3 0 * dB t (rsl s t c0 c1 c2 c3 0) + rm s t c0 c1 c2 c3 1 * dB t (rsl s t c0 c1 c2 c3 1) + rm s t c0 c1 c2 c3 2 * dB t (rsl s t c0 c1 c2 c3 2) +
        rl0 s t c0 c1 c2 c3 * Bc t = 0 ∧
      0 < rm s t c0 c1 c2 c3 0 * ((cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0)) +
        rm s t c0 c1 c2 c3 1 * ((cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 1) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 1)) +
        rm s t c0 c1 c2 c3 2 * ((cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 2) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 2)) + rl0 s t c0 c1 c2 c3 * (R0c s + 1 - Cc s t))

/-- Kind 2: the line of slot k1 has no lattice points. -/
def ok2 (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  decide (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1 ∧ rl0 s t c0 c1 c2 c3 ∣ dA t (rsl s t c0 c1 c2 c3 0) ∧ rl0 s t c0 c1 c2 c3 ∣ dB t (rsl s t c0 c1 c2 c3 0) ∧
    ¬ rl0 s t c0 c1 c2 c3 ∣ (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0))

def ruleOK (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  if rk s t c0 c1 c2 c3 = 0 then ok0 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 1 then ok1 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 2 then ok2 s t c0 c1 c2 c3 else false

/-- Every pattern of slack classes that can occur at the maximal potential t has a valid rule. -/
def rulesOK (t : Fin 10) : Bool :=
  (List.range 3).all fun c0 => (List.range 3).all fun c1 => (List.range 3).all fun c2 => (List.range 3).all fun c3 =>
    !adm t c0 c1 c2 c3 || (List.finRange 13).all fun s => !repB s t || ruleOK s t c0 c1 c2 c3

/-- The side certificates and the edge tables. The kernel decisions are definitions, which the
elaborator checks one after another, and the large ones come in pieces (one per potential or class):
as theorems they run in parallel and their memory adds up. -/
def tables_ok_dec : PLift (sidesOK = true ∧ dlOK = true) := ⟨by
  decide +kernel⟩

theorem tables_ok : sidesOK = true ∧ dlOK = true := tables_ok_dec.down

def farsOK0_dec : PLift (farsOK 0 = true) := ⟨by
  decide +kernel⟩

def farsOK1_dec : PLift (farsOK 1 = true) := ⟨by
  decide +kernel⟩

def farsOK2_dec : PLift (farsOK 2 = true) := ⟨by
  decide +kernel⟩

def farsOK3_dec : PLift (farsOK 3 = true) := ⟨by
  decide +kernel⟩

def farsOK4_dec : PLift (farsOK 4 = true) := ⟨by
  decide +kernel⟩

def farsOK5_dec : PLift (farsOK 5 = true) := ⟨by
  decide +kernel⟩

def farsOK6_dec : PLift (farsOK 6 = true) := ⟨by
  decide +kernel⟩

def farsOK7_dec : PLift (farsOK 7 = true) := ⟨by
  decide +kernel⟩

def farsOK8_dec : PLift (farsOK 8 = true) := ⟨by
  decide +kernel⟩

def farsOK9_dec : PLift (farsOK 9 = true) := ⟨by
  decide +kernel⟩

theorem farsOK_all (k : Fin 10) : farsOK k = true := by
  fin_cases k
  exacts [farsOK0_dec.down, farsOK1_dec.down, farsOK2_dec.down, farsOK3_dec.down, farsOK4_dec.down, farsOK5_dec.down, farsOK6_dec.down, farsOK7_dec.down, farsOK8_dec.down, farsOK9_dec.down]

def rulesOK0_dec : PLift (rulesOK 0 = true) := ⟨by
  decide +kernel⟩

def rulesOK1_dec : PLift (rulesOK 1 = true) := ⟨by
  decide +kernel⟩

def rulesOK2_dec : PLift (rulesOK 2 = true) := ⟨by
  decide +kernel⟩

def rulesOK3_dec : PLift (rulesOK 3 = true) := ⟨by
  decide +kernel⟩

def rulesOK4_dec : PLift (rulesOK 4 = true) := ⟨by
  decide +kernel⟩

def rulesOK5_dec : PLift (rulesOK 5 = true) := ⟨by
  decide +kernel⟩

def rulesOK6_dec : PLift (rulesOK 6 = true) := ⟨by
  decide +kernel⟩

def rulesOK7_dec : PLift (rulesOK 7 = true) := ⟨by
  decide +kernel⟩

def rulesOK8_dec : PLift (rulesOK 8 = true) := ⟨by
  decide +kernel⟩

def rulesOK9_dec : PLift (rulesOK 9 = true) := ⟨by
  decide +kernel⟩

theorem rulesOK_all (k : Fin 10) : rulesOK k = true := by
  fin_cases k
  exacts [rulesOK0_dec.down, rulesOK1_dec.down, rulesOK2_dec.down, rulesOK3_dec.down, rulesOK4_dec.down, rulesOK5_dec.down, rulesOK6_dec.down, rulesOK7_dec.down, rulesOK8_dec.down, rulesOK9_dec.down]

theorem far_ok (s : Fin 13) (t j : Fin 10) (hrep : repB s t = true) (hjt : j ≠ t) (hjn : ∀ k, j ≠ nb t k) :
    farXY t j = true ∧ farC s t j = true := by
  have h := farsOK_all t
  unfold farsOK at h
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  have hn : nonadj t j = true := by simp [nonadj, hjt, hjn]
  have h' := h j
  rw [hn] at h'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h'
  have h2 := h'.2 s
  rw [hrep] at h2
  exact ⟨h'.1, by simpa using h2⟩

theorem side_ok (s : Fin 13) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) (hrep : repB s t = true) (hsp : facetB t = true)
    (hi : (kl = 0 ∧ kr = 2 ∧ i = 0) ∨ (kl = 0 ∧ kr = 3 ∧ i = 1) ∨ (kl = 1 ∧ kr = 2 ∧ i = 2) ∨
      (kl = 1 ∧ kr = 3 ∧ i = 3))
    (hl : real t kl = true) (hr : real t kr = true) : sideXY t kl kr i = true ∧ sideC s t kl kr i = true := by
  have h := tables_ok.1
  unfold sidesOK at h
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  have h' := h t
  rw [hsp] at h'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h'
  have key : sideOK t kl kr i = true := by
    rcases hi with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact h'.1.1.1
    · exact h'.1.1.2
    · exact h'.1.2
    · exact h'.2
  unfold sideOK at key
  rw [hl, hr] at key
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at key
  have h2 := key.2 s
  rw [hrep] at h2
  exact ⟨key.1, by simpa using h2⟩

theorem rule_ok (s : Fin 13) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (hrep : repB s t = true) (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
    (ha : adm t c0 c1 c2 c3 = true) : ruleOK s t c0 c1 c2 c3 = true := by
  have h := rulesOK_all t
  unfold rulesOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h c0 h0 c1 h1 c2 h2 c3 h3
  rw [ha] at h'
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_finRange, forall_const] at h'
  have h4 := h' s
  rw [hrep] at h4
  simpa using h4

theorem dlOKl_spec : ∀ (l : List (Fin 13 × Fin 13 × ℤ × ℤ)) (p : ℕ), dlOKl l p = true →
    ∀ i (hi : i < l.length), (srcv (p + i) = l[i].1.val ∧ tgtv (p + i) = l[i].2.1.val ∧ dxv (p + i) = l[i].2.2.1 ∧
      dyv (p + i) = l[i].2.2.2 ∧ (l[i].2.2.1 ≠ 0 ∨ l[i].2.2.2 ≠ 0 ∨ l[i].1 ≠ l[i].2.1)) ∧
      ∀ j, dlv (p + i) j = dl l[i] j ∧ dl l[i] j ≤ 1 ∧ -dl l[i] j ≤ 1
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | e :: l, p, h, i, hi => by
    simp only [dlOKl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i =>
      have h4 := dlOKl_spec l (p + 1) h3 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      exact h4

theorem E_len : E.length = 48 := by
  decide +kernel

/-- The edge at position p of E, read from the tables. -/
theorem edge_of (p : ℕ) (hp : p < 48) : ∃ e ∈ E, e.1.val = srcv p ∧ e.2.1.val = tgtv p ∧
    e.2.2.1 = dxv p ∧ e.2.2.2 = dyv p ∧ ∀ j, dlv p j = dl e j := by
  have hp' : p < E.length := E_len ▸ hp
  obtain ⟨⟨h1, h2, h3, h4, -⟩, h5⟩ := dlOKl_spec E 0 tables_ok.2 p hp'
  simp only [Nat.zero_add] at h1 h2 h3 h4 h5
  exact ⟨E[p], List.getElem_mem hp', h1.symm, h2.symm, h3.symm, h4.symm, fun j => (h5 j).1⟩

theorem E_step : ∀ e ∈ E, ∀ j : Fin 10, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  intro e he j
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ((dlOKl_spec E 0 tables_ok.2 i hi).2 j).2

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact (dlOKl_spec E 0 tables_ok.2 i hi).1.2.2.2.2

theorem adj_of_mem (e : Fin 13 × Fin 13 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

theorem lip (u w : V) (h : G.Adj u w) : F w ≤ F u + 1 := by
  rw [G, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := u
    obtain ⟨x', y', s'⟩ := w
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    apply F_le_all
    intro j
    have hs := (E_step e he j).1
    have hu := le_F (x, y, e.1) j
    rw [shift x y e j]
    omega
  · obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := w
    obtain ⟨x', y', s'⟩ := u
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    apply F_le_all
    intro j
    have hs := (E_step e he j).2
    have hu := le_F (x + e.2.2.1, y + e.2.2.2, e.2.1) j
    rw [shift x y e j] at hu
    omega

theorem step_down (v w : V) (hadj : G.Adj v w) (h : ∀ j, pot w j ≤ F v - 1) : F w + 1 = F v := by
  have hw := F_le_all w (F v - 1) h
  have hl := lip w v hadj.symm
  omega

/-- Slot facts m * c ≤ m * slack for three slots and the bound R0c s + 1 ≤ pot t, with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas_slot (x y : ℤ) (s : Fin 13) (t : Fin 10) (k1 k2 k3 : Fin 4) (c1 c2 c3 m1 m2 m3 l0 : ℤ)
    (hl0 : 0 ≤ l0)
    (ha : m1 * dA t k1 + m2 * dA t k2 + m3 * dA t k3 + l0 * Ac t = 0)
    (hb : m1 * dB t k1 + m2 * dB t k2 + m3 * dB t k3 + l0 * Bc t = 0)
    (hc : 0 < m1 * (c1 - dC s t k1) + m2 * (c2 - dC s t k2) + m3 * (c3 - dC s t k3) + l0 * (R0c s + 1 - Cc s t))
    (h1 : m1 * c1 ≤ m1 * (pot (x, y, s) t - pot (x, y, s) (nb t k1)))
    (h2 : m2 * c2 ≤ m2 * (pot (x, y, s) t - pot (x, y, s) (nb t k2)))
    (h3 : m3 * c3 ≤ m3 * (pot (x, y, s) t - pot (x, y, s) (nb t k3)))
    (hF : R0c s < pot (x, y, s) t) : False := by
  have e0 := mul_le_mul_of_nonneg_left (show R0c s + 1 ≤ pot (x, y, s) t by omega) hl0
  have ha' : (m1 * dA t k1 + m2 * dA t k2 + m3 * dA t k3 + l0 * Ac t) * x = 0 := by rw [ha, zero_mul]
  have hb' : (m1 * dB t k1 + m2 * dB t k2 + m3 * dB t k3 + l0 * Bc t) * y = 0 := by rw [hb, zero_mul]
  simp only [pot, dA, dB, dC] at h1 h2 h3 e0 ha' hb' hc
  linarith

theorem dvd_contra (x y : ℤ) (a b c g : ℤ) (ha : g ∣ a) (hb : g ∣ b) (hc : ¬ g ∣ c) (e : a * x + b * y = c) :
    False :=
  hc (e ▸ dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y))

/-- Beyond F = R0c s every vertex of class s has a neighbor where F is one less. -/
theorem far_step (s : Fin 13) (t : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) (hrep : repB s t = true) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
  have p : ∀ k, 0 ≤ pot (x, y, s) t - pot (x, y, s) (nb t k) := fun k => by
    have := le_F (x, y, s) (nb t k)
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℕ, ∀ k, c k = (scl (pot (x, y, s) t - pot (x, y, s) (nb t k))).val :=
    ⟨_, fun _ => rfl⟩
  have c3 : ∀ k, c k < 3 := fun k => by
    rw [hc k]
    exact (scl _).isLt
  have q : ∀ k, (c k : ℤ) ≤ pot (x, y, s) t - pot (x, y, s) (nb t k) := fun k => by
    rw [hc k]
    exact scl_le _ (p k)
  have e : ∀ k, c k ≤ 1 → pot (x, y, s) t - pot (x, y, s) (nb t k) = c k := fun k hk => by
    rw [hc k] at hk ⊢
    exact scl_eq _ (p k) hk
  have hs : ∀ (m : ℤ) k, (m < 0 → c k ≤ 1) →
      m * (c k : ℤ) ≤ m * (pot (x, y, s) t - pot (x, y, s) (nb t k)) := fun m k hk => by
    by_cases hm : m < 0
    · exact le_of_eq (by rw [e k (hk hm)])
    · exact mul_le_mul_of_nonneg_left (q k) (by omega)
  have hcv : ∀ k, cv (c 0) (c 1) (c 2) (c 3) k = c k := by
    intro k
    fin_cases k <;> rfl
  have hpad : padOK t (c 0) (c 1) (c 2) (c 3) = true := by
    have hk : ∀ k, real t k = true ∨ c k = 0 := fun k => by
      by_cases hr : real t k = true
      · exact Or.inl hr
      right
      simp only [real, decide_eq_true_eq, not_not] at hr
      rw [hc k, hr, sub_self]
      rfl
    simp only [padOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hk 0, hk 1⟩, hk 2⟩, hk 3⟩
  have hadm : adm t (c 0) (c 1) (c 2) (c 3) = true := by
    unfold adm
    rw [hpad, Bool.true_and]
    cases hsp : facetB t
    · rfl
    cases hl : closeL t (c 0) (c 1)
    · rfl
    cases hr : closeR t (c 2) (c 3)
    · rfl
    exfalso
    simp only [closeL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [closeR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hl with ⟨hl, hl1⟩ | ⟨hl, hl1⟩ <;> rcases hr with ⟨hr, hr1⟩ | ⟨hr, hr1⟩
    · obtain ⟨hxy, hc0⟩ := side_ok s t 0 2 0 hrep hsp (Or.inl ⟨rfl, rfl, rfl⟩) hl hr
      exact side s t 0 2 0 hxy hc0 x y (by have := e 0 hl1; omega) (by have := e 2 hr1; omega) h hF
    · obtain ⟨hxy, hc0⟩ := side_ok s t 0 3 1 hrep hsp (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) hl hr
      exact side s t 0 3 1 hxy hc0 x y (by have := e 0 hl1; omega) (by have := e 3 hr1; omega) h hF
    · obtain ⟨hxy, hc0⟩ := side_ok s t 1 2 2 hrep hsp (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) hl hr
      exact side s t 1 2 2 hxy hc0 x y (by have := e 1 hl1; omega) (by have := e 2 hr1; omega) h hF
    · obtain ⟨hxy, hc0⟩ := side_ok s t 1 3 3 hrep hsp (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) hl hr
      exact side s t 1 3 3 hxy hc0 x y (by have := e 1 hl1; omega) (by have := e 3 hr1; omega) h hF
  have hv := rule_ok s t (c 0) (c 1) (c 2) (c 3) hrep (c3 0) (c3 1) (c3 2) (c3 3) hadm
  unfold ruleOK at hv
  split_ifs at hv with k0 k1 k2
  · -- an edge that descends
    simp only [ok0, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, Nat.add_eq, and_assoc] at hv
    obtain ⟨hlen, hsrc, hdiN, hd0, hd1, hd2, hd3⟩ := hv
    have hdi : dlv (re s t (c 0) (c 1) (c 2) (c 3)) t ≤ -1 := by
      unfold dlv
      omega
    have hd' : ∀ k, dlvN (re s t (c 0) (c 1) (c 2) (c 3)) (nb t k) + 1 ≤ c k + 8 := by
      intro k
      fin_cases k
      exacts [hd0, hd1, hd2, hd3]
    have hdk : ∀ k, dlv (re s t (c 0) (c 1) (c 2) (c 3)) (nb t k) ≤ (c k : ℤ) - 1 := fun k => by
      have := hd' k
      unfold dlv
      omega
    obtain ⟨e, hmem, hs1, -, -, -, hdl⟩ := edge_of _ hlen
    rw [hdl] at hdi
    simp only [hdl] at hdk
    have hs' : e.1 = s := Fin.ext (hs1.trans hsrc)
    have ha := adj_of_mem e hmem x y
    rw [hs'] at ha
    refine ⟨_, ha, step_down _ _ ha (fun j => ?_)⟩
    have hsh := shift x y e j
    rw [hs'] at hsh
    rw [hsh]
    have hst := (E_step e hmem j).1
    have hj := le_F (x, y, s) j
    by_cases hjt : j = t
    · subst hjt
      omega
    by_cases hjn : ∃ k, j = nb t k
    · obtain ⟨k, rfl⟩ := hjn
      have := hdk k
      have := q k
      omega
    push Not at hjn
    have hf := far_ok s t j hrep hjt hjn
    have := far s t j hf.1 hf.2 x y h hF
    omega
  · -- a Farkas certificate over the slot facts and the bound
    simp only [ok1, decide_eq_true_eq, hcv] at hv
    obtain ⟨hl0, hn1, hn2, hn3, ha, hb, hcc⟩ := hv
    exact (farkas_slot x y s t _ _ _ _ _ _ _ _ _ _ hl0 ha hb hcc (hs _ _ hn1) (hs _ _ hn2) (hs _ _ hn3)
      (h ▸ hF)).elim
  · -- a line without lattice points
    simp only [ok2, decide_eq_true_eq, hcv] at hv
    obtain ⟨hc1, ha, hb, hcc⟩ := hv
    have e1 := e _ hc1
    simp only [pot] at e1
    exact (dvd_contra x y _ _ _ _ ha hb hcc (by simp only [dA, dB, dC]; linear_combination e1)).elim

theorem far_step' (v : V) (t : Fin 10) (h : F v = pot v t) (hF : R0c v.2.2 < F v) (hrep : repB v.2.2 t = true) :
    ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  exact far_step s t x y h hF hrep

def rep_all_dec : PLift ((∀ s t, repB s t = true) ∧ ∀ s, repC s = true) := ⟨by
  decide +kernel⟩

theorem rep_all : (∀ s t, repB s t = true) ∧ ∀ s, repC s = true := rep_all_dec.down

theorem far_desc (v : V) (hF : R0c v.2.2 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨t, ht⟩ := exists_F (x, y, s)
  exact far_step s t x y ht hF (rep_all.1 s t)

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 13) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
    (hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ lq ∧
      l1 * Ac a1 + l2 * Ac a2 + l3 * Ac a3 + lq * px = 0 ∧
      l1 * Bc a1 + l2 * Bc a2 + l3 * Bc a3 + lq * py = 0 ∧
      0 < l1 * (Cc s a1 - t) + l2 * (Cc s a2 - t) + l3 * (Cc s a3 - t) + lq * q)
    (h1 : pot (x, y, s) a1 ≤ t) (h2 : pot (x, y, s) a2 ≤ t) (h3 : pot (x, y, s) a3 ≤ t)
    (h4 : px * x + py * y + q ≤ 0) : False := by
  obtain ⟨hl1, hl2, hl3, hlq, hx, hy, hk⟩ := hc
  have e1 := mul_le_mul_of_nonneg_left h1 hl1
  have e2 := mul_le_mul_of_nonneg_left h2 hl2
  have e3 := mul_le_mul_of_nonneg_left h3 hl3
  have e4 := mul_le_mul_of_nonneg_left h4 hlq
  have hx' : (l1 * Ac a1 + l2 * Ac a2 + l3 * Ac a3 + lq * px) * x = 0 := by rw [hx, zero_mul]
  have hy' : (l1 * Bc a1 + l2 * Bc a2 + l3 * Bc a3 + lq * py) * y = 0 := by rw [hy, zero_mul]
  simp only [pot] at e1 e2 e3
  nlinarith [e1, e2, e3, e4, hx', hy', hk]

/-- The near box of class s: the cells |x| ≤ BXn s, |y| ≤ BYn s hold its vertices with F ≤ R0c s. -/
def BXn (s : Fin 13) : ℕ := tgetN 50309886 2 s.val

def BYn (s : Fin 13) : ℕ := tgetN 50315262 2 s.val

theorem nb_c0 : ∀ s : Fin 13, 0 < 1 * (Cc s 8 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 5 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c0 : ∀ s : Fin 13, 0 < 1 * (Cc s 8 - (9)) + 0 * (Cc s 0 - (9)) + 0 * (Cc s 0 - (9)) + 5 * (3) := by
  decide +kernel

theorem nb_c1 : ∀ s : Fin 13, 0 < 1 * (Cc s 3 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 5 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c1 : ∀ s : Fin 13, 0 < 4 * (Cc s 4 - (9)) + 1 * (Cc s 9 - (9)) + 0 * (Cc s 0 - (9)) + 15 * (3) := by
  decide +kernel

theorem nb_c2 : ∀ s : Fin 13, 0 < 1 * (Cc s 2 - (R0c s)) + 5 * (Cc s 9 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 25 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c2 : ∀ s : Fin 13, 0 < 1 * (Cc s 2 - (9)) + 5 * (Cc s 9 - (9)) + 0 * (Cc s 0 - (9)) + 25 * (3) := by
  decide +kernel

theorem nb_c3 : ∀ s : Fin 13, 0 < 1 * (Cc s 5 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 5 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c3 : ∀ s : Fin 13, 0 < 1 * (Cc s 5 - (9)) + 0 * (Cc s 0 - (9)) + 0 * (Cc s 0 - (9)) + 5 * (3) := by
  decide +kernel

theorem nn_c : ∀ s : Fin 13, 0 < 20 * (Cc s 4 - (-1)) + 15 * (Cc s 8 - (-1)) + 5 * (Cc s 9 - (-1)) + 0 * (0) := by
  decide +kernel

/-- Every vertex of class s with F at most R0c s lies in the near box of class s. -/
theorem near_box (x y : ℤ) (s : Fin 13) (hF : F (x, y, s) ≤ R0c s) :
    -(BXn s : ℤ) ≤ x ∧ x ≤ BXn s ∧ -(BYn s : ℤ) ≤ y ∧ y ≤ BYn s := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 8 0 0 (R0c s) 1 0 0 (1) (0) ((BXn s : ℤ) + 1) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 0 0 (R0c s) 1 0 0 (-1) (0) ((BXn s : ℤ) + 1) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 9 0 (R0c s) 1 5 0 (0) (1) ((BYn s : ℤ) + 1) 25 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 0 0 (R0c s) 1 0 0 (0) (-1) ((BYn s : ℤ) + 1) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c3 s⟩ (u _) (u _) (u _) (by omega)

/-- Every vertex with F at most 9 lies in the cells |x| ≤ 2, |y| ≤ 2. -/
theorem small_box (x y : ℤ) (s : Fin 13) (hF : F (x, y, s) ≤ 9) :
    -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 8 0 0 (9) 1 0 0 (1) (0) (3) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 9 0 (9) 4 1 0 (-1) (0) (3) 15 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 9 0 (9) 1 5 0 (0) (1) (3) 25 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 0 0 (9) 1 0 0 (0) (-1) (3) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 8 9 (-1) 20 15 5 (0) (0) (0) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nn_c s⟩ (u _) (u _) (u _) (by norm_num)

/-- The vertices near v0 where the graph distance is not the largest potential, with the distance. -/
def O : List (V × ℤ) :=
  [((0, 0, 1), 0),
    ((0, 0, 0), 1),
    ((0, 0, 2), 1),
    ((0, 0, 6), 1),
    (((-1), (-1), 11), 2),
    ((0, 0, 3), 2),
    ((0, 0, 5), 2),
    ((0, 0, 7), 2),
    ((0, 0, 9), 2),
    (((-1), (-1), 10), 3),
    ((0, (-1), 4), 3),
    ((0, 0, 4), 3),
    ((0, 0, 8), 3),
    (((-1), (-1), 9), 4),
    ((0, (-1), 5), 4),
    ((0, 1, 3), 4),
    (((-1), (-1), 2), 5),
    (((-1), (-1), 8), 5),
    ((0, (-1), 6), 5),
    ((0, 1, 2), 5),
    (((-1), (-1), 3), 6),
    ((0, (-1), 1), 6),
    ((0, 1, 1), 6),
    ((0, 1, 6), 7)]

/-- The cells (x, y) of the vertices of O. -/
def obox (x y : ℤ) : Bool := decide ((-1) ≤ x ∧ x ≤ 0 ∧ (-1) ≤ y ∧ y ≤ 1)

/-- The distance formula: the value listed in O, and the largest potential off O. -/
def fv (v : V) : ℤ :=
  if obox v.1 v.2.1 then ((O.find? fun o => decide (o.1 = v)).map Prod.snd).getD (F v) else F v

theorem fv_out (x y : ℤ) (s : Fin 13) (h : ¬ obox x y = true) : fv (x, y, s) = F (x, y, s) := by
  unfold fv
  rw [if_neg h]

theorem fv_of (v : V) (h : ∀ o ∈ O, o.1 ≠ v) : fv v = F v := by
  have hn : O.find? (fun o => decide (o.1 = v)) = none := by
    rw [List.find?_eq_none]
    intro o ho
    simpa using h o ho
  unfold fv
  split_ifs
  · simp [hn]
  · rfl

/-- The vertices of O have F and fv below 9 and fv nonnegative, and fv changes by at most one
along the edges at the vertices of O. -/
def O_ok_dec : PLift (∀ o ∈ O, F o.1 < 9 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 9 ∧ ∀ e ∈ E,
    (e.1 = o.1.2.2 → fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1) ∧
    (e.2.1 = o.1.2.2 → fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1)) := ⟨by
  decide +kernel⟩

theorem O_ok : ∀ o ∈ O, F o.1 < 9 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 9 ∧ ∀ e ∈ E,
    (e.1 = o.1.2.2 → fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1) ∧
    (e.2.1 = o.1.2.2 → fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1) := O_ok_dec.down

theorem adj_cases (u w : V) (h : G.Adj u w) : ∃ e ∈ E,
    (e.1 = u.2.2 ∧ w = (u.1 + e.2.2.1, u.2.1 + e.2.2.2, e.2.1)) ∨
    (e.2.1 = u.2.2 ∧ w = (u.1 - e.2.2.1, u.2.1 - e.2.2.2, e.1)) := by
  rw [G, SimpleGraph.fromRel_adj] at h
  obtain ⟨x, y, s⟩ := u
  obtain ⟨x', y', s'⟩ := w
  obtain ⟨-, ⟨e, he, h1, h2, h3, h4⟩ | ⟨e, he, h1, h2, h3, h4⟩⟩ := h
  · simp only at h1 h2 h3 h4
    exact ⟨e, he, Or.inl ⟨h1.symm, by rw [h2, h3, h4]⟩⟩
  · simp only at h1 h2 h3 h4
    refine ⟨e, he, Or.inr ⟨h2.symm, ?_⟩⟩
    rw [h1, h3, h4]
    simp

theorem lip_fv (u w : V) (h : G.Adj u w) : fv w ≤ fv u + 1 := by
  by_cases hu : ∃ o ∈ O, o.1 = u
  · obtain ⟨o, ho, rfl⟩ := hu
    obtain ⟨-, -, -, hO⟩ := O_ok o ho
    obtain ⟨e, he, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := adj_cases o.1 w h
    · exact ((hO e he).1 h1).1
    · exact ((hO e he).2 h1).1
  by_cases hw : ∃ o ∈ O, o.1 = w
  · obtain ⟨o, ho, rfl⟩ := hw
    obtain ⟨-, -, -, hO⟩ := O_ok o ho
    obtain ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := adj_cases o.1 u h.symm
    · rw [h2]
      exact ((hO e he).1 h1).2
    · rw [h2]
      exact ((hO e he).2 h1).2
  push Not at hu hw
  rw [fv_of u hu, fv_of w hw]
  exact lip u w h

theorem fv_nonneg (v : V) : 0 ≤ fv v := by
  by_cases hv : ∃ o ∈ O, o.1 = v
  · obtain ⟨o, ho, rfl⟩ := hv
    exact (O_ok o ho).2.1
  push Not at hv
  rw [fv_of v hv]
  exact F_nonneg v

def R0c_ge_dec : PLift (∀ s, 9 ≤ R0c s) := ⟨by
  decide +kernel⟩

theorem R0c_ge : ∀ s, 9 ≤ R0c s := R0c_ge_dec.down

/-- The near check computes the potentials as differences of natural numbers: at the cell (a, b) of
the near box of class s, pot = potP - potQ. -/
def apN (i : Fin 10) : ℕ := tgetN 19280 3 i.val

def amN (i : Fin 10) : ℕ := tgetN 229376000 3 i.val

def bpN (i : Fin 10) : ℕ := tgetN 11964416 3 i.val

def bmN (i : Fin 10) : ℕ := tgetN 536871277 3 i.val

def kpN (s : Fin 13) (i : Fin 10) : ℕ := tgetN 1637916181740357834969347030980680989995814799743849100348626380762128546190452761801287335168269706175622075835734556060115558316589713111458758672947635735726769626136041616770712641204310245643 5 (Nat.add (Nat.mul s.val 10) i.val)

def kmN (s : Fin 13) (i : Fin 10) : ℕ := tgetN 451569340374535947115091576606953349968702974779494070361505860433563255356516653263463489724927160538084562572446376899186365257482049665409221765841669556733562230291822592337698760264352768 5 (Nat.add (Nat.mul s.val 10) i.val)

def pqOK : Bool :=
  (List.finRange 10).all fun i => decide ((apN i : ℤ) - amN i = Ac i ∧ (bpN i : ℤ) - bmN i = Bc i) &&
    (List.finRange 13).all fun s => decide ((kpN s i : ℤ) - kmN s i = Cc s i - Ac i * BXn s - Bc i * BYn s)

def pq_ok_dec : PLift (pqOK = true) := ⟨by
  decide +kernel⟩

theorem pq_ok : pqOK = true := pq_ok_dec.down

def potP (s : Fin 13) (a b : ℕ) (i : Fin 10) : ℕ :=
  Nat.add (Nat.add (Nat.mul (apN i) a) (Nat.mul (bpN i) b)) (kpN s i)

def potQ (s : Fin 13) (a b : ℕ) (i : Fin 10) : ℕ :=
  Nat.add (Nat.add (Nat.mul (amN i) a) (Nat.mul (bmN i) b)) (kmN s i)

theorem potPQ_val (s : Fin 13) (a b : ℕ) (i : Fin 10) :
    (potP s a b i : ℤ) - potQ s a b i = pot ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) i := by
  have h := pq_ok
  unfold pqOK at h
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, decide_eq_true_eq, forall_const] at h
  obtain ⟨⟨hA, hB⟩, hK⟩ := h i
  have hK' := hK s
  simp only [potP, potQ, pot, Nat.add_eq, Nat.mul_eq]
  push_cast
  linear_combination (a : ℤ) * hA + (b : ℤ) * hB + hK'

/-- The larger of the differences p.1 - p.2 and q.1 - q.2, as a pair. -/
def pmax (p q : ℕ × ℕ) : ℕ × ℕ := cond (Nat.ble (Nat.add p.1 q.2) (Nat.add q.1 p.2)) q p

theorem pmax_val (p q : ℕ × ℕ) :
    ((pmax p q).1 : ℤ) - (pmax p q).2 = max ((p.1 : ℤ) - p.2) ((q.1 : ℤ) - q.2) := by
  unfold pmax
  cases h : Nat.ble (Nat.add p.1 q.2) (Nat.add q.1 p.2)
  · have h' : ¬ Nat.add p.1 q.2 ≤ Nat.add q.1 p.2 := fun hc =>
      absurd (Nat.ble_eq_true_of_le hc) (by rw [h]; decide)
    simp only [cond_false, Nat.add_eq] at h' ⊢
    omega
  · have h' := Nat.le_of_ble_eq_true h
    simp only [cond_true, Nat.add_eq] at h' ⊢
    omega

/-- F at the cell (a, b) of the near box of class s, and at the end of the edge at position p from
there, as pairs. -/
def FP (s : Fin 13) (a b : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((potP s a b 0, potQ s a b 0)) (potP s a b 1, potQ s a b 1)) (potP s a b 2, potQ s a b 2)) (potP s a b 3, potQ s a b 3)) (potP s a b 4, potQ s a b 4)) (potP s a b 5, potQ s a b 5)) (potP s a b 6, potQ s a b 6)) (potP s a b 7, potQ s a b 7)) (potP s a b 8, potQ s a b 8)) (potP s a b 9, potQ s a b 9)

def FPn (s : Fin 13) (a b p : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((Nat.add (potP s a b 0) (dlvN p 0), Nat.add (potQ s a b 0) 8)) (Nat.add (potP s a b 1) (dlvN p 1), Nat.add (potQ s a b 1) 8)) (Nat.add (potP s a b 2) (dlvN p 2), Nat.add (potQ s a b 2) 8)) (Nat.add (potP s a b 3) (dlvN p 3), Nat.add (potQ s a b 3) 8)) (Nat.add (potP s a b 4) (dlvN p 4), Nat.add (potQ s a b 4) 8)) (Nat.add (potP s a b 5) (dlvN p 5), Nat.add (potQ s a b 5) 8)) (Nat.add (potP s a b 6) (dlvN p 6), Nat.add (potQ s a b 6) 8)) (Nat.add (potP s a b 7) (dlvN p 7), Nat.add (potQ s a b 7) 8)) (Nat.add (potP s a b 8) (dlvN p 8), Nat.add (potQ s a b 8) 8)) (Nat.add (potP s a b 9) (dlvN p 9), Nat.add (potQ s a b 9) 8)

theorem FP_val (s : Fin 13) (a b : ℕ) :
    ((FP s a b).1 : ℤ) - (FP s a b).2 = F ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  simp only [FP, F, pmax_val, potPQ_val]

theorem FPn_val (s : Fin 13) (a b p : ℕ) (hp : p < 48) (hs : srcv p = s.val) :
    ((FPn s a b p).1 : ℤ) - (FPn s a b p).2 = F ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  obtain ⟨e, -, h1, h2, h3, h4, h5⟩ := edge_of p hp
  have hs' : e.1 = s := Fin.ext (h1.trans hs)
  have ht' : e.2.1 = tgtF p := Fin.ext (by
    show e.2.1.val = tgtv p % 13
    rw [← h2, Nat.mod_eq_of_lt e.2.1.isLt])
  have key : ∀ i, ((Nat.add (potP s a b i) (dlvN p i) : ℕ) : ℤ) - (Nat.add (potQ s a b i) 8 : ℕ) =
      pot ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) i := by
    intro i
    have hsh := shift ((a : ℤ) - BXn s) ((b : ℤ) - BYn s) e i
    rw [hs', ht', h3, h4] at hsh
    rw [hsh, ← potPQ_val, ← h5 i]
    simp only [dlv, Nat.add_eq]
    push_cast
    ring
  simp only [FPn, F, pmax_val, key]

/-- fv at the cell (a, b) of the near box of class s, and at the end of the edge at position p from
there: by the pairs off the cells of O. -/
def fvN (s : Fin 13) (a b : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s) ((b : ℤ) - BYn s) then fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s)
  else Int.subNatNat (FP s a b).1 (FP s a b).2

def fvNn (s : Fin 13) (a b p : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s + dxv p) ((b : ℤ) - BYn s + dyv p) then
    fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p)
  else Int.subNatNat (FPn s a b p).1 (FPn s a b p).2

theorem fvN_eq (s : Fin 13) (a b : ℕ) : fvN s a b = fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  unfold fvN
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FP_val, Int.subNatNat_eq_coe]

theorem fvNn_eq (s : Fin 13) (a b p : ℕ) (hp : p < 48) (hs : srcv p = s.val) :
    fvNn s a b p = fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  unfold fvNn
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FPn_val s a b p hp hs, Int.subNatNat_eq_coe]

/-- For each class s and each cell of its near box with F at most R0c s, other than v0, the position
in E of an edge along which fv decreases. -/
def nearT (s : ℕ) : ℕ :=
  match s with
  | 0 => 45314722280330236352137024602029184037945344
  | 1 => 31575958049487846573805101549939382961286045066708182992127142015425251815704937910592
  | 2 => 917189895031927270294187867034300838669671001186660708722663705085780984320
  | 3 => 1261809187697392081918889767755518035707978208609546257636067618978794881792
  | 4 => 95627721750053212866417438975279968921032278105445046748241
  | 5 => 7754084157782006745075699328915558268522653979796239505499282
  | 6 => 9386558175238633814430374189687716631017615307979600526927254
  | 7 => 611669805212952436830239385407582687838963289
  | 8 => 3216446731544338241833615645789988614966678351247749875287076936375256602432
  | 9 => 57436333098004131401297361725383496752498463017035196911575426707623385152
  | 10 => 62820989325942420451327720131925951468280923250351227665575473728928766272
  | 11 => 248691843876233551495047029549832445391681044423502054189440
  | 12 => 928341100288956550395935921749011309
  | _ => 0

def nearE (s : Fin 13) (a b : ℕ) : ℕ := tgetN (nearT s.val) 6 (a * (2 * BYn s + 1) + b)

/-- The near check of class s. -/
def nearOK (s : Fin 13) : Bool :=
  !repC s || (List.range (2 * BXn s + 1)).all fun a => (List.range (2 * BYn s + 1)).all fun b =>
    Nat.blt (Nat.add (R0N s) (FP s a b).2) (FP s a b).1 ||
      (Nat.beq a (BXn s) && Nat.beq b (BYn s) && Nat.beq s.val 1) ||
      (Nat.blt (nearE s a b) 48 && Nat.beq (srcv (nearE s a b)) s.val &&
        decide (fvNn s a b (nearE s a b) + 1 = fvN s a b))

def nearOK0_dec : PLift (nearOK 0 = true) := ⟨by
  decide +kernel⟩

def nearOK1_dec : PLift (nearOK 1 = true) := ⟨by
  decide +kernel⟩

def nearOK2_dec : PLift (nearOK 2 = true) := ⟨by
  decide +kernel⟩

def nearOK3_dec : PLift (nearOK 3 = true) := ⟨by
  decide +kernel⟩

def nearOK4_dec : PLift (nearOK 4 = true) := ⟨by
  decide +kernel⟩

def nearOK5_dec : PLift (nearOK 5 = true) := ⟨by
  decide +kernel⟩

def nearOK6_dec : PLift (nearOK 6 = true) := ⟨by
  decide +kernel⟩

def nearOK7_dec : PLift (nearOK 7 = true) := ⟨by
  decide +kernel⟩

def nearOK8_dec : PLift (nearOK 8 = true) := ⟨by
  decide +kernel⟩

def nearOK9_dec : PLift (nearOK 9 = true) := ⟨by
  decide +kernel⟩

def nearOK10_dec : PLift (nearOK 10 = true) := ⟨by
  decide +kernel⟩

def nearOK11_dec : PLift (nearOK 11 = true) := ⟨by
  decide +kernel⟩

def nearOK12_dec : PLift (nearOK 12 = true) := ⟨by
  decide +kernel⟩

theorem nearOK_all (k : Fin 13) : nearOK k = true := by
  fin_cases k
  exacts [nearOK0_dec.down, nearOK1_dec.down, nearOK2_dec.down, nearOK3_dec.down, nearOK4_dec.down, nearOK5_dec.down, nearOK6_dec.down, nearOK7_dec.down, nearOK8_dec.down, nearOK9_dec.down, nearOK10_dec.down, nearOK11_dec.down, nearOK12_dec.down]

/-- Every vertex of a checked class s with F at most R0c s, other than v0, has a neighbor where fv is
one less. -/
theorem near_desc_rep (v : V) (hF : F v ≤ R0c v.2.2) (hv : v ≠ v0) (hrep : repC v.2.2 = true) :
    ∃ w, G.Adj v w ∧ fv w + 1 = fv v := by
  obtain ⟨x, y, s⟩ := v
  change F (x, y, s) ≤ R0c s at hF
  change repC s = true at hrep
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h1 := nearOK_all s
  unfold nearOK at h1
  rw [hrep] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h' := h1 (x + BXn s).toNat (by omega) (y + BYn s).toNat (by omega)
  have ex : (((x + BXn s).toNat : ℕ) : ℤ) - BXn s = x := by omega
  have ey : (((y + BYn s).toNat : ℕ) : ℤ) - BYn s = y := by omega
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h'
  rcases h' with (h2 | ⟨⟨h2, h3⟩, h4⟩) | ⟨⟨hlt, hs⟩, hfe⟩
  · have hv' := FP_val s (x + BXn s).toNat (y + BYn s).toNat
    rw [ex, ey] at hv'
    have hr : R0c s = (R0N s : ℤ) := rfl
    omega
  · exfalso
    apply hv
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hs0 : s = 1 := Fin.ext h4
    rw [hx0, hy0, hs0]
    rfl
  · rw [fvNn_eq _ _ _ _ hlt hs, fvN_eq, ex, ey] at hfe
    obtain ⟨e, hmem, h1, h2, h3, h4, -⟩ := edge_of _ hlt
    have ha := adj_of_mem e hmem x y
    have hs' : e.1 = s := Fin.ext (h1.trans hs)
    have ht' : e.2.1 = tgtF (nearE s (x + BXn s).toNat (y + BYn s).toNat) := Fin.ext (by
      show e.2.1.val = tgtv (nearE s (x + BXn s).toNat (y + BYn s).toNat) % 13
      rw [← h2, Nat.mod_eq_of_lt e.2.1.isLt])
    rw [hs', ht', h3, h4] at ha
    exact ⟨_, ha, hfe⟩

theorem near_desc (v : V) (hF : F v ≤ R0c v.2.2) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ fv w + 1 = fv v :=
  near_desc_rep v hF hv (rep_all.2 v.2.2)

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ fv w + 1 = fv v := by
  by_cases hF : F v ≤ R0c v.2.2
  · exact near_desc v hF hv
  have hge := R0c_ge v.2.2
  have hvO : ∀ o ∈ O, o.1 ≠ v := fun o ho he => by
    have := (O_ok o ho).1
    rw [he] at this
    omega
  obtain ⟨w, hw, he⟩ := far_desc v (by omega)
  have hwO : ∀ o ∈ O, o.1 ≠ w := fun o ho hw' => by
    have := (O_ok o ho).1
    rw [hw'] at this
    omega
  exact ⟨w, hw, by rw [fv_of v hvO, fv_of w hwO]; exact he⟩

theorem dist_eq_of_potential {W : Type*} (H : SimpleGraph W) (w0 : W) (f : W → ℕ)
    (h0 : f w0 = 0) (hlip : ∀ u w, H.Adj u w → f w ≤ f u + 1)
    (hdesc : ∀ v, v ≠ w0 → ∃ w, H.Adj v w ∧ f w + 1 = f v) (v : W) :
    H.dist w0 v = f v := by
  have up : ∀ n, ∀ v, f v = n → ∃ p : H.Walk w0 v, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro v hv
      by_cases hv0 : v = w0
      · subst hv0
        exact ⟨SimpleGraph.Walk.nil, rfl⟩
      · obtain ⟨w, -, hw⟩ := hdesc v hv0
        omega
    | succ n ih =>
      intro v hv
      have hv0 : v ≠ w0 := by
        rintro rfl
        omega
      obtain ⟨w, hvw, hw⟩ := hdesc v hv0
      obtain ⟨p, hp⟩ := ih w (by omega)
      exact ⟨p.concat hvw.symm, by rw [SimpleGraph.Walk.length_concat, hp]⟩
  have low : ∀ (u : W) (p : H.Walk u v), f v ≤ f u + p.length := by
    intro u p
    induction p with
    | nil => simp
    | cons h p ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := hlip _ _ h
      omega
  obtain ⟨p, hp⟩ := up (f v) v rfl
  apply le_antisymm
  · exact (H.dist_le p).trans hp.le
  · obtain ⟨q, hq⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (G := H) ⟨p⟩
    have := low w0 q
    omega

/-- The graph distance from v0 is fv: the value listed in O, and the largest potential off O. -/
theorem dist_eq (v : V) : G.dist v0 v = (fv v).toNat := by
  apply dist_eq_of_potential G v0 (fun v => (fv v).toNat)
  · show (fv v0).toNat = 0
    decide +kernel
  · intro u w h
    have := lip_fv u w h
    have := fv_nonneg w
    have := fv_nonneg u
    show (fv w).toNat ≤ (fv u).toNat + 1
    omega
  · intro v hv
    obtain ⟨w, hw, he⟩ := desc v hv
    refine ⟨w, hw, ?_⟩
    have := fv_nonneg w
    show (fv w).toNat + 1 = (fv v).toNat
    omega

/-- Off the list O the graph distance from v0 is the largest potential. -/
theorem dist_eq_F (v : V) (hv : ∀ o ∈ O, o.1 ≠ v) : G.dist v0 v = (F v).toNat := by
  rw [dist_eq v, fv_of v hv]

/-- From n = 9 on, the coordination sequence counts the level set F = n. -/
theorem a_eq_F (n : ℕ) (hn : 9 ≤ n) : a n = Set.ncard {v : V | (F v).toNat = n} := by
  unfold a
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [dist_eq v]
  by_cases hv : ∃ o ∈ O, o.1 = v
  · obtain ⟨o, ho, rfl⟩ := hv
    obtain ⟨h1, h2, h3, -⟩ := O_ok o ho
    omega
  push Not at hv
  rw [fv_of v hv]

/-- The cells |x| ≤ 2, |y| ≤ 2, every class. -/
def boxF : Finset V :=
  (Finset.range 5 ×ˢ Finset.range 5 ×ˢ (Finset.univ : Finset (Fin 13))).map
    ⟨fun p => ((p.1 : ℤ) - 2, (p.2.1 : ℤ) - 2, p.2.2), fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (Prod.ext (by omega) h.2.2)⟩

theorem mem_boxF (v : V) (h : (fv v).toNat ≤ 9) : v ∈ boxF := by
  obtain ⟨x, y, s⟩ := v
  have hb : F (x, y, s) ≤ 9 := by
    by_cases hv : ∃ o ∈ O, o.1 = (x, y, s)
    · obtain ⟨o, ho, he⟩ := hv
      have := (O_ok o ho).1
      rw [he] at this
      omega
    push Not at hv
    rw [fv_of _ hv] at h
    have := F_nonneg (x, y, s)
    omega
  obtain ⟨h1, h2, h3, h4⟩ := small_box x y s hb
  rw [boxF, Finset.mem_map]
  refine ⟨((x + 2).toNat, (y + 2).toNat, s), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    omega
  · show ((((x + 2).toNat : ℕ) : ℤ) - 2, (((y + 2).toNat : ℕ) : ℤ) - 2, s) = (x, y, s)
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨by omega, by omega, rfl⟩

/-- Up to n = 9, a n counts the cells of the box where fv = n. -/
theorem a_small (n : ℕ) (hn : n ≤ 9) : a n = (boxF.filter fun v => (fv v).toNat = n).card := by
  unfold a
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Finset.coe_filter]
  rw [dist_eq v]
  constructor
  · intro h
    exact ⟨mem_boxF v (by omega), h⟩
  · rintro ⟨-, h⟩
    exact h

/-- The coordination sequence below n = 9. -/
theorem small_vals : (List.range 9).map a = [1, 3, 6, 9, 11, 13, 17, 22, 27] := by
  rw [List.map_congr_left (fun n hn => a_small n (by rw [List.mem_range] at hn; omega))]
  decide +kernel


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 9 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 5 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 229022541 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 306313515 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 3

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 91979404292 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 5

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 363234 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 2

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 363072 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 10) : ℤ := beN i.val

theorem prim : ∀ i : Fin 10, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 10) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 10) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 10, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 13) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 13) (i j : Fin 10) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 10) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 10) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 13) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
  intro u u' h
  simp only [par, Prod.mk.injEq] at h
  have hb := (prim i).2.2.2
  have h1 : Bp i * (u - u') = 0 := by linarith [h.1]
  have h2 : Ap i * (u - u') = 0 := by linarith [h.2.1]
  have h3 : (u - u') = (u - u') * (al i * Ap i + be i * Bp i) := by rw [hb, mul_one]
  have : u - u' = 0 := by
    rw [h3]
    linear_combination (al i) * h2 + (be i) * h1
  linarith

/-- Some facet attains the maximum. -/
theorem F_attained (v : V) : ∃ k : Fin 10, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 10 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 10) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
  constructor
  · rintro rfl
    exact fi_spec v
  · rintro ⟨h1, h2⟩
    obtain ⟨g1, g2⟩ := fi_spec v
    rcases lt_trichotomy (fi v) i with h | h | h
    · exact absurd g1 (ne_of_lt (h2 _ h))
    · exact h
    · exact absurd h1 (ne_of_lt (g2 _ h))

theorem ite01 (c : Prop) [Decidable c] : (0 : ℤ) ≤ (if c then 1 else 0) ∧ (if c then 1 else 0 : ℤ) ≤ 1 := by
  split_ifs <;> norm_num

/-- On the sphere F = n, the first maximal facet is i exactly when potential i is n and every
potential j is at most n - [j < i]. -/
theorem piece_iff (v : V) (i : Fin 10) (n : ℤ) :
    (F v = n ∧ fi v = i) ↔ (pot v i = n ∧ ∀ j, pot v j ≤ n - (if j < i then 1 else 0)) := by
  rw [fi_iff]
  constructor
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    split_ifs with hj
    · have := h2 j hj
      omega
    · have := le_F v j
      omega
  · rintro ⟨h1, h2⟩
    have h3 : ∀ j, pot v j ≤ n := fun j => le_trans (h2 j) (sub_le_self n (ite01 _).1)
    have hF : F v = n := le_antisymm (F_le_all v n h3) (h1 ▸ le_F v i)
    refine ⟨hF, hF ▸ h1, fun j hj => ?_⟩
    have := h2 j
    rw [if_pos hj] at this
    omega

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (9 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 215498204614000852675268421274417072844523787851015287819252813167278777035629175963297914069477565595725594706581380368875973614528004084442595328 5 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 10) (j : Fin 10) : ℤ := cf1N (j.val + 10 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 309355313323519153361747102073265806450449150417723933121328121791303899275299271691674946060168236168707634817017179115194139988310382517691782144 5 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 10) (j : Fin 10) : ℤ := cf2N (j.val + 10 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 830069078339171807473676677623931370282633541794102978926885929338742866367099777864068995515711894795411191109919232 4 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 10) (j : Fin 10) : ℤ := cf3N (j.val + 10 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 911499137106207654886000869319293540711499382787436835637380317768398317223997088340753506540254666554936005220245504 4 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 10) (j : Fin 10) : ℤ := cf0N (j.val + 10 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 1262315381850715786872216715926657636157987884975535450467687736026317852016457172433700546660821072333929815978882220 3 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 3

def cT (s : Fin 13) (i : Fin 10) : ℤ := cTN (i.val + 10 * s.val)

theorem cT_eq : ∀ s : Fin 13, ∀ i : Fin 10, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 13) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (9 - cT s i)

instance (i j : Fin 10) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 10, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

/-- certC in natural numbers, for the kernel: Cc = cTV - 3, the negative terms moved across; the
previous facet of i is (i + 9) % 10, the next one (i + 1) % 10. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 10 * i) + cf2V (j + 10 * i) + cf0V (j + 10 * i)) * cTV (i + 10 * s) +
      cf3V (j + 10 * i) * cTV (j + 10 * s))
    (cf1V (j + 10 * i) * (cTV ((i + 9) % 10 + 10 * s) + (if (i + 9) % 10 < i then 1 else 0)) +
      cf2V (j + 10 * i) * (cTV ((i + 1) % 10 + 10 * s) + (if (i + 1) % 10 < i then 1 else 0)) +
      cf3V (j + 10 * i) * cTV (i + 10 * s) + cf0V (j + 10 * i) * 12)

def certOK : Bool :=
  (List.range 13).all fun s => (List.range 10).all fun i => (List.range 10).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 10, (i - 1).val = (i.val + 9) % 10 := by decide +kernel

theorem fin_next : ∀ i : Fin 10, (i + 1).val = (i.val + 1) % 10 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 13) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 10 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 9) % 10 := fun h => e1 (Fin.ext (h.trans a1.symm))
    simp only [nearB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨n1, n2⟩, n3⟩
  have hc := certOK_eq
  unfold certOK at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hk := hc s.val s.isLt i.val i.isLt j.val j.isLt
  rw [hn, Bool.false_or] at hk
  simp only [certNat, Nat.blt_eq] at hk
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  show 0 < cf1 i j * (cT s (i - 1) - cT s i + (if i - 1 < i then 1 else 0)) +
    cf2 i j * (cT s (i + 1) - cT s i + (if i + 1 < i then 1 else 0)) +
    cf3 i j * (cT s i - cT s j) + cf0 i j * (9 - cT s i)
  simp only [cf1, cf2, cf3, cf0, cf1N, cf2N, cf3N, cf0N, cT, cTN, Fin.lt_def, a1, a2]
  push_cast at ck ⊢
  ring_nf at ck ⊢
  linarith

theorem farkas4 (v : V) (h i k j : Fin 10) (e1 e2 r l1 l2 l3 l0 : ℤ)
    (hl : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l0)
    (hx : l1 * (Ac h - Ac i) + l2 * (Ac k - Ac i) + l3 * (Ac i - Ac j) - l0 * Ac i = 0)
    (hy : l1 * (Bc h - Bc i) + l2 * (Bc k - Bc i) + l3 * (Bc i - Bc j) - l0 * Bc i = 0)
    (hc : 0 < l1 * (Cc v.2.2 h - Cc v.2.2 i + e1) + l2 * (Cc v.2.2 k - Cc v.2.2 i + e2) +
      l3 * (Cc v.2.2 i - Cc v.2.2 j) + l0 * (r - Cc v.2.2 i))
    (f1 : pot v h ≤ pot v i - e1) (f2 : pot v k ≤ pot v i - e2) (f3 : pot v i ≤ pot v j)
    (f0 : r ≤ pot v i) : False := by
  have g1 := mul_nonpos_of_nonneg_of_nonpos hl.1 (show pot v h - pot v i + e1 ≤ 0 by linarith)
  have g2 := mul_nonpos_of_nonneg_of_nonpos hl.2.1 (show pot v k - pot v i + e2 ≤ 0 by linarith)
  have g3 := mul_nonpos_of_nonneg_of_nonpos hl.2.2.1 (show pot v i - pot v j ≤ 0 by linarith)
  have g0 := mul_nonpos_of_nonneg_of_nonpos hl.2.2.2 (show r - pot v i ≤ 0 by linarith)
  have e : l1 * (pot v h - pot v i + e1) + l2 * (pot v k - pot v i + e2) +
      l3 * (pot v i - pot v j) + l0 * (r - pot v i) =
      l1 * (Cc v.2.2 h - Cc v.2.2 i + e1) + l2 * (Cc v.2.2 k - Cc v.2.2 i + e2) +
        l3 * (Cc v.2.2 i - Cc v.2.2 j) + l0 * (r - Cc v.2.2 i) := by
    simp only [pot]
    linear_combination v.1 * hx + v.2.1 * hy
  linarith

/-- The level of the line of facet i through the points of class s with pot_i = n. -/
def lev (s : Fin 13) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 13) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 13) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 13) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 13) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 13) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 13) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 13) (i : Fin 10) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 10) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 10) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 13) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 9 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 13) (i : Fin 10) (n u : ℤ) (hn : 9 ≤ n)
    (hd : (n - Cc s i) % gc i = 0) (h1 : lo s i n ≤ u) (h2 : u ≤ hi s i n) :
    ∀ j, pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) := by
  have hi' := pot_par_self s i n u hd
  have hh := (pot_le_iff s i (i - 1) n u).2 ((le_hi_iff s i n u).1 h2)
  have hk := (pot_le_iff s i (i + 1) n u).2 ((lo_le_iff s i n u).1 h1)
  intro j
  by_cases e1 : j = i - 1
  · rw [e1]; exact hh
  by_cases e2 : j = i
  · simp only [e2, hi', lt_irrefl, if_false, sub_zero, le_refl]
  by_cases e3 : j = i + 1
  · rw [e3]; exact hk
  obtain ⟨c1, c2, c3, c0, cx, cy⟩ := certG_ok i j e1 e2 e3
  have cc := certC_ok s i j e1 e2 e3
  simp only [certC, cT_eq] at cc
  by_contra hne
  have f3 : pot (par s i (lev s i n) u) i ≤ pot (par s i (lev s i n) u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 9 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ
    (Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 13, ∀ j : Fin 10, -4 ≤ Cc s j ∧ Cc s j ≤ 4 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 3 + 0 * Ac 3 = 5 ∧ 1 * Bc 3 + 0 * Bc 3 = 0 ∧
    1 * Ac 8 + 0 * Ac 8 = (-5) ∧ 1 * Bc 8 + 0 * Bc 8 = 0 ∧
    1 * Ac 5 + 0 * Ac 5 = 0 ∧ 1 * Bc 5 + 0 * Bc 5 = 5 ∧
    1 * Ac 0 + 0 * Ac 0 = 0 ∧ 1 * Bc 0 + 0 * Bc 0 = (-5) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 13) :
    5 * x ≤ 1 * F (x, y, s) + 4 ∧
    5 * (-x) ≤ 1 * F (x, y, s) + 4 ∧
    5 * y ≤ 1 * F (x, y, s) + 4 ∧
    5 * (-y) ≤ 1 * F (x, y, s) + 4 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 3 + 0 * pot (x, y, s) 3 =
      5 * x + 1 * Cc s 3 + 0 * Cc s 3 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 3
  have k0 := Cbound s 3
  have l0 := Cbound s 3
  have e1 : 1 * pot (x, y, s) 8 + 0 * pot (x, y, s) 8 =
      5 * (-x) + 1 * Cc s 8 + 0 * Cc s 8 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 8
  have r1 := le_F (x, y, s) 8
  have k1 := Cbound s 8
  have l1 := Cbound s 8
  have e2 : 1 * pot (x, y, s) 5 + 0 * pot (x, y, s) 5 =
      5 * y + 1 * Cc s 5 + 0 * Cc s 5 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 5
  have r2 := le_F (x, y, s) 5
  have k2 := Cbound s 5
  have l2 := Cbound s 5
  have e3 : 1 * pot (x, y, s) 0 + 0 * pot (x, y, s) 0 =
      5 * (-y) + 1 * Cc s 0 + 0 * Cc s 0 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 0
  have r3 := le_F (x, y, s) 0
  have k3 := Cbound s 0
  have l3 := Cbound s 0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 13) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 13) (i : Fin 10) (n : ℤ) (hn : 9 ≤ n) :
    PF s i n = if (n - Cc s i) % gc i = 0 then
      (Finset.Icc (lo s i n) (hi s i n)).image (par s i (lev s i n)) else ∅ := by
  split_ifs with hd
  · ext v
    simp only [PF, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hs, hv⟩
      obtain ⟨h1, h2⟩ := (piece_iff v i n).1 hv
      have hl : lev s i n = Ap i * v.1 + Bp i * v.2.1 := by
        rw [lev, ← h1, pot_lev, hs, Int.add_sub_cancel,
          Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
      have hv' := par_inv v i
      rw [hs, ← hl] at hv'
      refine ⟨be i * v.1 - al i * v.2.1, ⟨?_, ?_⟩, hv'.symm⟩
      · rw [lo_le_iff, ← pot_le_iff, ← hv']
        exact h2 (i + 1)
      · rw [le_hi_iff, ← pot_le_iff, ← hv']
        exact h2 (i - 1)
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      have hp := par_piece s i n u hn hd h1 h2
      have hv := (piece_iff (par s i (lev s i n) u) i n).2 ⟨pot_par_self s i n u hd, hp⟩
      exact ⟨mem_Bx _ n (le_of_eq hv.1), rfl, hv⟩
  · rw [PF]
    apply Finset.filter_false_of_mem
    rintro v - ⟨hs, hv⟩
    obtain ⟨h1, -⟩ := (piece_iff v i n).1 hv
    apply hd
    rw [← hs, ← h1, pot_lev, Int.add_sub_cancel, Int.mul_emod_right]

/-- The length of the piece (s, i) at level n, as an integer. -/
def inner (s : Fin 13) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 13) (i : Fin 10) (n : ℤ) (hn : 9 ≤ n) :
    (PF s i n).card = (inner s i n).toNat := by
  rw [piece_eq s i n hn, inner]
  split_ifs
  · rw [Finset.card_image_of_injective _ (par_inj s i _), Int.card_Icc]
  · rfl

/-- The number of points with F = n. -/
noncomputable def cnt (n : ℤ) : ℕ := Set.ncard {v : V | F v = n}

theorem cnt_eq_card (n : ℤ) : cnt n = ((Bx n).filter (fun v => F v = n)).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Finset.coe_filter]
  exact ⟨fun h => ⟨mem_Bx v n (le_of_eq h), h⟩, fun h => h.2⟩

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 13 × Fin 10, (PF p.1 p.2 n).card := by
  rw [cnt_eq_card, Finset.card_eq_sum_card_fiberwise (f := fun v => (v.2.2, fi v))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [PF, Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro v _
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h2]
    exact ⟨rfl, h1, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, by rw [h1, h3]⟩

/-- The closed form of the sphere size: the sum of the piece lengths. -/
def S (n : ℤ) : ℤ := ∑ p : Fin 13 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 5 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 691327593 3 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 173126787 3 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 2

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 459347682 3 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 2

def mk (i : Fin 10) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 10, (5 : ℤ) = gc i * Lq i ∧
    5 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    5 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 13) (i : Fin 10) (n : ℤ) :
    inner s i (n + 5) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 5 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 5 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 5) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 5) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 5) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 5 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 13 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 5) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 691327593 3 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 10) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 10, (5 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 5 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 5 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 10, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 10 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then mhN (c % 10) + mkN (c % 10) else 0

theorem gsN_eq (s : Fin 13) (i : Fin 10) (n : ℤ) :
    gsN (i.val + 10 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (13 * 10)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 18430116869 4 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 4

def uh (i : Fin 10) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 709269965147457 5 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 10) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 380377258404 4 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 4

def uk (i : Fin 10) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 180502564738530 5 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 10) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 1771716992749895607586718358117630002623093882334504932550752894369386442267363478666547059298625208747447959496477692412979510459038454415962061729357447508 4 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 5

def vh (s : Fin 13) (i : Fin 10) : ℤ := vhN (i.val + 10 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 647255762926081456506143065364013309069752186305692701386799845083912437835090890738883004468129050696802438495810311482316088018543108185120708950224090227 4 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 4

def vk (s : Fin 13) (i : Fin 10) : ℤ := vkN (i.val + 10 * s.val)

def levT (s : Fin 13) (i : Fin 10) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 13) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 13, ∀ i : Fin 10,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 13) (i : Fin 10) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 13) (i : Fin 10) (n : ℤ) : inner s i n = innerT s i n := by
  have hl : levT s i n = lev s i n := by rw [levT, lev, cT_eq]
  rw [inner, innerT, cT_eq, hl]
  split_ifs with hd
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tab_ok s i
    have hc := lev_mul s i n hd
    have r1 : Rb s i (i - 1) n = uh i * lev s i n + vh s i := by
      rw [e1, e2, Rb]; linear_combination (-1 : ℤ) * hc
    have r2 : Rb s i (i + 1) n = uk i * lev s i n + vk s i := by
      rw [e4, e5, Rb]; linear_combination (-1 : ℤ) * hc
    rw [hi, lo, r1, r2, e3, e6]
    ring
  · rfl

/-- The closed form in table form. -/
def ST (n : ℤ) : ℤ := ∑ p : Fin 13 × Fin 10, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 10 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then
    (uhN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vhN c) / dhN (c % 10) +
      (ukN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vkN c) / dkN (c % 10) + 1
  else 0

theorem innerN_eq (s : Fin 13) (i : Fin 10) (n : ℤ) :
    innerN (i.val + 10 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (13 * 10)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 13 × Fin 10 => innerT q.1 q.2 n)
    (fun c : Fin (13 * 10) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (13 * 10), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 13 × Fin 10 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (13 * 10) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (13 * 10), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 9 and below 9. -/
def dtabV (k : ℕ) : ℕ := ctabN 17317391 5 k

def tblV (k : ℕ) : ℕ := ctabN 748820251 6 k

def initV (k : ℕ) : ℕ := ctabN 30461429848161 5 k

/-- The step of the closed form at residue t mod 5. -/
def dv (t : ℕ) : ℕ := dtabV (t % 5)

/-- The sequence in closed form: b(n + 5) = b(n) + dv (n - 9) for n ≥ 9. -/
def b (n : ℕ) : ℕ :=
  if n < 9 then initV n else dv (n - 9) * ((n - 9) / 5) + tblV ((n - 9) % 5)

theorem b_step (n : ℕ) (hn : 9 ≤ n) : b (n + 5) = b n + dv (n - 9) := by
  rw [b, b, if_neg (show ¬ (n + 5 < 9) by omega), if_neg (show ¬ (n < 9) by omega),
    show n + 5 - 9 = n - 9 + 5 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 5)]
  ring

theorem b_shift (n : ℕ) (hn : 9 ≤ n) : b (n + 5) = b n + 1 * dv (n - 9) := by
  rw [b, b, if_neg (show ¬ (n + 5 < 9) by omega), if_neg (show ¬ (n < 9) by omega),
    show n + 5 - 9 = n - 9 + 5 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 5)]
  ring

/-- b on the residue class of 9 + j mod 5. -/
theorem b_res (k j : ℕ) (hj : j < 5) : b (5 * k + (9 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (5 * k + (9 + j) < 9) by omega),
    show 5 * k + (9 + j) - 9 = j + 5 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 5), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 5. -/
def GsT : List ℤ := [16, 15, 16, 16, 15]

theorem Gs_tab : ∀ r : ℕ, r < 5 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 5 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 5 → 1 * (dv t : ℤ) = GsT.getD ((9 + t) % 5) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 9 ≤ n) : 1 * (dv (n - 9) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 9) % 5) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 9) % 5) = dv (n - 9) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 5 ∣ 5)]
  have e2 : (9 + (n - 9) % 5) % 5 = n % 5 := by omega
  rw [e1, e2, ← Gs_tab (n % 5) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 5 : ℕ) : ℤ) + 5 * ((n / 5 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 9, ..., 13: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 5 →
    ((List.range (13 * 10)).all fun c => decide (0 ≤ innerN c (9 + (r : ℤ)))) = true ∧
      STN (9 + (r : ℤ)) = b (9 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 9 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 13) (i : Fin 10) (n : ℤ) (hn : 9 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 9 + t := ⟨(n - 9).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 5
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 10 * s.val < 13 * 10 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 5) (by omega) (by omega)
      have e : (9 : ℤ) + t = (9 + (t - 5 : ℕ)) + 5 := by
        push_cast [Nat.cast_sub (by omega : 5 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 9 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 9 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 14
    · obtain ⟨r, rfl⟩ : ∃ r, n = 9 + r := ⟨n - 9, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 5) (by omega) (by omega)
      have h2 := S_shift ((n - 5 : ℕ) : ℤ)
      have h3 := b_shift (n - 5) (by omega)
      have h4 := grow (n - 5) (by omega)
      rw [show n - 5 + 5 = n by omega] at h3
      rw [show ((n - 5 : ℕ) : ℤ) + 5 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 8 lie in the box -2 ≤ x ≤ 2, -2 ≤ y ≤ 2 (`small_box`), and
the kernel checks that those of the box are the 109 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 13) (h : F (x, y, s) ≤ 8) :
    -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 8, with their values of F. -/
def smallV : List (V × ℤ) :=
  [(((-1), 0, 12), 2), ((0, 0, 0), 2), ((0, 0, 1), 2), ((0, 0, 2), 2), (((-1), (-1), 4), 3), (((-1), (-1), 11), 3), (((-1), 0, 3), 3), (((-1), 0, 8), 3), ((0, 0, 3), 3), ((0, 0, 5), 3), ((0, 0, 6), 3), ((0, 0, 7), 3), ((0, 0, 9), 3), ((0, 0, 10), 3), ((0, 0, 12), 3), (((-1), (-1), 5), 4), (((-1), (-1), 10), 4), (((-1), 0, 2), 4), (((-1), 0, 9), 4), ((0, (-1), 4), 4), ((0, (-1), 11), 4), ((0, 0, 4), 4), ((0, 0, 8), 4), ((0, 0, 11), 4), ((0, 1, 12), 4), ((1, 0, 0), 4), ((1, 0, 7), 4), (((-1), (-1), 6), 5), (((-1), (-1), 9), 5), (((-1), 0, 1), 5), (((-1), 0, 10), 5), ((0, (-1), 5), 5), ((0, (-1), 10), 5), ((0, 1, 3), 5), ((0, 1, 8), 5), ((1, 0, 1), 5), ((1, 0, 6), 5), ((1, 1, 0), 5), ((1, 1, 7), 5), (((-1), (-1), 1), 6), (((-1), (-1), 2), 6), (((-1), (-1), 7), 6), (((-1), (-1), 8), 6), (((-1), (-1), 12), 6), (((-1), 0, 0), 6), (((-1), 0, 5), 6), (((-1), 0, 6), 6), (((-1), 0, 11), 6), ((0, (-1), 6), 6), ((0, (-1), 7), 6), ((0, (-1), 9), 6), ((0, 1, 2), 6), ((0, 1, 9), 6), ((1, 0, 2), 6), ((1, 0, 5), 6), ((1, 1, 1), 6), ((1, 1, 6), 6), (((-2), (-1), 8), 7), (((-2), (-1), 11), 7), (((-2), (-1), 12), 7), (((-2), 0, 12), 7), (((-1), (-2), 4), 7), (((-1), (-2), 11), 7), (((-1), (-1), 0), 7), (((-1), (-1), 3), 7), (((-1), 0, 4), 7), (((-1), 0, 7), 7), (((-1), 1, 12), 7), ((0, (-1), 0), 7), ((0, (-1), 1), 7), ((0, (-1), 2), 7), ((0, (-1), 8), 7), ((0, 1, 0), 7), ((0, 1, 1), 7), ((0, 1, 10), 7), ((1, 0, 3), 7), ((1, 0, 4), 7), ((1, 0, 9), 7), ((1, 0, 10), 7), ((1, 1, 2), 7), ((1, 1, 5), 7), (((-2), (-2), 4), 8), (((-2), (-2), 11), 8), (((-2), (-1), 3), 8), (((-2), (-1), 4), 8), (((-2), (-1), 9), 8), (((-2), (-1), 10), 8), (((-2), 0, 3), 8), (((-2), 0, 8), 8), (((-1), (-2), 5), 8), (((-1), (-2), 10), 8), (((-1), 1, 3), 8), (((-1), 1, 8), 8), ((0, (-1), 3), 8), ((0, (-1), 12), 8), ((0, 1, 5), 8), ((0, 1, 6), 8), ((0, 1, 7), 8), ((0, 1, 11), 8), ((1, (-1), 4), 8), ((1, (-1), 7), 8), ((1, 0, 8), 8), ((1, 0, 11), 8), ((1, 0, 12), 8), ((1, 1, 3), 8), ((1, 1, 4), 8), ((1, 1, 9), 8), ((1, 1, 10), 8), ((1, 1, 12), 8)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 5, Bc = BTV - 5. -/
def ATV (k : ℕ) : ℕ := ctabN 274917337717 4 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 5

def AT (i : Fin 10) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 93057339392 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 5

def BT (i : Fin 10) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 10, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 8 at the box point ((a : ℤ) - 2, (b : ℤ) - 2, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 10).any fun i =>
    Nat.blt (11 + ATV i * 2 + 5 * a + BTV i * 2 + 5 * b)
      (ATV i * a + 10 + BTV i * b + 10 + cTV (i + 10 * s))

theorem big_pot (a b : ℕ) (s : Fin 13) (h : bigNat a b s.val = true) :
    (8 : ℤ) < F ((a : ℤ) - 2, (b : ℤ) - 2, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 2, (b : ℤ) - 2, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b => (List.finRange 13).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 2, (b : ℤ) - 2, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 8) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 2).toNat (by omega) (y + 2).toNat (by omega) s
  have ex : (((x + 2).toNat : ℕ) : ℤ) - 2 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · have := big_pot _ _ s h1
    rw [ex, ey] at this
    omega
  · rw [ex, ey] at h1
    exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 8) :
    cnt n = (((smallV.filter (fun q => decide (q.2 = n))).map Prod.fst).toFinset).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  have hv := smallV_ok
  simp only [List.all_eq_true, decide_eq_true_eq] at hv
  simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (small_mem v (by omega))
    exact ⟨q, ⟨hq, by rw [← hv q hq]; exact h⟩, rfl⟩
  · rintro ⟨q, ⟨hq, h2⟩, rfl⟩
    rw [hv q hq]
    exact h2

/-- The small spheres from 9 on, in closed form. -/
theorem small_ok : ∀ n : ℕ, 9 ≤ n → n < 9 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n from n = 9 on (`a_eq_cnt`, from `a_eq_F`), and `small_vals`
lists the terms below 9. The terms from 9 to 8 are counted in `smallL`, those from 9 on
are S(n), and all agree with the closed form b (`a_eq_b`). The step from n to n + 5, the closed form
per residue (`a_closed`), the controls, the recurrence and the g.f. follow, their base cases checked by
the kernel on b. -/

theorem a_eq_cnt (n : ℕ) (hn : 9 ≤ n) : a n = cnt n := by
  rw [a_eq_F n hn, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 9 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt n (by omega)]
  exact cnt_eq_S n (by exact_mod_cast hn)

theorem a_lt_R0 (n : ℕ) (hn : n < 9) : a n = b n := by
  have h : (List.range 9).map a = (List.range 9).map b := by
    rw [small_vals]
    decide +kernel
  exact List.map_inj_left.1 h n (List.mem_range.2 hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 9 ∨ (9 ≤ n ∧ n < 9) ∨ 9 ≤ n by omega) with h | ⟨h1, h2⟩ | h
  · exact a_lt_R0 n h
  · rw [a_eq_cnt n h1, cnt_small _ (by omega)]
    exact small_ok n h1 h2
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 5) = a(n) + dv (n - 9) for n ≥ 9. -/
theorem a_step (n : ℕ) (hn : 9 ≤ n) : a (n + 5) = a n + dv (n - 9) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 15 ∧ tblV 0 = 27 ∧ dv 1 = 16 ∧ tblV 1 = 28 ∧ dv 2 = 15 ∧ tblV 2 = 33 ∧ dv 3 = 16 ∧ tblV 3 = 40 ∧ dv 4 = 16 ∧ tblV 4 = 44 := by
  decide +kernel

/-- The closed form per residue of n mod 5, for n ≥ 9. -/
theorem a_closed (k : ℕ) :
    a (5 * k + 9) = 15 * k + 27 ∧
    a (5 * k + 10) = 16 * k + 28 ∧
    a (5 * k + 11) = 15 * k + 33 ∧
    a (5 * k + 12) = 16 * k + 40 ∧
    a (5 * k + 13) = 16 * k + 44 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show 5 * k + 9 = 5 * k + (9 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 5 * k + 10 = 5 * k + (9 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 5 * k + 11 = 5 * k + (9 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 5 * k + 12 = 5 * k + (9 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 5 * k + 13 = 5 * k + (9 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 6, 9, 11, 13, 17, 22, 27, 27, 28, 33, 40, 44, 42, 44, 48, 56, 60, 57, 60, 63, 72, 76, 72, 76, 78, 88, 92, 87, 92, 93, 104, 108, 102, 108, 108, 120, 124, 117, 124, 123, 136, 140, 132, 140, 138, 152, 156, 147] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 5 → (dv (t + 10) : ℤ) = 2 * (dv (t + 5) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = 2 * (dv (t + 5) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 5 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 5, e 10]
  exact drec_base (t % 5) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 5 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 5 → (b (q + 19) : ℤ) = 2 * b (q + 14) - b (q + 9) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 19) : ℤ) = 2 * b (q + 14) - b (q + 9) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 5 ∨ 5 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 5 := ⟨q - 5, by omega⟩
      have h0 : (b (v + 19) : ℤ) = 2 * b (v + 14) - b (v + 9) := ih (v + 0) (by omega)
      have s9 : b (v + 14) = b (v + 9) + dv (v + 0) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 5 = v + 14 by omega,
          show v + 9 - 9 = v + 0 by omega] at h
        exact h
      have s14 : b (v + 19) = b (v + 14) + dv (v + 5) := by
        have h := b_step (v + 14) (by omega)
        rw [show v + 14 + 5 = v + 19 by omega,
          show v + 14 - 9 = v + 5 by omega] at h
        exact h
      have s19 : b (v + 24) = b (v + 19) + dv (v + 10) := by
        have h := b_step (v + 19) (by omega)
        rw [show v + 19 + 5 = v + 24 by omega,
          show v + 19 - 9 = v + 10 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 24) : ℤ) = 2 * b (v + 19) - b (v + 14)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 18 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 19 := ⟨n - 19, by omega⟩
  rw [show q + 19 - 5 = q + 14 by omega, show q + 19 - 10 = q + 9 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 19, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 19 → 1 * (b n : ℤ) - 2 * (if 5 ≤ n then (b (n - 5) : ℤ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 3 + (if n = 2 then (1 : ℤ) else 0) * 6 + (if n = 3 then (1 : ℤ) else 0) * 9 + (if n = 4 then (1 : ℤ) else 0) * 11 + (if n = 5 then (1 : ℤ) else 0) * 11 + (if n = 6 then (1 : ℤ) else 0) * 11 + (if n = 7 then (1 : ℤ) else 0) * 10 + (if n = 8 then (1 : ℤ) else 0) * 9 + (if n = 9 then (1 : ℤ) else 0) * 5 + (if n = 10 then (1 : ℤ) else 0) * 3 + (if n = 11 then (1 : ℤ) else 0) * 2 + (if n = 12 then (1 : ℤ) else 0) * 2 - (if n = 13 then (1 : ℤ) else 0) * 1 - (if n = 14 then (1 : ℤ) else 0) * 1 + (if n = 15 then (1 : ℤ) else 0) * 1 - (if n = 16 then (1 : ℤ) else 0) * 1 - (if n = 17 then (1 : ℤ) else 0) * 2 - (if n = 18 then (1 : ℤ) else 0) * 1 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -X ^ 18 - 2 * X ^ 17 - X ^ 16 + X ^ 15 - X ^ 14 - X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 3 * X ^ 10 + 5 * X ^ 9 + 9 * X ^ 8 + 10 * X ^ 7 + 11 * X ^ 6 + 11 * X ^ 5 + 11 * X ^ 4 + 9 * X ^ 3 + 6 * X ^ 2 + 3 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 10 - 2 * X ^ 5 + 1) = C 1 * A - C 2 * (A * X ^ 5) + C 1 * (A * X ^ 10) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (-X ^ 18 - 2 * X ^ 17 - X ^ 16 + X ^ 15 - X ^ 14 - X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 3 * X ^ 10 + 5 * X ^ 9 + 9 * X ^ 8 + 10 * X ^ 7 + 11 * X ^ 6 + 11 * X ^ 5 + 11 * X ^ 4 + 9 * X ^ 3 + 6 * X ^ 2 + 3 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 3 + X ^ 2 * C 6 + X ^ 3 * C 9 + X ^ 4 * C 11 + X ^ 5 * C 11 + X ^ 6 * C 11 + X ^ 7 * C 10 + X ^ 8 * C 9 + X ^ 9 * C 5 + X ^ 10 * C 3 + X ^ 11 * C 2 + X ^ 12 * C 2 - X ^ 13 * C 1 - X ^ 14 * C 1 + X ^ 15 * C 1 - X ^ 16 * C 1 - X ^ 17 * C 2 - X ^ 18 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 19 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 19 := ⟨n - 19, by omega⟩
    have h : (b (q + 19) : ℤ) = 2 * b (q + 14) - b (q + 9) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 19 - 5 = q + 14 by omega, show q + 19 - 10 = q + 9 by omega, show 5 ≤ q + 19 by omega, show 10 ≤ q + 19 by omega, show ¬ q + 19 = 0 by omega, show ¬ q + 19 = 1 by omega, show ¬ q + 19 = 2 by omega, show ¬ q + 19 = 3 by omega, show ¬ q + 19 = 4 by omega, show ¬ q + 19 = 5 by omega, show ¬ q + 19 = 6 by omega, show ¬ q + 19 = 7 by omega, show ¬ q + 19 = 8 by omega, show ¬ q + 19 = 9 by omega, show ¬ q + 19 = 10 by omega, show ¬ q + 19 = 11 by omega, show ¬ q + 19 = 12 by omega, show ¬ q + 19 = 13 by omega, show ¬ q + 19 = 14 by omega, show ¬ q + 19 = 15 by omega, show ¬ q + 19 = 16 by omega, show ¬ q + 19 = 17 by omega, show ¬ q + 19 = 18 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -X ^ 18 - 2 * X ^ 17 - X ^ 16 + X ^ 15 - X ^ 14 - X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 3 * X ^ 10 + 5 * X ^ 9 + 9 * X ^ 8 + 10 * X ^ 7 + 11 * X ^ 6 + 11 * X ^ 5 + 11 * X ^ 4 + 9 * X ^ 3 + 6 * X ^ 2 + 3 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 18 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 6, 9, 11, 13, 17, 22, 27, 27, 28, 33, 40, 44, 42, 44, 48, 56, 60, 57, 60, 63, 72, 76, 72, 76, 78, 88, 92, 87, 92, 93, 104, 108, 102, 108, 108, 120, 124, 117, 124, 123, 136, 140, 132, 140, 138, 152, 156, 147] := Count.controls

/-- The step a(n + 5) = a(n) + Count.dv (n - 9) for n ≥ 9. -/
theorem a_step (n : ℕ) (hn : 9 ≤ n) : a (n + 5) = a n + Count.dv (n - 9) := Count.a_step n hn

/-- The closed form per residue of n mod 5, for n ≥ 9. -/
theorem a_closed (k : ℕ) :
    a (5 * k + 9) = 15 * k + 27 ∧
    a (5 * k + 10) = 16 * k + 28 ∧
    a (5 * k + 11) = 15 * k + 33 ∧
    a (5 * k + 12) = 16 * k + 40 ∧
    a (5 * k + 13) = 16 * k + 44 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -X ^ 18 - 2 * X ^ 17 - X ^ 16 + X ^ 15 - X ^ 14 - X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 3 * X ^ 10 + 5 * X ^ 9 + 9 * X ^ 8 + 10 * X ^ 7 + 11 * X ^ 6 + 11 * X ^ 5 + 11 * X ^ 4 + 9 * X ^ 3 + 6 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a310143

theorem OMA.solution : type_of% @OMA.S_oeis_a310143.main :=
  OMA.S_oeis_a310143.conjecture
