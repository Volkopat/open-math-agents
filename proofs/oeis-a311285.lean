import OMAStatements.S_oeis_a311285

namespace OMA.S_oeis_a311285






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 10

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 1680059629
  | 1 => 1697950684
  | 2 => 1413856459
  | 3 => 2290649224
  | 4 => 2574743449
  | 5 => 1984207564
  | 6 => 2002098619
  | 7 => 1718004394
  | 8 => 2004326809
  | 9 => 2288421034
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1738189174 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 3471589924 4 8 i.val

def Cc (s : Fin 10) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 1738189174 4 i

def BcN (i : ℕ) : ℕ := tgetN 3471589924 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 10) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


/-- The potential of facet i at v (facets in angular order around the growth polygon). -/
def pot (v : V) (i : Fin 8) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest facet potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 8) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩

/-- A statement about every vertex class follows from the statements about each class. -/
theorem cls (P : Fin 10 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 10 × Fin 10 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 8) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

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

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 10) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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

/-- Certificates of the far facts, the same for every class: for maximal facet i and a facet j not
adjacent to i, the fields k1, k2, m1, m2, m0, mj of entry i * 8 + j give the facts pot k1 ≤ pot i,
pot k2 ≤ pot i, 9 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 20916633739064931429235819426662767950816144446457591363086589835442222708396346338790848523487878694618179256354217143839542943696674371292097963980342787441832034424312083331619516365694180371750953369405946965616242687048049294639309576675955517715511791201941965857272301123329835007675918534332297663165569738757755504569039162647174155578296681112253455271789522429183007508487123575724313087970591408296718633106505191994095177421500044715029931508103292994288219543915666209056479362344205220673609111167148386879601397076854434701929453292450710814720 5 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 876899495659509344927533039265249360855872634880 4 p

def dstv (p : ℕ) : ℕ := tgetN 778666186842759038203517101877059577370116113185 4 p

def dxv (p : ℕ) : ℕ := tgetN 328599224878094537347393 2 p

def dyv (p : ℕ) : ℕ := tgetN 402975273204880703313157 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 9724911479585857736814994342740426715287651961035533889183617646687094927139334163145711660576045567071934307761630578884036318140823502132156867102211240091025309093148974749168221257645065123330215945716929694096239068986194538960059384345755190362876925011240810495112964714870792316306231759171985612617901679208938133061134537504446628608591282152313764722678204303746507480860535 4 (p * 8 + j)

def dlv (p : ℕ) (j : Fin 8) : ℤ := (dlvN p j.val : ℤ) - 8

theorem dlv_neg (p : ℕ) (j : Fin 8) (h : dlvN p j.val + 1 ≤ 8) : dlv p j ≤ -1 := by
  unfold dlv
  omega

theorem dlv_le (p : ℕ) (j : Fin 8) (c : ℕ) (h : dlvN p j.val + 1 ≤ c + 8) : dlv p j ≤ (c : ℤ) - 1 := by
  unfold dlv
  omega

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 8) : Fin 8 := ⟨(i.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 8) : Fin 8 := ⟨(i.val + 7) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 8) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 8). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 8) + fdN i j 3 * AcN (fdN i j 1 % 8) + fdN i j 5 * AcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 8) + fdN i j 3 * BcN (fdN i j 1 % 8) + fdN i j 5 * BcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 8) + fdN i j 3 * CcN s (fdN i j 1 % 8) + fdN i j 5 * CcN s i +
      fdN i j 4 * 17)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

def farOK : Bool := (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 10).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 40).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 10) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (9 - Cc s i)

/-- Beyond F = 8, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 10) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 8 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 9 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
    (pair_of (le_F _ _) h) (pair_of (le_F _ _) h) (not_pair2 hc') (bound_of hF h)

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

/-- Descent rules beyond F = 8, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 8 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 10401192663568270608655559001636779019304442313327286684226287025007274000680064951398900916005743801721767496926710042178701209737714921021925737831735339706331879400294035753682987539379117442166555841278942814313457210136225818868155667873979667449830873590842183683557600337454993609163058663110071896406200839677008681397512248119227343627066096600483862445568664018169758079802049705489208247623125582030341304024826041025395978711503771019122160671578774803685592969053273881548660978341311772576803873585712898887232997215244134972161814839818460545441808090988694895495027525623603897638054910930292116703165155226944267997733464859276693533853182587635266890811102677587912962520691614460353782634086294769350038274419495270445779131176466084573863800875520216400728006279147449569956954805150521960742073935969001766311549999906340226185332327315860571144963583370613816861210242008139250220649422913
  | 1 => 10401192665370368150884167740824300858554500035547379211354864364742054107507401331767566095660598158194351896977429120566141616043313865689199732151324670679109080070944649926892073829946365942314901788292659826905646130651672665138868006972222762684493694042605329889268841974112635192745305482505050449308020216906754401213093134158340195207045803722843016967215699728873771969291635846133052452043420871032076007576257040006204760871434245037945628284102426291847887195150026318402097692397439982052323221824277085387687707033149932157068065679112907830749673447048626763121671620709267389718983384667525294570677263913393248401828657252676918001439655791013506123157431228867444031487872716495773659369381756705131312166541204564755575865818821632246645237621482511205571865952529974720793472084703133306188121434371353370919648840556855766252281077120434713581418546628939929269445754657891695240739300160
  | 2 => 10401192666571766512369906900282648751387871850360774229440582591231907512059077751591793018415429318488253136502844761555967182375350357200473133772736908843573295918075422757707591590727099302320244458324459985460877485627404479143272628684798869202148279443547013865854717747775230723160959388275307021588105055181328939724010372644079683338604561427266133362581951931823520552542769582293857982567897461410934167587882430375917160947953780140037976987756104194723021760189859863248912489417255807984242906868788324504630847916752364920642220176964483116479092437574793934465623786906562519512913824368997772219140617938070168660588940318534452880869608015559149382381790118114188786019452113778671555647153932666527040283909622525826204100009445194670292925912665490387067690128697084652911896292934031583719843262325570854146713694764685711678410301286339752247007673588145440042096212094986651768288714817
  | 3 => 10401192670175961596827124378657692460943407062730694650009552978511025989533072638822269485223553880378454073923271617185715130184683679196925271182944935272273581837412633189169985226735182127288576909640177202084498093404624925404453809080545131560363155225959901138417344710681832915427526428264769752485280340972256220360878844192700125159652473077014772774278091891555876427008970997410055167591923637897793504909289811175614606189742758927221676369855790886038477203049085354293563371616598278586814712975118462945456816915255525775000594665602896780811582836715510769996956651945351729852602920112238706606621119984255456771108268236214081168193959782793319071352556473687205230853484925724482225325492444172857804618077176986450792411379851857866034568116369257253581759137300351757565460582503755428952381935281248839133771489349351914687059736162049120987330321365682065747457315816732067530892648513
  | 4 => 10401192672578758319798602697574388215554730924427749319869173723681174534817459850711931586229431027551429077676762568108528696253301683784353759648256882480174250909590825232615195354857026576089815787449401338305770123001918579462416535413082737785399115715931320710423786671708603467207271296593818357094173050087491932180468742655927902721848158235993637813770453124881781627000281717940740138149334328689783471863453469626617250228571615564747488715832768645263029342035189270709203264625576995034152932060792004363280065184702311736181915393903212778128569803141377120581400037200435911669329127377274888149238882607390960980659074624501351709036557863907771867818198365713006135507932957354265262530107748074660662891281600210835747868068557506552735252581821191220385863367504893273198539007029979587018031947817440050071013735835916876070947085031360447546683795753928456676503584196692875145269750080
  | 5 => 10401192673780156681284341857032736108388102739241144337954891950171027939369314519902007629201372069069280523620556849732263093660614701752892943164704325670307563472452336760935362158801285720416560948685485372439656774355678842409910339381465889325766953619851458028447716797477694684845972778317621437128450316436015515913999034634633678606879780165153724426028459975551744463064212408309337043583026695970833919101386995880852875638519665722081093171623972091044944168524295533557352992002139303527852619520652510411901172153338057749319143672600144786418504526214988971684727635905301889031155985831938081985799620837377584237955235479296975037182632969518407168857137450406450144908641381597647375223322391739855882465605286031882956182680718736630301311292987259984487854472633092606988324881605933678090759922311515633093367888291660472872672088524172392469729240746904328462791447369581611240066916417
  | 6 => 10401192677384351765741559335407779786888218183681329392212046629640588153024165530008175246608652940456147198142984866470116830708851005208865540715822348192913007050629438562309501750113911839343518773180265566590961901557758775898941000515966550601615253739385561928728518318609345690167585016994789993505439167466408379519929203165036647652626753112980575644749239902222653014972835959833519652681957570012187596483970221629297661391202645063511532927035338408123205922556661421560987624237077640726810963372699316803801003387562180599524001908855944238718311605289395045766695831720604360243826072977716325607880239441172090695864156773100518844386287556239725212339760874619585478824270645435707743361305306343592181046749006080104706850172345513922690921838521024736928566727295786094932726530030058248005554861597363584197553450104140672586469456139797234801028704478779632633127597097400529446841101632
  | 7 => 10401192678585750127227298494866127679721589998494724410297764856130441557575841949832402169363484100750048437582576558767125374478899804143788601489175867976993558303811727391291678030176045213355657003223739341626235292425200583628497172315616769538047382896711834732305106560765689779283028278730414656327902177783252780105013812552128584092780470246405675892894876352771152822685685926433016898978196936350123229102807744172256125376869228848496814610393549484157246124777043641224952281971363756698895349074750786445178507071852310194164883263326979336211691410557590311952776002407132429413174024390517534873914074261193253638326268041456620003170333493833832301123741819122872104723269847462876794794563479916379651467913824093226310455953759194010449925324448995129237774621639188250932281515586508166124592298454665875493764996825298502210663177725781076296723393537159896072800645968972853709242638401
  | 8 => 10401192681589246030941646393511997411805019535542334325382196810883904416198846524622709542356614306101562961648184204574759438253941588643736925315498751500329648741409890665980076264560130244592392400667234263864839726460634610325390927215608951860212131195940706441560513305811519206882379747334566990178712474705039811975266712655960857982741217365186403871570927368605620117850123988722728174912293358324975770659149306366944151373929640823426064196685874616137028373226353035547039320983678735286362385924787498143287686545440120533632736557424928005412851607662662029641469012028399340721419972859465460247200542902255805579393629304991558574686942964125562688551516112975638481352455405820376317506644639894454944899145024771919223529542631653426652750051764738290135463694945022403823516895938020144178294739001756534706193223845671548616794116958556862722519380685507075377590220703637350637171384385
  | 9 => 10401192683992042753913124712428693197471763165169124361553633263857390565722120730443476796043878644495453800260895929622623703276798267456505803656611456777147266978538517278519017422111265119372651568723437876406705143154002564310067333237633690834136197613475501091096614301720715508377943305286654436277673205085194280533365715072804727788739819618275555219354200037405552789368662378078345650893882602868828007747022093711317799652733896865213819586432471864551048209712230224127285759659588770304300772096839026079727288350839761602609528404860490770287984753469323922655525933787068657750751174846728774828555973231026576766500542270381297358915397775893308009616812686902900925084889010727003585468513541378188163302240301195556137817238469606476386379426638575298223106590666746637245371066297013591791425645611140810414703777459842894885472545954669829793815791761329005357797072306576651398662861760
  | _ => 0

def rd (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 40 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 8)
  else if rk s i c1 c2 = 2 then
    decide (c1.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (nxt i) ∧ rg s i c1 c2 ∣ Bc i - Bc (nxt i) ∧
      ¬ rg s i c1 c2 ∣ (c1.val : ℤ) - (Cc s i - Cc s (nxt i)))
  else if rk s i c1 c2 = 3 then
    decide (c2.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (prv i) ∧ rg s i c1 c2 ∣ Bc i - Bc (prv i) ∧
      ¬ rg s i c1 c2 ∣ (c2.val : ℤ) - (Cc s i - Cc s (prv i)))
  else false

/-- All the tables: the far certificates for non-adjacent facets, the edge tables and the descent
rules. -/
theorem tables_ok : farOK = true ∧ farCOK = true ∧ dlOK = true ∧ (∀ s i c1 c2, ruleOK s i c1 c2 = true) := by
  decide +kernel

/-- The far certificates hold in the integers: the natural-number checks moved across. -/
theorem far_cert (s : Fin 10) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
  have hn : nearB i.val j.val = false := by
    obtain ⟨h1, h2, h3⟩ := hij
    have e1 : j.val ≠ i.val := fun h => h1 (Fin.ext h)
    have e2 : j.val ≠ (i.val + 1) % 8 := fun h => h2 (Fin.ext h)
    have e3 : j.val ≠ (i.val + 7) % 8 := fun h => h3 (Fin.ext h)
    simp only [nearB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨e1, e2⟩, e3⟩
  have hxy := tables_ok.1
  have hc := tables_ok.2.1
  unfold farOK at hxy
  unfold farCOK at hc
  simp only [List.all_eq_true, List.mem_range] at hxy hc
  have hx := hxy i.val i.isLt j.val j.isLt
  have hk := hc s.val s.isLt i.val i.isLt j.val j.isLt
  rw [hn, Bool.false_or] at hx hk
  simp only [farXYN, Bool.and_eq_true, beq_iff_eq] at hx
  simp only [farCN, Nat.blt_eq] at hk
  obtain ⟨hA, hB⟩ := hx
  have cA := congrArg (Nat.cast : ℕ → ℤ) hA
  have cB := congrArg (Nat.cast : ℕ → ℤ) hB
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  push_cast at cA cB ck
  simp only [farCert, fm1, fm2, fmj, fm0, fd, Ac_eq, Bc_eq, Cc_eq, fk1, fk2]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by linear_combination cA,
    by linear_combination cB, ?_⟩
  ring_nf at ck ⊢
  linarith

theorem edge_at (p : ℕ) (hp : p < 40) :
    srcv p = (E.getD p (0, 0, 0, 0)).1.val ∧ ∀ j, dlv p j = dl (E.getD p (0, 0, 0, 0)) j := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h p hp
  refine ⟨h1.symm, fun j => ?_⟩
  have hN := congrArg (Nat.cast : ℕ → ℤ) (h5 j.val j.isLt)
  push_cast at hN
  generalize E.getD p (0, 0, 0, 0) = e at h1 h2 h3 h4 ⊢
  obtain ⟨s1, s2, dx, dy⟩ := e
  simp only at h1 h2 h3 h4
  have ex : dx = (dxv p : ℤ) - 1 := by omega
  have ey : dy = (dyv p : ℤ) - 1 := by omega
  subst ex ey
  simp only [dlv, dl, Ac_eq, Bc_eq, Cc_eq, h1, h2]
  linear_combination hN

theorem edge_tab (p : ℕ) (hp : p < 40) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 10) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 8)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 8 < pot (x, y, s) i) : False := by
  have m1 : u1 * (pot (x, y, s) i - pot (x, y, s) (nxt i)) = u1 * c1 := by rw [e1]
  have m2 : u2 * (pot (x, y, s) i - pot (x, y, s) (prv i)) = u2 * c2 := by rw [e2]
  have key := mul_lt_mul_of_pos_left hF hu0
  have ha' : (u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i))) * x = u0 * Ac i * x := by rw [ha]
  have hb' : (u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i))) * y = u0 * Bc i * y := by rw [hb]
  simp only [pot] at m1 m2 key
  nlinarith [ha', hb', m1, m2, key, hc]

theorem dvd_contra (x y : ℤ) (a b c g : ℤ) (ha : g ∣ a) (hb : g ∣ b) (hc : ¬ g ∣ c) (e : a * x + b * y = c) :
    False :=
  hc (e ▸ dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y))

/-- Beyond F = 8 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 10) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 8 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
  have p1 : 0 ≤ pot (x, y, s) i - pot (x, y, s) (nxt i) := by have := le_F (x, y, s) (nxt i); omega
  have p2 : 0 ≤ pot (x, y, s) i - pot (x, y, s) (prv i) := by have := le_F (x, y, s) (prv i); omega
  have hv := tables_ok.2.2.2 s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
    (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))
  have q1 := scl_le _ p1
  have q2 := scl_le _ p2
  unfold ruleOK at hv
  split_ifs at hv with k0 k1 k2 k3
  · -- an edge that descends
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hlen, hsrc, hdi, hdn, hdp⟩ := hv
    have hdi := dlv_neg _ _ hdi
    have hdn := dlv_le _ _ _ hdn
    have hdp := dlv_le _ _ _ hdp
    obtain ⟨hs0, hdl⟩ := edge_at _ hlen
    have hmem : E.getD (re s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
        (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    rw [hdl] at hdi hdn hdp
    rw [hs0] at hsrc
    generalize E.getD (re s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
        (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))) (0, 0, 0, 0) = e at hmem hsrc hdi hdn hdp
    have hs : e.1 = s := Fin.ext hsrc
    have ha := adj_of_mem e hmem x y
    rw [hs] at ha
    refine ⟨_, ha, step_down _ _ ha (fun j => ?_)⟩
    have hsh := shift x y e j
    rw [hs] at hsh
    rw [hsh]
    have hst := (E_step e hmem j).1
    have hj := le_F (x, y, s) j
    by_cases hji : j = i
    · subst hji
      omega
    by_cases hjn : j = nxt i
    · subst hjn
      omega
    by_cases hjp : j = prv i
    · subst hjp
      omega
    have hna : nonadj i j := ⟨hji, hjn, hjp⟩
    have := far s i j (far_cert s i j hna) x y h hF
    omega
  · -- a corner point within F ≤ 8
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc1, hc2, hu0, ha, hb, hc⟩ := hv
    exact (point_contra x y s i _ _ _ _ _ hu0 ha hb hc (scl_eq _ p1 hc1) (scl_eq _ p2 hc2) (h ▸ hF)).elim
  · -- the line of the next facet has no lattice point
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc1, ha, hb, hc⟩ := hv
    have e1 := scl_eq _ p1 hc1
    generalize scl (pot (x, y, s) i - pot (x, y, s) (nxt i)) = c at e1 ha hb hc
    simp only [pot] at e1
    exact (dvd_contra x y _ _ _ _ ha hb hc (by linear_combination e1)).elim
  · -- the line of the previous facet has no lattice point
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc2, ha, hb, hc⟩ := hv
    have e2 := scl_eq _ p2 hc2
    generalize scl (pot (x, y, s) i - pot (x, y, s) (prv i)) = c at e2 ha hb hc
    simp only [pot] at e2
    exact (dvd_contra x y _ _ _ _ ha hb hc (by linear_combination e2)).elim

theorem far_desc (v : V) (hF : 8 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 10) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 1 7 0 8 4 6 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 1 7 0 8 4 6 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 0 7 0 8 4 4 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 3 5 0 8 6 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 0 7 0 8 4 4 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 1 3 0 8 2 1 0 0 1 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 1 7 0 8 4 6 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 1 4 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box5 (x y : ℤ) (hF : F (x, y, 5) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 5) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 5 1 7 0 8 4 6 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg5 (x y : ℤ) : 0 ≤ F (x, y, 5) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 5) k).trans (show F (x, y, 5) ≤ -1 by omega)
  exact farkas_ub x y 5 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box6 (x y : ℤ) (hF : F (x, y, 6) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 6) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 6 1 7 0 8 4 6 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg6 (x y : ℤ) : 0 ≤ F (x, y, 6) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 6) k).trans (show F (x, y, 6) ≤ -1 by omega)
  exact farkas_ub x y 6 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box7 (x y : ℤ) (hF : F (x, y, 7) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 7) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 7 0 7 0 8 4 4 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 3 5 0 8 6 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg7 (x y : ℤ) : 0 ≤ F (x, y, 7) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 7) k).trans (show F (x, y, 7) ≤ -1 by omega)
  exact farkas_ub x y 7 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box8 (x y : ℤ) (hF : F (x, y, 8) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 8) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 8 0 7 0 8 4 4 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 3 5 0 8 6 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 2 7 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg8 (x y : ℤ) : 0 ≤ F (x, y, 8) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 8) k).trans (show F (x, y, 8) ≤ -1 by omega)
  exact farkas_ub x y 8 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box9 (x y : ℤ) (hF : F (x, y, 9) ≤ 8) : -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 9) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 9 1 7 0 8 4 6 0 1 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 9 3 4 0 8 4 4 0 (-1) 0 5 16 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 9 1 4 0 8 2 1 0 0 1 3 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 9 5 7 0 8 2 1 0 0 (-1) 3 16 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg9 (x y : ℤ) : 0 ≤ F (x, y, 9) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 9) k).trans (show F (x, y, 9) ≤ -1 by omega)
  exact farkas_ub x y 9 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 8 lies in the cells |x| ≤ 4, |y| ≤ 2. -/
theorem near_box (x y : ℤ) (s : Fin 10) (hF : F (x, y, s) ≤ 8) :
    -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2 :=
  cls (fun s => F (x, y, s) ≤ 8 → -4 ≤ x ∧ x ≤ 4 ∧ -2 ≤ y ∧ y ≤ 2)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) (near_box5 x y) (near_box6 x y) (near_box7 x y) (near_box8 x y) (near_box9 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) (F_nonneg5 v.1 v.2.1) (F_nonneg6 v.1 v.2.1) (F_nonneg7 v.1 v.2.1) (F_nonneg8 v.1 v.2.1) (F_nonneg9 v.1 v.2.1) v.2.2

/-- For the cell (a - 4, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 10244906111529425274415000757808382876283209165667091275995292171408464106949006797408725038988321770681192400610232498144604232779409208965003484189237194318536945877729043819931949748770858308676307382829038642397478528529606048581636087915808558619674571686406042357253479474920357208983781593515741746677049803787091798305988825686988914680526424280453986968755616735277999224727104546025240495491813462723169872830834841844395222934668451467484627259498032094323466959990360654724931071246700384913374355418709854759358891613354529403031901956449416451481167286905063672502389667388490732304679576650131279519357373105796715392643131307924987494147508367036966012483792775477166741746808321318813131201475969439609332935134821987715878123702801722621069396183892098303259239801421824 >>> (6 * ((a * 5 + b) * 10 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 4, b - 2) and class s, potential i plus
22 + 2 a + 6 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 8) : ℕ :=
  tgetN 20202256 4 i.val * a + tgetN 2898927618 4 i.val * b + tgetN 1083819546900419094634657461614595355206094288107020904373248088868239167409665623371953302559471888971681422486584690655318052170206535506602795 6 (s * 8 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)

theorem fnt_tab : ∀ s : Fin 10, ∀ i : Fin 8, (tgetN 20202256 4 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 2898927618 4 i.val : ℤ) = Bc i + 6 ∧
    (tgetN 1083819546900419094634657461614595355206094288107020904373248088868239167409665623371953302559471888971681422486584690655318052170206535506602795 6 (s.val * 8 + i.val) : ℤ) = Cc s i - Ac i * 4 - Bc i * 2 + 22 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 10) (i : Fin 8) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 4, (b : ℤ) - 2, s) i + (22 + 2 * a + 6 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 10) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 4, (b : ℤ) - 2, s) + (22 + 2 * a + 6 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 8, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 6) 1 = FN + 2 dx' + 6 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 9).all fun a => (List.range 5).all fun b => (List.range 10).all fun s =>
    Nat.blt (30 + 2 * a + 6 * b) (FN a b s) || (a == 4 && b == 2 && s == 3) ||
      (Nat.blt (hint a b s) 40 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 8 ==
          FN a b s + 2 * dxv (hint a b s) + 6 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 8) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 4).toNat (by omega) (y + 2).toNat (by omega) s.val s.isLt
  have ex : (((x + 4).toNat : ℕ) : ℤ) - 4 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  generalize (x + 4).toNat = a at h' ex
  generalize (y + 2).toNat = b at h' ey
  have fv := FN_eq a b s
  rw [ex, ey] at fv
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at h'
  rcases h' with (h1 | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨⟨⟨hlen, hs⟩, hdx⟩, hdy⟩, hfe⟩
  · have c1 := (Nat.cast_lt (α := ℤ)).mpr h1
    push_cast at c1
    omega
  · exfalso
    apply hv
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hs0 : s = 3 := Fin.ext (by rw [h3]; rfl)
    subst hx0 hy0 hs0
    rfl
  · obtain ⟨e1, e2, e3, e4⟩ := edge_tab _ hlen
    have he : E.getD (hint a b s.val) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    rw [← e2] at hfe
    generalize E.getD (hint a b s.val) (0, 0, 0, 0) = e at he e1 e2 e3 e4 hfe
    obtain ⟨s1, s2, dx, dy⟩ := e
    simp only at e1 e2 e3 e4 hfe
    have hs1 : s1 = s := Fin.ext (e1.trans hs)
    have ha := adj_of_mem _ he x y
    simp only at ha
    rw [hs1] at ha
    refine ⟨_, ha, ?_⟩
    have fw := FN_eq (a + dxv (hint a b s.val) - 1) (b + dyv (hint a b s.val) - 1) s2
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 4 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 2 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 8
  · exact near_desc v hF hv
  · exact far_desc v (by omega)

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

/-- The graph distance from v0 is the largest facet potential. -/
theorem dist_eq (v : V) : G.dist v0 v = (F v).toNat := by
  apply dist_eq_of_potential G v0 (fun v => (F v).toNat)
  · show (F v0).toNat = 0
    decide
  · intro u w h
    have := lip u w h
    have := F_nonneg w
    have := F_nonneg u
    show (F w).toNat ≤ (F u).toNat + 1
    omega
  · intro v hv
    obtain ⟨w, hw, he⟩ := desc v hv
    refine ⟨w, hw, ?_⟩
    have := F_nonneg w
    show (F w).toNat + 1 = (F v).toNat
    omega


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 6 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 24 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 38550 2 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 2720 2 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 1

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 2361933828 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 6

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 35360 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 8) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 38165 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 8) : ℤ := beN i.val

theorem prim : ∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 10) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 10) (i j : Fin 8) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 8) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 8) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 10) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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
theorem F_attained (v : V) : ∃ k : Fin 8, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 8 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 8) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
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
theorem piece_iff (v : V) (i : Fin 8) (n : ℤ) :
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
(pot_i ≤ pot_j) plus cf0 times (6 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 52128794020658818287354506698584234151607467377185816576 3 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 8) (j : Fin 8) : ℤ := cf1N (j.val + 8 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 29931576953894624666030525631877787814492828963210496 3 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 8) (j : Fin 8) : ℤ := cf2N (j.val + 8 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 12420041687148185714213823618264081760 2 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 8) (j : Fin 8) : ℤ := cf3N (j.val + 8 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 7414628198549724049668813187761313360 2 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 8) (j : Fin 8) : ℤ := cf0N (j.val + 8 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 853286683673074239816062126026202982548313486401970039735085288898718703983093050766136744970955 4 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 6

def cT (s : Fin 10) (i : Fin 8) : ℤ := cTN (i.val + 8 * s.val)

theorem cT_eq : ∀ s : Fin 10, ∀ i : Fin 8, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 10) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (6 - cT s i)

instance (i j : Fin 8) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

/-- certC in natural numbers, for the kernel: Cc = cTV - 6, the negative terms moved across; the
previous facet of i is (i + 7) % 8, the next one (i + 1) % 8. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 8 * i) + cf2V (j + 8 * i) + cf0V (j + 8 * i)) * cTV (i + 8 * s) +
      cf3V (j + 8 * i) * cTV (j + 8 * s))
    (cf1V (j + 8 * i) * (cTV ((i + 7) % 8 + 8 * s) + (if (i + 7) % 8 < i then 1 else 0)) +
      cf2V (j + 8 * i) * (cTV ((i + 1) % 8 + 8 * s) + (if (i + 1) % 8 < i then 1 else 0)) +
      cf3V (j + 8 * i) * cTV (i + 8 * s) + cf0V (j + 8 * i) * 12)

def certOK : Bool :=
  (List.range 10).all fun s => (List.range 8).all fun i => (List.range 8).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 8, (i - 1).val = (i.val + 7) % 8 := by decide +kernel

theorem fin_next : ∀ i : Fin 8, (i + 1).val = (i.val + 1) % 8 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 10) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 8 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 7) % 8 := fun h => e1 (Fin.ext (h.trans a1.symm))
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
    cf3 i j * (cT s i - cT s j) + cf0 i j * (6 - cT s i)
  simp only [cf1, cf2, cf3, cf0, cf1N, cf2N, cf3N, cf0N, cT, cTN, Fin.lt_def, a1, a2]
  push_cast at ck ⊢
  ring_nf at ck ⊢
  linarith

theorem farkas4 (v : V) (h i k j : Fin 8) (e1 e2 r l1 l2 l3 l0 : ℤ)
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
def lev (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 10) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 10) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 10) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 10) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 10) (i : Fin 8) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 8) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 8) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 10) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 6 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 10) (i : Fin 8) (n u : ℤ) (hn : 6 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 6 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 6)) (1 * n + 6) ×ˢ
    (Finset.Icc (-(1 * n + 6)) (1 * n + 6) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 10, ∀ j : Fin 8, -6 ≤ Cc s j ∧ Cc s j ≤ 6 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 3 + 1 * Ac 4 = 4 ∧ 1 * Bc 3 + 1 * Bc 4 = 0 ∧
    1 * Ac 0 + 1 * Ac 7 = (-4) ∧ 1 * Bc 0 + 1 * Bc 7 = 0 ∧
    1 * Ac 5 + 1 * Ac 6 = 0 ∧ 1 * Bc 5 + 1 * Bc 6 = 12 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-12) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 10) :
    4 * x ≤ 2 * F (x, y, s) + 12 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 12 ∧
    12 * y ≤ 2 * F (x, y, s) + 12 ∧
    12 * (-y) ≤ 2 * F (x, y, s) + 12 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 3 + 1 * pot (x, y, s) 4 =
      4 * x + 1 * Cc s 3 + 1 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 3
  have l0 := Cbound s 4
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 7 =
      4 * (-x) + 1 * Cc s 0 + 1 * Cc s 7 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 7
  have k1 := Cbound s 0
  have l1 := Cbound s 7
  have e2 : 1 * pot (x, y, s) 5 + 1 * pot (x, y, s) 6 =
      12 * y + 1 * Cc s 5 + 1 * Cc s 6 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 5
  have r2 := le_F (x, y, s) 6
  have k2 := Cbound s 5
  have l2 := Cbound s 6
  have e3 : 1 * pot (x, y, s) 1 + 1 * pot (x, y, s) 2 =
      12 * (-y) + 1 * Cc s 1 + 1 * Cc s 2 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 1
  have r3 := le_F (x, y, s) 2
  have k3 := Cbound s 1
  have l3 := Cbound s 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 10) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 10) (i : Fin 8) (n : ℤ) (hn : 6 ≤ n) :
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
def inner (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 10) (i : Fin 8) (n : ℤ) (hn : 6 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 10 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 10 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 24 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 438904972044 5 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 224988521 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 9

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 4034326646 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 3

def mk (i : Fin 8) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 8, (24 : ℤ) = gc i * Lq i ∧
    24 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    24 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 10) (i : Fin 8) (n : ℤ) :
    inner s i (n + 24) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 24 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 24 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 24) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 24) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 24) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 2 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 10 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 24) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 26985 2 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 8) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 8, (2 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 2 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 2 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 8, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 8 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then mhN (c % 8) + mkN (c % 8) else 0

theorem gsN_eq (s : Fin 10) (i : Fin 8) (n : ℤ) :
    gsN (i.val + 8 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (10 * 8)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 1388883 3 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 3

def uh (i : Fin 8) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 1284000904 4 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 8) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 2419232818 4 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 1

def uk (i : Fin 8) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 2294581444 4 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 8) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 1013415910525771602246875142890645496213365329872575865481124156627841553736087176268373999768975 4 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 8

def vh (s : Fin 10) (i : Fin 8) : ℤ := vhN (i.val + 8 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 737656644062480555743229432228252175034340170782617860369837765383845691352577151842613895756455 4 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 8

def vk (s : Fin 10) (i : Fin 8) : ℤ := vkN (i.val + 8 * s.val)

def levT (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 10, ∀ i : Fin 8,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 10) (i : Fin 8) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 10) (i : Fin 8) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 10 × Fin 8, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 8 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then
    (uhN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vhN c) / dhN (c % 8) +
      (ukN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vkN c) / dkN (c % 8) + 1
  else 0

theorem innerN_eq (s : Fin 10) (i : Fin 8) (n : ℤ) :
    innerN (i.val + 8 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (10 * 8)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 10 × Fin 8 => innerT q.1 q.2 n)
    (fun c : Fin (10 * 8) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (10 * 8), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 10 × Fin 8 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (10 * 8) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (10 * 8), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 1 and below 1. -/
def dtabV (k : ℕ) : ℕ := ctabN 294601904847804052803262454468794057505447819686500 7 k

def tblV (k : ℕ) : ℕ := ctabN 294509116846190775099290395199949459840651046880260 7 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 24. -/
def dv (t : ℕ) : ℕ := dtabV (t % 24)

/-- The sequence in closed form: b(n + 24) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 24) + tblV ((n - 1) % 24)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 24) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 24 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 24 - 1 = n - 1 + 24 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 24)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 24) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 24 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 24 - 1 = n - 1 + 24 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 24)]
  ring

/-- b on the residue class of 1 + j mod 24. -/
theorem b_res (k j : ℕ) (hj : j < 24) : b (24 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (24 * k + (1 + j) < 1) by omega),
    show 24 * k + (1 + j) - 1 = j + 24 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 24), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 2. -/
def GsT : List ℤ := [100, 100]

theorem Gs_tab : ∀ r : ℕ, r < 2 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 24 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 24 → 1 * (dv t : ℤ) = GsT.getD ((1 + t) % 2) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 1 ≤ n) : 1 * (dv (n - 1) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 1) % 24) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 1) % 24) = dv (n - 1) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 24 ∣ 24)]
  have e2 : (1 + (n - 1) % 24) % 2 = n % 2 := by omega
  rw [e1, e2, ← Gs_tab (n % 2) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 2 : ℕ) : ℤ) + 2 * ((n / 2 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 6, ..., 29: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 24 →
    ((List.range (10 * 8)).all fun c => decide (0 ≤ innerN c (6 + (r : ℤ)))) = true ∧
      STN (6 + (r : ℤ)) = b (6 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 6 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 10) (i : Fin 8) (n : ℤ) (hn : 6 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 6 + t := ⟨(n - 6).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 24
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 8 * s.val < 10 * 8 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 24) (by omega) (by omega)
      have e : (6 : ℤ) + t = (6 + (t - 24 : ℕ)) + 24 := by
        push_cast [Nat.cast_sub (by omega : 24 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 6 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 6 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 30
    · obtain ⟨r, rfl⟩ : ∃ r, n = 6 + r := ⟨n - 6, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 24) (by omega) (by omega)
      have h2 := S_shift ((n - 24 : ℕ) : ℤ)
      have h3 := b_shift (n - 24) (by omega)
      have h4 := grow (n - 24) (by omega)
      rw [show n - 24 + 24 = n by omega] at h3
      rw [show ((n - 24 : ℕ) : ℤ) + 24 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 5 lie in the box -5 ≤ x ≤ 5, -1 ≤ y ≤ 1 (`small_box`), and
the kernel checks that those of the box are the 62 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 10) (h : F (x, y, s) ≤ 5) :
    -5 ≤ x ∧ x ≤ 5 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 5, with their values of F. -/
def smallV : List (V × ℤ) :=
  [((0, 0, 3), 0), ((0, 0, 4), 1), ((0, 0, 8), 1), ((1, 0, 4), 1), ((1, 1, 0), 1), (((-1), 0, 3), 2), ((0, 0, 7), 2), ((0, 0, 9), 2), ((0, 1, 0), 2), ((0, 1, 2), 2), ((1, 0, 3), 2), ((1, 0, 9), 2), ((1, 1, 1), 2), (((-1), 0, 4), 3), (((-1), 0, 8), 3), (((-1), 1, 2), 3), ((0, 0, 6), 3), ((0, 1, 1), 3), ((1, 0, 5), 3), ((1, 0, 6), 3), ((1, 0, 8), 3), ((1, 1, 2), 3), ((1, 1, 5), 3), ((2, 0, 4), 3), ((2, 1, 0), 3), (((-2), 0, 3), 4), (((-1), 0, 7), 4), (((-1), 0, 9), 4), (((-1), 1, 0), 4), (((-1), 1, 1), 4), ((0, 0, 2), 4), ((0, 0, 5), 4), ((0, 1, 5), 4), ((0, 1, 7), 4), ((1, 0, 1), 4), ((1, 0, 7), 4), ((1, 1, 6), 4), ((2, 0, 3), 4), ((2, 0, 9), 4), ((2, 1, 1), 4), ((2, 1, 5), 4), (((-2), 0, 4), 5), (((-2), 0, 8), 5), (((-2), 1, 2), 5), (((-1), 0, 2), 5), (((-1), 0, 6), 5), (((-1), 1, 5), 5), (((-1), 1, 7), 5), ((0, 0, 1), 5), ((0, 1, 6), 5), ((0, 1, 8), 5), ((1, 0, 0), 5), ((1, 0, 2), 5), ((1, 1, 7), 5), ((1, 1, 9), 5), ((2, 0, 5), 5), ((2, 0, 6), 5), ((2, 0, 8), 5), ((2, 1, 2), 5), ((2, 1, 6), 5), ((3, 0, 4), 5), ((3, 1, 0), 5)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 2, Bc = BTV - 6. -/
def ATV (k : ℕ) : ℕ := ctabN 379080 3 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 2

def AT (i : Fin 8) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 2898927618 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 6

def BT (i : Fin 8) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 8, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 5 at the box point ((a : ℤ) - 5, (b : ℤ) - 1, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 8).any fun i =>
    Nat.blt (11 + ATV i * 5 + 2 * a + BTV i * 1 + 6 * b)
      (ATV i * a + 10 + BTV i * b + 6 + cTV (i + 8 * s))

theorem big_pot (a b : ℕ) (s : Fin 10) (h : bigNat a b s.val = true) :
    (5 : ℤ) < F ((a : ℤ) - 5, (b : ℤ) - 1, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 5, (b : ℤ) - 1, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 11).all fun a => (List.range 3).all fun b => (List.finRange 10).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 5, (b : ℤ) - 1, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 5) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 5).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 5).toNat : ℕ) : ℤ) - 5 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · have := big_pot _ _ s h1
    rw [ex, ey] at this
    omega
  · rw [ex, ey] at h1
    exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 5) :
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

/-- The small spheres in closed form. -/
theorem small_ok : ∀ n : ℕ, n < 6 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 6 are counted in
`smallL`, those from 6 on are S(n), and both agree with the closed form b (`a_eq_b`). The step
from n to n + 24, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f.
follow, their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 6 ∨ 6 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

theorem dconst_base : ∀ r : ℕ, r < 24 → dtabV r = 100 := by
  decide +kernel
theorem dv_const : ∀ t : ℕ, dv t = 100 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 24) = a(n) + 100 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 24) = a n + 100 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 100 ∧ tblV 0 = 4 ∧ dv 1 = 100 ∧ tblV 1 = 8 ∧ dv 2 = 100 ∧ tblV 2 = 12 ∧ dv 3 = 100 ∧ tblV 3 = 16 ∧ dv 4 = 100 ∧ tblV 4 = 21 ∧ dv 5 = 100 ∧ tblV 5 = 26 ∧ dv 6 = 100 ∧ tblV 6 = 30 ∧ dv 7 = 100 ∧ tblV 7 = 34 ∧ dv 8 = 100 ∧ tblV 8 = 37 ∧ dv 9 = 100 ∧ tblV 9 = 40 ∧ dv 10 = 100 ∧ tblV 10 = 45 ∧ dv 11 = 100 ∧ tblV 11 = 50 ∧ dv 12 = 100 ∧ tblV 12 = 55 ∧ dv 13 = 100 ∧ tblV 13 = 60 ∧ dv 14 = 100 ∧ tblV 14 = 63 ∧ dv 15 = 100 ∧ tblV 15 = 66 ∧ dv 16 = 100 ∧ tblV 16 = 70 ∧ dv 17 = 100 ∧ tblV 17 = 74 ∧ dv 18 = 100 ∧ tblV 18 = 79 ∧ dv 19 = 100 ∧ tblV 19 = 84 ∧ dv 20 = 100 ∧ tblV 20 = 88 ∧ dv 21 = 100 ∧ tblV 21 = 92 ∧ dv 22 = 100 ∧ tblV 22 = 96 ∧ dv 23 = 100 ∧ tblV 23 = 100 := by
  decide +kernel

/-- The closed form per residue of n mod 24, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (24 * k + 1) = 100 * k + 4 ∧
    a (24 * k + 2) = 100 * k + 8 ∧
    a (24 * k + 3) = 100 * k + 12 ∧
    a (24 * k + 4) = 100 * k + 16 ∧
    a (24 * k + 5) = 100 * k + 21 ∧
    a (24 * k + 6) = 100 * k + 26 ∧
    a (24 * k + 7) = 100 * k + 30 ∧
    a (24 * k + 8) = 100 * k + 34 ∧
    a (24 * k + 9) = 100 * k + 37 ∧
    a (24 * k + 10) = 100 * k + 40 ∧
    a (24 * k + 11) = 100 * k + 45 ∧
    a (24 * k + 12) = 100 * k + 50 ∧
    a (24 * k + 13) = 100 * k + 55 ∧
    a (24 * k + 14) = 100 * k + 60 ∧
    a (24 * k + 15) = 100 * k + 63 ∧
    a (24 * k + 16) = 100 * k + 66 ∧
    a (24 * k + 17) = 100 * k + 70 ∧
    a (24 * k + 18) = 100 * k + 74 ∧
    a (24 * k + 19) = 100 * k + 79 ∧
    a (24 * k + 20) = 100 * k + 84 ∧
    a (24 * k + 21) = 100 * k + 88 ∧
    a (24 * k + 22) = 100 * k + 92 ∧
    a (24 * k + 23) = 100 * k + 96 ∧
    a (24 * k + 24) = 100 * k + 100 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 24 * k + 1 = 24 * k + (1 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 24 * k + 2 = 24 * k + (1 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 24 * k + 3 = 24 * k + (1 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 24 * k + 4 = 24 * k + (1 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 24 * k + 5 = 24 * k + (1 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]
  · rw [show 24 * k + 6 = 24 * k + (1 + 5) from rfl, b_res k 5 (by norm_num), c10, c11]
  · rw [show 24 * k + 7 = 24 * k + (1 + 6) from rfl, b_res k 6 (by norm_num), c12, c13]
  · rw [show 24 * k + 8 = 24 * k + (1 + 7) from rfl, b_res k 7 (by norm_num), c14, c15]
  · rw [show 24 * k + 9 = 24 * k + (1 + 8) from rfl, b_res k 8 (by norm_num), c16, c17]
  · rw [show 24 * k + 10 = 24 * k + (1 + 9) from rfl, b_res k 9 (by norm_num), c18, c19]
  · rw [show 24 * k + 11 = 24 * k + (1 + 10) from rfl, b_res k 10 (by norm_num), c20, c21]
  · rw [show 24 * k + 12 = 24 * k + (1 + 11) from rfl, b_res k 11 (by norm_num), c22, c23]
  · rw [show 24 * k + 13 = 24 * k + (1 + 12) from rfl, b_res k 12 (by norm_num), c24, c25]
  · rw [show 24 * k + 14 = 24 * k + (1 + 13) from rfl, b_res k 13 (by norm_num), c26, c27]
  · rw [show 24 * k + 15 = 24 * k + (1 + 14) from rfl, b_res k 14 (by norm_num), c28, c29]
  · rw [show 24 * k + 16 = 24 * k + (1 + 15) from rfl, b_res k 15 (by norm_num), c30, c31]
  · rw [show 24 * k + 17 = 24 * k + (1 + 16) from rfl, b_res k 16 (by norm_num), c32, c33]
  · rw [show 24 * k + 18 = 24 * k + (1 + 17) from rfl, b_res k 17 (by norm_num), c34, c35]
  · rw [show 24 * k + 19 = 24 * k + (1 + 18) from rfl, b_res k 18 (by norm_num), c36, c37]
  · rw [show 24 * k + 20 = 24 * k + (1 + 19) from rfl, b_res k 19 (by norm_num), c38, c39]
  · rw [show 24 * k + 21 = 24 * k + (1 + 20) from rfl, b_res k 20 (by norm_num), c40, c41]
  · rw [show 24 * k + 22 = 24 * k + (1 + 21) from rfl, b_res k 21 (by norm_num), c42, c43]
  · rw [show 24 * k + 23 = 24 * k + (1 + 22) from rfl, b_res k 22 (by norm_num), c44, c45]
  · rw [show 24 * k + 24 = 24 * k + (1 + 23) from rfl, b_res k 23 (by norm_num), c46, c47]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 16, 21, 26, 30, 34, 37, 40, 45, 50, 55, 60, 63, 66, 70, 74, 79, 84, 88, 92, 96, 100, 104, 108, 112, 116, 121, 126, 130, 134, 137, 140, 145, 150, 155, 160, 163, 166, 170, 174, 179, 184, 188, 192, 196, 200, 204] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 24 → (dv (t + 10) : ℤ) = 2 * (dv (t + 9) : ℤ) - 2 * (dv (t + 8) : ℤ) + 2 * (dv (t + 7) : ℤ) - 3 * (dv (t + 6) : ℤ) + 4 * (dv (t + 5) : ℤ) - 3 * (dv (t + 4) : ℤ) + 2 * (dv (t + 3) : ℤ) - 2 * (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = 2 * (dv (t + 9) : ℤ) - 2 * (dv (t + 8) : ℤ) + 2 * (dv (t + 7) : ℤ) - 3 * (dv (t + 6) : ℤ) + 4 * (dv (t + 5) : ℤ) - 3 * (dv (t + 4) : ℤ) + 2 * (dv (t + 3) : ℤ) - 2 * (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 24 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10]
  exact drec_base (t % 24) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 24 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 24 → (b (q + 11) : ℤ) = 2 * b (q + 10) - 2 * b (q + 9) + 2 * b (q + 8) - 3 * b (q + 7) + 4 * b (q + 6) - 3 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 11) : ℤ) = 2 * b (q + 10) - 2 * b (q + 9) + 2 * b (q + 8) - 3 * b (q + 7) + 4 * b (q + 6) - 3 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 24 ∨ 24 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 24 := ⟨q - 24, by omega⟩
      have h0 : (b (v + 11) : ℤ) = 2 * b (v + 10) - 2 * b (v + 9) + 2 * b (v + 8) - 3 * b (v + 7) + 4 * b (v + 6) - 3 * b (v + 5) + 2 * b (v + 4) - 2 * b (v + 3) + 2 * b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have s1 : b (v + 25) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (by omega)
        rw [show v + 1 + 24 = v + 25 by omega,
          show v + 1 - 1 = v + 0 by omega] at h
        exact h
      have s2 : b (v + 26) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (by omega)
        rw [show v + 2 + 24 = v + 26 by omega,
          show v + 2 - 1 = v + 1 by omega] at h
        exact h
      have s3 : b (v + 27) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (by omega)
        rw [show v + 3 + 24 = v + 27 by omega,
          show v + 3 - 1 = v + 2 by omega] at h
        exact h
      have s4 : b (v + 28) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 24 = v + 28 by omega,
          show v + 4 - 1 = v + 3 by omega] at h
        exact h
      have s5 : b (v + 29) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (by omega)
        rw [show v + 5 + 24 = v + 29 by omega,
          show v + 5 - 1 = v + 4 by omega] at h
        exact h
      have s6 : b (v + 30) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (by omega)
        rw [show v + 6 + 24 = v + 30 by omega,
          show v + 6 - 1 = v + 5 by omega] at h
        exact h
      have s7 : b (v + 31) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (by omega)
        rw [show v + 7 + 24 = v + 31 by omega,
          show v + 7 - 1 = v + 6 by omega] at h
        exact h
      have s8 : b (v + 32) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (by omega)
        rw [show v + 8 + 24 = v + 32 by omega,
          show v + 8 - 1 = v + 7 by omega] at h
        exact h
      have s9 : b (v + 33) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 24 = v + 33 by omega,
          show v + 9 - 1 = v + 8 by omega] at h
        exact h
      have s10 : b (v + 34) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (by omega)
        rw [show v + 10 + 24 = v + 34 by omega,
          show v + 10 - 1 = v + 9 by omega] at h
        exact h
      have s11 : b (v + 35) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (by omega)
        rw [show v + 11 + 24 = v + 35 by omega,
          show v + 11 - 1 = v + 10 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 35) : ℤ) = 2 * b (v + 34) - 2 * b (v + 33) + 2 * b (v + 32) - 3 * b (v + 31) + 4 * b (v + 30) - 3 * b (v + 29) + 2 * b (v + 28) - 2 * b (v + 27) + 2 * b (v + 26) - b (v + 25)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 3 * a (n - 4) + 4 * a (n - 5) - 3 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  rw [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega, show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega, show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 11, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 11 → 1 * (b n : ℤ) - 2 * (if 1 ≤ n then (b (n - 1) : ℤ) else 0) + 2 * (if 2 ≤ n then (b (n - 2) : ℤ) else 0) - 2 * (if 3 ≤ n then (b (n - 3) : ℤ) else 0) + 3 * (if 4 ≤ n then (b (n - 4) : ℤ) else 0) - 4 * (if 5 ≤ n then (b (n - 5) : ℤ) else 0) + 3 * (if 6 ≤ n then (b (n - 6) : ℤ) else 0) - 2 * (if 7 ≤ n then (b (n - 7) : ℤ) else 0) + 2 * (if 8 ≤ n then (b (n - 8) : ℤ) else 0) - 2 * (if 9 ≤ n then (b (n - 9) : ℤ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 2 + (if n = 2 then (1 : ℤ) else 0) * 2 + (if n = 3 then (1 : ℤ) else 0) * 2 + (if n = 4 then (1 : ℤ) else 0) * 3 + (if n = 5 then (1 : ℤ) else 0) * 5 + (if n = 6 then (1 : ℤ) else 0) * 3 + (if n = 7 then (1 : ℤ) else 0) * 2 + (if n = 8 then (1 : ℤ) else 0) * 2 + (if n = 9 then (1 : ℤ) else 0) * 2 + (if n = 10 then (1 : ℤ) else 0) * 1 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1)) =
      (X ^ 5 + X ^ 4 + X ^ 2 + X + 1) * (X ^ 5 + X ^ 4 + X ^ 3 + X + 1) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * ((X - 1) ^ 2 * (X ^ 4 + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1)) = C 1 * A - C 2 * (A * X ^ 1) + C 2 * (A * X ^ 2) - C 2 * (A * X ^ 3) + C 3 * (A * X ^ 4) - C 4 * (A * X ^ 5) + C 3 * (A * X ^ 6) - C 2 * (A * X ^ 7) + C 2 * (A * X ^ 8) - C 2 * (A * X ^ 9) + C 1 * (A * X ^ 10) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : ((X ^ 5 + X ^ 4 + X ^ 2 + X + 1) * (X ^ 5 + X ^ 4 + X ^ 3 + X + 1) : ℚ⟦X⟧) = C 1 + X ^ 1 * C 2 + X ^ 2 * C 2 + X ^ 3 * C 2 + X ^ 4 * C 3 + X ^ 5 * C 5 + X ^ 6 * C 3 + X ^ 7 * C 2 + X ^ 8 * C 2 + X ^ 9 * C 2 + X ^ 10 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h : (b (q + 11) : ℤ) = 2 * b (q + 10) - 2 * b (q + 9) + 2 * b (q + 8) - 3 * b (q + 7) + 4 * b (q + 6) - 3 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega, show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega, show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega, show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show 3 ≤ q + 11 by omega, show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega, show 6 ≤ q + 11 by omega, show 7 ≤ q + 11 by omega, show 8 ≤ q + 11 by omega, show 9 ≤ q + 11 by omega, show 10 ≤ q + 11 by omega, show ¬ q + 11 = 0 by omega, show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega, show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega, show ¬ q + 11 = 7 by omega, show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1)) =
      (X ^ 5 + X ^ 4 + X ^ 2 + X + 1) * (X ^ 5 + X ^ 4 + X ^ 3 + X + 1) := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 3 * a (n - 4) + 4 * a (n - 5) - 3 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 16, 21, 26, 30, 34, 37, 40, 45, 50, 55, 60, 63, 66, 70, 74, 79, 84, 88, 92, 96, 100, 104, 108, 112, 116, 121, 126, 130, 134, 137, 140, 145, 150, 155, 160, 163, 166, 170, 174, 179, 184, 188, 192, 196, 200, 204] := Count.controls

/-- The step a(n + 24) = a(n) + 100 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 24) = a n + 100 := Count.a_step n hn

/-- The closed form per residue of n mod 24, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (24 * k + 1) = 100 * k + 4 ∧
    a (24 * k + 2) = 100 * k + 8 ∧
    a (24 * k + 3) = 100 * k + 12 ∧
    a (24 * k + 4) = 100 * k + 16 ∧
    a (24 * k + 5) = 100 * k + 21 ∧
    a (24 * k + 6) = 100 * k + 26 ∧
    a (24 * k + 7) = 100 * k + 30 ∧
    a (24 * k + 8) = 100 * k + 34 ∧
    a (24 * k + 9) = 100 * k + 37 ∧
    a (24 * k + 10) = 100 * k + 40 ∧
    a (24 * k + 11) = 100 * k + 45 ∧
    a (24 * k + 12) = 100 * k + 50 ∧
    a (24 * k + 13) = 100 * k + 55 ∧
    a (24 * k + 14) = 100 * k + 60 ∧
    a (24 * k + 15) = 100 * k + 63 ∧
    a (24 * k + 16) = 100 * k + 66 ∧
    a (24 * k + 17) = 100 * k + 70 ∧
    a (24 * k + 18) = 100 * k + 74 ∧
    a (24 * k + 19) = 100 * k + 79 ∧
    a (24 * k + 20) = 100 * k + 84 ∧
    a (24 * k + 21) = 100 * k + 88 ∧
    a (24 * k + 22) = 100 * k + 92 ∧
    a (24 * k + 23) = 100 * k + 96 ∧
    a (24 * k + 24) = 100 * k + 100 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1)) =
      (X ^ 5 + X ^ 4 + X ^ 2 + X + 1) * (X ^ 5 + X ^ 4 + X ^ 3 + X + 1) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 3 * a (n - 4) + 4 * a (n - 5) - 3 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a311285

theorem OMA.solution : type_of% @OMA.S_oeis_a311285.main :=
  OMA.S_oeis_a311285.conjecture
