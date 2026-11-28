import OMAStatements.S_oeis_a313962

namespace OMA.S_oeis_a313962






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 12

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 1664462299
  | 1 => 2290649224
  | 2 => 2023331959
  | 3 => 1397145034
  | 4 => 2004392344
  | 5 => 1737075079
  | 6 => 1682353354
  | 7 => 1450818199
  | 8 => 1718135464
  | 9 => 1415036089
  | 10 => 1432927144
  | 11 => 1700244409
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1738189174 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 3203093029 4 8 i.val

def Cc (s : Fin 12) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 1738189174 4 i

def BcN (i : ℕ) : ℕ := tgetN 3203093029 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 12) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


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
theorem cls (P : Fin 12 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 12 × Fin 12 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 12 × Fin 12 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 12 × Fin 12 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 12) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 5 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 23651640609696073651324301914129625488244131465829699790292628461037193297343930374461229954494844404411628085853224861157966225275632118247061125731893429334875377494889253140445563801479098408229610398363960767033745854447010886316855511448862477715645896387564910343245506452665043030972309884006516496355715333161557397250914464117822229027408255301946550429076649874315110836057182545148022417977118299990692342925241480311874292427438513979170379539755674273910851366965301006648313041075253100584118668600613852948280608408676737492808026220228536958976 5 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 1295687735170930265928301956589279919074510796165969801143904017427988480 4 p

def dstv (p : ℕ) : ℕ := tgetN 1177406135585703736481652233942563807271107140232010400952482512083759905 4 p

def dxv (p : ℕ) : ℕ := tgetN 360323787214354787674234739358778689 2 p

def dyv (p : ℕ) : ℕ := tgetN 443075998594971957634602336315070800 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 44740306512470336707537644312768427586715111968865614972532785324136258839849048468678292844162697665405363566074886914420662844253186833421253938973481726889144843070261076978342624680561246593822768835128392351279416979590885553238209336474915928704233522295386854710587377912365184333904513461102882620311713548561508568535088281447073647560948330819565630150137772020477671217597005419998143079640714182927686131052425335429369582317690586089404701215579876489749699266925667652677867179877960436638229260685823857267976312783803599847107346323502455256271413598348962732440 4 (p * 8 + j)

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
      fdN i j 4 * 13)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

def farOK : Bool := (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 12).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 60).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 12) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (5 - Cc s i)

/-- Beyond F = 4, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 12) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 4 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 5 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 4, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 4 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 10401192661766173066426950262449257180054384591107194157097709685272493893852372072295632361866220246617341029701270346767905889111002236914791416013233874914994578567797078291768969176700266367345506694946683465941780703374845366678328310307267286270572531748837000339761891705558368950439000257280100864103156093171597322957670329753383688554067600586196324441091351050958330611268024295096372007799034862524534032821231444870224750701279535018722863695236596572316596559472145915920294998717159233746009836745888517701090852734769526126473359115198092944183102121375387076180812537200861612657127703703571882325368063922685641687016439875196386201366328494523223400808395005612538458376779443784892279167912637633301620630796227518018798956770019205062685884281487362121403095920864946512823087062600399430807407838263272245060155615691799743860956082015866983572465651885813372782025693506210939171664568768
  | 1 => 10401192665971067331627037320553474836026605710883812086709539185790318406721032435687461935891648057275236882505518210001042491542490302999652999049039348300419065618033353043427971558525480247102762089829093098071976369822732420556996164164825113890093090120533086068799901787826531331061403622349601788183987294840705432746968500472044144830860609528333659532327456262881670445710360492088691739820711102468192469073679215818577822994872310535376415670426768047097371483619218524436955530769979533170714744329593182053850913264095549623193840093387617798059232883305185308096208174292333802112402957601501071004409051929853511921715974935481395100310583355203455324421549254149874465082905647785608200039023384538147908510880759370885140599320979902899330738897403823605445099265181300689021358167827673843529664809193566719845488484557726814082240370737362924298621678764752492124416663383392576022644794304
  | 2 => 10401192668974563235341385219199344537054615479987564265612019044211614321162430591239748840945014592872890487327095844337336131853640541706604309418195511007227216770428603861709008761486715449483848187152190012834665977116608430484552981936865366719885288076849061923713101406976856339150347370730159108306709488171502960393446808597439986320747222263105162240997245799235974698127622664271716433606219138297623930910801596288755672764300169022953190543312841428096744256562171900508315398797643235804958263848768825175596068811013557319948105512374164141342139194217974745148025406993372508378997805714226748774629306371589311149216422969864757152009560172430416012935011599278346335288928831674201757388124818345500636337273784357367326296422969069060314052046325170207080495911789743557319344991143923405059251015542843072765017310269786721152479658149377769747361646736033134400389831460460668701686046785
  | 3 => 10401192671377359958312863538116040322721359109614354301783455497191321130265783430887870671134625549325249547560206993518131174786747969610537471131044603726561168038115515453517436534098423136340309525262657176152729815876679182087297665985902897708813434398076591977199965761970935425598074570113584355010593406424589875550795118057159180637742872349794835673705125964921671581804215464531965267867428332877740078913798543880980046313215732455097847489309142808314244878943527037812180443605476760772279305467124082751280846903483090624837896740383917388704354475024398973009472613671044475274839742658004487937187507069167612781030481770591003664170545317897319772784092441770469838269291987716921602451009750064180540083626438325272795358017915005796871233387451917696367926251699981172455861158978613302361518791058245374873715349090777942990315099864019676734802065159782155233177794504294988052580999233
  | 4 => 10401192674981555042770081016491084063332314089914010088664241592267556537796398478375784181786336303939323734428233830955570057004301091906241362037546485642681043057315344437011472219736039042323184999480781369767332411095219950656706015060926083568868305213243578890366250104334744165614850103529452902697193908438995596885893619010021637828372333598931289629481074040537250711037362813410195809364317886407345259003380218359354701388649581849338594136338103812446259976058882419407134440755125713446006897598291194150893106292852701852354903481407767385444092909847237789232715296059401928577812324767185817728188798391447614137376601458632395593170320935448581723880811109378184672516266673620909656007806715861640569425327899286840614304909743477918809627399721728731754401614935943098574770836880217717908865124709155680450907187461459746217775082316190563154877541135614976062372232870737569001122048832
  | 5 => 10401192678585750127227298494866127679721589998494724410297764856130441557575841949832236161703458418682326728259540441060516303586070253322336956269743210234843524225926388634767893286198950674557479716195220620331778120517714774895817266555605012435782471373553213579766076851064824998111975495552427067234551208285567862494710172523441635721312947041383190863042096904329911111230395811756137675508109097063937697987375449272178917155680238630018023520533104787571881122954535336554828608490849978592840253175042132260809904775087174808474328605156701867859479549995960440785053123904696457618288306876932781251771118511760880200305472091584007854564119974486423890154901330265028456822971312339377809644382779689020537859927907227660344704322442833051658742386453741718451070051971857752630744254899292596620661092823866083528729164208347654736599785880031241254886741616507857724202106361148145996712321089
  | 6 => 10401192680387847669455907234053649518971647720714816937426342195865221664403356579568493542005692318089299453479329619499557549103203464581377776002961909050411211612898739674173219790320968969286476714441009980018336451579869044041103026447843696013093629177612821374499190766092453831313330737054269980680915237890909048477989689767204157435548654533131834555186774884665512608147654653403803928907283473304461684734779750761290871900587521398154894879959410581605236073586654534647181306345744477604400646226045570710149782724478173463598653539155801341313803725918803054413120779474464386513295929512450311491581687373747409732505256257314455226751598667430875314359653925024681758874854764144299449750531745966175736000826307149230070051056125823312252576093241876206945373165300707320951167710551455212201372425074576026998511554670997226622339532594861267264066335833834627397109535498455559020953481408
  | 7 => 10401192684592741934655994292157867143888449072561699500726355988579708580334224048952540737177485809813224378842318314012503910918838823082169860551992048991745487715768782952476607246282723623071788208639023490480985129794513597993305867186984141205423324998336743839635736040258762091948650939262044869807292619303559777004130640105840805794653459755447427698864981896528544436800296455271745441551277118935948462460982434426111227078481035033277227783845170241665128432905768272517879974031259764081481999234975069664015465803038033422991788457837183605248539329923677326284037398404280321711969668969783002714957491818184352616056022991644091962396761032182183023469570630074416284933858530810057861228469209266484635399596418365231146347516066263425782289171561078333950013991111745896199081761852433560144314527743155573516611612572543565818641873898495024425698451128328836165148629065400747040162652225
  | 8 => 10401192686995538657627472611074562960610612470118224903209608149362752986375369782608527950050743926233378659395048855120569327723701835150455067552857969567331358921321932287475180638982937083963996102269885956102971549915051027906218252273758100017881628719287530945360979448889538905067479516717726774915580268322138381390311539956631051706674556600531122565675593176755541406293482409886880756918271442324430588033743353694517554881510165375277135357666476818645044504535516894178934207403729779142196125517511407084364315293025739542251202171871547015070672359303696990382442413349149740530403918954238816960127966710266583307546523046942216314171828617280123310737331884337961523234705760287395989205152828722921226970716961504567862803403404511409207028907364535594750443215622162180191893220077664306807936323791391668172051763358816959781818155206645337696085373286032001307583558938146530502997194048
  | 9 => 10401192689999034561341820509720432661638622239221977082112088007784048900816767938160814855104110461831032264366818399669290806107665001704514639708544909582407130379298466629497801066289835031223566607311990377646832714743511026024200077806850565423038758875765683407810973575484431859915949143835154872368580131591770277186591141595293002048905904215218008168828420538880997073772402306605246469175475047487358942181198213769654658054988212192735309074736320905016530241296658794755861333667978341328183456357496623381932875736263043500831741202226941222572220003738374311963274763036820316256601447704852594950653736256850607777803768227083411452099241279103415858311481116882610566022395871289889835815328757720308640167137048657611254916718672736103712930407053512402471768450716833197580549097468239897176620426245559038499471336661707008012468486021482674800536641089160478232094296902448245689250160705
  | 10 => 10401192694203928826541907567824650286555423591068859645412101800498535816747635407545028057935929635622660619774762910735682131240603000536397672706119096712238504822188142651893900838348476095183582552022652386751277559117399664335936204560942454295882967226004075273471048492438410070865560629499223381891142164705210124937472745426907791291763125458708406493381478097156025386547599900373192918098512785451895164117991312142634508792464571352411963300000723664675664143368241165268618225390560514653183947985998987185983796489892847258215917039906103585456156242021524730762767186542620347137403090514510651766989993602642628417494926233581036574940244974777025019190477119132519612436130238287670293529364662279932614375078833759699021997491735850709386270113243484379087400506148697665295582245024501095389585099833283651276022640119255120670804330895724908340957231782463781790807393533380797231103418433
  | 11 => 10401192696006026368770516307012172125805481313288952172540679140233315923575150037281285438238163535029633344882980955874062223132484978526935466685622230170295907539816723161011736695281357277151594429980372287419891743377764893653079528582057705922012044105890565738006672220902977466640092094504035737178797098786508785978866271630820341723889354075352320046424602874380206969853913287594600059008461690348543190006636573419978728531526229750186614752136045129241527966279855725910008774338331498246802757330195301913146360338317133869082074558610495046368231247728272573673822324710030948411044170568277755000340702137083332896455149607467933067011382371031885443888990339035000407064820174584368999238101409525479923389598650355509300199396547905437648940895588169616475089737366200478935059674903905510855300038870421959985356205565776373619741832254376456700101688135334887957629403504878464888460033472
  | _ => 0

def rd (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 12) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 60 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 4)
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
theorem far_cert (s : Fin 12) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
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

theorem edge_at (p : ℕ) (hp : p < 60) :
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

theorem point_contra (x y : ℤ) (s : Fin 12) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 4)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 4 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 4 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 12) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 4 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 4
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

theorem far_desc (v : V) (hF : 4 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 12) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 2 7 0 4 3 6 0 1 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 3 5 0 4 6 3 0 (-1) 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 3 5 0 4 6 3 0 (-1) 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box5 (x y : ℤ) (hF : F (x, y, 5) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 5) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 5 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg5 (x y : ℤ) : 0 ≤ F (x, y, 5) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 5) k).trans (show F (x, y, 5) ≤ -1 by omega)
  exact farkas_ub x y 5 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box6 (x y : ℤ) (hF : F (x, y, 6) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 6) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 6 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 3 5 0 4 6 3 0 (-1) 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg6 (x y : ℤ) : 0 ≤ F (x, y, 6) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 6) k).trans (show F (x, y, 6) ≤ -1 by omega)
  exact farkas_ub x y 6 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box7 (x y : ℤ) (hF : F (x, y, 7) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 7) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 7 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg7 (x y : ℤ) : 0 ≤ F (x, y, 7) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 7) k).trans (show F (x, y, 7) ≤ -1 by omega)
  exact farkas_ub x y 7 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box8 (x y : ℤ) (hF : F (x, y, 8) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 8) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 8 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg8 (x y : ℤ) : 0 ≤ F (x, y, 8) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 8) k).trans (show F (x, y, 8) ≤ -1 by omega)
  exact farkas_ub x y 8 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box9 (x y : ℤ) (hF : F (x, y, 9) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 9) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 9 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 9 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 9 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 9 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg9 (x y : ℤ) : 0 ≤ F (x, y, 9) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 9) k).trans (show F (x, y, 9) ≤ -1 by omega)
  exact farkas_ub x y 9 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box10 (x y : ℤ) (hF : F (x, y, 10) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 10) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 10 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 10 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 10 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 10 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg10 (x y : ℤ) : 0 ≤ F (x, y, 10) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 10) k).trans (show F (x, y, 10) ≤ -1 by omega)
  exact farkas_ub x y 10 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box11 (x y : ℤ) (hF : F (x, y, 11) ≤ 4) : -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 11) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 11 1 7 0 4 3 6 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 11 3 6 0 4 6 3 0 (-1) 0 4 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 11 2 7 0 4 2 1 0 0 1 2 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 11 5 7 0 4 2 1 0 0 (-1) 2 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg11 (x y : ℤ) : 0 ≤ F (x, y, 11) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 11) k).trans (show F (x, y, 11) ≤ -1 by omega)
  exact farkas_ub x y 11 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 4 lies in the cells |x| ≤ 3, |y| ≤ 1. -/
theorem near_box (x y : ℤ) (s : Fin 12) (hF : F (x, y, s) ≤ 4) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 :=
  cls (fun s => F (x, y, s) ≤ 4 → -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) (near_box5 x y) (near_box6 x y) (near_box7 x y) (near_box8 x y) (near_box9 x y) (near_box10 x y) (near_box11 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) (F_nonneg5 v.1 v.2.1) (F_nonneg6 v.1 v.2.1) (F_nonneg7 v.1 v.2.1) (F_nonneg8 v.1 v.2.1) (F_nonneg9 v.1 v.2.1) (F_nonneg10 v.1 v.2.1) (F_nonneg11 v.1 v.2.1) v.2.2

/-- For the cell (a - 3, b - 1) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 288878149031346317464940071917510687554545301040660281953871667135351504532261719532831966091429653683098110514461932228435182098785477747292239742190021157591991808448053640545787763182938946223150351332781275903017670862892896555218665164183321207236426341738954306450455671296551492967122263480589723395659221094576136982743727268296954100799448339943714803494682624 >>> (6 * ((a * 3 + b) * 12 + s)) % 2 ^ 6

/-- Every vertex of the box with F at most 4, other than v0, has a neighbor where F is one less:
the edge at position hint. -/
def nearOK : Bool :=
  (List.range 7).all fun a => (List.range 3).all fun b => (List.finRange 12).all fun s =>
    decide (4 < F ((a : ℤ) - 3, (b : ℤ) - 1, s)) ||
      decide (((a : ℤ) - 3, (b : ℤ) - 1, s) = v0) ||
      decide (hint a b s.val < 60 ∧ (E.getD (hint a b s.val) (0, 0, 0, 0)).1 = s ∧
        F ((a : ℤ) - 3 + (E.getD (hint a b s.val) (0, 0, 0, 0)).2.2.1,
          (b : ℤ) - 1 + (E.getD (hint a b s.val) (0, 0, 0, 0)).2.2.2,
          (E.getD (hint a b s.val) (0, 0, 0, 0)).2.1) + 1 = F ((a : ℤ) - 3, (b : ℤ) - 1, s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 4) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 3).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  rw [ex, ey] at h'
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with (h1 | h1) | ⟨hlen, hs, hfe⟩
  · omega
  · exact absurd h1 hv
  · have he : E.getD (hint (x + 3).toNat (y + 1).toNat s.val) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    generalize E.getD (hint (x + 3).toNat (y + 1).toNat s.val) (0, 0, 0, 0) = e at he hs hfe
    subst hs
    exact ⟨_, adj_of_mem e he x y, hfe⟩

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 4
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
from below, and for n ≥ 3 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 18 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T, each stored as value + off. -/
def ctab (T B off k : ℕ) : ℤ := ((T >>> (B * k) % 2 ^ B : ℕ) : ℤ) - (off : ℤ)

def gcN (k : ℕ) : ℤ := ctab 255 1 0 k

def gc (i : Fin 8) : ℤ := gcN i.val

def ApN (k : ℕ) : ℤ := ctab 379080 3 2 k

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpN (k : ℕ) : ℤ := ctab 2630430723 4 6 k

def Bp (i : Fin 8) : ℤ := BpN i.val

def alN (k : ℕ) : ℤ := ctab 34850 2 1 k

def al (i : Fin 8) : ℤ := alN i.val

def beN (k : ℕ) : ℤ := ctab 38420 2 1 k

def be (i : Fin 8) : ℤ := beN i.val

theorem prim : ∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 12) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 12) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 12) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (3 ≤ pot_i) is a contradiction, for every class. -/

def cf1N (k : ℕ) : ℤ := ctab 42984704519227844900685379475595372353268245379063054848 3 0 k

def cf1 (i : Fin 8) (j : Fin 8) : ℤ := cf1N (j.val + 8 * i.val)

def cf2N (k : ℕ) : ℤ := ctab 15402777471518513979024121075438326585372342969752947008 3 0 k

def cf2 (i : Fin 8) (j : Fin 8) : ℤ := cf2N (j.val + 8 * i.val)

def cf3N (k : ℕ) : ℤ := ctab 14010960598654004454528867509618919837877676209712731328 3 0 k

def cf3 (i : Fin 8) (j : Fin 8) : ℤ := cf3N (j.val + 8 * i.val)

def cf0N (k : ℕ) : ℤ := ctab 664668071126218807697741434627041952 2 0 k

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
def cTN (k : ℕ) : ℤ := ctab 7717631559327246309757004646386444507157084429733615432480379502331387191861695816688295730398148473183280895785640 4 5 k

def cT (s : Fin 12) (i : Fin 8) : ℤ := cTN (i.val + 8 * s.val)

theorem cT_eq : ∀ s : Fin 12, ∀ i : Fin 8, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 12) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (3 - cT s i)

instance (i j : Fin 8) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- certC on the indices, for the kernel: the previous facet of i is (i + 7) % 8, the next
one (i + 1) % 8. -/
def certCN (s i j : ℕ) : Prop :=
  0 < cf1N (j + 8 * i) * (cTN ((i + 7) % 8 + 8 * s) - cTN (i + 8 * s) +
      (if (i + 7) % 8 < i then 1 else 0)) +
    cf2N (j + 8 * i) * (cTN ((i + 1) % 8 + 8 * s) - cTN (i + 8 * s) +
      (if (i + 1) % 8 < i then 1 else 0)) +
    cf3N (j + 8 * i) * (cTN (i + 8 * s) - cTN (j + 8 * s)) +
    cf0N (j + 8 * i) * (3 - cTN (i + 8 * s))

instance (s i j : ℕ) : Decidable (certCN s i j) := by
  unfold certCN; infer_instance

theorem certCN_ok : ∀ s, s < 12 → ∀ i, i < 8 → ∀ j, j < 8 →
    j = (i + 7) % 8 ∨ j = i ∨ j = (i + 1) % 8 ∨ certCN s i j := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 8, (i - 1).val = (i.val + 7) % 8 := by decide +kernel

theorem fin_next : ∀ i : Fin 8, (i + 1).val = (i.val + 1) % 8 := by decide +kernel

theorem certC_ok (s : Fin 12) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  rcases certCN_ok s.val s.isLt i.val i.isLt j.val j.isLt with h | h | h | h
  · exact absurd (Fin.ext (h.trans a1.symm)) e1
  · exact absurd (Fin.ext h) e2
  · exact absurd (Fin.ext (h.trans a2.symm)) e3
  · show 0 < cf1 i j * (cT s (i - 1) - cT s i + (if i - 1 < i then 1 else 0)) +
      cf2 i j * (cT s (i + 1) - cT s i + (if i + 1 < i then 1 else 0)) +
      cf3 i j * (cT s i - cT s j) + cf0 i j * (3 - cT s i)
    simp only [cf1, cf2, cf3, cf0, cT, Fin.lt_def, a1, a2]
    exact h

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
def lev (s : Fin 12) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 12) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 12) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 12) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 12) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 12) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 12) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 12) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 12) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 3 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 12) (i : Fin 8) (n u : ℤ) (hn : 3 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 3 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ
    (Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 12, ∀ j : Fin 8, -5 ≤ Cc s j ∧ Cc s j ≤ 5 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 3 + 1 * Ac 4 = 4 ∧ 1 * Bc 3 + 1 * Bc 4 = 0 ∧
    1 * Ac 0 + 1 * Ac 7 = (-4) ∧ 1 * Bc 0 + 1 * Bc 7 = 0 ∧
    1 * Ac 5 + 1 * Ac 6 = 0 ∧ 1 * Bc 5 + 1 * Bc 6 = 12 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-12) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 12) :
    4 * x ≤ 2 * F (x, y, s) + 10 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 10 ∧
    12 * y ≤ 2 * F (x, y, s) + 10 ∧
    12 * (-y) ≤ 2 * F (x, y, s) + 10 := by
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
noncomputable def PF (s : Fin 12) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 12) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
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
def inner (s : Fin 12) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 12) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 12 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 12 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 18 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqN (k : ℕ) : ℤ := ctab 638426106450 5 0 k

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhN (k : ℕ) : ℤ := ctab 12030323921 5 8 k

def mh (i : Fin 8) : ℤ := mhN i.val

def mkN (k : ℕ) : ℤ := ctab 590927665504 5 8 k

def mk (i : Fin 8) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 8, (18 : ℤ) = gc i * Lq i ∧
    18 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    18 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 12) (i : Fin 8) (n : ℤ) :
    inner s i (n + 18) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 18 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 18 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 18) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 18) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 18) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 1 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 12 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 18) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqN (k : ℕ) : ℤ := ctab 255 1 0 k

def lgq (i : Fin 8) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 8, (1 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 1 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 1 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 8, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 8 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then mhN (c % 8) + mkN (c % 8) else 0

theorem gsN_eq (s : Fin 12) (i : Fin 8) (n : ℤ) :
    gsN (i.val + 8 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (12 * 8)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhN (k : ℕ) : ℤ := ctab 104465978 4 4 k

def uh (i : Fin 8) : ℤ := uhN i.val

def dhN (k : ℕ) : ℤ := ctab 2627509404 4 0 k

def dh (i : Fin 8) : ℤ := dhN i.val

def ukN (k : ℕ) : ℤ := ctab 2741019488 4 4 k

def uk (i : Fin 8) : ℤ := ukN i.val

def dkN (k : ℕ) : ℤ := ctab 3385444809 4 0 k

def dk (i : Fin 8) : ℤ := dkN i.val

def vhN (k : ℕ) : ℤ := ctab 15575547264739569396711051008264268298124126112748160576858876729733473479485865071333138644161850293993717143446907 4 6 k

def vh (s : Fin 12) (i : Fin 8) : ℤ := vhN (i.val + 8 * s.val)

def vkN (k : ℕ) : ℤ := ctab 5757704354504500444669729472741792447469898716954876216910953693249953223314808629440393236118200498719327588497764 4 6 k

def vk (s : Fin 12) (i : Fin 8) : ℤ := vkN (i.val + 8 * s.val)

def levT (s : Fin 12) (i : Fin 8) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 12) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_ok : ∀ s : Fin 12, ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  decide +kernel

theorem inner_eq (s : Fin 12) (i : Fin 8) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 12 × Fin 8, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 8 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then
    (uhN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vhN c) / dhN (c % 8) +
      (ukN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vkN c) / dkN (c % 8) + 1
  else 0

theorem innerN_eq (s : Fin 12) (i : Fin 8) (n : ℤ) :
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
def STN (n : ℤ) : ℤ := ((List.range (12 * 8)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 12 × Fin 8 => innerT q.1 q.2 n)
    (fun c : Fin (12 * 8) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (12 * 8), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 12 × Fin 8 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (12 * 8) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (12 * 8), sum_range_list]

/-- The step of the closed form at residue t mod 9. -/
def dv (t : ℕ) : ℕ := [48, 48, 48, 48, 48, 48, 48, 48, 48].getD (t % 9) 0

/-- The sequence in closed form: b(n + 9) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then [1].getD n 0 else dv (n - 1) * ((n - 1) / 9) + [5, 10, 17, 21, 27, 31, 38, 43, 48].getD ((n - 1) % 9) 0

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 9) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 9 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 9 - 1 = n - 1 + 9 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 9)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 18) = b n + 2 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 18 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 18 - 1 = n - 1 + 9 * 2 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 9)]
  ring

/-- The growth of b over 18 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 9 → 2 * (dv t : ℤ) = GsN (1 + (t : ℤ)) := by
  decide +kernel

theorem grow (n : ℕ) (hn : 1 ≤ n) : 2 * (dv (n - 1) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 1) % 9) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 1) % 9) = dv (n - 1) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 9 ∣ 9)]
  rw [e1, ← Gs_eq_GsN] at h1
  rw [h1]
  have e : (((1 : ℤ) + (((n - 1) % 9 : ℕ) : ℤ)) + 1 * (9 * (((n - 1) / 9 : ℕ) : ℤ))) = n := by
    have := Nat.mod_add_div (n - 1) 9
    omega
  rw [← e, Gs_periodic]

/-- One kernel pass over n = 3, ..., 20: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 18 →
    ((List.range (12 * 8)).all fun c => decide (0 ≤ innerN c (3 + (r : ℤ)))) = true ∧
      STN (3 + (r : ℤ)) = b (3 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 3 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 12) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 3 + t := ⟨(n - 3).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 18
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 8 * s.val < 12 * 8 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 18) (by omega) (by omega)
      have e : (3 : ℤ) + t = (3 + (t - 18 : ℕ)) + 18 := by
        push_cast [Nat.cast_sub (by omega : 18 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 3 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 3 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 21
    · obtain ⟨r, rfl⟩ : ∃ r, n = 3 + r := ⟨n - 3, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 18) (by omega) (by omega)
      have h2 := S_shift ((n - 18 : ℕ) : ℤ)
      have h3 := b_shift (n - 18) (by omega)
      have h4 := grow (n - 18) (by omega)
      rw [show n - 18 + 18 = n by omega] at h3
      rw [show ((n - 18 : ℕ) : ℤ) + 18 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 2 lie in the box -3 ≤ x ≤ 3, -1 ≤ y ≤ 1 (`small_box`), and
the kernel checks that those of the box are the 16 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 12) (h : F (x, y, s) ≤ 2) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 2. -/
def smallL : List V :=
  [(0, 0, 1), ((-1), 0, 2), ((-1), 0, 5), (0, 0, 2), (0, 0, 4), (0, 1, 0), ((-1), 0, 1), ((-1), 0, 4), ((-1), 0, 7), ((-1), 1, 3), (0, 0, 5), (0, 0, 8), (0, 1, 3), (0, 1, 6), (1, 0, 1), (1, 1, 0)]

def smallOK : Bool :=
  (List.range 7).all fun a => (List.range 3).all fun b => (List.finRange 12).all fun s =>
    decide (2 < F ((a : ℤ) - 3, (b : ℤ) - 1, s)) ||
      decide (((a : ℤ) - 3, (b : ℤ) - 1, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 2) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 3).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  rw [ex, ey] at h'
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · omega
  · exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 2) :
    cnt n = ((smallL.filter (fun v => decide (F v = n))).toFinset).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨small_mem v (by omega), h⟩, fun h => h.2⟩

/-- The small spheres in closed form. -/
theorem small_ok : ∀ n : ℕ, n < 3 →
    ((smallL.filter (fun v => decide (F v = (n : ℤ)))).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 3 are counted in
`smallL`, those from 3 on are S(n), and both agree with the closed form b (`a_eq_b`). The step
from n to n + 9, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f.
follow, their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 3 ∨ 3 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

theorem dconst_base : ∀ r : ℕ, r < 9 → [48, 48, 48, 48, 48, 48, 48, 48, 48].getD r 0 = 48 := by
  decide +kernel
theorem dv_const : ∀ t : ℕ, dv t = 48 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 9) = a(n) + 48 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 9) = a n + 48 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-- The closed form per residue of n mod 9, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (9 * k + 1) = 48 * k + 5 ∧
    a (9 * k + 2) = 48 * k + 10 ∧
    a (9 * k + 3) = 48 * k + 17 ∧
    a (9 * k + 4) = 48 * k + 21 ∧
    a (9 * k + 5) = 48 * k + 27 ∧
    a (9 * k + 6) = 48 * k + 31 ∧
    a (9 * k + 7) = 48 * k + 38 ∧
    a (9 * k + 8) = 48 * k + 43 ∧
    a (9 * k + 9) = 48 * k + 48 := by
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, if_neg (show ¬ (9 * k + 1 < 1) by omega),
      show 9 * k + 1 - 1 = 9 * k by omega, dv, show (9 * k) / 9 = k by omega,
      show (9 * k) % 9 = 0 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 2 < 1) by omega),
      show 9 * k + 2 - 1 = 9 * k + 1 by omega, dv, show (9 * k + 1) / 9 = k by omega,
      show (9 * k + 1) % 9 = 1 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 3 < 1) by omega),
      show 9 * k + 3 - 1 = 9 * k + 2 by omega, dv, show (9 * k + 2) / 9 = k by omega,
      show (9 * k + 2) % 9 = 2 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 4 < 1) by omega),
      show 9 * k + 4 - 1 = 9 * k + 3 by omega, dv, show (9 * k + 3) / 9 = k by omega,
      show (9 * k + 3) % 9 = 3 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 5 < 1) by omega),
      show 9 * k + 5 - 1 = 9 * k + 4 by omega, dv, show (9 * k + 4) / 9 = k by omega,
      show (9 * k + 4) % 9 = 4 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 6 < 1) by omega),
      show 9 * k + 6 - 1 = 9 * k + 5 by omega, dv, show (9 * k + 5) / 9 = k by omega,
      show (9 * k + 5) % 9 = 5 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 7 < 1) by omega),
      show 9 * k + 7 - 1 = 9 * k + 6 by omega, dv, show (9 * k + 6) / 9 = k by omega,
      show (9 * k + 6) % 9 = 6 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 8 < 1) by omega),
      show 9 * k + 8 - 1 = 9 * k + 7 by omega, dv, show (9 * k + 7) / 9 = k by omega,
      show (9 * k + 7) % 9 = 7 by omega]
    rfl
  · rw [b, if_neg (show ¬ (9 * k + 9 < 1) by omega),
      show 9 * k + 9 - 1 = 9 * k + 8 by omega, dv, show (9 * k + 8) / 9 = k by omega,
      show (9 * k + 8) % 9 = 8 by omega]
    rfl

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 17, 21, 27, 31, 38, 43, 48, 53, 58, 65, 69, 75, 79, 86, 91, 96, 101, 106, 113, 117, 123, 127, 134, 139, 144, 149, 154, 161, 165, 171, 175, 182, 187, 192, 197, 202, 209, 213, 219, 223, 230, 235, 240, 245, 250, 257, 261] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 9 → (dv (t + 8) : ℤ) = 2 * (dv (t + 7) : ℤ) - (dv (t + 6) : ℤ) - (dv (t + 5) : ℤ) + 2 * (dv (t + 4) : ℤ) - (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 8) : ℤ) = 2 * (dv (t + 7) : ℤ) - (dv (t + 6) : ℤ) - (dv (t + 5) : ℤ) + 2 * (dv (t + 4) : ℤ) - (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 9 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8]
  exact drec_base (t % 9) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 9 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 9 → (b (q + 9) : ℤ) = 2 * b (q + 8) - b (q + 7) - b (q + 6) + 2 * b (q + 5) - b (q + 4) - b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 9) : ℤ) = 2 * b (q + 8) - b (q + 7) - b (q + 6) + 2 * b (q + 5) - b (q + 4) - b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 9 ∨ 9 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 9 := ⟨q - 9, by omega⟩
      have h0 : (b (v + 9) : ℤ) = 2 * b (v + 8) - b (v + 7) - b (v + 6) + 2 * b (v + 5) - b (v + 4) - b (v + 3) + 2 * b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have s1 : b (v + 10) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (by omega)
        rw [show v + 1 + 9 = v + 10 by omega,
          show v + 1 - 1 = v + 0 by omega] at h
        exact h
      have s2 : b (v + 11) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (by omega)
        rw [show v + 2 + 9 = v + 11 by omega,
          show v + 2 - 1 = v + 1 by omega] at h
        exact h
      have s3 : b (v + 12) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (by omega)
        rw [show v + 3 + 9 = v + 12 by omega,
          show v + 3 - 1 = v + 2 by omega] at h
        exact h
      have s4 : b (v + 13) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 9 = v + 13 by omega,
          show v + 4 - 1 = v + 3 by omega] at h
        exact h
      have s5 : b (v + 14) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (by omega)
        rw [show v + 5 + 9 = v + 14 by omega,
          show v + 5 - 1 = v + 4 by omega] at h
        exact h
      have s6 : b (v + 15) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (by omega)
        rw [show v + 6 + 9 = v + 15 by omega,
          show v + 6 - 1 = v + 5 by omega] at h
        exact h
      have s7 : b (v + 16) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (by omega)
        rw [show v + 7 + 9 = v + 16 by omega,
          show v + 7 - 1 = v + 6 by omega] at h
        exact h
      have s8 : b (v + 17) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (by omega)
        rw [show v + 8 + 9 = v + 17 by omega,
          show v + 8 - 1 = v + 7 by omega] at h
        exact h
      have s9 : b (v + 18) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 9 = v + 18 by omega,
          show v + 9 - 1 = v + 8 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 18) : ℤ) = 2 * b (v + 17) - b (v + 16) - b (v + 15) + 2 * b (v + 14) - b (v + 13) - b (v + 12) + 2 * b (v + 11) - b (v + 10)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5) - a (n - 6) + 2 * a (n - 7) - a (n - 8) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  rw [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

theorem bv0 : b 0 = 1 := by decide

theorem bv1 : b 1 = 5 := by decide

theorem bv2 : b 2 = 10 := by decide

theorem bv3 : b 3 = 17 := by decide

theorem bv4 : b 4 = 21 := by decide

theorem bv5 : b 5 = 27 := by decide

theorem bv6 : b 6 = 31 := by decide

theorem bv7 : b 7 = 38 := by decide

theorem bv8 : b 8 = 43 := by decide

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1)) =
      (X ^ 2 + 1) * (X ^ 6 + 3 * X ^ 5 + 3 * X + 1) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * ((X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1)) = C 1 * A - C 2 * (A * X ^ 1) + C 1 * (A * X ^ 2) + C 1 * (A * X ^ 3) - C 2 * (A * X ^ 4) + C 1 * (A * X ^ 5) + C 1 * (A * X ^ 6) - C 2 * (A * X ^ 7) + C 1 * (A * X ^ 8) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : ((X ^ 2 + 1) * (X ^ 6 + 3 * X ^ 5 + 3 * X + 1) : ℚ⟦X⟧) = C 1 + X ^ 1 * C 3 + X ^ 2 * C 1 + X ^ 3 * C 3 + X ^ 5 * C 3 + X ^ 6 * C 1 + X ^ 7 * C 3 + X ^ 8 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> norm_num [bv0, bv1, bv2, bv3, bv4, bv5, bv6, bv7, bv8]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h : (b (q + 9) : ℤ) = 2 * b (q + 8) - b (q + 7) - b (q + 6) + 2 * b (q + 5) - b (q + 4) - b (q + 3) + 2 * b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega, show 1 ≤ q + 9 by omega, show 2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega, show 6 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q + 9 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1)) =
      (X ^ 2 + 1) * (X ^ 6 + 3 * X ^ 5 + 3 * X + 1) := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5) - a (n - 6) + 2 * a (n - 7) - a (n - 8) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 17, 21, 27, 31, 38, 43, 48, 53, 58, 65, 69, 75, 79, 86, 91, 96, 101, 106, 113, 117, 123, 127, 134, 139, 144, 149, 154, 161, 165, 171, 175, 182, 187, 192, 197, 202, 209, 213, 219, 223, 230, 235, 240, 245, 250, 257, 261] := Count.controls

/-- The step a(n + 9) = a(n) + 48 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 9) = a n + 48 := Count.a_step n hn

/-- The closed form per residue of n mod 9, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (9 * k + 1) = 48 * k + 5 ∧
    a (9 * k + 2) = 48 * k + 10 ∧
    a (9 * k + 3) = 48 * k + 17 ∧
    a (9 * k + 4) = 48 * k + 21 ∧
    a (9 * k + 5) = 48 * k + 27 ∧
    a (9 * k + 6) = 48 * k + 31 ∧
    a (9 * k + 7) = 48 * k + 38 ∧
    a (9 * k + 8) = 48 * k + 43 ∧
    a (9 * k + 9) = 48 * k + 48 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1)) =
      (X ^ 2 + 1) * (X ^ 6 + 3 * X ^ 5 + 3 * X + 1) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5) - a (n - 6) + 2 * a (n - 7) - a (n - 8) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a313962

theorem OMA.solution : type_of% @OMA.S_oeis_a313962.main :=
  OMA.S_oeis_a313962.conjecture
