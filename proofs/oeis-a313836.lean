import OMAStatements.S_oeis_a313836

namespace OMA.S_oeis_a313836






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 9

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := ((T >>> (B * k) % 2 ^ B : ℕ) : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 2290649224
  | 1 => 2308540279
  | 2 => 1756080229
  | 3 => 1738189174
  | 4 => 2023397494
  | 5 => 2327545429
  | 6 => 2326431334
  | 7 => 1773971284
  | 8 => 2041288549
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1453046389 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 2612688214 4 8 i.val

def Cc (s : Fin 9) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val


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
theorem cls (P : Fin 9 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 9 × Fin 9 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 9) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 6 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (i j : Fin 8) (f : ℕ) : ℤ := tget 49017365254600847195519555559990902367201703201136411536181801143028952253521325844956590815652076918420583126406880072690981658838819361093742701275331847766489641743213518017348361028930368221250933069762820875098812736523030005751772570189073413361152614017184712563043282359395577943866078564307381508905712144912471158388944792332361038161101679649241666236823590086791556940984093418734574284431471476621573624264670179870069347460974517258322623274004331108872619054557591369601197212389256187656491990061166649830016189093518845786281136306954891464051604978982342640144 5 16 ((i.val * 8 + j.val) * 6 + f)

def fk1 (i j : Fin 8) : Fin 8 := ⟨(fd i j 0).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨(fd i j 1).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The source class and the potential changes dl of the edges of E, by position: entry p and
p * 8 + j. -/
def srcv (p : ℕ) : ℕ := (tget 51083178605933665575248835775560707259037945869369344 4 0 p).toNat

def dlv (p : ℕ) (j : Fin 8) : ℤ := tget 3336884503883393827609227961198022917517540430173173432376486509024785409824723452545510092110986388133526670640751015836834874697338829189211288696922300701673165740675739764550888190768280010610175405659688505147707014489367935552386890791492578486369950807086880870453113588120518787209803914546700034954556445448257745368093403632159154788249469149120114981061943929769352100657942387198473377508296008564902864338126711 4 8 (p * 8 + j.val)

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 8) : Fin 8 := ⟨(i.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 8) : Fin 8 := ⟨(i.val + 7) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 8) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel. -/
def farXY (i j : Fin 8) : Bool :=
  decide (0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farC (s : Fin 9) (i j : Fin 8) : Bool :=
  decide (0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
    fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (6 - Cc s i))

/-- The edge tables agree with E. -/
def dlOK : Bool :=
  (List.range 44).all fun p => decide (srcv p = (E.getD p (0, 0, 0, 0)).1.val) &&
    (List.finRange 8).all fun j => decide (dlv p j = dl (E.getD p (0, 0, 0, 0)) j)

/-- Beyond F = 5, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 9) (i j : Fin 8) (hxy : farXY i j = true) (hc0 : farC s i j = true) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 5 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc
  have q := of_decide_eq_true hxy
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 6 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j)
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) (pair_of (le_F _ _) h) (not_pair2 hc) (bound_of hF h)

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

/-- Descent rules beyond F = 5, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 5 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 10401192662967571427912689421907605072887756405920589175183427911762347298404048492119444265470987201741992836744317971385348524520871971946771405135896229466898419152336163408725236989981141008420277635841333157943840127128804323810691468490893163226948723814278803916733191341989932619145142173400025950975746514928153373310461941063855969801105889780058013453701806574056449625795688589559475537988177066530341544625624010924548613439673546646157551649932760163378851532070329748448775002737705407772405849158383319597035183724598296312263818488675639510974861271421558641240537909875935573865821381980533108947079894702671240241488394506021016187401531905646168841449685561666458024978842927327326592569771771682682985984535071656533183739254425199716536039422095293916308247793985640080293691021591489836567840315122255224798521827130614735422195454295782187476781394475090044889504436220528053463435862081
  | 1 => 10401192665971067331627037320553474804971185942954076720397723477986980809783239541679596553208000897307441662035706907861340376776590722665183022579549554554799276419928889358662945225954743237166332637536778897050005032375931166764521058408468902233354545067633086871320545274021675856303113413645186755610784350170904831634172013092241011677290201845946963923980079949578081046112458184877032308036889028125037451582341203167650818857570989791521557027774229235476571814335817849093181784718746682174891632774854198590895418650764418581418408017366018445631182125757732090268690587237426923887891115587366617161103176302843109760727006698488017652907546590385268622278688966135141763041936768472114640665814397118939522130335621217223186297059209379849819446527543548941139152584636029182321292109955165566284165728429048502181415799814186861619802317886055337837814096307290226641731696149863991987601039425
  | 2 => 10401192667172465693112776480011822697804557757767471738483441704476834214334915961503657468302806375533621192152262482451739849653809970778654438133470416596729793595225839431121336762039782072380293580551995167048285060014473027509212193000389607515522033056741713539317683372126026047897936807136510827032893869265742705213398514312259069139138620161831379804012967905572915630873002562391234078888064858641158134578504194054171012836601725177212224242478996339687925455870192009104921768509989758215821799332118484741356473039548042468381401556088729705190819222266038460139156773411529174637758630561814041000592475147209501519000707209905272512319425268005381917833613326793829853370128015933151144847779506456747009397083153826899211131197321430292188342050265120144811850281783368415422983970028600299347414883150798718397967616900899462613127466928447038446409698509204093364973208804153317403607064641
  | 3 => 10401192670175961596827124378657692429887987294800959283697737270701467725714107011063809756039820071099070017443651418927733653320194255658570890274746164325461277724897174995800867176347073024285234003375058556347745220130663254619496620652827532413701524689140896903909933465562095494727655603394616088362410350006668011885949318847695656101367510953659214907575624456758947204739276168634531559064507693982349254801915721006564886066649717885096169843105241337026940195683102694886361277775841264309277287687514907462507399649391743983908679535714841927274236136050569092779392122071887576854508320339767100030113840257645242699101417778651613843153308233351726769897687496477758390200032639169805433752957638512204614143821335641941442137898365713143472180070256828252439899719379812805430160087478790379065728474166283996091398095338285984154425411412756526553322259844029564191576404354854154239086846017
  | 4 => 10401192673780156681284341857032736139443522507170879704266707657974365536306929164543857884007883665745376618308013671662447791633382421156424493814911898866318478169008907142082945792350017341111134195921208691010193502610372314155385325212073674674842816605770022343587821913220256839140507046668950647747761064951685588507232371882138755942548213479959600118853302411594715994476092411602928449578949851877442454241530187378272046654847818139077623536401039546660591706326587807843462679827552383271593167087081842949709078313562896445876376745236277827593575931260554652851742675782406457755359182403683153522134267798182136675841358581525124645105358418190981847137475877548276251493265220910403567258883307186516490796705939272651689107759998558719956348923053264785235855876922789430613074707569669189628061379420047992591656983596116075607805405744221426193591443903579876811834988047194549952355248704
  | 5 => 10401192676783652584998689755678605933637791580063837982104634639805674241561706002119740937112191681246306195803780167057555182427567190290456885146327031850640270937152463001994781254038151050208452275233432054452589308692846831271600161853264444939566857886722503787123131612052855445119056157734837963017709226526410607746086808761080946089031723917451287856831864039714992405686755347749570564526763656203411572282602987110140228564530921363063378334121402507069099335501800817846522213962432333997162744427120651298243317623805243912530719482703251273871066149563501795627081397006006778385089594553605007829493788226291665825440495590145563894888108741497108825007041599425550005419260737525357287615659221995481811995744980685278937832385846041821554189293758590482208479277654308919658434723380630708297705558946018552583387218687125835852389920151241288119968552513729382429238572269783432880179915968
  | 6 => 10401192681589246030941646393511997411805019535528211955512060422355075068955032999392388449440472114247775553550929377536507180136456236959996156364686209569182736318979902047884806055849311526822616125060965503824533168725602531630831455056974223614037038953662577580669095298314696792451303885287446755597833088797846240764912839499806118068156246357363263972731352415365945835629820397326800005620310692051935033788030373778829585022829508431677847590605851947596841600179369395756428800340255974749109977579320601519433128096740871532418937295201458072179778581236129604850298897892046360326228221953054173602523500645124071937337837414431205822516516705883663446095079247007825963502034498221494001632035411699765479822804566756546293269074446769427560356574859407203459461841059806623394689686420973393597346321488320451941570114371722336362932799256816782328761033519937480950511083835030148363767144513
  | 7 => 10401192683992042753913124712428693197471763165155001991683496875334781878058385839040510279630083070700134613784040526717303198774896431944681735426296070825505166889456072311789087106206062082709258114868187507497625793978311045243390173068862711688401152282940480581292294918110153903230019780776908939278907349228504179137950315227732965575249721460905813886350326627899631224172001952186382093369761418895616703524106731090972346053511194679374145910325443218745705942970296688734349554338894741958923316457275962488703390661784609780275322825544255225576924454079807018893532122839589495775576396031246294327520763958737122589987671809921353014815083759489608539938679856398938099374978076570662067771141125051796265534097918399996925389950306673299019552708381042304987951570424589859057215286461307462913613559903028752783604907533655570680782418659435721501455666537956491375076357086905018768243712065
  | 8 => 10401192685193441115398863871887041090305134979968397009769215101824635282610062258864903210044939913061638949802942157749459400999476284112673216432519099122163460698480226676913543683010355329382915941677717854261302069034655412124368839739941347166130367683672481435474924055459814652567987763923658228017614031501957145207017827793459460916402308347586418884350973558584246597890066916000055813238865562199353084413729477642232080232461810512065560461937092071421810852635354519164752559979053165066177997420341797196235583315305897749603465564564306569315049633257981675517244047185447835597140395268310776875802952743100838144060574032800354549791687349714081116566202014787324593804048760030261976591035443132261396353225328425661200085901456424484720511594148961685141538654756650300903731654914175855273097400268445731311136511899075729813141191723822219676787519808995600680329846080163077270499505600
  | _ => 0

def rd (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 44 ∧ srcv (re s i c1 c2) = s.val ∧ dlv (re s i c1 c2) i ≤ -1 ∧
      dlv (re s i c1 c2) (nxt i) ≤ (c1.val : ℤ) - 1 ∧ dlv (re s i c1 c2) (prv i) ≤ (c2.val : ℤ) - 1)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 5)
  else if rk s i c1 c2 = 2 then
    decide (c1.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (nxt i) ∧ rg s i c1 c2 ∣ Bc i - Bc (nxt i) ∧
      ¬ rg s i c1 c2 ∣ (c1.val : ℤ) - (Cc s i - Cc s (nxt i)))
  else if rk s i c1 c2 = 3 then
    decide (c2.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (prv i) ∧ rg s i c1 c2 ∣ Bc i - Bc (prv i) ∧
      ¬ rg s i c1 c2 ∣ (c2.val : ℤ) - (Cc s i - Cc s (prv i)))
  else false

/-- All the tables: the far certificates for non-adjacent facets, the edge tables and the descent
rules. -/
theorem tables_ok : (∀ i j, nonadj i j → farXY i j = true) ∧ (∀ s i j, nonadj i j → farC s i j = true) ∧
    dlOK = true ∧ (∀ s i c1 c2, ruleOK s i c1 c2 = true) := by
  decide +kernel

theorem edge_at (p : ℕ) (hp : p < 44) :
    srcv p = (E.getD p (0, 0, 0, 0)).1.val ∧ ∀ j, dlv p j = dl (E.getD p (0, 0, 0, 0)) j := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.mem_finRange,
    forall_const] at h
  exact h p hp

theorem point_contra (x y : ℤ) (s : Fin 9) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 5)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 5 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 5 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 9) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 5 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
    have := far s i j (tables_ok.1 i j hna) (tables_ok.2.1 s i j hna) x y h hF
    omega
  · -- a corner point within F ≤ 5
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

theorem far_desc (v : V) (hF : 5 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 9) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 2 7 0 5 1 3 0 1 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 1 4 0 5 3 1 0 0 1 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box5 (x y : ℤ) (hF : F (x, y, 5) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 5) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 5 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg5 (x y : ℤ) : 0 ≤ F (x, y, 5) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 5) k).trans (show F (x, y, 5) ≤ -1 by omega)
  exact farkas_ub x y 5 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box6 (x y : ℤ) (hF : F (x, y, 6) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 6) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 6 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg6 (x y : ℤ) : 0 ≤ F (x, y, 6) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 6) k).trans (show F (x, y, 6) ≤ -1 by omega)
  exact farkas_ub x y 6 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box7 (x y : ℤ) (hF : F (x, y, 7) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 7) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 7 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg7 (x y : ℤ) : 0 ≤ F (x, y, 7) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 7) k).trans (show F (x, y, 7) ≤ -1 by omega)
  exact farkas_ub x y 7 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box8 (x y : ℤ) (hF : F (x, y, 8) ≤ 5) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 8) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 8 1 7 0 5 1 3 0 1 0 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 3 6 0 5 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 1 3 0 5 3 1 0 0 1 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 5 7 0 5 3 1 0 0 (-1) 3 10 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg8 (x y : ℤ) : 0 ≤ F (x, y, 8) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 8) k).trans (show F (x, y, 8) ≤ -1 by omega)
  exact farkas_ub x y 8 3 7 0 (-1) 3 3 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 5 lies in the cells |x| ≤ 2, |y| ≤ 2. -/
theorem near_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ 5) :
    -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 :=
  cls (fun s => F (x, y, s) ≤ 5 → -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) (near_box5 x y) (near_box6 x y) (near_box7 x y) (near_box8 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) (F_nonneg5 v.1 v.2.1) (F_nonneg6 v.1 v.2.1) (F_nonneg7 v.1 v.2.1) (F_nonneg8 v.1 v.2.1) v.2.2

/-- Every vertex of the box with F at most 5, other than v0, has a neighbor where F is one less. -/
def nearOK : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b => (List.finRange 9).all fun s =>
    decide (5 < F ((a : ℤ) - 2, (b : ℤ) - 2, s)) ||
      decide (((a : ℤ) - 2, (b : ℤ) - 2, s) = v0) ||
      E.any fun e => decide (e.1 = s ∧
        F ((a : ℤ) - 2 + e.2.2.1, (b : ℤ) - 2 + e.2.2.2, e.2.1) + 1 = F ((a : ℤ) - 2, (b : ℤ) - 2, s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 5) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 2).toNat (by omega) (y + 2).toNat (by omega) s
  have ex : (((x + 2).toNat : ℕ) : ℤ) - 2 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  rw [ex, ey] at h'
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h'
  rcases h' with (h1 | h1) | ⟨e, he, hs, hfe⟩
  · omega
  · exact absurd h1 hv
  · subst hs
    exact ⟨_, adj_of_mem e he x y, hfe⟩

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 5
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
from below, and for n ≥ 3 the other facets lie below by Farkas certificates (`certT`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`).
So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 21 moves every quotient by an integer (`inner_shift`, `S_shift`). -/

/-- The gradient of facet i is gc i times (Ap i, Bp i), and al i * Ap i + be i * Bp i = 1. -/
def gc : Fin 8 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1]

def Ap : Fin 8 → ℤ := ![(-3), (-1), 2, 3, 3, 1, (-2), (-3)]

def Bp : Fin 8 → ℤ := ![(-2), (-3), (-3), (-1), 2, 3, 3, 1]

def al : Fin 8 → ℤ := ![(-1), (-1), (-1), 0, 1, 1, 1, 0]

def be : Fin 8 → ℤ := ![1, 0, (-1), (-1), (-1), 0, 1, 1]

theorem prim : ∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 9) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 9) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 9) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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

/-- Multipliers (l1, l2, l3, l0) for the facet pair (i, j): l1 times (pot_(i-1) ≤ pot_i - [i-1 < i])
plus l2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus l3 times (pot_i ≤ pot_j) plus l0 times
(3 ≤ pot_i) is a contradiction, for every class. -/
def certT : Fin 8 → Fin 8 → ℤ × ℤ × ℤ × ℤ := ![
    ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 13, 7, 3), (3, 9, 4, 2), (0, 0, 1, 2), (7, 5, 4, 2), (13, 0, 9, 3), (0, 0, 0, 0)],
    ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (1, 3, 2, 1), (7, 7, 2, 1), (0, 0, 1, 2), (9, 5, 2, 1), (4, 2, 1, 0)],
    ![(8, 1, 5, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 13, 7, 3), (4, 9, 3, 0), (0, 0, 1, 2), (7, 6, 3, 0)],
    ![(9, 5, 2, 1), (4, 2, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (1, 3, 2, 1), (7, 7, 2, 1), (0, 0, 1, 2)],
    ![(0, 0, 1, 2), (7, 6, 3, 0), (8, 1, 5, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 13, 7, 3), (3, 9, 4, 2)],
    ![(7, 7, 2, 1), (0, 0, 1, 2), (9, 5, 2, 1), (4, 2, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (1, 3, 2, 1)],
    ![(0, 13, 7, 3), (3, 9, 4, 2), (0, 0, 1, 2), (7, 5, 4, 2), (8, 1, 5, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)],
    ![(0, 0, 0, 0), (1, 3, 2, 1), (7, 7, 2, 1), (0, 0, 1, 2), (9, 5, 2, 1), (4, 2, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0)]]

/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 8) : Prop :=
  let c := certT i j
  let h := i - 1
  let k := i + 1
  0 ≤ c.1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧ 0 ≤ c.2.2.2 ∧
    c.1 * (Ac h - Ac i) + c.2.1 * (Ac k - Ac i) + c.2.2.1 * (Ac i - Ac j) - c.2.2.2 * Ac i = 0 ∧
    c.1 * (Bc h - Bc i) + c.2.1 * (Bc k - Bc i) + c.2.2.1 * (Bc i - Bc j) - c.2.2.2 * Bc i = 0

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 9) (i j : Fin 8) : Prop :=
  let c := certT i j
  let h := i - 1
  let k := i + 1
  0 < c.1 * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    c.2.1 * (Cc s k - Cc s i + (if k < i then 1 else 0)) + c.2.2.1 * (Cc s i - Cc s j) +
    c.2.2.2 * (3 - Cc s i)

instance (i j : Fin 8) : Decidable (certG i j) := by
  unfold certG; infer_instance

instance (s : Fin 9) (i j : Fin 8) : Decidable (certC s i j) := by
  unfold certC; infer_instance

theorem certG_ok : ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

theorem certC_ok : ∀ s : Fin 9, ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certC s i j := by
  decide +kernel

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
def lev (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 9) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 9) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 9) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 9) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 9) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 9) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 3 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 9) (i : Fin 8) (n u : ℤ) (hn : 3 ≤ n)
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
  by_contra hne
  have f3 : pot (par s i (lev s i n) u) i ≤ pot (par s i (lev s i n) u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 3 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(2 * n + 8)) (2 * n + 8) ×ˢ
    (Finset.Icc (-(2 * n + 8)) (2 * n + 8) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 9, ∀ j : Fin 8, -4 ≤ Cc s j ∧ Cc s j ≤ 4 := by decide +kernel

/-- Opposite facet pairs: their potentials add up to a multiple of x or of y plus constants. -/
theorem box_pairs : Ac 2 + Ac 5 = 3 ∧ Bc 2 + Bc 5 = 0 ∧
    Ac 1 + Ac 6 = -3 ∧ Bc 1 + Bc 6 = 0 ∧
    Ac 4 + Ac 7 = 0 ∧ Bc 4 + Bc 7 = 3 ∧
    Ac 0 + Ac 3 = 0 ∧ Bc 0 + Bc 3 = -3 := by
  decide +kernel

theorem pair_le (pa pb f t ca cb lam cm : ℤ) (h1 : pa ≤ f) (h2 : pb ≤ f)
    (e : pa + pb = lam * t + ca + cb) (k1 : -cm ≤ ca) (k2 : -cm ≤ cb) :
    lam * t ≤ 2 * f + 2 * cm := by
  linarith

/-- Each pair of opposite facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 9) :
    3 * x ≤ 2 * F (x, y, s) + 2 * 4 ∧
    3 * (-x) ≤ 2 * F (x, y, s) + 2 * 4 ∧
    3 * y ≤ 2 * F (x, y, s) + 2 * 4 ∧
    3 * (-y) ≤ 2 * F (x, y, s) + 2 * 4 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  refine ⟨pair_le _ _ _ _ _ _ _ _ (le_F _ 2) (le_F _ 5) ?_ (Cbound s 2).1 (Cbound s 5).1,
    pair_le _ _ _ _ _ _ _ _ (le_F _ 1) (le_F _ 6) ?_ (Cbound s 1).1 (Cbound s 6).1,
    pair_le _ _ _ _ _ _ _ _ (le_F _ 4) (le_F _ 7) ?_ (Cbound s 4).1 (Cbound s 7).1,
    pair_le _ _ _ _ _ _ _ _ (le_F _ 0) (le_F _ 3) ?_ (Cbound s 0).1 (Cbound s 3).1⟩
  · simp only [pot]; linear_combination x * p1 + y * p2
  · simp only [pot]; linear_combination x * p3 + y * p4
  · simp only [pot]; linear_combination x * p5 + y * p6
  · simp only [pot]; linear_combination x * p7 + y * p8

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 9) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 9) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
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
def inner (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 9) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 9 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 8, inner p.1 p.2 n

/-- Shifting n by 21 = gc i * Lq i moves each quotient of a piece length by an integer. -/
def Lq : Fin 8 → ℤ := ![21, 21, 21, 21, 21, 21, 21, 21]

def mh : Fin 8 → ℤ := ![(-7), (-6), (-7), (-6), (-7), (-6), (-7), (-6)]

def mk : Fin 8 → ℤ := ![9, 7, 9, 7, 9, 7, 9, 7]

theorem shift_ok : ∀ i : Fin 8, (21 : ℤ) = gc i * Lq i ∧
    21 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    21 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 9) (i : Fin 8) (n : ℤ) :
    inner s i (n + 21) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 21 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 21 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 21) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 21) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 21) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 1 = gc i * lgq i. -/
def lgq : Fin 8 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1]

def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 9 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem lg_ok : ∀ i : Fin 8, (1 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_base : ∀ r : ℕ, r < 1 → Gs r = 108 := by
  decide +kernel

theorem Gs_const (n : ℤ) : Gs n = 108 := by
  have h0 := Int.emod_nonneg n (show (1 : ℤ) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos n (show (0 : ℤ) < 1 by norm_num)
  have e : Gs n = Gs (n % 1) := by
    simp only [Gs]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hq : n - Cc q.1 q.2 = (n % 1 - Cc q.1 q.2) + gc q.2 * (lgq q.2 * (n / 1)) := by
      have := Int.emod_add_mul_ediv n 1
      linear_combination (-1 : ℤ) * this + (n / 1) * lg_ok q.2
    rw [hq, Int.add_mul_emod_self_left]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, n % 1 = r := ⟨(n % 1).toNat, by omega⟩
  rw [e, hr]
  exact Gs_base r (by omega)

theorem S_shift (n : ℤ) : S (n + 21) = S n + 108 := by
  have h := Gs_const n
  simp only [Gs] at h
  simp only [S, inner_shift, Finset.sum_add_distrib, h]

theorem mhk_nonneg : ∀ i : Fin 8, 0 ≤ mh i + mk i := by decide +kernel

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uh : Fin 8 → ℤ := ![(-3), (-2), (-3), (-2), (-3), (-2), (-3), (-2)]

def vh : Fin 9 → Fin 8 → ℤ := ![![0, (-1), (-1), (-1), (-1), (-1), (-1), (-1)], ![(-1), (-1), (-1), 0, 0, (-1), (-1), (-2)], ![(-1), 0, 1, 1, 0, (-2), (-3), (-3)], ![0, 0, 1, 0, (-1), (-2), (-3), (-2)], ![(-1), 0, 0, 0, 0, (-2), (-2), (-2)], ![(-3), (-1), 0, 1, 2, (-1), (-2), (-3)], ![(-2), (-1), (-1), 1, 1, (-1), (-1), (-3)], ![(-2), 0, 1, 2, 1, (-2), (-3), (-4)], ![(-2), 0, 0, 1, 1, (-2), (-2), (-3)]]

def dh : Fin 8 → ℤ := ![9, 7, 9, 7, 9, 7, 9, 7]

def uk : Fin 8 → ℤ := ![3, 3, 3, 3, 3, 3, 3, 3]

def vk : Fin 9 → Fin 8 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, (-1)], ![0, 0, (-1), (-1), 0, 0, 1, 0], ![(-1), (-2), (-2), (-1), 1, 2, 2, 0], ![(-1), (-2), (-1), 0, 1, 2, 1, (-1)], ![(-1), (-1), (-1), (-1), 1, 1, 1, 0], ![0, (-1), (-2), (-3), 0, 1, 2, 2], ![0, 0, (-2), (-2), 0, 0, 2, 1], ![(-1), (-2), (-3), (-2), 1, 2, 3, 1], ![(-1), (-1), (-2), (-2), 1, 1, 2, 1]]

def dk : Fin 8 → ℤ := ![7, 9, 7, 9, 7, 9, 7, 9]

def innerT (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then
    (uh i * lev s i n + vh s i) / dh i + (uk i * lev s i n + vk s i) / dk i + 1 else 0

theorem tab_ok : ∀ s : Fin 9, ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  decide +kernel

theorem inner_eq (s : Fin 9) (i : Fin 8) (n : ℤ) : inner s i n = innerT s i n := by
  rw [inner, innerT]
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 8, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The sequence in closed form: b(n + 7) = b(n) + 36 for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then [1].getD n 0 else 36 * ((n - 1) / 7) + [5, 10, 16, 20, 26, 31, 36].getD ((n - 1) % 7) 0

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 7) = b n + 36 := by
  rw [b, b, if_neg (show ¬ (n + 7 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 7 - 1 = n - 1 + 7 by omega, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 7)]
  ring

/-- One kernel pass over n = 3, ..., 30: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 28 →
    (∀ q : Fin 9 × Fin 8, 0 ≤ innerT q.1 q.2 (3 + (r : ℤ))) ∧
      ST (3 + (r : ℤ)) = b (3 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 3 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 9) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 3 + t := ⟨(n - 3).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 21
    · rw [inner_eq]
      exact (period_ok t (by omega)).1 (s, i)
    · have := ih (t - 21) (by omega) (by omega)
      have e : (3 : ℤ) + t = (3 + (t - 21 : ℕ)) + 21 := by
        push_cast [Nat.cast_sub (by omega : 21 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 3 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The step of the closed form on one period. -/
theorem S_step_base (t : ℕ) (ht : t < 21) : S (3 + t + 7) = S (3 + t) + 36 := by
  have e : (3 : ℤ) + t + 7 = 3 + ((t + 7 : ℕ) : ℤ) := by push_cast; ring
  rw [e, S_eq_ST, S_eq_ST, (period_ok (t + 7) (by omega)).2, (period_ok t (by omega)).2,
    show 3 + (t + 7) = 3 + t + 7 by ring, b_step _ (by omega)]
  omega

theorem S_step (n : ℤ) (hn : 3 ≤ n) : S (n + 7) = S n + 36 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 3 + t := ⟨(n - 3).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 21
    · exact S_step_base t ht
    · have h := ih (t - 21) (by omega) (by omega)
      have e : (3 : ℤ) + t = (3 + (t - 21 : ℕ)) + 21 := by
        push_cast [Nat.cast_sub (by omega : 21 ≤ t)]; ring
      have h1 := S_shift ((3 : ℤ) + (t - 21 : ℕ))
      have h2 := S_shift ((3 : ℤ) + (t - 21 : ℕ) + 7)
      have e3 : S ((3 : ℤ) + (t - 21 : ℕ) + 21 + 7) = S ((3 : ℤ) + (t - 21 : ℕ) + 7 + 21) :=
        congrArg S (by ring)
      rw [e]
      linarith

/-! ## The small spheres

The points with F ≤ 2 lie in the box -4 ≤ x ≤ 4, -4 ≤ y ≤ 4 (`small_box`), and
the kernel checks that those of the box are the 16 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 9) (h : F (x, y, s) ≤ 2) :
    -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 2. -/
def smallL : List V :=
  [(0, 0, 0), ((-1), (-1), 7), ((-1), 0, 3), (0, (-1), 5), (0, (-1), 6), (0, 0, 1), ((-1), (-1), 2), ((-1), (-1), 5), ((-1), (-1), 8), ((-1), 0, 2), ((-1), 0, 4), (0, (-1), 1), (0, (-1), 8), (0, 0, 3), (0, 0, 4), (0, 0, 6)]

def smallOK : Bool :=
  (List.range 9).all fun a => (List.range 9).all fun b => (List.finRange 9).all fun s =>
    decide (2 < F ((a : ℤ) - 4, (b : ℤ) - 4, s)) ||
      decide (((a : ℤ) - 4, (b : ℤ) - 4, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 2) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 4).toNat (by omega) (y + 4).toNat (by omega) s
  have ex : (((x + 4).toNat : ℕ) : ℤ) - 4 = x := by omega
  have ey : (((y + 4).toNat : ℕ) : ℤ) - 4 = y := by omega
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
a(n + 7) = a(n) + 36 for n ≥ 1, the closed form per residue (`a_closed`), the controls, the
recurrence and the g.f. follow, their base cases checked by the kernel on b. -/

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

theorem S_eq_b (n : ℕ) (hn : 3 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · obtain ⟨r, rfl⟩ : ∃ r, n = 3 + r := ⟨n - 3, by omega⟩
      rw [S_eq_ST]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 7) (by omega) (by omega)
      have h2 := S_step ((n - 7 : ℕ) : ℤ) (by omega)
      have h3 := b_step (n - 7) (by omega)
      rw [show n - 7 + 7 = n by omega] at h3
      rw [show ((n - 7 : ℕ) : ℤ) + 7 = n by omega] at h2
      rw [h2, h1, h3]
      omega

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 3 ∨ 3 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 7) = a(n) + 36 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 7) = a n + 36 := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-- The closed form per residue of n mod 7, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (7 * k + 1) = 36 * k + 5 ∧
    a (7 * k + 2) = 36 * k + 10 ∧
    a (7 * k + 3) = 36 * k + 16 ∧
    a (7 * k + 4) = 36 * k + 20 ∧
    a (7 * k + 5) = 36 * k + 26 ∧
    a (7 * k + 6) = 36 * k + 31 ∧
    a (7 * k + 7) = 36 * k + 36 := by
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, if_neg (show ¬ (7 * k + 1 < 1) by omega),
      show 7 * k + 1 - 1 = 7 * k by omega, show (7 * k) / 7 = k by omega,
      show (7 * k) % 7 = 0 by omega]
    rfl
  · rw [b, if_neg (show ¬ (7 * k + 2 < 1) by omega),
      show 7 * k + 2 - 1 = 7 * k + 1 by omega, show (7 * k + 1) / 7 = k by omega,
      show (7 * k + 1) % 7 = 1 by omega]
    rfl
  · rw [b, if_neg (show ¬ (7 * k + 3 < 1) by omega),
      show 7 * k + 3 - 1 = 7 * k + 2 by omega, show (7 * k + 2) / 7 = k by omega,
      show (7 * k + 2) % 7 = 2 by omega]
    rfl
  · rw [b, if_neg (show ¬ (7 * k + 4 < 1) by omega),
      show 7 * k + 4 - 1 = 7 * k + 3 by omega, show (7 * k + 3) / 7 = k by omega,
      show (7 * k + 3) % 7 = 3 by omega]
    rfl
  · rw [b, if_neg (show ¬ (7 * k + 5 < 1) by omega),
      show 7 * k + 5 - 1 = 7 * k + 4 by omega, show (7 * k + 4) / 7 = k by omega,
      show (7 * k + 4) % 7 = 4 by omega]
    rfl
  · rw [b, if_neg (show ¬ (7 * k + 6 < 1) by omega),
      show 7 * k + 6 - 1 = 7 * k + 5 by omega, show (7 * k + 5) / 7 = k by omega,
      show (7 * k + 5) % 7 = 5 by omega]
    rfl
  · rw [b, if_neg (show ¬ (7 * k + 7 < 1) by omega),
      show 7 * k + 7 - 1 = 7 * k + 6 by omega, show (7 * k + 6) / 7 = k by omega,
      show (7 * k + 6) % 7 = 6 by omega]
    rfl

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 16, 20, 26, 31, 36, 41, 46, 52, 56, 62, 67, 72, 77, 82, 88, 92, 98, 103, 108, 113, 118, 124, 128, 134, 139, 144, 149, 154, 160, 164, 170, 175, 180, 185, 190, 196, 200, 206, 211, 216, 221, 226, 232, 236, 242, 247, 252] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The recurrence on its first 7 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 7 → (b (q + 9) : ℤ) = b (q + 8) + b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 9) : ℤ) = b (q + 8) + b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 7 ∨ 7 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨r, rfl⟩ : ∃ r, q = r + 7 := ⟨q - 7, by omega⟩
      have h0 : (b (r + 9) : ℤ) = b (r + 8) + b (r + 2) - b (r + 1) := ih r (by omega)
      have s1 : b (r + 8) = b (r + 1) + 36 := b_step (r + 1) (by omega)
      have s2 : b (r + 9) = b (r + 2) + 36 := b_step (r + 2) (by omega)
      have s8 : b (r + 15) = b (r + 8) + 36 := b_step (r + 8) (by omega)
      have s9 : b (r + 16) = b (r + 9) + 36 := b_step (r + 9) (by omega)
      show (b (r + 16) : ℤ) = b (r + 15) + b (r + 9) - b (r + 8)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = a (n - 1) + a (n - 7) - a (n - 8) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  rw [show q + 9 - 1 = q + 8 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

theorem bv0 : b 0 = 1 := by decide

theorem bv1 : b 1 = 5 := by decide

theorem bv2 : b 2 = 10 := by decide

theorem bv3 : b 3 = 16 := by decide

theorem bv4 : b 4 = 20 := by decide

theorem bv5 : b 5 = 26 := by decide

theorem bv6 : b 6 = 31 := by decide

theorem bv7 : b 7 = 36 := by decide

theorem bv8 : b 8 = 41 := by decide

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 8 - X ^ 7 - X + 1) =
      (X ^ 2 + X + 1) ^ 2 * (X ^ 4 + 2 * X ^ 3 - 2 * X ^ 2 + 2 * X + 1) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 8 - X ^ 7 - X + 1) = C 1 * A - C 1 * (A * X ^ 1) - C 1 * (A * X ^ 7) + C 1 * (A * X ^ 8) := by
    simp only [map_one]
    ring
  have e2 : ((X ^ 2 + X + 1) ^ 2 * (X ^ 4 + 2 * X ^ 3 - 2 * X ^ 2 + 2 * X + 1) : ℚ⟦X⟧) = C 1 + X ^ 1 * C 4 + X ^ 2 * C 5 + X ^ 3 * C 6 + X ^ 4 * C 4 + X ^ 5 * C 6 + X ^ 6 * C 5 + X ^ 7 * C 4 + X ^ 8 * C 1 := by
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
    have h : (b (q + 9) : ℤ) = b (q + 8) + b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega, show 1 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q + 9 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    linear_combination (1) * hq

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 8 - X ^ 7 - X + 1) =
      (X ^ 2 + X + 1) ^ 2 * (X ^ 4 + 2 * X ^ 3 - 2 * X ^ 2 + 2 * X + 1) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = a (n - 1) + a (n - 7) - a (n - 8) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a313836

theorem OMA.solution : type_of% @OMA.S_oeis_a313836.main :=
  OMA.S_oeis_a313836.conjecture
