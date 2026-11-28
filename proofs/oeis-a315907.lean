import OMAStatements.S_oeis_a315907

namespace OMA.S_oeis_a315907






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 5

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := ((T >>> (B * k) % 2 ^ B : ℕ) : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 2557966489
  | 1 => 2594797159
  | 2 => 2308474744
  | 3 => 2575792009
  | 4 => 2290649224
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1738189174 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 2612622679 4 8 i.val

def Cc (s : Fin 5) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val


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
theorem cls (P : Fin 5 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 5 × Fin 5 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 5 × Fin 5 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 5 × Fin 5 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 5) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
def fd (i j : Fin 8) (f : ℕ) : ℤ := tget 49017365254600847190210036405665234116903906762453286831533053760081723245389017369694584181791077432824917276771673239192155476761026691444757158921592033724388250061693493135395563367617098081040031092781402289131562973209777695366848937677851873922653934147756075942629337083045606733827850824906082817914326241873362411207319328728189406365122562326400463966408526718265507324856656177557019787698387679321796056542679085889814068361922350835950602160959711009477758873298227059777769037168585782117608975525756727364958270819141997893753795612013200828959669578578688229904 5 16 ((i.val * 8 + j.val) * 6 + f)

def fk1 (i j : Fin 8) : Fin 8 := ⟨(fd i j 0).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨(fd i j 1).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The source class and the potential changes dl of the edges of E, by position: entry p and
p * 8 + j. -/
def srcv (p : ℕ) : ℕ := (tget 2698492559504311615488 3 0 p).toNat

def dlv (p : ℕ) (j : Fin 8) : ℤ := tget 731381465217288937028647738282840554865975267890452681025225482583415582384641673555157042673524699606264307229458387676264830471337855350626875524686644866905656454489181677661523687855355781664656998599896491462321301219213539481 4 8 (p * 8 + j.val)

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
def farC (s : Fin 5) (i j : Fin 8) : Bool :=
  decide (0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
    fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (5 - Cc s i))

/-- The edge tables agree with E. -/
def dlOK : Bool :=
  (List.range 24).all fun p => decide (srcv p = (E.getD p (0, 0, 0, 0)).1.val) &&
    (List.finRange 8).all fun j => decide (dlv p j = dl (E.getD p (0, 0, 0, 0)) j)

/-- Beyond F = 4, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 5) (i j : Fin 8) (hxy : farXY i j = true) (hc0 : farC s i j = true) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 4 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc
  have q := of_decide_eq_true hxy
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 5 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j)
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

/-- Descent rules beyond F = 4, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 4 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 945275040453573506975553099471616265742755483828649257319504339260279199146054393160385527450641722824514538617187946583008757398865337236750731170674818433240256461433565095952928182369977907101038377900409852022457193380725966333848769623048073987418717554911840564093066814454934162906357460671683745900391175092648571743150365009542267803360641703887467976018042447532113690639761318733569134837006739301616402084703670210170965808378610902454166315771443945269089063761163326728009055504340724210538099370786857231906076635535470460868019177428968623864945585383921044970091144880203283624163622468456642968295337239952846173568431508230112353283524905647832746217910160667548963909154376645831798624834986614752965175698749877602951026714346009837018336912373480011635755296
  | 1 => 945275049119577712600195644065618163595438584543360950943606509716182470489766598039270064294423079332515529494881164170228507440697966101862746910639257528891451367260449773461825757394781434846118347703973561700394551172895289388987532903487231474860582519382831840138019389417764730162975109629690129451109866634580565960320387921745346680664773448361541991819532311104115871170780923138823009052981474717175369594044325142595443663608468317128208771681517096984055774086686375015372868487288619172696677267556665545739647061426535502196714967802798472653197438470535478596011940653825500283354209893796589333977198943243537943014370050740960910304825215692146848925329461644850538313435054228796846683788008852591645460385645709116041301660715747126849330602398827208411056544
  | 2 => 945275057785581918224838188658886022339811526657128577341929563854066105971439152313267568510651074978778906902922511317096508964878104344266390138982791830369788216730195819161006861889538755524253501918043063441988156544961045898771526719750498631569545762529664623208482130399590132366224835804895767500906725178314813582007106332678425402989628688494363741799011556192524878049476663496574736665126548833250735033175713846872941602238190637539811950402856853490448993540122715848856470015459892797737111045467117991223423807377244821856538252418038128218826451538245146566932292846997965850139219341408481810182380715557783789388111905824009575563485923574519967387222553469899289215053498440581013096240615041601814707557033560292595742719775742006798653087895171775094736929
  | 3 => 945275064718385282724552224334527964086944102389464372575455098345833305127591776846461432670817852453367443629425211640756227996106518723380868021182954360513087870572503218112345708024981455765431150844630036593899843200518010682774750895175584453698375864311579469174351437986938426966273703524631485495318042220955334420236322812829802360924665916072211023412110453063515033067115708207652385042389096386686799812933015492463324731162391586110674606145263538297393525782183633356454519687470334200188834460542241459347371828156560613996890735874693497831411491798996677950308717601613186754643533485764252651541340355852327049873323190614276183432716188579497899980769675573558351805753866218939300454377284495598542544488354050113499408798673158427143754969002279461227465696
  | 4 => 945275071651188647224266260008701827617456360919912033359869743529095631431746959635573201358658556702190401531510163104654987528098638697312027089218382110600813651501684304403492584332605267883373775374483905971893506708802019604332750511257749419229500705484331116377514932142996934837478194856283715992593491845301040574055341390173133006495975647917456742400095777623865792477360661107627865193986935872519956821858216948680204372507644193807972299199300218358794011233967136005212148650356245309159287134124754571143641803720846276846732363852231126005943388570616351387589128058116421819534786617716613075316054868312072247723354318903765034211530003456356923191873208231002795111426686145715690655842085040432445131628654702949365934575647724305306459225542396842671738336
  | _ => 0

def rd (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 6 32 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 5) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 24 ∧ srcv (re s i c1 c2) = s.val ∧ dlv (re s i c1 c2) i ≤ -1 ∧
      dlv (re s i c1 c2) (nxt i) ≤ (c1.val : ℤ) - 1 ∧ dlv (re s i c1 c2) (prv i) ≤ (c2.val : ℤ) - 1)
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
theorem tables_ok : (∀ i j, nonadj i j → farXY i j = true) ∧ (∀ s i j, nonadj i j → farC s i j = true) ∧
    dlOK = true ∧ (∀ s i c1 c2, ruleOK s i c1 c2 = true) := by
  decide +kernel

theorem edge_at (p : ℕ) (hp : p < 24) :
    srcv p = (E.getD p (0, 0, 0, 0)).1.val ∧ ∀ j, dlv p j = dl (E.getD p (0, 0, 0, 0)) j := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.mem_finRange,
    forall_const] at h
  exact h p hp

theorem point_contra (x y : ℤ) (s : Fin 5) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
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
theorem far_step (s : Fin 5) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
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
theorem farkas_ub (x y : ℤ) (s : Fin 5) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 4) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 2 7 0 4 1 3 0 1 0 3 5 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 3 5 0 4 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 2 7 0 4 2 1 0 0 1 3 5 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 5 7 0 4 2 1 0 0 (-1) 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 4) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 1 7 0 4 1 3 0 1 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 3 5 0 4 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 1 3 0 4 2 1 0 0 1 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 5 7 0 4 2 1 0 0 (-1) 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 4) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 1 7 0 4 1 3 0 1 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 3 5 0 4 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 2 7 0 4 2 1 0 0 1 3 5 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 5 7 0 4 2 1 0 0 (-1) 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 4) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 2 7 0 4 1 3 0 1 0 3 5 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 3 5 0 4 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 2 7 0 4 2 1 0 0 1 3 5 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 5 7 0 4 2 1 0 0 (-1) 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 4) : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 1 7 0 4 1 3 0 1 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 3 5 0 4 3 1 0 (-1) 0 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 2 7 0 4 2 1 0 0 1 3 5 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 5 7 0 4 2 1 0 0 (-1) 3 7 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 3 7 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 4 lies in the cells |x| ≤ 2, |y| ≤ 2. -/
theorem near_box (x y : ℤ) (s : Fin 5) (hF : F (x, y, s) ≤ 4) :
    -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 :=
  cls (fun s => F (x, y, s) ≤ 4 → -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) v.2.2

/-- Every vertex of the box with F at most 4, other than v0, has a neighbor where F is one less. -/
def nearOK : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b => (List.finRange 5).all fun s =>
    decide (4 < F ((a : ℤ) - 2, (b : ℤ) - 2, s)) ||
      decide (((a : ℤ) - 2, (b : ℤ) - 2, s) = v0) ||
      E.any fun e => decide (e.1 = s ∧
        F ((a : ℤ) - 2 + e.2.2.1, (b : ℤ) - 2 + e.2.2.2, e.2.1) + 1 = F ((a : ℤ) - 2, (b : ℤ) - 2, s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 4) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
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

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. On the
line pot_i = n the points are (al i c + Bc i u, be i c - Ac i u) with c = n - Cc s i, and there
potential j is ka i j c + Dm i j u + Cc s j (`pot_par`). The previous facet bounds u from above, the
next one from below, and for n ≥ 3 the other facets lie below by Farkas certificates (`certT`,
checked once for every class by `certOK`). So each piece is the interval [lo, hi] of integers
(`piece_eq`), the sphere size is a sum of floor quotients (`cnt_eq_S`), and shifting n by 30 moves
every quotient by an integer (`inner_shift`). -/

/-- Bezout coefficients of the facet gradients: al i * Ac i + be i * Bc i = 1. -/
def al : Fin 8 → ℤ := ![0, (-1), 1, 0, 0, 1, (-1), 0]

def be : Fin 8 → ℤ := ![(-1), 0, 0, (-1), 1, 0, 0, 1]

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bc i - Bc j * Ac i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

theorem bez : ∀ i : Fin 8, al i * Ac i + be i * Bc i = 1 := by decide +kernel

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line of facet i at level n, in class s. -/
def par (s : Fin 5) (i : Fin 8) (n u : ℤ) : V :=
  (al i * (n - Cc s i) + Bc i * u, be i * (n - Cc s i) - Ac i * u, s)

theorem pot_par (s : Fin 5) (i j : Fin 8) (n u : ℤ) :
    pot (par s i n u) j = ka i j * (n - Cc s i) + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 8) (n : ℤ) (hv : pot v i = n) :
    v = par v.2.2 i n (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := bez i
  simp only [pot] at hv
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb + (al i) * hv
  · linear_combination (-y) * hb + (be i) * hv

theorem par_inj (s : Fin 5) (i : Fin 8) (n : ℤ) : Function.Injective (par s i n) := by
  intro u u' h
  simp only [par, Prod.mk.injEq] at h
  have hb := bez i
  have h1 : Bc i * (u - u') = 0 := by linarith [h.1]
  have h2 : Ac i * (u - u') = 0 := by linarith [h.2.1]
  have h3 : (u - u') = (u - u') * (al i * Ac i + be i * Bc i) := by rw [hb, mul_one]
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
    ![(0, 0, 0, 0), (0, 0, 0, 0), (1, 5, 3, 2), (3, 4, 2, 2), (0, 0, 1, 2), (5, 2, 2, 2), (7, 0, 4, 2), (0, 0, 0, 0)],
    ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (1, 2, 1, 0), (4, 5, 2, 0), (0, 0, 1, 2), (6, 3, 2, 0), (4, 1, 2, 0)],
    ![(2, 1, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 7, 5, 2), (3, 6, 2, 0), (0, 0, 1, 2), (5, 4, 2, 0)],
    ![(4, 3, 2, 2), (3, 2, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 7, 4, 2), (2, 5, 2, 2), (0, 0, 1, 2)],
    ![(0, 0, 1, 2), (5, 3, 1, 0), (3, 1, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (1, 5, 3, 2), (3, 4, 2, 2)],
    ![(4, 5, 2, 0), (0, 0, 1, 2), (6, 3, 2, 0), (4, 1, 2, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (1, 2, 1, 0)],
    ![(0, 7, 5, 2), (3, 6, 2, 0), (0, 0, 1, 2), (5, 4, 2, 0), (2, 1, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)],
    ![(0, 0, 0, 0), (1, 3, 1, 0), (3, 5, 1, 0), (0, 0, 1, 2), (4, 4, 1, 0), (3, 2, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0)]]

/-- The certificate of (i, j) is valid for class s. -/
def certV (s : Fin 5) (i j : Fin 8) : Prop :=
  let c := certT i j
  let h := i - 1
  let k := i + 1
  0 ≤ c.1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧ 0 ≤ c.2.2.2 ∧
    c.1 * (Ac h - Ac i) + c.2.1 * (Ac k - Ac i) + c.2.2.1 * (Ac i - Ac j) - c.2.2.2 * Ac i = 0 ∧
    c.1 * (Bc h - Bc i) + c.2.1 * (Bc k - Bc i) + c.2.2.1 * (Bc i - Bc j) - c.2.2.2 * Bc i = 0 ∧
    0 < c.1 * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
      c.2.1 * (Cc s k - Cc s i + (if k < i then 1 else 0)) + c.2.2.1 * (Cc s i - Cc s j) +
      c.2.2.2 * (3 - Cc s i)

instance (s : Fin 5) (i j : Fin 8) : Decidable (certV s i j) := by
  unfold certV; infer_instance

theorem certOK : ∀ s : Fin 5, ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certV s i j := by
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

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 5) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * (n - Cc s i) - Cc s j

def hi (s : Fin 5) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 5) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 5) (i j : Fin 8) (n u : ℤ) :
    pot (par s i n u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 5) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 5) (i : Fin 8) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 8) : ka i i = 1 := by
  rw [ka, mul_comm (Ac i), mul_comm (Bc i)]
  exact bez i

theorem Dm_self (i : Fin 8) : Dm i i = 0 := by
  rw [Dm]; ring

/-- From n = 3 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 5) (i : Fin 8) (n u : ℤ) (hn : 3 ≤ n) (h1 : lo s i n ≤ u)
    (h2 : u ≤ hi s i n) : ∀ j, pot (par s i n u) j ≤ n - (if j < i then 1 else 0) := by
  have hi' : pot (par s i n u) i = n := by
    rw [pot_par, ka_self, Dm_self]; ring
  have hh := (pot_le_iff s i (i - 1) n u).2 ((le_hi_iff s i n u).1 h2)
  have hk := (pot_le_iff s i (i + 1) n u).2 ((lo_le_iff s i n u).1 h1)
  intro j
  by_cases e1 : j = i - 1
  · rw [e1]; exact hh
  by_cases e2 : j = i
  · simp only [e2, hi', lt_irrefl, if_false, sub_zero, le_refl]
  by_cases e3 : j = i + 1
  · rw [e3]; exact hk
  obtain ⟨c1, c2, c3, c0, cx, cy, cc⟩ := certOK s i j e1 e2 e3
  by_contra hne
  have f3 : pot (par s i n u) i ≤ pot (par s i n u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i n u) (i - 1) i (i + 1) j _ _ 3 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(2 * n + 4)) (2 * n + 4) ×ˢ
    (Finset.Icc (-(2 * n + 4)) (2 * n + 4) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 5, ∀ j : Fin 8, -2 ≤ Cc s j ∧ Cc s j ≤ 2 := by decide +kernel

/-- Opposite facet pairs: their potentials add up to a multiple of x or of y plus constants. -/
theorem box_pairs : Ac 2 + Ac 5 = 2 ∧ Bc 2 + Bc 5 = 0 ∧
    Ac 0 + Ac 7 = -4 ∧ Bc 0 + Bc 7 = 0 ∧
    Ac 4 + Ac 7 = 0 ∧ Bc 4 + Bc 7 = 2 ∧
    Ac 0 + Ac 3 = 0 ∧ Bc 0 + Bc 3 = -2 := by
  decide +kernel

theorem pair_le (pa pb f t ca cb lam cm : ℤ) (h1 : pa ≤ f) (h2 : pb ≤ f)
    (e : pa + pb = lam * t + ca + cb) (k1 : -cm ≤ ca) (k2 : -cm ≤ cb) :
    lam * t ≤ 2 * f + 2 * cm := by
  linarith

/-- Each pair of opposite facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 5) :
    2 * x ≤ 2 * F (x, y, s) + 2 * 2 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 2 * 2 ∧
    2 * y ≤ 2 * F (x, y, s) + 2 * 2 ∧
    2 * (-y) ≤ 2 * F (x, y, s) + 2 * 2 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  refine ⟨pair_le _ _ _ _ _ _ _ _ (le_F _ 2) (le_F _ 5) ?_ (Cbound s 2).1 (Cbound s 5).1,
    pair_le _ _ _ _ _ _ _ _ (le_F _ 0) (le_F _ 7) ?_ (Cbound s 0).1 (Cbound s 7).1,
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
noncomputable def PF (s : Fin 5) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 5) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
    PF s i n = (Finset.Icc (lo s i n) (hi s i n)).image (par s i n) := by
  ext v
  simp only [PF, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨-, hs, hv⟩
    obtain ⟨h1, h2⟩ := (piece_iff v i n).1 hv
    refine ⟨be i * v.1 - al i * v.2.1, ⟨?_, ?_⟩, ?_⟩
    · rw [lo_le_iff, ← pot_le_iff, ← hs, ← par_inv v i n h1]
      exact h2 (i + 1)
    · rw [le_hi_iff, ← pot_le_iff, ← hs, ← par_inv v i n h1]
      exact h2 (i - 1)
    · rw [← hs]
      exact (par_inv v i n h1).symm
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    have hp := par_piece s i n u hn h1 h2
    have hi' : pot (par s i n u) i = n := by
      rw [pot_par, ka_self, Dm_self]; ring
    have hv := (piece_iff (par s i n u) i n).2 ⟨hi', hp⟩
    exact ⟨mem_Bx _ n (le_of_eq hv.1), rfl, hv⟩

/-- The length of the piece (s, i) at level n, as an integer. -/
def inner (s : Fin 5) (i : Fin 8) (n : ℤ) : ℤ := hi s i n + 1 - lo s i n

theorem card_piece (s : Fin 5) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
    (PF s i n).card = (inner s i n).toNat := by
  rw [piece_eq s i n hn, Finset.card_image_of_injective _ (par_inj s i n), Int.card_Icc]
  rfl

/-- The number of points with F = n. -/
noncomputable def cnt (n : ℤ) : ℕ := Set.ncard {v : V | F v = n}

theorem cnt_eq_card (n : ℤ) : cnt n = ((Bx n).filter (fun v => F v = n)).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Finset.coe_filter]
  exact ⟨fun h => ⟨mem_Bx v n (le_of_eq h), h⟩, fun h => h.2⟩

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 5 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 5 × Fin 8, inner p.1 p.2 n

/-- Shifting n by 30 moves each quotient of a piece length by an integer. -/
def mh : Fin 8 → ℤ := ![15, (-6), 10, (-12), 15, (-6), 10, (-12)]

def mk : Fin 8 → ℤ := ![(-12), 10, (-6), 15, (-12), 10, (-6), 15]

theorem shift_ok : ∀ i : Fin 8, 30 * (1 - ka i (i - 1)) = Dm i (i - 1) * mh i ∧
    30 * (1 - ka i (i + 1)) = (-Dm i (i + 1)) * mk i := by decide +kernel

theorem inner_shift (s : Fin 5) (i : Fin 8) (n : ℤ) :
    inner s i (n + 30) = inner s i n + (mh i + mk i) := by
  obtain ⟨e1, e2⟩ := shift_ok i
  have r1 : Rb s i (i - 1) (n + 30) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb]; ring
  have r2 : Rb s i (i + 1) (n + 30) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb]; ring
  simp only [inner, hi, lo, r1, r2]
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
    Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
  ring

theorem S_shift (n : ℤ) : S (n + 30) = S n + 140 := by
  simp only [S, inner_shift, Finset.sum_add_distrib]
  congr 1

theorem mhk_nonneg : ∀ i : Fin 8, 0 ≤ mh i + mk i := by decide +kernel

/-! The piece length in table form, for the kernel: inner s i n is
(uh i n + vh s i) / dh i + (uk i n + vk s i) / dk i + 1. -/

def uh : Fin 8 → ℤ := ![2, (-1), 2, (-2), 2, (-1), 2, (-2)]

def vh : Fin 5 → Fin 8 → ℤ := ![![(-2), 0, (-2), (-4), 1, (-2), 0, 2], ![0, (-4), 3, (-2), (-1), 2, (-5), 0], ![0, (-3), 1, 0, (-1), 1, (-3), (-2)], ![(-2), (-2), 0, (-3), 1, 0, (-2), 1], ![0, (-1), (-1), (-1), (-1), (-1), (-1), (-1)]]

def dh : Fin 8 → ℤ := ![4, 5, 6, 5, 4, 5, 6, 5]

def uk : Fin 8 → ℤ := ![(-2), 2, (-1), 2, (-2), 2, (-1), 2]

def vk : Fin 5 → Fin 8 → ℤ := ![![2, (-1), 1, 2, (-2), 1, (-1), (-3)], ![(-1), 4, (-3), 0, 1, (-4), 3, (-1)], ![1, 2, (-2), 0, (-1), (-2), 2, (-1)], ![3, 1, (-1), 2, (-3), (-1), 1, (-3)], ![0, 0, 0, 0, 0, 0, 0, (-1)]]

def dk : Fin 8 → ℤ := ![5, 6, 5, 4, 5, 6, 5, 4]

def innerT (s : Fin 5) (i : Fin 8) (n : ℤ) : ℤ :=
  (uh i * n + vh s i) / dh i + (uk i * n + vk s i) / dk i + 1

theorem tab_ok : ∀ s : Fin 5, ∀ i : Fin 8, uh i = 1 - ka i (i - 1) ∧
    vh s i = ka i (i - 1) * Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = 1 - ka i (i + 1) ∧
    vk s i = ka i (i + 1) * Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  decide +kernel

theorem inner_eq (s : Fin 5) (i : Fin 8) (n : ℤ) : inner s i n = innerT s i n := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tab_ok s i
  have r1 : Rb s i (i - 1) n = uh i * n + vh s i := by rw [e1, e2, Rb]; ring
  have r2 : Rb s i (i + 1) n = uk i * n + vk s i := by rw [e4, e5, Rb]; ring
  rw [inner, hi, lo, innerT, r1, r2, e3, e6]
  ring

/-- The closed form in table form. -/
def ST (n : ℤ) : ℤ := ∑ p : Fin 5 × Fin 8, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- Every piece length is nonnegative from n = 3 on: checked on one period, then shifted. -/
theorem inner_nonneg_base : ∀ r : ℕ, r < 30 → ∀ p : Fin 5 × Fin 8,
    0 ≤ innerT p.1 p.2 (3 + (r : ℤ)) := by
  decide +kernel

theorem inner_nonneg (s : Fin 5) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 3 + t := ⟨(n - 3).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 30
    · rw [inner_eq]
      exact inner_nonneg_base t ht (s, i)
    · have := ih (t - 30) (by omega) (by omega)
      have e : (3 : ℤ) + t = (3 + (t - 30 : ℕ)) + 30 := by push_cast [Nat.cast_sub (by omega : 30 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      linarith

theorem cnt_eq_S (n : ℤ) (hn : 3 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The closed form at n = 3, ..., 35, each value computed once by the kernel. -/
def Stbl : List ℤ := [14, 20, 22, 28, 34, 36, 42, 48, 50, 56, 62, 64, 70, 76, 78, 84, 90, 92, 98, 104, 106, 112, 118, 120, 126, 132, 134, 140, 146, 148, 154, 160, 162]

theorem ST_tbl : ∀ r : ℕ, r < 33 → ST (3 + (r : ℤ)) = Stbl.getD r 0 := by
  decide +kernel

theorem Stbl_step : ∀ r : ℕ, r < 30 → Stbl.getD (r + 3) 0 = Stbl.getD r 0 + 14 := by
  decide +kernel

/-- The step of the closed form on one period. -/
theorem S_step_base (t : ℕ) (ht : t < 30) : S (3 + t + 3) = S (3 + t) + 14 := by
  have e : (3 : ℤ) + t + 3 = 3 + ((t + 3 : ℕ) : ℤ) := by push_cast; ring
  rw [e, S_eq_ST, S_eq_ST, ST_tbl (t + 3) (by omega), ST_tbl t (by omega), Stbl_step t ht]

theorem S_step (n : ℤ) (hn : 3 ≤ n) : S (n + 3) = S n + 14 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 3 + t := ⟨(n - 3).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 30
    · exact S_step_base t ht
    · have h := ih (t - 30) (by omega) (by omega)
      have e : (3 : ℤ) + t = (3 + (t - 30 : ℕ)) + 30 := by push_cast [Nat.cast_sub (by omega : 30 ≤ t)]; ring
      have e2 : (3 : ℤ) + t + 3 = (3 + (t - 30 : ℕ) + 3) + 30 := by rw [e]; ring
      rw [e2, e, S_shift, S_shift, h]
      ring

/-! ## The small spheres

The points with F ≤ 2 lie in the box -2 ≤ x ≤ 4, -4 ≤ y ≤ 4 (`small_box`), and the kernel
checks that those of the box are the 15 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 5) (h : F (x, y, s) ≤ 2) :
    -2 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 2. -/
def smallL : List V :=
  [(0, 0, 4), (0, (-1), 1), (0, 0, 0), (0, 0, 2), (0, 0, 3), (1, 0, 0), (1, 0, 3), ((-1), (-1), 1), ((-1), 0, 2), ((-1), 0, 4), (0, (-1), 2), (0, 0, 1), (1, (-1), 1), (1, 0, 2), (1, 0, 4)]

def smallOK : Bool :=
  (List.range 7).all fun a => (List.range 9).all fun b => (List.finRange 5).all fun s =>
    decide (2 < F ((a : ℤ) - 2, (b : ℤ) - 4, s)) ||
      decide (((a : ℤ) - 2, (b : ℤ) - 4, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 2) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 2).toNat (by omega) (y + 4).toNat (by omega) s
  have ex : (((x + 2).toNat : ℕ) : ℤ) - 2 = x := by omega
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

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 3 are counted in
`smallL`, those from 3 on are S(n), and a(n + 3) = a(n) + 14 for n ≥ 1 (`a_step`). The
closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow. -/

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

theorem av0 : a 0 = 1 := by
  rw [a_eq_cnt, cnt_small _ (by norm_num)]
  decide +kernel

theorem av1 : a 1 = 6 := by
  rw [a_eq_cnt, cnt_small _ (by norm_num)]
  decide +kernel

theorem av2 : a 2 = 8 := by
  rw [a_eq_cnt, cnt_small _ (by norm_num)]
  decide +kernel

theorem av3 : a 3 = 14 := by
  have h := a_eq_S 3 (by norm_num)
  have e : S 3 = 14 := by
    rw [S_eq_ST]
    decide +kernel
  push_cast at h
  omega

theorem av4 : a 4 = 20 := by
  have h := a_eq_S 4 (by norm_num)
  have e : S 4 = 20 := by
    rw [S_eq_ST]
    decide +kernel
  push_cast at h
  omega

theorem av5 : a 5 = 22 := by
  have h := a_eq_S 5 (by norm_num)
  have e : S 5 = 22 := by
    rw [S_eq_ST]
    decide +kernel
  push_cast at h
  omega

/-- The step a(n + 3) = a(n) + 14 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 3) = a n + 14 := by
  rcases (show n < 3 ∨ 3 ≤ n by omega) with h | h
  · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5]
  · have h1 := a_eq_S n h
    have h2 := a_eq_S (n + 3) (by omega)
    have h3 := S_step n (by exact_mod_cast h)
    push_cast at h2
    omega

/-- The closed form per residue of n mod 3, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (3 * k + 1) = 14 * k + 6 ∧ a (3 * k + 2) = 14 * k + 8 ∧ a (3 * k + 3) = 14 * k + 14 := by
  induction k with
  | zero => norm_num [av1, av2, av3]
  | succ k ih =>
    have s1 : a (3 * (k + 1) + 1) = a (3 * k + 1) + 14 := by
      rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by ring]
      exact a_step _ (by omega)
    have s2 : a (3 * (k + 1) + 2) = a (3 * k + 2) + 14 := by
      rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 3 by ring]
      exact a_step _ (by omega)
    have s3 : a (3 * (k + 1) + 3) = a (3 * k + 3) + 14 := by
      rw [show 3 * (k + 1) + 3 = 3 * k + 3 + 3 by ring]
      exact a_step _ (by omega)
    omega

/-- The sequence in closed form. -/
def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => 14 * (n / 3) + [6, 8, 14].getD (n % 3) 0

theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases n with _ | n
  · exact av0
  · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ n = 3 * k + j :=
      ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
    have hb : b (3 * k + j + 1) = 14 * k + [6, 8, 14].getD j 0 := by
      show 14 * ((3 * k + j) / 3) + [6, 8, 14].getD ((3 * k + j) % 3) 0 = _
      rw [show (3 * k + j) / 3 = k by omega, show (3 * k + j) % 3 = j by omega]
    rw [hb]
    obtain ⟨h1, h2, h3⟩ := a_closed k
    interval_cases j
    · exact h1
    · exact h2
    · exact h3

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 6, 8, 14, 20, 22, 28, 34, 36, 42, 48, 50, 56, 62, 64, 70, 76, 78, 84, 90, 92, 98, 104, 106, 112, 118, 120, 126, 132, 134, 140, 146, 148, 154, 160, 162, 168, 174, 176, 182, 188, 190, 196, 202, 204, 210, 216, 218, 224, 230] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

theorem av6 : a 6 = 28 := (a_eq_b 6).trans (by decide)

theorem av7 : a 7 = 34 := (a_eq_b 7).trans (by decide)

theorem recur_aux (q : ℕ) : (a (q + 5) : ℤ) = a (q + 4) + a (q + 2) - a (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 3 ∨ 3 ≤ q by omega) with hq | hq
    · interval_cases q <;> norm_num [av1, av2, av3, av4, av5, av6, av7]
    · obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
      have h0 : (a (r + 5) : ℤ) = a (r + 4) + a (r + 2) - a (r + 1) := ih r (by omega)
      have s1 : a (r + 4) = a (r + 1) + 14 := a_step (r + 1) (by omega)
      have s2 : a (r + 5) = a (r + 2) + 14 := a_step (r + 2) (by omega)
      have s4 : a (r + 7) = a (r + 4) + 14 := a_step (r + 4) (by omega)
      have s5 : a (r + 8) = a (r + 5) + 14 := a_step (r + 5) (by omega)
      show (a (r + 8) : ℤ) = a (r + 7) + a (r + 5) - a (r + 4)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 5 := ⟨n - 5, by omega⟩
  rw [show q + 5 - 1 = q + 4 by omega, show q + 5 - 3 = q + 2 by omega, show q + 5 - 4 = q + 1 by omega]
  exact recur_aux q

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X + X ^ 2) * (X - 1) ^ 2) =
      (1 + X + X ^ 2) * (X - 1) ^ 2 + 2 * X * (3 + X + 3 * X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * ((1 + X + X ^ 2) * (X - 1) ^ 2) = C 1 * A - C 1 * (A * X ^ 1) - C 1 * (A * X ^ 3) + C 1 * (A * X ^ 4) := by
    simp only [map_one]
    ring
  have e2 : ((1 + X + X ^ 2) * (X - 1) ^ 2 + 2 * X * (3 + X + 3 * X ^ 2) : ℚ⟦X⟧) = C 1 + X ^ 1 * C 5 + X ^ 2 * C 2 + X ^ 3 * C 5 + X ^ 4 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (a k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num [av0, av1, av2, av3, av4]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 5 := ⟨n - 5, by omega⟩
    have h := recur (q + 5) (by omega)
    rw [show q + 5 - 1 = q + 4 by omega, show q + 5 - 3 = q + 2 by omega, show q + 5 - 4 = q + 1 by omega] at h
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 5 - 1 = q + 4 by omega, show q + 5 - 3 = q + 2 by omega, show q + 5 - 4 = q + 1 by omega, show 1 ≤ q + 5 by omega, show 3 ≤ q + 5 by omega, show 4 ≤ q + 5 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 5 = 1 by omega, show ¬ q + 5 = 2 by omega, show ¬ q + 5 = 3 by omega, show ¬ q + 5 = 4 by omega, if_true, if_false]
    linear_combination (1) * hq

/-! ## The third conjecture: a(n) = 2 A047342(n + 1) for n > 0

A047342 lists the numbers congruent to 0, 3 or 4 mod 7 from offset 1, so A047342(n + 1) is
Nat.nth of that predicate at n. Three of every seven consecutive numbers satisfy it, so it counts
3k below 7k, and Nat.nth_count inverts the count at 7k, 7k + 3 and 7k + 4. -/

/-- The numbers congruent to 0, 3 or 4 mod 7 (A047342). -/
abbrev P7 (m : ℕ) : Prop := m % 7 = 0 ∨ m % 7 = 3 ∨ m % 7 = 4

theorem count_P7_add (n : ℕ) : Nat.count P7 (n + 7) = Nat.count P7 n + 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 7 = n + 7 + 1 by ring, Nat.count_succ P7 (n + 7), Nat.count_succ P7 n, ih]
    have e : (n + 7) % 7 = n % 7 := by omega
    simp only [P7, e]
    omega

theorem count_P7 (k j : ℕ) : Nat.count P7 (7 * k + j) = 3 * k + Nat.count P7 j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 7 * (k + 1) + j = 7 * k + j + 7 by ring, count_P7_add, ih]
    ring

theorem nth_P7 (k : ℕ) :
    Nat.nth P7 (3 * k) = 7 * k ∧ Nat.nth P7 (3 * k + 1) = 7 * k + 3 ∧
      Nat.nth P7 (3 * k + 2) = 7 * k + 4 := by
  have d3 : Nat.count P7 3 = 1 := by decide
  have d4 : Nat.count P7 4 = 2 := by decide
  have c0 : Nat.count P7 (7 * k) = 3 * k := by simpa using count_P7 k 0
  have c3 : Nat.count P7 (7 * k + 3) = 3 * k + 1 := by rw [count_P7, d3]
  have c4 : Nat.count P7 (7 * k + 4) = 3 * k + 2 := by rw [count_P7, d4]
  refine ⟨?_, ?_, ?_⟩
  · have h := Nat.nth_count (p := P7) (n := 7 * k) (Or.inl (by omega))
    rwa [c0] at h
  · have h := Nat.nth_count (p := P7) (n := 7 * k + 3) (Or.inr (Or.inl (by omega)))
    rwa [c3] at h
  · have h := Nat.nth_count (p := P7) (n := 7 * k + 4) (Or.inr (Or.inr (by omega)))
    rwa [c4] at h

/-- The third conjunct of main, from the closed form per residue of n mod 3. -/
theorem conj3 : ∀ n : ℕ, 0 < n → a n = 2 * Nat.nth (fun m => m % 7 = 0 ∨ m % 7 = 3 ∨ m % 7 = 4) n := by
  intro n hn
  show a n = 2 * Nat.nth P7 n
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ n = 3 * k + j + 1 :=
    ⟨(n - 1) / 3, (n - 1) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨h1, h2, h3⟩ := a_closed k
  obtain ⟨-, n1, n2⟩ := nth_P7 k
  obtain ⟨n3, -, -⟩ := nth_P7 (k + 1)
  rw [show 3 * k + 3 = 3 * (k + 1) by ring] at h3
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · rw [show 3 * k + 0 + 1 = 3 * k + 1 by ring]
    omega
  · rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring]
    omega
  · rw [show 3 * k + 2 + 1 = 3 * (k + 1) by ring]
    omega

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X + X ^ 2) * (X - 1) ^ 2) =
      (1 + X + X ^ 2) * (X - 1) ^ 2 + 2 * X * (3 + X + 3 * X ^ 2) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4)) ∧
    ∀ n : ℕ, 0 < n → a n = 2 * Nat.nth (fun m => m % 7 = 0 ∨ m % 7 = 3 ∨ m % 7 = 4) n :=
  ⟨gf, recur, conj3⟩

end OMA.S_oeis_a315907

theorem OMA.solution : type_of% @OMA.S_oeis_a315907.main :=
  OMA.S_oeis_a315907.conjecture
