import OMAStatements.S_oeis_a284300

-- Problem: A284300: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellula
-- Credit: @sobrien032

/-!
Robert Price defined A284300 by reading Rule 865 from the origin to
the right edge and interpreting the bits as decimal digits. Chai Wah Wu
conjectured its recurrence and ordinary generating function in May 2024.

The mask records the first stages exactly. At later times it records
the alternating strip along the axes and the moving boundary, leaving
the other interior cells unrestricted. A finite local check and two
translations propagate the mask for all times. After eight steps the
axis retains its old digits and acquires eight digits at the front.

Source: https://oeis.org/A284300
Lean proof by Codex.
-/

namespace Rule865

private def earlyWords : Array ℕ := #[
  1,
  0,
  393217,
  17180131329,
  6755502520401920,
  295163667898307969025,
  116057469008088260134961152,
  5070718459267371661601999814657,
  1993872417794700101700344011433574401,
  87116938305805690440857787739703813079041,
  34254118858155034758693854192368354878801707008,
  1496611931007050899635341624816794951887919534833665,
  588487267306995713883285147580627244928185683175727562752,
  25712381846597285248759064512318846635404129097040803664232449,
  10110031424748999743405252480222632937865152197483325763266912845824,
  441721876303154053704870273663509524873723108487887893795331885551058945,
  173690784170382042544555262533204704917819112735090502831636079081710057291776,
  7588955639194862384044778073770715344341381853044005283380516668607229811182796801,
  2983954596312102198021553925434261110530071207130890513343584689249591036944542926503936,
  130373286462770056947950308226455496831921591357070290826307620752167621095597071739071496193,
  51264471096847234455943207995431968056784450018715368013970570593132579136215177828599805495345152,
  2239864359407384244073856905647831309066569780084658510865882494743108990906923933798009925393707302913,
  880707948251816293041691657687670278773605685688043061063240500857842718022364874613524208027540956924739585,
  38479402390833986738680278974071638864729707400906466284216418214084153219024430654371438584092764223351397023745,
  15130601254361976947864113271244834480859706338990569644219331281241634390829126946146260288121786060064042051801841664,
  661091273564987200701180465785691433842982332563420172058677404243084776829756090849300797067048636408104290211992262934529,
  259939106001330066265271435506839059254109001421542419951422863474648547382537108006359310844289447126222696714646357764420534272,
  11357115008208112640997658402834147075377359104358538375217043465534202050567963710415625479762640349502918766634069897158827895422977,
  4465765264329015122795045886379903854346188846130523170607039182564861313055217661835018407372411609114736567148668854652268886578016944128,
  195119704525055055350677967725537996691762668353749321818489602607463791177135367502368002946214742707834229000157172743319240020499858534432769,
  76720482610486127773845787539409666718056054523573806017308678641726026079151460567759456804224125057681801139944985810962536119244741836374513156096,
  3352028703553589102964301839150460263713619307924740337153362296084819263311442615436511413359469480048198273454971302379274462571305442461584118711058433,
  1318061262789430785721801375458611470891209009570996101043449093810672091785989827774644747664173976395767216073492116507675733506098961283558008963241743613952,
  57589172049784699161676620923826817799466290609604694856936234037941603307231174558665911413038244029258004010203351465422740531743849221439370053595096095543001089]

private def edgeWords : Array ℕ := #[
  828870282109249797707728960180416744252543882129788211300161358481451551535591464501248,
  953201446926803854043091606821095402065188491529290617091807578897899716033181441458176,
  984284267774004316093646134259244224677854969694377304607362229844941113754102528344064,
  992054975417281054152210749783700381903688305299093523267649164752560438513952557760512,
  992176390254125123777348718063435642269281585171854752256565423748539826568994541142016,
  984405566008631941353700736170682667000924052164761782438129575069722949066301611573248,
  953201476570144091117148724223162262911136146740006605030109248948546137887040233406464,
  993997523306771321668848692925481928266477906698401589825719998066121668098118671007744,
  955144145462256733780098685663958618658738623571041895236218597478224919420903845396480,
  993997641876174521034818116097426881363461567317721430344059931469035990798168393646080,
  960971774193667729905758349192552382783862025335814392615643945249211291294602147266560,
  861895542116681965801602568479025418618517462456230602612444247266457396520104470118400,
  955144115819029582648818265629890533376650337705643467670612329648585913058313955049472,
  984284267771705618723102183426534286551762127991016161909201967135411571135101523853312,
  953201565489309283290317424161088922259765171725366636345437810704934525691556106993664,
  867722266736109649454976086983497041550898111040275914817747366455384577052233013788672,
  331547045699463155552346712033595904152087731332440493859697381588292054523058088968192,
  455878210517017211887709358674274561964732340731942899651343602004740219020648065925120,
  486961031364217673938263886112423384577398818897029587166898252951781616741569152811008,
  494731739007494411996828501636879541803232154501745805827185187859400941501419182227456,
  494853153844338481621966469916614802168825434374507034816101446855380329556461165608960,
  487082329598845299198318488023861826900467901367414064997665598176563452053768236040192,
  455878240160357448961766476076341422810679995942658887589645272055386640874506857873408,
  496674286896984679513466444778661088166021755901053872385256021172962171085585295474688,
  457820909052470091624716437517137778558282472773694177795754620585065422408370469863424,
  496674405466387878879435867950606041263005416520373712903595954575876493785635018113024,
  463648537783881087750376101045731542683405874538466675175179968356051794282068771733504,
  364572305706895323646220320332204578518061311658882885171980270373297899507571094585344,
  457820879409242940493436017483069693276194186908295750230148352755426416045780579516416,
  486961031361918976567719935279713446451305977193668444468737990242252074122568148320256,
  455878329079522641134935176014268082159309020928018918904973833811775028679022731460608,
  370399030326323007299593838836676201450441960242928197377283389562225080039699638255616]

/-- Rows in a quadrant of the initial diamonds, packed with 17 bits per row. -/
def earlyBit (t u v : ℕ) : Bool :=
  (earlyWords[t]?.getD 0).testBit (17*u+v)

/-- Periodic advancing-edge rows, with d measuring distance behind the leading cell. -/
def edgeBit (t d v : ℕ) : Bool :=
  (edgeWords[t%32]?.getD 0).testBit (17*d+v)

def mask (t x y : ℕ) : Option Bool :=
  let u := max x y
  let v := min x y
  if t < u+v then some (decide (0<t))
  else if t < 34 then some (earlyBit t u v)
  else if u+17 ≤ t then
    if v ≤ 1 then some (decide ((t+u+v)%2=1)) else none
  else some (edgeBit t (t-u) v)

def axisKnown (t x : ℕ) : Option Bool := mask t x 0

def near (x : ℕ) : ℕ := if x=0 then 1 else x-1

def goodCell (m : Option Bool) (b : Bool) : Prop := m = none ∨ m = some b

def stepVal (c l r b u : Bool) : Bool :=
  (865 : ℕ).testBit (c.toNat + 2*(l.toNat+r.toNat+b.toNat+u.toNat))

def stepAt (t x y : ℕ) : Prop := ∀ c l r b u : Bool,
  goodCell (mask t x y) c → goodCell (mask t (near x) y) l →
  goodCell (mask t (x+1) y) r → goodCell (mask t x (near y)) b →
  goodCell (mask t x (y+1)) u → goodCell (mask (t+1) x y) (stepVal c l r b u)

end Rule865

namespace Rule865

private def label : Option Bool → Fin 3
  | none => 2
  | some false => 0
  | some true => 1

private def transfer (a b c d e : Fin 3) : ℕ :=
  (133194604813482335205614804808841018718278840213280852158643989980839837506704113896043449306105269626837197222097224389740876460900327054695866401 >>> (2*(a.val+3*(b.val+3*(c.val+3*(d.val+3*e.val)))))) % 4

private def asBool (i : Fin 2) : Bool := decide (i.val=1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem transfer_sound : ∀ a b c d e : Fin 3, ∀ p q r s t : Fin 2,
    (a.val=2 ∨ a.val=p.val) → (b.val=2 ∨ b.val=q.val) →
    (c.val=2 ∨ c.val=r.val) → (d.val=2 ∨ d.val=s.val) →
    (e.val=2 ∨ e.val=t.val) →
    transfer a b c d e = 2 ∨
      transfer a b c d e = (stepVal (asBool p) (asBool q) (asBool r) (asBool s) (asBool t)).toNat := by
  decide +kernel

private def ix (b : Bool) : Fin 2 := if b then 1 else 0
private theorem ix_val (b : Bool) : (ix b).val = b.toNat := by cases b <;> decide
private theorem ix_bool (b : Bool) : asBool (ix b) = b := by cases b <;> decide

private theorem label_ok {m : Option Bool} {b : Bool} (h : goodCell m b) :
    (label m).val=2 ∨ (label m).val=b.toNat := by
  rcases h with h | h <;> subst m <;> cases b <;> decide

private def checkCell (t x y : ℕ) : Bool :=
  match mask (t+1) x y with
  | none => true
  | some v => transfer (label (mask t x y)) (label (mask t (near x) y))
      (label (mask t (x+1) y)) (label (mask t x (near y))) (label (mask t x (y+1))) == v.toNat

private theorem checked_step {t x y : ℕ} (h : checkCell t x y = true) : stepAt t x y := by
  intro c l r b u hc hl hr hb hu
  cases he : mask (t+1) x y with
  | none => simp [goodCell]
  | some v =>
    have htar := h
    simp only [checkCell, he, beq_iff_eq] at htar
    have hsound := transfer_sound (label (mask t x y)) (label (mask t (near x) y))
      (label (mask t (x+1) y)) (label (mask t x (near y))) (label (mask t x (y+1)))
      (ix c) (ix l) (ix r) (ix b) (ix u)
    simp only [ix_val, ix_bool] at hsound
    have hout := hsound (label_ok hc) (label_ok hl) (label_ok hr) (label_ok hb) (label_ok hu)
    rw [htar] at hout
    have hEq : v=stepVal c l r b u := by
      cases v <;> cases hs : stepVal c l r b u <;> simp_all
    simp [goodCell, hEq]

private def checkRow (t : ℕ) : Bool :=
  (List.range (t+2)).all fun x =>
    let bound := if 34 ≤ t+1 ∧ x+17 ≤ t+1 then 1 else 17
    (List.range (min bound (min x (t+1-x))+1)).all fun y => checkCell t x y

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private theorem checked_row (t : ℕ) (ht : t < 100) : checkRow t = true := by
  let j : Fin 5 := ⟨t%5, by omega⟩
  have he : t = 5*(t/5)+j.val := by dsimp [j]; omega
  generalize hq : t/5 = q at he
  have hq' : q < 20 := by omega
  rw [he]
  interval_cases q
  · have chk : ∀ z : Fin 5, checkRow (0+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (5+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (10+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (15+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (20+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (25+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (30+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (35+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (40+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (45+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (50+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (55+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (60+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (65+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (70+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (75+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (80+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (85+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (90+z.val) = true := by decide +kernel
    exact chk j
  · have chk : ∀ z : Fin 5, checkRow (95+z.val) = true := by decide +kernel
    exact chk j

theorem finite_step (t x y : ℕ) (ht : t < 100) (hyx : y ≤ x) (hin : x+y ≤ t+1)
    (hy : y ≤ 17) : stepAt t x y := by
  by_cases hs : 34 ≤ t+1 ∧ x+17 ≤ t+1 ∧ 1 < y
  · intro c l r b u _ _ _ _ _
    apply Or.inl
    simp [mask, max_eq_left hyx, min_eq_right hyx, show ¬t+1 < x+y by omega,
      show ¬t+1 < 34 by omega, hs.2.1, show ¬y ≤ 1 by omega]
  · have hr := checked_row t ht
    simp only [checkRow, List.all_eq_true, List.mem_range] at hr
    exact checked_step (hr x (by omega) y (by split <;> omega))

end Rule865

namespace Rule865

open OMA.S_oeis_a284300

private theorem mask_swap (t x y : ℕ) : mask t x y = mask t y x := by
  simp only [mask, max_comm x y, min_comm x y]

private theorem mask_out (t x y : ℕ) (h : t < x+y) :
    mask t x y = some (decide (0<t)) := by
  have hs : max x y + min x y = x+y := by omega
  simp [mask, hs, h]

private theorem deep_time (t x y : ℕ) (ht : 100 ≤ t)
    (hxy : x+y ≤ t-32) (hx : max x y + 17 ≤ t-32) :
    mask t x y = mask (t-32) x y := by
  have hs : max x y + min x y = x+y := by omega
  have hp : (t + max x y + min x y)%2 = ((t-32) + max x y + min x y)%2 := by omega
  simp [mask, hs, show ¬ t < x+y by omega, show ¬ t-32 < x+y by omega,
    show ¬ t < 34 by omega, show ¬ t-32 < 34 by omega, hx,
    show max x y+17 ≤ t by omega, hp]

private theorem slide_time (t x y : ℕ) (ht : 100 ≤ t) (hx : y+32 ≤ x) :
    mask t x y = mask (t-32) (x-32) y := by
  have hy : y ≤ x-32 := by omega
  have hd : t-x = (t-32)-(x-32) := by omega
  have hp : (t+x+y)%2 = ((t-32)+(x-32)+y)%2 := by omega
  have hh : t%32 = (t-32)%32 := by omega
  have he : t < x+y ↔ t-32 < x-32+y := by omega
  have hc : x+17 ≤ t ↔ x-32+17 ≤ t-32 := by omega
  simp only [mask, max_eq_left (show y ≤ x by omega), min_eq_right (show y ≤ x by omega),
    max_eq_left hy, min_eq_right hy, he, hc, if_neg (show ¬ t < 34 by omega),
    if_neg (show ¬ t-32 < 34 by omega), decide_eq_true (show 0 < t by omega),
    decide_eq_true (show 0 < t-32 by omega), edgeBit, hp, hd, hh]

private theorem near_bounds (x : ℕ) : near x ≤ x+1 ∧ x ≤ near x+1 := by
  unfold near
  split <;> omega

private theorem outside_step (t x y : ℕ) (h : t+1 < x+y) : stepAt t x y := by
  have hx := near_bounds x
  have hy := near_bounds y
  intro c l r b u hc hl hr hb hu
  rw [mask_out t x y (by omega)] at hc
  rw [mask_out t (near x) y (by omega)] at hl
  rw [mask_out t (x+1) y (by omega)] at hr
  rw [mask_out t x (near y) (by omega)] at hb
  rw [mask_out t x (y+1) (by omega)] at hu
  rw [mask_out (t+1) x y h]
  simp only [goodCell, Option.some.injEq, reduceCtorEq, false_or] at *
  subst_vars
  by_cases ht : 0 < t
  · simp [ht, stepVal]
    decide
  · simp [ht, stepVal]

private theorem free_step (t x y : ℕ) (hab : y ≤ x) (hi : x+y ≤ t+1)
    (hy : 17 < y) : stepAt t x y := by
  intro c l r b u hc hl hr hb hu
  apply Or.inl
  simp [mask, max_eq_left hab, min_eq_right hab, show ¬ t+1 < x+y by omega,
    show ¬ t+1 < 34 by omega, show x+17 ≤ t+1 by omega, show ¬ y ≤ 1 by omega]

private theorem ordered_step
    (finiteStep : ∀ t x y : ℕ, t < 100 → y ≤ x → x+y ≤ t+1 → y ≤ 17 → stepAt t x y)
    (t : ℕ) : ∀ x y, y ≤ x → stepAt t x y := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro x y hyx
    by_cases hin : x+y ≤ t+1
    · by_cases hy : y ≤ 17
      · by_cases ht : t < 100
        · exact finiteStep t x y ht hyx hin hy
        have hxN := near_bounds x
        have hyN := near_bounds y
        have hpred : t-32+1 = (t+1)-32 := by omega
        by_cases hfar : x+50 ≤ t
        · have h := ih (t-32) (by omega) x y hyx
          unfold stepAt at *
          rw [deep_time t x y (by omega) (by omega) (by omega),
            deep_time t (near x) y (by omega) (by omega) (by omega),
            deep_time t (x+1) y (by omega) (by omega) (by omega),
            deep_time t x (near y) (by omega) (by omega) (by omega),
            deep_time t x (y+1) (by omega) (by omega) (by omega),
            deep_time (t+1) x y (by omega) (by omega) (by omega), ← hpred]
          exact h
        · have h := ih (t-32) (by omega) (x-32) y (by omega)
          have hm : near x - 32 = near (x-32) := by
            simp [near, show x ≠ 0 by omega, show x-32 ≠ 0 by omega]
            omega
          have hp : x+1-32 = (x-32)+1 := by omega
          unfold stepAt at *
          rw [slide_time t x y (by omega) (by omega),
            slide_time t (near x) y (by omega) (by omega),
            slide_time t (x+1) y (by omega) (by omega),
            slide_time t x (near y) (by omega) (by omega),
            slide_time t x (y+1) (by omega) (by omega),
            slide_time (t+1) x y (by omega) (by omega), ← hpred, hm, hp]
          exact h
      · exact free_step t x y hyx hin (by omega)
    · exact outside_step t x y (by omega)

private theorem swap_step (t x y : ℕ) (h : stepAt t y x) : stepAt t x y := by
  intro c l r b u hc hl hr hb hu
  have hh := h c b u l r ((mask_swap t x y) ▸ hc)
    ((mask_swap t x (near y)) ▸ hb) ((mask_swap t x (y+1)) ▸ hu)
    ((mask_swap t (near x) y) ▸ hl) ((mask_swap t (x+1) y) ▸ hr)
  rw [mask_swap (t+1) x y]
  simpa only [stepVal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

private theorem abs_near (z : ℤ) :
    ((z+1).natAbs = near z.natAbs ∧ (z-1).natAbs = z.natAbs+1) ∨
    ((z-1).natAbs = near z.natAbs ∧ (z+1).natAbs = z.natAbs+1) := by
  unfold near
  split <;> omega

theorem all_correct
    (finiteStep : ∀ t x y : ℕ, t < 100 → y ≤ x → x+y ≤ t+1 → y ≤ 17 → stepAt t x y)
    (t : ℕ) : ∀ i j : ℤ, goodCell (mask t i.natAbs j.natAbs) (cell 865 t i j) := by
  induction t with
  | zero =>
    intro i j
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl,rfl⟩ := h
      exact Or.inr rfl
    · have he := mask_out 0 i.natAbs j.natAbs (by omega)
      simp [he, cell, h, goodCell]
  | succ t ih =>
    intro i j
    have hs : stepAt t i.natAbs j.natAbs := by
      by_cases h : j.natAbs ≤ i.natAbs
      · exact ordered_step finiteStep t _ _ h
      · exact swap_step t _ _ (ordered_step finiteStep t _ _ (by omega))
    have hl := ih (i-1) j
    have hr := ih (i+1) j
    have hb := ih i (j-1)
    have hu := ih i (j+1)
    rcases abs_near i with ⟨hR,hL⟩ | ⟨hL,hR⟩ <;>
      rcases abs_near j with ⟨hU,hB⟩ | ⟨hB,hU⟩ <;>
      rw [hL] at hl <;> rw [hR] at hr <;> rw [hB] at hb <;> rw [hU] at hu
    all_goals
      first
      | have hh := hs _ _ _ _ _ (ih i j) hl hr hb hu
      | have hh := hs _ _ _ _ _ (ih i j) hl hr hu hb
      | have hh := hs _ _ _ _ _ (ih i j) hr hl hb hu
      | have hh := hs _ _ _ _ _ (ih i j) hr hl hu hb
      simpa only [cell, stepVal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

end Rule865

namespace Rule865

open OMA.S_oeis_a284300

theorem axis_correct {t k : ℕ} {b : Bool} (h : axisKnown t k = some b) :
    cell 865 t k 0 = b := by
  have hh := all_correct finite_step t (k : ℤ) 0
  change mask t k 0 = some b at h
  simp only [Int.natAbs_natCast, Int.natAbs_zero, h, goodCell, reduceCtorEq, false_or,
    Option.some.injEq] at hh
  exact hh.symm

end Rule865

namespace Rule865

open OMA.S_oeis_a284300

private def axisBit (t k : ℕ) : Bool :=
  if t < k then decide (0 < t)
  else if t < 34 then earlyBit t k 0
  else if k + 17 ≤ t then decide ((t + k) % 2 = 1)
  else edgeBit t (t-k) 0

private theorem axisKnown_bit (t k : ℕ) : axisKnown t k = some (axisBit t k) := by
  simp only [axisKnown, mask, axisBit, Nat.max_zero, Nat.min_zero,
    Nat.add_zero, Nat.zero_le, if_true]
  split_ifs <;> rfl

private theorem first_eight_shifts :
    ∀ t : Fin 7, ∀ k : Fin 34, k.val ≤ t.val + 27 →
      axisBit (t.val + 27 + 8) (k.val + 8) = axisBit (t.val + 27) k.val := by
  decide

private theorem edge_axis_period :
    ∀ r : Fin 32, ∀ d : Fin 17, edgeBit (r.val+8) d.val 0 = edgeBit r.val d.val 0 := by
  decide

private theorem axis_shift (t k : ℕ) (ht : 27 ≤ t) (hk : k ≤ t) :
    axisBit (t+8) (k+8) = axisBit t k := by
  by_cases h : t < 34
  · have H := first_eight_shifts ⟨t-27, by omega⟩ ⟨k, by omega⟩
    simp only at H
    simpa only [show t-27+27=t by omega] using H (by omega)
  · have h₁ : ¬ (t+8 < k+8) := by omega
    have h₂ : ¬ (t+8 < 34) := by omega
    simp only [axisBit, Nat.not_lt.mpr hk, h, h₁, h₂, if_false]
    by_cases h₃ : k + 17 ≤ t
    · simp only [h₃, show k+8+17 ≤ t+8 by omega, if_true]
      rw [show (t+8+(k+8))%2 = (t+k)%2 by omega]
    · simp only [h₃, show ¬ (k+8+17 ≤ t+8) by omega, if_false,
        show t+8-(k+8)=t-k by omega]
      have H := edge_axis_period ⟨t%32, Nat.mod_lt _ (by decide)⟩ ⟨t-k, by omega⟩
      simpa only [edgeBit, Nat.mod_add_mod, Nat.mod_mod] using H

private theorem axis_prefix (t k : ℕ) (ht : 27 ≤ t) (hk : k < 8) :
    axisBit (t+2+8) k = axisBit (t+8) k := by
  simp only [axisBit, show ¬ (t+2+8 < k) by omega, show ¬ (t+8 < k) by omega,
    show ¬ (t+2+8 < 34) by omega, show ¬ (t+8 < 34) by omega,
    show k+17 ≤ t+2+8 by omega, show k+17 ≤ t+8 by omega, if_false, if_true]
  rw [show (t+2+8+k)%2 = (t+8+k)%2 by omega]

/-- The eight new leading digits, read as one decimal number. -/
private def axisPrefix (t : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 8, if axisBit (t+8) k then (10 : ℤ)^(7-k) else 0

private theorem axisPrefix_period (t : ℕ) (ht : 27 ≤ t) : axisPrefix (t+2) = axisPrefix t := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [axis_prefix t k ht (Finset.mem_range.mp hk)]

private theorem axis_extend
    (hcorrect : ∀ {t k : ℕ} {b : Bool}, axisKnown t k = some b → cell 865 t k 0 = b)
    (t : ℕ) (ht : 27 ≤ t) : a (t+8) = axisPrefix t * 10^(t+1) + a t := by
  have hb (s k : ℕ) : cell 865 s k 0 = axisBit s k := hcorrect (axisKnown_bit s k)
  unfold a
  rw [show t+8+1=8+(t+1) by omega, Finset.sum_range_add]
  congr 1
  · rw [axisPrefix, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hb, show t+8-k=(7-k)+(t+1) by omega, pow_add]
    split <;> simp_all
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ t := by simpa using hk
    have hval : cell 865 (t+8) (↑(8+k) : ℤ) 0 = cell 865 t (↑k : ℤ) 0 := by
      rw [hb, hb, Nat.add_comm 8 k, axis_shift t k ht hk']
    rw [hval, show t+8-(8+k)=t-k by omega]

theorem recurrence
    (hcorrect : ∀ {t k : ℕ} {b : Bool}, axisKnown t k = some b → cell 865 t k 0 = b) :
    ∀ n : ℕ, 37 ≤ n → (a n : ℚ) = 100 * a (n-2) + a (n-8) - 100 * a (n-10) := by
  intro n hn
  let t := n-10
  have ht : 27 ≤ t := by dsimp [t]; omega
  have h₀ := axis_extend hcorrect t ht
  have h₂ := axis_extend hcorrect (t+2) (by omega)
  rw [axisPrefix_period t ht, show t+2+1=(t+1)+2 by omega, pow_add] at h₂
  have H : a (t+2+8) = 100*a (t+8) + a (t+2) - 100*a t := by
    rw [h₀, h₂]
    ring
  rw [show n=t+2+8 by dsimp [t]; omega, show t+2+8-2=t+8 by omega,
    show t+2+8-8=t+2 by omega, show t+2+8-10=t by omega]
  exact_mod_cast H

end Rule865

namespace Rule865

open OMA.S_oeis_a284300 PowerSeries

def earlyValue (t : ℕ) : ℤ :=
  ([1,
    0,
    110,
    1010,
    1010,
    101110,
    101010,
    11101110,
    110101010,
    1011101110,
    1010101010,
    101011101110,
    101010101010,
    10101011101110,
    10101010101010,
    1010101111101110,
    1010101110101010,
    101011101011101110,
    101010101010101010,
    10111110101011101110,
    10111010101010101010,
    1110101010101011101110,
    11011101010101010101010,
    101010101010101111101110,
    111110101010101110101010,
    10111010101011101011101110,
    10101110101010101010101010,
    1010101010101110101011101110,
    1010101010101010101010101010,
    101010101010101010101011101110,
    101010101010101010101010101010,
    10101010101010101010101111101110,
    10101010101010101010101110101010,
    1010101010101010101011101011101110,
    1010101010101010101010101010101010,
    101010101010101010101110101011101110,
    101010101010101010101010101010101010] : List ℤ)[t]?.getD 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
theorem formula
    (hrec : ∀ n : ℕ, 37 ≤ n → (a n : ℚ) = 100*a (n-2)+a (n-8)-100*a (n-10))
    (hearly : ∀ n : ℕ, n ≤ 36 → a n = earlyValue n) :
    type_of% @OMA.S_oeis_a284300.main := by
  refine ⟨hrec, ?_⟩
  let F : PowerSeries ℚ := mk (fun n => (a n : ℚ))
  have hden : F * (100*X^10-X^8-100*X^2+1) =
      C (100:ℚ)*(F*X^10) - F*X^8 - C (100:ℚ)*(F*X^2) + F := by
    simp only [map_ofNat]
    ring
  have hnum : (10000000000000000000000 * X ^ 36
        + 1000000000000000000000000 * X ^ 35
        + 1009900000000000000000000 * X ^ 34
        - 10000000000000000000000 * X ^ 33
        + 990000000000000000000000 * X ^ 32
        + 10000000000000000000000 * X ^ 31
        - 10000000000000000000000 * X ^ 30
        - 99000000000000000000 * X ^ 29
        - 10000010000000000000000 * X ^ 28
        - 1000000010000000000000000 * X ^ 27
        - 1009900000000000000000000 * X ^ 26
        + 10000000000000000000000 * X ^ 25
        - 990000000000000000000000 * X ^ 24
        - 10000000000000000000000 * X ^ 23
        + 10000000000000000000000 * X ^ 22
        + 98990000000000000000 * X ^ 21
        + 10000000000000000 * X ^ 20
        + 10000000000000000 * X ^ 19
        + 990000000000 * X ^ 17
        - 99010000 * X ^ 13
        + 10000 * X ^ 12
        - 99010900 * X ^ 11
        - 10000000000 * X ^ 10
        - 99009890 * X ^ 9
        + 100000009 * X ^ 8
        + 990110 * X ^ 7
        + 10 * X ^ 6
        + 110 * X ^ 5
        - 9990 * X ^ 4
        + 1010 * X ^ 3
        + 10 * X ^ 2
        + 1 : PowerSeries ℚ) =
      C (10000000000000000000000 : ℚ) * X ^ 36
        + C (1000000000000000000000000 : ℚ) * X ^ 35
        + C (1009900000000000000000000 : ℚ) * X ^ 34
        - C (10000000000000000000000 : ℚ) * X ^ 33
        + C (990000000000000000000000 : ℚ) * X ^ 32
        + C (10000000000000000000000 : ℚ) * X ^ 31
        - C (10000000000000000000000 : ℚ) * X ^ 30
        - C (99000000000000000000 : ℚ) * X ^ 29
        - C (10000010000000000000000 : ℚ) * X ^ 28
        - C (1000000010000000000000000 : ℚ) * X ^ 27
        - C (1009900000000000000000000 : ℚ) * X ^ 26
        + C (10000000000000000000000 : ℚ) * X ^ 25
        - C (990000000000000000000000 : ℚ) * X ^ 24
        - C (10000000000000000000000 : ℚ) * X ^ 23
        + C (10000000000000000000000 : ℚ) * X ^ 22
        + C (98990000000000000000 : ℚ) * X ^ 21
        + C (10000000000000000 : ℚ) * X ^ 20
        + C (10000000000000000 : ℚ) * X ^ 19
        + C (990000000000 : ℚ) * X ^ 17
        - C (99010000 : ℚ) * X ^ 13
        + C (10000 : ℚ) * X ^ 12
        - C (99010900 : ℚ) * X ^ 11
        - C (10000000000 : ℚ) * X ^ 10
        - C (99009890 : ℚ) * X ^ 9
        + C (100000009 : ℚ) * X ^ 8
        + C (990110 : ℚ) * X ^ 7
        + C (10 : ℚ) * X ^ 6
        + C (110 : ℚ) * X ^ 5
        - C (9990 : ℚ) * X ^ 4
        + C (1010 : ℚ) * X ^ 3
        + C (10 : ℚ) * X ^ 2
        + 1 := by simp only [map_ofNat]
  change F * _ = _
  rw [hden, hnum]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one, F, coeff_mk]
  by_cases hn : n ≤ 36
  · simp (disch := omega) only [hearly]
    lift n to Fin 37 using (by omega)
    clear hn
    revert n
    decide +kernel
  · simp (disch := omega) only [if_neg, if_pos, add_zero, sub_zero]
    linarith [hrec n (by omega)]

end Rule865

namespace Rule865

open OMA.S_oeis_a284300

private def numberOnAxis (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n+1), if (axisKnown n k).getD false then (10:ℤ)^(n-k) else 0

private theorem earlyKnown (n k : ℕ) : (axisKnown n k).isSome = true := by
  simp only [axisKnown, mask, max_eq_left (Nat.zero_le _), min_eq_right (Nat.zero_le _),
    Nat.add_zero, show (0:ℕ) ≤ 1 by decide, ↓reduceIte]
  repeat' first | rfl | split

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
private theorem checkEarly : ∀ n : Fin 37, numberOnAxis n = earlyValue n := by
  decide +kernel

theorem early (hc : ∀ {n k : ℕ} {b : Bool}, axisKnown n k = some b →
      cell 865 n k 0 = b) (n : ℕ) (hn : n ≤ 36) : a n = earlyValue n := by
  calc
    a n = numberOnAxis n := by
      unfold a numberOnAxis
      apply Finset.sum_congr rfl
      intro k _
      cases hk : axisKnown n k with
      | none => have h := earlyKnown n k; simp [hk] at h
      | some b => rw [hc hk]; rfl
    _ = earlyValue n := checkEarly ⟨n, by omega⟩

end Rule865

theorem OMA.solution : type_of% @OMA.S_oeis_a284300.main :=
  Rule865.formula (Rule865.recurrence @Rule865.axis_correct) (Rule865.early @Rule865.axis_correct)
