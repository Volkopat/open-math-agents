import OMAStatements.S_oeis_a272743

open OMA.S_oeis_a272743

namespace CA

abbrev S := Fin 172

def trans (i : ℕ) : S :=
  ⟨(((18433723865539939405765259438098229581372583076958979523935139023588612560487345533300911498025606653943546566132579500659887452767384463582502558692008904655207015036155204049748577416566034580856877446788520072135373965596123268323498829519154952348529514895540113597906411477730020422701831433920201645986586033061049472065221298264705486776454593800591932934416409969625857471629286364328396140406834739591119838978905819348940172466846067284921041520920331426987256328414754236960345800525627989607273979224817681720354635523056631848062349108027118667671600645290964988079499010018756157364372740427785930463002160130181526339771863359409361863393684215571402798012335963211750288538675435794042683888344695323932435862477934279933274951038907511551137529701370180077540659508475198073067784420463875682802345760463135781079591341015985534209570770416449186500910000542882223745546113597809767526015338341812294235389403446897626791054793101158447648875231914790984237421523926271615290789548470222732497522604948043812303572943388005256885804358823694761925349520101859824836479006237307768632806684432591406751640327129485209169964348478481572329029673311587441921096850351680465834503493500821073306271572281712750319346313170849462383210416192062258534405206076814646160720920178731894538794560143298362116613835259314207070298021405591127420890010142008422426873795601079039722585921710824079264665978148674280991239415116424728585956755841930331496443614607357792454132536926108140223065501523935457204651913414361235952182133779894239297356300714387553905825370862271162033281581460465820340896845929939725731235772460044765669308733392651988289623114180744143117470997171047392545774653203001357672056094047450813051516643454815514427800844222506883941047949892206272776294121009492923009100435185091107245856674358901359259213095126765969041425838578302725883503520252686113067956933775375541780560452819373743869653948632172354360206340212548482458749376421686730955941797814219899615030359431493613402938014761169961785810724201865272885669496471853802601292342158303568703308904533340501926881813268446559065035317688268215563714070678639879834571053316771248694752785150491997914932863212933628016072806155485810852822004251028860943393168721446421607706572935043003020861369851545473012085903415659682832729336525998269231647407215142217488038184646717354283236172769714569787903976512701041372007849587309944495250801048816060642416100027418191312611781887638227874563915176981407989331538075933156617925671214190270490748139785107525109406873307452415957692063831520205219542546225418619177175687143624389379868442841368176779420818989201210520823850695832852404384635680251800750755933113248391963270908357086417225239967273571129889852936157815161154925259228985299216573152887969073991236241559393393005344344836924188123360608864352553520322519477071367371469999127590040071010061391913727375069121419240984533666405338543172929411200235455147282812363182011669366745815188008530109161696138465666735569940915001315810363096786453075877969729088448554420042342035550671453428899215255446629600888413700508541286294436119862014414907418618795081601296060375056555365868255379215184986885907011847597569908064863662893565410169959902568665972515251666627693411101885927907405876062737924096 : ℕ) >>> (8 * i)) % 256) % 172, Nat.mod_lt _ (by decide)⟩

def step (s : S) (t x y : Bool) : S := (trans (s.val * 8 + t.toNat * 4 + x.toNat * 2 + y.toNat))

def fields (i : ℕ) : ℕ :=
  ((16160356189886615287729845728507338767092274314960582592998680024046413868034418416966568243189810938563861713266605000378328596959706075316394731293516454247975422063166774879535364670252542503465700222302636881984729764681528252811808575817787749843659522241073544370075771563858871347137556824934013634486272 : ℕ) >>> (6 * i)) % 64

def bit (s : S) (i : ℕ) : Bool := (fields (s.val)).testBit i

def oddB (i : ℤ) : Bool := decide (i % 2 = 1)

def facesX (i : ℕ) : ℕ :=
  ((630836069730628670041096261063991293681405196570853773636301110534911757806570384047157945348696773942417294380048011025072591493817076418768001611039934792381111880209993217377898244561909340673261215936872166930714437481099755844454105388201253495623973013820158602572996420538764296602253831565218628039970429466356095061635566882998629388436868945185408139505848187738970865324751500851100186967505371270317651220578349396058830235726095502585508325455271484110839070718960055386182046998800637376754548476955394681968016328936242664102435287593240725215171542493369470485818244977617579116836015575156071824470835200 : ℕ) >>> (6 * i)) % 64

def faceX (b : Bool) (s : S) := (facesX (b.toNat * 172 + s.val))

def edgesX (i : ℕ) : ℕ :=
  ((72978254272151944033059869802942937886312840353037055788436594718278920453772315267223006002942670401279880005642947523852827508637688732386413411687975290481278700593040462369976528822617103953576246357703248617141488090454910228086414712339519275266590406432904094044198511114970845138263212032 : ℕ) >>> (6 * i)) % 64

def edgeX (i : ℕ) (h j : Bool) := (edgesX (i*4 + h.toNat*2 + j.toNat))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma innerX : ∀ (s : S) (t y : Bool), faceX true (step s t false y) = faceX false (step s t true y) := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma outerX : ∀ (s : S) (t y b : Bool), faceX b (step s t b y) = edgeX (faceX b s) t y := by decide

def obsX (i : ℕ) : ℕ :=
  ((4586426483039467940149648 : ℕ) >>> (2 * i)) % 4

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsXtrue0 : ∀ s : S, ((obsX (faceX true s))).testBit 0 = bit s 1 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsXfalse0 : ∀ s : S, ((obsX (faceX false s))).testBit 0 = bit s 0 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsXtrue1 : ∀ s : S, ((obsX (faceX true s))).testBit 1 = bit s 0 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsXfalse1 : ∀ s : S, ((obsX (faceX false s))).testBit 1 = bit s 2 := by decide

def facesY (i : ℕ) : ℕ :=
  ((2078914540861058935173681194193199110085609395339957855670721569361097654775767897070007844723696786391303464234425458872674898529945441233162374389474609937090942803446737746354856697363983494181370600817643406217689715765448594760521484504144010683767606332291940602282917907572184061529858113453812218413981699148330049558219640102147682806698048596613036501779103979889088033994407310194963527237055230926877709230934478766910051663510903301323651134064637212199175264849417228188783355419404214736781668757216652066454503559278383526955201584351922631373031368932005575156496559110817381026516744447397275688243200 : ℕ) >>> (6 * i)) % 64

def faceY (b : Bool) (s : S) := (facesY (b.toNat * 172 + s.val))

def edgesY (i : ℕ) : ℕ :=
  ((72977006567454379824779295849590090947280872125178421295910703067174334525380611903346129458722682029853344872289843764805072638891004095570009521735125262572236849557538069371882023383902780834342778718868509018938453893607479736577609299278110130818916024780757664746975226899446915264271089664 : ℕ) >>> (6 * i)) % 64

def edgeY (i : ℕ) (h j : Bool) := (edgesY (i*4 + h.toNat*2 + j.toNat))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma innerY : ∀ (s : S) (t x : Bool), faceY true (step s t x false) = faceY false (step s t x true) := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma outerY : ∀ (s : S) (t x b : Bool), faceY b (step s t x b) = edgeY (faceY b s) t x := by decide

def obsY (i : ℕ) : ℕ :=
  ((4699632710266337063664016 : ℕ) >>> (2 * i)) % 4

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsYtrue0 : ∀ s : S, ((obsY (faceY true s))).testBit 0 = bit s 3 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsYfalse0 : ∀ s : S, ((obsY (faceY false s))).testBit 0 = bit s 0 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsYtrue1 : ∀ s : S, ((obsY (faceY true s))).testBit 1 = bit s 0 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsYfalse1 : ∀ s : S, ((obsY (faceY false s))).testBit 1 = bit s 4 := by decide

def facesT (i : ℕ) : ℕ :=
  ((995901580218732554220621575644138633954803445473114786063662273195745332744743945006219983884002541991559640635298759431782028477731385197998768625137790657429452717028558213909074726451696698987569681110034726917901387021605799326157626127415804393707982455335456819465004698154788114451514786266846354588822255956977689422232861660869712316444031063505961255891017947601164685898982102888470547416154628586151483877161886936943773956409122725591546215040045193003518250194021616093483134370203062384630202905749646888347191419532218199063026784708573243720777556592575397243319862947976481617675612353440650661128568832 : ℕ) >>> (6 * i)) % 64

def faceT (b : Bool) (s : S) := (facesT (b.toNat * 172 + s.val))

def edgesT (i : ℕ) : ℕ :=
  ((515664477376649584789410880478183800771641966357795946777591344171765993135084086595430849707979772854312563963266427553567523968565138464885459525198295153251413659164049029602837360827226074878833759765070573737465323235141757380697928000653832232138105049291116864189990670380306562696215416150291945001480145138774466736841959652207965704087219538825174915533436111290368 : ℕ) >>> (6 * i)) % 64

def edgeT (i : ℕ) (h j : Bool) := (edgesT (i*4 + h.toNat*2 + j.toNat))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma innerT : ∀ (s : S) (x y : Bool), faceT true (step s false x y) = faceT false (step s true x y) := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma outerT : ∀ (s : S) (x y b : Bool), faceT b (step s b x y) = edgeT (faceT b s) x y := by decide

def obsT (i : ℕ) : ℕ :=
  ((2806543095076282 : ℕ) >>> (1 * i)) % 2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsTtrue0 : ∀ s : S, ((obsT (faceT true s))).testBit 0 = bit s 5 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma obsTfalse0 : ∀ s : S, ((obsT (faceT false s))).testBit 0 = bit s 0 := by decide

def roots (i : ℕ) : S :=
  ⟨(((12764689 : ℕ) >>> (3 * i)) % 8) % 172, Nat.mod_lt _ (by decide)⟩

def root (x y : ℤ) : S :=
  if -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 then (roots ((x+1).toNat * 3 + (y+1).toNat)) else 0

set_option maxHeartbeats 4000000 in
lemma rootBit (x y : ℤ) : bit (root x y) 0 = decide (x = 0 ∧ y = 0) := by
  by_cases hx : -4 ≤ x ∧ x ≤ 4
  · by_cases hy : -4 ≤ y ∧ y ≤ 4
    · obtain ⟨hx,hx'⟩ := hx
      obtain ⟨hy,hy'⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · simp only [root]; repeat' rw [if_neg (by omega)]
      exact (show bit 0 0 = false by decide).trans (by simp [show ¬ (x = 0 ∧ y = 0) by omega])
  · simp only [root]; repeat' rw [if_neg (by omega)]
    exact (show bit 0 0 = false by decide).trans (by simp [show ¬ (x = 0 ∧ y = 0) by omega])

set_option maxHeartbeats 4000000 in
lemma rootStep (x y : ℤ) : step (root (x/2) (y/2)) false (oddB x) (oddB y) = root x y := by
  by_cases hx : -4 ≤ x ∧ x ≤ 4
  · by_cases hy : -4 ≤ y ∧ y ≤ 4
    · obtain ⟨hx,hx'⟩ := hx
      obtain ⟨hy,hy'⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · simp only [root]; repeat' rw [if_neg (by omega)]
      cases oddB x <;> cases oddB y <;> decide
  · simp only [root]; repeat' rw [if_neg (by omega)]
    cases oddB x <;> cases oddB y <;> decide

set_option maxHeartbeats 4000000 in
lemma rootX (x y : ℤ) : faceX true (root x y) = faceX false (root (x+1) y) := by
  by_cases hx : -4 ≤ x ∧ x ≤ 4
  · by_cases hy : -4 ≤ y ∧ y ≤ 4
    · obtain ⟨hx,hx'⟩ := hx
      obtain ⟨hy,hy'⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · simp only [root]; repeat' rw [if_neg (by omega)]
      decide
  · simp only [root]; repeat' rw [if_neg (by omega)]
    decide

set_option maxHeartbeats 4000000 in
lemma rootY (x y : ℤ) : faceY true (root x y) = faceY false (root x (y+1)) := by
  by_cases hx : -4 ≤ x ∧ x ≤ 4
  · by_cases hy : -4 ≤ y ∧ y ≤ 4
    · obtain ⟨hx,hx'⟩ := hx
      obtain ⟨hy,hy'⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · simp only [root]; repeat' rw [if_neg (by omega)]
      decide
  · simp only [root]; repeat' rw [if_neg (by omega)]
    decide

def lab : ℕ → ℤ → ℤ → ℤ → S
  | 0, _, x, y => root x y
  | k+1, t, x, y => step (lab k (t/2) (x/2) (y/2)) (oddB t) (oddB x) (oddB y)

lemma start (k : ℕ) (x y : ℤ) : lab k 0 x y = root x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => simpa only [lab, Int.zero_ediv, ih, show oddB 0 = false by decide] using rootStep x y

lemma adjX (k : ℕ) (t x y : ℤ) :
    faceX true (lab k t x y) = faceX false (lab k t (x+1) y) := by
  induction k generalizing t x y with
  | zero => exact rootX x y
  | succ k ih =>
    simp only [lab]
    by_cases h : x % 2 = 0
    · rw [show oddB x = false by simp [oddB, h], show oddB (x+1) = true by simp [oddB]; omega,
          show (x+1)/2 = x/2 by omega]
      apply innerX
    · rw [show oddB x = true by simpa [oddB] using (show x%2 = 1 by omega),
          show oddB (x+1) = false by simp [oddB]; omega,
          show (x+1)/2 = x/2+1 by omega, outerX, outerX, ih (t/2) (x/2) (y/2)]

lemma adjY (k : ℕ) (t x y : ℤ) :
    faceY true (lab k t x y) = faceY false (lab k t x (y+1)) := by
  induction k generalizing t x y with
  | zero => exact rootY x y
  | succ k ih =>
    simp only [lab]
    by_cases h : y % 2 = 0
    · rw [show oddB y = false by simp [oddB, h], show oddB (y+1) = true by simp [oddB]; omega,
          show (y+1)/2 = y/2 by omega]
      apply innerY
    · rw [show oddB y = true by simpa [oddB] using (show y%2 = 1 by omega),
          show oddB (y+1) = false by simp [oddB]; omega,
          show (y+1)/2 = y/2+1 by omega, outerY, outerY, ih (t/2) (x/2) (y/2)]

lemma adjT (k : ℕ) (t x y : ℤ) (ht : 0 ≤ t) (hk : t+1 < (2:ℤ)^k) :
    faceT true (lab k t x y) = faceT false (lab k (t+1) x y) := by
  induction k generalizing t x y with
  | zero => simp at hk; omega
  | succ k ih =>
    simp only [lab]
    by_cases h : t % 2 = 0
    · rw [show oddB t = false by simp [oddB, h], show oddB (t+1) = true by simp [oddB]; omega,
          show (t+1)/2 = t/2 by omega]
      apply innerT
    · rw [show oddB t = true by simpa [oddB] using (show t%2 = 1 by omega),
          show oddB (t+1) = false by simp [oddB]; omega,
          show (t+1)/2 = t/2+1 by omega, outerT, outerT, ih (t/2) (x/2) (y/2) (by omega) (by rw [pow_succ] at hk; omega)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma rule : ∀ s : S, bit s 5 = (526:ℕ).testBit ((bit s 0).toNat + 2*((bit s 1).toNat + (bit s 2).toNat + (bit s 3).toNat + (bit s 4).toNat)) := by decide

lemma correct (k t : ℕ) (ht : (t:ℤ) < 2^k) (x y : ℤ) :
    cell 526 t x y = bit (lab k t x y) 0 := by
  induction t generalizing x y with
  | zero => simpa only [Nat.cast_zero, start, cell] using (rootBit x y).symm
  | succ t ih =>
    have ht' : (t:ℤ) + 1 < 2^k := by exact_mod_cast ht
    have hlt : (t:ℤ) < 2^k := by omega
    simp only [cell, ih hlt, Nat.cast_succ]
    have hx := congrArg (fun i : ℕ => ((obsX (i))).testBit 0) (adjX k t x y)
    have hxx := congrArg (fun i : ℕ => ((obsX (i))).testBit 1) (adjX k t (x-1) y)
    have hy := congrArg (fun i : ℕ => ((obsY (i))).testBit 0) (adjY k t x y)
    have hyy := congrArg (fun i : ℕ => ((obsY (i))).testBit 1) (adjY k t x (y-1))
    have hz := congrArg (fun i : ℕ => ((obsT (i))).testBit 0) (adjT k t x y (by positivity) ht')
    simp only [sub_add_cancel, obsXtrue0, obsXfalse0, obsXtrue1, obsXfalse1,
      obsYtrue0, obsYfalse0, obsYtrue1, obsYfalse1, obsTtrue0, obsTfalse0] at hx hxx hy hyy hz
    rw [← hx, hxx, ← hy, hyy, ← rule, hz]


def row (d : ℕ) (x : ℤ) (f : ℤ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range d, f (x + i)

lemma rowPair (d : ℕ) (x : ℤ) (f : ℤ → ℤ) :
    row (d*2) (2*x) f = row d x (fun i => f (2*i) + f (2*i+1)) := by
  induction d with
  | zero => simp [row]
  | succ d ih =>
    unfold row at *
    rw [Nat.succ_mul, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [Nat.cast_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf

lemma rowAdd (d : ℕ) (x : ℤ) (f g : ℤ → ℤ) :
    row d x (fun i => f i + g i) = row d x f + row d x g := by
  simp [row, Finset.sum_add_distrib]

def liftW (w : S → ℤ) (s : S) : ℤ :=
  (w (step s true false false) + w (step s true false true)) +
  (w (step s true true false) + w (step s true true true))

def total (k : ℕ) (w : S → ℤ) : ℤ :=
  row (2^k*2) (-(2:ℤ)^k) fun x =>
    row (2^k*2) (-(2:ℤ)^k) fun y => w (lab k (2^k-1) x y)

lemma totalStep (k : ℕ) (w : S → ℤ) : total (k+1) w = total k (liftW w) := by
  unfold total
  rw [pow_succ, pow_succ, show -((2:ℤ)^k*2) = 2*(-(2:ℤ)^k) by ring, rowPair]
  simp_rw [rowPair]
  simp_rw [← rowAdd]
  simp only [lab, liftW]
  have ho (z : ℤ) : oddB (2*z) = false := by simp [oddB, Int.mul_emod]
  have hi (z : ℤ) : oddB (2*z+1) = true := by simp [oddB, Int.add_emod, Int.mul_emod]
  have div0 (z : ℤ) : 2*z/2 = z := by omega
  have div1 (z : ℤ) : (2*z+1)/2 = z := by omega
  rw [show (2:ℤ)^k*2-1 = 2*((2:ℤ)^k-1)+1 by ring]
  simp only [div0, div1, ho, hi]

def weight (s : S) : ℤ := (bit s 0).toNat

lemma exterior (t : ℕ) (x y : ℤ)
    (h : x < -(t:ℤ) ∨ (t:ℤ) < x ∨ y < -(t:ℤ) ∨ (t:ℤ) < y) :
    cell 526 t x y = false := by
  induction t generalizing x y with
  | zero =>
    simp only [cell, Nat.cast_zero, neg_zero] at *
    simp [show ¬ (x = 0 ∧ y = 0) by omega, oddB]
  | succ t ih =>
    simp only [Nat.cast_succ] at h
    simp only [cell]
    rw [ih x y (by omega), ih (x+1) y (by omega), ih (x-1) y (by omega),
      ih x (y+1) (by omega), ih x (y-1) (by omega)]
    all_goals decide

lemma rowHead (n : ℕ) (x : ℤ) (f : ℤ → ℤ) :
    row (n+1) x f = f x + row n (x+1) f := by
  unfold row
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
  simp_rw [show ∀ i : ℤ, x + (i+1) = x+1+i by intro i; ring]
  exact add_comm _ _

def countZ (t : ℕ) : ℤ := onCount 526 t

lemma countSquare (t : ℕ) :
    row (2*t+2) (-(t:ℤ)-1) (fun x => row (2*t+2) (-(t:ℤ)-1)
      (fun y => ((cell 526 t x y).toNat : ℤ))) =
    countZ t + (4*(t:ℤ)+3) * (false).toNat := by
  have he (j : ℤ) : cell 526 t (-(t:ℤ)-1) j = false := exterior _ _ _ (by omega)
  have hf (i : ℤ) : cell 526 t i (-(t:ℤ)-1) = false := exterior _ _ _ (by omega)
  rw [rowHead]
  simp_rw [he]
  simp_rw [rowHead (2*t+1), hf]
  simp only [sub_add_cancel]
  unfold countZ onCount row
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have eqb (v : Bool) : (v.toNat : ℤ) = (if v then 1 else 0) := by cases v <;> rfl
  simp_rw [eqb]
  simp only [sub_eq_neg_add]
  push_cast
  ring_nf

lemma totalCount (n : ℕ) : total n weight = a n + 0 := by
  let t : ℕ := 2^n-1
  have hp : 0 < (2:ℕ)^n := by positivity
  have hcast : (t:ℤ) = 2^n-1 := by dsimp [t]; rw [Nat.cast_sub (by omega : 1 ≤ (2:ℕ)^n)]; push_cast; rfl
  have hn : (2:ℕ)^n*2 = 2*t+2 := by dsimp [t]; omega
  have hx : -(2:ℤ)^n = -(t:ℤ)-1 := by omega
  unfold total weight
  rw [← hcast, hx, hn]
  simp_rw [← correct n t (by omega)]
  have h := countSquare t
  simpa [countZ, a, t] using h



lemma totalScale (k : ℕ) (c : ℤ) (w : S → ℤ) :
    total k (fun s => c*w s) = c*total k w := by
  simp [total, row, Finset.mul_sum]

lemma totalAdd (k : ℕ) (v w : S → ℤ) :
    total k (fun s => v s + w s) = total k v + total k w := by
  simp [total, row, Finset.sum_add_distrib]

lemma totalEigen (k : ℕ) (e : ℤ) (w : S → ℤ) (h : ∀ s, liftW w s = e*w s) :
    total k w = e^k * total 0 w := by
  induction k with
  | zero => simp
  | succ k ih => rw [totalStep, funext h, totalScale, ih, pow_succ]; ring

def v1 (s : S) : ℤ := ((((13671775197043680468402454355285162703843059292196519042256415188641865708674788310793342868436443104080:ℕ) >>> (2*s.val)) % 4 : ℕ) : ℤ) + (0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma level1 : ∀ s : S, liftW weight s = v1 s := by decide

def v2 (s : S) : ℤ := ((((361900763660007669229888067198022694241342134123501291789858624236791635915007044819532873841297186924184201064222913671911725057261769399326105948713890824198652347499787970556990572046042384342459001291808:ℕ) >>> (4*s.val)) % 16 : ℕ) : ℤ) + (0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma level2 : ∀ s : S, liftW v1 s = v2 s := by decide

def p1 (s : S) : ℤ := ((((163074056349556013423985885750804478424854401192597087609474676535045627161066539419202479674303999458930120016971072213364865365184370576541265777323836315038517791135669446209348011297544624151895163937412:ℕ) >>> (4*s.val)) % 16 : ℕ) : ℤ) + (-4)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma eig1 : ∀ s : S, liftW p1 s = 1 * p1 s := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma base1 : total 0 p1 = (-2) := by decide

def p2 (s : S) : ℤ := ((((13145681207529314046138505404776182790494783052962573908727072847601569767086310282112068978504864809332625476726022664309593277855033302674567055831282651414469919843687134337120820155330958847493315163970505953015083322188321098357841119366462771524924770461301848344842717921006880372909465748529130064388114:ℕ) >>> (6*s.val)) % 64 : ℕ) : ℤ) + (-18)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma eig2 : ∀ s : S, liftW p2 s = 2 * p2 s := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma base2 : total 0 p2 = (0) := by decide

def p3 (s : S) : ℤ := ((((0:ℕ) >>> (1*s.val)) % 2 : ℕ) : ℤ) + (0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma eig3 : ∀ s : S, liftW p3 s = 3 * p3 s := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma base3 : total 0 p3 = (0) := by decide

def p4 (s : S) : ℤ := ((((19284896910351163835046939352492837600639048055127387070962459299087595261151616242158170627123077463277514645842492739499196853928599909130617944833866552401033236285307603778448762515020138789440145529609652526176177879032817736185799121152544702869793489734569823480452065747747842715525035701001181033244288:ℕ) >>> (6*s.val)) % 64 : ℕ) : ℤ) + (0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma eig4 : ∀ s : S, liftW p4 s = 4 * p4 s := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma base4 : total 0 p4 = (104) := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma decomp : ∀ s : S, (6:ℤ) * v2 s = p1 s + p2 s + p3 s + p4 s := by decide

lemma scaled (k : ℕ) : 6 * total (k+2) weight = (1:ℤ)^k * (-2) + (2:ℤ)^k * (0) + (3:ℤ)^k * (0) + (4:ℤ)^k * (104) := by
  rw [totalStep, funext level1, totalStep, funext level2, ← totalScale, funext decomp]
  rw [totalAdd, totalAdd, totalAdd, totalEigen k 1 p1 eig1, base1, totalEigen k 2 p2 eig2, base2, totalEigen k 3 p3 eig3, base3, totalEigen k 4 p4 eig4, base4]

lemma formQ (n : ℕ) (h : 2 ≤ n) :
    (a n : ℚ) = (13*(4:ℚ)^(n-1)-1)/3 := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  have hv := scaled k
  rw [totalCount] at hv
  have hq : (6:ℚ) * ((a (k+2):ℚ) + 0) =
      1^k*(-2)+2^k*0+3^k*0+4^k*104 := by exact_mod_cast hv
  rw [show k+2-1=k+1 by omega, pow_succ]
  norm_num at hq ⊢
  linarith

lemma recQ (n : ℕ) (h : 4 ≤ n) :
    (a n : ℚ) = 5*(a (n-1):ℚ)-4*(a (n-2):ℚ) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4,by omega⟩
  rw [formQ _ (by omega), formQ _ (by omega), formQ _ (by omega)]
  simp only [show k+4-1=k+3 by omega, show k+4-2=k+2 by omega,
    show k+3-1=k+2 by omega, show k+2-1=k+1 by omega, pow_add, pow_one]
  ring

lemma initial : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 17 ∧ a 3 = 69 := by
  have h0 : total 0 weight = 1 := by decide
  have h1 : total 0 v1 = 5 := by decide
  have hh1 : total 1 weight = 5 := by rw [show 1=0+1 by decide, totalStep, funext level1]; exact h1
  rw [totalCount] at h0 hh1
  have h2 := formQ 2 (by decide)
  have h3 := formQ 3 (by decide)
  norm_num at *
  exact ⟨h0,hh1,by exact_mod_cast h2,by exact_mod_cast h3⟩

end CA

open CA PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a272743.main := by
  refine ⟨formQ, fun n hn => recQ n (by omega), ?_⟩



  let P := PowerSeries.mk (fun n => (a n : ℚ))
  have hg : (1:ℤ) • (P * X^0) + (-5:ℤ) • (P * X^1) + (4:ℤ) • (P * X^2) =
      (1:ℤ) • (X^0 : PowerSeries ℚ) + (-4:ℤ) • (X^2 : PowerSeries ℚ) + (4:ℤ) • (X^3 : PowerSeries ℚ) := by
    ext n
    simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, P, coeff_mk]
    simp only [zsmul_eq_mul]
    by_cases h : n < 4
    · interval_cases n <;> norm_num [initial]
    · have hr := recQ n (by omega)
      simp only [Nat.sub_zero, if_pos (by omega : 0 ≤ n)] at *
      split_ifs <;> first | omega | (norm_num <;> linarith)
  simp only [zsmul_eq_mul, P] at hg
  linear_combination hg

