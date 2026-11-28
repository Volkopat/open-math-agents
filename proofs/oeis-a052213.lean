import OMAStatements.S_oeis_a052213

/-!
# A counterexample to the prime-signature conjecture for consecutive integers

The witness is a pair of consecutive 1,393-digit integers. Their numbers
of distinct prime factors are 31 and 27. Nevertheless the products of
the divisor counts of their divisors agree.

For widths w=e+1 of a prime-exponent list, write T for their product.
The divisor product is the product of (w!)^(T/w). The base width
profiles {2:10, 7:7, 10:5, 16:8} and {4:2, 5:5, 8:12, 14:7} have the
same T and the same valuations of the divisor product at every prime.
One further width 2 is added on each side to realize consecutiveness.

Both large cofactor primes are certified here. Roots of exact order L
modulo every prime divisor, with L=2^1178 or 3^744, put all prime
divisors in the residue class 1 modulo L. The cubic bound and a
discriminant check exclude a factorization into two proper factors.

Sources: https://oeis.org/A052213 and https://oeis.org/A211776
-/

namespace Sign213

theorem iterate_prime_power {N p g : ℕ} (k : ℕ) :
    ((Nat.rec (motive := fun _ => ℕ) g (fun _ x => x^p % N) k : ℕ) : ZMod N) =
      (g : ZMod N) ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul]
    simpa only [Nat.rec_add_one, ZMod.natCast_mod, Nat.cast_pow] using
      congrArg (fun x : ZMod N => x^p) ih

/-- A primitive prime-power root certified by repeated modular powering forces every
prime factor of N to lie in the residue class one modulo that prime power. -/
theorem order_certificate (N p k g z u : ℕ) (hN : 1 < N) (hp : p.Prime)
    (iter : Nat.rec (motive := fun _ => ℕ) g (fun _ x => x^p % N) k = z)
    (last : z^p % N = 1) (hz : 1 ≤ z) (inv : (z-1)*u % N = 1) :
    ∀ r : ℕ, r.Prime → r ∣ N → p^(k+1) ∣ r-1 := by
  intro r hr hrN
  let : Fact r.Prime := ⟨hr⟩
  have mod_one {v : ℕ} (hv : v % N = 1) : (v : ZMod r) = 1 := by
    have e : v ≡ 1 [MOD N] := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hN] using hv
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (e.of_dvd hrN) |>.trans (Nat.cast_one)
  have power : (g : ZMod r)^(p^k) = (z : ZMod r) := by
    have a := iterate_prime_power (N := N) (p := p) (g := g) k
    rw [iter] at a
    let f := ZMod.castHom hrN (ZMod r)
    simpa only [map_pow, map_natCast] using congrArg f a.symm
  have good : (g : ZMod r)^(p^(k+1)) = 1 := by
    rw [pow_succ,pow_mul,power,← Nat.cast_pow]
    exact mod_one last
  have test : (z : ZMod r) ≠ 1 := by
    have ok := mod_one inv
    rw [Nat.cast_mul, Nat.cast_sub hz, Nat.cast_one] at ok
    intro bad
    simp [bad] at ok
  have exact_order : orderOf (g : ZMod r) = p^(k+1) := by
    apply orderOf_eq_of_pow_and_pow_div_prime (pow_pos hp.pos _) good
    intro q hq hqd
    have eq := Nat.dvd_prime hp |>.mp (hq.dvd_of_dvd_pow hqd)
    rcases eq with h|rfl
    · exact (hq.ne_one h).elim
    rw [pow_succ,Nat.mul_div_cancel _ hp.pos,power]
    exact test
  have nz : (g : ZMod r) ≠ 0 := by
    rintro h
    rw [h,zero_pow (pow_ne_zero _ hp.ne_zero)] at good
    exact zero_ne_one good
  simpa only [exact_order] using ZMod.orderOf_dvd_card_sub_one nz

end Sign213

namespace Sign213

theorem prime_of_cubic (P L : ℕ) (hP : 2 ≤ P) (hL : 2 ≤ L) (hc : P < L^3)
    (horder : ∀ q : ℕ, q.Prime → q ∣ P → q%L = 1)
    (hex : ¬ ∃ a b : ℕ, a+b = ((P-1)/L)%L ∧ a*b = ((P-1)/L)/L) : P.Prime := by
  have hLpos : 0 < L := by omega
  have hd (x : ℕ) : x ∣ P → x%L = 1 := by
    induction x using Nat.recOnMul with
    | zero => intro h; simp at h; omega
    | one => intro _; exact Nat.mod_eq_of_lt (by omega)
    | prime p hp => exact horder p hp
    | mul a b ha hb =>
      intro hab
      rw [Nat.mul_mod, ha ((dvd_mul_right a b).trans hab),
        hb ((dvd_mul_left b a).trans hab), one_mul, Nat.mod_eq_of_lt (by omega)]
  by_contra hcomp
  obtain ⟨x,y,hx,hy,hxy⟩ := (Nat.not_prime_iff_exists_mul_eq hP).mp hcomp
  have hxm := hd x (hxy ▸ dvd_mul_right x y)
  have hym := hd y (hxy ▸ dvd_mul_left y x)
  let a := x/L
  let b := y/L
  have hxe : x = 1+L*a := by simpa [a,hxm] using (Nat.mod_add_div x L).symm
  have hye : y = 1+L*b := by simpa [b,hym] using (Nat.mod_add_div y L).symm
  have ha : 0 < a := by
    by_contra! h
    have hx1 : x=1 := by simpa [Nat.eq_zero_of_le_zero h] using hxe
    simp [hx1] at hxy
    omega
  have hb : 0 < b := by
    by_contra! h
    have hy1 : y=1 := by simpa [Nat.eq_zero_of_le_zero h] using hye
    simp [hy1] at hxy
    omega
  have hfactor : P = 1+L*((a+b)+L*(a*b)) := by rw [← hxy,hxe,hye]; ring
  have hab1 : a+b ≤ a*b+1 := by
    obtain ⟨c,hc'⟩ := Nat.exists_eq_add_of_le' ha
    obtain ⟨d,hd'⟩ := Nat.exists_eq_add_of_le' hb
    rw [hc',hd']
    nlinarith
  have hs : a+b < L := by
    by_contra! hbad
    have h1 := Nat.mul_le_mul_right (L^2) (hbad.trans hab1)
    have h2 := Nat.mul_le_mul_left L hbad
    nlinarith [hfactor]
  have ht : (P-1)/L = a+b+L*(a*b) := by simp [hfactor, Nat.add_comm 1 _, hLpos]
  apply hex
  refine ⟨a,b,?_,?_⟩
  · rw [ht, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  · rw [ht, Nat.add_mul_div_left _ _ hLpos, Nat.div_eq_of_lt hs, zero_add]

theorem prime_of_cubic_discriminant (P L : ℕ) (hP : 2 ≤ P) (hL : 2 ≤ L) (hc : P < L^3)
    (horder : ∀ q : ℕ, q.Prime → q ∣ P → q%L = 1)
    (hex : let t := (P-1)/L
           let u := t%L
           let v := t/L
           u^2 < 4*v ∨ (u^2-4*v).sqrt^2 ≠ u^2-4*v) : P.Prime := by
  apply prime_of_cubic P L hP hL hc horder
  rintro ⟨a,b,hs,hp⟩
  dsimp only at hex
  rw [← hs, ← hp] at hex
  have claim (a b : ℕ) (hab : a ≤ b) :
      4*(a*b) ≤ (a+b)^2 ∧ ((a+b)^2 - 4*(a*b)).sqrt^2 = (a+b)^2 - 4*(a*b) := by
    obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
    have eq : (a+(a+c))^2 = 4*(a*(a+c)) + c^2 := by ring
    rw [eq, Nat.add_sub_cancel_left, Nat.sqrt_eq']
    omega
  rcases le_total a b with h | h
  · have h' := claim a b h
    exact hex.elim (Nat.not_lt.mpr h'.1) (fun hn => hn h'.2)
  · have h' := claim b a h
    rw [add_comm b a, mul_comm b a] at h'
    exact hex.elim (Nat.not_lt.mpr h'.1) (fun hn => hn h'.2)

theorem prime_of_cubic_order (P L : ℕ) (hP : 2 ≤ P) (hL : 2 ≤ L) (hc : P < L^3)
    (horder : ∀ q : ℕ, q.Prime → q ∣ P → L ∣ q-1)
    (hex : let t := (P-1)/L
           let u := t%L
           let v := t/L
           u^2 < 4*v ∨ (u^2-4*v).sqrt^2 ≠ u^2-4*v) : P.Prime := by
  apply prime_of_cubic_discriminant P L hP hL hc _ hex
  intro q hq hqP
  obtain ⟨c,hc'⟩ := horder q hq hqP
  have he : q = 1+L*c := by have := hq.two_le; omega
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

end Sign213

namespace Sign213

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem left_prime : Nat.Prime 53648899649139058753506168322954088663801719471362405718766409250399581973666981381441531827395831340093095894760168980319991116242265931873762178566095838052155837969158951943267815929125982015070823518775922187268418225886665009232416232895038803319733462837075843155990292000014729870941037329196534902941998900798604242738939928922128543441431435860422359478772183742042634802597599976207011392119097116574658009851973129839906780377655972217357050717436528888372814357830661519268259047755084173398203921719648050478820125102269290683968755716664394899911516296773697780029484100496805475718837095630612828367124213338183812720905390496907255840925309307572247617812688924580198819198114267423161444767674609832134806276024816882351035756867882758045490662206506052590535879990321365431595618588124289128105207457496971602944221989180976063630618865223849103068700718478739784134070250380714946038305351501962190591280372307217138913485480005403513630285547215209678726811452836579758322248051318895732395859043794667476657705240599558942980157997057 := by
  apply prime_of_cubic_order _ (2^(1177+1)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  · exact order_certificate _ 2 1177 10867412869146762425681811417248219356703722172746189436318392153011990708477838440236765842982266491370071109982201881013626977970770774617970355761264140579883666751234118365998465674036371840541391949125024747236449651239918314142702883962223224258391634410785481587185293757666842097738500602612995709043020309890673943214641798108357996152345687334901626420889388134270478130449614966423941918439538941148809138354032482424871494974962337374240862569388563969658788159103869115946272651052031475416614602454283286001375806774893474613520797497738904580432907350962206211259758921159547887051205170830530960534859206510089534030538739841911163490050357532826080671576485282434372373859497898377875038299533514986471519633955810040534017176803590428431229755988478761555343427126855087033339455426167589001130029368602436133878533383131312799297418924572749579193486862942326503812119075209845179697811837955789748889353185584412935372554777709049459252171878813910671481395559198745898263568014539862227610536878987429467516706815864829004681748342452
      53648899649139058753506168322954088663801719471362405718766409250399581973666981381441531827395831340093095894760168980319991116242265931873762178566095838052155837969158951943267815929125982015070823518775922187268418225886665009232416232895038803319733462837075843155990292000014729870941037329196534902941998900798604242738939928922128543441431435860422359478772183742042634802597599976207011392119097116574658009851973129839906780377655972217357050717436528888372814357830661519268259047755084173398203921719648050478820125102269290683968755716664394899911516296773697780029484100496805475718837095630612828367124213338183812720905390496907255840925309307572247617812688924580198819198114267423161444767674609832134806276024816882351035756867882758045490662206506052590535879990321365431595618588124289128105207457496971602944221989180976063630618865223849103068700718478739784134070250380714946038305351501962190591280372307217138913485480005403513630285547215209678726811452836579758322248051318895732395859043794667476657705240599558942980157997056 26824449824569529376753084161477044331900859735681202859383204625199790986833490690720765913697915670046547947380084490159995558121132965936881089283047919026077918984579475971633907964562991007535411759387961093634209112943332504616208116447519401659866731418537921577995146000007364935470518664598267451470999450399302121369469964461064271720715717930211179739386091871021317401298799988103505696059548558287329004925986564919953390188827986108678525358718264444186407178915330759634129523877542086699101960859824025239410062551134645341984377858332197449955758148386848890014742050248402737859418547815306414183562106669091906360452695248453627920462654653786123808906344462290099409599057133711580722383837304916067403138012408441175517878433941379022745331103253026295267939995160682715797809294062144564052603728748485801472110994590488031815309432611924551534350359239369892067035125190357473019152675750981095295640186153608569456742740002701756815142773607604839363405726418289879161124025659447866197929521897333738328852620299779471490078998528
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem right_prime : Nat.Prime 52662173052214904866391331213558949759451854459271525361140379259298937965949681027140025510556076768177789792898225437616544794561995009898693919907413654625686114435042782780476997960838193245607258565174305305215400225846300765095806006808935020724928012337646722179966752384888676801889521338797672316945254058614708915815415714688605696774556008264173295526203713902502198768971062466163158609504063627381807323145928279753523634238888343797253672914509195962863720377360262033700011713474956236929211735526431275151230242101848877237400278978799983635536692878651336937103759332524765165324979546406381792214761182281736314339040631155155340932257840319755339922984945914412533741483214849958649340621466379396578140330137170913358723111912428650489162775162505587717126769692166543548235251427906749949866713964667343110928175533365599110062258324871840959547584211965224216789188864640476104823074061042127067307469069583456261083980134764642088385619150928701137504428994138636587224383985189987198347746315661272121944734125125576038512653120701 := by
  apply prime_of_cubic_order _ (3^(743+1)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  · exact order_certificate _ 3 743 4833323709367841583145618957607778413956402546819280219324341479482779687593632173517702912233284503983009035948753927479685674126141533480271097711345222800565314440239859837776085901783496300942824308598571907608530801454315541979351524299948867064039760822790428715772205374394829447683424564305031567433214248300347937712292963941553676977282510250449927689298927661112145390878762965313571092410010545912638465997277873448088524071813040942933878731544088504687173733816255931280370947045018991599522097938472540289099831314228399333083635557902881836528876600521758459627078172439832098081846243591970254996395528822050399301924338739912206831531008018689115222492653757729141114569434125331866849979633754506004798030624733935196174929716728143435392916480131489520297720638491898846674320275572822164784973411831943955752847613923841909324500412907446165110324663448326123491564425651177016055643143362584226866165374437933500244909060883570371071238108171292783575887984969684227215039631830225374392618914709205391243900098085991087055941136145
      1880380061620868842801355845316998245200539811949196380472867658209795508600313137735874375945468195663630607929738133815978842530915566898037893983717728242771641001431436195726365110115197413962968164363609869687223715938040381433370507103389291513288040754593101111607904864638320940273975590648354677029674893022245893261438322066916605304398785908468201844988284973322798909704843842973015726783562231968819852207184788897712166837219089677687953169339438886988926047234556357227910275677648888830840263839921299966806152190088449386915275799149253301420463377355282622700800830428488097193677733701055743921528824603174368112675002461567924044870853592873848153784790096058879956528296618150306475829511043372793719738337235021781674542148020956388829923703744695039437258846555205298704622782490303542024518153752200846184522497319717435677747742257836152646533730773514753321270275019596668652395927444315785202463386072652606386137636949890778468013651355439629961591307275123203108494433848462916898777875348063597176529769261377023774336134749 16927264330198012007863325122747317171417104882440776326889170533696380819116455963134717044870202857504719728322829101266855317343693147666885341974565308794304824477870448861583544283574331943881430133603565145176058836636086794554145166568515243070546657194351207022786282506750118620538515249383105879971859721864154340851325797540563030490052407451901697893738476309726466619755406207730047627573500465137662490312914496951937155800556418039855239915056585691958264776708568558824033812599102449366123823895503325061474696637253475950161667726550243444705409833765351438134319500698759022710433937568442016097744119226187315408788542897862472295795662242293830589733385272784551261651639410602780954930651778674594806863933311963859016189921469231366777617152920297559229836948537112749843542881805482135947398603638380754914551012015293891461503527538001602300350160397236487822639529873626478723559377865937094035001894503601218232614165938250436639201833191087169180945895621171128038629850447174760482989480104402841589401451954733004912772328650
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · decide +kernel

end Sign213

open Finset OMA.S_oeis_a052213

namespace Sign213

theorem divisorProduct_mul {m n : ℕ} (h : m.Coprime n) :
    divisorProduct (m*n) = divisorProduct m ^ n.divisors.card *
      divisorProduct n ^ m.divisors.card := by
  unfold divisorProduct
  rw [h.divisors_mul, Finset.prod_map]
  change (∏ z ∈ (m.divisors ×ˢ n.divisors).attach, (z.val.1*z.val.2).divisors.card) = _
  rw [Finset.prod_attach (m.divisors ×ˢ n.divisors) (fun z => (z.1*z.2).divisors.card),
    Finset.prod_product]
  calc
    _ = ∏ x ∈ m.divisors, ∏ y ∈ n.divisors, (x.divisors.card * y.divisors.card) := by
      refine Finset.prod_congr rfl fun x hx => Finset.prod_congr rfl fun y hy => ?_
      exact ((h.coprime_dvd_left (Nat.mem_divisors.mp hx).1).coprime_dvd_right
        (Nat.mem_divisors.mp hy).1).card_divisors_mul
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]

theorem card_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : (p^e).divisors.card = e+1 := by
  simp [Nat.divisors_prime_pow hp]

theorem divisorProduct_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    divisorProduct (p^e) = (e+1).factorial := by
  rw [divisorProduct, Nat.prod_divisors_prime_pow hp]
  simpa only [card_prime_pow hp] using Finset.prod_range_add_one_eq_factorial (e+1)

theorem card_signature {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card = ((primeSignature n).map (fun e => e+1)).prod := by
  rw [Nat.card_divisors hn, primeSignature, Multiset.map_map]
  rfl

theorem signature_prime_pow_mul (a p e : ℕ) (hp : p.Prime) (hpa : ¬p∣a) (he : 0<e) :
    primeSignature (p^e*a) = e ::ₘ primeSignature a := by
  have ha : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero _)
  have hpn : p ∉ a.primeFactors := fun h => hpa (Nat.dvd_of_mem_primeFactors h)
  rw [primeSignature, Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) ha,
    Nat.primeFactors_prime_pow he.ne' hp, Finset.singleton_union, ← Finset.cons_eq_insert _ _ hpn,
    Finset.cons_val, Multiset.map_cons, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) ha,
    Finsupp.add_apply, Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hpa,
    add_zero]
  congr 1
  refine Multiset.map_congr rfl fun q hq => ?_
  have hqp : q ≠ p := by rintro rfl; exact hpn hq
  simp [hp.factorization_pow, Finsupp.single_eq_of_ne hqp]

theorem signature_product_cons (s : Multiset ℕ) (e : ℕ) :
    ((e ::ₘ s).map (fun j => (j+1).factorial ^
      (((e ::ₘ s).erase j).map (fun k => k+1)).prod)).prod =
    (e+1).factorial ^ (s.map (fun k => k+1)).prod *
    ((s.map (fun j => (j+1).factorial ^ ((s.erase j).map (fun k => k+1)).prod)).prod)^(e+1) := by
  rw [Multiset.map_cons, Multiset.prod_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.prod_map_pow]
  apply congrArg Multiset.prod
  refine Multiset.map_congr rfl fun j hj => ?_
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons, ← pow_mul]
  rw [Nat.mul_comm]

theorem divisorProduct_signature (n : ℕ) (hn : n ≠ 0) :
    divisorProduct n = ((primeSignature n).map (fun e => (e+1).factorial ^
      (((primeSignature n).erase e).map (fun f => f+1)).prod)).prod := by
  induction n using Nat.recOnPrimePow with
  | zero => exact (hn rfl).elim
  | one => simp [divisorProduct, primeSignature]
  | prime_pow_mul a p e hp hpa he ih =>
    have ha : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero _)
    have hc : (p^e).Coprime a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left e
    rw [divisorProduct_mul hc, divisorProduct_prime_pow hp, card_prime_pow hp,
      signature_prime_pow_mul a p e hp hpa he, signature_product_cons, ih ha,
      card_signature ha]

theorem same_signature {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : primeSignature m = primeSignature n) : divisorProduct m = divisorProduct n := by
  rw [divisorProduct_signature m hm, divisorProduct_signature n hn, h]

end Sign213

namespace Sign213
open OMA.S_oeis_a052213

def sigCard (s : Multiset ℕ) : ℕ := (s.map (fun e => e+1)).prod
def sigValue (s : Multiset ℕ) : ℕ :=
  (s.map (fun e => (e+1).factorial ^ ((s.erase e).map (fun k => k+1)).prod)).prod

theorem sigCard_cons (e : ℕ) (s : Multiset ℕ) : sigCard (e ::ₘ s) = (e+1)*sigCard s := by
  simp [sigCard]
theorem sigValue_cons (e : ℕ) (s : Multiset ℕ) :
    sigValue (e ::ₘ s) = (e+1).factorial ^ sigCard s * (sigValue s)^(e+1) :=
  signature_product_cons s e

private theorem value_pos (s : Multiset ℕ) : 0 < sigValue s := by
  induction s using Multiset.induction_on with
  | empty => simp [sigValue]
  | cons e t ih => rw [sigValue_cons]; positivity

private theorem add_common {a b : Multiset ℕ} (hc : sigCard a = sigCard b)
    (hv : sigValue a = sigValue b) (s : Multiset ℕ) :
    sigCard (s+a) = sigCard (s+b) ∧ sigValue (s+a) = sigValue (s+b) := by
  induction s using Multiset.induction_on with
  | empty => simpa using And.intro hc hv
  | cons e t ih =>
    simp only [Multiset.cons_add, sigCard_cons, sigValue_cons, ih.1, ih.2, and_self]

private def sigValuation : List ℕ → ℕ → ℕ
  | [], _ => 0
  | e :: t, p => (t.map (fun k => k+1)).prod * (e+1).factorial.factorization p +
      (e+1) * sigValuation t p

private theorem val_spec (t : List ℕ) (p : ℕ) :
    (sigValue (t : Multiset ℕ)).factorization p = sigValuation t p := by
  induction t with
  | nil => simp [sigValue,sigValuation]
  | cons e t ih =>
    change (sigValue (e ::ₘ (t : Multiset ℕ))).factorization p = _
    rw [sigValue_cons, Nat.factorization_mul (by positivity) (pow_ne_zero _ (value_pos _).ne'),
      Nat.factorization_pow, Nat.factorization_pow, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ih]
    rfl

private theorem val_large {t : List ℕ} {p m : ℕ} (h : ∀ e ∈ t, e + 1 ≤ m) (hp : m < p) :
    sigValuation t p = 0 := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    have he := h e (by simp)
    have hzero : (e+1).factorial.factorization p = 0 := by
      by_cases hpr : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => (not_le_of_gt (lt_of_le_of_lt he hp))
          ((hpr.dvd_factorial).mp hd))
      · exact Nat.factorization_eq_zero_of_not_prime _ hpr
    simp [sigValuation, hzero, ih (fun z hz => h z (by simp [hz]))]

def leftProfile : List ℕ :=
  List.replicate 10 1 ++ List.replicate 7 6 ++ List.replicate 5 9 ++ List.replicate 8 15
def rightProfile : List ℕ :=
  List.replicate 2 3 ++ List.replicate 5 4 ++ List.replicate 12 7 ++ List.replicate 7 13

private theorem profile_card : sigCard (leftProfile : Multiset ℕ) = sigCard (rightProfile : Multiset ℕ) := by
  decide +kernel

private theorem profile_values : sigValue (leftProfile : Multiset ℕ) = sigValue (rightProfile : Multiset ℕ) := by
  apply Nat.eq_of_factorization_eq (value_pos _).ne' (value_pos _).ne'
  intro p
  rw [val_spec,val_spec]
  by_cases h : p≤16
  · interval_cases p <;> decide +kernel
  · rw [val_large (m:=16) (by decide +kernel) (by omega), val_large (m:=16) (by decide +kernel) (by omega)]

theorem profile_collision {x y : ℕ} (hx : 0<x) (hy : 0<y) (s : Multiset ℕ)
    (sx : primeSignature x = s + (leftProfile : Multiset ℕ))
    (sy : primeSignature y = s + (rightProfile : Multiset ℕ)) :
    divisorProduct x = divisorProduct y ∧ primeSignature x ≠ primeSignature y := by
  constructor
  · rw [divisorProduct_signature x hx.ne',divisorProduct_signature y hy.ne',sx,sy]
    exact (add_common profile_card profile_values s).2
  · rw [sx, sy]
    intro h
    have h' : (leftProfile : Multiset ℕ) = (rightProfile : Multiset ℕ) := add_left_cancel h
    have := congrArg Multiset.card h'
    change 30 = 26 at this
    omega
end Sign213

open OMA.S_oeis_a052213

namespace Sign213

theorem signature_from_factors (n : ℕ) (fs : List (ℕ × ℕ))
    (hrec : n = (fs.map (fun z => z.1 ^ z.2)).prod)
    (hd : (fs.map Prod.fst).Nodup)
    (hp : ∀ z ∈ fs, z.1.Prime ∧ 0 < z.2) :
    primeSignature n = (↑(fs.map Prod.snd) : Multiset ℕ) := by
  subst n
  induction fs with
  | nil => simp [primeSignature]
  | cons z fs ih =>
    rcases z with ⟨p,e⟩
    obtain ⟨hprime, he⟩ := hp (p,e) (by simp)
    have htail := fun w (hw : w ∈ fs) => hp w (List.mem_cons_of_mem _ hw)
    obtain ⟨hnmem, hn⟩ := List.nodup_cons.mp hd
    have hnodiv : ¬ p ∣ (fs.map (fun z => z.1^z.2)).prod := by
      intro hdiv
      obtain ⟨w,hw,hpw⟩ := hprime.prime.dvd_prod_iff.mp hdiv
      obtain ⟨entry,hentry,rfl⟩ := List.mem_map.mp hw
      have heq := ((Nat.dvd_prime (htail entry hentry).1).mp (hprime.dvd_of_dvd_pow hpw)).resolve_left
        hprime.ne_one
      apply hnmem
      exact List.mem_map.mpr ⟨entry,hentry,heq.symm⟩
    simp only [List.map_cons, List.prod_cons]
    rw [signature_prime_pow_mul _ p e hprime hnodiv he, ih hn htail]
    rfl

theorem signature_with_large (n P : ℕ) (fs : List (ℕ × ℕ)) (hP : P.Prime)
    (hrec : n = (fs.map (fun z => z.1 ^ z.2)).prod)
    (hd : (fs.map Prod.fst).Nodup)
    (hvalid : fs.all (fun z => (decide (z.1=P) || decide z.1.Prime) && decide (0<z.2)) = true) :
    primeSignature n = (↑(fs.map Prod.snd) : Multiset ℕ) := by
  apply signature_from_factors n fs hrec hd
  intro z hz
  have hv := List.all_eq_true.mp hvalid z hz
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1.elim (fun h => h ▸ hP) id, hv.2⟩

theorem signature_ne_of_lengths {m n : ℕ} {fs gs : List (ℕ × ℕ)}
    (hm : primeSignature m = (↑(fs.map Prod.snd) : Multiset ℕ))
    (hn : primeSignature n = (↑(gs.map Prod.snd) : Multiset ℕ))
    (hne : fs.length ≠ gs.length) : primeSignature m ≠ primeSignature n := by
  intro h
  rw [hm, hn] at h
  exact hne (by simpa using congrArg Multiset.card h)

end Sign213

namespace Sign213
open OMA.S_oeis_a052213

/-- The first integer of the consecutive pair. -/
def witness : ℕ := 3617714390303061070995679152327479935972724773184563654758129750541354513132289355834002491303853486893486351862860882034086040753592065539457993723636581703960549916558713619013730282620671319944793346296308012886620713370777359120745651405257217751859923099422581822299592155423289751048264653337180082578403905892992440347613825183703153941006083917730151573113092832176723836938641619550514771823054563744884991933394532243462549376365820681706594990142501128525704076222241341038135896407628606756762730700028228729358467623051963825387444466704544216901432236509839047558043222226859218922902744742434029872193028765982802289222807240714809915447386681162495410664843472269297736964300771220777004906911480115270105826953060462562306551715831019916645050062634833401840743417922745086613162817609397472850682714017023297547358883940158451119067163640307854451054991278941940872867080375242111674575632784961410374441011915542253244532625626587633587900317240445372193985812962231568354338984030155943751745531744026464988202625650605532085666479968120273298639252831516590147283829664650468465017862490770351611250996056129168709101100826646654639270484098144916574450466720111743379225694144788871873105938242019479484838740897263455352691169536775840475469271171017394613279112120071747128166621113031743879460285881804395512047734043035992289352228057622298230187944939000000000000000

private def leftFactors : List (ℕ × ℕ) :=
  [(53648899649139058753506168322954088663801719471362405718766409250399581973666981381441531827395831340093095894760168980319991116242265931873762178566095838052155837969158951943267815929125982015070823518775922187268418225886665009232416232895038803319733462837075843155990292000014729870941037329196534902941998900798604242738939928922128543441431435860422359478772183742042634802597599976207011392119097116574658009851973129839906780377655972217357050717436528888372814357830661519268259047755084173398203921719648050478820125102269290683968755716664394899911516296773697780029484100496805475718837095630612828367124213338183812720905390496907255840925309307572247617812688924580198819198114267423161444767674609832134806276024816882351035756867882758045490662206506052590535879990321365431595618588124289128105207457496971602944221989180976063630618865223849103068700718478739784134070250380714946038305351501962190591280372307217138913485480005403513630285547215209678726811452836579758322248051318895732395859043794667476657705240599558942980157997057, 1),
   (193, 1), (223, 1), (227, 1), (229, 1), (233, 1),
   (239, 1), (241, 1), (251, 1), (257, 1), (263, 1),
   (83, 6), (157, 6), (163, 6), (173, 6), (181, 6),
   (197, 6), (211, 6), (53, 9), (59, 9), (71, 9),
   (79, 9), (113, 9), (2, 15), (5, 15), (13, 15),
   (17, 15), (19, 15), (23, 15), (37, 15), (43, 15)]

private theorem left_signature : primeSignature (witness) =
    ({1} : Multiset ℕ) + (leftProfile : Multiset ℕ) := by
  have h := signature_with_large (witness) 53648899649139058753506168322954088663801719471362405718766409250399581973666981381441531827395831340093095894760168980319991116242265931873762178566095838052155837969158951943267815929125982015070823518775922187268418225886665009232416232895038803319733462837075843155990292000014729870941037329196534902941998900798604242738939928922128543441431435860422359478772183742042634802597599976207011392119097116574658009851973129839906780377655972217357050717436528888372814357830661519268259047755084173398203921719648050478820125102269290683968755716664394899911516296773697780029484100496805475718837095630612828367124213338183812720905390496907255840925309307572247617812688924580198819198114267423161444767674609832134806276024816882351035756867882758045490662206506052590535879990321365431595618588124289128105207457496971602944221989180976063630618865223849103068700718478739784134070250380714946038305351501962190591280372307217138913485480005403513630285547215209678726811452836579758322248051318895732395859043794667476657705240599558942980157997057 leftFactors
    left_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact h.trans (by decide +kernel)

private def rightFactors : List (ℕ × ℕ) :=
  [(52662173052214904866391331213558949759451854459271525361140379259298937965949681027140025510556076768177789792898225437616544794561995009898693919907413654625686114435042782780476997960838193245607258565174305305215400225846300765095806006808935020724928012337646722179966752384888676801889521338797672316945254058614708915815415714688605696774556008264173295526203713902502198768971062466163158609504063627381807323145928279753523634238888343797253672914509195962863720377360262033700011713474956236929211735526431275151230242101848877237400278978799983635536692878651336937103759332524765165324979546406381792214761182281736314339040631155155340932257840319755339922984945914412533741483214849958649340621466379396578140330137170913358723111912428650489162775162505587717126769692166543548235251427906749949866713964667343110928175533365599110062258324871840959547584211965224216789188864640476104823074061042127067307469069583456261083980134764642088385619150928701137504428994138636587224383985189987198347746315661272121944734125125576038512653120701, 1),
   (167, 3), (199, 3), (67, 4), (109, 4), (151, 4),
   (179, 4), (191, 4), (61, 7), (73, 7), (89, 7),
   (97, 7), (101, 7), (103, 7), (107, 7), (127, 7),
   (131, 7), (137, 7), (139, 7), (149, 7), (3, 13),
   (7, 13), (11, 13), (29, 13), (31, 13), (41, 13),
   (47, 13)]

private theorem right_signature : primeSignature (witness+1) =
    ({1} : Multiset ℕ) + (rightProfile : Multiset ℕ) := by
  have h := signature_with_large (witness+1) 52662173052214904866391331213558949759451854459271525361140379259298937965949681027140025510556076768177789792898225437616544794561995009898693919907413654625686114435042782780476997960838193245607258565174305305215400225846300765095806006808935020724928012337646722179966752384888676801889521338797672316945254058614708915815415714688605696774556008264173295526203713902502198768971062466163158609504063627381807323145928279753523634238888343797253672914509195962863720377360262033700011713474956236929211735526431275151230242101848877237400278978799983635536692878651336937103759332524765165324979546406381792214761182281736314339040631155155340932257840319755339922984945914412533741483214849958649340621466379396578140330137170913358723111912428650489162775162505587717126769692166543548235251427906749949866713964667343110928175533365599110062258324871840959547584211965224216789188864640476104823074061042127067307469069583456261083980134764642088385619150928701137504428994138636587224383985189987198347746315661272121944734125125576038512653120701 rightFactors
    right_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact h.trans (by decide +kernel)

end Sign213

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a052213.main) := by
  intro conjecture
  obtain ⟨heq, hne⟩ := Sign213.profile_collision (x := Sign213.witness)
    (y := Sign213.witness+1) (by decide +kernel) (Nat.succ_pos _) {1}
    Sign213.left_signature Sign213.right_signature
  exact hne ((conjecture Sign213.witness (by decide +kernel)).mpr heq)
