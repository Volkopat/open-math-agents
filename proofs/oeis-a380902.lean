import OMAStatements.S_oeis_a380902

-- Credit: @CubeJerry

/-!
# A380902: a counterexample to the prime-factor restriction

The list `[3, 3, 5, P, Q]` consists entirely of primes, and its product equals the
sum of the squares of its entries. Its product is greater than 27. This refutes
the fourth conjunct of the registered statement; the first three conjectures
are not resolved here.

The constants `A380902Core.P` and `A380902Core.Q` are the consecutive terms
`u 54` and `u 55` of `u 0 = u 1 = 1`, `u (n + 2) = 45 * u (n + 1) - u n`.
This recurrence comes from Vieta mutations of the seed `(1, 1, 3, 3, 5)`.
The proof below certifies the explicit integers directly, including primality.

Earlier desk note 60581 proposed Vieta mutations to
investigate infinitude. The present counterexample addresses the separate
restriction on representations whose factors are all prime.

Source: https://oeis.org/A380902.
-/

namespace A380902Pocklington

/-- A partial-factorization primality certificate, expressed through a root of unity whose
order exceeds the square root of the candidate. Unit differences ensure that the same order
is retained after reduction modulo any divisor. -/
theorem prime_of_order_certificate (n F : ℕ) (a : ZMod n)
    (hn : 2 ≤ n) (hF : n < F ^ 2) (ha : a ^ F = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ (F / q) - 1)) : n.Prime := by
  have hFpos : 0 < F := by
    by_contra h
    have h0 : F = 0 := Nat.eq_zero_of_not_pos h
    simp [h0] at hF
  have hFsqrt : Nat.sqrt n < F := Nat.sqrt_lt'.mpr hF
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨hn, ?_⟩
  intro m hm hms hmn
  have hmpos : 0 < m := by omega
  let : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  let : Fact (1 < m) := ⟨hm⟩
  let φ : ZMod n →+* ZMod m := ZMod.castHom hmn (ZMod m)
  let b : ZMod m := φ a
  have hb : b ^ F = 1 := by
    simpa only [b, map_pow, map_one] using congrArg φ ha
  have hbd : ∀ q : ℕ, q.Prime → q ∣ F → b ^ (F / q) ≠ 1 := by
    intro q hq hqF heq
    have hu := (hd q hq hqF).map φ
    have hu' : IsUnit (b ^ (F / q) - 1) := by
      simpa only [b, map_sub, map_pow, map_one] using hu
    exact hu'.ne_zero (sub_eq_zero.mpr heq)
  have hord : orderOf b = F :=
    orderOf_eq_of_pow_and_pow_div_prime hFpos hb hbd
  let u : (ZMod m)ˣ := Units.mkOfMulEqOne b (b ^ (F - 1)) (by
    rw [← pow_succ', Nat.sub_add_cancel hFpos]
    exact hb)
  have hbound : F ≤ Fintype.card (ZMod m)ˣ := calc
    F = orderOf b := hord.symm
    _ = orderOf u := orderOf_injective (Units.coeHom _) Units.val_injective u
    _ ≤ Fintype.card (ZMod m)ˣ := orderOf_le_card_univ
  have hcard := Nat.card_units_zmod_lt_sub_one (show 1 < m by omega)
  omega

end A380902Pocklington

namespace A380902Certificates

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem prime_24260815981 : Nat.Prime 24260815981 := by
  apply A380902Pocklington.prime_of_order_certificate 24260815981 24260815980 (2 : ZMod 24260815981)
  · norm_num
  · norm_num
  · reduce_mod_char
  · intro q hq hqd
    have hf : 24260815980 = 2 * 2 * 3 * 3 * 3 * 5 * 887 * 50651 := by norm_num
    rw [hf] at hqd
    simp only [hq.dvd_mul] at hqd
    have h2 : q ∣ 2 ↔ q = 2 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h3 : q ∣ 3 ↔ q = 3 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h5 : q ∣ 5 ↔ q = 5 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h887 : q ∣ 887 ↔ q = 887 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h50651 : q ∣ 50651 ↔ q = 50651 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    simp only [h2, h3, h5, h887, h50651, or_assoc] at hqd
    rcases hqd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨12130407990, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨12130407990, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨18848633689, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨18848633689, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨18848633689, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨20540378605, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨18366621236, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨3782985177, ?_⟩
      reduce_mod_char

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem prime_P : Nat.Prime 3975008818510860570063178521896626877423134543956742110665444401955840619438206454686489 := by
  apply A380902Pocklington.prime_of_order_certificate 3975008818510860570063178521896626877423134543956742110665444401955840619438206454686489 408910519881415028672461389376987174686255032 (1585840194018088447872075906219124494085652036757750707094276509138048551170729759498502 : ZMod 3975008818510860570063178521896626877423134543956742110665444401955840619438206454686489)
  · norm_num
  · norm_num
  · reduce_mod_char
  · intro q hq hqd
    have hf : 408910519881415028672461389376987174686255032 = 2 * 2 * 2 * 11 * 19 * 23 * 43 * 107 * 379 * 541 * 3347 * 4789 * 10259 * 31051 * 90989 * 24260815981 := by norm_num
    rw [hf] at hqd
    simp only [hq.dvd_mul] at hqd
    have h2 : q ∣ 2 ↔ q = 2 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h11 : q ∣ 11 ↔ q = 11 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h19 : q ∣ 19 ↔ q = 19 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h23 : q ∣ 23 ↔ q = 23 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h43 : q ∣ 43 ↔ q = 43 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h107 : q ∣ 107 ↔ q = 107 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h379 : q ∣ 379 ↔ q = 379 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h541 : q ∣ 541 ↔ q = 541 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h3347 : q ∣ 3347 ↔ q = 3347 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h4789 : q ∣ 4789 ↔ q = 4789 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h10259 : q ∣ 10259 ↔ q = 10259 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h31051 : q ∣ 31051 ↔ q = 31051 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h90989 : q ∣ 90989 ↔ q = 90989 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h24260815981 : q ∣ 24260815981 ↔ q = 24260815981 := Nat.prime_dvd_prime_iff_eq hq prime_24260815981
    simp only [h2, h11, h19, h23, h43, h107, h379, h541, h3347, h4789, h10259, h31051, h90989, h24260815981, or_assoc] at hqd
    rcases hqd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1987504409255430285031589260948313438711567271978371055332722200977920309719103227343244, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1987504409255430285031589260948313438711567271978371055332722200977920309719103227343244, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1987504409255430285031589260948313438711567271978371055332722200977920309719103227343244, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨3875575508964678156698564301610442584280905310388884167305177570113954000601892486700096, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨2070448722833914559202845530300941089660015636353019779436020541840793188761380173561891, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1727151442374556926045981004202424691890708543300284845091852520765099891969171243516599, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1239935193743340429052432818868598834654001690912406608839215723758821117317595910566947, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1648049477104206573666497667353007506959497498540425707623526281454967156009593160216821, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨2597396422963645831104365916926803203307944849505572458034584376191958245111576645010331, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1111331629612932489080235015441319810100792586667006308946696602033455352613067133518198, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨3553567138869172258056414383712688964790210329906099521326870665701595219861597274309717, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨3102638817848720011888239616268665878411782227332189653127246907492596792656299544967772, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨753913873938617150822957197116911424149006058174590870293384092212008153054700514644288, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨941838909033359095914136625670277755942033105012007796636839428164238909841933051878922, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1699009245474413114182072689502714723281529128577830422373844612013524265730923960350032, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨354194219109267089469562582648871067362229178748199461330186207729704573645494043771082, ?_⟩
      reduce_mod_char

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem prime_Q : Nat.Prime 178787019639056312114272069094606410564986435927077305481693028686338614052391094299501609 := by
  apply A380902Pocklington.prime_of_order_certificate 178787019639056312114272069094606410564986435927077305481693028686338614052391094299501609 846035865634647694323322614620986464425861661208 (48704101245893275351058420530204799530557347351289843526966450306591679382214623680117544 : ZMod 178787019639056312114272069094606410564986435927077305481693028686338614052391094299501609)
  · norm_num
  · norm_num
  · reduce_mod_char
  · intro q hq hqd
    have hf : 846035865634647694323322614620986464425861661208 = 2 * 2 * 2 * 11 * 19 * 23 * 43 * 107 * 379 * 541 * 3347 * 4789 * 10259 * 31051 * 90989 * 24260815981 * 2069 := by norm_num
    rw [hf] at hqd
    simp only [hq.dvd_mul] at hqd
    have h2 : q ∣ 2 ↔ q = 2 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h11 : q ∣ 11 ↔ q = 11 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h19 : q ∣ 19 ↔ q = 19 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h23 : q ∣ 23 ↔ q = 23 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h43 : q ∣ 43 ↔ q = 43 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h107 : q ∣ 107 ↔ q = 107 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h379 : q ∣ 379 ↔ q = 379 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h541 : q ∣ 541 ↔ q = 541 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h3347 : q ∣ 3347 ↔ q = 3347 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h4789 : q ∣ 4789 ↔ q = 4789 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h10259 : q ∣ 10259 ↔ q = 10259 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h31051 : q ∣ 31051 ↔ q = 31051 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h90989 : q ∣ 90989 ↔ q = 90989 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    have h24260815981 : q ∣ 24260815981 ↔ q = 24260815981 := Nat.prime_dvd_prime_iff_eq hq prime_24260815981
    have h2069 : q ∣ 2069 ↔ q = 2069 := Nat.prime_dvd_prime_iff_eq hq (by norm_num)
    simp only [h2, h11, h19, h23, h43, h107, h379, h541, h3347, h4789, h10259, h31051, h90989, h24260815981, h2069, or_assoc] at hqd
    rcases hqd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨89393509819528156057136034547303205282493217963538652740846514343169307026195547149750804, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨89393509819528156057136034547303205282493217963538652740846514343169307026195547149750804, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨89393509819528156057136034547303205282493217963538652740846514343169307026195547149750804, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨33663522516908565257945731087249559133307525636480801819761212938355890350769421904508519, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨36552044772667295389630421035780447276062694945949905370782805542292827887219985319403729, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨163222202112999940713119851669128629927718539628242195030456798570283097668659570031023349, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨59537752132855708174238560527405340875614803450668330383851932297651031968496469700421488, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨114327552282755252567102490938477211036937114753604705702656786469429685049314239706057202, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨171097237209163111666840232318794797383310255710259900916785165482292884938232814078313126, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨128756725661827289514567435510885358442750558045410883247514450944268235921653336327314057, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨173158462905586208698825056198198981391941666663515049566750886216111358656851779347828577, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨95189377287587791980281811362844243123195058175112509410591901537919273708918255114042451, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨90177668770875497478530961682554772255545902850480646630076658918786224987777085115450445, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨40404801137693197808372048082823178866084621814172320184328651819666007638070509082893503, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨1988365658514732924808310946558628245533572654612794976308717004188232105674468494394105, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨64497529272417185258140688399186726909827678961086441272680592743741504473612133493643785, ?_⟩
      reduce_mod_char
    · apply isUnit_iff_exists_inv.mpr
      refine ⟨27064555703761158244184234872702506365442919037728522841142031058870166517598249013817236, ?_⟩
      reduce_mod_char

end A380902Certificates

namespace A380902Core

open OMA.S_oeis_a380902

def P : ℕ :=
  3975008818510860570063178521896626877423134543956742110665444401955840619438206454686489

def Q : ℕ :=
  178787019639056312114272069094606410564986435927077305481693028686338614052391094299501609

theorem tuple_represents : represents [3, 3, 5, P, Q] (45 * P * Q) := by
  norm_num [represents, P, Q]

theorem tuple_primes (hP : P.Prime) (hQ : Q.Prime) :
    ∀ p ∈ ([3, 3, 5, P, Q] : List ℕ), p.Prime := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · exact hP
  · exact hQ

theorem product_ne_exceptions : 45 * P * Q ≠ 16 ∧ 45 * P * Q ≠ 27 := by
  norm_num [P, Q]

theorem disproof (hP : P.Prime) (hQ : Q.Prime) :
    ¬ (terms.Infinite ∧
      (∀ n ∈ terms, ¬ Squarefree n) ∧
      (∀ n ∈ terms, squareful n → n = 16 ∨ n = 27) ∧
      (∀ n f, represents f n → (∀ p ∈ f, Nat.Prime p) → n = 16 ∨ n = 27)) := by
  intro h
  have hc := h.2.2.2 (45 * P * Q) [3, 3, 5, P, Q]
    tuple_represents (tuple_primes hP hQ)
  rcases hc with hc | hc
  · exact product_ne_exceptions.1 hc
  · exact product_ne_exceptions.2 hc

end A380902Core

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a380902.main) := by
  exact A380902Core.disproof
    A380902Certificates.prime_P A380902Certificates.prime_Q
