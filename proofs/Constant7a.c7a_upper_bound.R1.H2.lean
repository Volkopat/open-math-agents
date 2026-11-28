import OMAReductions.R_Constant7a_c7a_upper_bound_R1
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A rational two-segment replacement for each half of Bai’s contour. The intermediate coordinates are 16/45 and 23/16. Nonnegative Bernstein coefficients control the rational amplitude on both segments. -/

open Complex Set MeasureTheory
private noncomputable def poly (z : ℂ) := z*(z^4+6*z^2+25)
private noncomputable def den (z : ℂ) := 25-z^2
private noncomputable def rat (n : ℕ) (z : ℂ) := 5*(poly z)^(3714*n)/(den z)^(5570*n+1)
private theorem prim (n : ℕ) : ∃ F : ℂ → ℂ, ∀ z ∈ Metric.ball (0:ℂ) 5, HasDerivAt F (rat n z) z := by
  apply DifferentiableOn.isExactOn_ball
  intro z hz
  have h : den z ≠ 0 := by
    simp only [Metric.mem_ball,dist_zero_right] at hz
    intro he
    have he' : (25:ℂ)=z^2 := sub_eq_zero.mp he
    have he'' := congrArg norm he'
    simp [norm_pow] at he''
    nlinarith [norm_nonneg z]
  unfold rat poly den
  apply DifferentiableAt.differentiableWithinAt
  fun_prop (disch := positivity)

private theorem segment_bound {F f : ℂ → ℂ} (a d : ℂ) (B : ℝ)
    (der : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt F (f (a+t*d)) (a+t*d))
    (bound : ∀ t ∈ Icc (0:ℝ) 1, ‖f (a+t*d)‖ ≤ B) :
    ‖F (a+d)-F a‖ ≤ B*‖d‖ := by
  have h (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun y : ℝ => F (a+y*d)) (f (a+t*d)*d) t := by
    have hg : HasDerivAt (fun w : ℂ => a+w*d) d (t:ℂ) := by simpa using
      (((hasDerivAt_id (t:ℂ)).mul_const d).const_add a)
    exact ((der t ht).comp (t:ℂ) hg).comp_ofReal
  have he := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (h t ht).hasDerivWithinAt) (fun t ht => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (bound t ⟨ht.1,ht.2.le⟩) (norm_nonneg d))
  simpa using he

private theorem vertical {F f : ℂ → ℂ}
    (der : ∀ z ∈ Metric.ball (0:ℂ) 5, HasDerivAt F (f z) z)
    (cont : ContinuousOn f (Metric.ball (0:ℂ) 5)) :
    |-(∫ y in (-2:ℝ)..2, (f (-1+(y:ℂ)*I)).re)| ≤ ‖F (-1+2*I)-F (-1-2*I)‖ := by
  have inside (y : ℝ) (hy : y ∈ uIcc (-2:ℝ) 2) : (-1+(y:ℂ)*I) ∈ Metric.ball (0:ℂ) 5 := by
    rw [uIcc_of_le (by norm_num)] at hy
    rw [Metric.mem_ball,dist_zero_right, ← sq_lt_sq₀ (norm_nonneg _) (by norm_num), ← normSq_eq_norm_sq]
    simp [normSq_apply,Complex.mul_re,Complex.mul_im]
    nlinarith [hy.1,hy.2, mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hy.1)]
  have hD (y : ℝ) (hy : y ∈ uIcc (-2:ℝ) 2) :
      HasDerivAt (fun t : ℝ => (F (-1+(t:ℂ)*I)).im) (f (-1+(y:ℂ)*I)).re y := by
    have hg : HasDerivAt (fun w : ℂ => -1+w*I) I (y:ℂ) := by
      simpa using (((hasDerivAt_id (y:ℂ)).mul_const I).const_add (-1))
    have hc := ((der _ (inside y hy)).comp (y:ℂ) hg).comp_ofReal
    simpa [Function.comp_def] using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hc
  have hC : ContinuousOn (fun y : ℝ => (f (-1+(y:ℂ)*I)).re) (uIcc (-2:ℝ) 2) :=
    Complex.continuous_re.comp_continuousOn (cont.comp (by fun_prop) inside)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hC.intervalIntegrable,abs_neg]
  convert Complex.abs_im_le_norm (F (-1+2*I)-F (-1-2*I)) using 1 <;> norm_num [sub_eq_add_neg]

private def numSq (x y : ℝ) :=
  (x^2+y^2)*((x-1)^2+(y-2)^2)*((x-1)^2+(y+2)^2)*
  ((x+1)^2+(y-2)^2)*((x+1)^2+(y+2)^2)
private def denSq (x y : ℝ) := ((x-5)^2+y^2)*((x+5)^2+y^2)

set_option maxHeartbeats 1600000 in
private theorem bound000 (t : ℝ) (hl : 0 ≤ t) (hr : t ≤ (199/200)) :
    0 ≤ (173561/200000000) * (denSq (0+(16/45)*t) (0+(23/16)*t))^3 - (numSq (0+(16/45)*t) (0+(23/16)*t))^2 := by
  have hL : 0 ≤ t-0 := sub_nonneg.mpr hl
  have hR : 0 ≤ (199/200)-t := sub_nonneg.mpr hr
  apply nonneg_of_mul_nonneg_right (a := (13295707639944931050073185160018744740526628440549372521814828118481389200088865177600000000000000000000 : ℝ)) ?_ (by norm_num)
  calc
    0 ≤ 3113952918802277996210859825243723277617070080000000000000000000000000000000000000000000000000000000000000000 * ((199/200)-t)^20 + (t-0) * (62279058376045559924217196504874465552341401600000000000000000000000000000000000000000000000000000000000000000 * ((199/200)-t)^19 + (t-0) * (593086438742197955691071646266356871455354649848892620800000000000000000000000000000000000000000000000000000000 * ((199/200)-t)^18 + (t-0) * (3575743242490369371078529231238734613229463914880067174400000000000000000000000000000000000000000000000000000000 * ((199/200)-t)^17 + (t-0) * (15279947737766517002734182495294278492813373467666058256601579520000000000000000000000000000000000000000000000000 * ((199/200)-t)^16 + (t-0) * (49021712626765497207968724907273012808676059254384174960025272320000000000000000000000000000000000000000000000000 * ((199/200)-t)^15 + (t-0) * (121926863329307288043011979506209055306364962823953096349888624587282841600000000000000000000000000000000000000000 * ((199/200)-t)^14 + (t-0) * (239400902371931786893200968132653109611715286599149701735071681821959782400000000000000000000000000000000000000000 * ((199/200)-t)^13 + (t-0) * (374687387084002146392626097632967313483131429586301596297614821133956967911391232000000000000000000000000000000000 * ((199/200)-t)^12 + (t-0) * (469358694429093313259976013512982726565481933892860549961248647825574930136694784000000000000000000000000000000000 * ((199/200)-t)^11 + (t-0) * (470532658957238648432518651855868439247378540522057669320285003236735237865271616757301248000000000000000000000000 * ((199/200)-t)^10 + (t-0) * (376038271166809552616215264023390624454179505719296776937790719670268628840574087573012480000000000000000000000000 * ((199/200)-t)^9 + (t-0) * (237622934049353354285918654892680702329809660625315596187730938183452993875032234910266185933127680000000000000000 * ((199/200)-t)^8 + (t-0) * (117098720340246682040415478385767789038254654249735338476662448072099270084761761529829967465021440000000000000000 * ((199/200)-t)^7 + (t-0) * (44011200364015325442592639228281493207904288233433973139024231931089154701575914889956968932311040000000000000000 * ((199/200)-t)^6 + (t-0) * (12171007150962708375587365989687267852428507591338196648198185505560418636241576828560925083566080000000000000000 * ((199/200)-t)^5 + (t-0) * (2330249323628590354585139308367639406443121795606222533470977598548883528114268708159918777607389184000000000000 * ((199/200)-t)^4 + (t-0) * (275191804597562698962428515977864030698326714366515786291218357057410992505440520128793900389236736000000000000 * ((199/200)-t)^3 + (t-0) * (15051649714989447849356341939036439018255349839644933137300241038101582253847822030596927209782679525376000000 * ((199/200)-t)^2 + (t-0) * (4883855025360477602375403103704174842727164154417381039744338113455223142102471550649588611887050752000000 * ((199/200)-t)^1 + (t-0) * (9926253336143437799419769014129168841618312555092508895427271672708083813245947158063881664928569124399)))))))))))))))))))) := by positivity
    _ = _ := by unfold denSq numSq; ring

set_option maxHeartbeats 1600000 in
private theorem bound001 (t : ℝ) (hl : (199/200) ≤ t) (hr : t ≤ 1) :
    0 ≤ (173561/200000000) * (denSq (0+(16/45)*t) (0+(23/16)*t))^3 - (numSq (0+(16/45)*t) (0+(23/16)*t))^2 := by
  have hL : 0 ≤ t-(199/200) := sub_nonneg.mpr hl
  have hR : 0 ≤ 1-t := sub_nonneg.mpr hr
  apply nonneg_of_mul_nonneg_right (a := (1401683395356260729391818575873415577600000000000000000000 : ℝ)) ?_ (by norm_num)
  calc
    0 ≤ 9926253336143437799419769014129168841618312555092508895427271672708083813245947158063881664928569124399 * (1-t)^20 + (t-(199/200)) * (174980695071423485403536044989007540320332090783681681115400746619985487994378477797014764059433295204000 * (1-t)^19 + (t-(199/200)) * (1816432059122490852148179456386006863770897236725384530479508621488173816179582044378020533271104568400000 * (1-t)^18 + (t-(199/200)) * (14089361636282589113997671832315637472015279599251787627112494156747765392728249650200391966863119520000000 * (1-t)^17 + (t-(199/200)) * (83068607130562886432674415329515277310147443325904996610701931221596348059445371711632819289856568000000000 * (1-t)^16 + (t-(199/200)) * (370824549265896545223245123865821904690136842318864972323929614024204817724381431678709601750881280000000000 * (1-t)^15 + (t-(199/200)) * (1266553138058983300843327283819208828894639599893547112491790392436948117095390221461092386383360000000000000 * (1-t)^14 + (t-(199/200)) * (3366002381170755411634340455886787840964225609526788198783456793255806318584942667617941799936000000000000000 * (1-t)^13 + (t-(199/200)) * (7073242520482453680522246685318723717341245962446816857118710739852291218001929411694423444480000000000000000 * (1-t)^12 + (t-(199/200)) * (11902249820621495216452111210843201264521393006191549960674933168017274068895852672294105088000000000000000000 * (1-t)^11 + (t-(199/200)) * (16177349884005278923564465750128214618503775759942607932254580405617683467712337813144780800000000000000000000 * (1-t)^10 + (t-(199/200)) * (17844181764368479911257815731223714001899352377912427388938119593827449399359847215104000000000000000000000000 * (1-t)^9 + (t-(199/200)) * (15985983691228316628113122037306582318334342421145469340463313870935618641521209303040000000000000000000000000 * (1-t)^8 + (t-(199/200)) * (11592906929663483505200717726186605879369915479449573189298500143948561891027963084800000000000000000000000000 * (1-t)^7 + (t-(199/200)) * (6750931097045240018596891986010520588220679266700034282494977093972336813983662080000000000000000000000000000 * (1-t)^6 + (t-(199/200)) * (3112868836809974471825385937934016776727674402171108555590653624255665895112704000000000000000000000000000000 * (1-t)^5 + (t-(199/200)) * (1111268896702903888583612444362127444285319932691273538581799837018728136704000000000000000000000000000000000 * (1-t)^4 + (t-(199/200)) * (296318906071685187544145216209331980304940132509906815396042792699664793600000000000000000000000000000000000 * (1-t)^3 + (t-(199/200)) * (55569711742153716959846428535577486833294863211358198953300470492823552000000000000000000000000000000000000 * (1-t)^2 + (t-(199/200)) * (6539865988320994262432106065987978201988713840543264939649420964659200000000000000000000000000000000000000 * (1-t)^1 + (t-(199/200)) * (363491583093578093460086056901855935904410700901851989038879211520000000000000000000000000000000000000000)))))))))))))))))))) := by positivity
    _ = _ := by unfold denSq numSq; ring

set_option maxHeartbeats 1600000 in
private theorem bound010 (t : ℝ) (hl : 0 ≤ t) (hr : t ≤ 1) :
    0 ≤ 27^2 - denSq (0+(16/45)*t) (0+(23/16)*t) := by
  have hL : 0 ≤ t-0 := sub_nonneg.mpr hl
  have hR : 0 ≤ 1-t := sub_nonneg.mpr hr
  apply nonneg_of_mul_nonneg_right (a := (268738560000 : ℝ)) ?_ (by norm_num)
  calc
    0 ≤ 27948810240000 * (1-t)^4 + (t-0) * (111795240960000 * (1-t)^3 + (t-0) * (141625402560000 * (1-t)^2 + (t-0) * (59660323200000 * (1-t)^1 + (t-0) * (589125788879)))) := by positivity
    _ = _ := by unfold denSq ; ring

set_option maxHeartbeats 1600000 in
private theorem bound100 (t : ℝ) (hl : 0 ≤ t) (hr : t ≤ 1) :
    0 ≤ (173549/200000000) * (denSq ((16/45)+(29/45)*t) ((23/16)+(9/16)*t))^3 - (numSq ((16/45)+(29/45)*t) ((23/16)+(9/16)*t))^2 := by
  have hL : 0 ≤ t-0 := sub_nonneg.mpr hl
  have hR : 0 ≤ 1-t := sub_nonneg.mpr hr
  apply nonneg_of_mul_nonneg_right (a := (1401683395356260729391818575873415577600000000000000000000 : ℝ)) ?_ (by norm_num)
  calc
    0 ≤ 2375861562963981761452145744584264633949865906715295092751 * (1-t)^20 + (t-0) * (14152254820513806841537072455972831642661881326834184172922496 * (1-t)^19 + (t-0) * (1121295493414198166309411429361592091321479572092481431852176896 * (1-t)^18 + (t-0) * (18764295986611494429192516435445824690615944698029250033922506752 * (1-t)^17 + (t-0) * (160995405213065139000414739058203864127873134906833360363762155520 * (1-t)^16 + (t-0) * (883032693199247134597378719827794370873710609799238161332187430912 * (1-t)^15 + (t-0) * (3418179413172226503537416894333957723408626414293258630221619265536 * (1-t)^14 + (t-0) * (9857946850629176107171339624725761207103747156376874631699477037056 * (1-t)^13 + (t-0) * (21878291716207188858230983582513744844350001033095908359504545185792 * (1-t)^12 + (t-0) * (38113633178381627223772480011702022903227960962058029749015916052480 * (1-t)^11 + (t-0) * (52723330803841686386411875586394640585863389505345413028954243072000 * (1-t)^10 + (t-0) * (58229992537927633450322493480031265836666028464507137504218972160000 * (1-t)^9 + (t-0) * (51368110656394754633306169173481208452091446147962372485231411200000 * (1-t)^8 + (t-0) * (36043050685195272392585715436084015935327177757164702672932044800000 * (1-t)^7 + (t-0) * (19937648177767266350530978191458433120714374642514558286036992000000 * (1-t)^6 + (t-0) * (8572439948820176372579833731659308898031210249110525942169600000000 * (1-t)^5 + (t-0) * (2805741251837530308074582199372222244251400556742589808640000000000 * (1-t)^4 + (t-0) * (677581693101450448099237795958096787427306917800706048000000000000 * (1-t)^3 + (t-0) * (114674648008836807032085156359475092271339104580403200000000000000 * (1-t)^2 + (t-0) * (12260082401531438747651577487918979624782465597440000000000000000 * (1-t)^1 + (t-0) * (622747524046550254912565048382093824196870144000000000000000000)))))))))))))))))))) := by positivity
    _ = _ := by unfold denSq numSq; ring

set_option maxHeartbeats 1600000 in
private theorem bound110 (t : ℝ) (hl : 0 ≤ t) (hr : t ≤ 1) :
    0 ≤ 29^2 - denSq ((16/45)+(29/45)*t) ((23/16)+(9/16)*t) := by
  have hL : 0 ≤ t-0 := sub_nonneg.mpr hl
  have hR : 0 ≤ 1-t := sub_nonneg.mpr hr
  apply nonneg_of_mul_nonneg_right (a := (268738560000 : ℝ)) ?_ (by norm_num)
  calc
    0 ≤ 30687844508879 * (1-t)^4 + (t-0) * (104732985352320 * (1-t)^3 + (t-0) * (129380839142400 * (1-t)^2 + (t-0) * (66497863680000 * (1-t)^1 + (t-0) * (11018280960000)))) := by positivity
    _ = _ := by unfold denSq ; ring

private theorem exp_rate : Real.exp 1.174535 ≤ 3.23664 := by
  have hh := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 0.174535)
    (by norm_num : (0.174535:ℝ) ≤ 1) (by decide : 0 < 9)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hh
  rw [show (1.174535 : ℝ) = 1+0.174535 by norm_num,Real.exp_add]
  nlinarith [Real.exp_one_lt_d9,Real.exp_pos 0.174535,
    mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le (Real.exp_pos 0.174535).le]

private theorem num1 : (27:ℝ)^2 * ((867805/1000000000:ℝ)*3.23664^6)^1857 ≤ 3.23664^2 := by
  have h : (867805/1000000000:ℝ)*3.23664^6 ≤ 0.997674 := by norm_num
  calc
    _ ≤ 27^2 * (0.997674:ℝ)^1857 := by gcongr
    _ = 27^2 * ((0.997674:ℝ)^100)^18 * (0.997674:ℝ)^57 := by rw [← pow_mul, mul_assoc, ← pow_add]
    _ ≤ 27^2 * (0.79226:ℝ)^18 * 0.8757 := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num
private theorem num2 : (29:ℝ)^2 * ((867745/1000000000:ℝ)*3.23664^6)^1857 ≤ 3.23664^2 := by
  have h : (867745/1000000000:ℝ)*3.23664^6 ≤ 0.997605 := by norm_num
  calc
    _ ≤ 29^2 * (0.997605:ℝ)^1857 := by gcongr
    _ = 29^2 * ((0.997605:ℝ)^100)^18 * (0.997605:ℝ)^57 := by rw [← pow_mul, mul_assoc, ← pow_add]
    _ ≤ 29^2 * (0.7868:ℝ)^18 * 0.87226 := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num

private theorem scale (u v q V : ℝ) (hu : 0 ≤ u) (hv : 25 ≤ v) (hq : 0≤q)
    (hvV : v≤V) (huv : u^4 ≤ q*v^6)
    (cert : V^2*(q*(3.23664:ℝ)^6)^1857 ≤ 3.23664^2) :
    u^3714*(3.23664:ℝ)^5570 ≤ v^5570 := by
  let r : ℝ := 3.23664
  have hr : 0<r := by norm_num [r]
  have hv0 : 0<v := by linarith
  have hvroot : v^2 * (q*r^6)^1857 ≤ r^2 := by
    apply le_trans _ cert
    gcongr
  have bound : u^7428 * r^11142 ≤ v^11140 * r^2 := by
    calc
      _ = (u^4)^1857 * (r^6)^1857 := by rw [← pow_mul,← pow_mul]
      _ ≤ (q*v^6)^1857 * (r^6)^1857 := by gcongr
      _ = v^11140 * (v^2*(q*r^6)^1857) := by rw [mul_pow,mul_pow,← pow_mul,← pow_mul]; ring
      _ ≤ _ := by gcongr
  have hb : (u^3714*r^5570)^2 ≤ (v^5570)^2 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr)).mp
    calc
      _ = u^7428*r^11142 := by ring
      _ ≤ _ := bound
      _ = _ := by ring
  exact le_of_sq_le_sq hb (by positivity)

private def pt (b : Bool) (x y : ℝ) : ℂ := ⟨-x, if b then y else -y⟩

private theorem pt_num (b : Bool) (x y : ℝ) :
    ‖poly (pt b x y)‖^2 = numSq x y := by
  rw [← Complex.normSq_eq_norm_sq]
  cases b <;> simp [poly,pt,numSq,Complex.normSq_apply,pow_succ,Complex.mul_re,Complex.mul_im] <;> ring
private theorem pt_den (b : Bool) (x y : ℝ) :
    ‖den (pt b x y)‖^2 = denSq x y := by
  rw [← Complex.normSq_eq_norm_sq]
  cases b <;> simp [den,pt,denSq,Complex.normSq_apply,pow_succ,Complex.mul_re,Complex.mul_im] <;> ring
private theorem den_lower (b : Bool) (x y : ℝ) (hx : 0≤x) (hy : x≤y) : 25 ≤ ‖den (pt b x y)‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  cases b <;> simp [pt,den,pow_two,Complex.mul_re] <;> nlinarith [sq_nonneg (y-x)]
private theorem pt_inside (b : Bool) (x y : ℝ) (hx : 0≤x) (hx' : x≤1) (hy : 0≤y) (hy' : y≤2) :
    pt b x y ∈ Metric.ball (0:ℂ) 5 := by
  rw [Metric.mem_ball,dist_zero_right, ← sq_lt_sq₀ (norm_nonneg _) (by norm_num), ← Complex.normSq_eq_norm_sq]
  cases b <;> simp [Complex.normSq_apply,pt] <;> nlinarith [mul_nonneg hx (sub_nonneg.mpr hx'),mul_nonneg hy (sub_nonneg.mpr hy')]

private theorem rat_bound (z : ℂ) (n : ℕ) (q V : ℝ) (hv : 25 ≤ ‖den z‖) (hq : 0≤q)
    (hV : ‖den z‖ ≤ V) (h : ‖poly z‖^4 ≤ q * ‖den z‖^6)
    (hc : V^2*(q*3.23664^6)^1857 ≤ 3.23664^2) :
    ‖rat n z‖ ≤ (1/5) / ((3.23664:ℝ)^5570)^n := by
  have hb := scale _ _ _ _ (norm_nonneg _) hv hq hV h hc
  let r : ℝ := 3.23664
  let u := ‖poly z‖
  let v := ‖den z‖
  have hr : 0 < r := by norm_num [r]
  have hv' : 0 < v := by change 0 < ‖den z‖; linarith
  have hu : 0 ≤ u := norm_nonneg _
  change u^3714*r^5570 ≤ v^5570 at hb
  have hpow := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hu _) (pow_nonneg hr.le _)) hb n
  unfold rat
  rw [norm_div,norm_mul,norm_pow,norm_pow,show ‖(5:ℂ)‖ = 5 by norm_num]
  change 5*u^(3714*n)/v^(5570*n+1) ≤ (1/5)/(r^5570)^n
  apply (div_le_div_iff₀ (pow_pos hv' _) (pow_pos (pow_pos hr _) n)).mpr
  calc
    _ = 5*(u^3714*r^5570)^n := by rw [pow_mul u, mul_pow, mul_assoc]
    _ ≤ 5*(v^5570)^n := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (1/5*v)*(v^5570)^n := mul_le_mul_of_nonneg_right (by change (5:ℝ) ≤ 1/5*‖den z‖; linarith) (pow_nonneg (pow_nonneg hv'.le _) _)
    _ = _ := by rw [pow_succ v (5570*n),pow_mul v]; ring

private theorem ray_bound (b : Bool) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖rat n (pt b (0+16/45*t) (0+23/16*t))‖ ≤ (1/5) / ((3.23664:ℝ)^5570)^n := by
  let x : ℝ := 0+16/45*t
  let y : ℝ := 0+23/16*t
  change ‖rat n (pt b x y)‖ ≤ _
  apply rat_bound _ n (867805/1000000000) 27 (den_lower b x y (by dsimp [x]; linarith [ht.1]) (by dsimp [x,y]; linarith [ht.1])) (by norm_num) _ _ num1
  · apply le_of_sq_le_sq _ (by norm_num)
    rw [pt_den]
    linarith [bound010 t ht.1 ht.2]
  · rw [show (4:ℕ)=2*2 by decide, pow_mul,pt_num,show (6:ℕ)=2*3 by decide,pow_mul,pt_den]
    rcases le_total t (199/200) with hl | hr
    · linarith [bound000 t ht.1 hl]
    · linarith [bound001 t hr ht.2]

private theorem outer_bound (b : Bool) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖rat n (pt b (16/45+29/45*t) (23/16+9/16*t))‖ ≤ (1/5) / ((3.23664:ℝ)^5570)^n := by
  let x : ℝ := 16/45+29/45*t
  let y : ℝ := 23/16+9/16*t
  change ‖rat n (pt b x y)‖ ≤ _
  apply rat_bound _ n (867745/1000000000) 29 (den_lower b x y (by dsimp [x]; linarith [ht.1]) (by dsimp [x,y]; linarith [ht.1,ht.2])) (by norm_num) _ _ num2
  · apply le_of_sq_le_sq _ (by norm_num)
    rw [pt_den]
    linarith [bound110 t ht.1 ht.2]
  · rw [show (4:ℕ)=2*2 by decide, pow_mul,pt_num,show (6:ℕ)=2*3 by decide,pow_mul,pt_den]
    linarith [bound100 t ht.1 ht.2]

private theorem pt_affine (b : Bool) (x y u v t : ℝ) :
    pt b x y + (t:ℂ)*pt b u v = pt b (x+u*t) (y+v*t) := by
  cases b <;> apply Complex.ext <;> simp [pt,Complex.mul_re,Complex.mul_im] <;> ring

private theorem pt_segment {F : ℂ → ℂ} {n : ℕ}
    (der : ∀ z ∈ Metric.ball (0:ℂ) 5, HasDerivAt F (rat n z) z)
    (b : Bool) (x y u v B L : ℝ) (hB : 0 ≤ B) (hL : ‖pt b u v‖ ≤ L)
    (ins : ∀ t ∈ Icc (0:ℝ) 1, pt b (x+u*t) (y+v*t) ∈ Metric.ball (0:ℂ) 5)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖rat n (pt b (x+u*t) (y+v*t))‖ ≤ B) :
    ‖F (pt b (x+u) (y+v))-F (pt b x y)‖ ≤ B*L := by
  have h := segment_bound (F := F) (f := rat n) (pt b x y) (pt b u v) B
    (fun t ht => by rw [pt_affine]; exact der _ (ins t ht))
    (fun t ht => by rw [pt_affine]; exact hb t ht)
  have he := pt_affine b x y u v 1
  simp only [ofReal_one,one_mul,mul_one] at he
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hL hB)

private theorem half_path {F : ℂ → ℂ} {n : ℕ}
    (der : ∀ z ∈ Metric.ball (0:ℂ) 5, HasDerivAt F (rat n z) z)
    (b : Bool) :
    ‖F (pt b 1 2)-F 0‖ ≤ ((1/5) / ((3.23664:ℝ)^5570)^n) * (5/2) := by
  let B : ℝ := (1/5) / ((3.23664:ℝ)^5570)^n
  have hB : 0≤B := by dsimp [B]; positivity
  have a := pt_segment der b 0 0 (16/45) (23/16) B (3/2) hB (by
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), ← normSq_eq_norm_sq]
    cases b <;> norm_num [pt,normSq_apply])
    (fun t ht => pt_inside _ _ _ (by linarith [ht.1]) (by linarith [ht.2])
      (by linarith [ht.1]) (by linarith [ht.2])) (ray_bound b n)
  have c := pt_segment der b (16/45) (23/16) (29/45) (9/16) B 1 hB (by
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), ← normSq_eq_norm_sq]
    cases b <;> norm_num [pt,normSq_apply])
    (fun t ht => pt_inside _ _ _ (by linarith [ht.1]) (by linarith [ht.2])
      (by linarith [ht.1]) (by linarith [ht.2])) (outer_bound b n)
  have hz : pt b 0 0 = 0 := by cases b <;> apply Complex.ext <;> simp [pt]
  rw [hz,zero_add,zero_add] at a
  norm_num only [show (16/45+29/45:ℝ)=1 by norm_num,show (23/16+9/16:ℝ)=2 by norm_num,mul_one] at c
  have ht := norm_sub_le_norm_sub_add_norm_sub (F (pt b 1 2)) (F (pt b (16/45) (23/16))) (F 0)
  change _ ≤ B*(5/2)
  linarith

theorem OMA.solution : OMA.R_Constant7a_c7a_upper_bound_R1.H2 := by
  apply Filter.Eventually.of_forall
  intro n
  rw [OMA.R_Constant7a_c7a_upper_bound_R1.contour_eq]
  obtain ⟨F,hF⟩ := prim n
  have hc : ContinuousOn (rat n) (Metric.ball (0:ℂ) 5) :=
    (show Complex.IsExactOn (rat n) (Metric.ball (0:ℂ) 5) from ⟨F,hF⟩).differentiableOn Metric.isOpen_ball |>.continuousOn
  have h := vertical hF hc
  have he1 : pt true 1 2 = -1+2*I := by apply Complex.ext <;> norm_num [pt]
  have he2 : pt false 1 2 = -1-2*I := by apply Complex.ext <;> norm_num [pt]
  have hh1 := half_path hF true
  have hh2 := half_path hF false
  rw [he1] at hh1
  rw [he2,norm_sub_rev] at hh2
  have ht := norm_sub_le_norm_sub_add_norm_sub (F (-1+2*I)) (F 0) (F (-1-2*I))
  have hexp : Real.exp ((5570*1.174535:ℝ)*n) ≤ ((3.23664:ℝ)^5570)^n := by
    rw [mul_comm (5570*1.174535) _, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    rw [show (5570*1.174535:ℝ) = (5570:ℕ)* (1.174535:ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_rate _
  calc
    _ = |-(∫ y in (-2:ℝ)..2, (rat n (-1+(y:ℂ)*I)).re)| := by
      simp only [rat,poly,den,mul_pow,mul_assoc]
    _ ≤ _ := h
    _ ≤ (1:ℝ)/((3.23664:ℝ)^5570)^n := by
      have comb (K : ℝ) : 1/5/K*(5/2)+1/5/K*(5/2) = 1/K := by ring
      exact (ht.trans (add_le_add hh1 hh2)).trans_eq (comb _)
    _ ≤ _ := one_div_le_one_div_of_le (Real.exp_pos _) hexp
