import OMAStatements.S_arxiv_2610_39051
import Mathlib

namespace OMA.P_arxiv_2610_39051

open OMA.S_arxiv_2610_39051

def D : ℤ := 390597270
def K1 : ℤ := 27506850
def K2 : ℤ := -306974300465700
def K3 : ℤ := 1737729329305248531000
def K4 : ℤ := -4990825970776184359412576250
def K5 : ℤ := 5819113430538141468069406229602500

def aSeq : ℕ → ℤ
  | 0 => 1
  | 1 => K1 * aSeq 0
  | 2 => K1 * aSeq 1 + K2 * aSeq 0
  | 3 => K1 * aSeq 2 + K2 * aSeq 1 + K3 * aSeq 0
  | 4 => K1 * aSeq 3 + K2 * aSeq 2 + K3 * aSeq 1 + K4 * aSeq 0
  | n + 5 => K1 * aSeq (n + 4) + K2 * aSeq (n + 3) + K3 * aSeq (n + 2) + K4 * aSeq (n + 1) + K5 * aSeq n

private lemma aSeq_zero : aSeq 0 = 1 := rfl
private lemma aSeq_one : aSeq 1 = K1 * aSeq 0 := rfl
private lemma aSeq_two : aSeq 2 = K1 * aSeq 1 + K2 * aSeq 0 := rfl
private lemma aSeq_three : aSeq 3 = K1 * aSeq 2 + K2 * aSeq 1 + K3 * aSeq 0 := rfl
private lemma aSeq_four : aSeq 4 = K1 * aSeq 3 + K2 * aSeq 2 + K3 * aSeq 1 + K4 * aSeq 0 := rfl
private lemma aSeq_add_five (n : ℕ) :
    aSeq (n + 5) = K1 * aSeq (n + 4) + K2 * aSeq (n + 3) + K3 * aSeq (n + 2) +
      K4 * aSeq (n + 1) + K5 * aSeq n := rfl

private lemma a_eq_0 : aSeq 0 = 1 := rfl
private lemma a_eq_1 : aSeq 1 = 27506850 := by rw [aSeq_one, a_eq_0]; norm_num [K1]
private lemma a_eq_2 : aSeq 2 = 449652496456800 := by rw [aSeq_two, a_eq_1, a_eq_0]; norm_num [K1, K2]
private lemma a_eq_3 : aSeq 3 = 5662357064703037566000 := by rw [aSeq_three, a_eq_2, a_eq_1, a_eq_0]; norm_num [K1, K2, K3]
private lemma a_eq_4 : aSeq 4 = 60530479903768812227920113750 := by rw [aSeq_four, a_eq_3, a_eq_2, a_eq_1, a_eq_0]; norm_num [K1, K2, K3, K4]
private lemma a_eq_5 : aSeq 5 = 576716275381352763115288474586077500 := by rw [show (5 : ℕ) = 0 + 5 from rfl, aSeq_add_five, a_eq_4, a_eq_3, a_eq_2, a_eq_1, a_eq_0]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_6 : aSeq 6 = 5037918421620119913864844857322596149625000 := by rw [show (6 : ℕ) = 1 + 5 from rfl, aSeq_add_five, a_eq_5, a_eq_4, a_eq_3, a_eq_2, a_eq_1]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_7 : aSeq 7 = 41082521565946476948594936857861907814799555250000 := by rw [show (7 : ℕ) = 2 + 5 from rfl, aSeq_add_five, a_eq_6, a_eq_5, a_eq_4, a_eq_3, a_eq_2]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_8 : aSeq 8 = 316568868390454889348261036107027122583769688542219062500 := by rw [show (8 : ℕ) = 3 + 5 from rfl, aSeq_add_five, a_eq_7, a_eq_6, a_eq_5, a_eq_4, a_eq_3]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_9 : aSeq 9 = 2325015821931392436876423893361591408165033920950791750403125000 := by rw [show (9 : ℕ) = 4 + 5 from rfl, aSeq_add_five, a_eq_8, a_eq_7, a_eq_6, a_eq_5, a_eq_4]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_10 : aSeq 10 = 16378260511484069454192523805183024810199894130512359303450007037500000 := by rw [show (10 : ℕ) = 5 + 5 from rfl, aSeq_add_five, a_eq_9, a_eq_8, a_eq_7, a_eq_6, a_eq_5]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_11 : aSeq 11 = 111185760161215332660247779493714226375942015647065046674510281475105000000000 := by rw [show (11 : ℕ) = 6 + 5 from rfl, aSeq_add_five, a_eq_10, a_eq_9, a_eq_8, a_eq_7, a_eq_6]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_12 : aSeq 12 = 730036871504097415646390256093718843516885430075493523222538796448421245248984375000 := by rw [show (12 : ℕ) = 7 + 5 from rfl, aSeq_add_five, a_eq_11, a_eq_10, a_eq_9, a_eq_8, a_eq_7]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_13 : aSeq 13 = 4649228232684585883539396366855545356230972576115395284988531319787157018189759264843750000 := by rw [show (13 : ℕ) = 8 + 5 from rfl, aSeq_add_five, a_eq_12, a_eq_11, a_eq_10, a_eq_9, a_eq_8]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_14 : aSeq 14 = 28782304980086435635911697551844150126377173538524547085638854026125579984147915553085929687500000 := by rw [show (14 : ℕ) = 9 + 5 from rfl, aSeq_add_five, a_eq_13, a_eq_12, a_eq_11, a_eq_10, a_eq_9]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_15 : aSeq 15 = 173521620712818139083906285532392155750714250458983718607818118635836820217433546156870311043921875000000 := by rw [show (15 : ℕ) = 10 + 5 from rfl, aSeq_add_five, a_eq_14, a_eq_13, a_eq_12, a_eq_11, a_eq_10]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_16 : aSeq 16 = 1020221086533801296094206618546492247106262133223702361252762457335721716128700963593446610500047201660156250000 := by rw [show (16 : ℕ) = 11 + 5 from rfl, aSeq_add_five, a_eq_15, a_eq_14, a_eq_13, a_eq_12, a_eq_11]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_17 : aSeq 17 = 5856924145044589017863886837581433550654238263083341460516125678527907375617296640116466209088102401410359570312500000 := by rw [show (17 : ℕ) = 12 + 5 from rfl, aSeq_add_five, a_eq_16, a_eq_15, a_eq_14, a_eq_13, a_eq_12]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_18 : aSeq 18 = 32864400398330790973850008696950606006015722445400168576120848534610432121897903680570483518928741200074188729710937500000000 := by rw [show (18 : ℕ) = 13 + 5 from rfl, aSeq_add_five, a_eq_17, a_eq_16, a_eq_15, a_eq_14, a_eq_13]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_19 : aSeq 19 = 180410330563307374428036741582175933831865992851589077742782588204609959329818673111423039713927874068887816166658885664062500000000 := by rw [show (19 : ℕ) = 14 + 5 from rfl, aSeq_add_five, a_eq_18, a_eq_17, a_eq_16, a_eq_15, a_eq_14]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_20 : aSeq 20 = 969738544085407243811819743683185152662340501730161356727976010221577228335501947748870156793810397072248955251838387716353334960937500000 := by rw [show (20 : ℕ) = 15 + 5 from rfl, aSeq_add_five, a_eq_19, a_eq_18, a_eq_17, a_eq_16, a_eq_15]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_21 : aSeq 21 = 5108443206941638364376854811925509122533905791520683052661907790140192517610110587951611385625277485424510546141758809276350129779052734375000000 := by rw [show (21 : ℕ) = 16 + 5 from rfl, aSeq_add_five, a_eq_20, a_eq_19, a_eq_18, a_eq_17, a_eq_16]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_22 : aSeq 22 = 26398295483228240392659347943255883118607603658667362300069123749838972516163418958338251560082344965629743503980322668040039639908637766113281250000000 := by rw [show (22 : ℕ) = 17 + 5 from rfl, aSeq_add_five, a_eq_21, a_eq_20, a_eq_19, a_eq_18, a_eq_17]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_23 : aSeq 23 = 133961394580991961299753429910167059103639736984146600595727171511612893712561902825616962403789068646065462396543219187527137979843598927256665039062500000000 := by rw [show (23 : ℕ) = 18 + 5 from rfl, aSeq_add_five, a_eq_22, a_eq_21, a_eq_20, a_eq_19, a_eq_18]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_24 : aSeq 24 = 668381151776599277891200483428533494012555691548034449250177250129142645457628604953917368775158845902098144462239715983699437061306974504713374211578369140625000000 := by rw [show (24 : ℕ) = 19 + 5 from rfl, aSeq_add_five, a_eq_23, a_eq_22, a_eq_21, a_eq_20, a_eq_19]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_25 : aSeq 25 = 3283114557266899755407095268229076946422646869014871701330975217328243006339669767330559737743840968912301666513701707888004956542190860417597140052877764074707031250000000 := by rw [show (25 : ℕ) = 20 + 5 from rfl, aSeq_add_five, a_eq_24, a_eq_23, a_eq_22, a_eq_21, a_eq_20]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_26 : aSeq 26 = 15898259299235791914834942941516028951085550463655216461658820972458495136931193168530450987328951886492577675280801671694177961699440338896204869591124798124356689453125000000000 := by rw [show (26 : ℕ) = 21 + 5 from rfl, aSeq_add_five, a_eq_25, a_eq_24, a_eq_23, a_eq_22, a_eq_21]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_27 : aSeq 27 = 75981438469997636581933294358708562771839832235235942387525931565112353713657785741869329033282541985008913279610624870027630385495122131175274553916612304284337632524414062500000000000 := by rw [show (27 : ℕ) = 22 + 5 from rfl, aSeq_add_five, a_eq_26, a_eq_25, a_eq_24, a_eq_23, a_eq_22]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_28 : aSeq 28 = 358580001120864473489865261628280479581153914882501348290354705215295917181563824810514733773608914571692530341213539821412466587947549161416175546872587574200561282422765684509277343750000000 := by rw [show (28 : ℕ) = 23 + 5 from rfl, aSeq_add_five, a_eq_27, a_eq_26, a_eq_25, a_eq_24, a_eq_23]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_29 : aSeq 29 = 1669861189889005891011275794502478852852987976920831176899509213203085644405721364853389567505887004758813085646936824410315004496850675673156125743861801590243722341117864401040390014648437500000000 := by rw [show (29 : ℕ) = 24 + 5 from rfl, aSeq_add_five, a_eq_28, a_eq_27, a_eq_26, a_eq_25, a_eq_24]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_30 : aSeq 30 = 7652320991575239048913607031078716613044425919295076172326171136369267504193179918843106512979395104886110167543452417263212621486877733025627844913518035742847632515361157303696705313812255859375000000000 := by rw [show (30 : ℕ) = 25 + 5 from rfl, aSeq_add_five, a_eq_29, a_eq_28, a_eq_27, a_eq_26, a_eq_25]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_31 : aSeq 31 = 34305397673511458447364972117262141867406319526814604926742854555451980105962960023678661205433871943042495949199123778250779349251437041442531640101839837665297611997741389635156235816630540466308593750000000000 := by rw [show (31 : ℕ) = 26 + 5 from rfl, aSeq_add_five, a_eq_30, a_eq_29, a_eq_28, a_eq_27, a_eq_26]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_32 : aSeq 32 = 148868537083921287629696569693751458373531626303835400262864842554915345602203154481111283298381088916327267363109303392975088728256782502652897567580473546817293453441224035828488363001326006196033096313476562500000000 := by rw [show (32 : ℕ) = 27 + 5 from rfl, aSeq_add_five, a_eq_31, a_eq_30, a_eq_29, a_eq_28, a_eq_27]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_33 : aSeq 33 = 614322796937074744920009417138475519108882863202382340583256444164570296218959702990362890226937402887019216499072505519916778622377070971032034678315664261540236153976399594753569397478942288846239673816680908203125000000000 := by rw [show (33 : ℕ) = 28 + 5 from rfl, aSeq_add_five, a_eq_32, a_eq_31, a_eq_30, a_eq_29, a_eq_28]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_34 : aSeq 34 = 2338475020728668029647617747271627772020749270171701708063804996335623272335787343010612021153815805287888879240689878829618494892360540568050348643577386258207490647051205350440653854844231738339753404125930480957031250000000000000 := by rw [show (34 : ℕ) = 29 + 5 from rfl, aSeq_add_five, a_eq_33, a_eq_32, a_eq_31, a_eq_30, a_eq_29]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_35 : aSeq 35 = 7753448085634170515018111212998670523583322723275908281128393040304110492353436156311355785930523992630068096976089675375977210981426406420907475253286733815529168596783616845896679953687054605086529919682384772244110107421875000000000000 := by rw [show (35 : ℕ) = 30 + 5 from rfl, aSeq_add_five, a_eq_34, a_eq_33, a_eq_32, a_eq_31, a_eq_30]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_36 : aSeq 36 = 19597980960007969127152541582332691584187205381925388159114252314261730639381028328383533416292191136403229035546119203212331621375930570172774521426936890149768197131517289999967216245465547542975024609376325037030702752590179443359375000000000 := by rw [show (36 : ℕ) = 31 + 5 from rfl, aSeq_add_five, a_eq_35, a_eq_34, a_eq_33, a_eq_32, a_eq_31]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_37 : aSeq 37 = 22910783789225228871478191245920565408058826417621448480658553486428384221382535387259884390088685586764471669318972546928778950579588227654092187399467901300996489384151778621603438847162216763732436007836756359255099054862814903259277343750000000000 := by rw [show (37 : ℕ) = 32 + 5 from rfl, aSeq_add_five, a_eq_36, a_eq_35, a_eq_34, a_eq_33, a_eq_32]; norm_num [K1, K2, K3, K4, K5]
private lemma a_eq_38 : aSeq 38 = -8586688135499133613534762029863945676714046948949967884741284230533337859276790714745736212256260766419308396266975178356237610329962747701220086291529806380820187620413501695748508046753328996948613157502475733012624540121866515951156616210937500000000000 := by rw [show (38 : ℕ) = 33 + 5 from rfl, aSeq_add_five, a_eq_37, a_eq_36, a_eq_35, a_eq_34, a_eq_33]; norm_num [K1, K2, K3, K4, K5]

lemma aSeq_38_neg : aSeq 38 < 0 := by
  rw [a_eq_38]
  norm_num

private def qCoeff66_5 (j : ℕ) : ℚ :=
  if j = 0 then 1
  else if j = 1 then -5 / 71
  else if j = 2 then 1 / 497
  else if j = 3 then -1 / 34293
  else if j = 4 then 1 / 4663848
  else if j = 5 then -1 / 1562389080
  else 0

private lemma qPade_66_5_eq :
    qPade 66 5 =
      PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 +
      PowerSeries.C (-5 / 71 : ℚ) * PowerSeries.X ^ 1 +
      PowerSeries.C (1 / 497 : ℚ) * PowerSeries.X ^ 2 +
      PowerSeries.C (-1 / 34293 : ℚ) * PowerSeries.X ^ 3 +
      PowerSeries.C (1 / 4663848 : ℚ) * PowerSeries.X ^ 4 +
      PowerSeries.C (-1 / 1562389080 : ℚ) * PowerSeries.X ^ 5 := by
  unfold qPade
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h0 : ((((Nat.factorial 71 * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial 71 * Nat.factorial 5 * Nat.factorial 0 : ℕ) : ℚ)) * (-1 : ℚ) ^ 0) = 1 := by
    have h71 : (Nat.factorial 71 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 71)
    have h5 : (Nat.factorial 5 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 5)
    simp only [Nat.factorial_zero, mul_one, pow_zero, Nat.cast_mul]
    field_simp [h71, h5]
  have h1 : ((((Nat.factorial 70 * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial 71 * Nat.factorial 4 * Nat.factorial 1 : ℕ) : ℚ)) * (-1 : ℚ) ^ 1) = -5 / 71 := by
    have h70 : (Nat.factorial 70 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 70)
    have h4 : (Nat.factorial 4 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 4)
    have hf71 : (Nat.factorial 71 : ℚ) = 71 * (Nat.factorial 70 : ℚ) := by
      exact_mod_cast Nat.factorial_succ 70
    have hf5 : (Nat.factorial 5 : ℚ) = 5 * (Nat.factorial 4 : ℚ) := by
      exact_mod_cast Nat.factorial_succ 4
    simp only [Nat.cast_mul, Nat.factorial_one, mul_one, hf71, hf5]
    field_simp [h70, h4]
  have h2 : ((((Nat.factorial 69 * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial 71 * Nat.factorial 3 * Nat.factorial 2 : ℕ) : ℚ)) * (-1 : ℚ) ^ 2) = 1 / 497 := by
    have h69 : (Nat.factorial 69 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 69)
    have h3 : (Nat.factorial 3 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 3)
    have hf71 : (Nat.factorial 71 : ℚ) = 71 * (70 * (Nat.factorial 69 : ℚ)) := by
      have a := Nat.factorial_succ 70
      have b := Nat.factorial_succ 69
      rw [b] at a
      exact_mod_cast a
    have hf5 : (Nat.factorial 5 : ℚ) = 5 * (4 * (Nat.factorial 3 : ℚ)) := by
      have a := Nat.factorial_succ 4
      have b := Nat.factorial_succ 3
      rw [b] at a
      exact_mod_cast a
    have hf2 : (Nat.factorial 2 : ℚ) = 2 := by decide
    simp only [Nat.cast_mul, hf71, hf5, hf2]
    field_simp [h69, h3]
    norm_num
  have h3 : ((((Nat.factorial 68 * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial 71 * Nat.factorial 2 * Nat.factorial 3 : ℕ) : ℚ)) * (-1 : ℚ) ^ 3) = -1 / 34293 := by
    have h68 : (Nat.factorial 68 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 68)
    have hf71 : (Nat.factorial 71 : ℚ) = 71 * (70 * (69 * (Nat.factorial 68 : ℚ))) := by
      have a := Nat.factorial_succ 70
      have b := Nat.factorial_succ 69
      have c := Nat.factorial_succ 68
      rw [c] at b; rw [b] at a
      exact_mod_cast a
    have hf5 : (Nat.factorial 5 : ℚ) = 120 := by decide
    have hf2 : (Nat.factorial 2 : ℚ) = 2 := by decide
    have hf3 : (Nat.factorial 3 : ℚ) = 6 := by decide
    simp only [Nat.cast_mul, hf71, hf5, hf2, hf3]
    field_simp [h68]
    norm_num
  have h4 : ((((Nat.factorial 67 * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial 71 * Nat.factorial 1 * Nat.factorial 4 : ℕ) : ℚ)) * (-1 : ℚ) ^ 4) = 1 / 4663848 := by
    have h67 : (Nat.factorial 67 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 67)
    have hf71 : (Nat.factorial 71 : ℚ) = 71 * (70 * (69 * (68 * (Nat.factorial 67 : ℚ)))) := by
      have a := Nat.factorial_succ 70
      have b := Nat.factorial_succ 69
      have c := Nat.factorial_succ 68
      have d := Nat.factorial_succ 67
      rw [d] at c; rw [c] at b; rw [b] at a
      exact_mod_cast a
    have hf5 : (Nat.factorial 5 : ℚ) = 120 := by decide
    have hf1 : (Nat.factorial 1 : ℚ) = 1 := by decide
    have hf4 : (Nat.factorial 4 : ℚ) = 24 := by decide
    simp only [Nat.cast_mul, hf71, hf5, hf1, hf4]
    field_simp [h67]
    norm_num
  have h5 : ((((Nat.factorial 66 * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial 71 * Nat.factorial 0 * Nat.factorial 5 : ℕ) : ℚ)) * (-1 : ℚ) ^ 5) = -1 / 1562389080 := by
    have h66 : (Nat.factorial 66 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 66)
    have hf71 : (Nat.factorial 71 : ℚ) = 71 * (70 * (69 * (68 * (67 * (Nat.factorial 66 : ℚ))))) := by
      have a := Nat.factorial_succ 70
      have b := Nat.factorial_succ 69
      have c := Nat.factorial_succ 68
      have d := Nat.factorial_succ 67
      have e := Nat.factorial_succ 66
      rw [e] at d; rw [d] at c; rw [c] at b; rw [b] at a
      exact_mod_cast a
    have hf5 : (Nat.factorial 5 : ℚ) = 120 := by decide
    have hf0 : (Nat.factorial 0 : ℚ) = 1 := by decide
    simp only [Nat.cast_mul, hf71, hf5, hf0]
    field_simp [h66]
    norm_num
  change
    PowerSeries.C _ * PowerSeries.X ^ 0 +
    PowerSeries.C _ * PowerSeries.X ^ 1 +
    PowerSeries.C _ * PowerSeries.X ^ 2 +
    PowerSeries.C _ * PowerSeries.X ^ 3 +
    PowerSeries.C _ * PowerSeries.X ^ 4 +
    PowerSeries.C _ * PowerSeries.X ^ 5 = _
  rw [h0, h1, h2, h3, h4, h5]

private lemma coeff_qPade_66_5 (j : ℕ) :
    PowerSeries.coeff j (qPade 66 5) = qCoeff66_5 j := by
  rw [qPade_66_5_eq]
  simp only [map_add, PowerSeries.coeff_C_mul_X_pow, qCoeff66_5]
  rcases j with _ | _ | _ | _ | _ | _ | j
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have h0 : j + 6 ≠ 0 := by omega
    have h1 : j + 6 ≠ 1 := by omega
    have h2 : j + 6 ≠ 2 := by omega
    have h3 : j + 6 ≠ 3 := by omega
    have h4 : j + 6 ≠ 4 := by omega
    have h5 : j + 6 ≠ 5 := by omega
    change ((((if j + 6 = 0 then (1 : ℚ) else 0) +
      (if j + 6 = 1 then (-5 / 71 : ℚ) else 0)) +
      (if j + 6 = 2 then (1 / 497 : ℚ) else 0)) +
      (if j + 6 = 3 then (-1 / 34293 : ℚ) else 0)) +
      (if j + 6 = 4 then (1 / 4663848 : ℚ) else 0) +
      (if j + 6 = 5 then (-1 / 1562389080 : ℚ) else 0) =
      if j + 6 = 0 then 1
      else if j + 6 = 1 then -5 / 71
      else if j + 6 = 2 then 1 / 497
      else if j + 6 = 3 then -1 / 34293
      else if j + 6 = 4 then 1 / 4663848
      else if j + 6 = 5 then -1 / 1562389080
      else 0
    simp only [h0, h1, h2, h3, h4, h5, ↓reduceIte, add_zero]

lemma isUnit_qPade_66_5 : IsUnit (qPade 66 5) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_qPade_66_5]
  simp [qCoeff66_5]

lemma coeff_mul_qPade (c : PowerSeries ℚ) (hc : qPade 66 5 * c = 1) :
    ∀ n : ℕ, PowerSeries.coeff n c = (aSeq n : ℚ) / (D : ℚ) ^ n := by
  have hD : (D : ℚ) ≠ 0 := by norm_num [D]
  have hK1 : (K1 : ℚ) = (5 / 71 : ℚ) * (D : ℚ) := by norm_num [K1, D]
  have hK2 : (K2 : ℚ) = (-1 / 497 : ℚ) * (D : ℚ) ^ 2 := by norm_num [K2, D]
  have hK3 : (K3 : ℚ) = (1 / 34293 : ℚ) * (D : ℚ) ^ 3 := by norm_num [K3, D]
  have hK4 : (K4 : ℚ) = (-1 / 4663848 : ℚ) * (D : ℚ) ^ 4 := by norm_num [K4, D]
  have hK5 : (K5 : ℚ) = (1 / 1562389080 : ℚ) * (D : ℚ) ^ 5 := by norm_num [K5, D]
  have hmul : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1), qCoeff66_5 i * PowerSeries.coeff (n - i) c) =
        if n = 0 then 1 else 0 := by
    intro n
    have h := congrArg (PowerSeries.coeff n) hc
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j c)] at h
    convert h using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_qPade_66_5]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hm := hmul n
    rcases n with _ | _ | _ | _ | _ | n
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_self,
        qCoeff66_5, ↓reduceIte, one_mul] at hm
      rw [hm, aSeq_zero]; norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, qCoeff66_5] at hm
      norm_num at hm
      rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hm
      have h0 := ih 0 (by omega)
      have hstep : PowerSeries.coeff 1 c = (5 / 71 : ℚ) * PowerSeries.coeff 0 c := by linarith
      change PowerSeries.coeff 1 c = (aSeq 1 : ℚ) / (D : ℚ) ^ 1
      rw [hstep, h0, aSeq_one]
      simp only [Int.cast_mul, hK1, pow_zero, div_one, pow_one]
      field_simp [hD]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, qCoeff66_5] at hm
      norm_num at hm
      rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hm
      have h0 := ih 0 (by omega)
      have h1 := ih 1 (by omega)
      have hstep : PowerSeries.coeff 2 c =
          (5 / 71 : ℚ) * PowerSeries.coeff 1 c - (1 / 497 : ℚ) * PowerSeries.coeff 0 c := by linarith
      change PowerSeries.coeff 2 c = (aSeq 2 : ℚ) / (D : ℚ) ^ 2
      rw [hstep, h1, h0, aSeq_two]
      simp only [Int.cast_add, Int.cast_mul, hK1, hK2, pow_zero, div_one, pow_one]
      field_simp [hD]
      ring
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, qCoeff66_5] at hm
      norm_num at hm
      rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hm
      have h0 := ih 0 (by omega)
      have h1 := ih 1 (by omega)
      have h2 := ih 2 (by omega)
      have hstep : PowerSeries.coeff 3 c =
          (5 / 71 : ℚ) * PowerSeries.coeff 2 c - (1 / 497 : ℚ) * PowerSeries.coeff 1 c +
          (1 / 34293 : ℚ) * PowerSeries.coeff 0 c := by linarith
      change PowerSeries.coeff 3 c = (aSeq 3 : ℚ) / (D : ℚ) ^ 3
      rw [hstep, h2, h1, h0, aSeq_three]
      simp only [Int.cast_add, Int.cast_mul, hK1, hK2, hK3, pow_zero, div_one, pow_one]
      field_simp [hD]
      ring
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, qCoeff66_5] at hm
      norm_num at hm
      rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hm
      have h0 := ih 0 (by omega)
      have h1 := ih 1 (by omega)
      have h2 := ih 2 (by omega)
      have h3 := ih 3 (by omega)
      have hstep : PowerSeries.coeff 4 c =
          (5 / 71 : ℚ) * PowerSeries.coeff 3 c - (1 / 497 : ℚ) * PowerSeries.coeff 2 c +
          (1 / 34293 : ℚ) * PowerSeries.coeff 1 c - (1 / 4663848 : ℚ) * PowerSeries.coeff 0 c := by
        linarith
      change PowerSeries.coeff 4 c = (aSeq 4 : ℚ) / (D : ℚ) ^ 4
      rw [hstep, h3, h2, h1, h0, aSeq_four]
      simp only [Int.cast_add, Int.cast_mul, hK1, hK2, hK3, hK4, pow_zero, div_one, pow_one]
      field_simp [hD]
      ring
    · have hzero : ∀ i ∈ Finset.range (n + 5 + 1), i ∉ Finset.range 6 →
          qCoeff66_5 i * PowerSeries.coeff (n + 5 - i) c = 0 := by
        intro i _ hi
        rw [Finset.mem_range] at hi
        have : qCoeff66_5 i = 0 := by unfold qCoeff66_5; split_ifs <;> first | omega | rfl
        rw [this, zero_mul]
      rw [← Finset.sum_subset (Finset.range_mono (by omega : 6 ≤ n + 5 + 1)) hzero] at hm
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hm
      have hs0 : n + 5 - 0 = n + 5 := by omega
      have hs1 : n + 5 - 1 = n + 4 := by omega
      have hs2 : n + 5 - 2 = n + 3 := by omega
      have hs3 : n + 5 - 3 = n + 2 := by omega
      have hs4 : n + 5 - 4 = n + 1 := by omega
      have hs5 : n + 5 - 5 = n := by omega
      rw [hs0, hs1, hs2, hs3, hs4, hs5] at hm
      have hne : n + 5 ≠ 0 := by omega
      rw [if_neg hne] at hm
      simp only [qCoeff66_5] at hm
      norm_num at hm
      have h4 := ih (n + 4) (by omega)
      have h3 := ih (n + 3) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have hstep : PowerSeries.coeff (n + 5) c =
          (5 / 71 : ℚ) * PowerSeries.coeff (n + 4) c -
          (1 / 497 : ℚ) * PowerSeries.coeff (n + 3) c +
          (1 / 34293 : ℚ) * PowerSeries.coeff (n + 2) c -
          (1 / 4663848 : ℚ) * PowerSeries.coeff (n + 1) c +
          (1 / 1562389080 : ℚ) * PowerSeries.coeff n c := by linarith
      rw [hstep, h4, h3, h2, h1, h0, aSeq_add_five]
      simp only [Int.cast_add, Int.cast_mul, hK1, hK2, hK3, hK4, hK5]
      have hp5 : (D : ℚ) ^ (n + 5) = (D : ℚ) ^ n * (D : ℚ) ^ 5 := by ring
      have hp4 : (D : ℚ) ^ (n + 4) = (D : ℚ) ^ n * (D : ℚ) ^ 4 := by ring
      have hp3 : (D : ℚ) ^ (n + 3) = (D : ℚ) ^ n * (D : ℚ) ^ 3 := by ring
      have hp2 : (D : ℚ) ^ (n + 2) = (D : ℚ) ^ n * (D : ℚ) ^ 2 := by ring
      have hp1 : (D : ℚ) ^ (n + 1) = (D : ℚ) ^ n * (D : ℚ) := by ring
      rw [hp5, hp4, hp3, hp2, hp1]
      have hDn : (D : ℚ) ^ n ≠ 0 := pow_ne_zero n hD
      field_simp [hDn, hD]
      ring

end OMA.P_arxiv_2610_39051

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_39051.main) := by
  intro h
  obtain ⟨u, hu⟩ := OMA.P_arxiv_2610_39051.isUnit_qPade_66_5
  let c : PowerSeries ℚ := ↑(u⁻¹)
  have hmul : OMA.S_arxiv_2610_39051.qPade 66 5 * c = 1 := by
    rw [← hu]
    exact u.mul_inv
  have hpos := h 66 5 ⟨2, rfl⟩ c hmul 38
  have heq := OMA.P_arxiv_2610_39051.coeff_mul_qPade c hmul 38
  rw [heq] at hpos
  have hnum : (OMA.P_arxiv_2610_39051.aSeq 38 : ℚ) < 0 := by
    exact_mod_cast OMA.P_arxiv_2610_39051.aSeq_38_neg
  have hden : (0 : ℚ) < (OMA.P_arxiv_2610_39051.D : ℚ) ^ 38 := by
    unfold OMA.P_arxiv_2610_39051.D
    positivity
  have hneg : (OMA.P_arxiv_2610_39051.aSeq 38 : ℚ) / (OMA.P_arxiv_2610_39051.D : ℚ) ^ 38 < 0 :=
    div_neg_of_neg_of_pos hnum hden
  linarith
