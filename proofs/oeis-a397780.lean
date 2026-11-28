import OMAStatements.S_oeis_a397780

/-! # Decimal support certificates for OEIS A397780

Each row supplies a digit mask and a nonnegative witness. A witness need not
be minimal; the least eligible integer with the same support is a sequence term.
-/
namespace DigitSupports
open OMA.S_oeis_a397780

/-- Read at most the given number of decimal digits, least significant first. -/
private def readDigits : ℕ → ℕ → List ℕ
  | 0,_ => []
  | k+1,n => if n < 10 then [n] else n%10 :: readDigits k (n/10)

private theorem readDigits_eq (k n : ℕ) (hk : n<10^k) (hpos : 0<k) :
    readDigits k n=decimalDigits n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    by_cases h : n<10
    · by_cases hn : n=0
      · simp [readDigits,decimalDigits,hn]
      · simp [readDigits,h,decimalDigits,hn]
    · have hn : n≠0 := by omega
      have hq : n/10≠0 := by omega
      have hk' : 0<k := by
        by_contra! he
        simp [show k=0 by omega] at hk
        omega
      have hbound : n/10<10^k := (Nat.div_lt_iff_lt_mul (by decide : 0<10)).mpr
        (by simpa only [pow_succ] using hk)
      simp only [readDigits,if_neg h,ih _ hbound hk',decimalDigits,if_neg hq,if_neg hn]
      exact (Nat.digits_eq_cons_digits_div (by decide : 1<10) hn).symm

private def fastDigits (n : ℕ) := readDigits (n.log2+1) n
private theorem fastDigits_eq (n : ℕ) : fastDigits n=decimalDigits n :=
  readDigits_eq _ _ (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_left (by decide : 2≤10) _)) (by omega)

private def word (n : ℕ) := fastDigits n ++ fastDigits (n*n)
private theorem word_eq (n : ℕ) : word n=combined n := by simp [word,combined,fastDigits_eq]

/-- The bit of weight 2^d records that d occurs. -/
def mask (s : Finset ℕ) : ℕ := (((List.range 10).filter (fun d => d∈s)).map (2^·)).sum

private def seen (w : List ℕ) := (List.range 10).filter (fun d => w.contains d)

def rowOK (r : ℕ × ℕ) : Bool :=
  let w := word r.2
  let ds := seen w
  ((ds.map (2^·)).sum==r.1) && ds.all fun d => decide (d ≤ w.count d)

def rowHasSize (k : ℕ) (r : ℕ × ℕ) : Bool := (seen (word r.2)).length == k

private theorem decimal_lt {n d : ℕ} (h : d∈decimalDigits n) : d<10 := by
  by_cases hn : n=0
  · simp [hn,decimalDigits] at h
    omega
  · apply Nat.digits_lt_base (by decide : 1<10)
    simpa [decimalDigits,hn] using h

private theorem combined_lt {n d : ℕ} (h : d∈combined n) : d<10 := by
  rcases List.mem_append.mp h with h|h <;> exact decimal_lt h

private theorem seen_mem {n d : ℕ} : d∈seen (combined n) ↔ d∈support n := by
  simp only [seen,List.mem_filter,List.mem_range,List.contains_iff_mem,support,List.mem_toFinset]
  exact ⟨And.right, fun h => ⟨combined_lt h,h⟩⟩

theorem row_sound {r : ℕ×ℕ} (h : rowOK r=true) :
    mask (support r.2)=r.1 ∧ eligible r.2 := by
  simp only [rowOK,word_eq,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at h
  refine ⟨?_, fun d hd => h.2 d (seen_mem.mpr hd)⟩
  simpa [mask,seen,support,List.contains_iff_mem] using h.1

theorem size_sound {r : ℕ×ℕ} {k : ℕ} (h : rowHasSize k r=true) :
    (support r.2).card=k := by
  have hs : (seen (combined r.2)).toFinset=support r.2 := by
    ext d
    simpa only [List.mem_toFinset] using (seen_mem (n:=r.2) (d:=d))
  have hn : (seen (combined r.2)).Nodup := List.Nodup.filter _ List.nodup_range
  simpa only [rowHasSize,word_eq,beq_iff_eq,←List.toFinset_card_of_nodup hn,hs] using h

private noncomputable def first (s : Finset ℕ) : ℕ := sInf {n | eligible n ∧ support n=s}

private theorem first_spec {n : ℕ} (h : eligible n) :
    isTerm (first (support n)) ∧ support (first (support n))=support n := by
  let A := {m | eligible m ∧ support m=support n}
  have hf : first (support n)∈A := Nat.sInf_mem (⟨n,h,rfl⟩ : A.Nonempty)
  refine ⟨⟨hf.1, ?_⟩,hf.2⟩
  intro m hm he hs
  exact (Nat.not_le_of_gt hm) (Nat.sInf_le (show m∈A from ⟨he,hs.trans hf.2⟩))

theorem finite_terms : {n | isTerm n}.Finite := by
  have hi : Set.InjOn support {n | isTerm n} := by
    intro a ha b hb he
    rcases lt_trichotomy a b with h|h|h
    · exact False.elim (hb.2 a h ha.1 he)
    · exact h
    · exact False.elim (ha.2 b h hb.1 he.symm)
  apply Set.Finite.of_finite_image (f:=support) _ hi
  apply (Finset.finite_toSet (Finset.range 10).powerset).subset
  rintro _ ⟨n,_,rfl⟩
  apply Finset.mem_powerset.mpr
  intro d hd
  exact Finset.mem_range.mpr (combined_lt (List.mem_toFinset.mp hd))

private theorem table_bound (rows : List (ℕ×ℕ)) (P : ℕ → Prop)
    (hv : rows.all rowOK=true) (hn : (rows.map Prod.fst).Nodup)
    (hP : ∀ r∈rows, P (first (support r.2))) :
    rows.length ≤ {n | isTerm n ∧ P n}.ncard := by
  let w (i : Fin rows.length) := first (support rows[i.val].2)
  have hj (i : Fin rows.length) := row_sound (List.all_eq_true.mp hv _ (List.getElem_mem (n:=i.val) i.isLt))
  have hfirst (i : Fin rows.length) := first_spec (hj i).2
  have hinj : Function.Injective w := by
    intro i j he
    have hm : rows[i.val].1 = rows[j.val].1 := by
      rw [←(hj i).1,←(hj j).1,←(hfirst i).2,←(hfirst j).2]
      exact congrArg (fun m => mask (support m)) he
    let i' : Fin (rows.map Prod.fst).length := ⟨i.val,by simp⟩
    let j' : Fin (rows.map Prod.fst).length := ⟨j.val,by simp⟩
    have eq := (List.nodup_iff_injective_getElem.mp hn) (a₁:=i') (a₂:=j') (by simpa [i',j'] using hm)
    exact Fin.ext (congrArg (fun t : Fin (rows.map Prod.fst).length => t.val) eq)
  have hfin : {n | isTerm n ∧ P n}.Finite := finite_terms.subset (fun _ h => h.1)
  have hb := Set.ncard_le_ncard_of_injOn (s:=Set.univ) (t:={n | isTerm n ∧ P n}) w
    (fun i _ => ⟨(hfirst i).1,hP _ (List.getElem_mem (n:=i.val) i.isLt)⟩) hinj.injOn hfin
  simpa using hb

theorem term_count_ge (rows : List (ℕ×ℕ)) (hv : rows.all rowOK=true)
    (hn : (rows.map Prod.fst).Nodup) :
    rows.length ≤ {n | isTerm n}.ncard := by
  simpa using table_bound rows (fun _ => True) hv hn (fun _ _ => trivial)

theorem term_count_ge_size (rows : List (ℕ×ℕ)) (k : ℕ) (hv : rows.all rowOK=true)
    (hn : (rows.map Prod.fst).Nodup) (hs : rows.all (rowHasSize k)=true) :
    rows.length ≤ {n | isTerm n ∧ (support n).card=k}.ncard := by
  apply table_bound rows _ hv hn
  intro r hr
  have he := (first_spec (row_sound (List.all_eq_true.mp hv _ hr)).2).2
  exact (congrArg Finset.card he).trans (size_sound (List.all_eq_true.mp hs _ hr))

end DigitSupports

namespace DigitSupports
open OMA.S_oeis_a397780

private def block00 : List (ℕ × ℕ) :=
  [(1, 0),
   (2, 1),
   (3, 10),
   (7, 1011),
   (15, 10010111),
   (23, 201102),
   (31, 321312),
   (37, 505),
   (39, 5015),
   (43, 550501),
   (45, 235235),
   (46, 33515),
   (47, 335150),
   (53, 452245),
   (55, 1025405),
   (59, 1055050451),
   (60, 2354235),
   (61, 23542350),
   (62, 21341332),
   (63, 213413320),
   (78, 33336363361),
   (79, 333363633610),
   (86, 6664414162),
   (87, 66644141620),
   (91, 6634306),
   (93, 2462442),
   (94, 16316132),
   (95, 163161320),
   (101, 256255),
   (102, 5162525125),
   (103, 51625251250),
   (107, 10056666)]

set_option maxRecDepth 100000 in
private theorem block00_valid : block00.all rowOK = true := by decide +kernel

private def block01 : List (ℕ × ℕ) :=
  [(108, 23523653335),
   (109, 235236533350),
   (110, 3356566),
   (111, 33565660),
   (114, 66645451116),
   (115, 666454511160),
   (116, 25625465),
   (117, 256254650),
   (118, 46524666),
   (119, 465246660),
   (121, 60443656),
   (122, 64463566),
   (123, 644635660),
   (124, 2333526656),
   (125, 23335266560),
   (126, 46425666),
   (127, 66533025),
   (143, 37113030101),
   (150, 2777177421),
   (151, 27771774210),
   (155, 10037304071),
   (157, 2702734302),
   (158, 377774171),
   (159, 3777741710),
   (165, 5002775005005),
   (167, 150700755),
   (171, 733315553751),
   (173, 5777000755),
   (174, 275232115),
   (175, 2752321150),
   (179, 71770575501),
   (181, 474402545)]

set_option maxRecDepth 100000 in
private theorem block01_valid : block01.all rowOK = true := by decide +kernel

private def block02 : List (ℕ × ℕ) :=
  [(182, 2777512271),
   (183, 27775122710),
   (186, 7357537313175771),
   (187, 73575373131757710),
   (188, 7372744235),
   (189, 73727442350),
   (190, 2734177312),
   (191, 7437454751),
   (199, 77627776),
   (203, 17636076),
   (205, 27760263026),
   (206, 266671376),
   (207, 2666713760),
   (211, 7747064074),
   (213, 264664074),
   (214, 1664766424),
   (215, 16647664240),
   (217, 63776467006),
   (218, 646331776),
   (219, 6463317760),
   (220, 4727236262),
   (221, 47272362620),
   (222, 3662612144),
   (223, 20777643376),
   (227, 717757666),
   (229, 756750076),
   (230, 266752275),
   (231, 2667522750),
   (233, 750757666),
   (234, 577637756),
   (235, 5776377560),
   (236, 5266666275)]

set_option maxRecDepth 100000 in
private theorem block02_valid : block02.all rowOK = true := by decide +kernel

private def block03 : List (ℕ × ℕ) :=
  [(237, 52666662750),
   (238, 75317576725),
   (239, 7250356731),
   (241, 77754457474),
   (242, 6675751776),
   (243, 66757517760),
   (244, 744766725),
   (245, 7447667250),
   (246, 162626774475),
   (247, 74246576774),
   (248, 6676476434),
   (249, 66764764340),
   (250, 561671767534),
   (251, 65656513346),
   (252, 7574544526),
   (253, 666736567526),
   (254, 64471523526),
   (255, 27700475746),
   (271, 1838828111),
   (275, 10004441414401),
   (277, 20020202002),
   (279, 102020022),
   (282, 338841141),
   (283, 3388411410),
   (285, 2882438),
   (286, 1218312128),
   (287, 12183121280),
   (293, 500000508805),
   (295, 500881805),
   (299, 3883501133151),
   (301, 2833528205),
   (302, 358123385)]

set_option maxRecDepth 100000 in
private theorem block03_valid : block03.all rowOK = true := by decide +kernel

private def block04 : List (ℕ × ℕ) :=
  [(303, 3581233850),
   (307, 104154155488),
   (309, 242504805),
   (310, 1552821888),
   (311, 15528218880),
   (313, 5480500300888),
   (314, 3848833388),
   (315, 38488333880),
   (316, 288588885),
   (317, 2885888850),
   (318, 5584425828),
   (319, 53158803112),
   (327, 2611288228101),
   (331, 101888668006),
   (333, 60688288686006),
   (334, 6231868361),
   (335, 62318683610),
   (338, 68444641),
   (339, 684446410),
   (341, 20640886808),
   (342, 6842281668),
   (343, 68422816680),
   (345, 66608038808),
   (346, 431838683844),
   (347, 4318386838440),
   (348, 8262462338),
   (349, 82624623380),
   (350, 18266484838),
   (351, 6214386844),
   (355, 81000068881551),
   (357, 82858680225),
   (358, 81151628615)]

set_option maxRecDepth 100000 in
private theorem block04_valid : block04.all rowOK = true := by decide +kernel

private def block05 : List (ℕ × ℕ) :=
  [(359, 811516286150),
   (361, 80808635063566),
   (362, 18885666156),
   (363, 188856661560),
   (364, 6235588656),
   (365, 62355886560),
   (366, 8156522156),
   (367, 368806562535),
   (369, 6844450648884),
   (370, 64548885884),
   (371, 645488858840),
   (372, 828664865),
   (373, 8286648650),
   (374, 216445486568),
   (375, 806516128888),
   (376, 58854538388),
   (377, 588545383880),
   (378, 558463638466),
   (379, 583685156104),
   (380, 58522348368656),
   (381, 82855685688),
   (382, 485354168482),
   (383, 485415886806),
   (391, 878001780811),
   (398, 878281781311),
   (399, 8782817813110),
   (403, 87800040878),
   (405, 8847478448),
   (406, 14747284878),
   (407, 147472848780),
   (409, 87774340088),
   (410, 87848433878)]

set_option maxRecDepth 100000 in
private theorem block05_valid : block05.all rowOK = true := by decide +kernel

private def block06 : List (ℕ × ℕ) :=
  [(411, 878484338780),
   (412, 882288778),
   (413, 8822887780),
   (414, 878474372841),
   (415, 878873324702),
   (419, 887585775501),
   (421, 2788778555),
   (422, 87851515515),
   (423, 878515155150),
   (427, 8818038777501),
   (428, 2787872885885),
   (429, 27878728858850),
   (430, 11777853587385),
   (431, 887838572705),
   (433, 75875480088),
   (434, 7181558875888),
   (435, 71815588758880),
   (436, 88574425478),
   (437, 885744254780),
   (438, 88174575828),
   (439, 72447071427888),
   (440, 88585753588),
   (441, 885857535880),
   (442, 857773738141),
   (443, 17543875888),
   (444, 88784877585),
   (445, 4873780744248),
   (446, 8577387354482),
   (447, 84351337777405),
   (451, 8160887008776),
   (453, 8786767826),
   (454, 87628868626)]

set_option maxRecDepth 100000 in
private theorem block06_valid : block06.all rowOK = true := by decide +kernel

private def block07 : List (ℕ × ℕ) :=
  [(455, 876288686260),
   (457, 8778773308876),
   (458, 17716768376),
   (459, 177167683760),
   (460, 62267678826),
   (461, 622676788260),
   (462, 8738828218861),
   (463, 87677663181),
   (465, 66787778880474),
   (466, 864741688474),
   (467, 8647416884740),
   (468, 278727226474),
   (469, 2787272264740),
   (470, 27778447846881),
   (471, 88680477618474),
   (472, 684388368376),
   (473, 6843883683760),
   (474, 881671417318474),
   (475, 8870648443478),
   (476, 8734282247378),
   (477, 276887788424),
   (478, 27883388688144),
   (479, 4667728373678),
   (481, 888077060766),
   (482, 817658716816),
   (483, 8176587168160),
   (484, 28786572875),
   (485, 287865728750),
   (486, 766628211881266),
   (487, 287761685688265),
   (488, 887567776756),
   (489, 8875677767560)]

set_option maxRecDepth 100000 in
private theorem block07_valid : block07.all rowOK = true := by decide +kernel

private def block08 : List (ℕ × ℕ) :=
  [(490, 8585853583876),
   (491, 7660717188076),
   (492, 85765837536765),
   (493, 826352378687850),
   (494, 7865225722626),
   (495, 76632305705126),
   (496, 667746775766),
   (497, 6677467757660),
   (498, 8157546678858),
   (499, 84017151676116),
   (500, 88687565456875),
   (501, 88648226478062),
   (502, 65456717666528),
   (503, 870672660524466),
   (504, 8587568565478),
   (505, 8766854487408),
   (506, 5883777346874),
   (507, 875133640471738),
   (508, 747232787446766),
   (509, 88226345446674),
   (510, 572875847447475),
   (511, 887345784751608),
   (527, 3032990923),
   (531, 104900499999),
   (535, 4999299),
   (539, 331949414993),
   (540, 4999932923),
   (541, 49999329230),
   (542, 1394393923),
   (543, 13943939230),
   (549, 50009995),
   (551, 999995505)]

set_option maxRecDepth 100000 in
private theorem block08_valid : block08.all rowOK = true := by decide +kernel

private def block09 : List (ℕ × ℕ) :=
  [(555, 30093111503),
   (557, 50950952203),
   (558, 22932993523),
   (559, 229329935230),
   (563, 995514919499),
   (565, 49994905),
   (566, 2441299229),
   (567, 24412992290),
   (569, 599950493),
   (570, 4399945449143),
   (571, 43999454491430),
   (572, 4999395523),
   (573, 49993955230),
   (574, 95913239511),
   (575, 4939149309345),
   (583, 99961026911),
   (585, 96936063),
   (587, 199909963),
   (589, 9969906036),
   (590, 1291999213),
   (591, 12919992130),
   (595, 44610166946),
   (596, 49999296962),
   (597, 499992969620),
   (598, 2499929292),
   (599, 24999292920),
   (601, 630003940063),
   (602, 13963141969),
   (603, 139631419690),
   (604, 499969236),
   (605, 4999692360),
   (606, 49996931369)]

set_option maxRecDepth 100000 in
private theorem block09_valid : block09.all rowOK = true := by decide +kernel

private def block10 : List (ℕ × ℕ) :=
  [(607, 603691499194),
   (611, 9516599166699),
   (613, 99952965265),
   (614, 511529659619),
   (615, 5115296596190),
   (617, 9953359563),
   (618, 995969663),
   (619, 9959696630),
   (620, 236566259923),
   (621, 2365662599230),
   (622, 263999915366),
   (623, 995339122663),
   (626, 441549165614),
   (627, 4415491656140),
   (628, 49999596925),
   (629, 499995969250),
   (630, 51956669415),
   (631, 9599111946699),
   (632, 96936549634),
   (633, 969365496340),
   (634, 9966515516143),
   (635, 996553619049),
   (636, 99963464593),
   (637, 2539565453563),
   (638, 496624253535),
   (639, 6595010966956),
   (647, 27799279077),
   (653, 3037930277997),
   (654, 17312192177),
   (655, 173121921770),
   (659, 1410947094747),
   (660, 499979277)]

set_option maxRecDepth 100000 in
private theorem block10_valid : block10.all rowOK = true := by decide +kernel

private def block11 : List (ℕ × ℕ) :=
  [(661, 4999792770),
   (662, 4471911777),
   (663, 44719117770),
   (665, 700339044997),
   (666, 9997174339479),
   (667, 99971743394790),
   (668, 49999477277),
   (669, 499994772770),
   (670, 27373339729),
   (671, 949093237743),
   (675, 979775075755000001),
   (677, 22929790577),
   (678, 99755797715),
   (679, 997557977150),
   (681, 5999799955753),
   (683, 1339319959911503),
   (684, 523392775777),
   (685, 5233927757770),
   (686, 5399771993123),
   (687, 959777733295539),
   (689, 747994504997),
   (690, 7719779447479),
   (691, 77197794474790),
   (692, 49957729727),
   (693, 499577297270),
   (694, 97955457222912),
   (695, 9957204472712507),
   (696, 59999477779357),
   (697, 599994777793570),
   (698, 955797777479),
   (699, 979773955757),
   (700, 243359247975773)]

set_option maxRecDepth 100000 in
private theorem block11_valid : block11.all rowOK = true := by decide +kernel

private def block12 : List (ℕ × ℕ) :=
  [(701, 7037970570943),
   (702, 97453543955939),
   (703, 97943727573297),
   (707, 10911906797676),
   (709, 2626799779027),
   (710, 2679172767161),
   (711, 26791727671610),
   (713, 7979960963397),
   (714, 199917399637),
   (715, 1999173996370),
   (716, 9663993676),
   (717, 96639936760),
   (718, 799619767313),
   (719, 996627923137),
   (721, 9697460996007),
   (722, 669174694469),
   (723, 6691746944690),
   (724, 49776497764),
   (725, 497764977640),
   (726, 4794991946776),
   (727, 67946149272747),
   (728, 999973373364),
   (729, 9999733733640),
   (730, 41673969949736),
   (731, 369431964196007),
   (732, 96937737634694),
   (733, 96422739940676),
   (734, 79997779327924),
   (735, 403690963747939),
   (737, 979799957009576),
   (738, 7595756551969),
   (739, 75957565519690)]

set_option maxRecDepth 100000 in
private theorem block12_valid : block12.all rowOK = true := by decide +kernel

private def block13 : List (ℕ × ℕ) :=
  [(740, 962579759277),
   (741, 9625797592770),
   (742, 72799696267619),
   (743, 79199909576966),
   (744, 75999973663),
   (745, 759999736630),
   (746, 193957669957576),
   (747, 3956979976769),
   (748, 5977229265967366),
   (749, 99699336695656),
   (750, 7956927596565),
   (751, 627675677999556),
   (752, 676444969676),
   (753, 6764449696760),
   (754, 76155614497419),
   (755, 9745499174776),
   (756, 54294775294469777),
   (757, 74560092949007297),
   (758, 122444999724762),
   (759, 7476997565976747),
   (760, 7744649375366),
   (761, 739567304547963),
   (762, 676139763596976),
   (763, 95171770534990963),
   (764, 2397444467956773),
   (765, 9729629779734477),
   (766, 7469374652497773),
   (767, 9797576739545063),
   (771, 90099999990009999),
   (775, 8999899901),
   (779, 8999399891),
   (781, 938099083303)]

set_option maxRecDepth 100000 in
private theorem block13_valid : block13.all rowOK = true := by decide +kernel

private def block14 : List (ℕ × ℕ) :=
  [(782, 29988318391),
   (783, 299883183910),
   (785, 9989999048998),
   (787, 444981891991),
   (789, 28999990498),
   (790, 4999891288),
   (791, 49998912880),
   (792, 943394898438),
   (793, 9433948984380),
   (794, 948388891391),
   (795, 9483888913910),
   (796, 49894833228),
   (797, 498948332280),
   (798, 99922214213928),
   (799, 149999938283),
   (803, 9959919585599),
   (805, 2829998095805),
   (806, 22991198589589),
   (807, 229911985895890),
   (809, 583095050833),
   (810, 39993891891),
   (811, 399938918910),
   (812, 599998823823),
   (813, 5999988238230),
   (814, 9238958393339115),
   (815, 5315919393283),
   (817, 98994949845888),
   (818, 9459859859),
   (819, 94598598590),
   (820, 499998585828),
   (821, 4999985858280),
   (822, 4991442558148891)]

set_option maxRecDepth 100000 in
private theorem block14_valid : block14.all rowOK = true := by decide +kernel

private def block15 : List (ℕ × ℕ) :=
  [(823, 94408425945989),
   (824, 93994438583333),
   (825, 939944385833330),
   (826, 5994984449891),
   (827, 4303485910845359),
   (828, 498593882333),
   (829, 499598838354830),
   (830, 4991584914224538),
   (831, 583388599898553),
   (835, 8989919999699),
   (837, 999609968886),
   (838, 299699682886),
   (839, 2996996828860),
   (841, 89999366886),
   (842, 99668911396),
   (843, 996689113960),
   (844, 2939382399236),
   (845, 29393823992360),
   (846, 83199831669883),
   (847, 301369689886),
   (849, 66984960886),
   (850, 6666998199864),
   (851, 66669981998640),
   (852, 94866689886),
   (853, 948666898860),
   (854, 99412684869261),
   (855, 9698804981491908),
   (856, 9484969498633),
   (857, 94849694986330),
   (858, 918394696466688),
   (859, 998408468318996),
   (860, 99824688499338)]

set_option maxRecDepth 100000 in
private theorem block15_valid : block15.all rowOK = true := by decide +kernel

private def block16 : List (ℕ × ℕ) :=
  [(861, 98303934298882),
   (862, 9393241983692128),
   (863, 999446181236609),
   (865, 809869680866),
   (866, 81615658159859),
   (867, 816156581598590),
   (868, 92859692869886),
   (869, 928596928698860),
   (870, 995922529682816),
   (871, 812218111089669),
   (872, 8366599898336),
   (873, 83665998983360),
   (874, 19896185535658869),
   (875, 3159380533538013),
   (876, 996639352358565),
   (877, 599983880285956),
   (878, 1816186385953336),
   (879, 930160693815083),
   (880, 6699895446684),
   (881, 66998954466840),
   (882, 699686965446591616),
   (883, 9480854099661059),
   (884, 94584684625469886),
   (885, 69920666400290098),
   (886, 946481198518484),
   (887, 9465991158469041),
   (888, 68553589985985383),
   (889, 9800859699469934),
   (890, 938943894468386),
   (891, 9688085411166358),
   (892, 99459958694686),
   (893, 8994392524605886)]

set_option maxRecDepth 100000 in
private theorem block16_valid : block16.all rowOK = true := by decide +kernel

private def block17 : List (ℕ × ℕ) :=
  [(894, 83485682394268),
   (895, 6392882913596953),
   (899, 9988987790917),
   (901, 2779800889827),
   (902, 297989811777),
   (903, 2979898117770),
   (905, 998887897083),
   (906, 999889187917),
   (907, 9998891879170),
   (908, 279997839277),
   (909, 2799978392770),
   (910, 889818992177),
   (911, 8883910789911),
   (913, 8998770997978),
   (914, 889887471417),
   (915, 8898874714170),
   (916, 99497978788),
   (917, 994979787880),
   (918, 172892419497788118),
   (919, 2981907900824207),
   (920, 9377837943788),
   (921, 93778379437880),
   (922, 91177398139499143),
   (923, 98989041809878),
   (924, 289792942327772),
   (925, 894300779827872),
   (926, 4997793297978),
   (927, 98893778832378),
   (930, 8919517917891),
   (931, 89195179178910),
   (932, 9797895588277),
   (933, 97978955882770)]

set_option maxRecDepth 100000 in
private theorem block17_valid : block17.all rowOK = true := by decide +kernel

private def block18 : List (ℕ × ℕ) :=
  [(934, 9998927888915),
   (935, 8819880892517717),
   (936, 599898977793583),
   (937, 5998989777935830),
   (938, 99885791781583),
   (939, 98883059001783000),
   (940, 299898937858777),
   (941, 908778728893327530),
   (942, 883831759959773),
   (943, 890729985550150195),
   (944, 9797887475857),
   (945, 97978874758570),
   (946, 954985757547978),
   (947, 7054855058715578),
   (948, 884574942528827),
   (949, 529894280859822552),
   (950, 99444898957777417),
   (951, 98982272195478527),
   (952, 97895799477739543),
   (953, 999448799855880),
   (954, 7738973991735583),
   (955, 1997743853898570),
   (956, 94487479527493477),
   (957, 937805329370578323),
   (958, 9724183843998917),
   (959, 99713988435785570),
   (960, 99889877798998667),
   (961, 998898777989986670),
   (962, 989887769796),
   (963, 9898877697960),
   (964, 982986769887),
   (965, 9829867698870)]

set_option maxRecDepth 100000 in
private theorem block18_valid : block18.all rowOK = true := by decide +kernel

private def block19 : List (ℕ × ℕ) :=
  [(966, 79291662978712767),
   (967, 9097807269818986),
   (968, 799799889833),
   (969, 7997998898330),
   (970, 368967979317839719),
   (971, 988773871869037),
   (972, 99983662283887),
   (973, 96607329029832767),
   (974, 99366339289721176),
   (975, 9291811970099739),
   (976, 998888877687),
   (977, 9988888776870),
   (978, 81846177491664),
   (979, 66869118889790809),
   (980, 4986769994688794426),
   (981, 697908788092897064),
   (982, 4268447994879286),
   (983, 40926296998969962),
   (984, 9938679488934633),
   (985, 9873939877009783),
   (986, 66968649379681713),
   (987, 177438346779913938),
   (988, 8323837389982738),
   (989, 7993662989379788),
   (990, 92186493931989917),
   (991, 216727678931367887),
   (992, 9877695869867),
   (993, 98776958698670),
   (994, 9888977999681166),
   (995, 7589867587057687),
   (996, 928577829785579626),
   (997, 899789029650655887)]

set_option maxRecDepth 100000 in
private theorem block19_valid : block19.all rowOK = true := by decide +kernel

private def block20 : List (ℕ × ℕ) :=
  [(998, 992767788165889666),
   (999, 76980897998978796),
   (1000, 5989979687597937),
   (1001, 983807687965985753),
   (1002, 9796317618633987),
   (1003, 776889175365180133),
   (1004, 93799396882696827),
   (1005, 8958798608573937),
   (1006, 98686159978169613),
   (1007, 876978150399560387),
   (1008, 6778477688948969874),
   (1009, 9896947966856997),
   (1010, 6969911898988478),
   (1011, 98889174781497598),
   (1012, 9988792854477286),
   (1013, 988058488079929888),
   (1014, 861157856749794618),
   (1015, 144186561779484158),
   (1016, 74764548878435386),
   (1017, 597983743064859367),
   (1018, 785459985544567117),
   (1019, 978079069894563678),
   (1020, 92678986698563277),
   (1021, 94756724979629068),
   (1022, 543587937566958157),
   (1023, 9897358187087565788)]

set_option maxRecDepth 100000 in
private theorem block20_valid : block20.all rowOK = true := by decide +kernel

def certifiedRows : List (ℕ × ℕ) :=
  block00 ++ block01 ++ block02 ++ block03 ++ block04 ++ block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20

private theorem validAppend {a b : List (ℕ × ℕ)}
    (ha : a.all rowOK = true) (hb : b.all rowOK = true) :
    (a ++ b).all rowOK = true := by simp only [List.all_append, ha, hb, Bool.true_and]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certifiedRows_valid : certifiedRows.all rowOK = true :=
  validAppend (a := block00) (b := block01 ++ block02 ++ block03 ++ block04 ++ block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block00_valid (validAppend (a := block01) (b := block02 ++ block03 ++ block04 ++ block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block01_valid (validAppend (a := block02) (b := block03 ++ block04 ++ block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block02_valid (validAppend (a := block03) (b := block04 ++ block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block03_valid (validAppend (a := block04) (b := block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block04_valid (validAppend (a := block05) (b := block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block05_valid (validAppend (a := block06) (b := block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block06_valid (validAppend (a := block07) (b := block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block07_valid (validAppend (a := block08) (b := block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block08_valid (validAppend (a := block09) (b := block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block09_valid (validAppend (a := block10) (b := block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block10_valid (validAppend (a := block11) (b := block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block11_valid (validAppend (a := block12) (b := block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block12_valid (validAppend (a := block13) (b := block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block13_valid (validAppend (a := block14) (b := block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20) block14_valid (validAppend (a := block15) (b := block16 ++ block17 ++ block18 ++ block19 ++ block20) block15_valid (validAppend (a := block16) (b := block17 ++ block18 ++ block19 ++ block20) block16_valid (validAppend (a := block17) (b := block18 ++ block19 ++ block20) block17_valid (validAppend (a := block18) (b := block19 ++ block20) block18_valid (validAppend (a := block19) (b := block20) block19_valid (block20_valid))))))))))))))))))))

set_option maxRecDepth 100000 in
private theorem masks_increase : (certifiedRows.map Prod.fst).IsChain (· < ·) := by
  decide +kernel

theorem certifiedRows_distinct : (certifiedRows.map Prod.fst).Nodup :=
  (List.isChain_iff_pairwise.mp masks_increase).imp (fun h => Nat.ne_of_lt h)

set_option maxRecDepth 100000 in
theorem certifiedRows_length : certifiedRows.length = 666 := by decide +kernel

theorem at_least_666 : 666 ≤ {n | isTerm n}.ncard := by
  simpa only [certifiedRows_length] using
    term_count_ge certifiedRows certifiedRows_valid certifiedRows_distinct

end DigitSupports

namespace DigitSupports
open OMA.S_oeis_a397780

/-- One further support, with digits zero, four, five, six and nine. -/
def furtherRow : ℕ × ℕ := (625, 999544945995646564)

private def extended := furtherRow :: certifiedRows

private theorem extended_valid : extended.all rowOK = true := by
  have hf : rowOK furtherRow = true := by decide +kernel
  simp only [extended, List.all_cons, hf, certifiedRows_valid, Bool.true_and]

set_option maxRecDepth 100000 in
private theorem further_mask_new : furtherRow.1 ∉ certifiedRows.map Prod.fst := by decide +kernel

private theorem extended_distinct : (extended.map Prod.fst).Nodup :=
  List.nodup_cons.mpr ⟨further_mask_new, certifiedRows_distinct⟩

theorem at_least_667 : 667 ≤ {n | isTerm n}.ncard := by
  simpa only [extended, List.length_cons, certifiedRows_length] using
    term_count_ge extended extended_valid extended_distinct

private def fiveRows := extended.filter (rowHasSize 5)

private theorem fiveRows_valid : fiveRows.all rowOK = true := by
  apply List.all_eq_true.mpr
  intro r hr
  exact List.all_eq_true.mp extended_valid r (List.mem_filter.mp hr).1

private theorem fiveRows_distinct : (fiveRows.map Prod.fst).Nodup :=
  List.Nodup.sublist ((List.filter_sublist (l := extended) (p := rowHasSize 5)).map _) extended_distinct

private theorem fiveRows_size : fiveRows.all (rowHasSize 5) = true :=
  List.all_eq_true.mpr (fun _ hr => (List.mem_filter.mp hr).2)

set_option maxRecDepth 100000 in
private theorem fiveRows_length : fiveRows.length = 244 := by decide +kernel

theorem at_least_244_five : 244 ≤ {n | isTerm n ∧ (support n).card = 5}.ncard := by
  simpa only [fiveRows_length] using
    term_count_ge_size fiveRows 5 fiveRows_valid fiveRows_distinct fiveRows_size

end DigitSupports

namespace DigitSupports

def fourRows : List (ℕ × ℕ) :=
  [(15, 10010111),
   (23, 201102),
   (39, 5015),
   (43, 550501),
   (45, 235235),
   (46, 33515),
   (53, 452245),
   (60, 2354235),
   (78, 33336363361),
   (86, 6664414162),
   (101, 256255),
   (102, 5162525125),
   (108, 23523653335),
   (114, 66645451116),
   (116, 25625465),
   (150, 2777177421),
   (165, 5002775005005),
   (275, 10004441414401),
   (277, 20020202002),
   (282, 338841141),
   (293, 500000508805),
   (338, 68444641),
   (531, 104900499999),
   (540, 4999932923),
   (549, 50009995),
   (585, 96936063),
   (596, 49999296962),
   (660, 499979277),
   (771, 90099999990009999),
   (785, 9989999048998),
   (792, 943394898438),
   (960, 99889877798998667)]

set_option maxRecDepth 100000 in
theorem fourRows_valid : fourRows.all rowOK = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fourRows_four_digits : fourRows.all (rowHasSize 4) = true := by decide +kernel

theorem fourRows_distinct : (fourRows.map Prod.fst).Nodup := by decide +kernel

theorem fourRows_length : fourRows.length = 32 := by decide

end DigitSupports

namespace DigitSupports
open OMA.S_oeis_a397780

theorem at_least_32_four_kinds : 32 ≤ {n | isTerm n ∧ (support n).card=4}.ncard := by
  simpa only [fourRows_length] using
    term_count_ge_size fourRows 4 fourRows_valid fourRows_distinct fourRows_four_digits

theorem distribution_ne :
    (List.range 10).map (fun j => {n : ℕ | isTerm n ∧ (support n).card=j+1}.ncard) ≠
    [2,1,2,31,243,210,120,45,10,1] := by
  intro h
  have h4 := congrArg (fun ns : List ℕ => ns[3]?) h
  change some ({n | isTerm n ∧ (support n).card=4}.ncard) = some 31 at h4
  have he := Option.some.inj h4
  have := at_least_32_four_kinds
  omega

end DigitSupports

/-! # Counterexamples to the total and two digit-set counts in OEIS A397780 -/
namespace DigitSupports
open OMA.S_oeis_a397780

theorem total_ne_665 : {n | isTerm n}.ncard ≠ 665 := by
  have := at_least_667
  omega

theorem five_count_ne_243 : {n | isTerm n ∧ (support n).card = 5}.ncard ≠ 243 := by
  have := at_least_244_five
  omega

theorem disproof :
    ¬ ({n : ℕ | isTerm n}.ncard=665 ∧
      (List.range 10).map (fun j => {n : ℕ | isTerm n ∧ (support n).card=j+1}.ncard) =
      [2,1,2,31,243,210,120,45,10,1]) :=
  fun h => total_ne_665 h.1

end DigitSupports

namespace SupportBounds

open DigitSupports OMA.S_oeis_a397780

/-- Further eligible witnesses with decimal supports {0,1,2,6} and {0,1,2,9}. -/
def row0126 : ℕ × ℕ := (71, 101001020100101)
def row0129 : ℕ × ℕ := (519, 101090009991101)

private theorem extra_valid :
    rowOK row0126 = true ∧ rowOK row0129 = true ∧ rowOK furtherRow = true := by
  decide +kernel

private def allRows := row0126 :: row0129 :: furtherRow :: certifiedRows

private theorem all_valid : allRows.all rowOK = true := by
  simp only [allRows, List.all_cons, extra_valid.1, extra_valid.2.1, extra_valid.2.2,
    certifiedRows_valid, Bool.true_and]

set_option maxRecDepth 100000 in
private theorem extra_disjoint :
    row0126.1 ∉ (row0129 :: furtherRow :: certifiedRows).map Prod.fst ∧
    row0129.1 ∉ (furtherRow :: certifiedRows).map Prod.fst ∧
    furtherRow.1 ∉ certifiedRows.map Prod.fst := by decide +kernel

private theorem all_distinct : (allRows.map Prod.fst).Nodup :=
  List.nodup_cons.mpr ⟨extra_disjoint.1, List.nodup_cons.mpr ⟨extra_disjoint.2.1,
    List.nodup_cons.mpr ⟨extra_disjoint.2.2, certifiedRows_distinct⟩⟩⟩

theorem at_least_669 : 669 ≤ {n | isTerm n}.ncard := by
  simpa only [allRows, List.length_cons, certifiedRows_length] using
    term_count_ge allRows all_valid all_distinct

private def rows4 := row0126 :: row0129 :: fourRows

private theorem four_valid : rows4.all rowOK = true := by
  simp only [rows4, List.all_cons, extra_valid.1, extra_valid.2.1, fourRows_valid, Bool.true_and]

private theorem four_size : rows4.all (rowHasSize 4) = true := by
  have he : rowHasSize 4 row0126 = true ∧ rowHasSize 4 row0129 = true := by decide +kernel
  simp only [rows4, List.all_cons, he.1, he.2, fourRows_four_digits, Bool.true_and]

private theorem four_distinct : (rows4.map Prod.fst).Nodup := by
  have he : row0126.1 ∉ (row0129 :: fourRows).map Prod.fst ∧
      row0129.1 ∉ fourRows.map Prod.fst := by decide +kernel
  exact List.nodup_cons.mpr ⟨he.1, List.nodup_cons.mpr ⟨he.2, fourRows_distinct⟩⟩

theorem at_least_34_four : 34 ≤ {n | isTerm n ∧ (support n).card = 4}.ncard := by
  simpa only [rows4, List.length_cons, fourRows_length] using
    term_count_ge_size rows4 4 four_valid four_distinct four_size

end SupportBounds

namespace SupportBounds
open OMA.S_oeis_a397780

private theorem decimal_bound {n d : ℕ} (h : d ∈ decimalDigits n) : d < 10 := by
  by_cases hz : n = 0
  · simp [decimalDigits, hz] at h
    omega
  · exact Nat.digits_lt_base (by decide : 1 < 10) (by simpa [decimalDigits, hz] using h)

private theorem support_subset (n : ℕ) : support n ⊆ Finset.range 10 := by
  intro d hd
  apply Finset.mem_range.mpr
  rcases List.mem_append.mp (List.mem_toFinset.mp hd) with h | h <;> exact decimal_bound h

/-- An excluded family of k-digit supports can be subtracted from the binomial bound. -/
theorem ncard_le_excluding (k : ℕ) (excluded : Finset (Finset ℕ))
    (hsub : excluded ⊆ (Finset.range 10).powersetCard k)
    (hmiss : ∀ {n}, eligible n → support n ∉ excluded) :
    {n | isTerm n ∧ (support n).card = k}.ncard ≤ Nat.choose 10 k - excluded.card := by
  let S : Set ℕ := {n | isTerm n ∧ (support n).card = k}
  let remaining := (Finset.range 10).powersetCard k \ excluded
  have hmap (n : ℕ) (hn : n ∈ S) : support n ∈ remaining :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨support_subset n, hn.2⟩, hmiss hn.1.1⟩
  have hj : Set.InjOn support S := by
    intro a ha b hb he
    rcases lt_trichotomy a b with hab | hab | hab
    · exact False.elim (hb.1.2 a hab ha.1.1 he)
    · exact hab
    · exact False.elim (ha.1.2 b hab hb.1.1 he.symm)
  have hb := Set.ncard_le_ncard_of_injOn (s := S) (t := (↑remaining : Set (Finset ℕ))) support hmap hj
    remaining.finite_toSet
  simpa only [S, Set.ncard_coe_finset, remaining, Finset.card_sdiff_of_subset hsub,
    Finset.card_powersetCard, Finset.card_range] using hb

end SupportBounds

namespace SupportBounds

/-- Five-digit supports excluded by the units and tens digits of a square
and the stationary decimal suffixes of a small set of residues. -/
def forbiddenFive : Finset (Finset ℕ) :=
  {{0,1,3,7,8}, {0,1,3,7,9}, {0,2,3,7,8}, {0,3,4,5,7},
   {0,3,5,7,8}, {0,5,7,8,9}, {1,3,5,7,8}, {1,3,5,7,9}}

end SupportBounds

namespace SupportBounds

open OMA.S_oeis_a397780

/-- Strip all trailing zeros, preserving every positive digit in both supports. -/
theorem core_exists {n : ℕ} (hn : n≠0) :
    ∃ m : ℕ, 0 < m ∧ m % 10 ≠ 0 ∧ support n ⊆ insert 0 (support m) ∧
      (∀ d ∈ Nat.digits 10 m, d ∈ support n) ∧
      (∀ d ∈ Nat.digits 10 (m*m), d ∈ support n) := by
  obtain ⟨k,m,hnd,he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 10 (by decide)
  have hm : 0 < m := by
    by_contra! h
    simp [show m=0 by omega] at he
    exact hn he
  have hp : 0 < m*m := Nat.mul_pos hm hm
  have hsq : n*n=10^(k+k)*(m*m) := by rw [he,pow_add]; ring
  have hword : combined n = (List.replicate k 0 ++ Nat.digits 10 m) ++
      (List.replicate (k+k) 0 ++ Nat.digits 10 (m*m)) := by
    simp only [combined,decimalDigits,if_neg hn,if_neg (Nat.mul_ne_zero hn hn)]
    rw [hsq,he,Nat.digits_base_pow_mul (by decide) hm,Nat.digits_base_pow_mul (by decide) hp]
  refine ⟨m,hm,fun h => hnd (Nat.dvd_iff_mod_eq_zero.mpr h),?_,?_,?_⟩
  · intro d hd
    simp only [support,List.mem_toFinset,hword,List.mem_append,List.mem_replicate] at hd
    simp only [Finset.mem_insert,support,List.mem_toFinset,combined,decimalDigits,
      if_neg hm.ne',if_neg hp.ne',List.mem_append]
    aesop
  · intro d hd
    simp [support,hword,hd]
  · intro d hd
    simp [support,hword,hd]

theorem real_low_two {D : Finset ℕ} {m : ℕ} (hm : 10 ≤ m)
    (h : ∀ d ∈ Nat.digits 10 m, d ∈ D) : m%10 ∈ D ∧ m/10%10 ∈ D := by
  have h1 : m≠0 := by omega
  have h2 : m/10≠0 := by omega
  rw [Nat.digits_eq_cons_digits_div (by decide) h1,
      Nat.digits_eq_cons_digits_div (by decide) h2] at h
  exact ⟨h _ (by simp),h _ (by simp)⟩

end SupportBounds

namespace SupportBounds

/-- The digit at position k, with zeros above the written decimal expansion. -/
def digit (n k : ℕ) : ℕ := n / 10^k % 10

theorem digit_mem {D : Finset ℕ} {n : ℕ} (h : ∀ d ∈ Nat.digits 10 n, d ∈ D)
    (hz : 0 ∈ D) (k : ℕ) : digit n k ∈ D := by
  unfold digit
  rw [← Nat.getD_digits _ _ (by decide : 2 ≤ 10),List.getD_eq_getElem?_getD]
  by_cases hk : k < (Nat.digits 10 n).length
  · rw [List.getElem?_eq_getElem hk]
    exact h _ (List.getElem_mem hk)
  · simpa [List.getElem?_eq_none (by omega : (Nat.digits 10 n).length ≤ k)] using hz

private theorem square_digit (m P : ℕ) (hp : 0<P) (hpd : 10 ∣ P) :
    (m*m/P)%10 = ((m%P)*(m%P)/P+2*(m%P)*(m/P%10))%10 := by
  let r := m%P
  let q := m/P
  have he : m*m = r*r+P*(2*r*q+P*q*q) := calc
    m*m = (r+P*q)*(r+P*q) := by rw [show r+P*q=m by exact Nat.mod_add_div _ _]
    _ = _ := by ring
  change (m*m/P)%10 = (r*r/P+2*r*(q%10))%10
  rw [he,Nat.add_mul_div_left _ _ hp]
  have hx : P*q*q ≡ 0 [MOD 10] := Nat.modEq_zero_iff_dvd.mpr
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpd _) _)
  have hq := (Nat.mod_modEq q 10).symm.mul_left (2*r)
  simpa only [Nat.ModEq,add_zero] using (hq.add hx).add_left (r*r/P)

private theorem stationary_parameters (k : ℕ) :
    10 ≤ 10^(k+1) ∧ 10 ∣ 10^(k+1) := by
  rw [pow_succ]
  refine ⟨?_,dvd_mul_left _ _⟩
  have h : 0 < 10^k := by positivity
  omega

theorem stationary_positive {D : Finset ℕ} {m a : ℕ}
    (hm : ∀ k, digit m k ∈ D) (hs : ∀ k, digit (m*m) k ∈ D)
    (ha : a*a<10) (hu : m%10=a)
    (hforce : ∀ d : Fin 10, d.val ∈ D → (2*a*d.val)%10 ∈ D → d.val=0) :
    m=a := by
  have hall (k : ℕ) : m%(10^(k+1))=a := by
    induction k with
    | zero => simpa using hu
    | succ k ih =>
      let P := 10^(k+1)
      obtain ⟨hpl,hpd⟩ := stationary_parameters k
      have hp : 0<P := by dsimp [P]; omega
      have hm' := hm (k+1)
      have hs' := hs (k+1)
      change m/P%10 ∈ D at hm'
      change m*m/P%10 ∈ D at hs'
      rw [square_digit _ P hp hpd,show m%P=a from ih,
          Nat.div_eq_of_lt (by dsimp [P]; omega),zero_add] at hs'
      have h0 := hforce ⟨m/P%10,Nat.mod_lt _ (by decide)⟩ hm' hs'
      change m/P%10=0 at h0
      change m%(P*10)=a
      rw [Nat.mod_mul,h0,mul_zero,add_zero]
      exact ih
  have hlarge : m<10^(m+1) := by
    have h := Nat.lt_pow_self (n:=m+1) (by decide : 1<10)
    omega
  simpa [Nat.mod_eq_of_lt hlarge] using hall m

theorem stationary_negative {D : Finset ℕ} {m a : ℕ}
    (hm : ∀ k, digit m k ∈ D) (hs : ∀ k, digit (m*m) k ∈ D)
    (ha0 : 0<a) (ha : a*a<10) (hat : 2*a<10) (hu : m%10+a=10)
    (hforce : ∀ d : Fin 10, d.val ∈ D → ((10-2*a)+2*(10-a)*d.val)%10 ∈ D → d.val=9) :
    False := by
  have hall (k : ℕ) : m%(10^(k+1))+a=10^(k+1) := by
    induction k with
    | zero => simpa using hu
    | succ k ih =>
      let P := 10^(k+1)
      obtain ⟨hpl,hpd⟩ := stationary_parameters k
      change 10≤P at hpl
      change 10∣P at hpd
      have hp : 0<P := by omega
      have hp0 : P%10=0 := Nat.mod_eq_zero_of_dvd hpd
      change m%P+a=P at ih
      have hr : m%P=P-a := by omega
      have htw : 2*a≤P := by omega
      obtain ⟨u,hu'⟩ := Nat.exists_eq_add_of_le htw
      have hid : (P-a)*(P-a) = a*a+P*(P-2*a) := by
        have h1 : P-a=a+u := by omega
        have h2 : P-2*a=u := by omega
        rw [h1,h2,hu']
        ring
      have divsq : (P-a)*(P-a)/P=P-2*a := by
        rw [hid,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt (by omega),zero_add]
      have hm' := hm (k+1)
      have hs' := hs (k+1)
      change m/P%10 ∈ D at hm'
      change m*m/P%10 ∈ D at hs'
      rw [square_digit _ P hp hpd,hr,divsq] at hs'
      have eq1 : P-a ≡ 10-a [MOD 10] := by unfold Nat.ModEq; omega
      have eq2 : P-2*a ≡ 10-2*a [MOD 10] := by unfold Nat.ModEq; omega
      have eq3 := eq2.add ((eq1.mul_left 2).mul_right (m/P%10))
      have hd := hforce ⟨m/P%10,Nat.mod_lt _ (by decide)⟩ hm' (eq3 ▸ hs')
      change m/P%10=9 at hd
      change m%(P*10)+a=P*10
      rw [Nat.mod_mul,hd]
      omega
  have hlarge := Nat.lt_pow_self (n:=m+a+1) (by decide : 1<10)
  have hcontra := hall (m+a)
  rw [Nat.mod_eq_of_lt (by omega)] at hcontra
  omega

end SupportBounds

namespace SupportBounds

open OMA.S_oeis_a397780

private def positiveCase (D : Finset ℕ) (r : ℕ) : Prop :=
  ∃ a : Fin 4, a.val*a.val < 10 ∧ r%10=a.val ∧
    ∀ d : Fin 10, d.val ∈ D → (2*a.val*d.val)%10 ∈ D → d.val=0

private def negativeCase (D : Finset ℕ) (r : ℕ) : Prop :=
  ∃ a : Fin 4, 0<a.val ∧ a.val*a.val < 10 ∧ 2*a.val<10 ∧ r%10+a.val=10 ∧
    ∀ d : Fin 10, d.val ∈ D → ((10-2*a.val)+2*(10-a.val)*d.val)%10 ∈ D → d.val=9

private instance (D : Finset ℕ) (r : ℕ) : Decidable (positiveCase D r) := by unfold positiveCase; infer_instance
private instance (D : Finset ℕ) (r : ℕ) : Decidable (negativeCase D r) := by unfold negativeCase; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem classify : ∀ D ∈ forbiddenFive, ∀ r : Fin 100,
    r.val%10≠0 → r.val%10 ∈ D → r.val/10 ∈ D →
    (r.val*r.val)%10 ∈ D → (r.val*r.val)%100/10 ∈ D →
    0 ∈ D ∧ (positiveCase D r.val ∨ negativeCase D r.val) := by
  decide +kernel

private theorem small : ∀ D ∈ forbiddenFive, ∀ a : Fin 10, ¬D ⊆ insert 0 (support a.val) := by
  decide +kernel

/-- None of the eight impossible five-digit sets is even the support of a
decimal integer and its square, independently of the multiplicity condition. -/
theorem five_exclusions_unconditional (n : ℕ) : support n ∉ forbiddenFive := by
  intro h
  by_cases hz : n=0
  · subst n
    exact (by decide +kernel : support 0 ∉ forbiddenFive) h
  obtain ⟨m,hm,hu,hsub,hd,hs⟩ := core_exists hz
  by_cases hsmall : m<10
  · exact small _ h ⟨m,hsmall⟩ hsub
  have hl := real_low_two (by omega : 10 ≤ m) hd
  have hls := real_low_two (by nlinarith : 10 ≤ m*m) hs
  let r : Fin 100 := ⟨m%100,Nat.mod_lt _ (by decide)⟩
  have hrem : m ≡ r.val [MOD 100] := (Nat.mod_modEq m 100).symm
  have hs100 : (m*m)%100 = (r.val*r.val)%100 := hrem.mul hrem
  have hs10 : (m*m)%10 = (r.val*r.val)%10 := (hrem.mul hrem).of_dvd (by decide : 10∣100)
  have hu10 : r.val%10=m%10 := hrem.symm.of_dvd (by decide : 10∣100)
  have hrten : r.val/10=m/10%10 := Nat.mod_mul_right_div_self m 10 10
  have hsten : (r.val*r.val)%100/10=m*m/10%10 := by
    rw [←hs100]
    exact Nat.mod_mul_right_div_self _ 10 10
  have hv := classify _ h r (by simpa only [hu10] using hu) (hu10.symm ▸ hl.1)
      (hrten.symm ▸ hl.2) (hs10 ▸ hls.1) (hsten.symm ▸ hls.2)
  obtain ⟨h0,hpos|hneg⟩ := hv
  · obtain ⟨a,ha,he,force⟩ := hpos
    have me := stationary_positive (digit_mem hd h0) (digit_mem hs h0) ha (hu10 ▸ he) force
    exact small _ h ⟨m,by have := a.isLt; omega⟩ hsub
  · obtain ⟨a,ha0,ha,ht,he,force⟩ := hneg
    exact stationary_negative (digit_mem hd h0) (digit_mem hs h0) ha0 ha ht (hu10 ▸ he) force

theorem five_exclusions {n : ℕ} (_ : eligible n) : support n ∉ forbiddenFive :=
  five_exclusions_unconditional n

end SupportBounds

namespace SupportBounds
open OMA.S_oeis_a397780

private theorem five_subset : forbiddenFive ⊆ (Finset.range 10).powersetCard 5 := by
  decide +kernel

private theorem five_card : forbiddenFive.card = 8 := by decide +kernel

theorem at_most_244_five : {n | isTerm n ∧ (support n).card = 5}.ncard ≤ 244 := by
  have hc : Nat.choose 10 5 - 8 = 244 := by decide +kernel
  simpa only [five_card, hc] using ncard_le_excluding 5 forbiddenFive five_subset @five_exclusions

/-- Exactly 244 least eligible integers have a five-digit support. -/
theorem exactly_244_five : {n | isTerm n ∧ (support n).card = 5}.ncard = 244 :=
  Nat.le_antisymm at_most_244_five DigitSupports.at_least_244_five

end SupportBounds

namespace SupportBounds.Symmetric
open DigitSupports OMA.S_oeis_a397780

/-- A semantic row can be supplied by any proved decimal representation. -/
def validFor (P : Finset ℕ → Prop) (r : ℕ × ℕ) : Prop :=
  mask (support r.2)=r.1 ∧ eligible r.2 ∧ P (support r.2)

private noncomputable def representative (s : Finset ℕ) : ℕ :=
  sInf {n | eligible n ∧ support n=s}

private theorem repr_spec {n : ℕ} (h : eligible n) :
    isTerm (representative (support n)) ∧ support (representative (support n))=support n := by
  let A := {m | eligible m ∧ support m=support n}
  have hf : representative (support n)∈A := Nat.sInf_mem (⟨n,h,rfl⟩ : A.Nonempty)
  refine ⟨⟨hf.1, ?_⟩,hf.2⟩
  intro m hm he hs
  exact (Nat.not_le_of_gt hm) (Nat.sInf_le (show m∈A from ⟨he,hs.trans hf.2⟩))

theorem semantic_bound (rows : List (ℕ×ℕ)) (P : Finset ℕ → Prop)
    (hv : ∀ r∈rows, validFor P r) (hn : (rows.map Prod.fst).Nodup) :
    rows.length ≤ {n | isTerm n ∧ P (support n)}.ncard := by
  let w (i : Fin rows.length) := representative (support rows[i.val].2)
  have hj (i : Fin rows.length) := hv _ (List.getElem_mem (n:=i.val) i.isLt)
  have hs (i : Fin rows.length) := repr_spec (hj i).2.1
  have hinj : Function.Injective w := by
    intro i j he
    have hm : rows[i.val].1 = rows[j.val].1 := by
      rw [←(hj i).1,←(hj j).1,←(hs i).2,←(hs j).2]
      exact congrArg (fun m => mask (support m)) he
    let i' : Fin (rows.map Prod.fst).length := ⟨i.val,by simp⟩
    let j' : Fin (rows.map Prod.fst).length := ⟨j.val,by simp⟩
    have h := (List.nodup_iff_injective_getElem.mp hn) (a₁:=i') (a₂:=j')
      (by simpa [i',j'] using hm)
    exact Fin.ext (congrArg (fun f : Fin (rows.map Prod.fst).length => f.val) h)
  have hfin : {n | isTerm n ∧ P (support n)}.Finite := finite_terms.subset (fun _ h => h.1)
  have hb := Set.ncard_le_ncard_of_injOn (s:=Set.univ) (t:={n | isTerm n ∧ P (support n)}) w
    (fun i _ => ⟨(hs i).1,(hs i).2.symm ▸ (hj i).2.2⟩) hinj.injOn hfin
  simpa using hb

end SupportBounds.Symmetric

namespace SupportBounds.Symmetric

open OMA.S_oeis_a397780

/-- Each leaf skips decimal zeros and then places a nonzero digit.
The left child contains the less significant positions. -/
inductive Word where
  | digit (gap index : ℕ)
  | join (low high : Word)

namespace Word

def digits : Word → List ℕ
  | .digit g i => List.replicate g 0 ++ [i % 9 + 1]
  | .join x y => x.digits ++ y.digits

def len : Word → ℕ
  | .digit g _ => g+1
  | .join x y => x.len+y.len

def value : Word → ℕ
  | .digit g i => 10^g*(i%9+1)
  | .join x y => x.value + 10^x.len*y.value

def freq (d : ℕ) : Word → ℕ
  | .digit g i => (if 0==d then g else 0) + (if i%9+1==d then 1 else 0)
  | .join x y => x.freq d+y.freq d

theorem lengths (w : Word) : w.digits.length=w.len := by
  induction w <;> simp [digits,len, *]

theorem numeric (w : Word) : Nat.ofDigits 10 w.digits=w.value := by
  induction w <;> simp [digits,value,Nat.ofDigits_append,Nat.ofDigits_cons, * ,lengths]

theorem frequencies (w : Word) (d : ℕ) : w.digits.count d=w.freq d := by
  induction w <;> simp [digits,freq,List.count_replicate, *,List.count_cons]

theorem nonempty (w : Word) : w.digits ≠ [] := by
  induction w <;> simp [digits, *]

theorem bounded (w : Word) : ∀ d∈w.digits, d<10 := by
  induction w with
  | digit g i =>
    intro d hd
    simp [digits] at hd
    rcases hd with h|h <;> omega
  | join x y hx hy =>
    intro d hd
    exact (List.mem_append.mp hd).elim (hx d) (hy d)

theorem high (w : Word) : w.digits.getLast w.nonempty≠0 := by
  induction w with
  | digit g i => simp [digits]
  | join x y hx hy =>
    simpa only [digits,List.getLast_append_of_right_ne_nil _ _ y.nonempty] using hy

theorem decimal (w : Word) : decimalDigits w.value=w.digits := by
  have e := Nat.digits_ofDigits 10 (by decide) w.digits w.bounded (fun _ => w.high)
  rw [w.numeric] at e
  have hn : w.value≠0 := fun he => w.nonempty (by simpa [he] using e.symm)
  simpa [decimalDigits,hn] using e

end Word

def certOK (r s : Word) (key : Finset ℕ) : Prop :=
  r.value*r.value=s.value ∧
  (∀ d : Fin 10, (d.val∈key ↔ 0<r.freq d+s.freq d) ∧
    (d.val∈key → d.val≤r.freq d+s.freq d))

theorem cert_sound {r s : Word} {key : Finset ℕ} (hk : ∀ d∈key, d<10)
    (h : certOK r s key) : support r.value=key ∧ eligible r.value := by
  have hword : combined r.value=r.digits++s.digits := by
    simp [combined,h.1,Word.decimal]
  have hc (d : ℕ) : (combined r.value).count d=r.freq d+s.freq d := by
    simp [hword,Word.frequencies]
  have hm (d : ℕ) : d∈support r.value ↔ 0<r.freq d+s.freq d := by
    rw [←hc,List.count_pos_iff]
    simp [support]
  have hr (d : ℕ) (hd : d∈support r.value) : d<10 := by
    have := List.mem_toFinset.mp hd
    rw [hword] at this
    exact (List.mem_append.mp this).elim (r.bounded d) (s.bounded d)
  have he : support r.value=key := by
    ext d
    constructor
    · intro hd
      exact (h.2 ⟨d,hr d hd⟩).1.mpr ((hm d).mp hd)
    · intro hd
      exact (hm d).mpr ((h.2 ⟨d,hk d hd⟩).1.mp hd)
  refine ⟨he,fun d hd => ?_⟩
  rw [hc]
  exact (h.2 ⟨d,hr d hd⟩).2 (he ▸ hd)

end SupportBounds.Symmetric

namespace SupportBounds.Symmetric

open OMA.S_oeis_a397780

private def root7Part0 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 0) (.digit 72 0)) (.join (.digit 294 0) (.digit 173 0))) (.join (.join (.digit 142 0) (.digit 11 0)) (.join (.digit 34 0) (.digit 163 0)))) (.join (.join (.join (.digit 21 0) (.digit 17 0)) (.join (.digit 49 0) (.digit 1217 0))) (.join (.join (.digit 441 0) (.digit 68 0)) (.join (.digit 937 0) (.digit 388 0))))) (.join (.join (.join (.join (.digit 112 0) (.digit 63 0)) (.join (.digit 371 0) (.digit 9 0))) (.join (.join (.digit 134 0) (.digit 239 0)) (.join (.digit 276 0) (.digit 291 0)))) (.join (.join (.join (.digit 233 0) (.digit 829 0)) (.join (.digit 216 0) (.digit 111 0))) (.join (.join (.digit 242 0) (.digit 71 0)) (.join (.digit 1030 0) (.digit 10 0))))))

private def root7Part1 : Word :=
  (.join (.join (.join (.join (.digit 174 0) (.digit 7 0)) (.join (.digit 181 0) (.digit 0 0))) (.join (.join (.digit 311 0) (.digit 425 0)) (.join (.digit 704 0) (.digit 300 0)))) (.join (.join (.join (.digit 287 0) (.digit 396 0)) (.join (.digit 1067 0) (.digit 8 0))) (.join (.join (.digit 633 0) (.digit 112 0)) (.join (.digit 55 0) (.join (.digit 455 0) (.digit 39 0))))))

def root7 : Word :=
  (.join root7Part0 root7Part1)

private def square7Part0 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 0) (.digit 72 1)) (.join (.digit 72 0) (.digit 221 1))) (.join (.join (.digit 72 1) (.digit 100 1)) (.join (.digit 72 1) (.digit 69 1)))) (.join (.join (.join (.digit 11 1) (.digit 34 1)) (.join (.digit 3 0) (.digit 21 1))) (.join (.join (.digit 11 1) (.digit 34 1)) (.join (.digit 90 1) (.digit 13 1))))) (.join (.join (.join (.join (.digit 7 1) (.digit 17 1)) (.join (.digit 32 1) (.digit 16 1))) (.join (.join (.digit 4 1) (.digit 17 1)) (.join (.digit 43 1) (.digit 5 1)))) (.join (.join (.join (.digit 5 1) (.digit 18 0)) (.join (.digit 15 1) (.digit 126 1))) (.join (.join (.digit 11 1) (.digit 24 1)) (.join (.digit 9 1) (.digit 11 1))))))

private def square7Part1 : Word :=
  (.join (.join (.join (.join (.join (.digit 17 1) (.digit 49 1)) (.join (.digit 15 0) (.digit 11 1))) (.join (.join (.digit 11 0) (.digit 22 1)) (.join (.digit 11 1) (.digit 8 1)))) (.join (.join (.join (.digit 21 1) (.digit 3 0)) (.join (.digit 13 1) (.digit 49 1))) (.join (.join (.digit 52 1) (.digit 11 1)) (.join (.digit 9 1) (.digit 11 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 6 1)) (.join (.digit 4 1) (.digit 16 1))) (.join (.join (.digit 17 1) (.digit 2 1)) (.join (.digit 11 1) (.digit 34 1)))) (.join (.join (.join (.digit 73 0) (.digit 21 1)) (.join (.digit 17 1) (.digit 3 0))) (.join (.join (.digit 17 1) (.digit 17 0)) (.join (.digit 9 1) (.digit 21 1))))))

private def square7Part2 : Word :=
  (.join (.join (.join (.join (.join (.digit 17 1) (.digit 49 0)) (.join (.digit 231 1) (.digit 72 1))) (.join (.join (.digit 294 1) (.digit 73 1)) (.join (.digit 68 1) (.digit 3 1)))) (.join (.join (.join (.digit 26 1) (.digit 41 1)) (.join (.digit 100 1) (.digit 11 1))) (.join (.join (.digit 34 1) (.digit 77 1)) (.join (.digit 68 1) (.digit 16 1))))) (.join (.join (.join (.join (.digit 21 1) (.digit 17 1)) (.join (.digit 47 1) (.digit 1 1))) (.join (.join (.digit 66 1) (.digit 73 1)) (.join (.digit 11 1) (.digit 34 1)))) (.join (.join (.join (.digit 21 1) (.digit 11 1)) (.join (.digit 34 1) (.digit 94 1))) (.join (.join (.digit 21 1) (.digit 17 1)) (.join (.digit 28 1) (.digit 20 1))))))

private def square7Part3 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 1) (.digit 17 1)) (.join (.digit 1 1) (.digit 47 1))) (.join (.join (.digit 24 1) (.digit 294 1)) (.join (.digit 20 1) (.digit 72 1)))) (.join (.join (.join (.digit 39 1) (.digit 39 1)) (.join (.digit 23 1) (.digit 8 1))) (.join (.join (.digit 63 1) (.digit 45 1)) (.join (.digit 11 1) (.digit 34 1))))) (.join (.join (.join (.join (.digit 22 0) (.digit 1 1)) (.join (.digit 112 1) (.digit 25 1))) (.join (.join (.digit 21 1) (.digit 12 1)) (.join (.digit 2 1) (.digit 1 1)))) (.join (.join (.join (.digit 1 1) (.digit 9 1)) (.join (.digit 37 1) (.digit 24 1))) (.join (.join (.digit 9 1) (.digit 22 1)) (.join (.digit 29 1) (.digit 8 1))))))

private def square7Part4 : Word :=
  (.join (.join (.join (.join (.join (.digit 2 1) (.digit 21 1)) (.join (.digit 12 1) (.digit 34 1))) (.join (.join (.digit 30 1) (.digit 9 1)) (.join (.digit 1 1) (.digit 34 1)))) (.join (.join (.join (.digit 16 1) (.digit 11 1)) (.join (.digit 2 1) (.digit 18 1))) (.join (.join (.digit 12 1) (.digit 7 1)) (.join (.digit 0 1) (.digit 8 1))))) (.join (.join (.join (.join (.digit 6 1) (.digit 1 1)) (.join (.digit 49 1) (.digit 20 1))) (.join (.join (.digit 1 1) (.digit 21 1)) (.join (.digit 17 1) (.digit 12 1)))) (.join (.join (.join (.digit 10 1) (.digit 17 1)) (.join (.digit 3 1) (.digit 3 1))) (.join (.join (.digit 1 1) (.digit 11 1)) (.join (.digit 49 1) (.digit 47 1))))))

private def square7Part5 : Word :=
  (.join (.join (.join (.join (.join (.digit 22 1) (.digit 1 1)) (.join (.digit 7 1) (.digit 1 1))) (.join (.join (.digit 3 0) (.digit 5 1)) (.join (.digit 24 1) (.digit 2 1)))) (.join (.join (.join (.digit 6 1) (.digit 10 1)) (.join (.digit 16 1) (.digit 59 1))) (.join (.join (.digit 8 0) (.digit 2 1)) (.join (.digit 34 1) (.digit 18 1))))) (.join (.join (.join (.join (.digit 9 1) (.digit 11 1)) (.join (.digit 8 1) (.digit 0 1))) (.join (.join (.digit 7 1) (.digit 9 1)) (.join (.digit 7 1) (.digit 31 1)))) (.join (.join (.join (.digit 9 1) (.digit 30 1)) (.join (.digit 2 1) (.digit 10 1))) (.join (.join (.digit 21 1) (.digit 6 1)) (.join (.digit 10 1) (.digit 0 1))))))

private def square7Part6 : Word :=
  (.join (.join (.join (.join (.join (.digit 34 1) (.digit 13 1)) (.join (.digit 56 1) (.digit 15 1))) (.join (.join (.digit 56 1) (.digit 4 1)) (.join (.digit 14 1) (.digit 21 1)))) (.join (.join (.join (.digit 17 1) (.digit 0 1)) (.join (.digit 24 1) (.digit 11 1))) (.join (.join (.digit 11 1) (.digit 22 1)) (.join (.digit 101 1) (.digit 59 1))))) (.join (.join (.join (.join (.digit 1 1) (.digit 21 1)) (.join (.digit 17 1) (.digit 40 1))) (.join (.join (.digit 8 1) (.digit 2 1)) (.join (.digit 3 1) (.digit 30 1)))) (.join (.join (.join (.digit 21 1) (.digit 21 1)) (.join (.digit 37 1) (.digit 8 1))) (.join (.join (.digit 54 1) (.digit 17 1)) (.join (.digit 21 1) (.digit 0 1))))))

private def square7Part7 : Word :=
  (.join (.join (.join (.join (.join (.digit 11 1) (.digit 4 1)) (.join (.digit 29 1) (.digit 19 1))) (.join (.join (.digit 77 1) (.digit 65 1)) (.join (.digit 6 1) (.digit 5 1)))) (.join (.join (.join (.digit 8 1) (.digit 17 1)) (.join (.digit 41 1) (.digit 7 1))) (.join (.join (.digit 29 1) (.digit 5 1)) (.join (.digit 3 1) (.digit 20 1))))) (.join (.join (.join (.join (.digit 38 1) (.digit 4 1)) (.join (.digit 28 1) (.digit 34 1))) (.join (.join (.digit 3 1) (.digit 1 1)) (.join (.digit 36 1) (.digit 33 1)))) (.join (.join (.join (.digit 139 1) (.digit 28 1)) (.join (.digit 0 1) (.digit 12 1))) (.join (.join (.digit 42 1) (.digit 9 1)) (.join (.digit 5 1) (.digit 0 1))))))

private def square7Part8 : Word :=
  (.join (.join (.join (.join (.join (.digit 39 1) (.digit 11 6)) (.join (.digit 9 1) (.digit 9 1))) (.join (.join (.digit 14 1) (.digit 26 1)) (.join (.digit 13 1) (.digit 68 1)))) (.join (.join (.join (.digit 5 1) (.digit 22 1)) (.join (.digit 24 1) (.digit 5 1))) (.join (.join (.digit 11 1) (.digit 3 1)) (.join (.digit 17 1) (.digit 3 1))))) (.join (.join (.join (.join (.digit 8 1) (.digit 36 1)) (.join (.digit 25 1) (.digit 0 1))) (.join (.join (.digit 0 1) (.digit 11 1)) (.join (.digit 34 1) (.digit 20 1)))) (.join (.join (.join (.digit 3 1) (.digit 26 1)) (.join (.digit 0 1) (.digit 20 1))) (.join (.join (.digit 4 1) (.digit 12 1)) (.join (.digit 32 1) (.digit 12 1))))))

private def square7Part9 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 21 1)) (.join (.digit 21 1) (.digit 9 1))) (.join (.join (.digit 5 1) (.digit 1 1)) (.join (.digit 3 1) (.digit 20 1)))) (.join (.join (.join (.digit 13 1) (.digit 10 1)) (.join (.digit 13 1) (.digit 11 1))) (.join (.join (.digit 17 1) (.digit 14 1)) (.join (.digit 1 1) (.digit 91 1))))) (.join (.join (.join (.join (.digit 6 0) (.digit 14 1)) (.join (.digit 17 1) (.digit 31 1))) (.join (.join (.digit 17 1) (.digit 3 1)) (.join (.digit 17 1) (.digit 1 1)))) (.join (.join (.join (.digit 5 1) (.digit 41 1)) (.join (.digit 4 1) (.digit 9 1))) (.join (.join (.digit 5 1) (.digit 0 1)) (.join (.digit 22 1) (.digit 10 1))))))

private def square7Part10 : Word :=
  (.join (.join (.join (.join (.join (.digit 14 0) (.digit 46 1)) (.join (.digit 10 1) (.digit 5 1))) (.join (.join (.digit 14 1) (.digit 35 1)) (.join (.digit 12 0) (.digit 31 1)))) (.join (.join (.join (.digit 7 1) (.digit 15 1)) (.join (.digit 48 1) (.digit 7 1))) (.join (.join (.digit 77 1) (.digit 3 1)) (.join (.digit 9 1) (.digit 8 1))))) (.join (.join (.join (.join (.digit 7 1) (.digit 0 1)) (.join (.digit 1 1) (.digit 69 1))) (.join (.join (.digit 0 1) (.digit 11 1)) (.join (.digit 9 1) (.digit 21 1)))) (.join (.join (.join (.digit 31 1) (.digit 2 1)) (.join (.digit 6 1) (.digit 5 1))) (.join (.join (.digit 10 1) (.digit 0 1)) (.join (.digit 7 1) (.digit 44 1))))))

private def square7Part11 : Word :=
  (.join (.join (.join (.join (.join (.digit 14 1) (.digit 48 1)) (.join (.digit 13 1) (.digit 3 1))) (.join (.join (.digit 6 1) (.digit 0 1)) (.join (.digit 10 1) (.digit 19 1)))) (.join (.join (.join (.digit 3 1) (.digit 1 1)) (.join (.digit 1 1) (.digit 6 1))) (.join (.join (.digit 0 1) (.digit 0 1)) (.join (.digit 0 1) (.digit 15 1))))) (.join (.join (.join (.join (.digit 84 1) (.digit 10 1)) (.join (.digit 12 1) (.digit 7 1))) (.join (.join (.digit 3 1) (.digit 7 1)) (.join (.digit 4 1) (.digit 1 0)))) (.join (.join (.join (.digit 8 1) (.digit 0 1)) (.join (.digit 2 1) (.digit 2 1))) (.join (.join (.digit 3 6) (.digit 0 1)) (.join (.digit 6 1) (.digit 2 1))))))

private def square7Part12 : Word :=
  (.join (.join (.join (.join (.join (.digit 6 1) (.digit 10 1)) (.join (.digit 23 1) (.digit 14 1))) (.join (.join (.digit 10 1) (.digit 13 1)) (.join (.digit 28 1) (.digit 2 1)))) (.join (.join (.join (.digit 9 1) (.digit 3 1)) (.join (.digit 3 1) (.digit 0 1))) (.join (.join (.digit 10 1) (.digit 0 1)) (.join (.digit 7 1) (.digit 7 1))))) (.join (.join (.join (.join (.digit 10 1) (.digit 2 1)) (.join (.digit 3 1) (.digit 0 1))) (.join (.join (.digit 2 1) (.digit 2 1)) (.join (.digit 6 1) (.digit 1 1)))) (.join (.join (.join (.digit 5 1) (.digit 17 1)) (.join (.digit 23 1) (.digit 0 1))) (.join (.join (.digit 6 1) (.digit 7 6)) (.join (.digit 42 1) (.digit 25 1))))))

private def square7Part13 : Word :=
  (.join (.join (.join (.join (.join (.digit 14 1) (.digit 0 1)) (.join (.digit 9 1) (.digit 9 1))) (.join (.join (.digit 0 1) (.digit 0 1)) (.join (.digit 4 1) (.digit 2 1)))) (.join (.join (.join (.digit 8 1) (.digit 0 1)) (.join (.digit 48 1) (.digit 0 1))) (.join (.join (.digit 5 1) (.digit 4 1)) (.join (.digit 11 1) (.digit 29 1))))) (.join (.join (.join (.join (.digit 4 1) (.digit 6 1)) (.join (.digit 51 1) (.digit 2 1))) (.join (.join (.digit 53 1) (.digit 5 1)) (.join (.digit 16 1) (.digit 9 1)))) (.join (.join (.join (.digit 14 1) (.digit 21 1)) (.join (.digit 4 1) (.digit 2 1))) (.join (.join (.digit 9 1) (.digit 24 1)) (.join (.digit 6 1) (.digit 10 0))))))

private def square7Part14 : Word :=
  (.join (.join (.join (.join (.join (.digit 6 1) (.digit 8 1)) (.join (.digit 20 1) (.digit 8 1))) (.join (.join (.digit 85 1) (.digit 11 1)) (.join (.digit 7 1) (.digit 26 1)))) (.join (.join (.join (.digit 4 1) (.digit 9 1)) (.join (.digit 30 1) (.digit 51 1))) (.join (.join (.digit 32 1) (.digit 18 1)) (.join (.digit 13 1) (.digit 21 1))))) (.join (.join (.join (.join (.digit 17 1) (.digit 34 1)) (.join (.digit 9 1) (.digit 4 1))) (.join (.join (.digit 19 1) (.digit 66 1)) (.join (.digit 5 1) (.digit 0 1)))) (.join (.join (.join (.digit 8 1) (.digit 10 1)) (.join (.digit 6 0) (.digit 8 1))) (.join (.join (.digit 5 1) (.digit 69 1)) (.join (.digit 54 1) (.digit 4 1))))))

private def square7Part15 : Word :=
  (.join (.join (.join (.join (.join (.digit 22 1) (.digit 7 1)) (.join (.digit 10 1) (.digit 61 1))) (.join (.join (.digit 8 1) (.digit 1 1)) (.join (.digit 6 1) (.digit 15 1)))) (.join (.join (.join (.digit 8 1) (.digit 2 1)) (.join (.digit 26 1) (.digit 5 1))) (.join (.join (.digit 1 1) (.digit 27 1)) (.join (.digit 0 1) (.digit 2 1))))) (.join (.join (.join (.join (.digit 37 1) (.digit 23 1)) (.join (.digit 10 1) (.digit 5 1))) (.join (.join (.digit 32 1) (.digit 0 1)) (.join (.digit 17 1) (.digit 0 1)))) (.join (.join (.join (.digit 9 1) (.digit 11 1)) (.join (.digit 9 1) (.digit 7 1))) (.join (.join (.digit 4 1) (.digit 15 1)) (.join (.digit 28 6) (.digit 2 1))))))

private def square7Part16 : Word :=
  (.join (.join (.join (.join (.join (.digit 8 1) (.digit 13 1)) (.join (.digit 7 1) (.digit 12 1))) (.join (.join (.digit 19 1) (.digit 5 1)) (.join (.digit 13 1) (.digit 7 1)))) (.join (.join (.join (.digit 7 1) (.digit 6 1)) (.join (.digit 9 1) (.digit 12 1))) (.join (.join (.digit 11 1) (.digit 59 1)) (.join (.digit 5 1) (.digit 4 1))))) (.join (.join (.join (.join (.digit 0 1) (.digit 15 1)) (.join (.digit 0 1) (.digit 11 1))) (.join (.join (.digit 4 1) (.digit 3 1)) (.join (.digit 29 1) (.digit 0 1)))) (.join (.join (.join (.digit 1 1) (.digit 11 1)) (.join (.digit 0 1) (.digit 8 1))) (.join (.join (.digit 7 1) (.digit 8 1)) (.join (.digit 7 1) (.digit 1 1))))))

private def square7Part17 : Word :=
  (.join (.join (.join (.join (.join (.digit 30 1) (.digit 13 1)) (.join (.digit 56 1) (.digit 9 1))) (.join (.join (.digit 18 0) (.digit 3 1)) (.join (.digit 22 1) (.digit 3 1)))) (.join (.join (.join (.digit 13 1) (.digit 7 1)) (.join (.digit 7 1) (.digit 9 1))) (.join (.join (.digit 2 1) (.digit 41 1)) (.join (.digit 4 1) (.digit 8 1))))) (.join (.join (.join (.join (.digit 83 1) (.digit 2 1)) (.join (.digit 6 1) (.digit 4 1))) (.join (.join (.digit 14 1) (.digit 19 1)) (.join (.digit 21 1) (.digit 9 1)))) (.join (.join (.join (.digit 7 1) (.digit 51 1)) (.join (.digit 2 1) (.digit 19 1))) (.join (.join (.digit 10 1) (.digit 37 1)) (.join (.digit 2 1) (.digit 18 1))))))

private def square7Part18 : Word :=
  (.join (.join (.join (.join (.join (.digit 17 1) (.digit 18 1)) (.join (.digit 30 1) (.digit 2 1))) (.join (.join (.digit 34 1) (.digit 8 1)) (.join (.digit 7 1) (.digit 22 1)))) (.join (.join (.join (.digit 2 1) (.digit 0 1)) (.join (.digit 8 1) (.digit 23 1))) (.join (.join (.digit 37 1) (.digit 1 1)) (.join (.digit 8 1) (.digit 67 1))))) (.join (.join (.join (.join (.digit 4 1) (.digit 0 1)) (.join (.digit 11 1) (.digit 10 1))) (.join (.join (.digit 33 1) (.digit 16 1)) (.join (.digit 45 1) (.digit 4 1)))) (.join (.join (.join (.digit 10 1) (.digit 32 1)) (.join (.digit 19 1) (.digit 2 1))) (.join (.join (.digit 5 1) (.digit 1 1)) (.join (.digit 5 1) (.digit 5 1))))))

private def square7Part19 : Word :=
  (.join (.join (.join (.join (.join (.digit 8 1) (.digit 69 1)) (.join (.digit 3 1) (.digit 15 1))) (.join (.join (.digit 0 1) (.digit 6 1)) (.join (.digit 55 1) (.digit 7 1)))) (.join (.join (.join (.digit 2 1) (.digit 1 1)) (.join (.digit 0 1) (.digit 5 1))) (.join (.join (.digit 7 1) (.digit 8 1)) (.join (.digit 23 1) (.digit 47 1))))) (.join (.join (.join (.join (.digit 2 1) (.digit 13 1)) (.join (.digit 0 1) (.digit 2 1))) (.join (.join (.digit 23 1) (.digit 8 1)) (.join (.digit 2 1) (.digit 8 1)))) (.join (.join (.join (.digit 9 1) (.digit 0 1)) (.join (.digit 3 1) (.digit 0 1))) (.join (.join (.digit 4 1) (.digit 0 1)) (.join (.digit 3 1) (.digit 5 1))))))

private def square7Part20 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 1) (.digit 1 1)) (.join (.digit 14 1) (.digit 45 1))) (.join (.join (.digit 9 1) (.digit 16 1)) (.join (.digit 27 1) (.digit 4 1)))) (.join (.join (.join (.digit 10 1) (.digit 0 1)) (.join (.digit 10 1) (.digit 7 1))) (.join (.join (.digit 0 1) (.digit 1 1)) (.join (.digit 6 1) (.digit 1 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 1 1)) (.join (.digit 4 1) (.digit 2 1))) (.join (.join (.digit 5 1) (.digit 8 1)) (.join (.digit 8 1) (.digit 16 1)))) (.join (.join (.join (.digit 7 1) (.digit 15 1)) (.join (.digit 8 1) (.digit 15 1))) (.join (.join (.digit 22 1) (.digit 13 1)) (.join (.digit 7 1) (.digit 3 0))))))

private def square7Part21 : Word :=
  (.join (.join (.join (.join (.join (.digit 32 1) (.digit 0 1)) (.join (.digit 7 1) (.digit 0 1))) (.join (.join (.digit 0 1) (.digit 8 1)) (.join (.digit 10 1) (.digit 11 1)))) (.join (.join (.join (.digit 43 1) (.digit 0 1)) (.join (.digit 3 1) (.digit 52 1))) (.join (.join (.digit 0 1) (.digit 10 1)) (.join (.digit 17 1) (.digit 8 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 4 1)) (.join (.digit 7 1) (.digit 1 1))) (.join (.join (.digit 9 1) (.digit 19 1)) (.join (.digit 11 1) (.digit 0 1)))) (.join (.join (.join (.digit 12 1) (.digit 20 1)) (.join (.digit 3 1) (.digit 1 1))) (.join (.join (.digit 7 1) (.digit 0 1)) (.join (.digit 5 1) (.digit 9 1))))))

private def square7Part22 : Word :=
  (.join (.join (.join (.join (.join (.digit 9 1) (.digit 24 1)) (.join (.digit 11 1) (.digit 6 1))) (.join (.join (.digit 17 1) (.digit 0 1)) (.join (.digit 8 1) (.digit 5 0)))) (.join (.join (.join (.digit 2 1) (.digit 11 1)) (.join (.digit 29 1) (.digit 4 1))) (.join (.join (.digit 6 1) (.digit 9 1)) (.join (.digit 3 1) (.digit 7 1))))) (.join (.join (.join (.join (.digit 4 1) (.digit 0 1)) (.join (.digit 19 1) (.digit 6 1))) (.join (.join (.digit 22 1) (.digit 2 1)) (.join (.digit 3 1) (.digit 10 1)))) (.join (.join (.join (.digit 4 1) (.digit 18 1)) (.join (.digit 2 1) (.digit 1 1))) (.join (.join (.digit 5 1) (.digit 9 1)) (.join (.digit 11 1) (.digit 3 1))))))

private def square7Part23 : Word :=
  (.join (.join (.join (.join (.join (.digit 9 0) (.digit 11 1)) (.join (.digit 11 1) (.digit 5 1))) (.join (.join (.digit 6 1) (.digit 0 1)) (.join (.digit 34 1) (.digit 6 1)))) (.join (.join (.join (.digit 11 1) (.digit 21 1)) (.join (.digit 9 1) (.digit 6 1))) (.join (.join (.digit 0 1) (.digit 6 1)) (.join (.digit 7 1) (.digit 34 1))))) (.join (.join (.join (.join (.digit 4 1) (.digit 10 1)) (.join (.digit 4 1) (.digit 31 1))) (.join (.join (.digit 7 1) (.digit 3 1)) (.join (.digit 11 1) (.digit 10 1)))) (.join (.join (.join (.digit 4 1) (.digit 6 1)) (.join (.digit 4 1) (.digit 27 1))) (.join (.join (.digit 6 1) (.digit 6 1)) (.join (.digit 0 1) (.digit 19 1))))))

private def square7Part24 : Word :=
  (.join (.join (.join (.join (.join (.digit 22 1) (.digit 7 1)) (.join (.digit 1 1) (.digit 62 1))) (.join (.join (.digit 0 1) (.digit 20 1)) (.join (.digit 1 1) (.digit 15 6)))) (.join (.join (.join (.digit 8 1) (.digit 3 1)) (.join (.digit 8 1) (.digit 17 1))) (.join (.join (.digit 9 1) (.digit 21 1)) (.join (.digit 4 1) (.digit 0 1))))) (.join (.join (.join (.join (.digit 6 1) (.digit 4 1)) (.join (.digit 53 0) (.digit 11 1))) (.join (.join (.digit 41 1) (.digit 63 1)) (.join (.digit 27 1) (.digit 42 1)))) (.join (.join (.join (.digit 9 1) (.digit 29 1)) (.join (.digit 7 1) (.digit 8 1))) (.join (.join (.digit 51 1) (.digit 8 1)) (.join (.digit 26 1) (.digit 7 1))))))

private def square7Part25 : Word :=
  (.join (.join (.join (.join (.join (.digit 24 1) (.digit 8 1)) (.join (.digit 10 1) (.digit 10 1))) (.join (.join (.digit 7 1) (.digit 31 1)) (.join (.digit 51 1) (.digit 8 1)))) (.join (.join (.join (.digit 0 1) (.digit 72 1)) (.join (.digit 0 1) (.digit 6 1))) (.join (.join (.digit 22 1) (.digit 7 1)) (.join (.digit 2 1) (.digit 10 1))))) (.join (.join (.join (.join (.digit 8 1) (.digit 32 1)) (.join (.digit 3 1) (.digit 43 1))) (.join (.join (.digit 10 1) (.digit 11 1)) (.join (.digit 23 1) (.digit 0 1)))) (.join (.join (.join (.digit 13 1) (.digit 9 1)) (.join (.digit 1 1) (.digit 7 1))) (.join (.join (.digit 4 1) (.digit 47 1)) (.join (.digit 23 1) (.digit 26 1))))))

private def square7Part26 : Word :=
  (.join (.join (.join (.join (.join (.digit 7 1) (.digit 12 1)) (.join (.digit 17 1) (.digit 17 1))) (.join (.join (.digit 10 1) (.digit 9 1)) (.join (.digit 0 1) (.digit 28 1)))) (.join (.join (.join (.digit 20 1) (.digit 10 1)) (.join (.digit 11 1) (.digit 21 1))) (.join (.join (.digit 15 1) (.digit 0 1)) (.join (.digit 16 1) (.digit 12 1))))) (.join (.join (.join (.join (.digit 0 1) (.digit 18 1)) (.join (.digit 1 1) (.digit 6 1))) (.join (.join (.digit 0 1) (.digit 9 1)) (.join (.digit 0 1) (.digit 10 1)))) (.join (.join (.join (.digit 3 1) (.digit 5 1)) (.join (.digit 31 1) (.digit 7 1))) (.join (.join (.digit 67 1) (.digit 11 1)) (.join (.digit 8 1) (.digit 5 1))))))

private def square7Part27 : Word :=
  (.join (.join (.join (.join (.join (.digit 14 1) (.digit 0 1)) (.join (.digit 40 1) (.digit 27 1))) (.join (.join (.digit 1 1) (.digit 0 1)) (.join (.digit 31 1) (.digit 3 1)))) (.join (.join (.join (.digit 57 1) (.digit 57 1)) (.join (.digit 5 1) (.digit 39 1))) (.join (.join (.digit 28 1) (.digit 12 1)) (.join (.digit 26 1) (.digit 2 1))))) (.join (.join (.join (.join (.digit 15 1) (.digit 8 1)) (.join (.digit 15 1) (.digit 0 1))) (.join (.join (.digit 11 1) (.digit 74 1)) (.join (.digit 8 1) (.digit 14 1)))) (.join (.join (.join (.digit 5 1) (.digit 33 1)) (.join (.digit 8 1) (.digit 67 1))) (.join (.join (.digit 17 1) (.digit 94 1)) (.join (.digit 0 0) (.digit 10 1))))))

private def square7Part28 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 1) (.digit 9 0)) (.join (.digit 32 1) (.digit 11 1))) (.join (.join (.digit 16 1) (.digit 60 1)) (.join (.digit 35 1) (.digit 4 1)))) (.join (.join (.join (.digit 3 1) (.digit 0 1)) (.join (.digit 2 1) (.digit 2 1))) (.join (.join (.digit 2 1) (.digit 4 1)) (.join (.digit 69 1) (.digit 25 1))))) (.join (.join (.join (.join (.digit 24 1) (.digit 8 1)) (.join (.digit 26 1) (.digit 9 0))) (.join (.join (.digit 3 1) (.digit 0 1)) (.join (.digit 2 1) (.digit 6 1)))) (.join (.join (.join (.digit 0 6) (.digit 55 1)) (.join (.digit 1 1) (.digit 5 1))) (.join (.join (.digit 21 1) (.digit 26 1)) (.join (.digit 9 1) (.digit 39 1))))))

private def square7Part29 : Word :=
  (.join (.join (.join (.join (.join (.digit 5 1) (.digit 4 1)) (.join (.digit 0 1) (.digit 1 1))) (.join (.join (.digit 0 1) (.digit 3 1)) (.join (.digit 0 1) (.digit 3 1)))) (.join (.join (.join (.digit 45 1) (.digit 41 1)) (.join (.digit 25 1) (.digit 10 1))) (.join (.join (.digit 16 1) (.digit 16 1)) (.join (.digit 17 0) (.digit 0 1))))) (.join (.join (.join (.join (.digit 0 0) (.digit 20 1)) (.join (.digit 13 1) (.digit 34 1))) (.join (.join (.digit 9 1) (.digit 8 1)) (.join (.digit 8 1) (.digit 22 1)))) (.join (.join (.join (.digit 7 1) (.digit 16 1)) (.join (.digit 36 1) (.digit 2 1))) (.join (.join (.digit 6 1) (.digit 3 1)) (.join (.digit 17 1) (.digit 23 1))))))

private def square7Part30 : Word :=
  (.join (.join (.join (.join (.join (.digit 9 1) (.digit 9 1)) (.join (.digit 4 1) (.digit 34 1))) (.join (.join (.digit 9 1) (.digit 1 1)) (.join (.digit 0 1) (.digit 10 1)))) (.join (.join (.join (.digit 4 1) (.digit 7 1)) (.join (.digit 24 1) (.digit 1 1))) (.join (.join (.digit 8 1) (.digit 4 1)) (.join (.digit 3 1) (.digit 2 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 64 1)) (.join (.digit 91 1) (.digit 4 1))) (.join (.join (.digit 2 1) (.digit 12 1)) (.join (.digit 25 1) (.digit 20 1)))) (.join (.join (.join (.digit 8 6) (.digit 70 1)) (.join (.digit 9 1) (.digit 0 1))) (.join (.join (.digit 25 1) (.digit 2 1)) (.join (.digit 1 1) (.digit 0 1))))))

private def square7Part31 : Word :=
  (.join (.join (.join (.join (.join (.digit 6 1) (.digit 94 1)) (.join (.digit 4 1) (.digit 34 1))) (.join (.join (.digit 20 1) (.digit 47 1)) (.join (.digit 71 1) (.digit 2 1)))) (.join (.join (.join (.digit 25 1) (.digit 15 1)) (.join (.digit 10 1) (.digit 2 1))) (.join (.join (.digit 39 1) (.digit 16 1)) (.join (.digit 55 1) (.digit 58 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 1 1)) (.join (.digit 96 1) (.digit 9 1))) (.join (.join (.digit 3 1) (.digit 6 1)) (.join (.digit 18 1) (.digit 29 1)))) (.join (.join (.join (.digit 14 1) (.digit 0 1)) (.join (.digit 1 1) (.digit 8 1))) (.join (.join (.digit 21 0) (.digit 76 1)) (.join (.digit 7 1) (.digit 87 1))))))

private def square7Part32 : Word :=
  (.join (.join (.join (.join (.join (.digit 5 1) (.digit 6 1)) (.join (.digit 3 1) (.digit 4 1))) (.join (.join (.digit 17 1) (.digit 53 1)) (.join (.digit 0 1) (.digit 10 1)))) (.join (.join (.join (.digit 18 1) (.digit 8 1)) (.join (.digit 57 1) (.digit 7 1))) (.join (.join (.digit 33 1) (.digit 39 1)) (.join (.digit 93 1) (.digit 8 1))))) (.join (.join (.join (.join (.digit 4 1) (.digit 0 1)) (.join (.digit 19 1) (.digit 3 1))) (.join (.join (.digit 6 1) (.digit 24 1)) (.join (.digit 0 1) (.digit 8 1)))) (.join (.join (.join (.digit 82 1) (.digit 19 1)) (.join (.digit 36 1) (.digit 7 1))) (.join (.join (.digit 10 1) (.digit 47 1)) (.join (.digit 38 1) (.digit 72 1))))))

private def square7Part33 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 1) (.digit 9 1)) (.join (.digit 0 1) (.digit 44 1))) (.join (.join (.digit 7 1) (.digit 47 1)) (.join (.digit 55 1) (.digit 73 1)))) (.join (.join (.join (.digit 52 1) (.digit 18 1)) (.join (.digit 8 1) (.digit 11 1))) (.join (.join (.digit 16 1) (.digit 2 1)) (.join (.digit 55 1) (.digit 15 1))))) (.join (.join (.join (.join (.digit 40 0) (.digit 14 1)) (.join (.digit 28 1) (.digit 39 1))) (.join (.join (.digit 71 1) (.digit 39 1)) (.join (.digit 37 1) (.digit 8 1)))) (.join (.join (.join (.digit 1 1) (.digit 8 1)) (.join (.digit 26 1) (.digit 19 1))) (.join (.join (.digit 97 1) (.digit 20 1)) (.join (.digit 7 1) (.digit 0 1))))))

private def square7Part34 : Word :=
  (.join (.join (.join (.join (.join (.digit 7 1) (.digit 1 1)) (.join (.digit 31 1) (.digit 39 1))) (.join (.join (.digit 77 1) (.digit 12 0)) (.join (.digit 7 1) (.digit 0 1)))) (.join (.join (.join (.digit 7 1) (.digit 0 1)) (.join (.digit 256 1) (.digit 10 1))) (.join (.join (.digit 1 1) (.digit 32 1)) (.join (.digit 8 1) (.digit 53 1))))) (.join (.join (.join (.join (.digit 3 1) (.digit 10 1)) (.join (.digit 44 1) (.digit 10 1))) (.join (.join (.digit 5 1) (.digit 7 1)) (.join (.digit 104 1) (.digit 1 0)))) (.join (.join (.join (.digit 5 1) (.digit 47 1)) (.join (.digit 7 1) (.digit 12 1))) (.join (.join (.digit 0 1) (.digit 32 1)) (.join (.digit 61 1) (.digit 8 1))))))

private def square7Part35 : Word :=
  (.join (.join (.join (.join (.join (.digit 7 1) (.digit 0 1)) (.join (.digit 54 1) (.digit 0 1))) (.join (.join (.digit 78 1) (.digit 10 1)) (.join (.digit 28 1) (.digit 10 1)))) (.join (.join (.join (.digit 12 1) (.digit 8 1)) (.join (.digit 103 1) (.digit 8 1))) (.join (.join (.digit 7 1) (.digit 31 1)) (.join (.digit 6 1) (.digit 0 1))))) (.join (.join (.join (.join (.digit 141 1) (.digit 0 1)) (.join (.digit 38 1) (.digit 0 1))) (.join (.join (.digit 52 0) (.digit 19 1)) (.join (.digit 61 1) (.digit 8 1)))) (.join (.join (.join (.digit 41 1) (.digit 55 1)) (.join (.digit 29 1) (.digit 39 1))) (.join (.join (.digit 123 1) (.digit 8 1)) (.join (.digit 252 1) (.digit 25 1))))))

private def square7Part36 : Word :=
  (.join (.join (.join (.join (.join (.digit 8 1) (.digit 4 1)) (.join (.digit 39 1) (.digit 112 1))) (.join (.join (.digit 55 1) (.digit 131 1)) (.join (.digit 41 1) (.digit 8 1)))) (.join (.join (.join (.digit 61 1) (.digit 55 1)) (.join (.digit 118 1) (.digit 35 1))) (.join (.join (.digit 39 1) (.digit 36 1)) (.join (.digit 55 1) (.digit 167 1))))) (.join (.join (.join (.join (.digit 39 1) (.digit 19 1)) (.join (.digit 112 1) (.digit 55 1))) (.join (.join (.digit 58 1) (.digit 39 1)) (.join (.digit 156 0) (.digit 8 1)))) (.join (.join (.join (.digit 8 0) (.digit 181 1)) (.join (.digit 39 1) (.digit 402 1))) (.join (.join (.digit 8 1) (.digit 103 1)) (.join (.digit 8 1) (.digit 46 1))))))

private def square7Part37 : Word :=
  (.join (.join (.join (.join (.digit 8 1) (.digit 446 1)) (.join (.digit 8 1) (.join (.digit 8 0) (.digit 21 1)))) (.join (.join (.digit 8 1) (.digit 81 1)) (.join (.digit 55 1) (.join (.digit 56 0) (.digit 55 1))))) (.join (.join (.join (.digit 55 0) (.digit 286 1)) (.join (.digit 39 1) (.join (.digit 72 1) (.digit 39 1)))) (.join (.join (.digit 15 1) (.digit 39 1)) (.join (.digit 415 0) (.join (.digit 39 1) (.digit 39 0))))))

def square7 : Word :=
  (.join (.join (.join (.join (.join square7Part0 square7Part1) (.join square7Part2 square7Part3)) (.join (.join square7Part4 square7Part5) (.join square7Part6 (.join square7Part7 square7Part8)))) (.join (.join (.join square7Part9 square7Part10) (.join square7Part11 (.join square7Part12 square7Part13))) (.join (.join square7Part14 square7Part15) (.join square7Part16 (.join square7Part17 square7Part18))))) (.join (.join (.join (.join square7Part19 square7Part20) (.join square7Part21 square7Part22)) (.join (.join square7Part23 square7Part24) (.join square7Part25 (.join square7Part26 square7Part27)))) (.join (.join (.join square7Part28 square7Part29) (.join square7Part30 (.join square7Part31 square7Part32))) (.join (.join square7Part33 square7Part34) (.join square7Part35 (.join square7Part36 square7Part37))))))

def key7 : Finset ℕ := {0,1,2,7}

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
private theorem certified7 : certOK root7 square7 key7 := by
  unfold certOK
  constructor <;> decide +kernel

theorem checked7 : support root7.value=key7 ∧ eligible root7.value :=
  cert_sound (by intro d hd; simp [key7] at hd; omega) certified7

end SupportBounds.Symmetric

namespace SupportBounds.Symmetric

open OMA.S_oeis_a397780

private def root8Part0 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 0) (.digit 607 0)) (.join (.digit 309 0) (.digit 572 0))) (.join (.join (.digit 166 0) (.digit 197 0)) (.join (.digit 432 0) (.digit 1668 0)))) (.join (.join (.join (.digit 391 0) (.digit 1126 0)) (.join (.digit 2069 0) (.digit 678 0))) (.join (.join (.digit 61 0) (.digit 1365 0)) (.join (.digit 881 0) (.digit 178 0))))) (.join (.join (.join (.join (.digit 265 0) (.digit 301 0)) (.join (.digit 265 0) (.digit 200 0))) (.join (.join (.digit 938 0) (.digit 3 0)) (.join (.digit 1485 0) (.digit 220 0)))) (.join (.join (.join (.digit 316 0) (.digit 1135 0)) (.join (.digit 794 0) (.digit 435 0))) (.join (.join (.digit 1164 0) (.digit 859 0)) (.join (.digit 18 0) (.digit 871 0))))))

private def root8Part1 : Word :=
  (.join (.join (.join (.join (.join (.digit 585 0) (.digit 1069 0)) (.join (.digit 396 0) (.digit 1316 0))) (.join (.join (.digit 25 0) (.digit 181 0)) (.join (.digit 550 0) (.digit 806 0)))) (.join (.join (.join (.digit 561 0) (.digit 85 0)) (.join (.digit 278 0) (.digit 58 0))) (.join (.join (.digit 56 0) (.digit 603 0)) (.join (.digit 268 0) (.digit 464 0))))) (.join (.join (.join (.join (.digit 630 0) (.digit 256 0)) (.join (.digit 482 0) (.digit 3320 0))) (.join (.join (.digit 68 0) (.digit 30 0)) (.join (.digit 603 0) (.digit 60 0)))) (.join (.join (.join (.digit 534 0) (.digit 1673 0)) (.join (.digit 338 0) (.digit 2246 0))) (.join (.join (.digit 2013 0) (.digit 497 0)) (.join (.digit 522 0) (.digit 419 0))))))

def root8 : Word :=
  (.join root8Part0 root8Part1)

private def square8Part0 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 0) (.digit 607 1)) (.join (.digit 309 1) (.digit 297 0))) (.join (.join (.digit 274 1) (.digit 34 1)) (.join (.digit 131 1) (.digit 177 0)))) (.join (.join (.join (.digit 19 1) (.digit 242 1)) (.join (.digit 166 1) (.digit 22 1))) (.join (.join (.digit 119 1) (.digit 54 1)) (.join (.digit 111 1) (.digit 197 1))))) (.join (.join (.join (.join (.digit 122 1) (.digit 84 0)) (.join (.digit 166 1) (.digit 57 1))) (.join (.join (.digit 108 0) (.digit 30 1)) (.join (.digit 166 1) (.digit 197 0)))) (.join (.join (.join (.digit 67 1) (.digit 166 1)) (.join (.digit 10 1) (.digit 186 1))) (.join (.join (.digit 204 1) (.digit 215 1)) (.join (.digit 11 0) (.digit 297 1))))))

private def square8Part1 : Word :=
  (.join (.join (.join (.join (.join (.digit 81 1) (.digit 309 1)) (.join (.digit 180 1) (.digit 27 1))) (.join (.join (.digit 138 1) (.digit 197 1)) (.join (.digit 26 1) (.digit 166 1)))) (.join (.join (.join (.digit 76 1) (.digit 120 1)) (.join (.digit 40 1) (.digit 147 1))) (.join (.join (.digit 243 1) (.digit 328 1)) (.join (.digit 166 1) (.digit 197 1))))) (.join (.join (.join (.join (.digit 213 1) (.digit 218 1)) (.join (.digit 149 0) (.digit 238 1))) (.join (.join (.digit 70 1) (.digit 61 1)) (.join (.digit 19 1) (.digit 156 1)))) (.join (.join (.join (.digit 234 0) (.digit 133 1)) (.join (.digit 61 1) (.digit 141 1))) (.join (.join (.digit 105 1) (.digit 60 1)) (.join (.digit 0 1) (.digit 196 1))))))

private def square8Part2 : Word :=
  (.join (.join (.join (.join (.join (.digit 31 1) (.digit 218 1)) (.join (.digit 62 1) (.digit 61 1))) (.join (.join (.digit 47 1) (.digit 8 1)) (.join (.digit 47 1) (.digit 61 1)))) (.join (.join (.join (.digit 135 1) (.digit 61 1)) (.join (.digit 117 1) (.digit 252 1))) (.join (.join (.digit 20 1) (.digit 35 1)) (.join (.digit 4 1) (.digit 137 1))))) (.join (.join (.join (.join (.digit 238 0) (.digit 26 1)) (.join (.digit 162 1) (.digit 0 1))) (.join (.join (.digit 137 1) (.digit 28 1)) (.join (.digit 10 1) (.digit 130 1)))) (.join (.join (.join (.digit 50 1) (.digit 4 1)) (.join (.digit 38 1) (.digit 39 1))) (.join (.join (.digit 43 1) (.digit 116 1)) (.join (.digit 140 1) (.digit 5 1))))))

private def square8Part3 : Word :=
  (.join (.join (.join (.join (.join (.digit 1 1) (.digit 43 1)) (.join (.digit 83 1) (.digit 129 1))) (.join (.join (.digit 26 1) (.digit 9 1)) (.join (.digit 6 1) (.digit 4 1)))) (.join (.join (.join (.digit 39 1) (.digit 111 1)) (.join (.digit 14 1) (.digit 18 1))) (.join (.join (.digit 74 1) (.digit 4 1)) (.join (.digit 98 1) (.digit 4 1))))) (.join (.join (.join (.join (.digit 61 1) (.digit 0 1)) (.join (.digit 28 1) (.digit 20 1))) (.join (.join (.digit 3 1) (.digit 80 1)) (.join (.digit 50 1) (.digit 11 1)))) (.join (.join (.join (.digit 103 1) (.digit 62 1)) (.join (.digit 19 1) (.digit 15 1))) (.join (.join (.digit 98 1) (.digit 67 1)) (.join (.digit 33 1) (.digit 28 1))))))

private def square8Part4 : Word :=
  (.join (.join (.join (.join (.join (.digit 26 1) (.digit 3 1)) (.join (.digit 103 1) (.digit 2 1))) (.join (.join (.digit 163 1) (.digit 33 1)) (.join (.digit 0 1) (.digit 3 1)))) (.join (.join (.join (.digit 0 1) (.digit 90 1)) (.join (.digit 61 1) (.digit 72 1))) (.join (.join (.digit 165 1) (.digit 34 1)) (.join (.digit 139 1) (.digit 0 1))))) (.join (.join (.join (.join (.digit 3 1) (.digit 162 1)) (.join (.digit 3 1) (.digit 48 1))) (.join (.join (.digit 93 1) (.digit 50 1)) (.join (.digit 3 1) (.digit 123 1)))) (.join (.join (.join (.digit 43 1) (.digit 69 1)) (.join (.digit 98 1) (.digit 52 1))) (.join (.join (.digit 38 1) (.digit 3 1)) (.join (.digit 25 1) (.digit 56 1))))))

private def square8Part5 : Word :=
  (.join (.join (.join (.join (.join (.digit 28 0) (.digit 2 1)) (.join (.digit 33 1) (.digit 109 1))) (.join (.join (.digit 76 1) (.digit 6 1)) (.join (.digit 5 1) (.digit 175 1)))) (.join (.join (.join (.digit 125 1) (.digit 1 1)) (.join (.digit 34 1) (.digit 37 1))) (.join (.join (.digit 64 1) (.digit 61 1)) (.join (.digit 1 1) (.digit 15 1))))) (.join (.join (.join (.join (.digit 37 1) (.digit 7 1)) (.join (.digit 113 1) (.digit 21 1))) (.join (.join (.digit 22 1) (.digit 41 1)) (.join (.digit 91 1) (.digit 15 1)))) (.join (.join (.join (.digit 47 1) (.digit 118 1)) (.join (.digit 76 0) (.digit 5 1))) (.join (.join (.digit 2 1) (.digit 6 1)) (.join (.digit 45 1) (.digit 58 1))))))

private def square8Part6 : Word :=
  (.join (.join (.join (.join (.join (.digit 2 0) (.digit 70 1)) (.join (.digit 0 1) (.digit 2 1))) (.join (.join (.digit 37 1) (.digit 70 1)) (.join (.digit 10 1) (.digit 234 1)))) (.join (.join (.join (.digit 19 1) (.digit 12 1)) (.join (.digit 3 1) (.digit 40 1))) (.join (.join (.digit 116 1) (.digit 25 1)) (.join (.digit 28 1) (.digit 87 1))))) (.join (.join (.join (.join (.digit 166 1) (.digit 54 1)) (.join (.digit 125 1) (.digit 16 1))) (.join (.join (.digit 170 1) (.digit 61 1)) (.join (.digit 59 1) (.digit 80 1)))) (.join (.join (.join (.digit 53 1) (.digit 1 1)) (.join (.digit 2 1) (.digit 23 1))) (.join (.join (.digit 3 1) (.digit 78 1)) (.join (.digit 12 1) (.digit 43 1))))))

private def square8Part7 : Word :=
  (.join (.join (.join (.join (.join (.digit 51 1) (.digit 145 1)) (.join (.digit 23 1) (.digit 0 1))) (.join (.join (.digit 45 1) (.digit 99 1)) (.join (.digit 66 1) (.digit 7 1)))) (.join (.join (.join (.digit 11 1) (.digit 61 1)) (.join (.digit 5 1) (.digit 26 1))) (.join (.join (.digit 79 1) (.digit 2 1)) (.join (.digit 0 1) (.digit 61 1))))) (.join (.join (.join (.join (.digit 63 1) (.digit 28 1)) (.join (.digit 12 1) (.digit 18 1))) (.join (.join (.digit 38 1) (.digit 39 1)) (.join (.digit 61 1) (.digit 27 1)))) (.join (.join (.join (.digit 10 0) (.digit 64 1)) (.join (.digit 135 1) (.digit 61 1))) (.join (.join (.digit 84 1) (.digit 60 1)) (.join (.digit 18 1) (.digit 3 1))))))

private def square8Part8 : Word :=
  (.join (.join (.join (.join (.join (.digit 34 1) (.digit 35 1)) (.join (.digit 25 1) (.digit 39 1))) (.join (.join (.digit 29 1) (.digit 68 1)) (.join (.digit 23 1) (.digit 26 1)))) (.join (.join (.join (.digit 10 1) (.digit 7 1)) (.join (.digit 58 1) (.digit 84 1))) (.join (.join (.digit 3 1) (.digit 8 1)) (.join (.digit 32 1) (.digit 3 1))))) (.join (.join (.join (.join (.digit 128 1) (.digit 168 1)) (.join (.digit 47 1) (.digit 13 1))) (.join (.join (.digit 5 1) (.digit 1 1)) (.join (.digit 10 1) (.digit 15 1)))) (.join (.join (.join (.digit 131 1) (.digit 18 1)) (.join (.digit 128 1) (.digit 2 1))) (.join (.join (.digit 0 1) (.digit 17 1)) (.join (.digit 27 1) (.digit 11 1))))))

private def square8Part9 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 2 1)) (.join (.digit 13 1) (.digit 43 1))) (.join (.join (.digit 29 0) (.digit 121 1)) (.join (.digit 8 1) (.digit 47 1)))) (.join (.join (.join (.digit 78 1) (.digit 67 1)) (.join (.digit 5 1) (.digit 12 1))) (.join (.join (.digit 12 0) (.digit 3 1)) (.join (.digit 56 1) (.digit 12 1))))) (.join (.join (.join (.join (.digit 12 1) (.digit 138 1)) (.join (.digit 1 1) (.digit 37 1))) (.join (.join (.digit 29 1) (.digit 92 1)) (.join (.digit 36 1) (.digit 90 1)))) (.join (.join (.join (.digit 14 0) (.digit 35 1)) (.join (.digit 54 1) (.digit 23 1))) (.join (.join (.digit 7 1) (.digit 39 1)) (.join (.digit 81 1) (.digit 36 1))))))

private def square8Part10 : Word :=
  (.join (.join (.join (.join (.join (.digit 19 7) (.digit 21 1)) (.join (.digit 2 1) (.digit 53 1))) (.join (.join (.digit 3 1) (.digit 57 1)) (.join (.digit 36 1) (.digit 22 1)))) (.join (.join (.join (.digit 1 1) (.digit 62 1)) (.join (.digit 30 1) (.digit 4 0))) (.join (.join (.digit 7 1) (.digit 24 1)) (.join (.digit 26 1) (.digit 34 1))))) (.join (.join (.join (.join (.digit 26 1) (.digit 42 1)) (.join (.digit 100 1) (.digit 42 1))) (.join (.join (.digit 67 1) (.digit 27 1)) (.join (.digit 33 1) (.digit 27 1)))) (.join (.join (.join (.digit 33 1) (.digit 18 1)) (.join (.digit 11 0) (.digit 48 1))) (.join (.join (.digit 77 1) (.digit 3 1)) (.join (.digit 69 1) (.digit 14 1))))))

private def square8Part11 : Word :=
  (.join (.join (.join (.join (.join (.digit 55 1) (.digit 25 1)) (.join (.digit 3 1) (.digit 3 1))) (.join (.join (.digit 3 1) (.digit 50 1)) (.join (.digit 18 1) (.digit 21 0)))) (.join (.join (.join (.digit 11 1) (.digit 31 1)) (.join (.digit 33 1) (.digit 91 1))) (.join (.join (.digit 3 1) (.digit 36 1)) (.join (.digit 14 1) (.digit 106 1))))) (.join (.join (.join (.join (.digit 75 1) (.digit 35 1)) (.join (.digit 12 1) (.digit 13 1))) (.join (.join (.digit 3 1) (.digit 1 1)) (.join (.digit 25 1) (.digit 49 1)))) (.join (.join (.join (.digit 24 1) (.digit 49 1)) (.join (.digit 11 1) (.digit 44 1))) (.join (.join (.digit 8 1) (.digit 42 1)) (.join (.digit 3 1) (.digit 45 1))))))

private def square8Part12 : Word :=
  (.join (.join (.join (.join (.join (.digit 25 1) (.digit 27 1)) (.join (.digit 7 1) (.digit 20 1))) (.join (.join (.digit 67 1) (.digit 3 1)) (.join (.digit 52 1) (.digit 47 1)))) (.join (.join (.join (.digit 41 1) (.digit 18 1)) (.join (.digit 25 1) (.digit 83 1))) (.join (.join (.digit 21 1) (.digit 123 1)) (.join (.digit 12 1) (.digit 12 1))))) (.join (.join (.join (.join (.digit 6 1) (.digit 41 7)) (.join (.digit 91 1) (.digit 18 1))) (.join (.join (.digit 6 1) (.digit 14 1)) (.join (.digit 45 1) (.digit 44 1)))) (.join (.join (.join (.digit 65 1) (.digit 9 1)) (.join (.digit 15 1) (.digit 0 1))) (.join (.join (.digit 56 1) (.digit 61 1)) (.join (.digit 5 0) (.digit 2 1))))))

private def square8Part13 : Word :=
  (.join (.join (.join (.join (.join (.digit 0 1) (.digit 3 0)) (.join (.digit 45 1) (.digit 1 1))) (.join (.join (.digit 27 1) (.digit 14 1)) (.join (.digit 20 1) (.digit 8 1)))) (.join (.join (.join (.digit 36 1) (.digit 39 1)) (.join (.digit 29 1) (.digit 5 1))) (.join (.join (.digit 38 1) (.digit 23 1)) (.join (.digit 1 1) (.digit 12 1))))) (.join (.join (.join (.join (.digit 29 1) (.digit 58 1)) (.join (.digit 8 1) (.digit 57 1))) (.join (.join (.digit 8 1) (.digit 3 1)) (.join (.digit 54 1) (.digit 6 1)))) (.join (.join (.join (.digit 19 1) (.digit 29 1)) (.join (.digit 5 1) (.digit 14 1))) (.join (.join (.digit 5 1) (.digit 4 1)) (.join (.digit 51 1) (.digit 42 1))))))

private def square8Part14 : Word :=
  (.join (.join (.join (.join (.join (.digit 43 1) (.digit 41 1)) (.join (.digit 73 1) (.digit 35 1))) (.join (.join (.digit 86 1) (.digit 13 1)) (.join (.digit 12 1) (.digit 1 1)))) (.join (.join (.join (.digit 8 1) (.digit 39 1)) (.join (.digit 3 1) (.digit 3 1))) (.join (.join (.digit 26 1) (.digit 27 1)) (.join (.digit 6 1) (.digit 30 1))))) (.join (.join (.join (.join (.digit 14 1) (.digit 3 1)) (.join (.digit 6 1) (.digit 61 1))) (.join (.join (.digit 18 1) (.digit 62 1)) (.join (.digit 42 1) (.digit 10 1)))) (.join (.join (.join (.digit 41 1) (.digit 5 1)) (.join (.digit 11 1) (.digit 15 1))) (.join (.join (.digit 3 1) (.digit 24 1)) (.join (.digit 91 1) (.digit 85 1))))))

private def square8Part15 : Word :=
  (.join (.join (.join (.join (.join (.digit 13 1) (.digit 3 1)) (.join (.digit 39 1) (.digit 2 1))) (.join (.join (.digit 19 1) (.digit 27 1)) (.join (.digit 6 1) (.digit 33 1)))) (.join (.join (.join (.digit 16 1) (.digit 74 1)) (.join (.digit 10 1) (.digit 6 1))) (.join (.join (.digit 18 7) (.digit 8 1)) (.join (.digit 33 1) (.digit 4 1))))) (.join (.join (.join (.join (.digit 3 1) (.digit 3 1)) (.join (.digit 2 1) (.digit 2 1))) (.join (.join (.digit 23 1) (.digit 19 1)) (.join (.digit 9 1) (.digit 30 1)))) (.join (.join (.join (.digit 19 1) (.digit 8 1)) (.join (.digit 5 1) (.digit 10 1))) (.join (.join (.digit 32 1) (.digit 22 1)) (.join (.digit 16 1) (.digit 8 1))))))

private def square8Part16 : Word :=
  (.join (.join (.join (.join (.join (.digit 7 1) (.digit 81 1)) (.join (.digit 0 1) (.digit 25 1))) (.join (.join (.digit 23 1) (.digit 7 1)) (.join (.digit 8 1) (.digit 11 1)))) (.join (.join (.join (.digit 35 1) (.digit 37 1)) (.join (.digit 29 1) (.digit 21 1))) (.join (.join (.digit 2 1) (.digit 2 1)) (.join (.digit 16 1) (.digit 116 1))))) (.join (.join (.join (.join (.digit 8 1) (.digit 12 1)) (.join (.digit 45 1) (.digit 18 1))) (.join (.join (.digit 44 1) (.digit 7 1)) (.join (.digit 5 1) (.digit 14 1)))) (.join (.join (.join (.digit 8 1) (.digit 5 1)) (.join (.digit 26 1) (.digit 19 1))) (.join (.join (.digit 54 1) (.digit 14 0)) (.join (.digit 8 1) (.digit 30 1))))))

private def square8Part17 : Word :=
  (.join (.join (.join (.join (.join (.digit 40 1) (.digit 39 1)) (.join (.digit 30 1) (.digit 31 1))) (.join (.join (.digit 3 1) (.digit 9 1)) (.join (.digit 22 1) (.digit 53 1)))) (.join (.join (.join (.digit 54 1) (.digit 19 1)) (.join (.digit 54 1) (.digit 18 1))) (.join (.join (.digit 2 1) (.digit 14 0)) (.join (.digit 7 1) (.digit 3 1))))) (.join (.join (.join (.join (.digit 0 1) (.digit 20 1)) (.join (.digit 12 1) (.digit 18 1))) (.join (.join (.digit 5 1) (.digit 0 1)) (.join (.digit 0 1) (.digit 19 1)))) (.join (.join (.join (.digit 1 1) (.digit 67 1)) (.join (.digit 10 1) (.digit 79 1))) (.join (.join (.digit 61 1) (.digit 5 1)) (.join (.digit 17 1) (.digit 31 1))))))

private def square8Part18 : Word :=
  (.join (.join (.join (.join (.join (.digit 29 1) (.digit 26 1)) (.join (.digit 55 1) (.digit 9 1))) (.join (.join (.digit 40 1) (.digit 3 1)) (.join (.digit 92 0) (.digit 4 1)))) (.join (.join (.join (.digit 16 1) (.digit 75 1)) (.join (.digit 9 1) (.digit 57 1))) (.join (.join (.digit 5 7) (.digit 38 1)) (.join (.digit 8 1) (.digit 9 1))))) (.join (.join (.join (.join (.digit 31 1) (.digit 76 1)) (.join (.digit 3 1) (.digit 20 1))) (.join (.join (.digit 5 1) (.digit 16 1)) (.join (.digit 2 1) (.digit 18 1)))) (.join (.join (.join (.digit 4 1) (.digit 14 1)) (.join (.digit 16 1) (.digit 1 1))) (.join (.join (.digit 51 1) (.digit 2 1)) (.join (.digit 6 1) (.digit 54 1))))))

private def square8Part19 : Word :=
  (.join (.join (.join (.join (.join (.digit 32 1) (.digit 28 1)) (.join (.digit 28 1) (.digit 18 1))) (.join (.join (.digit 69 1) (.digit 33 1)) (.join (.digit 23 1) (.digit 2 1)))) (.join (.join (.join (.digit 12 1) (.digit 18 1)) (.join (.digit 6 1) (.digit 49 1))) (.join (.join (.digit 11 1) (.digit 4 1)) (.join (.digit 45 1) (.digit 18 1))))) (.join (.join (.join (.join (.digit 1 1) (.digit 80 1)) (.join (.digit 41 1) (.digit 4 1))) (.join (.join (.digit 2 1) (.digit 25 1)) (.join (.digit 87 1) (.digit 18 1)))) (.join (.join (.join (.digit 37 1) (.digit 94 1)) (.join (.digit 16 1) (.digit 31 1))) (.join (.join (.digit 18 1) (.digit 38 1)) (.join (.digit 15 1) (.digit 4 1))))))

private def square8Part20 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 0 1)) (.join (.digit 31 1) (.digit 1 1))) (.join (.join (.digit 3 1) (.digit 66 1)) (.join (.digit 12 1) (.digit 60 1)))) (.join (.join (.join (.digit 2 1) (.digit 76 1)) (.join (.digit 60 1) (.digit 11 1))) (.join (.join (.digit 7 1) (.digit 17 1)) (.join (.digit 8 1) (.digit 29 1))))) (.join (.join (.join (.join (.digit 24 1) (.digit 33 1)) (.join (.digit 56 1) (.digit 27 1))) (.join (.join (.digit 64 1) (.digit 17 1)) (.join (.digit 28 1) (.digit 25 1)))) (.join (.join (.join (.digit 35 1) (.digit 8 1)) (.join (.digit 8 1) (.digit 7 1))) (.join (.join (.digit 21 0) (.digit 0 1)) (.join (.digit 42 1) (.digit 47 1))))))

private def square8Part21 : Word :=
  (.join (.join (.join (.join (.join (.digit 2 1) (.digit 0 1)) (.join (.digit 1 1) (.digit 12 1))) (.join (.join (.digit 3 1) (.digit 44 1)) (.join (.digit 2 1) (.digit 36 1)))) (.join (.join (.join (.digit 102 1) (.digit 50 1)) (.join (.digit 17 1) (.digit 30 1))) (.join (.join (.digit 25 1) (.digit 27 1)) (.join (.digit 28 1) (.digit 105 1))))) (.join (.join (.join (.join (.digit 30 1) (.digit 6 1)) (.join (.digit 18 1) (.digit 15 1))) (.join (.join (.digit 45 1) (.digit 10 1)) (.join (.digit 54 1) (.digit 17 1)))) (.join (.join (.join (.digit 53 1) (.digit 33 1)) (.join (.digit 27 1) (.digit 19 1))) (.join (.join (.digit 8 1) (.digit 2 1)) (.join (.digit 36 1) (.digit 2 1))))))

private def square8Part22 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 19 1)) (.join (.digit 3 1) (.digit 50 1))) (.join (.join (.digit 5 1) (.digit 19 1)) (.join (.digit 132 1) (.digit 9 1)))) (.join (.join (.join (.digit 1 1) (.digit 26 1)) (.join (.digit 29 1) (.digit 27 1))) (.join (.join (.digit 2 1) (.digit 6 1)) (.join (.digit 3 1) (.digit 6 1))))) (.join (.join (.join (.join (.digit 4 1) (.digit 80 1)) (.join (.digit 30 1) (.digit 42 1))) (.join (.join (.digit 18 1) (.digit 7 1)) (.join (.digit 42 1) (.digit 3 1)))) (.join (.join (.join (.digit 8 1) (.digit 7 0)) (.join (.digit 10 1) (.digit 1 1))) (.join (.join (.digit 11 1) (.digit 14 1)) (.join (.digit 45 1) (.digit 23 1))))))

private def square8Part23 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 14 1)) (.join (.digit 43 1) (.digit 30 1))) (.join (.join (.digit 8 1) (.digit 16 1)) (.join (.digit 1 1) (.digit 40 1)))) (.join (.join (.join (.digit 30 1) (.digit 1 1)) (.join (.digit 28 1) (.digit 35 1))) (.join (.join (.digit 14 1) (.digit 9 1)) (.join (.digit 31 1) (.digit 7 1))))) (.join (.join (.join (.join (.digit 3 1) (.digit 30 1)) (.join (.digit 15 1) (.digit 2 1))) (.join (.join (.digit 16 1) (.digit 6 1)) (.join (.digit 15 1) (.digit 18 1)))) (.join (.join (.join (.digit 19 1) (.digit 6 1)) (.join (.digit 33 1) (.digit 10 1))) (.join (.join (.digit 14 1) (.digit 1 1)) (.join (.digit 30 1) (.digit 119 1))))))

private def square8Part24 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 12 1)) (.join (.digit 8 1) (.digit 2 1))) (.join (.join (.digit 15 1) (.digit 17 1)) (.join (.digit 2 1) (.digit 13 1)))) (.join (.join (.join (.digit 2 0) (.digit 10 1)) (.join (.digit 24 1) (.digit 0 1))) (.join (.join (.digit 4 1) (.digit 16 1)) (.join (.digit 37 1) (.digit 1 1))))) (.join (.join (.join (.join (.digit 25 1) (.digit 4 1)) (.join (.digit 46 1) (.digit 3 1))) (.join (.join (.digit 1 1) (.digit 15 1)) (.join (.digit 3 1) (.digit 5 1)))) (.join (.join (.join (.digit 20 1) (.digit 0 1)) (.join (.digit 0 1) (.digit 31 1))) (.join (.join (.digit 126 1) (.digit 9 1)) (.join (.digit 20 1) (.digit 39 1))))))

private def square8Part25 : Word :=
  (.join (.join (.join (.join (.join (.digit 22 1) (.digit 11 1)) (.join (.digit 13 1) (.digit 37 1))) (.join (.join (.digit 24 1) (.digit 3 1)) (.join (.digit 18 1) (.digit 34 1)))) (.join (.join (.join (.digit 8 1) (.digit 34 1)) (.join (.digit 16 1) (.digit 2 1))) (.join (.join (.digit 6 1) (.digit 25 1)) (.join (.digit 21 1) (.digit 25 1))))) (.join (.join (.join (.join (.digit 16 1) (.digit 4 1)) (.join (.digit 13 1) (.digit 1 1))) (.join (.join (.digit 2 1) (.digit 15 1)) (.join (.digit 60 1) (.digit 14 1)))) (.join (.join (.join (.digit 31 1) (.digit 9 1)) (.join (.digit 6 1) (.digit 12 1))) (.join (.join (.digit 5 1) (.digit 5 1)) (.join (.digit 12 1) (.digit 72 1))))))

private def square8Part26 : Word :=
  (.join (.join (.join (.join (.join (.digit 64 1) (.digit 18 1)) (.join (.digit 5 1) (.digit 4 1))) (.join (.join (.digit 78 1) (.digit 59 1)) (.join (.digit 22 1) (.digit 21 1)))) (.join (.join (.join (.digit 25 1) (.digit 32 1)) (.join (.digit 14 1) (.digit 6 1))) (.join (.join (.digit 6 1) (.digit 27 1)) (.join (.digit 17 1) (.digit 26 1))))) (.join (.join (.join (.join (.digit 73 1) (.digit 4 1)) (.join (.digit 18 1) (.digit 58 1))) (.join (.join (.digit 17 1) (.digit 25 1)) (.join (.digit 21 1) (.digit 15 1)))) (.join (.join (.join (.digit 12 1) (.digit 36 1)) (.join (.digit 66 1) (.digit 1 1))) (.join (.join (.digit 19 1) (.digit 2 1)) (.join (.digit 3 1) (.digit 3 1))))))

private def square8Part27 : Word :=
  (.join (.join (.join (.join (.join (.digit 17 1) (.digit 3 1)) (.join (.digit 30 1) (.digit 53 1))) (.join (.join (.digit 18 1) (.digit 18 1)) (.join (.digit 0 1) (.digit 5 1)))) (.join (.join (.join (.digit 12 1) (.digit 2 1)) (.join (.digit 0 1) (.digit 0 1))) (.join (.join (.digit 2 1) (.digit 26 1)) (.join (.digit 3 1) (.digit 27 1))))) (.join (.join (.join (.join (.digit 59 1) (.digit 13 1)) (.join (.digit 25 1) (.digit 28 1))) (.join (.join (.digit 2 1) (.digit 7 1)) (.join (.digit 13 1) (.digit 4 1)))) (.join (.join (.join (.digit 0 1) (.digit 14 1)) (.join (.digit 4 1) (.digit 5 1))) (.join (.join (.digit 7 1) (.digit 4 0)) (.join (.digit 7 1) (.digit 8 1))))))

private def square8Part28 : Word :=
  (.join (.join (.join (.join (.join (.digit 49 1) (.digit 12 1)) (.join (.digit 58 1) (.digit 3 1))) (.join (.join (.digit 6 1) (.digit 22 1)) (.join (.digit 14 1) (.digit 7 1)))) (.join (.join (.join (.digit 37 1) (.digit 37 1)) (.join (.digit 10 1) (.digit 31 1))) (.join (.join (.digit 4 1) (.digit 3 1)) (.join (.digit 16 1) (.digit 4 1))))) (.join (.join (.join (.join (.digit 22 1) (.digit 35 1)) (.join (.digit 10 1) (.digit 45 1))) (.join (.join (.digit 10 1) (.digit 4 1)) (.join (.digit 3 1) (.digit 66 1)))) (.join (.join (.join (.digit 15 1) (.digit 20 1)) (.join (.digit 34 1) (.digit 4 1))) (.join (.join (.digit 8 1) (.digit 12 1)) (.join (.digit 31 1) (.digit 26 1))))))

private def square8Part29 : Word :=
  (.join (.join (.join (.join (.join (.digit 28 1) (.digit 13 1)) (.join (.digit 13 1) (.digit 4 1))) (.join (.join (.digit 4 1) (.digit 25 1)) (.join (.digit 35 1) (.digit 23 1)))) (.join (.join (.join (.digit 18 1) (.digit 10 1)) (.join (.digit 23 1) (.digit 58 1))) (.join (.join (.digit 14 1) (.digit 22 1)) (.join (.digit 18 1) (.digit 20 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 8 1)) (.join (.digit 2 1) (.digit 1 1))) (.join (.join (.digit 5 1) (.digit 10 1)) (.join (.digit 15 1) (.digit 8 1)))) (.join (.join (.join (.digit 1 1) (.digit 11 1)) (.join (.digit 3 1) (.digit 29 1))) (.join (.join (.digit 10 1) (.digit 1 1)) (.join (.digit 56 1) (.digit 27 1))))))

private def square8Part30 : Word :=
  (.join (.join (.join (.join (.join (.digit 12 1) (.digit 25 1)) (.join (.digit 36 1) (.digit 19 1))) (.join (.join (.digit 5 1) (.digit 6 1)) (.join (.digit 39 1) (.digit 71 1)))) (.join (.join (.join (.digit 53 1) (.digit 54 1)) (.join (.digit 25 1) (.digit 18 1))) (.join (.join (.digit 2 1) (.digit 41 1)) (.join (.digit 9 1) (.digit 2 1))))) (.join (.join (.join (.join (.digit 0 1) (.digit 26 0)) (.join (.digit 18 1) (.digit 11 1))) (.join (.join (.digit 1 1) (.digit 4 0)) (.join (.digit 16 1) (.digit 3 1)))) (.join (.join (.join (.digit 17 1) (.digit 2 1)) (.join (.digit 5 1) (.digit 3 1))) (.join (.join (.digit 24 1) (.digit 8 1)) (.join (.digit 58 1) (.digit 82 1))))))

private def square8Part31 : Word :=
  (.join (.join (.join (.join (.join (.digit 2 1) (.digit 41 1)) (.join (.digit 22 1) (.digit 3 1))) (.join (.join (.digit 43 1) (.digit 1 1)) (.join (.digit 8 1) (.digit 3 1)))) (.join (.join (.join (.digit 47 1) (.digit 4 1)) (.join (.digit 3 1) (.digit 28 1))) (.join (.join (.digit 38 1) (.digit 0 1)) (.join (.digit 44 1) (.digit 48 1))))) (.join (.join (.join (.join (.digit 10 1) (.digit 19 1)) (.join (.digit 53 1) (.digit 8 1))) (.join (.join (.digit 11 1) (.digit 118 1)) (.join (.digit 6 1) (.digit 41 1)))) (.join (.join (.join (.digit 5 1) (.digit 12 1)) (.join (.digit 8 1) (.digit 48 1))) (.join (.join (.digit 36 1) (.digit 0 1)) (.join (.digit 2 1) (.digit 3 1))))))

private def square8Part32 : Word :=
  (.join (.join (.join (.join (.join (.digit 17 1) (.digit 22 1)) (.join (.digit 3 1) (.digit 3 1))) (.join (.join (.digit 52 1) (.digit 2 1)) (.join (.digit 66 1) (.digit 21 1)))) (.join (.join (.join (.digit 5 1) (.digit 56 1)) (.join (.digit 8 1) (.digit 43 1))) (.join (.join (.digit 3 1) (.digit 10 1)) (.join (.digit 26 1) (.digit 41 1))))) (.join (.join (.join (.join (.digit 27 1) (.digit 2 1)) (.join (.digit 12 1) (.digit 2 1))) (.join (.join (.digit 4 1) (.digit 17 1)) (.join (.digit 2 1) (.digit 15 1)))) (.join (.join (.join (.digit 39 1) (.digit 8 1)) (.join (.digit 94 1) (.digit 39 1))) (.join (.join (.digit 6 1) (.digit 49 1)) (.join (.digit 15 1) (.digit 10 1))))))

private def square8Part33 : Word :=
  (.join (.join (.join (.join (.join (.digit 1 1) (.digit 15 0)) (.join (.digit 5 1) (.digit 3 1))) (.join (.join (.digit 7 1) (.digit 23 1)) (.join (.digit 1 1) (.digit 36 1)))) (.join (.join (.join (.digit 19 1) (.digit 56 1)) (.join (.digit 32 1) (.digit 23 1))) (.join (.join (.digit 10 1) (.digit 8 1)) (.join (.digit 1 1) (.digit 22 1))))) (.join (.join (.join (.join (.digit 2 1) (.digit 33 1)) (.join (.digit 3 1) (.digit 0 1))) (.join (.join (.digit 1 1) (.digit 16 1)) (.join (.digit 0 1) (.digit 12 1)))) (.join (.join (.join (.digit 30 1) (.digit 12 1)) (.join (.digit 17 1) (.digit 40 1))) (.join (.join (.digit 15 1) (.digit 5 1)) (.join (.digit 19 1) (.digit 20 1))))))

private def square8Part34 : Word :=
  (.join (.join (.join (.join (.join (.digit 78 1) (.digit 5 1)) (.join (.digit 17 1) (.digit 32 1))) (.join (.join (.digit 1 1) (.digit 1 1)) (.join (.digit 20 1) (.digit 26 1)))) (.join (.join (.join (.digit 6 1) (.digit 65 1)) (.join (.digit 2 1) (.digit 11 1))) (.join (.join (.digit 6 1) (.digit 4 1)) (.join (.digit 9 1) (.digit 56 1))))) (.join (.join (.join (.join (.digit 37 1) (.digit 3 1)) (.join (.digit 40 1) (.digit 43 1))) (.join (.join (.digit 15 1) (.digit 0 1)) (.join (.digit 0 1) (.digit 22 1)))) (.join (.join (.join (.digit 6 1) (.digit 30 1)) (.join (.digit 11 1) (.digit 87 1))) (.join (.join (.digit 9 0) (.digit 8 1)) (.join (.digit 30 1) (.digit 0 1))))))

private def square8Part35 : Word :=
  (.join (.join (.join (.join (.join (.digit 27 1) (.digit 10 1)) (.join (.digit 47 1) (.digit 50 1))) (.join (.join (.digit 25 1) (.digit 3 1)) (.join (.digit 55 1) (.digit 1 1)))) (.join (.join (.join (.digit 56 1) (.digit 25 1)) (.join (.digit 4 1) (.digit 7 1))) (.join (.join (.digit 33 1) (.digit 2 1)) (.join (.digit 11 1) (.digit 12 1))))) (.join (.join (.join (.join (.digit 21 1) (.digit 12 1)) (.join (.digit 12 1) (.digit 10 1))) (.join (.join (.digit 6 1) (.digit 52 1)) (.join (.digit 0 1) (.digit 14 1)))) (.join (.join (.join (.digit 6 1) (.digit 23 1)) (.join (.digit 11 1) (.digit 51 1))) (.join (.join (.digit 4 1) (.digit 39 1)) (.join (.digit 46 1) (.digit 17 1))))))

private def square8Part36 : Word :=
  (.join (.join (.join (.join (.join (.digit 4 1) (.digit 77 1)) (.join (.digit 13 1) (.digit 18 1))) (.join (.join (.digit 41 1) (.digit 31 1)) (.join (.digit 18 1) (.digit 85 1)))) (.join (.join (.join (.digit 9 1) (.digit 19 1)) (.join (.digit 85 1) (.digit 18 1))) (.join (.join (.digit 2 1) (.digit 7 1)) (.join (.digit 5 1) (.digit 43 1))))) (.join (.join (.join (.join (.digit 7 1) (.digit 23 1)) (.join (.digit 18 1) (.digit 18 1))) (.join (.join (.digit 6 1) (.digit 5 1)) (.join (.digit 3 1) (.digit 8 1)))) (.join (.join (.join (.digit 5 1) (.digit 14 1)) (.join (.digit 24 1) (.digit 11 1))) (.join (.join (.digit 22 1) (.digit 8 1)) (.join (.digit 12 1) (.digit 11 1))))))

private def square8Part37 : Word :=
  (.join (.join (.join (.join (.join (.digit 5 1) (.digit 19 1)) (.join (.digit 2 1) (.digit 13 1))) (.join (.join (.digit 4 1) (.digit 17 1)) (.join (.digit 0 1) (.digit 17 1)))) (.join (.join (.join (.digit 68 1) (.digit 30 1)) (.join (.digit 42 1) (.digit 1 1))) (.join (.join (.digit 10 1) (.digit 12 1)) (.join (.digit 28 1) (.digit 24 1))))) (.join (.join (.join (.join (.digit 15 1) (.digit 26 1)) (.join (.digit 15 1) (.digit 39 1))) (.join (.join (.digit 12 1) (.digit 3 1)) (.join (.digit 24 1) (.digit 1 1)))) (.join (.join (.join (.digit 79 1) (.digit 14 1)) (.join (.digit 23 1) (.digit 21 1))) (.join (.join (.digit 6 1) (.digit 10 1)) (.join (.digit 7 1) (.digit 13 1))))))

private def square8Part38 : Word :=
  (.join (.join (.join (.join (.join (.digit 20 1) (.digit 17 1)) (.join (.digit 1 0) (.digit 0 1))) (.join (.join (.digit 47 1) (.digit 8 1)) (.join (.digit 21 1) (.digit 3 1)))) (.join (.join (.join (.digit 8 1) (.digit 22 1)) (.join (.digit 60 1) (.digit 10 1))) (.join (.join (.digit 40 1) (.digit 6 1)) (.join (.digit 9 1) (.digit 19 1))))) (.join (.join (.join (.join (.digit 31 1) (.digit 16 1)) (.join (.digit 30 1) (.digit 8 1))) (.join (.join (.digit 26 1) (.digit 14 1)) (.join (.digit 37 1) (.digit 7 1)))) (.join (.join (.join (.digit 3 1) (.digit 41 1)) (.join (.digit 26 1) (.digit 4 1))) (.join (.join (.digit 11 1) (.digit 13 1)) (.join (.digit 73 1) (.digit 2 1))))))

private def square8Part39 : Word :=
  (.join (.join (.join (.join (.join (.digit 19 1) (.digit 8 1)) (.join (.digit 16 1) (.digit 13 1))) (.join (.join (.digit 27 1) (.digit 14 1)) (.join (.digit 5 1) (.digit 11 1)))) (.join (.join (.join (.digit 0 1) (.digit 5 1)) (.join (.digit 41 0) (.digit 5 1))) (.join (.join (.digit 16 1) (.digit 34 1)) (.join (.digit 6 1) (.digit 56 1))))) (.join (.join (.join (.join (.digit 33 1) (.digit 27 1)) (.join (.digit 32 1) (.digit 77 1))) (.join (.join (.digit 29 1) (.digit 31 1)) (.join (.digit 60 1) (.digit 16 1)))) (.join (.join (.join (.digit 20 1) (.digit 29 1)) (.join (.digit 3 1) (.digit 10 1))) (.join (.join (.digit 18 1) (.digit 10 1)) (.join (.digit 55 1) (.digit 4 1))))))

private def square8Part40 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 9 1)) (.join (.digit 2 1) (.digit 51 1))) (.join (.join (.digit 3 1) (.digit 26 1)) (.join (.digit 3 1) (.digit 29 1)))) (.join (.join (.join (.digit 20 1) (.digit 4 1)) (.join (.digit 77 1) (.digit 17 1))) (.join (.join (.digit 17 1) (.digit 3 1)) (.join (.digit 5 1) (.digit 8 1))))) (.join (.join (.join (.join (.digit 34 1) (.digit 4 1)) (.join (.digit 0 1) (.digit 17 1))) (.join (.join (.digit 1 1) (.digit 6 1)) (.join (.digit 0 1) (.digit 27 1)))) (.join (.join (.join (.digit 12 1) (.digit 5 1)) (.join (.digit 8 1) (.digit 117 1))) (.join (.join (.digit 54 1) (.digit 46 1)) (.join (.digit 37 1) (.digit 27 1))))))

private def square8Part41 : Word :=
  (.join (.join (.join (.join (.join (.digit 3 1) (.digit 16 1)) (.join (.digit 25 1) (.digit 13 1))) (.join (.join (.digit 3 1) (.digit 30 1)) (.join (.digit 20 1) (.digit 2 1)))) (.join (.join (.join (.digit 35 1) (.digit 7 1)) (.join (.digit 17 1) (.digit 46 1))) (.join (.join (.digit 60 1) (.digit 5 1)) (.join (.digit 12 1) (.digit 60 1))))) (.join (.join (.join (.join (.digit 12 1) (.digit 9 1)) (.join (.digit 61 1) (.digit 0 1))) (.join (.join (.digit 4 1) (.digit 58 1)) (.join (.digit 38 1) (.digit 2 1)))) (.join (.join (.join (.digit 14 1) (.digit 0 1)) (.join (.digit 17 1) (.digit 3 1))) (.join (.join (.digit 34 1) (.digit 43 1)) (.join (.digit 2 1) (.digit 85 1))))))

private def square8Part42 : Word :=
  (.join (.join (.join (.join (.join (.digit 11 1) (.digit 5 1)) (.join (.digit 8 1) (.digit 59 1))) (.join (.join (.digit 8 1) (.digit 21 1)) (.join (.digit 14 1) (.digit 105 1)))) (.join (.join (.join (.digit 16 1) (.digit 18 1)) (.join (.digit 3 1) (.digit 4 1))) (.join (.join (.digit 23 1) (.digit 22 1)) (.join (.digit 6 1) (.digit 0 1))))) (.join (.join (.join (.join (.digit 22 1) (.digit 32 1)) (.join (.digit 17 1) (.digit 8 1))) (.join (.join (.digit 12 1) (.digit 120 1)) (.join (.digit 6 1) (.digit 6 0)))) (.join (.join (.join (.digit 25 1) (.digit 25 0)) (.join (.digit 2 1) (.digit 30 1))) (.join (.join (.digit 25 1) (.digit 18 1)) (.join (.digit 20 1) (.digit 44 1))))))

private def square8Part43 : Word :=
  (.join (.join (.join (.join (.join (.digit 10 1) (.digit 4 1)) (.join (.digit 20 1) (.digit 14 1))) (.join (.join (.digit 67 1) (.digit 14 1)) (.join (.digit 3 1) (.digit 36 1)))) (.join (.join (.join (.digit 16 1) (.digit 23 1)) (.join (.digit 1 0) (.digit 12 1))) (.join (.join (.digit 4 1) (.digit 48 1)) (.join (.digit 16 1) (.digit 73 1))))) (.join (.join (.join (.join (.digit 2 1) (.digit 15 1)) (.join (.digit 96 1) (.digit 7 1))) (.join (.join (.digit 49 1) (.digit 2 1)) (.join (.digit 7 1) (.digit 19 1)))) (.join (.join (.join (.digit 5 1) (.digit 25 1)) (.join (.digit 26 1) (.digit 49 1))) (.join (.join (.digit 6 1) (.digit 1 1)) (.join (.digit 34 1) (.digit 3 1))))))

private def square8Part44 : Word :=
  (.join (.join (.join (.join (.join (.digit 30 1) (.digit 1 1)) (.join (.digit 87 1) (.digit 11 1))) (.join (.join (.digit 6 1) (.digit 45 1)) (.join (.digit 8 1) (.digit 31 1)))) (.join (.join (.join (.digit 12 1) (.digit 14 1)) (.join (.digit 16 1) (.digit 13 1))) (.join (.join (.digit 12 1) (.digit 35 1)) (.join (.digit 3 1) (.digit 10 1))))) (.join (.join (.join (.join (.digit 5 1) (.digit 72 1)) (.join (.digit 45 1) (.digit 53 1))) (.join (.join (.digit 33 1) (.digit 18 0)) (.join (.digit 25 1) (.digit 21 1)))) (.join (.join (.join (.digit 0 1) (.digit 24 1)) (.join (.digit 36 1) (.digit 138 1))) (.join (.join (.digit 5 1) (.digit 19 1)) (.join (.digit 15 1) (.digit 15 1))))))

private def square8Part45 : Word :=
  (.join (.join (.join (.join (.join (.digit 4 1) (.digit 55 1)) (.join (.digit 8 1) (.digit 20 1))) (.join (.join (.digit 30 1) (.digit 37 1)) (.join (.digit 30 1) (.digit 33 1)))) (.join (.join (.join (.digit 38 1) (.digit 21 1)) (.join (.digit 15 1) (.digit 23 1))) (.join (.join (.digit 1 1) (.digit 10 1)) (.join (.digit 48 1) (.digit 18 1))))) (.join (.join (.join (.join (.digit 6 1) (.digit 84 1)) (.join (.digit 10 1) (.digit 16 1))) (.join (.join (.digit 24 1) (.digit 43 7)) (.join (.digit 30 1) (.digit 39 1)))) (.join (.join (.join (.digit 3 1) (.digit 12 1)) (.join (.digit 8 1) (.digit 14 1))) (.join (.join (.digit 17 1) (.digit 19 1)) (.join (.digit 5 1) (.digit 0 1))))))

private def square8Part46 : Word :=
  (.join (.join (.join (.join (.join (.digit 29 1) (.digit 11 1)) (.join (.digit 8 1) (.digit 4 1))) (.join (.join (.digit 7 1) (.digit 38 1)) (.join (.digit 18 1) (.digit 58 1)))) (.join (.join (.join (.digit 0 1) (.digit 55 1)) (.join (.digit 46 1) (.digit 22 1))) (.join (.join (.digit 72 1) (.digit 12 1)) (.join (.digit 8 1) (.digit 12 1))))) (.join (.join (.join (.join (.digit 61 1) (.digit 60 1)) (.join (.digit 2 1) (.digit 10 0))) (.join (.join (.digit 80 1) (.digit 3 1)) (.join (.digit 21 1) (.digit 12 1)))) (.join (.join (.join (.digit 8 1) (.digit 37 1)) (.join (.digit 11 1) (.digit 56 1))) (.join (.join (.digit 10 1) (.digit 41 1)) (.join (.digit 60 1) (.digit 25 1))))))

private def square8Part47 : Word :=
  (.join (.join (.join (.join (.join (.digit 9 7) (.digit 3 1)) (.join (.digit 35 1) (.digit 28 1))) (.join (.join (.digit 16 1) (.digit 13 1)) (.join (.digit 34 1) (.digit 36 1)))) (.join (.join (.join (.digit 3 1) (.digit 85 1)) (.join (.digit 43 1) (.digit 52 1))) (.join (.join (.digit 60 1) (.digit 8 1)) (.join (.digit 24 1) (.digit 0 1))))) (.join (.join (.join (.join (.digit 27 1) (.digit 54 1)) (.join (.digit 2 1) (.digit 36 1))) (.join (.join (.digit 21 1) (.digit 7 1)) (.join (.digit 28 1) (.digit 19 1)))) (.join (.join (.join (.digit 46 1) (.digit 18 1)) (.join (.digit 14 0) (.digit 26 1))) (.join (.join (.digit 38 1) (.digit 19 1)) (.join (.digit 35 1) (.digit 13 1))))))

private def square8Part48 : Word :=
  (.join (.join (.join (.join (.join (.digit 4 1) (.digit 2 1)) (.join (.digit 27 0) (.digit 6 1))) (.join (.join (.digit 11 1) (.digit 18 1)) (.join (.digit 11 1) (.digit 18 1)))) (.join (.join (.join (.digit 80 1) (.digit 0 1)) (.join (.digit 13 1) (.digit 10 1))) (.join (.join (.digit 16 1) (.digit 2 1)) (.join (.digit 55 1) (.digit 25 1))))) (.join (.join (.join (.join (.digit 0 1) (.digit 29 1)) (.join (.digit 28 1) (.digit 12 1))) (.join (.join (.digit 6 1) (.digit 31 1)) (.join (.digit 1 1) (.digit 2 1)))) (.join (.join (.join (.digit 11 1) (.digit 9 1)) (.join (.digit 15 1) (.digit 28 1))) (.join (.join (.digit 0 1) (.digit 94 0)) (.join (.digit 12 1) (.digit 8 1))))))

private def square8Part49 : Word :=
  (.join (.join (.join (.join (.join (.digit 34 1) (.digit 1 1)) (.join (.digit 2 1) (.digit 33 1))) (.join (.join (.digit 8 1) (.digit 9 1)) (.join (.digit 0 1) (.digit 1 0)))) (.join (.join (.join (.digit 38 1) (.digit 3 1)) (.join (.digit 13 1) (.digit 0 1))) (.join (.join (.digit 55 0) (.digit 10 1)) (.join (.digit 0 1) (.digit 34 1))))) (.join (.join (.join (.join (.digit 3 1) (.digit 48 1)) (.join (.digit 8 1) (.digit 9 1))) (.join (.join (.digit 0 1) (.digit 2 1)) (.join (.digit 2 1) (.digit 24 1)))) (.join (.join (.join (.digit 43 1) (.digit 13 1)) (.join (.digit 85 1) (.digit 12 1))) (.join (.join (.digit 5 1) (.digit 3 1)) (.join (.digit 9 1) (.digit 20 1))))))

private def square8Part50 : Word :=
  (.join (.join (.join (.join (.join (.digit 26 1) (.digit 15 1)) (.join (.digit 3 1) (.digit 51 1))) (.join (.join (.digit 11 1) (.digit 17 1)) (.join (.digit 0 1) (.digit 8 1)))) (.join (.join (.join (.digit 58 1) (.digit 56 1)) (.join (.digit 10 1) (.digit 21 1))) (.join (.join (.digit 68 1) (.digit 30 1)) (.join (.digit 17 1) (.digit 1 1))))) (.join (.join (.join (.join (.digit 54 1) (.digit 3 7)) (.join (.digit 40 1) (.digit 1 1))) (.join (.join (.digit 13 1) (.digit 52 1)) (.join (.digit 16 1) (.digit 239 1)))) (.join (.join (.join (.digit 24 0) (.digit 13 1)) (.join (.digit 51 1) (.digit 6 1))) (.join (.join (.digit 53 1) (.digit 2 1)) (.join (.digit 0 1) (.digit 1 1))))))

private def square8Part51 : Word :=
  (.join (.join (.join (.join (.join (.digit 9 1) (.digit 50 1)) (.join (.digit 61 1) (.digit 12 1))) (.join (.join (.digit 10 1) (.digit 85 1)) (.join (.digit 38 1) (.digit 52 1)))) (.join (.join (.join (.digit 40 1) (.digit 37 1)) (.join (.digit 0 0) (.digit 8 1))) (.join (.join (.digit 3 1) (.digit 16 1)) (.join (.digit 27 1) (.digit 2 1))))) (.join (.join (.join (.join (.digit 23 1) (.digit 21 1)) (.join (.digit 58 1) (.digit 24 1))) (.join (.join (.digit 4 1) (.digit 26 1)) (.join (.digit 55 1) (.digit 78 1)))) (.join (.join (.join (.digit 5 1) (.digit 23 1)) (.join (.digit 18 1) (.digit 15 1))) (.join (.join (.digit 3 1) (.digit 30 1)) (.join (.digit 6 1) (.digit 14 1))))))

private def square8Part52 : Word :=
  (.join (.join (.join (.join (.join (.digit 1 1) (.digit 30 1)) (.join (.digit 42 1) (.digit 11 1))) (.join (.join (.digit 27 1) (.digit 68 1)) (.join (.digit 60 1) (.digit 0 1)))) (.join (.join (.join (.digit 18 1) (.digit 30 1)) (.join (.digit 49 1) (.digit 19 1))) (.join (.join (.digit 58 1) (.digit 23 0)) (.join (.digit 18 1) (.digit 13 1))))) (.join (.join (.join (.join (.digit 98 1) (.digit 16 1)) (.join (.digit 4 1) (.digit 9 1))) (.join (.join (.digit 1 1) (.digit 26 1)) (.join (.digit 137 1) (.digit 17 1)))) (.join (.join (.join (.digit 20 1) (.digit 52 1)) (.join (.digit 145 1) (.digit 61 1))) (.join (.join (.digit 5 1) (.digit 49 1)) (.join (.digit 0 1) (.digit 39 1))))))

private def square8Part53 : Word :=
  (.join (.join (.join (.join (.join (.digit 16 1) (.digit 25 1)) (.join (.digit 18 1) (.digit 11 1))) (.join (.join (.digit 11 1) (.digit 25 1)) (.join (.digit 4 1) (.digit 25 1)))) (.join (.join (.join (.digit 16 1) (.digit 17 1)) (.join (.digit 28 1) (.digit 17 1))) (.join (.join (.digit 68 1) (.digit 30 1)) (.join (.digit 53 1) (.digit 76 1))))) (.join (.join (.join (.join (.digit 77 0) (.digit 11 1)) (.join (.digit 25 1) (.digit 70 1))) (.join (.join (.digit 77 1) (.digit 25 1)) (.join (.digit 28 1) (.digit 5 1)))) (.join (.join (.join (.digit 8 1) (.digit 16 1)) (.join (.digit 36 1) (.digit 23 1))) (.join (.join (.digit 6 1) (.digit 52 1)) (.join (.digit 60 1) (.digit 57 0))))))

private def square8Part54 : Word :=
  (.join (.join (.join (.join (.join (.digit 46 1) (.digit 178 1)) (.join (.digit 2 1) (.digit 27 1))) (.join (.join (.digit 10 1) (.digit 0 1)) (.join (.digit 17 1) (.digit 7 1)))) (.join (.join (.join (.digit 23 1) (.digit 112 1)) (.join (.digit 34 1) (.digit 9 1))) (.join (.join (.digit 5 1) (.digit 9 1)) (.join (.digit 41 1) (.digit 32 1))))) (.join (.join (.join (.join (.digit 35 1) (.digit 21 1)) (.join (.digit 8 1) (.digit 119 1))) (.join (.join (.digit 86 1) (.digit 122 1)) (.join (.digit 0 0) (.digit 61 1)))) (.join (.join (.join (.digit 68 1) (.digit 61 1)) (.join (.digit 6 1) (.digit 16 1))) (.join (.join (.digit 13 1) (.digit 41 1)) (.join (.digit 12 1) (.digit 9 1))))))

private def square8Part55 : Word :=
  (.join (.join (.join (.join (.join (.digit 15 1) (.digit 4 1)) (.join (.digit 16 1) (.digit 121 1))) (.join (.join (.digit 39 1) (.digit 58 1)) (.join (.digit 9 1) (.digit 30 1)))) (.join (.join (.join (.digit 15 1) (.digit 11 1)) (.join (.digit 30 1) (.digit 25 1))) (.join (.join (.digit 30 1) (.digit 19 1)) (.join (.digit 46 1) (.digit 55 1))))) (.join (.join (.join (.join (.digit 33 1) (.digit 26 1)) (.join (.digit 24 1) (.digit 32 1))) (.join (.join (.digit 22 1) (.digit 4 1)) (.join (.digit 20 1) (.digit 181 1)))) (.join (.join (.join (.digit 14 1) (.digit 15 1)) (.join (.digit 42 1) (.digit 1 1))) (.join (.join (.digit 23 1) (.digit 30 7)) (.join (.digit 3 1) (.digit 14 1))))))

private def square8Part56 : Word :=
  (.join (.join (.join (.join (.join (.digit 6 1) (.digit 34 1)) (.join (.digit 53 1) (.digit 45 1))) (.join (.join (.digit 7 1) (.digit 31 1)) (.join (.digit 6 1) (.digit 29 1)))) (.join (.join (.join (.digit 30 1) (.digit 150 1)) (.join (.digit 59 1) (.digit 17 1))) (.join (.join (.digit 18 1) (.digit 15 1)) (.join (.digit 5 1) (.digit 41 1))))) (.join (.join (.join (.join (.digit 14 1) (.digit 7 1)) (.join (.digit 29 1) (.digit 30 1))) (.join (.join (.digit 37 1) (.digit 30 1)) (.join (.digit 24 1) (.digit 113 1)))) (.join (.join (.join (.digit 17 1) (.digit 38 1)) (.join (.digit 3 1) (.digit 86 1))) (.join (.join (.digit 18 1) (.digit 159 1)) (.join (.digit 26 1) (.digit 37 1))))))

private def square8Part57 : Word :=
  (.join (.join (.join (.join (.join (.digit 68 1) (.digit 3 1)) (.join (.digit 26 1) (.digit 23 1))) (.join (.join (.digit 9 1) (.digit 41 1)) (.join (.digit 18 1) (.digit 8 1)))) (.join (.join (.join (.digit 7 1) (.digit 44 1)) (.join (.digit 43 1) (.digit 24 1))) (.join (.join (.digit 30 1) (.digit 166 1)) (.join (.digit 85 1) (.digit 36 1))))) (.join (.join (.join (.join (.digit 21 1) (.digit 34 1)) (.join (.digit 5 1) (.digit 29 1))) (.join (.join (.digit 24 1) (.digit 43 1)) (.join (.digit 30 1) (.digit 22 1)))) (.join (.join (.join (.digit 25 1) (.digit 58 1)) (.join (.digit 0 1) (.digit 11 1))) (.join (.join (.digit 20 1) (.digit 22 1)) (.join (.digit 2 1) (.digit 13 1))))))

private def square8Part58 : Word :=
  (.join (.join (.join (.join (.join (.digit 44 1) (.digit 122 1)) (.join (.digit 37 1) (.digit 4 1))) (.join (.join (.digit 48 1) (.digit 4 1)) (.join (.digit 12 1) (.digit 43 1)))) (.join (.join (.join (.digit 99 1) (.digit 60 1)) (.join (.digit 51 1) (.digit 51 1))) (.join (.join (.digit 43 1) (.digit 25 1)) (.join (.digit 61 1) (.digit 38 1))))) (.join (.join (.join (.join (.digit 97 1) (.digit 69 1)) (.join (.digit 91 1) (.digit 136 1))) (.join (.join (.digit 39 1) (.digit 85 1)) (.join (.digit 39 1) (.digit 204 1)))) (.join (.join (.join (.digit 133 1) (.digit 17 1)) (.join (.digit 22 1) (.digit 250 1))) (.join (.join (.digit 21 1) (.digit 25 1)) (.join (.digit 87 1) (.digit 9 1))))))

private def square8Part59 : Word :=
  (.join (.join (.join (.join (.join (.digit 75 1) (.digit 7 1)) (.join (.digit 26 1) (.digit 81 1))) (.join (.join (.digit 161 1) (.digit 18 1)) (.join (.digit 25 1) (.digit 13 1)))) (.join (.join (.join (.digit 35 1) (.digit 20 1)) (.join (.digit 110 1) (.digit 11 1))) (.join (.join (.digit 40 1) (.digit 261 1)) (.join (.digit 25 1) (.digit 9 1))))) (.join (.join (.join (.join (.digit 7 0) (.digit 68 1)) (.join (.digit 30 1) (.digit 33 1))) (.join (.join (.digit 3 0) (.digit 25 1)) (.join (.digit 4 1) (.digit 22 1)))) (.join (.join (.join (.digit 7 0) (.digit 175 1)) (.join (.digit 25 1) (.digit 0 1))) (.join (.join (.digit 97 1) (.digit 82 1)) (.join (.digit 119 1) (.digit 10 1))))))

private def square8Part60 : Word :=
  (.join (.join (.join (.join (.join (.digit 49 1) (.digit 7 1)) (.join (.digit 30 1) (.digit 29 1))) (.join (.join (.digit 30 1) (.digit 2 1)) (.join (.digit 130 1) (.digit 63 1)))) (.join (.join (.join (.digit 71 1) (.digit 13 1)) (.join (.digit 150 1) (.digit 68 1))) (.join (.join (.digit 30 1) (.digit 7 0)) (.join (.digit 19 1) (.digit 40 1))))) (.join (.join (.join (.join (.digit 17 1) (.digit 11 1)) (.join (.digit 22 1) (.digit 7 0))) (.join (.join (.digit 13 1) (.digit 16 1)) (.join (.digit 85 1) (.digit 108 1)))) (.join (.join (.join (.digit 169 1) (.digit 15 1)) (.join (.digit 42 1) (.digit 18 1))) (.join (.join (.digit 37 1) (.digit 22 1)) (.join (.digit 18 1) (.digit 63 1))))))

private def square8Part61 : Word :=
  (.join (.join (.join (.join (.join (.digit 21 1) (.digit 68 1)) (.join (.digit 177 1) (.digit 31 1))) (.join (.join (.digit 54 1) (.digit 3 1)) (.join (.digit 56 1) (.digit 24 1)))) (.join (.join (.join (.digit 9 0) (.digit 45 1)) (.join (.digit 222 1) (.digit 12 1))) (.join (.join (.digit 32 1) (.digit 12 1)) (.join (.digit 45 1) (.digit 10 1))))) (.join (.join (.join (.join (.digit 57 1) (.digit 30 1)) (.join (.digit 94 1) (.digit 143 1))) (.join (.join (.digit 66 1) (.digit 1 1)) (.join (.digit 30 1) (.digit 24 1)))) (.join (.join (.join (.digit 74 1) (.digit 75 1)) (.join (.digit 88 1) (.digit 60 1))) (.join (.join (.digit 30 1) (.digit 87 1)) (.join (.digit 44 1) (.digit 107 1))))))

private def square8Part62 : Word :=
  (.join (.join (.join (.join (.join (.digit 5 1) (.digit 60 1)) (.join (.digit 174 1) (.digit 14 1))) (.join (.join (.digit 5 1) (.digit 48 1)) (.join (.digit 210 1) (.digit 78 1)))) (.join (.join (.join (.digit 137 1) (.digit 39 1)) (.join (.digit 162 1) (.digit 256 1))) (.join (.join (.digit 62 1) (.digit 285 1)) (.join (.digit 68 1) (.digit 30 1))))) (.join (.join (.join (.join (.digit 33 1) (.digit 253 0)) (.join (.digit 315 1) (.digit 22 1))) (.join (.join (.digit 37 1) (.digit 300 0)) (.join (.digit 233 1) (.digit 713 1)))) (.join (.join (.join (.digit 68 1) (.digit 30 1)) (.join (.digit 397 1) (.digit 68 1))) (.join (.join (.digit 30 1) (.digit 105 1)) (.join (.digit 60 1) (.digit 194 1))))))

private def square8Part63 : Word :=
  (.join (.join (.join (.join (.join (.digit 60 1) (.digit 68 1)) (.join (.digit 30 1) (.digit 80 1))) (.join (.join (.digit 60 1) (.digit 35 1)) (.join (.digit 0 1) (.digit 140 1)))) (.join (.join (.join (.digit 68 1) (.digit 30 1)) (.join (.digit 183 1) (.digit 60 1))) (.join (.join (.digit 11 1) (.digit 346 1)) (.join (.digit 60 1) (.digit 114 1))))) (.join (.join (.join (.join (.digit 419 1) (.digit 232 1)) (.join (.digit 338 1) (.digit 158 1))) (.join (.join (.digit 73 0) (.digit 264 1)) (.join (.digit 183 1) (.digit 338 1)))) (.join (.join (.join (.digit 80 1) (.digit 338 1)) (.join (.digit 805 1) (.digit 497 1))) (.join (.join (.digit 522 1) (.digit 419 1)) (.join (.digit 572 0) (.digit 497 1))))))

private def square8Part64 : Word :=
  (.join (.join (.join (.digit 497 0) (.digit 24 1)) (.join (.digit 419 1) (.digit 77 1))) (.join (.join (.digit 419 1) (.digit 102 0)) (.join (.digit 419 1) (.digit 419 0))))

def square8 : Word :=
  (.join (.join (.join (.join (.join (.join square8Part0 square8Part1) (.join square8Part2 square8Part3)) (.join (.join square8Part4 square8Part5) (.join square8Part6 square8Part7))) (.join (.join (.join square8Part8 square8Part9) (.join square8Part10 square8Part11)) (.join (.join square8Part12 square8Part13) (.join square8Part14 square8Part15)))) (.join (.join (.join (.join square8Part16 square8Part17) (.join square8Part18 square8Part19)) (.join (.join square8Part20 square8Part21) (.join square8Part22 square8Part23))) (.join (.join (.join square8Part24 square8Part25) (.join square8Part26 square8Part27)) (.join (.join square8Part28 square8Part29) (.join square8Part30 square8Part31))))) (.join (.join (.join (.join (.join square8Part32 square8Part33) (.join square8Part34 square8Part35)) (.join (.join square8Part36 square8Part37) (.join square8Part38 square8Part39))) (.join (.join (.join square8Part40 square8Part41) (.join square8Part42 square8Part43)) (.join (.join square8Part44 square8Part45) (.join square8Part46 square8Part47)))) (.join (.join (.join (.join square8Part48 square8Part49) (.join square8Part50 square8Part51)) (.join (.join square8Part52 square8Part53) (.join square8Part54 square8Part55))) (.join (.join (.join square8Part56 square8Part57) (.join square8Part58 square8Part59)) (.join (.join square8Part60 square8Part61) (.join square8Part62 (.join square8Part63 square8Part64)))))))

def key8 : Finset ℕ := {0,1,2,8}

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
private theorem certified8 : certOK root8 square8 key8 := by
  unfold certOK
  constructor <;> decide +kernel

theorem checked8 : support root8.value=key8 ∧ eligible root8.value :=
  cert_sound (by intro d hd; simp [key8] at hd; omega) certified8

end SupportBounds.Symmetric

namespace SupportBounds.Symmetric
open DigitSupports OMA.S_oeis_a397780

private def seven : ℕ × ℕ := (135,root7.value)
private def eight : ℕ × ℕ := (263,root8.value)
private def added := [seven,eight,row0126,row0129]
private def every := added ++ furtherRow :: certifiedRows
private def four := added ++ fourRows

private theorem knownOK : rowOK row0126=true ∧ rowOK row0129=true ∧ rowOK furtherRow=true ∧
    rowHasSize 4 row0126=true ∧ rowHasSize 4 row0129=true := by decide +kernel

private theorem smaller {r : ℕ × ℕ} (h : rowOK r=true) (h4 : rowHasSize 4 r=true) :
    validFor (fun s => s.card = 4) r :=
  ⟨(row_sound h).1,(row_sound h).2,size_sound h4⟩

private theorem added_good (r : ℕ × ℕ) (hr : r∈added) : validFor (fun s => s.card=4) r := by
  have h7 : mask key7=135 ∧ key7.card=4 := by decide +kernel
  have h8 : mask key8=263 ∧ key8.card=4 := by decide +kernel
  simp only [added,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact ⟨(congrArg mask checked7.1).trans h7.1,checked7.2,(congrArg Finset.card checked7.1).trans h7.2⟩
  · exact ⟨(congrArg mask checked8.1).trans h8.1,checked8.2,(congrArg Finset.card checked8.1).trans h8.2⟩
  · exact smaller knownOK.1 knownOK.2.2.2.1
  · exact smaller knownOK.2.1 knownOK.2.2.2.2

set_option maxRecDepth 100000 in
private theorem disjoint_all :
    seven.1 ∉ (eight :: row0126 :: row0129 :: furtherRow :: certifiedRows).map Prod.fst ∧
    eight.1 ∉ (row0126 :: row0129 :: furtherRow :: certifiedRows).map Prod.fst ∧
    row0126.1 ∉ (row0129 :: furtherRow :: certifiedRows).map Prod.fst ∧
    row0129.1 ∉ (furtherRow :: certifiedRows).map Prod.fst ∧
    furtherRow.1 ∉ certifiedRows.map Prod.fst := by
  decide +kernel

private theorem every_distinct : (every.map Prod.fst).Nodup :=
  List.nodup_cons.mpr ⟨disjoint_all.1,List.nodup_cons.mpr ⟨disjoint_all.2.1,
    List.nodup_cons.mpr ⟨disjoint_all.2.2.1,List.nodup_cons.mpr ⟨disjoint_all.2.2.2.1,
      List.nodup_cons.mpr ⟨disjoint_all.2.2.2.2,certifiedRows_distinct⟩⟩⟩⟩⟩

private theorem four_distinct : (four.map Prod.fst).Nodup := by decide +kernel

theorem at_least_671 : 671 ≤ {n | isTerm n}.ncard := by
  have hv (r) (hr : r∈every) : validFor (fun _ => True) r := by
    rcases List.mem_append.mp hr with h|h
    · exact ⟨(added_good r h).1,(added_good r h).2.1,trivial⟩
    · have hh : (furtherRow :: certifiedRows).all rowOK=true := by
        simp [knownOK.2.2.1,certifiedRows_valid]
      have good := row_sound (List.all_eq_true.mp hh r h)
      exact ⟨good.1,good.2,trivial⟩
  have hl : every.length=671 := by simp [every,added,certifiedRows_length]
  simpa [hl] using semantic_bound every _ hv every_distinct

theorem at_least_36_four : 36 ≤ {n | isTerm n ∧ (support n).card=4}.ncard := by
  have hv (r) (hr : r∈four) : validFor (fun s => s.card=4) r := by
    rcases List.mem_append.mp hr with h|h
    · exact added_good r h
    · exact smaller (List.all_eq_true.mp fourRows_valid r h)
        (List.all_eq_true.mp fourRows_four_digits r h)
  have hl : four.length=36 := by simp [four,added,fourRows_length]
  simpa only [hl] using semantic_bound four _ hv four_distinct

end SupportBounds.Symmetric

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a397780.main) := by
  intro h
  have lower := SupportBounds.Symmetric.at_least_671
  have proposed := h.1
  omega
