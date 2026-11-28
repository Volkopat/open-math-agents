import OMAReductions.R_Erdos848_erdos_848_R3
/-! Finite range N ≤ 986746 of Erdős 848 by kernel-checked greedy colouring certificates.
Small-colouring certificates and soundness are adapted from MacchaCat/erdos848, commit
99b8d9bf40fdd090a2a117328c5707ca21ec748e (Apache-2.0); condensed greedy replay by the math06 worker. -/
/- Small-colouring certificates and soundness adapted from MacchaCat, Erdos848. -/
namespace ErdosComp

def minFacAux (n : Nat) : Nat → Nat → Nat
  | _, 0 => n
  | k, f + 1 => if n < k * k then n else if n % k == 0 then k else minFacAux n (k + 2) f
def isPrimeB (n : Nat) : Bool :=
  if n < 2 then false else if n % 2 == 0 then n == 2 else minFacAux n 3 n == n
def PS4 : Nat :=
  59490679579998635868564022242503445659680322440679327938309703916140405638383434744833220555452130558140772894046169700747186409941317550665821619479140098743288335106272856533978719769677794737287419461899922456614256826709727133515885581878614846298251428096512495590545989536239739285290509870860732435109794045491640561011775744617218426011793283330497878491137999673760740717904979730106994180691956740996319139767941335979146924614249205862051182094081815447356600355657858936442589201739350474320966093143098768914226528498860747050474426418211313776073365498029087492308102876323562641651940555529817223923967479711293692697592800750806084802623966596666156361791014935954720420383555300213829134029560826306201326905674141090667002959274513478562033467485802590354539887133866434256562999666615074220857502563011098759348850149774083443643246907501430076141377431759984926248272553982527014011245310690986644461251576837779050124866641531488351016070300247918750613207952783437248236577750579092103591540592540838395240861443615842939673889972504776455114767522430347610500271801944701491874649306605557851914677316523034726044356368337787113190245601235705959816327016988315321850324065292964680148884818699916224411245926491625245571963741062587277736372090007125908660590314049976206281064703285728879581199596401313352724403492043120507597057004633720111008838673185885941472392623805512709896864520875740497617898566981218781313900004406341154884180472153171064617953661517880143988867189622824081729539392205701820144922307223627345876707465251206005262622236311161449785941834002795854996108322186230425179217618301526151712928790928933798369678844576216735378555233905935973195721247604933753363412045618703247367192610615234835041956551569232557323060407648325565048712478527583315981204846341857095134567470182330491262285172727037299211391244340592936174221176781260586188162350081192408213470101717320475998863222409777310443027421196981193126541663212124245716187453863438039402316877152286468198891603632606578778749292403571792687832081974134637014026451921536576338243322267400651083805535119025415817887075652758045539565968044552126338330231434466204888993650859153585380124240540573308417330478048240203241631072371322849430883727355239704116556046700749530006852187064160849175332758172150251213637470549781080491037088372092203085237973008861896576796238915011886636658033019385943299986285181723378096425117379056207797455963451889971988904466449319007760192467211209692128894691704353648198130409333996534250878389064152054828983825841234644875996912485916827004219887033833599723481903489316488764021700996686817244736947119285629049355809027206179193628292018441744552168286541735687924729198455883895791600170372255284216915442808139396541702893732917062958054499525549626455191658842064247047426187897146172971001949767308335268505414284088528125611263685734457560292833389995980698745893243832547007166243476192958601735336260255598581701267151224204461879782815468518040925292817115377696676461775120750971210951527384637825092221708015393564320979357698186262039029460777050248162599194429941464248920952161182024344007059684970270762248243899640259750891406957836740989312390963091260380990901672119736141666856448171380781556117025832312710039041398538035351795267732240730608951176127282191528457681241590895740457571038936173983449289126574141189374690274057472401359482497502067814596008557725079835212621242944853319496441084441343866446380876967613370281793088540430288658573281302876742323336651987699532240686371751448290351615451932054274752105688318766958111191822471878078268490672607804265064578569581247796205593441336042254502454646980009177290888726099355974892680373341371214123450598691915802122913613669446370194221846225597401405625536693874723700374068542217340621938985167525416725638580266200550048001242788847319217369432802469735271132107428204697172144851088692772696511622350096452418244968500432645305761138012204888798724453956720733374364721511323104353496583927094760495687785031050687852300161433757934364774351673531859394855389527851678630166084819717354779333605871648837631164630550613112327670353108353791304451834904017538583880634608113426156225757314283269948216017294095002859515842577481167417167637534527111130468710

end ErdosComp
namespace ErdosComp
def isSqK (m : Nat) : Bool := Nat.beq (Nat.sqrt m * Nat.sqrt m) m
def sqfK (n : Nat) : Bool :=
  Nat.blt 0 n && Nat.blt n (10007 * 10007 * 10007) &&
    Nat.beq (Nat.gcd (Nat.gcd n PS4) (n / Nat.gcd n PS4)) 1 &&
    !(Nat.blt 1 (n / Nat.gcd n PS4) && isSqK (n / Nat.gcd n PS4))
end ErdosComp
namespace Erdos848
open Finset ErdosComp
def Admissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)
def c7 (N : ℕ) : ℕ := (N + 18) / 25
def Statement (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible A → A.card ≤ c7 N
end Erdos848
namespace Erdos848.ColPack
open ErdosComp
def maskOK (q mask : Nat) := (List.range q).all (fun i => mask.testBit ((i*i)%q))
lemma nonsquare {q mask : Nat} (hq : 0<q) (hm : maskOK q mask = true) {m : Nat} (h : mask.testBit (m%q) = false) : isSqK m = false := by
  apply Bool.eq_false_iff.mpr
  intro he; have hs := Nat.beq_eq.mp he
  have hi := List.all_eq_true.mp hm (m.sqrt%q) (List.mem_range.mpr (Nat.mod_lt _ hq))
  change mask.testBit ((m.sqrt%q*(m.sqrt%q))%q) = true at hi
  rw [← Nat.mul_mod,hs,h] at hi; contradiction
def qm : Nat := 0x2000200000000000002000002000002000010000002000000001000000202000002010002000000000002000000000201000002000012000202000000000002010210000000000002000002000012000000000002000000010000000202000002000002000010000002010000000200010002000002000203000000000002000200010000001002000012000002000000000002000010000000010202000002010012000000000002000000000200000002000002000202000010000002000200000000000002000002010002001000000003000000000000000202000012000002000000000002010010000200000002001002000212000000000002000200010000000002000002000002000010000002010000001000010202000002000002000000000002000000010200000002000012000202000000000002000210000000010002000002010012000000000003000000000000000202000002000002000011000002000000000200000002000002010202000000000002000200000000001002000012000002000000000002010010000000000202000002000012000000000002000000010201000002000002000202000010000002010200000000010002000002000002001000000002000000010000000202000012000002000001000002000010000200010002001002010213
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma maskChecked : maskOK 4032 qm = true := by decide +kernel
def fastSq (n : Nat) : Bool :=
  let g := Nat.gcd n PS4; let m := n/g
  Nat.blt 0 n && Nat.blt n (10007*10007*10007) && Nat.beq (Nat.gcd g m) 1 && !(Nat.blt 1 m && qm.testBit (m%4032) && isSqK m)
lemma fastEq (n : Nat) : fastSq n = sqfK n := by
  unfold fastSq sqfK
  let m := n / n.gcd PS4
  cases he : qm.testBit (m%4032) with
  | false => have hh := nonsquare (q := 4032) (by decide) maskChecked he
             change isSqK m = false at hh
             simp only [← show m = n/n.gcd PS4 from rfl,he,hh,Bool.and_false,Bool.false_and]
  | true => simp only [← show m = n/n.gcd PS4 from rfl,he,Bool.and_true]
end Erdos848.ColPack
namespace ErdosComp
def ps0 : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251]
def ps256 : List Nat := [257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509]
def ps512 : List Nat := [521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761]
def ps768 : List Nat := [769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021]
def ps1024 : List Nat := [1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279]
def ps1280 : List Nat := [1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531]
def ps1536 : List Nat := [1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789]
def ps1792 : List Nat := [1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039]
def ps2048 : List Nat := [2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297]
def ps2304 : List Nat := [2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557]
def ps2560 : List Nat := [2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803]
def ps2816 : List Nat := [2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067]
def ps3072 : List Nat := [3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323]
def ps3328 : List Nat := [3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583]
def ps3584 : List Nat := [3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833]
def ps3840 : List Nat := [3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093]
def ps4096 : List Nat := [4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349]
def ps4352 : List Nat := [4357,4363,4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603]
def ps4608 : List Nat := [4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831,4861]
def ps4864 : List Nat := [4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119]
def ps5120 : List Nat := [5147,5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281,5297,5303,5309,5323,5333,5347,5351]
def ps5376 : List Nat := [5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531,5557,5563,5569,5573,5581,5591,5623]
def ps5632 : List Nat := [5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,5693,5701,5711,5717,5737,5741,5743,5749,5779,5783,5791,5801,5807,5813,5821,5827,5839,5843,5849,5851,5857,5861,5867,5869,5879,5881]
def ps5888 : List Nat := [5897,5903,5923,5927,5939,5953,5981,5987,6007,6011,6029,6037,6043,6047,6053,6067,6073,6079,6089,6091,6101,6113,6121,6131,6133,6143]
def ps6144 : List Nat := [6151,6163,6173,6197,6199,6203,6211,6217,6221,6229,6247,6257,6263,6269,6271,6277,6287,6299,6301,6311,6317,6323,6329,6337,6343,6353,6359,6361,6367,6373,6379,6389,6397]
def ps6400 : List Nat := [6421,6427,6449,6451,6469,6473,6481,6491,6521,6529,6547,6551,6553,6563,6569,6571,6577,6581,6599,6607,6619,6637,6653]
def ps6656 : List Nat := [6659,6661,6673,6679,6689,6691,6701,6703,6709,6719,6733,6737,6761,6763,6779,6781,6791,6793,6803,6823,6827,6829,6833,6841,6857,6863,6869,6871,6883,6899,6907,6911]
def ps6912 : List Nat := [6917,6947,6949,6959,6961,6967,6971,6977,6983,6991,6997,7001,7013,7019,7027,7039,7043,7057,7069,7079,7103,7109,7121,7127,7129,7151,7159]
def ps7168 : List Nat := [7177,7187,7193,7207,7211,7213,7219,7229,7237,7243,7247,7253,7283,7297,7307,7309,7321,7331,7333,7349,7351,7369,7393,7411,7417]
def ps7424 : List Nat := [7433,7451,7457,7459,7477,7481,7487,7489,7499,7507,7517,7523,7529,7537,7541,7547,7549,7559,7561,7573,7577,7583,7589,7591,7603,7607,7621,7639,7643,7649,7669,7673]
def ps7680 : List Nat := [7681,7687,7691,7699,7703,7717,7723,7727,7741,7753,7757,7759,7789,7793,7817,7823,7829,7841,7853,7867,7873,7877,7879,7883,7901,7907,7919,7927,7933]
def ps7936 : List Nat := [7937,7949,7951,7963,7993,8009,8011,8017,8039,8053,8059,8069,8081,8087,8089,8093,8101,8111,8117,8123,8147,8161,8167,8171,8179,8191]
def ps8192 : List Nat := [8209,8219,8221,8231,8233,8237,8243,8263,8269,8273,8287,8291,8293,8297,8311,8317,8329,8353,8363,8369,8377,8387,8389,8419,8423,8429,8431,8443,8447]
def ps8448 : List Nat := [8461,8467,8501,8513,8521,8527,8537,8539,8543,8563,8573,8581,8597,8599,8609,8623,8627,8629,8641,8647,8663,8669,8677,8681,8689,8693,8699]
def ps8704 : List Nat := [8707,8713,8719,8731,8737,8741,8747,8753,8761,8779,8783,8803,8807,8819,8821,8831,8837,8839,8849,8861,8863,8867,8887,8893,8923,8929,8933,8941,8951]
def ps8960 : List Nat := [8963,8969,8971,8999,9001,9007,9011,9013,9029,9041,9043,9049,9059,9067,9091,9103,9109,9127,9133,9137,9151,9157,9161,9173,9181,9187,9199,9203,9209]
def ps9216 : List Nat := [9221,9227,9239,9241,9257,9277,9281,9283,9293,9311,9319,9323,9337,9341,9343,9349,9371,9377,9391,9397,9403,9413,9419,9421,9431,9433,9437,9439,9461,9463,9467]
def ps9472 : List Nat := [9473,9479,9491,9497,9511,9521,9533,9539,9547,9551,9587,9601,9613,9619,9623,9629,9631,9643,9649,9661,9677,9679,9689,9697,9719,9721]
def ps9728 : List Nat := [9733,9739,9743,9749,9767,9769,9781,9787,9791,9803,9811,9817,9829,9833,9839,9851,9857,9859,9871,9883,9887,9901,9907,9923,9929,9931,9941,9949,9967,9973]
def ps9984 : List Nat := []
def pf0f256 := ps0 ++ ps256
def pf512f768 := ps512 ++ ps768
def pf1024f1280 := ps1024 ++ ps1280
def pf1536f1792 := ps1536 ++ ps1792
def pf2048f2304 := ps2048 ++ ps2304
def pf2560f2816 := ps2560 ++ ps2816
def pf3072f3328 := ps3072 ++ ps3328
def pf3584f3840 := ps3584 ++ ps3840
def pf4096f4352 := ps4096 ++ ps4352
def pf4608f4864 := ps4608 ++ ps4864
def pf5120f5376 := ps5120 ++ ps5376
def pf5632f5888 := ps5632 ++ ps5888
def pf6144f6400 := ps6144 ++ ps6400
def pf6656f6912 := ps6656 ++ ps6912
def pf7168f7424 := ps7168 ++ ps7424
def pf7680f7936 := ps7680 ++ ps7936
def pf8192f8448 := ps8192 ++ ps8448
def pf8704f8960 := ps8704 ++ ps8960
def pf9216f9472 := ps9216 ++ ps9472
def pf9728f9984 := ps9728 ++ ps9984
def pf0x256f512x256 := pf0f256 ++ pf512f768
def pf1024x256f1536x256 := pf1024f1280 ++ pf1536f1792
def pf2048x256f2560x256 := pf2048f2304 ++ pf2560f2816
def pf3072x256f3584x256 := pf3072f3328 ++ pf3584f3840
def pf4096x256f4608x256 := pf4096f4352 ++ pf4608f4864
def pf5120x256f5632x256 := pf5120f5376 ++ pf5632f5888
def pf6144x256f6656x256 := pf6144f6400 ++ pf6656f6912
def pf7168x256f7680x256 := pf7168f7424 ++ pf7680f7936
def pf8192x256f8704x256 := pf8192f8448 ++ pf8704f8960
def pf9216x256f9728x17 := pf9216f9472 ++ pf9728f9984
def pf0x256x512f1024x256x512 := pf0x256f512x256 ++ pf1024x256f1536x256
def pf2048x256x512f3072x256x512 := pf2048x256f2560x256 ++ pf3072x256f3584x256
def pf4096x256x512f5120x256x512 := pf4096x256f4608x256 ++ pf5120x256f5632x256
def pf6144x256x512f7168x256x512 := pf6144x256f6656x256 ++ pf7168x256f7680x256
def pf8192x256x512f9216x256x273 := pf8192x256f8704x256 ++ pf9216x256f9728x17
def pf0x256x512x1024f2048x256x512x1024 := pf0x256x512f1024x256x512 ++ pf2048x256x512f3072x256x512
def pf4096x256x512x1024f6144x256x512x1024 := pf4096x256x512f5120x256x512 ++ pf6144x256x512f7168x256x512
def pf0x256x512x1024x2048f4096x256x512x1024x2048 := pf0x256x512x1024f2048x256x512x1024 ++ pf4096x256x512x1024f6144x256x512x1024
def pf0x256x512x1024x2048x4096f8192x256x512x785 := pf0x256x512x1024x2048f4096x256x512x1024x2048 ++ pf8192x256x512f9216x256x273
def smallPrimes4L := pf0x256x512x1024x2048x4096f8192x256x512x785
end ErdosComp
namespace Erdos848
open Finset ErdosComp
lemma sqf_of_big_factors {rem P : ℕ} (hrem : 0 < rem) (hlt : rem < P * P * P)
    (hP : ∀ q, q.Prime → q ∣ rem → P ≤ q) (hsq : ¬ (1 < rem ∧ ∃ k, k * k = rem)) :
    Squarefree rem := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hqP := hP q hq ⟨q * m, by rw [hm]; ring⟩
  by_cases hm1 : m = 1
  · subst hm1
    apply hsq
    refine ⟨?_, q, by rw [hm]; ring⟩
    have := hq.two_le; nlinarith
  · obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have hrP := hP r hr (Dvd.dvd.mul_left hrm _ |>.trans (by rw [hm]))
    have hrle : r ≤ m := Nat.le_of_dvd hm0 hrm
    have : P * P * P ≤ q * q * m := by
      have h1 : P * P ≤ q * q := Nat.mul_le_mul hqP hqP
      exact Nat.mul_le_mul h1 (hrP.trans hrle)
    omega
lemma minFacAux_prime {n : ℕ} (hn : n.Prime) : ∀ f k, 2 ≤ k → ErdosComp.minFacAux n k f = n := by
  intro f
  induction f with
  | zero => intro k _; rfl
  | succ f ih =>
    intro k hk
    simp only [ErdosComp.minFacAux]
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : k ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h2)
      rcases hn.eq_one_or_self_of_dvd k hdvd with h | h
      · omega
      · subst h; push Not at h1; nlinarith
    · exact ih (k + 2) (by omega)
lemma isPrimeB_of_prime {n : ℕ} (hn : n.Prime) : isPrimeB n = true := by
  unfold isPrimeB
  have h2 := hn.two_le
  have hlt : ¬ n < 2 := by omega
  simp only [hlt, ↓reduceIte]
  split_ifs with he
  · have : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using he)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hn).mp this
    simp [this]
  · simp [minFacAux_prime hn n 3 (by norm_num)]
lemma minFacAux_spec {n : ℕ} (hodd : n % 2 = 1) : ∀ f k, k % 2 = 1 → 3 ≤ k →
    n < (k + 2 * f) * (k + 2 * f) → ErdosComp.minFacAux n k f = n →
    ∀ d, k ≤ d → d * d ≤ n → ¬ d ∣ n := by
  intro f
  induction f with
  | zero =>
    intro k _hk _hk3 hlt _hres d hd hdd _hdvd
    have : k * k ≤ d * d := Nat.mul_le_mul hd hd
    simp only [mul_zero, add_zero] at hlt; omega
  | succ f ih =>
    intro k hk hk3 hlt hres d hd hdd hdvd
    simp only [ErdosComp.minFacAux] at hres
    split_ifs at hres with h1 h2
    · have : k * k ≤ d * d := Nat.mul_le_mul hd hd
      omega
    · -- returned k = n, impossible since k * k ≤ n
      push Not at h1
      have : k * k ≤ k := hres ▸ h1
      nlinarith
    · rcases Nat.lt_or_ge d (k + 2) with hlt2 | hge
      · rcases (show d = k ∨ d = k + 1 by omega) with rfl | rfl
        · exact h2 (by simpa using Nat.mod_eq_zero_of_dvd hdvd)
        · have h2k : 2 ∣ k + 1 := by omega
          have := Nat.dvd_trans h2k hdvd
          omega
      · exact ih (k + 2) (by omega) (by omega) (by nlinarith) hres d hge hdd hdvd
lemma prime_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  unfold isPrimeB at h
  by_cases h1 : n < 2
  · simp [h1] at h
  by_cases h2 : n % 2 = 0
  · simp only [h1, h2, ↓reduceIte, beq_self_eq_true, beq_iff_eq] at h
    subst h; exact Nat.prime_two
  simp only [h1, ↓reduceIte, beq_iff_eq, h2] at h
  have hodd : n % 2 = 1 := by omega
  rw [Nat.prime_def_le_sqrt]
  refine ⟨by omega, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · omega
  · exact minFacAux_spec hodd n 3 rfl le_rfl (by nlinarith) h m h3 hmm hdvd
lemma isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime :=
  ⟨prime_of_isPrimeB, isPrimeB_of_prime⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f0 : ((List.range' 0 256).filter isPrimeB) = ps0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f256 : ((List.range' 256 256).filter isPrimeB) = ps256 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f512 : ((List.range' 512 256).filter isPrimeB) = ps512 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f768 : ((List.range' 768 256).filter isPrimeB) = ps768 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f1024 : ((List.range' 1024 256).filter isPrimeB) = ps1024 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f1280 : ((List.range' 1280 256).filter isPrimeB) = ps1280 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f1536 : ((List.range' 1536 256).filter isPrimeB) = ps1536 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f1792 : ((List.range' 1792 256).filter isPrimeB) = ps1792 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f2048 : ((List.range' 2048 256).filter isPrimeB) = ps2048 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f2304 : ((List.range' 2304 256).filter isPrimeB) = ps2304 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f2560 : ((List.range' 2560 256).filter isPrimeB) = ps2560 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f2816 : ((List.range' 2816 256).filter isPrimeB) = ps2816 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f3072 : ((List.range' 3072 256).filter isPrimeB) = ps3072 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f3328 : ((List.range' 3328 256).filter isPrimeB) = ps3328 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f3584 : ((List.range' 3584 256).filter isPrimeB) = ps3584 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f3840 : ((List.range' 3840 256).filter isPrimeB) = ps3840 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f4096 : ((List.range' 4096 256).filter isPrimeB) = ps4096 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f4352 : ((List.range' 4352 256).filter isPrimeB) = ps4352 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f4608 : ((List.range' 4608 256).filter isPrimeB) = ps4608 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f4864 : ((List.range' 4864 256).filter isPrimeB) = ps4864 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f5120 : ((List.range' 5120 256).filter isPrimeB) = ps5120 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f5376 : ((List.range' 5376 256).filter isPrimeB) = ps5376 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f5632 : ((List.range' 5632 256).filter isPrimeB) = ps5632 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f5888 : ((List.range' 5888 256).filter isPrimeB) = ps5888 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f6144 : ((List.range' 6144 256).filter isPrimeB) = ps6144 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f6400 : ((List.range' 6400 256).filter isPrimeB) = ps6400 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f6656 : ((List.range' 6656 256).filter isPrimeB) = ps6656 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f6912 : ((List.range' 6912 256).filter isPrimeB) = ps6912 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f7168 : ((List.range' 7168 256).filter isPrimeB) = ps7168 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f7424 : ((List.range' 7424 256).filter isPrimeB) = ps7424 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f7680 : ((List.range' 7680 256).filter isPrimeB) = ps7680 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f7936 : ((List.range' 7936 256).filter isPrimeB) = ps7936 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f8192 : ((List.range' 8192 256).filter isPrimeB) = ps8192 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f8448 : ((List.range' 8448 256).filter isPrimeB) = ps8448 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f8704 : ((List.range' 8704 256).filter isPrimeB) = ps8704 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f8960 : ((List.range' 8960 256).filter isPrimeB) = ps8960 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f9216 : ((List.range' 9216 256).filter isPrimeB) = ps9216 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f9472 : ((List.range' 9472 256).filter isPrimeB) = ps9472 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f9728 : ((List.range' 9728 256).filter isPrimeB) = ps9728 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma f9984 : ((List.range' 9984 17).filter isPrimeB) = ps9984 := by decide +kernel
lemma f0x256 : ((List.range' 0 512).filter isPrimeB) = pf0f256 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f0 f256
lemma f512x256 : ((List.range' 512 512).filter isPrimeB) = pf512f768 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f512 f768
lemma f1024x256 : ((List.range' 1024 512).filter isPrimeB) = pf1024f1280 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f1024 f1280
lemma f1536x256 : ((List.range' 1536 512).filter isPrimeB) = pf1536f1792 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f1536 f1792
lemma f2048x256 : ((List.range' 2048 512).filter isPrimeB) = pf2048f2304 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f2048 f2304
lemma f2560x256 : ((List.range' 2560 512).filter isPrimeB) = pf2560f2816 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f2560 f2816
lemma f3072x256 : ((List.range' 3072 512).filter isPrimeB) = pf3072f3328 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f3072 f3328
lemma f3584x256 : ((List.range' 3584 512).filter isPrimeB) = pf3584f3840 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f3584 f3840
lemma f4096x256 : ((List.range' 4096 512).filter isPrimeB) = pf4096f4352 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f4096 f4352
lemma f4608x256 : ((List.range' 4608 512).filter isPrimeB) = pf4608f4864 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f4608 f4864
lemma f5120x256 : ((List.range' 5120 512).filter isPrimeB) = pf5120f5376 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f5120 f5376
lemma f5632x256 : ((List.range' 5632 512).filter isPrimeB) = pf5632f5888 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f5632 f5888
lemma f6144x256 : ((List.range' 6144 512).filter isPrimeB) = pf6144f6400 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f6144 f6400
lemma f6656x256 : ((List.range' 6656 512).filter isPrimeB) = pf6656f6912 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f6656 f6912
lemma f7168x256 : ((List.range' 7168 512).filter isPrimeB) = pf7168f7424 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f7168 f7424
lemma f7680x256 : ((List.range' 7680 512).filter isPrimeB) = pf7680f7936 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f7680 f7936
lemma f8192x256 : ((List.range' 8192 512).filter isPrimeB) = pf8192f8448 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f8192 f8448
lemma f8704x256 : ((List.range' 8704 512).filter isPrimeB) = pf8704f8960 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f8704 f8960
lemma f9216x256 : ((List.range' 9216 512).filter isPrimeB) = pf9216f9472 := by
  rw [show 512 = 256+256 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f9216 f9472
lemma f9728x17 : ((List.range' 9728 273).filter isPrimeB) = pf9728f9984 := by
  rw [show 273 = 256+17 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f9728 f9984
lemma f0x256x512 : ((List.range' 0 1024).filter isPrimeB) = pf0x256f512x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f0x256 f512x256
lemma f1024x256x512 : ((List.range' 1024 1024).filter isPrimeB) = pf1024x256f1536x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f1024x256 f1536x256
lemma f2048x256x512 : ((List.range' 2048 1024).filter isPrimeB) = pf2048x256f2560x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f2048x256 f2560x256
lemma f3072x256x512 : ((List.range' 3072 1024).filter isPrimeB) = pf3072x256f3584x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f3072x256 f3584x256
lemma f4096x256x512 : ((List.range' 4096 1024).filter isPrimeB) = pf4096x256f4608x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f4096x256 f4608x256
lemma f5120x256x512 : ((List.range' 5120 1024).filter isPrimeB) = pf5120x256f5632x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f5120x256 f5632x256
lemma f6144x256x512 : ((List.range' 6144 1024).filter isPrimeB) = pf6144x256f6656x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f6144x256 f6656x256
lemma f7168x256x512 : ((List.range' 7168 1024).filter isPrimeB) = pf7168x256f7680x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f7168x256 f7680x256
lemma f8192x256x512 : ((List.range' 8192 1024).filter isPrimeB) = pf8192x256f8704x256 := by
  rw [show 1024 = 512+512 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f8192x256 f8704x256
lemma f9216x256x273 : ((List.range' 9216 785).filter isPrimeB) = pf9216x256f9728x17 := by
  rw [show 785 = 512+273 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f9216x256 f9728x17
lemma f0x256x512x1024 : ((List.range' 0 2048).filter isPrimeB) = pf0x256x512f1024x256x512 := by
  rw [show 2048 = 1024+1024 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f0x256x512 f1024x256x512
lemma f2048x256x512x1024 : ((List.range' 2048 2048).filter isPrimeB) = pf2048x256x512f3072x256x512 := by
  rw [show 2048 = 1024+1024 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f2048x256x512 f3072x256x512
lemma f4096x256x512x1024 : ((List.range' 4096 2048).filter isPrimeB) = pf4096x256x512f5120x256x512 := by
  rw [show 2048 = 1024+1024 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f4096x256x512 f5120x256x512
lemma f6144x256x512x1024 : ((List.range' 6144 2048).filter isPrimeB) = pf6144x256x512f7168x256x512 := by
  rw [show 2048 = 1024+1024 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f6144x256x512 f7168x256x512
lemma f8192x256x512x785 : ((List.range' 8192 1809).filter isPrimeB) = pf8192x256x512f9216x256x273 := by
  rw [show 1809 = 1024+785 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f8192x256x512 f9216x256x273
lemma f0x256x512x1024x2048 : ((List.range' 0 4096).filter isPrimeB) = pf0x256x512x1024f2048x256x512x1024 := by
  rw [show 4096 = 2048+2048 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f0x256x512x1024 f2048x256x512x1024
lemma f4096x256x512x1024x2048 : ((List.range' 4096 4096).filter isPrimeB) = pf4096x256x512x1024f6144x256x512x1024 := by
  rw [show 4096 = 2048+2048 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f4096x256x512x1024 f6144x256x512x1024
lemma f0x256x512x1024x2048x4096 : ((List.range' 0 8192).filter isPrimeB) = pf0x256x512x1024x2048f4096x256x512x1024x2048 := by
  rw [show 8192 = 4096+4096 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f0x256x512x1024x2048 f4096x256x512x1024x2048
lemma f0x256x512x1024x2048x4096x1809 : ((List.range' 0 10001).filter isPrimeB) = pf0x256x512x1024x2048x4096f8192x256x512x785 := by
  rw [show 10001 = 8192+1809 by decide, ← List.range'_append, List.filter_append]; exact congrArg₂ List.append f0x256x512x1024x2048x4096 f8192x256x512x785
lemma smallPrimes4_filter : (List.range 10001).filter isPrimeB = smallPrimes4L := by
  rw [List.range_eq_range']; exact f0x256x512x1024x2048x4096x1809
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma PS4_eq : PS4 = smallPrimes4L.prod := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma PS4_sq : smallPrimes4L.all (fun p => PS4 % (p * p) != 0) = true := by decide +kernel
lemma mem_smallPrimes4 {p : ℕ} : p ∈ smallPrimes4L ↔ p ≤ 10000 ∧ p.Prime := by
  rw [← smallPrimes4_filter, List.mem_filter, List.mem_range, isPrimeB_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
lemma prime_dvd_PS4 {p : ℕ} (hp : p.Prime) (h : p ∣ PS4) : p ≤ 10000 := by
  rw [PS4_eq] at h
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff hp.prime).mp h
  have ha' := mem_smallPrimes4.mp ha
  have := (Nat.prime_dvd_prime_iff_eq hp ha'.2).mp hpa
  omega
lemma not_sq_dvd_PS4 {p : ℕ} (hp : p.Prime) : ¬ p * p ∣ PS4 := by
  intro h
  have hle := prime_dvd_PS4 hp (dvd_trans (dvd_mul_right p p) h)
  have hmem : p ∈ smallPrimes4L := mem_smallPrimes4.mpr ⟨hle, hp⟩
  have := List.all_eq_true.mp PS4_sq p hmem
  simp only [bne_iff_ne, ne_eq] at this
  exact this (Nat.mod_eq_zero_of_dvd h)
lemma sqfK_sound {n : ℕ} (h : sqfK n = true) : Squarefree n := by
  unfold sqfK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hn0, hnB⟩, hcop⟩, hsq⟩ := h
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at hsq
  set g := Nat.gcd n PS4 with hg
  set m := n / g with hm
  have hgn : g ∣ n := Nat.gcd_dvd_left n PS4
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hn0
  have hnm : n = g * m := (Nat.mul_div_cancel' hgn).symm
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd hn0 hgn) hg0
  -- the prime factors of `m` are large
  have hbig : ∀ q, q.Prime → q ∣ m → 10007 ≤ q := by
    intro q hq hqm
    by_contra hlt
    have hq10 : q ≤ 10000 := by
      by_contra h'
      interval_cases q <;> norm_num at hq
    have hq4 : q ∈ smallPrimes4L := mem_smallPrimes4.mpr ⟨hq10, hq⟩
    have hqP : q ∣ PS4 := by rw [PS4_eq]; exact List.dvd_prod hq4
    have hqn : q ∣ n := hnm ▸ dvd_mul_of_dvd_right hqm g
    have hqg : q ∣ g := Nat.dvd_gcd hqn hqP
    have : q ∣ Nat.gcd g m := Nat.dvd_gcd hqg hqm
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hmsq : Squarefree m := by
    apply sqf_of_big_factors hm0 (lt_of_le_of_lt (Nat.div_le_self n g) hnB) hbig
    rintro ⟨h1, k, hk⟩
    rcases hsq with h' | h'
    · have : Nat.blt 1 m = true := Nat.blt_eq.mpr h1
      rw [this] at h'; exact Bool.noConfusion h'
    · unfold isSqK at h'
      rw [← hk, Nat.sqrt_eq k] at h'
      simp at h'
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  by_cases hpg : p ∣ g
  · -- `p ≤ 10⁴`: then `p ∣ m` too
    have hpP : p ∣ PS4 := dvd_trans hpg (Nat.gcd_dvd_right n PS4)
    have hpm : p ∣ m := by
      by_contra hpm
      have : p * p ∣ g := by
        rw [hnm] at hpp
        exact Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpm,
            (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm⟩) hpp
      exact not_sq_dvd_PS4 hp (dvd_trans this (Nat.gcd_dvd_right n PS4))
    have : p ∣ Nat.gcd g m := Nat.dvd_gcd hpg hpm
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · have hcop' : Nat.Coprime (p * p) g :=
      Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpg,
        (Nat.Prime.coprime_iff_not_dvd hp).mpr hpg⟩
    rw [hnm] at hpp
    have : p * p ∣ m := hcop'.dvd_of_dvd_mul_left hpp
    exact (Nat.squarefree_iff_prime_squarefree.mp hmsq) p hp this
lemma statement_of_classes {N : ℕ} (k : ℕ) (g : ℕ → List ℕ)
    (hP : ∀ j < k, ∀ u ∈ g j, ∀ w ∈ g j, u ≠ w → Squarefree (u * w + 1))
    (hC : ∀ v, 1 ≤ v → v ≤ N → ¬ Squarefree (v * v + 1) → ∃ j < k, v ∈ g j) (hk : k ≤ c7 N) :
    Statement N := by
  classical
  intro A hsub hA
  let f : ℕ → ℕ := fun a => if h : ∃ j < k, a ∈ g j then Classical.choose h else 0
  have hf : ∀ a ∈ A, f a < k ∧ a ∈ g (f a) := by
    intro a ha
    have haI := mem_Icc.mp (hsub ha)
    have h := hC a haI.1 haI.2 (hA a ha a ha)
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  calc A.card ≤ (range k).card := by
        apply card_le_card_of_injOn f (fun a ha => mem_range.mpr (hf a ha).1)
        intro a ha b hb hab
        by_contra hne
        have h1 := hf a ha
        have h2 := hf b hb
        have hb' : b ∈ g (f a) := by rw [hab]; exact h2.2
        exact hA a ha b hb (hP (f a) h1.1 a h1.2 b hb' hne)
    _ = k := card_range _
    _ ≤ c7 N := hk
end Erdos848
namespace Erdos848.Greedy
open ErdosComp
/- A deterministic online colouring (window of the 16 newest classes, insert or one swap)
   replacing MacchaCat's recorded move history; soundness adapted from MacchaCat, ColSound. -/
abbrev K := 16
def Clq (c : List Nat) : Prop := ∀ u ∈ c, ∀ w ∈ c, u ≠ w → Squarefree (u*w+1)
def cmp (v : Nat) (c : List Nat) : Bool := c.all (fun u => ColPack.fastSq (u*v+1))
lemma cmp_ok {v c} (h : cmp v c = true) : ∀ u ∈ c, Squarefree (u*v+1) := fun u hu =>
  sqfK_sound ((ColPack.fastEq _).symm.trans (List.all_eq_true.mp h u hu))
lemma clq_cons {v c} (hc : Clq c) (h : ∀ u ∈ c, Squarefree (u*v+1)) : Clq (v :: c) := by
  intro a ha b hb hne
  rcases List.mem_cons.mp ha with ha'|ha' <;> rcases List.mem_cons.mp hb with hb'|hb'
  · exact absurd (ha'.trans hb'.symm) hne
  · rw [ha', Nat.mul_comm]; exact h b hb'
  · rw [hb']; exact h a ha'
  · exact hc a ha' b hb' hne
lemma clq_sub {c d : List Nat} (hc : Clq c) (h : ∀ x ∈ d, x ∈ c) : Clq d :=
  fun a ha b hb hne => hc a (h a ha) b (h b hb) hne
def Ext (W W' : List (List Nat)) (x : Nat) : Prop :=
  W'.length = W.length ∧ ((∀ c ∈ W, Clq c) → ∀ c ∈ W', Clq c) ∧
  ∀ y, (y = x ∨ ∃ c ∈ W, y ∈ c) → ∃ c ∈ W', y ∈ c
def ins (v : Nat) : List (List Nat) → Option (List (List Nat))
  | [] => none
  | c :: W => if cmp v c then some ((v :: c) :: W) else
    match ins v W with
    | some r => some (c :: r)
    | none => none
lemma ins_ok {v} : ∀ {W r}, ins v W = some r → Ext W r v := by
  intro W
  induction W with
  | nil => intro r h; simp [ins] at h
  | cons c W ih =>
    intro r h
    unfold ins at h
    split at h
    · rename_i hc
      cases h
      refine ⟨by simp, ?_, ?_⟩
      · intro hall d hd
        rcases List.mem_cons.mp hd with rfl|hd
        · exact clq_cons (hall c (by simp)) (cmp_ok hc)
        · exact hall d (by simp [hd])
      · rintro y (hyx|⟨d,hd,hy⟩)
        · exact ⟨v :: c, by simp, by simp [hyx]⟩
        · rcases List.mem_cons.mp hd with hdc|hd
          · rw [hdc] at hy; exact ⟨v :: c, by simp, List.mem_cons_of_mem _ hy⟩
          · exact ⟨d, by simp [hd], hy⟩
    · split at h
      · rename_i r' hr
        cases h
        obtain ⟨hl,hq,hv⟩ := ih hr
        refine ⟨by simp [hl], ?_, ?_⟩
        · intro hall d hd
          rcases List.mem_cons.mp hd with rfl|hd
          · exact hall d (by simp)
          · exact hq (fun e he => hall e (by simp [he])) d hd
        · rintro y (hyx|⟨d,hd,hy⟩)
          · obtain ⟨e,he,hy⟩ := hv y (Or.inl hyx); exact ⟨e, by simp [he], hy⟩
          · rcases List.mem_cons.mp hd with hdc|hd
            · rw [hdc] at hy; exact ⟨c, by simp, hy⟩
            · obtain ⟨e,he,hy⟩ := hv y (Or.inr ⟨d,hd,hy⟩); exact ⟨e, by simp [he], hy⟩
      · cases h
def tryMem (v : Nat) (pre rest : List (List Nat)) (c : List Nat) : List Nat → Option (List (List Nat))
  | [] => none
  | w :: ws =>
    match (if cmp v (c.erase w) then ins w (pre.reverse ++ (v :: c.erase w) :: rest) else none) with
    | some r => some r
    | none => tryMem v pre rest c ws
lemma tryMem_ok {v pre rest c} : ∀ {ws r}, tryMem v pre rest c ws = some r → Ext (pre.reverse ++ c :: rest) r v := by
  intro ws
  induction ws with
  | nil => intro r h; simp [tryMem] at h
  | cons w ws ih =>
    intro r h
    unfold tryMem at h
    split at h
    · rename_i r' hr
      cases h
      split at hr
      · rename_i hc
        obtain ⟨hl,hq,hv⟩ := ins_ok hr
        refine ⟨by simp [hl], ?_, ?_⟩
        · intro hall
          apply hq
          intro d hd
          simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hd
          rcases hd with hd|hdc|hd
          · exact hall d (by simp [hd])
          · rw [hdc]; exact clq_cons (clq_sub (hall c (by simp)) (fun x hx => List.mem_of_mem_erase hx)) (cmp_ok hc)
          · exact hall d (by simp [hd])
        · rintro y (hyx|⟨d,hd,hy⟩)
          · exact hv _ (Or.inr ⟨v :: c.erase w, by simp, by simp [hyx]⟩)
          · simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hd
            rcases hd with hd|hdc|hd
            · exact hv _ (Or.inr ⟨d, by simp [hd], hy⟩)
            · rw [hdc] at hy
              by_cases hyw : y = w
              · exact hv _ (Or.inl hyw)
              · exact hv _ (Or.inr ⟨v :: c.erase w, by simp, List.mem_cons_of_mem _ ((List.mem_erase_of_ne hyw).mpr hy)⟩)
            · exact hv _ (Or.inr ⟨d, by simp [hd], hy⟩)
      · cases hr
    · exact ih h
def swpAux (v : Nat) : List (List Nat) → List (List Nat) → Option (List (List Nat))
  | _, [] => none
  | pre, c :: rest =>
    match tryMem v pre rest c c with
    | some r => some r
    | none => swpAux v (c :: pre) rest
lemma swpAux_ok {v} : ∀ {rest pre r}, swpAux v pre rest = some r → Ext (pre.reverse ++ rest) r v := by
  intro rest
  induction rest with
  | nil => intro pre r h; simp [swpAux] at h
  | cons c rest ih =>
    intro pre r h
    unfold swpAux at h
    split at h
    · rename_i r' hr; cases h; exact tryMem_ok hr
    · have := ih h; simpa using this
def step (n : Nat) (W : List (List Nat)) : Option (List (List Nat)) :=
  if (n+1) % 25 = 7 then some (([n+1] :: W).take K)
  else if ColPack.fastSq ((n+1)*(n+1)+1) then some W
  else match ins (n+1) W with
    | some r => some r
    | none => swpAux (n+1) [] W
def Good (L : List (List Nat)) (n : Nat) : Prop :=
  (∀ c ∈ L, Clq c) ∧ L.length = c7 n ∧
  ∀ v, 1 ≤ v → v ≤ n → ¬ Squarefree (v*v+1) → ∃ c ∈ L, v ∈ c
def Inv (n : Nat) (W : List (List Nat)) : Prop := ∃ F, Good (W ++ F) n
lemma good_stmt {L n} (h : Good L n) : Statement n := by
  obtain ⟨hq,hl,hc⟩ := h
  apply statement_of_classes L.length (fun j => L.getD j [])
  · intro j hj u hu w hw hne
    rw [List.getD_eq_getElem _ _ hj] at hu hw
    exact hq _ (List.getElem_mem hj) u hu w hw hne
  · intro v h1 h2 hn
    obtain ⟨c,hcL,hv⟩ := hc v h1 h2 hn
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hcL
    exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj]; exact hv⟩
  · omega
lemma ext_good {W W' F n} (he : Ext W W' (n+1)) (hg : Good (W ++ F) n) (h7 : (n+1) % 25 ≠ 7) :
    Good (W' ++ F) (n+1) := by
  obtain ⟨hl,hq,hv⟩ := he
  obtain ⟨gq,gl,gc⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact hq (fun d hd => gq d (List.mem_append_left _ hd)) c hc
    · exact gq c (List.mem_append_right _ hc)
  · simp only [List.length_append] at gl ⊢; unfold c7 at gl ⊢; omega
  · intro v h1 h2 hn
    by_cases hv1 : v = n+1
    · obtain ⟨c,hc,hm⟩ := hv v (Or.inl hv1); exact ⟨c, List.mem_append_left _ hc, hm⟩
    · obtain ⟨c,hc,hm⟩ := gc v h1 (by omega) hn
      rcases List.mem_append.mp hc with hc|hc
      · obtain ⟨d,hd,hm⟩ := hv v (Or.inr ⟨c,hc,hm⟩); exact ⟨d, List.mem_append_left _ hd, hm⟩
      · exact ⟨c, List.mem_append_right _ hc, hm⟩
lemma step_ok {n W W'} (hi : Inv n W) (h : step n W = some W') : Inv (n+1) W' := by
  obtain ⟨F,gq,gl,gc⟩ := hi
  unfold step at h
  split at h
  · rename_i h7
    cases h
    refine ⟨(([n+1] :: W).drop K) ++ F, ?_⟩
    rw [← List.append_assoc, List.take_append_drop]
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · intro a ha b hb hne; simp at ha hb; omega
      · exact gq c hc
    · simp only [List.length_append, List.length_cons] at gl ⊢; unfold c7 at gl ⊢; omega
    · intro v h1 h2 hn
      by_cases hv1 : v = n+1
      · exact ⟨[n+1], by simp, by simp [hv1]⟩
      · obtain ⟨c,hc,hm⟩ := gc v h1 (by omega) hn; exact ⟨c, by simp [hc], hm⟩
  · rename_i h7
    split at h
    · rename_i hs
      cases h
      refine ⟨F, gq, by unfold c7 at gl ⊢; omega, ?_⟩
      intro v h1 h2 hn
      by_cases hv1 : v = n+1
      · subst hv1; exact absurd (sqfK_sound ((ColPack.fastEq _).symm.trans hs)) hn
      · exact gc v h1 (by omega) hn
    · split at h
      · rename_i r hr; cases h; exact ⟨F, ext_good (ins_ok hr) ⟨gq,gl,gc⟩ h7⟩
      · exact ⟨F, ext_good (by simpa using swpAux_ok h) ⟨gq,gl,gc⟩ h7⟩
def run (W : List (List Nat)) (n : Nat) : Nat → Option (List (List Nat))
  | 0 => some W
  | f+1 => match step n W with
    | some W' => run W' (n+1) f
    | none => none
def Upto (n : Nat) (W : List (List Nat)) : Prop := Inv n W ∧ ∀ N ≤ n, Statement N
lemma run_ok : ∀ {f n W W'}, Upto n W → run W n f = some W' → Upto (n+f) W' := by
  intro f
  induction f with
  | zero => intro n W W' h e; simp [run] at e; subst e; exact h
  | succ f ih =>
    intro n W W' h e
    unfold run at e
    split at e
    · rename_i W1 h1
      have hi := step_ok h.1 h1
      have := ih (n := n+1) ⟨hi, fun N hN => if hl : N ≤ n then h.2 N hl else by
        obtain ⟨F,hg⟩ := hi; have : N = n+1 := by omega
        subst this; exact good_stmt hg⟩ e
      rwa [show n+1+f = n+(f+1) by omega] at this
    · cases e
lemma start : Upto 0 [] := by
  have g0 : Good ([] ++ []) 0 := ⟨by simp, by simp [c7], fun v h1 h2 => by omega⟩
  refine ⟨⟨[], g0⟩, ?_⟩
  intro N hN
  have : N = 0 := by omega
  subst this; exact good_stmt g0
lemma ch {n W W'} (f : Nat) (h : Upto n W) (e : run W n f = some W' := by
    set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in decide +kernel) : Upto (n+f) W' := run_ok h e
end Erdos848.Greedy
namespace Erdos848.Greedy
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allSmall : ∀ N ≤ 986746, Statement N := by
  have k0 : Upto 0 [] := start
  have k1 : Upto 4096 [[4068,4082],[4093,4084,4060,4057],[4052,4043,4032],[4030,3918,4008,4007],[4005,3993,3990,3986,3982],[3968,3957],[4018,3932],[3943,3907],[3893,3882],[3768,3861,3857],[3843,3832],[3818,3807],[3868,3795,3788,3782],[3817,3793,3757],[3743,3740,3732],[3719,3668,3707]] := ch 4096 k0
  have k2 : Upto 8192 [[8182],[8168,8157],[8118,8132],[8143,8130,8124,8119,8107],[8097,8093,8082],[8018,8057],[8054,8043,8042,8032],[8068,8027,8007],[8013,7968,7982],[7993,7957],[7943,7932],[7868,7907],[7893,7882],[7918,7873,7857],[7927,7850,7743,7832],[7844,7818,7807]] := ch 4096 k1
  have k3 : Upto 12288 [[12282],[12218,12257],[12267,12243,12238,12232],[12268,12207],[12168,12182],[12193,12157],[12176,12156,12143,12132],[12204,12018,12107],[12145,12100,12093,12082],[12098,12069,12068,12057],[12118,12032],[12043,12007],[11993,11982],[11918,11957],[11981,11968,11932],[11943,11907]] := ch 4096 k2
  have k4 : Upto 16384 [[16382],[16368,16357],[16343,16332],[16323,16268,16311,16307],[16354,16294,16293,16282],[16318,16257],[16218,16232],[16243,16222,16207],[16193,16182],[16118,16157],[16154,16146,16143,16132],[16168,16107],[16125,16068,16082],[16093,16057],[16043,16032],[15968,16007]] := ch 4096 k3
  have k5 : Upto 20480 [[20468,20457],[20418,20432],[20443,20407],[20393,20382],[20318,20357],[20379,20350,20343,20332],[20368,20307],[20268,20282],[20293,20257],[20243,20232],[20168,20207],[20210,20193,20192,20182],[20218,20181,20157],[20163,20118,20132],[20143,20107],[20225,20093,20082]] := ch 4096 k4
  have k6 : Upto 24576 [[24518,24557],[24543,24532],[24568,24527,24507],[24525,24468,24482],[24493,24457],[24575,24443,24435,24432],[24430,24368,24407],[24406,24393,24382],[24418,24357],[24348,24318,24332],[24343,24307],[24314,24293,24282],[24218,24266,24257],[24243,24232],[24268,24207],[24237,24168,24182]] := ch 4096 k5
  have k7 : Upto 28672 [[28668,28660,28657],[28643,28635,28632],[28631,28568,28607],[28649,28593,28590,28582],[28618,28573,28557],[28553,28518,28532],[28543,28507],[28493,28488,28482],[28418,28462,28457],[28443,28432],[28491,28468,28407],[28368,28382],[28393,28360,28357],[28343,28332],[28322,28268,28307],[28293,28282]] := ch 4096 k6
  have k8 : Upto 32768 [[32768,32758,32757],[32718,32739,32732],[32743,32707],[32716,32693,32682],[32750,32618,32657],[32687,32643,32632],[32695,32668,32619,32607],[32568,32582],[32593,32557],[32547,32543,32532],[32468,32507],[32493,32482],[32518,32457],[32491,32418,32432],[32443,32407],[32406,32393,32382]] := ch 4096 k7
  have k9 : Upto 36864 [[36857],[36846,36843,36832],[36818,36807],[36743,36782],[36772,36768,36757],[36793,36732],[36618,36707],[36741,36693,36682],[36668,36665,36657],[36718,36632],[36643,36607],[36597,36593,36582],[36574,36468,36557],[36604,36603,36543,36532],[36528,36527,36518,36507],[36568,36482]] := ch 4096 k8
  have k10 : Upto 40960 [[40957],[40953,40818,40932],[40868,40907],[40893,40882],[40918,40857],[40943,40832],[40843,40828,40807],[40793,40782],[40718,40757],[40799,40787,40743,40732],[40768,40722,40707],[40668,40682],[40693,40657],[40659,40643,40632],[40630,40568,40607],[40593,40582]] := ch 4096 k9
  have k11 : Upto 45056 [[45046,44943,45032],[45018,45007],[45053,45024,45009,44993,44982],[44918,44957],[45043,44932],[44968,44907],[44868,44882],[44893,44884,44857],[44855,44843,44832],[44768,44807],[44833,44793,44782],[44818,44757],[44693,44732],[44718,44715,44707],[44743,44682],[44618,44657]] := ch 4096 k10
  have k12 : Upto 49152 [[49143,49132],[49127,49118,49107],[49109,49068,49092,49082],[49093,49080,49057],[49055,49043,49032],[48918,49007],[48993,48982],[48968,48957],[49018,48940,48932],[48943,48911,48907],[48893,48882],[48818,48857],[48879,48843,48832],[48868,48807],[48803,48768,48782],[48793,48757]] := ch 4096 k11
  have k13 : Upto 53248 [[53243,53232],[53168,53214,53207],[53193,53182],[53218,53165,53157],[53118,53136,53132],[53143,53138,53107],[52968,53082],[53093,53057],[53043,53032],[53068,53024,53007],[53018,52996,52982],[52993,52957],[52943,52942,52932],[52967,52868,52907],[52893,52882],[52918,52857]] := ch 4096 k12
  have k14 : Upto 57344 [[57318,57332],[57343,57307],[57293,57282],[57218,57260,57257],[57243,57232],[57268,57207],[57168,57192,57182],[57229,57221,57193,57184,57157],[57147,57143,57132],[57068,57107],[57093,57082],[57118,57057],[57018,57032],[57052,57043,57007],[56993,56982],[56918,56957]] := ch 4096 k13
  have k15 : Upto 61440 [[61432],[61434,61418,61407],[61417,61368,61382],[61393,61357],[61352,61343,61332],[61243,61307],[61306,61293,61282],[61277,61268,61257],[61298,61248,61218,61232],[61318,61230,61207],[61193,61182],[61118,61157],[61143,61132],[61168,61108,61107],[61068,61082],[61093,61057]] := ch 4096 k14
  have k16 : Upto 65536 [[65532],[65468,65507],[65502,65493,65482],[65518,65473,65457],[65418,65432],[65443,65407],[65393,65382],[65318,65357],[65352,65343,65332],[65368,65307],[65333,65304,65268,65282],[65293,65276,65257],[65243,65232],[65168,65207],[65193,65182],[65218,65181,65164,65157]] := ch 4096 k15
  have k17 : Upto 69632 [[69632],[69618,69611,69607],[69593,69582],[69518,69558,69557],[69543,69532],[69568,69507],[69468,69482],[69493,69457],[69443,69432],[69318,69407],[69529,69393,69382],[69398,69389,69368,69360,69357],[69418,69399,69332],[69343,69322,69307],[69293,69282],[69218,69257]] := ch 4096 k16
  have k18 : Upto 73728 [[73718,73707],[73668,73682],[73693,73657],[73643,73632],[73568,73614,73607],[73593,73586,73585,73582],[73618,73557],[73518,73532],[73543,73534,73507],[73493,73482],[73418,73457],[73444,73443,73432],[73468,73407],[73445,73416,73368,73382],[73393,73357],[73343,73332]] := ch 4096 k17
  have k19 : Upto 77824 [[77768,77810,77807],[77793,77782],[77818,77757],[77718,77732],[77779,77743,77707],[77693,77682],[77670,77618,77657],[77704,77703,77643,77632],[77668,77607],[77641,77568,77582],[77593,77557],[77543,77532],[77468,77507],[77501,77493,77490,77482],[77518,77472,77457],[77459,77418,77432]] := ch 4096 k18
  have k20 : Upto 81920 [[81918,81907],[81893,81882],[81818,81866,81857],[81895,81879,81843,81832],[81868,81807],[81825,81768,81782],[81793,81757],[81743,81732],[81726,81618,81707],[81697,81694,81693,81682],[81689,81668,81657],[81749,81718,81632],[81643,81607],[81593,81582],[81468,81557],[81543,81536,81532]] := ch 4096 k19
  have k21 : Upto 86016 [[86007],[85998,85968,85982],[85993,85957],[85951,85943,85932],[85922,85868,85907],[85893,85882],[85918,85857],[85871,85818,85832],[85843,85807],[85795,85718,85782],[85793,85757],[85823,85743,85732],[85768,85707],[85741,85668,85682],[85753,85693,85657],[85643,85632]] := ch 4096 k20
  have k22 : Upto 90112 [[90107],[90093,90082],[90068,90057],[90018,90038,90032],[90043,90028,90007],[89993,89982],[89978,89918,89957],[89986,89946,89943,89932],[89968,89907],[89917,89868,89882],[89893,89857],[89843,89838,89832],[89768,89807],[89841,89817,89809,89793,89782],[89818,89757],[89718,89732]] := ch 4096 k21
  have k23 : Upto 94208 [[94207],[94193,94182],[94176,94118,94157],[94203,94151,94143,94132],[94168,94107],[94068,94082],[94093,94057],[94043,94032],[94034,93968,94007],[93993,93982],[94018,93957],[94063,93963,93918,93932],[93943,93907],[93894,93893,93882],[93768,93857],[93887,93818,93832]] := ch 4096 k22
  have k24 : Upto 98304 [[98268,98288,98282],[98293,98257],[98298,98259,98243,98232],[98222,98168,98207],[98193,98182],[98218,98157],[98118,98142,98132],[98143,98119,98107],[98093,98090,98082],[98018,98057],[98043,98032],[98068,98007],[98009,97968,97982],[97993,97957],[97950,97943,97932],[97868,97907]] := ch 4096 k23
  have k25 : Upto 102400 [[102393,102382],[102368,102357],[102344,102318,102332],[102343,102315,102307],[102293,102282],[102218,102257],[102243,102232],[102268,102207],[102168,102182],[102193,102157],[102146,102143,102132],[102175,102068,102107],[102093,102082],[102118,102057],[102163,102055,102018,102032],[102043,102007]] := ch 4096 k24
  have k26 : Upto 106496 [[106493,106482],[106418,106457],[106443,106432],[106468,106407],[106475,106400,106368,106390,106382],[106393,106357],[106371,106343,106332],[106218,106314,106307],[106293,106282],[106281,106268,106257],[106193,106242,106232],[106318,106231,106207],[106243,106202,106182],[106118,106157],[106143,106132],[106168,106107]] := ch 4096 k25
  have k27 : Upto 110592 [[110582],[110568,110557],[110543,110532],[110468,110507],[110493,110482],[110518,110457],[110456,110418,110436,110432],[110443,110427,110407],[110393,110382],[110318,110360,110357],[110343,110332],[110368,110307],[110268,110287,110282],[110293,110258,110257],[110243,110232],[110168,110212,110207]] := ch 4096 k26
  have k28 : Upto 114688 [[114686,114682],[114681,114669,114668,114657],[114618,114632],[114643,114627,114607],[114652,114593,114582],[114393,114557],[114543,114532],[114518,114512,114507],[114568,114482],[114468,114457],[114483,114443,114432],[114368,114407],[114493,114417,114406,114382],[114418,114357],[114318,114335,114332],[114343,114307]] := ch 4096 k27
  have k29 : Upto 118784 [[118782],[118718,118757],[118768,118741,118737,118732],[118743,118708,118707],[118668,118682],[118693,118657],[118643,118632],[118622,118568,118607],[118593,118582],[118618,118557],[118443,118540,118532],[118539,118528,118518,118507],[118493,118482],[118478,118418,118457],[118543,118452,118432],[118468,118407]] := ch 4096 k28
  have k30 : Upto 122880 [[122868,122857],[122875,122843,122832],[122768,122807],[122793,122782],[122818,122764,122757],[122745,122718,122732],[122863,122827,122743,122707],[122693,122682],[122676,122618,122657],[122787,122643,122632],[122668,122624,122607],[122543,122582],[122574,122568,122557],[122593,122532],[122595,122418,122507],[122493,122482]] := ch 4096 k29
  have k31 : Upto 126976 [[126968,126957],[126950,126843,126932],[126918,126907],[126909,126905,126893,126882],[126818,126857],[126943,126832],[126868,126807],[126849,126833,126768,126782],[126820,126793,126757],[126743,126732],[126618,126707],[126693,126682],[126680,126668,126657],[126718,126651,126632],[126643,126607],[126620,126593,126582]] := ch 4096 k30
  have k32 : Upto 131072 [[131018,131057],[131043,131032],[131068,131007],[130968,130982],[130993,130957],[130955,130943,130932],[130868,130907],[131045,130918,130917,130905,130882],[130893,130876,130857],[130743,130832],[130879,130818,130807],[130796,130793,130782],[130718,130757],[130843,130740,130736,130732],[130768,130707],[130668,130682]] := ch 4096 k31
  have k33 : Upto 135168 [[135168,135157],[135143,135132],[135130,135068,135107],[135101,135093,135082],[135118,135057],[135018,135032],[135043,135007],[135001,134993,134982],[134918,134961,134957],[134950,134943,134932],[134968,134907],[134925,134868,134882],[134893,134858,134857],[134843,134832],[134718,134807],[134793,134792,134782]] := ch 4096 k32
  have k34 : Upto 139264 [[139260,139257],[139218,139232],[139243,139207],[139193,139182],[139118,139157],[139143,139132],[139186,139168,139107],[139145,139068,139082],[139093,139057],[139047,139043,139032],[138968,139007],[139017,138993,138988,138982],[139018,138957],[138971,138918,138932],[138943,138907],[138893,138882]] := ch 4096 k33
  have k35 : Upto 143360 [[143357],[143343,143332],[143318,143307],[143306,143268,143282],[143329,143293,143257],[143243,143242,143232],[143168,143207],[143213,143193,143182],[143218,143157],[143263,143118,143132],[143143,143107],[143093,143082],[143073,143018,143057],[143044,143043,143032],[143068,143007],[143017,142968,142982]] := ch 4096 k34
  have k36 : Upto 147456 [[147443,147438,147432],[147428,147368,147407],[147393,147382],[147418,147357],[147318,147332],[147352,147343,147307],[147298,147293,147282],[147269,147218,147257],[147316,147243,147232],[147268,147207],[147216,147168,147182],[147193,147157],[147143,147139,147132],[147134,146918,147107],[147129,147100,147093,147082],[147068,147057]] := ch 4096 k35
  have k37 : Upto 151552 [[151518,151532],[151543,151507],[151494,151493,151482],[151418,151457],[151523,151474,151443,151432],[151468,151407],[151398,151368,151382],[151421,151393,151357],[151343,151339,151332],[151268,151307],[151354,151293,151282],[151318,151257],[151325,151218,151232],[151243,151207],[151193,151185,151182],[151068,151157]] := ch 4096 k36
  have k38 : Upto 155648 [[155643,155632],[155626,155618,155607],[155600,155568,155582],[155593,155557],[155579,155550,155544,155543,155532],[155520,155468,155507],[155493,155482],[155518,155457],[155418,155432],[155443,155410,155407],[155393,155382],[155444,155381,155318,155357],[155343,155332],[155368,155307],[155243,155282],[155326,155317,155268,155257]] := ch 4096 k37
  have k39 : Upto 159744 [[159743,159732],[159668,159707],[159693,159682],[159718,159657],[159618,159635,159632],[159643,159607],[159606,159593,159582],[159468,159566,159557],[159543,159532],[159518,159507],[159613,159568,159490,159482],[159493,159457],[159466,159443,159432],[159368,159407],[159437,159393,159382],[159418,159357]] := ch 4096 k38
  have k40 : Upto 163840 [[163832],[163831,163818,163807],[163825,163793,163782],[163718,163757],[163743,163732],[163768,163731,163707],[163668,163690,163682],[163593,163662,163657],[163691,163643,163632],[163518,163612,163607],[163693,163582],[163568,163557],[163618,163536,163532],[163543,163522,163507],[163493,163482],[163368,163458,163457]] := ch 4096 k39
  have k41 : Upto 167936 [[167932],[167918,167907],[167916,167868,167887,167882],[167893,167857],[167843,167832],[167768,167807],[167793,167782],[167818,167757],[167871,167747,167718,167732],[167743,167722,167707],[167693,167682],[167618,167658,167657],[167643,167632],[167668,167607],[167568,167582],[167593,167578,167557]] := ch 4096 k40
  have k42 : Upto 172032 [[172032],[171968,172007],[171993,171982],[172018,171972,171957],[171918,171932],[171943,171907],[171917,171893,171882],[171818,171857],[171843,171840,171832],[171868,171807],[171848,171803,171768,171782],[171849,171793,171774,171757],[171743,171732],[171668,171707],[171704,171693,171682],[171718,171657]] := ch 4096 k41
  have k43 : Upto 176128 [[176127,176118,176107],[176093,176082],[175993,176057],[176043,176032],[176039,176028,176018,176007],[175999,175968,175982],[176068,175957],[175943,175932],[175868,175907],[175893,175882],[175918,175864,175857],[175859,175818,175832],[175963,175843,175830,175810,175807],[175793,175782],[175718,175757],[175750,175743,175732]] := ch 4096 k42
  have k44 : Upto 180224 [[180224,180218,180207],[180168,180182],[180193,180157],[180143,180132],[180068,180107],[180093,180085,180082],[180118,180084,180057],[180055,180018,180032],[180043,180015,180007],[179993,179982],[180009,179918,179957],[179943,179932],[179968,179915,179907],[179843,179886,179882],[179933,179868,179857],[179893,179832]] := ch 4096 k43
  have k45 : Upto 184320 [[184218,184307],[184309,184293,184282],[184280,184268,184257],[184193,184232],[184318,184207],[184243,184182],[184220,184118,184157],[184143,184138,184132],[184168,184131,184128,184107],[184133,184140,184068,184082],[184093,184057],[184055,184043,184032],[184111,183968,184007],[183993,183982],[184018,183957],[183971,183959,183918,183942,183932]] := ch 4096 k44
  have k46 : Upto 188416 [[188407],[188393,188390,188382],[188268,188365,188357],[188343,188336,188332],[188318,188307],[188243,188282],[188368,188257],[188293,188232],[188118,188207],[188196,188193,188182],[188177,188168,188157],[188218,188167,188132],[188143,188107],[188101,188093,188088,188082],[188018,188057],[188043,188032]] := ch 4096 k45
  have k47 : Upto 192512 [[192512,192507],[192468,192482],[192493,192457],[192443,192432],[192368,192407],[192436,192421,192393,192382],[192418,192392,192357],[192318,192332],[192343,192307],[192293,192282],[192218,192257],[192252,192243,192232],[192268,192223,192207],[192168,192182],[192193,192157],[192147,192143,192132]] := ch 4096 k46
  have k48 : Upto 196608 [[196607],[196593,196582],[196568,196557],[196558,196518,196532],[196543,196531,196507],[196493,196482],[196368,196457],[196443,196432],[196448,196418,196407],[196477,196468,196382],[196393,196357],[196343,196332],[196268,196308,196307],[196293,196282],[196318,196269,196257],[196397,196262,196218,196233,196232]] := ch 4096 k47
  have k49 : Upto 200704 [[200702,200693,200682],[200673,200618,200657],[200643,200632],[200668,200607],[200568,200582],[200604,200593,200557],[200543,200532],[200468,200507],[200528,200504,200493,200482],[200518,200457],[200343,200432],[200418,200407],[200533,200417,200393,200382],[200318,200364,200357],[200443,200335,200332],[200368,200315,200307]] := ch 4096 k48
  have k50 : Upto 204800 [[204768,204782],[204793,204758,204757],[204743,204732],[204668,204707],[204729,204704,204693,204682],[204718,204657],[204650,204618,204632],[204643,204607],[204593,204589,204582],[204518,204560,204557],[204574,204543,204532],[204568,204535,204507],[204468,204482],[204493,204457],[204443,204432],[204368,204407]] := ch 4096 k49
  have k51 : Upto 208896 [[208893,208882],[208868,208857],[208818,208832],[208843,208822,208807],[208814,208793,208785,208782],[208718,208757],[208743,208732],[208768,208707],[208696,208668,208682],[208693,208657],[208643,208632],[208620,208568,208616,208607],[208609,208593,208582],[208645,208618,208557],[208518,208532],[208543,208527,208507]] := ch 4096 k50
  have k52 : Upto 212992 [[212982],[212984,212918,212957],[212955,212943,212932],[212968,212907],[212768,212882],[212893,212870,212857],[212843,212832],[212868,212814,212807],[212841,212793,212782],[212818,212757],[212718,212742,212732],[212779,212743,212707],[212701,212693,212682],[212672,212618,212666,212657],[212643,212632],[212668,212607]] := ch 4096 k51
  have k53 : Upto 217088 [[217082],[217077,217068,217057],[217066,217043,217032],[217019,216968,217007],[217001,216993,216982],[217018,216957],[216918,216937,216932],[216943,216926,216907],[216897,216893,216882],[216818,216857],[216843,216832],[216868,216807],[216768,216788,216782],[216793,216757],[216743,216732],[216668,216712,216707]] := ch 4096 k52
  have k54 : Upto 221184 [[221182],[221168,221157],[221151,221118,221142,221132],[221143,221122,221107],[221093,221082],[220968,221057],[221123,221047,221043,221032],[221018,221007],[220943,220982],[221068,220957],[220993,220932],[220868,220907],[220953,220893,220882],[220918,220857],[220818,220832],[220843,220834,220807]] := ch 4096 k53
  have k55 : Upto 225280 [[225218,225257],[225243,225232],[225268,225207],[225168,225182],[225220,225193,225178,225169,225157],[225143,225132],[225068,225107],[225093,225082],[225118,225057],[225018,225038,225032],[225043,225007],[225009,224993,224982],[224918,224957],[224943,224932],[224968,224907],[224937,224868,224882]] := ch 4096 k54
  have k56 : Upto 229376 [[229368,229357],[229343,229332],[229268,229307],[229293,229282],[229318,229257],[229263,229218,229232],[229243,229234,229215,229207],[229193,229182],[229068,229157],[229143,229132],[229139,229118,229107],[229094,228993,229082],[229168,229065,229057],[229043,229032],[228968,229007],[229093,228994,228982]] := ch 4096 k55
  have k57 : Upto 233472 [[233468,233457],[233459,233418,233432],[233443,233407],[233393,233382],[233318,233357],[233343,233332],[233368,233319,233307],[233193,233290,233282],[233268,233261,233257],[233243,233232],[233168,233207],[233293,233281,233182],[233218,233185,233157],[233150,233118,233132],[233143,233107],[233121,233093,233082]] := ch 4096 k56
  have k58 : Upto 237568 [[237518,237557],[237544,237543,237532],[237568,237523,237507],[237515,237468,237482],[237520,237493,237462,237457],[237443,237432],[237368,237407],[237393,237382],[237418,237384,237357],[237399,237375,237346,237318,237332],[237343,237307],[237293,237282],[237218,237257],[237243,237232],[237268,237231,237207],[237206,237203,237143,237182]] := ch 4096 k57
  have k59 : Upto 241664 [[241657],[241643,241642,241632],[241568,241607],[241600,241593,241582],[241618,241557],[241566,241493,241532],[241571,241518,241507],[241543,241482],[241418,241457],[241491,241443,241432],[241468,241431,241408,241407],[241368,241382],[241402,241393,241357],[241353,241218,241332],[241343,241326,241307],[241293,241282]] := ch 4096 k58
  have k60 : Upto 245760 [[245757],[245718,245732],[245743,245707],[245693,245688,245682],[245568,245657],[245656,245643,245632],[245618,245612,245607],[245668,245627,245595,245582],[245613,245593,245557],[245543,245532],[245531,245468,245507],[245493,245482],[245518,245458,245457],[245487,245418,245432],[245443,245407],[245393,245382]] := ch 4096 k59
  have k61 : Upto 249856 [[249852,249843,249832],[249818,249807],[249768,249782],[249793,249757],[249743,249732],[249734,249668,249712,249707],[249736,249718,249687,249683,249682],[249693,249658,249657],[249618,249632],[249643,249611,249607],[249593,249582],[249518,249557],[249543,249532],[249568,249514,249507],[249501,249468,249482],[249493,249457]] := ch 4096 k60
  have k62 : Upto 253952 [[253818,253941,253937,253932],[253943,253908,253907],[253893,253882],[253868,253857],[253918,253832],[253843,253807],[253793,253782],[253780,253668,253757],[253743,253732],[253739,253718,253707],[253768,253710,253704,253682],[253693,253657],[253670,253643,253632],[253568,253607],[253593,253582],[253618,253557]] := ch 4096 k61
  have k63 : Upto 258048 [[258018,258039,258032],[258043,258007],[257993,257982],[257918,257957],[257964,257943,257932],[257968,257928,257907],[257868,257882],[257893,257857],[257843,257832],[257826,257768,257807],[257824,257793,257782],[257818,257757],[257750,257693,257732],[257718,257707],[257743,257682],[257618,257657]] := ch 4096 k62
  have k64 : Upto 262144 [[262143,262132],[262118,262107],[262068,262085,262082],[262124,262093,262057],[262043,262032],[262020,261968,262007],[262049,261993,261982],[262018,261957],[261918,261932],[261943,261907],[261897,261893,261882],[261872,261768,261858,261857],[261851,261843,261832],[261818,261807],[261880,261868,261796,261782],[261793,261757]] := ch 4096 k63
  have k65 : Upto 266240 [[266232],[266168,266207],[266193,266182],[266218,266157],[266118,266132],[266143,266131,266107],[266105,266093,266082],[266076,266018,266057],[266043,266032],[266068,266007],[265968,265982],[265993,265976,265957],[265943,265932],[265868,265907],[265936,265893,265882],[265918,265857]] := ch 4096 k64
  have k66 : Upto 270336 [[270332],[270330,270318,270307],[270301,270293,270282],[270270,270218,270257],[270243,270232],[270268,270263,270207],[270253,270168,270182],[270193,270177,270161,270157],[270164,270143,270132],[270068,270107],[270093,270082],[270118,270057],[270018,270032],[270043,270007],[270002,269993,269992,269982],[269918,269964,269957]] := ch 4096 k65
  have k67 : Upto 274432 [[274432],[274418,274407],[274368,274386,274382],[274393,274381,274357],[274343,274332],[274268,274307],[274293,274282],[274318,274257],[274299,274218,274232],[274243,274207],[274217,274193,274188,274182],[274118,274157],[274223,274143,274132],[274168,274107],[274125,274068,274082],[274093,274057]] := ch 4096 k66
  have k68 : Upto 278528 [[278468,278507],[278493,278482],[278518,278457],[278418,278442,278432],[278443,278412,278407],[278393,278382],[278268,278357],[278343,278332],[278330,278318,278307],[278413,278368,278345,278282],[278293,278269,278257],[278244,278243,278232],[278168,278207],[278273,278193,278182],[278218,278157],[278175,278118,278132]] := ch 4096 k67
  have k69 : Upto 282624 [[282618,282607],[282617,282602,282518,282582],[282593,282557],[282604,282543,282535,282532],[282568,282507],[282498,282468,282482],[282493,282469,282457],[282443,282432],[282368,282407],[282393,282382],[282418,282357],[282391,282318,282332],[282343,282315,282307],[282300,282293,282282],[282329,282218,282257],[282243,282232]] := ch 4096 k68
  have k70 : Upto 286720 [[286718,286707],[286694,286668,286682],[286693,286657],[286650,286643,286632],[286568,286607],[286593,286582],[286618,286557],[286554,286518,286532],[286543,286507],[286525,286418,286482],[286493,286457],[286443,286432],[286468,286407],[286368,286385,286382],[286437,286393,286361,286357],[286356,286343,286332]] := ch 4096 k69
  have k71 : Upto 290816 [[290807],[290793,290782],[290772,290768,290757],[290750,290718,290732],[290779,290743,290707],[290696,290693,290682],[290618,290657],[290643,290632],[290668,290610,290607],[290568,290582],[290593,290581,290557],[290543,290532],[290418,290507],[290493,290482],[290518,290457],[290483,290468,290435,290432]] := ch 4096 k70
  have k72 : Upto 294912 [[294907],[294893,294882],[294818,294857],[294843,294835,294832],[294868,294807],[294806,294768,294782],[294793,294757],[294743,294742,294732],[294668,294707],[294693,294682],[294718,294657],[294666,294618,294641,294637,294632],[294643,294607],[294593,294582],[294518,294557],[294543,294532]] := ch 4096 k71
  have k73 : Upto 299008 [[299007],[298968,298982],[298993,298957],[298943,298932],[298818,298907],[298893,298882],[298868,298862,298857],[298918,298891,298850,298840,298832],[298864,298843,298807],[298793,298788,298782],[298718,298757],[298768,298732],[298743,298722,298707],[298668,298682],[298693,298657],[298643,298632]] := ch 4096 k72
  have k74 : Upto 303104 [[303093,303082],[303068,303057],[303081,302868,303032],[303091,303043,303007],[302993,302982],[303018,302958,302957],[303087,302947,302943,302932],[302968,302910,302907],[302977,302918,302882],[302893,302872,302857],[302843,302832],[302834,302768,302807],[302801,302793,302782],[302818,302778,302769,302757],[302749,302718,302732],[302743,302719,302707]] := ch 4096 k73
  have k75 : Upto 307200 [[307193,307182],[307172,307169,307118,307157],[307190,307143,307132],[307168,307107],[307068,307082],[307093,307057],[307043,307032],[306968,307007],[307006,306993,306982],[307018,306974,306957],[306956,306918,306932],[307003,306943,306924,306907],[306917,306893,306882],[306880,306818,306857],[306843,306832],[306868,306834,306807]] := ch 4096 k74
  have k76 : Upto 311296 [[311268,311291,311282],[311293,311257],[311243,311232],[311228,311118,311215,311211,311207],[311193,311182],[311168,311157],[311218,311199,311132],[311143,311107],[311129,311093,311082],[310968,311057],[311059,311043,311032],[311030,311018,311007],[311068,310982],[311002,310993,310957],[310943,310932],[310926,310818,310907]] := ch 4096 k75
  have k77 : Upto 315392 [[315382],[315368,315357],[315318,315337,315332],[315343,315334,315307],[315293,315282],[315218,315261,315257],[315255,315243,315232],[315268,315207],[315168,315187,315182],[315284,315193,315157],[315143,315132],[315068,315108,315107],[315093,315086,315082],[315118,315057],[315048,315018,315032],[315115,315043,315007]] := ch 4096 k76
  have k78 : Upto 319488 [[319482],[319480,319418,319457],[319443,319432],[319468,319407],[319368,319383,319382],[319393,319357],[319375,319343,319340,319332],[319324,319218,319311,319307],[319293,319282],[319268,319257],[319193,319232],[319318,319207],[319243,319182],[319118,319157],[319143,319142,319132],[319171,319168,319107]] := ch 4096 k77
  have k79 : Upto 323584 [[323582],[323568,323565,323557],[323468,323536,323535,323532],[323543,323507],[323493,323482],[323518,323457],[323418,323432],[323443,323407],[323429,323396,323393,323382],[323318,323357],[323367,323343,323332],[323368,323307],[323353,323268,323282],[323293,323257],[323243,323232],[323118,323207]] := ch 4096 k78
  have k80 : Upto 327680 [[327668,327657],[327543,327632],[327618,327607],[327621,327593,327592,327582],[327518,327557],[327643,327532],[327568,327507],[327468,327482],[327493,327457],[327475,327452,327443,327432],[327423,327368,327407],[327417,327393,327382],[327418,327357],[327399,327318,327332],[327343,327308,327307],[327293,327282]] := ch 4096 k79
  have k81 : Upto 331776 [[331718,331757],[331743,331732],[331768,331734,331707],[331668,331682],[331693,331677,331657],[331648,331643,331632],[331568,331607],[331593,331582],[331618,331557],[331518,331535,331532],[331543,331508,331507],[331521,331493,331482],[331418,331457],[331479,331455,331443,331432],[331468,331415,331407],[331395,331368,331382]] := ch 4096 k80
  have k82 : Upto 335872 [[335868,335857],[335856,335843,335832],[335822,335718,335807],[335793,335782],[335780,335768,335757],[335818,335733,335732],[335743,335707],[335693,335682],[335618,335657],[335704,335643,335632],[335668,335607],[335600,335568,335582],[335593,335572,335557],[335567,335564,335543,335535,335532],[335522,335468,335507],[335493,335482]] := ch 4096 k81
  have k83 : Upto 339968 [[339968,339958,339957],[339918,339940,339932],[339943,339907],[339929,339902,339893,339882],[339768,339857],[339843,339832],[339743,339807],[339877,339868,339826,339805,339789,339782],[339793,339760,339757],[339818,339732],[339723,339668,339707],[339693,339682],[339718,339657],[339618,339632],[339643,339607],[339629,339620,339593,339582]] := ch 4096 k82
  have k84 : Upto 344064 [[344057],[344043,344032],[344018,344014,344010,344007],[343968,343985,343982],[343993,343957],[343948,343943,343932],[343928,343868,343907],[343893,343882],[343918,343872,343857],[343845,343818,343832],[343843,343807],[343816,343793,343782],[343718,343757],[343743,343732],[343768,343736,343707],[343668,343682]] := ch 4096 k83
  have k85 : Upto 348160 [[348157],[348143,348132],[348068,348107],[348133,348093,348082],[348118,348057],[348018,348041,348032],[348070,348043,348007],[347993,347982],[347994,347918,347957],[347943,347932],[347968,347907],[347901,347868,347888,347882],[347893,347872,347857],[347843,347832],[347718,347816,347807],[347793,347782]] := ch 4096 k84
  have k86 : Upto 352256 [[352253,352218,352232],[352243,352207],[352193,352185,352182],[352118,352157],[352143,352132],[352168,352107],[352126,352068,352083,352082],[352093,352057],[352043,352040,352032],[351968,352007],[351993,351982],[352018,351957],[351964,351950,351918,351932],[351943,351928,351907],[352097,351893,351882],[351818,351857]] := ch 4096 k85
  have k87 : Upto 356352 [[356351,356343,356332],[356322,356318,356307],[356299,356268,356282],[356293,356257],[356267,356243,356232],[356168,356207],[356193,356182],[356218,356157],[356153,356118,356132],[356143,356107],[356093,356082],[355993,356057],[356104,356086,356043,356032],[356018,356010,356007],[356013,355994,355968,355982],[356068,355984,355957]] := ch 4096 k86
  have k88 : Upto 360448 [[360443,360432],[360368,360407],[360421,360393,360382],[360418,360378,360357],[360345,360293,360332],[360318,360307],[360343,360306,360282],[360218,360257],[360255,360243,360238,360232],[360268,360207],[360209,360168,360182],[360193,360157],[360164,360143,360132],[360068,360112,360107],[360093,360082],[360118,360069,360057]] := ch 4096 k87
  have k89 : Upto 364544 [[364518,364532],[364543,364507],[364493,364482],[364418,364457],[364467,364463,364443,364436,364432],[364468,364434,364407],[364399,364368,364391,364382],[364393,364357],[364343,364332],[364268,364307],[364294,364293,364282],[364318,364265,364257],[364271,364218,364232],[364243,364207],[364194,364193,364182],[364178,364068,364157]] := ch 4096 k88
  have k90 : Upto 368640 [[368632],[368618,368607],[368543,368591,368582],[368568,368557],[368593,368532],[368519,368468,368507],[368517,368513,368493,368490,368482],[368518,368477,368457],[368418,368437,368432],[368479,368443,368426,368407],[368399,368318,368382],[368393,368378,368357],[368350,368343,368332],[368368,368307],[368321,368317,368268,368282],[368293,368257]] := ch 4096 k89
  have k91 : Upto 372736 [[372732],[372618,372715,372707],[372693,372682],[372668,372657],[372718,372632],[372643,372607],[372593,372582],[372518,372557],[372604,372559,372546,372543,372532],[372568,372522,372507],[372575,372468,372483,372482],[372493,372485,372457],[372443,372432],[372318,372407],[372406,372393,372382],[372389,372377,372368,372357]] := ch 4096 k90
  have k92 : Upto 376832 [[376832],[376818,376807],[376809,376800,376793,376782],[376718,376757],[376771,376743,376732],[376768,376727,376707],[376668,376682],[376693,376657],[376643,376632],[376631,376568,376607],[376605,376602,376593,376592,376582],[376618,376557],[376518,376532],[376543,376507],[376493,376482],[376529,376418,376462,376457]] := ch 4096 k91
  have k93 : Upto 380928 [[380918,380907],[380868,380882],[380893,380857],[380864,380856,380843,380832],[380768,380807],[380793,380782],[380818,380757],[380753,380718,380732],[380827,380743,380707],[380693,380682],[380568,380658,380657],[380687,380651,380643,380632],[380699,380618,380607],[380668,380582],[380593,380557],[380575,380543,380532]] := ch 4096 k92
  have k94 : Upto 385024 [[384968,385007],[384993,384986,384982],[385018,384957],[384918,384932],[384943,384910,384907],[384912,384893,384882],[384818,384857],[384883,384843,384832],[384868,384807],[384806,384768,384782],[384793,384780,384757],[384743,384732],[384668,384714,384707],[384697,384693,384682],[384718,384657],[384618,384632]] := ch 4096 k93
  have k95 : Upto 389120 [[389118,389108,389107],[389093,389082],[389018,389057],[389043,389032],[389068,389007],[388968,388982],[388993,388957],[388956,388943,388939,388932],[388868,388907],[388913,388893,388882],[388918,388857],[388818,388832],[388843,388807],[388793,388782],[388770,388718,388757],[388799,388743,388732]] := ch 4096 k94
  have k96 : Upto 393216 [[393207],[393168,393182],[393193,393157],[393164,393143,393132],[393068,393107],[393109,393093,393082],[393118,393078,393057],[393018,393032],[393043,393024,393007],[393020,393002,392993,392982],[392976,392918,392957],[392995,392943,392932],[392968,392907],[392868,392882],[392893,392857],[392855,392843,392832]] := ch 4096 k95
  have k97 : Upto 397312 [[397307],[397293,397282],[397268,397257],[397193,397232],[397218,397207],[397243,397220,397182],[397118,397157],[397259,397143,397132],[397168,397127,397124,397107],[397094,397018,397082],[397249,397068,397057],[397080,397051,397048,397043,397032],[396968,397007],[396993,396982],[397093,396957],[396918,396932]] := ch 4096 k96
  have k98 : Upto 401408 [[401407],[401393,401382],[401318,401362,401357],[401343,401332],[401383,401368,401307],[401381,401305,401268,401282],[401293,401276,401257],[401243,401232],[401234,401118,401207],[401193,401186,401182],[401198,401168,401157],[401218,401187,401136,401132],[401170,401143,401107],[401116,401094,401093,401082],[401018,401057],[401043,401032]] := ch 4096 k97
  have k99 : Upto 405504 [[405499,405468,405482],[405501,405493,405457],[405443,405432],[405368,405407],[405402,405393,405382],[405429,405418,405357],[405318,405341,405332],[405403,405343,405307],[405361,405321,405293,405282],[405325,405218,405257],[405243,405232],[405268,405207],[405216,405093,405192,405182],[405168,405157],[405143,405140,405132],[405068,405107]] := ch 4096 k98
  have k100 : Upto 409600 [[409593,409586,409582],[409568,409557],[409551,409518,409532],[409543,409526,409507],[409493,409482],[409368,409457],[409443,409432],[409475,409418,409407],[409468,409388,409382],[409448,409417,409393,409357],[409343,409332],[409218,409307],[409293,409282],[409268,409262,409257],[409318,409248,409232],[409243,409219,409207]] := ch 4096 k99
  have k101 : Upto 413696 [[413693,413682],[413618,413657],[413643,413642,413632],[413668,413607],[413613,413597,413493,413582],[413568,413557],[413555,413543,413532],[413468,413507],[413593,413521,413482],[413518,413473,413457],[413444,413418,413432],[413443,413407],[413393,413382],[413318,413357],[413423,413343,413332],[413368,413308,413307]] := ch 4096 k100
  have k102 : Upto 417792 [[417782],[417768,417757],[417618,417732],[417743,417726,417707],[417693,417682],[417698,417669,417668,417662,417657],[417718,417632],[417643,417607],[417593,417582],[417518,417557],[417567,417543,417532],[417568,417507],[417500,417468,417482],[417529,417493,417457],[417443,417432],[417428,417368,417407]] := ch 4096 k101
  have k103 : Upto 421888 [[421882],[421868,421857],[421850,421818,421832],[421843,421807],[421793,421782],[421769,421718,421757],[421767,421754,421743,421732],[421768,421707],[421725,421668,421689,421682],[421693,421657],[421643,421632],[421518,421607],[421613,421593,421585,421582],[421618,421573,421557],[421568,421556,421535,421532],[421579,421543,421507]] := ch 4096 k102
  have k104 : Upto 425984 [[425982],[425918,425957],[425979,425950,425943,425932],[425968,425907],[425948,425868,425882],[425893,425876,425857],[425843,425832],[425768,425810,425807],[425793,425782],[425818,425781,425757],[425618,425735,425732],[425718,425707],[425693,425682],[425593,425657],[425659,425643,425642,425632],[425743,425671,425612,425607]] := ch 4096 k103
  have k105 : Upto 430080 [[430068,430057],[430070,430051,430043,430035,430032],[429968,430007],[430006,429993,429982],[430018,429994,429958,429957],[429918,429932],[429943,429907],[429893,429882],[429818,429866,429857],[429843,429832],[429868,429807],[429983,429768,429792,429782],[429837,429793,429781,429757],[429743,429732],[429668,429710,429707],[429705,429697,429693,429682]] := ch 4096 k104
  have k106 : Upto 434176 [[434168,434157],[434093,434132],[434118,434107],[434143,434116,434090,434082],[434076,434018,434062,434057],[434091,434043,434040,434032],[434068,434007],[433997,433968,433982],[433993,433957],[433943,433932],[433843,433915,433907],[433922,433893,433882],[433868,433857],[433856,433853,433818,433832],[433918,433827,433807],[433793,433782]] := ch 4096 k105
  have k107 : Upto 438272 [[438168,438257],[438243,438232],[438268,438207],[438218,438197,438182],[438193,438162,438157],[438202,438171,438147,438143,438132],[438128,438120,438068,438107],[438093,438086,438082],[438118,438057],[438018,438032],[438043,438007],[437993,437982],[437978,437918,437957],[437963,437943,437932],[437968,437907],[437949,437868,437882]] := ch 4096 k106
  have k108 : Upto 442368 [[442368,442357],[442343,442332],[442218,442307],[442304,442293,442282],[442325,442276,442268,442257],[442318,442232],[442243,442208,442207],[442193,442182],[442118,442157],[442143,442132],[442174,442168,442107],[442117,442068,442082],[442093,442057],[442203,442070,442043,442032],[442034,441968,442007],[442005,441993,441982]] := ch 4096 k107
  have k109 : Upto 446464 [[446457],[446418,446432],[446443,446428,446411,446407],[446393,446382],[446318,446357],[446343,446332],[446399,446368,446307],[446268,446282],[446293,446257],[446259,446243,446232],[446275,446230,446168,446207],[446254,446193,446182],[446218,446178,446177,446157],[446118,446132],[446143,446131,446107],[446093,446090,446082]] := ch 4096 k108
  have k110 : Upto 450560 [[450557],[450543,450532],[450518,450507],[450513,450368,450482],[450493,450457],[450455,450443,450432],[450484,450468,450407],[450393,450382],[450418,450357],[450293,450332],[450318,450315,450307],[450343,450282],[450284,450218,450257],[450300,450286,450243,450232],[450268,450224,450207],[450168,450182]] := ch 4096 k109
  have k111 : Upto 454656 [[454644,454643,454632],[454635,454518,454607],[454593,454582],[454625,454568,454558,454557],[454618,454559,454540,454532],[454543,454511,454507],[454493,454482],[454418,454457],[454443,454432],[454468,454407],[454368,454391,454382],[454393,454357],[454371,454346,454343,454342,454332],[454268,454316,454307],[454293,454282],[454321,454318,454257]] := ch 4096 k110
  have k112 : Upto 458752 [[458718,458736,458732],[458743,458707],[458693,458682],[458681,458618,458657],[458643,458632],[458668,458607],[458605,458596,458568,458582],[458593,458557],[458567,458543,458535,458532],[458530,458418,458507],[458493,458482],[458498,458468,458457],[458518,458432],[458443,458427,458407],[458398,458393,458392,458382],[458268,458365,458357]] := ch 4096 k111
  have k113 : Upto 462848 [[462847,462843,462832],[462839,462818,462807],[462821,462768,462792,462782],[462793,462757],[462743,462732],[462668,462707],[462693,462682],[462718,462657],[462727,462651,462618,462632],[462643,462612,462607],[462653,462605,462593,462582],[462652,462518,462557],[462623,462591,462543,462532],[462568,462507],[462443,462483,462482],[462468,462457]] := ch 4096 k112
  have k114 : Upto 466944 [[466943,466940,466932],[466868,466907],[466893,466882],[466918,466877,466857],[466848,466818,466832],[466843,466807],[466794,466793,466782],[466796,466773,466668,466757],[466743,466732],[466718,466712,466708,466707],[466768,466714,466697,466682],[466693,466657],[466643,466632],[466679,466568,466607],[466593,466582],[466618,466557]] := ch 4096 k113
  have k115 : Upto 471040 [[471032],[471018,471007],[471001,470993,470982],[470918,470957],[470943,470932],[470968,470919,470907],[470904,470843,470882],[470933,470868,470857],[470893,470832],[470819,470768,470807],[470793,470782],[470818,470764,470757],[470718,470732],[470743,470735,470707],[470693,470682],[470618,470657]] := ch 4096 k114
  have k116 : Upto 475136 [[475132],[475124,475118,475107],[475068,475082],[475129,475093,475078,475057],[475043,475032],[474918,475007],[474993,474982],[474989,474968,474960,474957],[475018,474932],[474943,474926,474907],[474916,474893,474882],[474768,474865,474857],[474743,474832],[474818,474807],[474868,474789,474782],[474820,474793,474757]] := ch 4096 k115
  have k117 : Upto 479232 [[479232],[479168,479214,479207],[479200,479193,479185,479182],[479218,479157],[479118,479138,479132],[479143,479124,479107],[479121,479093,479082],[479018,479057],[479043,479032],[479068,479007],[479045,479033,479016,478968,478982],[478993,478957],[478943,478932],[478868,478911,478907],[478893,478882],[478918,478876,478857]] := ch 4096 k116
  have k118 : Upto 483328 [[483318,483307],[483293,483282],[483270,483218,483257],[483246,483243,483232],[483268,483207],[483241,483168,483182],[483193,483157],[483170,483143,483140,483132],[483068,483107],[483093,483082],[483118,483101,483072,483057],[483048,483018,483032],[483043,483007],[482993,482982],[482918,482957],[482943,482932]] := ch 4096 k117
  have k119 : Upto 487424 [[487418,487407],[487343,487382],[487368,487357],[487393,487332],[487326,487268,487307],[487293,487292,487282],[487318,487257],[487218,487241,487232],[487247,487243,487207],[487297,487216,487193,487182],[487068,487157],[487143,487132],[487118,487112,487107],[487128,487043,487082],[487168,487057],[487093,487042,487032]] := ch 4096 k118
  have k120 : Upto 491520 [[491468,491507],[491493,491482],[491518,491457],[491418,491432],[491443,491407],[491393,491382],[491318,491357],[491343,491338,491332],[491368,491354,491307],[491243,491282],[491353,491268,491262,491257],[491293,491232],[491230,491168,491207],[491213,491193,491185,491182],[491218,491184,491157],[491118,491132]] := ch 4096 k119
  have k121 : Upto 495616 [[495607],[495597,495593,495582],[495578,495518,495557],[495552,495543,495532],[495568,495507],[495517,495468,495482],[495493,495461,495457],[495575,495443,495438,495432],[495368,495407],[495409,495393,495390,495382],[495418,495384,495357],[495318,495332],[495343,495308,495307],[495293,495282],[495269,495218,495257],[495243,495240,495232]] := ch 4096 k120
  have k122 : Upto 499712 [[499707],[499701,499668,499682],[499693,499657],[499643,499635,499632],[499634,499568,499607],[499593,499582],[499618,499557],[499663,499595,499518,499532],[499543,499507],[499494,499493,499482],[499502,499368,499465,499457],[499443,499432],[499430,499418,499407],[499513,499468,499382],[499393,499357],[499343,499332]] := ch 4096 k121
  have k123 : Upto 503808 [[503807],[503800,503793,503782],[503768,503757],[503765,503718,503732],[503743,503719,503707],[503693,503689,503682],[503690,503618,503657],[503643,503632],[503668,503607],[503675,503568,503582],[503593,503557],[503550,503543,503532],[503468,503507],[503521,503493,503482],[503518,503457],[503476,503418,503432]] := ch 4096 k122
  have k124 : Upto 507904 [[507893,507882],[507818,507857],[507843,507832],[507868,507807],[507800,507768,507782],[507793,507757],[507746,507743,507735,507732],[507811,507775,507723,507668,507707],[507693,507682],[507718,507657],[507593,507632],[507618,507607],[507643,507606,507582],[507518,507557],[507543,507532],[507568,507522,507507]] := ch 4096 k123
  have k125 : Upto 512000 [[512000,511968,511982],[511993,511957],[511971,511943,511932],[511919,511743,511907],[511893,511882],[511889,511868,511857],[511918,511832],[511831,511818,511807],[511802,511793,511782],[511781,511718,511757],[511843,511738,511732],[511768,511707],[511668,511682],[511693,511662,511657],[511643,511632],[511568,511607]] := ch 4096 k124
  have k126 : Upto 516096 [[516093,516082],[516068,516057],[516056,516018,516032],[516043,516027,516007],[516006,515996,515993,515982],[515918,515957],[515943,515932],[515968,515907],[515868,515887,515882],[515893,515858,515857],[515903,515843,515832],[515768,515807],[515793,515782],[515818,515757],[515718,515732],[515827,515743,515707]] := ch 4096 k125
  have k127 : Upto 520192 [[520182],[520093,520165,520162,520157],[520164,520143,520132],[520118,520107],[520112,520068,520083,520082],[520168,520057],[520103,520043,520032],[519968,520007],[519993,519982],[520018,519957],[519949,519918,519932],[519943,519907],[519914,519893,519882],[519818,519857],[519843,519832],[519868,519807]] := ch 4096 k126
  have k128 : Upto 524288 [[524282],[524284,524268,524257],[524243,524232],[524168,524208,524207],[524210,524193,524182],[524218,524157],[524118,524139,524132],[524143,524107],[524094,524093,524082],[524018,524057],[524043,524032],[524068,524007],[523793,523982],[523984,523968,523957],[523995,523979,523970,523943,523932],[523768,523907]] := ch 4096 k127
  have k129 : Upto 528384 [[528382],[528368,528364,528357],[528347,528318,528332],[528343,528330,528307],[528293,528282],[528317,528168,528257],[528254,528243,528232],[528224,528218,528212,528207],[528268,528189,528182],[528193,528157],[528195,528143,528132],[528068,528107],[528093,528082],[528118,528057],[528018,528041,528032],[528043,528026,528007]] := ch 4096 k128
  have k130 : Upto 532480 [[532418,532457],[532443,532432],[532468,532424,532407],[532449,532394,532368,532382],[532393,532376,532357],[532420,532343,532332],[532218,532312,532307],[532300,532293,532282],[532280,532268,532257],[532318,532251,532232],[532243,532207],[532261,532193,532182],[532068,532157],[532168,532145,532132],[532124,532118,532107],[532143,532087,532082]] := ch 4096 k129
  have k131 : Upto 536576 [[536568,536557],[536543,536532],[536531,536468,536507],[536517,536506,536505,536493,536482],[536518,536476,536457],[536418,536432],[536443,536407],[536393,536382],[536318,536357],[536346,536343,536336,536332],[536422,536368,536307],[536268,536282],[536293,536257],[536243,536232],[536118,536207],[536193,536182]] := ch 4096 k130
  have k132 : Upto 540672 [[540668,540657],[540618,540638,540632],[540643,540607],[540593,540582],[540518,540561,540557],[540543,540532],[540568,540507],[540468,540482],[540493,540457],[540443,540432],[540318,540407],[540393,540392,540382],[540389,540368,540365,540357],[540418,540363,540332],[540343,540307],[540293,540282]] := ch 4096 k131
  have k133 : Upto 544768 [[544718,544757],[544743,544732],[544768,544727,544719,544707],[544745,544668,544682],[544693,544657],[544643,544632],[544568,544607],[544617,544593,544588,544582],[544618,544557],[544518,544532],[544543,544507],[544514,544493,544482],[544368,544457],[544446,544443,544438,544432],[544448,544419,544418,544407],[544343,544382]] := ch 4096 k132
  have k134 : Upto 548864 [[548857],[548852,548843,548842,548832],[548768,548807],[548849,548813,548793,548782],[548818,548773,548757],[548718,548732],[548743,548707],[548693,548682],[548673,548618,548657],[548644,548643,548632],[548668,548607],[548568,548582],[548593,548557],[548560,548543,548532],[548468,548507],[548493,548482]] := ch 4096 k133
  have k135 : Upto 552960 [[552957],[552959,552918,552932],[552943,552907],[552898,552893,552882],[552873,552869,552818,552857],[552843,552832],[552895,552868,552819,552807],[552768,552782],[552793,552757],[552743,552732],[552668,552707],[552729,552700,552693,552682],[552718,552657],[552671,552663,552618,552632],[552643,552607],[552606,552593,552582]] := ch 4096 k134
  have k136 : Upto 557056 [[557043,557032],[557018,557007],[556968,556982],[556993,556957],[556943,556932],[556868,556907],[556954,556941,556893,556882],[556918,556865,556857],[556925,556818,556832],[556843,556807],[556793,556782],[556785,556769,556668,556757],[556783,556756,556743,556732],[556768,556707],[556789,556718,556701,556682],[556693,556657]] := ch 4096 k135
  have k137 : Upto 561152 [[561150,561143,561132],[561068,561107],[561093,561082],[561118,561076,561057],[561018,561032],[561043,561010,561007],[560993,560988,560982],[560981,560918,560957],[560987,560943,560932],[560968,560907],[560906,560868,560882],[560893,560857],[560911,560843,560832],[560768,560812,560807],[560841,560793,560782],[560818,560757]] := ch 4096 k136
  have k138 : Upto 565248 [[565218,565235,565232],[565246,565243,565207],[565206,565194,565193,565182],[565118,565157],[565143,565132],[565168,565107],[565109,565068,565082],[565093,565057],[564918,565037,565033,565032],[565111,565066,564968,565007],[564993,564982],[565018,564957],[565043,564932],[564943,564907],[564910,564897,564893,564882],[564818,564857]] := ch 4096 k137
  have k139 : Upto 569344 [[569343,569332],[569318,569307],[569316,569268,569292,569291,569282],[569293,569262,569257],[569243,569232],[569118,569207],[569193,569182],[569093,569157],[569218,569132],[569143,569122,569107],[569168,569082],[568993,569057],[569083,569079,569043,569032],[569018,569007],[569003,568968,568982],[569068,568957]] := ch 4096 k138
  have k140 : Upto 573440 [[573432],[573368,573414,573407],[573393,573382],[573418,573357],[573347,573318,573338,573332],[573343,573307],[573218,573282],[573293,573257],[573243,573232],[573268,573207],[573168,573182],[573193,573178,573157],[573143,573132],[573068,573107],[573149,573093,573082],[573118,573057]] := ch 4096 k139
  have k141 : Upto 577536 [[577532],[577518,577507],[577493,577482],[577418,577460,577457],[577443,577432],[577468,577407],[577403,577368,577382],[577437,577393,577384,577374,577357],[577343,577332],[577268,577307],[577293,577282],[577318,577257],[577218,577232],[577243,577234,577207],[577205,577193,577182],[577118,577157]] := ch 4096 k140
  have k142 : Upto 581632 [[581632],[581618,581607],[581628,581599,581568,581582],[581593,581557],[581543,581532],[581468,581507],[581506,581493,581482],[581518,581457],[581418,581432],[581443,581430,581407],[581393,581382],[581318,581357],[581459,581343,581332],[581368,581307],[581243,581282],[581268,581261,581257]] := ch 4096 k141
  have k143 : Upto 585728 [[585668,585707],[585693,585682],[585718,585685,585684,585664,585657],[585655,585618,585632],[585643,585607],[585593,585582],[585518,585557],[585552,585543,585532],[585568,585515,585507],[585468,585486,585482],[585493,585476,585457],[585443,585432],[585368,585414,585407],[585393,585382],[585418,585377,585357],[585346,585318,585339,585332]] := ch 4096 k142
  have k144 : Upto 589824 [[589818,589811,589807],[589793,589782],[589718,589757],[589743,589740,589732],[589768,589707],[589668,589682],[589693,589657],[589711,589643,589632],[589543,589607],[589653,589593,589582],[589598,589568,589557],[589493,589542,589532],[589571,589522,589518,589507],[589618,589500,589482],[589418,589457],[589443,589432]] := ch 4096 k143
  have k145 : Upto 593920 [[593918,593907],[593768,593882],[593893,593857],[593843,593832],[593868,593807],[593796,593793,593782],[593818,593757],[593787,593771,593767,593718,593732],[593743,593707],[593720,593705,593693,593682],[593618,593657],[593644,593643,593632],[593668,593627,593607],[593598,593568,593582],[593593,593557],[593543,593532]] := ch 4096 k144
  have k146 : Upto 598016 [[598007],[597993,597992,597982],[597968,597957],[597945,597918,597936,597932],[597943,597910,597907],[597893,597882],[597818,597857],[597979,597903,597852,597843,597832],[597868,597823,597807],[597817,597768,597782],[597793,597757],[597743,597732],[597668,597707],[597693,597690,597682],[597718,597657],[597683,597654,597543,597632]] := ch 4096 k145
  have k147 : Upto 602112 [[602107],[602093,602082],[601968,602057],[602043,602032],[602048,602018,602007],[602077,602068,602025,601982],[601993,601957],[601943,601932],[601868,601908,601907],[601949,601893,601882],[601918,601857],[601853,601818,601832],[601879,601843,601807],[601793,601782],[601668,601757],[601743,601736,601732]] := ch 4096 k146
  have k148 : Upto 606208 [[606207],[606168,606182],[606193,606157],[606143,606132],[606068,606107],[606104,606093,606082],[606133,606118,606057],[606071,606056,606018,606032],[606043,606007],[605993,605982],[605918,605964,605957],[605995,605943,605935,605932],[605968,605907],[605868,605882],[605893,605857],[605843,605832]] := ch 4096 k147
  have k149 : Upto 610304 [[610293,610282],[610268,610257],[610218,610232],[610243,610207],[610193,610189,610182],[610118,610160,610157],[610143,610132],[610168,610107],[610117,610068,610082],[610093,610057],[610043,610032],[610020,609968,610007],[610053,610041,609993,609982],[610018,609957],[609991,609918,609932],[609943,609907]] := ch 4096 k148
  have k150 : Upto 614400 [[614393,614385,614382],[614376,614268,614357],[614343,614332],[614318,614307],[614368,614282],[614293,614257],[614243,614232],[614168,614216,614207],[614245,614193,614182],[614218,614157],[614163,614118,614132],[614143,614107],[614093,614082],[614076,614018,614057],[614087,614047,614043,614032],[614068,614007]] := ch 4096 k149
  have k151 : Upto 618496 [[618468,618482],[618493,618480,618457],[618470,618443,618432],[618422,618368,618407],[618441,618393,618382],[618418,618357],[618318,618332],[618343,618307],[618301,618293,618282],[618168,618257],[618272,618243,618232],[618230,618218,618207],[618268,618182],[618193,618176,618157],[618143,618132],[618068,618107]] := ch 4096 k150
  have k152 : Upto 622592 [[622582],[622568,622557],[622544,622518,622532],[622543,622526,622507],[622493,622482],[622497,622368,622457],[622443,622432],[622418,622407],[622468,622382],[622393,622381,622357],[622348,622343,622332],[622328,622268,622307],[622337,622293,622282],[622318,622257],[622299,622255,622218,622232],[622243,622207]] := ch 4096 k151
  have k153 : Upto 626688 [[626682],[626593,626657],[626643,626635,626632],[626618,626607],[626568,626590,626586,626582],[626668,626557],[626543,626532],[626468,626514,626507],[626553,626504,626493,626482],[626518,626457],[626418,626432],[626443,626407],[626393,626382],[626384,626318,626357],[626351,626343,626332],[626368,626307]] := ch 4096 k152
  have k154 : Upto 630784 [[630782],[630778,630768,630757],[630743,630732],[630668,630707],[630753,630709,630693,630682],[630718,630657],[630618,630636,630632],[630643,630638,630607],[630609,630593,630582],[630518,630560,630557],[630543,630532],[630568,630507],[630468,630482],[630493,630469,630457],[630443,630440,630432],[630368,630407]] := ch 4096 k153
  have k155 : Upto 634880 [[634868,634857],[634863,634818,634832],[634843,634834,634807],[634793,634782],[634718,634757],[634743,634732],[634768,634707],[634694,634668,634682],[634693,634665,634657],[634643,634632],[634568,634607],[634606,634593,634582],[634618,634557],[634518,634532],[634543,634507],[634496,634493,634482]] := ch 4096 k154
  have k156 : Upto 638976 [[638918,638957],[638943,638932],[638968,638923,638919,638907],[638941,638868,638890,638882],[638893,638857],[638843,638832],[638768,638807],[638793,638782],[638818,638757],[638750,638718,638732],[638743,638728,638707],[638721,638693,638682],[638618,638657],[638704,638643,638632],[638668,638652,638607],[638568,638582]] := ch 4096 k155
  have k157 : Upto 643072 [[643068,643057],[643051,643043,643032],[642968,643007],[642993,642982],[643018,642957],[643063,642975,642946,642918,642932],[642987,642943,642907],[642893,642882],[642818,642857],[642843,642832],[642868,642807],[642806,642768,642782],[642793,642777,642774,642761,642757],[642743,642732],[642618,642707],[642693,642682]] := ch 4096 k156
  have k158 : Upto 647168 [[647168,647157],[647118,647132],[647143,647107],[647109,647093,647082],[647018,647057],[647043,647032],[647068,647031,647007],[647033,646968,646982],[647002,646993,646957],[646943,646932],[646818,646907],[646893,646882],[646868,646862,646857],[646918,646833,646832],[646843,646807],[646820,646793,646782]] := ch 4096 k157
  have k159 : Upto 651264 [[651257],[651243,651232],[651227,651218,651207],[651168,651188,651182],[651256,651193,651157],[651155,651143,651132],[651068,651107],[651093,651082],[651118,651058,651057],[651087,651018,651032],[651079,651043,651007],[650993,650982],[650918,650957],[650943,650932],[650968,650914,650907],[650925,650868,650882]] := ch 4096 k158
  have k160 : Upto 655360 [[655357],[655343,655332],[655268,655312,655307],[655293,655282],[655318,655257],[655283,655218,655232],[655243,655212,655207],[655201,655193,655182],[655180,655118,655157],[655143,655132],[655168,655114,655107],[655125,655098,655068,655082],[655093,655057],[655043,655032],[654918,655007],[654997,654993,654982]] := ch 4096 k159
  have k161 : Upto 659456 [[659418,659432],[659443,659407],[659393,659385,659382],[659293,659357],[659343,659332],[659339,659330,659318,659307],[659303,659299,659268,659282],[659368,659257],[659247,659243,659232],[659168,659207],[659193,659182],[659218,659200,659157],[659199,659171,659118,659132],[659170,659143,659107],[659093,659082],[658993,659057]] := ch 4096 k160
  have k162 : Upto 663552 [[663543,663532],[663518,663508,663507],[663528,663506,663443,663482],[663468,663457],[663493,663432],[663368,663407],[663424,663393,663382],[663418,663357],[663395,663318,663332],[663343,663307],[663293,663282],[663218,663257],[663255,663243,663232],[663268,663226,663207],[663217,663168,663182],[663193,663157]] := ch 4096 k161
  have k163 : Upto 667648 [[667643,667632],[667628,667620,667568,667607],[667593,667582],[667618,667557],[667518,667532],[667552,667543,667507],[667493,667482],[667480,667418,667457],[667451,667443,667432],[667468,667407],[667368,667382],[667393,667357],[667343,667339,667332],[667355,667268,667311,667307],[667293,667282],[667318,667257]] := ch 4096 k162
  have k164 : Upto 671744 [[671718,671732],[671743,671707],[671705,671693,671682],[671676,671618,671657],[671679,671674,671643,671632],[671668,671607],[671598,671568,671582],[671593,671557],[671543,671532],[671468,671507],[671536,671493,671482],[671518,671473,671457],[671418,671432],[671443,671407],[671393,671382],[671385,671293,671357]] := ch 4096 k163
  have k165 : Upto 675840 [[675832],[675818,675807],[675768,675782],[675793,675761,675757],[675618,675732],[675720,675668,675707],[675693,675682],[675718,675657],[675743,675644,675632],[675643,675607],[675593,675592,675582],[675581,675518,675557],[675563,675543,675532],[675568,675507],[675468,675482],[675493,675457]] := ch 4096 k164
  have k166 : Upto 679936 [[679932],[679868,679907],[679893,679882],[679918,679857],[679818,679832],[679843,679807],[679793,679788,679782],[679693,679766,679757],[679743,679732],[679718,679707],[679668,679690,679682],[679768,679657],[679648,679643,679632],[679619,679568,679607],[679817,679593,679582],[679618,679569,679557]] := ch 4096 k165
  have k167 : Upto 684032 [[684032],[684018,684007],[684025,683993,683982],[683918,683957],[683943,683932],[683968,683907],[683768,683882],[684013,683893,683857],[683844,683843,683832],[683868,683812,683807],[683873,683793,683782],[683789,683774,683718,683757],[683818,683736,683732],[683743,683707],[683693,683692,683682],[683618,683657]] := ch 4096 k166
  have k168 : Upto 688128 [[688118,688107],[688098,688068,688082],[688093,688069,688057],[688071,688043,688032],[687968,688007],[687993,687982],[688018,687957],[687918,687932],[687979,687943,687907],[687929,687897,687893,687882],[687900,687818,687858,687857],[687843,687840,687832],[687868,687807],[687816,687768,687782],[687793,687760,687757],[687743,687732]] := ch 4096 k167
  have k169 : Upto 692224 [[692118,692214,692207],[692194,692193,692182],[692184,692168,692157],[692218,692154,692132],[692143,692107],[692125,692117,692102,692093,692082],[692018,692057],[692043,692032],[692068,692007],[691994,691968,691985,691982],[691993,691957],[691956,691943,691932],[691868,691907],[691893,691882],[691918,691904,691857],[691818,691832]] := ch 4096 k168
  have k170 : Upto 696320 [[696318,696312,696307],[696293,696282],[696168,696257],[696243,696232],[696239,696218,696210,696207],[696268,696182],[696193,696181,696157],[696143,696132],[696068,696107],[696093,696082],[696118,696057],[696018,696041,696032],[696163,696043,696012,696007],[695993,695982],[695918,695957],[695950,695943,695932]] := ch 4096 k169
  have k171 : Upto 700416 [[700407],[700368,700382],[700406,700393,700357],[700343,700332],[700268,700307],[700293,700285,700282],[700318,700257],[700266,700168,700237,700232],[700230,700218,700207],[700209,700193,700182],[700118,700157],[700143,700132],[700243,700107],[700097,700068,700082],[700093,700057],[700043,700032]] := ch 4096 k170
  have k172 : Upto 704512 [[704507],[704493,704482],[704468,704462,704457],[704491,704418,704432],[704443,704407],[704393,704382],[704318,704357],[704343,704332],[704368,704331,704322,704307],[704384,704268,704282],[704293,704257],[704255,704243,704232],[704168,704207],[704204,704193,704182],[704218,704157],[704153,704118,704132]] := ch 4096 k171
  have k173 : Upto 708608 [[708607],[708593,708590,708582],[708518,708557],[708547,708543,708532],[708568,708507],[708468,708482],[708493,708457],[708443,708432],[708368,708407],[708393,708382],[708418,708378,708377,708357],[708243,708332],[708318,708307],[708301,708293,708282],[708218,708257],[708343,708232]] := ch 4096 k172
  have k174 : Upto 712704 [[712668,712682],[712693,712657],[712643,712632],[712568,712607],[712636,712593,712582],[712618,712574,712557],[712603,712566,712518,712532],[712543,712507],[712493,712482],[712418,712457],[712443,712432],[712468,712434,712423,712407],[712405,712368,712382],[712393,712357],[712366,712347,712343,712335,712332],[712268,712307]] := ch 4096 k173
  have k175 : Upto 716800 [[716793,716782],[716768,716758,716757],[716795,716751,716718,716732],[716799,716774,716743,716707],[716693,716682],[716568,716657],[716659,716643,716632],[716630,716618,716607],[716543,716582],[716668,716557],[716593,716532],[716468,716507],[716573,716493,716482],[716518,716490,716484,716469,716457],[716491,716418,716432],[716443,716407]] := ch 4096 k174
  have k176 : Upto 720896 [[720893,720882],[720884,720693,720857],[720855,720843,720832],[720818,720807],[720868,720804,720782],[720778,720768,720757],[720771,720743,720732],[720728,720668,720707],[720793,720686,720682],[720718,720696,720657],[720618,720632],[720715,720643,720607],[720593,720582],[720518,720557],[720546,720543,720532],[720568,720515,720507]] := ch 4096 k175
  have k177 : Upto 724992 [[724983,724982],[724968,724957],[724943,724940,724932],[724843,724911,724907],[724913,724901,724893,724882],[724889,724868,724857],[724871,724850,724818,724832],[724918,724807],[724793,724782],[724718,724757],[724786,724743,724742,724732],[724774,724771,724768,724707],[724668,724682],[724693,724672,724657],[724643,724632],[724568,724607]] := ch 4096 k176
  have k178 : Upto 729088 [[729082],[729068,729057],[729018,729032],[729043,729007],[728996,728993,728982],[728918,728957],[728967,728943,728932],[728968,728907],[728896,728868,728882],[728893,728857],[728843,728832],[728820,728718,728807],[728793,728782],[728798,728768,728757],[728827,728818,728732],[728743,728707]] := ch 4096 k177
  have k179 : Upto 733184 [[733182],[733118,733162,733157],[733155,733143,733132],[733168,733107],[733068,733082],[733093,733057],[733052,733043,733032],[732968,733007],[732993,732982],[733018,732957],[732893,732942,732932],[733023,732918,732907],[732943,732882],[732818,732866,732857],[732854,732843,732832],[732883,732868,732807]] := ch 4096 k178
  have k180 : Upto 737280 [[737277,737268,737257],[737248,737247,737243,737232],[737168,737207],[737193,737182],[737218,737201,737157],[737093,737132],[737118,737108,737107],[737143,737082],[737018,737057],[737079,737043,737032],[737068,737007],[736893,736988,736982],[736968,736957],[736943,736939,736932],[736868,736910,736907],[736993,736912,736882]] := ch 4096 k179
  have k181 : Upto 741376 [[741368,741357],[741318,741333,741332],[741343,741307],[741293,741282],[741218,741257],[741304,741247,741243,741232],[741323,741268,741207],[741168,741182],[741193,741161,741157],[741164,741143,741135,741132],[741068,741107],[741093,741082],[741118,741076,741057],[741018,741032],[741043,741034,741007],[740993,740982]] := ch 4096 k180
  have k182 : Upto 745472 [[745418,745457],[745443,745432],[745468,745407],[745368,745389,745382],[745393,745369,745360,745357],[745343,745332],[745268,745307],[745293,745282],[745318,745284,745257],[745218,745232],[745243,745207],[745220,745193,745188,745182],[745118,745157],[745191,745143,745132],[745168,745167,745107],[745068,745085,745082]] := ch 4096 k181
  have k183 : Upto 749568 [[749568,749557],[749543,749532],[749468,749507],[749493,749482],[749518,749457],[749445,749418,749432],[749443,749415,749407],[749416,749393,749382],[749372,749268,749357],[749343,749332],[749348,749339,749318,749307],[749503,749368,749290,749282],[749293,749276,749257],[749247,749243,749232],[749168,749207],[749193,749182]] := ch 4096 k182
  have k184 : Upto 753664 [[753657],[753618,753641,753632],[753643,753607],[753593,753582],[753518,753557],[753543,753532],[753568,753507],[753495,753468,753482],[753577,753501,753493,753461,753457],[753466,753443,753432],[753318,753407],[753472,753393,753385,753382],[753368,753357],[753418,753332],[753343,753312,753307],[753293,753282]] := ch 4096 k183
  have k185 : Upto 757760 [[757757],[757743,757732],[757718,757707],[757753,757726,757700,757668,757682],[757720,757697,757693,757657],[757643,757632],[757568,757607],[757593,757582],[757618,757557],[757493,757532],[757528,757518,757507],[757543,757494,757482],[757418,757457],[757443,757432],[757468,757431,757407],[757368,757388,757382]] := ch 4096 k184
  have k186 : Upto 761856 [[761843,761842,761832],[761768,761807],[761793,761782],[761818,761757],[761718,761739,761732],[761766,761743,761707],[761753,761693,761682],[761618,761657],[761643,761632],[761668,761607],[761613,761568,761582],[761593,761584,761557],[761543,761532],[761468,761507],[761553,761493,761482],[761518,761477,761457]] := ch 4096 k185
  have k187 : Upto 765952 [[765918,765932],[765943,765907],[765893,765888,765882],[765768,765857],[765843,765838,765832],[765844,765818,765812,765807],[765868,765782],[765793,765757],[765743,765732],[765668,765707],[765809,765693,765682],[765718,765669,765657],[765543,765640,765632],[765618,765607],[765593,765590,765582],[765518,765557]] := ch 4096 k186
  have k188 : Upto 770048 [[770043,770032],[770034,770018,770007],[769968,769982],[770005,769993,769957],[769943,769932],[769934,769868,769907],[769894,769893,769882],[769918,769865,769857],[769858,769818,769832],[769843,769807],[769793,769782],[769718,769757],[769743,769732],[769768,769707],[769725,769696,769668,769682],[769693,769657]] := ch 4096 k187
  have k189 : Upto 774144 [[774143,774132],[774068,774107],[774093,774090,774082],[774118,774057],[774119,774018,774032],[774043,774007],[773993,773982],[773980,773918,773957],[773950,773943,773932],[773968,773907],[773921,773868,773882],[773904,773893,773857],[773843,773832],[773768,773807],[773793,773782],[773818,773781,773757]] := ch 4096 k188
  have k190 : Upto 778240 [[778239,778232],[778218,778207],[778193,778182],[778118,778157],[778146,778143,778132],[778168,778107],[778175,778068,778082],[778093,778057],[778043,778032],[778026,777968,778007],[778009,778006,777993,777982],[778018,777977,777957],[777966,777950,777918,777932],[777943,777907],[777925,777893,777882],[777884,777818,777857]] := ch 4096 k189
  have k191 : Upto 782336 [[782332],[782334,782318,782307],[782268,782285,782282],[782293,782257],[782243,782232],[782275,782231,782168,782207],[782202,782193,782182],[782218,782157],[782171,782118,782132],[782143,782107],[782093,782092,782089,782082],[782072,782018,782062,782057],[781893,782033,782032],[782068,782007],[781996,781968,781982],[781993,781957]] := ch 4096 k190
  have k192 : Upto 786432 [[786432],[786368,786407],[786393,786382],[786418,786376,786357],[786427,786318,786332],[786343,786331,786330,786307],[786294,786293,786282],[786193,786258,786257],[786304,786287,786243,786232],[786218,786207],[786168,786182],[786268,786157],[786143,786132],[786018,786107],[786093,786082],[786089,786068,786057]] := ch 4096 k191
  have k193 : Upto 790528 [[790518,790512,790507],[790516,790493,790482],[790368,790457],[790499,790443,790432],[790448,790418,790407],[790468,790453,790382],[790393,790377,790357],[790483,790343,790332],[790268,790314,790307],[790293,790282],[790318,790257],[790283,790218,790232],[790243,790207],[790193,790182],[790118,790164,790157],[790143,790132]] := ch 4096 k192
  have k194 : Upto 794624 [[794618,794607],[794568,794582],[794593,794557],[794543,794539,794532],[794468,794507],[794493,794482],[794518,794457],[794499,794418,794432],[794447,794443,794408,794407],[794393,794382],[794268,794357],[794423,794399,794370,794343,794332],[794318,794307],[794243,794282],[794368,794257],[794293,794232]] := ch 4096 k193
  have k195 : Upto 798720 [[798668,798707],[798693,798682],[798718,798657],[798651,798618,798632],[798643,798624,798607],[798593,798582],[798518,798557],[798595,798574,798543,798532],[798568,798507],[798545,798468,798482],[798493,798469,798457],[798455,798443,798432],[798426,798368,798407],[798393,798382],[798418,798357],[798318,798332]] := ch 4096 k194
  have k196 : Upto 802816 [[802807],[802793,802782],[802718,802757],[802804,802743,802732],[802768,802707],[802737,802593,802682],[802680,802668,802657],[802651,802643,802632],[802568,802607],[802693,802582],[802618,802557],[802591,802518,802532],[802543,802515,802511,802507],[802493,802482],[802418,802457],[802443,802432]] := ch 4096 k195
  have k197 : Upto 806912 [[806907],[806905,806868,806882],[806893,806876,806857],[806850,806843,806832],[806768,806807],[806793,806782],[806818,806757],[806718,806732],[806775,806743,806736,806707],[806568,806683,806682],[806693,806657],[806643,806632],[806618,806607],[806668,806637,806582],[806593,806560,806557],[806567,806543,806538,806532]] := ch 4096 k196
  have k198 : Upto 811008 [[811007],[810968,810982],[810993,810957],[810972,810918,810932],[810943,810907],[810896,810893,810882],[810961,810818,810857],[810843,810832],[810868,810807],[810768,810792,810782],[810793,810784,810765,810757],[810743,810732],[810668,810707],[810693,810682],[810718,810657],[810763,810683,810618,810632]] := ch 4096 k197
  have k199 : Upto 815104 [[815093,815082],[814968,815057],[815043,815032],[815018,815007],[815068,814988,814982],[815017,814993,814957],[814943,814932],[814970,814868,814907],[814942,814893,814888,814882],[814918,814857],[814848,814818,814832],[814843,814819,814807],[814793,814782],[814718,814757],[814743,814732],[814768,814707]] := ch 4096 k198
  have k200 : Upto 819200 [[819168,819182],[819193,819157],[819175,819143,819132],[819068,819107],[819093,819082],[819118,819073,819057],[819044,819018,819032],[819064,819043,819007],[819025,818993,818988,818982],[818918,818957],[818968,818932],[818943,818926,818907],[818904,818868,818882],[818893,818857],[818875,818843,818832],[818768,818807]] := ch 4096 k199
  have k201 : Upto 823296 [[823293,823282],[823269,823268,823257],[823218,823232],[823243,823207],[823193,823182],[823181,823118,823157],[823143,823132],[823168,823110,823107],[823100,823068,823082],[823129,823093,823057],[823043,823032],[823023,822968,823007],[822993,822982],[823018,822960,822957],[823034,822918,822932],[822943,822931,822907]] := ch 4096 k200
  have k202 : Upto 827392 [[827382],[827369,827318,827357],[827354,827343,827332],[827368,827307],[827325,827268,827282],[827293,827257],[827243,827232],[827168,827207],[827193,827185,827182],[827218,827157],[827156,827118,827132],[827143,827107],[827093,827082],[827080,827018,827057],[827043,827032],[827068,827007]] := ch 4096 k201
  have k203 : Upto 831488 [[831482],[831468,831457],[831443,831432],[831318,831415,831410,831407],[831393,831382],[831381,831368,831357],[831418,831332],[831343,831307],[831293,831282],[831168,831257],[831243,831232],[831218,831212,831207],[831268,831241,831182],[831202,831193,831157],[831143,831132],[831126,831068,831107]] := ch 4096 k202
  have k204 : Upto 835584 [[835582],[835568,835557],[835518,835537,835532],[835566,835543,835507],[835493,835482],[835418,835466,835461,835457],[835443,835432],[835468,835407],[835343,835382],[835368,835357],[835437,835393,835332],[835268,835307],[835297,835293,835282],[835318,835257],[835248,835218,835232],[835243,835207]] := ch 4096 k203
  have k205 : Upto 839680 [[839618,839662,839657],[839643,839632],[839668,839607],[839568,839583,839582],[839617,839593,839557],[839543,839532],[839468,839507],[839522,839493,839482],[839518,839457],[839418,839432],[839443,839407],[839393,839382],[839318,839357],[839391,839359,839343,839332],[839368,839324,839314,839307],[839353,839294,839268,839282]] := ch 4096 k204
  have k206 : Upto 843776 [[843768,843757],[843747,843743,843732],[843668,843707],[843693,843686,843682],[843718,843657],[843543,843632],[843618,843607],[843629,843593,843582],[843578,843518,843564,843557],[843643,843532],[843568,843507],[843468,843487,843482],[843553,843549,843493,843484,843457],[843443,843432],[843318,843407],[843421,843409,843393,843382]] := ch 4096 k205
  have k207 : Upto 847872 [[847868,847857],[847793,847832],[847818,847807],[847843,847782],[847718,847757],[847803,847774,847743,847732],[847768,847707],[847618,847687,847682],[847769,847706,847568,847657],[847675,847643,847632],[847668,847634,847607],[847605,847593,847582],[847693,847602,847557],[847599,847518,847532],[847543,847528,847507],[847493,847482]] := ch 4096 k206
  have k208 : Upto 851968 [[851918,851957],[851943,851932],[851968,851934,851907],[851868,851892,851889,851882],[851893,851857],[851864,851859,851843,851832],[851830,851768,851807],[851793,851782],[851818,851757],[851718,851732],[851743,851707],[851721,851697,851693,851690,851682],[851618,851661,851657],[851643,851635,851632],[851668,851628,851627,851607],[851645,851568,851582]] := ch 4096 k207
  have k209 : Upto 856064 [[856057],[856056,856055,856043,856032],[855918,856007],[855993,855982],[855980,855968,855957],[856018,855932],[855943,855915,855907],[855893,855882],[855818,855857],[855886,855843,855832],[855868,855807],[855768,855782],[855793,855757],[855746,855643,855742,855732],[855668,855707],[855717,855693,855682]] := ch 4096 k208
  have k210 : Upto 860160 [[860157],[860118,860140,860132],[860143,860111,860107],[860102,860093,860082],[860018,860057],[860054,860043,860032],[860068,860026,860007],[859968,859982],[859993,859957],[859971,859943,859942,859932],[859868,859907],[859893,859882],[859918,859857],[859849,859818,859832],[859843,859807],[859802,859793,859782]] := ch 4096 k209
  have k211 : Upto 864256 [[864243,864232],[864218,864207],[864196,864168,864182],[864193,864180,864157],[864167,864148,864143,864132],[864128,864068,864107],[864093,864082],[864118,864072,864057],[864095,864074,864018,864032],[864043,864027,864007],[863998,863993,863982],[863918,863957],[863954,863943,863932],[863968,863907],[863868,863882],[863956,863893,863858,863857]] := ch 4096 k210
  have k212 : Upto 868352 [[868343,868332],[868268,868307],[868293,868282],[868318,868257],[868218,868232],[868252,868243,868207],[868194,868193,868182],[868118,868157],[868223,868143,868132],[868168,868107],[868068,868083,868082],[868093,868057],[868043,868032],[867968,868007],[868054,867993,867982],[868018,867957]] := ch 4096 k211
  have k213 : Upto 872448 [[872448,872418,872432],[872443,872407],[872393,872382],[872318,872357],[872343,872332],[872368,872308,872307],[872268,872282],[872293,872257],[872279,872243,872240,872232],[872168,872207],[872193,872182],[872218,872164,872158,872157],[872018,872139,872132],[872118,872110,872107],[872170,872143,872082],[872093,872076,872061,872057]] := ch 4096 k212
  have k214 : Upto 876544 [[876543,876532],[876518,876507],[876533,876504,876468,876482],[876493,876457],[876443,876432],[876368,876407],[876393,876382],[876418,876364,876357],[876363,876318,876335,876332],[876499,876346,876343,876307],[876293,876282],[876281,876218,876257],[876286,876243,876232],[876268,876210,876207],[876195,876168,876182],[876277,876193,876157]] := ch 4096 k213
  have k215 : Upto 880640 [[880632],[880518,880607],[880621,880593,880582],[880589,880568,880560,880557],[880618,880545,880532],[880543,880507],[880493,880482],[880418,880466,880457],[880486,880443,880432],[880468,880407],[880394,880368,880391,880382],[880420,880393,880384,880357],[880343,880332],[880268,880307],[880293,880282],[880318,880257]] := ch 4096 k214
  have k216 : Upto 884736 [[884732],[884718,884707],[884693,884682],[884568,884657],[884691,884667,884643,884632],[884668,884616,884607],[884618,884591,884582],[884629,884593,884584,884557],[884543,884532],[884468,884507],[884645,884493,884482],[884518,884476,884457],[884491,884447,884418,884432],[884443,884407],[884393,884382],[884378,884318,884357]] := ch 4096 k215
  have k217 : Upto 888832 [[888832],[888818,888807],[888768,888782],[888793,888757],[888756,888743,888732],[888668,888707],[888713,888701,888693,888682],[888718,888672,888657],[888618,888637,888632],[888643,888607],[888598,888593,888582],[888518,888557],[888543,888532],[888568,888507],[888503,888498,888468,888482],[888493,888457]] := ch 4096 k216
  have k218 : Upto 892928 [[892926,892868,892907],[892897,892893,892882],[892918,892857],[892818,892832],[892843,892807],[892793,892782],[892718,892762,892757],[892759,892743,892732],[892768,892728,892707],[892668,892683,892682],[892705,892693,892657],[892643,892632],[892568,892607],[892593,892588,892582],[892618,892557],[892559,892518,892532]] := ch 4096 k217
  have k219 : Upto 897024 [[897018,897007],[896993,896982],[896868,896957],[896943,896932],[896918,896907],[896968,896953,896882],[896893,896857],[896843,896832],[896768,896812,896807],[896813,896805,896793,896782],[896818,896784,896757],[896819,896718,896732],[896743,896707],[896729,896693,896682],[896618,896657],[896644,896643,896632]] := ch 4096 k218
  have k220 : Upto 901120 [[901118,901107],[901068,901082],[901093,901057],[901064,901043,901038,901032],[900968,901007],[901009,900993,900982],[901018,900957],[900995,900918,900932],[900943,900919,900907],[900893,900882],[900869,900818,900857],[900851,900843,900840,900832],[900868,900807],[900768,900782],[900793,900757],[900752,900743,900732]] := ch 4096 k219
  have k221 : Upto 905216 [[905207],[905193,905182],[905186,905168,905157],[905154,905118,905132],[905143,905110,905107],[905094,905093,905082],[904968,905065,905057],[905043,905032],[905018,905007],[905068,905026,904998,904982],[904993,904957],[904943,904932],[904743,904907],[904897,904896,904893,904885,904882],[904925,904889,904868,904857],[904918,904875,904832]] := ch 4096 k220
  have k222 : Upto 909312 [[909307],[909293,909290,909282],[909218,909257],[909243,909232],[909268,909207],[909168,909182],[909193,909162,909157],[909156,909150,909143,909132],[909018,909111,909107],[909121,909093,909082],[909080,909068,909057],[909118,909032],[909043,909007],[909133,908993,908982],[908981,908918,908957],[908952,908943,908932]] := ch 4096 k221
  have k223 : Upto 913408 [[913407],[913293,913382],[913368,913357],[913375,913367,913343,913332],[913346,913268,913307],[913393,913285,913282],[913318,913278,913257],[913218,913240,913232],[913243,913207],[913206,913202,913193,913182],[913118,913161,913157],[913163,913143,913132],[913168,913107],[913043,913082],[913177,913068,913057],[913093,913032]] := ch 4096 k222
  have k224 : Upto 917504 [[917493,917490,917482],[917468,917457],[917448,917418,917432],[917443,917431,917407],[917402,917393,917382],[917318,917364,917357],[917347,917343,917332],[917368,917324,917307],[917268,917285,917282],[917293,917262,917257],[917248,917243,917232],[917168,917207],[917233,917193,917182],[917218,917157],[917118,917132],[917143,917107]] := ch 4096 k223
  have k225 : Upto 921600 [[921593,921582],[921518,921566,921557],[921583,921543,921532],[921568,921507],[921468,921487,921482],[921493,921458,921457],[921443,921432],[921368,921407],[921454,921393,921382],[921418,921357],[921318,921332],[921370,921343,921307],[921294,921293,921289,921282],[921218,921257],[921243,921232],[921268,921207]] := ch 4096 k224
  have k226 : Upto 925696 [[925668,925683,925682],[925693,925657],[925644,925643,925632],[925568,925607],[925629,925593,925582],[925618,925557],[925518,925532],[925543,925507],[925514,925493,925485,925482],[925561,925418,925457],[925443,925432],[925468,925407],[925416,925368,925382],[925393,925374,925357],[925343,925340,925332],[925268,925307]] := ch 4096 k225
  have k227 : Upto 929792 [[929782],[929768,929757],[929751,929718,929739,929732],[929743,929707],[929693,929682],[929618,929657],[929643,929632],[929668,929607],[929675,929543,929582],[929568,929557],[929593,929570,929532],[929343,929507],[929493,929482],[929468,929462,929457],[929599,929518,929432],[929430,929418,929407]] := ch 4096 k226
  have k228 : Upto 933888 [[933882],[933818,933857],[933843,933832],[933868,933824,933807],[933797,933768,933782],[933793,933757],[933795,933775,933743,933732],[933847,933668,933707],[933721,933693,933682],[933718,933657],[933655,933618,933632],[933643,933626,933607],[933593,933582],[933518,933557],[933551,933543,933532],[933568,933508,933507]] := ch 4096 k227
  have k229 : Upto 937984 [[937982],[937977,937968,937957],[937943,937932],[937818,937907],[937893,937882],[937880,937868,937857],[937918,937851,937832],[937843,937807],[937793,937782],[937668,937757],[937767,937756,937743,937732],[937768,937711,937707],[937718,937706,937682],[937693,937674,937657],[937648,937643,937632],[937620,937568,937607]] := ch 4096 k228
  have k230 : Upto 942080 [[942076,942068,942057],[942018,942032],[942043,942007],[941993,941989,941982],[941918,941961,941957],[941943,941936,941932],[941968,941907],[941921,941868,941889,941882],[941893,941857],[941879,941843,941832],[941768,941807],[941813,941793,941782],[941718,941757],[941818,941755,941738,941732],[941767,941743,941707],[941693,941682]] := ch 4096 k229
  have k231 : Upto 946176 [[946068,946161,946157],[946143,946132],[946166,946148,946118,946107],[946168,946133,946096,946082],[946093,946084,946057],[946043,946032],[945968,946007],[945993,945992,945982],[946018,945957],[945963,945918,945935,945932],[945943,945907],[946025,945893,945882],[945818,945862,945857],[945859,945843,945832],[945868,945823,945807],[945794,945768,945782]] := ch 4096 k230
  have k232 : Upto 950272 [[950268,950257],[950270,950243,950232],[950118,950207],[950217,950194,950193,950188,950182],[950093,950157],[950203,950168,950132],[950218,950107],[950143,950082],[950018,950057],[950043,950032],[950068,950019,950007],[950048,949968,949982],[949993,949981,949969,949957],[949943,949942,949932],[949868,949907],[949905,949893,949882]] := ch 4096 k231
  have k233 : Upto 954368 [[954368,954357],[954318,954332],[954343,954330,954307],[954361,954316,954310,954293,954282],[954273,954218,954257],[954244,954243,954240,954232],[954268,954207],[954168,954182],[954193,954157],[954143,954132],[954068,954107],[954104,954093,954082],[954118,954076,954057],[954018,954032],[954075,954043,954027,954007],[953993,953982]] := ch 4096 k232
  have k234 : Upto 958464 [[958457],[958444,958443,958432],[958368,958407],[958418,958417,958382],[958393,958369,958362,958357],[958379,958343,958332],[958218,958307],[958300,958293,958286,958282],[958329,958268,958257],[958318,958232],[958243,958207],[958193,958182],[958118,958160,958157],[958183,958143,958132],[958168,958131,958107],[958068,958082]] := ch 4096 k233
  have k235 : Upto 962560 [[962557],[962543,962532],[962468,962507],[962554,962501,962493,962482],[962524,962518,962457],[962525,962393,962432],[962418,962408,962407],[962443,962382],[962385,962318,962357],[962356,962343,962332],[962368,962307],[962268,962290,962282],[962302,962293,962257],[962243,962232],[962168,962216,962207],[962193,962182]] := ch 4096 k234
  have k236 : Upto 966656 [[966618,966632],[966643,966631,966610,966607],[966593,966582],[966581,966518,966557],[966543,966532],[966568,966507],[966468,966482],[966493,966457],[966443,966432],[966368,966412,966407],[966454,966441,966397,966393,966382],[966418,966378,966357],[966350,966318,966332],[966343,966307],[966293,966282],[966272,966218,966257]] := ch 4096 k235
  have k237 : Upto 970752 [[970743,970738,970732],[970718,970707],[970643,970682],[970713,970568,970666,970657],[970693,970632],[970668,970607],[970654,970637,970593,970582],[970618,970557],[970555,970518,970532],[970543,970507],[970497,970493,970482],[970500,970473,970418,970457],[970504,970499,970443,970432],[970468,970422,970407],[970424,970368,970382],[970393,970357]] := ch 4096 k236
  have k238 : Upto 974848 [[974843,974835,974832],[974718,974807],[974845,974793,974782],[974768,974760,974757],[974818,974732],[974743,974722,974707],[974693,974682],[974678,974568,974657],[974759,974643,974632],[974618,974607],[974668,974582],[974602,974593,974557],[974546,974543,974532],[974611,974468,974507],[974553,974524,974493,974482],[974518,974484,974457]] := ch 4096 k237
  have k239 : Upto 978944 [[978918,978932],[978943,978907],[978893,978882],[978881,978818,978857],[978883,978843,978832],[978868,978807],[978805,978768,978782],[978793,978781,978778,978757],[978743,978732],[978720,978668,978707],[978749,978693,978682],[978718,978657],[978618,978632],[978643,978607],[978609,978593,978592,978588,978582],[978580,978518,978557]] := ch 4096 k238
  have k240 : Upto 983040 [[983032],[983026,983018,983007],[983003,982968,982982],[982993,982974,982957],[982943,982932],[982868,982907],[982893,982882],[982918,982857],[982927,982851,982818,982832],[982843,982834,982807],[982805,982793,982782],[982825,982718,982757],[982743,982732],[982768,982707],[982668,982682],[982693,982665,982657]] := ch 4096 k239
  have k241 : Upto 986746 [[986718,986732],[986743,986707],[986721,986693,986692,986682],[986684,986568,986657],[986643,986632],[986618,986608,986607],[986668,986582],[986641,986593,986557],[986552,986543,986532],[986534,986523,986468,986507],[986493,986482],[986518,986457],[986459,986418,986432],[986452,986443,986407],[986393,986382],[986369,986318,986357]] := ch 3706 k240
  exact k241.2
end Erdos848.Greedy
lemma Erdos848.statement_small : ∀ N ≤ 986746, Erdos848.Statement N := Erdos848.Greedy.allSmall

theorem Erdos848.R3H1_candidate : ∀ N : ℕ, N ≤ 986746 → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25 :=
  fun N hN A hA hadm => Erdos848.statement_small N hN A hA hadm

theorem OMA.solution : OMA.R_Erdos848_erdos_848_R3.H1 := Erdos848.R3H1_candidate
