import OMAReductions.R_OeisA247824_conjecture_2_R2_H4_R1_H1_R1
import Mathlib

/-!
# A certified value of the prime-counting function at 94085731

The finite tables in this file are proved correct by
induction. A square-cutoff form of Legendre's recurrence and a Meissel
semiprime correction reduce the numerical calculation to checked rows.
The Meissel identity comes from Physbuzz's published reduction for A247824.
The Legendre recursion adapts Daniel Veljjanoski's Palomar proof as formalized
by rleshner in OeisA100475.conjecture (Apache-2.0).
Palomar source: https://github.com/veljjanoski/oeis100475-palomar/tree/0968200356e449a24a023264821d4ea966091cf0
Reference: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9315
-/

/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace WheelTableA94

def index (n : ℕ) : ℕ := 8*(n/30) + ((703383147439395582067753010374709520 : ℕ) >>> (4*(n%30)))%16

def number (i : ℕ) : ℕ := 30*(i/8) + ((1021784272097 : ℕ) >>> (5*(i%8)))%32

theorem shift_index (q r : ℕ) : index (30*q+r) = 8*q+index r := by
  unfold index
  rw [Nat.mul_add_div (by decide : 0<30),Nat.mul_add_mod]
  omega

theorem shift_number (q j : ℕ) : number (8*q+j) = 30*q+number j := by
  unfold number
  rw [Nat.mul_add_div (by decide : 0<8),Nat.mul_add_mod]
  omega

theorem wheel_step (n : ℕ) :
    (index (n+1) = index n ∧ (2 ∣ n+1 ∨ 3 ∣ n+1 ∨ 5 ∣ n+1)) ∨
    (index (n+1) = index n+1 ∧ number (index n) = n+1) := by
  have tab : ∀ r : Fin 30,
      (index (r.1+1) = index r.1 ∧ (2 ∣ r.1+1 ∨ 3 ∣ r.1+1 ∨ 5 ∣ r.1+1)) ∨
      (index (r.1+1) = index r.1+1 ∧ number (index r.1) = r.1+1) := by decide +kernel
  let q := n/30
  let r := n%30
  have split : n = 30*q+r := (Nat.div_add_mod n 30).symm
  have next : n+1 = 30*q+(r+1) := by omega
  rcases tab ⟨r,Nat.mod_lt _ (by decide)⟩ with ⟨eq,hd⟩ | ⟨eq,hn⟩
  · left
    constructor
    · rw [next,split,shift_index,shift_index,eq]
    · rw [next]
      rcases hd with h|h|h
      · exact Or.inl (dvd_add (dvd_mul_of_dvd_left (by decide : 2 ∣ 30) q) h)
      · exact Or.inr (Or.inl (dvd_add (dvd_mul_of_dvd_left (by decide : 3 ∣ 30) q) h))
      · exact Or.inr (Or.inr (dvd_add (dvd_mul_of_dvd_left (by decide : 5 ∣ 30) q) h))
  · change index (r+1) = index r+1 at eq
    change number (index r) = r+1 at hn
    right
    constructor
    · rw [next,split,shift_index,shift_index,eq]
      omega
    · rw [next,split,shift_index,shift_number,hn]

theorem skips_composite {n : ℕ} (large : 5 < n) (d : 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n) : ¬ n.Prime := by
  intro h
  rcases d with hd|hd|hd
  all_goals rcases (Nat.dvd_prime h).mp hd with e|e <;> omega

theorem index_bound {n b : ℕ} (h : n ≤ b) : index n < 8*(b/30+2) := by
  have t : ∀ r : Fin 30, ((703383147439395582067753010374709520 : ℕ) >>> (4*r.val))%16 ≤ 8 := by decide +kernel
  have a := t ⟨n%30,Nat.mod_lt _ (by decide)⟩
  change ((703383147439395582067753010374709520 : ℕ) >>> (4*(n%30)))%16 ≤ 8 at a
  have d : n/30 ≤ b/30 := Nat.div_le_div_right h
  unfold index
  omega


private def packet (i : ℕ) : ℕ := (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x3ab60e119d9b6d2b63403944308218d32405aae037a522434c0a262c7570360b01689d1784d8c180345ada9c22287ce24050328618302abcad593d2030c2770494d45aa5a8602f214089851b7e3556002d62e1568bf88056a0702b99c742f3ad40648d102a0c41e22a6502b962402838dea735ca89501190266f8246c44cbf10b43024b307a4c570c944ab2022f02cdcdb50238f12c0211c383dc8219f6264e01f44c58b42aa71c8b5a01d64d33f3243e88518d01b999eb813c26c73811019ea0e3266581d892d2017b87588f9265aefb720162468c83e5081a96540142ef17c19b7171582101224f8cbcc8b37ac18c010454bf11453a2b4cb800e13a13f666e944fd2e00c1f8a154039ff0a3d9009f554c2ade2dade356007d56a61e78bd92676a0059a559dd3bd3d30ce600319eeda6eaf31e4fd50000f93ddbb67eefdffe else (if i < 2 then 0x6e2a1aab3e1522a44b506cc155941180896a81606b0b1474266d75888980693f40c0fd888a13367068030831c4901c11218066ae8021d1461b0180d064c5c788582a4742d9f0635a08ac312424892d5061f073110366302a4b006041b6614e808d83c6a05ebc476e0092ca50a6105ce4a84d62d2a8b935605b3c319653818c126cd059b91500ec0f60c2e06057e15a9d8d2182f54f0056a0931a610461a818205518bc61a44c88c27220536c760421da13859b20520104ac2b029c3d3000506a508e9861b26568204ee818992787024225d04d24c8ed84446e5c16c04bbb430300a25c31934049de34730e982b129e904831006c514dc3dcb1404672e644e1194e3471a044f2902ac8f81c5680a04301cb59861572ae6c3041838b14873440319e003fc32c8231e685da12703e5105574a88388099a03ca947a44d060391a67 else 0x9f0b7484c511415c01609d61a8596b4a171c00e09c12d050c8b409530c009a8197c9080613a698c098ed9364b110a8445650976866253324449301d095ab2f02e6f10089770094214780a82150eaae109291483817d0c62a4720913c280308cf932444108fe912809c930700d0608e5e0bb5812248c845908c938db21462d1ccc9208afc1834c29426c92b3089804002a54cd032bd3087d7e47c008a48aa32e08690c518403e11464280856903c80a0805a42c40841c525021058098e490827076a4626448f309c080d6b2520cf8291bc0807f33730adc5093211c107dd328a0cb018b1e12007bfa3d629317a25562c07aa022439c28252c20b0790750b88570ce409c407791063206c478c980b076250a0560e57012ca8074c840a61d07801915607347e08150c826b362007170ad654be00673ca306ff0ca5111855624559)) else (if i < 4 then 0xcd75a952b004238a29c0cc230860982146a41a90caa09532438eb84908c0c9728221601d91888810c81c45009c1612370160c6a04484ac5b842d1520c542145352a53c102600c3d5e80848b24268a1a0c20612c29522ec79b2c0c0ab618c242e1ca01800bf3b2f000a50c4409b30bdd230686435c3148060bc11aecd9f8078851140bac0c05b083829632030b9b02808f29811480420b81391b8914542e144d0b658ca9445083dddc830b515014462046a0a3520b37d11286981d9228d50b20442e88092671216c0b0ac88a3421c16342480af1d2692cf1064001da0ada898452e13c015aa00ac229ca1712421c40b60aad4872222704a918880a9923548144410652a10a866061d12c829004060a69a851a1197b5528e30a4f471023aae20ec48b0a335c2033c078e91eb40a20220891108190d51c0a08a1022e8a89109579 else (if i < 5 then 0xfb843047663443486d20fa66028088a811e1b000f9312a5510c8c02022c0f770ac891af329768430f620890ae31701848510f4da5208a1206a1ca280f3219e99312448f94a10f1963544a82996538180f02f30800c84c2ac2c50eed22860514324b021e0ed5cac44930a9342e040ec1d1800300025c605f0eab3101326344489b050e9393030404e496acac0e8018010ca0c2543c220e690472a44ad18459c00e512a2d9990a44135120e39ce4bc11c093338000e25062c8203074461540e0b319473a1482016f90df3b6c2644aa60269100ddcf9953002096585800dc1d14c62c8d991c3820dac206c0ee4203a500a0d9145c2ec1c1b220ccd0d7707e91cf0071849c80d608c30aaf430c54a000d4c1148b010c1853c220d361ac2144a1d1c26800d1f001e821b9016f3600d066e2e8c05a928c0540cef270445ada2c14a02 else 0x1289458300a4e80050c912745e009b10131a8508125fb0994855002a489112470eb264624015843712348051400a1968928a121c9160a29c4485981712074e0288dc9740601011f12d140009fa811ca411d681e5312936166d4811c4418240017e28070411ad258a73380c109415119b11740005c14502431187222442481990c8a311704ac18069a41a51521159aed22c04239040a6113e5f583b28a342cc1011259c9ba22404cd0878110b8cbb115a89c0641510f382a014a717d880e110dfd122480cb415402110c42a4f4cf12d18061610ab8b0844aa0a6274e91099116480b800322350108489a2d92078020740106e00d0470862cc392a1058083460e442811ad31041b424a48aa8268162102c04c505e00560a24e10148c594005f2a50e280ffddaa01c6043284e440fe35529094232cec38c0fd1a1c836400401f100))) else (if i < 9 then (if i < 7 then 0x154b8130c418eb9c2182153818204627062818a1151fb02c068d30997286150902615b108ce1821a14f3089255945026206714e14c9520184006ac0114cb4582e2412e4a144114b53303211c248ac1a8149eb2523081c168930a1483c6448743c4b7d041146b3c821851a278231c1458200599016194288c144552a9009a444209061431102f01e24a018454141d1a6165064c0710101401d1e5528e4c2c027313eb811449473813911113d5382a4a00b3c0866413be638c382c1231404713a5c3908ec1225ca988138d500229b20ea3970c1377003930646141d8171362c8907244460c8522134f841a8a05a12820d0133806c6c3412250b330131f0e1d8438a8a5284b130757008532344c82da12f1a11110813ae4503512df02180208849341b612c80196184788e8858a12b3a046a31781210192129c342d02a09d0b406c else (if i < 8 then 0x180d02c18a6c0341414417fd008d24240346140117e54a79b0a00508ce1a17cf88a1b3572000949817bc02c242484b10613417a60a8034aa1dd0069817968514240288082324177f58c2c1e4370116201767620e5c32d2b54001174d4869b242a46a4acc17392d9498517680010017233151512a86044c2a170d2a04060d934cb81116f760040b96e18e21a016e156c641181851842a16c8a0cf4116e2a2660116b55130304a120242ca169d318119a50c4cc8e4168392989600e8552d9c166c4243706a130d156016526134204eacba4b11163e4aa0412038b0322616282149d40980d2108f160f0e842afad040471515f95c2da8a01485109115e38121417c4100a8bb15d0014212c0c781246815bca43206846022d10315a3602a11d10e638678158b20d1ec17116452841579020919290540a20d156250249a370684c158 else 0x1ab8a00b01a5404212f51aa48801c1162a8c98a01a8fc111106515d83a001a7ea10421018422f0051a68140c9129080a966e1a52054248a32a7548a01a3b810494b29344e60a1a2475a420e0108d113c1a0e3499a440c6c9081819f6b9602a4d049409a919e146404891518968a419cf1a8448599a01410019bc8404e41038c6168019a64c54342111762091198a01bb921662a38b7119768220326a4518188a195f3220486e14e5a148194a715021138534601419344c4202889c0b653219254008a80cc061400a19118c640350311c088518ff1818d210208b005918e388e94452ab86b09718c9b221542a5861a39318b6531c86030130808618a14a2a81803d80b450188e65028509494118281877d25508a8165a80511865080619704008d584184c0fa0851a8347948a183b20250a2804142a43182053566841d82659c1)) else (if i < 11 then (if i < 10 then 0x1d6807184210d1841a211d530e2655410c42b0481d3e08c1e90a007228651d2c80240fe2070808881d14441b504538e0c4b41cfe0b19d54080141d921ce752c222889b8934881cd52060069c002168561cbe6647022591ba90081ca8099255073084642c1c900e580b1a8204ae931c7ca901c306162045601c681252b060091414a91c51c15072c550d00b281c3f4602ad0629108a001c2c240154048c70e2181c15e34769a00a10182a1bfe94ad3858022640591beb34050062460a138c1bd53d0074202d9859201bbbd94342a394d130911ba8042ec142401829921b8d086c4aacb06bf20a1b790e98210758a024a01b5f8935a391c5326c401b4b488822821a2390cc1b3622833434a809c1031b1d628426c38e518f201b089520af00858482321af674809c30231140401ae14010803d5a260ce41acd06180072c45c09c2 else 0x20121ad51590303a80421ffbad2588570083d0141fe81880c544624841191fd50231204986948e101fc10214ab53a81181201faa724f9810021163621f9a08d1082049c0120c1f83d4703c200308e5071f6ea182d9d0040a45a01f59142307726949a0001f3f5135780e4ba1888a1f29822064921c9632a41f1700ee52800a21240c1f02e902cc00c8714a041ee886543d7920486b901ecf088ca8f132091f941ebc35601212418c30821ea510c32282c92d311a1e92740603048432d0601e7a1c8b1cdd0290003e1e67220f64a1a30044041e4f59389298a46885811e3c542ec142086400b01e2704a1721888d780111e11530068424b8983921e009032040214170a211deb604cda310420a5121dd88a84602818a046491dbc196cb42307066bc31da761b411300aa68a041d90bcf04506460144831d7b2a440cc0d04c13a1) else (if i < 12 then 0x22ab48260a0540d037612299200a064f0518414422874025015c0488c0782272491b70042b406a80225bc86db4318008a2942249111710434c4a008422342a30953088027921222160301e2cc0082542220692764883108ec17721ef2a608ab410a9a26221d9c00025b851741c0b21c4c510a918d540224821ac64166880426b1995219406d821108a4b483f2181e10324011f40318021701048c1c01910803321630481864402802208214ea0109d198914168821364158116187642dc8211f383b8b85404b184021098258c61c0d03818920f69844260c44a4b80020e42750404648a4620020d03022c42c2513444820b4a59d091e2ae0266520a30b1c0a803324000c209028805bb0440443442079346396142158108e2064b1012c0c4a009ac9204dc02244cf04932133203d102801b0118a05142028c708e18020244ce1 else 0x2551ea8a1409f0a30846253c0764381220242716252930102235480540bc250fa8e04458c44ab1ba24fb70903428039c20c124e594104c48912ac8a624d232821e302303502024c008c104130382544624ad8065bc88330021022497418070757045806924862813f0020c408508247113b4124140211ea8245ac10640161c32aab424490a0708013418121a2434a744841043c064e024214d2192900220c819240a31322b056200cdc823f4135b0004665124a623e010670ca94880930223c6d62cc9904907794023b114e8058818883664239d6702188a01814a4923849d880a43d43081c72372310940a3008c07a0235a8a883266264d7104234b11820c208c40028323360478285f88029054231f02e21c5da022a12c230b4ad0d0015035142822ef1e8525a34252cd9322db9809330018a3812922c09eda4310215b88b8)))) else (if i < 20 then (if i < 16 then (if i < 14 then 0x27eb300a64000216888027d5e14226440261a39827c144088e911817c04127a91c2e94692e93810027930f01100d53145a85277b9b39083a34402cc22769000cc256488a894027562200350a054a602b2740005172e4109016ab272c876002ccb1205050271b12040360912a43042701a1860ca988d74e2426ef881885d2412c801026d9cc821993006c106926c1306a302a44ddb90026afc8820e0d10800863269b2340c15b60840914268a0cae02889180031026780b01082eb0c014422667418c072121182c002650043a58065066c871263d051832028291c02d2623627504a11c358969260e9250a604e838128425f7366144491161441e25e04cd220a48a63480b25c9d0013a49a43e244425b614a30256500050c525a69083406860816100258db27548a2034c8e48257b4326020a688c20c0256922c0898500c30720 else (if i < 15 then 0x2a71084c5a209601c60a2a5e0409282250b166c02a4941a5ac19c30a000a2a38d100901408a486a02a222678164040da0d092a0d28d244e40050a27129fda17008120c04123029eb468242100d71300229d0800a609ff9546c4529ba9f109123e410890229a7913100060a410cdc29978803042020500cb6297e0ba1764a8448a552296b34048218e02841d229557425d10d0202c6442942c600c49e10662008292e165101c8330600c32917a90069802286dea129058881d0146184040728ec28d37a4a0d30872028dc00208d056519004128ce00a008e48a02045028b8cb48bda26005060028a04c21a2e21632058d288c48169a054a224085287681a3c55048904507285cb8d25ec0146c2522284a30102b001119627028370e21443098017142281f4b4e842630a1064e280a850518515272011927f91438d10304e10800 else 0x2d0b34aa80914c21404c2cf701b0860a2e9468012ce0f0421c20d904bc0a2cc73110848df51819952cb920c24800304015122ca1041d3134d143508b2c8c8440b3cb614680802c78259488011c21d6102c5d1eb2a3466b0098b12c486195146212d481402c37400647442120ca022c2248a91a010b3234142c0b4d482c0521a6624c2bf39241b33853042b882be3488010b02060053c2bce105a01688183b8922bbbd00050065f0909212ba690168287640988c42b942880415829a264402b820218f02c21c210092b6c075801b88214ae052b54c192cb072c2c88302b400341a3700056408d2b2c41a204a588cc180a2b15a4044e5064a879412b02108a8b80152234502af0800880bc11451a442add15252008e26005922acb850ba0031083880c2aae0d79e3464fd550082a9a8a144e85504881a02a8524200c57ac20a245)) else (if i < 18 then (if i < 17 then 0x2f9851582a9289a0b8d02f851823c445890214222f70e3430806c23150092f6000482a9890040d822f477408f2b426e08c212f34140876402c9a20032f1dc2c122455da588402f08c61cc00330104af02ef224640981a0db230c2edbe207950642314c882ecad02c800a4410c1052eb3401aaa320442d3c52e9caad037602482540a2e8708604845079534322e772050c841811c00832e6628480034980107682e51c940450d0807022f2e3f46490200a65601112e27792041461222176d2e1600617432080149902dff4b1658a5961401222deb320444c29908a1622dd624459640253b40482dc622478100b20050602daecfa88668e04804132d9a0c886322700019f02d832f103108cd0acc122d73100106e8454410482d5c6646021e941343212d434c0e126c82aa96382d32044620a0a2c420432d1f4150a1130158a406 else 0x322680958a605434c4023212c81351807086091432010a4a8028c81a501031eb91505a08d8e9844031d7c120a7505930320031c2202ec9c002e1a40c31af028cd18c03811c08319197650d4a2678c55a317da81912526240c128316a324a4030028cd0253154202302478605325b313de5204110bc8e2982312870a10f110599410431148490a8b2a0060e8231025330109045028e8030f2809f000058840a1130d981e9d00e2a42d11530c64080762ac029988030b48018490d04804b9430a2628c02448c20c406308c82468193887544093077189806d26128408730637084507442000fa1304a36a3136620037924303520312847118898533024602063106804b021301000a3d0ac04b002742ffda90f1101930504402fe696b03708055007582fd411854804288d01612fc30983620200088c962fb01880202b03ed80a0) else (if i < 19 then 0x34a40a2100e283380cc3348c84580c90391d1365347a4a25048018c2c02a34674200c4842855304b34540510b802a204cb143441a40680846ac18111342b852270602446a12b341c08407c20080d03083409870a0081c00f532033f508a4928c2288711233e0ecd308291010600733cf0ee00210860e404833be0009e8a01a0e060433aab13041304200b58a3398da8100885445220233858204035468b40930337016a491058712014c335561487404b2b662e933451004a1b104604a04332ec0270ad14ca18605331d142b04402a00a09c33063836422985902e6032edb34a038b0018687732d80444c6112893131632c68844019800a7306132b115450309102aa4d1329f0c02a384120558303288a89a34686f0a0401327992804c849009001232658250e8c12438082632500061169097e20318323a258a1c8c22642807 else 0x373620506da222d330243725ca2817a2000401183711509e8001642b80b036fb8379a15240d0051136e5aa30182c84018cf236d26640011a10a4cac036c010444e41b240303036a92e4434189980624b369051543a2963528b04367a6815827008a85e09366521d90404038271a3365180a36c825014b041363f1200a01639244a50362d4026547808c1900236158fd8210413d344053601418885a85432090635eda19c200038408d4d35d68b808474c705489235be23a04249c82d92b835a85514068f410bc09035944c421d0c382a2028357f23190990a1631424356d0c202883c11e8804355ecc014210222004683547112ae462288d109a3534091702430380a710351d5524e84835908930350912c811843a09460c34f602d8941228210e8234e482c10863c010225234ce2ca20ab440a14b0934b80410c2744d86388c))) else (if i < 23 then (if i < 21 then 0x39b118190402a640512a399dc29130081871049a3984241c899329b38960397344028c0908d252403960e000491308e1020f394ec08ca430030481983935c12ee831164e01d0391f21c984646a151881390c3224500058acb60038fbc22880584421188138ea18c00915b100805238d547155912908028a238c141752048244e248138b10c88030222e4010c389e16920748c182c400388bb0b2002588682a10387071080983193cd9b6385b264150c10790d026384b0c0990014a31008a3834997485616200850e38241011800550a200b9381232000326a085842638020000040e0d89265837e81572e15814a9a23137d4240948489f00526437c12104ad0742201c8237ae12c5005a025c24423797b08a58253041c1ac3786084150208a82612937714932188c0c381113375bd6420700748c3301374c02000ae884802446 else (if i < 22 then 0x3c1c0a09d0c4004124543c09c2180991802158253bf70b882100514046ca3be61118014220c60ac83bd511080326cc0024343bc390840a415d1800513bb001442eca4401a3803b9934814318a03a97063b81ce82d084a0077c423b698c018848b246ee073b5b0400111022e80b803b488e889222289600213b380847404115011a103b2463208081fc0a40153b0d30ad5900aad003623afc291c5002614144083aeb08e0b601904801093adb0035208608830a483ac71e232004481439a83ab1135104a491ac25483a9d30186114891fc0023a8a2445d424250960103a76c45b440b08101e803a6343c819133000a8443a4ec58632800c038a8c3a381213242aac0681a63a20695424c542583a283a0e4320c180880072d43a0124800040a120c01639eb8b920d01e024106d39d54d90082191246c4739c31805c0061241c8c1 else 0x3e9b21b443953a8381393e83289a7660045355213e6cc0c0344f0e0c8cb03e56a308ca840c3818a63e45488d04080860c44a3e34414c048a291300843e2700012041b42049803e128993422424205c913dff0828e318898050073dea324450821384a4713dd6041022d1053730323dc146804a94152290783dab0c8a99a6222044e43d9d074801800032009c3d8a5880b1d0260094283d768c2b60080056e0833d5f102506834ac89ac93d4b44322001dd2043453d3652608878859a10183d23a087240012d026c43d0c19680e08d22cc6903cf90929a20570a20c403ce80490c14c4040bc043cd5093078c2011814233cbe4352641ba40720833cad50c083302a4814083c9269cf102898e652a23c7f04458452244603583c69e1808b502a8c408d3c5516aa1142414169103c4110a06463d040ac303c2d86242118b880b910)) else (if i < 25 then (if i < 24 then 0x411b212c8504b418430341074264582ca832070040f828900c007341020440de578019f2c53002d940cd28b3a8620044110040b8818296408498742a40a4132148a8100d1439408d926a8490a88e4950407b3009c09084682432406285c7a03331911246404cc98c02083274a708403c3020b80062498030402984b204000e58482d401ac81108030c248c00400ba00209020138c1843ffa042210d000c3c1543fe44810c125131634633fd3c5018410021c48433fbba49e8af0008bd4203fa32a307134484dc88a3f8c826546864c9416033f782448680b0826a8153f606402412d3a98c13a3f4bc418001d00636e073f36830934838258058a3f221481b1421885124c3f0e30310422689a78013efe89160c60013010413eed2008c10b500f20603edc126108908b8050063ec86500082e2a045c623eb50280b3b0540c8205 else 0x439982882160041e0d4843843012e39014208d1c4370b30bf40800098031435e019600890e60a112434bd410800165840ac6433358e803a032a8517843230ac2010000c632254313464528020422241842fe090602d33089162c42eb0a3012484705483842d2c8222a8cd839159142be7206011ca82221a242ad00030c348819d10442962e4e052240a75608428344c0880a81488b13427020a44b65448002a442609a02000027024907424f3255084050440522423c253c0208910a03c142274a8ad4b00818027442106741f90570c2280041fd90102ba100284e4a41eb34a470a11c84000141d8a11083300815892a41c1b1060e80da04266a41aa51360a58608dc28241907246ce050428336e417e8152048101e018e44168104900d36340a3d44155143832804c208bc041410208554a218e3016412fc054324302802119) else (if i < 26 then 0x460ee2110c428041b81a45fc2360c2514083100645ec440c00c100b9021645d7ce818025fb00240845c484889648e108604445acac32631032490635459a0c18c02223481918458601f2548e0014182a4570c40caa0704b07121455d102044602da381384547e649180192512a60453548cc0402942c43104521818492a30e40426145112c618228a002801444fd1934100157a0830344e741680b1e01aa58c044d60287057c2310800044c4c4019118a242548044accca4072920580e174499089478c02640432444813c22e00620da1d2a4473008520431064090844660308088038200a2244512429599012488370443b015d940ce1551840442688809e18a40a40c74415480bd2120441180143ff2c4ac0084344693543e921503a2a432512d043d40212039d1d1aa03043c10c0411581c72016443abe00e44894b005a8a else 0x48580000d8602000800548439858014284d3102e482a88870065c9992b70481440400e86d48d1b904808406012500860044047f00f0a9880e2a25a4947db5e3402229202424d47c711156151284c806847b511581130045d018847a29022044998500783478e04760217c1a58004477d40004d581402906a4766a38a05906241308f4757000800f91204a88447410001a1b05c4d8f884733808b704804100014471e8b23508d10b084504709821e62089433411246f820a0450100cb066246e821900921180034a246d21c8506295266640246b97c973244244b40c446a5a612033c41904c8046938282140641c81921467f94082306390030e5466f344012a40148a110465f8096e00040430a03464a0d552818421605544637c11010416ae0140d46222098412e8a0da412)))))


private def pop (x : ℕ) :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c * 0x0101010101010101) >>> 56) % 256

private def raw (j : ℕ) : ℕ :=
  let entry := ((packet (j/2048)) >>> (80*((j%2048)/64))) % (2^80)
  (entry >>> 64) + pop (entry % (2^(j%64)))

private def small (n : ℕ) : ℕ := if 5≤n then 3 else if 3≤n then 2 else if 2≤n then 1 else 0

def fast (n : ℕ) : ℕ := raw (index n) + small n

private def quick (n : ℕ) : Bool := if n≤454 then decide n.Prime else n.gcd 47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810 == 1

private theorem quick_ok {n : ℕ} (hn : n ≤ 206781) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · simp
  · have hm : 47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810 ∣ Nat.factorial 454 := by decide +kernel
    have allsmall : ∀ p : Fin 455, p.val.Prime → p.val ∣ 47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 454 := by
        by_contra! hi
        have hb := Nat.mul_le_mul hi hi
        rw [pow_two] at hsq
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (allsmall ⟨n.minFac,by omega⟩ hpr)
      rw [eq] at hd
      exact hpr.not_dvd_one hd
    · intro hp
      exact Nat.Coprime.of_dvd_right hm (hp.coprime_factorial_of_lt (by omega))

private def step (j : ℕ) : Bool := raw (j+1) == raw j + (if quick (number j) then 1 else 0)
private def valid (lo len : ℕ) : Prop := (List.range' lo len).all step = true
private theorem glue {lo a b : ℕ} (left : valid lo a) (right : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [←List.range'_append_1,List.all_append,left,right]
  rfl

set_option maxRecDepth 6000 in
private theorem leaf0 : valid 0 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf430 : valid 430 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf861 : valid 861 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf1292 : valid 1292 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf1723 : valid 1723 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf2154 : valid 2154 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf2585 : valid 2585 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf3016 : valid 3016 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf3447 : valid 3447 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf3877 : valid 3877 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf4308 : valid 4308 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf4739 : valid 4739 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf5170 : valid 5170 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf5601 : valid 5601 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf6032 : valid 6032 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf6463 : valid 6463 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf6894 : valid 6894 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf7324 : valid 7324 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf7755 : valid 7755 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf8186 : valid 8186 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf8617 : valid 8617 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf9048 : valid 9048 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf9479 : valid 9479 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf9910 : valid 9910 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf10341 : valid 10341 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf10771 : valid 10771 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf11202 : valid 11202 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf11633 : valid 11633 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf12064 : valid 12064 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf12495 : valid 12495 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf12926 : valid 12926 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf13357 : valid 13357 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf13788 : valid 13788 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf14218 : valid 14218 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf14649 : valid 14649 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf15080 : valid 15080 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf15511 : valid 15511 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf15942 : valid 15942 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf16373 : valid 16373 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf16804 : valid 16804 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf17235 : valid 17235 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf17665 : valid 17665 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf18096 : valid 18096 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf18527 : valid 18527 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf18958 : valid 18958 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf19389 : valid 19389 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf19820 : valid 19820 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf20251 : valid 20251 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf20682 : valid 20682 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf21112 : valid 21112 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf21543 : valid 21543 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf21974 : valid 21974 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf22405 : valid 22405 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf22836 : valid 22836 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf23267 : valid 23267 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf23698 : valid 23698 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf24129 : valid 24129 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf24559 : valid 24559 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf24990 : valid 24990 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf25421 : valid 25421 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf25852 : valid 25852 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf26283 : valid 26283 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf26714 : valid 26714 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf27145 : valid 27145 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf27576 : valid 27576 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf28006 : valid 28006 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf28437 : valid 28437 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf28868 : valid 28868 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf29299 : valid 29299 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf29730 : valid 29730 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf30161 : valid 30161 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf30592 : valid 30592 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf31023 : valid 31023 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf31453 : valid 31453 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf31884 : valid 31884 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf32315 : valid 32315 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf32746 : valid 32746 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf33177 : valid 33177 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf33608 : valid 33608 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf34039 : valid 34039 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf34470 : valid 34470 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf34900 : valid 34900 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf35331 : valid 35331 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf35762 : valid 35762 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf36193 : valid 36193 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf36624 : valid 36624 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf37055 : valid 37055 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf37486 : valid 37486 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf37917 : valid 37917 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf38347 : valid 38347 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf38778 : valid 38778 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf39209 : valid 39209 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf39640 : valid 39640 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf40071 : valid 40071 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf40502 : valid 40502 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf40933 : valid 40933 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf41364 : valid 41364 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf41794 : valid 41794 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf42225 : valid 42225 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf42656 : valid 42656 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf43087 : valid 43087 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf43518 : valid 43518 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf43949 : valid 43949 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf44380 : valid 44380 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf44811 : valid 44811 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf45241 : valid 45241 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf45672 : valid 45672 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf46103 : valid 46103 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf46534 : valid 46534 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf46965 : valid 46965 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf47396 : valid 47396 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf47827 : valid 47827 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf48258 : valid 48258 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf48688 : valid 48688 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf49119 : valid 49119 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf49550 : valid 49550 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf49981 : valid 49981 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf50412 : valid 50412 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf50843 : valid 50843 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf51274 : valid 51274 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf51705 : valid 51705 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf52135 : valid 52135 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf52566 : valid 52566 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf52997 : valid 52997 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf53428 : valid 53428 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf53859 : valid 53859 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf54290 : valid 54290 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf54721 : valid 54721 431 := by unfold valid; decide +kernel


set_option maxRecDepth 20000 in
private theorem allrows : valid 0 55152 := (glue (lo:=0) (a:=27576) (b:=27576) (glue (lo:=0) (a:=13788) (b:=13788) (glue (lo:=0) (a:=6894) (b:=6894) (glue (lo:=0) (a:=3447) (b:=3447) (glue (lo:=0) (a:=1723) (b:=1724) (glue (lo:=0) (a:=861) (b:=862) (glue (lo:=0) (a:=430) (b:=431) leaf0 leaf430) (glue (lo:=861) (a:=431) (b:=431) leaf861 leaf1292)) (glue (lo:=1723) (a:=862) (b:=862) (glue (lo:=1723) (a:=431) (b:=431) leaf1723 leaf2154) (glue (lo:=2585) (a:=431) (b:=431) leaf2585 leaf3016))) (glue (lo:=3447) (a:=1723) (b:=1724) (glue (lo:=3447) (a:=861) (b:=862) (glue (lo:=3447) (a:=430) (b:=431) leaf3447 leaf3877) (glue (lo:=4308) (a:=431) (b:=431) leaf4308 leaf4739)) (glue (lo:=5170) (a:=862) (b:=862) (glue (lo:=5170) (a:=431) (b:=431) leaf5170 leaf5601) (glue (lo:=6032) (a:=431) (b:=431) leaf6032 leaf6463)))) (glue (lo:=6894) (a:=3447) (b:=3447) (glue (lo:=6894) (a:=1723) (b:=1724) (glue (lo:=6894) (a:=861) (b:=862) (glue (lo:=6894) (a:=430) (b:=431) leaf6894 leaf7324) (glue (lo:=7755) (a:=431) (b:=431) leaf7755 leaf8186)) (glue (lo:=8617) (a:=862) (b:=862) (glue (lo:=8617) (a:=431) (b:=431) leaf8617 leaf9048) (glue (lo:=9479) (a:=431) (b:=431) leaf9479 leaf9910))) (glue (lo:=10341) (a:=1723) (b:=1724) (glue (lo:=10341) (a:=861) (b:=862) (glue (lo:=10341) (a:=430) (b:=431) leaf10341 leaf10771) (glue (lo:=11202) (a:=431) (b:=431) leaf11202 leaf11633)) (glue (lo:=12064) (a:=862) (b:=862) (glue (lo:=12064) (a:=431) (b:=431) leaf12064 leaf12495) (glue (lo:=12926) (a:=431) (b:=431) leaf12926 leaf13357))))) (glue (lo:=13788) (a:=6894) (b:=6894) (glue (lo:=13788) (a:=3447) (b:=3447) (glue (lo:=13788) (a:=1723) (b:=1724) (glue (lo:=13788) (a:=861) (b:=862) (glue (lo:=13788) (a:=430) (b:=431) leaf13788 leaf14218) (glue (lo:=14649) (a:=431) (b:=431) leaf14649 leaf15080)) (glue (lo:=15511) (a:=862) (b:=862) (glue (lo:=15511) (a:=431) (b:=431) leaf15511 leaf15942) (glue (lo:=16373) (a:=431) (b:=431) leaf16373 leaf16804))) (glue (lo:=17235) (a:=1723) (b:=1724) (glue (lo:=17235) (a:=861) (b:=862) (glue (lo:=17235) (a:=430) (b:=431) leaf17235 leaf17665) (glue (lo:=18096) (a:=431) (b:=431) leaf18096 leaf18527)) (glue (lo:=18958) (a:=862) (b:=862) (glue (lo:=18958) (a:=431) (b:=431) leaf18958 leaf19389) (glue (lo:=19820) (a:=431) (b:=431) leaf19820 leaf20251)))) (glue (lo:=20682) (a:=3447) (b:=3447) (glue (lo:=20682) (a:=1723) (b:=1724) (glue (lo:=20682) (a:=861) (b:=862) (glue (lo:=20682) (a:=430) (b:=431) leaf20682 leaf21112) (glue (lo:=21543) (a:=431) (b:=431) leaf21543 leaf21974)) (glue (lo:=22405) (a:=862) (b:=862) (glue (lo:=22405) (a:=431) (b:=431) leaf22405 leaf22836) (glue (lo:=23267) (a:=431) (b:=431) leaf23267 leaf23698))) (glue (lo:=24129) (a:=1723) (b:=1724) (glue (lo:=24129) (a:=861) (b:=862) (glue (lo:=24129) (a:=430) (b:=431) leaf24129 leaf24559) (glue (lo:=24990) (a:=431) (b:=431) leaf24990 leaf25421)) (glue (lo:=25852) (a:=862) (b:=862) (glue (lo:=25852) (a:=431) (b:=431) leaf25852 leaf26283) (glue (lo:=26714) (a:=431) (b:=431) leaf26714 leaf27145)))))) (glue (lo:=27576) (a:=13788) (b:=13788) (glue (lo:=27576) (a:=6894) (b:=6894) (glue (lo:=27576) (a:=3447) (b:=3447) (glue (lo:=27576) (a:=1723) (b:=1724) (glue (lo:=27576) (a:=861) (b:=862) (glue (lo:=27576) (a:=430) (b:=431) leaf27576 leaf28006) (glue (lo:=28437) (a:=431) (b:=431) leaf28437 leaf28868)) (glue (lo:=29299) (a:=862) (b:=862) (glue (lo:=29299) (a:=431) (b:=431) leaf29299 leaf29730) (glue (lo:=30161) (a:=431) (b:=431) leaf30161 leaf30592))) (glue (lo:=31023) (a:=1723) (b:=1724) (glue (lo:=31023) (a:=861) (b:=862) (glue (lo:=31023) (a:=430) (b:=431) leaf31023 leaf31453) (glue (lo:=31884) (a:=431) (b:=431) leaf31884 leaf32315)) (glue (lo:=32746) (a:=862) (b:=862) (glue (lo:=32746) (a:=431) (b:=431) leaf32746 leaf33177) (glue (lo:=33608) (a:=431) (b:=431) leaf33608 leaf34039)))) (glue (lo:=34470) (a:=3447) (b:=3447) (glue (lo:=34470) (a:=1723) (b:=1724) (glue (lo:=34470) (a:=861) (b:=862) (glue (lo:=34470) (a:=430) (b:=431) leaf34470 leaf34900) (glue (lo:=35331) (a:=431) (b:=431) leaf35331 leaf35762)) (glue (lo:=36193) (a:=862) (b:=862) (glue (lo:=36193) (a:=431) (b:=431) leaf36193 leaf36624) (glue (lo:=37055) (a:=431) (b:=431) leaf37055 leaf37486))) (glue (lo:=37917) (a:=1723) (b:=1724) (glue (lo:=37917) (a:=861) (b:=862) (glue (lo:=37917) (a:=430) (b:=431) leaf37917 leaf38347) (glue (lo:=38778) (a:=431) (b:=431) leaf38778 leaf39209)) (glue (lo:=39640) (a:=862) (b:=862) (glue (lo:=39640) (a:=431) (b:=431) leaf39640 leaf40071) (glue (lo:=40502) (a:=431) (b:=431) leaf40502 leaf40933))))) (glue (lo:=41364) (a:=6894) (b:=6894) (glue (lo:=41364) (a:=3447) (b:=3447) (glue (lo:=41364) (a:=1723) (b:=1724) (glue (lo:=41364) (a:=861) (b:=862) (glue (lo:=41364) (a:=430) (b:=431) leaf41364 leaf41794) (glue (lo:=42225) (a:=431) (b:=431) leaf42225 leaf42656)) (glue (lo:=43087) (a:=862) (b:=862) (glue (lo:=43087) (a:=431) (b:=431) leaf43087 leaf43518) (glue (lo:=43949) (a:=431) (b:=431) leaf43949 leaf44380))) (glue (lo:=44811) (a:=1723) (b:=1724) (glue (lo:=44811) (a:=861) (b:=862) (glue (lo:=44811) (a:=430) (b:=431) leaf44811 leaf45241) (glue (lo:=45672) (a:=431) (b:=431) leaf45672 leaf46103)) (glue (lo:=46534) (a:=862) (b:=862) (glue (lo:=46534) (a:=431) (b:=431) leaf46534 leaf46965) (glue (lo:=47396) (a:=431) (b:=431) leaf47396 leaf47827)))) (glue (lo:=48258) (a:=3447) (b:=3447) (glue (lo:=48258) (a:=1723) (b:=1724) (glue (lo:=48258) (a:=861) (b:=862) (glue (lo:=48258) (a:=430) (b:=431) leaf48258 leaf48688) (glue (lo:=49119) (a:=431) (b:=431) leaf49119 leaf49550)) (glue (lo:=49981) (a:=862) (b:=862) (glue (lo:=49981) (a:=431) (b:=431) leaf49981 leaf50412) (glue (lo:=50843) (a:=431) (b:=431) leaf50843 leaf51274))) (glue (lo:=51705) (a:=1723) (b:=1724) (glue (lo:=51705) (a:=861) (b:=862) (glue (lo:=51705) (a:=430) (b:=431) leaf51705 leaf52135) (glue (lo:=52566) (a:=431) (b:=431) leaf52566 leaf52997)) (glue (lo:=53428) (a:=862) (b:=862) (glue (lo:=53428) (a:=431) (b:=431) leaf53428 leaf53859) (glue (lo:=54290) (a:=431) (b:=431) leaf54290 leaf54721)))))))

theorem fast_correct (n : ℕ) (bound : n ≤ 206781) : fast n = Nat.primeCounting n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases smallN : n < 6
    · have tests : ∀ i : Fin 7, fast i.val = Nat.primeCounting i.val := by decide +kernel
      exact tests ⟨n+1,by omega⟩
    · have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤206781 by omega)
        have ok : (List.range 55152).all step=true := by rw [List.range_eq_range']; exact allrows
        have h := beq_iff_eq.mp (List.all_eq_true.mp ok (index n) (List.mem_range.mpr ix))
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
end WheelTableA94


/- The Legendre and Meissel identities below are the public Physbuzz reduction
for OEIS A247824, itself crediting Daniel Veljjanoski and rleshner. The new
certificate evaluates the first of the eight residual rank anchors. -/
open Finset
namespace RankWheel94

lemma legendre {ps : List ℕ} (hsort : ps.Pairwise (· > ·)) (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hcomp : ∀ p ∈ ps, ∀ q, Nat.Prime q → q < p → q ∈ ps) (x : ℕ) :
    ps.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x =
      ((Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)).card := by
  let sieveSet (ps : List ℕ) (x : ℕ) := (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)
  have mem_sieveSet {ps : List ℕ} {x n : ℕ} :
      n ∈ sieveSet ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by
    simp [sieveSet]

  have sieveSet_nil (x : ℕ) : sieveSet [] x = Finset.Icc 1 x := by
    ext n; simp [sieveSet]

  /- Legendre's recursion step. -/
  have card_sieveSet_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime ∧ q ≠ p)
      (x : ℕ) :
      (sieveSet (p :: ps) x).card = (sieveSet ps x).card - (sieveSet ps (x / p)).card := by
    have hsplit : sieveSet (p :: ps) x = (sieveSet ps x).filter (fun n => ¬ p ∣ n) := by
      ext n; simp [sieveSet, List.mem_cons]; tauto
    have himage : (sieveSet ps x).filter (fun n => p ∣ n) = (sieveSet ps (x / p)).image (p * ·) := by
      ext n
      simp only [Finset.mem_filter, mem_sieveSet, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
        refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at h1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact hx)
        · intro q hq' hdvd
          exact hq q hq' (dvd_mul_of_dvd_right hdvd p)
      · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
        · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
        · intro q hq' hdvd
          obtain ⟨hqp, hqne⟩ := hps q hq'
          rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h | h
          · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h)
          · exact hq q hq' h
    have hcard := Finset.card_filter_add_card_filter_not (s := sieveSet ps x) (fun n => p ∣ n)
    rw [himage, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcard
    rw [hsplit]
    omega

  /- Pruning: below `p`, only `1` survives the sieve by all primes less than `p`. -/
  have card_sieveSet_of_lt {p : ℕ} {ps : List ℕ} (hps : ∀ q ∈ ps, q.Prime)
      (hcomplete : ∀ q, q.Prime → q < p → q ∈ ps) {x : ℕ} (hx : x < p) :
      (sieveSet (p :: ps) x).card = if x = 0 then 0 else 1 := by
    split_ifs with h0
    · subst h0; simp [sieveSet]
    · have : sieveSet (p :: ps) x = {1} := by
        ext n
        simp only [mem_sieveSet, Finset.mem_singleton, List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨⟨h1, hnx⟩, -, hq⟩
          by_contra hne
          have hn1 : n ≠ 1 := hne
          have hmf := Nat.minFac_prime hn1
          have hlt : Nat.minFac n < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
          exact hq _ (hcomplete _ hmf hlt) (Nat.minFac_dvd n)
        · rintro rfl
          refine ⟨⟨le_rfl, by omega⟩, ?_, ?_⟩
          · intro h
            have := Nat.le_of_dvd one_pos h
            omega
          · intro q hq; exact Nat.Prime.not_dvd_one (hps q hq)
      rw [this, Finset.card_singleton]

  change _ = (sieveSet ps x).card
  induction ps generalizing x with
  | nil => simp [sieveSet_nil]
  | cons p ps ih =>
    obtain ⟨hgt,hs⟩ := List.pairwise_cons.mp hsort
    have hp := hprime p List.mem_cons_self
    have hq (q) (hq : q ∈ ps) := hprime q (List.mem_cons_of_mem p hq)
    have hc (q) (h : q.Prime) (lt : q < p) : q ∈ ps := by
      rcases List.mem_cons.mp (hcomp p List.mem_cons_self q h lt) with eq | hm
      · omega
      · exact hm
    have closed (r) (hr : r ∈ ps) (q) (h : q.Prime) (lt : q < r) := hc q h (lt.trans (hgt r hr))
    simp only [List.foldr_cons]
    split_ifs with lt zero
    · rw [card_sieveSet_of_lt hq hc lt, if_pos zero]
    · rw [card_sieveSet_of_lt hq hc lt, if_neg zero]
    · rw [card_sieveSet_cons hp (fun q h => ⟨hq q h, (hgt q h).ne⟩), ih hs hq closed, ih hs hq closed]

lemma legendre_range (y x : ℕ) :
    (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) =
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card := by
  let ps := ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse
  have mem (p : ℕ) : p ∈ ps ↔ p ∈ Nat.primesLE y := by simp [ps, Nat.mem_primesLE]
  have hsort : ps.Pairwise (· > ·) := by
    apply List.pairwise_reverse.mpr
    exact List.pairwise_lt_range.filter _
  have e := legendre hsort (fun p hp => Nat.prime_of_mem_primesLE ((mem p).mp hp))
    (fun p hp q hq hlt => (mem q).mpr (Nat.mem_primesLE.mpr ⟨hlt.le.trans (Nat.le_of_mem_primesLE ((mem p).mp hp)), hq⟩)) x
  convert e using 1
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem]

/-- At a cube-root cutoff, every surviving composite has exactly two prime factors,
with multiplicity. Sorting the factors makes this parametrization injective. -/
lemma meissel {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) :
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card +
      (Nat.primesLE y).card = 1 + (Nat.primesLE x).card +
      ∑ p ∈ (Nat.primesLE z).filter (y < ·), ((Nat.primesLE (x/p)).filter (p ≤ ·)).card := by
  classical
  let R := (Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)
  let T := R.filter (fun n => n ≠ 1 ∧ ¬n.Prime)
  let B := (Nat.primesLE z).filter (y < ·)
  let Q (p : ℕ) := (Nat.primesLE (x/p)).filter (p ≤ ·)
  have memR (n) : n ∈ R ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ Nat.primesLE y, ¬ p ∣ n := by simp [R]
  have memT (n) : n ∈ T ↔ n ∈ R ∧ n ≠ 1 ∧ ¬n.Prime := by simp [T]
  have memB (p) : p ∈ B ↔ (p ≤ z ∧ p.Prime) ∧ y < p := by simp [B, Nat.mem_primesLE]
  have memQ (p q) : q ∈ Q p ↔ (q ≤ x/p ∧ q.Prime) ∧ p ≤ q := by simp [Q, Nat.mem_primesLE]
  have least {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p ≤ q) : (p*q).minFac = p := by
    have hn : p*q ≠ 1 := by have := hp.two_le; have := hq.two_le; nlinarith
    have hm := Nat.minFac_prime hn
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q))
    rcases hm.dvd_mul.mp (Nat.minFac_dvd (p*q)) with a | b
    · exact ((Nat.prime_dvd_prime_iff_eq hm hp).mp a).symm.le
    · exact pq.trans_eq ((Nat.prime_dvd_prime_iff_eq hm hq).mp b).symm
  have pair : (B.sigma Q).card = T.card := by
    apply card_bij (fun a _ => a.1 * a.2)
    · intro ⟨p,q⟩ h
      obtain ⟨hb,hq⟩ := mem_sigma.mp h
      obtain ⟨⟨_,pp⟩,yp⟩ := (memB p).mp hb
      obtain ⟨⟨ub,qp⟩,ord⟩ := (memQ p q).mp hq
      have pos := Nat.mul_pos pp.pos qp.pos
      have bound : p*q ≤ x := by simpa [mul_comm] using (Nat.le_div_iff_mul_le pp.pos).mp ub
      apply (memT _).mpr
      refine ⟨(memR _).mpr ⟨⟨pos,bound⟩, ?_⟩, ?_, ?_⟩
      · intro r hr hd
        obtain ⟨ry,rp⟩ := Nat.mem_primesLE.mp hr
        rcases rp.dvd_mul.mp hd with a | b
        · have := (Nat.prime_dvd_prime_iff_eq rp pp).mp a; omega
        · have := (Nat.prime_dvd_prime_iff_eq rp qp).mp b; omega
      · have := pp.two_le; have := qp.two_le; dsimp; nlinarith
      · intro prime
        have := (Nat.prime_dvd_prime_iff_eq pp prime).mp (dvd_mul_right p q)
        have := pp.two_le; have := qp.two_le; dsimp at *; nlinarith
    · intro ⟨p,q⟩ ha ⟨r,s⟩ hb eq
      obtain ⟨ha,hq⟩ := mem_sigma.mp ha
      obtain ⟨hb,hs⟩ := mem_sigma.mp hb
      obtain ⟨⟨_,pp⟩,_⟩ := (memB p).mp ha
      obtain ⟨⟨_,rp⟩,_⟩ := (memB r).mp hb
      obtain ⟨⟨_,qp⟩,a⟩ := (memQ p q).mp hq
      obtain ⟨⟨_,sp⟩,b⟩ := (memQ r s).mp hs
      change p*q=r*s at eq
      have same := (least pp qp a).symm.trans ((congrArg Nat.minFac eq).trans (least rp sp b))
      subst r
      obtain rfl := Nat.eq_of_mul_eq_mul_left pp.pos eq
      rfl
    · intro n hn
      obtain ⟨hr,ne,np⟩ := (memT n).mp hn
      obtain ⟨⟨pos,bound⟩,rough⟩ := (memR n).mp hr
      let p := n.minFac
      let q := n / p
      have pp : p.Prime := Nat.minFac_prime ne
      have product : p*q = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have ord : p ≤ q := Nat.minFac_le_div pos np
      have yp : y < p := by
        by_contra! h
        exact rough _ (Nat.mem_primesLE.mpr ⟨h,pp⟩) (Nat.minFac_dvd n)
      have qp : q.Prime := by
        by_contra hq
        have qpos : 0 < q := pp.pos.trans_le ord
        have qq := Nat.minFac_sq_le_self qpos hq
        have qne : q ≠ 1 := by have := pp.two_le; omega
        have rprime := Nat.minFac_prime qne
        have yr : y < q.minFac := by
          by_contra! h
          apply rough _ (Nat.mem_primesLE.mpr ⟨h,rprime⟩)
          rw [← product]
          exact dvd_mul_of_dvd_right (Nat.minFac_dvd q) _
        have b := Nat.mul_le_mul (show y+1 ≤ p by omega)
          (le_trans (Nat.pow_le_pow_left (show y+1 ≤ q.minFac by omega) 2) qq)
        nlinarith only [product,b,bound,cube]
      have pz : p ≤ z := by
        by_contra! h
        have a := Nat.mul_le_mul (show z+1≤p by omega) (show z+1≤q by omega)
        nlinarith only [product,a,sq,bound]
      refine ⟨⟨p,q⟩, mem_sigma.mpr ⟨(memB _).mpr ⟨⟨pz,pp⟩,yp⟩,
        (memQ _ _).mpr ⟨⟨(Nat.le_div_iff_mul_le pp.pos).mpr ?_,qp⟩,ord⟩⟩, product⟩
      simpa [mul_comm,product] using (product.le.trans bound)
  have primepart : R.filter Nat.Prime = (Nat.primesLE x).filter (fun n => ¬ n ≤ y) := by
    ext n
    simp only [mem_filter,memR,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨_,ub⟩,r⟩,np⟩
      exact ⟨⟨ub,np⟩,fun h => r n ⟨h,np⟩ (dvd_refl n)⟩
    · rintro ⟨⟨ub,np⟩,gt⟩
      refine ⟨⟨⟨np.one_le,ub⟩,fun p hp hd => ?_⟩, np⟩
      exact gt (((Nat.prime_dvd_prime_iff_eq hp.2 np).mp hd) ▸ hp.1)
  have low : (Nat.primesLE x).filter (· ≤ y) = Nat.primesLE y := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans hy,h.2⟩,h.1⟩⟩
  have other : R.filter (fun n => ¬n.Prime) = insert 1 T := by
    ext n
    simp only [mem_filter,mem_insert,memT]
    constructor
    · rintro ⟨hr,hp⟩; by_cases h : n=1
      · exact Or.inl h
      · exact Or.inr ⟨hr,h,hp⟩
    · rintro (rfl | ⟨hr,_,hp⟩)
      · exact ⟨(memR _).mpr ⟨⟨le_rfl,hx⟩,fun p hp => (Nat.prime_of_mem_primesLE hp).not_dvd_one⟩,Nat.not_prime_one⟩
      · exact ⟨hr,hp⟩
  have one : 1 ∉ T := fun h => ((memT 1).mp h).2.1 rfl
  have v := card_filter_add_card_filter_not (s:=R) Nat.Prime
  have w := card_filter_add_card_filter_not (s:=Nat.primesLE x) (· ≤ y)
  rw [primepart,other,card_insert_of_notMem one] at v
  rw [low] at w
  rw [card_sigma] at pair
  change R.card + _ = 1 + _ + ∑ p ∈ B, (Q p).card
  omega

/-- Interval subtraction evaluates each row of the semiprime count using only ordinary prime counts. -/
lemma prime_row {p t : ℕ} (pos : 0 < p) (le : p ≤ t) :
    ((Nat.primesLE t).filter (p ≤ ·)).card = Nat.primeCounting t - Nat.primeCounting (p-1) := by
  have eq : (Nat.primesLE t).filter (fun n => ¬p ≤ n) = Nat.primesLE (p-1) := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,pr⟩,lt⟩; exact ⟨by omega,pr⟩
    · rintro ⟨ub,pr⟩; exact ⟨⟨by omega,pr⟩,by omega⟩
  have h := card_filter_add_card_filter_not (s:=Nat.primesLE t) (p ≤ ·)
  rw [eq, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
  omega

lemma rank_of_parts {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) +
      (Nat.primesLE y).card = a)
    (pairs : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (result : 1+r+b = a) : Nat.primeCounting x = r := by
  have e := meissel hx hy cube sq
  have row (p : ℕ) (hp : p ∈ (Nat.primesLE z).filter (y < ·)) := by
    have bound := Nat.le_of_mem_primesLE (mem_filter.mp hp).1
    have pos := (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
    exact prime_row pos ((Nat.le_div_iff_mul_le pos).mpr ((Nat.mul_le_mul bound bound).trans zs))
  rw [legendre_range] at sieved
  rw [sum_congr rfl row, pairs, Nat.primesLE_card_eq_primeCounting x] at e
  omega

def advance (p : ℕ) (f : ℕ → ℕ) (x : ℕ) :=
  if x < p then (if x=0 then 0 else 1) else f x - f (x/p)

private def evalPhi (table : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], t => t
  | p :: ps, t => if t < p then (if t=0 then 0 else 1) else
      if t < (p+1)^2 then 1 + table t - table p else
        evalPhi table ps t - evalPhi table ps (t/p)

private theorem square_cut {p t : ℕ} (hp : 0 < p) (pt : p ≤ t) (square : t < (p+1)^2) :
    (((List.range (p+1)).filter (fun n => decide n.Prime)).reverse.foldr advance id) t +
      Nat.primeCounting p = 1 + Nat.primeCounting t := by
  have cube : t < (p+1)^3 :=
    lt_of_lt_of_le square (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  have empty : (Nat.primesLE p).filter (p < ·) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp hn).1))
      (Finset.mem_filter.mp hn).2
  have h := meissel (x:=t) (y:=p) (z:=p) (by omega) pt cube square
  simp only [empty,Finset.sum_empty,Nat.add_zero,Nat.primesLE_card_eq_primeCounting] at h
  rw [←legendre_range] at h
  exact h

private theorem refine_row {bound p : ℕ} (tab : ℕ → ℕ) (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t)
    (ps : List ℕ) (lst : ((List.range (p+1)).filter (fun n => decide n.Prime)).reverse = p::ps)
    (prev : ∀ t, ps.foldr advance id t = evalPhi tab ps t)
    (pos : 0 < p) (cap : (p+1)^2 ≤ bound+1) : ∀ t,
    (p::ps).foldr advance id t = evalPhi tab (p::ps) t := by
  intro t
  by_cases sm : t < p
  · simp [List.foldr_cons,advance,evalPhi,sm]
  · by_cases short : t < (p+1)^2
    · have h := square_cut pos (by omega : p ≤ t) short
      rw [lst] at h
      rw [evalPhi,if_neg sm,if_pos short,ok t (by omega),ok p (by omega)]
      omega
    · simp only [List.foldr_cons,advance,evalPhi,if_neg sm,if_neg short,prev]

private def primeBit (tab : ℕ → ℕ) (n : ℕ) : Bool :=
  if n=0 then false else decide (tab (n-1) < tab n)

private theorem primeBit_eq {bound : ℕ} (tab : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t) (n : ℕ) (hn : n ≤ bound) :
    primeBit tab n = decide n.Prime := by
  cases n with
  | zero => simp [primeBit]
  | succ n =>
    simp only [primeBit,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,ok n (by omega),ok _ hn]
    rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
        from Nat.count_succ Nat.Prime (n+1)]
    by_cases hp : (n+1).Prime <;> simp [hp]

private theorem filter_bits {bound : ℕ} (tab : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t) (p : ℕ) (hp : p ≤ bound) :
    (List.range (p+1)).filter (fun n => decide n.Prime) =
      (List.range (p+1)).filter (primeBit tab) := by
  apply List.filter_congr
  intro n hn
  have := List.mem_range.mp hn
  exact (primeBit_eq tab ok n (by omega)).symm

private theorem merge_filter (f : ℕ → Bool) (lo a b : ℕ) (l r : List ℕ)
    (hl : (List.range' lo a).filter f = l) (hr : (List.range' (lo+a) b).filter f = r) :
    (List.range' lo (a+b)).filter f = l++r := by
  rw [←List.range'_append_1,List.filter_append,hl,hr]

private theorem eval_delta (tab : ℕ → ℕ) (ps : List ℕ) (p n q old dec ans : ℕ)
    (le : p ≤ n) (sq : (p+1)^2 ≤ n) (div : n/p = q)
    (base : evalPhi tab ps n = old) (cut : evalPhi tab ps q = dec) (sub : old-dec=ans) :
    evalPhi tab (p::ps) n = ans := by
  rw [evalPhi,if_neg (not_lt.mpr le),if_neg (not_lt.mpr sq),div,base,cut,sub]

private theorem assemble {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id x) +
      (Nat.primesLE y).card = a)
    (rows : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (total : 1+r+b=a) : Nat.primeCounting x=r := by
  exact rank_of_parts hx hy cube sq zs sieved rows total

private def ps0 : List ℕ := []
private theorem agree0 (t : ℕ) : ps0.foldr advance id t = evalPhi WheelTableA94.fast ps0 t := rfl

private theorem value0 : evalPhi WheelTableA94.fast ps0 94085731 = 94085731 := rfl

private def ps1 : List ℕ := 2 :: ps0
private theorem row1 :
    ((List.range (2+1)).filter (fun n => decide n.Prime)).reverse = ps1 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 2 (by decide)]
  decide +kernel
private theorem agree1 : ∀ t, ps1.foldr advance id t = evalPhi WheelTableA94.fast ps1 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row1 agree0 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut1 : evalPhi WheelTableA94.fast ps0 47042865 = 47042865 := by decide +kernel
private theorem value1 : evalPhi WheelTableA94.fast ps1 94085731 = 47042866 :=
  eval_delta WheelTableA94.fast ps0 2 94085731 47042865 94085731 47042865 47042866
    (by decide) (by decide) rfl value0 cut1 rfl

private def ps2 : List ℕ := 3 :: ps1
private theorem row2 :
    ((List.range (3+1)).filter (fun n => decide n.Prime)).reverse = ps2 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 3 (by decide)]
  decide +kernel
private theorem agree2 : ∀ t, ps2.foldr advance id t = evalPhi WheelTableA94.fast ps2 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row2 agree1 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut2 : evalPhi WheelTableA94.fast ps1 31361910 = 15680955 := by decide +kernel
private theorem value2 : evalPhi WheelTableA94.fast ps2 94085731 = 31361911 :=
  eval_delta WheelTableA94.fast ps1 3 94085731 31361910 47042866 15680955 31361911
    (by decide) (by decide) rfl value1 cut2 rfl

private def ps3 : List ℕ := 5 :: ps2
private theorem row3 :
    ((List.range (5+1)).filter (fun n => decide n.Prime)).reverse = ps3 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 5 (by decide)]
  decide +kernel
private theorem agree3 : ∀ t, ps3.foldr advance id t = evalPhi WheelTableA94.fast ps3 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row3 agree2 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut3 : evalPhi WheelTableA94.fast ps2 18817146 = 6272382 := by decide +kernel
private theorem value3 : evalPhi WheelTableA94.fast ps3 94085731 = 25089529 :=
  eval_delta WheelTableA94.fast ps2 5 94085731 18817146 31361911 6272382 25089529
    (by decide) (by decide) rfl value2 cut3 rfl

private def ps4 : List ℕ := 7 :: ps3
private theorem row4 :
    ((List.range (7+1)).filter (fun n => decide n.Prime)).reverse = ps4 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 7 (by decide)]
  decide +kernel
private theorem agree4 : ∀ t, ps4.foldr advance id t = evalPhi WheelTableA94.fast ps4 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row4 agree3 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut4 : evalPhi WheelTableA94.fast ps3 13440818 = 3584218 := by decide +kernel
private theorem value4 : evalPhi WheelTableA94.fast ps4 94085731 = 21505311 :=
  eval_delta WheelTableA94.fast ps3 7 94085731 13440818 25089529 3584218 21505311
    (by decide) (by decide) rfl value3 cut4 rfl

private def ps5 : List ℕ := 11 :: ps4
private theorem row5 :
    ((List.range (11+1)).filter (fun n => decide n.Prime)).reverse = ps5 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 11 (by decide)]
  decide +kernel
private theorem agree5 : ∀ t, ps5.foldr advance id t = evalPhi WheelTableA94.fast ps5 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row5 agree4 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut5 : evalPhi WheelTableA94.fast ps4 8553248 = 1955028 := by decide +kernel
private theorem value5 : evalPhi WheelTableA94.fast ps5 94085731 = 19550283 :=
  eval_delta WheelTableA94.fast ps4 11 94085731 8553248 21505311 1955028 19550283
    (by decide) (by decide) rfl value4 cut5 rfl

private def ps6 : List ℕ := 13 :: ps5
private theorem row6 :
    ((List.range (13+1)).filter (fun n => decide n.Prime)).reverse = ps6 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 13 (by decide)]
  decide +kernel
private theorem agree6 : ∀ t, ps6.foldr advance id t = evalPhi WheelTableA94.fast ps6 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row6 agree5 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut6 : evalPhi WheelTableA94.fast ps5 7237363 = 1503868 := by decide +kernel
private theorem value6 : evalPhi WheelTableA94.fast ps6 94085731 = 18046415 :=
  eval_delta WheelTableA94.fast ps5 13 94085731 7237363 19550283 1503868 18046415
    (by decide) (by decide) rfl value5 cut6 rfl

private def ps7 : List ℕ := 17 :: ps6
private theorem row7 :
    ((List.range (17+1)).filter (fun n => decide n.Prime)).reverse = ps7 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 17 (by decide)]
  decide +kernel
private theorem agree7 : ∀ t, ps7.foldr advance id t = evalPhi WheelTableA94.fast ps7 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row7 agree6 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut7 : evalPhi WheelTableA94.fast ps6 5534454 = 1061555 := by decide +kernel
private theorem value7 : evalPhi WheelTableA94.fast ps7 94085731 = 16984860 :=
  eval_delta WheelTableA94.fast ps6 17 94085731 5534454 18046415 1061555 16984860
    (by decide) (by decide) rfl value6 cut7 rfl

private def ps8 : List ℕ := 19 :: ps7
private theorem row8 :
    ((List.range (19+1)).filter (fun n => decide n.Prime)).reverse = ps8 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 19 (by decide)]
  decide +kernel
private theorem agree8 : ∀ t, ps8.foldr advance id t = evalPhi WheelTableA94.fast ps8 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row8 agree7 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut8 : evalPhi WheelTableA94.fast ps7 4951880 = 893941 := by decide +kernel
private theorem value8 : evalPhi WheelTableA94.fast ps8 94085731 = 16090919 :=
  eval_delta WheelTableA94.fast ps7 19 94085731 4951880 16984860 893941 16090919
    (by decide) (by decide) rfl value7 cut8 rfl

private def ps9 : List ℕ := 23 :: ps8
private theorem row9 :
    ((List.range (23+1)).filter (fun n => decide n.Prime)).reverse = ps9 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 23 (by decide)]
  decide +kernel
private theorem agree9 : ∀ t, ps9.foldr advance id t = evalPhi WheelTableA94.fast ps9 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row9 agree8 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut9 : evalPhi WheelTableA94.fast ps8 4090683 = 699607 := by decide +kernel
private theorem value9 : evalPhi WheelTableA94.fast ps9 94085731 = 15391312 :=
  eval_delta WheelTableA94.fast ps8 23 94085731 4090683 16090919 699607 15391312
    (by decide) (by decide) rfl value8 cut9 rfl

private def ps10 : List ℕ := 29 :: ps9
private theorem row10 :
    ((List.range (29+1)).filter (fun n => decide n.Prime)).reverse = ps10 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 29 (by decide)]
  decide +kernel
private theorem agree10 : ∀ t, ps10.foldr advance id t = evalPhi WheelTableA94.fast ps10 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row10 agree9 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut10 : evalPhi WheelTableA94.fast ps9 3244335 = 530737 := by decide +kernel
private theorem value10 : evalPhi WheelTableA94.fast ps10 94085731 = 14860575 :=
  eval_delta WheelTableA94.fast ps9 29 94085731 3244335 15391312 530737 14860575
    (by decide) (by decide) rfl value9 cut10 rfl

private def ps11 : List ℕ := 31 :: ps10
private theorem row11 :
    ((List.range (31+1)).filter (fun n => decide n.Prime)).reverse = ps11 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 31 (by decide)]
  decide +kernel
private theorem agree11 : ∀ t, ps11.foldr advance id t = evalPhi WheelTableA94.fast ps11 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row11 agree10 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut11 : evalPhi WheelTableA94.fast ps10 3035023 = 479372 := by decide +kernel
private theorem value11 : evalPhi WheelTableA94.fast ps11 94085731 = 14381203 :=
  eval_delta WheelTableA94.fast ps10 31 94085731 3035023 14860575 479372 14381203
    (by decide) (by decide) rfl value10 cut11 rfl

private def ps12 : List ℕ := 37 :: ps11
private theorem row12 :
    ((List.range (37+1)).filter (fun n => decide n.Prime)).reverse = ps12 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 37 (by decide)]
  decide +kernel
private theorem agree12 : ∀ t, ps12.foldr advance id t = evalPhi WheelTableA94.fast ps12 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row12 agree11 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut12 : evalPhi WheelTableA94.fast ps11 2542857 = 388669 := by decide +kernel
private theorem value12 : evalPhi WheelTableA94.fast ps12 94085731 = 13992534 :=
  eval_delta WheelTableA94.fast ps11 37 94085731 2542857 14381203 388669 13992534
    (by decide) (by decide) rfl value11 cut12 rfl

private def ps13 : List ℕ := 41 :: ps12
private theorem row13 :
    ((List.range (41+1)).filter (fun n => decide n.Prime)).reverse = ps13 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 41 (by decide)]
  decide +kernel
private theorem agree13 : ∀ t, ps13.foldr advance id t = evalPhi WheelTableA94.fast ps13 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row13 agree12 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut13 : evalPhi WheelTableA94.fast ps12 2294773 = 341255 := by decide +kernel
private theorem value13 : evalPhi WheelTableA94.fast ps13 94085731 = 13651279 :=
  eval_delta WheelTableA94.fast ps12 41 94085731 2294773 13992534 341255 13651279
    (by decide) (by decide) rfl value12 cut13 rfl

private def ps14 : List ℕ := 43 :: ps13
private theorem row14 :
    ((List.range (43+1)).filter (fun n => decide n.Prime)).reverse = ps14 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 43 (by decide)]
  decide +kernel
private theorem agree14 : ∀ t, ps14.foldr advance id t = evalPhi WheelTableA94.fast ps14 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row14 agree13 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut14 : evalPhi WheelTableA94.fast ps13 2188040 = 317423 := by decide +kernel
private theorem value14 : evalPhi WheelTableA94.fast ps14 94085731 = 13333856 :=
  eval_delta WheelTableA94.fast ps13 43 94085731 2188040 13651279 317423 13333856
    (by decide) (by decide) rfl value13 cut14 rfl

private def ps15 : List ℕ := 47 :: ps14
private theorem row15 :
    ((List.range (47+1)).filter (fun n => decide n.Prime)).reverse = ps15 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 47 (by decide)]
  decide +kernel
private theorem agree15 : ∀ t, ps15.foldr advance id t = evalPhi WheelTableA94.fast ps15 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row15 agree14 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut15 : evalPhi WheelTableA94.fast ps14 2001824 = 283664 := by decide +kernel
private theorem value15 : evalPhi WheelTableA94.fast ps15 94085731 = 13050192 :=
  eval_delta WheelTableA94.fast ps14 47 94085731 2001824 13333856 283664 13050192
    (by decide) (by decide) rfl value14 cut15 rfl

private def ps16 : List ℕ := 53 :: ps15
private theorem row16 :
    ((List.range (53+1)).filter (fun n => decide n.Prime)).reverse = ps16 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 53 (by decide)]
  decide +kernel
private theorem agree16 : ∀ t, ps16.foldr advance id t = evalPhi WheelTableA94.fast ps16 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row16 agree15 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut16 : evalPhi WheelTableA94.fast ps15 1775202 = 246216 := by decide +kernel
private theorem value16 : evalPhi WheelTableA94.fast ps16 94085731 = 12803976 :=
  eval_delta WheelTableA94.fast ps15 53 94085731 1775202 13050192 246216 12803976
    (by decide) (by decide) rfl value15 cut16 rfl

private def ps17 : List ℕ := 59 :: ps16
private theorem row17 :
    ((List.range (59+1)).filter (fun n => decide n.Prime)).reverse = ps17 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 59 (by decide)]
  decide +kernel
private theorem agree17 : ∀ t, ps17.foldr advance id t = evalPhi WheelTableA94.fast ps17 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row17 agree16 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut17 : evalPhi WheelTableA94.fast ps16 1594673 = 217050 := by decide +kernel
private theorem value17 : evalPhi WheelTableA94.fast ps17 94085731 = 12586926 :=
  eval_delta WheelTableA94.fast ps16 59 94085731 1594673 12803976 217050 12586926
    (by decide) (by decide) rfl value16 cut17 rfl

private def ps18 : List ℕ := 61 :: ps17
private theorem row18 :
    ((List.range (61+1)).filter (fun n => decide n.Prime)).reverse = ps18 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 61 (by decide)]
  decide +kernel
private theorem agree18 : ∀ t, ps18.foldr advance id t = evalPhi WheelTableA94.fast ps18 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row18 agree17 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut18 : evalPhi WheelTableA94.fast ps17 1542389 = 206430 := by decide +kernel
private theorem value18 : evalPhi WheelTableA94.fast ps18 94085731 = 12380496 :=
  eval_delta WheelTableA94.fast ps17 61 94085731 1542389 12586926 206430 12380496
    (by decide) (by decide) rfl value17 cut18 rfl

private def ps19 : List ℕ := 67 :: ps18
private theorem row19 :
    ((List.range (67+1)).filter (fun n => decide n.Prime)).reverse = ps19 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 67 (by decide)]
  decide +kernel
private theorem agree19 : ∀ t, ps19.foldr advance id t = evalPhi WheelTableA94.fast ps19 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row19 agree18 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut19 : evalPhi WheelTableA94.fast ps18 1404264 = 184939 := by decide +kernel
private theorem value19 : evalPhi WheelTableA94.fast ps19 94085731 = 12195557 :=
  eval_delta WheelTableA94.fast ps18 67 94085731 1404264 12380496 184939 12195557
    (by decide) (by decide) rfl value18 cut19 rfl

private def ps20 : List ℕ := 71 :: ps19
private theorem row20 :
    ((List.range (71+1)).filter (fun n => decide n.Prime)).reverse = ps20 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 71 (by decide)]
  decide +kernel
private theorem agree20 : ∀ t, ps20.foldr advance id t = evalPhi WheelTableA94.fast ps20 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row20 agree19 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut20 : evalPhi WheelTableA94.fast ps19 1325151 = 172001 := by decide +kernel
private theorem value20 : evalPhi WheelTableA94.fast ps20 94085731 = 12023556 :=
  eval_delta WheelTableA94.fast ps19 71 94085731 1325151 12195557 172001 12023556
    (by decide) (by decide) rfl value19 cut20 rfl

private def ps21 : List ℕ := 73 :: ps20
private theorem row21 :
    ((List.range (73+1)).filter (fun n => decide n.Prime)).reverse = ps21 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 73 (by decide)]
  decide +kernel
private theorem agree21 : ∀ t, ps21.foldr advance id t = evalPhi WheelTableA94.fast ps21 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row21 agree20 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut21 : evalPhi WheelTableA94.fast ps20 1288845 = 165000 := by decide +kernel
private theorem value21 : evalPhi WheelTableA94.fast ps21 94085731 = 11858556 :=
  eval_delta WheelTableA94.fast ps20 73 94085731 1288845 12023556 165000 11858556
    (by decide) (by decide) rfl value20 cut21 rfl

private def ps22 : List ℕ := 79 :: ps21
private theorem row22 :
    ((List.range (79+1)).filter (fun n => decide n.Prime)).reverse = ps22 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 79 (by decide)]
  decide +kernel
private theorem agree22 : ∀ t, ps22.foldr advance id t = evalPhi WheelTableA94.fast ps22 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row22 agree21 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut22 : evalPhi WheelTableA94.fast ps21 1190958 = 150470 := by decide +kernel
private theorem value22 : evalPhi WheelTableA94.fast ps22 94085731 = 11708086 :=
  eval_delta WheelTableA94.fast ps21 79 94085731 1190958 11858556 150470 11708086
    (by decide) (by decide) rfl value21 cut22 rfl

private def ps23 : List ℕ := 83 :: ps22
private theorem row23 :
    ((List.range (83+1)).filter (fun n => decide n.Prime)).reverse = ps23 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 83 (by decide)]
  decide +kernel
private theorem agree23 : ∀ t, ps23.foldr advance id t = evalPhi WheelTableA94.fast ps23 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row23 agree22 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut23 : evalPhi WheelTableA94.fast ps22 1133563 = 141471 := by decide +kernel
private theorem value23 : evalPhi WheelTableA94.fast ps23 94085731 = 11566615 :=
  eval_delta WheelTableA94.fast ps22 83 94085731 1133563 11708086 141471 11566615
    (by decide) (by decide) rfl value22 cut23 rfl

private def ps24 : List ℕ := 89 :: ps23
private theorem row24 :
    ((List.range (89+1)).filter (fun n => decide n.Prime)).reverse = ps24 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 89 (by decide)]
  decide +kernel
private theorem agree24 : ∀ t, ps24.foldr advance id t = evalPhi WheelTableA94.fast ps24 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row24 agree23 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut24 : evalPhi WheelTableA94.fast ps23 1057143 = 130408 := by decide +kernel
private theorem value24 : evalPhi WheelTableA94.fast ps24 94085731 = 11436207 :=
  eval_delta WheelTableA94.fast ps23 89 94085731 1057143 11566615 130408 11436207
    (by decide) (by decide) rfl value23 cut24 rfl

private def ps25 : List ℕ := 97 :: ps24
private theorem row25 :
    ((List.range (97+1)).filter (fun n => decide n.Prime)).reverse = ps25 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 97 (by decide)]
  decide +kernel
private theorem agree25 : ∀ t, ps25.foldr advance id t = evalPhi WheelTableA94.fast ps25 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row25 agree24 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut25 : evalPhi WheelTableA94.fast ps24 969955 = 118343 := by decide +kernel
private theorem value25 : evalPhi WheelTableA94.fast ps25 94085731 = 11317864 :=
  eval_delta WheelTableA94.fast ps24 97 94085731 969955 11436207 118343 11317864
    (by decide) (by decide) rfl value24 cut25 rfl

private def ps26 : List ℕ := 101 :: ps25
private theorem row26 :
    ((List.range (101+1)).filter (fun n => decide n.Prime)).reverse = ps26 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 101 (by decide)]
  decide +kernel
private theorem agree26 : ∀ t, ps26.foldr advance id t = evalPhi WheelTableA94.fast ps26 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row26 agree25 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut26 : evalPhi WheelTableA94.fast ps25 931541 = 112492 := by decide +kernel
private theorem value26 : evalPhi WheelTableA94.fast ps26 94085731 = 11205372 :=
  eval_delta WheelTableA94.fast ps25 101 94085731 931541 11317864 112492 11205372
    (by decide) (by decide) rfl value25 cut26 rfl

private def ps27 : List ℕ := 103 :: ps26
private theorem row27 :
    ((List.range (103+1)).filter (fun n => decide n.Prime)).reverse = ps27 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 103 (by decide)]
  decide +kernel
private theorem agree27 : ∀ t, ps27.foldr advance id t = evalPhi WheelTableA94.fast ps27 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row27 agree26 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut27 : evalPhi WheelTableA94.fast ps26 913453 = 109207 := by decide +kernel
private theorem value27 : evalPhi WheelTableA94.fast ps27 94085731 = 11096165 :=
  eval_delta WheelTableA94.fast ps26 103 94085731 913453 11205372 109207 11096165
    (by decide) (by decide) rfl value26 cut27 rfl

private def ps28 : List ℕ := 107 :: ps27
private theorem row28 :
    ((List.range (107+1)).filter (fun n => decide n.Prime)).reverse = ps28 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 107 (by decide)]
  decide +kernel
private theorem agree28 : ∀ t, ps28.foldr advance id t = evalPhi WheelTableA94.fast ps28 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row28 agree27 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut28 : evalPhi WheelTableA94.fast ps27 879305 = 104081 := by decide +kernel
private theorem value28 : evalPhi WheelTableA94.fast ps28 94085731 = 10992084 :=
  eval_delta WheelTableA94.fast ps27 107 94085731 879305 11096165 104081 10992084
    (by decide) (by decide) rfl value27 cut28 rfl

private def ps29 : List ℕ := 109 :: ps28
private theorem row29 :
    ((List.range (109+1)).filter (fun n => decide n.Prime)).reverse = ps29 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 109 (by decide)]
  decide +kernel
private theorem agree29 : ∀ t, ps29.foldr advance id t = evalPhi WheelTableA94.fast ps29 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row29 agree28 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut29 : evalPhi WheelTableA94.fast ps28 863171 = 101171 := by decide +kernel
private theorem value29 : evalPhi WheelTableA94.fast ps29 94085731 = 10890913 :=
  eval_delta WheelTableA94.fast ps28 109 94085731 863171 10992084 101171 10890913
    (by decide) (by decide) rfl value28 cut29 rfl

private def ps30 : List ℕ := 113 :: ps29
private theorem row30 :
    ((List.range (113+1)).filter (fun n => decide n.Prime)).reverse = ps30 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 113 (by decide)]
  decide +kernel
private theorem agree30 : ∀ t, ps30.foldr advance id t = evalPhi WheelTableA94.fast ps30 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row30 agree29 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut30 : evalPhi WheelTableA94.fast ps29 832617 = 96640 := by decide +kernel
private theorem value30 : evalPhi WheelTableA94.fast ps30 94085731 = 10794273 :=
  eval_delta WheelTableA94.fast ps29 113 94085731 832617 10890913 96640 10794273
    (by decide) (by decide) rfl value29 cut30 rfl

private def ps31 : List ℕ := 127 :: ps30
private theorem row31 :
    ((List.range (127+1)).filter (fun n => decide n.Prime)).reverse = ps31 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 127 (by decide)]
  decide +kernel
private theorem agree31 : ∀ t, ps31.foldr advance id t = evalPhi WheelTableA94.fast ps31 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row31 agree30 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut31 : evalPhi WheelTableA94.fast ps30 740832 = 85101 := by decide +kernel
private theorem value31 : evalPhi WheelTableA94.fast ps31 94085731 = 10709172 :=
  eval_delta WheelTableA94.fast ps30 127 94085731 740832 10794273 85101 10709172
    (by decide) (by decide) rfl value30 cut31 rfl

private def ps32 : List ℕ := 131 :: ps31
private theorem row32 :
    ((List.range (131+1)).filter (fun n => decide n.Prime)).reverse = ps32 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 131 (by decide)]
  decide +kernel
private theorem agree32 : ∀ t, ps32.foldr advance id t = evalPhi WheelTableA94.fast ps32 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row32 agree31 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut32 : evalPhi WheelTableA94.fast ps31 718211 = 81770 := by decide +kernel
private theorem value32 : evalPhi WheelTableA94.fast ps32 94085731 = 10627402 :=
  eval_delta WheelTableA94.fast ps31 131 94085731 718211 10709172 81770 10627402
    (by decide) (by decide) rfl value31 cut32 rfl

private def ps33 : List ℕ := 137 :: ps32
private theorem row33 :
    ((List.range (137+1)).filter (fun n => decide n.Prime)).reverse = ps33 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 137 (by decide)]
  decide +kernel
private theorem agree33 : ∀ t, ps33.foldr advance id t = evalPhi WheelTableA94.fast ps33 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row33 agree32 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut33 : evalPhi WheelTableA94.fast ps32 686757 = 77487 := by decide +kernel
private theorem value33 : evalPhi WheelTableA94.fast ps33 94085731 = 10549915 :=
  eval_delta WheelTableA94.fast ps32 137 94085731 686757 10627402 77487 10549915
    (by decide) (by decide) rfl value32 cut33 rfl

private def ps34 : List ℕ := 139 :: ps33
private theorem row34 :
    ((List.range (139+1)).filter (fun n => decide n.Prime)).reverse = ps34 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 139 (by decide)]
  decide +kernel
private theorem agree34 : ∀ t, ps34.foldr advance id t = evalPhi WheelTableA94.fast ps34 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row34 agree33 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut34 : evalPhi WheelTableA94.fast ps33 676875 = 75731 := by decide +kernel
private theorem value34 : evalPhi WheelTableA94.fast ps34 94085731 = 10474184 :=
  eval_delta WheelTableA94.fast ps33 139 94085731 676875 10549915 75731 10474184
    (by decide) (by decide) rfl value33 cut34 rfl

private def ps35 : List ℕ := 149 :: ps34
private theorem row35 :
    ((List.range (149+1)).filter (fun n => decide n.Prime)).reverse = ps35 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 149 (by decide)]
  decide +kernel
private theorem agree35 : ∀ t, ps35.foldr advance id t = evalPhi WheelTableA94.fast ps35 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row35 agree34 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut35 : evalPhi WheelTableA94.fast ps34 631447 = 70001 := by decide +kernel
private theorem value35 : evalPhi WheelTableA94.fast ps35 94085731 = 10404183 :=
  eval_delta WheelTableA94.fast ps34 149 94085731 631447 10474184 70001 10404183
    (by decide) (by decide) rfl value34 cut35 rfl

private def ps36 : List ℕ := 151 :: ps35
private theorem row36 :
    ((List.range (151+1)).filter (fun n => decide n.Prime)).reverse = ps36 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 151 (by decide)]
  decide +kernel
private theorem agree36 : ∀ t, ps36.foldr advance id t = evalPhi WheelTableA94.fast ps36 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row36 agree35 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut36 : evalPhi WheelTableA94.fast ps35 623084 = 68547 := by decide +kernel
private theorem value36 : evalPhi WheelTableA94.fast ps36 94085731 = 10335636 :=
  eval_delta WheelTableA94.fast ps35 151 94085731 623084 10404183 68547 10335636
    (by decide) (by decide) rfl value35 cut36 rfl

private def ps37 : List ℕ := 157 :: ps36
private theorem row37 :
    ((List.range (157+1)).filter (fun n => decide n.Prime)).reverse = ps37 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 157 (by decide)]
  decide +kernel
private theorem agree37 : ∀ t, ps37.foldr advance id t = evalPhi WheelTableA94.fast ps37 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row37 agree36 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut37 : evalPhi WheelTableA94.fast ps36 599272 = 65371 := by decide +kernel
private theorem value37 : evalPhi WheelTableA94.fast ps37 94085731 = 10270265 :=
  eval_delta WheelTableA94.fast ps36 157 94085731 599272 10335636 65371 10270265
    (by decide) (by decide) rfl value36 cut37 rfl

private def ps38 : List ℕ := 163 :: ps37
private theorem row38 :
    ((List.range (163+1)).filter (fun n => decide n.Prime)).reverse = ps38 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 163 (by decide)]
  decide +kernel
private theorem agree38 : ∀ t, ps38.foldr advance id t = evalPhi WheelTableA94.fast ps38 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row38 agree37 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut38 : evalPhi WheelTableA94.fast ps37 577213 = 62458 := by decide +kernel
private theorem value38 : evalPhi WheelTableA94.fast ps38 94085731 = 10207807 :=
  eval_delta WheelTableA94.fast ps37 163 94085731 577213 10270265 62458 10207807
    (by decide) (by decide) rfl value37 cut38 rfl

private def ps39 : List ℕ := 167 :: ps38
private theorem row39 :
    ((List.range (167+1)).filter (fun n => decide n.Prime)).reverse = ps39 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 167 (by decide)]
  decide +kernel
private theorem agree39 : ∀ t, ps39.foldr advance id t = evalPhi WheelTableA94.fast ps39 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row39 agree38 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut39 : evalPhi WheelTableA94.fast ps38 563387 = 60485 := by decide +kernel
private theorem value39 : evalPhi WheelTableA94.fast ps39 94085731 = 10147322 :=
  eval_delta WheelTableA94.fast ps38 167 94085731 563387 10207807 60485 10147322
    (by decide) (by decide) rfl value38 cut39 rfl

private def ps40 : List ℕ := 173 :: ps39
private theorem row40 :
    ((List.range (173+1)).filter (fun n => decide n.Prime)).reverse = ps40 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 173 (by decide)]
  decide +kernel
private theorem agree40 : ∀ t, ps40.foldr advance id t = evalPhi WheelTableA94.fast ps40 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row40 agree39 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut40 : evalPhi WheelTableA94.fast ps39 543848 = 57944 := by decide +kernel
private theorem value40 : evalPhi WheelTableA94.fast ps40 94085731 = 10089378 :=
  eval_delta WheelTableA94.fast ps39 173 94085731 543848 10147322 57944 10089378
    (by decide) (by decide) rfl value39 cut40 rfl

private def ps41 : List ℕ := 179 :: ps40
private theorem row41 :
    ((List.range (179+1)).filter (fun n => decide n.Prime)).reverse = ps41 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 179 (by decide)]
  decide +kernel
private theorem agree41 : ∀ t, ps41.foldr advance id t = evalPhi WheelTableA94.fast ps41 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row41 agree40 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut41 : evalPhi WheelTableA94.fast ps40 525618 = 55577 := by decide +kernel
private theorem value41 : evalPhi WheelTableA94.fast ps41 94085731 = 10033801 :=
  eval_delta WheelTableA94.fast ps40 179 94085731 525618 10089378 55577 10033801
    (by decide) (by decide) rfl value40 cut41 rfl

private def ps42 : List ℕ := 181 :: ps41
private theorem row42 :
    ((List.range (181+1)).filter (fun n => decide n.Prime)).reverse = ps42 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 181 (by decide)]
  decide +kernel
private theorem agree42 : ∀ t, ps42.foldr advance id t = evalPhi WheelTableA94.fast ps42 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row42 agree41 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut42 : evalPhi WheelTableA94.fast ps41 519810 = 54570 := by decide +kernel
private theorem value42 : evalPhi WheelTableA94.fast ps42 94085731 = 9979231 :=
  eval_delta WheelTableA94.fast ps41 181 94085731 519810 10033801 54570 9979231
    (by decide) (by decide) rfl value41 cut42 rfl

private def ps43 : List ℕ := 191 :: ps42
private theorem row43 :
    ((List.range (191+1)).filter (fun n => decide n.Prime)).reverse = ps43 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 191 (by decide)]
  decide +kernel
private theorem agree43 : ∀ t, ps43.foldr advance id t = evalPhi WheelTableA94.fast ps43 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row43 agree42 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut43 : evalPhi WheelTableA94.fast ps42 492595 = 51297 := by decide +kernel
private theorem value43 : evalPhi WheelTableA94.fast ps43 94085731 = 9927934 :=
  eval_delta WheelTableA94.fast ps42 191 94085731 492595 9979231 51297 9927934
    (by decide) (by decide) rfl value42 cut43 rfl

private def ps44 : List ℕ := 193 :: ps43
private theorem row44 :
    ((List.range (193+1)).filter (fun n => decide n.Prime)).reverse = ps44 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 193 (by decide)]
  decide +kernel
private theorem agree44 : ∀ t, ps44.foldr advance id t = evalPhi WheelTableA94.fast ps44 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row44 agree43 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut44 : evalPhi WheelTableA94.fast ps43 487490 = 50422 := by decide +kernel
private theorem value44 : evalPhi WheelTableA94.fast ps44 94085731 = 9877512 :=
  eval_delta WheelTableA94.fast ps43 193 94085731 487490 9927934 50422 9877512
    (by decide) (by decide) rfl value43 cut44 rfl

private def ps45 : List ℕ := 197 :: ps44
private theorem row45 :
    ((List.range (197+1)).filter (fun n => decide n.Prime)).reverse = ps45 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 197 (by decide)]
  decide +kernel
private theorem agree45 : ∀ t, ps45.foldr advance id t = evalPhi WheelTableA94.fast ps45 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row45 agree44 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut45 : evalPhi WheelTableA94.fast ps44 477592 = 49069 := by decide +kernel
private theorem value45 : evalPhi WheelTableA94.fast ps45 94085731 = 9828443 :=
  eval_delta WheelTableA94.fast ps44 197 94085731 477592 9877512 49069 9828443
    (by decide) (by decide) rfl value44 cut45 rfl

private def ps46 : List ℕ := 199 :: ps45
private theorem row46 :
    ((List.range (199+1)).filter (fun n => decide n.Prime)).reverse = ps46 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 199 (by decide)]
  decide +kernel
private theorem agree46 : ∀ t, ps46.foldr advance id t = evalPhi WheelTableA94.fast ps46 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row46 agree45 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut46 : evalPhi WheelTableA94.fast ps45 472792 = 48240 := by decide +kernel
private theorem value46 : evalPhi WheelTableA94.fast ps46 94085731 = 9780203 :=
  eval_delta WheelTableA94.fast ps45 199 94085731 472792 9828443 48240 9780203
    (by decide) (by decide) rfl value45 cut46 rfl

private def ps47 : List ℕ := 211 :: ps46
private theorem row47 :
    ((List.range (211+1)).filter (fun n => decide n.Prime)).reverse = ps47 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 211 (by decide)]
  decide +kernel
private theorem agree47 : ∀ t, ps47.foldr advance id t = evalPhi WheelTableA94.fast ps47 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row47 agree46 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut47 : evalPhi WheelTableA94.fast ps46 445903 = 45174 := by decide +kernel
private theorem value47 : evalPhi WheelTableA94.fast ps47 94085731 = 9735029 :=
  eval_delta WheelTableA94.fast ps46 211 94085731 445903 9780203 45174 9735029
    (by decide) (by decide) rfl value46 cut47 rfl

private def ps48 : List ℕ := 223 :: ps47
private theorem row48 :
    ((List.range (223+1)).filter (fun n => decide n.Prime)).reverse = ps48 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 223 (by decide)]
  decide +kernel
private theorem agree48 : ∀ t, ps48.foldr advance id t = evalPhi WheelTableA94.fast ps48 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row48 agree47 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut48 : evalPhi WheelTableA94.fast ps47 421909 = 42418 := by decide +kernel
private theorem value48 : evalPhi WheelTableA94.fast ps48 94085731 = 9692611 :=
  eval_delta WheelTableA94.fast ps47 223 94085731 421909 9735029 42418 9692611
    (by decide) (by decide) rfl value47 cut48 rfl

private def ps49 : List ℕ := 227 :: ps48
private theorem row49 :
    ((List.range (227+1)).filter (fun n => decide n.Prime)).reverse = ps49 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 227 (by decide)]
  decide +kernel
private theorem agree49 : ∀ t, ps49.foldr advance id t = evalPhi WheelTableA94.fast ps49 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row49 agree48 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut49 : evalPhi WheelTableA94.fast ps48 414474 = 41420 := by decide +kernel
private theorem value49 : evalPhi WheelTableA94.fast ps49 94085731 = 9651191 :=
  eval_delta WheelTableA94.fast ps48 227 94085731 414474 9692611 41420 9651191
    (by decide) (by decide) rfl value48 cut49 rfl

private def ps50 : List ℕ := 229 :: ps49
private theorem row50 :
    ((List.range (229+1)).filter (fun n => decide n.Prime)).reverse = ps50 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 229 (by decide)]
  decide +kernel
private theorem agree50 : ∀ t, ps50.foldr advance id t = evalPhi WheelTableA94.fast ps50 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row50 agree49 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut50 : evalPhi WheelTableA94.fast ps49 410854 = 40825 := by decide +kernel
private theorem value50 : evalPhi WheelTableA94.fast ps50 94085731 = 9610366 :=
  eval_delta WheelTableA94.fast ps49 229 94085731 410854 9651191 40825 9610366
    (by decide) (by decide) rfl value49 cut50 rfl

private def ps51 : List ℕ := 233 :: ps50
private theorem row51 :
    ((List.range (233+1)).filter (fun n => decide n.Prime)).reverse = ps51 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 233 (by decide)]
  decide +kernel
private theorem agree51 : ∀ t, ps51.foldr advance id t = evalPhi WheelTableA94.fast ps51 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row51 agree50 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut51 : evalPhi WheelTableA94.fast ps50 403801 = 39876 := by decide +kernel
private theorem value51 : evalPhi WheelTableA94.fast ps51 94085731 = 9570490 :=
  eval_delta WheelTableA94.fast ps50 233 94085731 403801 9610366 39876 9570490
    (by decide) (by decide) rfl value50 cut51 rfl

private def ps52 : List ℕ := 239 :: ps51
private theorem row52 :
    ((List.range (239+1)).filter (fun n => decide n.Prime)).reverse = ps52 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 239 (by decide)]
  decide +kernel
private theorem agree52 : ∀ t, ps52.foldr advance id t = evalPhi WheelTableA94.fast ps52 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row52 agree51 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut52 : evalPhi WheelTableA94.fast ps51 393664 = 38658 := by decide +kernel
private theorem value52 : evalPhi WheelTableA94.fast ps52 94085731 = 9531832 :=
  eval_delta WheelTableA94.fast ps51 239 94085731 393664 9570490 38658 9531832
    (by decide) (by decide) rfl value51 cut52 rfl

private def ps53 : List ℕ := 241 :: ps52
private theorem row53 :
    ((List.range (241+1)).filter (fun n => decide n.Prime)).reverse = ps53 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 241 (by decide)]
  decide +kernel
private theorem agree53 : ∀ t, ps53.foldr advance id t = evalPhi WheelTableA94.fast ps53 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row53 agree52 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut53 : evalPhi WheelTableA94.fast ps52 390397 = 38111 := by decide +kernel
private theorem value53 : evalPhi WheelTableA94.fast ps53 94085731 = 9493721 :=
  eval_delta WheelTableA94.fast ps52 241 94085731 390397 9531832 38111 9493721
    (by decide) (by decide) rfl value52 cut53 rfl

private def ps54 : List ℕ := 251 :: ps53
private theorem row54 :
    ((List.range (251+1)).filter (fun n => decide n.Prime)).reverse = ps54 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 251 (by decide)]
  decide +kernel
private theorem agree54 : ∀ t, ps54.foldr advance id t = evalPhi WheelTableA94.fast ps54 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row54 agree53 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut54 : evalPhi WheelTableA94.fast ps53 374843 = 36367 := by decide +kernel
private theorem value54 : evalPhi WheelTableA94.fast ps54 94085731 = 9457354 :=
  eval_delta WheelTableA94.fast ps53 251 94085731 374843 9493721 36367 9457354
    (by decide) (by decide) rfl value53 cut54 rfl

private def ps55 : List ℕ := 257 :: ps54
private theorem row55 :
    ((List.range (257+1)).filter (fun n => decide n.Prime)).reverse = ps55 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 257 (by decide)]
  decide +kernel
private theorem agree55 : ∀ t, ps55.foldr advance id t = evalPhi WheelTableA94.fast ps55 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row55 agree54 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut55 : evalPhi WheelTableA94.fast ps54 366092 = 35334 := by decide +kernel
private theorem value55 : evalPhi WheelTableA94.fast ps55 94085731 = 9422020 :=
  eval_delta WheelTableA94.fast ps54 257 94085731 366092 9457354 35334 9422020
    (by decide) (by decide) rfl value54 cut55 rfl

private def ps56 : List ℕ := 263 :: ps55
private theorem row56 :
    ((List.range (263+1)).filter (fun n => decide n.Prime)).reverse = ps56 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 263 (by decide)]
  decide +kernel
private theorem agree56 : ∀ t, ps56.foldr advance id t = evalPhi WheelTableA94.fast ps56 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row56 agree55 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut56 : evalPhi WheelTableA94.fast ps55 357740 = 34359 := by decide +kernel
private theorem value56 : evalPhi WheelTableA94.fast ps56 94085731 = 9387661 :=
  eval_delta WheelTableA94.fast ps55 263 94085731 357740 9422020 34359 9387661
    (by decide) (by decide) rfl value55 cut56 rfl

private def ps57 : List ℕ := 269 :: ps56
private theorem row57 :
    ((List.range (269+1)).filter (fun n => decide n.Prime)).reverse = ps57 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 269 (by decide)]
  decide +kernel
private theorem agree57 : ∀ t, ps57.foldr advance id t = evalPhi WheelTableA94.fast ps57 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row57 agree56 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut57 : evalPhi WheelTableA94.fast ps56 349761 = 33414 := by decide +kernel
private theorem value57 : evalPhi WheelTableA94.fast ps57 94085731 = 9354247 :=
  eval_delta WheelTableA94.fast ps56 269 94085731 349761 9387661 33414 9354247
    (by decide) (by decide) rfl value56 cut57 rfl

private def ps58 : List ℕ := 271 :: ps57
private theorem row58 :
    ((List.range (271+1)).filter (fun n => decide n.Prime)).reverse = ps58 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 271 (by decide)]
  decide +kernel
private theorem agree58 : ∀ t, ps58.foldr advance id t = evalPhi WheelTableA94.fast ps58 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row58 agree57 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut58 : evalPhi WheelTableA94.fast ps57 347179 = 33012 := by decide +kernel
private theorem value58 : evalPhi WheelTableA94.fast ps58 94085731 = 9321235 :=
  eval_delta WheelTableA94.fast ps57 271 94085731 347179 9354247 33012 9321235
    (by decide) (by decide) rfl value57 cut58 rfl

private def ps59 : List ℕ := 277 :: ps58
private theorem row59 :
    ((List.range (277+1)).filter (fun n => decide n.Prime)).reverse = ps59 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 277 (by decide)]
  decide +kernel
private theorem agree59 : ∀ t, ps59.foldr advance id t = evalPhi WheelTableA94.fast ps59 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row59 agree58 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut59 : evalPhi WheelTableA94.fast ps58 339659 = 32131 := by decide +kernel
private theorem value59 : evalPhi WheelTableA94.fast ps59 94085731 = 9289104 :=
  eval_delta WheelTableA94.fast ps58 277 94085731 339659 9321235 32131 9289104
    (by decide) (by decide) rfl value58 cut59 rfl

private def ps60 : List ℕ := 281 :: ps59
private theorem row60 :
    ((List.range (281+1)).filter (fun n => decide n.Prime)).reverse = ps60 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 281 (by decide)]
  decide +kernel
private theorem agree60 : ∀ t, ps60.foldr advance id t = evalPhi WheelTableA94.fast ps60 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row60 agree59 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut60 : evalPhi WheelTableA94.fast ps59 334824 = 31529 := by decide +kernel
private theorem value60 : evalPhi WheelTableA94.fast ps60 94085731 = 9257575 :=
  eval_delta WheelTableA94.fast ps59 281 94085731 334824 9289104 31529 9257575
    (by decide) (by decide) rfl value59 cut60 rfl

private def ps61 : List ℕ := 283 :: ps60
private theorem row61 :
    ((List.range (283+1)).filter (fun n => decide n.Prime)).reverse = ps61 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 283 (by decide)]
  decide +kernel
private theorem agree61 : ∀ t, ps61.foldr advance id t = evalPhi WheelTableA94.fast ps61 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row61 agree60 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut61 : evalPhi WheelTableA94.fast ps60 332458 = 31171 := by decide +kernel
private theorem value61 : evalPhi WheelTableA94.fast ps61 94085731 = 9226404 :=
  eval_delta WheelTableA94.fast ps60 283 94085731 332458 9257575 31171 9226404
    (by decide) (by decide) rfl value60 cut61 rfl

private def ps62 : List ℕ := 293 :: ps61
private theorem row62 :
    ((List.range (293+1)).filter (fun n => decide n.Prime)).reverse = ps62 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 293 (by decide)]
  decide +kernel
private theorem agree62 : ∀ t, ps62.foldr advance id t = evalPhi WheelTableA94.fast ps62 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row62 agree61 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut62 : evalPhi WheelTableA94.fast ps61 321111 = 29952 := by decide +kernel
private theorem value62 : evalPhi WheelTableA94.fast ps62 94085731 = 9196452 :=
  eval_delta WheelTableA94.fast ps61 293 94085731 321111 9226404 29952 9196452
    (by decide) (by decide) rfl value61 cut62 rfl

private def ps63 : List ℕ := 307 :: ps62
private theorem row63 :
    ((List.range (307+1)).filter (fun n => decide n.Prime)).reverse = ps63 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 307 (by decide)]
  decide +kernel
private theorem agree63 : ∀ t, ps63.foldr advance id t = evalPhi WheelTableA94.fast ps63 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row63 agree62 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut63 : evalPhi WheelTableA94.fast ps62 306468 = 28447 := by decide +kernel
private theorem value63 : evalPhi WheelTableA94.fast ps63 94085731 = 9168005 :=
  eval_delta WheelTableA94.fast ps62 307 94085731 306468 9196452 28447 9168005
    (by decide) (by decide) rfl value62 cut63 rfl

private def ps64 : List ℕ := 311 :: ps63
private theorem row64 :
    ((List.range (311+1)).filter (fun n => decide n.Prime)).reverse = ps64 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 311 (by decide)]
  decide +kernel
private theorem agree64 : ∀ t, ps64.foldr advance id t = evalPhi WheelTableA94.fast ps64 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row64 agree63 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut64 : evalPhi WheelTableA94.fast ps63 302526 = 27961 := by decide +kernel
private theorem value64 : evalPhi WheelTableA94.fast ps64 94085731 = 9140044 :=
  eval_delta WheelTableA94.fast ps63 311 94085731 302526 9168005 27961 9140044
    (by decide) (by decide) rfl value63 cut64 rfl

private def ps65 : List ℕ := 313 :: ps64
private theorem row65 :
    ((List.range (313+1)).filter (fun n => decide n.Prime)).reverse = ps65 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 313 (by decide)]
  decide +kernel
private theorem agree65 : ∀ t, ps65.foldr advance id t = evalPhi WheelTableA94.fast ps65 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row65 agree64 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut65 : evalPhi WheelTableA94.fast ps64 300593 = 27676 := by decide +kernel
private theorem value65 : evalPhi WheelTableA94.fast ps65 94085731 = 9112368 :=
  eval_delta WheelTableA94.fast ps64 313 94085731 300593 9140044 27676 9112368
    (by decide) (by decide) rfl value64 cut65 rfl

private def ps66 : List ℕ := 317 :: ps65
private theorem row66 :
    ((List.range (317+1)).filter (fun n => decide n.Prime)).reverse = ps66 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 317 (by decide)]
  decide +kernel
private theorem agree66 : ∀ t, ps66.foldr advance id t = evalPhi WheelTableA94.fast ps66 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row66 agree65 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut66 : evalPhi WheelTableA94.fast ps65 296800 = 27239 := by decide +kernel
private theorem value66 : evalPhi WheelTableA94.fast ps66 94085731 = 9085129 :=
  eval_delta WheelTableA94.fast ps65 317 94085731 296800 9112368 27239 9085129
    (by decide) (by decide) rfl value65 cut66 rfl

private def ps67 : List ℕ := 331 :: ps66
private theorem row67 :
    ((List.range (331+1)).filter (fun n => decide n.Prime)).reverse = ps67 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 331 (by decide)]
  decide +kernel
private theorem agree67 : ∀ t, ps67.foldr advance id t = evalPhi WheelTableA94.fast ps67 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row67 agree66 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut67 : evalPhi WheelTableA94.fast ps66 284246 = 26012 := by decide +kernel
private theorem value67 : evalPhi WheelTableA94.fast ps67 94085731 = 9059117 :=
  eval_delta WheelTableA94.fast ps66 331 94085731 284246 9085129 26012 9059117
    (by decide) (by decide) rfl value66 cut67 rfl

private def ps68 : List ℕ := 337 :: ps67
private theorem row68 :
    ((List.range (337+1)).filter (fun n => decide n.Prime)).reverse = ps68 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 337 (by decide)]
  decide +kernel
private theorem agree68 : ∀ t, ps68.foldr advance id t = evalPhi WheelTableA94.fast ps68 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row68 agree67 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut68 : evalPhi WheelTableA94.fast ps67 279186 = 25466 := by decide +kernel
private theorem value68 : evalPhi WheelTableA94.fast ps68 94085731 = 9033651 :=
  eval_delta WheelTableA94.fast ps67 337 94085731 279186 9059117 25466 9033651
    (by decide) (by decide) rfl value67 cut68 rfl

private def ps69 : List ℕ := 347 :: ps68
private theorem row69 :
    ((List.range (347+1)).filter (fun n => decide n.Prime)).reverse = ps69 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 347 (by decide)]
  decide +kernel
private theorem agree69 : ∀ t, ps69.foldr advance id t = evalPhi WheelTableA94.fast ps69 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row69 agree68 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut69 : evalPhi WheelTableA94.fast ps68 271140 = 24664 := by decide +kernel
private theorem value69 : evalPhi WheelTableA94.fast ps69 94085731 = 9008987 :=
  eval_delta WheelTableA94.fast ps68 347 94085731 271140 9033651 24664 9008987
    (by decide) (by decide) rfl value68 cut69 rfl

private def ps70 : List ℕ := 349 :: ps69
private theorem row70 :
    ((List.range (349+1)).filter (fun n => decide n.Prime)).reverse = ps70 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 349 (by decide)]
  decide +kernel
private theorem agree70 : ∀ t, ps70.foldr advance id t = evalPhi WheelTableA94.fast ps70 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row70 agree69 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut70 : evalPhi WheelTableA94.fast ps69 269586 = 24457 := by decide +kernel
private theorem value70 : evalPhi WheelTableA94.fast ps70 94085731 = 8984530 :=
  eval_delta WheelTableA94.fast ps69 349 94085731 269586 9008987 24457 8984530
    (by decide) (by decide) rfl value69 cut70 rfl

private def ps71 : List ℕ := 353 :: ps70
private theorem row71 :
    ((List.range (353+1)).filter (fun n => decide n.Prime)).reverse = ps71 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 353 (by decide)]
  decide +kernel
private theorem agree71 : ∀ t, ps71.foldr advance id t = evalPhi WheelTableA94.fast ps71 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row71 agree70 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut71 : evalPhi WheelTableA94.fast ps70 266531 = 24102 := by decide +kernel
private theorem value71 : evalPhi WheelTableA94.fast ps71 94085731 = 8960428 :=
  eval_delta WheelTableA94.fast ps70 353 94085731 266531 8984530 24102 8960428
    (by decide) (by decide) rfl value70 cut71 rfl

private def ps72 : List ℕ := 359 :: ps71
private theorem row72 :
    ((List.range (359+1)).filter (fun n => decide n.Prime)).reverse = ps72 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 359 (by decide)]
  decide +kernel
private theorem agree72 : ∀ t, ps72.foldr advance id t = evalPhi WheelTableA94.fast ps72 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row72 agree71 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut72 : evalPhi WheelTableA94.fast ps71 262077 = 23634 := by decide +kernel
private theorem value72 : evalPhi WheelTableA94.fast ps72 94085731 = 8936794 :=
  eval_delta WheelTableA94.fast ps71 359 94085731 262077 8960428 23634 8936794
    (by decide) (by decide) rfl value71 cut72 rfl

private def ps73 : List ℕ := 367 :: ps72
private theorem row73 :
    ((List.range (367+1)).filter (fun n => decide n.Prime)).reverse = ps73 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 367 (by decide)]
  decide +kernel
private theorem agree73 : ∀ t, ps73.foldr advance id t = evalPhi WheelTableA94.fast ps73 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row73 agree72 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut73 : evalPhi WheelTableA94.fast ps72 256364 = 23084 := by decide +kernel
private theorem value73 : evalPhi WheelTableA94.fast ps73 94085731 = 8913710 :=
  eval_delta WheelTableA94.fast ps72 367 94085731 256364 8936794 23084 8913710
    (by decide) (by decide) rfl value72 cut73 rfl

private def ps74 : List ℕ := 373 :: ps73
private theorem row74 :
    ((List.range (373+1)).filter (fun n => decide n.Prime)).reverse = ps74 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 373 (by decide)]
  decide +kernel
private theorem agree74 : ∀ t, ps74.foldr advance id t = evalPhi WheelTableA94.fast ps74 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row74 agree73 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut74 : evalPhi WheelTableA94.fast ps73 252240 = 22666 := by decide +kernel
private theorem value74 : evalPhi WheelTableA94.fast ps74 94085731 = 8891044 :=
  eval_delta WheelTableA94.fast ps73 373 94085731 252240 8913710 22666 8891044
    (by decide) (by decide) rfl value73 cut74 rfl

private def ps75 : List ℕ := 379 :: ps74
private theorem row75 :
    ((List.range (379+1)).filter (fun n => decide n.Prime)).reverse = ps75 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 379 (by decide)]
  decide +kernel
private theorem agree75 : ∀ t, ps75.foldr advance id t = evalPhi WheelTableA94.fast ps75 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row75 agree74 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut75 : evalPhi WheelTableA94.fast ps74 248247 = 22263 := by decide +kernel
private theorem value75 : evalPhi WheelTableA94.fast ps75 94085731 = 8868781 :=
  eval_delta WheelTableA94.fast ps74 379 94085731 248247 8891044 22263 8868781
    (by decide) (by decide) rfl value74 cut75 rfl

private def ps76 : List ℕ := 383 :: ps75
private theorem row76 :
    ((List.range (383+1)).filter (fun n => decide n.Prime)).reverse = ps76 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 383 (by decide)]
  decide +kernel
private theorem agree76 : ∀ t, ps76.foldr advance id t = evalPhi WheelTableA94.fast ps76 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row76 agree75 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut76 : evalPhi WheelTableA94.fast ps75 245654 = 21986 := by decide +kernel
private theorem value76 : evalPhi WheelTableA94.fast ps76 94085731 = 8846795 :=
  eval_delta WheelTableA94.fast ps75 383 94085731 245654 8868781 21986 8846795
    (by decide) (by decide) rfl value75 cut76 rfl

private def ps77 : List ℕ := 389 :: ps76
private theorem row77 :
    ((List.range (389+1)).filter (fun n => decide n.Prime)).reverse = ps77 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 389 (by decide)]
  decide +kernel
private theorem agree77 : ∀ t, ps77.foldr advance id t = evalPhi WheelTableA94.fast ps77 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row77 agree76 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut77 : evalPhi WheelTableA94.fast ps76 241865 = 21614 := by decide +kernel
private theorem value77 : evalPhi WheelTableA94.fast ps77 94085731 = 8825181 :=
  eval_delta WheelTableA94.fast ps76 389 94085731 241865 8846795 21614 8825181
    (by decide) (by decide) rfl value76 cut77 rfl

private def ps78 : List ℕ := 397 :: ps77
private theorem row78 :
    ((List.range (397+1)).filter (fun n => decide n.Prime)).reverse = ps78 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 397 (by decide)]
  decide +kernel
private theorem agree78 : ∀ t, ps78.foldr advance id t = evalPhi WheelTableA94.fast ps78 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row78 agree77 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut78 : evalPhi WheelTableA94.fast ps77 236991 = 21151 := by decide +kernel
private theorem value78 : evalPhi WheelTableA94.fast ps78 94085731 = 8804030 :=
  eval_delta WheelTableA94.fast ps77 397 94085731 236991 8825181 21151 8804030
    (by decide) (by decide) rfl value77 cut78 rfl

private def ps79 : List ℕ := 401 :: ps78
private theorem row79 :
    ((List.range (401+1)).filter (fun n => decide n.Prime)).reverse = ps79 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 401 (by decide)]
  decide +kernel
private theorem agree79 : ∀ t, ps79.foldr advance id t = evalPhi WheelTableA94.fast ps79 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row79 agree78 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut79 : evalPhi WheelTableA94.fast ps78 234627 = 20927 := by decide +kernel
private theorem value79 : evalPhi WheelTableA94.fast ps79 94085731 = 8783103 :=
  eval_delta WheelTableA94.fast ps78 401 94085731 234627 8804030 20927 8783103
    (by decide) (by decide) rfl value78 cut79 rfl

private def ps80 : List ℕ := 409 :: ps79
private theorem row80 :
    ((List.range (409+1)).filter (fun n => decide n.Prime)).reverse = ps80 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 409 (by decide)]
  decide +kernel
private theorem agree80 : ∀ t, ps80.foldr advance id t = evalPhi WheelTableA94.fast ps80 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row80 agree79 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut80 : evalPhi WheelTableA94.fast ps79 230038 = 20520 := by decide +kernel
private theorem value80 : evalPhi WheelTableA94.fast ps80 94085731 = 8762583 :=
  eval_delta WheelTableA94.fast ps79 409 94085731 230038 8783103 20520 8762583
    (by decide) (by decide) rfl value79 cut80 rfl

private def ps81 : List ℕ := 419 :: ps80
private theorem row81 :
    ((List.range (419+1)).filter (fun n => decide n.Prime)).reverse = ps81 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 419 (by decide)]
  decide +kernel
private theorem agree81 : ∀ t, ps81.foldr advance id t = evalPhi WheelTableA94.fast ps81 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row81 agree80 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut81 : evalPhi WheelTableA94.fast ps80 224548 = 20020 := by decide +kernel
private theorem value81 : evalPhi WheelTableA94.fast ps81 94085731 = 8742563 :=
  eval_delta WheelTableA94.fast ps80 419 94085731 224548 8762583 20020 8742563
    (by decide) (by decide) rfl value80 cut81 rfl

private def ps82 : List ℕ := 421 :: ps81
private theorem row82 :
    ((List.range (421+1)).filter (fun n => decide n.Prime)).reverse = ps82 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 421 (by decide)]
  decide +kernel
private theorem agree82 : ∀ t, ps82.foldr advance id t = evalPhi WheelTableA94.fast ps82 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row82 agree81 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut82 : evalPhi WheelTableA94.fast ps81 223481 = 19915 := by decide +kernel
private theorem value82 : evalPhi WheelTableA94.fast ps82 94085731 = 8722648 :=
  eval_delta WheelTableA94.fast ps81 421 94085731 223481 8742563 19915 8722648
    (by decide) (by decide) rfl value81 cut82 rfl

private def ps83 : List ℕ := 431 :: ps82
private theorem row83 :
    ((List.range (431+1)).filter (fun n => decide n.Prime)).reverse = ps83 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 431 (by decide)]
  decide +kernel
private theorem agree83 : ∀ t, ps83.foldr advance id t = evalPhi WheelTableA94.fast ps83 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row83 agree82 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut83 : evalPhi WheelTableA94.fast ps82 218296 = 19447 := by decide +kernel
private theorem value83 : evalPhi WheelTableA94.fast ps83 94085731 = 8703201 :=
  eval_delta WheelTableA94.fast ps82 431 94085731 218296 8722648 19447 8703201
    (by decide) (by decide) rfl value82 cut83 rfl

private def ps84 : List ℕ := 433 :: ps83
private theorem row84 :
    ((List.range (433+1)).filter (fun n => decide n.Prime)).reverse = ps84 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 433 (by decide)]
  decide +kernel
private theorem agree84 : ∀ t, ps84.foldr advance id t = evalPhi WheelTableA94.fast ps84 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row84 agree83 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut84 : evalPhi WheelTableA94.fast ps83 217288 = 19348 := by decide +kernel
private theorem value84 : evalPhi WheelTableA94.fast ps84 94085731 = 8683853 :=
  eval_delta WheelTableA94.fast ps83 433 94085731 217288 8703201 19348 8683853
    (by decide) (by decide) rfl value83 cut84 rfl

private def ps85 : List ℕ := 439 :: ps84
private theorem row85 :
    ((List.range (439+1)).filter (fun n => decide n.Prime)).reverse = ps85 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 439 (by decide)]
  decide +kernel
private theorem agree85 : ∀ t, ps85.foldr advance id t = evalPhi WheelTableA94.fast ps85 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row85 agree84 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut85 : evalPhi WheelTableA94.fast ps84 214318 = 19099 := by decide +kernel
private theorem value85 : evalPhi WheelTableA94.fast ps85 94085731 = 8664754 :=
  eval_delta WheelTableA94.fast ps84 439 94085731 214318 8683853 19099 8664754
    (by decide) (by decide) rfl value84 cut85 rfl

private def ps86 : List ℕ := 443 :: ps85
private theorem row86 :
    ((List.range (443+1)).filter (fun n => decide n.Prime)).reverse = ps86 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 443 (by decide)]
  decide +kernel
private theorem agree86 : ∀ t, ps86.foldr advance id t = evalPhi WheelTableA94.fast ps86 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row86 agree85 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut86 : evalPhi WheelTableA94.fast ps85 212383 = 18932 := by decide +kernel
private theorem value86 : evalPhi WheelTableA94.fast ps86 94085731 = 8645822 :=
  eval_delta WheelTableA94.fast ps85 443 94085731 212383 8664754 18932 8645822
    (by decide) (by decide) rfl value85 cut86 rfl

private def ps87 : List ℕ := 449 :: ps86
private theorem row87 :
    ((List.range (449+1)).filter (fun n => decide n.Prime)).reverse = ps87 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 449 (by decide)]
  decide +kernel
private theorem agree87 : ∀ t, ps87.foldr advance id t = evalPhi WheelTableA94.fast ps87 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row87 agree86 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut87 : evalPhi WheelTableA94.fast ps86 209545 = 18685 := by decide +kernel
private theorem value87 : evalPhi WheelTableA94.fast ps87 94085731 = 8627137 :=
  eval_delta WheelTableA94.fast ps86 449 94085731 209545 8645822 18685 8627137
    (by decide) (by decide) rfl value86 cut87 rfl

private theorem last_row :
    ((List.range (454+1)).filter (fun n => decide n.Prime)).reverse = ps87 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 454 (by decide)]
  decide +kernel

private theorem left_part :
    (((List.range (454+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id 94085731) +
       (Nat.primesLE 454).card = 8627224 := by
  rw [last_row,agree87,value87,Nat.primesLE_card_eq_primeCounting,←WheelTableA94.fast_correct 454 (by decide)]
  decide +kernel

private def term (p : ℕ) : ℕ := if 454<p then WheelTableA94.fast (94085731/p) - WheelTableA94.fast (p-1) else 0

private def rr0_151 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149]
set_option maxRecDepth 3000 in
private theorem okrr0_151 : (List.range' 0 151).filter (primeBit WheelTableA94.fast) = rr0_151 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr0_151 : (rr0_151.map term).sum = 0 := by decide +kernel

private def rr151_303 : List ℕ := [151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293]
set_option maxRecDepth 3000 in
private theorem okrr151_303 : (List.range' 151 152).filter (primeBit WheelTableA94.fast) = rr151_303 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr151_303 : (rr151_303.map term).sum = 0 := by decide +kernel

private def rr0_303 : List ℕ := rr0_151 ++ rr151_303
set_option maxRecDepth 3000 in
private theorem okrr0_303 : (List.range' 0 303).filter (primeBit WheelTableA94.fast) = rr0_303 := merge_filter (primeBit WheelTableA94.fast) 0 151 152 rr0_151 rr151_303 okrr0_151 okrr151_303
set_option maxRecDepth 3000 in
private theorem vrr0_303 : (rr0_303.map term).sum = 0 := by rw [rr0_303,List.map_append,List.sum_append,vrr0_151,vrr151_303]

private def rr303_454 : List ℕ := [307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449]
set_option maxRecDepth 3000 in
private theorem okrr303_454 : (List.range' 303 151).filter (primeBit WheelTableA94.fast) = rr303_454 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr303_454 : (rr303_454.map term).sum = 0 := by decide +kernel

private def rr454_606 : List ℕ := [457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601]
set_option maxRecDepth 3000 in
private theorem okrr454_606 : (List.range' 454 152).filter (primeBit WheelTableA94.fast) = rr454_606 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr454_606 : (rr454_606.map term).sum = 372094 := by decide +kernel

private def rr303_606 : List ℕ := rr303_454 ++ rr454_606
set_option maxRecDepth 3000 in
private theorem okrr303_606 : (List.range' 303 303).filter (primeBit WheelTableA94.fast) = rr303_606 := merge_filter (primeBit WheelTableA94.fast) 303 151 152 rr303_454 rr454_606 okrr303_454 okrr454_606
set_option maxRecDepth 3000 in
private theorem vrr303_606 : (rr303_606.map term).sum = 372094 := by rw [rr303_606,List.map_append,List.sum_append,vrr303_454,vrr454_606]

private def rr0_606 : List ℕ := rr0_303 ++ rr303_606
set_option maxRecDepth 3000 in
private theorem okrr0_606 : (List.range' 0 606).filter (primeBit WheelTableA94.fast) = rr0_606 := merge_filter (primeBit WheelTableA94.fast) 0 303 303 rr0_303 rr303_606 okrr0_303 okrr303_606
set_option maxRecDepth 3000 in
private theorem vrr0_606 : (rr0_606.map term).sum = 372094 := by rw [rr0_606,List.map_append,List.sum_append,vrr0_303,vrr303_606]

private def rr606_757 : List ℕ := [607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751]
set_option maxRecDepth 3000 in
private theorem okrr606_757 : (List.range' 606 151).filter (primeBit WheelTableA94.fast) = rr606_757 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr606_757 : (rr606_757.map term).sum = 296099 := by decide +kernel

private def rr757_909 : List ℕ := [757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907]
set_option maxRecDepth 3000 in
private theorem okrr757_909 : (List.range' 757 152).filter (primeBit WheelTableA94.fast) = rr757_909 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr757_909 : (rr757_909.map term).sum = 233510 := by decide +kernel

private def rr606_909 : List ℕ := rr606_757 ++ rr757_909
set_option maxRecDepth 3000 in
private theorem okrr606_909 : (List.range' 606 303).filter (primeBit WheelTableA94.fast) = rr606_909 := merge_filter (primeBit WheelTableA94.fast) 606 151 152 rr606_757 rr757_909 okrr606_757 okrr757_909
set_option maxRecDepth 3000 in
private theorem vrr606_909 : (rr606_909.map term).sum = 529609 := by rw [rr606_909,List.map_append,List.sum_append,vrr606_757,vrr757_909]

private def rr909_1060 : List ℕ := [911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051]
set_option maxRecDepth 3000 in
private theorem okrr909_1060 : (List.range' 909 151).filter (primeBit WheelTableA94.fast) = rr909_1060 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr909_1060 : (rr909_1060.map term).sum = 198946 := by decide +kernel

private def rr1060_1212 : List ℕ := [1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201]
set_option maxRecDepth 3000 in
private theorem okrr1060_1212 : (List.range' 1060 152).filter (primeBit WheelTableA94.fast) = rr1060_1212 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1060_1212 : (rr1060_1212.map term).sum = 159338 := by decide +kernel

private def rr909_1212 : List ℕ := rr909_1060 ++ rr1060_1212
set_option maxRecDepth 3000 in
private theorem okrr909_1212 : (List.range' 909 303).filter (primeBit WheelTableA94.fast) = rr909_1212 := merge_filter (primeBit WheelTableA94.fast) 909 151 152 rr909_1060 rr1060_1212 okrr909_1060 okrr1060_1212
set_option maxRecDepth 3000 in
private theorem vrr909_1212 : (rr909_1212.map term).sum = 358284 := by rw [rr909_1212,List.map_append,List.sum_append,vrr909_1060,vrr1060_1212]

private def rr606_1212 : List ℕ := rr606_909 ++ rr909_1212
set_option maxRecDepth 3000 in
private theorem okrr606_1212 : (List.range' 606 606).filter (primeBit WheelTableA94.fast) = rr606_1212 := merge_filter (primeBit WheelTableA94.fast) 606 303 303 rr606_909 rr909_1212 okrr606_909 okrr909_1212
set_option maxRecDepth 3000 in
private theorem vrr606_1212 : (rr606_1212.map term).sum = 887893 := by rw [rr606_1212,List.map_append,List.sum_append,vrr606_909,vrr909_1212]

private def rr0_1212 : List ℕ := rr0_606 ++ rr606_1212
set_option maxRecDepth 3000 in
private theorem okrr0_1212 : (List.range' 0 1212).filter (primeBit WheelTableA94.fast) = rr0_1212 := merge_filter (primeBit WheelTableA94.fast) 0 606 606 rr0_606 rr606_1212 okrr0_606 okrr606_1212
set_option maxRecDepth 3000 in
private theorem vrr0_1212 : (rr0_1212.map term).sum = 1259987 := by rw [rr0_1212,List.map_append,List.sum_append,vrr0_606,vrr606_1212]

private def rr1212_1363 : List ℕ := [1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361]
set_option maxRecDepth 3000 in
private theorem okrr1212_1363 : (List.range' 1212 151).filter (primeBit WheelTableA94.fast) = rr1212_1363 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1212_1363 : (rr1212_1363.map term).sum = 148558 := by decide +kernel

private def rr1363_1515 : List ℕ := [1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511]
set_option maxRecDepth 3000 in
private theorem okrr1363_1515 : (List.range' 1363 152).filter (primeBit WheelTableA94.fast) = rr1363_1515 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1363_1515 : (rr1363_1515.map term).sum = 138199 := by decide +kernel

private def rr1212_1515 : List ℕ := rr1212_1363 ++ rr1363_1515
set_option maxRecDepth 3000 in
private theorem okrr1212_1515 : (List.range' 1212 303).filter (primeBit WheelTableA94.fast) = rr1212_1515 := merge_filter (primeBit WheelTableA94.fast) 1212 151 152 rr1212_1363 rr1363_1515 okrr1212_1363 okrr1363_1515
set_option maxRecDepth 3000 in
private theorem vrr1212_1515 : (rr1212_1515.map term).sum = 286757 := by rw [rr1212_1515,List.map_append,List.sum_append,vrr1212_1363,vrr1363_1515]

private def rr1515_1666 : List ℕ := [1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663]
set_option maxRecDepth 3000 in
private theorem okrr1515_1666 : (List.range' 1515 151).filter (primeBit WheelTableA94.fast) = rr1515_1666 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1515_1666 : (rr1515_1666.map term).sum = 120336 := by decide +kernel

private def rr1666_1818 : List ℕ := [1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811]
set_option maxRecDepth 3000 in
private theorem okrr1666_1818 : (List.range' 1666 152).filter (primeBit WheelTableA94.fast) = rr1666_1818 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1666_1818 : (rr1666_1818.map term).sum = 99531 := by decide +kernel

private def rr1515_1818 : List ℕ := rr1515_1666 ++ rr1666_1818
set_option maxRecDepth 3000 in
private theorem okrr1515_1818 : (List.range' 1515 303).filter (primeBit WheelTableA94.fast) = rr1515_1818 := merge_filter (primeBit WheelTableA94.fast) 1515 151 152 rr1515_1666 rr1666_1818 okrr1515_1666 okrr1666_1818
set_option maxRecDepth 3000 in
private theorem vrr1515_1818 : (rr1515_1818.map term).sum = 219867 := by rw [rr1515_1818,List.map_append,List.sum_append,vrr1515_1666,vrr1666_1818]

private def rr1212_1818 : List ℕ := rr1212_1515 ++ rr1515_1818
set_option maxRecDepth 3000 in
private theorem okrr1212_1818 : (List.range' 1212 606).filter (primeBit WheelTableA94.fast) = rr1212_1818 := merge_filter (primeBit WheelTableA94.fast) 1212 303 303 rr1212_1515 rr1515_1818 okrr1212_1515 okrr1515_1818
set_option maxRecDepth 3000 in
private theorem vrr1212_1818 : (rr1212_1818.map term).sum = 506624 := by rw [rr1212_1818,List.map_append,List.sum_append,vrr1212_1515,vrr1515_1818]

private def rr1818_1969 : List ℕ := [1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951]
set_option maxRecDepth 3000 in
private theorem okrr1818_1969 : (List.range' 1818 151).filter (primeBit WheelTableA94.fast) = rr1818_1969 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1818_1969 : (rr1818_1969.map term).sum = 82090 := by decide +kernel

private def rr1969_2121 : List ℕ := [1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113]
set_option maxRecDepth 3000 in
private theorem okrr1969_2121 : (List.range' 1969 152).filter (primeBit WheelTableA94.fast) = rr1969_2121 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1969_2121 : (rr1969_2121.map term).sum = 98226 := by decide +kernel

private def rr1818_2121 : List ℕ := rr1818_1969 ++ rr1969_2121
set_option maxRecDepth 3000 in
private theorem okrr1818_2121 : (List.range' 1818 303).filter (primeBit WheelTableA94.fast) = rr1818_2121 := merge_filter (primeBit WheelTableA94.fast) 1818 151 152 rr1818_1969 rr1969_2121 okrr1818_1969 okrr1969_2121
set_option maxRecDepth 3000 in
private theorem vrr1818_2121 : (rr1818_2121.map term).sum = 180316 := by rw [rr1818_2121,List.map_append,List.sum_append,vrr1818_1969,vrr1969_2121]

private def rr2121_2273 : List ℕ := [2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269]
set_option maxRecDepth 3000 in
private theorem okrr2121_2273 : (List.range' 2121 152).filter (primeBit WheelTableA94.fast) = rr2121_2273 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2121_2273 : (rr2121_2273.map term).sum = 74632 := by decide +kernel

private def rr2273_2425 : List ℕ := [2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423]
set_option maxRecDepth 3000 in
private theorem okrr2273_2425 : (List.range' 2273 152).filter (primeBit WheelTableA94.fast) = rr2273_2425 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2273_2425 : (rr2273_2425.map term).sum = 88710 := by decide +kernel

private def rr2121_2425 : List ℕ := rr2121_2273 ++ rr2273_2425
set_option maxRecDepth 3000 in
private theorem okrr2121_2425 : (List.range' 2121 304).filter (primeBit WheelTableA94.fast) = rr2121_2425 := merge_filter (primeBit WheelTableA94.fast) 2121 152 152 rr2121_2273 rr2273_2425 okrr2121_2273 okrr2273_2425
set_option maxRecDepth 3000 in
private theorem vrr2121_2425 : (rr2121_2425.map term).sum = 163342 := by rw [rr2121_2425,List.map_append,List.sum_append,vrr2121_2273,vrr2273_2425]

private def rr1818_2425 : List ℕ := rr1818_2121 ++ rr2121_2425
set_option maxRecDepth 3000 in
private theorem okrr1818_2425 : (List.range' 1818 607).filter (primeBit WheelTableA94.fast) = rr1818_2425 := merge_filter (primeBit WheelTableA94.fast) 1818 303 304 rr1818_2121 rr2121_2425 okrr1818_2121 okrr2121_2425
set_option maxRecDepth 3000 in
private theorem vrr1818_2425 : (rr1818_2425.map term).sum = 343658 := by rw [rr1818_2425,List.map_append,List.sum_append,vrr1818_2121,vrr2121_2425]

private def rr1212_2425 : List ℕ := rr1212_1818 ++ rr1818_2425
set_option maxRecDepth 3000 in
private theorem okrr1212_2425 : (List.range' 1212 1213).filter (primeBit WheelTableA94.fast) = rr1212_2425 := merge_filter (primeBit WheelTableA94.fast) 1212 606 607 rr1212_1818 rr1818_2425 okrr1212_1818 okrr1818_2425
set_option maxRecDepth 3000 in
private theorem vrr1212_2425 : (rr1212_2425.map term).sum = 850282 := by rw [rr1212_2425,List.map_append,List.sum_append,vrr1212_1818,vrr1818_2425]

private def rr0_2425 : List ℕ := rr0_1212 ++ rr1212_2425
set_option maxRecDepth 3000 in
private theorem okrr0_2425 : (List.range' 0 2425).filter (primeBit WheelTableA94.fast) = rr0_2425 := merge_filter (primeBit WheelTableA94.fast) 0 1212 1213 rr0_1212 rr1212_2425 okrr0_1212 okrr1212_2425
set_option maxRecDepth 3000 in
private theorem vrr0_2425 : (rr0_2425.map term).sum = 2110269 := by rw [rr0_2425,List.map_append,List.sum_append,vrr0_1212,vrr1212_2425]

private def rr2425_2576 : List ℕ := [2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557]
set_option maxRecDepth 3000 in
private theorem okrr2425_2576 : (List.range' 2425 151).filter (primeBit WheelTableA94.fast) = rr2425_2576 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2425_2576 : (rr2425_2576.map term).sum = 54220 := by decide +kernel

private def rr2576_2728 : List ℕ := [2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719]
set_option maxRecDepth 3000 in
private theorem okrr2576_2728 : (List.range' 2576 152).filter (primeBit WheelTableA94.fast) = rr2576_2728 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2576_2728 : (rr2576_2728.map term).sum = 74403 := by decide +kernel

private def rr2425_2728 : List ℕ := rr2425_2576 ++ rr2576_2728
set_option maxRecDepth 3000 in
private theorem okrr2425_2728 : (List.range' 2425 303).filter (primeBit WheelTableA94.fast) = rr2425_2728 := merge_filter (primeBit WheelTableA94.fast) 2425 151 152 rr2425_2576 rr2576_2728 okrr2425_2576 okrr2576_2728
set_option maxRecDepth 3000 in
private theorem vrr2425_2728 : (rr2425_2728.map term).sum = 128623 := by rw [rr2425_2728,List.map_append,List.sum_append,vrr2425_2576,vrr2576_2728]

private def rr2728_2879 : List ℕ := [2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861]
set_option maxRecDepth 3000 in
private theorem okrr2728_2879 : (List.range' 2728 151).filter (primeBit WheelTableA94.fast) = rr2728_2879 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2728_2879 : (rr2728_2879.map term).sum = 60728 := by decide +kernel

private def rr2879_3031 : List ℕ := [2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023]
set_option maxRecDepth 3000 in
private theorem okrr2879_3031 : (List.range' 2879 152).filter (primeBit WheelTableA94.fast) = rr2879_3031 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2879_3031 : (rr2879_3031.map term).sum = 54042 := by decide +kernel

private def rr2728_3031 : List ℕ := rr2728_2879 ++ rr2879_3031
set_option maxRecDepth 3000 in
private theorem okrr2728_3031 : (List.range' 2728 303).filter (primeBit WheelTableA94.fast) = rr2728_3031 := merge_filter (primeBit WheelTableA94.fast) 2728 151 152 rr2728_2879 rr2879_3031 okrr2728_2879 okrr2879_3031
set_option maxRecDepth 3000 in
private theorem vrr2728_3031 : (rr2728_3031.map term).sum = 114770 := by rw [rr2728_3031,List.map_append,List.sum_append,vrr2728_2879,vrr2879_3031]

private def rr2425_3031 : List ℕ := rr2425_2728 ++ rr2728_3031
set_option maxRecDepth 3000 in
private theorem okrr2425_3031 : (List.range' 2425 606).filter (primeBit WheelTableA94.fast) = rr2425_3031 := merge_filter (primeBit WheelTableA94.fast) 2425 303 303 rr2425_2728 rr2728_3031 okrr2425_2728 okrr2728_3031
set_option maxRecDepth 3000 in
private theorem vrr2425_3031 : (rr2425_3031.map term).sum = 243393 := by rw [rr2425_3031,List.map_append,List.sum_append,vrr2425_2728,vrr2728_3031]

private def rr3031_3182 : List ℕ := [3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181]
set_option maxRecDepth 3000 in
private theorem okrr3031_3182 : (List.range' 3031 151).filter (primeBit WheelTableA94.fast) = rr3031_3182 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3031_3182 : (rr3031_3182.map term).sum = 45358 := by decide +kernel

private def rr3182_3334 : List ℕ := [3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331]
set_option maxRecDepth 3000 in
private theorem okrr3182_3334 : (List.range' 3182 152).filter (primeBit WheelTableA94.fast) = rr3182_3334 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3182_3334 : (rr3182_3334.map term).sum = 53543 := by decide +kernel

private def rr3031_3334 : List ℕ := rr3031_3182 ++ rr3182_3334
set_option maxRecDepth 3000 in
private theorem okrr3031_3334 : (List.range' 3031 303).filter (primeBit WheelTableA94.fast) = rr3031_3334 := merge_filter (primeBit WheelTableA94.fast) 3031 151 152 rr3031_3182 rr3182_3334 okrr3031_3182 okrr3182_3334
set_option maxRecDepth 3000 in
private theorem vrr3031_3334 : (rr3031_3334.map term).sum = 98901 := by rw [rr3031_3334,List.map_append,List.sum_append,vrr3031_3182,vrr3182_3334]

private def rr3334_3485 : List ℕ := [3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469]
set_option maxRecDepth 3000 in
private theorem okrr3334_3485 : (List.range' 3334 151).filter (primeBit WheelTableA94.fast) = rr3334_3485 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3334_3485 : (rr3334_3485.map term).sum = 43148 := by decide +kernel

private def rr3485_3637 : List ℕ := [3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631]
set_option maxRecDepth 3000 in
private theorem okrr3485_3637 : (List.range' 3485 152).filter (primeBit WheelTableA94.fast) = rr3485_3637 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3485_3637 : (rr3485_3637.map term).sum = 50503 := by decide +kernel

private def rr3334_3637 : List ℕ := rr3334_3485 ++ rr3485_3637
set_option maxRecDepth 3000 in
private theorem okrr3334_3637 : (List.range' 3334 303).filter (primeBit WheelTableA94.fast) = rr3334_3637 := merge_filter (primeBit WheelTableA94.fast) 3334 151 152 rr3334_3485 rr3485_3637 okrr3334_3485 okrr3485_3637
set_option maxRecDepth 3000 in
private theorem vrr3334_3637 : (rr3334_3637.map term).sum = 93651 := by rw [rr3334_3637,List.map_append,List.sum_append,vrr3334_3485,vrr3485_3637]

private def rr3031_3637 : List ℕ := rr3031_3334 ++ rr3334_3637
set_option maxRecDepth 3000 in
private theorem okrr3031_3637 : (List.range' 3031 606).filter (primeBit WheelTableA94.fast) = rr3031_3637 := merge_filter (primeBit WheelTableA94.fast) 3031 303 303 rr3031_3334 rr3334_3637 okrr3031_3334 okrr3334_3637
set_option maxRecDepth 3000 in
private theorem vrr3031_3637 : (rr3031_3637.map term).sum = 192552 := by rw [rr3031_3637,List.map_append,List.sum_append,vrr3031_3334,vrr3334_3637]

private def rr2425_3637 : List ℕ := rr2425_3031 ++ rr3031_3637
set_option maxRecDepth 3000 in
private theorem okrr2425_3637 : (List.range' 2425 1212).filter (primeBit WheelTableA94.fast) = rr2425_3637 := merge_filter (primeBit WheelTableA94.fast) 2425 606 606 rr2425_3031 rr3031_3637 okrr2425_3031 okrr3031_3637
set_option maxRecDepth 3000 in
private theorem vrr2425_3637 : (rr2425_3637.map term).sum = 435945 := by rw [rr2425_3637,List.map_append,List.sum_append,vrr2425_3031,vrr3031_3637]

private def rr3637_3788 : List ℕ := [3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779]
set_option maxRecDepth 3000 in
private theorem okrr3637_3788 : (List.range' 3637 151).filter (primeBit WheelTableA94.fast) = rr3637_3788 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3637_3788 : (rr3637_3788.map term).sum = 41057 := by decide +kernel

private def rr3788_3940 : List ℕ := [3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931]
set_option maxRecDepth 3000 in
private theorem okrr3788_3940 : (List.range' 3788 152).filter (primeBit WheelTableA94.fast) = rr3788_3940 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3788_3940 : (rr3788_3940.map term).sum = 43300 := by decide +kernel

private def rr3637_3940 : List ℕ := rr3637_3788 ++ rr3788_3940
set_option maxRecDepth 3000 in
private theorem okrr3637_3940 : (List.range' 3637 303).filter (primeBit WheelTableA94.fast) = rr3637_3940 := merge_filter (primeBit WheelTableA94.fast) 3637 151 152 rr3637_3788 rr3788_3940 okrr3637_3788 okrr3788_3940
set_option maxRecDepth 3000 in
private theorem vrr3637_3940 : (rr3637_3940.map term).sum = 84357 := by rw [rr3637_3940,List.map_append,List.sum_append,vrr3637_3788,vrr3788_3940]

private def rr3940_4091 : List ℕ := [3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079]
set_option maxRecDepth 3000 in
private theorem okrr3940_4091 : (List.range' 3940 151).filter (primeBit WheelTableA94.fast) = rr3940_4091 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3940_4091 : (rr3940_4091.map term).sum = 32900 := by decide +kernel

private def rr4091_4243 : List ℕ := [4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241]
set_option maxRecDepth 3000 in
private theorem okrr4091_4243 : (List.range' 4091 152).filter (primeBit WheelTableA94.fast) = rr4091_4243 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4091_4243 : (rr4091_4243.map term).sum = 37143 := by decide +kernel

private def rr3940_4243 : List ℕ := rr3940_4091 ++ rr4091_4243
set_option maxRecDepth 3000 in
private theorem okrr3940_4243 : (List.range' 3940 303).filter (primeBit WheelTableA94.fast) = rr3940_4243 := merge_filter (primeBit WheelTableA94.fast) 3940 151 152 rr3940_4091 rr4091_4243 okrr3940_4091 okrr4091_4243
set_option maxRecDepth 3000 in
private theorem vrr3940_4243 : (rr3940_4243.map term).sum = 70043 := by rw [rr3940_4243,List.map_append,List.sum_append,vrr3940_4091,vrr4091_4243]

private def rr3637_4243 : List ℕ := rr3637_3940 ++ rr3940_4243
set_option maxRecDepth 3000 in
private theorem okrr3637_4243 : (List.range' 3637 606).filter (primeBit WheelTableA94.fast) = rr3637_4243 := merge_filter (primeBit WheelTableA94.fast) 3637 303 303 rr3637_3940 rr3940_4243 okrr3637_3940 okrr3940_4243
set_option maxRecDepth 3000 in
private theorem vrr3637_4243 : (rr3637_4243.map term).sum = 154400 := by rw [rr3637_4243,List.map_append,List.sum_append,vrr3637_3940,vrr3940_4243]

private def rr4243_4394 : List ℕ := [4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391]
set_option maxRecDepth 3000 in
private theorem okrr4243_4394 : (List.range' 4243 151).filter (primeBit WheelTableA94.fast) = rr4243_4394 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4243_4394 : (rr4243_4394.map term).sum = 31610 := by decide +kernel

private def rr4394_4546 : List ℕ := [4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523]
set_option maxRecDepth 3000 in
private theorem okrr4394_4546 : (List.range' 4394 152).filter (primeBit WheelTableA94.fast) = rr4394_4546 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4394_4546 : (rr4394_4546.map term).sum = 29946 := by decide +kernel

private def rr4243_4546 : List ℕ := rr4243_4394 ++ rr4394_4546
set_option maxRecDepth 3000 in
private theorem okrr4243_4546 : (List.range' 4243 303).filter (primeBit WheelTableA94.fast) = rr4243_4546 := merge_filter (primeBit WheelTableA94.fast) 4243 151 152 rr4243_4394 rr4394_4546 okrr4243_4394 okrr4394_4546
set_option maxRecDepth 3000 in
private theorem vrr4243_4546 : (rr4243_4546.map term).sum = 61556 := by rw [rr4243_4546,List.map_append,List.sum_append,vrr4243_4394,vrr4394_4546]

private def rr4546_4698 : List ℕ := [4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691]
set_option maxRecDepth 3000 in
private theorem okrr4546_4698 : (List.range' 4546 152).filter (primeBit WheelTableA94.fast) = rr4546_4698 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4546_4698 : (rr4546_4698.map term).sum = 31831 := by decide +kernel

private def rr4698_4850 : List ℕ := [4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831]
set_option maxRecDepth 3000 in
private theorem okrr4698_4850 : (List.range' 4698 152).filter (primeBit WheelTableA94.fast) = rr4698_4850 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4698_4850 : (rr4698_4850.map term).sum = 25469 := by decide +kernel

private def rr4546_4850 : List ℕ := rr4546_4698 ++ rr4698_4850
set_option maxRecDepth 3000 in
private theorem okrr4546_4850 : (List.range' 4546 304).filter (primeBit WheelTableA94.fast) = rr4546_4850 := merge_filter (primeBit WheelTableA94.fast) 4546 152 152 rr4546_4698 rr4698_4850 okrr4546_4698 okrr4698_4850
set_option maxRecDepth 3000 in
private theorem vrr4546_4850 : (rr4546_4850.map term).sum = 57300 := by rw [rr4546_4850,List.map_append,List.sum_append,vrr4546_4698,vrr4698_4850]

private def rr4243_4850 : List ℕ := rr4243_4546 ++ rr4546_4850
set_option maxRecDepth 3000 in
private theorem okrr4243_4850 : (List.range' 4243 607).filter (primeBit WheelTableA94.fast) = rr4243_4850 := merge_filter (primeBit WheelTableA94.fast) 4243 303 304 rr4243_4546 rr4546_4850 okrr4243_4546 okrr4546_4850
set_option maxRecDepth 3000 in
private theorem vrr4243_4850 : (rr4243_4850.map term).sum = 118856 := by rw [rr4243_4850,List.map_append,List.sum_append,vrr4243_4546,vrr4546_4850]

private def rr3637_4850 : List ℕ := rr3637_4243 ++ rr4243_4850
set_option maxRecDepth 3000 in
private theorem okrr3637_4850 : (List.range' 3637 1213).filter (primeBit WheelTableA94.fast) = rr3637_4850 := merge_filter (primeBit WheelTableA94.fast) 3637 606 607 rr3637_4243 rr4243_4850 okrr3637_4243 okrr4243_4850
set_option maxRecDepth 3000 in
private theorem vrr3637_4850 : (rr3637_4850.map term).sum = 273256 := by rw [rr3637_4850,List.map_append,List.sum_append,vrr3637_4243,vrr4243_4850]

private def rr2425_4850 : List ℕ := rr2425_3637 ++ rr3637_4850
set_option maxRecDepth 3000 in
private theorem okrr2425_4850 : (List.range' 2425 2425).filter (primeBit WheelTableA94.fast) = rr2425_4850 := merge_filter (primeBit WheelTableA94.fast) 2425 1212 1213 rr2425_3637 rr3637_4850 okrr2425_3637 okrr3637_4850
set_option maxRecDepth 3000 in
private theorem vrr2425_4850 : (rr2425_4850.map term).sum = 709201 := by rw [rr2425_4850,List.map_append,List.sum_append,vrr2425_3637,vrr3637_4850]

private def rr0_4850 : List ℕ := rr0_2425 ++ rr2425_4850
set_option maxRecDepth 3000 in
private theorem okrr0_4850 : (List.range' 0 4850).filter (primeBit WheelTableA94.fast) = rr0_4850 := merge_filter (primeBit WheelTableA94.fast) 0 2425 2425 rr0_2425 rr2425_4850 okrr0_2425 okrr2425_4850
set_option maxRecDepth 3000 in
private theorem vrr0_4850 : (rr0_4850.map term).sum = 2819470 := by rw [rr0_4850,List.map_append,List.sum_append,vrr0_2425,vrr2425_4850]

private def rr4850_5001 : List ℕ := [4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999]
set_option maxRecDepth 3000 in
private theorem okrr4850_5001 : (List.range' 4850 151).filter (primeBit WheelTableA94.fast) = rr4850_5001 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4850_5001 : (rr4850_5001.map term).sum = 28626 := by decide +kernel

private def rr5001_5153 : List ℕ := [5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119,5147]
set_option maxRecDepth 3000 in
private theorem okrr5001_5153 : (List.range' 5001 152).filter (primeBit WheelTableA94.fast) = rr5001_5153 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5001_5153 : (rr5001_5153.map term).sum = 24589 := by decide +kernel

private def rr4850_5153 : List ℕ := rr4850_5001 ++ rr5001_5153
set_option maxRecDepth 3000 in
private theorem okrr4850_5153 : (List.range' 4850 303).filter (primeBit WheelTableA94.fast) = rr4850_5153 := merge_filter (primeBit WheelTableA94.fast) 4850 151 152 rr4850_5001 rr5001_5153 okrr4850_5001 okrr5001_5153
set_option maxRecDepth 3000 in
private theorem vrr4850_5153 : (rr4850_5153.map term).sum = 53215 := by rw [rr4850_5153,List.map_append,List.sum_append,vrr4850_5001,vrr5001_5153]

private def rr5153_5304 : List ℕ := [5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281,5297,5303]
set_option maxRecDepth 3000 in
private theorem okrr5153_5304 : (List.range' 5153 151).filter (primeBit WheelTableA94.fast) = rr5153_5304 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5153_5304 : (rr5153_5304.map term).sum = 23270 := by decide +kernel

private def rr5304_5456 : List ℕ := [5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449]
set_option maxRecDepth 3000 in
private theorem okrr5304_5456 : (List.range' 5304 152).filter (primeBit WheelTableA94.fast) = rr5304_5456 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5304_5456 : (rr5304_5456.map term).sum = 23285 := by decide +kernel

private def rr5153_5456 : List ℕ := rr5153_5304 ++ rr5304_5456
set_option maxRecDepth 3000 in
private theorem okrr5153_5456 : (List.range' 5153 303).filter (primeBit WheelTableA94.fast) = rr5153_5456 := merge_filter (primeBit WheelTableA94.fast) 5153 151 152 rr5153_5304 rr5304_5456 okrr5153_5304 okrr5304_5456
set_option maxRecDepth 3000 in
private theorem vrr5153_5456 : (rr5153_5456.map term).sum = 46555 := by rw [rr5153_5456,List.map_append,List.sum_append,vrr5153_5304,vrr5304_5456]

private def rr4850_5456 : List ℕ := rr4850_5153 ++ rr5153_5456
set_option maxRecDepth 3000 in
private theorem okrr4850_5456 : (List.range' 4850 606).filter (primeBit WheelTableA94.fast) = rr4850_5456 := merge_filter (primeBit WheelTableA94.fast) 4850 303 303 rr4850_5153 rr5153_5456 okrr4850_5153 okrr5153_5456
set_option maxRecDepth 3000 in
private theorem vrr4850_5456 : (rr4850_5456.map term).sum = 99770 := by rw [rr4850_5456,List.map_append,List.sum_append,vrr4850_5153,vrr5153_5456]

private def rr5456_5607 : List ℕ := [5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531,5557,5563,5569,5573,5581,5591]
set_option maxRecDepth 3000 in
private theorem okrr5456_5607 : (List.range' 5456 151).filter (primeBit WheelTableA94.fast) = rr5456_5607 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5456_5607 : (rr5456_5607.map term).sum = 20964 := by decide +kernel

private def rr5607_5759 : List ℕ := [5623,5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,5693,5701,5711,5717,5737,5741,5743,5749]
set_option maxRecDepth 3000 in
private theorem okrr5607_5759 : (List.range' 5607 152).filter (primeBit WheelTableA94.fast) = rr5607_5759 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5607_5759 : (rr5607_5759.map term).sum = 22209 := by decide +kernel

private def rr5456_5759 : List ℕ := rr5456_5607 ++ rr5607_5759
set_option maxRecDepth 3000 in
private theorem okrr5456_5759 : (List.range' 5456 303).filter (primeBit WheelTableA94.fast) = rr5456_5759 := merge_filter (primeBit WheelTableA94.fast) 5456 151 152 rr5456_5607 rr5607_5759 okrr5456_5607 okrr5607_5759
set_option maxRecDepth 3000 in
private theorem vrr5456_5759 : (rr5456_5759.map term).sum = 43173 := by rw [rr5456_5759,List.map_append,List.sum_append,vrr5456_5607,vrr5607_5759]

private def rr5759_5910 : List ℕ := [5779,5783,5791,5801,5807,5813,5821,5827,5839,5843,5849,5851,5857,5861,5867,5869,5879,5881,5897,5903]
set_option maxRecDepth 3000 in
private theorem okrr5759_5910 : (List.range' 5759 151).filter (primeBit WheelTableA94.fast) = rr5759_5910 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5759_5910 : (rr5759_5910.map term).sum = 22138 := by decide +kernel

private def rr5910_6062 : List ℕ := [5923,5927,5939,5953,5981,5987,6007,6011,6029,6037,6043,6047,6053]
set_option maxRecDepth 3000 in
private theorem okrr5910_6062 : (List.range' 5910 152).filter (primeBit WheelTableA94.fast) = rr5910_6062 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5910_6062 : (rr5910_6062.map term).sum = 13607 := by decide +kernel

private def rr5759_6062 : List ℕ := rr5759_5910 ++ rr5910_6062
set_option maxRecDepth 3000 in
private theorem okrr5759_6062 : (List.range' 5759 303).filter (primeBit WheelTableA94.fast) = rr5759_6062 := merge_filter (primeBit WheelTableA94.fast) 5759 151 152 rr5759_5910 rr5910_6062 okrr5759_5910 okrr5910_6062
set_option maxRecDepth 3000 in
private theorem vrr5759_6062 : (rr5759_6062.map term).sum = 35745 := by rw [rr5759_6062,List.map_append,List.sum_append,vrr5759_5910,vrr5910_6062]

private def rr5456_6062 : List ℕ := rr5456_5759 ++ rr5759_6062
set_option maxRecDepth 3000 in
private theorem okrr5456_6062 : (List.range' 5456 606).filter (primeBit WheelTableA94.fast) = rr5456_6062 := merge_filter (primeBit WheelTableA94.fast) 5456 303 303 rr5456_5759 rr5759_6062 okrr5456_5759 okrr5759_6062
set_option maxRecDepth 3000 in
private theorem vrr5456_6062 : (rr5456_6062.map term).sum = 78918 := by rw [rr5456_6062,List.map_append,List.sum_append,vrr5456_5759,vrr5759_6062]

private def rr4850_6062 : List ℕ := rr4850_5456 ++ rr5456_6062
set_option maxRecDepth 3000 in
private theorem okrr4850_6062 : (List.range' 4850 1212).filter (primeBit WheelTableA94.fast) = rr4850_6062 := merge_filter (primeBit WheelTableA94.fast) 4850 606 606 rr4850_5456 rr5456_6062 okrr4850_5456 okrr5456_6062
set_option maxRecDepth 3000 in
private theorem vrr4850_6062 : (rr4850_6062.map term).sum = 178688 := by rw [rr4850_6062,List.map_append,List.sum_append,vrr4850_5456,vrr5456_6062]

private def rr6062_6213 : List ℕ := [6067,6073,6079,6089,6091,6101,6113,6121,6131,6133,6143,6151,6163,6173,6197,6199,6203,6211]
set_option maxRecDepth 3000 in
private theorem okrr6062_6213 : (List.range' 6062 151).filter (primeBit WheelTableA94.fast) = rr6062_6213 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6062_6213 : (rr6062_6213.map term).sum = 17860 := by decide +kernel

private def rr6213_6365 : List ℕ := [6217,6221,6229,6247,6257,6263,6269,6271,6277,6287,6299,6301,6311,6317,6323,6329,6337,6343,6353,6359,6361]
set_option maxRecDepth 3000 in
private theorem okrr6213_6365 : (List.range' 6213 152).filter (primeBit WheelTableA94.fast) = rr6213_6365 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6213_6365 : (rr6213_6365.map term).sum = 19551 := by decide +kernel

private def rr6062_6365 : List ℕ := rr6062_6213 ++ rr6213_6365
set_option maxRecDepth 3000 in
private theorem okrr6062_6365 : (List.range' 6062 303).filter (primeBit WheelTableA94.fast) = rr6062_6365 := merge_filter (primeBit WheelTableA94.fast) 6062 151 152 rr6062_6213 rr6213_6365 okrr6062_6213 okrr6213_6365
set_option maxRecDepth 3000 in
private theorem vrr6062_6365 : (rr6062_6365.map term).sum = 37411 := by rw [rr6062_6365,List.map_append,List.sum_append,vrr6062_6213,vrr6213_6365]

private def rr6365_6516 : List ℕ := [6367,6373,6379,6389,6397,6421,6427,6449,6451,6469,6473,6481,6491]
set_option maxRecDepth 3000 in
private theorem okrr6365_6516 : (List.range' 6365 151).filter (primeBit WheelTableA94.fast) = rr6365_6516 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6365_6516 : (rr6365_6516.map term).sum = 11422 := by decide +kernel

private def rr6516_6668 : List ℕ := [6521,6529,6547,6551,6553,6563,6569,6571,6577,6581,6599,6607,6619,6637,6653,6659,6661]
set_option maxRecDepth 3000 in
private theorem okrr6516_6668 : (List.range' 6516 152).filter (primeBit WheelTableA94.fast) = rr6516_6668 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6516_6668 : (rr6516_6668.map term).sum = 14047 := by decide +kernel

private def rr6365_6668 : List ℕ := rr6365_6516 ++ rr6516_6668
set_option maxRecDepth 3000 in
private theorem okrr6365_6668 : (List.range' 6365 303).filter (primeBit WheelTableA94.fast) = rr6365_6668 := merge_filter (primeBit WheelTableA94.fast) 6365 151 152 rr6365_6516 rr6516_6668 okrr6365_6516 okrr6516_6668
set_option maxRecDepth 3000 in
private theorem vrr6365_6668 : (rr6365_6668.map term).sum = 25469 := by rw [rr6365_6668,List.map_append,List.sum_append,vrr6365_6516,vrr6516_6668]

private def rr6062_6668 : List ℕ := rr6062_6365 ++ rr6365_6668
set_option maxRecDepth 3000 in
private theorem okrr6062_6668 : (List.range' 6062 606).filter (primeBit WheelTableA94.fast) = rr6062_6668 := merge_filter (primeBit WheelTableA94.fast) 6062 303 303 rr6062_6365 rr6365_6668 okrr6062_6365 okrr6365_6668
set_option maxRecDepth 3000 in
private theorem vrr6062_6668 : (rr6062_6668.map term).sum = 62880 := by rw [rr6062_6668,List.map_append,List.sum_append,vrr6062_6365,vrr6365_6668]

private def rr6668_6819 : List ℕ := [6673,6679,6689,6691,6701,6703,6709,6719,6733,6737,6761,6763,6779,6781,6791,6793,6803]
set_option maxRecDepth 3000 in
private theorem okrr6668_6819 : (List.range' 6668 151).filter (primeBit WheelTableA94.fast) = rr6668_6819 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6668_6819 : (rr6668_6819.map term).sum = 13289 := by decide +kernel

private def rr6819_6971 : List ℕ := [6823,6827,6829,6833,6841,6857,6863,6869,6871,6883,6899,6907,6911,6917,6947,6949,6959,6961,6967]
set_option maxRecDepth 3000 in
private theorem okrr6819_6971 : (List.range' 6819 152).filter (primeBit WheelTableA94.fast) = rr6819_6971 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6819_6971 : (rr6819_6971.map term).sum = 13874 := by decide +kernel

private def rr6668_6971 : List ℕ := rr6668_6819 ++ rr6819_6971
set_option maxRecDepth 3000 in
private theorem okrr6668_6971 : (List.range' 6668 303).filter (primeBit WheelTableA94.fast) = rr6668_6971 := merge_filter (primeBit WheelTableA94.fast) 6668 151 152 rr6668_6819 rr6819_6971 okrr6668_6819 okrr6819_6971
set_option maxRecDepth 3000 in
private theorem vrr6668_6971 : (rr6668_6971.map term).sum = 27163 := by rw [rr6668_6971,List.map_append,List.sum_append,vrr6668_6819,vrr6819_6971]

private def rr6971_7123 : List ℕ := [6971,6977,6983,6991,6997,7001,7013,7019,7027,7039,7043,7057,7069,7079,7103,7109,7121]
set_option maxRecDepth 3000 in
private theorem okrr6971_7123 : (List.range' 6971 152).filter (primeBit WheelTableA94.fast) = rr6971_7123 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr6971_7123 : (rr6971_7123.map term).sum = 11616 := by decide +kernel

private def rr7123_7275 : List ℕ := [7127,7129,7151,7159,7177,7187,7193,7207,7211,7213,7219,7229,7237,7243,7247,7253]
set_option maxRecDepth 3000 in
private theorem okrr7123_7275 : (List.range' 7123 152).filter (primeBit WheelTableA94.fast) = rr7123_7275 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr7123_7275 : (rr7123_7275.map term).sum = 10176 := by decide +kernel

private def rr6971_7275 : List ℕ := rr6971_7123 ++ rr7123_7275
set_option maxRecDepth 3000 in
private theorem okrr6971_7275 : (List.range' 6971 304).filter (primeBit WheelTableA94.fast) = rr6971_7275 := merge_filter (primeBit WheelTableA94.fast) 6971 152 152 rr6971_7123 rr7123_7275 okrr6971_7123 okrr7123_7275
set_option maxRecDepth 3000 in
private theorem vrr6971_7275 : (rr6971_7275.map term).sum = 21792 := by rw [rr6971_7275,List.map_append,List.sum_append,vrr6971_7123,vrr7123_7275]

private def rr6668_7275 : List ℕ := rr6668_6971 ++ rr6971_7275
set_option maxRecDepth 3000 in
private theorem okrr6668_7275 : (List.range' 6668 607).filter (primeBit WheelTableA94.fast) = rr6668_7275 := merge_filter (primeBit WheelTableA94.fast) 6668 303 304 rr6668_6971 rr6971_7275 okrr6668_6971 okrr6971_7275
set_option maxRecDepth 3000 in
private theorem vrr6668_7275 : (rr6668_7275.map term).sum = 48955 := by rw [rr6668_7275,List.map_append,List.sum_append,vrr6668_6971,vrr6971_7275]

private def rr6062_7275 : List ℕ := rr6062_6668 ++ rr6668_7275
set_option maxRecDepth 3000 in
private theorem okrr6062_7275 : (List.range' 6062 1213).filter (primeBit WheelTableA94.fast) = rr6062_7275 := merge_filter (primeBit WheelTableA94.fast) 6062 606 607 rr6062_6668 rr6668_7275 okrr6062_6668 okrr6668_7275
set_option maxRecDepth 3000 in
private theorem vrr6062_7275 : (rr6062_7275.map term).sum = 111835 := by rw [rr6062_7275,List.map_append,List.sum_append,vrr6062_6668,vrr6668_7275]

private def rr4850_7275 : List ℕ := rr4850_6062 ++ rr6062_7275
set_option maxRecDepth 3000 in
private theorem okrr4850_7275 : (List.range' 4850 2425).filter (primeBit WheelTableA94.fast) = rr4850_7275 := merge_filter (primeBit WheelTableA94.fast) 4850 1212 1213 rr4850_6062 rr6062_7275 okrr4850_6062 okrr6062_7275
set_option maxRecDepth 3000 in
private theorem vrr4850_7275 : (rr4850_7275.map term).sum = 290523 := by rw [rr4850_7275,List.map_append,List.sum_append,vrr4850_6062,vrr6062_7275]

private def rr7275_7426 : List ℕ := [7283,7297,7307,7309,7321,7331,7333,7349,7351,7369,7393,7411,7417]
set_option maxRecDepth 3000 in
private theorem okrr7275_7426 : (List.range' 7275 151).filter (primeBit WheelTableA94.fast) = rr7275_7426 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr7275_7426 : (rr7275_7426.map term).sum = 7708 := by decide +kernel

private def rr7426_7578 : List ℕ := [7433,7451,7457,7459,7477,7481,7487,7489,7499,7507,7517,7523,7529,7537,7541,7547,7549,7559,7561,7573,7577]
set_option maxRecDepth 3000 in
private theorem okrr7426_7578 : (List.range' 7426 152).filter (primeBit WheelTableA94.fast) = rr7426_7578 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr7426_7578 : (rr7426_7578.map term).sum = 11425 := by decide +kernel

private def rr7275_7578 : List ℕ := rr7275_7426 ++ rr7426_7578
set_option maxRecDepth 3000 in
private theorem okrr7275_7578 : (List.range' 7275 303).filter (primeBit WheelTableA94.fast) = rr7275_7578 := merge_filter (primeBit WheelTableA94.fast) 7275 151 152 rr7275_7426 rr7426_7578 okrr7275_7426 okrr7426_7578
set_option maxRecDepth 3000 in
private theorem vrr7275_7578 : (rr7275_7578.map term).sum = 19133 := by rw [rr7275_7578,List.map_append,List.sum_append,vrr7275_7426,vrr7426_7578]

private def rr7578_7729 : List ℕ := [7583,7589,7591,7603,7607,7621,7639,7643,7649,7669,7673,7681,7687,7691,7699,7703,7717,7723,7727]
set_option maxRecDepth 3000 in
private theorem okrr7578_7729 : (List.range' 7578 151).filter (primeBit WheelTableA94.fast) = rr7578_7729 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr7578_7729 : (rr7578_7729.map term).sum = 9434 := by decide +kernel

private def rr7729_7881 : List ℕ := [7741,7753,7757,7759,7789,7793,7817,7823,7829,7841,7853,7867,7873,7877,7879]
set_option maxRecDepth 3000 in
private theorem okrr7729_7881 : (List.range' 7729 152).filter (primeBit WheelTableA94.fast) = rr7729_7881 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr7729_7881 : (rr7729_7881.map term).sum = 6806 := by decide +kernel

private def rr7578_7881 : List ℕ := rr7578_7729 ++ rr7729_7881
set_option maxRecDepth 3000 in
private theorem okrr7578_7881 : (List.range' 7578 303).filter (primeBit WheelTableA94.fast) = rr7578_7881 := merge_filter (primeBit WheelTableA94.fast) 7578 151 152 rr7578_7729 rr7729_7881 okrr7578_7729 okrr7729_7881
set_option maxRecDepth 3000 in
private theorem vrr7578_7881 : (rr7578_7881.map term).sum = 16240 := by rw [rr7578_7881,List.map_append,List.sum_append,vrr7578_7729,vrr7729_7881]

private def rr7275_7881 : List ℕ := rr7275_7578 ++ rr7578_7881
set_option maxRecDepth 3000 in
private theorem okrr7275_7881 : (List.range' 7275 606).filter (primeBit WheelTableA94.fast) = rr7275_7881 := merge_filter (primeBit WheelTableA94.fast) 7275 303 303 rr7275_7578 rr7578_7881 okrr7275_7578 okrr7578_7881
set_option maxRecDepth 3000 in
private theorem vrr7275_7881 : (rr7275_7881.map term).sum = 35373 := by rw [rr7275_7881,List.map_append,List.sum_append,vrr7275_7578,vrr7578_7881]

private def rr7881_8032 : List ℕ := [7883,7901,7907,7919,7927,7933,7937,7949,7951,7963,7993,8009,8011,8017]
set_option maxRecDepth 3000 in
private theorem okrr7881_8032 : (List.range' 7881 151).filter (primeBit WheelTableA94.fast) = rr7881_8032 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr7881_8032 : (rr7881_8032.map term).sum = 5825 := by decide +kernel

private def rr8032_8184 : List ℕ := [8039,8053,8059,8069,8081,8087,8089,8093,8101,8111,8117,8123,8147,8161,8167,8171,8179]
set_option maxRecDepth 3000 in
private theorem okrr8032_8184 : (List.range' 8032 152).filter (primeBit WheelTableA94.fast) = rr8032_8184 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8032_8184 : (rr8032_8184.map term).sum = 6419 := by decide +kernel

private def rr7881_8184 : List ℕ := rr7881_8032 ++ rr8032_8184
set_option maxRecDepth 3000 in
private theorem okrr7881_8184 : (List.range' 7881 303).filter (primeBit WheelTableA94.fast) = rr7881_8184 := merge_filter (primeBit WheelTableA94.fast) 7881 151 152 rr7881_8032 rr8032_8184 okrr7881_8032 okrr8032_8184
set_option maxRecDepth 3000 in
private theorem vrr7881_8184 : (rr7881_8184.map term).sum = 12244 := by rw [rr7881_8184,List.map_append,List.sum_append,vrr7881_8032,vrr8032_8184]

private def rr8184_8335 : List ℕ := [8191,8209,8219,8221,8231,8233,8237,8243,8263,8269,8273,8287,8291,8293,8297,8311,8317,8329]
set_option maxRecDepth 3000 in
private theorem okrr8184_8335 : (List.range' 8184 151).filter (primeBit WheelTableA94.fast) = rr8184_8335 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8184_8335 : (rr8184_8335.map term).sum = 6099 := by decide +kernel

private def rr8335_8487 : List ℕ := [8353,8363,8369,8377,8387,8389,8419,8423,8429,8431,8443,8447,8461,8467]
set_option maxRecDepth 3000 in
private theorem okrr8335_8487 : (List.range' 8335 152).filter (primeBit WheelTableA94.fast) = rr8335_8487 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8335_8487 : (rr8335_8487.map term).sum = 4229 := by decide +kernel

private def rr8184_8487 : List ℕ := rr8184_8335 ++ rr8335_8487
set_option maxRecDepth 3000 in
private theorem okrr8184_8487 : (List.range' 8184 303).filter (primeBit WheelTableA94.fast) = rr8184_8487 := merge_filter (primeBit WheelTableA94.fast) 8184 151 152 rr8184_8335 rr8335_8487 okrr8184_8335 okrr8335_8487
set_option maxRecDepth 3000 in
private theorem vrr8184_8487 : (rr8184_8487.map term).sum = 10328 := by rw [rr8184_8487,List.map_append,List.sum_append,vrr8184_8335,vrr8335_8487]

private def rr7881_8487 : List ℕ := rr7881_8184 ++ rr8184_8487
set_option maxRecDepth 3000 in
private theorem okrr7881_8487 : (List.range' 7881 606).filter (primeBit WheelTableA94.fast) = rr7881_8487 := merge_filter (primeBit WheelTableA94.fast) 7881 303 303 rr7881_8184 rr8184_8487 okrr7881_8184 okrr8184_8487
set_option maxRecDepth 3000 in
private theorem vrr7881_8487 : (rr7881_8487.map term).sum = 22572 := by rw [rr7881_8487,List.map_append,List.sum_append,vrr7881_8184,vrr8184_8487]

private def rr7275_8487 : List ℕ := rr7275_7881 ++ rr7881_8487
set_option maxRecDepth 3000 in
private theorem okrr7275_8487 : (List.range' 7275 1212).filter (primeBit WheelTableA94.fast) = rr7275_8487 := merge_filter (primeBit WheelTableA94.fast) 7275 606 606 rr7275_7881 rr7881_8487 okrr7275_7881 okrr7881_8487
set_option maxRecDepth 3000 in
private theorem vrr7275_8487 : (rr7275_8487.map term).sum = 57945 := by rw [rr7275_8487,List.map_append,List.sum_append,vrr7275_7881,vrr7881_8487]

private def rr8487_8638 : List ℕ := [8501,8513,8521,8527,8537,8539,8543,8563,8573,8581,8597,8599,8609,8623,8627,8629]
set_option maxRecDepth 3000 in
private theorem okrr8487_8638 : (List.range' 8487 151).filter (primeBit WheelTableA94.fast) = rr8487_8638 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8487_8638 : (rr8487_8638.map term).sum = 4257 := by decide +kernel

private def rr8638_8790 : List ℕ := [8641,8647,8663,8669,8677,8681,8689,8693,8699,8707,8713,8719,8731,8737,8741,8747,8753,8761,8779,8783]
set_option maxRecDepth 3000 in
private theorem okrr8638_8790 : (List.range' 8638 152).filter (primeBit WheelTableA94.fast) = rr8638_8790 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8638_8790 : (rr8638_8790.map term).sum = 4593 := by decide +kernel

private def rr8487_8790 : List ℕ := rr8487_8638 ++ rr8638_8790
set_option maxRecDepth 3000 in
private theorem okrr8487_8790 : (List.range' 8487 303).filter (primeBit WheelTableA94.fast) = rr8487_8790 := merge_filter (primeBit WheelTableA94.fast) 8487 151 152 rr8487_8638 rr8638_8790 okrr8487_8638 okrr8638_8790
set_option maxRecDepth 3000 in
private theorem vrr8487_8790 : (rr8487_8790.map term).sum = 8850 := by rw [rr8487_8790,List.map_append,List.sum_append,vrr8487_8638,vrr8638_8790]

private def rr8790_8941 : List ℕ := [8803,8807,8819,8821,8831,8837,8839,8849,8861,8863,8867,8887,8893,8923,8929,8933]
set_option maxRecDepth 3000 in
private theorem okrr8790_8941 : (List.range' 8790 151).filter (primeBit WheelTableA94.fast) = rr8790_8941 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8790_8941 : (rr8790_8941.map term).sum = 3088 := by decide +kernel

private def rr8941_9093 : List ℕ := [8941,8951,8963,8969,8971,8999,9001,9007,9011,9013,9029,9041,9043,9049,9059,9067,9091]
set_option maxRecDepth 3000 in
private theorem okrr8941_9093 : (List.range' 8941 152).filter (primeBit WheelTableA94.fast) = rr8941_9093 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr8941_9093 : (rr8941_9093.map term).sum = 2692 := by decide +kernel

private def rr8790_9093 : List ℕ := rr8790_8941 ++ rr8941_9093
set_option maxRecDepth 3000 in
private theorem okrr8790_9093 : (List.range' 8790 303).filter (primeBit WheelTableA94.fast) = rr8790_9093 := merge_filter (primeBit WheelTableA94.fast) 8790 151 152 rr8790_8941 rr8941_9093 okrr8790_8941 okrr8941_9093
set_option maxRecDepth 3000 in
private theorem vrr8790_9093 : (rr8790_9093.map term).sum = 5780 := by rw [rr8790_9093,List.map_append,List.sum_append,vrr8790_8941,vrr8941_9093]

private def rr8487_9093 : List ℕ := rr8487_8790 ++ rr8790_9093
set_option maxRecDepth 3000 in
private theorem okrr8487_9093 : (List.range' 8487 606).filter (primeBit WheelTableA94.fast) = rr8487_9093 := merge_filter (primeBit WheelTableA94.fast) 8487 303 303 rr8487_8790 rr8790_9093 okrr8487_8790 okrr8790_9093
set_option maxRecDepth 3000 in
private theorem vrr8487_9093 : (rr8487_9093.map term).sum = 14630 := by rw [rr8487_9093,List.map_append,List.sum_append,vrr8487_8790,vrr8790_9093]

private def rr9093_9244 : List ℕ := [9103,9109,9127,9133,9137,9151,9157,9161,9173,9181,9187,9199,9203,9209,9221,9227,9239,9241]
set_option maxRecDepth 3000 in
private theorem okrr9093_9244 : (List.range' 9093 151).filter (primeBit WheelTableA94.fast) = rr9093_9244 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr9093_9244 : (rr9093_9244.map term).sum = 2181 := by decide +kernel

private def rr9244_9396 : List ℕ := [9257,9277,9281,9283,9293,9311,9319,9323,9337,9341,9343,9349,9371,9377,9391]
set_option maxRecDepth 3000 in
private theorem okrr9244_9396 : (List.range' 9244 152).filter (primeBit WheelTableA94.fast) = rr9244_9396 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr9244_9396 : (rr9244_9396.map term).sum = 1281 := by decide +kernel

private def rr9093_9396 : List ℕ := rr9093_9244 ++ rr9244_9396
set_option maxRecDepth 3000 in
private theorem okrr9093_9396 : (List.range' 9093 303).filter (primeBit WheelTableA94.fast) = rr9093_9396 := merge_filter (primeBit WheelTableA94.fast) 9093 151 152 rr9093_9244 rr9244_9396 okrr9093_9244 okrr9244_9396
set_option maxRecDepth 3000 in
private theorem vrr9093_9396 : (rr9093_9396.map term).sum = 3462 := by rw [rr9093_9396,List.map_append,List.sum_append,vrr9093_9244,vrr9244_9396]

private def rr9396_9548 : List ℕ := [9397,9403,9413,9419,9421,9431,9433,9437,9439,9461,9463,9467,9473,9479,9491,9497,9511,9521,9533,9539,9547]
set_option maxRecDepth 3000 in
private theorem okrr9396_9548 : (List.range' 9396 152).filter (primeBit WheelTableA94.fast) = rr9396_9548 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr9396_9548 : (rr9396_9548.map term).sum = 1125 := by decide +kernel

private def rr9548_9700 : List ℕ := [9551,9587,9601,9613,9619,9623,9629,9631,9643,9649,9661,9677,9679,9689,9697]
set_option maxRecDepth 3000 in
private theorem okrr9548_9700 : (List.range' 9548 152).filter (primeBit WheelTableA94.fast) = rr9548_9700 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr9548_9700 : (rr9548_9700.map term).sum = 222 := by decide +kernel

private def rr9396_9700 : List ℕ := rr9396_9548 ++ rr9548_9700
set_option maxRecDepth 3000 in
private theorem okrr9396_9700 : (List.range' 9396 304).filter (primeBit WheelTableA94.fast) = rr9396_9700 := merge_filter (primeBit WheelTableA94.fast) 9396 152 152 rr9396_9548 rr9548_9700 okrr9396_9548 okrr9548_9700
set_option maxRecDepth 3000 in
private theorem vrr9396_9700 : (rr9396_9700.map term).sum = 1347 := by rw [rr9396_9700,List.map_append,List.sum_append,vrr9396_9548,vrr9548_9700]

private def rr9093_9700 : List ℕ := rr9093_9396 ++ rr9396_9700
set_option maxRecDepth 3000 in
private theorem okrr9093_9700 : (List.range' 9093 607).filter (primeBit WheelTableA94.fast) = rr9093_9700 := merge_filter (primeBit WheelTableA94.fast) 9093 303 304 rr9093_9396 rr9396_9700 okrr9093_9396 okrr9396_9700
set_option maxRecDepth 3000 in
private theorem vrr9093_9700 : (rr9093_9700.map term).sum = 4809 := by rw [rr9093_9700,List.map_append,List.sum_append,vrr9093_9396,vrr9396_9700]

private def rr8487_9700 : List ℕ := rr8487_9093 ++ rr9093_9700
set_option maxRecDepth 3000 in
private theorem okrr8487_9700 : (List.range' 8487 1213).filter (primeBit WheelTableA94.fast) = rr8487_9700 := merge_filter (primeBit WheelTableA94.fast) 8487 606 607 rr8487_9093 rr9093_9700 okrr8487_9093 okrr9093_9700
set_option maxRecDepth 3000 in
private theorem vrr8487_9700 : (rr8487_9700.map term).sum = 19439 := by rw [rr8487_9700,List.map_append,List.sum_append,vrr8487_9093,vrr9093_9700]

private def rr7275_9700 : List ℕ := rr7275_8487 ++ rr8487_9700
set_option maxRecDepth 3000 in
private theorem okrr7275_9700 : (List.range' 7275 2425).filter (primeBit WheelTableA94.fast) = rr7275_9700 := merge_filter (primeBit WheelTableA94.fast) 7275 1212 1213 rr7275_8487 rr8487_9700 okrr7275_8487 okrr8487_9700
set_option maxRecDepth 3000 in
private theorem vrr7275_9700 : (rr7275_9700.map term).sum = 77384 := by rw [rr7275_9700,List.map_append,List.sum_append,vrr7275_8487,vrr8487_9700]

private def rr4850_9700 : List ℕ := rr4850_7275 ++ rr7275_9700
set_option maxRecDepth 3000 in
private theorem okrr4850_9700 : (List.range' 4850 4850).filter (primeBit WheelTableA94.fast) = rr4850_9700 := merge_filter (primeBit WheelTableA94.fast) 4850 2425 2425 rr4850_7275 rr7275_9700 okrr4850_7275 okrr7275_9700
set_option maxRecDepth 3000 in
private theorem vrr4850_9700 : (rr4850_9700.map term).sum = 367907 := by rw [rr4850_9700,List.map_append,List.sum_append,vrr4850_7275,vrr7275_9700]

private def rr0_9700 : List ℕ := rr0_4850 ++ rr4850_9700
set_option maxRecDepth 3000 in
private theorem okrr0_9700 : (List.range' 0 9700).filter (primeBit WheelTableA94.fast) = rr0_9700 := merge_filter (primeBit WheelTableA94.fast) 0 4850 4850 rr0_4850 rr4850_9700 okrr0_4850 okrr4850_9700
set_option maxRecDepth 3000 in
private theorem vrr0_9700 : (rr0_9700.map term).sum = 3187377 := by rw [rr0_9700,List.map_append,List.sum_append,vrr0_4850,vrr4850_9700]

private theorem right_part :
    (∑ p ∈ (Nat.primesLE 9699).filter (454 < ·), (Nat.primeCounting (94085731/p) - Nat.primeCounting (p-1))) = 3187377 := by
  have rows : (List.range (9699+1)).filter (fun p => decide p.Prime) = rr0_9700 := by
    rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct _ (by decide),List.range_eq_range']
    exact okrr0_9700
  have nd : rr0_9700.Nodup := by rw [←rows]; exact List.nodup_range.filter _
  have same : Nat.primesLE 9699 = rr0_9700.toFinset := by
    rw [←rows]
    ext n
    simp [Nat.mem_primesLE]
    omega
  calc
    _ = ∑ p ∈ (Nat.primesLE 9699).filter (454<·), (WheelTableA94.fast (94085731/p)-WheelTableA94.fast (p-1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨mem,above⟩ := Finset.mem_filter.mp hp
      have ub := Nat.le_of_mem_primesLE mem
      have lim : 94085731/p ≤ 206781 :=
        Nat.div_le_div_left (show 455 ≤ p by omega) (by decide)
      rw [WheelTableA94.fast_correct _ (by omega),WheelTableA94.fast_correct _ (by omega)]
    _ = (rr0_9700.map term).sum := by
      rw [same,Finset.sum_filter]
      exact List.sum_toFinset term nd
    _ = _ := vrr0_9700

set_option maxRecDepth 12000 in
theorem first_anchor : Nat.primeCounting 94085731 = 5439846 :=
  assemble (x:=94085731) (y:=454) (z:=9699) (a:=8627224) (b:=3187377) (r:=5439846)
    (by decide) (by decide) (by decide) (by decide) (by decide) left_part right_part (by decide)
end RankWheel94

theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R2_H4_R1_H1_R1.H1 :=
  RankWheel94.first_anchor
