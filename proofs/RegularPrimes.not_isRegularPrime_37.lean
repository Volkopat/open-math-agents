import FormalConjectures.Wikipedia.RegularPrimes

-- Problem: Infinite Regular Primes — not isRegularPrime 37
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RegularPrimes.lean:45 (declaration RegularPrimes.not_isRegularPrime_37)
-- Credit: @chris01-dev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# 37 is irregular: a direct certificate, without Kummer's criterion

Write `K = ℚ(ζ)` with `ζ` a primitive 37-th root of unity and `R = 𝓞 K = ℤ[ζ]`.
We show that `37` divides the class number of `K` by exhibiting an ideal class of order `37`.

* `al` is an explicit element `α ∈ R` and `I = (149, α)` is a prime above `149`.  The identities
  `α * κ = 149 ^ 37` and `κ * x + α * y = 1` (checked by the kernel as polynomial identities modulo
  the 37-th cyclotomic polynomial) give `I ^ 37 = (α)`.
* If the class number were prime to `37`, then `I = (β)` would be principal and `α = u * β ^ 37`
  for a unit `u`.
* By Kronecker's theorem `u / conj u` is a root of unity, so `u = ± ζ ^ m * conj u`.  Hence, with
  `s : ζ ↦ ζ ^ 2` and `c : ζ ↦ ζ⁻¹`, the unit cancels from
  `s α * (c α) ^ 2` versus `s (c α) * α ^ 2`: their quotient is a `37`-th power in `K`.
* Reducing modulo the prime `(223, ζ - 2)` (note `223 ∣ 2 ^ 37 - 1`) and raising to the power
  `(223 - 1) / 37 = 6` gives an equality in `ZMod 223` which is false by direct computation.
-/

namespace OMA.Irr37

open NumberField

/-- Horner evaluation of an integer coefficient list at `z`. -/
def ev {A : Type*} [CommRing A] (z : A) : List ℤ → A
  | [] => 0
  | a :: L => (a : A) + z * ev z L

/-- Horner evaluation over `ℤ`, for kernel computation. -/
def evZ (r : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: L => a + r * evZ r L

def padd : List ℤ → List ℤ → List ℤ
  | [], M => M
  | a :: L, [] => a :: L
  | a :: L, b :: M => (a + b) :: padd L M

def psmul (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: L => (c * a) :: psmul c L

def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: L, M => padd (psmul a M) (0 :: pmul L M)

lemma ev_padd {A : Type*} [CommRing A] (z : A) :
    ∀ L M : List ℤ, ev z (padd L M) = ev z L + ev z M
  | [], M => by simp [padd, ev]
  | a :: L, [] => by simp [padd, ev]
  | a :: L, b :: M => by
    simp only [padd, ev, ev_padd z L M, Int.cast_add]
    ring

lemma ev_psmul {A : Type*} [CommRing A] (z : A) (c : ℤ) :
    ∀ L : List ℤ, ev z (psmul c L) = (c : A) * ev z L
  | [] => by simp [psmul, ev]
  | a :: L => by
    simp only [psmul, ev, ev_psmul z c L, Int.cast_mul]
    ring

lemma ev_pmul {A : Type*} [CommRing A] (z : A) :
    ∀ L M : List ℤ, ev z (pmul L M) = ev z L * ev z M
  | [], M => by simp [pmul, ev]
  | a :: L, M => by
    simp only [pmul, ev, ev_padd, ev_psmul, ev_pmul z L M, Int.cast_zero]
    ring

lemma map_ev {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (z : A) :
    ∀ L : List ℤ, f (ev z L) = ev (f z) L
  | [] => by simp [ev]
  | a :: L => by simp [ev, map_ev f z L]

lemma ev_cast {A : Type*} [CommRing A] (r : ℤ) :
    ∀ L : List ℤ, ev (r : A) L = ((evZ r L : ℤ) : A)
  | [] => by simp [ev, evZ]
  | a :: L => by simp [ev, evZ, ev_cast r L]

def phi : List ℤ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1]

lemma ev_phi {A : Type*} [CommRing A] (z : A) : ev z phi = ∑ i ∈ Finset.range 37, z ^ i := by
  simp only [phi, ev, Finset.sum_range_succ, Finset.sum_range_zero, Int.cast_one]
  ring

/- ### The certificate -/

def al : List ℤ :=
  [128, -23, 87, 40, 60, 38, 12, 24, 48, 35, 115, 8, 39, 54, 107, 37, 146, -68, 180, 73, 18, 108,
   -43, 59, 155, 49, 96, 46, -38, 145, 20, 55, 65, 44, 21, 102]

def k1 : List ℤ :=
  [0xef53c15abf0269b99d3d72ac92f049b4f2199440c99b4a1c050cd648aee138ee5,
   0x1dff39e314e42089dad7b58b6685bce41978620e437199729ccfdffc2e5e27a989,
   0xcb07709109c9d5d088f006f812ce9500d2ac12d1e05c30780296f1e203d734c2f,
   0x20e75b52ce4ecc231087e243583a13784764796c5c6a2093b08ed9307dc15fb7b,
   0x109ff351b427ee82bb442414bfe403fa02e0367be72390592d829bcb1e9f757dd0,
   0x152bcbdafd552b0da37ff8b51d76ec9b06c57d9ef087b84cd11c7e55020bd89286,
   0xc75287843b084b6f10396d1277ce3ea0b9edd4acab118ef8fef0dbcf17875eaf2,
   0x50b28d7dc86d839a02f517fc98245a9b599e0b9a79972c3ae5962ae463b49bdbe,
   0xab8af9140ce9e51f21d51bd756728e6de7bec541254a086d8a84f5c643c1ee024,
   0x11b5cd15b6acc4bf45a09d43bc24fd2d9194bafa0a9ed9959e6920918189d5db35,
   0x11b80d8ebd04ba3673512d1f78719983e6dc7290b3b94a8f795b710d452c5ca72a,
   0x8d8e51c488d661b652d6b96f247655b5667a37734bb097a8986904b2ddaf8e4b0,
   0xa49e961f1170bcd3eca8b6ea51651436edbdc95ec9b54ff6117d08b242e1f4bd2,
   0x17c6bcd44c12cafffdebe89185d0e269b3f204c146f5bfbeae2281eea5ea83033c,
   0x1323a010fb6bb0f9150d671fa3d7730c20e68c1cbda62708666230ce961e68c87e,
   0x3888a299b2508a9a7155f22c692f0ebb3a6b1419964dd1835e106a78d3edac457,
   0x4c27c24d5c2d189251c494186731e183d35f691a5eaed1459c7cf2842764764c1,
   0x10dd175f26b3f00f8c1a7ee038d8b0a398560fa446be09eccc3adb89edc19c5e43,
   0x16f360451a07e70e89dafe4f5932a8246fcaa37b8b2a101f9b7757dd3aa9a4501f,
   0xc512cbb77bfaf1e1aaefd26603537c2081b5575c595e7f1b03bcb55120e117f79,
   0x56e8cc15c79f2225443c1d57f469f0f2a07f126dbab279bfa5e3e1e67d6cb1003,
   0x168f0ed262856900ae7d03e2623d3e23405625c595bb2722471e8b8f09f05ff34e,
   0x18eeed47dc28487eee9701575bde7634d094a52348bca9b1e3183147474afcc9d5,
   0x981064f95f0cd0fabd4945f363d721c7c4afb5ef97ed54a720d5bba2916663a80,
   0x4058da2e31cc4af63f873c87f7c3451e478d7ceb423b7b8247116f15d84141e88,
   0x144e9e87d8104b9ff174310c3482558854955e2aa6f2a0744556ef19c1b378431a,
   0x1394963cdb6f5301c3605f0e959f954b8b8b0f9aae0d0ecedbedb2969af1aea024,
   0x696782323362ea323d6ada64ef1fb537d70093b770cf90727805eb61975f5b8e1,
   0x83fea670f9c2183fd19a50be6533407937a2d841fb054a42ed0c3ffff4c7dc236,
   0xc90e535c5abe8c672e1ee844c9640a4dc742a5c3b15c6db09fa4eda6acaf84e7c,
   0x1222f56e3b304c4d3f1ae07bcc83d10d7aa9f2b2eb06966785c956c24a4ef47fe8,
   0xec56d4de16b16df44588d622c7e71e36e5c1632f2228fa98b424cdb6002366708,
   0x41449b34a827fd50fd9976c96ac2ce2623af5eb77a744ea5db7fc3d1615c6ecce,
   0x7cf02c0d0c489fc6bda77099dcf9fd6f293f7abaa430968e90b08be3d1729eb4b,
   0x16a6e39dade1edced5121efc29a556a0da3cd0105453098f6d5fdf19e7f303ef02,
   0x103906480c3d5db7a551ffe6c1125bfbc2f8f247654c1105c8de08a120e88b45a9]

def xl : List ℤ :=
  [-131, -29, -40, 110, -174, 162, -278, 78, -56, -67, -101, 115, -83, 97, -134, -70, -94, 48,
   -107, 180, -180, 49, -104, 7, -67, 24, 21, -48, 39, -185, 59, -81, 1, -52, 119, -151]

def yl : List ℤ :=
  [-0xcd5caba2962431712386d3f995263446e1a10947b4bdb7576b09390299ab19dd2,
   0xadcef173ae175bd462e7f279ee9a614123669ce7876d29696c977f8cd13eeb292,
   0x1317ab3c903f585aec1469b4edfa1865b36ce0970fade4f7bd349ae2907f41c581,
   0x541a580110e57a63ad79595a74f800bceb5879739e38d1123129dfe28157f6874,
   0x4872ff49f69dbff5b5a4dbf9426f8f7ea5a73666daf940794dfc5315c4c56bb8e,
   0x1ec1793c8e968012308015cb01e6f5943e2a463134b64295a9a8e16ff30f38d52,
   0x2ecaa12f6bdf5ac9d8a09a7cb04af4e93f197507026769df877df48bcbbcd05d5,
   0x4008c1d47d320f8553921942ccf9d855b19840bfbe3d824e66fcd44fedd842f11,
   0x126b58ca44686fc81837d0bfc98785b152702dc4138b8deaf4ddcdca335a3cd1b,
   -0x92785d1ca3aa95c0e817ddd5a494743fb1fa94f82668888970e9fd075e546756c,
   0xe1c89d38fe41db487b5adac3c29b4269ed668976ebb2ca33964e87cdad1d8266c,
   0x185afb760aac99ba7a88421680e661e7cfa6a01fd923a45628372880851e284eec,
   -0x68ed56f27dc241e8cb414eca034a360ef417bd2cc24f6a26c31b9275dc736c3f4,
   -0xcdc6f3c995c95e8fd756ebe1a913747572efe066d08a146700cdae3ba3853f4b1,
   0x116b1eb2cd4f7ac8e8b5ca675bf7e896ca6feeba9eedd0b90193e9668a9753c74e,
   0xee8eb90a4156d82ccd46454b54f5b97f738c87c37d16cdf205cd64db032fd7946,
   -0xf5aadee694b8de968215a5e5f26814a59ee15928d13e00cb79b1298c055c051a0,
   -0x4527ef69ae946f0f8e756925c313b7136d1a8e27ca088f68ee44b6ffaddefc9c3,
   0x16548109d4be1b76b168dce59e2ab77c99794aba00a4807e3dafab0e8b8e672fd4,
   0x94cd7b16979162bba4cd68b761537ff0838c47fb5f52e48118d7bef44864ae1c3,
   -0x8b4e373ee6a273a309cfcd3179d178b3f8bfdf11e4df91bbcd64118e9adb8fbda,
   0xdb1de1dff45266c2894c5bd897a8745a3f26c66f697b9e6d0c5e6f9afd56bb37,
   0xb4ff37a7f253ac392682de83c2e2b62aff2879b4717f7340e63adfbe9d6b82a5c,
   0xc6af37ebf8dba4ad8ddc75e92e14a8ceb1173ab67c10d31d85a5f257326b834f2,
   0x9e3ea6fec280d07a6f37a8fab9e0305888c59f63263e1d54bba6653bc826cd97,
   -0x51a2adf35c04133b4058cb0ca19cb1d7fdab70c12068504b6e65df7179d2defe8,
   0x13e52fcd70d585d5f2a8de5bd32799aab9ee9ff2f69f1437be2204b38f215ff1d,
   0xfb73ef6f9d022451dce5ce60c2e00f6e45216ebdc8492d1786067777c41fb5c56,
   0x39ca6e69a89ebba2f132dd669837b780f06cf5ebb8437849697391244761e156f,
   -0x8820118e2228323ad3446371f184d673d0889c9a0ccc0339f7a43eaf1e2893ea7,
   0x5760b95f0aa6d8dc575341a4ff2147671bcad896857f07f62bbd48675206abbc2,
   0x160f2209c47316e3c7bccd19bc7f81a7d58b3014799761f1099f090d886698f2ff,
   0x56515daddc646c0d974db5f2c6eedccd9e4f770fe6b0d06b5d9c4c0dce3739541,
   -0xca3bffe4d5789f087ad3dea36032b5cc910fe129854350fe03a43f4d585ce1bba,
   0x305d61d6637367c54018a4d625fdf444d04d1d289013b64cbfe04b1b50c77e801,
   0x125850698da5cfe7d0bc86047603f2d3843dcc317a2254d5f62f87f841c3f793e8]

def g1 : List ℤ :=
  [-0x126788494d0a44d521ecfa44f7aa88b1025b100bd00659c3d436b66bb240c9e8905,
   0xece0d102cd0211a44b8a2152aaa4d9328c5dd42c197631b036418f0c9d7bcb176f2,
   -0x4ebefcf19230febefb4b569167039c7c87031649d5b146159c72d4d7b88835781e9,
   0x3afc97bd60f0473e342b15160ae284f09e17ad868d882c0bdfe82c7a5548b6f6a9a,
   0x8369271e2551c43a53a744dadc7c8d3e9783bfe1a6a3f56f63cfd6f55dea1915862,
   0x643b7d5d7fd3e877aad5e29e8bb0c1ad60fc752795d74a7345bbcd671a0cae168f,
   -0x2993bd8335f9b716f3ad95d9928a6f74e76d91568409d4298a7a1bfea551db9319b,
   -0x20e889f94ddeafac41d95805e023f16e95527f9193a41dacf8a3c311369157f44f6,
   0x67e58ce5787bb313657d68eb4572fe651fe0115ac98d71ec8ca776866b6b61f071c,
   0x513341f27328cd1f76422616ffc46bbcc45f459ed3b6abba7463a7ba7064d7917ff,
   0x3ff243234abc61854082cadd70b0d8dbebb19a057fdd0d46be5950eab62b884b85e,
   0x3c99d428893938c54472303b24e6c9b00242eddb762e64f24434aa9fde7c9564d2,
   -0xe33882839128850e482137b0c6a7d0cb8f133f4676393a80514f79fca8f7a3e8e6,
   0x7e3e3b63b12be9794f7715a7078a18002c7f0d06749cd1240d6887024afae0a11f1,
   0x82bd7eaa9c8a18e9b206b5e7d503d1e0645b6c6e9a0edc478ee72d77ce891f7d11c,
   -0xb3cb587491513735bd7fdd9b09ecd420433bc3787526c0772c138b187af4e2df4b,
   0x1f2ec0e2aed4a1ae6b6bd1688225de4485a5e0022df366f3e8b7b9fc3a5afa57952,
   0x2c800d85a1837223163433b95db9cc7ff8bad4d88304c2fa8d66a5f1ec7525bf2f1,
   0x4327bd352555b58b995c6b00745b3ea4b486981f527ac283d7ded5dd5a514abda8c,
   0xaedc2b211a7bf15f899f1838e83a3e98c9f12cb7ca2e1c9eb91208db2af717d2a50,
   0x63e1f4efd415c3694ebba75933b530d2c7666d68ae366b66eaa3964c1b0b104341,
   -0x14db4c89a889e1fab8e2f2c08c90fa44b3f52bc92f6165da991bd9d613cc8bdfde3,
   0x53c80a5ce97783fd47bd84f4dc9de340549035ce309f93666a6af6d6952d493a155,
   -0xd846a195c6ae77131be0e88bc11643b986c465d5506cd0cd7a29a029b8322667ff,
   0x87f9509024efa968ef28e846d19d29633a05ec721bcf8f1e6b4377b3973123f2eac,
   0xbc5b01c5e5e286e01b43137cfacdf401a9cd3f7dc4199e4492e392c87ff572a92a8,
   -0x58f613937a1d516c98ba878fc76dda67823d5ccc1ba030afef0eff28fe4a87cc019,
   0x639648772f6bb2ef444611ac6b52571043f34afbb8439fb83be7f669fff0d4faa6,
   0x57303605771f000b2a059321793e459f7e3156ef40796d717ddf3eef9724a9ba0ef,
   0x74f34d319cfdddcbdd3de168de0b71ad7f99d6019a92bbdf0b93bc0daa54521462,
   0x6854de7bec82be903ed58a94b1b670ca8f897e3c4dfb5665ce56290007eec62264f,
   0x285417581422453abe4ed71ceae44a34afc8f2fd3b022bc8be8a47cb10241c61764,
   -0x299335b97bca9d85e97526238f3f075a1e1eb625abdbabf0fb4fd54ec17c5079d91,
   0x3e473b407689a194d964660758111696e43763dea8c046c5105f22957013f803053,
   0x676b880b4e073572bdeabf5f0ed50a64faf3088725c4ec84e087770331ca77dc156]

def g2 : List ℤ :=
  [-0xe12631c2bad054d28d39dbab19c40fdb08b39b81018952980c1a2e287e52cd10830,
   0x39cad70daaaa32cb3248dd90996b7c48e8b5d92a177443060c8b53e72b4e39c8e02,
   0x270820d7f0be5ae8a0533c6697a1d41daabc9649dc5f98c734bbed4536a3dbc08d8,
   0x9deae9d4fd5e462feb89408c9471843ca4bbbc19256054ad4519eb4a7cdf7878b47,
   -0x2e1674302ef14d638fb6e5dc00c3d103cb845b9fc8ab5c741a62c0d403011ffb96d,
   -0xb835fc22120c4bffa67110a227331592637bc3c4239f0faaf0fa95736f0c8876102,
   0x54e8173a6faa7054ba96ca671311144975f03e8f3375801bd97ded6ade137b5957a,
   -0x7d552c1928eed30a353855db00cdfac3f28ba952632a5d348afe984f405349fb223,
   0x11c915e7eec4bce3c83c453b73fa8b5e4cfccabd3263aac8e42d9349486c6abb913,
   -0x3e37cdb193e3bf6ce6caa71a9c82bc1bed9929ed497c8e3ae81a1a5582e87e2284e,
   -0xbe37ea029e4c343f9847b91a46a7bd4ca83aa0562734448dfe339b3a06bb95e66b2,
   0x14a0255a778ed9615de4669c6e059d39be53b661042c029a5785957ac5c6542075e6,
   0x3905a329f705ebbd6cc5aa8490ce816cc393eb7032ab112e12d2b62066d48b77401,
   -0xaa06fb9b971f0d3e6166fb99a65a65a265d5b285e191557ea407dcde4ad249e9d95,
   -0x2e065fd9b373cac4ab490cb23a057ae2dbfd149f6117a9b650068aa569edbb55ab1,
   0x1c2ad577d174913e3d21159e43bc3e9b8c0b69f1796c0deb165cddbec960b0ef8d2,
   -0xea32a70d705e391cebf739a997601ed3afe4bd240fced27ae8c6555c7bacf48c53f,
   0x15cce486596c7825353bccc0c92178ddc5ada21bc829fcbaaa01dcbce09676e8643f,
   -0xce785d6f762596f88297f34636fb1747ec35c193f573bed1d9b71fb5cbd36d2ce2a,
   -0xa78d41f4b1965812ddf89ed2fa63556123e04dee42baca96381c2017d2b46f8bd2d,
   0x1bf43e43d7c010bb8e71fbe72edaf1054b6b4dc9492f8be1b56784d0175ba0f8d397,
   -0xacd403e77768652f8457e525c4b89a2c8d7a076985b38d0fbf3cbc4f36c671e522d,
   -0xb8edc3d0425418039557fb8ba6b5a8a1facf4e7ef7f1e9fd4e6ae82db3f337b7a87,
   -0xf8df335f7700e777ef414200555554035a10b862abf1729339a753eda965cc4ab,
   0x3dd145853b888adce5ee4b26321c880f38ff292f39559d2f5d6e3e3311d69eba92b,
   0x28abd7464e0bf73eed7ad41cb66038d7443a95767aecc47d93d91d47663b2588767,
   0x56e3228552c3611eda35a5c7feb9d5c37a4bf2a2236fb3ada64cebd5f41c523902a,
   -0x8ca433caae28e6c561ae5e190593b62c0b0c30521c49d62a86486d32e2e4e3f3b6f,
   0x3768fbf5e0ae64a69dc00cce66238a7eb6c5e5a4fa7f23338648ae9385ffc8c0b93,
   -0x297c4e9f3c388ba812c1f018da2cd8257e287acd3202d4d40f6d8642d33060dee43,
   -0x4a7aea5fcbe62ef5227bbe63d5032c83e91a76ac99d481ea8647e650a1bba10a8ed,
   0x1fb8cfb2a425d788b8beaedc608ebbb50b24eebea898bb01af5f7ac4e838f6e791e,
   0x41aaa394da4ea4d3ccae724bdd4688a1e40d43eb2c65ed987f4fa09022aa8939867,
   -0xd9e9c3b3bf01801ee43dadf11435f50f3ef13419f51fdd094733a515c71dfdddf2,
   -0x24272aa70c82170f558408b54dc41813950378c6616303d296406ea20351581283f]

lemma cert1 : pmul al k1 = padd [149 ^ 37] (pmul phi g1) := by decide +kernel

lemma cert2 : padd (pmul k1 xl) (pmul al yl) = padd [1] (pmul phi g2) := by decide +kernel

lemma cert3 : evZ 2 phi = 223 * 616318177 := by decide +kernel

def NA : ℤ := evZ (2 ^ 2) al * evZ (2 ^ 36) al ^ 2

def NB : ℤ := evZ ((2 ^ 2) ^ 36) al * evZ 2 al ^ 2

lemma cert4 : NA % 223 ≠ 0 ∧ NB % 223 ≠ 0 ∧ (NA ^ 6 - NB ^ 6) % 223 ≠ 0 := by decide +kernel

/- ### Ideals -/

lemma span_pair_pow_le {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    Ideal.span {a, b} ^ n ≤ Ideal.span {a ^ n} ⊔ Ideal.span {b} := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hab : Ideal.span {a, b} ≤ Ideal.span {a} ⊔ Ideal.span {b} := (Ideal.span_insert a {b}).le
    have h1 : Ideal.span {a ^ n} * Ideal.span {a} = Ideal.span {a ^ (n + 1)} := by
      rw [Ideal.span_singleton_mul_span_singleton, pow_succ]
    have h2 : Ideal.span {a, b} ^ (n + 1) ≤
        (Ideal.span {a ^ n} ⊔ Ideal.span {b}) * (Ideal.span {a} ⊔ Ideal.span {b}) := by
      rw [pow_succ]
      exact mul_le_mul' ih hab
    have h3 : (Ideal.span {a ^ n} ⊔ Ideal.span {b}) * (Ideal.span {a} ⊔ Ideal.span {b}) =
        Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {a ^ n} * Ideal.span {b} ⊔
            (Ideal.span {b} * Ideal.span {a} ⊔ Ideal.span {b} * Ideal.span {b}) := by
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, h1]
    rw [h3] at h2
    have e1 : Ideal.span {a ^ n} * Ideal.span {b} ≤ Ideal.span {b} := Ideal.mul_le_right
    have e2 : Ideal.span {b} * Ideal.span {a} ≤ Ideal.span {b} := Ideal.mul_le_left
    have e3 : Ideal.span {b} * Ideal.span {b} ≤ Ideal.span {b} := Ideal.mul_le_left
    have e4 : Ideal.span {b} ≤ Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {b} := le_sup_right
    exact h2.trans (sup_le (sup_le le_sup_left (e1.trans e4)) (sup_le (e2.trans e4) (e3.trans e4)))

/-- If the class number is prime to `n`, an element generating the `n`-th power of the ideal
`(l, a)` is a unit times an `n`-th power. -/
lemma key_ideal {R : Type*} [CommRing R] [IsDedekindDomain R] [Fintype (ClassGroup R)] (n : ℕ)
    (h : Nat.Coprime n (Fintype.card (ClassGroup R))) (l a k x y : R) (hl : l ≠ 0)
    (h1 : a * k = l ^ n) (h2 : k * x + a * y = 1) :
    ∃ (b : R) (u : Rˣ), a = u * b ^ n := by
  set I : Ideal R := Ideal.span {l, a} with hI
  have hlI : l ∈ I := Ideal.subset_span (by simp)
  have haI : a ∈ I := Ideal.subset_span (by simp)
  have hI37 : I ^ n = Ideal.span {a} := by
    apply le_antisymm
    · refine (span_pair_pow_le l a n).trans (sup_le ?_ le_rfl)
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨k, h1.symm⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      have hc : IsCoprime k (a ^ n) := IsCoprime.pow_right ⟨x, y, by linear_combination h2⟩
      obtain ⟨s, t, hst⟩ := hc
      have h3 : l ^ n ∈ I ^ n := Ideal.pow_mem_pow hlI n
      have h4 : a ^ n ∈ I ^ n := Ideal.pow_mem_pow haI n
      have h5 : a = l ^ n * s + a ^ n * (a * t) := by linear_combination (-a) * hst + s * h1
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right s _ h3) (Ideal.mul_mem_right (a * t) _ h4)
  have hI0 : I ≠ ⊥ := fun h0 => hl (by simpa [h0] using hlI)
  have hInz : I ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero hI0
  have hpow : (ClassGroup.mk0 ⟨I, hInz⟩) ^ n = 1 := by
    rw [← map_pow]
    have h6 : ((⟨I, hInz⟩ : nonZeroDivisors (Ideal R)) ^ n) =
        ⟨I ^ n, pow_mem hInz n⟩ := Subtype.ext (by simp)
    rw [h6, ClassGroup.mk0_eq_one_iff, hI37]
    exact ⟨⟨a, rfl⟩⟩
  have hord : orderOf (ClassGroup.mk0 ⟨I, hInz⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes h (orderOf_dvd_of_pow_eq_one hpow) orderOf_dvd_card
  rw [orderOf_eq_one_iff, ClassGroup.mk0_eq_one_iff] at hord
  obtain ⟨b, hb⟩ := hord.principal
  have hb' : I = Ideal.span {b} := hb
  rw [hb', Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hI37
  obtain ⟨u, hu⟩ := hI37
  exact ⟨b, u, by rw [← hu, mul_comm]⟩

/- ### The cyclotomic ring -/

section Cyc

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] {ζ : K}

/-- Ring homomorphisms out of `ℤ[ζ]` are given by roots of the 37-th cyclotomic polynomial. -/
lemma exists_hom (hζ : IsPrimitiveRoot ζ 37) {S : Type*} [CommRing S] (y : S)
    (hy : ∑ i ∈ Finset.range 37, y ^ i = 0) : ∃ f : 𝓞 K →+* S, f hζ.toInteger = y := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hmin : minpoly ℤ hζ.integralPowerBasis.gen = Polynomial.cyclotomic 37 ℤ := by
    rw [hζ.integralPowerBasis_gen, Polynomial.cyclotomic_eq_minpoly hζ (by norm_num)]
    exact (minpoly.algebraMap_eq RingOfIntegers.coe_injective hζ.toInteger).symm
  have h0 : Polynomial.aeval y (minpoly ℤ hζ.integralPowerBasis.gen) = 0 := by
    rw [hmin, Polynomial.cyclotomic_prime]
    simpa using hy
  refine ⟨(hζ.integralPowerBasis.lift y h0 : 𝓞 K →ₐ[ℤ] S), ?_⟩
  have h := hζ.integralPowerBasis.lift_gen y h0
  rw [hζ.integralPowerBasis_gen] at h
  exact h

/-- An endomorphism of `ℤ[ζ]` sending `ζ` to `ζ⁻¹` is complex conjugation in every embedding. -/
lemma conj_compat (hζ : IsPrimitiveRoot ζ 37) (c : 𝓞 K →+* 𝓞 K)
    (hc : c hζ.toInteger = hζ.toInteger ^ 36) (τ : K →+* ℂ) (v : 𝓞 K) :
    τ (algebraMap (𝓞 K) K (c v)) = (starRingEnd ℂ) (τ (algebraMap (𝓞 K) K v)) := by
  have hz : τ ζ ^ 37 = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hn : ‖τ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (by norm_num)
  have hne : τ ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have h1 : τ ζ * (starRingEnd ℂ) (τ ζ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have hgen : τ ζ ^ 36 = (starRingEnd ℂ) (τ ζ) := by
    apply mul_left_cancel₀ hne
    rw [h1, ← pow_succ', hz]
  have key : ((τ.comp (algebraMap (𝓞 K) K)).comp c).toIntAlgHom =
      ((starRingEnd ℂ).comp (τ.comp (algebraMap (𝓞 K) K))).toIntAlgHom := by
    apply hζ.integralPowerBasis.algHom_ext
    rw [hζ.integralPowerBasis_gen]
    change τ (algebraMap (𝓞 K) K (c hζ.toInteger)) =
      (starRingEnd ℂ) (τ (algebraMap (𝓞 K) K hζ.toInteger))
    rw [hc, map_pow, map_pow]
    exact hgen
  exact DFunLike.congr_fun key v

/-- Kummer's lemma on units, in the weak form needed here. -/
lemma unit_lemma (hζ : IsPrimitiveRoot ζ 37) (c : 𝓞 K →+* 𝓞 K)
    (hc : c hζ.toInteger = hζ.toInteger ^ 36) (u : (𝓞 K)ˣ) :
    ∃ (e : 𝓞 K) (m : ℕ), (e = 1 ∨ e = -1) ∧ (u : 𝓞 K) = e * hζ.toInteger ^ m * c u := by
  have hcu : c (u : 𝓞 K) * c ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 K, w = u * c ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := ⟨_, rfl⟩
  have hu : (u : 𝓞 K) = w * c u := by
    rw [hw, mul_assoc, mul_comm (c _) (c _), hcu, mul_one]
  have hnorm : ∀ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K w)‖ = 1 := by
    intro τ
    rw [hw, map_mul, map_mul, norm_mul, conj_compat hζ c hc τ, RCLike.norm_conj, ← norm_mul,
      ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    (RingOfIntegers.isIntegral_coe w) hnorm
  have hfin : IsOfFinOrder (algebraMap (𝓞 K) K w) := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩
  obtain ⟨r, -, hr⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide) hfin
  rcases hr with hr | hr
  · refine ⟨1, r, Or.inl rfl, ?_⟩
    have hwr : w = hζ.toInteger ^ r := RingOfIntegers.coe_injective (by rw [hr, map_pow]; rfl)
    rw [one_mul, ← hwr]
    exact hu
  · refine ⟨-1, r, Or.inr rfl, ?_⟩
    have hwr : w = -hζ.toInteger ^ r :=
      RingOfIntegers.coe_injective (by rw [hr, map_neg, map_pow]; rfl)
    rw [neg_one_mul, ← hwr]
    exact hu

end Cyc

/- ### The final computation in `ZMod 223` -/

lemma final_step [Fact (Nat.Prime 223)] (U2 U4 b1 b2 b3 b4 t e A B : ZMod 223)
    (he : e = 1 ∨ e = -1)
    (hA : A = (e * t ^ 2 * U4) * b3 ^ 37 * (U2 * b2 ^ 37) ^ 2)
    (hB : B = U4 * b4 ^ 37 * (e * t * U2 * b1 ^ 37) ^ 2) (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    A ^ 6 = B ^ 6 := by
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hX0 : b4 * b1 ^ 2 ≠ 0 := by
    intro h
    apply hB0
    rw [hB]
    linear_combination (U4 * b4 ^ 36 * e ^ 2 * t ^ 2 * U2 ^ 2 * (b1 ^ 2) ^ 36) * h
  have hY0 : b3 * b2 ^ 2 ≠ 0 := by
    intro h
    apply hA0
    rw [hA]
    linear_combination (e * t ^ 2 * U4 * b3 ^ 36 * U2 ^ 2 * (b2 ^ 2) ^ 36) * h
  have hX : (b4 * b1 ^ 2) ^ 222 = 1 := ZMod.pow_card_sub_one_eq_one hX0
  have hY : (b3 * b2 ^ 2) ^ 222 = 1 := ZMod.pow_card_sub_one_eq_one hY0
  have hA6 : A ^ 6 = (e ^ 2) ^ 3 * (t ^ 2 * U4 * U2 ^ 2) ^ 6 * (b3 * b2 ^ 2) ^ 222 := by
    rw [hA]
    ring
  have hB6 : B ^ 6 = (e ^ 2) ^ 6 * (t ^ 2 * U4 * U2 ^ 2) ^ 6 * (b4 * b1 ^ 2) ^ 222 := by
    rw [hB]
    ring
  rw [hA6, hB6, he2, hX, hY, one_pow, one_pow]

theorem main {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fintype (ClassGroup (𝓞 K))] : ¬ Nat.Coprime 37 (Fintype.card (ClassGroup (𝓞 K))) := by
  intro hcop
  have : Fact (Nat.Prime 223) := ⟨by norm_num⟩
  have hζK := IsCyclotomicExtension.zeta_spec 37 ℚ K
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : 𝓞 K, ζ = hζK.toInteger := ⟨_, rfl⟩
  have hζR : IsPrimitiveRoot ζ 37 := hζdef ▸ hζK.toInteger_isPrimitiveRoot
  have hsum : ∀ j : ℕ, Nat.Coprime j 37 → ∑ i ∈ Finset.range 37, (ζ ^ j) ^ i = 0 :=
    fun j hj => (hζR.pow_of_coprime j hj).geom_sum_eq_zero (by norm_num)
  have hphi : ev ζ phi = 0 := by
    rw [ev_phi]
    exact hζR.geom_sum_eq_zero (by norm_num)
  -- the three ring homomorphisms
  obtain ⟨s, hs⟩ := exists_hom hζK (ζ ^ 2) (hsum 2 (by decide))
  obtain ⟨c, hc⟩ := exists_hom hζK (ζ ^ 36) (hsum 36 (by decide))
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = 2 := ⟨2, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_hom hζK ((r : ℤ) : ZMod 223) (by
    rw [← ev_phi, ev_cast, hr, cert3, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨616318177, by norm_num⟩)
  rw [← hζdef] at hs hc hφ
  -- the ideal certificate
  have h1 : ev ζ al * ev ζ k1 = (149 : 𝓞 K) ^ 37 := by
    have h := congrArg (ev ζ) cert1
    rw [ev_pmul, ev_padd, ev_pmul, hphi] at h
    rw [h]
    simp only [ev, mul_zero, add_zero, zero_mul, Int.cast_pow, Int.cast_ofNat]
  have h2 : ev ζ k1 * ev ζ xl + ev ζ al * ev ζ yl = 1 := by
    have h := congrArg (ev ζ) cert2
    rw [ev_padd, ev_pmul, ev_pmul, ev_padd, ev_pmul, hphi] at h
    rw [h]
    simp only [ev, mul_zero, add_zero, zero_mul, Int.cast_one]
  obtain ⟨b, u, hab⟩ := key_ideal 37 hcop (149 : 𝓞 K) (ev ζ al) (ev ζ k1) (ev ζ xl) (ev ζ yl)
    (by norm_num) h1 h2
  obtain ⟨e, m, he, hu⟩ := unit_lemma hζK c (by rw [← hζdef]; exact hc) u
  rw [← hζdef] at hu
  -- values of the four conjugates of `α` in `ZMod 223`
  have hval : ∀ (ψ : 𝓞 K →+* ZMod 223) (q : ℤ), ψ ζ = (q : ZMod 223) →
      ψ (ev ζ al) = ((evZ q al : ℤ) : ZMod 223) := by
    intro ψ q hq
    rw [map_ev, hq, ev_cast]
  have v1 : φ (ev ζ al) = ((evZ r al : ℤ) : ZMod 223) := hval φ r hφ
  have v2 : φ (c (ev ζ al)) = ((evZ (r ^ 36) al : ℤ) : ZMod 223) :=
    hval (φ.comp c) (r ^ 36) (by simp [hc, hφ])
  have v3 : φ (s (ev ζ al)) = ((evZ (r ^ 2) al : ℤ) : ZMod 223) :=
    hval (φ.comp s) (r ^ 2) (by simp [hs, hφ])
  have v4 : φ (s (c (ev ζ al))) = ((evZ ((r ^ 2) ^ 36) al : ℤ) : ZMod 223) :=
    hval ((φ.comp s).comp c) ((r ^ 2) ^ 36) (by simp [hs, hc, hφ])
  -- the unit relation in `ZMod 223`
  have hE : φ e = 1 ∨ φ e = -1 := by rcases he with rfl | rfl <;> simp
  have hsE : φ (s e) = φ e := by rcases he with rfl | rfl <;> simp
  have hU1 : φ u = φ e * (r : ZMod 223) ^ m * φ (c u) := by
    have h := congrArg φ hu
    rw [map_mul, map_mul, map_pow, hφ] at h
    exact h
  have hU3 : φ (s u) = φ e * ((r : ZMod 223) ^ m) ^ 2 * φ (s (c u)) := by
    have h := congrArg (fun z => φ (s z)) hu
    simp only [map_mul, map_pow, hs, hφ, hsE] at h
    rw [h]
    ring
  have hA : φ (s (ev ζ al)) * φ (c (ev ζ al)) ^ 2 =
      (φ e * ((r : ZMod 223) ^ m) ^ 2 * φ (s (c u))) * φ (s b) ^ 37 *
        (φ (c u) * φ (c b) ^ 37) ^ 2 := by
    rw [← hU3]
    conv_lhs => rw [hab]
    simp only [map_mul, map_pow]
  have hB : φ (s (c (ev ζ al))) * φ (ev ζ al) ^ 2 =
      φ (s (c u)) * φ (s (c b)) ^ 37 *
        (φ e * (r : ZMod 223) ^ m * φ (c u) * φ b ^ 37) ^ 2 := by
    rw [← hU1]
    conv_lhs => rw [hab]
    simp only [map_mul, map_pow]
  -- conclusion
  obtain ⟨c1, c2, c3⟩ := cert4
  rw [v3, v2] at hA
  rw [v4, v1] at hB
  subst hr
  have hNA : ((NA : ℤ) : ZMod 223) =
      ((evZ (2 ^ 2) al : ℤ) : ZMod 223) * ((evZ (2 ^ 36) al : ℤ) : ZMod 223) ^ 2 := by
    rw [NA, Int.cast_mul, Int.cast_pow]
  have hNB : ((NB : ℤ) : ZMod 223) =
      ((evZ ((2 ^ 2) ^ 36) al : ℤ) : ZMod 223) * ((evZ 2 al : ℤ) : ZMod 223) ^ 2 := by
    rw [NB, Int.cast_mul, Int.cast_pow]
  have hA' := hNA.trans hA
  have hB' := hNB.trans hB
  have hA0 : ((NA : ℤ) : ZMod 223) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => c1 (Int.emod_eq_zero_of_dvd h)
  have hB0 : ((NB : ℤ) : ZMod 223) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => c2 (Int.emod_eq_zero_of_dvd h)
  have hfin := final_step _ _ _ _ _ _ _ _ _ _ hE hA' hB' hA0 hB0
  apply c3
  apply Int.emod_eq_zero_of_dvd
  have h6 : (((NA ^ 6 - NB ^ 6 : ℤ)) : ZMod 223) = 0 := by
    rw [Int.cast_sub, Int.cast_pow, Int.cast_pow, hfin, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 223).mp h6

end OMA.Irr37

theorem OMA.solution : type_of% @RegularPrimes.not_isRegularPrime_37 := by
  intro h
  have inst : IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 37 ℚ
  exact OMA.Irr37.main h
