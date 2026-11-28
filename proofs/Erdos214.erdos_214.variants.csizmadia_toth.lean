import FormalConjectures.ErdosProblems.«214»

-- Problem: Erdős Problem 214 — Csizmadia–Tóth bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/214.lean (declaration Erdos214.erdos_214.variants.csizmadia_toth)
-- The statement k ≤ 7 is due to G. Csizmadia and G. Tóth (J. Combin. Theory Ser. A, 1994).

/-
Construction. S is the union of the open disks of radius 1/2 centred at the lattice points
(2a+b, 7b/4), a b integers; distinct centres are at distance at least 2, so S has no two points
at distance 1. K is the centre (0,0) together with seven points close to a regular heptagon of
radius 4/5. Take a congruent copy p of K. The image of the centre lies in a lattice triangle
with vertices A, A+(2,0), A+(1,±7/4). Pull the triangle back to the frame of K with the
isometry carrying p to K: the centre then has barycentric coordinates (s,t) in a triangle with
edge vectors e = 2(u,v), f = (u,v) ± (7/4)(-v,u), u^2+v^2 = 1. A finite certificate (a
subdivision of the (s,t,direction) parameter box, checked by kernel evaluation) shows that
some vertex of the triangle is within distance 1/2 of some point of K, so the corresponding
point of the copy lies in S.
The direction (u,v) is written as ±((1-x^2)/(1+x^2), 2x/(1+x^2)) with x in [-1,1]; on an
interval of x the arc lies in the triangle formed by its end points and the meeting point of
the end tangents, and the squared distance is affine in (u,v) and convex in (s,t), so it is
enough to test the corners.
-/

open scoped EuclideanGeometry Congruent

namespace OMA214C

inductive Tr where
  | l : ℕ → Tr
  | q : ℕ → Tr
  | k : Tr
  | s : Tr → Tr → Tr
  | t : Tr → Tr → Tr
  | j : Tr → Tr → Tr

def dec : ℕ → ℕ → Tr × ℕ
  | f+1, c =>
    if c % 64 < 24 then (.l (c % 64), c / 64)
    else if c % 64 < 48 then (.q (c % 64 - 24), c / 64)
    else if c % 64 = 48 then (.k, c / 64)
    else match dec f (c / 64) with
      | (a, r) => match dec f r with
        | (b, r) => (if c % 64 = 49 then .s a b else if c % 64 = 50 then .t a b else .j a b, r)
  | 0, c => (.k, c)

def kxn : ℕ → ℤ
  | 0 => 0 | 1 => 80 | 2 => 50 | 3 => -18 | 4 => -72 | 5 => -72 | 6 => -18 | 7 => 50 | _ => 0

def kyn : ℕ → ℤ
  | 0 => 0 | 1 => 0 | 2 => 63 | 3 => 78 | 4 => 35 | 5 => -35 | 6 => -78 | 7 => -63 | _ => 0

def amn : ℕ → ℤ
  | 1 => 1 | _ => 0

def bmn : ℕ → ℤ
  | 2 => 1 | _ => 0

def Dz (sg A B U V Z k1 k2 : ℤ) : ℤ :=
  10000 * Z * (64 * A * A + 64 * A * B + 65 * B * B)
    - 409600 * ((64 * A + 32 * B) * (k1 * U + k2 * V) + 56 * sg * B * (k2 * U - k1 * V))
    + 268435456 * Z * (k1 * k1 + k2 * k2)

def ok1 (sg A B U V Z k1 k2 : ℤ) : Bool := Dz sg A B U V Z k1 k2 < 671088640000 * Z

def okc (sg ep : ℤ) (c : ℕ) (S T j0 j1 : ℤ) : Bool :=
  ok1 sg (amn (c / 8) * 4096 - S) (bmn (c / 8) * 4096 - T) (ep * (4096 - j0 * j0)) (ep * (128 * j0))
      (4096 + j0 * j0) (kxn (c % 8)) (kyn (c % 8)) &&
  ok1 sg (amn (c / 8) * 4096 - S) (bmn (c / 8) * 4096 - T) (ep * (4096 - j1 * j1)) (ep * (128 * j1))
      (4096 + j1 * j1) (kxn (c % 8)) (kyn (c % 8)) &&
  ok1 sg (amn (c / 8) * 4096 - S) (bmn (c / 8) * 4096 - T) (ep * (4096 - j0 * j1)) (ep * (64 * (j0 + j1)))
      (4096 + j0 * j1) (kxn (c % 8)) (kyn (c % 8))

def leafok (sg ep : ℤ) (c : ℕ) (S0 S1 T0 T1 j0 j1 : ℤ) : Bool :=
  decide (j0 < j1) && decide (-64 ≤ j0) && decide (j1 ≤ 64) && decide (0 < 4096 + j0 * j1) &&
  okc sg ep c S0 T0 j0 j1 && okc sg ep c S0 T1 j0 j1 && okc sg ep c S1 T0 j0 j1 && okc sg ep c S1 T1 j0 j1

def chk (sg ep : ℤ) : Tr → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Bool
  | .l c, S0, S1, T0, T1, j0, j1 => leafok sg ep c S0 S1 T0 T1 j0 j1
  | .q c, S0, _, T0, _, j0, j1 => decide (4096 ≤ S0 + T0) && leafok sg ep c S0 S0 T0 T0 j0 j1
  | .k, S0, _, T0, _, _, _ => decide (4096 < S0 + T0)
  | .s a b, S0, S1, T0, T1, j0, j1 =>
      chk sg ep a S0 ((S0 + S1) / 2) T0 T1 j0 j1 && chk sg ep b ((S0 + S1) / 2) S1 T0 T1 j0 j1
  | .t a b, S0, S1, T0, T1, j0, j1 =>
      chk sg ep a S0 S1 T0 ((T0 + T1) / 2) j0 j1 && chk sg ep b S0 S1 ((T0 + T1) / 2) T1 j0 j1
  | .j a b, S0, S1, T0, T1, j0, j1 =>
      chk sg ep a S0 S1 T0 T1 j0 ((j0 + j1) / 2) && chk sg ep b S0 S1 T0 T1 ((j0 + j1) / 2) j1


def trpp0 : Tr := (dec 999 0x2aaa8431410410412431431431490c50c50471c52431431411c71490c50c50471c52431431411c71cb2cb2cb2cb2cb2c6a492492492473cf2cb1c72492492492473cb1c71c52492491c72c71492472c52472471cd1c72cf1492491c91c73c52472491c91c51c73471cd2473473471c90472472472471471451451451444cf2cb1c71c71c71cb1c30c30c30c30c30c30c30c30c30c309a5cf2cb2cb2cb2cb2cb1c71c71c71c71c6698ec8ec6534ec7134ec4ec72cf2392cd2ccecb134d34d94d34ecb2cb1c71c4d34d34d34e373cb2c71c7134ec4dcce3733b1cb2c73c6020820838dcc8cb1c71c7120820820820820820820820820820f3b3cb2cb2cb2cb2cb1c71c71c71c71c7238d38dcf2ccec8e3733b23b2c4ec4e38e38f3b33b3cb2c71c4e3ceccecf23ce3f2cf120fc8fc8fc4fc4fc4fc723b3cb1c923b238e38e3843b3cb2c71c713923b23b2c52484c84c7248ec91c4ec91c73c4e13213138e131c73131cb1492392471471cf2c4e34ecb33b13b1c91c4e38e131c71c8d34d472c7147147134ec8ec4ec4ec4ec51383c72c72cf3491cd1cd1c51c44c91cd1132133c44473132131131131131cb138e10ecf1c4f3b33f2c84c4e3843b3c44c4e383cb1cf1cc41040f3cb2131131131131131c44104100c72c44031cb1c4f103cb1103cb13c3c43cc3c43c73104032c430c0c40c71031c80c71c8e383c83c710f20c40f20f2c440f30c0c80c72c44100cb2032c71cf2c72).1

def trpp1 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c2b9b3cb2cb2cb2cb2cb2cb1c71c71c71c71c71ae843141041042b4314314314314314314314d3431c50c50c50c50c50c50410491cf1c71c534d34d34d2cf3cb1c534d2cf3c71431431431431431410412473c71c714d34d34b3cf14d34b3cf1c50c50c50c50c50c50410491cf1c71c534d34d2cf3c534d2cf3c714d34b3cd0c50c50c50c71431431431431410412473c71c71cb2cb2cb2cb2cb2c6b4f24d34d34d2cb3cf2c71ae63b23934b34d2cd2c92c72c71c934d34b1cb1a92c92c734d2cd2c92c52c72c734d34d2cb14d2c92cd2c71cd34b24b34b24b14b1cd0412c714b24b24b1492473cf1c534d2cf14d2c92c714b34b3492485cb1473cf1cb1cb1c30c30c30c30c30c30c30c30c30c309e6ce6cf2cb2cb2cb2cb2cb1c71c71c71c71c679cfc8fc4e38e3f2c4fc72cf23d3cd34ce4f13f1cb2ccfcb198ec8e38e3f13b3c4e3f13f1c8ecf2c73c6020820880f3b33b3c48c88c88c88c88cb1c71c712082082082082082082082082082093f3cb2cb2cb2cb2cb1c71c71c71c71c723ceccfc8fc4ecc8c882093f3cb2c8f3b323220824fcf2cb23cecc8c882093f3cb2c8f3b323220824fcf2cb23cecc8c882093f3cb2cb1c71c4f3b323220824fcf2cb23cecc8c882093f3cb2cb13cecc8c882093f3cb2cb13cecc8c882093f3cb2cb13cecc8c882093f3cb2cb1c4f3b32322093f32723f3cb2c4f3b323220f24fcf2c493f3c8fcf2c4f38e38e38e38f3b3cb1c71c71c4f38fcb3cb33c9c89c8fccfcf2c4f38fc8fc8fc4fc4fc4e38fcb2cf324fccfcf2c4f3cf2723f3cb124f2723cf131c73cf23ceccfc8fc8fc73c71c934d33f2cb13f23cf3cf1723f3cb1c724d34d2cf3c533d2cf3c8f3cf3cf3cf3c53f3cb1c71c71c71c934d34b3c714cf171cc5cb24b3c4f1721721711713cf172171c73cb138e38f3b33b3c8f4b34b33b3c72c4e392c724b24b14b1c52c4f3d2cf33f24b1492484cb1484c84c71c733cf4b14923b3cf33cecc4c72cd23c4c723c4c73133c72cb34d34b1cd2cd2cd2c52c45485cf1c85c92492171cb1152171132171105c73cf2171492491c73c52492171c71492133171c72484c84c73c84c92172172171171444171cb3172171c73cf13cf1723f3c493c9c8fcf3c853f3172171171c45c45146173140c72032c71c49245c49c85c49131cb1144cb1145031c45133100c72031c80c71c8f3cf3cf132c713c4c44c72cb114f171132cf13c4c84c84c44c44c44c72145140c72c44104140c80cb1140c80c80c40c71c40c71031cb1ccf132131104104144cc4cb1c71100cb2c45133171144cc0c80c40c72032c71cf2c72).1

def trpp2 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c2c9f3cb2cb2cb2cb2cb2cb1c71c71c71c71c71b28431410410414431431431431431510c50c50c50c504104104134d2cf3c71c71c71c544314314314314104104134d2cf3c71c71c71510c50c50c50c504104104d34b3cf1c71c71c544314314314314104104d34b3cf1c71c71cb2cb2cb2cb2cb2c6c5325145145144f3cb2c71c71b14514513cb1c71c54514514513cf2c71c715144f2c544f2cd3c71cabad44f3c544f34f1cb13d3c72cf3514513c944f24f1cf3c54513c734f3513cd3c724f24f1cd0413cb14f24f24f14d34d2cf3cf1c54513cf1513c93c53c734f34d34d2cd2c73cf1cb1cb1c30c30c30c30c30c30c30c30c30c30867cf2cb2cb2cb2cb2cb1c71c71c71c71c61272271854c613c9c7124fcc9c72271cb39cf3cf3cf3cf3c93f3cb1c71c71c71c8f3c9c4f3c9cb1cc9c8f3cf3c93f3cb1c71cf2c73c6020820824fcc8cb1c71c7120820820820820820820820820820a273cb2cb2cb2cb2cb1c71c71c71c71c7224fcc8c8820a273cb2c893f3232208289cf2cb224fcc8c8820a273cb2c893f3232208289cf2cb224fcc8c8820a273cb2cb1c71c493f3232208289cf2cb224fcc8c8820a273cb2cb124fcc8c8820a273cb2cb124fcc8c8820a273cb2cb124fcc8c8820a273cb2cb1c493c8cb32322082b22b2273cb2c493c93f3cb3232209289cf2c4a2732b22b1c89cf2c493c9c89c89c4f3c9cb2cf324ac8ac8ac4ac492b2cc9cf2c4924fcf32722892b2cc9cf2c49289cc9cf228a273ccacb224f272cc9c89c89c49c73c71c94272509c89249249249246273cb1c71c71c71c94272246273cb2c715145141b2c46cb2c54272272509c93cd3c71cc91b21b11b12491b2c731b1cb1514272271c8f3cf4f2c71cd4513cf12724f3c49c8f4f13d3c53c493d3171c49171cb3cb2cd3253c53c49246c49171cf1c934c5c72172cf2c735144f14f1cd3cd3cd34d34d34d2cf3cf3cb1c464d34c6c714d3173173172c45cb3cf3c864c6c86c531b1173172172172cf3c931b24f11b3186486173cb3cc6c731b2c7124ac89ccac86c49246273c71249249249249245cb2cb2c71c71c46246c731b1245c73c72cc6189172cf31b11b11b1c461861c6cf1180c72032c71c4a1b128a173c45cc5c45c73186173031c86172173185cc0c80c40c71031c80c71c89245c45c45c71172146173173140c40cb2c461731b1180c45031cc0c72032c71cf2c72).1

def trpp3 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c2d873cb2cb2cb2cb2cb2cb1c71c71c71c71c71861555289ccac72cb18492b1273c492b12732b1c892b22b22b12b12b12b1c72849c892492b2c492b12b1c89cf2c73c60208208248c88c88cb1c71c7120820820820820820820820820820b2b3cb2cb2cb2cb2cb1c71c71c71c71c7224ac8ac8ac8ac4ac4ac4928824acb1cf2cca289cf32b2c4a28a2f22b3cb2c8a24acb32b22b22b12b12b128a2f21b12b3cb2c71cb2b55555555531532cf2c71b49255533254c54c72c71c95555531cb1b15531c55531531cb3554cd4c94c54c54c72c73ca8431410410415431431431431550c50c50c50410513cf1c71c554314314315104144f3c71c71550c50c50c54410513cf1c71c554314314315104144f3c71c71cb2cb2cb2cb2cb2555431431532c55531533531531cd5533533531c94c94514513cf2c54513cf1513c93c73c73c72c555552b2cb12b22b22955322b2531531531ccac942b2533531531287c87c72c7124924924924a273273cb2cb1c49294cc9cf2c72c49532531531c54c492b22b22b12b12b150a506cb1286c72cb1254c4a254c732b2c94506cb11b2c73cb328a28a28a286cb11b2cb1c4a1b21b1cb2c47287c47c46c86cf31b3c4a1b21b21b11b11b1cb2514514514514513cf3c71c71c54507c71506c941b21b31b2c73cb3cc7507c47c87c46187c71cf3c945141f11f1cb15141f2c47c87c721f21f21f11f1c471b31861c6cc0c80cb11c6cc0c80cb1031c721c71b2cc7c47c47c47c471c6cf30310311c6031cc0c40c72032c80cb1cb1cb1).1

def trpm0 : Tr := (dec 999 0x22c30c30c30c30c30c30c30c30c30c30badcf2cb2cb2cb2cb2cb1c71c71c71c71c68431410410416573431431431431595cd0c50c55c50410531c71c56573431431571410414c71c71595cd0c50c55c50410531c71c56573431431571410414c71c71cb2cb2cb2cb2cb2c6e58accacf2596595cb1c6d595c71595c55c72cd6573572571571cb1b6d572571cb0572572571571571571c73595cd5cd6573571571571c95c95c95c95c55555531533cf2c55555554cf2c71555554c73c55532531cf1554cd4c94c54c73c71cb18a288ac8ac7288ac8ac4a28bcb128bc4bc722b32b3cb1c60208288cb1c7120820820820820820bcb1c71c71c71c71c7228a2f2c4bc4acc82caccbc8b2b32f22f1c4bc4bc712f1c8bc4a28b2b3cb1cc820bc722caccbcb12f22f12f1cb1c8a28b2b32f22b3cb158bc95cd5cd5c7128bc8bc8bc4bc4bc4bc4bc4bc72295c4a5712ca571ccbcb2cb3555555547cb3c712d51f3c4b1f1c87cf2cb128a28a1f11f12b3cb2c555555555551f2cb1c71c71295287c47c72c73287c87c87c47c47c72c73555555547cf3c95541cb1072071c72c550710720711c7071c73c95072072072071071c55554cd4c71533547cc7c87c47c47c47c47c47c47c72507047cf1cb11c71c1c71c72cf12ca2f22f21f128b2b32f2cb3cc72f3c8b1f31c72c6cb2cf2c471c71c6cf2cb2c471c7047c87cc7cb1c711c7031c471c71b3031cf2031cb20411c0c73032c871c0cb1cc1047cf3047cc0c72032c40cb1c72c72).1

def trpm1 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c23bb3cb2cb2cb2cb2cb2cb1c71c71c71c71c71c30c30c30c30c30c30c30c30c30c30beeceecf2cb2cb2cb2cb2cb1c71c71c71c71c684314104104284314314314314314314315d6cd6cd0c50c50c50c50c50410415c71c71c575b35b3431431431431431410410571c71c715d6cd6cd0c50c50c50c50c50410415c71c71c575b35b3431431431431410410571c71c71cb2cb2cb2cb2cb2c70c30c30c30c30c30c30c30c30c2fbb3cb2cb2cb2cb2cb1c71c71c71c715d75d6cb1c6eb96c96c715b2cd6cf15d6cd6cd6c96c96c56595cf1c56596572c71596572c56572573571c73415c95c95c55c55c71cf15cbce32d6c712f2cd6cd75b35b35b35b2596596573cf3cb1c565960b2c56573571cf1596571cd5cd5c55c73c72cb18e32f22cb3312f330bcccc722f3cb18e32f22f128a2f2c73cae2cacf25962f2c712f2c73c60208208208208808c88c8bc8bcb1c71c702322322f22f22f2c0bc8bc8bc8bc8bc8bc712f1c48cb1c71c71208208208208208208332cb1c71c71c71c71c722cb332c4cc8cc4b2cb332c4b332c72ccc2cccb3332331c4cc8b2cb2cb2cc2f3cb2c71c7120bc4bc4b332c4cc8cc4b2ccc4b332cf2cf2cf1c9730b332cf22f35cb5b1ccc5b3c975b25b25b15b15b15b15b1c56cf130b5b15b1cccc8cc8ccb2596316c562f3ccc2f3071cb2cb359630c0b1c4c071cf2596072c56071073c41cb3cb158bc8b2cb2cb2cb04bcf2c71c71c71c96596072cb12cb541cb1c7358bc8bc95c55cf32c1c81c41c4b2c1c81c71cf2c735960b1081cf20b1c82c56596573571cf1596582c71c56081cf1c96071072071cf2072582c82c42c55042c72cc2072c82c71cd6573573571571571072072cf130c073c4b30b3322f3cf204bcc104bcf3071071071c81c41c712cb2cb1f2cb1c73cc10412c1c47cb3cf3c41042073073072c71082032c81040cb1cc1cc2041031cb3032c71c4130c307cc7c73c411f2c47cf3041047cf3031c81040c711c7031031c73031c80c71cb2c72).1

def trpm2 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c24bf3cb2cb2cb2cb2cb2cb1c71c71c71c71c71c30c30c30c30c30c30c30c30c30c30a6fcf2cb2cb2cb2cb2cb1c71c71c71c71c684314104104115f3431431431431457cd0c50c50c504104104105b25b1c71c71c71c515f34314314314104104175b35b35b1c71c71c71457cd0c50c50c504104105d6cd6cd6c71c71c71c515f34314314314104104104105d6cd6cf1c71c575b35b35b1c71c71c71cb2cb2cb2cb2cb2c70c30c30c30c30c30c30c30c30c29bf3cb2cb2cb2cb2cb1c71c71c71c71469457cf1457c57c72cef5f25f1cf14515f1cd7cd7c97c575d75b1cf1c575d75d6cb1c575d6c715d6c56cb35b2c735d6c96cd6c56c71cf144ccd1457c57cf25f35f1c575d75d75b3cf2c71cd75d75b35b1cf15d75b3c56cd6c73c72cb192433230c34c371cf137230c30c372cb1c73cb1924332331c64332331331ca35f18cc2f3c4c2f3331c8cc72cf3c60208208308cb1c71c71208208208208208208372cb1c71c71c71c71c7230d333333c8834cccdc8d333372c4dc71c8d333372c4d333372371371371371c4dc8c30d333333cb130dc8dc8dc4dc4c34ccf134cccdcb2cf2cf1c9144dc8dc7230c30c357cf2cb1c734515f3c4dc8c5f25f15f1cf137230c5f134cccdcb2c975d7372cb2c735d75cd5f15c2c73cb234d0f1342c73c42cf2cb15ccc8cc9733230c30c0b2333cb1c725ccc8c08ccf2cb1c575d7302c42c73cb130c5b15b3ccc5b35b35b1c73302c82c82c42c4c08ccf1cc23330b20b10b10b10b10b10b10b1c72c735d75d75c2cf3c830c30b3cf3c72c570f20f15c3c42cc2c82cb3c975d70f1cb15c3c43c83c720f20f20f10f1c57582cb35d6c56cd6c56c715b35b10960820f10b3c72c720820830b3c71c72cf134c3720b133334d34cccdc82c710b10b1c720b130c0b23333023330b10b10b10b1cb130c072c73c73cc2082302c41cb3cf30b1c420c2cc2cc2cf10c2cc3c43c43083c730310c2cc0c40c72032c820830b3c42031c80cb1cf1c42342372c42081cb2c4d073073071071cf3082082073cf2031c82081cc1c82073032031031c73031c80c71cb2c72).1

def trpm3 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c25a73cb2cb2cb2cb2cb2cb1c71c71c71c71c7196020820d232c71c712082082082082082083b2cb1c71c71c71c71c72ca537237196537237190c371c4c371371cb3ca9351cf2471372c7334838dcf138dcf1c8e34d3b1c733b2c4d34d34d34d34e373cb2c71c71c71cce34e373c4e373c4e34ecb33b1cb3cb2c72a68431410410411431431450c50417c71c514314105f1c71450c50417c71c514314105f1c71cb2cb2cb2cb2cb2c69a52471473c52471473471cb194d473c4dc91c72a51c914514515f3cb2c71c734514515f2457cd7c57c71cf14515f1c57cd7c72cd1457cf2457cd7c97c57c57c73457c97cd7c97c57c57c71c71c8d471471351c4e34d0f20f1c73c91443cb1443c43c730f2c7244dc8dc913723724510f20f1c973725f1cf1343c83c4dcc3c72c73383c43c4d38d3b2cf2343c43c83c43c7134d343c4dcf1343cb134d0b2c73c730c3342cb3cc3c43c7138e0f10b2c430b2c4e0b10b30b10b10b1cf2cf24514515f1c57cf3c51444c71444c510f1cf2443c43cc3c73c915f35f35f15f15f10f2cc30c30c30c40f30f30f20f20f20f20f20f20f2c71c71c71c830c30c30c2cf3cb2031c830c0c71082031c73031cb2c911321321311311315c3131c83cb31310d70f20f2c730c3032c440c3031cb3032c40cb2c71cb1).1

def trmp0 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c21b33cb2cb2cb2cb2cb2cb1c71c71c71c71c718612722492493f2c493f13f1cb3cb18545093f33f1cb2c612493f1cf12493f1ccfc7224fc8fc8fc4fc4fc4fc71cb3c60208208248c88c88cb1c71c7120820820820820820820820820820f3b3cb2cb2cb2cb2cb1c71c71c71c71c7224824fcb13f3c893f23f23f23f13f13f1cc93f33f33f2c4f3cf3cecb3cb2c893f23f33f23f23f13f13f13cf3cec83c73cb2c71cb2b2c249554cc9571571cb1c72b54571c54571571c94514571cb1cd5533572571571571cb1514514571572533cb1c73ca8431410410414431431431431510c50c50c50410595cf1c71c54431431431550416573c71c71510c50c50c55410595cf1c71c54431431431550416573c71c71cb2cb2cb2cb2cb2554571cd5c55c54510c50c55cb1cd5554cf3571c95c95556573cb1556c96c55595cf1cf1573c72c492492492492493f3cf2cb2c7124954fcf3cb1cb1255c95c55c71571255c495713f33f2c95543cb10f2c493f23f23f13f13f154f543cb13c3c72cb1cf251450fcb2c4fc8fc945723f25715715713f33f25553f2cd5c55c4f0b20b1cb1c733cf3cf3cf3c3cb10f2cb1c4f0f20f1cb2c430cf0b10b10f2cc2cf3c4f0f20f20f10f10f1cb2555555556573573c71c71c550f20d50f2cc3cb15550b1c73c95cd5cc30c2c71542c42c82c730b3c955550b10b1cb15550b2c42c82c720b20b20b10b1c430b30c30c2cc0c80cb10c2cc0c80cb1031c72083c82cc2c42c42c42c430b30b30310310c0c42cc0c40c72032c80cb1cb1cb1).1

def trmp1 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c22b73cb2cb2cb2cb2cb2cb1c71c71c71c71c71b68431410410415431431431431431550c50c50c50c504104104175b35b3c71c71c71c554314314314314104104175b35b3c71c71c71550c50c50c50c504104105d6cd6cf1c71c71c554314314314314104105d6cd6cf1c71c71cb2cb2cb2cb2cb2c6eb96573c565735b1cb1296c72b55555556cb1c71c55555555595cf2c71c71556c95556cb1cd6c71cb3b55c95555555595cf2cb1c71c735955b1573cd65735b1c96c96c55556c96c555b2cd5cf1cd0416cb15b25b25b15d6cd6cd6cf1c56556c96c56c55595cf1cf35d6cd7c56cd6cf1cb1cb1c30c30c30c30c30c30c30c30c30c308a1cf2cb2cb2cb2cb2cb1c71c71c71c71c6228a28a28a28a289cf2c71c71c71c7228a28a28a273cb1c7128a272c4a271cc9cb3cb1855c61289c71289cc9c72271ca1272271cf3c60208208289cc8cb1c71c712082082082082082082082082082093f3cb2cb2cb2cb2cb1c71c71c71c71c72289cc8c882093f3cb2c8a27323220824fcf2cb2289cc8c882093f3cb2c8a27323220824fcf2cb2289cc8c882093f3cb2cb1c71c4a27323220824fcf2cb2289cc8c882093f3cb2cb1289cc8c882093f3cb2cb1289cc8c882093f3cb2cb1289cc8c882093f3cb2cb1c4a23227323220920fc8fcb3cb2c4a289cf22732322482493f3cb124fccfc8fc72cf2c4a289cb2289c89c89c732732493f224fc8fc8fc4fc73cf2c4a2732732722493f23f3cf2c4a27227327227227127124924fcf3c893f33f33f2cb3c71c8a5b1296c56c4a584c71244c72273cb228a296cb1c55549c89c72cd6556573c49cb3c49cb3596584c72132256c56c49244c490f1cf1cb3cb1549c95272249249249249243cf2c71c71c71c72549c89243cf2cb1c55272272595272cd6c715555550f2c43cb2c732490f2c490f20f10f1cc3c72c73596556c56c55cf3cd65975b35b35b35b3cb1c561045b3cc4cb11325960f1c735b30f3c84583c73132132132583c83c730f3c97103cf20f30f30f10d60f25b1cf30f2c71249131131131c44c841040f3cc4031032cb1103cc3c440310c0c73031c80cb1c492490f3c71249249249249244cb2cb2c71c71c49131243c43cc3c73c722493f2ccfc83c73244c83cc3cc3c43c43c710c30c30b3c43031c80cb1c7110f10fcf1cc4c44c4f0f1cc3103cc0c72103132cc40f3032031031c40c72031c72cf2c72).1

def trmp2 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c23bb3cb2cb2cb2cb2cb2cb1c71c71c71c71c71ba843141041042e431431431431431431431596431c50c50c50c50c50c50410457cf1c71c565965975b35b3cb1c575b35b3c714314314314314314104115f3c71c715965d6cd6cf15d6cd6cf1c50c50c50c50c50c50410457cf1c71c565975b35b3c575b35b3c715d6cd6cd0c50c50c50c714314314314314104115f3c71c71cb2cb2cb2cb2cb2c6e8cbc8b5d6cd75b35f25f1cb1c72bd7c97c565965f1cb1cd75b35f25f15f1cb1b96c965965f25b35b3cb1c735d65f2cd7c97c57c56597cb15d65f2cd7c715b3cd0417c715f25f25f1457cd7cf1c575d65d6cf1597c97c71cf34575c4cb1cd7cf1cb1cb1c30c30c30c30c30c30c30c30c30c308e38b3cf2cb2cb2cb2cb2cb1c71c71c71c71c632f22cb2cb2cac73c4b2b12b1cb3cb188b2cb2b2c4ac7288ac8ac73c9658b5b12b1cb258acf32b2c73c6020820880b2cacf3c48c88c88c88c88cb1c71c7120820820820820820820820820820a273cb2cb2cb2cb2cb1c71c71c71c71c722cb2b32b22b1cc8c8820a273cb2c8b2b3232208289cf2cb22cacc8c8820a273cb2c8b2b3232208289cf2cb22cacc8c8820a273cb2cb1c71c4b2b3232208289cf2cb22cacc8c8820a273cb2cb12cacc8c8820a273cb2cb12cacc8c8820a273cb2cb12cacc8c8820a273cb2cb1c4b2b323220a289cc9cb3cb2c4b2b323228828a273cb1289cf2cf2c4b2cb2cb2cb2cacf2c71c71c712cac8acf22b328a289c89cb3cf2c4b2cacb22cac8ac8ac4ac4ac732b328a273cf2c4b2b32b22b22b128a28a272cf2c4a285c71289cb3273cb3c71c8b2cb2cb2b3cf22d75cacf3cf1cb12cb5f1c97c97c57c715f15d75c5cb15c5c85c71c572b32b32b25f1ccb5f35f3297c732cacc5c722b314a1715ca171cb3cf1cb259658acb2c4ac8a28a28a132cf2c71c965d6cd6cf15cacd6cf228a28a28a28a284cf2c71c71c71c725d65975b3c71284c56cc4cb2cf128a132131c4a132132131131cf2c735d74715f3c571721715d75c4c71c57157cc4c71cb3c85c91144c725c4c84c84c44c73132131c575d7131cb1144c57131172131cc4cf2131cd75d65f15b3cf35f15f11045f3c72132cf1285c85c45145145133172c71c45032cb1144cc4c45133032031031c80cb1c4a28a28a172c71285c45c72cb1284c45c84cf1285c85c85c45c45c45c72104100c72c45145100c80cb1100c80c80c40c71c40c71031cb128a284cb3c4a289cb3273c8a133132131131c44c441040f3100c72032c71c49244c49c84c49171cb1105cb1104031c45133140c72031c80c71cb3cf2c72).1

def trmp3 : Tr := (dec 999 0x2fbe84314104104174314314315d0c50c50471c57431431411c715d0c50c50471c57431431411c71cb2cb2cb2cb2cb2c6f5d75d7457cd7cf2cb1c725d75d7471cb1c574724715d7472c73471c975d75d7457cf2c71c71cf15d1c91c51c57472cd1c575d1c91c57cf1cd1457cf3471c90472472472471471451451451151cf2cb1c71c71c71cb1c30c30c30c30c30c30c30c30c30c30923cf2cb2cb2cb2cb2cb1c71c71c71c71c4c30c32430c2f2cb2c71c7130c30c30c30bcf2cb1c71c4c30bc7330bccbc72cb18e430bc7130bc4bc728cbc8bc73c975cbcf32f2c73c6020820830bcc8cb1c71c7120820820820820820820820820820b2b3cb2cb2cb2cb2cb1c71c71c71c71c7230c2f3c8bccbc8c2f32f22f2c4bc4b2cb2cb2cacf3cb2c71c4b2cb2cacf3c8b2b22b3c482b22b22b12b12b12b1cb3cb1c8c30c472c7147147130bc8bc4bc4bc4bc512c6c72c725d75d1c51c4bcf2c4c2f22f32f12f1c91c4b2cb171c71cb35cbc8b2cb2cb2c5cf2cb1c71c4b5cbc8bcb15cbc91c4bc91c575c5c85c72cf12cb171c4b172171cc5c72c73451457cf3471471172cc5445cb3c51173172171171171171cb12cb1b21b1c46c86146c86cb1185cc6032031cb1145032c80cb1c4b2cb1b2c4b2c5cf1171cf12cb2c5cf1c4b2b32b2c85c73145185cf2c85c45c45c45c45c71145145031cb1140c72c7118a1b1cc6c46c4a146cb1146cb1cc5140cb1186031031c40c72031c72cf2c72).1

def trmm0 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c29933cb2cb2cb2cb2cb2cb1c71c71c71c71c7192020820c232c71c712082082082082082082f2cb1c71c71c71c71c72ca494d331c4d331331ca4332331cf2a51333c91c4ccb190cc8cc7330c30c30c30c30bcf2cb1c71c71c4c20c2f3c4c2f3c7230c2f1c4bccbcb1ccc30bcf130bcf130bc8bccbc722f3cb2c72a68431410410411431431450c50412c71c514314104b1c71450c50412c71c514314104b1c71cb2cb2cb2cb2cb2c69472451451491cf2cb1c71a69457471cf1457471cd1c72c6444ccf1332471cb34514b2491cd2c52c71473c524514b1c734b1c91cd24734b24b14b14b1452473cb34914b2cd2c92c52c52c71c71c9133233244cc8cc923324b14511b21b1cb3c4c306c86c731b1cb1311c51c4c47130c1b21b1c4bcf2446c46c51446cb1cc6cb1cb330c307cb130c306c73c4c1b2c73c4c30bc8bcf2306c46c86c46c71ccc1f21b31b31b11b1c472c7c731f11f11f12cb1b11f2c461f2c73c8b1b11b1cf2492473cd2c52c52c46c91491452c71cd1cf11911b1cc6c51445c71446c51171cf2cf2cc6186186186185cf31b21b21b21b21b21b21b2c71c71c71c861861871b31b3cb2031c871c0c71186031c73031cb2c86486c86cb1486171c86c91172172171171171cc5c73186032c46180c72173032c40cb2c71cb1).1

def trmm1 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c2a973cb2cb2cb2cb2cb2cb1c71c71c71c71c71c30c30c30c30c30c30c30c30c30c30aa9cf2cb2cb2cb2cb2cb1c71c71c71c71c68431410410412473431431431431491cd0c50c50c504104104104f24f1c71c71c71c524734314314314104104134d2cf34f1c71c71c71491cd0c50c50c504104104d34b3cd3c71c71c71c524734314314314104104104104d34b3cf1c71c534d2cf34f1c71c71c71cb2cb2cb2cb2cb2c70c30c30c30c30c30c30c30c30c2aa73cb2cb2cb2cb2cb1c71c71c71c71a92c92c69491cf1452c52c72473cf1492493cb1c524f14f24924f1c734f2c52cd3493cb34f14f1c52452c51cf34b24b14924f14b3c71cf14924934b34b3cb1c4d4734914914b1cf2cd2c71cd34934b3c734f14934b34f14b3c73c72cb19664b198e373c4e373371c8dc72965372371c65372371371cb394dc8d34d34d332cb1c4d34cc4ccf1332cf2c73c60208208348cb1c71c71208208208208208208332cb1c71c71c71c71c7234d34d333cf2c4d34ccf134cccccb234cc8cc8cc4cc73c8d34d333cf220d33333234cccccb1331c7234cccccb134ccccc8cc4cc4cc4cc71332cf1c9237237248dc8d34d34d1f2cf2c71c9237234d1f3cb2c714cd4f1ccdcd34cdcf34f1c5248d1f11f14b3cb1ccd347cf1347c87c87c47c73347cc7c87c47c47c47c47c47c47c71cb134d4b134cccccb2c92492332cb2c4d34d352333cb2c71451332331cb3352c92c52c51491cf1332cf1332cd2492487c4c4b1cf2c8730c1f1306c73c73cb2c734d31f24b34d24f1cd3c53c71cd3c474c71c71b1cf1cb1c871c71c6cf1c71c924921d2cd2cf21c6cc6cc6cf1cb11d21b1cc7c87c921b21b1cf2492486c72c521b11b21b1c86c86c86c46c71cf134d341cb134d1f2ccd347cc7c47c47c47c72c73c4d34cc87c7330c34ccccc87c711f11f1c721f1cccccd1f10721f31f31f31f1c471c71c6cf3cf11c71c6cf11c0c72032c471b31b11b11c6c46cc0c471b3031031c80cb2cf1c4104ccf3071071307332c471c1cb2c731f31c7047cc7cf2031c811f3072047cc0c80c40c711f3031c80c71cb2c72).1

def trmm2 : Tr := (dec 999 0x30c30c30c30c30c30c30c30c30c30c30c2b9b3cb2cb2cb2cb2cb2cb1c71c71c71c71c71c30c30c30c30c30c30c30c30c30c30aebab3cf2cb2cb2cb2cb2cb1c71c71c71c71c684314104104284314314314314314314314d34b3cd0c50c50c50c50c50410414c71c71c534d2cf3431431431431431410410531c71c714d34b3cd0c50c50c50c50c50410414c71c71c534d2cf3431431431431410410531c71c71cb2cb2cb2cb2cb2c70c30c30c30c30c30c30c30c30c2bab3cb2cb2cb2cb2cb1c71c71c71c714ebad3c93c714f2492493cb1c73cf14d3532c544d4cb3531c534d3532c71cd0532532531531531c534d2cf34f24f24f14d44f3c71cf14e6393c713b2392cf3cd34d34b3cf34f24d44f34f34f3cb1c544d4c53cf35315314d44f35314d31f2c73c73c72cb19a63cf3b2c663b23b1cf2acf3b3c934cecb1c4ecb198ec8e38e38dc7338dccdc72cf2c73c60208208208208808c88c8ec8ecb1c71c702322323b23b23b2c0ec8ec8ec8ec8ec8ec713b1c48cb1c71c71208208208208208208372cb1c71c71c71c71c7238e38e38e38dcf2cb1c71c4e38dc8e371cf220ec4ec4e372c4dc8dc73c8e38e372c4e372c7238e372c4dc8dc7338dc8dccdc8dc71372cf1c933b238e38e38e38e073cb1c71c71c725133b23b2531cce394072c714d34c1cb2c73cce381c81c71381c81c41c73cb14d3393ccd4f1cce373071cb2c8e48e372373cb34ce4f14b34cdcf2493c93c93c53c53c53c53c71cf1393c53c4dccdc8dc8dcb2cd34d3072c414c1c73c41c93341c4d347c71cf2cf2c735144f3cd4c54c54c41c81c93513cd4c53cf14c1c41c81c534d31f1c714c11f3c72cf20725011f1c931f21f11f1cc7072c87c714d31f1047cf21f1c87c73cf138e38e0b2cb1c4e38e372ccdcf2381cce073073071071071c81c41c71ccd04dcf1cce0710b2073073073c41041047cf3072c71041040cb11c7032cb3cc1040c721f3032c71c423423730b1373c410b2c73073042073073031c82080c40c71041031c73031c80c71cb2c72).1

def trmm3 : Tr := (dec 999 0x27c30c30c30c30c30c30c30c30c30c30b2bcf2cb2cb2cb2cb2cb1c71c71c71c71c684314104104144f3431431431431513cd0c50c54c50410571c71c544f3431431531410415c71c71513cd0c50c54c50410571c71c544f3431431531410415c71c71cb2cb2cb2cb2cb2c6cb14c94c72c14c94c94c54c54c54c71acf3d3cf3cac4d4c714d4c54c724d34d4cb1c73513cd4c94c54c72c735144f3cd44f3531531531c94c94c94c94c54554571cd4cf2c55533572571571514515533cb1c54572571514571533c73c73c71cb19e79cfc8fc729cfc8fc4f3cf3cecb13cec4ec72cf3cb1c602083c8cb1c7120820820820820820ecb1c71c71c71c71c723cf3cecf2c4f3cf3b2c4ec7320f3b33b23ceccec8ec713b13b1c4ec723b1cc820ec723ceccecb13b23b13b1cb1c8f3cf3cf0b10b1cf2cb13d43c2c42c72c545145145140b2cb1c71c71ccf0b20b20b10b10b1cb13d4c4f5313d4c4eccecb2c8f3cf3ceccecb3cb15144cecb3cd4c713cec8ec8ec4ec4ec4ec4ec4ec72cd4514502c94cf1c42382533c4e0b1cb3cb2c73554554cd5c71cc25330b20b10b10b10b10b10b10b1c95082073c72c42082071c71c94514094cd4cf2514072c41c81c71cb1082071c54071072071cf2501c81c81c81c41c71cf13cf3b33b2c8f3b23b20b1ccecce0b3c823b308e0f2c82cf2c420820c2cf2cb2c420820810b2cc2cb1c71082031c420c2cc0c42cf2031cb2082032c41080c41cc0cb2cc2073073081cc0c72032c40cb1c72c72).1

theorem c_pp0 : chk (1) (1) trpp0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_pp1 : chk (1) (1) trpp1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_pp2 : chk (1) (1) trpp2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_pp3 : chk (1) (1) trpp3 0 4096 0 4096 (32) (64) = true := by decide +kernel
theorem c_pm0 : chk (1) (-1) trpm0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_pm1 : chk (1) (-1) trpm1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_pm2 : chk (1) (-1) trpm2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_pm3 : chk (1) (-1) trpm3 0 4096 0 4096 (32) (64) = true := by decide +kernel
theorem c_mp0 : chk (-1) (1) trmp0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_mp1 : chk (-1) (1) trmp1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_mp2 : chk (-1) (1) trmp2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_mp3 : chk (-1) (1) trmp3 0 4096 0 4096 (32) (64) = true := by decide +kernel
theorem c_mm0 : chk (-1) (-1) trmm0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_mm1 : chk (-1) (-1) trmm1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_mm2 : chk (-1) (-1) trmm2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_mm3 : chk (-1) (-1) trmm3 0 4096 0 4096 (32) (64) = true := by decide +kernel

noncomputable def Dr (σ α β u v κ1 κ2 : ℝ) : ℝ :=
  4 * α ^ 2 + 4 * α * β + 65 / 16 * β ^ 2 - 4 * α * (κ1 * u + κ2 * v)
    - 2 * β * ((κ1 * u + κ2 * v) + 7 / 4 * σ * (κ2 * u - κ1 * v)) + κ1 ^ 2 + κ2 ^ 2

noncomputable def G (σ ε α β κ1 κ2 pu pv pw : ℝ) : ℝ :=
  (4 * α ^ 2 + 4 * α * β + 65 / 16 * β ^ 2 + κ1 ^ 2 + κ2 ^ 2 - 1 / 4) * pw
    + ε * ((-4 * α * κ1 - 2 * β * (κ1 + 7 / 4 * σ * κ2)) * pu
      + (-4 * α * κ2 - 2 * β * (κ2 - 7 / 4 * σ * κ1)) * pv)

lemma Dz_G (sg ep A B PU PV PW k1 k2 : ℤ) :
    ((Dz sg A B (ep * PU) (ep * PV) PW k1 k2 : ℤ) : ℝ) - 671088640000 * (PW : ℝ)
      = 2684354560000 * G sg ep ((A : ℝ) / 4096) ((B : ℝ) / 4096) ((k1 : ℝ) / 100) ((k2 : ℝ) / 100)
        PU PV PW := by
  unfold Dz G
  push_cast
  ring

lemma ok1_G (sg ep A B PU PV PW k1 k2 : ℤ) (h : ok1 sg A B (ep * PU) (ep * PV) PW k1 k2 = true) :
    G sg ep ((A : ℝ) / 4096) ((B : ℝ) / 4096) ((k1 : ℝ) / 100) ((k2 : ℝ) / 100) PU PV PW < 0 := by
  unfold ok1 at h
  have h1 : Dz sg A B (ep * PU) (ep * PV) PW k1 k2 < 671088640000 * PW := of_decide_eq_true h
  have h2 : ((Dz sg A B (ep * PU) (ep * PV) PW k1 k2 : ℤ) : ℝ) < 671088640000 * (PW : ℝ) := by
    exact_mod_cast h1
  have h3 := Dz_G sg ep A B PU PV PW k1 k2
  linarith

lemma G_hom (σ ε α β κ1 κ2 pu pv pw c : ℝ) :
    G σ ε α β κ1 κ2 (c * pu) (c * pv) (c * pw) = c * G σ ε α β κ1 κ2 pu pv pw := by
  unfold G
  ring

lemma G_tri (σ ε α β κ1 κ2 a b x : ℝ) (hab : a < b) (_hab1 : 0 < 1 + a * b) (hxa : a ≤ x)
    (hxb : x ≤ b) (ha : G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2) < 0)
    (hb : G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2) < 0)
    (hT : G σ ε α β κ1 κ2 (1 - a * b) (a + b) (1 + a * b) < 0) :
    G σ ε α β κ1 κ2 (1 - x ^ 2) (2 * x) (1 + x ^ 2) < 0 := by
  have key : (b - a) ^ 2 * G σ ε α β κ1 κ2 (1 - x ^ 2) (2 * x) (1 + x ^ 2)
      = (b - x) ^ 2 * G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2)
        + (x - a) ^ 2 * G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2)
        + 2 * (x - a) * (b - x) * G σ ε α β κ1 κ2 (1 - a * b) (a + b) (1 + a * b) := by
    unfold G
    ring
  have hba : 0 < (b - a) ^ 2 := by nlinarith
  have e1 : (b - x) ^ 2 * G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ha.le
  have e2 : (x - a) ^ 2 * G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hb.le
  have e3 : 2 * (x - a) * (b - x) * G σ ε α β κ1 κ2 (1 - a * b) (a + b) (1 + a * b) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos _ hT.le
    have : 0 ≤ (x - a) * (b - x) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hpos : 0 < (b - x) ^ 2 + (x - a) ^ 2 := by
    rcases lt_or_ge x b with h | h
    · nlinarith
    · nlinarith
  have e4 : (b - x) ^ 2 * G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2)
      + (x - a) ^ 2 * G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2) < 0 := by
    rcases lt_or_ge x b with h | h
    · have : 0 < (b - x) ^ 2 := by nlinarith
      have := mul_neg_of_pos_of_neg this ha
      linarith
    · have : 0 < (x - a) ^ 2 := by nlinarith
      have := mul_neg_of_pos_of_neg this hb
      linarith
  by_contra hc
  rw [not_lt] at hc
  have := mul_nonneg hba.le hc
  linarith

lemma G_Dr (σ ε α β κ1 κ2 x : ℝ) :
    (1 + x ^ 2) * (Dr σ α β (ε * ((1 - x ^ 2) / (1 + x ^ 2))) (ε * (2 * x / (1 + x ^ 2))) κ1 κ2 - 1 / 4)
      = G σ ε α β κ1 κ2 (1 - x ^ 2) (2 * x) (1 + x ^ 2) := by
  have h : (1 + x ^ 2) ≠ 0 := by positivity
  unfold Dr G
  field_simp
  ring

lemma stepA (σ α0 α1 α β u v κ1 κ2 M : ℝ) (h0 : Dr σ α0 β u v κ1 κ2 < M)
    (h1 : Dr σ α1 β u v κ1 κ2 < M) (ha0 : α0 ≤ α) (ha1 : α ≤ α1) : Dr σ α β u v κ1 κ2 < M := by
  have key : (α1 - α0) * (Dr σ α β u v κ1 κ2 - M) = (α1 - α) * (Dr σ α0 β u v κ1 κ2 - M)
      + (α - α0) * (Dr σ α1 β u v κ1 κ2 - M) - 4 * (α1 - α0) * (α - α0) * (α1 - α) := by
    unfold Dr
    ring
  rcases eq_or_lt_of_le (le_trans ha0 ha1) with he | hlt
  · have e1 : α = α0 := by linarith
    rw [e1]; exact h0
  · have p1 : 0 ≤ (α1 - α) * (M - Dr σ α0 β u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (α - α0) * (M - Dr σ α1 β u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p3 : 0 ≤ (α1 - α0) * (α - α0) * (α1 - α) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have p4 : 0 < (α1 - α) * (M - Dr σ α0 β u v κ1 κ2) + (α - α0) * (M - Dr σ α1 β u v κ1 κ2) := by
      rcases lt_or_ge α α1 with h | h
      · have := mul_pos (sub_pos.2 h) (sub_pos.2 h0); linarith
      · have := mul_pos (show (0:ℝ) < α - α0 by linarith) (sub_pos.2 h1); linarith
    by_contra hc
    rw [not_lt] at hc
    have := mul_nonneg (sub_pos.2 hlt).le (sub_nonneg.2 hc)
    linarith

lemma stepB (σ α β0 β1 β u v κ1 κ2 M : ℝ) (h0 : Dr σ α β0 u v κ1 κ2 < M)
    (h1 : Dr σ α β1 u v κ1 κ2 < M) (hb0 : β0 ≤ β) (hb1 : β ≤ β1) : Dr σ α β u v κ1 κ2 < M := by
  have key : (β1 - β0) * (Dr σ α β u v κ1 κ2 - M) = (β1 - β) * (Dr σ α β0 u v κ1 κ2 - M)
      + (β - β0) * (Dr σ α β1 u v κ1 κ2 - M) - 65 / 16 * (β1 - β0) * (β - β0) * (β1 - β) := by
    unfold Dr
    ring
  rcases eq_or_lt_of_le (le_trans hb0 hb1) with he | hlt
  · have e1 : β = β0 := by linarith
    rw [e1]; exact h0
  · have p1 : 0 ≤ (β1 - β) * (M - Dr σ α β0 u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (β - β0) * (M - Dr σ α β1 u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p3 : 0 ≤ (β1 - β0) * (β - β0) * (β1 - β) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have p4 : 0 < (β1 - β) * (M - Dr σ α β0 u v κ1 κ2) + (β - β0) * (M - Dr σ α β1 u v κ1 κ2) := by
      rcases lt_or_ge β β1 with h | h
      · have := mul_pos (sub_pos.2 h) (sub_pos.2 h0); linarith
      · have := mul_pos (show (0:ℝ) < β - β0 by linarith) (sub_pos.2 h1); linarith
    by_contra hc
    rw [not_lt] at hc
    have := mul_nonneg (sub_pos.2 hlt).le (sub_nonneg.2 hc)
    linarith

lemma corner (sg ep : ℤ) (c : ℕ) (S T j0 j1 : ℤ) (h : okc sg ep c S T j0 j1 = true)
    (hj : j0 < j1) (hj1 : 0 < 4096 + j0 * j1) (x : ℝ) (hx0 : (j0 : ℝ) / 64 ≤ x)
    (hx1 : x ≤ (j1 : ℝ) / 64) :
    Dr sg ((amn (c / 8) : ℝ) - (S : ℝ) / 4096) ((bmn (c / 8) : ℝ) - (T : ℝ) / 4096)
      (ep * ((1 - x ^ 2) / (1 + x ^ 2))) (ep * (2 * x / (1 + x ^ 2)))
      ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  unfold okc at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have g1 := ok1_G _ _ _ _ _ _ _ _ _ h1
  have g2 := ok1_G _ _ _ _ _ _ _ _ _ h2
  have g3 := ok1_G _ _ _ _ _ _ _ _ _ h3
  set α : ℝ := (amn (c / 8) : ℝ) - (S : ℝ) / 4096 with hα
  set β : ℝ := (bmn (c / 8) : ℝ) - (T : ℝ) / 4096 with hβ
  have eA : (((amn (c / 8) * 4096 - S : ℤ) : ℝ) / 4096) = α := by rw [hα]; push_cast; ring
  have eB : (((bmn (c / 8) * 4096 - T : ℤ) : ℝ) / 4096) = β := by rw [hβ]; push_cast; ring
  rw [eA, eB] at g1 g2 g3
  set a : ℝ := (j0 : ℝ) / 64 with ha
  set b : ℝ := (j1 : ℝ) / 64 with hb
  have q1 : (((4096 - j0 * j0 : ℤ) : ℝ)) = 4096 * (1 - a ^ 2) := by rw [ha]; push_cast; ring
  have q2 : (((128 * j0 : ℤ) : ℝ)) = 4096 * (2 * a) := by rw [ha]; push_cast; ring
  have q3 : (((4096 + j0 * j0 : ℤ) : ℝ)) = 4096 * (1 + a ^ 2) := by rw [ha]; push_cast; ring
  have r1 : (((4096 - j1 * j1 : ℤ) : ℝ)) = 4096 * (1 - b ^ 2) := by rw [hb]; push_cast; ring
  have r2 : (((128 * j1 : ℤ) : ℝ)) = 4096 * (2 * b) := by rw [hb]; push_cast; ring
  have r3 : (((4096 + j1 * j1 : ℤ) : ℝ)) = 4096 * (1 + b ^ 2) := by rw [hb]; push_cast; ring
  have t1 : (((4096 - j0 * j1 : ℤ) : ℝ)) = 4096 * (1 - a * b) := by rw [ha, hb]; push_cast; ring
  have t2 : (((64 * (j0 + j1) : ℤ) : ℝ)) = 4096 * (a + b) := by rw [ha, hb]; push_cast; ring
  have t3 : (((4096 + j0 * j1 : ℤ) : ℝ)) = 4096 * (1 + a * b) := by rw [ha, hb]; push_cast; ring
  rw [q1, q2, q3, G_hom] at g1
  rw [r1, r2, r3, G_hom] at g2
  rw [t1, t2, t3, G_hom] at g3
  have hab : a < b := by
    rw [ha, hb]
    have : (j0 : ℝ) < j1 := by exact_mod_cast hj
    linarith
  have hab1 : 0 < 1 + a * b := by
    have : (0 : ℝ) < 4096 + (j0 : ℝ) * j1 := by exact_mod_cast hj1
    rw [ha, hb]
    nlinarith
  have gx := G_tri (sg : ℝ) (ep : ℝ) α β ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) a b x
    hab hab1 hx0 hx1 (by nlinarith) (by nlinarith) (by nlinarith)
  have e := G_Dr (sg : ℝ) (ep : ℝ) α β ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) x
  rw [← e] at gx
  have hx2 : 0 < 1 + x ^ 2 := by positivity
  by_contra hc
  rw [not_lt] at hc
  have := mul_nonneg hx2.le (sub_nonneg.2 hc)
  linarith

lemma leaf_sound (sg ep : ℤ) (c : ℕ) (S0 S1 T0 T1 j0 j1 : ℤ)
    (h : leafok sg ep c S0 S1 T0 T1 j0 j1 = true) (s t x : ℝ) (hs0 : (S0 : ℝ) / 4096 ≤ s)
    (hs1 : s ≤ (S1 : ℝ) / 4096) (ht0 : (T0 : ℝ) / 4096 ≤ t) (ht1 : t ≤ (T1 : ℝ) / 4096)
    (hx0 : (j0 : ℝ) / 64 ≤ x) (hx1 : x ≤ (j1 : ℝ) / 64) :
    Dr sg ((amn (c / 8) : ℝ) - s) ((bmn (c / 8) : ℝ) - t)
      (ep * ((1 - x ^ 2) / (1 + x ^ 2))) (ep * (2 * x / (1 + x ^ 2)))
      ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  unfold leafok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hj, _⟩, _⟩, hj1⟩, c00⟩, c01⟩, c10⟩, c11⟩ := h
  have d00 := corner sg ep c S0 T0 j0 j1 c00 hj hj1 x hx0 hx1
  have d01 := corner sg ep c S0 T1 j0 j1 c01 hj hj1 x hx0 hx1
  have d10 := corner sg ep c S1 T0 j0 j1 c10 hj hj1 x hx0 hx1
  have d11 := corner sg ep c S1 T1 j0 j1 c11 hj hj1 x hx0 hx1
  have b0 := stepB _ _ _ _ _ _ _ _ _ _ d01 d00 (show (bmn (c / 8) : ℝ) - (T1 : ℝ) / 4096
    ≤ (bmn (c / 8) : ℝ) - t by linarith) (show (bmn (c / 8) : ℝ) - t
    ≤ (bmn (c / 8) : ℝ) - (T0 : ℝ) / 4096 by linarith)
  have b1 := stepB _ _ _ _ _ _ _ _ _ _ d11 d10 (show (bmn (c / 8) : ℝ) - (T1 : ℝ) / 4096
    ≤ (bmn (c / 8) : ℝ) - t by linarith) (show (bmn (c / 8) : ℝ) - t
    ≤ (bmn (c / 8) : ℝ) - (T0 : ℝ) / 4096 by linarith)
  exact stepA _ _ _ _ _ _ _ _ _ _ b1 b0 (by linarith) (by linarith)

lemma chk_sound (sg ep : ℤ) (tr : Tr) : ∀ (S0 S1 T0 T1 j0 j1 : ℤ),
    chk sg ep tr S0 S1 T0 T1 j0 j1 = true → ∀ s t x : ℝ, (S0 : ℝ) / 4096 ≤ s →
    s ≤ (S1 : ℝ) / 4096 → (T0 : ℝ) / 4096 ≤ t → t ≤ (T1 : ℝ) / 4096 → (j0 : ℝ) / 64 ≤ x →
    x ≤ (j1 : ℝ) / 64 → s + t ≤ 1 → ∃ c : ℕ, Dr sg ((amn (c / 8) : ℝ) - s) ((bmn (c / 8) : ℝ) - t)
      (ep * ((1 - x ^ 2) / (1 + x ^ 2))) (ep * (2 * x / (1 + x ^ 2)))
      ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  induction tr with
  | l c =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 _
    exact ⟨c, leaf_sound sg ep c S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1⟩
  | q c =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 _ ht0 _ hx0 hx1 hst
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hq, h⟩ := h
    have hq' : (4096 : ℝ) ≤ (S0 : ℝ) + T0 := by exact_mod_cast hq
    exact ⟨c, leaf_sound sg ep c S0 S0 T0 T0 j0 j1 h s t x hs0 (by linarith) ht0 (by linarith)
      hx0 hx1⟩
  | k =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 _ ht0 _ _ _ hst
    simp only [chk, decide_eq_true_eq] at h
    have hq' : (4096 : ℝ) < (S0 : ℝ) + T0 := by exact_mod_cast h
    exfalso
    linarith
  | s a b iha ihb =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 hst
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total s ((((S0 + S1) / 2 : ℤ) : ℝ) / 4096) with hm | hm
    · exact iha _ _ _ _ _ _ h.1 s t x hs0 hm ht0 ht1 hx0 hx1 hst
    · exact ihb _ _ _ _ _ _ h.2 s t x hm hs1 ht0 ht1 hx0 hx1 hst
  | t a b iha ihb =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 hst
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total t ((((T0 + T1) / 2 : ℤ) : ℝ) / 4096) with hm | hm
    · exact iha _ _ _ _ _ _ h.1 s t x hs0 hs1 ht0 hm hx0 hx1 hst
    · exact ihb _ _ _ _ _ _ h.2 s t x hs0 hs1 hm ht1 hx0 hx1 hst
  | j a b iha ihb =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 hst
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total x ((((j0 + j1) / 2 : ℤ) : ℝ) / 64) with hm | hm
    · exact iha _ _ _ _ _ _ h.1 s t x hs0 hs1 ht0 ht1 hx0 hm hst
    · exact ihb _ _ _ _ _ _ h.2 s t x hs0 hs1 ht0 ht1 hm hx1 hst

lemma chart0 (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (hu : 0 ≤ u) : ∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧
    u = (1 - x ^ 2) / (1 + x ^ 2) ∧ v = 2 * x / (1 + x ^ 2) := by
  have h1 : 0 < 1 + u := by linarith
  refine ⟨v / (1 + u), ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h1]; nlinarith
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination (1 + u) * h
  · rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination v * h

lemma chart (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) : ∃ ep : ℤ, (ep = 1 ∨ ep = -1) ∧ ∃ x : ℝ,
    -1 ≤ x ∧ x ≤ 1 ∧ u = (ep : ℝ) * ((1 - x ^ 2) / (1 + x ^ 2)) ∧
      v = (ep : ℝ) * (2 * x / (1 + x ^ 2)) := by
  rcases le_total 0 u with hu | hu
  · obtain ⟨x, h1, h2, h3, h4⟩ := chart0 u v h hu
    exact ⟨1, Or.inl rfl, x, h1, h2, by rw [h3]; push_cast; ring, by rw [h4]; push_cast; ring⟩
  · obtain ⟨x, h1, h2, h3, h4⟩ := chart0 (-u) (-v) (by linear_combination h) (by linarith)
    exact ⟨-1, Or.inr rfl, x, h1, h2, by push_cast; linarith, by push_cast; linarith⟩

lemma geo (sg : ℤ) (hsg : sg = 1 ∨ sg = -1) (u v s t : ℝ) (huv : u ^ 2 + v ^ 2 = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) : ∃ c : ℕ,
      Dr sg ((amn (c / 8) : ℝ) - s) ((bmn (c / 8) : ℝ) - t) u v
        ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  obtain ⟨ep, hep, x, hx0, hx1, hu, hv⟩ := chart u v huv
  rw [hu, hv]
  rcases hsg with rfl | rfl <;> rcases hep with rfl | rfl
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trpp0 0 4096 0 4096 (-64) (-32) c_pp0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trpp1 0 4096 0 4096 (-32) (0) c_pp1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trpp2 0 4096 0 4096 (0) (32) c_pp2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trpp3 0 4096 0 4096 (32) (64) c_pp3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trpm0 0 4096 0 4096 (-64) (-32) c_pm0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trpm1 0 4096 0 4096 (-32) (0) c_pm1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trpm2 0 4096 0 4096 (0) (32) c_pm2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trpm3 0 4096 0 4096 (32) (64) c_pm3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trmp0 0 4096 0 4096 (-64) (-32) c_mp0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trmp1 0 4096 0 4096 (-32) (0) c_mp1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trmp2 0 4096 0 4096 (0) (32) c_mp2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trmp3 0 4096 0 4096 (32) (64) c_mp3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trmm0 0 4096 0 4096 (-64) (-32) c_mm0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trmm1 0 4096 0 4096 (-32) (0) c_mm1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trmm2 0 4096 0 4096 (0) (32) c_mm2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trmm3 0 4096 0 4096 (32) (64) c_mm3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst

lemma sign_lemma {ι : Type*} (C C' : ι → ℝ) (hC : ∀ i j, C i * C j = C' i * C' j) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ i, C i = σ * C' i := by
  by_cases h : ∀ i, C' i = 0
  · refine ⟨1, by norm_num, fun i => ?_⟩
    have := hC i i
    rw [h i] at this ⊢
    have h2 : C i ^ 2 = 0 := by nlinarith
    simpa using h2
  · simp only [not_forall] at h
    obtain ⟨r, hr⟩ := h
    have hrr := hC r r
    refine ⟨C r / C' r, ?_, fun i => ?_⟩
    · rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hr)]
      linear_combination hrr
    · have hir := hC i r
      have hz : C' r * (C i * C' r - C r * C' i) = 0 := by
        linear_combination (-C i) * hrr + C r * hir
      rcases mul_eq_zero.mp hz with h0 | h0
      · exact absurd h0 hr
      · rw [div_mul_eq_mul_div, eq_div_iff hr]
        linear_combination h0

lemma alg_step (D1 D2 P1 P2 Q1 Q2 w1 w2 W1 W2 σ k0x k0y kix kiy lx ly pix piy : ℝ)
    (hs : w1 ^ 2 + w2 ^ 2 = W1 ^ 2 + W2 ^ 2) (hne : W1 ^ 2 + W2 ^ 2 ≠ 0) (hσ2 : σ ^ 2 = 1)
    (hA : P1 * w1 + P2 * w2 = Q1 * W1 + Q2 * W2) (hC : P1 * w2 - P2 * w1 = σ * (Q1 * W2 - Q2 * W1))
    (hQ1 : kix = k0x + Q1) (hQ2 : kiy = k0y + Q2) (hD1 : lx - pix = D1 - P1)
    (hD2 : ly - piy = D2 - P2) :
    (k0x + ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2) / (W1 ^ 2 + W2 ^ 2) - kix) ^ 2
      + (k0y + ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
        - kiy) ^ 2 = (lx - pix) ^ 2 + (ly - piy) ^ 2 := by
  rw [hD1, hD2, hQ1, hQ2]
  have e1 : (W1 ^ 2 + W2 ^ 2) * ((k0x + ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2)
        / (W1 ^ 2 + W2 ^ 2) - (k0x + Q1)) ^ 2
      + (k0y + ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
        - (k0y + Q2)) ^ 2)
      = ((D1 * w1 + D2 * w2) - (Q1 * W1 + Q2 * W2)) ^ 2
        + (σ * (D1 * w2 - D2 * w1) - (Q1 * W2 - Q2 * W1)) ^ 2 := by
    field_simp
    ring
  have e2 : (W1 ^ 2 + W2 ^ 2) * ((D1 - P1) ^ 2 + (D2 - P2) ^ 2)
      = ((D1 * w1 + D2 * w2) - (P1 * w1 + P2 * w2)) ^ 2
        + ((D1 * w2 - D2 * w1) - (P1 * w2 - P2 * w1)) ^ 2 := by
    rw [← hs]
    ring
  have e3 : ((D1 * w2 - D2 * w1) - (P1 * w2 - P2 * w1)) ^ 2
      = (σ * (D1 * w2 - D2 * w1) - (Q1 * W2 - Q2 * W1)) ^ 2 := by
    rw [hC]
    linear_combination ((Q1 * W2 - Q2 * W1) ^ 2 - (D1 * w2 - D2 * w1) ^ 2) * hσ2
  apply mul_left_cancel₀ hne
  rw [e1, e2, e3, hA]


lemma transfer2 {ι : Type*} (px py kx ky : ι → ℝ) (i0 i1 : ι)
    (hd : ∀ i j, (px i - px j) ^ 2 + (py i - py j) ^ 2 = (kx i - kx j) ^ 2 + (ky i - ky j) ^ 2)
    (hne : (kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2 ≠ 0) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ (lx ly : ℝ) (i : ι),
      (kx i0 + (((lx - px i0) * (px i1 - px i0) + (ly - py i0) * (py i1 - py i0)) * (kx i1 - kx i0)
        + σ * ((lx - px i0) * (py i1 - py i0) - (ly - py i0) * (px i1 - px i0)) * (ky i1 - ky i0))
        / ((kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2) - kx i) ^ 2
      + (ky i0 + (((lx - px i0) * (px i1 - px i0) + (ly - py i0) * (py i1 - py i0)) * (ky i1 - ky i0)
        - σ * ((lx - px i0) * (py i1 - py i0) - (ly - py i0) * (px i1 - px i0)) * (kx i1 - kx i0))
        / ((kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2) - ky i) ^ 2
      = (lx - px i) ^ 2 + (ly - py i) ^ 2 := by
  have hs : (px i1 - px i0) ^ 2 + (py i1 - py i0) ^ 2 = (kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2 :=
    hd i1 i0
  have hA : ∀ i, (px i - px i0) * (px i1 - px i0) + (py i - py i0) * (py i1 - py i0)
      = (kx i - kx i0) * (kx i1 - kx i0) + (ky i - ky i0) * (ky i1 - ky i0) := by
    intro i
    have h1 := hd i i0
    have h2 := hd i i1
    linear_combination (h1 + hs - h2) / 2
  have hC : ∀ i j, ((px i - px i0) * (py i1 - py i0) - (py i - py i0) * (px i1 - px i0)) *
        ((px j - px i0) * (py i1 - py i0) - (py j - py i0) * (px i1 - px i0))
      = ((kx i - kx i0) * (ky i1 - ky i0) - (ky i - ky i0) * (kx i1 - kx i0)) *
        ((kx j - kx i0) * (ky i1 - ky i0) - (ky j - ky i0) * (kx i1 - kx i0)) := by
    intro i j
    have hAi := hA i
    have hAj := hA j
    have h1 := hd i i0
    have h2 := hd j i0
    have h3 := hd i j
    linear_combination ((px i1 - px i0) ^ 2 + (py i1 - py i0) ^ 2) * (h1 + h2 - h3) / 2
      + (((kx i - kx i0) * (kx j - kx i0) + (ky i - ky i0) * (ky j - ky i0))) * hs
      - ((px i - px i0) * (px i1 - px i0) + (py i - py i0) * (py i1 - py i0)) * hAj
      - ((kx j - kx i0) * (kx i1 - kx i0) + (ky j - ky i0) * (ky i1 - ky i0)) * hAi
  obtain ⟨σ, hσ2, hσ⟩ := sign_lemma
    (fun i => (px i - px i0) * (py i1 - py i0) - (py i - py i0) * (px i1 - px i0))
    (fun i => (kx i - kx i0) * (ky i1 - ky i0) - (ky i - ky i0) * (kx i1 - kx i0)) hC
  exact ⟨σ, hσ2, fun lx ly i => alg_step (lx - px i0) (ly - py i0) (px i - px i0) (py i - py i0)
    (kx i - kx i0) (ky i - ky i0) (px i1 - px i0) (py i1 - py i0) (kx i1 - kx i0) (ky i1 - ky i0)
    σ (kx i0) (ky i0) (kx i) (ky i) (lx) (ly) (px i) (py i) hs hne hσ2 (hA i) (hσ i)
    (by ring) (by ring) (by ring) (by ring)⟩

lemma lattice_sep_int (da db : ℤ) (h : da ≠ 0 ∨ db ≠ 0) :
    64 ≤ 16 * (2 * da + db) ^ 2 + 49 * db ^ 2 := by
  have hc : db = 0 ∨ db = 1 ∨ db = -1 ∨ 2 ≤ db ∨ db ≤ -2 := by omega
  rcases hc with hc | hc | hc | hc | hc
  · subst hc
    have : da ≤ -1 ∨ 1 ≤ da := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + 1 ≤ -1 ∨ 1 ≤ 2 * da + 1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + -1 ≤ -1 ∨ 1 ≤ 2 * da + -1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · nlinarith [sq_nonneg (2 * da + db)]
  · nlinarith [sq_nonneg (2 * da + db)]


noncomputable def L (a b : ℤ) : ℝ² := !₂[2 * (a : ℝ) + b, 7 / 4 * (b : ℝ)]

def S : Set ℝ² := {x | ∃ a b : ℤ, dist x (L a b) < 1 / 2}

noncomputable def K (i : Fin 8) : ℝ² := !₂[(kxn i.val : ℝ) / 100, (kyn i.val : ℝ) / 100]

lemma dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

lemma L_sep (a b a' b' : ℤ) (h : (a, b) ≠ (a', b')) : 2 ≤ dist (L a b) (L a' b') := by
  have h1 : a - a' ≠ 0 ∨ b - b' ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    apply h
    have e1 : a = a' := by omega
    have e2 : b = b' := by omega
    rw [e1, e2]
  have h2 := lattice_sep_int (a - a') (b - b') h1
  have h2' : (64 : ℝ) ≤ 16 * (2 * ((a : ℝ) - a') + ((b : ℝ) - b')) ^ 2 + 49 * ((b : ℝ) - b') ^ 2 := by
    exact_mod_cast h2
  have h3 : dist (L a b) (L a' b') ^ 2
      = (2 * (a : ℝ) + b - (2 * a' + b')) ^ 2 + (7 / 4 * (b : ℝ) - 7 / 4 * b') ^ 2 := by
    rw [dist_sq]
    simp [L]
  have h4 : (4 : ℝ) ≤ dist (L a b) (L a' b') ^ 2 := by
    rw [h3]
    nlinarith
  nlinarith [dist_nonneg (x := L a b) (y := L a' b')]

lemma S_avoid : Erdos214.UnitDistanceAvoiding S := by
  intro x hx y hy hxy
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨a', b', hab'⟩ := hy
  by_cases he : (a, b) = (a', b')
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := dist_triangle_right x y (L a b)
    linarith
  · have h2 := L_sep a b a' b' he
    have t1 := dist_triangle (L a b) x (L a' b')
    have t2 := dist_triangle x y (L a' b')
    rw [dist_comm] at hab
    linarith

lemma K_inj_aux : ∀ i j : Fin 8, kxn i.val = kxn j.val → kyn i.val = kyn j.val → i = j := by
  decide

lemma K_inj : Function.Injective K := by
  intro i j h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp [K] at h0 h1
  exact K_inj_aux i j (by exact_mod_cast h0) (by exact_mod_cast h1)

lemma alg_fin (σ σ' lx ly px0 py0 px1 py1 kx0 ky0 kx1 ky1 A B κ1 κ2 u v : ℝ) (hk0 : kx0 = 0)
    (hk0' : ky0 = 0) (hW : (kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2 ≠ 0) (hσ2 : σ ^ 2 = 1)
    (hu : u = ((px1 - px0) * (kx1 - kx0) + σ * (py1 - py0) * (ky1 - ky0))
      / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2))
    (hv : v = ((px1 - px0) * (ky1 - ky0) - σ * (py1 - py0) * (kx1 - kx0))
      / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2))
    (huv : u ^ 2 + v ^ 2 = 1) (hσ' : σ' ^ 2 = 1) (hD1 : lx - px0 = 2 * A + B)
    (hD2 : ly - py0 = 7 / 4 * (σ' * σ) * B) :
    (kx0 + (((lx - px0) * (px1 - px0) + (ly - py0) * (py1 - py0)) * (kx1 - kx0)
        + σ * ((lx - px0) * (py1 - py0) - (ly - py0) * (px1 - px0)) * (ky1 - ky0))
        / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2) - κ1) ^ 2
      + (ky0 + (((lx - px0) * (px1 - px0) + (ly - py0) * (py1 - py0)) * (ky1 - ky0)
        - σ * ((lx - px0) * (py1 - py0) - (ly - py0) * (px1 - px0)) * (kx1 - kx0))
        / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2) - κ2) ^ 2
      = Dr σ' A B u v κ1 κ2 := by
  set D1 := lx - px0 with eD1
  set D2 := ly - py0 with eD2
  set w1 := px1 - px0 with ew1
  set w2 := py1 - py0 with ew2
  set W1 := kx1 - kx0 with eW1
  set W2 := ky1 - ky0 with eW2
  have ex : ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2) / (W1 ^ 2 + W2 ^ 2)
      = D1 * u - σ * D2 * v := by
    rw [hu, hv]
    field_simp
    linear_combination (-(D2 * w2 * W1)) * hσ2
  have ey : ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
      = D1 * v + σ * D2 * u := by
    rw [hu, hv]
    field_simp
    linear_combination (-(D2 * w2 * W2)) * hσ2
  rw [ex, ey, hD1, hD2, hk0, hk0']
  unfold Dr
  linear_combination ((2 * A + B) ^ 2 + 49 / 16 * B ^ 2 * σ' ^ 2 * σ ^ 4) * huv
    + (49 / 16 * B ^ 2 * σ' ^ 2 * (σ ^ 2 + 1) - 7 / 2 * σ' * B * (κ2 * u - κ1 * v)) * hσ2
    + 49 / 16 * B ^ 2 * hσ'

lemma main (p : Fin 8 → ℝ²) (hpS : ∀ i, p i ∈ Sᶜ) (hc : p ≅ K) : False := by
  have hd : ∀ i j, (p i 0 - p j 0) ^ 2 + (p i 1 - p j 1) ^ 2
      = (K i 0 - K j 0) ^ 2 + (K i 1 - K j 1) ^ 2 := by
    intro i j
    rw [← dist_sq, ← dist_sq, (congruent_iff_dist_eq.mp hc) i j]
  have hK0 : K 0 0 = 0 ∧ K 0 1 = 0 := by simp [K, kxn, kyn]
  have hK1 : K 1 0 = 4 / 5 ∧ K 1 1 = 0 := by
    simp [K, kxn, kyn]
    norm_num
  have hne : (K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2 ≠ 0 := by
    rw [hK0.1, hK0.2, hK1.1, hK1.2]
    norm_num
  obtain ⟨σ, hσ2, hz⟩ := transfer2 (fun i => p i 0) (fun i => p i 1) (fun i => K i 0)
    (fun i => K i 1) 0 1 hd hne
  simp only at hz
  have hs : (p 1 0 - p 0 0) ^ 2 + (p 1 1 - p 0 1) ^ 2
      = (K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2 := hd 1 0
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ((p 1 0 - p 0 0) * (K 1 0 - K 0 0)
      + σ * (p 1 1 - p 0 1) * (K 1 1 - K 0 1)) / ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = ((p 1 0 - p 0 0) * (K 1 1 - K 0 1)
      - σ * (p 1 1 - p 0 1) * (K 1 0 - K 0 0)) / ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) :=
    ⟨_, rfl⟩
  have huv' : ((p 1 0 - p 0 0) * (K 1 0 - K 0 0) + σ * (p 1 1 - p 0 1) * (K 1 1 - K 0 1)) ^ 2
      + ((p 1 0 - p 0 0) * (K 1 1 - K 0 1) - σ * (p 1 1 - p 0 1) * (K 1 0 - K 0 0)) ^ 2
      = ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) ^ 2 := by
    linear_combination ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) * hs
      + ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) * (p 1 1 - p 0 1) ^ 2 * hσ2
  have huv : u ^ 2 + v ^ 2 = 1 := by
    rw [hu, hv, div_pow, div_pow, ← add_div, huv', div_self (pow_ne_zero 2 hne)]
  have key : ∀ (c : ℕ) (LA LB : ℤ) (A' B' σ' : ℝ), σ' ^ 2 = 1 →
      2 * (LA : ℝ) + LB - p 0 0 = 2 * A' + B' → 7 / 4 * (LB : ℝ) - p 0 1 = 7 / 4 * (σ' * σ) * B' →
      Dr σ' A' B' u v ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 → False := by
    intro c LA LB A' B' σ' hσ' hD1 hD2 hlt
    let i : Fin 8 := ⟨c % 8, Nat.mod_lt _ (by norm_num)⟩
    have hKi : K i 0 = (kxn (c % 8) : ℝ) / 100 ∧ K i 1 = (kyn (c % 8) : ℝ) / 100 := by
      simp [K, i]
    have h := hz (2 * (LA : ℝ) + LB) (7 / 4 * (LB : ℝ)) i
    rw [alg_fin σ σ' (2 * (LA : ℝ) + LB) (7 / 4 * (LB : ℝ)) (p 0 0) (p 0 1) (p 1 0) (p 1 1)
      (K 0 0) (K 0 1) (K 1 0) (K 1 1) A' B' (K i 0) (K i 1) u v hK0.1 hK0.2 hne hσ2 hu hv huv hσ'
      hD1 hD2, hKi.1, hKi.2] at h
    apply hpS i
    refine ⟨LA, LB, ?_⟩
    have e0 : (L LA LB) 0 = 2 * (LA : ℝ) + LB := by simp [L]
    have e1 : (L LA LB) 1 = 7 / 4 * (LB : ℝ) := by simp [L]
    have hdl : dist (p i) (L LA LB) ^ 2 < 1 / 4 := by
      rw [dist_sq, e0, e1]
      have q0 : (p i 0 - (2 * (LA : ℝ) + LB)) ^ 2 = (2 * (LA : ℝ) + LB - p i 0) ^ 2 := by ring
      have q1 : (p i 1 - 7 / 4 * (LB : ℝ)) ^ 2 = (7 / 4 * (LB : ℝ) - p i 1) ^ 2 := by ring
      rw [q0, q1, ← h]
      exact hlt
    have h4 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h4]; exact hdl)
  have hσc : σ = 1 ∨ σ = -1 := by
    have : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ2
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  obtain ⟨sg, hsg, hsgσ⟩ : ∃ sg : ℤ, (sg = 1 ∨ sg = -1) ∧ (sg : ℝ) = σ := by
    rcases hσc with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
  have hb1 : ((⌊4 * p 0 1 / 7⌋ : ℤ) : ℝ) ≤ 4 * p 0 1 / 7 := Int.floor_le _
  have hb2 : 4 * p 0 1 / 7 < ((⌊4 * p 0 1 / 7⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have ha1 : ((⌊(p 0 0 - 4 * p 0 1 / 7) / 2⌋ : ℤ) : ℝ) ≤ (p 0 0 - 4 * p 0 1 / 7) / 2 :=
    Int.floor_le _
  have ha2 : (p 0 0 - 4 * p 0 1 / 7) / 2 < ((⌊(p 0 0 - 4 * p 0 1 / 7) / 2⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  generalize ⌊4 * p 0 1 / 7⌋ = b0 at hb1 hb2
  generalize ⌊(p 0 0 - 4 * p 0 1 / 7) / 2⌋ = a0 at ha1 ha2
  have hX : p 0 0 = 2 * (a0 : ℝ) + b0 + 2 * ((p 0 0 - 4 * p 0 1 / 7) / 2 - a0)
      + (4 * p 0 1 / 7 - b0) := by ring
  have hY : p 0 1 = 7 / 4 * ((b0 : ℝ) + (4 * p 0 1 / 7 - b0)) := by ring
  generalize hα : (p 0 0 - 4 * p 0 1 / 7) / 2 - a0 = α at hX
  generalize hβ : 4 * p 0 1 / 7 - (b0 : ℝ) = β at hX hY
  have hα0 : 0 ≤ α := by rw [← hα]; linarith
  have hα1 : α < 1 := by rw [← hα]; linarith
  have hβ0 : 0 ≤ β := by rw [← hβ]; linarith
  have hβ1 : β < 1 := by rw [← hβ]; linarith
  rcases le_total (α + β) 1 with hup | hdn
  · obtain ⟨c, hc⟩ := geo sg hsg u v α β huv hα0 hβ0 hup
    refine key c (a0 + amn (c / 8)) (b0 + bmn (c / 8)) (amn (c / 8) - α) (bmn (c / 8) - β) sg
      (by rcases hsg with h | h <;> rw [h] <;> norm_num) ?_ ?_ hc
    · rw [hX]; push_cast; ring
    · rw [hY, ← hsgσ]
      have : ((sg : ℝ)) * sg = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
      push_cast
      linear_combination (-(7 / 4) * ((bmn (c / 8) : ℝ) - β)) * this
  · obtain ⟨c, hc⟩ := geo (-sg) (by rcases hsg with h | h <;> rw [h] <;> norm_num) u v (α + β - 1)
      (1 - β) huv (by linarith) (by linarith) (by linarith)
    refine key c (a0 + amn (c / 8) + bmn (c / 8)) (b0 + 1 - bmn (c / 8)) (amn (c / 8) - (α + β - 1))
      (bmn (c / 8) - (1 - β)) ((-sg : ℤ) : ℝ)
      (by rcases hsg with h | h <;> rw [h] <;> norm_num) ?_ ?_ hc
    · rw [hX]; push_cast; ring
    · rw [hY, ← hsgσ]
      have : ((sg : ℝ)) * sg = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
      push_cast
      linear_combination (7 / 4 * ((bmn (c / 8) : ℝ) - (1 - β))) * this

end OMA214C

theorem OMA.solution : type_of% @Erdos214.erdos_214.variants.csizmadia_toth := by
  intro hR
  obtain ⟨p, hpS, hc⟩ := hR OMA214C.S OMA214C.S_avoid OMA214C.K OMA214C.K_inj
  exact OMA214C.main p hpS hc
