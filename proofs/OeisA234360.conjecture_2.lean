import FormalConjectures.OEIS.«234360»
import Mathlib.Tactic.NormNum.PowMod

/-! Certificates for the counterexample 1408 from the OEIS Open project.
Each possible square root is ruled out by a divisor or a base-two Fermat test.
Credit: @Deldor14. -/
namespace OMA.Composite
private def phi (n : ℕ) : ℕ :=
  (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p-1)
private lemma phi_eq (n : ℕ) : phi n = n.totient := (Nat.totient_eq_div_primeFactors_mul n).symm
private def cand (k : ℕ) : ℕ := (k+1)^(phi (1408-k)/2) - k

private lemma fermat {p : ℕ} (h : (2 : ZMod p)^p ≠ 2) : ¬ p.Prime := by
  intro hp
  have : Fact p.Prime := ⟨hp⟩
  exact h (ZMod.pow_card _)


private abbrev Row := {k : ℕ // ¬(cand k).Prime}
private def row (k p : ℕ) (he : cand k = p := by decide +kernel)
    (hw : (2 : ZMod p)^p ≠ 2 := by
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub]
      reduce_mod_char
      all_goals decide +kernel) : Row :=
  ⟨k, by rw [he]; exact fermat hw⟩

private def fermatBlock0 : List Row := [
  row 11 ((12^157)^4*12^2-11),
  row 17 ((18^159)^4*18^0-17),
  row 30 ((31^78)^4*31^0-30),
  row 41 ((42^170)^4*42^3-41),
  row 65 ((66^156)^4*66^0-65)]

private def fermatBlock1 : List Row := [
  row 75 ((76^157)^4*76^2-75),
  row 77 ((78^151)^4*78^1-77),
  row 84 ((85^82)^4*85^2-84),
  row 95 ((96^150)^4*96^0-95),
  row 125 ((126^160)^4*126^1-125)]

private def fermatBlock2 : List Row := [
  row 138 ((139^63)^4*139^0-138),
  row 146 ((147^78)^4*147^3-146),
  row 153 ((154^125)^4*154^0-153),
  row 164 ((165^77)^4*165^2-164),
  row 168 ((169^60)^4*169^0-168)]

private def fermatBlock3 : List Row := [
  row 170 ((171^77)^4*171^1-170),
  row 192 ((193^72)^4*193^0-192),
  row 200 ((201^75)^4*201^0-200),
  row 203 ((204^120)^4*204^0-203),
  row 210 ((211^74)^4*211^3-210)]

private def fermatBlock4 : List Row := [
  row 221 ((222^148)^4*222^1-221),
  row 228 ((229^58)^4*229^0-228),
  row 230 ((231^67)^4*231^2-230),
  row 233 ((234^115)^4*234^0-233),
  row 234 ((235^73)^4*235^1-234)]

private def fermatBlock5 : List Row := [
  row 254 ((255^72)^4*255^0-254),
  row 255 ((256^144)^4*256^0-255),
  row 264 ((265^60)^4*265^0-264),
  row 266 ((267^71)^4*267^1-266),
  row 275 ((276^127)^4*276^2-275)]

private def fermatBlock6 : List Row := [
  row 282 ((283^70)^4*283^1-282),
  row 287 ((288^130)^4*288^2-287),
  row 305 ((306^137)^4*306^3-305),
  row 317 ((318^136)^4*318^1-317),
  row 329 ((330^123)^4*330^0-329)]

private def fermatBlock7 : List Row := [
  row 335 ((336^126)^4*336^0-335),
  row 345 ((346^132)^4*346^3-345),
  row 354 ((355^60)^4*355^0-354),
  row 357 ((358^131)^4*358^1-357),
  row 369 ((370^129)^4*370^3-369)]

private def fermatBlock8 : List Row := [
  row 383 ((384^100)^4*384^0-383),
  row 398 ((399^50)^4*399^0-398),
  row 438 ((439^48)^4*439^0-438),
  row 444 ((445^60)^4*445^0-444),
  row 458 ((459^45)^4*459^0-458)]

private def fermatBlock9 : List Row := [
  row 459 ((460^108)^4*460^0-459),
  row 462 ((463^52)^4*463^2-462),
  row 464 ((465^58)^4*465^0-464),
  row 474 ((475^58)^4*475^1-474),
  row 494 ((495^57)^4*495^0-494)]

private def fermatBlock10 : List Row := [
  row 524 ((525^48)^4*525^0-524),
  row 530 ((531^54)^4*531^3-530),
  row 534 ((535^49)^4*535^2-534),
  row 539 ((540^97)^4*540^2-539),
  row 548 ((549^42)^4*549^0-548)]

private def fermatBlock11 : List Row := [
  row 566 ((567^52)^4*567^2-566),
  row 567 ((568^101)^4*568^2-567),
  row 569 ((570^104)^4*570^3-569),
  row 584 ((585^51)^4*585^0-584),
  row 590 ((591^51)^4*591^0-590)]

private def fermatBlock12 : List Row := [
  row 614 ((615^49)^4*615^2-614),
  row 621 ((622^98)^4*622^1-621),
  row 623 ((624^78)^4*624^0-623),
  row 632 ((633^48)^4*633^0-632),
  row 644 ((645^47)^4*645^2-644)]

private def fermatBlock13 : List Row := [
  row 650 ((651^47)^4*651^1-650),
  row 665 ((666^92)^4*666^3-665),
  row 668 ((669^36)^4*669^0-668),
  row 678 ((679^36)^4*679^0-678),
  row 686 ((687^42)^4*687^3-686)]

private def fermatBlock14 : List Row := [
  row 693 ((694^60)^4*694^0-693),
  row 695 ((696^82)^4*696^2-695),
  row 704 ((705^40)^4*705^0-704),
  row 714 ((715^43)^4*715^1-714),
  row 717 ((718^86)^4*718^1-717)]

private def fermatBlock15 : List Row := [
  row 719 ((720^78)^4*720^0-719),
  row 734 ((735^42)^4*735^0-734),
  row 735 ((736^84)^4*736^0-735),
  row 737 ((738^75)^4*738^0-737),
  row 752 ((753^40)^4*753^0-752)]

private def fermatBlock16 : List Row := [
  row 756 ((757^40)^4*757^2-756),
  row 765 ((766^80)^4*766^1-765),
  row 773 ((774^63)^4*774^0-773),
  row 779 ((780^72)^4*780^0-779),
  row 780 ((781^39)^4*781^0-780)]

private def fermatBlock17 : List Row := [
  row 782 ((783^39)^4*783^0-782),
  row 786 ((787^38)^4*787^3-786),
  row 788 ((789^30)^4*789^0-788),
  row 789 ((790^77)^4*790^1-789),
  row 809 ((810^74)^4*810^3-809)]

private def fermatBlock18 : List Row := [
  row 810 ((811^33)^4*811^0-810),
  row 819 ((820^67)^4*820^2-819),
  row 825 ((826^65)^4*826^0-825),
  row 849 ((850^63)^4*850^0-849),
  row 852 ((853^34)^4*853^2-852)]

private def fermatBlock19 : List Row := [
  row 854 ((855^34)^4*855^2-854),
  row 866 ((867^33)^4*867^3-866),
  row 867 ((868^67)^4*868^2-867),
  row 884 ((885^32)^4*885^2-884),
  row 885 ((886^65)^4*886^1-885)]

private def fermatBlock20 : List Row := [
  row 888 ((889^24)^4*889^0-888),
  row 893 ((894^51)^4*894^0-893),
  row 894 ((895^32)^4*895^0-894),
  row 899 ((900^63)^4*900^2-899),
  row 906 ((907^31)^4*907^1-906)]

private def fermatBlock21 : List Row := [
  row 912 ((913^30)^4*913^0-912),
  row 914 ((915^27)^4*915^0-914),
  row 915 ((916^56)^4*916^0-915),
  row 944 ((945^28)^4*945^0-944),
  row 965 ((966^55)^4*966^1-965)]

private def fermatBlock22 : List Row := [
  row 971 ((972^49)^4*972^2-971),
  row 978 ((979^21)^4*979^0-978),
  row 980 ((981^26)^4*981^2-980),
  row 986 ((987^26)^4*987^1-986),
  row 1007 ((1008^50)^4*1008^0-1007)]

private def fermatBlock23 : List Row := [
  row 1013 ((1014^39)^4*1014^0-1013),
  row 1026 ((1027^23)^4*1027^3-1026),
  row 1040 ((1041^22)^4*1041^0-1040),
  row 1041 ((1042^45)^4*1042^3-1041),
  row 1083 ((1084^30)^4*1084^0-1083)]

private def fermatBlock24 : List Row := [
  row 1092 ((1093^19)^4*1093^2-1092),
  row 1109 ((1110^33)^4*1110^0-1109),
  row 1118 ((1119^14)^4*1119^0-1118),
  row 1125 ((1126^35)^4*1126^1-1125),
  row 1133 ((1134^25)^4*1134^0-1133)]

private def fermatBlock25 : List Row := [
  row 1152 ((1153^16)^4*1153^0-1152),
  row 1157 ((1158^31)^4*1158^1-1157),
  row 1165 ((1166^20)^4*1166^1-1165),
  row 1179 ((1180^28)^4*1180^2-1179),
  row 1185 ((1186^27)^4*1186^3-1185)]

private def fermatBlock26 : List Row := [
  row 1194 ((1195^13)^4*1195^1-1194),
  row 1197 ((1198^26)^4*1198^1-1197),
  row 1218 ((1219^9)^4*1219^0-1218),
  row 1227 ((1228^22)^4*1228^2-1227),
  row 1251 ((1252^19)^4*1252^2-1251)]

private def fermatBlock27 : List Row := [
  row 1253 ((1254^15)^4*1254^0-1253),
  row 1266 ((1267^8)^4*1267^3-1266),
  row 1274 ((1275^8)^4*1275^1-1274),
  row 1277 ((1278^16)^4*1278^1-1277),
  row 1278 ((1279^6)^4*1279^0-1278)]

private def fermatBlock28 : List Row := [
  row 1284 ((1285^7)^4*1285^2-1284),
  row 1286 ((1287^7)^4*1287^2-1286),
  row 1295 ((1296^14)^4*1296^0-1295),
  row 1299 ((1300^13)^4*1300^2-1299),
  row 1316 ((1317^5)^4*1317^2-1316)]

private def fermatBlock29 : List Row := [
  row 1322 ((1323^5)^4*1323^1-1322),
  row 1334 ((1335^4)^4*1335^2-1334),
  row 1335 ((1336^9)^4*1336^0-1335),
  row 1341 ((1342^8)^4*1342^1-1341),
  row 1364 ((1365^2)^4*1365^2-1364)]

private def fermatBlock30 : List Row := [
  row 1365 ((1366^5)^4*1366^1-1365),
  row 1371 ((1372^4)^4*1372^2-1371),
  row 1386 ((1387^1)^4*1387^1-1386)]

private def hard : List Row :=
  fermatBlock0 ++
  fermatBlock1 ++
  fermatBlock2 ++
  fermatBlock3 ++
  fermatBlock4 ++
  fermatBlock5 ++
  fermatBlock6 ++
  fermatBlock7 ++
  fermatBlock8 ++
  fermatBlock9 ++
  fermatBlock10 ++
  fermatBlock11 ++
  fermatBlock12 ++
  fermatBlock13 ++
  fermatBlock14 ++
  fermatBlock15 ++
  fermatBlock16 ++
  fermatBlock17 ++
  fermatBlock18 ++
  fermatBlock19 ++
  fermatBlock20 ++
  fermatBlock21 ++
  fermatBlock22 ++
  fermatBlock23 ++
  fermatBlock24 ++
  fermatBlock25 ++
  fermatBlock26 ++
  fermatBlock27 ++
  fermatBlock28 ++
  fermatBlock29 ++
  fermatBlock30

private def divisors : Array ℕ := #[
  0, 3, 31, 13, 3, 8819, 43, 3, 7, 5867, 3, 0, 47, 3, 47, 7,
  3, 0, 191, 3, 13679, 5, 3, 29, 601, 3, 23, 347, 3, 7, 0, 3,
  881, 97, 3, 13, 7, 3, 1483, 19, 3, 0, 17, 3, 269, 19, 3, 37,
  107, 3, 7, 7, 3, 13, 2971, 3, 5, 7, 3, 67, 11, 3, 199, 37,
  3, 0, 5, 3, 67, 743, 3, 7, 7, 3, 7, 0, 3, 0, 7, 3,
  101, 11, 3, 41, 0, 3, 8719, 101, 3, 19, 313, 3, 7, 7, 3, 0,
  5, 3, 17, 7, 3, 1129, 7, 3, 9161, 3307, 3, 7, 23, 3, 487, 5,
  3, 7, 11, 3, 5, 23, 3, 19, 7, 3, 13, 7, 3, 0, 5, 3,
  89, 41, 3, 17293, 4987, 3, 7, 11, 3, 17, 0, 3, 17, 5, 3, 547,
  13, 3, 0, 73, 3, 83, 43, 3, 29, 0, 3, 7, 5, 3, 67, 79,
  3, 5, 7, 3, 0, 7, 3, 397, 0, 3, 0, 31, 3, 23, 31, 3,
  5, 5, 3, 7, 2381, 3, 101, 7, 3, 19, 5, 3, 11, 41, 3, 5,
  0, 3, 4363, 587, 3, 7, 449, 3, 0, 5, 3, 0, 7, 3, 5, 1063,
  3, 13, 0, 3, 11, 19, 3, 1531, 5, 3, 7, 7, 3, 0, 17, 3,
  11, 7, 3, 73, 0, 3, 0, 73, 3, 0, 0, 3, 5, 41, 3, 7,
  103, 3, 7, 13, 3, 47, 7, 3, 37, 31, 3, 5, 103, 3, 0, 0,
  3, 5, 4339, 3, 7, 5, 3, 167, 0, 3, 0, 7, 3, 67, 7, 3,
  2423, 19, 3, 0, 137, 3, 11, 5839, 3, 7, 0, 3, 23, 149, 3, 0,
  7, 3, 67, 17, 3, 17, 23, 3, 5, 67, 3, 271, 13, 3, 7, 2753,
  3, 0, 5, 3, 13, 7, 3, 5, 7, 3, 59, 59, 3, 0, 31, 3,
  19, 14281, 3, 7, 19, 3, 4027, 283, 3, 0, 7, 3, 283, 229, 3, 0,
  5, 3, 7, 251, 3, 5, 11, 3, 7, 0, 3, 7, 83, 3, 31, 7,
  3, 11, 0, 3, 47, 0, 3, 7, 13, 3, 1613, 181, 3, 7, 5, 3,
  79, 0, 3, 5, 7, 3, 139, 293, 3, 5, 13, 3, 23, 5, 3, 0,
  29, 3, 5, 53, 3, 809, 31, 3, 41, 7, 3, 331, 5, 3, 0, 11,
  3, 5, 5, 3, 23, 1949, 3, 7, 7, 3, 11, 11, 3, 29, 7, 3,
  5, 5, 3, 223, 41, 3, 7, 19, 3, 137, 23, 3, 7, 7, 3, 5,
  109, 3, 431, 7, 3, 4363, 0, 3, 157, 269, 3, 11, 0, 3, 5, 13,
  3, 7, 47, 3, 13, 149, 3, 23, 5, 3, 0, 0, 3, 19, 0, 3,
  0, 337, 3, 19, 1901, 3, 7, 5, 3, 7, 0, 3, 5, 7, 3, 43,
  7, 3, 5, 241, 3, 11, 19, 3, 127, 647, 3, 7, 7307, 3, 0, 23,
  3, 5, 7, 3, 11, 17, 3, 2083, 199, 3, 5, 37, 3, 67, 13, 3,
  7, 7, 3, 23, 5507, 3, 19, 7, 3, 11, 197, 3, 0, 13, 3, 7,
  17, 3, 0, 577, 3, 7, 0, 3, 5, 67, 3, 0, 7, 3, 149, 7,
  3, 107, 19, 3, 0, 503, 3, 5, 31, 3, 7, 11, 3, 881, 113, 3,
  19, 7, 3, 359, 4231, 3, 0, 0, 3, 0, 31, 3, 2473, 67, 3, 7,
  5, 3, 7, 157, 3, 983, 7, 3, 0, 23, 3, 23, 37, 3, 0, 509,
  3, 37, 233, 3, 5, 11731, 3, 7, 19, 3, 23, 7, 3, 151, 5, 3,
  37, 11, 3, 7, 5527, 3, 0, 197, 3, 7, 269, 3, 139, 0, 3, 0,
  7, 3, 5, 7, 3, 1213, 11, 3, 0, 17, 3, 103, 5, 3, 7, 127,
  3, 5, 5, 3, 0, 7, 3, 211, 1249, 3, 0, 173, 3, 59, 641, 3,
  5, 5, 3, 7, 967, 3, 29, 37, 3, 0, 5, 3, 0, 2633, 3, 67,
  13, 3, 61, 83, 3, 13, 0, 3739, 7, 1657, 3, 11, 353, 3, 0, 7,
  3, 11, 127, 3, 31, 0, 3, 0, 5, 3, 13, 71, 3, 5, 7, 3,
  0, 1699, 3, 19, 7, 3, 521, 5, 3, 367, 0, 3, 5, 0, 3, 0,
  109, 3, 5, 7, 3, 1321, 97, 3, 89, 7, 3, 13, 67, 3, 0, 0,
  3, 0, 67, 3, 17, 5, 3, 7, 7, 3, 13, 43, 3, 41, 7, 3,
  0, 7, 3, 379, 0, 3, 53, 53, 3, 1187, 11, 3, 7, 0, 3, 7,
  23, 3, 13, 5, 3, 0, 7, 3, 5, 5, 3, 0, 0, 3, 0, 3089,
  3, 7, 0, 3, 0, 0, 3, 5, 7, 3, 173, 401, 3, 11, 97, 3,
  17, 29, 3, 17, 11, 3, 7, 13, 3, 0, 0, 3, 17, 7, 3, 13,
  5, 3, 18869, 0, 3, 59, 13, 3, 14831, 0, 3, 7, 317, 3, 11, 5,
  3, 19, 7, 3, 5, 13, 3, 11, 37, 3, 23, 19, 3, 769, 5, 3,
  7, 0, 3, 7, 0, 3, 0, 7, 3, 199, 283, 3, 47, 389, 3, 11,
  3767, 3, 0, 0, 3, 7, 7, 3, 13, 31, 3, 313, 5, 3, 7933, 10711,
  3, 5, 5, 3, 0, 0, 3, 13, 0, 3, 7, 7, 3, 0, 0, 3,
  5, 7, 3, 0, 1163, 3, 199, 11, 3, 3793, 0, 3, 5477, 11, 3, 7,
  0, 3, 0, 0, 3, 1667, 7, 3, 107, 6047, 10039, 569, 31, 3, 5, 3413,
  3, 887, 59, 3, 7, 1579, 3, 293, 5, 3, 19, 7, 3, 271, 7, 3,
  0, 29, 3, 7, 2437, 3, 1753, 5, 3, 7, 10847, 3, 5, 19, 3, 37,
  7, 3, 5, 7, 3, 0, 5, 3, 7, 89, 3, 0, 11, 3, 7, 23,
  3, 5, 0, 3, 0, 5, 3, 179, 7, 3, 0, 191, 3, 271, 47, 3,
  2917, 11, 3, 7, 107, 3, 7, 1801, 3, 5, 7, 3, 3359, 10501, 3, 0,
  727, 3, 349, 47, 3, 0, 19, 3, 5, 7, 3, 7, 67, 3, 439, 7,
  3, 6361, 0, 3, 13, 59, 3, 5, 571, 3, 67, 5059, 3, 7, 17, 3,
  0, 0, 3, 41, 7, 3, 11, 5, 3, 19, 163, 3, 37, 547, 3, 17,
  5, 3, 7, 11, 3, 239, 13, 3, 101, 7, 3, 23, 157, 3, 31, 5,
  3, 67, 19009, 3, 13, 11681, 3, 7, 7, 3, 101, 0, 3, 359, 7, 3,
  67, 7, 3, 3559, 0, 3, 4127, 61, 3, 5, 1223, 3, 7, 61, 3, 3373,
  53, 3, 71, 7, 3, 0, 7, 3, 107, 19, 3, 7, 5, 3, 0, 6131,
  3, 5, 223, 3, 631, 0, 3, 13, 7, 3, 17, 2693, 3, 0, 13, 3,
  5, 5, 3, 43, 67, 3, 7, 7, 3, 19, 61, 3, 11, 7, 3, 5,
  0, 3, 67, 1069, 3, 0, 733, 3, 17, 5, 3, 7, 937, 0, 941, 11,
  3, 11, 7, 3, 257, 7, 3, 151, 5, 3, 7, 0, 3, 11, 11, 3,
  7, 0, 3, 281, 149, 3, 12641, 7, 3, 79, 0, 3, 5, 0, 3, 14771,
  23, 3, 5, 31, 3, 7, 7, 3, 17, 97, 3, 541, 7, 3, 11, 11,
  3, 5, 0, 3, 2711, 5, 3, 13, 11, 3, 5, 0, 3, 1097, 953, 3,
  19, 7, 3, 23, 1229, 3, 13, 47, 3, 29, 197, 3, 11, 23, 17, 7,
  7, 3, 11, 0, 3, 0, 7, 3, 5, 5, 3, 937, 23, 3, 13, 389,
  3, 53, 0, 3, 7, 53, 3, 5, 569, 3, 0, 7, 3, 0, 0, 3,
  19, 863, 3, 7, 0, 3, 0, 5, 3, 7, 11, 3, 101, 139, 3, 0,
  5, 3, 73, 0, 3, 241, 67, 3, 31, 107, 3, 31, 877, 3, 7, 5,
  3, 131, 37, 3, 0, 7, 3, 47, 7, 3, 0, 61, 3, 557, 5, 5,
  37, 29, 3, 7, 1033, 3, 0, 0, 3, 5, 7, 3, 23, 0, 3, 89,
  17, 3, 97, 23, 3, 11, 313, 3, 7, 7, 67, 7, 5, 3, 19, 7,
  3, 8243, 5, 3, 0, 0, 3, 7, 11, 3, 13, 0, 3, 7, 7, 3,
  5, 5, 3, 17, 7, 127, 2351, 3413, 3, 1597, 0, 3, 223, 11, 11, 5,
  83, 3, 7, 2417, 3, 53, 19, 19, 13, 7, 0, 373, 0, 0, 0, 0]

private def checked (k : ℕ) : Bool :=
  let d := divisors[k]?.getD 0
  if d = 0 then decide (k ∈ hard.map Subtype.val) || decide (cand k ≤ 1)
  else decide (1 < d ∧ d < cand k ∧ cand k % d = 0)

private lemma checked_sound {k : ℕ} (h : checked k = true) : ¬(cand k).Prime := by
  dsimp only [checked] at h
  split at h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨z, _, hz⟩ := List.mem_map.mp h
      exact hz ▸ z.property
    · exact fun hp => (Nat.not_lt_of_ge h) hp.one_lt
  · simp only [decide_eq_true_eq] at h
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h.2.2) h.1 h.2.1

private theorem block0 : ∀ j : Fin 32, checked (0+j.val+1) = true := by decide +kernel

private theorem block1 : ∀ j : Fin 32, checked (32+j.val+1) = true := by decide +kernel

private theorem block2 : ∀ j : Fin 32, checked (64+j.val+1) = true := by decide +kernel

private theorem block3 : ∀ j : Fin 32, checked (96+j.val+1) = true := by decide +kernel

private theorem block4 : ∀ j : Fin 32, checked (128+j.val+1) = true := by decide +kernel

private theorem block5 : ∀ j : Fin 32, checked (160+j.val+1) = true := by decide +kernel

private theorem block6 : ∀ j : Fin 32, checked (192+j.val+1) = true := by decide +kernel

private theorem block7 : ∀ j : Fin 32, checked (224+j.val+1) = true := by decide +kernel

private theorem block8 : ∀ j : Fin 32, checked (256+j.val+1) = true := by decide +kernel

private theorem block9 : ∀ j : Fin 32, checked (288+j.val+1) = true := by decide +kernel

private theorem block10 : ∀ j : Fin 32, checked (320+j.val+1) = true := by decide +kernel

private theorem block11 : ∀ j : Fin 32, checked (352+j.val+1) = true := by decide +kernel

private theorem block12 : ∀ j : Fin 32, checked (384+j.val+1) = true := by decide +kernel

private theorem block13 : ∀ j : Fin 32, checked (416+j.val+1) = true := by decide +kernel

private theorem block14 : ∀ j : Fin 32, checked (448+j.val+1) = true := by decide +kernel

private theorem block15 : ∀ j : Fin 32, checked (480+j.val+1) = true := by decide +kernel

private theorem block16 : ∀ j : Fin 32, checked (512+j.val+1) = true := by decide +kernel

private theorem block17 : ∀ j : Fin 32, checked (544+j.val+1) = true := by decide +kernel

private theorem block18 : ∀ j : Fin 32, checked (576+j.val+1) = true := by decide +kernel

private theorem block19 : ∀ j : Fin 32, checked (608+j.val+1) = true := by decide +kernel

private theorem block20 : ∀ j : Fin 32, checked (640+j.val+1) = true := by decide +kernel

private theorem block21 : ∀ j : Fin 32, checked (672+j.val+1) = true := by decide +kernel

private theorem block22 : ∀ j : Fin 32, checked (704+j.val+1) = true := by decide +kernel

private theorem block23 : ∀ j : Fin 32, checked (736+j.val+1) = true := by decide +kernel

private theorem block24 : ∀ j : Fin 32, checked (768+j.val+1) = true := by decide +kernel

private theorem block25 : ∀ j : Fin 32, checked (800+j.val+1) = true := by decide +kernel

private theorem block26 : ∀ j : Fin 32, checked (832+j.val+1) = true := by decide +kernel

private theorem block27 : ∀ j : Fin 32, checked (864+j.val+1) = true := by decide +kernel

private theorem block28 : ∀ j : Fin 32, checked (896+j.val+1) = true := by decide +kernel

private theorem block29 : ∀ j : Fin 32, checked (928+j.val+1) = true := by decide +kernel

private theorem block30 : ∀ j : Fin 32, checked (960+j.val+1) = true := by decide +kernel

private theorem block31 : ∀ j : Fin 32, checked (992+j.val+1) = true := by decide +kernel

private theorem block32 : ∀ j : Fin 32, checked (1024+j.val+1) = true := by decide +kernel

private theorem block33 : ∀ j : Fin 32, checked (1056+j.val+1) = true := by decide +kernel

private theorem block34 : ∀ j : Fin 32, checked (1088+j.val+1) = true := by decide +kernel

private theorem block35 : ∀ j : Fin 32, checked (1120+j.val+1) = true := by decide +kernel

private theorem block36 : ∀ j : Fin 32, checked (1152+j.val+1) = true := by decide +kernel

private theorem block37 : ∀ j : Fin 32, checked (1184+j.val+1) = true := by decide +kernel

private theorem block38 : ∀ j : Fin 32, checked (1216+j.val+1) = true := by decide +kernel

private theorem block39 : ∀ j : Fin 32, checked (1248+j.val+1) = true := by decide +kernel

private theorem block40 : ∀ j : Fin 32, checked (1280+j.val+1) = true := by decide +kernel

private theorem block41 : ∀ j : Fin 32, checked (1312+j.val+1) = true := by decide +kernel

private theorem block42 : ∀ j : Fin 32, checked (1344+j.val+1) = true := by decide +kernel

private theorem block43 : ∀ j : Fin 32, checked (1376+j.val+1) = true := by decide +kernel

private lemma all_checked (k : ℕ) (h0 : 0 < k) (hk : k < 1406) : checked k = true := by
  let j : Fin 32 := ⟨(k-1)%32, Nat.mod_lt _ (by decide)⟩
  let b := (k-1)/32
  have hsplit : k = 32*b + j.val + 1 := by dsimp [b,j]; omega
  have hb : b ≤ 43 := by dsimp [b]; omega
  rw [hsplit]
  interval_cases b

  · exact block0 j

  · exact block1 j

  · exact block2 j

  · exact block3 j

  · exact block4 j

  · exact block5 j

  · exact block6 j

  · exact block7 j

  · exact block8 j

  · exact block9 j

  · exact block10 j

  · exact block11 j

  · exact block12 j

  · exact block13 j

  · exact block14 j

  · exact block15 j

  · exact block16 j

  · exact block17 j

  · exact block18 j

  · exact block19 j

  · exact block20 j

  · exact block21 j

  · exact block22 j

  · exact block23 j

  · exact block24 j

  · exact block25 j

  · exact block26 j

  · exact block27 j

  · exact block28 j

  · exact block29 j

  · exact block30 j

  · exact block31 j

  · exact block32 j

  · exact block33 j

  · exact block34 j

  · exact block35 j

  · exact block36 j

  · exact block37 j

  · exact block38 j

  · exact block39 j

  · exact block40 j

  · exact block41 j

  · exact block42 j

  · exact block43 j

end OMA.Composite

open OMA.Composite in
theorem OMA.solution : type_of% @OeisA234360.conjecture_2 := by
  intro h
  obtain ⟨k, hk0, hk, p, hp, heq⟩ := h 1408 (by decide)
  by_cases hlarge : 1406 ≤ k
  · have hp' := hp.two_le
    have ht : (1408-k).totient = 1 := Nat.totient_eq_one_iff.mpr (by omega)
    rw [ht,pow_one] at heq
    nlinarith [Nat.zero_le p]
  · have hphi := Nat.totient_even (show 2 < 1408-k by omega)
    obtain ⟨t,ht⟩ := hphi
    have hx : p+k = (k+1)^t := by
      rw [ht, pow_add, ← sq] at heq
      exact Nat.pow_left_injective (by decide : 2 ≠ 0) heq
    have hpval : cand k = p := by
      unfold cand
      rw [phi_eq,ht,show (t+t)/2=t by omega,← hx]
      omega
    exact checked_sound (all_checked k hk0 (by omega)) (hpval.symm ▸ hp)
