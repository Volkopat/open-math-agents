import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
import Mathlib

/-!
Analytic counting certificate for Erdos Problem 848 (N >= 160000000).
Adapted under Apache-2.0 from MacchaCat/erdos848
(commit 99b8d9bf40fdd090a2a117328c5707ca21ec748e),
upgraded with discrete Chebyshev summation by parts, a Selberg upper sieve
for primes 1 mod 4, witness parity and mod-25 divisor bounds, and mod-168
admissible Pell filtering so the entire table verifies below PM = 15000
via decide +kernel.
-/


namespace ErdosComp

def minFacAux (n : Nat) : Nat → Nat → Nat
  | _, 0 => n
  | k, f + 1 => if n < k * k then n else if n % k == 0 then k else minFacAux n (k + 2) f

def isPrimeB (n : Nat) : Bool :=
  if n < 2 then false else if n % 2 == 0 then n == 2 else minFacAux n 3 n == n

def isU1B (n : Nat) : Bool := isPrimeB n && n % 4 == 1 && 13 ≤ n

def KS : Nat := 10 ^ 30

def ceilK (p : Nat) : Nat := (KS + p * p - 1) / (p * p)

structure PSt where
  cp : Nat
  cu : Nat
  fp : Nat
  fu : Nat

def stepSt (n : Nat) (s : PSt) : PSt :=
  if isPrimeB n then
    if isU1B n then ⟨s.cp + 1, s.cu + 1, s.fp + ceilK n, s.fu + ceilK n⟩
    else ⟨s.cp + 1, s.cu, s.fp + ceilK n, s.fu⟩
  else s

def stAt : Nat → PSt
  | 0 => ⟨0, 0, 0, 0⟩
  | n + 1 => stepSt (n + 1) (stAt n)

def advance : Nat → Nat → PSt → PSt
  | 0, _, s => s
  | k + 1, n, s => advance k (n + 1) (stepSt (n + 1) s)

def evalPts : List Nat → Nat → PSt → List (Nat × PSt)
  | [], _, _ => []
  | x :: xs, n, s =>
    (n + (x - n), advance (x - n) n s) :: evalPts xs (n + (x - n)) (advance (x - n) n s)

def lookD (tab : List (Nat × PSt)) (x : Nat) : PSt :=
  match tab.find? (fun e => e.1 == x) with
  | some e => e.2
  | none => stAt x

end ErdosComp


namespace ErdosComp

def smallPrimesL : List Nat := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
  101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
  197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
  311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
  431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
  557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
  661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
  809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
  937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
  1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153,
  1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279,
  1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
  1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499,
  1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613,
  1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741,
  1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873,
  1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
  2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113,
  2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251,
  2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371,
  2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477,
  2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647,
  2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
  2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857,
  2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001,
  3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163,
  3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299,
  3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407,
  3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539,
  3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659,
  3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793,
  3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919,
  3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051,
  4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201,
  4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327,
  4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463]

def PSH : Nat :=
  1712206997547039466982080380802562617513640622660404539488732266867734052454912549211247312353510670872239109204835668619255337723406347697120578163621873004188676950202496281339613141723411755313851668223070201874897473765432878798797825303702315538257763183917479990736581855640357675819362115977545579162072041548861479842137949540240824044635600826131346583717289492135556898090908210310321583953545458293278373612303718136593713347898861174863307716186021231461352994801334844086370560863034312639820458008473225357563665749069971895913864646708678567318341055120382276955526692969603832181090329131437160325498703358342206988852834902205279045474841211815470529563730984412451072607041009386477982638899441242962956061280167336843818496872379760619421664276397568912114767324551934275021303521947691264955368056875918133507730726277661585927173243576194286843138980567823668819868297010390876136623551377521671698181784731418189823129810750377779267784511186426882600087182176517902536425298588948911945603727586511616832857611651189077032881319990509541384577233224043022983636859164543006737282909449089509941910034477021756197256306138778461273866586547626245709570305098305551070978626081565380687431353194121035701960864741842894158169783508406061505522573355999150397901038105721713910698581047286961635743226304064636262691668641269263871155270211131767040920771796814076191058091216279859206626354935145988591815472506221493598848403010368977985498273357704411623817469628683823807634962777935055117307137104627917130674478676202697456832490050411386675176334184218792989383445153088634013472791158113214998985325694669016457688316441160127453766404310719601084196494485508025226383190125498850912437235988221377088282846853321002821345148932702434206947782314406573635933913455786117433391418672835490673012301796655154950380144794559608208473257851290654036956224890277331837818736277225670

end ErdosComp


namespace ErdosComp

def fastP (n : Nat) : Bool := cond (Nat.blt n 4473) (isPrimeB n) (Nat.beq (Nat.gcd n PSH) 1)

def zeroSt : PSt := ⟨0, 0, 0, 0⟩

def addSt (a b : PSt) : PSt := ⟨a.cp + b.cp, a.cu + b.cu, a.fp + b.fp, a.fu + b.fu⟩

def contribF (n : Nat) : PSt :=
  cond (fastP n)
    (cond (n % 4 == 1 && decide (13 ≤ n)) ⟨1, 1, ceilK n, ceilK n⟩ ⟨1, 0, ceilK n, 0⟩)
    zeroSt

def segB (f : Nat) : Nat → Nat → PSt :=
  Nat.rec (motive := fun _ => Nat → Nat → PSt) (fun _ _ => zeroSt)
    (fun _ ih lo len => cond (Nat.beq len 0) zeroSt (cond (Nat.beq len 1) (contribF (lo + 1))
      (addSt (ih lo (len / 2)) (ih (lo + len / 2) (len - len / 2))))) f

def eqSt (a b : PSt) : Bool :=
  Nat.beq a.cp b.cp && Nat.beq a.cu b.cu && Nat.beq a.fp b.fp && Nat.beq a.fu b.fu

def chainOK : Nat → PSt → List (Nat × PSt) → Bool
  | _, _, [] => true
  | x, v, (y, w) :: rest =>
    Nat.ble x y && Nat.blt y 20007729 && eqSt w (addSt v (segB 64 x (y - x))) && chainOK y w rest

inductive PTree where
  | leaf : PTree

end ErdosComp


namespace ErdosComp

def PM : Nat := 15000

def logLoF (x : Nat) : Rat :=
  let k := Nat.log2 x
  let r := (64 * (x - 2 ^ k)) / x
  (k : Rat) * (693147 / 1000000) + (r : Rat) / 64

def piStep (hi : Nat) (st : Nat × Rat × Rat) (nd : Nat × Nat) : Nat × Rat × Rat :=
  let x := st.1
  let w := st.2.1
  let B := st.2.2
  let x' := max x ((hi * nd.1) / nd.2)
  let w' := max w (logLoF x')
  (x', w', B + (13863 / 10000 : Rat) * x' * (1 / w - 1 / w'))

def piFracs : List (Nat × Nat) :=
  [(1, 1024), (1, 512), (1, 256), (1, 128), (1, 64), (1, 32), (2, 32), (3, 32), (4, 32),
   (5, 32), (6, 32), (7, 32), (8, 32), (9, 32), (10, 32), (11, 32), (12, 32), (13, 32),
   (14, 32), (15, 32), (16, 32), (17, 32), (18, 32), (19, 32), (20, 32), (21, 32), (22, 32),
   (23, 32), (24, 32), (25, 32), (26, 32), (27, 32), (28, 32), (29, 32), (30, 32), (31, 32),
   (1, 1)]

def piAfterPM (hi : Nat) : Rat :=
  if hi ≤ PM then 0
  else
    let stf := piFracs.foldl (piStep hi) (PM, logLoF PM, 0)
    stf.2.2 + (13863 / 10000 : Rat) * hi / stf.2.1

def s2P (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).fp - (lookD tab lo).fp : Nat) : Rat) / KS
  else if lo ≤ PM then (((lookD tab PM).fp - (lookD tab lo).fp : Nat) : Rat) / KS + 1 / PM
  else 1 / lo

def s2U (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).fu - (lookD tab lo).fu : Nat) : Rat) / KS
  else if lo ≤ PM then (((lookD tab PM).fu - (lookD tab lo).fu : Nat) : Rat) / KS + 1 / PM
  else 1 / lo

def cP (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).cp - (lookD tab lo).cp : Nat) : Rat)
  else if lo ≤ PM then (((lookD tab PM).cp - (lookD tab lo).cp : Nat) : Rat) + piAfterPM hi
  else piAfterPM hi

def cU (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).cu - (lookD tab lo).cu : Nat) : Rat)
  else if lo ≤ PM then
    min ((((lookD tab PM).cu - (lookD tab lo).cu : Nat) : Rat) + piAfterPM hi)
      ((69446 / 1000000 : Rat) * hi + 1860)
  else min (piAfterPM hi) ((69446 / 1000000 : Rat) * hi + 1860)

end ErdosComp


namespace ErdosComp

def prodF (cond : Nat → Bool) (f : Nat → Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => prodF cond f n * (if cond n then f n else 1)

def sumF (cond : Nat → Bool) (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumF cond f n + (if cond n then f n else 0)

def cntF (cond : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cntF cond n + (if cond n then 1 else 0)

def condP (excl : List Nat) (p : Nat) : Bool := isPrimeB p && !(excl.contains p)
def prod1 (excl : List Nat) : Rat := prodF (condP excl) (fun p => 1 - 1 / ((p : Rat) * p)) 32
def k1 (excl : List Nat) : Nat := cntF (condP excl) 32
def prodU : Rat := prodF isU1B (fun p => 1 - 2 / ((p : Rat) * p)) 42
def kU : Nat := cntF isU1B 42
def condE (p q : Nat) : Bool := isU1B q && q != p
def prErase (p : Nat) : Rat := prodF (condE p) (fun q => 1 - 2 / ((q : Rat) * q)) 42
def kErase (p : Nat) : Nat := cntF (condE p) 42
def condOdd (p : Nat) : Bool := isPrimeB p && p != 2 && p != 5
def cNon : Rat := sumF condOdd (fun p => 23 / 25 * (1 / ((p : Rat) * p)) * (1 - prErase p)) 1001
def eNon : Rat := sumF condOdd (fun p => 3 * ((3 : Rat) ^ kErase p - 1)) 1001

def UL : List Nat := [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173,
  181, 193, 197, 229, 233, 241, 257, 269, 277, 281, 293, 313, 317]

def gA (p : Nat) : Rat := 23 / 25 * prErase p / ((p : Rat) * p)
def gE (p : Nat) : Rat := 3 - 3 * ((3 : Rat) ^ kErase p - 1)

def OPc : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

def primeProdC (k : Nat) : Nat := (OPc.take k).prod
def Wc (L : Nat) : Nat := ((List.range 45).filter (fun k => primeProdC (k + 1) ≤ L)).length
def rhoMaxC (N : Nat) : Nat := max (2 ^ Wc N) (max (2 * 2 ^ Wc (N / 4)) (4 * 2 ^ Wc (N / 8)))
def rhoOddC (N : Nat) : Nat := 2 ^ Wc N

def OPNo5c : List Nat := [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

def primeProdNo5C (k : Nat) : Nat := (OPNo5c.take k).prod
def WcNo5 (L : Nat) : Nat := ((List.range 44).filter (fun k => primeProdNo5C (k + 1) ≤ L)).length
def rhoNo5C (N : Nat) : Nat := max (2 ^ WcNo5 N) (max (2 * 2 ^ WcNo5 (N / 4)) (4 * 2 ^ WcNo5 (N / 8)))

def log3Go (n : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if 3 ^ (k + 1) ≤ n then log3Go n f (k + 1) else k

def log3C (n : Nat) : Nat := log3Go n n 0

def pellAdmM (M : Nat) : Nat := min M (36 * (M / 168 + 1))

def pellC (N Y : Nat) : Nat :=
  pellAdmM ((N * N + 1) / ((Y + 1) * (Y + 1))) * (log3C N + 1)

abbrev CE := Rat × Rat

def addCE (a b : CE) : CE := (a.1 + b.1, a.2 + b.2)

def resCE (tab : List (Nat × PSt)) (q T : Nat) (excl : List Nat) (pc : Nat) : CE :=
  ((T : Rat) / q * (1 - prod1 excl + s2P tab 31 pc),
   (T : Rat) * ((2 : Rat) ^ k1 excl - 1 + cP tab 31 pc))

def shCEWith (tab : List (Nat × PSt)) (Nhi pc Y rval : Nat) : CE :=
  (s2P tab pc Y,
   cP tab pc Y + (rval : Rat) * (2 * ((Nhi : Rat) + 1) / Y + ((Nhi : Rat) * Nhi + 1) / ((Y : Rat) * Y)))

def shCE (tab : List (Nat × PSt)) (Nhi pc Y : Nat) : CE :=
  shCEWith tab Nhi pc Y (rhoMaxC Nhi)

def lemBCE (tab : List (Nat × PSt)) (Nhi q T pB YB : Nat) : CE :=
  ((T : Rat) / q * (1 - prodU) + 2 * (T : Rat) / q * s2U tab 41 pB + 2 * s2U tab pB YB,
   (T : Rat) * ((3 : Rat) ^ kU - 1) + 2 * (T : Rat) * cU tab 41 pB + 2 * cU tab pB YB +
     (pellC Nhi YB : Rat))

def gSumC (L : Nat) : Rat := sumF (fun _ => true) (fun j => gA (UL.getD j 0)) L
def gSumE (Nlo L : Nat) : Rat :=
  sumF (fun _ => true) (fun j => max (gE (UL.getD j 0)) (-(gA (UL.getD j 0)) * Nlo)) L

def ulProd : Nat → Nat
  | 0 => 1
  | l + 1 => ulProd l * UL.getD l 0

def lemCCE (tab : List (Nat × PSt)) (Nlo Nhi pB YB pc L : Nat) : CE :=
  (46 / 25 * s2U tab 41 pB + 2 * s2U tab pB YB + (1 - prodU) / 25 + cNon + gSumC L +
     s2P tab 1000 pc,
   46 * cU tab 41 pB + 2 * cU tab pB YB + (pellC Nhi YB : Rat) + ((3 : Rat) ^ kU - 1) + eNon +
     gSumE Nlo L + cP tab 1000 pc)

def Lval (Nhi : Nat) : Nat :=
  ((List.range 29).filter (fun l => ulProd (l + 1) * ulProd (l + 1) ≤ Nhi * Nhi + 1)).length

structure Row6 where
  Nlo : Nat
  Nhi : Nat
  pc : Nat
  Y : Nat
  YB : Nat
  pB : Nat

def okCE (Nlo : Nat) (c : CE) : Bool :=
  decide (c.1 < 1 / 25) && decide (c.1 * Nlo + c.2 < ((Nlo : Rat) - 6) / 25)

def caseII6 (tab : List (Nat × PSt)) (r : Row6) : CE :=
  addCE (addCE (resCE tab 25 2 [2, 5] r.pc) (lemCCE tab r.Nlo r.Nhi r.pB r.YB r.pc (Lval r.Nhi)))
    (shCEWith tab r.Nhi r.pc r.Y (rhoMaxC r.Nhi))

def caseIII16 (tab : List (Nat × PSt)) (r : Row6) : CE :=
  addCE (addCE (addCE (resCE tab 100 6 [2, 5] r.pc) (shCEWith tab r.Nhi r.pc r.Y (rhoOddC r.Nhi)))
    (addCE (resCE tab 100 2 [2, 5] r.pc) (shCEWith tab r.Nhi r.pc r.Y (rhoOddC r.Nhi))))
    (lemBCE tab r.Nhi 50 23 r.pB r.YB)

def caseIII2a6 (tab : List (Nat × PSt)) (r : Row6) : CE :=
  addCE (addCE (2 / 100, 2) (addCE (resCE tab 100 2 [2, 5] r.pc) (shCEWith tab r.Nhi r.pc r.Y (rhoOddC r.Nhi))))
    (lemBCE tab r.Nhi 100 23 r.pB r.YB)

def caseIII2b6 (tab : List (Nat × PSt)) (r : Row6) : CE :=
  addCE (addCE (addCE (1 / 100, 1) (addCE (resCE tab 100 3 [2, 5] r.pc) (shCEWith tab r.Nhi r.pc r.Y (rhoOddC r.Nhi))))
    (addCE (resCE tab 25 1 [2, 5] r.pc) (shCEWith tab r.Nhi r.pc r.Y (rhoNo5C r.Nhi))))
    (lemBCE tab r.Nhi 100 23 r.pB r.YB)

def checkRowH4 (tab : List (Nat × PSt)) (r : Row6) : Bool :=
  decide (1 ≤ r.Y) && decide (7 ≤ r.Nlo) && decide (r.Nlo ≤ r.Nhi) &&
  decide (r.Nhi < primeProdC 45) && decide (r.Nhi < primeProdNo5C 44) &&
  okCE r.Nlo (caseIII2a6 tab r) && okCE r.Nlo (caseIII2b6 tab r)

def checkRowH3 (tab : List (Nat × PSt)) (r : Row6) : Bool :=
  decide (1 ≤ r.Y) && decide (7 ≤ r.Nlo) && decide (r.Nlo ≤ r.Nhi) &&
  decide (r.Nhi < primeProdC 45) &&
  decide (Nat.succ (Lval r.Nhi) ≤ 30) &&
  decide (r.Nhi * r.Nhi + 1 < ulProd (Lval r.Nhi + 1) * ulProd (Lval r.Nhi + 1)) &&
  okCE r.Nlo (caseII6 tab r) && okCE r.Nlo (caseIII16 tab r)

def chain6 : Nat → Nat → List Row6 → Bool
  | a, b, [] => a == b
  | a, b, r :: rs => r.Nlo == a && chain6 r.Nhi b rs

def PM1 : Nat := PM + 1
def shT (tab : List (Nat × PSt)) : CE := (s2P tab 2000 PM1, 0)

def lemBT (tab : List (Nat × PSt)) (q T : Nat) : CE :=
  ((T : Rat) / q * (1 - prodU) + 2 * (T : Rat) / q * s2U tab 41 2000 + 2 * s2U tab 2000 PM1,
   (T : Rat) * ((3 : Rat) ^ kU - 1) + 2 * (T : Rat) * cU tab 41 2000)

def gAllC : Rat := sumF isU1B gA 1001
def gAllE (Nt : Nat) : Rat := sumF isU1B (fun p => max (gE p) (-(gA p) * Nt)) 1001

def lemCT (tab : List (Nat × PSt)) (Nt : Nat) : CE :=
  (46 / 25 * s2U tab 41 2000 + 2 * s2U tab 2000 PM1 + (1 - prodU) / 25 + cNon + gAllC +
     s2P tab 1000 2000,
   46 * cU tab 41 2000 + ((3 : Rat) ^ kU - 1) + eNon + gAllE Nt + cP tab 1000 2000)

def caseIIT (tab : List (Nat × PSt)) (Nt : Nat) : CE :=
  addCE (addCE (resCE tab 25 2 [2, 5] 2000) (lemCT tab Nt)) (shT tab)

def caseIII1T (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (addCE (resCE tab 100 6 [2, 5] 2000) (shT tab))
    (addCE (resCE tab 100 2 [2, 5] 2000) (shT tab))) (lemBT tab 50 23)

def caseIII2aT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (2 / 100, 2) (addCE (resCE tab 100 2 [2, 5] 2000) (shT tab))) (lemBT tab 100 23)

def caseIII2bT (tab : List (Nat × PSt)) : CE :=
  addCE (addCE (addCE (1 / 100, 1) (addCE (resCE tab 100 3 [2, 5] 2000) (shT tab)))
    (addCE (resCE tab 25 1 [2, 5] 2000) (shT tab))) (lemBT tab 100 23)

def okT (c : CE) : Bool := decide (c.1 ≤ 1 / 25 - 1 / 1000) && decide (c.2 ≤ 10 ^ 30)

def checkTailH4 (tab : List (Nat × PSt)) : Bool :=
  okT (caseIII2aT tab) && okT (caseIII2bT tab)

def checkTailH3 (tab : List (Nat × PSt)) (Nt : Nat) : Bool :=
  okT (caseIIT tab Nt) && okT (caseIII1T tab)

end ErdosComp


namespace Erdos848

def Admissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

def c7 (N : ℕ) : ℕ := (N + 18) / 25

def C7set (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => n % 25 = 7)

def Statement (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible A → A.card ≤ c7 N

lemma not_squarefree_of_mul_self_dvd {n p : ℕ} (hp : 2 ≤ p) (h : p * p ∣ n) :
    ¬ Squarefree n := by
  intro hs
  have hu := hs p h
  rw [Nat.isUnit_iff] at hu
  omega

lemma C7set_card (N : ℕ) : (C7set N).card = c7 N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    unfold C7set at ih ⊢
    rw [hIcc, Finset.filter_insert]
    unfold c7 at ih ⊢
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

theorem C7set_admissible (N : ℕ) : Admissible (C7set N) := by
  intro a ha b hb
  simp only [C7set, Finset.mem_filter] at ha hb
  apply not_squarefree_of_mul_self_dvd (p := 5) (by norm_num)
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mul_mod, ha.2, hb.2]

theorem lower_bound (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Admissible A ∧ A.card = c7 N :=
  ⟨C7set N, Finset.filter_subset _ _, C7set_admissible N, C7set_card N⟩

theorem card_le_of_coloring {A : Finset ℕ} {k : ℕ} (f : ℕ → ℕ) (hA : Admissible A)
    (hf : ∀ a ∈ A, f a < k)
    (hcol : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → f a = f b → Squarefree (a * b + 1)) :
    A.card ≤ k := by
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    by_contra hne
    exact hA a ha b hb (hcol a ha b hb hne hab)
  calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simpa using hf a ha
    _ = k := Finset.card_range k

lemma mod_mul_add_one (a b m : ℕ) : (a * b + 1) % m = ((a % m) * (b % m) + 1) % m := by
  rw [Nat.add_mod, Nat.mul_mod]; conv_rhs => rw [Nat.add_mod]

lemma F1 (x : ℕ) : 25 ∣ x * x + 1 ↔ x % 25 = 7 ∨ x % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  have h := Nat.mod_lt x (by norm_num : 25 > 0)
  interval_cases (x % 25) <;> simp

lemma F2_seven (a b : ℕ) (ha : a % 25 = 7) : 25 ∣ a * b + 1 ↔ b % 25 = 7 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one, ha]
  have h := Nat.mod_lt b (by norm_num : 25 > 0)
  interval_cases (b % 25) <;> simp

lemma F2_eighteen (a b : ℕ) (ha : a % 25 = 18) : 25 ∣ a * b + 1 ↔ b % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one, ha]
  have h := Nat.mod_lt b (by norm_num : 25 > 0)
  interval_cases (b % 25) <;> simp

lemma F3 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) : ¬ 25 ∣ a * b + 1 := by
  rw [F2_seven a b ha, hb]; norm_num

lemma F4 (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) : 4 ∣ a * b + 1 ↔ a % 4 ≠ b % 4 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases ha4 with h1 | h1 <;> rcases hb4 with h2 | h2 <;> simp [h1, h2]

lemma F4_even (a b : ℕ) (h : a % 2 = 0 ∨ b % 2 = 0) : ¬ 2 ∣ a * b + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, mod_mul_add_one]
  rcases h with h | h <;> simp [h]

lemma mem_V_of_admissible {A : Finset ℕ} (hA : Admissible A) {a : ℕ} (ha : a ∈ A) :
    ¬ Squarefree (a * a + 1) := hA a ha a ha

end Erdos848


namespace Erdos848

open Finset

def IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18

instance : DecidablePred IsStar := fun _ => inferInstanceAs (Decidable (_ ∧ _))

def badCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card

def classCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ := ((Icc 1 N).filter P).card

def vCount (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  ((Icc 1 N).filter (fun x => P x ∧ ¬ Squarefree (x * x + 1))).card

def lemCCount (N b : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))).card

def Witness (N b : ℕ) : Prop := 1 ≤ b ∧ b ≤ N ∧ ¬ Squarefree (b * b + 1)

structure CountBounds (N : ℕ) : Prop where

  caseIb : ∀ b b', Witness N b → b % 25 = 7 → Witness N b' → b' % 25 = 18 →
    badCount N (fun a => a % 25 = 18) b + badCount N (fun a => a % 25 = 7) b' ≤ c7 N

  caseII : ∀ b, Witness N b → IsStar b → b % 2 = 0 →
    badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount N b ≤ c7 N

  caseIII1 : ∀ b₁ b₃, Witness N b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness N b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount N (fun x => IsStar x ∧ x % 2 = 1) ≤ c7 N

  caseIII2a : ∀ b r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N

  caseIII2b7 : ∀ b b' r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount N (fun a => a % 25 = 18) b' +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N

  caseIII2b18 : ∀ b b' r, Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness N b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount N (fun a => a % 25 = 7) b' +
    vCount N (fun x => IsStar x ∧ x % 4 = r) ≤ c7 N

end Erdos848


namespace Erdos848

open Finset

lemma card_mod_eq_le (N Q r : ℕ) :
    ((Icc 1 N).filter (fun a => a % Q = r)).card ≤ N / Q + 1 := by

  calc ((Icc 1 N).filter (fun a => a % Q = r)).card
      ≤ (range (N / Q + 1)).card := by
        apply card_le_card_of_injOn (fun a => a / Q)
        · intro a ha
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right ha.1.2)
        · intro a ha a' ha' h
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ha'
          simp only at h
          rw [← Nat.div_add_mod a Q, ← Nat.div_add_mod a' Q, h, ha.2, ha'.2]
    _ = N / Q + 1 := card_range _

lemma exists_prime_sq_dvd {n : ℕ} (h : ¬ Squarefree n) : ∃ p, p.Prime ∧ p * p ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, hd⟩

lemma not_sq_dvd_of_dvd {p a b : ℕ} (hp : p.Prime) (hpb : p ∣ b) : ¬ p * p ∣ a * b + 1 := by
  intro h
  have h1 : p ∣ a * b + 1 := dvd_trans (Dvd.intro p rfl) h
  have h2 : p ∣ a * b := dvd_mul_of_dvd_right hpb a
  have : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

lemma prime_sq_dvd_mul_add_one_iff {p b : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    ∃ c < p * p, ∀ a, p * p ∣ a * b + 1 ↔ a % (p * p) = c := by
  have hpp : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  have hcop : Nat.Coprime b (p * p) :=
    Nat.Coprime.mul_right ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))

  set u := ((ZMod.unitOfCoprime b hcop)⁻¹ : (ZMod (p * p))ˣ)
  set c := ((-(u : ZMod (p * p))).val) with hc
  have : NeZero (p * p) := ⟨hpp.ne'⟩
  refine ⟨c, ZMod.val_lt _, fun a => ?_⟩
  have hb : ((b : ZMod (p * p)) * (u : ZMod (p * p))) = 1 := by
    have := Units.mul_inv (ZMod.unitOfCoprime b hcop)
    simp [u, ZMod.coe_unitOfCoprime] at this ⊢
  rw [← ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    have h' : ((a : ZMod (p * p)) * b + 1) = 0 := by exact_mod_cast h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      have := congrArg (· * (u : ZMod (p * p))) h'
      simp only [add_mul, zero_mul, one_mul, mul_assoc, hb, mul_one] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [hc, ← this, ZMod.val_natCast]
  · intro h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      rw [← ZMod.natCast_mod a (p * p), h, hc, ZMod.natCast_zmod_val]
    push_cast
    rw [this, neg_mul, mul_comm (u : ZMod (p * p)) (b : ZMod (p * p)), hb, neg_add_cancel]

lemma badCount_le_sum (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] (S : Finset ℕ)
    (hS : ∀ p, p.Prime → ¬ p ∣ b → p * p ≤ N * b + 1 → p ∈ S) :
    badCount N P b ≤ ∑ p ∈ S, ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card := by
  unfold badCount
  calc ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card
      ≤ (S.biUnion (fun p => (Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1))).card := by
        apply card_le_card
        intro a ha
        simp only [mem_filter, mem_Icc] at ha
        obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd ha.2.2
        have hpb : ¬ p ∣ b := fun h => not_sq_dvd_of_dvd hp h hd
        have hle : p * p ≤ N * b + 1 := by
          have := Nat.le_of_dvd (Nat.succ_pos _) hd
          have : a * b ≤ N * b := Nat.mul_le_mul_right b ha.1.2
          omega
        simp only [mem_biUnion, mem_filter, mem_Icc]
        exact ⟨p, hS p hp hpb hle, ⟨ha.1, ha.2.1, hd⟩⟩
    _ ≤ _ := card_biUnion_le

lemma card_sq_dvd_le (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card ≤ N / (p * p) + 1 := by
  obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp hpb
  calc ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card
      ≤ ((Icc 1 N).filter (fun a => a % (p * p) = c)).card := by
        apply card_le_card; intro a ha
        simp only [mem_filter] at ha ⊢
        exact ⟨ha.1, (hc a).mp ha.2.2⟩
    _ ≤ N / (p * p) + 1 := card_mod_eq_le N (p * p) c

end Erdos848


namespace Erdos848

open Finset

lemma card_mod_eq_ge (N Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    N / Q ≤ ((Icc 1 N).filter (fun a => a % Q = r)).card := by

  let f : ℕ → ℕ := fun i => if r = 0 then (i + 1) * Q else i * Q + r
  calc N / Q = (range (N / Q)).card := (card_range _).symm
    _ ≤ ((Icc 1 N).filter (fun a => a % Q = r)).card := by
      apply card_le_card_of_injOn f
      · intro i hi
        simp only [coe_range, Set.mem_Iio] at hi
        have hiQ : (i + 1) * Q ≤ N := by
          have := (Nat.lt_div_iff_mul_lt hQ).mp hi
          calc (i + 1) * Q ≤ N / Q * Q := Nat.mul_le_mul_right Q hi
            _ ≤ N := Nat.div_mul_le_self N Q
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc, f]
        split_ifs with h0
        · refine ⟨⟨by nlinarith, hiQ⟩, ?_⟩
          rw [h0]; exact Nat.mul_mod_left _ _
        · refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      · intro i _ j _ hij
        simp only [f] at hij
        split_ifs at hij with h0
        · exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right hQ hij)
        · have : i * Q = j * Q := by omega
          exact Nat.eq_of_mul_eq_mul_right hQ this

lemma card_mod_eq_real (N Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    |(((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q| ≤ 1 := by
  have h1 := card_mod_eq_le N Q r
  have h2 := card_mod_eq_ge N Q r hQ hr
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have e1 : ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) / Q := Nat.cast_div_le
  have e2 : (N : ℝ) / Q < ((N / Q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hQ']
    have := Nat.lt_div_mul_add hQ (a := N)
    exact_mod_cast (by nlinarith [Nat.div_add_mod N Q, Nat.mod_lt N hQ] : N < (N / Q + 1) * Q)
  rw [abs_le]
  constructor
  · have : ((N / Q : ℕ) : ℝ) ≤ (((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) := by exact_mod_cast h2
    linarith
  · have : (((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) ≤ ((N / Q : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith

lemma card_mod_mem_real (N Q : ℕ) (hQ : 0 < Q) (D : Finset ℕ) (hD : ∀ r ∈ D, r < Q) :
    |(((Icc 1 N).filter (fun a => a % Q ∈ D)).card : ℝ) - D.card * ((N : ℝ) / Q)| ≤ D.card := by
  have hsplit : ((Icc 1 N).filter (fun a => a % Q ∈ D)).card =
      ∑ r ∈ D, ((Icc 1 N).filter (fun a => a % Q = r)).card := by
    rw [← card_biUnion]
    · congr 1; ext a; simp only [mem_filter, mem_biUnion]
      constructor
      · rintro ⟨ha, hD'⟩; exact ⟨a % Q, hD', ha, rfl⟩
      · rintro ⟨r, hr, ha, rfl⟩; exact ⟨ha, hr⟩
    · intro r _ s _ hrs
      rw [Function.onFun, disjoint_left]
      intro a ha hb
      simp only [mem_filter] at ha hb
      exact hrs (ha.2.symm.trans hb.2)
  rw [hsplit]
  push_cast
  calc |∑ r ∈ D, ((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ)) - D.card * ((N : ℝ) / Q)|
      = |∑ r ∈ D, ((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q)| := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ D, |((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ D, (1 : ℝ) := sum_le_sum (fun r hr => card_mod_eq_real N Q r hQ (hD r hr))
    _ = D.card := by simp

section CRT
variable (q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ)

def bigMod (T : Finset ℕ) : ℕ := q * ∏ p ∈ T, m p

def resSet (T : Finset ℕ) : Finset ℕ :=
  (range (bigMod q m T)).filter (fun r => r % q = t ∧ ∀ p ∈ T, r % m p ∈ Rs p)

variable {q t m Rs}

lemma mod_bigMod_mod_q (T : Finset ℕ) (a : ℕ) : a % bigMod q m T % q = a % q :=
  Nat.mod_mod_of_dvd a (dvd_mul_right q _)

lemma mod_bigMod_mod_m {T : Finset ℕ} {p : ℕ} (hp : p ∈ T) (a : ℕ) :
    a % bigMod q m T % m p = a % m p :=
  Nat.mod_mod_of_dvd a (dvd_mul_of_dvd_right (dvd_prod_of_mem m hp) q)

lemma cond_iff_resSet (T : Finset ℕ) (hq : 0 < q) (hm : ∀ p ∈ T, 0 < m p) (a : ℕ) :
    (a % q = t ∧ ∀ p ∈ T, a % m p ∈ Rs p) ↔ a % bigMod q m T ∈ resSet q t m Rs T := by
  have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p hp))
  simp only [resSet, mem_filter, mem_range, Nat.mod_lt _ hpos, true_and, mod_bigMod_mod_q]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp => by rw [mod_bigMod_mod_m hp]; exact h2 p hp⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp => by have := h2 p hp; rwa [mod_bigMod_mod_m hp] at this⟩

theorem card_resSet (T : Finset ℕ) (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ T, 0 < m p) (hR : ∀ p ∈ T, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ T, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (resSet q t m Rs T).card = ∏ p ∈ T, (Rs p).card := by
  induction T using Finset.induction_on with
  | empty =>
    have : resSet q t m Rs ∅ = {t} := by
      ext r
      simp only [resSet, bigMod, prod_empty, mul_one, mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hr, h, -⟩; rwa [Nat.mod_eq_of_lt hr] at h
      · rintro rfl; exact ⟨ht, Nat.mod_eq_of_lt ht, fun p hp => absurd hp (Finset.notMem_empty p)⟩
    rw [this]; simp
  | insert p T hpT ih =>
    have ih' := ih (fun p' hp' => hm p' (mem_insert_of_mem hp'))
      (fun p' hp' => hR p' (mem_insert_of_mem hp')) (fun p' hp' => hcopq p' (mem_insert_of_mem hp'))
      (fun a ha b hb hab => hcop a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
    rw [prod_insert hpT, ← ih']
    set Q' := bigMod q m T
    have hQ'pos : 0 < Q' := Nat.mul_pos hq (prod_pos (fun p' hp' => hm p' (mem_insert_of_mem hp')))
    have hmp : 0 < m p := hm p (mem_insert_self p T)
    have hcopQ : Nat.Coprime Q' (m p) := by
      apply Nat.coprime_mul_iff_left.mpr
      refine ⟨hcopq p (mem_insert_self p T), ?_⟩
      rw [Nat.coprime_prod_left_iff]
      intro p' hp'
      exact hcop p' (mem_insert_of_mem hp') p (mem_insert_self p T) (fun h => hpT (h ▸ hp'))
    have hbig : bigMod q m (insert p T) = Q' * m p := by
      simp only [bigMod, Q', prod_insert hpT]; ring

    rw [mul_comm, ← card_product]
    apply card_bij (fun r _ => (r % Q', r % m p))
    · intro r hr
      simp only [resSet, mem_filter, mem_range, hbig] at hr
      simp only [mem_product, resSet, mem_filter, mem_range]
      refine ⟨⟨Nat.mod_lt _ hQ'pos, ?_, ?_⟩, ?_⟩
      · rw [mod_bigMod_mod_q]; exact hr.2.1
      · intro p' hp'; rw [mod_bigMod_mod_m hp']; exact hr.2.2 p' (mem_insert_of_mem hp')
      · exact hr.2.2 p (mem_insert_self p T)
    · intro r hr r' hr' h
      simp only [Prod.mk.injEq] at h
      simp only [resSet, mem_filter, mem_range, hbig] at hr hr'
      have := (Nat.modEq_and_modEq_iff_modEq_mul hcopQ).mp ⟨h.1, h.2⟩
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt hr'.1] at this
    · intro ⟨u, v⟩ huv
      simp only [mem_product, resSet, mem_filter, mem_range] at huv
      obtain ⟨⟨hu, hut, huT⟩, hv⟩ := huv
      have hvm : v < m p := hR p (mem_insert_self p T) v hv
      let k := Nat.chineseRemainder hcopQ u v
      refine ⟨k.1 % (Q' * m p), ?_, ?_⟩
      · simp only [resSet, mem_filter, mem_range, hbig]
        have hk1 : k.1 % (Q' * m p) % Q' = u := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right Q' (m p))]
          have := k.2.1; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hu]
        have hk2 : k.1 % (Q' * m p) % m p = v := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (m p) Q')]
          have := k.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hvm]
        refine ⟨Nat.mod_lt _ (Nat.mul_pos hQ'pos hmp), ?_, ?_⟩
        · rw [← mod_bigMod_mod_q (m := m) T, hk1]; exact hut
        · intro p' hp'
          rcases mem_insert.mp hp' with rfl | hp''
          · rw [hk2]; exact hv
          · rw [← mod_bigMod_mod_m (q := q) hp'', hk1]; exact huT p' hp''
      · simp only [Prod.mk.injEq]
        constructor
        · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right Q' (m p))]
          have := k.2.1; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hu]
        · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (m p) Q')]
          have := k.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hvm]

end CRT

lemma sum_powerset_alt (P : Finset ℕ) (x : ℕ → ℝ) :
    ∑ T ∈ P.powerset.filter (·.Nonempty), (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, x p =
      1 - ∏ p ∈ P, (1 - x p) := by
  have h := Finset.prod_add (fun p => -x p) (fun _ => (1 : ℝ)) P
  simp only [prod_const_one, mul_one] at h
  have h' : ∏ p ∈ P, (1 - x p) = ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
    rw [show (fun p => 1 - x p) = (fun p => -x p + 1) by ext; ring, h]
    apply sum_congr rfl; intro T _
    rw [prod_neg]
  rw [h', ← sum_filter_add_sum_filter_not P.powerset (·.Nonempty)]
  have hempty : ∑ T ∈ P.powerset.filter (fun T => ¬ T.Nonempty), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p = 1 := by
    rw [show P.powerset.filter (fun T => ¬ T.Nonempty) = {∅} by
      ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨empty_subset _, rfl⟩]
    simp
  rw [hempty]
  have : ∀ T ∈ P.powerset.filter (·.Nonempty),
      (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, x p = -((-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
    intro T _; ring
  rw [sum_congr rfl this, sum_neg_distrib]; ring

lemma sum_powerset_prod (P : Finset ℕ) (y : ℕ → ℝ) :
    ∑ T ∈ P.powerset.filter (·.Nonempty), ∏ p ∈ T, y p = ∏ p ∈ P, (1 + y p) - 1 := by
  have h := Finset.prod_add y (fun _ => (1 : ℝ)) P
  simp only [prod_const_one, mul_one] at h
  rw [show (fun p => 1 + y p) = (fun p => y p + 1) by ext; ring, h,
    ← sum_filter_add_sum_filter_not P.powerset (·.Nonempty)]
  rw [show P.powerset.filter (fun T => ¬ T.Nonempty) = {∅} by
      ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨empty_subset _, rfl⟩]
  simp

theorem card_union_abs (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    |(((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) -
      (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p))| ≤
        ∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1 := by
  classical
  let S : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun a => a % q = t ∧ a % m p ∈ Rs p)
  have hunion : (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p) = P.biUnion S := by
    ext a; simp only [mem_filter, mem_biUnion, S]
    constructor
    · rintro ⟨ha, h1, p, hp, h2⟩; exact ⟨p, hp, ha, h1, h2⟩
    · rintro ⟨p, hp, ha, h1, h2⟩; exact ⟨ha, h1, p, hp, h2⟩

  have hinter : ∀ T (hT : T.Nonempty), T ⊆ P →
      T.inf' hT S = (Icc 1 N).filter (fun a => a % bigMod q m T ∈ resSet q t m Rs T) := by
    intro T hT hTP
    ext a
    rw [mem_inf']
    simp only [S, mem_filter]
    rw [← cond_iff_resSet T hq (fun p hp => hm p (hTP hp))]
    constructor
    · intro h
      obtain ⟨p0, hp0⟩ := hT
      exact ⟨(h p0 hp0).1, (h p0 hp0).2.1, fun p hp => (h p hp).2.2⟩
    · rintro ⟨ha, h1, h2⟩ p hp; exact ⟨ha, h1, h2 p hp⟩

  have hT : ∀ T ∈ P.powerset.filter (·.Nonempty),
      |(-1 : ℝ) ^ (T.card + 1) * (((Icc 1 N).filter
          (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ) -
        (-1 : ℝ) ^ (T.card + 1) * ((N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p)| ≤
          ∏ p ∈ T, ((Rs p).card : ℝ) := by
    intro T hTm
    simp only [mem_filter, mem_powerset] at hTm
    have hTP := hTm.1
    have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p (hTP hp)))
    have hD : ∀ r ∈ resSet q t m Rs T, r < bigMod q m T := by
      intro r hr; simp only [resSet, mem_filter, mem_range] at hr; exact hr.1
    have hc := card_mod_mem_real N (bigMod q m T) hpos (resSet q t m Rs T) hD
    have hcard := card_resSet T hq ht (fun p hp => hm p (hTP hp)) (fun p hp => hR p (hTP hp))
      (fun p hp => hcopq p (hTP hp)) (fun p hp p' hp' => hcop p (hTP hp) p' (hTP hp'))
    rw [hcard] at hc
    have hbigR : ((bigMod q m T : ℕ) : ℝ) = (q : ℝ) * ∏ p ∈ T, (m p : ℝ) := by
      simp only [bigMod, Nat.cast_mul, Nat.cast_prod]
    have hmain : ((∏ p ∈ T, (Rs p).card : ℕ) : ℝ) * ((N : ℝ) / ((bigMod q m T : ℕ) : ℝ)) =
        (N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p := by
      rw [hbigR, Nat.cast_prod, prod_div_distrib]; ring
    rw [hmain, Nat.cast_prod] at hc
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hc
  rw [hunion]
  have hIE := inclusion_exclusion_card_biUnion P S
  have hIE' : ((P.biUnion S).card : ℝ) = ∑ T ∈ P.powerset.filter (·.Nonempty),
      (-1 : ℝ) ^ (T.card + 1) * (((Icc 1 N).filter
          (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIE
    simp only [Int.cast_natCast] at this
    rw [this]; push_cast
    rw [← sum_coe_sort (P.powerset.filter (·.Nonempty))]
    apply sum_congr rfl
    intro T _
    have hTP : T.1 ⊆ P := (mem_powerset.mp (mem_filter.mp T.2).1)
    rw [hinter T.1 (mem_filter.mp T.2).2 hTP]
  have hmainE : (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) =
      ∑ T ∈ P.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (T.card + 1) * ((N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p) := by
    rw [← sum_powerset_alt, mul_sum]; apply sum_congr rfl; intro T _; ring
  rw [hIE', hmainE, ← sum_sub_distrib, ← sum_powerset_prod]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hT)

theorem card_union_le (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) +
        (∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1) := by
  have := card_union_abs N q t m Rs P hq ht hm hR hcopq hcop
  rw [abs_le] at this; linarith [this.2]

theorem card_union_ge (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) -
        (∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1) ≤
      (((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) := by
  have := card_union_abs N q t m Rs P hq ht hm hR hcopq hcop
  rw [abs_le] at this; linarith [this.1]

end Erdos848


namespace Erdos848

open Finset

def sqrtCount (b c : ℕ) : ℕ := ((range b).filter (fun x => x * x % b = c % b)).card

theorem sqrtCount_mul_le {b₁ b₂ : ℕ} (h : Nat.Coprime b₁ b₂) (c : ℕ) :
    sqrtCount (b₁ * b₂) c ≤ sqrtCount b₁ c * sqrtCount b₂ c := by
  unfold sqrtCount
  rw [← card_product]
  apply card_le_card_of_injOn (fun x => (x % b₁, x % b₂))
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hx
    have hb₁ : 0 < b₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
    have hb₂ : 0 < b₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
    have hmod := hx.2
    simp only [coe_product, coe_filter, Set.mem_prod, Set.mem_ofPred_eq, mem_range]
    refine ⟨⟨Nat.mod_lt _ hb₁, ?_⟩, ⟨Nat.mod_lt _ hb₂, ?_⟩⟩
    · have : x * x % b₁ = c % b₁ := by
        have := congrArg (· % b₁) hmod
        simpa [Nat.mod_mod_of_dvd _ (dvd_mul_right b₁ b₂)] using this
      rw [← Nat.mul_mod]; exact this
    · have : x * x % b₂ = c % b₂ := by
        have := congrArg (· % b₂) hmod
        simpa [Nat.mod_mod_of_dvd _ (dvd_mul_left b₂ b₁)] using this
      rw [← Nat.mul_mod]; exact this
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have h1 : x ≡ y [MOD b₁] := hxy.1
    have h2 : x ≡ y [MOD b₂] := hxy.2
    have h12 : x ≡ y [MOD b₁ * b₂] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1, h2⟩
    unfold Nat.ModEq at h12
    rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h12

theorem sqrtCount_oddPrimePow_le {p e c : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpc : ¬ p ∣ c) :
    sqrtCount (p ^ e) c ≤ 2 := by
  unfold sqrtCount
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [pow_zero]
    calc ((range 1).filter (fun x => x * x % 1 = c % 1)).card ≤ (range 1).card := card_filter_le _ _
      _ ≤ 2 := by simp
  set P := p ^ e with hP
  set S := (range P).filter (fun x => x * x % P = c % P)
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hS
  have hPpos : 0 < P := pow_pos hp.pos e
  have hpP : p ∣ P := dvd_pow_self p he.ne'

  have hnd : ∀ z, z * z % P = c % P → ¬ p ∣ z := by
    intro z hz hpz
    apply hpc
    have h2 : (z * z) % P % p = c % P % p := by rw [hz]
    rw [Nat.mod_mod_of_dvd _ hpP, Nat.mod_mod_of_dvd _ hpP] at h2
    exact Nat.dvd_of_mod_eq_zero (h2 ▸ Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpz z))
  simp only [S, mem_filter, mem_range] at hx₀
  have hx0 := hnd x₀ hx₀.2
  have key : ∀ y ∈ S, y = x₀ ∨ y = P - x₀ := by
    intro y hy
    simp only [S, mem_filter, mem_range] at hy

    have hmod : y * y ≡ x₀ * x₀ [MOD P] := by unfold Nat.ModEq; rw [hx₀.2, hy.2]
    have hdvd : (P : ℤ) ∣ ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      push_cast at this
      have e1 : ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) = (x₀ : ℤ) * x₀ - y * y := by ring
      rw [e1]; exact this
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp

    have hnot : ¬ ((p : ℤ) ∣ (x₀ : ℤ) - y ∧ (p : ℤ) ∣ (x₀ : ℤ) + y) := by
      rintro ⟨h1, h2⟩
      have h3 : (p : ℤ) ∣ 2 * (x₀ : ℤ) := by
        have := dvd_add h1 h2; rw [show (x₀ : ℤ) - y + (x₀ + y) = 2 * x₀ by ring] at this; exact this
      rcases hpZ.dvd_or_dvd h3 with h4 | h4
      · have : p ∣ 2 := by exact_mod_cast h4
        exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact hx0 (by exact_mod_cast h4)
    have hPZ : (P : ℤ) = (p : ℤ) ^ e := by rw [hP]; push_cast; ring
    by_cases hu : (p : ℤ) ∣ (x₀ : ℤ) - y
    ·
      have hv : ¬ (p : ℤ) ∣ (x₀ : ℤ) + y := fun hv => hnot ⟨hu, hv⟩
      have hcop : IsCoprime ((p : ℤ) ^ e) ((x₀ : ℤ) + y) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hv)
      have : (P : ℤ) ∣ (x₀ : ℤ) - y := by
        rw [hPZ] at hdvd ⊢; exact hcop.dvd_of_dvd_mul_right hdvd
      left
      have hlt : |(x₀ : ℤ) - y| < (P : ℤ) := by
        rw [abs_lt]; constructor <;> push_cast <;> omega
      have := Int.eq_zero_of_abs_lt_dvd this hlt
      omega
    ·
      have hcop : IsCoprime ((p : ℤ) ^ e) ((x₀ : ℤ) - y) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hu)
      have h1 : (P : ℤ) ∣ (x₀ : ℤ) + y := by
        rw [hPZ] at hdvd ⊢; exact hcop.dvd_of_dvd_mul_left hdvd
      have h2 : P ∣ x₀ + y := by exact_mod_cast h1
      right
      obtain ⟨k, hk⟩ := h2
      have hx0pos : 0 < x₀ := Nat.pos_of_ne_zero (fun h => hx0 (h ▸ dvd_zero p))
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
  calc S.card ≤ ({x₀, P - x₀} : Finset ℕ).card := by
        apply card_le_card; intro y hy
        rcases key y hy with h | h <;> simp [h]
    _ ≤ 2 := card_le_two

lemma two_pow_sq_eq {e : ℕ} (he : 3 ≤ e) {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : (2 : ℤ) ^ e ∣ (x - y) * (x + y)) :
    (2 : ℤ) ^ (e - 1) ∣ x - y ∨ (2 : ℤ) ^ (e - 1) ∣ x + y := by
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ x - y := Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ x + y := Int.dvd_of_emod_eq_zero (by omega)
  have hsum : u + v = x := by linarith
  have h4 : (2 : ℤ) ^ e = 2 * 2 * 2 ^ (e - 2) := by
    conv_lhs => rw [show e = (e - 2) + 2 from by omega]
    rw [pow_add]; ring
  have hdvd : (2 : ℤ) ^ (e - 2) ∣ u * v := by
    rw [hu, hv, h4] at h
    have : (2 * 2 * 2 ^ (e - 2) : ℤ) ∣ 2 * 2 * (u * v) := by
      rw [show (2 : ℤ) * u * (2 * v) = 2 * 2 * (u * v) by ring] at h; exact h
    exact (mul_dvd_mul_iff_left (by norm_num : (2 * 2 : ℤ) ≠ 0)).mp this
  have hodd2 : ∀ w : ℤ, w % 2 = 1 → IsCoprime ((2 : ℤ) ^ (e - 2)) w := by
    intro w hw
    apply IsCoprime.pow_left
    exact (Prime.coprime_iff_not_dvd Int.prime_two).mpr (by omega)
  have hpow : (2 : ℤ) ^ (e - 1) = 2 * 2 ^ (e - 2) := by
    rw [← pow_succ']; congr 1; omega
  rcases Int.emod_two_eq_zero_or_one u with hu0 | hu1
  ·
    have hv1 : v % 2 = 1 := by omega
    have := (hodd2 v hv1).dvd_of_dvd_mul_right hdvd
    left; rw [hu, hpow]; exact mul_dvd_mul_left 2 this
  ·
    have := (hodd2 u hu1).dvd_of_dvd_mul_left hdvd
    right; rw [hv, hpow]; exact mul_dvd_mul_left 2 this

theorem sqrtCount_twoPow_le {e c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ e) c ≤ 4 := by
  unfold sqrtCount
  rcases Nat.lt_or_ge e 3 with he | he
  · calc ((range (2 ^ e)).filter (fun x => x * x % 2 ^ e = c % 2 ^ e)).card ≤ (range (2 ^ e)).card :=
          card_filter_le _ _
      _ = 2 ^ e := card_range _
      _ ≤ 4 := by interval_cases e <;> norm_num
  set P := 2 ^ e with hP
  set Q := 2 ^ (e - 1) with hQ
  have hPQ : P = 2 * Q := by rw [hP, hQ, ← pow_succ']; congr 1; omega
  have hQpos : 0 < Q := pow_pos (by norm_num) _
  set S := (range P).filter (fun x => x * x % P = c % P)
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hS
  have h2P : 2 ∣ P := by rw [hPQ]; exact dvd_mul_right 2 Q
  have hoddsol : ∀ z, z * z % P = c % P → z % 2 = 1 := by
    intro z hz
    have h2 : (z * z) % P % 2 = c % P % 2 := by rw [hz]
    rw [Nat.mod_mod_of_dvd _ h2P, Nat.mod_mod_of_dvd _ h2P, hc] at h2
    rcases Nat.mod_two_eq_zero_or_one z with h | h
    · rw [Nat.mul_mod, h] at h2; simp at h2
    · exact h
  simp only [S, mem_filter, mem_range] at hx₀
  have hx0o := hoddsol x₀ hx₀.2

  have key : ∀ y ∈ S, y % Q = x₀ % Q ∨ (y + x₀) % Q = 0 := by
    intro y hy
    simp only [S, mem_filter, mem_range] at hy
    have hyo := hoddsol y hy.2
    have hmod : y * y ≡ x₀ * x₀ [MOD P] := by unfold Nat.ModEq; rw [hx₀.2, hy.2]
    have hdvd : ((2 : ℤ) ^ e) ∣ ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) := by
      have := (Nat.modEq_iff_dvd.mp hmod)
      rw [hP] at this; push_cast at this
      have e1 : ((x₀ : ℤ) - y) * ((x₀ : ℤ) + y) = (x₀ : ℤ) * x₀ - y * y := by ring
      rw [e1]; exact this
    have hQZ : ((Q : ℕ) : ℤ) = (2 : ℤ) ^ (e - 1) := by rw [hQ]; push_cast; ring
    rcases two_pow_sq_eq he (by omega) (by omega) hdvd with h1 | h1
    · left
      have : ((Q : ℕ) : ℤ) ∣ (x₀ : ℤ) - y := by rw [hQZ]; exact h1
      exact (Nat.modEq_iff_dvd).mpr this
    · right
      have : ((Q : ℕ) : ℤ) ∣ (x₀ : ℤ) + y := by rw [hQZ]; exact h1
      have h2 : Q ∣ y + x₀ := by
        have : ((Q : ℕ) : ℤ) ∣ ((y + x₀ : ℕ) : ℤ) := by push_cast; rwa [add_comm]
        exact_mod_cast this
      exact Nat.mod_eq_zero_of_dvd h2

  set r₁ := x₀ % Q
  set r₂ := (Q - x₀ % Q) % Q
  calc S.card ≤ ({r₁, r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card := by
        apply card_le_card
        intro y hy
        have hyP : y < P := by simp only [S, mem_filter, mem_range] at hy; exact hy.1
        have hr1 : r₁ < Q := Nat.mod_lt _ hQpos
        rcases key y hy with h | h
        ·
          have : y = r₁ ∨ y = r₁ + Q := by
            have := Nat.div_add_mod y Q
            have hq : y / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            interval_cases hyq : y / Q <;> omega
          rcases this with h' | h' <;> simp [h']
        ·
          have hy2 : y % Q = r₂ := by
            have ha : y % Q < Q := Nat.mod_lt _ hQpos
            have hb : x₀ % Q < Q := Nat.mod_lt _ hQpos
            rw [Nat.add_mod] at h
            have hdm := Nat.div_add_mod (y % Q + x₀ % Q) Q
            rw [h] at hdm
            have hq : (y % Q + x₀ % Q) / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            simp only [r₂]
            interval_cases hq' : (y % Q + x₀ % Q) / Q
            ·
              have h0 : x₀ % Q = 0 := by omega
              have h0' : y % Q = 0 := by omega
              rw [h0, h0', Nat.sub_zero, Nat.mod_self]
            ·
              rcases Nat.eq_zero_or_pos (x₀ % Q) with h0 | h0
              · rw [h0, Nat.sub_zero, Nat.mod_self]; omega
              · rw [Nat.mod_eq_of_lt (show Q - x₀ % Q < Q by omega)]; omega
          have : y = r₂ ∨ y = r₂ + Q := by
            have := Nat.div_add_mod y Q
            have hq : y / Q < 2 := by rw [Nat.div_lt_iff_lt_mul hQpos]; omega
            interval_cases hyq : y / Q <;> omega
          rcases this with h' | h' <;> simp [h']
    _ ≤ 4 := by
        calc ({r₁, r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card
            ≤ ({r₁ + Q, r₂, r₂ + Q} : Finset ℕ).card + 1 := card_insert_le _ _
          _ ≤ (({r₂, r₂ + Q} : Finset ℕ).card + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ ≤ ((({r₂ + Q} : Finset ℕ).card + 1) + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ = 4 := by simp

lemma sqrtCount_two_le {c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ 1) c ≤ 1 := by
  unfold sqrtCount; rw [pow_one, hc]; decide

lemma sqrtCount_four_le {c : ℕ} (hc : c % 2 = 1) : sqrtCount (2 ^ 2) c ≤ 2 := by
  unfold sqrtCount
  have : c % 4 = 1 ∨ c % 4 = 3 := by omega
  norm_num
  rcases this with h | h <;> rw [h] <;> decide

def oddOmega (b : ℕ) : ℕ := (b.primeFactors.filter (· ≠ 2)).card

def twoFactor (b : ℕ) : ℕ := if 8 ∣ b then 4 else if 4 ∣ b then 2 else 1

def rhoBound (b : ℕ) : ℕ := twoFactor b * 2 ^ oddOmega b

lemma oddOmega_mul {a b : ℕ} (h : Nat.Coprime a b) : oddOmega (a * b) = oddOmega a + oddOmega b := by
  unfold oddOmega
  rw [Nat.Coprime.primeFactors_mul h, filter_union]
  exact card_union_of_disjoint (disjoint_filter_filter h.disjoint_primeFactors)

lemma twoFactor_mul {a b : ℕ} (h : Nat.Coprime a b) : twoFactor a * twoFactor b = twoFactor (a * b) := by

  have h2 : ¬ (2 ∣ a ∧ 2 ∣ b) := by
    rintro ⟨ha, hb⟩
    have := Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.coprime_dvd_right hb h)
    norm_num at this
  have key : ∀ x y : ℕ, ¬ 2 ∣ x → twoFactor x * twoFactor y = twoFactor (x * y) := by
    intro x y hx
    have hx8 : ¬ 8 ∣ x := fun h8 => hx (dvd_trans (by norm_num) h8)
    have hx4 : ¬ 4 ∣ x := fun h4 => hx (dvd_trans (by norm_num) h4)
    have c8 : Nat.Coprime 8 x := Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
    have c4 : Nat.Coprime 4 x := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
    have e8 : 8 ∣ x * y ↔ 8 ∣ y := ⟨fun h => c8.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h x⟩
    have e4 : 4 ∣ x * y ↔ 4 ∣ y := ⟨fun h => c4.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h x⟩
    unfold twoFactor
    simp only [hx8, hx4, ite_false, one_mul, e8, e4]
  by_cases ha : 2 ∣ a
  · have hb : ¬ 2 ∣ b := fun hb => h2 ⟨ha, hb⟩
    rw [mul_comm, mul_comm a b]; exact key b a hb
  · exact key a b ha

lemma rhoBound_mul {a b : ℕ} (h : Nat.Coprime a b) : rhoBound a * rhoBound b = rhoBound (a * b) := by
  unfold rhoBound
  rw [oddOmega_mul h, pow_add, ← twoFactor_mul h]; ring

theorem sqrtCount_le_rhoBound : ∀ b c, Nat.Coprime c b → sqrtCount b c ≤ rhoBound b := by
  intro b
  induction b using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro c hc
    rcases eq_or_ne p 2 with rfl | hp2
    · have hodd : c % 2 = 1 := by
        have : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 hn.ne') hc
        rcases Nat.mod_two_eq_zero_or_one c with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) (by
            intro h2; have := Nat.Coprime.coprime_dvd_left h2 this; norm_num at this)
        · exact h
      have hω : oddOmega (2 ^ n) = 0 := by
        unfold oddOmega; rw [Nat.primeFactors_prime_pow hn.ne' Nat.prime_two]; simp
      unfold rhoBound; rw [hω, pow_zero, mul_one]
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
      · subst h1; calc sqrtCount (2 ^ 1) c ≤ 1 := sqrtCount_two_le hodd
          _ = twoFactor (2 ^ 1) := by decide
      · subst h2; calc sqrtCount (2 ^ 2) c ≤ 2 := sqrtCount_four_le hodd
          _ = twoFactor (2 ^ 2) := by decide
      · calc sqrtCount (2 ^ n) c ≤ 4 := sqrtCount_twoPow_le hodd
          _ = twoFactor (2 ^ n) := by
            unfold twoFactor
            have : 8 ∣ 2 ^ n := by
              have : (8 : ℕ) = 2 ^ 3 := by norm_num
              rw [this]; exact Nat.pow_dvd_pow 2 h3
            simp [this]
    · have hpc : ¬ p ∣ c := by
        intro h
        have : p ∣ Nat.gcd c (p ^ n) := Nat.dvd_gcd h (dvd_pow_self p hn.ne')
        rw [hc] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      calc sqrtCount (p ^ n) c ≤ 2 := sqrtCount_oddPrimePow_le hp hp2 hpc
        _ = rhoBound (p ^ n) := by
          unfold rhoBound oddOmega
          rw [Nat.primeFactors_prime_pow hn.ne' hp]
          have h2 : ¬ 2 ∣ p ^ n := by
            intro h
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
            exact hp2 this.symm
          have h8 : ¬ 8 ∣ p ^ n := fun h8 => h2 (dvd_trans (by norm_num) h8)
          have h4 : ¬ 4 ∣ p ^ n := fun h4 => h2 (dvd_trans (by norm_num) h4)
          simp [twoFactor, h8, h4, Finset.filter_singleton, hp2]
  | zero => intro c _; simp [sqrtCount]
  | one =>
    intro c _
    unfold sqrtCount rhoBound oddOmega twoFactor
    calc ((range 1).filter (fun x => x * x % 1 = c % 1)).card ≤ (range 1).card := card_filter_le _ _
      _ = 1 := by simp
      _ ≤ _ := by simp
  | coprime a b ha hb hab iha ihb =>
    intro c hc
    calc sqrtCount (a * b) c ≤ sqrtCount a c * sqrtCount b c := sqrtCount_mul_le hab c
      _ ≤ rhoBound a * rhoBound b := Nat.mul_le_mul
          (iha c (Nat.Coprime.coprime_mul_right_right hc)) (ihb c (Nat.Coprime.coprime_mul_left_right hc))
      _ = rhoBound (a * b) := rhoBound_mul hab

end Erdos848


namespace Erdos848

open Finset

def OP : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

lemma OP_length : OP.length = 45 := rfl

def primeProd (k : ℕ) : ℕ := (OP.take k).prod

set_option maxRecDepth 20000 in
lemma OP_complete : ∀ p < 200, p.Prime → p ≠ 2 → p ∈ OP := by decide

set_option maxRecDepth 20000 in
lemma OP_count : ∀ a < 200, ∀ k < 45, a < OP[k]! → (OP.filter (· ≤ a)).length ≤ k := by decide

lemma OP_le_199 : ∀ k < 45, OP[k]! ≤ 199 := by decide

lemma primeProd_succ {k : ℕ} (hk : k < 45) : primeProd (k + 1) = primeProd k * OP[k]! := by
  unfold primeProd
  rw [List.prod_take_succ OP k (by rw [OP_length]; exact hk)]
  congr 1
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [OP_length]; exact hk)]

theorem primeProd_le_prod : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ 45 →
    primeProd S.card ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _ _; simp [primeProd]
  | insert a s hlt ih =>
    intro hS hcard
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, prod_insert has] at *
    have hk : s.card < 45 := by omega
    have ih' := ih (fun p hp => hS p (mem_insert_of_mem hp)) (by omega)
    rw [primeProd_succ hk]

    have hOa : OP[s.card]! ≤ a := by
      by_contra hcon
      push Not at hcon
      have ha200 : a < 200 := lt_of_lt_of_le hcon (by have := OP_le_199 s.card hk; omega)
      have hsub : insert a s ⊆ (OP.filter (· ≤ a)).toFinset := by
        intro x hx
        have hxp := hS x hx
        have hxa : x ≤ a := by
          rcases mem_insert.mp hx with rfl | hx'
          · exact le_refl _
          · exact (hlt x hx').le
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨OP_complete x (by omega) hxp.1 hxp.2, by simpa using hxa⟩
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem has] at h1
      have h2 := List.toFinset_card_le (OP.filter (· ≤ a))
      have h3 := OP_count a ha200 s.card hk hcon
      omega
    calc primeProd s.card * OP[s.card]! ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul ih' hOa
      _ = a * ∏ p ∈ s, p := mul_comm _ _

def oddPF (b : ℕ) : Finset ℕ := b.primeFactors.filter (· ≠ 2)

lemma oddOmega_eq (b : ℕ) : oddOmega b = (oddPF b).card := rfl

lemma oddPF_prime {b p : ℕ} (hp : p ∈ oddPF b) : p.Prime ∧ p ≠ 2 := by
  unfold oddPF at hp
  rw [mem_filter, Nat.mem_primeFactors] at hp
  exact ⟨hp.1.1, hp.2⟩

lemma prod_oddPF_dvd (b : ℕ) : (∏ p ∈ oddPF b, p) ∣ b :=
  dvd_trans (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)) (Nat.prod_primeFactors_dvd b)

lemma coprime_two_prod_oddPF (b : ℕ) (n : ℕ) : Nat.Coprime (2 ^ n) (∏ p ∈ oddPF b, p) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  have := oddPF_prime hp
  exact (Nat.coprime_primes Nat.prime_two this.1).mpr (Ne.symm this.2)

def W (L : ℕ) : ℕ := Nat.findGreatest (fun k => primeProd k ≤ L) 45

lemma le_W {k L : ℕ} (hk : k ≤ 45) (h : primeProd k ≤ L) : k ≤ W L := Nat.le_findGreatest hk h

def rhoMax (N : ℕ) : ℕ := max (2 ^ W N) (max (2 * 2 ^ W (N / 4)) (4 * 2 ^ W (N / 8)))

lemma card_oddPF_le {b L : ℕ} (hprod : (∏ p ∈ oddPF b, p) ≤ L) (hL : L < primeProd 45) :
    (oddPF b).card ≤ W L := by
  by_cases h45 : (oddPF b).card ≤ 45
  · exact le_W h45 ((primeProd_le_prod _ (fun p hp => oddPF_prime hp) h45).trans hprod)
  ·
    exfalso
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (show 45 ≤ (oddPF b).card by omega)
    have h1 := primeProd_le_prod T (fun p hp => oddPF_prime (hT hp)) (by omega)
    rw [hTc] at h1
    have h2 : (∏ p ∈ T, p) ≤ ∏ p ∈ oddPF b, p :=
      prod_le_prod_of_subset_of_one_le' hT (fun p hp _ => (oddPF_prime hp).1.one_lt.le)
    omega

theorem rhoBound_le_rhoMax {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) (hN : N < primeProd 45) :
    rhoBound b ≤ rhoMax N := by
  unfold rhoBound twoFactor rhoMax
  rw [oddOmega_eq]
  set P := ∏ p ∈ oddPF b, p
  have hb0 : b ≠ 0 := by omega
  have hPb : P ∣ b := prod_oddPF_dvd b
  split_ifs with h8 h4
  ·
    have : 2 ^ 3 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 3) (by simpa using h8) hPb
    have hP : P ≤ N / 8 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_le hP (by have := Nat.div_le_self N 8; omega)
    calc 4 * 2 ^ (oddPF b).card ≤ 4 * 2 ^ W (N / 8) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
  ·
    have : 2 ^ 2 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 2) (by simpa using h4) hPb
    have hP : P ≤ N / 4 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_le hP (by have := Nat.div_le_self N 4; omega)
    calc 2 * 2 ^ (oddPF b).card ≤ 2 * 2 ^ W (N / 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · have hP : P ≤ N := (Nat.le_of_dvd (by omega) hPb).trans hbN
    have := card_oddPF_le hP hN
    calc 1 * 2 ^ (oddPF b).card ≤ 2 ^ W N := by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) this
      _ ≤ _ := le_max_left _ _

end Erdos848


namespace Erdos848

open Finset ErdosComp

def OPNo5 : List ℕ := [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

lemma OPNo5_length : OPNo5.length = 44 := rfl

def primeProdNo5 (k : ℕ) : ℕ := (OPNo5.take k).prod

lemma OPNo5_sub : ∀ p ∈ OP, p ≠ 5 → p ∈ OPNo5 := by decide

lemma OPNo5_complete : ∀ p < 200, p.Prime → p ≠ 2 → p ≠ 5 → p ∈ OPNo5 :=
  fun p hp hpr h2 h5 => OPNo5_sub p (OP_complete p hp hpr h2) h5

set_option maxRecDepth 20000 in
lemma OPNo5_count : ∀ a < 200, ∀ k < 44, a < OPNo5[k]! → (OPNo5.filter (· ≤ a)).length ≤ k := by decide

lemma OPNo5_le_199 : ∀ k < 44, OPNo5[k]! ≤ 199 := by decide

lemma primeProdNo5_succ {k : ℕ} (hk : k < 44) : primeProdNo5 (k + 1) = primeProdNo5 k * OPNo5[k]! := by
  unfold primeProdNo5
  rw [List.prod_take_succ OPNo5 k (by rw [OPNo5_length]; exact hk)]
  congr 1
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [OPNo5_length]; exact hk)]

theorem primeProdNo5_le_prod : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ p ≠ 5) → S.card ≤ 44 →
    primeProdNo5 S.card ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _ _; simp [primeProdNo5]
  | insert a s hlt ih =>
    intro hS hcard
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, prod_insert has] at *
    have hk : s.card < 44 := by omega
    have ih' := ih (fun p hp => hS p (mem_insert_of_mem hp)) (by omega)
    rw [primeProdNo5_succ hk]
    have hOa : OPNo5[s.card]! ≤ a := by
      by_contra hcon
      push Not at hcon
      have ha200 : a < 200 := lt_of_lt_of_le hcon (by have := OPNo5_le_199 s.card hk; omega)
      have hsub : insert a s ⊆ (OPNo5.filter (· ≤ a)).toFinset := by
        intro x hx
        have hxp := hS x hx
        have hxa : x ≤ a := by
          rcases mem_insert.mp hx with rfl | hx'
          · exact le_refl _
          · exact (hlt x hx').le
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨OPNo5_complete x (by omega) hxp.1 hxp.2.1 hxp.2.2, by simpa using hxa⟩
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem has] at h1
      have h2 := List.toFinset_card_le (OPNo5.filter (· ≤ a))
      have h3 := OPNo5_count a ha200 s.card hk hcon
      omega
    calc primeProdNo5 s.card * OPNo5[s.card]! ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul ih' hOa
      _ = a * ∏ p ∈ s, p := mul_comm _ _

def WNo5 (L : ℕ) : ℕ := Nat.findGreatest (fun k => primeProdNo5 k ≤ L) 44

lemma le_WNo5 {k L : ℕ} (hk : k ≤ 44) (h : primeProdNo5 k ≤ L) : k ≤ WNo5 L :=
  Nat.le_findGreatest hk h

def rhoMaxNo5 (N : ℕ) : ℕ := max (2 ^ WNo5 N) (max (2 * 2 ^ WNo5 (N / 4)) (4 * 2 ^ WNo5 (N / 8)))

lemma oddPF_no5 {b : ℕ} (h5 : ¬ 5 ∣ b) : ∀ p ∈ oddPF b, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 := by
  intro p hp
  have hp' := oddPF_prime hp
  refine ⟨hp'.1, hp'.2, ?_⟩
  rintro rfl
  unfold oddPF at hp
  rw [mem_filter, Nat.mem_primeFactors] at hp
  exact h5 hp.1.2.1

lemma card_oddPF_no5_le {b L : ℕ} (h5 : ¬ 5 ∣ b) (hprod : (∏ p ∈ oddPF b, p) ≤ L)
    (hL : L < primeProdNo5 44) : (oddPF b).card ≤ WNo5 L := by
  by_cases h44 : (oddPF b).card ≤ 44
  · exact le_WNo5 h44 ((primeProdNo5_le_prod _ (oddPF_no5 h5) h44).trans hprod)
  · exfalso
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (show 44 ≤ (oddPF b).card by omega)
    have h1 := primeProdNo5_le_prod T (fun p hp => oddPF_no5 h5 p (hT hp)) (by omega)
    rw [hTc] at h1
    have h2 : (∏ p ∈ T, p) ≤ ∏ p ∈ oddPF b, p :=
      prod_le_prod_of_subset_of_one_le' hT (fun p hp _ => (oddPF_prime hp).1.one_lt.le)
    omega

theorem rhoBound_le_rhoMaxNo5 {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) (h5 : ¬ 5 ∣ b)
    (hN : N < primeProdNo5 44) : rhoBound b ≤ rhoMaxNo5 N := by
  unfold rhoBound twoFactor rhoMaxNo5
  rw [oddOmega_eq]
  set P := ∏ p ∈ oddPF b, p
  have hPb : P ∣ b := prod_oddPF_dvd b
  split_ifs with h8 h4
  · have : 2 ^ 3 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 3) (by simpa using h8) hPb
    have hP : P ≤ N / 8 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_no5_le h5 hP (by have := Nat.div_le_self N 8; omega)
    calc 4 * 2 ^ (oddPF b).card ≤ 4 * 2 ^ WNo5 (N / 8) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
  · have : 2 ^ 2 * P ∣ b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b 2) (by simpa using h4) hPb
    have hP : P ≤ N / 4 := by
      have := Nat.le_of_dvd (by omega) this
      rw [Nat.le_div_iff_mul_le (by norm_num)]; norm_num at this; linarith
    have := card_oddPF_no5_le h5 hP (by have := Nat.div_le_self N 4; omega)
    calc 2 * 2 ^ (oddPF b).card ≤ 2 * 2 ^ WNo5 (N / 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) this)
      _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · have hP : P ≤ N := (Nat.le_of_dvd (by omega) hPb).trans hbN
    have := card_oddPF_no5_le h5 hP hN
    calc 1 * 2 ^ (oddPF b).card ≤ 2 ^ WNo5 N := by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) this
      _ ≤ _ := le_max_left _ _

end Erdos848


namespace Erdos848

open Finset Real

lemma sum_inv_sqrt_le (M : ℕ) : ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) ≤ 2 * √(M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) ≤ M := by positivity
    have key : 1 / √((M + 1 : ℕ) : ℝ) ≤ 2 * √((M + 1 : ℕ) : ℝ) - 2 * √(M : ℝ) := by
      push_cast
      have h1 : 0 < √((M : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      rw [div_le_iff₀ h1]
      have hsq : √(M : ℝ) * √((M : ℝ) + 1) ≤ (M : ℝ) + 1 / 2 := by
        rw [← Real.sqrt_mul hM]
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      have e1 : √((M : ℝ) + 1) * √((M : ℝ) + 1) = (M : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
      nlinarith
    linarith

def exSet (N b Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => ∃ p ∈ Icc (Y + 1) (N * b + 1), p * p ∣ a * b + 1)

def rootSet (b m : ℕ) : Finset ℕ := (range b).filter (fun s => s * s * m % b = 1 % b)

lemma card_rootSet_le (b m : ℕ) : (rootSet b m).card ≤ rhoBound b := by
  by_cases hR : rootSet b m = ∅
  · rw [hR]; simp
  obtain ⟨s₀, hs₀⟩ := nonempty_iff_ne_empty.mpr hR
  simp only [rootSet, mem_filter, mem_range] at hs₀

  have hcop : Nat.Coprime (s₀ * s₀ * m) b := by
    have : s₀ * s₀ * m ≡ 1 [MOD b] := hs₀.2
    have h := Nat.ModEq.gcd_eq this
    rw [Nat.gcd_one_left] at h
    exact h
  have hm : Nat.Coprime m b := Nat.Coprime.coprime_mul_left hcop
  have hs : Nat.Coprime (s₀ * s₀) b := Nat.Coprime.coprime_mul_right hcop
  calc (rootSet b m).card ≤ sqrtCount b (s₀ * s₀) := by
        apply card_le_card
        intro x hx
        simp only [rootSet, mem_filter, mem_range] at hx
        simp only [mem_filter, mem_range]
        refine ⟨hx.1, ?_⟩

        have h1 : x * x * m ≡ s₀ * s₀ * m [MOD b] := by
          unfold Nat.ModEq; rw [hx.2, hs₀.2]
        have h2 : x * x ≡ s₀ * s₀ [MOD b] :=
          Nat.ModEq.cancel_right_of_coprime (Nat.coprime_comm.mp hm) h1
        exact h2
    _ ≤ rhoBound b := sqrtCount_le_rhoBound b _ hs

lemma card_mod_mem_le (X b : ℕ) (R : Finset ℕ) :
    ((Icc 1 X).filter (fun p => p % b ∈ R)).card ≤ R.card * (X / b + 1) := by
  calc ((Icc 1 X).filter (fun p => p % b ∈ R)).card
      ≤ (R.biUnion (fun r => (Icc 1 X).filter (fun p => p % b = r))).card := by
        apply card_le_card; intro p hp
        simp only [mem_filter] at hp
        simp only [mem_biUnion, mem_filter]
        exact ⟨p % b, hp.2, hp.1, rfl⟩
    _ ≤ ∑ r ∈ R, ((Icc 1 X).filter (fun p => p % b = r)).card := card_biUnion_le
    _ ≤ ∑ _r ∈ R, (X / b + 1) := sum_le_sum (fun r _ => card_mod_eq_le X b r)
    _ = R.card * (X / b + 1) := by simp

theorem card_exSet_le (N b Y : ℕ) (hb : 1 ≤ b) (hY : 1 ≤ Y) :
    ((exSet N b Y).card : ℝ) ≤ rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  classical
  set K := N * b + 1 with hK
  set M := K / ((Y + 1) * (Y + 1)) with hM

  let Pm : ℕ → Finset ℕ := fun m => (Icc 1 (Nat.sqrt (K / m))).filter (fun p => p % b ∈ rootSet b m)

  have hcard : (exSet N b Y).card ≤ ((Icc 1 M).sigma Pm).card := by
    calc (exSet N b Y).card
        ≤ (((Icc 1 M).sigma Pm).image (fun x => (x.2 * x.2 * x.1 - 1) / b)).card := by
          apply card_le_card
          intro a ha
          simp only [exSet, mem_filter, mem_Icc] at ha
          obtain ⟨⟨ha1, haN⟩, p, hpI, hdvd⟩ := ha
          have hp1 : Y + 1 ≤ p := hpI.1
          obtain ⟨m, hm⟩ := hdvd
          have hp0 : 0 < p * p := Nat.mul_pos (by omega) (by omega)
          have hab : a * b + 1 ≤ K := by rw [hK]; nlinarith
          have hm1 : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · rw [h0] at hm; simp at hm
            · exact h0
          rw [mem_image]
          refine ⟨⟨m, p⟩, ?_, ?_⟩
          · simp only [mem_sigma, mem_Icc, Pm, mem_filter]
            refine ⟨⟨hm1, ?_⟩, ⟨by omega, ?_⟩, ?_⟩
            · rw [hM, Nat.le_div_iff_mul_le (by positivity)]
              calc m * ((Y + 1) * (Y + 1)) ≤ m * (p * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hp1 hp1)
                _ = a * b + 1 := by rw [hm]; ring
                _ ≤ K := hab
            · apply Nat.le_sqrt.mpr
              rw [Nat.le_div_iff_mul_le (by omega)]
              rw [show p * p * m = a * b + 1 by rw [hm]]; exact hab
            · simp only [rootSet, mem_filter, mem_range]
              refine ⟨Nat.mod_lt _ (by omega), ?_⟩
              have h1 : p * p * m % b = 1 % b := by
                rw [← hm, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
              have h2 : p % b * (p % b) * m % b = p * p * m % b :=
                (((Nat.mod_modEq p b).mul (Nat.mod_modEq p b)).mul_right m)
              rw [h2, h1]
          · simp only
            rw [show p * p * m = a * b + 1 by rw [hm], Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]
      _ ≤ ((Icc 1 M).sigma Pm).card := card_image_le

  have hsig : ((Icc 1 M).sigma Pm).card ≤ ∑ m ∈ Icc 1 M, rhoBound b * (Nat.sqrt (K / m) / b + 1) := by
    rw [card_sigma]
    apply sum_le_sum; intro m _
    calc (Pm m).card ≤ (rootSet b m).card * (Nat.sqrt (K / m) / b + 1) := card_mod_mem_le _ _ _
      _ ≤ rhoBound b * (Nat.sqrt (K / m) / b + 1) := Nat.mul_le_mul_right _ (card_rootSet_le b m)

  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hKpos : (0 : ℝ) < K := by positivity
  have hterm : ∀ m ∈ Icc 1 M, ((Nat.sqrt (K / m) / b + 1 : ℕ) : ℝ) ≤ √(K : ℝ) / b * (1 / √(m : ℝ)) + 1 := by
    intro m hm
    simp only [mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    push_cast
    have h1 : ((Nat.sqrt (K / m) / b : ℕ) : ℝ) ≤ (Nat.sqrt (K / m) : ℝ) / b := Nat.cast_div_le
    have h2 : (Nat.sqrt (K / m) : ℝ) ≤ √((K / m : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h3 : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have h4 : √((K / m : ℕ) : ℝ) ≤ √((K : ℝ) / m) := Real.sqrt_le_sqrt h3
    have h5 : √((K : ℝ) / m) = √(K : ℝ) * (1 / √(m : ℝ)) := by
      rw [Real.sqrt_div' _ hm0.le, div_eq_mul_one_div]
    have hbpos : (0 : ℝ) < b := by linarith
    have : (Nat.sqrt (K / m) : ℝ) / b ≤ √(K : ℝ) / b * (1 / √(m : ℝ)) := by
      rw [div_mul_eq_mul_div, ← h5]
      exact div_le_div_of_nonneg_right (h2.trans h4) hbpos.le
    linarith
  have hsum := sum_inv_sqrt_le M
  have hMreal : (M : ℝ) ≤ (K : ℝ) / ((Y : ℝ) + 1) ^ 2 := by
    rw [hM]
    have := (Nat.cast_div_le (m := K) (n := (Y + 1) * (Y + 1)) : ((K / ((Y + 1) * (Y + 1)) : ℕ) : ℝ) ≤ _)
    push_cast at this; rw [sq]; exact this
  have hsqM : √(M : ℝ) ≤ √(K : ℝ) / ((Y : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Y : ℝ) + 1),
      ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc (M : ℝ) * ((Y : ℝ) + 1) ^ 2 ≤ (K : ℝ) / ((Y : ℝ) + 1) ^ 2 * ((Y : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hMreal (by positivity)
      _ = K := by field_simp
  calc ((exSet N b Y).card : ℝ) ≤ ((∑ m ∈ Icc 1 M, rhoBound b * (Nat.sqrt (K / m) / b + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard.trans hsig
    _ = rhoBound b * ∑ m ∈ Icc 1 M, ((Nat.sqrt (K / m) / b + 1 : ℕ) : ℝ) := by
        push_cast; rw [mul_sum]
    _ ≤ rhoBound b * ∑ m ∈ Icc 1 M, (√(K : ℝ) / b * (1 / √(m : ℝ)) + 1) := by
        apply mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = rhoBound b * (√(K : ℝ) / b * ∑ m ∈ Icc 1 M, (1 / √(m : ℝ)) + M) := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ rhoBound b * (√(K : ℝ) / b * (2 * √(M : ℝ)) + (K : ℝ) / ((Y : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) hMreal
    _ ≤ rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hKN : (K : ℝ) = N * b + 1 := by rw [hK]; push_cast; ring
        have hsK : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt hKpos.le
        have e1 : √(K : ℝ) / b * (2 * √(M : ℝ)) ≤ 2 * (N + 1) / Y := by
          calc √(K : ℝ) / b * (2 * √(M : ℝ)) ≤ √(K : ℝ) / b * (2 * (√(K : ℝ) / ((Y : ℝ) + 1))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
            _ = 2 * (√(K : ℝ) * √(K : ℝ)) / (b * ((Y : ℝ) + 1)) := by
                have : (b : ℝ) ≠ 0 := by linarith
                field_simp
            _ = 2 * K / (b * ((Y : ℝ) + 1)) := by rw [hsK]
            _ ≤ 2 * (N + 1) / Y := by
                rw [hKN, div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ N) (by linarith : (0:ℝ) ≤ b - 1)]
        have e2 : (K : ℝ) / ((Y : ℝ) + 1) ^ 2 ≤ (N * b + 1) / (Y : ℝ) ^ 2 := by
          rw [hKN]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
        linarith

end Erdos848


namespace Erdos848

open Finset

theorem pell_growth {m x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ ^ 2 + 1 = m * y₁ ^ 2)
    (h₂ : x₂ ^ 2 + 1 = m * y₂ ^ 2) (hlt : x₁ < x₂) : 3 * x₁ ≤ x₂ := by
  have H₁ : (x₁ : ℤ) ^ 2 + 1 = m * (y₁ : ℤ) ^ 2 := by exact_mod_cast h₁
  have H₂ : (x₂ : ℤ) ^ 2 + 1 = m * (y₂ : ℤ) ^ 2 := by exact_mod_cast h₂
  have hlt' : (x₁ : ℤ) < x₂ := by exact_mod_cast hlt
  have hx₁ : (0 : ℤ) ≤ x₁ := by positivity
  have hx₂ : (0 : ℤ) ≤ x₂ := by positivity
  have hy₁ : (0 : ℤ) ≤ y₁ := by positivity
  have hy₂ : (0 : ℤ) ≤ y₂ := by positivity
  have hm : (0 : ℤ) ≤ m := by positivity
  set a : ℤ := m * y₁ * y₂ - x₁ * x₂ with ha
  set c : ℤ := x₂ * y₁ - x₁ * y₂ with hc
  have hnorm : a ^ 2 - m * c ^ 2 = 1 := by
    rw [ha, hc]; linear_combination ((x₂ : ℤ) ^ 2 - m * (y₂ : ℤ) ^ 2) * H₁ - H₂
  have hx₂eq : (x₂ : ℤ) = a * x₁ + m * c * y₁ := by
    rw [ha, hc]; linear_combination (x₂ : ℤ) * H₁

  have hsq : ((x₁ : ℤ) * y₂) ^ 2 < ((x₂ : ℤ) * y₁) ^ 2 := by
    have hyy : (y₁ : ℤ) ^ 2 < (y₂ : ℤ) ^ 2 := by nlinarith
    have : ((x₂ : ℤ) * y₁) ^ 2 - ((x₁ : ℤ) * y₂) ^ 2 = (y₂ : ℤ) ^ 2 - (y₁ : ℤ) ^ 2 := by
      linear_combination (y₁ : ℤ) ^ 2 * H₂ - (y₂ : ℤ) ^ 2 * H₁
    linarith
  have hc1 : 1 ≤ c := by
    have : (x₁ : ℤ) * y₂ < x₂ * y₁ :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [hc]; linarith

  have ha1 : 1 ≤ a := by
    have hsq' : ((x₁ : ℤ) * x₂) ^ 2 < ((m : ℤ) * y₁ * y₂) ^ 2 := by
      have : ((m : ℤ) * y₁ * y₂) ^ 2 = ((x₁ : ℤ) ^ 2 + 1) * ((x₂ : ℤ) ^ 2 + 1) := by
        rw [H₁, H₂]; ring
      rw [this]; nlinarith [sq_nonneg ((x₁ : ℤ)), sq_nonneg ((x₂ : ℤ))]
    have : (x₁ : ℤ) * x₂ < m * y₁ * y₂ := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq'
    rw [ha]; linarith
  have hm1 : (1 : ℤ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp at h₁
    · exact_mod_cast hpos
  have ha2 : 2 ≤ a := by
    by_contra hlt2
    have : a = 1 := by omega
    rw [this] at hnorm
    nlinarith

  have hmy : (x₁ : ℤ) ≤ m * y₁ := by
    have : ((x₁ : ℤ)) ^ 2 < ((m : ℤ) * y₁) ^ 2 := by
      have : (m : ℤ) * y₁ ^ 2 ≤ (m * y₁) ^ 2 := by nlinarith
      nlinarith
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) this).le
  have : (3 : ℤ) * x₁ ≤ x₂ := by
    rw [hx₂eq]; nlinarith
  exact_mod_cast this

def pellSet (m N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ y ∈ range (x + 1), x ^ 2 + 1 = m * y ^ 2)

lemma mem_pellSet {m N x : ℕ} :
    x ∈ pellSet m N ↔ 1 ≤ x ∧ x ≤ N ∧ ∃ y, x ^ 2 + 1 = m * y ^ 2 := by
  unfold pellSet
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, y, -, hy⟩; exact ⟨h1, h2, y, hy⟩
  · rintro ⟨h1, h2, y, hy⟩
    refine ⟨⟨h1, h2⟩, y, ?_, hy⟩

    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; simp at hy
    · by_contra hge
      push Not at hge
      have : (x + 1) ^ 2 ≤ m * y ^ 2 := by
        calc (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hge 2
          _ ≤ m * y ^ 2 := Nat.le_mul_of_pos_left _ hm
      nlinarith

lemma card_pellSet_le (m : ℕ) : ∀ N, (pellSet m N).card ≤ Nat.log 3 N + 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 3 with hN | hN
    ·

      have : (pellSet m N).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_pellSet] at hx hx'
        obtain ⟨hx1, hxN, y, hy⟩ := hx
        obtain ⟨hx1', hxN', y', hy'⟩ := hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have := pell_growth hy hy' hlt; omega
        · have := pell_growth hy' hy hlt; omega
      omega
    ·
      have hsplit : pellSet m N ⊆ pellSet m (N / 3) ∪ (pellSet m N).filter (fun x => N / 3 < x) := by
        intro x hx
        by_cases h : N / 3 < x
        · exact mem_union_right _ (mem_filter.mpr ⟨hx, h⟩)
        · apply mem_union_left
          rw [mem_pellSet] at hx ⊢
          exact ⟨hx.1, by omega, hx.2.2⟩
      have hone : ((pellSet m N).filter (fun x => N / 3 < x)).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_filter, mem_pellSet] at hx hx'
        obtain ⟨⟨hx1, hxN, y, hy⟩, hxl⟩ := hx
        obtain ⟨⟨hx1', hxN', y', hy'⟩, hxl'⟩ := hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have := pell_growth hy hy' hlt; omega
        · have := pell_growth hy' hy hlt; omega
      have hih := ih (N / 3) (by omega)
      have hlog : Nat.log 3 (N / 3) + 1 = Nat.log 3 N := by
        rw [Nat.log_div_base]
        have : 1 ≤ Nat.log 3 N := Nat.log_pos (by norm_num) hN
        omega
      calc (pellSet m N).card ≤ (pellSet m (N / 3)).card + ((pellSet m N).filter (fun x => N / 3 < x)).card :=
            (card_le_card hsplit).trans (Finset.card_union_le _ _)
        _ ≤ Nat.log 3 (N / 3) + 1 + 1 := by omega
        _ = Nat.log 3 N + 1 := by omega

theorem pellTail_le (N Y : ℕ) :
    ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card ≤
      ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) := by
  set M := (N ^ 2 + 1) / (Y + 1) ^ 2
  calc ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card
      ≤ ((Icc 1 M).biUnion (fun m => pellSet m N)).card := by
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_Icc] at hn
        obtain ⟨⟨hn1, hnN⟩, p, ⟨hp1, -⟩, hd⟩ := hn
        obtain ⟨m, hm⟩ := hd
        have hp0 : 0 < p := by omega
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | h
          · subst h0; simp at hm
          · exact h
        have hmM : m ≤ M := by
          apply (Nat.le_div_iff_mul_le (by positivity)).mpr
          have h1 : (Y + 1) ^ 2 ≤ p * p := by nlinarith
          have h2 : n ^ 2 + 1 ≤ N ^ 2 + 1 := by nlinarith
          calc m * (Y + 1) ^ 2 ≤ m * (p * p) := Nat.mul_le_mul_left _ h1
            _ = n ^ 2 + 1 := by rw [hm]; ring
            _ ≤ N ^ 2 + 1 := h2
        simp only [mem_biUnion, mem_Icc]
        refine ⟨m, ⟨hm1, hmM⟩, mem_pellSet.mpr ⟨hn1, hnN, p, ?_⟩⟩
        rw [hm]; ring
    _ ≤ ∑ m ∈ Icc 1 M, (pellSet m N).card := card_biUnion_le
    _ ≤ ∑ _m ∈ Icc 1 M, (Nat.log 3 N + 1) := sum_le_sum (fun m _ => card_pellSet_le m N)
    _ = M * (Nat.log 3 N + 1) := by simp

end Erdos848


namespace Erdos848

open Finset

theorem pell_growth2 {m x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ ^ 2 + 1 = m * y₁ ^ 2)
    (h₂ : x₂ ^ 2 + 1 = m * y₂ ^ 2) (hlt : x₁ < x₂) : 4 * m * x₁ ^ 2 ≤ x₂ ^ 2 := by
  have H₁ : (x₁ : ℤ) ^ 2 + 1 = m * (y₁ : ℤ) ^ 2 := by exact_mod_cast h₁
  have H₂ : (x₂ : ℤ) ^ 2 + 1 = m * (y₂ : ℤ) ^ 2 := by exact_mod_cast h₂
  have hlt' : (x₁ : ℤ) < x₂ := by exact_mod_cast hlt
  have hx₁ : (0 : ℤ) ≤ x₁ := by positivity
  have hy₁ : (0 : ℤ) ≤ y₁ := by positivity
  have hy₂ : (0 : ℤ) ≤ y₂ := by positivity
  have hm : (0 : ℤ) ≤ m := by positivity
  set a : ℤ := m * y₁ * y₂ - x₁ * x₂ with ha
  set c : ℤ := x₂ * y₁ - x₁ * y₂ with hc
  have hnorm : a ^ 2 - m * c ^ 2 = 1 := by
    rw [ha, hc]; linear_combination ((x₂ : ℤ) ^ 2 - m * (y₂ : ℤ) ^ 2) * H₁ - H₂
  have hx₂eq : (x₂ : ℤ) = a * x₁ + m * c * y₁ := by
    rw [ha, hc]; linear_combination (x₂ : ℤ) * H₁

  have hm0 : (0 : ℤ) < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at h₁
    · exact_mod_cast h0
  have hyy : (y₁ : ℤ) ^ 2 < (y₂ : ℤ) ^ 2 := by
    have : (m : ℤ) * y₁ ^ 2 < m * y₂ ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hm0.le
  have hsq : ((x₁ : ℤ) * y₂) ^ 2 < ((x₂ : ℤ) * y₁) ^ 2 := by
    have : ((x₂ : ℤ) * y₁) ^ 2 - ((x₁ : ℤ) * y₂) ^ 2 = (y₂ : ℤ) ^ 2 - (y₁ : ℤ) ^ 2 := by
      linear_combination (y₁ : ℤ) ^ 2 * H₂ - (y₂ : ℤ) ^ 2 * H₁
    linarith
  have hc1 : 1 ≤ c := by
    have hpos : (x₁ : ℤ) * y₂ < x₂ * y₁ :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [hc]; linarith

  have ha2 : a ^ 2 = 1 + m * c ^ 2 := by linarith

  have hay : (x₁ : ℤ) ^ 2 < (a * y₁) ^ 2 := by
    have : (a * y₁) ^ 2 = (1 + m * c ^ 2) * y₁ ^ 2 := by rw [mul_pow, ha2]
    rw [this]
    have hc2 : (1 : ℤ) ≤ c ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 hm) (sq_nonneg (y₁ : ℤ))]
  have ha1 : 0 < a := by
    have hsq2 : ((m : ℤ) * y₁ * y₂) ^ 2 = ((x₁ : ℤ) ^ 2 + 1) * ((x₂ : ℤ) ^ 2 + 1) := by
      linear_combination (-(m : ℤ) * y₂ ^ 2) * H₁ - ((x₁ : ℤ) ^ 2 + 1) * H₂
    have hlt2 : ((x₁ : ℤ) * x₂) ^ 2 < ((m : ℤ) * y₁ * y₂) ^ 2 := by rw [hsq2]; nlinarith
    have h0 : (0 : ℤ) ≤ (m : ℤ) * y₁ * y₂ := by positivity
    have := lt_of_pow_lt_pow_left₀ 2 h0 hlt2
    rw [ha]; linarith
  have hx2 : (x₂ : ℤ) ^ 2 ≥ 4 * m * x₁ ^ 2 := by
    have hA : (0 : ℤ) ≤ a * x₁ := by positivity
    have hB : (0 : ℤ) ≤ m * c * y₁ := by positivity
    have hamgm : 4 * (a * x₁) * (m * c * y₁) ≤ (x₂ : ℤ) ^ 2 := by
      have hid : (a * x₁ + m * c * y₁) ^ 2 - 4 * (a * x₁) * (m * c * y₁) = (a * x₁ - m * c * y₁) ^ 2 := by
        ring
      rw [hx₂eq]; linarith [sq_nonneg (a * x₁ - m * c * y₁)]
    have hay0 : (0 : ℤ) ≤ a * y₁ := by positivity
    have hayx : (x₁ : ℤ) ≤ a * y₁ := (lt_of_pow_lt_pow_left₀ 2 hay0 hay).le
    have e1 : (x₁ : ℤ) * x₁ ≤ x₁ * (a * y₁) := mul_le_mul_of_nonneg_left hayx hx₁
    have e2 : (x₁ : ℤ) * (a * y₁) ≤ x₁ * (a * y₁) * c :=
      le_mul_of_one_le_right (mul_nonneg hx₁ hay0) hc1
    have e3 : 4 * (a * x₁) * (m * c * y₁) = 4 * m * (x₁ * (a * y₁) * c) := by ring
    have : 4 * (m : ℤ) * x₁ ^ 2 ≤ 4 * m * (x₁ * (a * y₁) * c) := by
      have h4m : (0 : ℤ) ≤ 4 * m := by positivity
      rw [sq]; exact mul_le_mul_of_nonneg_left (e1.trans e2) h4m
    linarith
  exact_mod_cast hx2

def chainCnt (G X₂ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, T => if T < X₂ then 0 else 1 + chainCnt G X₂ f (T / G)

theorem card_chain_le (G X₂ : ℕ) (hG : 2 ≤ G) (hX : 1 ≤ X₂) :
    ∀ f T (S : Finset ℕ), T < f → (∀ x ∈ S, X₂ ≤ x ^ 2 ∧ x ^ 2 ≤ T) →
      (∀ x ∈ S, ∀ x' ∈ S, x < x' → G * x ^ 2 ≤ x' ^ 2) → S.card ≤ chainCnt G X₂ f T := by
  intro f
  induction f with
  | zero => intro T S hT; omega
  | succ f ih =>
    intro T S hT hS hgr
    unfold chainCnt
    split_ifs with hTX
    ·
      apply Nat.le_of_eq
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx; have := hS x hx; omega
    ·
      set S' := S.filter (fun x => x ^ 2 ≤ T / G)
      have hone : (S.filter (fun x => T / G < x ^ 2)).card ≤ 1 := by
        rw [card_le_one]
        intro x hx x' hx'
        rw [mem_filter] at hx hx'
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have h1 := hgr x hx.1 x' hx'.1 hlt
          have h2 := (hS x' hx'.1).2
          have : T < G * x ^ 2 := by
            have := Nat.lt_mul_of_div_lt hx.2 (by omega : 0 < G); linarith
          omega
        · have h1 := hgr x' hx'.1 x hx.1 hlt
          have h2 := (hS x hx.1).2
          have : T < G * x' ^ 2 := by
            have := Nat.lt_mul_of_div_lt hx'.2 (by omega : 0 < G); linarith
          omega
      have hS'b : S'.card ≤ chainCnt G X₂ f (T / G) := by
        apply ih (T / G) S'
        · have : T / G < T ∨ T = 0 := by
            rcases Nat.eq_zero_or_pos T with h | h
            · right; exact h
            · left; exact Nat.div_lt_self h (by omega)
          omega
        · intro x hx; rw [mem_filter] at hx; exact ⟨(hS x hx.1).1, hx.2⟩
        · intro x hx x' hx' hlt
          exact hgr x (mem_filter.mp hx).1 x' (mem_filter.mp hx').1 hlt
      have hsplit := card_filter_add_card_filter_not (s := S) (fun x => x ^ 2 ≤ T / G)
      have hneg : (S.filter (fun x => ¬ x ^ 2 ≤ T / G)).card ≤ 1 := by
        have : S.filter (fun x => ¬ x ^ 2 ≤ T / G) = S.filter (fun x => T / G < x ^ 2) := by
          apply filter_congr; intro x _; omega
        rw [this]; exact hone
      calc S.card = S'.card + (S.filter (fun x => ¬ x ^ 2 ≤ T / G)).card := hsplit.symm
        _ ≤ chainCnt G X₂ f (T / G) + 1 := Nat.add_le_add hS'b hneg
        _ = 1 + chainCnt G X₂ f (T / G) := by ring

def admB (m : ℕ) : Bool :=
  (m % 8 == 1 || m % 8 == 2 || m % 8 == 5) && m % 3 != 0 && m % 7 != 0 && m % 11 != 0 &&
    m % 19 != 0 && m % 23 != 0

lemma sq_add_one_mod_k (n k : ℕ) (hk : 0 < k) : (n ^ 2 + 1) % k = ((n % k) ^ 2 + 1) % k := by
  rw [Nat.add_mod, Nat.pow_mod]; conv_rhs => rw [Nat.add_mod]

lemma sq_add_one_mod (n : ℕ) : (n ^ 2 + 1) % 4 ≠ 0 ∧ (n ^ 2 + 1) % 3 ≠ 0 ∧ (n ^ 2 + 1) % 7 ≠ 0 ∧
    (n ^ 2 + 1) % 11 ≠ 0 ∧ (n ^ 2 + 1) % 19 ≠ 0 ∧ (n ^ 2 + 1) % 23 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq_add_one_mod_k n 4 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 4 by norm_num); interval_cases (n % 4) <;> decide
  · rw [sq_add_one_mod_k n 3 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 3 by norm_num); interval_cases (n % 3) <;> decide
  · rw [sq_add_one_mod_k n 7 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 7 by norm_num); interval_cases (n % 7) <;> decide
  · rw [sq_add_one_mod_k n 11 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 11 by norm_num); interval_cases (n % 11) <;> decide
  · rw [sq_add_one_mod_k n 19 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 19 by norm_num); interval_cases (n % 19) <;> decide
  · rw [sq_add_one_mod_k n 23 (by norm_num)]
    have := Nat.mod_lt n (show 0 < 23 by norm_num); interval_cases (n % 23) <;> decide

lemma admB_of_eq {n p m : ℕ} (h : n ^ 2 + 1 = m * p ^ 2) : admB m = true := by
  obtain ⟨h4, h3, h7, h11, h19, h23⟩ := sq_add_one_mod n

  have hp : p % 2 = 1 := by
    by_contra hp
    have : p % 2 = 0 := by omega
    have h4' : 4 ∣ n ^ 2 + 1 := by
      rw [h]; obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
      exact ⟨m * k ^ 2, by rw [hk]; ring⟩
    exact h4 (Nat.mod_eq_zero_of_dvd h4')
  have hp8 : p ^ 2 % 8 = 1 := by
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h] <;> norm_num
  have hn8 : (n ^ 2 + 1) % 8 = 1 ∨ (n ^ 2 + 1) % 8 = 2 ∨ (n ^ 2 + 1) % 8 = 5 := by
    have hk : (n ^ 2 + 1) % 8 = ((n % 8) ^ 2 + 1) % 8 := by
      rw [Nat.add_mod, Nat.pow_mod]; conv_rhs => rw [Nat.add_mod]
    rw [hk]; have := Nat.mod_lt n (show 0 < 8 by norm_num)
    interval_cases (n % 8) <;> simp
  have hm8 : m % 8 = (n ^ 2 + 1) % 8 := by
    rw [h, Nat.mul_mod, hp8, mul_one, Nat.mod_mod]
  have hdiv : ∀ l, m % l = 0 → (n ^ 2 + 1) % l = 0 := by
    intro l hl; rw [h]; exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hl) _)
  unfold admB
  have e3 : m % 3 ≠ 0 := fun hz => h3 (hdiv 3 hz)
  have e7 : m % 7 ≠ 0 := fun hz => h7 (hdiv 7 hz)
  have e11 : m % 11 ≠ 0 := fun hz => h11 (hdiv 11 hz)
  have e19 : m % 19 ≠ 0 := fun hz => h19 (hdiv 19 hz)
  have e23 : m % 23 ≠ 0 := fun hz => h23 (hdiv 23 hz)
  rcases hn8 with h1 | h1 | h1 <;> rw [h1] at hm8 <;> simp [hm8, e3, e7, e11, e19, e23]


def R168 : Finset ℕ :=
  (range 168).filter (fun r => (r % 8 == 1 || r % 8 == 2 || r % 8 == 5) && r % 3 != 0 && r % 7 != 0)

lemma R168_card : R168.card = 36 := by decide

lemma mod168_mem_R168_of_admB {m : ℕ} (h : admB m = true) : m % 168 ∈ R168 := by
  unfold admB at h
  simp only [R168, mem_filter, mem_range, Nat.mod_lt _ (show 0 < 168 by norm_num), true_and]
  have h8 : (m % 168) % 8 = m % 8 := Nat.mod_mod_of_dvd m (by norm_num)
  have h3 : (m % 168) % 3 = m % 3 := Nat.mod_mod_of_dvd m (by norm_num)
  have h7 : (m % 168) % 7 = m % 7 := Nat.mod_mod_of_dvd m (by norm_num)
  rw [h8, h3, h7]
  simp only [Bool.and_eq_true] at h ⊢
  exact h.1.1.1

theorem pellTail_adm_le (N Y : ℕ) :
    ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card ≤
      ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) := by
  set M := (N ^ 2 + 1) / (Y + 1) ^ 2
  set A := (Icc 1 M).filter (fun m => m % 168 ∈ R168)
  have hsub : (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1) ⊆
      A.biUnion (fun m => pellSet m N) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, p, ⟨hp1, -⟩, ⟨m, hm⟩⟩ := hn
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · subst h0; simp at hm
      · exact h
    have hmM : m ≤ M := by
      apply (Nat.le_div_iff_mul_le (by positivity)).mpr
      have h1 : (Y + 1) ^ 2 ≤ p * p := by nlinarith
      have h2 : n ^ 2 + 1 ≤ N ^ 2 + 1 := by nlinarith
      calc m * (Y + 1) ^ 2 ≤ m * (p * p) := Nat.mul_le_mul_left _ h1
        _ = n ^ 2 + 1 := by rw [hm]; ring
        _ ≤ N ^ 2 + 1 := h2
    have heq : n ^ 2 + 1 = m * p ^ 2 := by rw [hm]; ring
    simp only [A, mem_biUnion, mem_filter, mem_Icc]
    exact ⟨m, ⟨⟨hm1, hmM⟩, mod168_mem_R168_of_admB (admB_of_eq heq)⟩,
      mem_pellSet.mpr ⟨hn1, hnN, p, heq⟩⟩
  have hA_M : A.card ≤ M :=
    (card_filter_le _ _).trans (by simp)
  have hA_168 : A.card ≤ 36 * (M / 168 + 1) := by
    rw [← R168_card]; exact card_mod_mem_le M 168 R168
  have hcardA : A.card ≤ ErdosComp.pellAdmM M := le_min hA_M hA_168
  calc ((Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)).card
      ≤ (A.biUnion (fun m => pellSet m N)).card := card_le_card hsub
    _ ≤ ∑ m ∈ A, (pellSet m N).card := card_biUnion_le
    _ ≤ ∑ _m ∈ A, (Nat.log 3 N + 1) := sum_le_sum (fun m _ => card_pellSet_le m N)
    _ = A.card * (Nat.log 3 N + 1) := by simp
    _ ≤ ErdosComp.pellAdmM M * (Nat.log 3 N + 1) := Nat.mul_le_mul_right _ hcardA

end Erdos848


namespace Erdos848

open Finset

def witRoots (b p : ℕ) : Finset ℕ := (range (p * p)).filter (fun r => p * p ∣ r * b + 1)

def sqRoots (p : ℕ) : Finset ℕ := (range (p * p)).filter (fun r => p * p ∣ r * r + 1)

lemma witRoots_sub (b p : ℕ) : witRoots b p ⊆ range (p * p) := filter_subset _ _
lemma sqRoots_sub (p : ℕ) : sqRoots p ⊆ range (p * p) := filter_subset _ _

lemma mod_mem_witRoots {b p : ℕ} (hp : 0 < p) (a : ℕ) :
    a % (p * p) ∈ witRoots b p ↔ p * p ∣ a * b + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hmod : (a % (p * p)) * b + 1 ≡ a * b + 1 [MOD p * p] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul_right b (Nat.mod_modEq a _))
  simp only [witRoots, mem_filter, mem_range, Nat.mod_lt a hpp, true_and]
  exact (Nat.ModEq.dvd_iff hmod dvd_rfl)

lemma mod_mem_sqRoots {p : ℕ} (hp : 0 < p) (a : ℕ) :
    a % (p * p) ∈ sqRoots p ↔ p * p ∣ a * a + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hmod : (a % (p * p)) * (a % (p * p)) + 1 ≡ a * a + 1 [MOD p * p] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul (Nat.mod_modEq a _) (Nat.mod_modEq a _))
  simp only [sqRoots, mem_filter, mem_range, Nat.mod_lt a hpp, true_and]
  exact (Nat.ModEq.dvd_iff hmod dvd_rfl)

lemma card_witRoots_le {b p : ℕ} (hp : p.Prime) : (witRoots b p).card ≤ 1 := by
  by_cases hpb : p ∣ b
  · have : witRoots b p = ∅ := by
      rw [witRoots, filter_eq_empty_iff]
      intro r _; exact not_sq_dvd_of_dvd hp hpb
    rw [this]; simp
  · obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp hpb
    rw [card_le_one]
    intro r hr r' hr'
    simp only [witRoots, mem_filter, mem_range] at hr hr'
    have h1 := (hc r).mp hr.2
    have h2 := (hc r').mp hr'.2
    rw [Nat.mod_eq_of_lt hr.1] at h1
    rw [Nat.mod_eq_of_lt hr'.1] at h2
    omega

lemma card_sqRoots_le {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : (sqRoots p).card ≤ 2 := by
  have hpp : 1 ≤ p * p := Nat.mul_pos hp.pos hp.pos
  have hpc : ¬ p ∣ p * p - 1 := by
    intro h
    have h1 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub (dvd_mul_right p p) h
    rw [Nat.sub_sub_self hpp] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have := sqrtCount_oddPrimePow_le (e := 2) hp hodd hpc
  unfold sqrtCount at this
  rw [pow_two] at this
  refine le_trans (card_le_card ?_) this
  intro r hr
  simp only [sqRoots, mem_filter, mem_range] at hr ⊢
  refine ⟨hr.1, ?_⟩
  rw [Nat.mod_eq_of_lt (Nat.sub_lt hpp one_pos)]
  obtain ⟨k, hk⟩ := hr.2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0] at hk; omega
    · exact h
  have : r * r = (p * p) * (k - 1) + (p * p - 1) := by
    have : p * p * k = p * p * (k - 1) + p * p := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hk1)]
    omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.sub_lt hpp one_pos)]

def IsU1 (p : ℕ) : Prop := p.Prime ∧ p % 4 = 1 ∧ 13 ≤ p

instance : DecidablePred IsU1 := fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma prime_mod_four_of_sq_dvd {p x : ℕ} (hp : p.Prime) (h : p * p ∣ x * x + 1) : p % 4 = 1 := by
  have hdvd : p ∣ x * x + 1 := dvd_trans (dvd_mul_right p p) h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
      rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
    omega
  have h3 : p % 4 ≠ 3 := by
    have := Fact.mk hp
    apply ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := (x : ZMod p))
    have : ((x * x + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    linear_combination this
  rcases Nat.Prime.eq_two_or_odd hp with h2 | h2
  · exact absurd h2 hp2
  · omega

lemma isU1_of_sq_dvd {p x : ℕ} (hp : p.Prime) (h : p * p ∣ x * x + 1)
    (hx : x % 25 ≠ 7 ∧ x % 25 ≠ 18) : IsU1 p := by
  have h4 := prime_mod_four_of_sq_dvd hp h
  refine ⟨hp, h4, ?_⟩
  by_contra hlt
  push Not at hlt
  have hp5 : p = 5 := by
    interval_cases p <;> first | rfl | omega | (exfalso; norm_num at hp)
  subst hp5
  have h25 : (x * x + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
  have hx25 : (x * x + 1) % 25 = ((x % 25) * (x % 25) + 1) % 25 := by
    rw [Nat.add_mod, Nat.mul_mod]; conv_rhs => rw [Nat.add_mod]
  have : x % 25 < 25 := Nat.mod_lt _ (by norm_num)
  rw [hx25] at h25
  interval_cases hr : x % 25 <;> omega

def smallP (z : ℕ) (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (range (z + 1)).filter (fun p => p.Prime ∧ Q p)

def midP (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] : Finset ℕ :=
  (Ioc z w).filter (fun p => p.Prime ∧ Q p)

lemma coprime_sq_of_primes {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : p ≠ p') :
    Nat.Coprime (p * p) (p' * p') := by
  have := (Nat.coprime_primes hp hp').mpr h
  have h2 : Nat.Coprime (p * p) p' := Nat.coprime_mul_iff_left.mpr ⟨this, this⟩
  exact Nat.Coprime.mul_right h2 h2

lemma card_single_le (N q t p : ℕ) (R : Finset ℕ) (hq : 0 < q) (ht : t < q) (hp : 0 < p)
    (hR : R ⊆ range (p * p)) (hcop : Nat.Coprime q p) :
    (((Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ R)).card : ℝ) ≤
      (R.card : ℝ) * ((N : ℝ) / q / (p * p)) + R.card := by
  have h := card_union_le N q t (fun p => p * p) (fun _ => R) {p} hq ht
    (by simp [hp.ne']) (fun p' hp' r hr => by
      rw [mem_singleton] at hp'; subst hp'; exact mem_range.mp (hR hr))
    (fun p' hp' => by rw [mem_singleton] at hp'; subst hp'; exact Nat.Coprime.mul_right hcop hcop)
    (fun p₁ h₁ p₂ h₂ hne => by rw [mem_singleton] at h₁ h₂; exact absurd (h₁.trans h₂.symm) hne)
  have hset : (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p' ∈ ({p} : Finset ℕ), a % (p' * p') ∈ R) =
      (Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ R) := by
    apply filter_congr; intro a _; simp
  rw [hset] at h
  simp only [prod_singleton, Nat.cast_mul] at h
  have : (N : ℝ) / q * (1 - (1 - (R.card : ℝ) / (p * p))) + (1 + (R.card : ℝ) - 1) =
      (R.card : ℝ) * ((N : ℝ) / q / (p * p)) + R.card := by ring
  linarith

theorem classSieve_le (N q t z w c : ℕ) (Rs : ℕ → Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hq : 0 < q) (ht : t < q) (hc : c ≤ 4)
    (hRs : ∀ p, Rs p ⊆ range (p * p)) (hRc : ∀ p, p.Prime → Q p → (Rs p).card ≤ c)
    (hcop : ∀ p, p.Prime → Q p → Nat.Coprime q p) :
    (((Icc 1 N).filter (fun a => a % q = t ∧
        ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) +
        (((1 + c : ℕ) : ℝ) ^ (smallP z Q).card - 1) +
        ∑ p ∈ midP z w Q, ((c : ℝ) * ((N : ℝ) / q / (p * p)) + c) := by
  classical
  set A := (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ smallP z Q, a % (p * p) ∈ Rs p)
  set B : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun a => a % q = t ∧ a % (p * p) ∈ Rs p)
  have hsub : (Icc 1 N).filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p) ⊆ A ∪ (midP z w Q).biUnion B := by
    intro a ha
    simp only [mem_filter] at ha
    obtain ⟨ha1, hat, p, hpw, hp, hQ, hR⟩ := ha
    by_cases hpz : p ≤ z
    · apply mem_union_left
      simp only [A, mem_filter, smallP, mem_range]
      exact ⟨ha1, hat, p, ⟨by omega, hp, hQ⟩, hR⟩
    · apply mem_union_right
      simp only [mem_biUnion, B, mem_filter, midP, mem_Ioc]
      exact ⟨p, ⟨⟨by omega, hpw⟩, hp, hQ⟩, ha1, hat, hR⟩
  have hcard : (((Icc 1 N).filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (A.card : ℝ) + ∑ p ∈ midP z w Q, ((B p).card : ℝ) := by
    have h1 := (card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := card_biUnion_le (s := midP z w Q) (t := B)
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)

  have hsmallP : ∀ p ∈ smallP z Q, p.Prime ∧ Q p := fun p hp => (mem_filter.mp hp).2
  have hA := card_union_le N q t (fun p => p * p) Rs (smallP z Q) hq ht
    (fun p hp => Nat.mul_pos (hsmallP p hp).1.pos (hsmallP p hp).1.pos)
    (fun p _ r hr => mem_range.mp (hRs p hr))
    (fun p hp => Nat.Coprime.mul_right (hcop p (hsmallP p hp).1 (hsmallP p hp).2)
      (hcop p (hsmallP p hp).1 (hsmallP p hp).2))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hsmallP p hp).1 (hsmallP p' hp').1 hne)
  have hNq : (0 : ℝ) ≤ (N : ℝ) / q := by positivity
  have hprod : ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p)) ≤
      ∏ p ∈ smallP z Q, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) := by
    apply prod_le_prod
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hsmallP p hp).1.two_le
      have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
      rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
      push_cast
      have : (0 : ℝ) < p * p := by have := (hsmallP p hp).1.pos; positivity
      gcongr
  have hprod2 : ∏ p ∈ smallP z Q, (1 + ((Rs p).card : ℝ)) ≤ ((1 + c : ℕ) : ℝ) ^ (smallP z Q).card := by
    rw [← prod_const]
    apply prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
      push_cast; linarith
  have hA' : (A.card : ℝ) ≤ (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) +
      (((1 + c : ℕ) : ℝ) ^ (smallP z Q).card - 1) := by
    have : (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
        (N : ℝ) / q * (1 - ∏ p ∈ smallP z Q, (1 - (c : ℝ) / (p * p))) :=
      mul_le_mul_of_nonneg_left (by linarith) hNq
    linarith

  have hB : ∀ p ∈ midP z w Q, ((B p).card : ℝ) ≤ (c : ℝ) * ((N : ℝ) / q / (p * p)) + c := by
    intro p hp
    have hpQ := (mem_filter.mp hp).2
    have h := card_single_le N q t p (Rs p) hq ht hpQ.1.pos (hRs p) (hcop p hpQ.1 hpQ.2)
    have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hpQ.1 hpQ.2
    have : (0 : ℝ) ≤ (N : ℝ) / q / (p * p) := by positivity
    calc ((B p).card : ℝ) ≤ ((Rs p).card : ℝ) * ((N : ℝ) / q / (p * p)) + (Rs p).card := h
      _ ≤ _ := by gcongr
  have := sum_le_sum hB
  linarith

def midSet (N b pc Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => ∃ p ≤ Y, p.Prime ∧ pc < p ∧ a % (p * p) ∈ witRoots b p)

def resPart (N b q t pc : ℕ) (excl : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ≤ pc, p.Prime ∧ p ∉ excl ∧ a % (p * p) ∈ witRoots b p)

lemma witness_cover (N b q pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop) [DecidablePred Pa]
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (Icc 1 N).filter (fun a => Pa a ∧ ¬ Squarefree (a * b + 1)) ⊆
      (Tset.biUnion (fun t => resPart N b q t pc excl) ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro a ha
  simp only [mem_filter, mem_Icc] at ha
  obtain ⟨⟨ha1, haN⟩, hPa, hsq⟩ := ha
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hpe : p ∉ excl := fun h => hexcl a hPa p h hd
  have hR : a % (p * p) ∈ witRoots b p := (mod_mem_witRoots hp.pos a).mpr hd
  by_cases hpc : p ≤ pc
  · apply mem_union_left; apply mem_union_left
    simp only [mem_biUnion, resPart, mem_filter, mem_Icc]
    exact ⟨a % q, hT a hPa, ⟨ha1, haN⟩, rfl, p, hpc, hp, hpe, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [midSet, mem_filter, mem_Icc]
    exact ⟨⟨ha1, haN⟩, p, hpY, hp, by omega, hR⟩
  · apply mem_union_right
    simp only [exSet, mem_filter, mem_Icc]
    have h1 : p ≤ a * b + 1 :=
      le_trans (Nat.le_mul_self p) (Nat.le_of_dvd (Nat.succ_pos _) hd)
    have h2 : a * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b haN) 1
    exact ⟨⟨ha1, haN⟩, p, ⟨by omega, h1.trans h2⟩, hd⟩

lemma card_midSet_le (N b pc Y : ℕ) :
    ((midSet N b pc Y).card : ℝ) ≤
      ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) := by
  have h := classSieve_le N 1 0 pc Y 1 (witRoots b) (fun p => pc < p) one_pos one_pos
    (by norm_num) (witRoots_sub b) (fun p hp _ => card_witRoots_le hp)
    (fun p _ _ => Nat.coprime_one_left p)
  have hsmall : smallP pc (fun p => pc < p) = ∅ := by
    rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
  rw [hsmall] at h
  simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_one,
    Nat.mod_one, true_and, div_one, one_mul] at h
  have hset : midSet N b pc Y = (Icc 1 N).filter
      (fun a => ∃ p ≤ Y, p.Prime ∧ pc < p ∧ a % (p * p) ∈ witRoots b p) := rfl
  rw [hset]
  simpa using h

lemma card_resPart_le (N b q t z pc : ℕ) (excl : Finset ℕ) (hq : 0 < q) (ht : t < q)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p) :
    ((resPart N b q t pc excl).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1) := by
  have h := classSieve_le N q t z pc 1 (witRoots b) (· ∉ excl) hq ht (by norm_num)
    (witRoots_sub b) (fun p hp _ => card_witRoots_le hp) hcop
  simp only [Nat.cast_one, one_mul, Nat.reduceAdd, Nat.cast_ofNat] at h
  exact h

theorem badCount_le (N b q z pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop) [DecidablePred Pa]
    (hb : 1 ≤ b) (hY : 1 ≤ Y) (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q)
    (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p)
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (badCount N Pa b : ℝ) ≤
      Tset.card * ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1)) +
      ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) +
      rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  have hc := card_le_card (witness_cover N b q pc Y Tset excl Pa hT hexcl)
  have h1 := Finset.card_union_le (Tset.biUnion (fun t => resPart N b q t pc excl) ∪ midSet N b pc Y)
    (exSet N b Y)
  have h1' := Finset.card_union_le (Tset.biUnion (fun t => resPart N b q t pc excl)) (midSet N b pc Y)
  have h2 := card_biUnion_le (s := Tset) (t := fun t => resPart N b q t pc excl)
  have hcN : badCount N Pa b ≤ ∑ t ∈ Tset, (resPart N b q t pc excl).card +
      (midSet N b pc Y).card + (exSet N b Y).card := by
    unfold badCount; omega
  have hcR : (badCount N Pa b : ℝ) ≤ ∑ t ∈ Tset, ((resPart N b q t pc excl).card : ℝ) +
      ((midSet N b pc Y).card : ℝ) + ((exSet N b Y).card : ℝ) := by exact_mod_cast hcN
  have hres : ∑ t ∈ Tset, ((resPart N b q t pc excl).card : ℝ) ≤ ∑ _t ∈ Tset,
      ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
        ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
        ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1)) :=
    sum_le_sum (fun t ht => card_resPart_le N b q t z pc excl hq (hTq t ht) hcop)
  rw [sum_const, nsmul_eq_mul] at hres
  have := card_midSet_le N b pc Y
  have := card_exSet_le N b Y hb hY
  linarith

lemma isU1_odd {p : ℕ} (h : IsU1 p) : p ≠ 2 := by have := h.2.1; omega

def vResPart (N q t pB : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => x % q = t ∧ ∃ p ≤ pB, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

def vMidSet (N pB Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ Y, p.Prime ∧ (IsU1 p ∧ pB < p) ∧ x % (p * p) ∈ sqRoots p)

def vPellSet (N Y : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∃ p ∈ Icc (Y + 1) (N + 1), p * p ∣ n ^ 2 + 1)

lemma v_cover (N q pB Y : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (Icc 1 N).filter (fun x => Px x ∧ ¬ Squarefree (x * x + 1)) ⊆
      (Tset.biUnion (fun t => vResPart N q t pB) ∪ vMidSet N pB Y) ∪ vPellSet N Y := by
  intro x hx
  simp only [mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hPx, hsq⟩ := hx
  obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd hsq
  have hU := isU1_of_sq_dvd hp hd (hstar x hPx)
  have hR : x % (p * p) ∈ sqRoots p := (mod_mem_sqRoots hp.pos x).mpr hd
  by_cases hpB : p ≤ pB
  · apply mem_union_left; apply mem_union_left
    simp only [mem_biUnion, vResPart, mem_filter, mem_Icc]
    exact ⟨x % q, hT x hPx, ⟨hx1, hxN⟩, rfl, p, hpB, hp, hU, hR⟩
  by_cases hpY : p ≤ Y
  · apply mem_union_left; apply mem_union_right
    simp only [vMidSet, mem_filter, mem_Icc]
    exact ⟨⟨hx1, hxN⟩, p, hpY, hp, ⟨hU, by omega⟩, hR⟩
  · apply mem_union_right
    simp only [vPellSet, mem_filter, mem_Icc]
    have h1 : p * p ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    have h2 : x * x + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hxN hxN) 1
    have h3 : p ≤ N + 1 := by
      by_contra hc; push Not at hc
      have : (N + 2) * (N + 2) ≤ p * p := Nat.mul_le_mul hc hc
      nlinarith
    refine ⟨⟨hx1, hxN⟩, p, ⟨by omega, h3⟩, ?_⟩
    rw [sq]; exact hd

theorem vCount_le (N q zB pB Y : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hcop : ∀ p, p.Prime → IsU1 p → Nat.Coprime q p)
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (vCount N Px : ℝ) ≤
      Tset.card * ((N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
        ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2)) +
      ∑ p ∈ midP pB Y (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
      ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  have hc := card_le_card (v_cover N q pB Y Tset Px hT hstar)
  have h1 := Finset.card_union_le (Tset.biUnion (fun t => vResPart N q t pB) ∪ vMidSet N pB Y)
    (vPellSet N Y)
  have h1' := Finset.card_union_le (Tset.biUnion (fun t => vResPart N q t pB)) (vMidSet N pB Y)
  have h2 := card_biUnion_le (s := Tset) (t := fun t => vResPart N q t pB)
  have hcN : vCount N Px ≤ ∑ t ∈ Tset, (vResPart N q t pB).card +
      (vMidSet N pB Y).card + (vPellSet N Y).card := by
    unfold vCount; omega
  have hcR : (vCount N Px : ℝ) ≤ ∑ t ∈ Tset, ((vResPart N q t pB).card : ℝ) +
      ((vMidSet N pB Y).card : ℝ) + ((vPellSet N Y).card : ℝ) := by exact_mod_cast hcN
  have hres : ∀ t ∈ Tset, ((vResPart N q t pB).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
        ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2) := by
    intro t ht
    have h := classSieve_le N q t zB pB 2 (fun p => sqRoots p) IsU1 hq (hTq t ht) (by norm_num)
      sqRoots_sub (fun p hp hU => card_sqRoots_le hp (isU1_odd hU)) hcop
    simp only [Nat.cast_ofNat, Nat.reduceAdd] at h
    exact h
  have hres' := sum_le_sum hres
  rw [sum_const, nsmul_eq_mul] at hres'
  have hmid : ((vMidSet N pB Y).card : ℝ) ≤
      ∑ p ∈ midP pB Y (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) := by
    have h := classSieve_le N 1 0 pB Y 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ pB < p)
      one_pos one_pos (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1)) (fun p _ _ => Nat.coprime_one_left p)
    have hsmall : smallP pB (fun p => IsU1 p ∧ pB < p) = ∅ := by
      rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
    rw [hsmall] at h
    simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat,
      Nat.mod_one, true_and] at h
    simpa [vMidSet] using h
  have hpell : ((vPellSet N Y).card : ℝ) ≤
      ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast pellTail_adm_le N Y
  linarith

end Erdos848


namespace Erdos848

open Finset

lemma crt_class {m n a c : ℕ} (h : Nat.Coprime m n) (ha : a < m) (hc : c < n) :
    ∃ t < m * n, ∀ x, x % (m * n) = t ↔ x % m = a ∧ x % n = c := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h a c
  have hmn : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  refine ⟨k % (m * n), Nat.mod_lt _ hmn, fun x => ?_⟩
  have e : x % (m * n) = k % (m * n) ↔ x ≡ k [MOD m] ∧ x ≡ k [MOD n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul h).symm
  rw [e]
  unfold Nat.ModEq at hk1 hk2 ⊢
  rw [hk1, hk2, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]

lemma card_three_le {A X B C : Finset ℕ} (hX : X ⊆ A) (hB : B ⊆ A) (hC : C ⊆ A)
    (hXB : Disjoint X B) (hXC : Disjoint X C) (hBC : Disjoint B C) :
    X.card + B.card + C.card ≤ A.card := by
  rw [← card_union_of_disjoint hXB, ← card_union_of_disjoint (disjoint_union_left.mpr ⟨hXC, hBC⟩)]
  exact card_le_card (union_subset (union_subset hX hB) hC)

lemma sq_dvd_of_roots {p b c : ℕ} (h1 : p * p ∣ c * b + 1) (h2 : p * p ∣ c * c + 1) :
    p * p ∣ b * b + 1 := by
  have e1 := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr h1
  have e2 := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr h2
  apply (ZMod.natCast_eq_zero_iff _ (p * p)).mp
  push_cast at e1 e2 ⊢
  linear_combination ((b : ZMod (p * p)) * b) * e2 - ((c : ZMod (p * p)) * b - 1) * e1

lemma ie_mono (P : Finset ℕ) (Rs : ℕ → Finset ℕ) (c : ℕ) (hc : c ≤ 4)
    (hP : ∀ p ∈ P, p.Prime) (hRc : ∀ p ∈ P, (Rs p).card ≤ c) :
    (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
        1 - ∏ p ∈ P, (1 - (c : ℝ) / (p * p)) ∧
      ∏ p ∈ P, (1 + ((Rs p).card : ℝ)) ≤ ((1 + c : ℕ) : ℝ) ^ P.card := by
  constructor
  · have : ∏ p ∈ P, (1 - (c : ℝ) / (p * p)) ≤
        ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) := by
      apply prod_le_prod
      · intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
        have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
        rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
      · intro p hp
        have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hp
        push_cast
        have : (0 : ℝ) < p * p := by have := (hP p hp).pos; positivity
        gcongr
    linarith
  · rw [← prod_const]
    apply prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hp
      push_cast; linarith

def xSet (N b p₂ z₁ : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => IsStar x ∧ x % (p₂ * p₂) ∈ witRoots b p₂ ∧
    ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p)

noncomputable def nonB (N p₂ z₁ : ℕ) : ℝ :=
  23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) *
      (1 - ∏ p ∈ (smallP z₁ IsU1).erase p₂, (1 - 2 / ((p : ℝ) * p))) +
    3 * ((3 : ℝ) ^ ((smallP z₁ IsU1).erase p₂).card - 1)

noncomputable def wholeB (N p₂ : ℕ) : ℝ := 23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) + 3

lemma prod_one_sub_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, (1 - 2 / ((p : ℝ) * p)) ≤ 1 := by
  apply prod_le_one
  · intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  · intro p _; have : 0 ≤ 2 / ((p : ℝ) * p) := by positivity
    linarith

lemma nonB_nonneg (N p₂ z₁ : ℕ) : 0 ≤ nonB N p₂ z₁ := by
  unfold nonB
  have h1 := prod_one_sub_le_one ((smallP z₁ IsU1).erase p₂)
    (fun p hp => (mem_filter.mp (mem_of_mem_erase hp)).2.1)
  have h2 : (1 : ℝ) ≤ 3 ^ ((smallP z₁ IsU1).erase p₂).card := one_le_pow₀ (by norm_num)
  have : 0 ≤ (N : ℝ) / ((p₂ : ℝ) * p₂) := by positivity
  have : 0 ≤ 23 / 25 * ((N : ℝ) / ((p₂ : ℝ) * p₂)) * (1 - ∏ p ∈ (smallP z₁ IsU1).erase p₂,
      (1 - 2 / ((p : ℝ) * p))) := by
    apply mul_nonneg (by positivity); linarith
  linarith

lemma wholeB_nonneg (N p₂ : ℕ) : 0 ≤ wholeB N p₂ := by unfold wholeB; positivity

lemma coprime_25_sq {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 (p * p) :=
  coprime_sq_of_primes Nat.prime_five hp (Ne.symm h5)

theorem card_xSet_le (N b p₂ z₁ : ℕ) (hp₂ : p₂.Prime) (h5 : p₂ ≠ 5) :
    ((xSet N b p₂ z₁).card : ℝ) ≤
      if p₂ * p₂ ∣ b * b + 1 then wholeB N p₂ else nonB N p₂ z₁ := by
  classical
  by_cases hW : witRoots b p₂ = ∅
  · have : xSet N b p₂ z₁ = ∅ := by
      rw [xSet, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]
    split_ifs
    · exact wholeB_nonneg N p₂
    · exact nonB_nonneg N p₂ z₁
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hpp : 0 < p₂ * p₂ := Nat.mul_pos hp₂.pos hp₂.pos
  have hc_lt : c < p₂ * p₂ := mem_range.mp (witRoots_sub b p₂ hcW)
  have hcdvd : p₂ * p₂ ∣ c * b + 1 := (mem_filter.mp hcW).2
  have huniq : ∀ x, x % (p₂ * p₂) ∈ witRoots b p₂ → x % (p₂ * p₂) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le hp₂) _ hx _ hcW
  have hcop25 := coprime_25_sq hp₂ h5
  obtain ⟨t7, ht7, H7⟩ := crt_class hcop25 (a := 7) (by norm_num) hc_lt
  obtain ⟨t18, ht18, H18⟩ := crt_class hcop25 (a := 18) (by norm_num) hc_lt
  have hQ : ((25 * (p₂ * p₂) : ℕ) : ℝ) = 25 * ((p₂ : ℝ) * p₂) := by push_cast; ring
  have hQ' : ((p₂ * p₂ : ℕ) : ℝ) = (p₂ : ℝ) * p₂ := by push_cast; ring
  have hp2R : (0 : ℝ) < (p₂ : ℝ) * p₂ := by have := hp₂.pos; positivity
  have hNdiv : (N : ℝ) / (25 * ((p₂ : ℝ) * p₂)) = (N : ℝ) / ((p₂ : ℝ) * p₂) / 25 := by
    rw [div_div, mul_comm]
  split_ifs with hsq
  ·
    set A := (Icc 1 N).filter (fun x => x % (p₂ * p₂) = c)
    set B7 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t7)
    set B18 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t18)
    have h3 := card_three_le (A := A) (X := xSet N b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSet, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, huniq x hx.2.2.1⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2).2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2).2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2).1; have := ((H18 x).mp hb.2).1; omega)
    have hA := card_mod_eq_real N (p₂ * p₂) c hpp hc_lt
    have hB7 := card_mod_eq_real N (25 * (p₂ * p₂)) t7 (by omega) ht7
    have hB18 := card_mod_eq_real N (25 * (p₂ * p₂)) t18 (by omega) ht18
    rw [hQ'] at hA; rw [hQ, hNdiv] at hB7 hB18
    rw [abs_le] at hA hB7 hB18
    have h3R : ((xSet N b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    unfold wholeB
    linarith [hA.2, hB7.1, hB18.1]
  ·
    set U' := (smallP z₁ IsU1).erase p₂
    have hU' : ∀ p ∈ U', p.Prime ∧ IsU1 p ∧ p ≠ p₂ := by
      intro p hp
      have := mem_erase.mp hp
      exact ⟨(mem_filter.mp this.2).2.1, (mem_filter.mp this.2).2.2, this.1⟩
    set A := (Icc 1 N).filter (fun x => x % (p₂ * p₂) = c ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    set B7 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t7 ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    set B18 := (Icc 1 N).filter (fun x => x % (25 * (p₂ * p₂)) = t18 ∧
      ∃ p ∈ U', x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)
    have h3 := card_three_le (A := A) (X := xSet N b p₂ z₁) (B := B7) (C := B18)
      (fun x hx => by
        simp only [xSet, mem_filter] at hx; simp only [A, mem_filter]
        obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
        have hxc := huniq x hxW
        refine ⟨hx1, hxc, p, ?_, hpR⟩
        have hne : p ≠ p₂ := by
          rintro rfl
          rw [hxc] at hpR
          exact hsq (sq_dvd_of_roots hcdvd (mem_filter.mp hpR).2)
        exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩⟩)
      (fun x hx => by
        simp only [B7, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H7 x).mp hx.2.1).2, hx.2.2⟩)
      (fun x hx => by
        simp only [B18, mem_filter] at hx; simp only [A, mem_filter]
        exact ⟨hx.1, ((H18 x).mp hx.2.1).2, hx.2.2⟩)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B7, mem_filter] at hx hb
        exact hx.2.1.1 ((H7 x).mp hb.2.1).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [xSet, B18, mem_filter] at hx hb
        exact hx.2.1.2 ((H18 x).mp hb.2.1).1)
      (disjoint_left.mpr fun x hx hb => by
        simp only [B7, B18, mem_filter] at hx hb
        have := ((H7 x).mp hx.2.1).1; have := ((H18 x).mp hb.2.1).1; omega)
    have hm : ∀ p ∈ U', 0 < (fun p => p * p) p := fun p hp =>
      Nat.mul_pos (hU' p hp).1.pos (hU' p hp).1.pos
    have hR : ∀ p ∈ U', ∀ r ∈ (fun p => sqRoots p) p, r < (fun p => p * p) p :=
      fun p _ r hr => mem_range.mp (sqRoots_sub p hr)
    have hcp : ∀ p ∈ U', ∀ p' ∈ U', p ≠ p' →
        Nat.Coprime ((fun p => p * p) p) ((fun p => p * p) p') := fun p hp p' hp' hne =>
      coprime_sq_of_primes (hU' p hp).1 (hU' p' hp').1 hne
    have hcq1 : ∀ p ∈ U', Nat.Coprime (p₂ * p₂) ((fun p => p * p) p) := fun p hp =>
      coprime_sq_of_primes hp₂ (hU' p hp).1 (Ne.symm (hU' p hp).2.2)
    have hcq2 : ∀ p ∈ U', Nat.Coprime (25 * (p₂ * p₂)) ((fun p => p * p) p) := fun p hp =>
      Nat.coprime_mul_iff_left.mpr ⟨coprime_25_sq (hU' p hp).1
        (by have := (hU' p hp).2.1.2.2; omega), hcq1 p hp⟩
    have hA := card_union_le N (p₂ * p₂) c (fun p => p * p) (fun p => sqRoots p) U' hpp hc_lt
      hm hR hcq1 hcp
    have hB7 := card_union_ge N (25 * (p₂ * p₂)) t7 (fun p => p * p) (fun p => sqRoots p) U'
      (by omega) ht7 hm hR hcq2 hcp
    have hB18 := card_union_ge N (25 * (p₂ * p₂)) t18 (fun p => p * p) (fun p => sqRoots p) U'
      (by omega) ht18 hm hR hcq2 hcp
    rw [hQ'] at hA; rw [hQ, hNdiv] at hB7 hB18
    have h3R : ((xSet N b p₂ z₁).card : ℝ) + B7.card + B18.card ≤ A.card := by exact_mod_cast h3
    obtain ⟨hM, hE⟩ := ie_mono U' (fun p => sqRoots p) 2 (by norm_num) (fun p hp => (hU' p hp).1)
      (fun p hp => card_sqRoots_le (hU' p hp).1 (isU1_odd (hU' p hp).2.1))
    set M := 1 - ∏ p ∈ U', (1 - (((fun p => sqRoots p) p).card : ℝ) / (((fun p => p * p) p : ℕ) : ℝ))
    set E := ∏ p ∈ U', (1 + (((fun p => sqRoots p) p).card : ℝ))
    set X := (N : ℝ) / ((p₂ : ℝ) * p₂)
    have hX : 0 ≤ X := by positivity
    have hmain : ((xSet N b p₂ z₁).card : ℝ) ≤ 23 / 25 * X * M + 3 * (E - 1) := by
      linarith [hA, hB7, hB18]
    unfold nonB
    simp only [Nat.cast_ofNat, Nat.reduceAdd] at hM hE
    have : 23 / 25 * X * M ≤ 23 / 25 * X * (1 - ∏ p ∈ U', (1 - 2 / ((p : ℝ) * p))) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    linarith

theorem card_xSet5_le (N b z₁ : ℕ) :
    ((xSet N b 5 z₁).card : ℝ) ≤
      (N : ℝ) / 25 * (1 - ∏ p ∈ smallP z₁ IsU1, (1 - 2 / ((p : ℝ) * p))) +
        ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1) := by
  classical
  set U := smallP z₁ IsU1
  have hU : ∀ p ∈ U, p.Prime ∧ IsU1 p := fun p hp => (mem_filter.mp hp).2
  have hRHS : 0 ≤ (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) +
      ((3 : ℝ) ^ U.card - 1) := by
    have h1 := prod_one_sub_le_one U (fun p hp => (hU p hp).1)
    have h2 : (1 : ℝ) ≤ 3 ^ U.card := one_le_pow₀ (by norm_num)
    have : 0 ≤ (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  by_cases hW : witRoots b 5 = ∅
  · have : xSet N b 5 z₁ = ∅ := by
      rw [xSet, filter_eq_empty_iff]; intro x _ h; rw [hW] at h; simp at h
    rw [this, card_empty, Nat.cast_zero]; exact hRHS
  obtain ⟨c, hcW⟩ := nonempty_iff_ne_empty.mpr hW
  have hc_lt : c < 5 * 5 := mem_range.mp (witRoots_sub b 5 hcW)
  have huniq : ∀ x, x % (5 * 5) ∈ witRoots b 5 → x % (5 * 5) = c := fun x hx =>
    card_le_one.mp (card_witRoots_le Nat.prime_five) _ hx _ hcW
  have hsub : xSet N b 5 z₁ ⊆ (Icc 1 N).filter (fun x => x % 25 = c ∧
      ∃ p ∈ U, x % (fun p => p * p) p ∈ (fun p => sqRoots p) p) := by
    intro x hx
    simp only [xSet, mem_filter] at hx
    obtain ⟨hx1, -, hxW, p, hpz, hp, hpU, hpR⟩ := hx
    exact mem_filter.mpr ⟨hx1, huniq x hxW, p,
      mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpU⟩, hpR⟩
  have hA := card_union_le N 25 c (fun p => p * p) (fun p => sqRoots p) U (by norm_num) hc_lt
    (fun p hp => Nat.mul_pos (hU p hp).1.pos (hU p hp).1.pos)
    (fun p _ r hr => mem_range.mp (sqRoots_sub p hr))
    (fun p hp => coprime_25_sq (hU p hp).1 (by have := (hU p hp).2.2.2; omega))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hU p hp).1 (hU p' hp').1 hne)
  obtain ⟨hM, hE⟩ := ie_mono U (fun p => sqRoots p) 2 (by norm_num) (fun p hp => (hU p hp).1)
    (fun p hp => card_sqRoots_le (hU p hp).1 (isU1_odd (hU p hp).2))
  simp only [Nat.cast_ofNat, Nat.reduceAdd] at hM hE hA
  have hcard : ((xSet N b 5 z₁).card : ℝ) ≤ ((Icc 1 N).filter (fun x => x % 25 = c ∧
      ∃ p ∈ U, x % (fun p => p * p) p ∈ (fun p => sqRoots p) p)).card := by
    exact_mod_cast card_le_card hsub
  have : (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - ((sqRoots p).card : ℝ) / ((p * p : ℕ) : ℝ))) ≤
      (N : ℝ) / 25 * (1 - ∏ p ∈ U, (1 - 2 / ((p : ℝ) * p))) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  linarith

def T25 : Finset ℕ := (range 25).filter (fun t => t ≠ 7 ∧ t ≠ 18)

def lcRes (N t z₁ pB : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => x % 25 = t ∧
    ∃ p ≤ pB, p.Prime ∧ (IsU1 p ∧ z₁ < p) ∧ x % (p * p) ∈ sqRoots p)

def lcMid (N b z₂ pc : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => ∃ p ≤ pc, p.Prime ∧ z₂ < p ∧ x % (p * p) ∈ witRoots b p)

def lemCSet (N b : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => IsStar x ∧ ¬ Squarefree (x * x + 1) ∧ ¬ Squarefree (x * b + 1))

def lemCPart (N b z₁ z₂ pB Y' pc : ℕ) : Finset ℕ :=
  ((T25.biUnion (fun t => lcRes N t z₁ pB) ∪ vMidSet N pB Y') ∪ vPellSet N Y') ∪
    ((smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSet N b p₂ z₁) ∪ lcMid N b z₂ pc)

lemma lemC_cover (N b z₁ z₂ pB Y' pc Y : ℕ) (hbe : b % 2 = 0) :
    lemCSet N b ⊆ (lemCPart N b z₁ z₂ pB Y' pc ∪ midSet N b pc Y) ∪ exSet N b Y := by
  intro x hx
  simp only [lemCSet, mem_filter, mem_Icc] at hx
  obtain ⟨⟨hx1, hxN⟩, hxs, hsq1, hsq2⟩ := hx
  obtain ⟨p₁, hp₁, hd₁⟩ := exists_prime_sq_dvd hsq1
  have hU₁ := isU1_of_sq_dvd hp₁ hd₁ hxs
  have hR₁ : x % (p₁ * p₁) ∈ sqRoots p₁ := (mod_mem_sqRoots hp₁.pos x).mpr hd₁
  by_cases hsmall : ∃ p ≤ z₁, p.Prime ∧ IsU1 p ∧ x % (p * p) ∈ sqRoots p
  ·
    obtain ⟨p₂, hp₂, hd₂⟩ := exists_prime_sq_dvd hsq2
    have hR₂ : x % (p₂ * p₂) ∈ witRoots b p₂ := (mod_mem_witRoots hp₂.pos x).mpr hd₂
    have hp₂2 : p₂ ≠ 2 := by
      rintro rfl
      have : 2 ∣ x * b + 1 := dvd_trans ⟨2, rfl⟩ hd₂
      have : 2 ∣ x * b := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hbe) x
      omega
    by_cases hz₂ : p₂ ≤ z₂
    · apply mem_union_left; apply mem_union_left; apply mem_union_right; apply mem_union_left
      simp only [mem_biUnion, smallP, mem_filter, mem_range, xSet, mem_Icc]
      exact ⟨p₂, ⟨by omega, hp₂, hp₂2⟩, ⟨hx1, hxN⟩, hxs, hR₂, hsmall⟩
    by_cases hpc : p₂ ≤ pc
    · apply mem_union_left; apply mem_union_left; apply mem_union_right; apply mem_union_right
      simp only [lcMid, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₂, hpc, hp₂, by omega, hR₂⟩
    by_cases hpY : p₂ ≤ Y
    · apply mem_union_left; apply mem_union_right
      simp only [midSet, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₂, hpY, hp₂, by omega, hR₂⟩
    · apply mem_union_right
      simp only [exSet, mem_filter, mem_Icc]
      have h1 : p₂ ≤ x * b + 1 :=
        le_trans (Nat.le_mul_self p₂) (Nat.le_of_dvd (Nat.succ_pos _) hd₂)
      have h2 : x * b + 1 ≤ N * b + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right b hxN) 1
      exact ⟨⟨hx1, hxN⟩, p₂, ⟨by omega, h1.trans h2⟩, hd₂⟩
  ·
    have hz₁ : z₁ < p₁ := by
      by_contra h; push Not at h; exact hsmall ⟨p₁, h, hp₁, hU₁, hR₁⟩
    apply mem_union_left; apply mem_union_left; apply mem_union_left
    by_cases hpB : p₁ ≤ pB
    · apply mem_union_left; apply mem_union_left
      simp only [mem_biUnion, T25, mem_filter, mem_range, lcRes, mem_Icc]
      exact ⟨x % 25, ⟨Nat.mod_lt _ (by norm_num), hxs⟩, ⟨hx1, hxN⟩, rfl, p₁, hpB, hp₁,
        ⟨hU₁, hz₁⟩, hR₁⟩
    by_cases hpY : p₁ ≤ Y'
    · apply mem_union_left; apply mem_union_right
      simp only [vMidSet, mem_filter, mem_Icc]
      exact ⟨⟨hx1, hxN⟩, p₁, hpY, hp₁, ⟨hU₁, by omega⟩, hR₁⟩
    · apply mem_union_right
      simp only [vPellSet, mem_filter, mem_Icc]
      have h1 : p₁ * p₁ ≤ x * x + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd₁
      have h2 : x * x + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hxN hxN) 1
      have h3 : p₁ ≤ N + 1 := by
        by_contra hc; push Not at hc
        have : (N + 2) * (N + 2) ≤ p₁ * p₁ := Nat.mul_le_mul hc hc
        nlinarith
      refine ⟨⟨hx1, hxN⟩, p₁, ⟨by omega, h3⟩, ?_⟩
      rw [sq]; exact hd₁

lemma isU1_infinite : (Set.ofPred IsU1).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hap, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (a + 13) (by norm_num)
  refine ⟨p, ?_, by omega⟩
  show IsU1 p
  unfold Nat.ModEq at hmod
  exact ⟨hp, by simpa using hmod, by omega⟩

noncomputable def u1 (j : ℕ) : ℕ := Nat.nth IsU1 j

lemma u1_isU1 (j : ℕ) : IsU1 (u1 j) := Nat.nth_mem_of_infinite isU1_infinite j

lemma u1_le_of_count {a k : ℕ} (ha : IsU1 a) (hk : k ≤ Nat.count IsU1 a) : u1 k ≤ a := by
  unfold u1
  calc Nat.nth IsU1 k ≤ Nat.nth IsU1 (Nat.count IsU1 a) := Nat.nth_monotone isU1_infinite hk
    _ = a := Nat.nth_count ha

theorem prefix_dom (g : ℕ → ℝ) (hg : ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → g p' ≤ g p) :
    ∀ S : Finset ℕ, (∀ p ∈ S, IsU1 p) →
      ∑ p ∈ S, g p ≤ ∑ j ∈ range S.card, g (u1 j) ∧
        ∏ j ∈ range S.card, u1 j ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro hS
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha : IsU1 a := hS a (mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have hcount : s.card ≤ Nat.count IsU1 a := by
      rw [Nat.count_eq_card_filter_range]
      apply card_le_card
      intro x hx
      simp only [mem_filter, mem_range]
      exact ⟨hlt x hx, hS x (mem_insert_of_mem hx)⟩
    have hua := u1_le_of_count ha hcount
    rw [card_insert_of_notMem has, sum_insert has, prod_insert has, sum_range_succ,
      prod_range_succ]
    refine ⟨?_, ?_⟩
    · have := hg (u1 s.card) a (u1_isU1 _) ha hua
      linarith
    · calc (∏ j ∈ range s.card, u1 j) * u1 s.card ≤ (∏ p ∈ s, p) * a :=
            Nat.mul_le_mul ih2 hua
        _ = a * ∏ p ∈ s, p := mul_comm _ _

theorem prefix_dom_max (g : ℕ → ℝ) (hg : ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → g p' ≤ g p)
    (S : Finset ℕ) (hS : ∀ p ∈ S, IsU1 p) (M L : ℕ) (hSM : ∏ p ∈ S, p ≤ M)
    (hL : M < ∏ j ∈ range (L + 1), u1 j) :
    ∑ p ∈ S, g p ≤ ∑ j ∈ range L, max (g (u1 j)) 0 := by
  obtain ⟨h1, h2⟩ := prefix_dom g hg S hS
  have hcard : S.card ≤ L := by
    by_contra hc
    push Not at hc
    have hmono : ∏ j ∈ range (L + 1), u1 j ≤ ∏ j ∈ range S.card, u1 j := by
      apply prod_le_prod_of_subset_of_one_le' (range_subset_range.mpr hc)
      intro j _ _; exact (u1_isU1 j).1.one_lt.le
    omega
  calc ∑ p ∈ S, g p ≤ ∑ j ∈ range S.card, g (u1 j) := h1
    _ ≤ ∑ j ∈ range S.card, max (g (u1 j)) 0 := sum_le_sum (fun j _ => le_max_left _ _)
    _ ≤ ∑ j ∈ range L, max (g (u1 j)) 0 :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hcard)
          (fun j _ _ => le_max_right _ _)

noncomputable def gC (N z₁ p : ℕ) : ℝ := wholeB N p - nonB N p z₁

noncomputable def PU (z₁ : ℕ) : ℝ := ∏ q ∈ smallP z₁ IsU1, (1 - 2 / ((q : ℝ) * q))

lemma factor_pos {q : ℕ} (hq : q.Prime) : 0 < 1 - 2 / ((q : ℝ) * q) := by
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  rw [sub_pos, div_lt_one (by positivity)]; nlinarith

lemma PU_pos (z₁ : ℕ) : 0 < PU z₁ :=
  prod_pos (fun _q hq => factor_pos (mem_filter.mp hq).2.1)

lemma mem_U_iff {z₁ p : ℕ} (hp : IsU1 p) : p ∈ smallP z₁ IsU1 ↔ p ≤ z₁ := by
  simp only [smallP, mem_filter, mem_range]
  constructor
  · intro h; omega
  · intro h; exact ⟨by omega, hp.1, hp⟩

lemma gC_in {N z₁ p : ℕ} (hpU : p ∈ smallP z₁ IsU1) :
    gC N z₁ p = 23 / 25 * N * PU z₁ / ((p : ℝ) * p - 2) + 3 -
      3 * ((3 : ℝ) ^ ((smallP z₁ IsU1).card - 1) - 1) := by
  have hp : p.Prime := (mem_filter.mp hpU).2.1
  have hf := factor_pos hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0 : ℝ) < p * p := by positivity
  have hpp2 : (0 : ℝ) < p * p - 2 := by nlinarith
  have hmul := mul_prod_erase (smallP z₁ IsU1) (fun q => (1 - 2 / ((q : ℝ) * q))) hpU
  have hpr : ∏ q ∈ (smallP z₁ IsU1).erase p, (1 - 2 / ((q : ℝ) * q)) =
      PU z₁ / (1 - 2 / ((p : ℝ) * p)) := by
    rw [PU, ← hmul, mul_div_cancel_left₀ _ hf.ne']
  unfold gC wholeB nonB
  rw [hpr, card_erase_of_mem hpU]
  have e : (1 : ℝ) - 2 / ((p : ℝ) * p) = ((p : ℝ) * p - 2) / ((p : ℝ) * p) := by
    field_simp
  rw [e]
  field_simp
  ring

lemma gC_out {N z₁ p : ℕ} (hpU : p ∉ smallP z₁ IsU1) :
    gC N z₁ p = 23 / 25 * N * PU z₁ / ((p : ℝ) * p) + 3 -
      3 * ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1) := by
  unfold gC wholeB nonB
  rw [erase_eq_of_notMem hpU]
  unfold PU
  ring

theorem gC_anti (N z₁ : ℕ) :
    ∀ p p', IsU1 p → IsU1 p' → p ≤ p' → gC N z₁ p' ≤ gC N z₁ p := by
  intro p p' hp hp' hle
  have hP := PU_pos z₁
  have hN : (0 : ℝ) ≤ N := by positivity
  have h13 : (13 : ℝ) ≤ p := by exact_mod_cast hp.2.2
  have hle' : (p : ℝ) ≤ p' := by exact_mod_cast hle
  have hsq : (p : ℝ) * p ≤ (p' : ℝ) * p' := by nlinarith
  have hNP : 0 ≤ 23 / 25 * (N : ℝ) * PU z₁ := by positivity
  by_cases hpU : p ≤ z₁
  · rw [gC_in ((mem_U_iff hp).mpr hpU)]
    by_cases hpU' : p' ≤ z₁
    · rw [gC_in ((mem_U_iff hp').mpr hpU')]
      have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p' - 2) ≤
          23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p - 2) :=
        div_le_div_of_nonneg_left hNP (by nlinarith) (by linarith)
      linarith
    · rw [gC_out (fun h => hpU' ((mem_U_iff hp').mp h))]
      have hcard : 1 ≤ (smallP z₁ IsU1).card :=
        card_pos.mpr ⟨p, (mem_U_iff hp).mpr hpU⟩
      have hpow : (3 : ℝ) ^ ((smallP z₁ IsU1).card - 1) ≤ 3 ^ (smallP z₁ IsU1).card :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p') ≤
          23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p - 2) :=
        div_le_div_of_nonneg_left hNP (by nlinarith) (by linarith)
      linarith
  · have hpU' : ¬ p' ≤ z₁ := by omega
    rw [gC_out (fun h => hpU ((mem_U_iff hp).mp h)),
      gC_out (fun h => hpU' ((mem_U_iff hp').mp h))]
    have : 23 / 25 * (N : ℝ) * PU z₁ / ((p' : ℝ) * p') ≤
        23 / 25 * (N : ℝ) * PU z₁ / ((p : ℝ) * p) :=
      div_le_div_of_nonneg_left hNP (by nlinarith) hsq
    linarith

lemma prod_sq_dvd {n : ℕ} : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p * p ∣ n) →
    (∏ p ∈ S, p) * (∏ p ∈ S, p) ∣ n := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a s has ih =>
    intro hP hd
    rw [prod_insert has]
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right (fun q hq =>
      (Nat.coprime_primes (hP a (mem_insert_self a s)) (hP q (mem_insert_of_mem hq))).mpr
        (fun h => has (h ▸ hq)))
    have hcop2 : Nat.Coprime (a * a) ((∏ p ∈ s, p) * (∏ p ∈ s, p)) :=
      Nat.Coprime.mul_right (Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩)
        (Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩)
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 (hd a (mem_insert_self a s))
      (ih (fun p hp => hP p (mem_insert_of_mem hp)) (fun p hp => hd p (mem_insert_of_mem hp)))
    calc a * (∏ p ∈ s, p) * (a * ∏ p ∈ s, p) = a * a * ((∏ p ∈ s, p) * (∏ p ∈ s, p)) := by ring
      _ ∣ n := this

lemma smallP_odd_eq (z₂ : ℕ) (h5 : 5 ≤ z₂) :
    smallP z₂ (· ≠ 2) = insert 5 (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)) := by
  ext p
  simp only [smallP, mem_insert, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases h : p = 5
    · left; exact h
    · right; exact ⟨h1, h2, h3, h⟩
  · rintro (rfl | ⟨h1, h2, h3, -⟩)
    · exact ⟨by omega, Nat.prime_five, by norm_num⟩
    · exact ⟨h1, h2, h3⟩

theorem card_lemCPart_le (N b z₁ z₂ pB Y' pc : ℕ) (G : ℝ) (hbN : b ≤ N) (hbs : IsStar b)
    (h5 : 5 ≤ z₂)
    (hG : ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 → ∑ p ∈ S, gC N z₁ p ≤ G) :
    ((lemCPart N b z₁ z₂ pB Y' pc).card : ℝ) ≤
      23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) +
      ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
      ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y' + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) +
      ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
      G +
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1) := by
  classical

  set R1 := T25.biUnion (fun t => lcRes N t z₁ pB)
  set X := (smallP z₂ (· ≠ 2)).biUnion (fun p₂ => xSet N b p₂ z₁)
  have hU : (lemCPart N b z₁ z₂ pB Y' pc).card ≤ R1.card + (vMidSet N pB Y').card +
      (vPellSet N Y').card + (X.card + (lcMid N b z₂ pc).card) := by
    have hdef : lemCPart N b z₁ z₂ pB Y' pc =
        ((R1 ∪ vMidSet N pB Y') ∪ vPellSet N Y') ∪ (X ∪ lcMid N b z₂ pc) := rfl
    rw [hdef]
    have a1 := Finset.card_union_le ((R1 ∪ vMidSet N pB Y') ∪ vPellSet N Y') (X ∪ lcMid N b z₂ pc)
    have a2 := Finset.card_union_le (R1 ∪ vMidSet N pB Y') (vPellSet N Y')
    have a3 := Finset.card_union_le R1 (vMidSet N pB Y')
    have a4 := Finset.card_union_le X (lcMid N b z₂ pc)
    omega
  have hUR : ((lemCPart N b z₁ z₂ pB Y' pc).card : ℝ) ≤ (R1.card : ℝ) + (vMidSet N pB Y').card +
      (vPellSet N Y').card + ((X.card : ℝ) + (lcMid N b z₂ pc).card) := by exact_mod_cast hU

  have hR1 : (R1.card : ℝ) ≤ 23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p),
      (2 * ((N : ℝ) / 25 / (p * p)) + 2) := by
    have h1 : (R1.card : ℝ) ≤ ∑ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 : ∀ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) ≤
        ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) := by
      intro t ht
      have ht25 : t < 25 := mem_range.mp (mem_filter.mp ht).1
      have h := classSieve_le N 25 t z₁ pB 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ z₁ < p)
        (by norm_num) ht25 (by norm_num) sqRoots_sub
        (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1))
        (fun p hp hU => Nat.Coprime.symm (Nat.Coprime.pow_right 2
          ((Nat.coprime_primes hp Nat.prime_five).mpr (by have := hU.1.2.2; omega))))
      have hsmall : smallP z₁ (fun p => IsU1 p ∧ z₁ < p) = ∅ := by
        rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
      rw [hsmall] at h
      simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat]
        at h
      simpa [lcRes] using h
    have hT : T25.card = 23 := by decide
    calc (R1.card : ℝ) ≤ ∑ t ∈ T25, ((lcRes N t z₁ pB).card : ℝ) := h1
      _ ≤ ∑ _t ∈ T25, ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p),
          (2 * ((N : ℝ) / 25 / (p * p)) + 2) := sum_le_sum h2
      _ = _ := by rw [sum_const, hT, nsmul_eq_mul]; norm_num

  have hmid : ((vMidSet N pB Y').card : ℝ) ≤
      ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) := by
    have h := classSieve_le N 1 0 pB Y' 2 (fun p => sqRoots p) (fun p => IsU1 p ∧ pB < p)
      one_pos one_pos (by norm_num) sqRoots_sub
      (fun p hp hU => card_sqRoots_le hp (isU1_odd hU.1)) (fun p _ _ => Nat.coprime_one_left p)
    have hsmall : smallP pB (fun p => IsU1 p ∧ pB < p) = ∅ := by
      rw [smallP, filter_eq_empty_iff]; intro p hp; simp only [mem_range] at hp; omega
    rw [hsmall] at h
    simp only [prod_empty, sub_self, mul_zero, card_empty, pow_zero, zero_add, Nat.cast_ofNat,
      Nat.mod_one, true_and] at h
    simpa [vMidSet] using h
  have hpell : ((vPellSet N Y').card : ℝ) ≤
      ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y' + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast pellTail_adm_le N Y'

  have hlc : ((lcMid N b z₂ pc).card : ℝ) ≤
      ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1) := card_midSet_le N b z₂ pc

  have hX1 : (X.card : ℝ) ≤ ∑ p ∈ smallP z₂ (· ≠ 2), ((xSet N b p z₁).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  have hX5 := card_xSet5_le N b z₁
  have hodd : ∀ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), ((xSet N b p z₁).card : ℝ) ≤
      nonB N p z₁ + if p * p ∣ b * b + 1 then gC N z₁ p else 0 := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have := card_xSet_le N b p z₁ hpp.1 hpp.2.2
    split_ifs at this ⊢ <;> unfold gC at * <;> linarith
  set S := (smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5)).filter (fun p => p * p ∣ b * b + 1)
  have hsplit : ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5),
      (nonB N p z₁ + if p * p ∣ b * b + 1 then gC N z₁ p else 0) =
      ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ + ∑ p ∈ S, gC N z₁ p := by
    rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero]
  have hSU1 : ∀ p ∈ S, IsU1 p := fun p hp =>
    isU1_of_sq_dvd (mem_filter.mp (mem_filter.mp hp).1).2.1 (mem_filter.mp hp).2 hbs
  have hSprod : (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 := by
    have hd := prod_sq_dvd S (fun p hp => (hSU1 p hp).1) (fun p hp => (mem_filter.mp hp).2)
    have h1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    have h2 : b * b + 1 ≤ N * N + 1 := Nat.add_le_add_right (Nat.mul_le_mul hbN hbN) 1
    omega
  have hC2 := hG S (filter_subset _ _) hSU1 hSprod
  have hXsum : ∑ p ∈ smallP z₂ (· ≠ 2), ((xSet N b p z₁).card : ℝ) ≤
      ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
      (∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
        G) := by
    rw [smallP_odd_eq z₂ h5, sum_insert (by simp [smallP])]
    have := sum_le_sum hodd
    rw [hsplit] at this
    unfold PU
    linarith
  linarith

lemma gBound_prefix (N z₁ z₂ L : ℕ)
    (hL : N * N + 1 < (∏ j ∈ range (L + 1), u1 j) * (∏ j ∈ range (L + 1), u1 j)) :
    ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 →
        ∑ p ∈ S, gC N z₁ p ≤ ∑ j ∈ range L, max (gC N z₁ (u1 j)) 0 := by
  intro S _ hSU1 hSprod
  have : ∏ p ∈ S, p < ∏ j ∈ range (L + 1), u1 j :=
    Nat.mul_self_lt_mul_self_iff.mp (by omega)
  exact prefix_dom_max (gC N z₁) (gC_anti N z₁) S hSU1 (∏ p ∈ S, p) L le_rfl this

lemma gBound_all (N z₁ z₂ : ℕ) :
    ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 →
        ∑ p ∈ S, gC N z₁ p ≤ ∑ p ∈ smallP z₂ IsU1, max (gC N z₁ p) 0 := by
  intro S hS hSU1 _
  have hsub : S ⊆ smallP z₂ IsU1 := fun p hp => by
    have := hS hp
    simp only [smallP, mem_filter] at this ⊢
    exact ⟨this.1, this.2.1, hSU1 p hp⟩
  calc ∑ p ∈ S, gC N z₁ p ≤ ∑ p ∈ S, max (gC N z₁ p) 0 := sum_le_sum (fun p _ => le_max_left _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => le_max_right _ _)

end Erdos848


namespace Erdos848

open Finset

open ErdosComp

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

lemma isU1B_of_isU1 {n : ℕ} (hn : IsU1 n) : isU1B n = true := by
  unfold isU1B
  simp [isPrimeB_of_prime hn.1, hn.2.1, hn.2.2]

def accP (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter (fun n => isPrimeB n = true)

def accU (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter (fun n => isU1B n = true)

lemma Ioc_succ (n : ℕ) : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
  ext x; simp only [mem_Ioc, mem_insert]; omega

lemma isPrimeB_of_isU1B {n : ℕ} (h : isU1B n = true) : isPrimeB n = true := by
  unfold isU1B at h; simp only [Bool.and_eq_true] at h; exact h.1.1

theorem stAt_spec (n : ℕ) :
    (stAt n).cp = (accP 0 n).card ∧ (stAt n).cu = (accU 0 n).card ∧
    (stAt n).fp = ∑ p ∈ accP 0 n, ceilK p ∧ (stAt n).fu = ∑ p ∈ accU 0 n, ceilK p := by
  induction n with
  | zero => simp [stAt, accP, accU]
  | succ n ih =>
    have hnot : n + 1 ∉ Ioc 0 n := by simp
    have hP : accP 0 (n + 1) = if isPrimeB (n + 1) = true then insert (n + 1) (accP 0 n)
        else accP 0 n := by
      unfold accP; rw [Ioc_succ, filter_insert]
    have hU : accU 0 (n + 1) = if isU1B (n + 1) = true then insert (n + 1) (accU 0 n)
        else accU 0 n := by
      unfold accU; rw [Ioc_succ, filter_insert]
    have hnP : n + 1 ∉ accP 0 n := fun h => hnot (mem_filter.mp h).1
    have hnU : n + 1 ∉ accU 0 n := fun h => hnot (mem_filter.mp h).1
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [stAt, stepSt]
    cases hp : isPrimeB (n + 1) with
    | true =>
      cases hu : isU1B (n + 1) with
      | true =>
        simp only [ite_true, hP, hp, hU, hu, card_insert_of_notMem hnP,
          card_insert_of_notMem hnU, sum_insert hnP, sum_insert hnU]
        refine ⟨by rw [h1], by rw [h2], by rw [h3]; ring, by rw [h4]; ring⟩
      | false =>
        simp only [ite_true, Bool.false_eq_true, ite_false, hP, hp, hU, hu,
          card_insert_of_notMem hnP, sum_insert hnP]
        refine ⟨by rw [h1], h2, by rw [h3]; ring, h4⟩
    | false =>
      have hu : isU1B (n + 1) = false := by
        cases h : isU1B (n + 1)
        · rfl
        · rw [isPrimeB_of_isU1B h] at hp; exact absurd hp (by simp)
      simp only [Bool.false_eq_true, ite_false, hP, hp, hU, hu]
      exact ⟨h1, h2, h3, h4⟩

lemma advance_stAt : ∀ k n, advance k n (stAt n) = stAt (n + k) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    show advance k (n + 1) (stepSt (n + 1) (stAt n)) = stAt (n + (k + 1))
    rw [show stepSt (n + 1) (stAt n) = stAt (n + 1) from rfl, ih, Nat.add_right_comm, add_assoc]

lemma evalPts_sound : ∀ xs n, ∀ e ∈ evalPts xs n (stAt n), e.2 = stAt e.1 := by
  intro xs
  induction xs with
  | nil => intro n e he; simp [evalPts] at he
  | cons x xs ih =>
    intro n e he
    simp only [evalPts, List.mem_cons] at he
    rw [advance_stAt] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ e he

lemma lookD_eq {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1) (x : ℕ) :
    lookD tab x = stAt x := by
  unfold lookD
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hx := List.find?_some he
    simp only [beq_iff_eq] at hx
    rw [htab e hmem, hx]
  · rfl

noncomputable def S2 (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1 / ((p : ℝ) * p)

def primesIn (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter Nat.Prime

def u1In (lo hi : ℕ) : Finset ℕ := (Ioc lo hi).filter IsU1

lemma S2_nonneg (P : Finset ℕ) : 0 ≤ S2 P := sum_nonneg (fun p _ => by positivity)

lemma S2_mono {P Q : Finset ℕ} (h : P ⊆ Q) : S2 P ≤ S2 Q :=
  sum_le_sum_of_subset_of_nonneg h (fun p _ _ => by positivity)

lemma primesIn_sub_accP (lo hi : ℕ) : primesIn lo hi ⊆ accP lo hi := fun p hp => by
  simp only [primesIn, accP, mem_filter] at hp ⊢; exact ⟨hp.1, isPrimeB_of_prime hp.2⟩

lemma u1In_sub_accU (lo hi : ℕ) : u1In lo hi ⊆ accU lo hi := fun p hp => by
  simp only [u1In, accU, mem_filter] at hp ⊢; exact ⟨hp.1, isU1B_of_isU1 hp.2⟩

lemma Ioc_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Ioc a c = Ioc a b ∪ Ioc b c := by
  ext x; simp only [mem_Ioc, mem_union]; omega

lemma Ioc_disj (a b c : ℕ) : Disjoint (Ioc a b) (Ioc b c) := by
  rw [disjoint_left]; intro x h1 h2; simp only [mem_Ioc] at h1 h2; omega

lemma filter_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → Bool) :
    (Ioc a c).filter (fun n => f n = true) =
      (Ioc a b).filter (fun n => f n = true) ∪ (Ioc b c).filter (fun n => f n = true) := by
  rw [Ioc_split hab hbc, filter_union]

lemma filter_disj (a b c : ℕ) (f : ℕ → Bool) :
    Disjoint ((Ioc a b).filter (fun n => f n = true)) ((Ioc b c).filter (fun n => f n = true)) :=
  disjoint_filter_filter (Ioc_disj a b c)

lemma inv_sq_le_ceilK {p : ℕ} (hp : 1 ≤ p) : 1 / ((p : ℝ) * p) ≤ (ceilK p : ℝ) / KS := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have h : KS ≤ ceilK p * (p * p) := by
    unfold ceilK
    have h1 := Nat.lt_div_mul_add (a := KS + p * p - 1) hpp
    have hK : 1 ≤ KS := by unfold KS; norm_num
    generalize (KS + p * p - 1) / (p * p) * (p * p) = y at h1 ⊢
    omega
  have hR : (KS : ℝ) ≤ (ceilK p : ℝ) * ((p : ℝ) * p) := by exact_mod_cast h
  have hK : (0 : ℝ) < KS := by unfold KS; positivity
  have hp' : (0 : ℝ) < (p : ℝ) * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  rw [div_le_div_iff₀ hp' hK]; linarith

lemma S2_accP_le (lo hi : ℕ) :
    S2 (accP lo hi) ≤ (((stAt hi).fp - (stAt lo).fp : ℕ) : ℝ) / KS := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isPrimeB
    have hdisj := filter_disj 0 lo hi isPrimeB
    have hfp : (stAt hi).fp = (stAt lo).fp + ∑ p ∈ accP lo hi, ceilK p := by
      rw [(stAt_spec hi).2.2.1, (stAt_spec lo).2.2.1]
      unfold accP; rw [hsplit, sum_union hdisj]
    rw [hfp, Nat.add_sub_cancel_left, Nat.cast_sum, sum_div]
    unfold S2
    apply sum_le_sum; intro p hp
    exact inv_sq_le_ceilK (by simp only [accP, mem_filter, mem_Ioc] at hp; omega)
  · have : accP lo hi = ∅ := by
      unfold accP; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; unfold S2; simp only [sum_empty]; positivity

lemma S2_accU_le (lo hi : ℕ) :
    S2 (accU lo hi) ≤ (((stAt hi).fu - (stAt lo).fu : ℕ) : ℝ) / KS := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isU1B
    have hdisj := filter_disj 0 lo hi isU1B
    have hfu : (stAt hi).fu = (stAt lo).fu + ∑ p ∈ accU lo hi, ceilK p := by
      rw [(stAt_spec hi).2.2.2, (stAt_spec lo).2.2.2]
      unfold accU; rw [hsplit, sum_union hdisj]
    rw [hfu, Nat.add_sub_cancel_left, Nat.cast_sum, sum_div]
    unfold S2
    apply sum_le_sum; intro p hp
    exact inv_sq_le_ceilK (by simp only [accU, mem_filter, mem_Ioc] at hp; omega)
  · have : accU lo hi = ∅ := by
      unfold accU; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; unfold S2; simp only [sum_empty]; positivity

lemma card_accP_le (lo hi : ℕ) : (accP lo hi).card ≤ (stAt hi).cp - (stAt lo).cp := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isPrimeB
    have hdisj := filter_disj 0 lo hi isPrimeB
    have : (stAt hi).cp = (stAt lo).cp + (accP lo hi).card := by
      rw [(stAt_spec hi).1, (stAt_spec lo).1]; unfold accP; rw [hsplit, card_union_of_disjoint hdisj]
    omega
  · have : accP lo hi = ∅ := by
      unfold accP; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; simp

lemma card_accU_le (lo hi : ℕ) : (accU lo hi).card ≤ (stAt hi).cu - (stAt lo).cu := by
  by_cases h : lo ≤ hi
  · have hsplit := filter_split (Nat.zero_le lo) h isU1B
    have hdisj := filter_disj 0 lo hi isU1B
    have : (stAt hi).cu = (stAt lo).cu + (accU lo hi).card := by
      rw [(stAt_spec hi).2.1, (stAt_spec lo).2.1]; unfold accU; rw [hsplit, card_union_of_disjoint hdisj]
    omega
  · have : accU lo hi = ∅ := by
      unfold accU; rw [filter_eq_empty_iff]; intro x hx; simp only [mem_Ioc] at hx; omega
    rw [this]; simp

lemma sum_inv_sq_Ioc_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ n ∈ Ioc a b, 1 / ((n : ℝ) * n) ≤ 1 / a - 1 / max a b := by
  induction b with
  | zero => rw [show Ioc a 0 = ∅ by ext; simp]; simp
  | succ b ih =>
    by_cases hab : b < a
    · have : Ioc a (b + 1) = ∅ := by
        ext x; simp only [mem_Ioc, notMem_empty, iff_false]; omega
      rw [this, max_eq_left (by omega)]; simp
    · push Not at hab
      have hins : Ioc a (b + 1) = insert (b + 1) (Ioc a b) := by
        ext x; simp only [mem_Ioc, mem_insert]; omega
      rw [hins, sum_insert (by simp), max_eq_right (by omega)]
      rw [max_eq_right hab] at ih
      have hb : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      have key : 1 / (((b + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

lemma S2_tail_le {a : ℕ} (ha : 1 ≤ a) (P : Finset ℕ) (b : ℕ) (hP : P ⊆ Ioc a b) :
    S2 P ≤ 1 / a := by
  have h1 := sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => by positivity : ∀ p ∈ Ioc a b,
    p ∉ P → (0 : ℝ) ≤ 1 / ((p : ℝ) * p))
  have h2 := sum_inv_sq_Ioc_le ha b
  have : (0 : ℝ) ≤ 1 / max (a : ℝ) b := by positivity
  unfold S2; push_cast at h2; linarith


section ExtraPrimeBounds

open Real Chebyshev

lemma logLoF_spec {x : ℕ} (hx : 4 ≤ x) :
    0 < ((logLoF x : ℚ) : ℝ) ∧ ((logLoF x : ℚ) : ℝ) ≤ Real.log x := by
  unfold logLoF
  set k := Nat.log2 x with hk_def
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hpow : 2 ^ (k + 1) ≤ 4 := by
      have : k + 1 ≤ 2 := by omega
      exact le_trans (Nat.pow_le_pow_right (by norm_num) this) (by norm_num)
    have hself : x < 2 ^ (k + 1) := by rw [hk_def]; exact Nat.lt_log2_self
    omega
  have h2k_le : 2 ^ k ≤ x := by rw [hk_def]; exact Nat.log2_self_le (by omega)
  have hxR : (0 : ℝ) < x := by positivity
  have h2kR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hr_le : (((64 * (x - 2 ^ k)) / x : ℕ) : ℝ) ≤ 64 * (1 - (2 : ℝ) ^ k / x) := by
    have h1 : (((64 * (x - 2 ^ k)) / x : ℕ) : ℝ) ≤ ((64 * (x - 2 ^ k) : ℕ) : ℝ) / x :=
      Nat.cast_div_le
    have h2 : ((64 * (x - 2 ^ k) : ℕ) : ℝ) = 64 * ((x : ℝ) - (2 : ℝ) ^ k) := by
      push_cast [Nat.cast_sub h2k_le]; ring
    rw [h2] at h1
    have h3 : 64 * ((x : ℝ) - (2 : ℝ) ^ k) / x = 64 * (1 - (2 : ℝ) ^ k / x) := by
      field_simp
    linarith
  have hsplit : Real.log x = k * Real.log 2 + Real.log (x / (2 : ℝ) ^ k) := by
    rw [Real.log_div hxR.ne' h2kR.ne', Real.log_pow]; ring
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hxR h2kR)
  rw [inv_div] at hlog
  have hl2 := Real.log_two_gt_d9
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hr0 : (0 : ℝ) ≤ (((64 * (x - 2 ^ k)) / x : ℕ) : ℝ) := by positivity
  push_cast
  refine ⟨by linarith, ?_⟩
  rw [hsplit]
  nlinarith

def piInvPM (st : Nat × Rat × Rat) : Prop :=
  PM ≤ st.1 ∧ 0 < (st.2.1 : ℝ) ∧ (st.2.1 : ℝ) ≤ Real.log st.1 ∧
    ((Nat.primesLE st.1).card : ℝ) - ((Nat.primesLE PM).card : ℝ) -
      (θ st.1 - θ PM) / (st.2.1 : ℝ) ≤ (st.2.2 : ℝ)

lemma log4_le_const : Real.log 4 ≤ 13863 / 10000 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9; push_cast; linarith

lemma piStep_preservesPM (hi : ℕ) (st : ℕ × ℚ × ℚ) (nd : ℕ × ℕ) (h : piInvPM st) :
    piInvPM (piStep hi st nd) ∧ st.1 ≤ (piStep hi st nd).1 := by
  rcases st with ⟨x, w, B⟩
  dsimp only [piInvPM] at h
  rcases h with ⟨hxPM, hwpos, hwlog, hB⟩
  dsimp only [piStep, piInvPM]
  set x' := max x ((hi * nd.1) / nd.2)
  set w' := max w (logLoF x')
  have hxx' : x ≤ x' := le_max_left _ _
  have hx'PM : PM ≤ x' := hxPM.trans hxx'
  have hx4 : 4 ≤ x := le_trans (by unfold PM; norm_num) hxPM
  have hx'4 : 4 ≤ x' := hx4.trans hxx'
  have hww' : (w : ℝ) ≤ (w' : ℝ) := by exact_mod_cast le_max_left w (logLoF x')
  have hw'pos : 0 < (w' : ℝ) := lt_of_lt_of_le hwpos hww'
  have hxpos : (0 : ℝ) < x := by positivity
  have hlog_mono : Real.log x ≤ Real.log x' := Real.log_le_log hxpos (by exact_mod_cast hxx')
  have hw'log : (w' : ℝ) ≤ Real.log x' := by
    have hlf := (logLoF_spec hx'4).2
    rw [show (w' : ℝ) = max (w : ℝ) ((logLoF x' : ℚ) : ℝ) from Rat.cast_max w (logLoF x')]
    exact max_le (hwlog.trans hlog_mono) hlf
  have hsub : Nat.primesLE x ⊆ Nat.primesLE x' := Nat.primesLE_mono hxx'
  have hcard : ((Nat.primesLE x').card : ℝ) - ((Nat.primesLE x).card : ℝ) =
      (((Nat.primesLE x' \ Nat.primesLE x).card : ℕ) : ℝ) := by
    have hc := card_sdiff_add_card_eq_card hsub
    have hcR : (((Nat.primesLE x' \ Nat.primesLE x).card : ℕ) : ℝ) + ((Nat.primesLE x).card : ℝ) =
        ((Nat.primesLE x').card : ℝ) := by exact_mod_cast hc
    linarith
  have htheta_diff : θ x' - θ x = ∑ p ∈ Nat.primesLE x' \ Nat.primesLE x, Real.log p := by
    rw [theta_eq_sum_primesLE_log x', theta_eq_sum_primesLE_log x]
    have hs := sum_sdiff_eq_sub hsub (f := fun p : ℕ => Real.log p)
    linarith
  have hstep_primes : (((Nat.primesLE x' \ Nat.primesLE x).card : ℕ) : ℝ) ≤ (θ x' - θ x) / (w : ℝ) := by
    rw [le_div_iff₀ hwpos, htheta_diff]
    calc (((Nat.primesLE x' \ Nat.primesLE x).card : ℕ) : ℝ) * (w : ℝ)
        = ∑ _p ∈ Nat.primesLE x' \ Nat.primesLE x, (w : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ Nat.primesLE x' \ Nat.primesLE x, Real.log p := by
          apply sum_le_sum; intro p hp
          rw [mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
          have hxp : x ≤ p := by by_contra hlt; exact hp.2 ⟨by omega, hp.1.2⟩
          exact hwlog.trans (Real.log_le_log hxpos (by exact_mod_cast hxp))
  have hinv_diff : 0 ≤ 1 / (w : ℝ) - 1 / (w' : ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hwpos hww')
  have htheta_PM : 0 ≤ θ PM := theta_nonneg PM
  have htheta_ub : θ x' - θ PM ≤ (13863 / 10000 : ℝ) * x' := by
    have h1 : θ x' ≤ Real.log 4 * x' := theta_le_log4_mul_x (by positivity)
    have h2 : Real.log 4 * x' ≤ (13863 / 10000 : ℝ) * x' :=
      mul_le_mul_of_nonneg_right log4_le_const (by positivity)
    linarith
  have hprod : (θ x' - θ PM) * (1 / (w : ℝ) - 1 / (w' : ℝ)) ≤
      (13863 / 10000 : ℝ) * x' * (1 / (w : ℝ) - 1 / (w' : ℝ)) :=
    mul_le_mul_of_nonneg_right htheta_ub hinv_diff
  have hid : ((Nat.primesLE x').card : ℝ) - ((Nat.primesLE PM).card : ℝ) - (θ x' - θ PM) / (w' : ℝ) =
      (((Nat.primesLE x').card : ℝ) - ((Nat.primesLE x).card : ℝ) - (θ x' - θ x) / (w : ℝ)) +
      (((Nat.primesLE x).card : ℝ) - ((Nat.primesLE PM).card : ℝ) - (θ x - θ PM) / (w : ℝ)) +
      (θ x' - θ PM) * (1 / (w : ℝ) - 1 / (w' : ℝ)) := by ring
  refine ⟨⟨hx'PM, hw'pos, hw'log, ?_⟩, hxx'⟩
  push_cast
  linarith

lemma foldl_piStep_specPM (hi : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (st : ℕ × ℚ × ℚ),
      piInvPM st → st.1 ≤ hi → (∀ nd ∈ l, nd.1 ≤ nd.2) →
      piInvPM (l.foldl (piStep hi) st) ∧ (l.foldl (piStep hi) st).1 ≤ hi := by
  intro l
  induction l with
  | nil => intro st h1 h2 _; exact ⟨h1, h2⟩
  | cons nd rest ih =>
    intro st hinv hle hnd
    have h1 := piStep_preservesPM hi st nd hinv
    have hnd0 := hnd nd (List.mem_cons_self ..)
    have hdiv : (hi * nd.1) / nd.2 ≤ hi := by
      rcases Nat.eq_zero_or_pos nd.2 with hz | _
      · rw [hz, Nat.div_zero]; exact Nat.zero_le _
      · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right hi hnd0)
    have hle' : (piStep hi st nd).1 ≤ hi := max_le hle hdiv
    exact ih _ h1.1 hle' (fun x hx => hnd x (List.mem_cons_of_mem _ hx))

theorem card_primesIn_PM_le (hi : ℕ) :
    ((primesIn PM hi).card : ℝ) ≤ ((piAfterPM hi : ℚ) : ℝ) := by
  unfold primesIn piAfterPM
  split_ifs with hle
  · have hemp : (Ioc PM hi).filter Nat.Prime = ∅ := by
      rw [filter_eq_empty_iff]; intro x hx; rw [mem_Ioc] at hx; omega
    rw [hemp]; simp
  · push Not at hle
    have hPM4 : 4 ≤ PM := by unfold PM; norm_num
    have hinv0 : piInvPM (PM, logLoF PM, 0) := by
      dsimp only [piInvPM]
      obtain ⟨hp, hl⟩ := logLoF_spec hPM4
      refine ⟨le_rfl, hp, hl, ?_⟩
      rw [sub_self, sub_self, zero_div, sub_zero, Rat.cast_zero]
    set init := piFracs.take 36
    have hfr_eq : piFracs = init ++ [(1, 1)] := by decide
    have hinit_nd : ∀ nd ∈ init, nd.1 ≤ nd.2 := by decide
    rw [hfr_eq, List.foldl_append]
    set st1 := init.foldl (piStep hi) (PM, logLoF PM, 0)
    obtain ⟨hinv1, hle1⟩ := foldl_piStep_specPM hi init (PM, logLoF PM, 0) hinv0 hle.le hinit_nd
    dsimp only [List.foldl]
    have hlast := (piStep_preservesPM hi st1 (1, 1) hinv1).1
    have hxf : (piStep hi st1 (1, 1)).1 = hi := by
      dsimp [piStep]; rw [Nat.mul_one, Nat.div_one]; exact max_eq_right hle1
    dsimp only [piInvPM] at hlast
    rw [hxf] at hlast
    rcases hlast with ⟨_, hwf_pos, _, hBf⟩
    have hsub_sdiff : (Ioc PM hi).filter Nat.Prime ⊆ Nat.primesLE hi \ Nat.primesLE PM := by
      intro p hp
      simp only [mem_filter, mem_Ioc, mem_sdiff, Nat.mem_primesLE] at hp ⊢
      exact ⟨⟨hp.1.2, hp.2⟩, fun h => by omega⟩
    have hcard_le : (((Ioc PM hi).filter Nat.Prime).card : ℝ) ≤
        ((Nat.primesLE hi).card : ℝ) - ((Nat.primesLE PM).card : ℝ) := by
      have h1 : ((Ioc PM hi).filter Nat.Prime).card ≤ (Nat.primesLE hi \ Nat.primesLE PM).card :=
        card_le_card hsub_sdiff
      have h2 := card_sdiff_add_card_eq_card (Nat.primesLE_mono hle.le)
      have h1R : (((Ioc PM hi).filter Nat.Prime).card : ℝ) ≤
          (((Nat.primesLE hi \ Nat.primesLE PM).card : ℕ) : ℝ) := by exact_mod_cast h1
      have h2R : (((Nat.primesLE hi \ Nat.primesLE PM).card : ℕ) : ℝ) + ((Nat.primesLE PM).card : ℝ) =
          ((Nat.primesLE hi).card : ℝ) := by exact_mod_cast h2
      linarith
    have hth_hi : (θ hi - θ PM) / ((piStep hi st1 (1, 1)).2.1 : ℝ) ≤
        (13863 / 10000 : ℝ) * hi / ((piStep hi st1 (1, 1)).2.1 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hwf_pos.le
      have h0 : 0 ≤ θ PM := theta_nonneg PM
      have h1 : θ hi ≤ Real.log 4 * hi := theta_le_log4_mul_x (by positivity)
      have h2 : Real.log 4 * hi ≤ (13863 / 10000 : ℝ) * hi :=
        mul_le_mul_of_nonneg_right log4_le_const (by positivity)
      linarith
    push_cast
    linarith

def gcdF : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | f + 1, a, b => cond (Nat.beq b 0) a (gcdF f b (a % b))

lemma gcdF_eq : ∀ f a b, b < f → gcdF f a b = Nat.gcd a b := by
  intro f
  induction f with
  | zero => intro a b hb; omega
  | succ f ih =>
    intro a b hb
    unfold gcdF
    cases h0 : Nat.beq b 0
    · rw [cond_false]
      have hb0 : b ≠ 0 := fun h => by subst h; simp at h0
      have hmod : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb0)
      rw [ih b (a % b) (by omega), Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm]
    · rw [cond_true]
      have hb0 : b = 0 := Nat.beq_eq.mp h0
      subst hb0; simp

def selL : List (Nat × Int) := [(1, 10000), (3, -8986), (5, -8180), (7, -7586), (11, -7108), (13, -6800), (15, 7031), (17, -6198), (19, -6157), (21, 6563), (23, -5566), (29, -5514), (31, -5502), (33, 6493), (35, 6076), (37, -4996), (39, 5642), (41, -4983), (43, -4977), (47, -4967), (51, 4427), (53, -4247), (55, 5729), (57, 4398), (59, -4239), (61, -4236), (65, 5642), (67, -4230), (69, 4356), (71, -4226), (73, -4225), (77, 5347), (79, -4220), (83, -4218), (85, 3689), (87, 4316), (89, -2809), (91, 3511), (93, 4306), (95, 3665), (97, -2807), (101, -2806), (103, -2805), (105, -6076), (107, -2804), (109, -2804), (111, 4282), (113, -2803), (115, 3630), (119, 3443), (123, 4271), (127, -2800), (129, 4266), (131, -2799), (133, 3421), (137, -2798), (139, -2798), (141, 4257), (143, 3310), (145, 3596), (149, -2797), (151, -2796), (155, 3588), (157, -2796), (159, 4247), (161, 3388), (163, -2795), (165, -5729), (167, -2795), (173, -2794), (177, 4239), (179, -2793), (181, -2793), (183, 4236), (185, 3569), (187, 3247), (191, -2792), (193, -2792), (195, -5642), (197, -2792), (199, -2792), (201, 4230), (203, 3357), (205, 3559), (209, 3225), (211, -2791), (213, 4226), (215, 3555), (217, 3349), (219, 4225), (221, 3197), (223, -2790), (227, -2790), (229, -2790), (231, -5347), (233, -2790), (235, 3548), (237, 4220), (239, -2789), (241, -2789), (247, 3176), (249, 4218)]
def selD (i : Nat) : Nat := (selL.getD i (1, 0)).1
def selW (i : Nat) : Int := (selL.getD i (1, 0)).2

def selTermC (i j : Nat) : Int :=
  let d1 := selD i
  let d2 := selD j
  let num : Int := selW i * selW j * (gcdF 250 d1 d2 : Int)
  let den : Int := (400000000 * d1 * d2 : Nat)
  (num * (100000000000000000000 : Int) + den - 1) / den

def selSumRow (f : Nat → Nat → Int) (i : Nat) : Nat → Int
  | 0 => 0
  | j + 1 => selSumRow f i j + f i j

def selSum2D (f : Nat → Nat → Int) : Nat → Nat → Int
  | 0, _ => 0
  | i + 1, m => selSum2D f i m + selSumRow f i m

lemma sel_props : selD 0 = 1 ∧ selW 0 = 10000 ∧
    ∀ i < 102, 1 ≤ selD i ∧ selD i < 250 ∧ selD i % 2 = 1 ∧ (0 < i → 1 < selD i) := by
  decide +kernel

set_option maxHeartbeats 20000000 in
lemma sel_main_ok : selSum2D selTermC 102 102 ≤ 69446 * (100000000000000 : Int) := by
  decide +kernel

set_option maxHeartbeats 20000000 in
lemma sel_err_ok :
    selSum2D (fun i j => (Int.natAbs (selW i * selW j) : Int)) 102 102 + 23 * 100000000 ≤
      1860 * 100000000 := by
  decide +kernel

lemma u1_250_card : ((range 251).filter (fun n => isU1B n = true)).card ≤ 23 := by
  decide +kernel

lemma selSumRow_eq (f : ℕ → ℕ → ℤ) (i m : ℕ) :
    ((selSumRow f i m : ℤ) : ℝ) = ∑ j ∈ range m, ((f i j : ℤ) : ℝ) := by
  induction m with
  | zero => simp [selSumRow]
  | succ m ih => rw [selSumRow, Int.cast_add, ih, sum_range_succ]

lemma selSum2D_eq (f : ℕ → ℕ → ℤ) (n m : ℕ) :
    ((selSum2D f n m : ℤ) : ℝ) = ∑ i ∈ range n, ∑ j ∈ range m, ((f i j : ℤ) : ℝ) := by
  induction n with
  | zero => simp [selSum2D]
  | succ n ih => rw [selSum2D, Int.cast_add, ih, selSumRow_eq, sum_range_succ]

lemma int_div_ceil_bound (num den K : ℤ) (hden : 0 < den) (hK : 0 < K) :
    (num : ℝ) / (den : ℝ) ≤ (((num * K + den - 1) / den : ℤ) : ℝ) / (K : ℝ) := by
  have hmod_lt : (num * K + den - 1) % den < den := Int.emod_lt_of_pos _ hden
  have hdiv := Int.mul_ediv_add_emod (num * K + den - 1) den
  have hleZ : num * K ≤ ((num * K + den - 1) / den) * den := by nlinarith
  have hleR : (num : ℝ) * (K : ℝ) ≤ (((num * K + den - 1) / den : ℤ) : ℝ) * (den : ℝ) := by
    exact_mod_cast hleZ
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_div_iff₀ hdenR hKR]
  linarith

lemma selberg_pair_bound (hi i j : ℕ) (hi102 : i < 102) (hj102 : j < 102) :
    ((selW i * selW j : ℤ) : ℝ) *
        ((((Icc 1 hi).filter (fun n => n % 4 = 1 ∧ selD i ∣ n ∧ selD j ∣ n)).card : ℕ) : ℝ) ≤
      (hi : ℝ) * (100000000 : ℝ) * (((selTermC i j : ℤ) : ℝ) / (100000000000000000000 : ℝ)) +
        ((Int.natAbs (selW i * selW j) : ℤ) : ℝ) := by
  obtain ⟨_, _, hprops⟩ := sel_props
  obtain ⟨hd1_pos, hd1_lt, hd1_odd, _⟩ := hprops i hi102
  obtain ⟨hd2_pos, hd2_lt, hd2_odd, _⟩ := hprops j hj102
  set d1 := selD i
  set d2 := selD j
  set L := Nat.lcm d1 d2
  have hL_pos : 0 < L := Nat.lcm_pos hd1_pos hd2_pos
  have hcop4prod : Nat.Coprime 4 (d1 * d2) := by
    change Nat.Coprime (2 ^ 2) (d1 * d2)
    apply Nat.Coprime.pow_left 2
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    have hm : (d1 * d2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
    rw [Nat.mul_mod, hd1_odd, hd2_odd] at hm
    norm_num at hm
  have hcop4L : Nat.Coprime 4 L :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul d1 d2) hcop4prod
  obtain ⟨t, ht_lt, hcrt⟩ := crt_class hcop4L (a := 1) (c := 0) (by norm_num) hL_pos
  have hset_eq : (Icc 1 hi).filter (fun n => n % 4 = 1 ∧ d1 ∣ n ∧ d2 ∣ n) =
      (Icc 1 hi).filter (fun n => n % (4 * L) = t) := by
    apply filter_congr; intro n _
    rw [hcrt n, ← Nat.lcm_dvd_iff, Nat.dvd_iff_mod_eq_zero]
  rw [hset_eq]
  set C : ℝ := ((((Icc 1 hi).filter (fun n => n % (4 * L) = t)).card : ℕ) : ℝ)
  have hmod := card_mod_eq_real hi (4 * L) t (by omega) ht_lt
  set w : ℝ := ((selW i * selW j : ℤ) : ℝ)
  have hw_abs : |w| = ((Int.natAbs (selW i * selW j) : ℤ) : ℝ) := by
    dsimp [w]
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
  have hwC : w * C ≤ w * ((hi : ℝ) / ((4 * L : ℕ) : ℝ)) + |w| := by
    have hdiff : |w * (C - (hi : ℝ) / ((4 * L : ℕ) : ℝ))| ≤ |w| * 1 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hmod (abs_nonneg w)
    have hle := le_abs_self (w * (C - (hi : ℝ) / ((4 * L : ℕ) : ℝ)))
    linarith
  have hgcd_lcm : (Nat.gcd d1 d2 : ℝ) * (L : ℝ) = (d1 : ℝ) * (d2 : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d1 d2
  have hgcdF : gcdF 250 d1 d2 = Nat.gcd d1 d2 := gcdF_eq 250 d1 d2 hd2_lt
  have hL_ne : (L : ℝ) ≠ 0 := by positivity
  have hd12_pos : (0 : ℝ) < (d1 : ℝ) * (d2 : ℝ) := by positivity
  have hmain_eq : w * ((hi : ℝ) / ((4 * L : ℕ) : ℝ)) =
      (hi : ℝ) * (100000000 : ℝ) *
        (((selW i * selW j * (gcdF 250 d1 d2 : ℤ) : ℤ) : ℝ) /
          (((400000000 * d1 * d2 : ℕ) : ℤ) : ℝ)) := by
    dsimp [w]
    rw [hgcdF]
    push_cast
    have hd1_ne : (d1 : ℝ) ≠ 0 := by positivity
    have hd2_ne : (d2 : ℝ) ≠ 0 := by positivity
    field_simp
    linear_combination (400000000 : ℝ) * (hi : ℝ) * ((selW i : ℝ) * (selW j : ℝ)) * hgcd_lcm.symm
  have hceil := int_div_ceil_bound
    (selW i * selW j * (gcdF 250 d1 d2 : ℤ))
    ((400000000 * d1 * d2 : ℕ) : ℤ)
    (100000000000000000000 : ℤ)
    (by exact_mod_cast (show 0 < 400000000 * d1 * d2 by positivity))
    (by norm_num)
  have hprod_le : (hi : ℝ) * (100000000 : ℝ) *
        (((selW i * selW j * (gcdF 250 d1 d2 : ℤ) : ℤ) : ℝ) /
          (((400000000 * d1 * d2 : ℕ) : ℤ) : ℝ)) ≤
      (hi : ℝ) * (100000000 : ℝ) * (((selTermC i j : ℤ) : ℝ) / (100000000000000000000 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [selTermC, d1, d2] using hceil
  linarith

theorem card_u1In_selberg_le (lo hi : ℕ) :
    ((u1In lo hi).card : ℝ) ≤ (69446 / 1000000 : ℝ) * hi + 1860 := by
  have hsub0 : u1In lo hi ⊆ u1In 0 hi := by
    intro p hp; simp only [u1In, mem_filter, mem_Ioc] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have h0_le : ((u1In lo hi).card : ℝ) ≤ ((u1In 0 hi).card : ℝ) := by
    exact_mod_cast card_le_card hsub0
  have hsplit := card_filter_add_card_filter_not (s := u1In 0 hi) (fun p => 250 < p)
  set Ubig := (u1In 0 hi).filter (fun p => 250 < p)
  set Usmall := (u1In 0 hi).filter (fun p => ¬ 250 < p)
  have hsmall_le : (Usmall.card : ℝ) ≤ 23 := by
    have hsubS : Usmall ⊆ (range 251).filter (fun n => isU1B n = true) := by
      intro p hp
      simp only [Usmall, u1In, mem_filter, mem_Ioc, mem_range] at hp ⊢
      exact ⟨by omega, isU1B_of_isU1 hp.1.2⟩
    have hc := (card_le_card hsubS).trans u1_250_card
    exact_mod_cast hc
  set S4 := (Icc 1 hi).filter (fun n => n % 4 = 1)
  have hUbig_sub : Ubig ⊆ S4 := by
    intro p hp
    simp only [Ubig, u1In, S4, mem_filter, mem_Ioc, mem_Icc] at hp ⊢
    exact ⟨⟨by omega, hp.1.1.2⟩, hp.1.2.2.1⟩
  let g : ℕ → ℝ := fun n => ∑ i ∈ range 102, if selD i ∣ n then ((selW i : ℤ) : ℝ) else 0
  have hg_prime : ∀ p ∈ Ubig, g p = 10000 := by
    intro p hp
    simp only [Ubig, u1In, mem_filter] at hp
    have hp_prime : p.Prime := hp.1.2.1
    have hp_gt : 250 < p := hp.2
    obtain ⟨hd0, hw0, hprops⟩ := sel_props
    have h0_in : (0 : ℕ) ∈ range 102 := by simp
    dsimp only [g]
    rw [← Finset.add_sum_erase _ _ h0_in]
    have hterm0 : (if selD 0 ∣ p then ((selW 0 : ℤ) : ℝ) else 0) = 10000 := by
      rw [hd0, hw0, if_pos (one_dvd p)]; norm_num
    have hrest : ∑ i ∈ (range 102).erase 0, (if selD i ∣ p then ((selW i : ℤ) : ℝ) else 0) = 0 := by
      apply sum_eq_zero; intro i hi_mem
      rw [mem_erase, mem_range] at hi_mem
      obtain ⟨_, hd_lt, _, hd_gt1⟩ := hprops i hi_mem.2
      have hd_gt1' := hd_gt1 (Nat.pos_of_ne_zero hi_mem.1)
      have hndvd : ¬ selD i ∣ p := by
        intro hdvd
        rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | hself <;> omega
      rw [if_neg hndvd]
    linarith
  have hsum_sq_lb : (100000000 : ℝ) * (Ubig.card : ℝ) ≤ ∑ n ∈ S4, (g n) ^ 2 := by
    calc (100000000 : ℝ) * (Ubig.card : ℝ)
        = ∑ _p ∈ Ubig, (100000000 : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ = ∑ p ∈ Ubig, (g p) ^ 2 := by
          apply sum_congr rfl; intro p hp; rw [hg_prime p hp]; norm_num
      _ ≤ ∑ n ∈ S4, (g n) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hUbig_sub (fun n _ _ => sq_nonneg (g n))
  have hsum_sq_eq : ∑ n ∈ S4, (g n) ^ 2 =
      ∑ i ∈ range 102, ∑ j ∈ range 102,
        ((selW i * selW j : ℤ) : ℝ) *
          ((((Icc 1 hi).filter (fun n => n % 4 = 1 ∧ selD i ∣ n ∧ selD j ∣ n)).card : ℕ) : ℝ) := by
    have hexp : ∀ n, (g n) ^ 2 = ∑ i ∈ range 102, ∑ j ∈ range 102,
        if selD i ∣ n ∧ selD j ∣ n then ((selW i * selW j : ℤ) : ℝ) else 0 := by
      intro n
      dsimp [g]
      rw [sq, sum_mul]
      apply sum_congr rfl; intro i _
      rw [mul_sum]
      apply sum_congr rfl; intro j _
      by_cases h1 : selD i ∣ n <;> by_cases h2 : selD j ∣ n <;> simp [h1, h2, Int.cast_mul]
    simp_rw [hexp]
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    rw [sum_comm]
    apply sum_congr rfl; intro j _
    rw [← sum_filter, filter_filter]
    simp [S4, mul_comm]
  have hsum_ub : ∑ i ∈ range 102, ∑ j ∈ range 102,
        ((selW i * selW j : ℤ) : ℝ) *
          ((((Icc 1 hi).filter (fun n => n % 4 = 1 ∧ selD i ∣ n ∧ selD j ∣ n)).card : ℕ) : ℝ) ≤
      (hi : ℝ) * (100000000 : ℝ) *
          (((selSum2D selTermC 102 102 : ℤ) : ℝ) / (100000000000000000000 : ℝ)) +
        ((selSum2D (fun i j => (Int.natAbs (selW i * selW j) : ℤ)) 102 102 : ℤ) : ℝ) := by
    have hpt : ∀ i ∈ range 102, ∑ j ∈ range 102,
          ((selW i * selW j : ℤ) : ℝ) *
            ((((Icc 1 hi).filter (fun n => n % 4 = 1 ∧ selD i ∣ n ∧ selD j ∣ n)).card : ℕ) : ℝ) ≤
        ∑ j ∈ range 102,
          ((hi : ℝ) * (100000000 : ℝ) * (((selTermC i j : ℤ) : ℝ) / (100000000000000000000 : ℝ)) +
            ((Int.natAbs (selW i * selW j) : ℤ) : ℝ)) := by
      intro i hi_m
      apply sum_le_sum; intro j hj_m
      exact selberg_pair_bound hi i j (mem_range.mp hi_m) (mem_range.mp hj_m)
    calc _ ≤ ∑ i ∈ range 102, ∑ j ∈ range 102,
          ((hi : ℝ) * (100000000 : ℝ) * (((selTermC i j : ℤ) : ℝ) / (100000000000000000000 : ℝ)) +
            ((Int.natAbs (selW i * selW j) : ℤ) : ℝ)) := sum_le_sum hpt
      _ = (hi : ℝ) * (100000000 : ℝ) *
            ((∑ i ∈ range 102, ∑ j ∈ range 102, ((selTermC i j : ℤ) : ℝ)) / (100000000000000000000 : ℝ)) +
          ∑ i ∈ range 102, ∑ j ∈ range 102, ((Int.natAbs (selW i * selW j) : ℤ) : ℝ) := by
          simp_rw [sum_add_distrib, ← mul_sum, ← sum_div]
      _ = _ := by rw [← selSum2D_eq, ← selSum2D_eq]
  have hmR : ((selSum2D selTermC 102 102 : ℤ) : ℝ) ≤ 69446 * (100000000000000 : ℝ) := by
    exact_mod_cast sel_main_ok
  have heR : ((selSum2D (fun i j => (Int.natAbs (selW i * selW j) : ℤ)) 102 102 : ℤ) : ℝ) +
      23 * 100000000 ≤ 1860 * 100000000 := by
    exact_mod_cast sel_err_ok
  have hsplitR : ((u1In 0 hi).card : ℝ) = (Ubig.card : ℝ) + (Usmall.card : ℝ) := by
    exact_mod_cast hsplit.symm
  have hhi0 : (0 : ℝ) ≤ hi := by positivity
  have hmain_scale : (hi : ℝ) * (100000000 : ℝ) *
      (((selSum2D selTermC 102 102 : ℤ) : ℝ) / (100000000000000000000 : ℝ)) ≤
      (100000000 : ℝ) * ((69446 / 1000000 : ℝ) * hi) := by
    have hdiv_le : (((selSum2D selTermC 102 102 : ℤ) : ℝ) / (100000000000000000000 : ℝ)) ≤
        69446 / 1000000 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    have := mul_le_mul_of_nonneg_left hdiv_le (show (0 : ℝ) ≤ (hi : ℝ) * 100000000 by positivity)
    linarith
  linarith

end ExtraPrimeBounds

lemma PM_pos : (1 : ℕ) ≤ PM := by unfold PM; norm_num

lemma S2_union_le (A B : Finset ℕ) : S2 (A ∪ B) ≤ S2 A + S2 B := by
  unfold S2
  have := sum_union_inter (s₁ := A) (s₂ := B) (f := fun p => 1 / ((p : ℝ) * p))
  have : 0 ≤ ∑ p ∈ A ∩ B, 1 / ((p : ℝ) * p) := sum_nonneg (fun p _ => by positivity)
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

theorem S2_primesIn_le (lo hi : ℕ) : S2 (primesIn lo hi) ≤ ((s2P tab lo hi : ℚ) : ℝ) := by
  unfold s2P
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact (S2_mono (primesIn_sub_accP lo hi)).trans (S2_accP_le lo hi)
  · push_cast
    have hsub : primesIn lo hi ⊆ accP lo PM ∪ primesIn PM hi := by
      intro p hp
      simp only [primesIn, accP, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isPrimeB_of_prime hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have e1 := S2_mono hsub
    have e2 := S2_union_le (accP lo PM) (primesIn PM hi)
    have e3 := S2_accP_le lo PM
    have e4 := S2_tail_le PM_pos (primesIn PM hi) hi (filter_subset _ _)
    linarith
  · push_cast
    exact S2_tail_le (show 1 ≤ lo by have := PM_pos; unfold PM at *; omega) (primesIn lo hi) hi
      (filter_subset _ _)

theorem S2_u1In_le (lo hi : ℕ) : S2 (u1In lo hi) ≤ ((s2U tab lo hi : ℚ) : ℝ) := by
  unfold s2U
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact (S2_mono (u1In_sub_accU lo hi)).trans (S2_accU_le lo hi)
  · push_cast
    have hsub : u1In lo hi ⊆ accU lo PM ∪ u1In PM hi := by
      intro p hp
      simp only [u1In, accU, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isU1B_of_isU1 hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have e1 := S2_mono hsub
    have e2 := S2_union_le (accU lo PM) (u1In PM hi)
    have e3 := S2_accU_le lo PM
    have e4 := S2_tail_le PM_pos (u1In PM hi) hi (filter_subset _ _)
    linarith
  · push_cast
    exact S2_tail_le (show 1 ≤ lo by have := PM_pos; unfold PM at *; omega) (u1In lo hi) hi
      (filter_subset _ _)

theorem card_primesIn_le (lo hi : ℕ) : ((primesIn lo hi).card : ℝ) ≤ ((cP tab lo hi : ℚ) : ℝ) := by
  unfold cP
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact_mod_cast (card_le_card (primesIn_sub_accP lo hi)).trans (card_accP_le lo hi)
  · push_cast
    have hsub : primesIn lo hi ⊆ accP lo PM ∪ primesIn PM hi := by
      intro p hp
      simp only [primesIn, accP, mem_filter, mem_Ioc, mem_union] at hp ⊢
      by_cases hpM : p ≤ PM
      · left; exact ⟨⟨hp.1.1, hpM⟩, isPrimeB_of_prime hp.2⟩
      · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    have hc : ((primesIn lo hi).card : ℝ) ≤ ((accP lo PM).card : ℝ) + ((primesIn PM hi).card : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (Finset.card_union_le _ _)
    have hacc : ((accP lo PM).card : ℝ) ≤ (((stAt PM).cp - (stAt lo).cp : ℕ) : ℝ) := by
      exact_mod_cast card_accP_le lo PM
    have hpm := card_primesIn_PM_le hi
    linarith
  · have hsub : primesIn lo hi ⊆ primesIn PM hi := by
      intro p hp; simp only [primesIn, mem_filter, mem_Ioc] at hp ⊢
      exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    exact (by exact_mod_cast card_le_card hsub : ((primesIn lo hi).card : ℝ) ≤ _).trans
      (card_primesIn_PM_le hi)

theorem card_u1In_le (lo hi : ℕ) : ((u1In lo hi).card : ℝ) ≤ ((cU tab lo hi : ℚ) : ℝ) := by
  unfold cU
  simp only [lookD_eq htab]
  split_ifs with h1 h2
  · push_cast
    exact_mod_cast (card_le_card (u1In_sub_accU lo hi)).trans (card_accU_le lo hi)
  · rw [Rat.cast_min]
    apply le_min
    · push_cast
      have hsub : u1In lo hi ⊆ accU lo PM ∪ primesIn PM hi := by
        intro p hp
        simp only [u1In, accU, primesIn, mem_filter, mem_Ioc, mem_union] at hp ⊢
        by_cases hpM : p ≤ PM
        · left; exact ⟨⟨hp.1.1, hpM⟩, isU1B_of_isU1 hp.2⟩
        · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2.1⟩
      have hc : ((u1In lo hi).card : ℝ) ≤ ((accU lo PM).card : ℝ) + ((primesIn PM hi).card : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans (Finset.card_union_le _ _)
      have hacc : ((accU lo PM).card : ℝ) ≤ (((stAt PM).cu - (stAt lo).cu : ℕ) : ℝ) := by
        exact_mod_cast card_accU_le lo PM
      have hpm := card_primesIn_PM_le hi
      linarith
    · push_cast
      exact card_u1In_selberg_le lo hi
  · rw [Rat.cast_min]
    apply le_min
    · have hsub : u1In lo hi ⊆ primesIn PM hi := by
        intro p hp; simp only [u1In, primesIn, mem_filter, mem_Ioc] at hp ⊢
        exact ⟨⟨by omega, hp.1.2⟩, hp.2.1⟩
      exact (by exact_mod_cast card_le_card hsub : ((u1In lo hi).card : ℝ) ≤ _).trans
        (card_primesIn_PM_le hi)
    · push_cast
      exact card_u1In_selberg_le lo hi

end

end Erdos848


namespace Erdos848

open Finset

noncomputable def resB (N q T z pc : ℕ) (excl : Finset ℕ) : ℝ :=
  T * ((N : ℝ) / q * (1 - ∏ p ∈ smallP z (· ∉ excl), (1 - 1 / ((p : ℝ) * p))) +
    ((2 : ℝ) ^ (smallP z (· ∉ excl)).card - 1) +
    ∑ p ∈ midP z pc (· ∉ excl), ((N : ℝ) / q / (p * p) + 1))

noncomputable def shB (N b pc Y : ℕ) : ℝ :=
  ∑ p ∈ midP pc Y (fun p => pc < p), ((N : ℝ) / (p * p) + 1) +
    rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2)

noncomputable def lemBB (N q T zB pB Y' : ℕ) : ℝ :=
  T * ((N : ℝ) / q * (1 - ∏ p ∈ smallP zB IsU1, (1 - 2 / ((p : ℝ) * p))) +
    ((3 : ℝ) ^ (smallP zB IsU1).card - 1) +
    ∑ p ∈ midP zB pB IsU1, (2 * ((N : ℝ) / q / (p * p)) + 2)) +
  ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
  ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y' + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ)

noncomputable def lemCB (N z₁ z₂ pB Y' pc : ℕ) (G : ℝ) : ℝ :=
  23 * ∑ p ∈ midP z₁ pB (fun p => IsU1 p ∧ z₁ < p), (2 * ((N : ℝ) / 25 / (p * p)) + 2) +
  ∑ p ∈ midP pB Y' (fun p => IsU1 p ∧ pB < p), (2 * ((N : ℝ) / (p * p)) + 2) +
  ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y' + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) +
  ((N : ℝ) / 25 * (1 - PU z₁) + ((3 : ℝ) ^ (smallP z₁ IsU1).card - 1)) +
  ∑ p ∈ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p z₁ +
  G +
  ∑ p ∈ midP z₂ pc (fun p => z₂ < p), ((N : ℝ) / (p * p) + 1)

lemma not25_star {a b : ℕ} (ha : a % 25 = 7 ∨ a % 25 = 18) (hb : IsStar b) :
    ¬ 5 * 5 ∣ a * b + 1 := by
  intro h
  have h0 : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
  rw [mod_mul_add_one] at h0
  have := Nat.mod_lt b (show 0 < 25 by norm_num)
  unfold IsStar at hb
  rcases ha with ha | ha <;> rw [ha] at h0 <;> interval_cases hr : b % 25 <;> omega

lemma not25_7_18 {a b : ℕ} (h : (a % 25 = 7 ∧ b % 25 = 18) ∨ (a % 25 = 18 ∧ b % 25 = 7)) :
    ¬ 5 * 5 ∣ a * b + 1 := by
  intro hd
  have h0 : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hd)
  rw [mod_mul_add_one] at h0
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h0 <;> norm_num at h0

lemma not4_even {a b : ℕ} (h : a % 2 = 0 ∨ b % 2 = 0) : ¬ 2 * 2 ∣ a * b + 1 := by
  intro hd
  have h2 : 2 ∣ a * b + 1 := dvd_trans ⟨2, rfl⟩ hd
  have : 2 ∣ a * b := by
    rcases h with h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) b
    · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) a
  omega

lemma not4_same {a b : ℕ} (h : (a % 4 = 1 ∧ b % 4 = 1) ∨ (a % 4 = 3 ∧ b % 4 = 3)) :
    ¬ 2 * 2 ∣ a * b + 1 := by
  intro hd
  have h0 : (a * b + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using hd)
  rw [mod_mul_add_one] at h0
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h0 <;> norm_num at h0

lemma coprime100 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) : Nat.Coprime 100 p := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have : p ∣ 2 ^ 2 * 5 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h'))

lemma coprime25 {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : Nat.Coprime 25 p := by
  have := (Nat.coprime_primes Nat.prime_five hp).mpr (Ne.symm h5)
  exact Nat.Coprime.pow_left 2 this

lemma coprime_U1 {p : ℕ} (hU : IsU1 p) : Nat.Coprime 100 p :=
  coprime100 hU.1 (by have := hU.2.2; omega) (by have := hU.2.2; omega)

lemma badCount_resB (N b q T z pc Y : ℕ) (Tset excl : Finset ℕ) (Pa : ℕ → Prop)
    [DecidablePred Pa] (hb : 1 ≤ b) (hY : 1 ≤ Y) (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q)
    (hTc : Tset.card = T) (hcop : ∀ p, p.Prime → p ∉ excl → Nat.Coprime q p)
    (hT : ∀ a, Pa a → a % q ∈ Tset) (hexcl : ∀ a, Pa a → ∀ p ∈ excl, ¬ p * p ∣ a * b + 1) :
    (badCount N Pa b : ℝ) ≤ resB N q T z pc excl + shB N b pc Y := by
  have := badCount_le N b q z pc Y Tset excl Pa hb hY hq hTq hcop hT hexcl
  unfold resB shB; rw [← hTc]; linarith

lemma vCount_lemBB (N q T zB pB Y' : ℕ) (Tset : Finset ℕ) (Px : ℕ → Prop) [DecidablePred Px]
    (hq : 0 < q) (hTq : ∀ t ∈ Tset, t < q) (hTc : Tset.card = T)
    (hcop : ∀ p, p.Prime → IsU1 p → Nat.Coprime q p)
    (hT : ∀ x, Px x → x % q ∈ Tset) (hstar : ∀ x, Px x → IsStar x) :
    (vCount N Px : ℝ) ≤ lemBB N q T zB pB Y' := by
  have := vCount_le N q zB pB Y' Tset Px hq hTq hcop hT hstar
  unfold lemBB; rw [← hTc]; linarith

lemma classCount_le (N : ℕ) (D : Finset ℕ) (hD : ∀ t ∈ D, t < 100) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ a, P a → a % 100 ∈ D) :
    (classCount N P : ℝ) ≤ D.card * ((N : ℝ) / 100) + D.card := by
  have h := card_mod_mem_real N 100 (by norm_num) D hD
  rw [abs_le] at h
  have hsub : classCount N P ≤ ((Icc 1 N).filter (fun a => a % 100 ∈ D)).card := by
    unfold classCount; apply card_le_card; intro a ha
    rw [mem_filter] at ha ⊢; exact ⟨ha.1, hP a ha.2⟩
  have : (classCount N P : ℝ) ≤ ((Icc 1 N).filter (fun a => a % 100 ∈ D)).card := by
    exact_mod_cast hsub
  push_cast at h
  linarith

theorem caseIb_real (N b b' z pc Y : ℕ) (hY : 1 ≤ Y) (hw : Witness N b) (h7 : b % 25 = 7)
    (hw' : Witness N b') (h18 : b' % 25 = 18) :
    (badCount N (fun a => a % 25 = 18) b : ℝ) + badCount N (fun a => a % 25 = 7) b' ≤
      (resB N 25 1 z pc {5} + shB N b pc Y) + (resB N 25 1 z pc {5} + shB N b' pc Y) := by
  have e1 := badCount_resB N b 25 1 z pc Y {18} {5} (fun a => a % 25 = 18) hw.1 hY (by norm_num)
    (by simp) (by simp) (fun p hp hne => coprime25 hp (by simpa using hne)) (by simp)
    (fun a ha p hp => by
      rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inr ⟨ha, h7⟩))
  have e2 := badCount_resB N b' 25 1 z pc Y {7} {5} (fun a => a % 25 = 7) hw'.1 hY (by norm_num)
    (by simp) (by simp) (fun p hp hne => coprime25 hp (by simpa using hne)) (by simp)
    (fun a ha p hp => by
      rw [mem_singleton] at hp; subst hp; exact not25_7_18 (Or.inl ⟨ha, h18⟩))
  linarith

theorem caseII_real (N b z pc Y z₁ z₂ pB Y' : ℕ) (G : ℝ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hbs : IsStar b) (hbe : b % 2 = 0) (h5 : 5 ≤ z₂)
    (hG : ∀ S ⊆ smallP z₂ (fun p => p ≠ 2 ∧ p ≠ 5), (∀ p ∈ S, IsU1 p) →
      (∏ p ∈ S, p) * (∏ p ∈ S, p) ≤ N * N + 1 → ∑ p ∈ S, gC N z₁ p ≤ G) :
    (badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b : ℝ) + lemCCount N b ≤
      resB N 25 2 z pc {2, 5} + lemCB N z₁ z₂ pB Y' pc G + shB N b pc Y := by
  classical
  set Tset : Finset ℕ := {7, 18}
  set Bset := (Icc 1 N).filter (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Squarefree (a * b + 1))
  set R := Tset.biUnion (fun t => resPart N b 25 t pc {2, 5})
  have hB := witness_cover N b 25 pc Y Tset {2, 5} (fun a => a % 25 = 7 ∨ a % 25 = 18)
    (fun a ha => by simp only [Tset, mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr hbe)
      · exact not25_star ha hbs)
  have hC := lemC_cover N b z₁ z₂ pB Y' pc Y hbe
  have hdisj : Disjoint Bset (lemCSet N b) := by
    rw [disjoint_left]; intro a ha hc
    simp only [Bset, lemCSet, mem_filter] at ha hc
    unfold IsStar at hc; omega
  have hsub : Bset ∪ lemCSet N b ⊆ ((R ∪ lemCPart N b z₁ z₂ pB Y' pc) ∪ midSet N b pc Y) ∪
      exSet N b Y := by
    intro a ha
    rcases mem_union.mp ha with h | h
    · have := hB h
      simp only [mem_union] at this ⊢; tauto
    · have := hC h
      simp only [mem_union] at this ⊢; tauto
  have hcard : Bset.card + (lemCSet N b).card ≤ R.card + (lemCPart N b z₁ z₂ pB Y' pc).card +
      (midSet N b pc Y).card + (exSet N b Y).card := by
    rw [← card_union_of_disjoint hdisj]
    have a0 := card_le_card hsub
    have a1 := Finset.card_union_le ((R ∪ lemCPart N b z₁ z₂ pB Y' pc) ∪ midSet N b pc Y)
      (exSet N b Y)
    have a2 := Finset.card_union_le (R ∪ lemCPart N b z₁ z₂ pB Y' pc) (midSet N b pc Y)
    have a3 := Finset.card_union_le R (lemCPart N b z₁ z₂ pB Y' pc)
    omega
  have hcardR : (badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b : ℝ) + lemCCount N b ≤
      (R.card : ℝ) + (lemCPart N b z₁ z₂ pB Y' pc).card + (midSet N b pc Y).card +
        (exSet N b Y).card := by
    have : badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount N b ≤ R.card +
        (lemCPart N b z₁ z₂ pB Y' pc).card + (midSet N b pc Y).card + (exSet N b Y).card :=
      hcard
    exact_mod_cast this
  have hR : (R.card : ℝ) ≤ resB N 25 2 z pc {2, 5} := by
    have h1 : (R.card : ℝ) ≤ ∑ t ∈ Tset, ((resPart N b 25 t pc {2, 5}).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 := sum_le_sum (fun t (ht : t ∈ Tset) => card_resPart_le N b 25 t z pc {2, 5}
      (by norm_num) (by simp only [Tset, mem_insert, mem_singleton] at ht; omega)
      (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)))
    rw [sum_const, show Tset.card = 2 by decide, nsmul_eq_mul] at h2
    unfold resB; push_cast at h2 ⊢; linarith
  have hCP := card_lemCPart_le N b z₁ z₂ pB Y' pc G hw.2.1 hbs h5 hG
  have hmid := card_midSet_le N b pc Y
  have hex := card_exSet_le N b Y hw.1 hY
  unfold lemCB shB
  linarith

def T50 : Finset ℕ := (range 50).filter (fun t => t % 2 = 1 ∧ t % 25 ≠ 7 ∧ t % 25 ≠ 18)

def T100 (r : ℕ) : Finset ℕ := (range 100).filter (fun t => t % 25 ≠ 7 ∧ t % 25 ≠ 18 ∧ t % 4 = r)

lemma T100_card {r : ℕ} (hr : r = 1 ∨ r = 3) : (T100 r).card = 23 := by
  rcases hr with rfl | rfl <;> decide

lemma vCount_III2 (N zB pB Y' r : ℕ) (hr : r = 1 ∨ r = 3) :
    (vCount N (fun x => IsStar x ∧ x % 4 = r) : ℝ) ≤ lemBB N 100 23 zB pB Y' :=
  vCount_lemBB N 100 23 zB pB Y' (T100 r) _ (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) (T100_card hr)
    (fun p _ hU => coprime_U1 hU)
    (fun x hx => by
      unfold IsStar at hx
      simp only [T100, mem_filter, mem_range]; omega)
    (fun x hx => hx.1)

theorem caseIII1_real (N b₁ b₃ z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y)
    (hw₁ : Witness N b₁) (hs₁ : IsStar b₁) (hr₁ : b₁ % 4 = 1)
    (hw₃ : Witness N b₃) (hs₃ : IsStar b₃) (hr₃ : b₃ % 4 = 3) :
    (badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ : ℝ) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
      vCount N (fun x => IsStar x ∧ x % 2 = 1) ≤
      (resB N 100 6 z pc {2, 5} + shB N b₁ pc Y) + (resB N 100 2 z pc {2, 5} + shB N b₃ pc Y) +
        lemBB N 50 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  have e1 := badCount_resB N b₁ 100 6 z pc Y {32, 57, 82, 18, 68, 93} {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) hw₁.1 hY
    (by norm_num) (by simp) (by decide) hcop
    (fun a ha => by simp only [mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · exact not4_same (Or.inl ⟨h, hr₁⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star ha.1 hs₁)
  have e3 := badCount_resB N b₃ 100 2 z pc Y {7, 43} {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) hw₃.1 hY
    (by norm_num) (by simp) (by decide) hcop
    (fun a ha => by simp only [mem_insert, mem_singleton]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_same (Or.inr ⟨ha.2, hr₃⟩)
      · exact not25_star ha.1 hs₃)
  have ev := vCount_lemBB N 50 23 zB pB Y' T50 (fun x => IsStar x ∧ x % 2 = 1) (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) (by decide)
    (fun p _ hU => Nat.Coprime.coprime_dvd_left (by norm_num) (coprime_U1 hU))
    (fun x hx => by
      have := hx.1; unfold IsStar at this
      simp only [T50, mem_filter, mem_range]; omega)
    (fun x hx => hx.1)
  linarith

theorem caseIII2a_real (N b r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3) :
    (classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      (2 * ((N : ℝ) / 100) + 2) + (resB N 100 2 z pc {2, 5} + shB N b pc Y) +
        lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ t % 4 = 4 - r)
  have hD : D.card = 2 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => (t % 25 = 7 ∨ t % 25 = 18) ∧ t % 4 = r)
  have hTs : Ts.card = 2 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 2 z pc Y Ts {2, 5}
    (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases hr with rfl | rfl
        · exact not4_same (Or.inl ⟨ha.2, hbr⟩)
        · exact not4_same (Or.inr ⟨ha.2, hbr⟩)
      · exact not25_star ha.1 hs)
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

theorem caseIII2b7_real (N b b' r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hw' : Witness N b') (h7 : b' % 25 = 7) (he : b' % 2 = 0) :
    (classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 18) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      ((N : ℝ) / 100 + 1) + (resB N 100 3 z pc {2, 5} + shB N b pc Y) +
        (resB N 25 1 z pc {2, 5} + shB N b' pc Y) + lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => t % 25 = 7 ∧ t % 4 = 4 - r)
  have hD : D.card = 1 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => a % 25 = 7 ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => t % 25 = 7 ∧ (t % 4 = r ∨ t % 2 = 0))
  have hTs : Ts.card = 3 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 3 z pc Y Ts {2, 5}
    (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · rcases hr with rfl | rfl
          · exact not4_same (Or.inl ⟨h, hbr⟩)
          · exact not4_same (Or.inr ⟨h, hbr⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star (Or.inl ha.1) hs)
  have eb' := badCount_resB N b' 25 1 z pc Y {18} {2, 5} (fun a => a % 25 = 18) hw'.1 hY
    (by norm_num) (by simp) (by simp)
    (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)) (by simp)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr he)
      · exact not25_7_18 (Or.inr ⟨ha, h7⟩))
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

theorem caseIII2b18_real (N b b' r z pc Y zB pB Y' : ℕ) (hY : 1 ≤ Y) (hw : Witness N b)
    (hs : IsStar b) (hbr : b % 4 = r) (hr : r = 1 ∨ r = 3)
    (hw' : Witness N b') (h18 : b' % 25 = 18) (he : b' % 2 = 0) :
    (classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) : ℝ) +
      badCount N (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 7) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = r) ≤
      ((N : ℝ) / 100 + 1) + (resB N 100 3 z pc {2, 5} + shB N b pc Y) +
        (resB N 25 1 z pc {2, 5} + shB N b' pc Y) + lemBB N 100 23 zB pB Y' := by
  have hcop : ∀ p, p.Prime → p ∉ ({2, 5} : Finset ℕ) → Nat.Coprime 100 p := fun p hp hne => by
    simp at hne; exact coprime100 hp hne.1 hne.2
  set D := (range 100).filter (fun t => t % 25 = 18 ∧ t % 4 = 4 - r)
  have hD : D.card = 1 := by rcases hr with rfl | rfl <;> decide
  have ec := classCount_le N D (fun t ht => mem_range.mp (mem_filter.mp ht).1)
    (fun a => a % 25 = 18 ∧ a % 4 = 4 - r)
    (fun a ha => by simp only [D, mem_filter, mem_range]; omega)
  rw [hD] at ec
  set Ts := (range 100).filter (fun t => t % 25 = 18 ∧ (t % 4 = r ∨ t % 2 = 0))
  have hTs : Ts.card = 3 := by rcases hr with rfl | rfl <;> decide
  have eb := badCount_resB N b 100 3 z pc Y Ts {2, 5}
    (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) hw.1 hY (by norm_num)
    (fun t ht => mem_range.mp (mem_filter.mp ht).1) hTs hcop
    (fun a ha => by simp only [Ts, mem_filter, mem_range]; omega)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · rcases ha.2 with h | h
        · rcases hr with rfl | rfl
          · exact not4_same (Or.inl ⟨h, hbr⟩)
          · exact not4_same (Or.inr ⟨h, hbr⟩)
        · exact not4_even (Or.inl h)
      · exact not25_star (Or.inr ha.1) hs)
  have eb' := badCount_resB N b' 25 1 z pc Y {7} {2, 5} (fun a => a % 25 = 7) hw'.1 hY
    (by norm_num) (by simp) (by simp)
    (fun p hp hne => coprime25 hp (by simp at hne; exact hne.2)) (by simp)
    (fun a ha p hp => by
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact not4_even (Or.inr he)
      · exact not25_7_18 (Or.inl ⟨ha, h18⟩))
  have ev := vCount_III2 N zB pB Y' r hr
  push_cast at ec
  linarith

end Erdos848


namespace Erdos848

open Finset ErdosComp

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
    ·
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

lemma isU1B_iff (n : ℕ) : isU1B n = true ↔ IsU1 n := by
  unfold isU1B IsU1
  simp only [Bool.and_eq_true, isPrimeB_iff, beq_iff_eq, decide_eq_true_eq]
  tauto

lemma prodF_eq (cond : ℕ → Bool) (f : ℕ → ℚ) (n : ℕ) :
    prodF cond f n = ∏ p ∈ (range n).filter (fun p => cond p = true), f p := by
  induction n with
  | zero => simp [prodF]
  | succ n ih =>
    rw [prodF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [prod_insert (by simp), mul_comm]
    · rw [mul_one]

lemma sumF_eq (cond : ℕ → Bool) (f : ℕ → ℚ) (n : ℕ) :
    sumF cond f n = ∑ p ∈ (range n).filter (fun p => cond p = true), f p := by
  induction n with
  | zero => simp [sumF]
  | succ n ih =>
    rw [sumF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [sum_insert (by simp), add_comm]
    · rw [add_zero]

lemma cntF_eq (cond : ℕ → Bool) (n : ℕ) :
    cntF cond n = ((range n).filter (fun p => cond p = true)).card := by
  induction n with
  | zero => simp [cntF]
  | succ n ih =>
    rw [cntF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
    · rw [add_zero]

lemma smallP_excl5 : smallP 31 (· ∉ ({5} : Finset ℕ)) =
    (range 32).filter (fun p => condP [5] p = true) := by
  ext p; simp [smallP, condP, isPrimeB_iff]

lemma smallP_excl25 : smallP 31 (· ∉ ({2, 5} : Finset ℕ)) =
    (range 32).filter (fun p => condP [2, 5] p = true) := by
  ext p; simp [smallP, condP, isPrimeB_iff]

lemma smallP_U : smallP 41 IsU1 = (range 42).filter (fun p => isU1B p = true) := by
  ext p; simp only [smallP, mem_filter, isU1B_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2⟩⟩

lemma smallP_U_erase (p : ℕ) :
    (smallP 41 IsU1).erase p = (range 42).filter (fun q => condE p q = true) := by
  rw [smallP_U]; ext q
  simp only [mem_erase, mem_filter, condE, Bool.and_eq_true, bne_iff_ne]
  tauto

lemma smallP_odd : smallP 1000 (fun p => p ≠ 2 ∧ p ≠ 5) =
    (range 1001).filter (fun p => condOdd p = true) := by
  ext p
  simp only [smallP, mem_filter, condOdd, Bool.and_eq_true, bne_iff_ne, isPrimeB_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

lemma OPc_eq : OPc = OP := by decide

lemma primeProdC_eq (k : ℕ) : primeProdC k = primeProd k := by
  unfold primeProdC primeProd; rw [OPc_eq]

lemma primeProd_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 45) : primeProd j ≤ primeProd k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]
    · rw [primeProd_succ (by omega)]
      have h1 : 1 ≤ OP[k]! := by
        have : ∀ k < 45, 1 ≤ OP[k]! := by decide
        exact this k (by omega)
      calc primeProd j ≤ primeProd k := ih (by omega) (by omega)
        _ ≤ primeProd k * OP[k]! := Nat.le_mul_of_pos_right _ h1

lemma countP_range_ge (P : ℕ → Bool) : ∀ n k, k ≤ n → (∀ j < k, P j = true) →
    k ≤ (List.range n).countP P := by
  intro n
  induction n with
  | zero => intro k hk _; omega
  | succ n ih =>
    intro k hk hP
    rw [List.range_succ, List.countP_append]
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · have := ih k (by omega) hP; omega
    · have hk' : k = n + 1 := by omega
      have := ih n le_rfl (fun j hj => hP j (by omega))
      have hn : P n = true := hP n (by omega)
      simp [hn]; omega

lemma le_Wc {k L : ℕ} (hk : k ≤ 45) (h : primeProd k ≤ L) : k ≤ Wc L := by
  unfold Wc
  rw [← List.countP_eq_length_filter]
  apply countP_range_ge _ 45 k hk
  intro j hj
  simp only [decide_eq_true_eq, primeProdC_eq]
  exact (primeProd_mono (by omega) hk).trans h

lemma W_le_Wc (L : ℕ) : W L ≤ Wc L := by
  rcases Nat.eq_zero_or_pos (W L) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hP : primeProd (W L) ≤ L :=
      Nat.findGreatest_of_ne_zero (P := fun k => primeProd k ≤ L) (n := 45) rfl
        (Nat.pos_iff_ne_zero.mp hpos)
    exact le_Wc (Nat.findGreatest_le 45) hP

lemma rhoMax_le_rhoMaxC (N : ℕ) : rhoMax N ≤ rhoMaxC N := by
  unfold rhoMax rhoMaxC
  have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc N)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc (N / 4))
  have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc (N / 8))
  omega

lemma rhoBound_le_C {b Nhi : ℕ} (hb : 1 ≤ b) (hbN : b ≤ Nhi) (hN : Nhi < primeProdC 45) :
    rhoBound b ≤ rhoMaxC Nhi :=
  (rhoBound_le_rhoMax hb hbN (by rw [← primeProdC_eq]; exact hN)).trans (rhoMax_le_rhoMaxC Nhi)

lemma log3Go_ge (n : ℕ) : ∀ f k, k ≤ log3Go n f k := by
  intro f
  induction f with
  | zero => intro k; simp [log3Go]
  | succ f ih =>
    intro k; simp only [log3Go]; split_ifs
    · exact (Nat.le_succ k).trans (ih (k + 1))
    · exact le_rfl

lemma log3Go_reach (n m : ℕ) (hm : 3 ^ m ≤ n) : ∀ f k, k ≤ m → m ≤ k + f → m ≤ log3Go n f k := by
  intro f
  induction f with
  | zero => intro k hk hkf; simp only [log3Go]; omega
  | succ f ih =>
    intro k hk hkf
    simp only [log3Go]
    rcases Nat.lt_or_ge k m with hlt | hge
    · have : 3 ^ (k + 1) ≤ n := (Nat.pow_le_pow_right (by norm_num) hlt).trans hm
      simp only [this, ↓reduceIte]; exact ih (k + 1) hlt (by omega)
    · split_ifs
      · exact (show m ≤ k + 1 by omega).trans (log3Go_ge n f (k + 1))
      · omega

lemma log_le_log3C {N Nhi : ℕ} (h : N ≤ Nhi) : Nat.log 3 N ≤ log3C Nhi := by
  have hmono : Nat.log 3 N ≤ Nat.log 3 Nhi := Nat.log_mono_right h
  refine hmono.trans ?_
  rcases Nat.eq_zero_or_pos Nhi with h0 | hpos
  · subst h0; simp
  have hm : 3 ^ Nat.log 3 Nhi ≤ Nhi := Nat.pow_log_le_self 3 (by omega)
  have hmn : Nat.log 3 Nhi ≤ Nhi := (Nat.lt_pow_self (by norm_num)).le.trans hm
  exact log3Go_reach Nhi _ hm Nhi 0 (Nat.zero_le _) (by omega)


lemma pellAdmM_mono {a b : ℕ} (h : a ≤ b) : ErdosComp.pellAdmM a ≤ ErdosComp.pellAdmM b := by
  unfold ErdosComp.pellAdmM
  exact min_le_min h (Nat.mul_le_mul_left 36 (Nat.add_le_add_right (Nat.div_le_div_right h) 1))

lemma pell_le_pellC {N Nhi : ℕ} (h : N ≤ Nhi) (Y : ℕ) :
    ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) ≤ pellC Nhi Y := by
  unfold pellC
  apply Nat.mul_le_mul
  · apply pellAdmM_mono
    rw [sq, sq]; apply Nat.div_le_div_right; exact Nat.add_le_add_right (Nat.mul_le_mul h h) 1
  · exact Nat.add_le_add_right (log_le_log3C h) 1

lemma OPNo5c_eq : OPNo5c = OPNo5 := by decide

lemma primeProdNo5C_eq (k : ℕ) : primeProdNo5C k = primeProdNo5 k := by
  unfold primeProdNo5C primeProdNo5; rw [OPNo5c_eq]

lemma primeProdNo5_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 44) :
    primeProdNo5 j ≤ primeProdNo5 k := by
  induction k with
  | zero => exact Nat.eq_zero_of_le_zero hjk ▸ le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]
    · rw [primeProdNo5_succ (by omega)]
      have h1 : 1 ≤ OPNo5[k]! := by
        have : ∀ k < 44, 1 ≤ OPNo5[k]! := by decide
        exact this k (by omega)
      calc primeProdNo5 j ≤ primeProdNo5 k := ih (by omega) (by omega)
        _ ≤ primeProdNo5 k * OPNo5[k]! := Nat.le_mul_of_pos_right _ h1

lemma le_WcNo5 {k L : ℕ} (hk : k ≤ 44) (h : primeProdNo5 k ≤ L) : k ≤ WcNo5 L := by
  unfold WcNo5
  rw [← List.countP_eq_length_filter]
  apply countP_range_ge _ 44 k hk
  intro j hj
  simp only [decide_eq_true_eq, primeProdNo5C_eq]
  exact (primeProdNo5_mono (by omega) hk).trans h

lemma WNo5_le_WcNo5 (L : ℕ) : WNo5 L ≤ WcNo5 L := by
  rcases Nat.eq_zero_or_pos (WNo5 L) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hP : primeProdNo5 (WNo5 L) ≤ L :=
      Nat.findGreatest_of_ne_zero (P := fun k => primeProdNo5 k ≤ L) (n := 44) rfl
        (Nat.pos_iff_ne_zero.mp hpos)
    exact le_WcNo5 (Nat.findGreatest_le 44) hP

lemma rhoMaxNo5_le_rhoNo5C (N : ℕ) : rhoMaxNo5 N ≤ rhoNo5C N := by
  unfold rhoMaxNo5 rhoNo5C
  have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (WNo5_le_WcNo5 N)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (WNo5_le_WcNo5 (N / 4))
  have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (WNo5_le_WcNo5 (N / 8))
  omega

lemma rhoBound_le_no5C {b Nhi : ℕ} (hb : 1 ≤ b) (hbN : b ≤ Nhi) (h5 : ¬ 5 ∣ b)
    (hN : Nhi < primeProdNo5C 44) : rhoBound b ≤ rhoNo5C Nhi :=
  (rhoBound_le_rhoMaxNo5 hb hbN h5 (by rw [← primeProdNo5C_eq]; exact hN)).trans
    (rhoMaxNo5_le_rhoNo5C Nhi)

lemma rhoBound_le_oddC {b Nhi : ℕ} (hb : 1 ≤ b) (hbN : b ≤ Nhi) (hodd : b % 2 = 1)
    (hN : Nhi < primeProdC 45) : rhoBound b ≤ rhoOddC Nhi := by
  unfold rhoBound twoFactor rhoOddC
  rw [oddOmega_eq]
  have h8 : ¬ 8 ∣ b := fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega
  have h4 : ¬ 4 ∣ b := fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega
  rw [if_neg h8, if_neg h4, one_mul]
  have hP : (∏ p ∈ oddPF b, p) ≤ Nhi := (Nat.le_of_dvd (by omega) (prod_oddPF_dvd b)).trans hbN
  have hcard := card_oddPF_le hP (by rwa [← primeProdC_eq])
  exact Nat.pow_le_pow_right (by norm_num) (hcard.trans (W_le_Wc Nhi))

lemma UL_spec : ∀ j < 30, isU1B (UL.getD j 0) = true ∧ cntF isU1B (UL.getD j 0) = j := by
  decide +kernel

lemma count_U1_eq (n : ℕ) : Nat.count IsU1 n = cntF isU1B n := by
  rw [Nat.count_eq_card_filter_range, cntF_eq]
  congr 1; apply filter_congr; intro p _; rw [isU1B_iff]

lemma u1_eq_UL {j : ℕ} (hj : j < 30) : u1 j = UL.getD j 0 := by
  obtain ⟨h1, h2⟩ := UL_spec j hj
  have hU : IsU1 (UL.getD j 0) := (isU1B_iff _).mp h1
  unfold u1
  conv_lhs => rw [← h2, ← count_U1_eq]
  exact Nat.nth_count hU

lemma prod1_cast (excl : List ℕ) :
    ((prod1 excl : ℚ) : ℝ) = ∏ p ∈ (range 32).filter (fun p => condP excl p = true),
      (1 - 1 / ((p : ℝ) * p)) := by
  unfold prod1; rw [prodF_eq]; push_cast; rfl

lemma k1_eq (excl : List ℕ) : k1 excl = ((range 32).filter (fun p => condP excl p = true)).card := by
  unfold k1; rw [cntF_eq]

lemma prodU_cast : ((prodU : ℚ) : ℝ) = PU 41 := by
  unfold prodU PU; rw [prodF_eq, smallP_U]; push_cast; rfl

lemma kU_eq : kU = (smallP 41 IsU1).card := by unfold kU; rw [cntF_eq, smallP_U]

lemma prErase_cast (p : ℕ) : ((prErase p : ℚ) : ℝ) =
    ∏ q ∈ (smallP 41 IsU1).erase p, (1 - 2 / ((q : ℝ) * q)) := by
  unfold prErase; rw [prodF_eq, smallP_U_erase]; push_cast; rfl

lemma kErase_eq (p : ℕ) : kErase p = ((smallP 41 IsU1).erase p).card := by
  unfold kErase; rw [cntF_eq, smallP_U_erase]

lemma prErase_nonneg (p : ℕ) : (0 : ℝ) ≤ ((prErase p : ℚ) : ℝ) := by
  rw [prErase_cast]
  apply prod_nonneg; intro q hq
  exact (factor_pos (mem_filter.mp (mem_of_mem_erase hq)).2.1).le

lemma gC_eq (N p : ℕ) : gC N 41 p = ((gA p : ℚ) : ℝ) * N + ((gE p : ℚ) : ℝ) := by
  unfold gC wholeB nonB gA gE
  push_cast
  rw [prErase_cast, kErase_eq]
  ring

lemma sumNon_eq (N : ℕ) : ∑ p ∈ smallP 1000 (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p 41 =
    ((cNon : ℚ) : ℝ) * N + ((eNon : ℚ) : ℝ) := by
  unfold cNon eNon
  rw [sumF_eq, sumF_eq, smallP_odd]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl; intro p _
  unfold nonB
  rw [← prErase_cast, ← kErase_eq]
  ring

lemma midsum_le (P S : Finset ℕ) (hPS : P ⊆ S) (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) ≤ a * S2 S + S.card := by
  have h1 : ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) = a * S2 P + P.card := by
    unfold S2; rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one]
    congr 1; apply sum_congr rfl; intro p _; ring
  have h2 : S2 P ≤ S2 S := S2_mono hPS
  have h3 : (P.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hPS
  rw [h1]; nlinarith

lemma midP_sub_primesIn (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    midP z w Q ⊆ primesIn z w := fun p hp => by
  simp only [midP, primesIn, mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩

lemma midP_sub_u1In (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p) :
    midP z w Q ⊆ u1In z w := fun p hp => by
  simp only [midP, u1In, mem_filter] at hp ⊢; exact ⟨hp.1, hQ p hp.2.2⟩

lemma sum_two (P : Finset ℕ) (a : ℝ) :
    ∑ p ∈ P, (2 * (a / ((p : ℝ) * p)) + 2) = 2 * ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) := by
  rw [mul_sum]; apply sum_congr rfl; intro p _; ring

lemma gmax_le (a e : ℝ) (ha : 0 ≤ a) {N Nlo : ℝ} (h : Nlo ≤ N) :
    max (a * N + e) 0 ≤ a * N + max e (-a * Nlo) := by
  rcases le_total 0 (a * N + e) with h0 | h0
  · rw [max_eq_left h0]; linarith [le_max_left e (-a * Nlo)]
  · rw [max_eq_right h0]
    have := le_max_right e (-a * Nlo)
    nlinarith

lemma gA_nonneg (p : ℕ) : (0 : ℝ) ≤ ((gA p : ℚ) : ℝ) := by
  unfold gA; push_cast
  have := prErase_nonneg p
  positivity

lemma gsum_sound (N Nlo L : ℕ) (hL : L ≤ 30) (hN : Nlo ≤ N) :
    ∑ j ∈ range L, max (gC N 41 (u1 j)) 0 ≤
      ((gSumC L : ℚ) : ℝ) * N + ((gSumE Nlo L : ℚ) : ℝ) := by
  unfold gSumC gSumE
  rw [sumF_eq, sumF_eq]
  have hf : (range L).filter (fun _ => true = true) = range L := filter_true_of_mem (fun _ _ => rfl)
  rw [hf]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_le_sum; intro j hj
  have hj30 : j < 30 := by have := mem_range.mp hj; omega
  rw [u1_eq_UL hj30, gC_eq]
  have := gmax_le ((gA (UL.getD j 0) : ℚ) : ℝ) ((gE (UL.getD j 0) : ℚ) : ℝ) (gA_nonneg _)
    (show (Nlo : ℝ) ≤ N by exact_mod_cast hN)
  push_cast at this
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

lemma primeSum_le (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((s2P tab z w : ℚ) : ℝ) + ((cP tab z w : ℚ) : ℝ) := by
  have := midsum_le _ _ (midP_sub_primesIn z w Q) a ha
  have h1 := S2_primesIn_le htab z w
  have h2 := card_primesIn_le htab z w
  nlinarith

lemma u1Sum_le (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p)
    (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((s2U tab z w : ℚ) : ℝ) + ((cU tab z w : ℚ) : ℝ) := by
  have := midsum_le _ _ (midP_sub_u1In z w Q hQ) a ha
  have h1 := S2_u1In_le htab z w
  have h2 := card_u1In_le htab z w
  nlinarith

lemma res_sound (N q T pc : ℕ) (excl : Finset ℕ) (exclL : List ℕ)
    (hS : smallP 31 (· ∉ excl) = (range 32).filter (fun p => condP exclL p = true)) :
    resB N q T 31 pc excl ≤
      ((resCE tab q T exclL pc).1 : ℝ) * N + ((resCE tab q T exclL pc).2 : ℝ) := by
  unfold resB resCE
  have hm := primeSum_le htab 31 pc (· ∉ excl) ((N : ℝ) / q) (by positivity)
  have hT : (0 : ℝ) ≤ T := by positivity
  have := mul_le_mul_of_nonneg_left hm hT
  dsimp only
  push_cast
  rw [prod1_cast, k1_eq, ← hS]
  linear_combination this

lemma sh_sound (N Nhi b pc Y : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N) (hN : N ≤ Nhi)
    (hNhi : Nhi < primeProdC 45) (hY : 1 ≤ Y) :
    shB N b pc Y ≤ ((shCE tab Nhi pc Y).1 : ℝ) * N + ((shCE tab Nhi pc Y).2 : ℝ) := by
  unfold shB shCE shCEWith
  have hm := primeSum_le htab pc Y (fun p => pc < p) (N : ℝ) (by positivity)
  have hρ : (rhoBound b : ℝ) ≤ rhoMaxC Nhi := by exact_mod_cast rhoBound_le_C hb (hbN.trans hN) hNhi
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hNR : (N : ℝ) ≤ Nhi := by exact_mod_cast hN
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hNb : (N : ℝ) * b ≤ (Nhi : ℝ) * Nhi := by
    have : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have hG : 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 ≤
      2 * ((Nhi : ℝ) + 1) / Y + ((Nhi : ℝ) * Nhi + 1) / ((Y : ℝ) * Y) := by
    rw [sq]
    have hY0 : (0 : ℝ) < Y := by linarith
    gcongr
  have hG0 : 0 ≤ 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 := by positivity
  have hρ0 : (0 : ℝ) ≤ rhoBound b := by positivity
  have := mul_le_mul hρ hG hG0 (by positivity)
  dsimp only
  push_cast
  linarith

lemma lemB_sound (N Nhi q T pB YB : ℕ) (hN : N ≤ Nhi) :
    lemBB N q T 41 pB YB ≤
      ((lemBCE tab Nhi q T pB YB).1 : ℝ) * N + ((lemBCE tab Nhi q T pB YB).2 : ℝ) := by
  unfold lemBB lemBCE
  have h1 := u1Sum_le htab 41 pB IsU1 (fun _ h => h) ((N : ℝ) / q) (by positivity)
  have h2 := u1Sum_le htab pB YB (fun p => IsU1 p ∧ pB < p) (fun _ h => h.1) (N : ℝ)
    (by positivity)
  have hp : ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (YB + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ (pellC Nhi YB : ℝ) := by
    exact_mod_cast pell_le_pellC hN YB
  rw [sum_two, sum_two]
  have hT : (0 : ℝ) ≤ T := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hT
  dsimp only
  push_cast
  rw [prodU_cast, kU_eq]
  unfold PU
  push_cast at hp
  linear_combination 2 * h1' + 2 * h2 + hp

lemma lemC_sound (N Nlo Nhi pB YB pc L : ℕ) (hL : L ≤ 30) (h1 : Nlo ≤ N) (h2 : N ≤ Nhi) :
    lemCB N 41 1000 pB YB pc (∑ j ∈ range L, max (gC N 41 (u1 j)) 0) ≤
      ((lemCCE tab Nlo Nhi pB YB pc L).1 : ℝ) * N + ((lemCCE tab Nlo Nhi pB YB pc L).2 : ℝ) := by
  unfold lemCB lemCCE
  have e1 := u1Sum_le htab 41 pB (fun p => IsU1 p ∧ 41 < p) (fun _ h => h.1) ((N : ℝ) / 25)
    (by positivity)
  have e2 := u1Sum_le htab pB YB (fun p => IsU1 p ∧ pB < p) (fun _ h => h.1) (N : ℝ)
    (by positivity)
  have e3 : ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (YB + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ (pellC Nhi YB : ℝ) := by
    exact_mod_cast pell_le_pellC h2 YB
  have e4 := sumNon_eq N
  have e5 := gsum_sound N Nlo L hL h1
  have e6 := primeSum_le htab 1000 pc (fun p => 1000 < p) (N : ℝ) (Nat.cast_nonneg N)
  rw [sum_two, sum_two]
  dsimp only
  push_cast
  rw [prodU_cast, kU_eq]
  push_cast at e3 e5
  linear_combination 46 * e1 + 2 * e2 + e3 + e4 + e5 + e6

end

lemma addCE_le {a b : CE} {N : ℕ} {X Y : ℝ} (hX : X ≤ (a.1 : ℝ) * N + a.2)
    (hY : Y ≤ (b.1 : ℝ) * N + b.2) :
    X + Y ≤ ((addCE a b).1 : ℝ) * N + (addCE a b).2 := by
  simp only [addCE]; push_cast; linarith

lemma const_le (a e : ℚ) (N : ℕ) : (a : ℝ) * N + e ≤ (((a, e) : CE).1 : ℝ) * N + ((a, e) : CE).2 :=
  le_rfl

lemma lemmaD {c : CE} {Nlo N X : ℕ} (hok : okCE Nlo c = true) (hN : Nlo ≤ N)
    (hX : (X : ℝ) ≤ (c.1 : ℝ) * N + c.2) : X ≤ c7 N := by
  unfold okCE at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  have h1R : (c.1 : ℝ) < 1 / 25 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2R : (c.1 : ℝ) * Nlo + c.2 < ((Nlo : ℝ) - 6) / 25 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h2; push_cast at this; exact this
  have hNR : (Nlo : ℝ) ≤ N := by exact_mod_cast hN
  have hc7 : ((N : ℝ) - 6) / 25 ≤ c7 N := by
    unfold c7
    have := Nat.div_add_mod (N + 18) 25
    have := Nat.mod_lt (N + 18) (show 0 < 25 by norm_num)
    have h : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast h
    linarith
  have : (X : ℝ) < c7 N := by nlinarith
  exact_mod_cast this.le

lemma ulProd_eq (n : ℕ) : ulProd n = ∏ j ∈ range n, UL.getD j 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ulProd, ih, prod_range_succ]

lemma ulProd_u1 {n : ℕ} (hn : n ≤ 30) : ulProd n = ∏ j ∈ range n, u1 j := by
  rw [ulProd_eq]; apply prod_congr rfl; intro j hj
  rw [u1_eq_UL (by have := mem_range.mp hj; omega)]


section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

lemma shWith_sound (N Nhi b pc Y rval : ℕ) (hbN : b ≤ N) (hN : N ≤ Nhi)
    (hρ_nat : rhoBound b ≤ rval) (hY : 1 ≤ Y) :
    shB N b pc Y ≤
      ((shCEWith tab Nhi pc Y rval).1 : ℝ) * N + ((shCEWith tab Nhi pc Y rval).2 : ℝ) := by
  unfold shB shCEWith
  have hm := primeSum_le htab pc Y (fun p => pc < p) (N : ℝ) (by positivity)
  have hρ : (rhoBound b : ℝ) ≤ rval := by exact_mod_cast hρ_nat
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hNR : (N : ℝ) ≤ Nhi := by exact_mod_cast hN
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hNb : (N : ℝ) * b ≤ (Nhi : ℝ) * Nhi := by
    have : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have hG : 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 ≤
      2 * ((Nhi : ℝ) + 1) / Y + ((Nhi : ℝ) * Nhi + 1) / ((Y : ℝ) * Y) := by
    rw [sq]
    have hY0 : (0 : ℝ) < Y := by linarith
    gcongr
  have hG0 : 0 ≤ 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 := by positivity
  have := mul_le_mul hρ hG hG0 (by positivity)
  push_cast
  linarith

end

lemma chain6_cover (b N : ℕ) : ∀ (rows : List Row6) (a : ℕ), chain6 a b rows = true →
    (∀ r ∈ rows, r.Nlo ≤ r.Nhi) → rows ≠ [] → a ≤ N → N ≤ b →
    ∃ r ∈ rows, r.Nlo ≤ N ∧ N ≤ r.Nhi := by
  intro rows
  induction rows with
  | nil => intro a _ _ h; exact absurd rfl h
  | cons r rs ih =>
    intro a hc hle _ haN hNb
    simp only [chain6, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hra, hc⟩ := hc
    by_cases hN : N ≤ r.Nhi
    · exact ⟨r, List.mem_cons_self .., hra ▸ haN, hN⟩
    · cases rs with
      | nil => simp [chain6] at hc; omega
      | cons r' rs' =>
        obtain ⟨r'', hmem, h⟩ := ih r.Nhi hc (fun x hx => hle x (List.mem_cons_of_mem _ hx))
          (by simp) (by omega) hNb
        exact ⟨r'', List.mem_cons_of_mem _ hmem, h⟩

end Erdos848


namespace Erdos848

open ErdosComp Finset

theorem smallPrimes_filter : (List.range 4473).filter isPrimeB = smallPrimesL := by decide +kernel

theorem PSH_eq : PSH = smallPrimesL.prod := by decide +kernel

lemma mem_smallPrimes {p : ℕ} : p ∈ smallPrimesL ↔ p < 4473 ∧ p.Prime := by
  rw [← smallPrimes_filter, List.mem_filter, List.mem_range, isPrimeB_iff]

theorem fastP_eq {n : ℕ} (hn : n < 20007729) : fastP n = isPrimeB n := by
  unfold fastP
  by_cases hs : n < 4473
  · rw [show Nat.blt n 4473 = true from Nat.blt_eq.mpr hs, cond_true]
  · have hb : Nat.blt n 4473 = false := by
      cases h : Nat.blt n 4473
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hs
    rw [hb, cond_false]

    have key : Nat.gcd n PSH = 1 ↔ n.Prime := by
      rw [PSH_eq]
      constructor
      · intro h
        by_contra hnp
        have hn0 : 0 < n := by omega
        have hsq := Nat.minFac_sq_le_self hn0 hnp
        have hmf : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
        have hlt : Nat.minFac n < 4473 := by
          by_contra hge; push Not at hge
          have : 4473 * 4473 ≤ Nat.minFac n ^ 2 := by nlinarith
          omega
        have hmem : Nat.minFac n ∈ smallPrimesL := mem_smallPrimes.mpr ⟨hlt, hmf⟩
        have hd1 : Nat.minFac n ∣ Nat.gcd n smallPrimesL.prod :=
          Nat.dvd_gcd (Nat.minFac_dvd n) (List.dvd_prod hmem)
        rw [h] at hd1
        exact hmf.one_lt.ne' (Nat.dvd_one.mp hd1)
      · intro hp
        have : Nat.Coprime n smallPrimesL.prod := by
          rw [Nat.coprime_list_prod_right_iff]
          intro q hq
          have hq' := mem_smallPrimes.mp hq
          rw [Nat.coprime_primes hp hq'.2]
          omega
        exact this
    have e1 : (Nat.beq (Nat.gcd n PSH) 1 = true) ↔ (isPrimeB n = true) := by
      rw [Nat.beq_eq, key, isPrimeB_iff]
    cases h1 : Nat.beq (Nat.gcd n PSH) 1 <;> cases h2 : isPrimeB n <;> simp_all

lemma addSt_zero (a : PSt) : addSt a zeroSt = a := by cases a; simp [addSt, zeroSt]
lemma zero_addSt (a : PSt) : addSt zeroSt a = a := by cases a; simp [addSt, zeroSt]
lemma addSt_assoc (a b c : PSt) : addSt (addSt a b) c = addSt a (addSt b c) := by
  cases a; cases b; cases c; simp [addSt]; omega

lemma stepSt_eq_add {n : ℕ} (hn : n < 20007729) (s : PSt) : stepSt n s = addSt s (contribF n) := by
  have hf := fastP_eq hn
  unfold stepSt contribF isU1B
  rw [hf]
  cases hp : isPrimeB n
  · simp [addSt_zero]
  · cases hu : (n % 4 == 1 && decide (13 ≤ n))
    · simp [hu, addSt]
    · simp [hu, addSt]

def segSeq (lo : ℕ) : ℕ → PSt
  | 0 => zeroSt
  | k + 1 => addSt (segSeq lo k) (contribF (lo + k + 1))

lemma segSeq_add (lo a : ℕ) : ∀ b, segSeq lo (a + b) = addSt (segSeq lo a) (segSeq (lo + a) b) := by
  intro b
  induction b with
  | zero => simp [segSeq, addSt_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, segSeq, ih, segSeq, addSt_assoc]
    congr 3; omega

lemma segB_eq : ∀ f lo len, len ≤ 2 ^ f → segB (f + 1) lo len = segSeq lo len := by
  intro f
  induction f with
  | zero =>
    intro lo len hlen
    simp only [pow_zero] at hlen
    interval_cases len
    · rfl
    · show contribF (lo + 1) = addSt zeroSt (contribF (lo + 0 + 1))
      rw [zero_addSt]
  | succ f ih =>
    intro lo len hlen
    show (cond (Nat.beq len 0) zeroSt (cond (Nat.beq len 1) (contribF (lo + 1))
      (addSt (segB (f + 1) lo (len / 2)) (segB (f + 1) (lo + len / 2) (len - len / 2))))) =
      segSeq lo len
    rcases Nat.lt_or_ge len 2 with h | h
    · interval_cases len
      · rfl
      · show contribF (lo + 1) = addSt zeroSt (contribF (lo + 0 + 1))
        rw [zero_addSt]
    · have h0 : Nat.beq len 0 = false := by
        cases hh : Nat.beq len 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
      have h1 : Nat.beq len 1 = false := by
        cases hh : Nat.beq len 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
      rw [h0, h1, cond_false, cond_false, ih lo (len / 2) (by rw [pow_succ] at hlen; omega),
        ih (lo + len / 2) (len - len / 2) (by rw [pow_succ] at hlen; omega), ← segSeq_add]
      congr 1; omega

lemma stAt_add_segSeq (lo : ℕ) : ∀ k, lo + k < 20007729 → stAt (lo + k) = addSt (stAt lo) (segSeq lo k) := by
  intro k
  induction k with
  | zero => intro _; simp [segSeq, addSt_zero]
  | succ k ih =>
    intro hk
    rw [← Nat.add_assoc, stAt, ih (by omega), stepSt_eq_add (by omega), segSeq, addSt_assoc]

theorem stAt_add_segB {lo len : ℕ} (h : lo + len < 20007729) :
    stAt (lo + len) = addSt (stAt lo) (segB 64 lo len) := by
  have h63 : (20007729 : ℕ) ≤ 2 ^ 63 := by norm_num
  rw [segB_eq 63 lo len (by omega), stAt_add_segSeq lo len h]

lemma eqSt_true {a b : PSt} (h : eqSt a b = true) : a = b := by
  unfold eqSt at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  cases a; cases b; simp_all

theorem chainOK_sound : ∀ (tab : List (ℕ × PSt)) (x : ℕ) (v : PSt), v = stAt x →
    chainOK x v tab = true → ∀ e ∈ tab, e.2 = stAt e.1 := by
  intro tab
  induction tab with
  | nil => intro _ _ _ _ e he; simp at he
  | cons hd rest ih =>
    obtain ⟨y, w⟩ := hd
    intro x v hv hc e he
    unfold chainOK at hc
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    obtain ⟨⟨⟨hxy, hy⟩, heq⟩, hrest⟩ := hc
    have hw : w = stAt y := by
      rw [eqSt_true heq, hv, show y = x + (y - x) by omega, ← stAt_add_segB (by omega)]
      congr 1; omega
    rcases List.mem_cons.mp he with rfl | he
    · exact hw
    · exact ih y w hw hrest e he

end Erdos848


namespace Erdos848

open Finset ErdosComp

def P10 : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

lemma P10_prod : ∏ p ∈ P10, p = 100280245065 := by decide

lemma mem_P10 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h31 : p ≤ 31) : p ∈ P10 := by
  have : ∀ p ≤ 31, p.Prime → p ≠ 2 → p ∈ P10 := by decide
  exact this p h31 hp h2

lemma P10_card : P10.card = 10 := by decide

lemma P10_le (p : ℕ) (hp : p ∈ P10) : p ≤ 32 := by
  simp only [P10, mem_insert, mem_singleton] at hp; omega

theorem pow32_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    32 ^ S.card * 100280245065 ≤ 32 ^ 10 * ∏ p ∈ S, p := by
  classical
  set S1 := S.filter (· ≤ 31)
  set S2 := S.filter (fun p => ¬ p ≤ 31)
  have hcard : S.card = S1.card + S2.card := (card_filter_add_card_filter_not _).symm
  have hprod : ∏ p ∈ S, p = (∏ p ∈ S1, p) * ∏ p ∈ S2, p := (prod_filter_mul_prod_filter_not S (· ≤ 31) (fun p => p)).symm
  have hS1 : S1 ⊆ P10 := fun p hp => by
    have h := mem_filter.mp hp
    exact mem_P10 (hS p h.1).1 (hS p h.1).2 h.2
  have h2 : 32 ^ S2.card ≤ ∏ p ∈ S2, p := by
    rw [← prod_const]
    apply Finset.prod_le_prod' ; intro p hp
    have h := mem_filter.mp hp
    omega
  have hsd : (∏ p ∈ S1, p) * ∏ p ∈ P10 \ S1, p = 100280245065 := by
    rw [mul_comm, prod_sdiff hS1, P10_prod]
  have hrest : ∏ p ∈ P10 \ S1, p ≤ 32 ^ (P10 \ S1).card := by
    rw [← prod_const]
    exact Finset.prod_le_prod' (fun p hp => P10_le p (mem_sdiff.mp hp).1)
  have hcd : (P10 \ S1).card + S1.card = 10 := by
    rw [card_sdiff_add_card_eq_card hS1, P10_card]
  rw [hcard, hprod, ← hsd, pow_add]
  calc 32 ^ S1.card * 32 ^ S2.card * ((∏ p ∈ S1, p) * ∏ p ∈ P10 \ S1, p)
      ≤ 32 ^ S1.card * 32 ^ S2.card * ((∏ p ∈ S1, p) * 32 ^ (P10 \ S1).card) := by gcongr
    _ = 32 ^ ((P10 \ S1).card + S1.card) * ((∏ p ∈ S1, p) * 32 ^ S2.card) := by ring
    _ ≤ 32 ^ ((P10 \ S1).card + S1.card) * ((∏ p ∈ S1, p) * ∏ p ∈ S2, p) := by gcongr
    _ = 32 ^ 10 * ((∏ p ∈ S1, p) * ∏ p ∈ S2, p) := by rw [hcd]

theorem rhoBound_pow5 {b : ℕ} (hb : 1 ≤ b) :
    rhoBound b ^ 5 * 100280245065 ≤ 1024 * 32 ^ 10 * b := by
  have hP := pow32_le_prod (oddPF b) (fun p hp => oddPF_prime hp)
  have hdiv : ∏ p ∈ oddPF b, p ≤ b := Nat.le_of_dvd (by omega) (prod_oddPF_dvd b)
  have htf : twoFactor b ≤ 4 := by unfold twoFactor; split_ifs <;> omega
  have hr : rhoBound b ≤ 4 * 2 ^ (oddPF b).card := by
    unfold rhoBound; rw [oddOmega_eq]; exact Nat.mul_le_mul_right _ htf
  have h5 : rhoBound b ^ 5 ≤ 1024 * 32 ^ (oddPF b).card := by
    calc rhoBound b ^ 5 ≤ (4 * 2 ^ (oddPF b).card) ^ 5 := Nat.pow_le_pow_left hr 5
      _ = 1024 * 32 ^ (oddPF b).card := by
          rw [mul_pow, ← pow_mul, mul_comm (oddPF b).card 5, pow_mul]; norm_num
  calc rhoBound b ^ 5 * 100280245065 ≤ 1024 * 32 ^ (oddPF b).card * 100280245065 :=
        Nat.mul_le_mul_right _ h5
    _ = 1024 * (32 ^ (oddPF b).card * 100280245065) := by ring
    _ ≤ 1024 * (32 ^ 10 * ∏ p ∈ oddPF b, p) := Nat.mul_le_mul_left _ hP
    _ ≤ 1024 * (32 ^ 10 * b) := by gcongr
    _ = 1024 * 32 ^ 10 * b := by ring

def tt (N : ℕ) : ℕ := Nat.sqrt (Nat.sqrt N)
def Yt (N : ℕ) : ℕ := N / tt N

lemma tt_pow4_le (N : ℕ) : tt N ^ 4 ≤ N := by
  have h1 := Nat.sqrt_le (Nat.sqrt N)
  have h2 := Nat.sqrt_le N
  unfold tt
  calc Nat.sqrt (Nat.sqrt N) ^ 4 =
        (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) * (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) := by ring
    _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul h1 h1
    _ ≤ N := h2

lemma lt_tt_pow4 (N : ℕ) : N < (tt N + 1) ^ 4 := by
  have h1 := Nat.lt_succ_sqrt (Nat.sqrt N)
  have h2 := Nat.lt_succ_sqrt N
  unfold tt
  set s := Nat.sqrt N
  set u := Nat.sqrt s
  have : s + 1 ≤ (u + 1) * (u + 1) := h1
  calc N < (s + 1) * (s + 1) := h2
    _ ≤ ((u + 1) * (u + 1)) * ((u + 1) * (u + 1)) := Nat.mul_le_mul this this
    _ = (u + 1) ^ 4 := by ring

lemma tt_ge {N : ℕ} (hN : 10 ^ 60 ≤ N) : 10 ^ 14 ≤ tt N := by
  by_contra h; push Not at h
  have h1 : (tt N + 1) ^ 4 ≤ (10 ^ 14) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have := lt_tt_pow4 N
  norm_num at h1; omega

lemma pow4_le_pow3 : ∀ k, 9 ≤ k → (k + 1) ^ 4 ≤ 3 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (k + 2) ^ 4 ≤ 3 * (k + 1) ^ 4 := by nlinarith [sq_nonneg (k * k), sq_nonneg k]
    calc (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring
      _ ≤ 3 * (k + 1) ^ 4 := this
      _ ≤ 3 * 3 ^ k := by omega
      _ = 3 ^ (k + 1) := by ring

lemma log3_lt_tt {N : ℕ} (hN : 10 ^ 60 ≤ N) : Nat.log 3 N + 1 ≤ tt N := by
  have ht := tt_ge hN
  set k := Nat.log 3 N
  by_cases hk : 9 ≤ k
  · have h1 := pow4_le_pow3 k hk
    have h2 : 3 ^ k ≤ N := Nat.pow_log_le_self 3 (by omega)
    have h3 := lt_tt_pow4 N
    have : (k + 1) ^ 4 < (tt N + 1) ^ 4 := by omega
    have := (Nat.pow_lt_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp this
    omega
  · omega

section
variable {N : ℕ} (hN : 10 ^ 60 ≤ N)
include hN

omit hN in
lemma Yt_mul_le : Yt N * tt N ≤ N := Nat.div_mul_le_self N (tt N)

lemma lt_Yt_mul : N < (Yt N + 1) * tt N := by
  have ht : 0 < tt N := by have := tt_ge hN; omega
  have := Nat.lt_div_mul_add (a := N) ht
  unfold Yt; nlinarith

lemma Yt_ge : tt N ^ 3 ≤ Yt N := by
  have ht : 0 < tt N := by have := tt_ge hN; omega
  unfold Yt
  rw [Nat.le_div_iff_mul_le ht]
  have := tt_pow4_le N
  calc tt N ^ 3 * tt N = tt N ^ 4 := by ring
    _ ≤ N := this

lemma Yt_big : PM < Yt N := by
  have h1 := Yt_ge hN
  have h2 : (10 ^ 14) ^ 3 ≤ tt N ^ 3 := Nat.pow_le_pow_left (tt_ge hN) 3
  unfold PM; norm_num at h2; omega

lemma Yt_pos : 1 ≤ Yt N := by have := Yt_big hN; unfold PM at this; omega

lemma growth_Y : (Yt N : ℝ) ≤ N / 10 ^ 14 := by
  have h1 := Yt_mul_le (N := N)
  have h2 := tt_ge hN
  have : Yt N * 10 ^ 14 ≤ N := le_trans (Nat.mul_le_mul_left _ h2) h1
  rw [le_div_iff₀ (by positivity)]; exact_mod_cast this


lemma growth_pell_adm :
    ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Yt N + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤
      N / 10 ^ 14 := by
  have ht := tt_ge hN
  have h1 := lt_Yt_mul hN
  have hdiv : (N ^ 2 + 1) / (Yt N + 1) ^ 2 ≤ tt N ^ 2 := by
    apply Nat.div_le_of_le_mul
    have : N + 1 ≤ (Yt N + 1) * tt N := h1
    nlinarith
  have hadm : ErdosComp.pellAdmM ((N ^ 2 + 1) / (Yt N + 1) ^ 2) ≤ tt N ^ 2 :=
    (min_le_left _ _).trans hdiv
  have hlog := log3_lt_tt hN
  have h4 := tt_pow4_le N
  have : ErdosComp.pellAdmM ((N ^ 2 + 1) / (Yt N + 1) ^ 2) * (Nat.log 3 N + 1) * 10 ^ 14 ≤ N := by
    calc ErdosComp.pellAdmM ((N ^ 2 + 1) / (Yt N + 1) ^ 2) * (Nat.log 3 N + 1) * 10 ^ 14
        ≤ tt N ^ 2 * tt N * tt N := by gcongr
      _ = tt N ^ 4 := by ring
      _ ≤ N := h4
  rw [le_div_iff₀ (by positivity)]; exact_mod_cast this

lemma rho_tt_le {b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) : 10 ^ 6 * rhoBound b * tt N ^ 2 ≤ N := by
  have h5 := rhoBound_pow5 hb
  have h4 := tt_pow4_le N
  set ρ := rhoBound b
  set t := tt N
  have hC : ρ ^ 5 * 100280245065 ≤ 1024 * 32 ^ 10 * N :=
    h5.trans (Nat.mul_le_mul_left _ hbN)
  have hN3 : 10 ^ 60 * (1024 * 32 ^ 10) ^ 2 ≤ N ^ 3 := by
    have : (10 ^ 60) ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    norm_num at this ⊢; omega
  have key : (10 ^ 6 * ρ * t ^ 2) ^ 10 * 100280245065 ^ 2 ≤ N ^ 10 * 100280245065 ^ 2 := by
    calc (10 ^ 6 * ρ * t ^ 2) ^ 10 * 100280245065 ^ 2
        = 10 ^ 60 * (ρ ^ 5 * 100280245065) ^ 2 * (t ^ 4) ^ 5 := by ring
      _ ≤ 10 ^ 60 * (1024 * 32 ^ 10 * N) ^ 2 * N ^ 5 := by gcongr
      _ = (10 ^ 60 * (1024 * 32 ^ 10) ^ 2) * N ^ 7 := by ring
      _ ≤ N ^ 3 * N ^ 7 := Nat.mul_le_mul_right _ hN3
      _ ≤ N ^ 10 * 100280245065 ^ 2 := by
          rw [← pow_add]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have := Nat.le_of_mul_le_mul_right key (by positivity)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (10 : ℕ) ≠ 0)).mp this

lemma growth_rho {b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) :
    (rhoBound b : ℝ) * (2 * ((N : ℝ) + 1) / (Yt N) + ((N : ℝ) * b + 1) / ((Yt N : ℝ) ^ 2)) ≤
      N / 50000 := by
  have hρ := rho_tt_le hN hb hbN
  have h1 := lt_Yt_mul hN
  have hY1 := Yt_pos hN
  have htt := tt_ge hN
  have hNY' : N ≤ 2 * Yt N * tt N := by nlinarith
  have hNY : (N : ℝ) ≤ 2 * (Yt N : ℝ) * (tt N : ℝ) := by exact_mod_cast hNY'
  have hYR : (1 : ℝ) ≤ Yt N := by exact_mod_cast hY1
  have hNR : (10 : ℝ) ^ 60 ≤ N := by exact_mod_cast hN
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hYpos : (0 : ℝ) < Yt N := by linarith
  have ht1 : (1 : ℝ) ≤ tt N := by exact_mod_cast (show 1 ≤ tt N by omega)
  have e1 : 2 * ((N : ℝ) + 1) / Yt N ≤ 8 * (tt N : ℝ) := by
    rw [div_le_iff₀ hYpos]; nlinarith
  have e2 : ((N : ℝ) * b + 1) / (Yt N : ℝ) ^ 2 ≤ 8 * (tt N : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (N : ℝ) * b + 1 ≤ 2 * (N : ℝ) * N := by nlinarith
    have hsq : (N : ℝ) * N ≤ (2 * (Yt N : ℝ) * tt N) * (2 * (Yt N : ℝ) * tt N) := by
      have : (0 : ℝ) ≤ N := by positivity
      exact mul_self_le_mul_self this hNY
    nlinarith
  have hρR : (10 : ℝ) ^ 6 * rhoBound b * (tt N : ℝ) ^ 2 ≤ N := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) ≤ rhoBound b := by positivity
  calc (rhoBound b : ℝ) * (2 * ((N : ℝ) + 1) / Yt N + ((N : ℝ) * b + 1) / (Yt N : ℝ) ^ 2)
      ≤ rhoBound b * (8 * (tt N : ℝ) + 8 * (tt N : ℝ) ^ 2) := by gcongr
    _ ≤ rhoBound b * (16 * (tt N : ℝ) ^ 2) := by gcongr; nlinarith
    _ ≤ N / 50000 := by rw [le_div_iff₀ (by norm_num)]; nlinarith

end

lemma s2P_big (tab : List (ℕ × PSt)) {lo Y : ℕ} (hlo : lo ≤ PM) (hY : PM < Y) :
    s2P tab lo Y = s2P tab lo PM1 := by
  unfold s2P PM1; simp [show ¬ Y ≤ PM by omega, hlo]

lemma s2U_big (tab : List (ℕ × PSt)) {lo Y : ℕ} (hlo : lo ≤ PM) (hY : PM < Y) :
    s2U tab lo Y = s2U tab lo PM1 := by
  unfold s2U PM1; simp [show ¬ Y ≤ PM by omega, hlo]

lemma card_Ioc_filter_le (lo Y : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (((Ioc lo Y).filter P).card : ℝ) ≤ Y := by
  have : ((Ioc lo Y).filter P).card ≤ Y :=
    (card_filter_le _ _).trans (by rw [Nat.card_Ioc]; omega)
  exact_mod_cast this

lemma smallP_U1000 : smallP 1000 IsU1 = (range 1001).filter (fun p => isU1B p = true) := by
  ext p; simp only [smallP, mem_filter, isU1B_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2⟩⟩

lemma gall_sound (N Nt : ℕ) (hN : Nt ≤ N) :
    ∑ p ∈ smallP 1000 IsU1, max (gC N 41 p) 0 ≤
      ((gAllC : ℚ) : ℝ) * N + ((gAllE Nt : ℚ) : ℝ) := by
  unfold gAllC gAllE
  rw [sumF_eq, sumF_eq, ← smallP_U1000]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_le_sum; intro p _
  rw [gC_eq]
  have := gmax_le ((gA p : ℚ) : ℝ) ((gE p : ℚ) : ℝ) (gA_nonneg _)
    (show (Nt : ℝ) ≤ N by exact_mod_cast hN)
  push_cast at this
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

lemma shT_sound (N b Y : ℕ) (hY : PM < Y) :
    shB N b 2000 Y ≤ ((shT tab).1 : ℝ) * N + ((shT tab).2 : ℝ) + Y +
      rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  unfold shB shT
  have h1 := midsum_le _ _ (midP_sub_primesIn 2000 Y (fun p => 2000 < p)) (N : ℝ) (by positivity)
  have h2 := S2_primesIn_le htab 2000 Y
  rw [s2P_big tab (by unfold PM; norm_num) hY] at h2
  have h3 : ((primesIn 2000 Y).card : ℝ) ≤ Y := card_Ioc_filter_le 2000 Y Nat.Prime
  have hN : (0 : ℝ) ≤ N := by positivity
  have := mul_le_mul_of_nonneg_left h2 hN
  dsimp only; push_cast
  linarith

lemma lemBT_sound (N q T Y : ℕ) (hY : PM < Y) :
    lemBB N q T 41 2000 Y ≤ ((lemBT tab q T).1 : ℝ) * N + ((lemBT tab q T).2 : ℝ) + 2 * Y +
      ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  unfold lemBB lemBT
  have h1 := u1Sum_le htab 41 2000 IsU1 (fun _ h => h) ((N : ℝ) / q) (by positivity)
  have h2 := midsum_le _ _ (midP_sub_u1In 2000 Y (fun p => IsU1 p ∧ 2000 < p) (fun _ h => h.1))
    (N : ℝ) (by positivity)
  have h3 := S2_u1In_le htab 2000 Y
  rw [s2U_big tab (by unfold PM; norm_num) hY] at h3
  have h4 : ((u1In 2000 Y).card : ℝ) ≤ Y := card_Ioc_filter_le 2000 Y IsU1
  have hT : (0 : ℝ) ≤ T := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hT
  have h3' := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ N by positivity)
  rw [sum_two, sum_two]
  dsimp only; push_cast
  rw [prodU_cast, kU_eq]
  unfold PU
  push_cast
  linear_combination 2 * h1' + 2 * h2 + 2 * h3' + 2 * h4

lemma lemCT_sound (N Nt Y : ℕ) (hY : PM < Y) (hNt : Nt ≤ N) :
    lemCB N 41 1000 2000 Y 2000 (∑ p ∈ smallP 1000 IsU1, max (gC N 41 p) 0) ≤
      ((lemCT tab Nt).1 : ℝ) * N + ((lemCT tab Nt).2 : ℝ) + 2 * Y +
      ((ErdosComp.pellAdmM ((N ^ 2 + 1) / (Y + 1) ^ 2) * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  unfold lemCB lemCT
  have e1 := u1Sum_le htab 41 2000 (fun p => IsU1 p ∧ 41 < p) (fun _ h => h.1) ((N : ℝ) / 25)
    (by positivity)
  have e2 := midsum_le _ _ (midP_sub_u1In 2000 Y (fun p => IsU1 p ∧ 2000 < p) (fun _ h => h.1))
    (N : ℝ) (by positivity)
  have e3 := S2_u1In_le htab 2000 Y
  rw [s2U_big tab (by unfold PM; norm_num) hY] at e3
  have e3' := mul_le_mul_of_nonneg_left e3 (show (0 : ℝ) ≤ N by positivity)
  have e4 : ((u1In 2000 Y).card : ℝ) ≤ Y := card_Ioc_filter_le 2000 Y IsU1
  have e5 := sumNon_eq N
  have e6 := gall_sound N Nt hNt
  have e7 := primeSum_le htab 1000 2000 (fun p => 1000 < p) (N : ℝ) (Nat.cast_nonneg N)
  rw [sum_two, sum_two]
  dsimp only; push_cast
  rw [prodU_cast, kU_eq]
  push_cast at e6
  linarith

end

lemma lemmaD_tail {c : CE} {N X : ℕ} (hok : okT c = true) (hN : 10 ^ 60 ≤ N) (g : ℝ)
    (hg : g ≤ N / 10000) (hX : (X : ℝ) ≤ (c.1 : ℝ) * N + c.2 + g) : X ≤ c7 N := by
  unfold okT at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  have h1R : (c.1 : ℝ) ≤ 1 / 25 - 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2R : (c.2 : ℝ) ≤ 10 ^ 30 := by
    have := (Rat.cast_le (K := ℝ)).mpr h2; push_cast at this; exact this
  have hNR : (10 : ℝ) ^ 60 ≤ N := by exact_mod_cast hN
  have hc7 : ((N : ℝ) - 6) / 25 ≤ c7 N := by
    unfold c7
    have := Nat.div_add_mod (N + 18) 25
    have := Nat.mod_lt (N + 18) (show 0 < 25 by norm_num)
    have h : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast h
    linarith
  have : (X : ℝ) < c7 N := by nlinarith
  exact_mod_cast this.le


def tabH4 : List (ℕ × PSt) := [
  (31, ⟨11, 3, 446051190201259476276220011855, 10566428017863103602383146205⟩),
  (41, ⟨13, 5, 447376534388799589664846994386, 11891772205403216991010128736⟩),
  (764, ⟨135, 63, 452077470129328135772704359799, 13728619787174427215784269266⟩),
  (1000, ⟨168, 79, 452120430249304581998945097207, 13749931498619531633258972673⟩),
  (2000, ⟨303, 146, 452189106009569515775438624162, 13784719359983660551765345707⟩),
  (2500, ⟨367, 179, 452201941983909991060301760800, 13791287922158301851772943534⟩),
  (3804, ⟨529, 259, 452218975297452481193294950070, 13799684902595045638392141296⟩),
  (5000, ⟨669, 328, 452226334178974578985408477369, 13803298842970054412617483750⟩),
  (15000, ⟨1754, 865, 452241107541874005071522928367, 13810605560246829058679723051⟩)
]

def rowsH4 : List Row6 := [
  ⟨160000000, 178474120, 3804, 6291456, 1048576, 764⟩,
  ⟨178474120, 185882853, 15000, 6291456, 1048576, 2500⟩,
  ⟨185882853, 196433708, 15000, 6291456, 1572864, 2500⟩,
  ⟨196433708, 215140108, 15000, 8388608, 1572864, 2500⟩,
  ⟨215140108, 253753775, 15000, 8388608, 1572864, 2500⟩,
  ⟨253753775, 319170794, 15000, 8388608, 1572864, 2500⟩,
  ⟨319170794, 471601920, 15000, 12582912, 2097152, 2500⟩,
  ⟨471601920, 856764596, 15000, 16777216, 3145728, 5000⟩,
  ⟨856764596, 2198858274, 15000, 33554432, 8388608, 5000⟩,
  ⟨2198858274, 7152731353, 15000, 100663296, 16777216, 5000⟩,
  ⟨7152731353, 42834313194, 15000, 402653184, 67108864, 15000⟩,
  ⟨42834313194, 521332075412, 15000, 2147483648, 268435456, 15000⟩,
  ⟨521332075412, 17982901920914, 15000, 34359738368, 4294967296, 15000⟩,
  ⟨17982901920914, 2977013216435848, 15000, 1099511627776, 137438953472, 15000⟩,
  ⟨2977013216435848, 4131536154434864208, 15000, 281474976710656, 17592186044416, 15000⟩,
  ⟨4131536154434864208, 75557533192304796343312, 3804, 576460752303423488, 36028797018963968, 764⟩,
  ⟨75557533192304796343312, 9903250317982197351919463440, 3804, 9444732965739290427392, 147573952589676412928, 764⟩,
  ⟨9903250317982197351919463440, 83074494746678322546087778153737232, 3804, 2475880078570760549798248448, 38685626227668133590597632, 764⟩,
  ⟨83074494746678322546087778153737232, 22300139962368694744652476290813065834867728, 3804, 20769187434139310514121985316880384, 81129638414606681695789005144064, 764⟩,
  ⟨22300139962368694744652476290813065834867728, 766226974699069856942284347180312500372827142045641744, 3804, 5575186299632655785383929568162090376495104, 5444517870735015415413993718908291383296, 764⟩,
  ⟨766226974699069856942284347180312500372827142045641744, 1000000000000000000000000000000000000000000000000000000000000, 3804, 730750818665451459101842416358141509827966271488, 356811923176489970264571492362373784095686656, 764⟩
]

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem tabH4_ok : chainOK 0 zeroSt tabH4 = true := by decide +kernel

theorem tabH4_valid : ∀ e ∈ tabH4, e.2 = stAt e.1 :=
  chainOK_sound tabH4 0 zeroSt rfl tabH4_ok

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem rowsH4_ok : rowsH4.all (checkRowH4 tabH4) = true := by decide +kernel

theorem chainH4_ok : chain6 160000000 (10 ^ 60) rowsH4 = true := by decide +kernel

theorem tailH4_ok : checkTailH4 tabH4 = true := by decide +kernel

lemma h4_of_row (r : Row6) (hr : checkRowH4 tabH4 r = true) (N : ℕ)
    (hlo : r.Nlo ≤ N) (hhi : N ≤ r.Nhi) :
    (∀ b rr, Witness N b → IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - rr) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = rr) b +
      vCount N (fun x => IsStar x ∧ x % 4 = rr) ≤ c7 N) ∧
    (∀ b b' rr, Witness N b → IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Witness N b' → b' % 25 = 7 → b' % 2 = 0 →
      classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - rr) +
      badCount N (fun a => a % 25 = 7 ∧ (a % 4 = rr ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 18) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = rr) ≤ c7 N) ∧
    (∀ b b' rr, Witness N b → IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Witness N b' → b' % 25 = 18 → b' % 2 = 0 →
      classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - rr) +
      badCount N (fun a => a % 25 = 18 ∧ (a % 4 = rr ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 7) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = rr) ≤ c7 N) := by
  unfold checkRowH4 at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨hY, _⟩, _⟩, hprod⟩, hprod5⟩, okIIIa⟩, okIIIb⟩ := hr
  have hS25 := smallP_excl25
  refine ⟨?_, ?_, ?_⟩
  · intro b rr hw hs hbr hrr
    have hodd : b % 2 = 1 := by omega
    have hsh := shWith_sound tabH4_valid N r.Nhi b r.pc r.Y (rhoOddC r.Nhi) hw.2.1 hhi
      (rhoBound_le_oddC hw.1 (hw.2.1.trans hhi) hodd hprod) hY
    have := caseIII2a_real N b rr 31 r.pc r.Y 41 r.pB r.YB hY hw hs hbr hrr
    have hc : 2 * ((N : ℝ) / 100) + 2 ≤ (((2 / 100 : ℚ), (2 : ℚ)) : CE).1 * N +
        (((2 / 100 : ℚ), (2 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le hc
      (addCE_le (res_sound tabH4_valid N 100 2 r.pc {2, 5} [2, 5] hS25) hsh))
      (lemB_sound tabH4_valid N r.Nhi 100 23 r.pB r.YB hhi)
    exact lemmaD okIIIa hlo (by push_cast; exact this.trans e)
  · intro b b' rr hw hs hbr hrr hw' h7' he
    have hodd : b % 2 = 1 := by omega
    have hno5 : ¬ 5 ∣ b' := fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega
    have hsh := shWith_sound tabH4_valid N r.Nhi b r.pc r.Y (rhoOddC r.Nhi) hw.2.1 hhi
      (rhoBound_le_oddC hw.1 (hw.2.1.trans hhi) hodd hprod) hY
    have hsh' := shWith_sound tabH4_valid N r.Nhi b' r.pc r.Y (rhoNo5C r.Nhi) hw'.2.1 hhi
      (rhoBound_le_no5C hw'.1 (hw'.2.1.trans hhi) hno5 hprod5) hY
    have := caseIII2b7_real N b b' rr 31 r.pc r.Y 41 r.pB r.YB hY hw hs hbr hrr hw' h7' he
    have hc : (N : ℝ) / 100 + 1 ≤ (((1 / 100 : ℚ), (1 : ℚ)) : CE).1 * N +
        (((1 / 100 : ℚ), (1 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le (addCE_le hc
      (addCE_le (res_sound tabH4_valid N 100 3 r.pc {2, 5} [2, 5] hS25) hsh))
      (addCE_le (res_sound tabH4_valid N 25 1 r.pc {2, 5} [2, 5] hS25) hsh'))
      (lemB_sound tabH4_valid N r.Nhi 100 23 r.pB r.YB hhi)
    exact lemmaD okIIIb hlo (by push_cast; exact this.trans e)
  · intro b b' rr hw hs hbr hrr hw' h18' he
    have hodd : b % 2 = 1 := by omega
    have hno5 : ¬ 5 ∣ b' := fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega
    have hsh := shWith_sound tabH4_valid N r.Nhi b r.pc r.Y (rhoOddC r.Nhi) hw.2.1 hhi
      (rhoBound_le_oddC hw.1 (hw.2.1.trans hhi) hodd hprod) hY
    have hsh' := shWith_sound tabH4_valid N r.Nhi b' r.pc r.Y (rhoNo5C r.Nhi) hw'.2.1 hhi
      (rhoBound_le_no5C hw'.1 (hw'.2.1.trans hhi) hno5 hprod5) hY
    have := caseIII2b18_real N b b' rr 31 r.pc r.Y 41 r.pB r.YB hY hw hs hbr hrr hw' h18' he
    have hc : (N : ℝ) / 100 + 1 ≤ (((1 / 100 : ℚ), (1 : ℚ)) : CE).1 * N +
        (((1 / 100 : ℚ), (1 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le (addCE_le hc
      (addCE_le (res_sound tabH4_valid N 100 3 r.pc {2, 5} [2, 5] hS25) hsh))
      (addCE_le (res_sound tabH4_valid N 25 1 r.pc {2, 5} [2, 5] hS25) hsh'))
      (lemB_sound tabH4_valid N r.Nhi 100 23 r.pB r.YB hhi)
    exact lemmaD okIIIb hlo (by push_cast; exact this.trans e)

lemma h4_tail (N : ℕ) (hN : 10 ^ 60 ≤ N) :
    (∀ b rr, Witness N b → IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - rr) +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = rr) b +
      vCount N (fun x => IsStar x ∧ x % 4 = rr) ≤ c7 N) ∧
    (∀ b b' rr, Witness N b → IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Witness N b' → b' % 25 = 7 → b' % 2 = 0 →
      classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - rr) +
      badCount N (fun a => a % 25 = 7 ∧ (a % 4 = rr ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 18) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = rr) ≤ c7 N) ∧
    (∀ b b' rr, Witness N b → IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Witness N b' → b' % 25 = 18 → b' % 2 = 0 →
      classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - rr) +
      badCount N (fun a => a % 25 = 18 ∧ (a % 4 = rr ∨ a % 2 = 0)) b +
      badCount N (fun a => a % 25 = 7) b' +
      vCount N (fun x => IsStar x ∧ x % 4 = rr) ≤ c7 N) := by
  have hc := tailH4_ok
  unfold checkTailH4 at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨okIIIa, okIIIb⟩ := hc
  set Y := Yt N
  have hYbig := Yt_big hN
  have hY1 := Yt_pos hN
  have gY := growth_Y hN
  have gP := growth_pell_adm hN
  have gR : ∀ b, Witness N b → (rhoBound b : ℝ) * (2 * ((N : ℝ) + 1) / Y +
      ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2) ≤ N / 50000 := fun b hw => growth_rho hN hw.1 hw.2.1
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hS25 := smallP_excl25
  have sh := fun b => shT_sound tabH4_valid N b Y hYbig
  refine ⟨?_, ?_, ?_⟩
  · intro b rr hw hs hbr hrr
    have := caseIII2a_real N b rr 31 2000 Y 41 2000 Y hY1 hw hs hbr hrr
    have r1 := res_sound tabH4_valid N 100 2 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound tabH4_valid N 100 23 Y hYbig
    have s1 := sh b; have g1 := gR b hw
    apply lemmaD_tail okIIIa hN (3 * Y + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII2aT, addCE]; push_cast; linarith
  · intro b b' rr hw hs hbr hrr hw' h7 he
    have := caseIII2b7_real N b b' rr 31 2000 Y 41 2000 Y hY1 hw hs hbr hrr hw' h7 he
    have r1 := res_sound tabH4_valid N 100 3 2000 {2, 5} [2, 5] hS25
    have r2 := res_sound tabH4_valid N 25 1 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound tabH4_valid N 100 23 Y hYbig
    have s1 := sh b; have s2 := sh b'; have g1 := gR b hw; have g2 := gR b' hw'
    apply lemmaD_tail okIIIb hN (4 * Y + N / 50000 + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII2bT, addCE]; push_cast; linarith
  · intro b b' rr hw hs hbr hrr hw' h18 he
    have := caseIII2b18_real N b b' rr 31 2000 Y 41 2000 Y hY1 hw hs hbr hrr hw' h18 he
    have r1 := res_sound tabH4_valid N 100 3 2000 {2, 5} [2, 5] hS25
    have r2 := res_sound tabH4_valid N 25 1 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound tabH4_valid N 100 23 Y hYbig
    have s1 := sh b; have s2 := sh b'; have g1 := gR b hw; have g2 := gR b' hw'
    apply lemmaD_tail okIIIb hN (4 * Y + N / 50000 + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII2bT, addCE]; push_cast; linarith

end Erdos848

private lemma fcard_eq4 (N : ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) :
    ((Finset.Icc 1 N).filter p).card = ((Finset.Icc 1 N).filter q).card :=
  congrArg Finset.card (Finset.filter_congr (fun x _ => hpq x))

private lemma le3_eq {a1 a2 a3 b1 b2 b3 c1 c2 : ℕ} (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3)
    (hc : b1 + b2 + b3 ≤ c1) (h4 : c1 = c2) : a1 + a2 + a3 ≤ c2 := by omega

private lemma le4_eq {a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 : ℕ}
    (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3) (h4 : a4 = b4)
    (hc : b1 + b2 + b3 + b4 ≤ c1) (h5 : c1 = c2) : a1 + a2 + a3 + a4 ≤ c2 := by omega

theorem OMA.solution : OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H4 := by
  dsimp only [OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H4]
  intro N hN
  have hmain : (∀ b rr, Erdos848.Witness N b → Erdos848.IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Erdos848.classCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - rr) +
      Erdos848.badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = rr) b +
      Erdos848.vCount N (fun x => Erdos848.IsStar x ∧ x % 4 = rr) ≤ Erdos848.c7 N) ∧
    (∀ b b' rr, Erdos848.Witness N b → Erdos848.IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Erdos848.Witness N b' → b' % 25 = 7 → b' % 2 = 0 →
      Erdos848.classCount N (fun a => a % 25 = 7 ∧ a % 4 = 4 - rr) +
      Erdos848.badCount N (fun a => a % 25 = 7 ∧ (a % 4 = rr ∨ a % 2 = 0)) b +
      Erdos848.badCount N (fun a => a % 25 = 18) b' +
      Erdos848.vCount N (fun x => Erdos848.IsStar x ∧ x % 4 = rr) ≤ Erdos848.c7 N) ∧
    (∀ b b' rr, Erdos848.Witness N b → Erdos848.IsStar b → b % 4 = rr → (rr = 1 ∨ rr = 3) →
      Erdos848.Witness N b' → b' % 25 = 18 → b' % 2 = 0 →
      Erdos848.classCount N (fun a => a % 25 = 18 ∧ a % 4 = 4 - rr) +
      Erdos848.badCount N (fun a => a % 25 = 18 ∧ (a % 4 = rr ∨ a % 2 = 0)) b +
      Erdos848.badCount N (fun a => a % 25 = 7) b' +
      Erdos848.vCount N (fun x => Erdos848.IsStar x ∧ x % 4 = rr) ≤ Erdos848.c7 N) := by
    by_cases h60 : N ≤ 10 ^ 60
    · have hall := List.all_eq_true.mp Erdos848.rowsH4_ok
      have hle : ∀ r ∈ Erdos848.rowsH4, r.Nlo ≤ r.Nhi := by
        intro r hr
        have h := hall r hr
        unfold ErdosComp.checkRowH4 at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1.1.1.2
      have hne : Erdos848.rowsH4 ≠ [] := List.ne_nil_of_length_pos (by decide)
      obtain ⟨r, hr, h1, h2⟩ := Erdos848.chain6_cover (10 ^ 60) N Erdos848.rowsH4 160000000
        Erdos848.chainH4_ok hle hne hN h60
      exact Erdos848.h4_of_row r (hall r hr) N h1 h2
    · exact Erdos848.h4_tail N (by omega)
  obtain ⟨c32a, c32b7, c32b18⟩ := hmain
  have hc7 : Erdos848.c7 N = ((Finset.Icc 1 N).filter (fun a => a % 25 = 7)).card :=
    (Erdos848.C7set_card N).symm
  refine ⟨?_, ?_, ?_⟩
  · intro b r hb hs hbr hr
    rw [Finset.mem_Icc] at hb
    have h := c32a b r ⟨hb.1.1, hb.1.2, hb.2⟩ hs hbr hr
    rw [hc7] at h
    dsimp only [Erdos848.classCount, Erdos848.badCount, Erdos848.vCount, Erdos848.IsStar] at h ⊢
    refine le3_eq ?_ ?_ ?_ h ?_ <;> exact fcard_eq4 N _ _ (fun _ => Iff.rfl)
  · intro b b' r hb hs hbr hr hb' h7 he'
    rw [Finset.mem_Icc] at hb hb'
    have h := c32b7 b b' r ⟨hb.1.1, hb.1.2, hb.2⟩ hs hbr hr ⟨hb'.1.1, hb'.1.2, hb'.2⟩ h7 he'
    rw [hc7] at h
    dsimp only [Erdos848.classCount, Erdos848.badCount, Erdos848.vCount, Erdos848.IsStar] at h ⊢
    refine le4_eq ?_ ?_ ?_ ?_ h ?_ <;> exact fcard_eq4 N _ _ (fun _ => Iff.rfl)
  · intro b b' r hb hs hbr hr hb' h18 he'
    rw [Finset.mem_Icc] at hb hb'
    have h := c32b18 b b' r ⟨hb.1.1, hb.1.2, hb.2⟩ hs hbr hr ⟨hb'.1.1, hb'.1.2, hb'.2⟩ h18 he'
    rw [hc7] at h
    dsimp only [Erdos848.classCount, Erdos848.badCount, Erdos848.vCount, Erdos848.IsStar] at h ⊢
    refine le4_eq ?_ ?_ ?_ ?_ h ?_ <;> exact fcard_eq4 N _ _ (fun _ => Iff.rfl)
